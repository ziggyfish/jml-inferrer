package com.z3x.theory;

import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Backtrackable congruence-closure E-graph.
 *
 * Each registered term gets a node; nodes form a union-find. Function-application terms
 * also live in a "signature table" keyed by (head, child reps...). When a merge changes
 * the rep of any child, all parent applications get re-signature'd, and any collision
 * triggers a further merge.
 *
 * The trail records every union and every signature-table insert so backtracking via
 * {@link #pushLevel()} / {@link #popLevel()} is O(events since last push).
 *
 * This implementation is intentionally simple: union by rank + path compression are kept
 * but undone by the trail (path compression is bounded by the size of the trail-walk
 * needed to recover the pre-union parent pointers).
 */
public final class EGraph {

    /** Node in the E-graph. One per registered term. */
    private static final class Node {
        final int termId;
        int parent;        // union-find parent
        int rank;          // union-find rank
        int classSize;
        // proof forest: edge from this node to the node it was directly merged with,
        // labelled with a "reason" (literal that caused the merge).
        int proofParent = -1;
        int proofReason = 0; // literal; 0 = congruence
        // class linked-list for fast iteration of class members:
        int next;          // next node in class circular list (== self if singleton)
        Node(int termId, int self) {
            this.termId = termId;
            this.parent = self;
            this.rank = 0;
            this.classSize = 1;
            this.next = self;
        }
    }

    /** Trail event types. */
    private enum Op { UNION, SIG_INSERT, SIG_REMOVE, EQ_ASSERT, DISEQ_ASSERT }

    private static final class Event {
        final Op op;
        final int a, b, c, d; // free-form payload
        Event(Op op, int a, int b, int c, int d) {
            this.op = op; this.a = a; this.b = b; this.c = c; this.d = d;
        }
    }

    private final TermFactory tf;
    private final Map<Integer, Integer> termIdToNode = new HashMap<>();
    private final List<Node> nodes = new ArrayList<>();

    /** parent edges (term-id -> list of parent application node ids). */
    private final Map<Integer, List<Integer>> parents = new HashMap<>();

    /** signature -> node id (canonical). Signature key uses representative term ids. */
    private final Map<String, Integer> sigTable = new HashMap<>();

    /** Trail of events for backtracking. */
    private final List<Event> trail = new ArrayList<>();
    private final List<Integer> levelMarks = new ArrayList<>();

    /** Asserted disequalities: pairs of node ids (canonical at assertion time). */
    private final List<int[]> diseqs = new ArrayList<>();

    /** Last conflict explanation (literals to negate). */
    public int[] lastConflict;

    public EGraph(TermFactory tf) { this.tf = tf; }

    public void pushLevel() { levelMarks.add(trail.size()); }

    public void popLevel() {
        if (levelMarks.isEmpty()) return;
        int mark = levelMarks.remove(levelMarks.size() - 1);
        while (trail.size() > mark) {
            Event e = trail.remove(trail.size() - 1);
            switch (e.op) {
                case UNION -> {
                    Node child = nodes.get(e.a);
                    Node oldRep = nodes.get(e.b);
                    int childRank = e.c;
                    int childClassSize = e.d;
                    // restore
                    child.parent = e.a;
                    child.rank = childRank;
                    child.classSize = childClassSize;
                    // Repair circular class list: we recorded enough to undo by swapping next pointers.
                    // The merge had stitched two circular lists; to undo, swap back.
                    int childNext = child.next;
                    int oldNext = oldRep.next;
                    child.next = oldNext;
                    oldRep.next = childNext;
                    oldRep.classSize -= childClassSize;
                }
                case SIG_INSERT -> sigTable.remove(decodeKey(e.a, e.b, e.c, e.d));
                case SIG_REMOVE -> sigTable.put(decodeKey(e.a, e.b, e.c, e.d), e.a);
                case EQ_ASSERT, DISEQ_ASSERT -> {
                    if (e.op == Op.DISEQ_ASSERT) {
                        diseqs.remove(diseqs.size() - 1);
                    }
                    // EQ_ASSERT itself is just a marker; the actual union event handles state.
                }
            }
        }
    }

    /** Register a term in the graph (idempotent). Returns the node id. */
    public int registerTerm(Term t) {
        Integer existing = termIdToNode.get(t.id);
        if (existing != null) return existing;
        int id = nodes.size();
        Node n = new Node(t.id, id);
        nodes.add(n);
        termIdToNode.put(t.id, id);

        // For applications, recurse on children, link parent edges, register signature.
        if (t instanceof Term.App app && !isInterpreted(app.symbol)) {
            for (Term c : app.args) {
                int cn = registerTerm(c);
                parents.computeIfAbsent(rep(cn), k -> new ArrayList<>()).add(id);
            }
            String key = signature(id);
            Integer existingSig = sigTable.get(key);
            if (existingSig != null) {
                // Will trigger a merge after caller finishes registration:
                // Defer by enqueueing through immediate union below.
                trail.add(new Event(Op.SIG_INSERT, id, 0, 0, 0));
                sigTable.put(key, id);
                // immediate congruence merge
                doUnion(id, existingSig, 0);
            } else {
                trail.add(new Event(Op.SIG_INSERT, id, 0, 0, 0));
                sigTable.put(key, id);
            }
        }
        return id;
    }

    public int rep(int n) {
        Node nd = nodes.get(n);
        while (nd.parent != n) { n = nd.parent; nd = nodes.get(n); }
        return n;
    }

    public int repOfTerm(Term t) {
        Integer n = termIdToNode.get(t.id);
        if (n == null) throw new IllegalStateException("Term not registered: " + t);
        return rep(n);
    }

    public boolean areEqual(Term a, Term b) {
        return repOfTerm(a) == repOfTerm(b);
    }

    /**
     * Assert a = b due to literal {@code reason}. Returns true if consistent, false if a conflict was
     * detected; on conflict, {@link #lastConflict} is populated.
     */
    public boolean assertEq(Term a, Term b, int reason) {
        int na = registerTerm(a);
        int nb = registerTerm(b);
        return doUnion(na, nb, reason);
    }

    /**
     * Assert a != b due to literal {@code reason}. If a and b are already in the same class, returns
     * false and populates {@link #lastConflict}.
     */
    public boolean assertDiseq(Term a, Term b, int reason) {
        int na = registerTerm(a);
        int nb = registerTerm(b);
        if (rep(na) == rep(nb)) {
            // Conflict: build explanation as path from a to b plus this disequality literal.
            int[] eqExpl = explainEq(na, nb);
            int[] out = new int[eqExpl.length + 1];
            System.arraycopy(eqExpl, 0, out, 0, eqExpl.length);
            out[eqExpl.length] = -reason; // negation: forcing a != b at the SAT layer
            // Conflict clause to learn = OR of (negation of each literal that participated).
            int[] conflict = new int[out.length];
            for (int i = 0; i < out.length; i++) conflict[i] = -out[i];
            lastConflict = conflict;
            return false;
        }
        diseqs.add(new int[] { na, nb, reason });
        trail.add(new Event(Op.DISEQ_ASSERT, na, nb, reason, 0));
        return true;
    }

    private boolean doUnion(int a, int b, int reason) {
        int ra = rep(a), rb = rep(b);
        if (ra == rb) return true;
        Node na = nodes.get(ra);
        Node nb = nodes.get(rb);
        // Union by rank: keep the larger as root.
        Node big, small;
        int bigId, smallId;
        if (na.rank < nb.rank) {
            small = na; smallId = ra; big = nb; bigId = rb;
        } else if (na.rank > nb.rank) {
            small = nb; smallId = rb; big = na; bigId = ra;
        } else {
            small = nb; smallId = rb; big = na; bigId = ra;
            big.rank++;
        }
        // Record event for undo.
        trail.add(new Event(Op.UNION, smallId, bigId, small.rank, small.classSize));
        // Set proof edge (small -> big) with reason.
        small.proofParent = bigId;
        small.proofReason = reason;
        // union-find link
        small.parent = bigId;
        big.classSize += small.classSize;
        // splice circular class lists
        int tmpNext = big.next;
        big.next = small.next;
        small.next = tmpNext;

        // Check disequalities for new conflict: any (x,y) with rep(x)==rep(y)?
        for (int[] dq : diseqs) {
            if (rep(dq[0]) == rep(dq[1])) {
                int[] eqExpl = explainEq(dq[0], dq[1]);
                int[] out = new int[eqExpl.length + 1];
                System.arraycopy(eqExpl, 0, out, 0, eqExpl.length);
                out[eqExpl.length] = -dq[2];
                int[] conflict = new int[out.length];
                for (int i = 0; i < out.length; i++) conflict[i] = -out[i];
                lastConflict = conflict;
                return false;
            }
        }

        // Re-signature parent applications of the small class — congruence closure.
        // Walk all members of small's class via the now-merged circular list starting from smallId.
        int start = smallId;
        int cur = start;
        do {
            List<Integer> ps = parents.get(cur);
            if (ps != null) {
                for (Integer pId : ps) {
                    String oldKey = signatureFromCurrent(pId); // recomputes with current reps
                    Integer collide = sigTable.get(oldKey);
                    if (collide == null) {
                        sigTable.put(oldKey, pId);
                        trail.add(new Event(Op.SIG_INSERT, pId, 0, 0, 0));
                    } else if (collide != pId && rep(collide) != rep(pId)) {
                        if (!doUnion(pId, collide, 0)) return false;
                    }
                }
            }
            cur = nodes.get(cur).next;
        } while (cur != start);

        return true;
    }

    private String signature(int nodeId) {
        return signatureFromCurrent(nodeId);
    }

    private String signatureFromCurrent(int nodeId) {
        Node n = nodes.get(nodeId);
        Term t = tf.termById(n.termId);
        if (!(t instanceof Term.App app)) return "atom:" + n.termId;
        StringBuilder sb = new StringBuilder(app.symbol).append('|');
        for (Term c : app.args) {
            sb.append(rep(termIdToNode.get(c.id))).append(',');
        }
        return sb.toString();
    }

    /** Build an explanation: literals whose conjunction implies a == b (via union-find proof tree). */
    private int[] explainEq(int a, int b) {
        // Find nearest common ancestor in proof forest, collect reasons.
        // Phase 1: mark all proof ancestors of a.
        java.util.Set<Integer> aChain = new java.util.LinkedHashSet<>();
        int x = a;
        while (x != -1) { aChain.add(x); int p = nodes.get(x).proofParent; if (p == -1) break; x = p; }
        // Phase 2: walk from b until we hit the chain.
        java.util.List<Integer> reasons = new ArrayList<>();
        int y = b;
        java.util.List<Integer> bPath = new ArrayList<>();
        while (y != -1 && !aChain.contains(y)) {
            bPath.add(y);
            int reason = nodes.get(y).proofReason;
            if (reason != 0) reasons.add(reason);
            int p = nodes.get(y).proofParent;
            if (p == -1) break;
            y = p;
        }
        int meet = y;
        // Walk from a to meet, collecting reasons.
        for (int z = a; z != meet; ) {
            int reason = nodes.get(z).proofReason;
            if (reason != 0) reasons.add(reason);
            int p = nodes.get(z).proofParent;
            if (p == -1) break;
            z = p;
        }
        int[] out = new int[reasons.size()];
        for (int i = 0; i < out.length; i++) out[i] = reasons.get(i);
        return out;
    }

    private static boolean isInterpreted(String sym) {
        return switch (sym) {
            case "and","or","not","=>","=","ite","distinct","xor",
                 "+","-","*","<=","<",">=",">","div","mod","abs",
                 "select","store" -> true;
            default -> false;
        };
    }

    private static String decodeKey(int a, int b, int c, int d) { return a+":"+b+":"+c+":"+d; }
}
