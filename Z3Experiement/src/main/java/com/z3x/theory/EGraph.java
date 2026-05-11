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
    private enum Op { UNION, SIG_INSERT_LONG, SIG_INSERT_KEY, EQ_ASSERT, DISEQ_ASSERT }

    private static final class Event {
        final Op op;
        final int a, b, c, d;
        final long key;
        final SigKey sk;
        Event(Op op, int a, int b, int c, int d) {
            this.op = op; this.a = a; this.b = b; this.c = c; this.d = d;
            this.key = 0; this.sk = null;
        }
        Event(Op op, long key) { this.op = op; this.a = 0; this.b = 0; this.c = 0; this.d = 0; this.key = key; this.sk = null; }
        Event(Op op, SigKey sk) { this.op = op; this.a = 0; this.b = 0; this.c = 0; this.d = 0; this.key = 0; this.sk = sk; }
    }

    private final TermFactory tf;
    private final Map<Integer, Integer> termIdToNode = new HashMap<>();
    private final List<Node> nodes = new ArrayList<>();

    /** parent edges (term-id -> list of parent application node ids). */
    private final Map<Integer, List<Integer>> parents = new HashMap<>();

    /** signature -> node id (canonical). Signature key is a packed long for the common
     *  unary/binary cases (no String allocation per re-signature), fallback to SigKey for
     *  higher arity. The Long path is the hot path on JML-shape workloads where most apps
     *  are 1-2 args (select, p(...), f(...)).
     */
    private final Map<Long, Integer> sigTableLong = new HashMap<>();
    private final Map<SigKey, Integer> sigTableKey = new HashMap<>();
    /** Interned symbol ids (so we can pack into 32 bits along with reps). */
    private final Map<String, Integer> symbolId = new HashMap<>();
    private int nextSymbolId = 1;

    private int symId(String sym) {
        Integer id = symbolId.get(sym);
        if (id != null) return id;
        id = nextSymbolId++;
        symbolId.put(sym, id);
        return id;
    }

    /** Packed signature key for high-arity applications. */
    private record SigKey(int symbolId, int[] reps) {
        @Override public boolean equals(Object o) {
            return o instanceof SigKey sk && sk.symbolId == symbolId && java.util.Arrays.equals(sk.reps, reps);
        }
        @Override public int hashCode() { return symbolId * 1315423911 ^ java.util.Arrays.hashCode(reps); }
    }

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
                case SIG_INSERT_LONG -> sigTableLong.remove(e.key);
                case SIG_INSERT_KEY -> sigTableKey.remove(e.sk);
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
            insertSig(id);
        }
        return id;
    }

    private void insertSig(int nodeId) {
        SigResult sig = signatureOf(nodeId);
        Integer existing;
        if (sig.key == null) {
            existing = sigTableLong.get(sig.longVal);
            if (existing != null) {
                sigTableLong.put(sig.longVal, nodeId);
                trail.add(new Event(Op.SIG_INSERT_LONG, sig.longVal));
                doUnion(nodeId, existing, 0);
            } else {
                sigTableLong.put(sig.longVal, nodeId);
                trail.add(new Event(Op.SIG_INSERT_LONG, sig.longVal));
            }
        } else {
            existing = sigTableKey.get(sig.key);
            if (existing != null) {
                sigTableKey.put(sig.key, nodeId);
                trail.add(new Event(Op.SIG_INSERT_KEY, sig.key));
                doUnion(nodeId, existing, 0);
            } else {
                sigTableKey.put(sig.key, nodeId);
                trail.add(new Event(Op.SIG_INSERT_KEY, sig.key));
            }
        }
    }

    /** Return the Term whose node is the given rep id. */
    public Term termOfRep(int repNodeId) {
        // Walk the class via the circular next-list and pick the most-constant-looking term.
        int start = repNodeId;
        int cur = start;
        Term best = tf.termById(nodes.get(cur).termId);
        do {
            Term t = tf.termById(nodes.get(cur).termId);
            if (t instanceof Term.IntConst || t instanceof Term.BoolConst || t instanceof Term.RatConst) {
                return t;
            }
            cur = nodes.get(cur).next;
        } while (cur != start);
        return best;
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
                    SigResult sig = signatureOf(pId);
                    Integer collide;
                    if (sig.key == null) {
                        collide = sigTableLong.get(sig.longVal);
                        if (collide == null) {
                            sigTableLong.put(sig.longVal, pId);
                            trail.add(new Event(Op.SIG_INSERT_LONG, sig.longVal));
                        } else if (collide != pId && rep(collide) != rep(pId)) {
                            if (!doUnion(pId, collide, 0)) return false;
                        }
                    } else {
                        collide = sigTableKey.get(sig.key);
                        if (collide == null) {
                            sigTableKey.put(sig.key, pId);
                            trail.add(new Event(Op.SIG_INSERT_KEY, sig.key));
                        } else if (collide != pId && rep(collide) != rep(pId)) {
                            if (!doUnion(pId, collide, 0)) return false;
                        }
                    }
                }
            }
            cur = nodes.get(cur).next;
        } while (cur != start);

        return true;
    }

    /** Compute the signature as either a packed long (lookup in sigTableLong) or a SigKey
     *  (lookup in sigTableKey). Returns:
     *    - longVal: the packed long, or Long.MIN_VALUE if not encodable as long.
     *    - key: the SigKey for non-long-encodable cases.
     */
    private static final class SigResult { long longVal; SigKey key; }
    private final SigResult sigBuf = new SigResult();

    private SigResult signatureOf(int nodeId) {
        Node n = nodes.get(nodeId);
        Term t = tf.termById(n.termId);
        sigBuf.longVal = Long.MIN_VALUE;
        sigBuf.key = null;
        if (!(t instanceof Term.App app)) {
            sigBuf.longVal = 1L; // sentinel — atoms never collide in sigTable.
            return sigBuf;
        }
        int sym = symId(app.symbol);
        int arity = app.args.size();
        if (arity == 0) {
            // (sym << 32) | 0
            sigBuf.longVal = ((long) sym) << 32;
            return sigBuf;
        }
        if (arity == 1) {
            int r0 = rep(termIdToNode.get(app.args.get(0).id));
            sigBuf.longVal = (((long) sym) << 32) | (r0 & 0xFFFFFFFFL);
            return sigBuf;
        }
        if (arity == 2) {
            int r0 = rep(termIdToNode.get(app.args.get(0).id));
            int r1 = rep(termIdToNode.get(app.args.get(1).id));
            // Three 21-bit slots: sym (top 22 bits incl sign), r0 (mid 21), r1 (low 21).
            // For symbols and node counts < 2M this is collision-free.
            if (sym < (1 << 21) && r0 < (1 << 21) && r1 < (1 << 21)) {
                sigBuf.longVal = (((long) sym) << 42) | (((long) r0) << 21) | r1;
                return sigBuf;
            }
            // Fall through to key.
        }
        int[] reps = new int[arity];
        for (int i = 0; i < arity; i++) reps[i] = rep(termIdToNode.get(app.args.get(i).id));
        sigBuf.key = new SigKey(sym, reps);
        return sigBuf;
    }

    /** Public: explain why two terms are currently in the same class. */
    public int[] explainEqTerms(Term a, Term b) {
        Integer na = termIdToNode.get(a.id);
        Integer nb = termIdToNode.get(b.id);
        if (na == null || nb == null) return new int[0];
        if (rep(na) != rep(nb)) return new int[0];
        return explainEq(na, nb);
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

}
