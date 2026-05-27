#!/usr/bin/env bash
# Build a full method-by-method comparison of Daikon invariants vs JML-Inferrer
# clauses over the same 11 Commons Lang classes.
set -e
cd "$(dirname "$0")"
DK=out/daikon-clean.txt
SRC=../results/annotated-source
OUT=out/ALL_EXAMPLES.md

# ---- 1. Daikon: key = simpleClass.method/arity ; emit key<TAB>kind<TAB>inv ----
awk '
  function simpleclass(fqcnMethod,   p, cls) {
    # fqcnMethod like org.apache.commons.lang3.mutable.MutableInt.add
    p = fqcnMethod
    sub(/\.[A-Za-z0-9_]+$/, "", p)          # strip .method -> class fqcn
    cls = p; sub(/.*\./, "", cls)           # simple class name
    return cls
  }
  /:::/ {
    line=$0
    idx=index(line,":::")
    head=substr(line,1,idx-1)               # ...Class.method(params)
    rest=substr(line,idx+3); sub(/[0-9].*/,"",rest); sub(/;.*/,"",rest); curkind=rest
    # only method entry/exit points; skip CLASS / OBJECT ppts
    if (curkind!="ENTER" && curkind!="EXIT") { curkey=""; next }
    pidx=index(head,"(")
    if (pidx==0) { curkey=""; next }
    name=substr(head,1,pidx-1)              # ...Class.method
    params=substr(head,pidx+1); sub(/\)$/,"",params)
    method=name; sub(/.*\./,"",method)      # simple method
    cls=simpleclass(name)
    arity=0
    if (params!="") { arity=1; for(i=1;i<=length(params);i++) if(substr(params,i,1)==",") arity++ }
    curkey=cls "." method "/" arity
    next
  }
  /^=====/ { next }
  {
    inv=$0
    if (inv=="") next
    if (curkey=="") next
    if (index(inv,"getClass().getName()")>0) next
    if (index(inv," == orig(")>0) next
    if (index(inv,"has only one value")>0) next
    print curkey "\t" curkind "\t" inv
  }
' "$DK" | sort -u > out/daikon_inv.tsv

# ---- 2. JML-Inferrer: scan annotated .java -> key<TAB>clause ----
: > out/jml_clauses.tsv
for f in $(find "$SRC" -name '*.java'); do
  cls=$(basename "$f" .java)
  awk -v cls="$cls" '
    function flush(decl,   nm, pidx, params, arity, i, c) {
      if (npend==0) return
      pidx=index(decl,"(")
      if(pidx==0){ npend=0; return }
      # method name = last identifier before (
      head=substr(decl,1,pidx-1)
      nm=head; sub(/.*[ \t*]/,"",nm)
      params=substr(decl,pidx+1); sub(/\).*/,"",params)
      gsub(/^[ \t]+|[ \t]+$/,"",params)
      arity=0
      if(params!=""){arity=1; for(i=1;i<=length(params);i++) if(substr(params,i,1)==",") arity++ }
      for(i=0;i<npend;i++) print cls "." nm "/" arity "\t" pend[i]
      npend=0
    }
    /@com\.jml\.inferrer\.annotations\.(Requires|Ensures|Signals|Assignable|LoopInvariant|Invariant)\(/ {
      c=$0; sub(/.*annotations\./,"",c); sub(/^[ \t]+/,"",c)
      pend[npend++]=c; next
    }
    /@com\.jml\.inferrer\.annotations\./ { next }   # other metadata annotations: ignore
    # a declaration line with a (   ) and { or ;
    /\(.*\)[ \t]*(\{|;|throws)/ {
      if(npend>0) flush($0)
      next
    }
    { if($0 !~ /@/ && npend>0 && $0 !~ /[A-Za-z]/) {} }  # noop
  ' "$f" >> out/jml_clauses.tsv
done

# ---- 3. join + emit markdown ----
{
echo "# Daikon vs JML-Inferrer — all observed methods"
echo
echo "Daikon 5.8.24 (dynamic, hand-written workload) vs JML-Inferrer (static)."
echo "Daikon invariants filtered to drop unchanged-field \`== orig()\` equalities,"
echo "\`getClass().getName()\` noise, and constant-only class fields. Methods are"
echo "those Daikon's workload exercised; JML-Inferrer clauses are from its"
echo "annotated source. Matching is by simple-class + method + arity (overloads"
echo "may occasionally mis-pair)."
echo
cut -f1 out/daikon_inv.tsv | sort -u | while read key; do
  echo "## \`$key\`"
  echo
  src=$(awk -v k="@@@KEY@@@ $key" '$0==k{p=1;next} /^@@@KEY@@@/{p=0} p' out/method_sources.txt)
  if [ -n "$src" ]; then
    echo "**Source:**"
    echo '```java'
    echo "$src"
    echo '```'
    echo
  fi
  echo "**Daikon:**"
  awk -F'\t' -v k="$key" '$1==k{printf "  - [%s] %s\n",$2,$3}' out/daikon_inv.tsv
  jml=$(awk -F'\t' -v k="$key" '$1==k{print "  - "$2}' out/jml_clauses.tsv | sort -u)
  echo
  echo "**JML-Inferrer:**"
  if [ -z "$jml" ]; then echo "  - (no matching clause found)"; else echo "$jml"; fi
  echo
done
} > "$OUT"

echo "wrote $OUT"
wc -l "$OUT"
echo "daikon methods: $(cut -f1 out/daikon_inv.tsv | sort -u | wc -l)"
echo "jml clause rows: $(wc -l < out/jml_clauses.tsv)"
