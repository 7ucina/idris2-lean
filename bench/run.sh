#!/usr/bin/env bash
# Run the benchmarks: best-of-3 wall time and peak RSS, checking every
# output against the Lean 4 version.  usage: bench/run.sh [lean4 lean chez refc]
HERE="$(cd "$(dirname "$0")" && pwd)"
cd "$HERE"
BACKENDS=${@:-lean4 lean chez refc}
OUT=$(mktemp)
printf "%-12s" bench; for be in $BACKENDS; do printf "| %-20s" $be; done; echo
for b in NFib BinaryTrees RBMap Deriv NQueens ListPipe; do
  ref=$(lean/out/$b 2>&1 | tail -1)
  printf "%-12s" $b
  for be in $BACKENDS; do
    if [ $be = lean4 ]; then exe=lean/out/$b; else exe=idris/build/exec/${b}_$be; fi
    if [ ! -x $exe ]; then printf "| %-20s" n/a; continue; fi
    best=999; mem=0; ok=1
    for i in 1 2 3; do
      r=$( { /usr/bin/time -f "%e %M" timeout 300 $exe > $OUT; } 2>&1 | tail -1)
      t=${r% *}; m=${r#* }
      [ "$(tail -1 $OUT)" = "$ref" ] || ok=0
      best=$(echo "if ($t < $best) $t else $best" | bc); mem=$m
    done
    s="${best}s $((mem/1024))MB"; [ $ok = 1 ] || s="$s WRONG"
    printf "| %-20s" "$s"
  done
  echo
done
rm -f $OUT
