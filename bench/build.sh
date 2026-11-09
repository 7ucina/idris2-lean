#!/usr/bin/env bash
# Build the benchmarks.  usage: bench/build.sh [lean4] [lean] [chez] [refc]
#   lean4 : the Lean 4 versions (needs LEAN_HOME)
#   lean  : the Idris versions with this backend
#   chez/refc : the Idris versions with the stock Idris2 backends
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
IL="${IDRIS2_LEAN:-$HERE/../build/exec/idris2-lean}"
LEAN_HOME="${LEAN_HOME:-$HOME/idris2-fast/lean/lean-4.35.0-linux}"
BACKENDS=${@:-lean4 lean chez refc}
for be in $BACKENDS; do
  if [ "$be" = lean4 ]; then
    mkdir -p "$HERE/lean/out"
    for f in "$HERE"/lean/*.lean; do
      b=$(basename "$f" .lean)
      "$LEAN_HOME/bin/lean" -c "$HERE/lean/out/$b.c" "$f" &&
        "$LEAN_HOME/bin/leanc" -O3 -DNDEBUG "$HERE/lean/out/$b.c" -o "$HERE/lean/out/$b" || echo "FAIL lean4 $b"
    done
    continue
  fi
  cd "$HERE/idris"
  for f in *.idr; do
    b=${f%.idr}
    case $be in
      lean) "$IL" --cg lean "$f" -o "${b}_lean" >/dev/null || echo "FAIL lean $b";;
      chez|refc) idris2 --cg $be "$f" -o "${b}_$be" >/dev/null || echo "FAIL $be $b";;
    esac
  done
done
