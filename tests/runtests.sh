#!/usr/bin/env bash
# Run tests from the Idris2 repository's test suite with this backend.
# usage: IDRIS2_TESTS=/path/to/Idris2/tests tests/runtests.sh chez/chez015 refc/strings ...
# Failing tests' outputs are saved to tests/results/.
HERE="$(cd "$(dirname "$0")" && pwd)"
T="${IDRIS2_TESTS:-$HOME/idris2-fast/Idris2/tests}"
W="$HERE/idris2-lean-wrap"
OUT="$HERE/results"
mkdir -p "$OUT"
one() {
  t=$1; name=$(echo $t | tr / _)
  d=$(mktemp -d)
  mkdir -p $d/x/y; cp -r $T/$t/. $d/x/y/; cp $T/testutils.sh $d/
  (cd $d/x/y && IDRIS2_CG=lean timeout 300 sh ./run $W > output 2>&1)
  if diff -q $d/x/y/expected $d/x/y/output >/dev/null 2>&1; then echo "PASS $t"
  else echo "FAIL $t"; cp $d/x/y/output $OUT/$name.output; cp $d/x/y/expected $OUT/$name.expected 2>/dev/null; fi
  rm -rf $d
}
export -f one; export T W OUT
printf "%s\n" "$@" | xargs -P "${JOBS:-8}" -I{} bash -c 'one {}'
