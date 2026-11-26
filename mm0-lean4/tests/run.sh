#!/bin/sh
# Regression tests for the Lean .mm0 parser. Run from anywhere.
#
#   tests/run.sh             fixed verdicts (tests/expected.txt)
#   tests/run.sh fuzz [N]    also N fuzzed mutants per seed run (default 300)
#                            against mm0-rs and mm0-c
#
# The fuzz step needs MM0_RS and MM0_C (paths to the mm0-rs and mm0-c
# binaries), or mm0-rs / mm0-c on PATH.
set -e
mode=$1; count=$2
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
cd "$here" && lake build mm0-lean mm0-fuzz >/dev/null
bin="$here/.lake/build/bin"
cd "$root"
fail=0
grep -v '^#' "$here/tests/expected.txt" | while read -r want file rest; do
  [ -z "$file" ] && continue
  if "$bin/mm0-lean" check "$file" >/dev/null 2>&1; then got=accept; else got=reject; fi
  if [ "$got" != "$want" ]; then echo "FAIL $file: expected $want, got $got"; echo x >> /tmp/mm0-lean-fail.$$; fi
done
if [ -f /tmp/mm0-lean-fail.$$ ]; then rm -f /tmp/mm0-lean-fail.$$; echo "fixed verdicts: FAILED"; exit 1; fi
echo "fixed verdicts: ok"

# Generated Lean environments must match what the parser produces today.
gen_ok=1
for pair in "examples/set.mm0 setEnv mm0-lean4/MM0Examples/SetEnv.lean"; do
  set -- $pair
  if ! "$bin/mm0-lean" lean "$1" "$2" | cmp -s - "$3"; then
    echo "FAIL $3 is out of date: regenerate with mm0-lean lean $1 $2 > $3"; gen_ok=0
  fi
done
[ $gen_ok = 1 ] || exit 1
echo "generated environments: ok"

[ "$mode" = fuzz ] || exit 0
rs=${MM0_RS:-mm0-rs}; c=${MM0_C:-mm0-c}
work=$(mktemp -d)
seeds=""
for b in peano hol set; do
  "$rs" compile "examples/$b.mm1" "$work/$b.mmb" >/dev/null
  seeds="$seeds examples/$b.mm0=$work/$b.mmb"
done
for m in tests/mm0_mmu/pass/*.mm0; do
  n=$(basename "${m%.mm0}")
  "$rs" compile "${m%.mm0}.mmu" "$work/t-$n.mmb" >/dev/null
  seeds="$seeds $m=$work/t-$n.mmb"
done
"$bin/mm0-fuzz" --iters "${count:-300}" --seed "${FUZZ_SEED:-1}" --out "$work/out" \
  --rs "$rs" --c "$c" $seeds
