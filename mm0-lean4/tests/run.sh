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

[ "$1" = fuzz ] || exit 0
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
"$bin/mm0-fuzz" --iters "${2:-300}" --seed "${FUZZ_SEED:-1}" --out "$work/out" \
  --rs "$rs" --c "$c" $seeds
