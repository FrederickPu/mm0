#!/bin/sh
# Regression tests for mm0-lean4. Run from anywhere.
#
#   tests/run.sh             fixed verdicts (tests/expected.txt), generated
#                            files up to date, checked-in .mmb files verified
#   tests/run.sh fuzz [N]    also: .mmb files built by mm0-rs verified by the
#                            Lean checker, and N fuzzed mutants (default 300)
#                            against mm0-rs and mm0-c
#
# The fuzz step needs MM0_RS and MM0_C (paths to the mm0-rs and mm0-c
# binaries), or mm0-rs / mm0-c on PATH.
#
# MM0_LEAN_INTERP=1 runs mm0-lean through Lean's interpreter instead of the
# built executable, for machines whose policy blocks freshly built binaries.
# (mm0-fuzz is always the built executable.)
set -e
mode=$1; count=$2
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
cd "$here" && lake build >/dev/null
bin="$here/.lake/build/bin"
cd "$root"
mm0lean() {
  if [ -n "$MM0_LEAN_INTERP" ]; then lake --dir "$here" env lean --run "$here/Main.lean" "$@"
  else "$bin/mm0-lean" "$@"; fi
}
grep -v '^#' "$here/tests/expected.txt" | while read -r want file rest; do
  [ -z "$file" ] && continue
  if mm0lean check "$file" >/dev/null 2>&1; then got=accept; else got=reject; fi
  if [ "$got" != "$want" ]; then echo "FAIL $file: expected $want, got $got"; echo x >> /tmp/mm0-lean-fail.$$; fi
done
if [ -f /tmp/mm0-lean-fail.$$ ]; then rm -f /tmp/mm0-lean-fail.$$; echo "fixed verdicts: FAILED"; exit 1; fi
echo "fixed verdicts: ok"

# Generated Lean files must match what the parser and the .mmb reader produce
# today.
gen_ok=1
if ! mm0lean lean examples/set.mm0 setEnv | cmp -s - mm0-lean4/MM0Examples/SetEnv.lean; then
  echo "FAIL MM0Examples/SetEnv.lean is out of date: regenerate with"
  echo "  mm0-lean lean examples/set.mm0 setEnv > mm0-lean4/MM0Examples/SetEnv.lean"
  gen_ok=0
fi
if ! mm0lean leanproof examples/set.mm0 mm0-lean4/tests/mmb/set.mmb setEnv MM0Examples.SetEnv setProved |
    cmp -s - mm0-lean4/MM0Examples/SetProof.lean; then
  echo "FAIL MM0Examples/SetProof.lean is out of date: regenerate with"
  echo "  mm0-lean leanproof examples/set.mm0 mm0-lean4/tests/mmb/set.mmb setEnv MM0Examples.SetEnv setProved > mm0-lean4/MM0Examples/SetProof.lean"
  gen_ok=0
fi
# T, the theory of the con-leche sanity check (mm0-sanity/T)
tmm0=$(mktemp)
{ sed -n '1,6p' mm0-sanity/T/lean.mm0; mm0lean genmm0 examples/lean.mm1 mm0-sanity/T/lean.mmb; } > "$tmm0"
if ! cmp -s "$tmm0" mm0-sanity/T/lean.mm0; then
  echo "FAIL mm0-sanity/T/lean.mm0 is out of date: regenerate with mm0-lean genmm0 (see its header)"
  gen_ok=0
fi
if ! mm0lean lean mm0-sanity/T/lean.mm0 T | cmp -s - mm0-sanity/MM0Sanity/T.lean; then
  echo "FAIL mm0-sanity/MM0Sanity/T.lean is out of date: regenerate with"
  echo "  mm0-lean lean mm0-sanity/T/lean.mm0 T > mm0-sanity/MM0Sanity/T.lean"
  gen_ok=0
fi
[ $gen_ok = 1 ] || exit 1
echo "generated files: ok"

mm0lean verify examples/set.mm0 mm0-lean4/tests/mmb/set.mmb
mm0lean verify mm0-sanity/T/lean.mm0 mm0-sanity/T/lean.mmb

[ "$mode" = fuzz ] || exit 0
rs=${MM0_RS:-mm0-rs}; c=${MM0_C:-mm0-c}
work=$(mktemp -d)
seeds=""
for b in peano hol set; do
  "$rs" compile "examples/$b.mm1" "$work/$b.mmb" >/dev/null
  mm0lean verify "examples/$b.mm0" "$work/$b.mmb"
  seeds="$seeds examples/$b.mm0=$work/$b.mmb"
done
for m in tests/mm0_mmu/pass/*.mm0; do
  n=$(basename "${m%.mm0}")
  "$rs" compile "${m%.mm0}.mmu" "$work/t-$n.mmb" >/dev/null
  mm0lean verify "$m" "$work/t-$n.mmb"
  seeds="$seeds $m=$work/t-$n.mmb"
done
"$bin/mm0-fuzz" --iters "${count:-300}" --seed "${FUZZ_SEED:-1}" --out "$work/out" \
  --rs "$rs" --c "$c" $seeds
