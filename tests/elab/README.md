**Elaboration tests for `.mm0` files**

These cover the checks that come after lexing: well-formed declarations,
definitions, notations and coercions. `mm0_mmu/` is mostly about lexing. Most
of these cases were found by the differential fuzzer in `mm0-lean4/Fuzz.lean`
and then cut down to a few lines. Each file starts with a comment saying
which rule it tests.

The groups are named for the combination of verdicts they assert, like the
`mmb/` groups. "Spec" means `mm0.md` (and `mm0-c` where it has an opinion).
`mm0-lean` is the Lean parser in `mm0-lean4/`, which follows the spec.

| group      | spec / mm0-lean | mm0-rs  |
| ---------- | --------------- | ------- |
| `pass/`    | accepts         | accepts |
| `fail/`    | rejects         | rejects |
| `fail-rs/` | rejects         | **accepts** |
| `pass-rs/` | accepts         | **rejects** |

The `-rs` groups record where mm0-rs currently differs from the spec. Most of
them look like mm0-rs bugs: duplicate sorts, leading zeros, mixed
associativity, unchecked notation binders, and inferred variables. When mm0-rs
is fixed, move the file to `fail/` or `pass/`.

Related: `mm0_mmu/fail/bad-int5.mm0` ("forbidden 0 prefix") fails only because
the term `p` is never declared, so it does not test the leading-zero rule.
`fail-rs/leading-zero.mm0` does.

    ./run-mm0-rs.sh GROUP/TEST
    ./run-mm0-lean.sh GROUP/TEST     # needs mm0-lean on PATH
