# AGENTS.md

Guidance for coding agents working in this repository. `CLAUDE.md` has the same content.

The proof of `PAL ∈ PEG` and the palindrome PEG generator moved to the separate repository
[kmizu/pal-peg](https://github.com/kmizu/pal-peg) (local checkout: `~/repo/pal-peg`). This
repository keeps Shallot and Lens.

## What is here

| Directory | Contents | Toolchain |
|---|---|---|
| `lean/` | **Shallot** (a PEG framework and a first-order functional language: specification, implementation and proofs) and **Lens** (a Lean 4 → Scala 3 extractor) | Lean v4.32.0, no external dependencies (no Mathlib) |
| `scala/` | Lens output (`generated/`, committed), the hand-written runtime, the CLI, and the differential harness drivers | Scala 3.7.4, sbt 1.11 |
| `corpus/` | Differential test cases and goldens | — |
| `docs/` | GitHub Pages site (served from `main:/docs`) | — |

## Commands

```sh
make verify        # audit → lean build → lake test → drift → sbt test → differential harnesses
make verify-fast   # audit + lake build only
make lean          # cd lean && lake build (all proofs + the axiom audit lean/Audit.lean)
make lake-test     # Lens golden tests (lean/tests/golden/Shallot.scala)
make regen         # regenerate scala/generated with Lens (committed; review the diff)
make check-drift   # committed scala/generated == fresh extraction
make scala         # cd scala && sbt -batch test
make corpus-golden # regenerate the goldens (deliberate; review with git diff)
```

Lens golden update: `cd lean && LENS_UPDATE_GOLDEN=1 lake test`, then review the diff.
`lake` may need `. ~/.elan/env` first. In WSL2, sbt sometimes fails on `/run/user/1000`; use
`XDG_RUNTIME_DIR=/tmp/xdg-1000 sbt ...` (after `mkdir -p /tmp/xdg-1000`).

## Rules

- `Shallot.lean` is the root import; a new module must be added there.
- No `sorry`, `admit`, `native_decide`, or extra `axiom`. `scripts/audit-source.sh` checks the
  sources, and the `#guard_msgs in #print axioms` blocks of `lean/Audit.lean` check the axioms. Add
  a guard there for every new flagship theorem.
- Code extracted by Lens must stay in the frozen subset of `docs/extractable-subset.md` (no
  `partial def`/`unsafe`/`opaque`, no indexed inductives, no Prop-carrying constructors, no `do`
  notation, only whitelisted type classes).
- `scala/generated` is committed. After changing the Lean side, run `make regen`, review the diff,
  and commit it.
- Scala 3 code uses brace syntax, not indentation syntax. Hand-written Scala compiles with
  `-Werror -Wunused:all`.
- Trusted base: the Lean kernel, Lens, the runtime `scala/runtime` (`shallot.rt`), the Scala
  compiler and the JVM.
