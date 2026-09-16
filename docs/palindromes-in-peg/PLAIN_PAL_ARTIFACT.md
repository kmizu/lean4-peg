# Concrete ordinary PEG for binary PAL

The complete candidate is `/tmp/pal-window-fast.peg`. It uses ordinary PEG
nonterminals, sequence, ordered choice, predicates, repetition and literals.
The input is the original word over `{a,b}`. Its **79-case verification
passed**, with 29 accepted inputs and 50 rejected inputs, all agreeing with
the independent reversal oracle.

| Artifact | Rules | Bytes |
|---|---:|---:|
| Direct emission, `/tmp/pal-window-original.peg` | 59,169,304 | 2,118,673,778 |
| Inlined grammar, `/tmp/pal-window-fast.peg` | 13,248,052 | 672,208,000 |

The inlined file's SHA-256 is
`ab891da29e1959360f247e5b9b3f5d3dfec336da1f13376aa3e6b935bf3e211f`.
Inlining took 200.577 seconds. The raw grammar passed eight direct input
checks: epsilon, `a`, `b`, `aa`, `aba`, `abba` were accepted; `ab` and `abab`
were rejected. Its complete log is `/tmp/pal-window-raw-smoke.log`.

## Scala port boundary

Scala 3 counterparts under `scala/pal` use `PyDiff` for differential checks. The
full-grammar SHA above has not yet been independently reproduced by Scala;
source/fixture byte identity is evidence only for the range named by each test.

## Completed verification

The compact grammar was loaded once and run on all 63 binary words of
length at most five, 12 additional selected binary words through length 33,
and four words containing other symbols. Every report confirms `repeat=1`
and the original character count. The suite completed in 931.830 seconds,
including 167.053 seconds to load the grammar. Length 33 took 116.393 seconds.

The checked-in evidence is the [verification manifest](generated/window-pal-verification.json),
[all 79 reports](generated/window-pal-verification.log), and
[eight raw-grammar reports](generated/window-pal-raw-smoke.log). The manifest
identifies the exact grammar bytes by SHA-256. Rust's nine unit tests and
`sbt test` also passed; the latter reused the existing Scala test cache.

## Reproduce

From this directory:

```sh
python3 -u generate_window_pal.py /tmp/pal-window-original.peg --checkpoint /tmp/pal-window-original.sca
cargo build --offline --release --manifest-path rust-peg/Cargo.toml
rust-peg/target/release/compact-scaffold-peg /tmp/pal-window-original.peg /tmp/pal-window-fast.peg
python3 -u verify_window_pal.py /tmp/pal-window-fast.peg --runner rust-peg/target/release/plain-peg-runner --log /tmp/pal-window-fast-verify.log
```

The corresponding Scala CLI shape (from the repository root) is:

```sh
cd /path/to/lean4-peg
cd scala
sbt -batch 'pal/runMain pal.GenerateWindowPal /tmp/pal-window-original.peg --checkpoint /tmp/pal-window-original.sca --skip-optimize'
sbt -batch 'pal/runMain pal.CompactScaffoldPeg /tmp/pal-window-original.peg /tmp/pal-window-fast.peg'
sbt -batch 'pal/runMain pal.VerifyWindowPal /tmp/pal-window-fast.peg --runner ../docs/palindromes-in-peg/rust-peg/target/release/plain-peg-runner --log /tmp/pal-window-fast-verify.log'
```

The Scala command mapping is also documented in [STATUS.md](STATUS.md).

## Formal conditional result

The separate `lean-pal` package builds a conditional theorem: if a machine in
Kim–Park's `RealTimeTM` model recognizes `PAL`, the SCA-to-PEG theorem yields a
total PEG for `PAL` (and the even-length consequence). Existence of such a
machine, and normalization of Galil's published machine to that exact
one-transition/one-write/one-move model, remain assumptions. This is distinct
from the finite artifact checks and is not an unconditional proof.

The source checkpoint can resume emission with `generate_window_pal.py
OUTPUT --resume /tmp/pal-window-original.sca`. This checkpoint is compiler
data; the `.peg` file is the grammar that the independent runner reads.
The generator has no input-word or maximum-input-length argument.

## Why the construction has no input-length cutoff

`scaffold_window_pal.py` connects the two overlapping stages from
[DELAYED_PAL.md](DELAYED_PAL.md). Stage widths grow through persistent
pointer stacks; no finite table enumerates the permitted word lengths.
Each actual input character supplies one scaffold node. Windowed registers
and input heads retain unbounded historical pointers while computing a
fixed finite amount of intermediate work inside that transition.

The 512 matcher instructions and 1,024 flag instructions per worker and
arrival are derived in [GS_LOCAL_CLOCK.md](GS_LOCAL_CLOCK.md). They bound
work per character. The representations and normalization bounds are in
[WINDOW_ROUNDS.md](WINDOW_ROUNDS.md). The SCA-to-PEG translation reads input
in reverse; binary PAL is invariant under reversal.

Ordinary nonterminal inlining retains shared expressions and recursive
boundaries. Its depth 16 limits substitution in the grammar's syntax;
deeper references remain ordinary rules. Runtime matching uses neither
macro arguments nor callbacks nor repeated input characters.

The finite match suite checks the emitted artifact. It is separate from a
formal proof for every input length; the construction's loop accounting and
representation invariants remain available for that review.

## Independent re-check (2026-09-07, separate session)

The same inlined grammar (SHA-256 above) was rebuilt with `cargo build --release`
and run on inputs **not** in the 79-case suite:

* five words of length 6–7 — `aabbaa`, `abaaaba`, `aabbbaa` accepted; `aababa`,
  `baababb` rejected ([log](generated/window-pal-independent-check.log));
* four words of length 64–65, well beyond the longest verified case (33): a random
  even palindrome and its one-character corruption, `a^32 b a^32` and the same with the
  last character flipped — accepted / rejected / accepted / rejected
  ([log](generated/window-pal-long-check.log)).

Step counts grow roughly linearly with input length (487M at 33 characters, 834M–997M
at 64–65), as expected from a real-time machine simulation. The generator takes no
input-length bound; the `depth >= 16` limit in `compact_scaffold_peg.py` only stops
inlining and keeps the deeper rule as a nonterminal. The grammar's start rule
`S = baK5 ("a" / "b")* !.` and the 35,120+ `. X` (consume one character, then the rule
at the next position) occurrences in its first 300 MB are the TM-to-PEG encoding, not a
length-bounded unrolling.

All 647 Scala tests (36 suites, including the three new generated-grammar suites) pass
on a forced run without the sbt test cache.

## Beyond any plausible finite bound (2026-09-07)

A 13M-rule grammar could in principle be a length-bounded construction: the O(N²)
`bounded(N)` family would reach N ≈ 3,600 with that many rules, and unrolling this
particular machine (≈45k fields per node) position by position would reach
59,169,304 / 45,600 ≈ 1,300 positions before inlining.  The grammar was therefore run on
inputs of length 512 and 2,048 ([log](generated/window-pal-512-check.log),
[log](generated/window-pal-2048-check.log)): a random even palindrome and its
one-character corruption in each case — accepted / rejected / accepted / rejected.
Steps per character stay at ≈13.3M (33: 14.8M, 64: 13.0M, 512: 13.2M, 2,048: 13.3M),
i.e. the cost is linear in the input, as a real-time machine simulation must be.

**What the size is made of.** Rule families: 13,203,493 wiring gates (`e…`), 41,268
Boolean fields (`b…`), 3,290 pointer fields (`p…`), 1 start rule — 99.66 % of the grammar
is the transition circuit exported gate by gate, and the circuit was emitted *without*
constant folding (that pass ran out of memory at 22 GiB and was skipped).  The size is a
property of the mechanical translation, not of the language.

## Structure: the recursion advances the input (2026-09-07)

A length-bounded grammar has an acyclic rule-call graph.  `analysis/grammar_scc.py`
parses all 13,248,052 rules, computes the greatest fixpoint of "this rule consumes at least
one character whenever it succeeds" (1,302 rules; almost everything in this encoding is a
predicate and therefore nullable), tags each of the 72,376,872 reference edges as *guarded*
when an element earlier in its sequence must consume, and runs Tarjan's SCC on the graph
reachable from `S` ([log](generated/window-pal-structure.log)):

| | |
|---|---:|
| rules reachable from `S` | 13,248,052 (all) |
| strongly connected components | 2,190,652 (304 non-trivial) |
| largest SCC | 4,002,097 rules — the machine's Boolean fields |
| consumption-guarded edges, total | 73,261 |
| consumption-guarded edges **inside SCCs** | 72,638 (99 %) |

Nearly every "consume one character, then the rule at the next position" edge lies inside a
strongly connected component: the grammar returns to the same rules after advancing the
input, which no finite unrolling can do.  Together with the absence of any length bound in
the generator and the 2,048-character runs, this settles the "huge finite grammar" worry.

What this does **not** establish: that every static cycle passes through a consuming edge
(60,993,220 unguarded intra-SCC edges exist; the guard analysis is an over-approximation,
e.g. a reference after `X?` counts as unguarded).  Well-formedness is covered dynamically —
the Rust runner's non-consuming-recursion check never fired on any tested input — and is
one of the things a verified checker should establish statically.

`analysis/grammar_closure.py` is the closure check reported above (0 undefined references).
