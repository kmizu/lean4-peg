# Both first-order CBV strategies are strictly contained in CBN

The following are proved unconditionally in Lean, on the original character-string languages:

- first-order CBV-Par ⊊ first-order CBN;
- first-order CBV-Seq ⊊ first-order CBN.

The flagship theorem is `Shallot.PegSeparation.firstOrder_cbv_par_seq_strict_cbn` in `lean/Shallot/Peg/Separation/CBVStrict.lean`. It supplies both inclusions and one CBN language outside both CBV classes. The individual results are `firstOrder_par_strict_cbn` and `firstOrder_seq_strict_cbn`.

The inclusion is established by an actual fixed grammar translation, independently of the earlier polynomial-time upper bounds for CBV. It does not change, pad, or encode the recognized input string.

## Translation contract

`CBVtoCBN.translate source strategy start` produces one first-order CBN grammar depending only on the source syntax and strategy. Its fixed start expression is `CBVtoCBN.candidateStart` (the historical low-level name). For every first-order source grammar and first-order start expression, either CBV strategy satisfies:

```lean
CBVtoCBN.translate_recognizes hg hs he x :
  MacroObs (CBVtoCBN.translate source strategy start)
    CBVtoCBN.candidateStart x (some []) ↔
  SObs source strategy start x (some [])
```

Here `hs` states that the source strategy is not CBN. There is no restriction on the original characters, input length, finite grammar arities, source recursion, or termination of the source computation. The target grammar's first-order property is `translate_firstOrder`. Acceptance preservation suffices for the language-class result; an undefined source computation is rejected by the total bounded success predicate.

## Captured values without higher-order parameters

Every logical remaining position `p` is represented by closed CBN counter expressions of lengths `p` and `n-p`. A captured substring from remaining position `a` to `b` is represented by four counters `[a,n-a,b,n-b]`, with `b ≤ a ≤ n`; its decoded value is exactly `pre x a b`.

All logical tests run at the unchanged original input root. The first-order interval matcher compares captured substrings character by character. Its fixed `unicodeAlphabet` covers every Lean character, so parameter replay is valid even for characters absent from the source grammar's literals. Named rules receive counters and captured intervals; no callable parameter is introduced.

The semantic interfaces keep source success-at-an-endpoint and source explicit failure as separate total `RootTest` predicates. Both are false for an undefined approximation. Negating success alone would incorrectly turn undefined evaluation into source failure, so ordered choice, negation and call short-circuiting use the explicit-failure predicate. Literal parameter failure can use negation of endpoint existence because literal matching itself is total.

The capture continuation is required to be total only when its argument actually succeeded. This guard matters: other candidate endpoints need not describe valid captured intervals, and their continuations are never evaluated.

## Clock and proof structure

For a fixed source grammar whose arities are bounded by `K`, `clockDigits source K = |rules| + 2K + 1` base-`n+1` digits suffice on nonempty inputs. `sourceArityBound` supplies a fixed bound from the source grammar. The all-`n` digit tuple reaches every finite observation of the source CBV table approximants. Fixed CBN rules discover `n`, initialize the tuple and decrement it with borrowing.

Arguments are evaluated at the current table round. Only entry into the called rule body decrements the clock. An exhausted clock gives an undefined table entry, not source explicit failure. Empty-input acceptance is computed from the source grammar at translation time and handled by a fixed separate branch.

The main proof chain is:

| Theorem | Evidence |
| --- | --- |
| `compiledArguments_correct` | The real argument-stage rules preserve the caller environment, accumulate captured intervals in order and use the correct Par or Seq current position. |
| `compiledLookup_correct` | Actual clock and packing rules implement a source table lookup, given body correctness at the predecessor clock. |
| `callHandler_of_lookup` | Correct table lookups discharge the call-constructor interface using the generated argument stages. |
| `compiledSyntax_correct` | Structural induction handles every first-order expression, using only proper argument-subexpression hypotheses at calls. |
| `compiledEvaluator_correct` | Strong induction on clock value closes the preceding interfaces unconditionally for the actual generated grammar. |
| `translate_recognizes` | Full-clock evaluation, empty-input handling and the fixed whole-input entry establish recognition equivalence for every original string. |
| `firstOrder_cbv_subset_cbn` | Recognition equivalence produces a CBN witness for every CBV language. |
| `firstOrder_cbv_par_seq_strict_cbn` | Both inclusions combine with the existing common noncontainment witness. |

The lower-level generator retains its `compileCandidate` name and explicit alphabet/digit parameters for executable checks. `translate` selects the unrestricted alphabet and sufficient fixed digit count. `compileCandidate_firstOrder` proves that every generated rule is first-order; `compileCandidate_at` checks the actual static rule layout. `ExprAvailable` carries all code locations of a source subtree, including every argument stage, so the simulation uses the actual collected dictionary.

## Verification

The proofs use standard Lean only. Exact dependency guards in `lean/Audit.lean` check the simulation, translation, class inclusion and strict-inclusion results against the standard dependencies `propext`, `Classical.choice` and `Quot.sound`. The source audit rejects proof placeholders, additional declarations of axioms and native proof computation.

From `lean/`:

```sh
lake build
lake env lean --run ../scripts/check-cbv-cbn-candidate.lean
```

From the repository root:

```sh
bash scripts/audit-source.sh
git diff --check
```

The executable routing suite compares Par and Seq with the generated CBN grammar on 288 cases, including recursion, multiple and nested captures, replay, ordered choice, negation, ranges, literals, empty iterations and left-recursive undefined results. Every checked target evaluation finishes within the interpreter bound. General preservation follows from the Lean theorems, rather than from these finite examples.
