# First-order CBV to CBN: construction in progress

The target is language-preserving inclusion for both call-by-value strategies, on the original character strings:

- first-order CBV-Par ⊊ first-order CBN;
- first-order CBV-Seq ⊊ first-order CBN.

These inclusions are **not proved yet**. `firstOrder_cbn_not_cbv` already supplies one CBN language outside both CBV classes. The remaining requirement is an actual first-order CBN grammar for each first-order CBV grammar and start expression. Polynomial-time membership and hardness under reductions do not supply this translation.

## Checked representation

The modules in `lean/MacroPeg/CBVtoCBN/` implement the following CBN components.

| Module | Checked property |
| --- | --- |
| `Positions` | A closed expression `skipN k` consumes exactly `k` arbitrary characters when available and explicitly fails otherwise. Complementary counters test equality and order of logical positions at the unchanged input root. |
| `Control` | A total zero-width guard selects exactly one branch, preserving that branch's success, failure, and absence of finite observations. |
| `LengthSearch` | Finite input-length and complement discovery passes frozen counters to a static continuation. |
| `SpanMatch` | A fixed first-order recursive rule compares two input intervals character by character. |
| `SpanValues` | A finite cover of all Lean characters makes interval comparison independent of the input alphabet. `capturedLiteral_iff` identifies this comparison with actual matching of the string captured by CBV. |
| `PositionSearch` | Finite existential position search retains arbitrary context arguments. Totality requires every candidate test to be a total zero-width predicate. |
| `ContextSearch` | Complement discovery retains arbitrary context arguments and preserves every observation of its continuation. |
| `CounterStep` | A paired prefix/complement counter branches at zero or decrements to its predecessor, retaining the context and the observations of a static continuation. |
| `EmptyInput` | A constant branch computed from the source grammar recognizes its acceptance of the empty input, for either CBV strategy. It rejects every nonempty original input. |
| `Routing` | Static parameter slices and paired arguments substitute to exactly the retained context. |
| `ClockStep` / `ClockGrammar` | An actual finite first-order rule fragment decrements the full fixed-width clock, handles borrowing and the all-zero case, and preserves every observation of either continuation. A fixed start fragment discovers the input length and initializes every digit. |
| `RootTests` / `PairSearch` | Total zero-width predicates compose under conjunction, disjunction and negation. A three-rule block quantifies over paired position counters while retaining context. |
| `PartialTests` | Successful alternatives, explicit alternative failure, and negation retain the distinction between unknown and failure. Actual generated fragments implement both success and failure of sequencing, given total subexpression predicates. |
| `CaptureStep` | A four-rule fragment passes the consumed interval and the correct Par/Seq current position to a named continuation. Both success and explicit failure use this bounded capture relation. Source call/argument clauses agree with this continuation form. Every successful finite approximation yields valid interval endpoints, in any literal environment. |
| `ClockBound` | On nonempty inputs, a grammar-dependent fixed number of base-`n+1` digits suffices to reach every finite observation of the source CBV evaluator. |

All calls in these constructions are to named rules. No callable parameter is introduced. There is no padding, input encoding, or reduction to a different recognition problem.

A logical position `p` is represented by closed counters of lengths `p` and `n-p`. A captured value is represented by two endpoints, rather than by an expression that tries to remember where it was evaluated. Evaluation of logical tests stays at the original physical input root. `LenRep` and first-order observational substitution allow different counter syntax to denote the same position; appending `.any` need not preserve the canonical syntax tree.

`capturedLiteral_iff` uses the source evaluator's remaining-input coordinates. For valid `j ≤ p ≤ n` and `r ≤ q ≤ n`, comparing `[n-p,n-j)` and `[n-q,n-r)` is equivalent to matching `pre x p j` at `sfx x q` and leaving exactly `sfx x r`. The matcher covers every Lean character, including inputs whose characters do not occur as literals in the source grammar.

## Remaining translation

The proposed target evaluator uses two total root predicates: success ending at a specified logical position, and explicit failure. At a bottom approximant both predicates fail. Negation of success alone must never stand for source failure, because that would identify divergence with failure.

For a fixed source grammar whose arities are bounded by `K`, `clockDigits g K = |rules| + 2K + 1` digits suffice on every nonempty input. `fullClock_sufficient` bounds `iterBoundV` by the all-`n` digit tuple, and `fullClock_eval_iff` connects evaluation at that bound to all finite source approximants. `ClockGrammar.clockBlock_iff` proves the generated CBN multiple-digit operation, and `clockStartBlock_iff` proves initialization from the unchanged input. These clock fragments are independent of the input string. `clockTable_step` identifies their numeric predecessor with exactly one source table round; `clockTable_zero` identifies exhaustion with an unknown entry. Arguments retain the current round, and only entry into the called body decrements it. `EmptyInput.emptyInputP_correct` supplies the separate empty-input acceptance branch, since base `n+1` degenerates there.

The remaining obligations are:

1. Generate a complete grammar from all source expressions and rule bodies. Allocate the checked sequence/capture fragments, route each subexpression's context, and compile the primitive expression cases.
2. Implement the repetition success predicate as bounded descending recursion on the current position. Its failure predicate must reflect that source repetition never explicitly fails; an empty successful iteration remains unknown at the approximant level.
3. Assemble captured intervals into the called rule's environment and connect its body to the decremented clock. Prove the mutual bounded-evaluator simulation, first for Par and then Seq. The checked one-argument capture step already supplies the different current-position routing: Par retains the start, Seq advances to the endpoint.
4. Combine the checked empty-input branch with the nonempty evaluator, supply a fixed start expression, and prove whole-input recognition equivalence for every original character string.
5. Derive both class inclusions and combine them with the existing common noncontainment witness for the requested strict inclusions.

`PartialTests.sequenceSuccessBlock_test` and `sequenceFailureBlock_test` check actual finite rule fragments; their hypotheses are the total correctness of the invoked subexpression predicates. `CaptureStep.captureBlock_test` likewise checks a real generated capture fragment against the evaluated argument and a named continuation. These hypotheses still need to be discharged together by a complete grammar translation and a mutual induction on the clock, expression syntax, and repetition position.

The helper theorems do not assert these final inclusions. Their dependency guards are in `lean/Audit.lean` and their source is part of the ordinary repository build.
