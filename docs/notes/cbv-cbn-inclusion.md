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
| `Repetition` | An actual five-rule fragment implements the source repetition success relation. Target recursion strictly decreases the current position, including when the operand's approximation is unknown or succeeds without consumption. Repetition's explicit-failure predicate is always false. |
| `LeafTests` | Epsilon, arbitrary characters, character literals, ranges and fixed strings are translated to total logical-position predicates, with exact correspondence to `evV`. |
| `ParameterTests` | Captured intervals implement both success and failure of source parameter lookup. Endpoint guards prevent the matcher from receiving an invalid interval. Missing parameters explicitly fail. |
| `CompilerPlan` | `compileCandidate` actually generates a finite target grammar from the source grammar, strategy, start expression, alphabet cover and digit count. This is an executable candidate whose complete language preservation remains unproved. |
| `CompilerFirstOrder` | Every rule of the candidate grammar is proved first-order, without assumptions on the source syntax. |
| `CompilerLayout` | Collected nodes resolve to their generated rules at every local slot. Start expressions, original rule bodies and table-lookup nodes are present in the dictionary. |
| `CompilerAvailability` / `CompilerState` | Source subtrees carry availability of all their collected code. Canonical target arguments encode positions, clock and captured environment; validity and decoding are explicit. This avoids a separate transitive search through the global dictionary. |
| `CompilerBasics` / `CompilerBlocks` | Primary predicates unfold at the actual generated addresses with checked arities. Fragment lookup certificates recover literal rule sublists and transport the template semantics to the full generated grammar. |
| `CompiledSequence` / `CompiledControl` / `CompiledParameters` | The actual generated sequence, repetition, negation and parameter predicates preserve the bounded source evaluation, assuming the corresponding proper subexpression predicates. The failure adapter supplies a valid unused endpoint zero. |
| `CompiledCalls` / `CompiledSyntax` | Source-call entry agrees with argument stage zero; missing and wrong-arity calls explicitly fail. Mutual structural induction establishes all source expression cases from a `CallHandler` which receives correctness of proper argument subexpressions. That handler is an explicit remaining obligation. |
| `ClockBound` | On nonempty inputs, a grammar-dependent fixed number of base-`n+1` digits suffices to reach every finite observation of the source CBV evaluator. |

All calls in these constructions are to named rules. No callable parameter is introduced. There is no padding, input encoding, or reduction to a different recognition problem.

A logical position `p` is represented by closed counters of lengths `p` and `n-p`. A captured value is represented by two endpoints, rather than by an expression that tries to remember where it was evaluated. Evaluation of logical tests stays at the original physical input root. `LenRep` and first-order observational substitution allow different counter syntax to denote the same position; appending `.any` need not preserve the canonical syntax tree.

`capturedLiteral_iff` uses the source evaluator's remaining-input coordinates. For valid `j ≤ p ≤ n` and `r ≤ q ≤ n`, comparing `[n-p,n-j)` and `[n-q,n-r)` is equivalent to matching `pre x p j` at `sfx x q` and leaving exactly `sfx x r`. The matcher covers every Lean character, including inputs whose characters do not occur as literals in the source grammar.

## Remaining translation

The proposed target evaluator uses two total root predicates: success ending at a specified logical position, and explicit failure. At a bottom approximant both predicates fail. Negation of success alone must never stand for source failure, because that would identify divergence with failure.

For a fixed source grammar whose arities are bounded by `K`, `clockDigits g K = |rules| + 2K + 1` digits suffice on every nonempty input. `fullClock_sufficient` bounds `iterBoundV` by the all-`n` digit tuple, and `fullClock_eval_iff` connects evaluation at that bound to all finite source approximants. `ClockGrammar.clockBlock_iff` proves the generated CBN multiple-digit operation, and `clockStartBlock_iff` proves initialization from the unchanged input. These clock fragments are independent of the input string. `clockTable_step` identifies their numeric predecessor with exactly one source table round; `clockTable_zero` identifies exhaustion with an unknown entry. Arguments retain the current round, and only entry into the called body decrements it. `EmptyInput.emptyInputP_correct` supplies the separate empty-input acceptance branch, since base `n+1` degenerates there.

The generated candidate uses four global rules (interval matcher, whole-input entry, length discovery and initialization) followed by fixed-width code slots. Expression predicates take a current-position pair, a queried-endpoint pair, the frozen input length, clock pairs and captured environment values. Argument stages append captured spans, preserve the original environment while evaluating each argument, and route either the original or advanced current position according to Par or Seq. Rule lookup decrements the clock only after the arguments have succeeded. The default alphabet for the final unrestricted theorem will be `unicodeAlphabet`; the generator's alphabet parameter also permits small executable checks.

The remaining obligations are:

1. Prove correctness of the generated argument stages, preserving the original caller environment while accumulating captured intervals in order. At a valid call, `CallHandler` already receives correctness of every proper argument subexpression; these hypotheses must be used to discharge the actual capture fragments and their routing wrappers. The completed expression induction does not assume that the surrounding expression is correct.
2. Prove correctness of generated table lookup using strong induction on clock value. An exhausted clock yields unknown, and a predecessor clock enters the called rule body with its captured environment. Instantiate the checked expression induction with the resulting call handler. This mutual evaluation argument is still unproved.
3. Combine the empty-input branch, full-clock bound and whole-input entry to establish language equivalence for every original character string. Choose the digit count from the fixed source grammar and instantiate the unrestricted alphabet cover.
4. Derive both class inclusions and combine them with the existing common noncontainment witness for the requested strict inclusions.

The earlier dictionary-closure obligation is handled by `ExprAvailable`: availability includes the entire collected source subtree. Its sequence, alternative, repetition, negation and call projections provide all children and argument stages directly. The source start and every original rule body satisfy this property in the actual candidate dictionary.

`lake env lean --run ../scripts/check-cbv-cbn-candidate.lean` (from `lean/`) exercises the actual generator and interpreter. The current suite compares Par and Seq with the generated CBN grammar on 288 cases covering recursive calls, one and two captured arguments, replay, nested capture, ordered choice, negation, ranges, fixed strings, empty iterations and left-recursive unknown results. It checks that each target evaluation finishes within its explicit interpreter bound. These finite checks are routing evidence, not a proof of general language preservation.

`PartialTests.sequenceSuccessBlock_test` and `sequenceFailureBlock_test` check actual finite rule fragments; their hypotheses are the total correctness of the invoked subexpression predicates. `CaptureStep.captureBlock_test` likewise checks a real generated capture fragment against the evaluated argument and a named continuation. The expression-side hypotheses are now assembled by `compiledSyntax_correct`. Its `CallHandler` parameter must still be proved using the generated argument stages and clocked table lookup; it is not an inclusion theorem or an unconditional evaluator simulation.

The helper theorems do not assert these final inclusions. Their dependency guards are in `lean/Audit.lean` and their source is part of the ordinary repository build.
