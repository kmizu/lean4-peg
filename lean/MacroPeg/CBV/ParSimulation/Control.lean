import MacroPeg.CBV.PrefixSearch
import MacroPeg.CBV.PrefixEndpoint
import MacroPeg.CBVtoCBN.PartialTests

namespace Shallot.MacroPeg.CBV.ParSimulation

open RootObservation PrefixCounters
open CBVtoCBN (paramsFrom subst_paramsFrom_cons subst_paramsFrom paramsFrom_firstOrder)
open CBVtoCBN (seqResult seqResult_success seqResult_failure altResult altResult_success altResult_failure
  notResult notResult_success)

/-- Explicit source failure is required before the right alternative is
selected. An undefined left result enables neither branch. -/
theorem alternative_success {g : MGrammar} {s : Strategy} {x : List Char}
    {a b : Res} {q : Nat} {leftOk leftFail rightOk : MExp}
    (ho : Predicate g s leftOk x (a = some (some q)))
    (hf : Predicate g s leftFail x (a = some none))
    (hb : Predicate g s rightOk x (b = some (some q))) :
    Predicate g s (.alt leftOk (.seq leftFail rightOk)) x
      (altResult a b = some (some q)) :=
  (ho.alt (hf.seq hb)).congr (altResult_success a b q).symm

theorem alternative_failure {g : MGrammar} {s : Strategy} {x : List Char}
    {a b : Res} {leftFail rightFail : MExp}
    (ha : Predicate g s leftFail x (a = some none))
    (hb : Predicate g s rightFail x (b = some none)) :
    Predicate g s (.seq leftFail rightFail) x (altResult a b = some none) :=
  (ha.seq hb).congr (altResult_failure a b).symm

theorem negation_success {g : MGrammar} {s : Strategy} {x : List Char}
    {a : Res} {p q : Nat} {positionsEqual failure : MExp}
    (he : Predicate g s positionsEqual x (p = q))
    (hf : Predicate g s failure x (a = some none)) :
    Predicate g s (.seq positionsEqual failure) x (notResult p a = some (some q)) :=
  (he.seq hf).congr (notResult_success p q a).symm

/-- The candidate intermediate position precedes the two endpoints. All
other captured source state is passed as enclosing root-prefix counters. -/
def sequenceTestBody (left right ctxSize : Nat) : MExp :=
  .seq (.call left (.param 1 :: .param 0 :: paramsFrom 3 ctxSize))
    (.call right (.param 0 :: .param 2 :: paramsFrom 3 ctxSize))

theorem sequenceTestBody_firstOrder (left right ctxSize : Nat) :
    (sequenceTestBody left right ctxSize).FirstOrder :=
  ⟨⟨trivial, trivial, paramsFrom_firstOrder 3 ctxSize⟩,
    ⟨trivial, trivial, paramsFrom_firstOrder 3 ctxSize⟩⟩

theorem sequenceTestBody_subst (left right : Nat) (j p q : MExp) (ctx : List MExp) :
    MExp.subst (j :: p :: q :: ctx) (sequenceTestBody left right ctx.length) =
      .seq (.call left (p :: j :: ctx)) (.call right (j :: q :: ctx)) := by
  simp [sequenceTestBody, MExp.subst, MExp.substArgs, argAt,
    subst_paramsFrom_cons, subst_paramsFrom]

/-- The actual named intermediate-position test composes the two source
success predicates without changing the original input. -/
theorem sequence_position_test {g : MGrammar} {test left right : Nat}
    (ctx : List Nat)
    (hr : ruleAtM g.rules test = some ⟨ctx.length + 3, sequenceTestBody left right ctx.length⟩)
    (x : List Char) (j p q : Nat) {a : Res} {b : Nat → Res}
    (hL : Predicate g .callByValuePar
      (.call left (.lit (x.take p) :: .lit (x.take j) :: prefixValues x ctx)) x (a = some (some j)))
    (hR : Predicate g .callByValuePar
      (.call right (.lit (x.take j) :: .lit (x.take q) :: prefixValues x ctx)) x (b j = some (some q))) :
    Predicate g .callByValuePar
      (.call test (.lit (x.take j) :: .lit (x.take p) :: .lit (x.take q) :: prefixValues x ctx)) x
      (a = some (some j) ∧ b j = some (some q)) := by
  have hv := prefixValues_args g x (j :: p :: q :: ctx)
  simp only [prefixValues] at hv
  have hctx : ctx.length = (prefixValues x ctx).length := by simp
  constructor
  · intro h
    apply par_call hr (by simp) hv
    rw [hctx, sequenceTestBody_subst]
    exact (hL.seq hR).1 h
  · intro h
    apply par_call hr (by simp) hv
    rw [hctx, sequenceTestBody_subst]
    exact (hL.seq hR).2 h

/-- A concrete pair of named Par rules implements successful sequential
composition of arbitrary partial source results. Undefined source results
remain distinct from explicit source failure. -/
theorem sequence_success_test {g : MGrammar} {entry test left right : Nat}
    (ctx : List Nat)
    (hSearch : ruleAtM g.rules entry = some ⟨ctx.length + 3, existsBody entry test (ctx.length + 2)⟩)
    (hTest : ruleAtM g.rules test = some ⟨ctx.length + 3, sequenceTestBody left right ctx.length⟩)
    (x : List Char) (p q : Nat) (a : Res) (b : Nat → Res) (ha : OkR x.length a)
    (hL : ∀ j, j ≤ x.length → Predicate g .callByValuePar
      (.call left (.lit (x.take p) :: .lit (x.take j) :: prefixValues x ctx)) x (a = some (some j)))
    (hR : ∀ j, j ≤ x.length → Predicate g .callByValuePar
      (.call right (.lit (x.take j) :: .lit (x.take q) :: prefixValues x ctx)) x (b j = some (some q))) :
    Predicate g .callByValuePar
      (.call entry (.lit [] :: .lit (x.take p) :: .lit (x.take q) :: prefixValues x ctx)) x
      (seqResult a b = some (some q)) := by
  let P : Nat → Bool := fun j => decide (a = some (some j) ∧ b j = some (some q))
  have hEach : ∀ j, j ≤ x.length → Test g .callByValuePar
      (.call test (.lit (x.take j) :: prefixValues x (p :: q :: ctx))) x (P j) := by
    intro j hj
    have h := sequence_position_test ctx hTest x j p q (hL j hj) (hR j hj)
    simpa only [Test, P, decide_eq_true_eq, prefixValues] using h.obs
  have hLookup : ruleAtM g.rules entry =
      some ⟨(p :: q :: ctx).length + 1, existsBody entry test (p :: q :: ctx).length⟩ := by
    simpa only [List.length_cons] using hSearch
  have h := exists_obs (p :: q :: ctx) hLookup x P hEach 0 (by omega)
  have hp : Predicate g .callByValuePar
      (.call entry (.lit [] :: .lit (x.take p) :: .lit (x.take q) :: prefixValues x ctx)) x
      (anyFrom P 0 (x.length - 0) = true) := Predicate.of_obs h
  apply hp.congr
  rw [anyFrom_true_iff, seqResult_success x.length a b ha q]
  simp only [Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and, P, decide_eq_true_eq]

def sequenceFailureTestBody (leftOk rightFail ctxSize : Nat) : MExp :=
  .seq (.call leftOk (.param 1 :: .param 0 :: paramsFrom 2 ctxSize))
    (.call rightFail (.param 0 :: paramsFrom 2 ctxSize))

theorem sequenceFailureTestBody_firstOrder (leftOk rightFail ctxSize : Nat) :
    (sequenceFailureTestBody leftOk rightFail ctxSize).FirstOrder :=
  ⟨⟨trivial, trivial, paramsFrom_firstOrder 2 ctxSize⟩,
    ⟨trivial, paramsFrom_firstOrder 2 ctxSize⟩⟩

theorem sequenceFailureTestBody_subst (leftOk rightFail : Nat) (j p : MExp) (ctx : List MExp) :
    MExp.subst (j :: p :: ctx) (sequenceFailureTestBody leftOk rightFail ctx.length) =
      .seq (.call leftOk (p :: j :: ctx)) (.call rightFail (j :: ctx)) := by
  simp [sequenceFailureTestBody, MExp.subst, MExp.substArgs, argAt,
    subst_paramsFrom_cons, subst_paramsFrom]

/-- Successful left evaluation followed by explicit right failure is
searched independently of the explicit-left-failure branch. -/
theorem sequence_failure_test {g : MGrammar} {search test leftOk leftFail rightFail : Nat}
    (ctx : List Nat)
    (hSearch : ruleAtM g.rules search =
      some ⟨ctx.length + 2, existsBody search test (ctx.length + 1)⟩)
    (hTest : ruleAtM g.rules test =
      some ⟨ctx.length + 2, sequenceFailureTestBody leftOk rightFail ctx.length⟩)
    (x : List Char) (p : Nat) (a : Res) (b : Nat → Res) (ha : OkR x.length a)
    (hL : ∀ j, j ≤ x.length → Predicate g .callByValuePar
      (.call leftOk (.lit (x.take p) :: .lit (x.take j) :: prefixValues x ctx)) x (a = some (some j)))
    (hLF : Predicate g .callByValuePar
      (.call leftFail (.lit (x.take p) :: prefixValues x ctx)) x (a = some none))
    (hRF : ∀ j, j ≤ x.length → Predicate g .callByValuePar
      (.call rightFail (.lit (x.take j) :: prefixValues x ctx)) x (b j = some none)) :
    Predicate g .callByValuePar
      (.alt (.call leftFail (.lit (x.take p) :: prefixValues x ctx))
        (.call search (.lit [] :: .lit (x.take p) :: prefixValues x ctx))) x
      (seqResult a b = some none) := by
  have hEach : ∀ j, j ≤ x.length → Predicate g .callByValuePar
      (.call test (.lit (x.take j) :: prefixValues x (p :: ctx))) x
      (a = some (some j) ∧ b j = some none) := by
    intro j hj
    have hv := prefixValues_args g x (j :: p :: ctx)
    simp only [prefixValues] at hv
    have hctx : ctx.length = (prefixValues x ctx).length := by simp
    constructor
    · intro h
      apply par_call hTest (by simp) hv
      rw [hctx, sequenceFailureTestBody_subst]
      exact ((hL j hj).seq (hRF j hj)).1 h
    · intro h
      apply par_call hTest (by simp) hv
      rw [hctx, sequenceFailureTestBody_subst]
      exact ((hL j hj).seq (hRF j hj)).2 h
  have hLookup : ruleAtM g.rules search =
      some ⟨(p :: ctx).length + 1, existsBody search test (p :: ctx).length⟩ := by
    simpa only [List.length_cons] using hSearch
  have hs := exists_predicate (p :: ctx) hLookup x
    (fun j => a = some (some j) ∧ b j = some none) hEach 0 (by omega)
  have hPred := hLF.alt hs
  apply hPred.congr
  rw [seqResult_failure x.length a b ha]
  simp only [Nat.zero_le, true_and]

end Shallot.MacroPeg.CBV.ParSimulation
