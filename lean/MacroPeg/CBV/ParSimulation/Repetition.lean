import MacroPeg.CBV.ParSimulation.Parameters
import MacroPeg.CBVtoCBN.Repetition

namespace Shallot.MacroPeg.CBV.ParSimulation

open RootObservation PrefixCounters
open CBVtoCBN (paramsFrom paramsFrom_firstOrder subst_paramsFrom_cons subst_paramsFrom evStar_success_iff)

def repetitionBody (equal failure search ctxSize : Nat) : MExp :=
  .alt (.seq (.call equal [.param 0, .param 1])
      (.call failure (.param 0 :: paramsFrom 2 ctxSize)))
    (.call search (.lit [] :: .param 0 :: .param 1 :: paramsFrom 2 ctxSize))

def repetitionCandidateBody (order success self ctxSize : Nat) : MExp :=
  .seq (.notP (.call order [.param 0, .param 1]))
    (.seq (.call success (.param 1 :: .param 0 :: paramsFrom 3 ctxSize))
      (.call self (.param 0 :: .param 2 :: paramsFrom 3 ctxSize)))

theorem repetitionBody_firstOrder (equal failure search ctxSize : Nat) :
    (repetitionBody equal failure search ctxSize).FirstOrder :=
  ⟨⟨⟨trivial, trivial, trivial⟩, trivial, paramsFrom_firstOrder 2 ctxSize⟩,
    ⟨trivial, trivial, trivial, paramsFrom_firstOrder 2 ctxSize⟩⟩

theorem repetitionCandidateBody_firstOrder (order success self ctxSize : Nat) :
    (repetitionCandidateBody order success self ctxSize).FirstOrder :=
  ⟨⟨trivial, trivial, trivial⟩,
    ⟨⟨trivial, trivial, paramsFrom_firstOrder 3 ctxSize⟩,
      ⟨trivial, trivial, paramsFrom_firstOrder 3 ctxSize⟩⟩⟩

theorem repetitionBody_subst (equal failure search : Nat) (p q : MExp) (ctx : List MExp) :
    MExp.subst (p :: q :: ctx) (repetitionBody equal failure search ctx.length) =
      .alt (.seq (.call equal [p, q]) (.call failure (p :: ctx)))
        (.call search (.lit [] :: p :: q :: ctx)) := by
  simp [repetitionBody, MExp.subst, MExp.substArgs, argAt,
    subst_paramsFrom_cons, subst_paramsFrom]

theorem repetitionCandidateBody_subst (order success self : Nat)
    (j p q : MExp) (ctx : List MExp) :
    MExp.subst (j :: p :: q :: ctx) (repetitionCandidateBody order success self ctx.length) =
      .seq (.notP (.call order [j, p]))
        (.seq (.call success (p :: j :: ctx)) (.call self (j :: q :: ctx))) := by
  simp [repetitionCandidateBody, MExp.subst, MExp.substArgs, argAt,
    subst_paramsFrom_cons, subst_paramsFrom]

/-- Three named Par rules implement source repetition. The candidate's
strict position guard ensures that the only recursive test advances the
logical position, including when the operand can succeed without consuming. -/
theorem repetition_test {g : MGrammar} {entry search candidate order equal success failure : Nat}
    (ctx : List Nat)
    (hEntry : ruleAtM g.rules entry =
      some ⟨ctx.length + 2, repetitionBody equal failure search ctx.length⟩)
    (hSearch : ruleAtM g.rules search =
      some ⟨ctx.length + 3, existsBody search candidate (ctx.length + 2)⟩)
    (hCandidate : ruleAtM g.rules candidate =
      some ⟨ctx.length + 3, repetitionCandidateBody order success entry ctx.length⟩)
    (hOrder : ruleAtM g.rules order = some ⟨2, leBody order equal⟩)
    (hEqual : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (x : List Char) (f : Nat → Res)
    (hS : ∀ p, p ≤ x.length → ∀ j, j ≤ x.length → Predicate g .callByValuePar
      (.call success (.lit (x.take (x.length - p)) :: .lit (x.take (x.length - j)) :: prefixValues x ctx)) x
      (f p = some (some j)))
    (hF : ∀ p, p ≤ x.length → Predicate g .callByValuePar
      (.call failure (.lit (x.take (x.length - p)) :: prefixValues x ctx)) x (f p = some none))
    (p q : Nat) (hp : p ≤ x.length) (hq : q ≤ x.length) :
    Predicate g .callByValuePar
      (.call entry (.lit (x.take (x.length - p)) :: .lit (x.take (x.length - q)) :: prefixValues x ctx)) x
      (evStar f p = some (some q)) := by
  have aux : ∀ p, p ≤ x.length → Predicate g .callByValuePar
      (.call entry (.lit (x.take (x.length - p)) :: .lit (x.take (x.length - q)) :: prefixValues x ctx)) x
      (evStar f p = some (some q)) := by
    intro p
    induction p using Nat.strongRecOn with
    | ind p ih =>
      intro hp
      let state := (x.length - p) :: (x.length - q) :: ctx
      have hEach : ∀ k, k ≤ x.length → Predicate g .callByValuePar
          (.call candidate (.lit (x.take k) :: prefixValues x state)) x
          (x.length - k < p ∧ f p = some (some (x.length - k)) ∧
            evStar f (x.length - k) = some (some q)) := by
        intro k hk
        have hLe := le_predicate hOrder hEqual x k (x.length - p) hk (by omega)
        have hStrict := hLe.notP.congr (show ¬ k ≤ x.length - p ↔ x.length - k < p by omega)
        have hGuarded := hStrict.guarded (fun hlt =>
          (hS p hp (x.length - k) (by omega)).seq (ih (x.length - k) hlt (by omega)))
        have hBack : x.length - (x.length - k) = k := by omega
        rw [hBack] at hGuarded
        have hv := prefixValues_args g x (k :: state)
        simp only [state, prefixValues] at hv
        have hctx : ctx.length = (prefixValues x ctx).length := by simp
        constructor
        · intro h
          apply par_call hCandidate (by simp) hv
          rw [hctx, repetitionCandidateBody_subst]
          exact hGuarded.1 h
        · intro h
          apply par_call hCandidate (by simp) hv
          rw [hctx, repetitionCandidateBody_subst]
          exact hGuarded.2 h
      have hLookup : ruleAtM g.rules search =
          some ⟨state.length + 1, existsBody search candidate state.length⟩ := by
        simpa only [state, List.length_cons] using hSearch
      have hExists := exists_predicate state hLookup x
        (fun k => x.length - k < p ∧ f p = some (some (x.length - k)) ∧
          evStar f (x.length - k) = some (some q)) hEach 0 (by omega)
      have hE := (Predicate.of_obs (equal_obs hEqual x (x.length - p) (x.length - q)
        (by omega) (by omega))).congr (show x.length - p = x.length - q ↔ p = q by omega)
      have hBody := (hE.seq (hF p hp)).alt hExists
      have hSpec : (p = q ∧ f p = some none) ∨
          (∃ k, 0 ≤ k ∧ k ≤ x.length ∧ x.length - k < p ∧
            f p = some (some (x.length - k)) ∧ evStar f (x.length - k) = some (some q)) ↔
          evStar f p = some (some q) := by
        rw [evStar_success_iff]
        constructor
        · rintro (h | ⟨k, _, hk, hlt, hs, hr⟩)
          · exact Or.inl h
          · exact Or.inr ⟨x.length - k, hlt, hs, hr⟩
        · rintro (h | ⟨j, hj, hs, hr⟩)
          · exact Or.inl h
          · refine Or.inr ⟨x.length - j, by omega, by omega, ?_⟩
            have hBack : x.length - (x.length - j) = j := by omega
            exact ⟨by omega, by simpa only [hBack] using hs, by simpa only [hBack] using hr⟩
      have hBody := hBody.congr hSpec
      have hv := prefixValues_args g x state
      simp only [state, prefixValues] at hv
      have hctx : ctx.length = (prefixValues x ctx).length := by simp
      constructor
      · intro h
        apply par_call hEntry (by simp) hv
        rw [hctx, repetitionBody_subst]
        exact hBody.1 h
      · intro h
        apply par_call hEntry (by simp) hv
        rw [hctx, repetitionBody_subst]
        exact hBody.2 h
  exact aux p hp

theorem repetition_failure_test (g : MGrammar) (x : List Char) (f : Nat → Res) (p : Nat) :
    Predicate g .callByValuePar MExp.failAlways x (evStar f p = some none) := by
  constructor
  · intro h
    exact False.elim (evStar_ne_fail p h)
  · intro _
    exact ⟨_, .notOk _ _ _ _ (.eps x), rfl⟩

end Shallot.MacroPeg.CBV.ParSimulation
