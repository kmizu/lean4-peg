import MacroPeg.CBVtoCBN.PartialTests

namespace Shallot.MacroPeg.CBVtoCBN

/-- One unfolding of source repetition, retaining the strict-decrease condition. -/
theorem evStar_success_iff (f : Nat → Res) (p q : Nat) :
    evStar f p = some (some q) ↔ (p = q ∧ f p = some none) ∨
      ∃ j, j < p ∧ f p = some (some j) ∧ evStar f j = some (some q) := by
  cases hf : f p with
  | none => simp [evStar_none hf]
  | some r => cases r with
    | none => simp [evStar_fail hf]
    | some j =>
      by_cases hj : j < p
      · rw [evStar_ok hf hj]
        simp only [Option.some.injEq, reduceCtorEq, and_false, false_or]
        constructor
        · intro h; exact ⟨j, hj, rfl, h⟩
        · rintro ⟨k, _, he, h⟩; subst k; exact h
      · rw [evStar_stuck hf hj]
        simp only [Option.some.injEq, reduceCtorEq, and_false, false_or, false_iff]
        rintro ⟨k, hk, he, _⟩
        subst k
        exact hj hk

def repetitionBody (failure search restSize : Nat) : MExp :=
  .alt (.seq (equalPositionP (.param 0) (.param 3))
      (.call failure (.param 0 :: .param 1 :: paramsFrom 4 restSize)))
    (.call search (.eps :: .param 0 :: .param 1 :: .param 2 :: .param 3 :: paramsFrom 4 restSize))

def repetitionCandidateBody (success self restSize : Nat) : MExp :=
  .seq (ltPositionP (.param 0) (.param 3))
    (.seq (.call success (.param 2 :: .param 3 :: .param 0 :: .param 1 :: paramsFrom 6 restSize))
      (.call self (.param 0 :: .param 1 :: .param 4 :: .param 5 :: paramsFrom 6 restSize)))

theorem repetitionBody_subst (failure search : Nat) (p p' q q' : MExp) (rest : List MExp) :
    MExp.subst (p :: p' :: q :: q' :: rest) (repetitionBody failure search rest.length) =
      .alt (.seq (equalPositionP p q') (.call failure (p :: p' :: rest)))
        (.call search (.eps :: p :: p' :: q :: q' :: rest)) := by
  simp [repetitionBody, equalPositionP, exactLengthP, andP, MExp.subst, MExp.substArgs,
    argAt, subst_paramsFrom_cons, subst_paramsFrom]

theorem repetitionCandidate_subst (success self : Nat) (j j' p p' q q' : MExp) (rest : List MExp) :
    MExp.subst (j :: j' :: p :: p' :: q :: q' :: rest) (repetitionCandidateBody success self rest.length) =
      .seq (ltPositionP j p') (.seq (.call success (p :: p' :: j :: j' :: rest))
        (.call self (j :: j' :: q :: q' :: rest))) := by
  simp [repetitionCandidateBody, ltPositionP, fitsLengthP, andP, MExp.subst, MExp.substArgs,
    argAt, subst_paramsFrom_cons, subst_paramsFrom]

/-- Five static rules recognize repetition's bounded success relation at the original input root. -/
def repetitionBlock (entry success failure restSize : Nat) : List MRule :=
  ⟨restSize + 4, repetitionBody failure (entry + 1) restSize⟩ ::
    (pairSearchBlock (entry + 1) (entry + 4) (restSize + 4) ++
      [⟨restSize + 6, repetitionCandidateBody success entry restSize⟩])

theorem repetitionBlock_firstOrder (entry success failure restSize : Nat) :
    ∀ rule ∈ repetitionBlock entry success failure restSize, rule.body.FirstOrder := by
  intro rule hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨⟨(positionTests_firstOrder (pre := .param 0) (suf := .param 3) trivial trivial).1,
      ⟨trivial, trivial, paramsFrom_firstOrder _ _⟩⟩,
      ⟨trivial, trivial, trivial, trivial, trivial, paramsFrom_firstOrder _ _⟩⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact pairSearchBlock_firstOrder _ _ _ rule hr
  · have he := List.mem_singleton.mp hr
    subst rule
    exact ⟨(positionTests_firstOrder (pre := .param 0) (suf := .param 3) trivial trivial).2.2,
      ⟨⟨trivial, trivial, trivial, trivial, paramsFrom_firstOrder _ _⟩,
        ⟨trivial, trivial, trivial, trivial, paramsFrom_firstOrder _ _⟩⟩⟩

/-- The recursive target rules are total: their only recursive call has a strictly smaller position.
A successful empty iteration or an unknown source result yields a false success test, preserving bottom. -/
theorem repetitionBlock_test (pre tail : List MRule) (success failure : Nat) (rest : List MExp)
    (x : List Char) (f : Nat → Res)
    (hs : ∀ p, p ≤ x.length → ∀ j, j ≤ x.length → RootTest
      ⟨pre ++ (repetitionBlock pre.length success failure rest.length ++ tail)⟩
      (.call success (skipN p :: skipN (x.length - p) :: skipN j :: skipN (x.length - j) :: rest)) x
      (f p = some (some j)))
    (hf : ∀ p, p ≤ x.length → RootTest
      ⟨pre ++ (repetitionBlock pre.length success failure rest.length ++ tail)⟩
      (.call failure (skipN p :: skipN (x.length - p) :: rest)) x (f p = some none))
    (p q : Nat) (hp : p ≤ x.length) (hq : q ≤ x.length) :
    RootTest ⟨pre ++ (repetitionBlock pre.length success failure rest.length ++ tail)⟩
      (.call pre.length (skipN p :: skipN (x.length - p) :: skipN q :: skipN (x.length - q) :: rest)) x
      (evStar f p = some (some q)) := by
  let g : MGrammar := ⟨pre ++ (repetitionBlock pre.length success failure rest.length ++ tail)⟩
  have h0 : ruleAtM g.rules pre.length = some
      ⟨rest.length + 4, repetitionBody failure (pre.length + 1) rest.length⟩ := by
    rw [show pre.length = pre.length + 0 by omega]
    exact (ruleAtM_append_offset pre _ 0).trans rfl
  have aux : ∀ p, p ≤ x.length → RootTest g
      (.call pre.length (skipN p :: skipN (x.length - p) :: skipN q :: skipN (x.length - q) :: rest)) x
      (evStar f p = some (some q)) := by
    intro p
    induction p using Nat.strongRecOn with
    | ind p ih =>
      intro hp
      let ctx := skipN p :: skipN (x.length - p) :: skipN q :: skipN (x.length - q) :: rest
      have h1 : ruleAtM g.rules (pre.length + 1) = some
          ⟨ctx.length + 1, anyPositionBody (pre.length + 1) (pre.length + 2) ctx.length⟩ := by
        rw [ruleAtM_append_offset]
        simp [repetitionBlock, pairSearchBlock, ctx, ruleAtM, Nat.add_comm, Nat.add_left_comm]
      have h2 : ruleAtM g.rules (pre.length + 2) = some
          ⟨ctx.length + 1, pairSeedBody (pre.length + 3) ctx.length⟩ := by
        rw [ruleAtM_append_offset]
        simp [repetitionBlock, pairSearchBlock, ctx, ruleAtM, Nat.add_comm, Nat.add_left_comm]
      have h3 : ruleAtM g.rules (pre.length + 3) = some
          ⟨ctx.length + 2, complementContextBody (pre.length + 3) (pre.length + 4) ctx.length⟩ := by
        rw [ruleAtM_append_offset]
        simp [repetitionBlock, pairSearchBlock, ctx, ruleAtM, Nat.add_comm, Nat.add_left_comm]
      have h4 : ruleAtM g.rules (pre.length + 4) = some
          ⟨rest.length + 6, repetitionCandidateBody success pre.length rest.length⟩ := by
        rw [ruleAtM_append_offset]
        rfl
      have ht : ∀ j, j ≤ x.length → RootTest g
          (.call (pre.length + 4) (skipN j :: skipN (x.length - j) :: ctx)) x
          (j < p ∧ f p = some (some j) ∧ evStar f j = some (some q)) := by
        intro j hj
        rw [rootTest_call_iff h4 (by simp [ctx]), repetitionCandidate_subst]
        have hg := ltPosition_obs (skipN_rep g j) (skipN_rep g (x.length - p)) x (by omega)
        rw [show x.length - (x.length - p) = p by omega] at hg
        exact (RootTest.of_obs hg).guarded (fun hlt => (hs p hp j hj).seq (ih j hlt (by omega)))
      have hex := anyPair_test ctx h1 h2 h3 x
        (fun j => j < p ∧ f p = some (some j) ∧ evStar f j = some (some q)) ht
      have heq := equalPosition_obs (skipN_rep g p) (skipN_rep g (x.length - q)) x (by omega)
      rw [show x.length - (x.length - q) = q by omega] at heq
      have hb := (RootTest.of_obs heq).seq (hf p hp)
      rw [rootTest_call_iff h0 (by simp), repetitionBody_subst]
      apply (hb.alt hex).congr
      rw [evStar_success_iff]
      constructor
      · rintro (h | ⟨j, _, hlt, hj, hr⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j, hlt, hj, hr⟩
      · rintro (h | ⟨j, hlt, hj, hr⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j, by omega, hlt, hj, hr⟩
  exact aux p hp

/-- Repetition never explicitly fails, even when its operand is unknown or loops without consuming. -/
theorem repetitionFailure_test (g : MGrammar) (x : List Char) (f : Nat → Res) (p : Nat) :
    RootTest g MExp.failAlways x (evStar f p = some none) :=
  (rootTest_fail g x).congr ⟨False.elim, fun h => (evStar_ne_fail p h).elim⟩

end Shallot.MacroPeg.CBVtoCBN
