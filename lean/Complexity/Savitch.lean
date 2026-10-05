import Complexity.WfSem
import Complexity.StepSem

/-!
# Reachability formulas (Savitch / Stockmeyer–Meyer)

`reach M S t X Y` is a quantified formula over the blocks `X` and `Y` (tags `[a, b]`) that is true exactly when the
configuration in `Y` is reached from the one in `X` within `2 ^ t` steps:

* `reach 0 X Y := X = Y ∨ Step(X, Y)`,
* `reach (t+1) X Y := ∃ Mid. WF(Mid) ∧ ∀ A ∀ B. ((A = X ∧ B = Mid) ∨ (A = Mid ∧ B = Y)) → reach t A B`,

where level `t + 1` uses the tags `[t+1, 0]` (Mid), `[t+1, 1]` (A), `[t+1, 2]` (B). The size is linear in `t`.
-/

namespace Complexity

section Reach

variable {k : Nat} (M : TM k) (S : Nat)

/-! ### Overwriting a block -/

/-- `ρ` with block `tg` set to the encoding of `c`. -/
def setBlock (ρ : Name → Bool) (tg : Name) (c : Cfg k) : Name → Bool := fun y =>
  if y.take tg.length = tg ∧ y.drop tg.length ∈ blockSuf M S then bit c (y.drop tg.length) else ρ y

theorem encodes_setBlock (ρ : Name → Bool) (tg : Name) (c : Cfg k) : Encodes M S (setBlock M S ρ tg c) tg c := by
  intro v hv
  simp [setBlock, hv]

theorem agreeOff_setBlock (ρ : Name → Bool) (tg : Name) (c : Cfg k) :
    AgreeOff (blockVars M S tg) ρ (setBlock M S ρ tg c) := by
  intro y hy
  simp only [setBlock]
  rw [if_neg]
  rintro ⟨h₁, h₂⟩
  apply hy
  simp only [blockVars, List.mem_map]
  refine ⟨_, h₂, ?_⟩
  conv => rhs; rw [← List.take_append_drop tg.length y]
  rw [h₁]

theorem not_mem_blockVars {X tg : Name} (hlen : X.length = tg.length) (hne : X ≠ tg) (v : Name) :
    X ++ v ∉ blockVars M S tg := by
  simp only [blockVars, List.mem_map, not_exists, not_and]
  intro v' _ h
  exact hne (List.append_inj h.symm hlen).1

theorem encodes_of_agree {ρ ρ' : Name → Bool} {X tg : Name} {c : Cfg k} (hlen : X.length = tg.length)
    (hne : X ≠ tg) (h : AgreeOff (blockVars M S tg) ρ ρ') (he : Encodes M S ρ X c) : Encodes M S ρ' X c := by
  intro v hv
  rw [h _ (not_mem_blockVars M S hlen hne v)]
  exact he v hv

theorem encodes_unique {ρ : Name → Bool} {b : Name} {c d : Cfg k} (hc : Good M S c) (hd : Good M S d)
    (h : Encodes M S ρ b c) (h' : Encodes M S ρ b d) : c = d :=
  good_ext M S hc hd (fun v hv => (h v hv).symm.trans (h' v hv))

/-! ### The formulas -/

def guardF (X Y Mi A B : Name) : Formula :=
  .or (.and (eqF M S A X) (eqF M S B Mi)) (.and (eqF M S A Mi) (eqF M S B Y))

def reach : Nat → Name → Name → QF
  | 0, X, Y => .prop (.or (eqF M S X Y) (stepF M S X Y))
  | t + 1, X, Y =>
    exBlock (blockVars M S [t + 1, 0]) (.andL (wfF M S [t + 1, 0])
      (allBlock (blockVars M S [t + 1, 1]) (allBlock (blockVars M S [t + 1, 2])
        (.impL (guardF M S X Y [t + 1, 0] [t + 1, 1] [t + 1, 2]) (reach t [t + 1, 1] [t + 1, 2])))))

/-- A tag usable as a free block of `reach t`: the levels `1 … t` are taken by the bound blocks. -/
def TagOK (t : Nat) (X : Name) : Prop := ∃ a b, X = [a, b] ∧ (a = 0 ∨ t < a)

theorem TagOK.ne {t : Nat} {X : Name} (h : TagOK (t + 1) X) (i : Nat) : X ≠ [t + 1, i] := by
  obtain ⟨a, b, rfl, ha⟩ := h
  intro he
  simp only [List.cons.injEq] at he
  omega

theorem TagOK.len {t : Nat} {X : Name} (h : TagOK t X) : X.length = 2 := by
  obtain ⟨a, b, rfl, _⟩ := h
  rfl

theorem tagOK_level (t i : Nat) : TagOK t [t + 1, i] := ⟨t + 1, i, rfl, Or.inr (Nat.lt_succ_self t)⟩

theorem good_run_of {c : Cfg k} (hall : ∀ j, Good M S (M.run c j)) (j : Nat) : ∀ i, Good M S (M.run (M.run c j) i) :=
  fun i => by rw [← TM.run_add]; exact hall (j + i)

/-- Correctness of `reach`. -/
theorem reach_iff : ∀ (t : Nat) (X Y : Name), TagOK t X → TagOK t Y → ∀ (ρ : Name → Bool) (c c' : Cfg k),
    Good M S c' → (∀ j, Good M S (M.run c j)) → Encodes M S ρ X c → Encodes M S ρ Y c' →
    ((reach M S t X Y).eval ρ = true ↔ ∃ j, j ≤ 2 ^ t ∧ M.run c j = c')
  | 0, X, Y, _, _, ρ, c, c', hc', hall, hX, hY => by
    have hc : Good M S c := hall 0
    simp only [reach, QF.eval, Formula.eval, Bool.or_eq_true, Nat.pow_zero]
    constructor
    · rintro (he | hs)
      · exact ⟨0, Nat.zero_le _, cfg_eq_of_eqF M S hc hc' hX hY he⟩
      · refine ⟨1, Nat.le_refl _, ?_⟩
        exact encodes_unique M S (hall 1) hc' ((stepF_iff M S hc hX).1 hs) hY
    · rintro ⟨j, hj, hrun⟩
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hj with rfl | rfl
      · left
        rw [show M.run c 0 = c from rfl] at hrun
        subst hrun
        exact eqF_of_encodes M S hX hY
      · right
        rw [show M.run c 1 = M.step c from rfl] at hrun
        subst hrun
        exact (stepF_iff M S hc hX).2 hY
  | t + 1, X, Y, hXt, hYt, ρ, c, c', hc', hall, hX, hY => by
    have hlX := hXt.len
    have hlY := hYt.len
    have l2 : ∀ i, ([t + 1, i] : Name).length = 2 := fun _ => rfl
    have hMA : ([t + 1, 0] : Name) ≠ [t + 1, 1] := by simp
    have hMB : ([t + 1, 0] : Name) ≠ [t + 1, 2] := by simp
    have hAB : ([t + 1, 1] : Name) ≠ [t + 1, 2] := by simp
    have hAM : ([t + 1, 1] : Name) ≠ [t + 1, 0] := by simp
    have hBA : ([t + 1, 2] : Name) ≠ [t + 1, 1] := by simp
    have hBM : ([t + 1, 2] : Name) ≠ [t + 1, 0] := by simp
    -- moving an encoding of a block `P` through the three overwritten blocks
    have mv : ∀ {P tg : Name} {ρ₁ ρ₂ : Name → Bool} {d : Cfg k}, P.length = 2 → P ≠ tg → tg.length = 2 →
        AgreeOff (blockVars M S tg) ρ₁ ρ₂ → Encodes M S ρ₁ P d → Encodes M S ρ₂ P d :=
      fun hP hne htg hag he => encodes_of_agree M S (hP.trans htg.symm) hne hag he
    simp only [reach, eval_exBlock, QF.eval, Bool.and_eq_true, eval_allBlock, Bool.or_eq_true, Bool.not_eq_true']
    constructor
    · rintro ⟨ρ₁, h₁, hwf, hall'⟩
      obtain ⟨m, hm, hEm⟩ := (wfF_iff M S ρ₁ [t + 1, 0]).1 hwf
      have hX₁ := mv hlX (hXt.ne 0) (l2 0) h₁ hX
      have hY₁ := mv hlY (hYt.ne 0) (l2 0) h₁ hY
      -- one half: instantiate A, B with `d`, `e`
      have half : ∀ (d e : Cfg k), Good M S e → (∀ j, Good M S (M.run d j)) →
          (∀ ρ'', Encodes M S ρ'' [t + 1, 1] d → Encodes M S ρ'' [t + 1, 2] e →
            AgreeOff (blockVars M S [t + 1, 1]) ρ₁ (setBlock M S ρ₁ [t + 1, 1] d) →
            ρ'' = setBlock M S (setBlock M S ρ₁ [t + 1, 1] d) [t + 1, 2] e →
            (guardF M S X Y [t + 1, 0] [t + 1, 1] [t + 1, 2]).eval ρ'' = true) →
          ∃ j, j ≤ 2 ^ t ∧ M.run d j = e := by
        intro d e he hd hg
        let ρa := setBlock M S ρ₁ [t + 1, 1] d
        let ρb := setBlock M S ρa [t + 1, 2] e
        have hA : Encodes M S ρb [t + 1, 1] d :=
          mv (l2 1) hAB (l2 2) (agreeOff_setBlock M S ρa _ e) (encodes_setBlock M S ρ₁ _ d)
        have hB : Encodes M S ρb [t + 1, 2] e := encodes_setBlock M S ρa _ e
        have hr := hall' ρa (agreeOff_setBlock M S ρ₁ _ d) ρb (agreeOff_setBlock M S ρa _ e)
        have hgt := hg ρb hA hB (agreeOff_setBlock M S ρ₁ _ d) rfl
        rcases hr with hng | hr
        · rw [hgt] at hng; exact absurd hng (by decide)
        · exact (reach_iff t _ _ (tagOK_level t 1) (tagOK_level t 2) ρb d e he hd hA hB).1 hr
      -- moving `X`, `Mid`, `Y` into `ρb`
      have into : ∀ {P : Name} {d e f : Cfg k}, P.length = 2 → P ≠ [t + 1, 1] → P ≠ [t + 1, 2] →
          Encodes M S ρ₁ P f → Encodes M S (setBlock M S (setBlock M S ρ₁ [t + 1, 1] d) [t + 1, 2] e) P f :=
        fun hP h1 h2 hf => mv hP h2 (l2 2) (agreeOff_setBlock M S _ _ _) (mv hP h1 (l2 1) (agreeOff_setBlock M S _ _ _) hf)
      obtain ⟨j₁, hj₁, hrun₁⟩ := half c m hm hall (by
        intro ρ'' hA hB _ hρ
        subst hρ
        simp only [guardF, Formula.eval, Bool.or_eq_true, Bool.and_eq_true]
        exact Or.inl ⟨eqF_of_encodes M S hA (into hlX (hXt.ne 1) (hXt.ne 2) hX₁),
          eqF_of_encodes M S hB (into (l2 0) hMA hMB hEm)⟩)
      subst hrun₁
      obtain ⟨j₂, hj₂, hrun₂⟩ := half (M.run c j₁) c' hc' (good_run_of M S hall j₁) (by
        intro ρ'' hA hB _ hρ
        subst hρ
        simp only [guardF, Formula.eval, Bool.or_eq_true, Bool.and_eq_true]
        exact Or.inr ⟨eqF_of_encodes M S hA (into (l2 0) hMA hMB hEm),
          eqF_of_encodes M S hB (into hlY (hYt.ne 1) (hYt.ne 2) hY₁)⟩)
      refine ⟨j₁ + j₂, ?_, by rw [TM.run_add]; exact hrun₂⟩
      rw [Nat.pow_succ]; omega
    · rintro ⟨j, hj, hrun⟩
      let j₁ := min j (2 ^ t)
      let j₂ := j - j₁
      have hj₁ : j₁ ≤ 2 ^ t := Nat.min_le_right _ _
      have hj₂ : j₂ ≤ 2 ^ t := by rw [Nat.pow_succ] at hj; omega
      have hsplit : j₁ + j₂ = j := by omega
      let m := M.run c j₁
      let ρ₁ := setBlock M S ρ [t + 1, 0] m
      have h₁ : AgreeOff (blockVars M S [t + 1, 0]) ρ ρ₁ := agreeOff_setBlock M S ρ _ m
      have hEm : Encodes M S ρ₁ [t + 1, 0] m := encodes_setBlock M S ρ _ m
      refine ⟨ρ₁, h₁, (wfF_iff M S ρ₁ [t + 1, 0]).2 ⟨m, hall j₁, hEm⟩, ?_⟩
      intro ρa ha ρb hb
      have mv2 : ∀ {P : Name} {f : Cfg k}, P.length = 2 → P ≠ [t + 1, 1] → P ≠ [t + 1, 2] →
          Encodes M S ρ₁ P f → Encodes M S ρb P f :=
        fun hP h1 h2 hf => mv hP h2 (l2 2) hb (mv hP h1 (l2 1) ha hf)
      have hXb := mv2 hlX (hXt.ne 1) (hXt.ne 2) (mv hlX (hXt.ne 0) (l2 0) h₁ hX)
      have hYb := mv2 hlY (hYt.ne 1) (hYt.ne 2) (mv hlY (hYt.ne 0) (l2 0) h₁ hY)
      have hMb := mv2 (l2 0) hMA hMB hEm
      by_cases hg : (guardF M S X Y [t + 1, 0] [t + 1, 1] [t + 1, 2]).eval ρb = true
      · right
        simp only [guardF, Formula.eval, Bool.or_eq_true, Bool.and_eq_true] at hg
        rcases hg with ⟨hAX, hBM'⟩ | ⟨hAM', hBY⟩
        · have hA := encodes_of_eqF M S hAX hXb
          have hB := encodes_of_eqF M S hBM' hMb
          exact (reach_iff t _ _ (tagOK_level t 1) (tagOK_level t 2) ρb c m (hall j₁) hall hA hB).2
            ⟨j₁, hj₁, rfl⟩
        · have hA := encodes_of_eqF M S hAM' hMb
          have hB := encodes_of_eqF M S hBY hYb
          refine (reach_iff t _ _ (tagOK_level t 1) (tagOK_level t 2) ρb m c' hc'
            (good_run_of M S hall j₁) hA hB).2 ⟨j₂, hj₂, ?_⟩
          show M.run (M.run c j₁) j₂ = c'
          rw [← TM.run_add, hsplit, hrun]
      · left
        simpa using hg

end Reach

end Complexity
