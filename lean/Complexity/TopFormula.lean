import Complexity.Savitch
import Complexity.Vars
import Complexity.Circuit
import Complexity.Count
import Complexity.QbfCodec

/-!
# The formula of a space-bounded computation

`topF M S T c₀ := ∃X ∃Y. Init_{c₀}(X) ∧ WF(Y) ∧ Acc(Y) ∧ reach T X Y` with `X = [0,0]`, `Y = [0,1]`. It is `Clean`
(side conditions never mention variables bound below them), so it compiles to a prenex QBF with the same value.

Main result (`reduction_correct`): if `M` decides `L` in space `s`, then for every input `w`,
`L w ↔ TQBF (encode (redQbf M (s |w|) w))`, where `T` is the number of variables of a block — by the pigeonhole bound
(`halt_within`) a halting run halts within `2 ^ T` steps.
-/

namespace Complexity

section Top

variable {k : Nat} (M : TM k) (S : Nat)

/-! ### Variables and bound names -/

theorem not_inBlock {a b l i : Nat} (h : ¬(a = l ∧ b = i)) (v : Name) : ¬ InBlock [a, b] ([l, i] ++ v) := by
  rintro ⟨v', hv'⟩
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hv'
  exact h ⟨hv'.1.symm, hv'.2.1.symm⟩

theorem mem_blockVars_iff {tg x : Name} : x ∈ blockVars M S tg ↔ ∃ v ∈ blockSuf M S, tg ++ v = x := by
  simp [blockVars]

/-- Names bound in `reach t` live in blocks of levels `1 … t`. -/
theorem reach_bound : ∀ (t : Nat) (X Y : Name), ∀ x ∈ (reach M S t X Y).bound,
    ∃ l i v, x = [l, i] ++ v ∧ 1 ≤ l ∧ l ≤ t
  | 0, _, _, x, hx => by simp [reach, QF.bound] at hx
  | t + 1, X, Y, x, hx => by
    simp only [reach, bound_exBlock, QF.bound, bound_allBlock, List.mem_append] at hx
    rcases hx with hx | hx | hx | hx
    · obtain ⟨v, _, rfl⟩ := (mem_blockVars_iff M S).1 hx; exact ⟨t + 1, 0, v, rfl, by omega, by omega⟩
    · obtain ⟨v, _, rfl⟩ := (mem_blockVars_iff M S).1 hx; exact ⟨t + 1, 1, v, rfl, by omega, by omega⟩
    · obtain ⟨v, _, rfl⟩ := (mem_blockVars_iff M S).1 hx; exact ⟨t + 1, 2, v, rfl, by omega, by omega⟩
    · obtain ⟨l, i, v, rfl, h1, h2⟩ := reach_bound t _ _ x hx
      exact ⟨l, i, v, rfl, h1, by omega⟩

theorem guardF_within (X Y Mi A B : Name) : (guardF M S X Y Mi A B).Within
    (fun y => InBlock X y ∨ InBlock Y y ∨ InBlock Mi y ∨ InBlock A y ∨ InBlock B y) := by
  refine ⟨⟨(eqF_within M S A X).mono ?_, (eqF_within M S B Mi).mono ?_⟩,
    ⟨(eqF_within M S A Mi).mono ?_, (eqF_within M S B Y).mono ?_⟩⟩ <;>
  · intro y hy; rcases hy with hy | hy <;> simp [hy]

/-- A block with tag `[a, b]` outside levels `1 … t` is untouched by the quantifiers of `reach t`. -/
theorem free_of_level {t : Nat} {a b : Nat} (ha : a = 0 ∨ t < a) (X Y : Name) :
    ∀ x ∈ (reach M S t X Y).bound, ¬ InBlock [a, b] x := by
  intro x hx
  obtain ⟨l, i, v, rfl, h1, h2⟩ := reach_bound M S t X Y x hx
  exact not_inBlock (by omega) v

theorem reach_clean : ∀ (t : Nat) (X Y : Name), TagOK t X → TagOK t Y → (reach M S t X Y).Clean
  | 0, _, _, _, _ => trivial
  | t + 1, X, Y, hX, hY => by
    obtain ⟨a, b, rfl, ha⟩ := hX
    obtain ⟨a', b', rfl, ha'⟩ := hY
    simp only [reach]
    apply clean_exBlock
    refine ⟨?_, ?_⟩
    · intro x hx ρ v
      refine eval_upd_of_within (wfF_within M S _) ?_ ρ v
      simp only [bound_allBlock, QF.bound, List.mem_append] at hx
      rcases hx with hx | hx | hx
      · obtain ⟨v, _, rfl⟩ := (mem_blockVars_iff M S).1 hx; exact not_inBlock (by omega) v
      · obtain ⟨v, _, rfl⟩ := (mem_blockVars_iff M S).1 hx; exact not_inBlock (by omega) v
      · exact free_of_level M S (Or.inr (Nat.lt_succ_self t)) _ _ x hx
    · apply clean_allBlock
      apply clean_allBlock
      refine ⟨?_, reach_clean t _ _ (tagOK_level t 1) (tagOK_level t 2)⟩
      intro x hx ρ v
      refine eval_upd_of_within (guardF_within M S _ _ _ _ _) ?_ ρ v
      have hfree : ∀ {c d : Nat}, (c = 0 ∨ t < c) → ¬ InBlock [c, d] x :=
        fun hc => free_of_level M S hc _ _ x hx
      rintro (h | h | h | h | h)
      · exact hfree (by omega) h
      · exact hfree (by omega) h
      · exact hfree (by omega) h
      · exact hfree (by omega) h
      · exact hfree (by omega) h

/-! ### The top formula -/

def topSide (c₀ : Cfg k) : Formula :=
  .and (initF M S [0, 0] c₀) (.and (wfF M S [0, 1]) (accF [0, 1]))

def topF (T : Nat) (c₀ : Cfg k) : QF :=
  exBlock (blockVars M S [0, 0]) (exBlock (blockVars M S [0, 1]) (.andL (topSide M S c₀) (reach M S T [0, 0] [0, 1])))

theorem topF_clean (T : Nat) (c₀ : Cfg k) : (topF M S T c₀).Clean := by
  apply clean_exBlock; apply clean_exBlock
  refine ⟨?_, reach_clean M S T _ _ ⟨0, 0, rfl, Or.inl rfl⟩ ⟨0, 1, rfl, Or.inl rfl⟩⟩
  intro x hx ρ v
  have hw : (topSide M S c₀).Within (fun y => InBlock [0, 0] y ∨ InBlock [0, 1] y) :=
    ⟨(initF_within M S _ c₀).mono (fun _ h => Or.inl h),
      (wfF_within M S _).mono (fun _ h => Or.inr h), (accF_within _).mono (fun _ h => Or.inr h)⟩
  refine eval_upd_of_within hw ?_ ρ v
  rintro (h | h)
  · exact free_of_level M S (Or.inl rfl) _ _ x hx h
  · exact free_of_level M S (Or.inl rfl) _ _ x hx h

theorem accF_iff {ρ : Name → Bool} {b : Name} {c : Cfg k} (h : Encodes M S ρ b c) :
    (accF b).eval ρ = true ↔ c.state = 0 := by
  have h0 : [0, 0] ∈ blockSuf M S := by
    simp only [blockSuf, sSuf, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl ⟨0, by have := M.three_le_nq; omega, rfl⟩)
  simp only [accF, Formula.eval, h _ h0, bit, decide_eq_true_eq]

theorem topF_iff (T : Nat) (c₀ : Cfg k) (hall : ∀ j, Good M S (M.run c₀ j)) (ρ : Name → Bool) :
    (topF M S T c₀).eval ρ = true ↔ ∃ j, j ≤ 2 ^ T ∧ (M.run c₀ j).state = 0 := by
  simp only [topF, eval_exBlock, QF.eval, Bool.and_eq_true, topSide, Formula.eval]
  constructor
  · rintro ⟨ρ₁, _, ρ₂, _, ⟨hi, hw, ha⟩, hr⟩
    have hX := (initF_iff M S ρ₂ _ c₀).1 hi
    obtain ⟨c', hc', hY⟩ := (wfF_iff M S ρ₂ _).1 hw
    obtain ⟨j, hj, hrun⟩ := (reach_iff M S T _ _ ⟨0, 0, rfl, Or.inl rfl⟩ ⟨0, 1, rfl, Or.inl rfl⟩ ρ₂ c₀ c' hc' hall
      hX hY).1 hr
    exact ⟨j, hj, hrun ▸ (accF_iff M S hY).1 ha⟩
  · rintro ⟨j, hj, hacc⟩
    let ρ₁ := setBlock M S ρ [0, 0] c₀
    let ρ₂ := setBlock M S ρ₁ [0, 1] (M.run c₀ j)
    have hX : Encodes M S ρ₂ [0, 0] c₀ :=
      encodes_of_agree M S (tg := [0, 1]) rfl (show ([0, 0] : Name) ≠ [0, 1] by decide) (agreeOff_setBlock M S ρ₁ [0, 1] (M.run c₀ j)) (encodes_setBlock M S ρ _ c₀)
    have hY : Encodes M S ρ₂ [0, 1] (M.run c₀ j) := encodes_setBlock M S ρ₁ _ _
    refine ⟨ρ₁, agreeOff_setBlock M S ρ _ _, ρ₂, agreeOff_setBlock M S ρ₁ _ _,
      ⟨(initF_iff M S ρ₂ _ c₀).2 hX, (wfF_iff M S ρ₂ _).2 ⟨_, hall j, hY⟩, (accF_iff M S hY).2 hacc⟩, ?_⟩
    exact (reach_iff M S T _ _ ⟨0, 0, rfl, Or.inl rfl⟩ ⟨0, 1, rfl, Or.inl rfl⟩ ρ₂ c₀ _ (hall j) hall hX hY).2
      ⟨j, hj, rfl⟩

/-! ### From runs to the language -/

/-- State and symbols stay in range. -/
def InRange (c : Cfg k) : Prop := c.state < M.nq ∧ ∀ i j, c.cells i j < M.na

theorem inRange_step {c : Cfg k} (h : InRange M c) : InRange M (M.step c) := by
  unfold TM.step
  split
  · exact h
  · have hr : ∀ i, c.read i < M.na := fun i => h.2 i _
    refine ⟨M.delta_state _ _ h.1 hr, fun i j => ?_⟩
    show (if j = c.pos i then _ else _) < M.na
    split
    · exact M.delta_sym _ _ h.1 hr i
    · exact h.2 i j

theorem inRange_run {c : Cfg k} (h : InRange M c) : ∀ t, InRange M (M.run c t)
  | 0 => h
  | t + 1 => inRange_step M (inRange_run h t)

theorem inRange_init (w : List Bool) : InRange M (initCfg k w) := by
  have h3 := M.three_le_na
  refine ⟨by have := M.three_le_nq; show 2 < M.nq; omega, fun i j => ?_⟩
  show (if i.val = 0 then (match w[j]? with | some b => bitSym b | none => 0) else 0) < M.na
  split
  · split
    · rename_i b _; cases b <;> simp [bitSym] <;> omega
    · omega
  · omega

theorem good_of {c : Cfg k} (hr : InRange M c) (hf : Fits S c) : Good M S c :=
  ⟨hr.1, fun i => ⟨(hf i).1, fun j => ⟨fun _ => hr.2 i j, fun hj => (hf i).2 j hj⟩⟩⟩

/-- The number of variables of a block. -/
def blockSize : Nat := (blockSuf M S).length

def redQF (w : List Bool) : QF := topF M S (blockSize M S) (initCfg k w)

def redQbf (w : List Bool) : Qbf := (redQF M S w).toQbf

theorem accepts_iff_bounded {L : Lang} (hdec : M.Decides L) (w : List Bool)
    (hall : ∀ j, Good M S (M.run (initCfg k w) j)) :
    L w ↔ ∃ j, j ≤ 2 ^ blockSize M S ∧ (M.run (initCfg k w) j).state = 0 := by
  obtain ⟨t, hht, hiff⟩ := hdec w
  constructor
  · intro hL
    obtain ⟨t', ht', heq⟩ := halt_within M.step (M.run (initCfg k w)) (fun _ => rfl) Cfg.halted
      (fun _ h => M.step_halted h) (fun c => (blockSuf M S).map (bit c)) (blockSize M S)
      (fun _ => by simp [blockSize]) (fun i j he => good_ext M S (hall i) (hall j) (fun v hv => List.map_inj_left.1 he v hv)) t hht
    exact ⟨t', Nat.le_of_lt ht', heq ▸ hiff.2 hL⟩
  · rintro ⟨j, _, hacc⟩
    have hhj : (M.run (initCfg k w) j).halted := Or.inl hacc
    apply hiff.1
    rcases Nat.le_total j t with hle | hle
    · rw [M.run_stays _ hle hhj]; exact hacc
    · rw [← M.run_stays _ hle hht]; exact hacc

/-- **Correctness of the reduction.** -/
theorem reduction_correct {L : Lang} {s : Nat → Nat} (hdec : M.Decides L) (hsp : M.SpaceBounded s)
    (w : List Bool) : L w ↔ TQBF (redQbf M (s w.length) w).encode := by
  have hall : ∀ j, Good M (s w.length) (M.run (initCfg k w) j) :=
    fun j => good_of M _ (inRange_run M (inRange_init M w) j) (hsp w j)
  rw [accepts_iff_bounded M (s w.length) hdec w hall]
  unfold TQBF
  rw [decode_encode, redQbf, redQF, QF.toQbf_value _ (topF_clean M _ _ _), topF_iff M _ _ _ hall]

end Top

end Complexity
