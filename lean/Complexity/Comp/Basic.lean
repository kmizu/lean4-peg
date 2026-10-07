import Complexity.TM

/-!
# Decidable and computable by Turing machines (no time bound)

* `TMDecidable L`: some machine decides `L`.
* `TMComputable f`: some machine halts on every input in the accepting state with `f w` on tape `0`.
* `tmDecidable_compl`: swapping the accepting and the rejecting state decides the complement.
* `tmComputable_of_polyTime`: polynomial-time computable functions are computable.
-/

namespace Complexity

/-- Decided by some Turing machine (no time bound). -/
def TMDecidable (L : Lang) : Prop := ∃ (k : Nat) (M : TM k), M.Decides L

/-- Computed by some Turing machine that halts in the accepting state with the output on tape 0 (no time bound). -/
def TMComputable (f : List Bool → List Bool) : Prop :=
  ∃ (k : Nat) (h : 0 < k) (M : TM k), ∀ w, ∃ t, (M.run (initCfg k w) t).state = 0 ∧ OutputIs h (M.run (initCfg k w) t) (f w)

/-- Polynomial-time computable functions are computable: drop the time bound. -/
theorem tmComputable_of_polyTime {f : List Bool → List Bool} (h : PolyTimeComputable f) : TMComputable f := by
  obtain ⟨k, hk, M, _, _, hM⟩ := h
  exact ⟨k, hk, M, fun w => let ⟨t, _, h₁, h₂⟩ := hM w; ⟨t, h₁, h₂⟩⟩

/-! ## The complement -/

/-- Swap the states `0` and `1`. -/
def swapQ (q : Nat) : Nat := if q = 0 then 1 else if q = 1 then 0 else q

theorem swapQ_swapQ (q : Nat) : swapQ (swapQ q) = q := by
  unfold swapQ
  by_cases h0 : q = 0
  · simp [h0]
  · by_cases h1 : q = 1
    · simp [h1]
    · simp [h0, h1]

theorem swapQ_lt {q n : Nat} (hn : 3 ≤ n) (h : q < n) : swapQ q < n := by
  unfold swapQ; split
  · omega
  · split <;> omega

/-- The machine with the accepting and the rejecting state swapped. -/
def TM.swap {k : Nat} (M : TM k) : TM k where
  nq := M.nq
  na := M.na
  delta q r := let d := M.delta (swapQ q) r; (swapQ d.1, d.2)
  three_le_nq := M.three_le_nq
  three_le_na := M.three_le_na
  delta_state _ r hq hr := swapQ_lt M.three_le_nq (M.delta_state _ r (swapQ_lt M.three_le_nq hq) hr)
  delta_sym _ r hq hr i := M.delta_sym _ r (swapQ_lt M.three_le_nq hq) hr i

/-- A configuration with its state swapped. -/
def Cfg.swap {k : Nat} (c : Cfg k) : Cfg k := { c with state := swapQ c.state }

theorem Cfg.swap_halted {k : Nat} (c : Cfg k) : c.swap.halted ↔ c.halted := by
  unfold Cfg.halted Cfg.swap swapQ
  simp only
  split
  · omega
  · split <;> omega

theorem TM.swap_step {k : Nat} (M : TM k) (c : Cfg k) : M.swap.step c.swap = (M.step c).swap := by
  by_cases h : c.halted
  · rw [TM.step_halted _ ((Cfg.swap_halted c).2 h), TM.step_halted _ h]
  · have h' : ¬ c.swap.halted := fun e => h ((Cfg.swap_halted c).1 e)
    unfold TM.step
    rw [if_neg h, if_neg h']
    simp only [TM.swap, Cfg.swap, swapQ_swapQ]
    rfl

theorem TM.swap_run {k : Nat} (M : TM k) (c : Cfg k) : ∀ t, M.swap.run c.swap t = (M.run c t).swap
  | 0 => rfl
  | t + 1 => by
    show M.swap.step (M.swap.run c.swap t) = (M.step (M.run c t)).swap
    rw [TM.swap_run M c t, TM.swap_step]

theorem initCfg_swap (k : Nat) (w : List Bool) : (initCfg k w).swap = initCfg k w := rfl

/-- **Swapping the halting states decides the complement**, with the same number of tapes. -/
theorem TM.decides_compl {k : Nat} {M : TM k} {L : Lang} (h : M.Decides L) :
    ∃ M' : TM k, M'.Decides (fun w => ¬ L w) := by
  refine ⟨M.swap, fun w => ?_⟩
  obtain ⟨t, hh, hs⟩ := h w
  refine ⟨t, ?_, ?_⟩
  · rw [← initCfg_swap, TM.swap_run]; exact (Cfg.swap_halted _).2 hh
  · rw [← initCfg_swap, TM.swap_run]
    simp only [Cfg.swap]
    unfold Cfg.halted at hh
    rcases hh with e | e
    · rw [e]; simp [swapQ]; exact hs.1 e
    · rw [e]; simp [swapQ]; intro hl; have := hs.2 hl; omega

/-- **The complement of a decidable language is decidable.** -/
theorem tmDecidable_compl {L : Lang} (h : TMDecidable L) : TMDecidable (fun w => ¬ L w) := by
  obtain ⟨k, M, hM⟩ := h
  obtain ⟨M', hM'⟩ := TM.decides_compl hM
  exact ⟨k, M', hM'⟩

end Complexity
