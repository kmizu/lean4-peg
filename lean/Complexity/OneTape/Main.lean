import Complexity.OneTape.Macro

/-!
# Every language decided by a `k`-tape machine is decided by a one-tape machine

The simulator `sim M` first marks cell `0` (`init_good`), then does one macro-step per step of `M`
(`macro_step`). By induction on the steps of `M` (`sim_tracks`): while `M` runs, the simulator reaches a
configuration at the start of the macro-step for `M`'s current configuration; once `M` has halted, the simulator
reaches a configuration in `M`'s halting state. So the simulator halts on every input, in the accepting state
exactly when `M` does (`oneTape_decides`).
-/

namespace Complexity
namespace OneTape

variable {k : Nat} (M : TM k)

/-- The input symbol at cell `j`. -/
def raw (w : List Bool) (j : Nat) : Nat := (initCfg 1 w).cells 0 j

theorem raw_lt (w : List Bool) (j : Nat) : raw w j < 3 := by
  simp only [raw, initCfg]
  split
  · split
    · rename_i b _; cases b <;> simp [bitSym]
    · omega
  · omega

theorem initCfg_cells (w : List Bool) (i : Fin k) (j : Nat) :
    (initCfg k w).cells i j = if i.val = 0 then raw w j else 0 := rfl

/-- **The start**: after its first step the simulator is at the start of the macro-step for `M`'s initial
configuration. -/
theorem init_good (w : List Bool) : Good M (initCfg k w) ((sim M).run (initCfg 1 w) 1) := by
  have h := step_init M (sc := initCfg 1 w) rfl (raw_lt w 0)
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨upd (raw w) 0 (initSym M (raw w 0)), ?_, h1, h2, h3⟩
  intro j
  by_cases hj : j = 0
  · subst hj
    rw [upd_eq]
    refine ⟨initSym_lt M (raw_lt w 0), by simp [clft_initSym], fun i => ?_⟩
    rw [cdig_initSym M (raw_lt w 0), initCfg_cells]
    have : flag (initCfg k w).pos i 0 = 1 := by simp [flag, initCfg]
    rw [this]
    split <;> omega
  · rw [upd_ne _ _ hj]
    refine ⟨raw_lt_NA M (raw_lt w j), by simp [clft_raw (raw_lt w j), hj], fun i => ?_⟩
    rw [cdig_raw M (raw_lt w j), initCfg_cells]
    have : flag (initCfg k w).pos i j = 0 := by simp [flag, initCfg]; omega
    rw [this]
    split <;> omega

/-- **The simulation**: at every time `t` of `M`, the simulator either is at the start of the macro-step for `M`'s
configuration (while `M` runs), or has reached `M`'s state (once `M` has halted). -/
theorem sim_tracks (w : List Bool) : ∀ t,
    (¬ (M.run (initCfg k w) t).halted ∧ ∃ n, Good M (M.run (initCfg k w) t) ((sim M).run (initCfg 1 w) n)) ∨
    ((M.run (initCfg k w) t).halted ∧ ∃ n, ((sim M).run (initCfg 1 w) n).state = (M.run (initCfg k w) t).state)
  | 0 => Or.inl ⟨by simp [Cfg.halted, initCfg, TM.run], 1, init_good M w⟩
  | t + 1 => by
    rcases sim_tracks w t with ⟨hn, n, hg⟩ | ⟨hh, n, hs⟩
    · have hr := frun_rep M w t
      obtain ⟨m, hm⟩ := macro_step M hr.qlt hr.sym hn _ hg
      rw [← TM.run_add] at hm
      rcases hm with ⟨hh, hs⟩ | ⟨hh, hg'⟩
      · exact Or.inr ⟨hh, n + m, hs⟩
      · exact Or.inl ⟨hh, n + m, hg'⟩
    · have e : M.run (initCfg k w) (t + 1) = M.run (initCfg k w) t := TM.step_halted M hh
      rw [e]
      exact Or.inr ⟨hh, n, hs⟩

/-- **Every language decided by a `k`-tape Turing machine is decided by a one-tape Turing machine.** -/
theorem oneTape_decides' (L : Lang) (h : M.Decides L) : (sim M).Decides L := by
  intro w
  obtain ⟨t, hh, hL⟩ := h w
  rcases sim_tracks M w t with ⟨hn, _⟩ | ⟨_, n, hs⟩
  · exact absurd hh hn
  · refine ⟨n, ?_, ?_⟩
    · unfold Cfg.halted; rw [hs]; exact hh
    · rw [hs]; exact hL

end OneTape

/-- **Every language decided by a `k`-tape Turing machine is decided by a one-tape Turing machine.** -/
theorem oneTape_decides {k : Nat} (M : TM k) (L : Lang) (h : M.Decides L) : ∃ M₁ : TM 1, M₁.Decides L :=
  ⟨OneTape.sim M, OneTape.oneTape_decides' M L h⟩

end Complexity
