import Complexity.ListClasses

/-!
# Deciding with a list program in bounded time

`lm_time`: a list program that, from `initLists w`, halts with the answer within `T |w|` steps while every list stays
below `s |w|` gives a machine that decides `L` and has halted after `4n + 8 + T n · (8 (s n + n + 2) + 20)` steps
(`initP`, then each list step costs `lcost` machine steps, `compile_exec`).
-/

namespace Complexity

variable {k : Nat}

/-- The machine-time bound for a list program with time `T` and list bound `s`. -/
def lmTime (s T : Nat → Nat) (n : Nat) : Nat := (4 * n + 8) + T n * (8 * (s n + (n + 2)) + 20)

theorem lm_time (h1 : 1 < k) (lp : LProg k) (E : Nat) (hE : 2 ≤ E) (hc : lp.ConstOK E) (L : Lang)
    (s T : Nat → Nat)
    (h : ∀ w, ∃ t b L', t ≤ T w.length ∧ LExec (LenOK (s w.length)) lp (initLists k w) t (.stop b L') ∧
      (b = true ↔ L w)) :
    ∃ M : TM k, M.Decides L ∧ ∀ w, (M.run (initCfg k w) (lmTime s T w.length)).halted := by
  let p : Prog k := .seq (initP h1) lp.compile
  have hsym : p.SymOK (E + 4) := ⟨initP_symOK h1 _ (by omega), compile_symOK E lp hc⟩
  let s' : Nat → Nat := fun n => s n + (n + 2)
  have hrun : ∀ w, ∃ t b τ, t ≤ lmTime s T w.length ∧
      Exec (TFits (s' w.length)) p (initTapes k w) t (.stop b τ) ∧ (b = true ↔ L w) := fun w => by
    obtain ⟨t, b, L', ht, hex, hb⟩ := h w
    obtain ⟨t₀, τ₀, ht₀, hex₀, hR₀⟩ := initP_spec h1 w
    have hQ : ∀ L₁ : Lists k, LenOK (s w.length) L₁ → LenOK (s' w.length) L₁ := fun _ hL => hL.mono (by simp [s'])
    obtain ⟨t', o', ht', hex', hr'⟩ := (compile_exec (B := s' w.length) hQ hex).1 τ₀ hR₀
    cases o' with
    | cont _ => exact hr'.elim
    | stop b' τ' =>
      obtain ⟨rfl, _⟩ := hr'
      refine ⟨t₀ + t', b, τ', ?_, Exec.seqC (hex₀.mono (fun _ ht => ht.mono (by simp [s']))) hex', hb⟩
      have : t * lcost (s' w.length) ≤ T w.length * (8 * (s w.length + (w.length + 2)) + 20) :=
        Nat.mul_le_mul ht (by simp [lcost, s'])
      simp only [lmTime]
      omega
  obtain ⟨hdec, _⟩ := p.decides_of_exec (E + 4) (by omega) hsym L s' (fun w => by
    obtain ⟨t, b, τ, _, hex, hb⟩ := hrun w
    exact ⟨t, b, τ, hex, hb⟩)
  refine ⟨p.machine (E + 4) (by omega) hsym, hdec, fun w => ?_⟩
  obtain ⟨t, b, τ, ht, hex, _⟩ := hrun w
  have hm := (p.machine_run (E + 4) (by omega) hsym hex).1
  have hh : ((p.machine (E + 4) (by omega) hsym).run (initCfg k w) t).halted := by
    rw [hm]; exact halted_of_stop b τ
  rw [TM.run_stays _ _ ht hh]
  exact hh

end Complexity
