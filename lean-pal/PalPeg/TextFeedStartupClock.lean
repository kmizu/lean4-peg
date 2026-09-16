import PalPeg.TextFeedPrepEndpoint

/-! Clock facts about startup are unconditional: even a suspended prep
loop returns to the same arrival phase after every complete frame. -/
set_option autoImplicit false

namespace PalPeg.TextFeedStartupClock
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist2
open PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.TextFeedStartupBank
open PalPeg.TextFeedStartupSchedule PalPeg.TextFeedPrepEndpoint

variable {k : ℕ} {Terminal : Type}
noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem stateBefore_boundary (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate : ℕ) (c : CallCtrl (programs e) (Outer e leftSym R rate))
    (T : Fin 27 → STape (Fin k)) (hc : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩) (word : List Terminal) :
    let z := stateBefore e leftSym enc R rate c T word
    z.state.1.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩ ∧
      z.state.1.2 = ⟨0, by omega⟩ ∧ z.state.2 = ⟨0, by omega⟩ := by
  induction word generalizing c T with
  | nil => exact ⟨hc, rfl, rfl⟩
  | cons a word ih =>
    let x := (run (Terminal := Terminal) e leftSym R rate)^[R + 1]
      (c, arriveA e.blank (capture enc) (some a) T)
    have hc' : x.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩ := by
      rw [run_counter_iterate, hc, nextPhase_iterate_round]
    have hh := ih x.1 x.2 hc'
    simpa only [stateBefore, List.foldl_cons, machine_round] using hh

theorem prefixRun_counter (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate : ℕ) (c : CallCtrl (programs e) (Outer e leftSym R rate))
    (T : Fin 27 → STape (Fin k)) (hc : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    (word : List Terminal) (a : Terminal) (N : ℕ) :
    (prefixRun e leftSym enc R rate c T word a N).1.1.1 =
      nextPhase^[N] ⟨0, Nat.zero_lt_succ R⟩ := by
  rw [prefixRun, run_counter_iterate]
  exact congrArg (nextPhase^[N]) (stateBefore_boundary e leftSym enc R rate c T hc word).1

/-- The remaining calls are exactly the tail of the same real frame,
not a fresh clock window inserted between two arrivals. -/
theorem finish_prefix (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate J : ℕ) (hJ : J < R) (c : CallCtrl (programs e) (Outer e leftSym R rate))
    (T : Fin 27 → STape (Fin k)) (hc : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    (word : List Terminal) (a : Terminal) :
    let x := (run (Terminal := Terminal) e leftSym R rate)^[R - J - 1]
      (prefixRun e leftSym enc R rate c T word a (J + 2))
    stateBefore e leftSym enc R rate c T (word ++ [a]) =
      { state := ((x.1, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := x.2 } := by
  let z := stateBefore e leftSym enc R rate c T word
  obtain ⟨_, hlocal, hglobal⟩ := stateBefore_boundary e leftSym enc R rate c T hc word
  have hz : { state := ((z.state.1.1, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := z.tape } = z := by
    have hh : z.state = ((z.state.1.1, ⟨0, by omega⟩), ⟨0, by omega⟩) :=
      Prod.ext (Prod.ext rfl hlocal) hglobal
    rw [← hh]
  have hnext : stateBefore e leftSym enc R rate c T (word ++ [a]) =
      (machine e leftSym enc R rate).sRound z a := by
    simp only [stateBefore, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rfl
  rw [hnext, ← hz, machine_round]
  dsimp only [prefixRun]
  rw [← Function.iterate_add_apply,
    show R - J - 1 + (J + 2) = R + 1 by omega]

/-- info: 'PalPeg.TextFeedStartupClock.finish_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finish_prefix

end PalPeg.TextFeedStartupClock
