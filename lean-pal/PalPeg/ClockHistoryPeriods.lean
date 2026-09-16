import PalPeg.ClockHistoryStartup

set_option autoImplicit false
namespace PalPeg.ClockHistoryPeriods
open PegSeparation.RealTimeTM PalPeg.Program
variable {k : ℕ} {Terminal : Type}

theorem no_power_between (g n : ℕ) (hl : 2 ^ g < n) (hh : n < 2 ^ (g + 1)) :
    ¬ ∃ j : ℕ, n = 2 ^ j := by
  rintro ⟨j, hj⟩
  by_cases h : j ≤ g
  · have := Nat.pow_le_pow_right (by decide : 0 < 2) h
    omega
  · have := Nat.pow_le_pow_right (by decide : 0 < 2) (show g + 1 ≤ j by omega)
    omega

theorem signal_quiet (g n : ℕ) (hg : 5 ≤ g) (hl : 2 ^ g < n) (hh : n < 2 ^ (g + 1)) :
    SlotClockBirth.startNow (SlotClockBirth.atTime n).state = false := by
  have h32 : 32 ≤ 2 ^ g := Nat.pow_le_pow_right (by decide : 0 < 2) hg
  cases he : SlotClockBirth.startNow (SlotClockBirth.atTime n).state with
  | false => rfl
  | true => exact False.elim (no_power_between g n hl hh
      ((SlotClockBirth.startNow_power n (by omega)).mp he))

theorem quiet_run (blank : Fin k) (enc : Terminal → Fin k) (g n : ℕ) (hg : 5 ≤ g)
    (w : List Terminal) (x : SConfig (ClockHistory.Core × Fin 33) (SlotClock.Symbol × Fin k) 12)
    (hp : x.state.2 = 0) (hc : ClockHistory.clock x = SlotClockBirth.atTime n)
    (hl : 2 ^ g < n) (hw : n + w.length ≤ 2 ^ (g + 1)) :
    ClockHistory.history (w.foldl (ClockHistory.machine blank enc).sRound x) =
      (w.map HistoryLoop.quiet).foldl (HistoryLoop.machine blank enc 32).sRound (ClockHistory.history x) := by
  induction w generalizing n x with
  | nil => rfl
  | cons a w ih =>
    have hh : n < 2 ^ (g + 1) := by simp only [List.length_cons] at hw; omega
    have hs : SlotClockBirth.startNow (ClockHistory.clock x).state = false := by
      rw [hc]
      exact signal_quiet g n hg hl hh
    have hc' : ClockHistory.clock ((ClockHistory.machine blank enc).sRound x a) =
        SlotClockBirth.atTime (n + 1) := by
      rw [ClockHistory.clock_round blank enc x hp a, hc, SlotClockBirth.at_succ]
    rw [List.foldl_cons, ih (n + 1) _ (ClockHistory.round_phase blank enc x hp a) hc'
      (by omega) (by simp only [List.length_cons] at hw; omega), ClockHistory.history_round, hs,
      List.map_cons, List.foldl_cons]
    rfl

/-- On every dyadic interval the actual clock supplies exactly the one
start bit expected by the proved history-loop block, on its first arrival. -/
theorem block_run (blank : Fin k) (enc : Terminal → Fin k) (g : ℕ) (hg : 5 ≤ g)
    (a : Terminal) (w : List Terminal)
    (x : SConfig (ClockHistory.Core × Fin 33) (SlotClock.Symbol × Fin k) 12)
    (hp : x.state.2 = 0) (hc : ClockHistory.clock x = SlotClockBirth.atTime (2 ^ g))
    (hw : (a :: w).length ≤ 2 ^ g) :
    ClockHistory.history ((a :: w).foldl (ClockHistory.machine blank enc).sRound x) =
      ((a, true) :: w.map HistoryLoop.quiet).foldl (HistoryLoop.machine blank enc 32).sRound
        (ClockHistory.history x) := by
  have h32 : 32 ≤ 2 ^ g := Nat.pow_le_pow_right (by decide : 0 < 2) hg
  have hs : SlotClockBirth.startNow (ClockHistory.clock x).state = true := by
    rw [hc, SlotClockBirth.startNow_power _ h32]
    exact ⟨g, rfl⟩
  have hc' : ClockHistory.clock ((ClockHistory.machine blank enc).sRound x a) =
      SlotClockBirth.atTime (2 ^ g + 1) := by
    rw [ClockHistory.clock_round blank enc x hp a, hc, SlotClockBirth.at_succ]
  rw [List.foldl_cons, quiet_run blank enc g (2 ^ g + 1) hg w _
    (ClockHistory.round_phase blank enc x hp a) hc' (by omega)
    (by rw [pow_succ]; simp only [List.length_cons] at hw; omega),
    ClockHistory.history_round, hs, List.foldl_cons]

/-- The clock-driven combined machine restores the cyclic history layout
within an eighth-length window, with no externally supplied start bits. -/
theorem block_layout (blank : Fin k) (enc : Terminal → Fin k) (g : ℕ) (hg : 5 ≤ g)
    (a : Terminal) (w : List Terminal) (u v : List (Fin k)) (hu : blank ∉ u) (hv : blank ∉ v)
    (x : SConfig (ClockHistory.Core × Fin 33) (SlotClock.Symbol × Fin k) 12)
    (hp : x.state.2 = 0) (hc : ClockHistory.clock x = SlotClockBirth.atTime (2 ^ g))
    (h : HistoryRotation.Layout blank (ClockHistory.history x).state.1 u v (ClockHistory.history x).tape)
    (hlen : u.length + v.length = 2 ^ g)
    (window : 2 ^ g / 8 ≤ (a :: w).length) (hw : (a :: w).length ≤ 2 ^ g) :
    let y := ClockHistory.history ((a :: w).foldl (ClockHistory.machine blank enc).sRound x)
    y.state.1 = HistoryRotation.roles.trans (ClockHistory.history x).state.1 ∧
      y.state.2 = (.inr (.inr (fun _ => 2)), 0) ∧
      HistoryRotation.Layout blank y.state.1 (u ++ v) ((a :: w).map enc) y.tape := by
  rw [block_run blank enc g hg a w x hp hc hw]
  have he : ClockHistory.history x = HistoryLoop.embed (ClockHistory.history x).state.1
      ⟨(ClockHistory.history x).state.2, (ClockHistory.history x).tape⟩ := rfl
  rw [he]
  apply HistoryLoop.block_by_eighth blank enc _ a w u v hu hv _ h
  · rw [hlen]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hg
  · simpa only [hlen] using window

/-- info: 'PalPeg.ClockHistoryPeriods.block_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms block_layout

end PalPeg.ClockHistoryPeriods
