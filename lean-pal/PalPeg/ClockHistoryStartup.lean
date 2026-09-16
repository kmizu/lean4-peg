import PalPeg.ClockHistory
import PalPeg.ProgramWarmStart

set_option autoImplicit false
set_option maxRecDepth 2048
namespace PalPeg.ClockHistoryStartup
open PegSeparation.RealTimeTM PalPeg.Program
open PalPeg.ClockRecycleMachine (mapTape map_action)
variable {k : ℕ} {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]

abbrev Symbol (k : ℕ) := SlotClock.Symbol × Fin k
abbrev Inner := ClockHistory.Core × Fin 33
local instance : DecidableEq Inner := inferInstance

/-- Reserve one blank cell to the left of each history head. Clock heads
stay at their true initial positions. The cached first arrival follows. -/
def setup (σ : Fin 12 → Symbol k) (j : Fin 12) : Symbol k × Move :=
  match (finSumFinEquiv.symm j : Fin 8 ⊕ Fin 4) with
  | .inl _ => (σ j, .stay)
  | .inr _ => (σ j, .right)

def machine (blank : Fin k) (enc : Terminal → Fin k) :=
  WarmStart.machine (ClockHistory.machine blank enc) setup

/-- A proof-side description of the real state after the one-time setup
action; the startup theorem below obtains it from all-blank tapes. -/
def seed (blank : Fin k) (enc : Terminal → Fin k) : SConfig Inner (Symbol k) 12 :=
  ⟨(ClockHistory.machine blank enc).initial,
    WarmStart.initTapes (ClockHistory.machine blank enc) setup
      (ClockHistory.machine blank enc).sInit.tape⟩

theorem seed_clock_tape (blank : Fin k) (enc : Terminal → Fin k) (j : Fin 8) :
    (seed blank enc).tape (ClockHistory.clockAddr j) = ⟨[], (.blank, blank), []⟩ := by
  simp only [seed, WarmStart.initTapes, StructuredMachine.sInit, setup,
    ClockHistory.clockAddr, Equiv.symm_apply_apply]
  rfl

theorem seed_history_tape (blank : Fin k) (enc : Terminal → Fin k) (j : Fin 4) :
    (seed blank enc).tape (ClockHistory.historyAddr j) =
      ⟨[(.blank, blank)], (.blank, blank), []⟩ := by
  simp only [seed, WarmStart.initTapes, StructuredMachine.sInit, setup,
    ClockHistory.historyAddr, Equiv.symm_apply_apply]
  rfl

theorem seed_clock (blank : Fin k) (enc : Terminal → Fin k) :
    ClockHistory.clock (seed blank enc) = SlotClockBirth.machine.sInit := by
  unfold ClockHistory.clock
  congr 1
  funext j
  rw [seed_clock_tape]
  rfl

theorem seed_layout (blank : Fin k) (enc : Terminal → Fin k) :
    HistoryRotation.Layout blank (Equiv.refl _) [] [] (ClockHistory.history (seed blank enc)).tape := by
  have ht (j : Fin 4) : (ClockHistory.history (seed blank enc)).tape j = ⟨[blank], blank, []⟩ := by
    change mapTape Prod.snd ((seed blank enc).tape (ClockHistory.historyAddr j)) = _
    rw [seed_history_tape]
    rfl
  unfold HistoryRotation.Layout
  simp only [Equiv.refl_apply, ht]
  exact ⟨STape.BlankEq.refl _ _, STape.BlankEq.refl _ _,
    STape.BlankEq.refl _ _, STape.BlankEq.refl _ _⟩

/-- All input symbols are processed from the correctly initialized tapes;
the first input is included in this exact run equality. -/
theorem from_blank (blank : Fin k) (enc : Terminal → Fin k) (a : Terminal) (w : List Terminal) :
    WarmStart.view ((machine blank enc).srun (a :: w)) =
      (a :: w).foldl (ClockHistory.machine blank enc).sRound (seed blank enc) :=
  WarmStart.from_blank (ClockHistory.machine blank enc) setup a w

/-- Startup costs one internal tick per arrival, not one input arrival.
The concrete clock therefore still sees exactly the original input count. -/
theorem clock_from_blank (blank : Fin k) (enc : Terminal → Fin k) (w : List Terminal) :
    ClockHistory.clock (WarmStart.view ((machine blank enc).srun w)) = SlotClockBirth.atTime w.length := by
  cases w with
  | nil => rfl
  | cons a w =>
    rw [from_blank, ClockHistory.clock_rounds blank enc (a :: w) (seed blank enc) rfl, seed_clock]
    rfl

theorem trigger_from_blank (blank : Fin k) (enc : Terminal → Fin k) (w : List Terminal)
    (hw : 32 ≤ w.length) :
    SlotClockBirth.startNow (ClockHistory.clock (WarmStart.view ((machine blank enc).srun w))).state = true ↔
      ∃ g : ℕ, w.length = 2 ^ g := by
  rw [clock_from_blank]
  exact SlotClockBirth.startNow_power w.length hw

theorem quiet_history (blank : Fin k) (enc : Terminal → Fin k) (n : ℕ) (w : List Terminal)
    (x : SConfig Inner (Symbol k) 12) (hp : x.state.2 = 0)
    (hc : ClockHistory.clock x = SlotClockBirth.atTime n) (hw : n + w.length ≤ 32) :
    ClockHistory.history (w.foldl (ClockHistory.machine blank enc).sRound x) =
      (w.map HistoryLoop.quiet).foldl (HistoryLoop.machine blank enc 32).sRound (ClockHistory.history x) := by
  induction w generalizing n x with
  | nil => rfl
  | cons a w ih =>
    have hn : n < 32 := by simp only [List.length_cons] at hw; omega
    have hs : SlotClockBirth.startNow (ClockHistory.clock x).state = false := by
      rw [hc]
      exact SlotClockBirth.startNow_early ⟨n, hn⟩
    have hc' : ClockHistory.clock ((ClockHistory.machine blank enc).sRound x a) =
        SlotClockBirth.atTime (n + 1) := by
      rw [ClockHistory.clock_round blank enc x hp a, hc, SlotClockBirth.at_succ]
    rw [List.foldl_cons, ih (n + 1) _ (ClockHistory.round_phase blank enc x hp a) hc'
      (by simp only [List.length_cons] at hw; omega), ClockHistory.history_round, hs]
    rw [List.map_cons, List.foldl_cons]
    rfl

/-- The first 32 arrivals produce the actual base case for all later
history cycles, not merely a correctly shaped hypothetical initial state. -/
theorem startup_layout (blank : Fin k) (enc : Terminal → Fin k) (w : List Terminal)
    (hw : w.length = 32) :
    HistoryRotation.Layout blank (Equiv.refl _) [] (w.map enc)
      (ClockHistory.history (WarmStart.view ((machine blank enc).srun w))).tape := by
  have hnon : w ≠ [] := by intro h; subst w; simp at hw
  have hrun : WarmStart.view ((machine blank enc).srun w) =
      w.foldl (ClockHistory.machine blank enc).sRound (seed blank enc) := by
    cases w with
    | nil => contradiction
    | cons a w => exact from_blank blank enc a w
  rw [hrun, quiet_history blank enc 0 w (seed blank enc) rfl (seed_clock blank enc) (by omega)]
  let T := (ClockHistory.history (seed blank enc)).tape
  have ht (j : Fin 4) : T j = ⟨[blank], blank, []⟩ := by
    change mapTape Prod.snd ((seed blank enc).tape (ClockHistory.historyAddr j)) = _
    rw [seed_history_tape]
    rfl
  have he : ClockHistory.history (seed blank enc) =
      HistoryLoop.embed (Equiv.refl _) (⟨(.inl 0, 0), T⟩ : SConfig (HistoryLoop.Inner 32) (Fin k) 4) := rfl
  rw [he, HistoryLoop.run_quiet]
  have hp := HistoryNextInput.prepared blank enc 32 w [] [] (by simp) (by simp) [blank] T
    (ht 0) (ht 1) (ht 2) (ht 3) (by simp [hw])
  change HistoryRotation.Layout blank (Equiv.refl _) [] (w.map enc)
    (w.foldl (HistoryNextInput.machine blank enc 32).sRound ⟨(.inl 0, 0), T⟩).tape
  refine ⟨hp.2.2.2.1, hp.2.2.2.2, hp.2.1, ?_⟩
  rw [Equiv.refl_apply, hp.2.2.1]
  exact STape.BlankEq.refl _ _

theorem startup_role (blank : Fin k) (enc : Terminal → Fin k) (w : List Terminal)
    (hw : w.length = 32) :
    (ClockHistory.history (WarmStart.view ((machine blank enc).srun w))).state.1 = Equiv.refl _ := by
  cases w with
  | nil => simp at hw
  | cons a w =>
    rw [from_blank, quiet_history blank enc 0 (a :: w) (seed blank enc) rfl
      (seed_clock blank enc) (by omega)]
    have he : ClockHistory.history (seed blank enc) =
        HistoryLoop.embed (Equiv.refl _)
          ⟨(.inl 0, 0), (ClockHistory.history (seed blank enc)).tape⟩ := rfl
    rw [he, HistoryLoop.run_quiet]
    rfl

/-- info: 'PalPeg.ClockHistoryStartup.startup_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms startup_layout

/-- info: 'PalPeg.ClockHistoryStartup.from_blank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms from_blank

/-- info: 'PalPeg.ClockHistoryStartup.trigger_from_blank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trigger_from_blank

end PalPeg.ClockHistoryStartup
