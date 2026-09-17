import PalPeg.CloseoutTerminalBreak
import PalPeg.CloseoutWatchRound2

/-!
# `TerminalN`: the fifth exit, and the wiring

`CloseoutTerminalBreak` settled where `roundStepC_of_align`'s terminal-match
case goes: the chain **breaks** there (the spec's `matchedPlace()` keeps
scanning and `ScaffoldChain.matched()`'s `consume()` fails), so the round
structure stops because the chain is no longer watching — an exit
`CloseoutWatchRound.TerminalC` simply does not list.

`TerminalN` adds it.  `BrokeEndN` is the missing disjunct, stated the same way
`BreakEndC` states the mismatch exit: a watch segment to a clock-`1` landing,
there a **matched** comparison at the round's **terminal**.  Nothing about the
input is assumed — `terminal_match_breaks` shows the chain breaks at exactly
such a landing.

`roundStepC_of_alignN` is then `roundStepC_of_align` with

* `MatchTickC` (refuted) replaced by `MatchTickN` (proved from the round datum,
  `CloseoutMatchTickN.matchTickN_of_round`), and
* the matched branch split on `singlePositive s1.cycle`.

So `RoundDataC`'s residue is discharged: no leaf is added, one refuted leaf is
replaced by a proved one, and the exit that was missing is supplied.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutTerminalN

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton
open PalPeg.GalilTickFun (ChainReady)
open PalPeg.CloseoutWatchRun
open PalPeg.CloseoutWatchRound
open PalPeg.CloseoutWatchRound2
open PalPeg.CloseoutMatchTickN PalPeg.CloseoutTerminalBreak

/-- **(NAMED) the fifth exit.**  A watch segment to a clock-`1` landing whose
comparison *matches* at the round's terminal — where
`CloseoutTerminalBreak.terminal_match_breaks` says the chain breaks. -/
def BrokeEndN (P : Shared) (q : ℕ) (first : Fin 9) (c : Control) (s : GalilVM) : Prop :=
  ∃ (c1 : Control) (s1 : GalilVM),
    WatchSeg P q first 2048 c s c1 s1 ∧ c1.clock = 1 ∧ LiveScanWatch c1 s1 ∧
      read (GalilScaffoldInputHead.left s1.left) = read (right s1.right) ∧
      singlePositive s1.cycle = true

/-- **`TerminalC` with the fifth exit.** -/
def TerminalN (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (Prep : Control → GalilVM → Prop) (c : Control) (s : GalilVM) : Prop :=
  LiveScanWatch c s ∧ Prep c s ∧
    (roundFuel h s = 0 ∨ shiftGuardVM s ∨ ¬ canRight s.right ∨
      BreakEndC P q first c s ∨ BrokeEndN P q first c s)

/-- `TerminalC` is one of `TerminalN`'s cases. -/
theorem terminalN_of_C {P : Shared} {q : ℕ} {first : Fin 9} {h : ℕ}
    {Prep : Control → GalilVM → Prop} {c : Control} {s : GalilVM}
    (hT : TerminalC P q first h Prep c s) :
    TerminalN P q first h Prep c s := by
  obtain ⟨hL, hP, hx⟩ := hT
  refine ⟨hL, hP, ?_⟩
  rcases hx with h1 | h2 | h3 | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))

/-- **`roundStepC_of_align` over the reformulated `MatchTickN` and the
five-exit `TerminalN`.**  The body is `CloseoutWatchRound2.roundStepC_of_align`
verbatim; the only changes are the four `TerminalC` exits re-tagged for
`TerminalN`, and the matched branch split on `singlePositive s1.cycle`: the
non-terminal half feeds `MatchTickN`, the terminal half takes the fifth exit
(where `CloseoutTerminalBreak.terminal_match_breaks` says the chain breaks). -/
theorem roundStepC_of_alignN (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (halign : MatchTickN raw)
    (hland : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s → LandingReadyC s)
    (c : Control) (s : GalilVM) (hL : LiveScanWatch c s) :
    RoundStepC P q first (roundFuel h) (TerminalN P q first h TrivPrep) c s := by
  classical
  obtain ⟨hm, hr, hclk, w, hw⟩ := hL
  have hL' : LiveScanWatch c s := ⟨hm, hr, hclk, w, hw⟩
  obtain ⟨hav, hrd, hnn⟩ := hland c s hL'
  by_cases hfuel : roundFuel h s = 0
  · exact Or.inl ⟨hL', trivial, Or.inl hfuel⟩
  have hd0 : 0 ≤ value w.machine.control.distance := hnn w hw
  have hbound : (value w.machine.control.distance).toNat < 4 * h + 1 := by
    have he : roundFuel h s = (4 * h + 1) - (value w.machine.control.distance).toNat := by
      simp only [roundFuel, hw]
    omega
  have hne : s.chain ≠ ChainVM.idle := by rw [hw]; intro h0; cases h0
  obtain ⟨k, hk⟩ : ∃ k, c.clock = k + 1 := ⟨c.clock - 1, by omega⟩
  obtain ⟨s1, hseg1, hne1, hrd1, hQ1, hl1, hr1, hC1, hrep1⟩ :=
    watchSeg_countdown P q first 2048 hready
      (fun x => ∃ w' : GalilScaffoldChainWatch.State, x = ChainVM.watch w' ∧
        value w.machine.control.distance ≤ value w'.machine.control.distance)
      (by
        intro x z hx ht
        obtain ⟨w', hxe, hle⟩ := hx
        subst hxe
        obtain ⟨w'', hze, hle2⟩ := distance_mono_false ht
        exact ⟨w'', hze, le_trans hle hle2⟩)
      k c s hm hr hk hav hne hrd ⟨w, hw, le_refl _⟩
  obtain ⟨w1, hw1, hdle⟩ := hQ1
  have hav1 : canRight s1.right := by rw [hr1]; exact hav
  have hL1 : LiveScanWatch {c with clock := 1} s1 := ⟨hm, hr, by simp, ⟨w1, hw1⟩⟩
  by_cases hmm : read (left s1.left) = read (right s1.right)
  · by_cases hterm : singlePositive s1.cycle = true
    · exact Or.inl ⟨hL', trivial,
        Or.inr (Or.inr (Or.inr (Or.inr
          ⟨{c with clock := 1}, s1, hseg1, rfl, hL1, hmm, hterm⟩)))⟩
    have hne0 : singlePositive s1.cycle = false := by
      cases hq0 : singlePositive s1.cycle with
      | false => rfl
      | true => exact absurd hq0 hterm
    obtain ⟨hz, hg⟩ := halign s1 w1 hw1 hav1 hmm hne0
    obtain ⟨htick0, hdist⟩ := watchTick_immediate hz hg
    have htick : ChainTick true s1.chain
        (ChainVM.watch (GalilScaffoldChainWatch.immediate w1)) := by
      rw [hw1]; exact htick0
    have hq : searchEffect P true s1 (searchLens.get s1) := Or.inr ⟨hne1, rfl⟩
    obtain ⟨o, hseg2⟩ :=
      watchSeg_matchStep P q first 2048 ({c with clock := 1} : Control) s1 hm hr rfl
        hav1 hne1 _ htick hmm _ hq
    have huch : (afterCompare s1 ⟨left s1.left, right s1.right,
        ChainVM.watch (GalilScaffoldChainWatch.immediate w1)⟩ (searchLens.get s1)).chain
        = ChainVM.watch (GalilScaffoldChainWatch.immediate w1) := rfl
    have hLu : LiveScanWatch
        ({c with clock := 2048, output := o, replaying := false} : Control)
        (afterCompare s1 ⟨left s1.left, right s1.right,
          ChainVM.watch (GalilScaffoldChainWatch.immediate w1)⟩ (searchLens.get s1)) :=
      ⟨hm, rfl, by simp, ⟨_, huch⟩⟩
    have hfu : roundFuel h (afterCompare s1 ⟨left s1.left, right s1.right,
          ChainVM.watch (GalilScaffoldChainWatch.immediate w1)⟩ (searchLens.get s1))
        < roundFuel h s := by
      have e1 : roundFuel h (afterCompare s1 ⟨left s1.left, right s1.right,
            ChainVM.watch (GalilScaffoldChainWatch.immediate w1)⟩ (searchLens.get s1))
          = (4 * h + 1) -
            (value (GalilScaffoldChainWatch.immediate w1).machine.control.distance).toNat := by
        simp only [roundFuel, huch]
      have e2 : roundFuel h s = (4 * h + 1) - (value w.machine.control.distance).toNat := by
        simp only [roundFuel, hw]
      rw [e1, e2, hdist]
      omega
    refine Or.inr ⟨{c with clock := 2048, output := o, replaying := false}, _, ?_, hLu, hfu⟩
    revert hseg2
    cases c with
    | mk mode clock output replaying odd pair =>
      intro hseg2
      exact watchSeg_append hseg1 hseg2
  · exact Or.inl ⟨hL', trivial,
      Or.inr (Or.inr (Or.inr (Or.inl
        ⟨{c with clock := 1}, s1, hseg1, rfl, hL1, hmm⟩)))⟩

#print axioms terminalN_of_C
#print axioms roundStepC_of_alignN

end PalPeg.CloseoutTerminalN
