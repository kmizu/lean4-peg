import PalPeg.ScaWindowReal
import PalPeg.ScaMatcherLifeSafe
import PalPeg.ScaFlagsJob

/-!
# `PAL ∈ PEG` from two step-count facts

The three promises of `ScaWindowReal.pal_in_peg_of_real_promises` are discharged from the head-VM
analysis of the real workers, except two statements about how many steps the head programs take:

* `StartupFast` (for every scheduled pattern length `2^j`, `j ≥ 1`): the matcher's startup
  (`Decompose` and site 0) reaches site 3 within `2013·|x| + 32·s + 2063` steps;
* `FlagsFast`: every flags job halts within `32768·S` steps.

The rest: the matcher lives are safe and a tick's output says whether a report ends at its letter
count (`ScaMatcherLifeSafe`), the reports are the occurrences (`ScaMatcherAnswer`), the answering
slot is the one born at `stageOf |w|` (`ScaMatcherLife2`), and the flags contract and no flags
fault follow from `FlagsFast` (`ScaFlagsJob`).
-/
set_option autoImplicit false
namespace PalPeg.ScaWindowFast
open PalPeg.ScaWindowPal PalPeg.ScaWindowInstance PalPeg.ScaWindowPlumbing PalPeg.ScaMatcherLife
  PalPeg.ScaMatcherLifeSafe

/-- The worker's ghost orientation at a matcher birth: `Origin` and the decomposition heads
reversed, everything else forward. -/
def rho0 (h : String) : Bool :=
  decide (h = "Origin" ∨ h = "Cut" ∨ h = "A" ∨ h = "P" ∨ h = "B" ∨ h = "KP" ∨ h = "First" ∨
    h = "KFirst" ∨ h = "Reach" ∨ h = "Second" ∨ h = "Walk")

theorem rho0_startOrient : ScaMatcherStart.StartOrient rho0 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩, by decide, by decide, by decide⟩

/-- `x` occurs as a suffix of the text after `S` letters iff it occurs as a suffix of the word,
when it fits. -/
theorem occursAt_drop {x w : List (Fin 2)} {S : ℕ} (hS : S ≤ w.length)
    (hx : x.length ≤ (w.drop S).length) :
    PalPeg.occursAt x (w.drop S) ↔ PalPeg.occursAt x w := by
  have hlen : (w.drop S).length = w.length - S := List.length_drop ..
  have key : (w.drop S).drop ((w.drop S).length - x.length) = w.drop (w.length - x.length) := by
    rw [List.drop_drop, hlen]; congr 1; omega
  unfold PalPeg.occursAt
  rw [key]
  constructor
  · rintro ⟨-, h⟩; exact ⟨by omega, h⟩
  · rintro ⟨-, h⟩; exact ⟨hx, h⟩

/-- The loop's reports, on the orbit's own indexing. -/
theorem rep_iff_orbit {x T : List (Fin 2)} {s p₁ r : ℕ} (hv : 0 < (x.drop s).length) (n : ℕ) :
    (∃ j, ScaMatcherTick.isRep x T s p₁ r j = true ∧ ScaMatcherTick.endOf x T s p₁ r j = n) ↔
      ∃ j, PalPeg.GSDrained.matchEvent (x.take s) (x.drop s)
          (PalPeg.GSDrained.orbit (x.take s) (x.drop s) 8 p₁ r T j) = true ∧
        (PalPeg.GSDrained.orbit (x.take s) (x.drop s) 8 p₁ r T j).1.pos + (x.drop s).length = n := by
  have hvl : (x.drop s).length = x.length - s := by simp
  constructor
  · rintro ⟨j, hr, he⟩
    refine ⟨j + 1, hr, ?_⟩
    rw [hvl]; exact he
  · rintro ⟨j, hm, he⟩
    cases j with
    | zero =>
      exfalso
      simp only [PalPeg.GSDrained.orbit, Function.iterate_zero, id, PalPeg.GSDrained.vInit,
        PalPeg.GSDrained.matchEvent, decide_eq_true_eq] at hm
      omega
    | succ j =>
      refine ⟨j, hm, ?_⟩
      unfold ScaMatcherTick.endOf
      rw [← hvl]; exact he

/-- **`PAL ∈ PEG`, given the two step-count facts.** -/
theorem pal_in_peg_of_fast
    (hstart : ∀ x : List (Fin 2), (∃ j, 1 ≤ j ∧ x.length = 2 ^ j) → StartupFast x rho0)
    (hflags : ScaFlagsJob.FlagsFast) :
    PegSeparation.RecognizedByTotalPEG PalPeg.PAL := by
  have hA := rho0_startOrient
  have hlives := scheduledLivesSafe'_of_startupFast hA hstart
  have hρ := startOrients_of hA
  refine ScaWindowReal.pal_in_peg_of_real_promises ?_
    (ScaFlagsJob.flagsContract_of_fast matcherOps matcherInit hflags)
    (fun w i => ⟨matcher_faulted_run' hρ hlives flagsOps flagsInit w i,
      ScaFlagsJob.flags_never_fault_of_fast matcherOps matcherInit hflags w i⟩)
  intro w hw
  obtain ⟨v0, v, hin, hout, -, -, houtput⟩ := answering_output' hρ hlives flagsOps flagsInit w hw
  rw [houtput]
  set S := PalPeg.stageOf w.length with hS
  set x := (w.take S).reverse with hxdef
  set T := w.drop S with hT
  have hspec := PalPeg.stageOf_spec (n := w.length) (by omega)
  have hS1 : 1 ≤ S := by
    obtain ⟨k, hk⟩ := PalPeg.stageOf_isPow w.length
    rw [hS, hk]; exact Nat.one_le_two_pow
  have hxlen : x.length = S := by
    rw [hxdef, List.length_reverse, List.length_take]; omega
  have hx : x ≠ [] := by intro h; rw [h] at hxlen; simp at hxlen; omega
  have hxpow : ∃ j, 1 ≤ j ∧ x.length = 2 ^ j := by
    refine ⟨Nat.log 2 w.length - 1, ?_, by rw [hxlen, hS, PalPeg.stageOf_pow]⟩
    have : 2 ≤ Nat.log 2 w.length := by
      have h4 : 2 ^ 2 ≤ w.length := by omega
      exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr h4
    omega
  obtain ⟨s, p, r, hdec⟩ : ∃ s p r, PalPeg.decompose x 8 = (s, p, r) := ⟨_, _, _, rfl⟩
  have hv := ScaMatcherAnswer.drop_length_pos hdec hx
  rw [tick_output_last hx hdec hA (hstart x hxpow) T hin hout, rep_iff_orbit hv,
    ScaMatcherAnswer.answer_iff_occursAt hdec hx T]
  apply occursAt_drop (by omega)
  rw [List.length_drop, hxlen]; omega

/-- info: 'PalPeg.ScaWindowFast.pal_in_peg_of_fast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pal_in_peg_of_fast

end PalPeg.ScaWindowFast
