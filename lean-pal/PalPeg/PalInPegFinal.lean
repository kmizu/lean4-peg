import PalPeg.ScaWindowFast
import PalPeg.EvenLength

/-!
# `PalInPeg.unconditional` — `PAL ∈ PEG`

The target theorem, with no hypothesis: the palindromes over `{0, 1}` are recognized by a total PEG.

The route follows the emitted Scala window-pal pipeline (scaffold → SCA → PEG): the window
controller (`ScaWindowPal`) with the real table-compiled matcher and flag workers, their stack
encodings (`ScaWorkerEnc`), and Kim–Park's SCA → PEG construction. `ScaWindowFast.pal_in_peg_of_fast`
reduces everything to two step-count facts of the head programs, both discharged here from the
proven linear step bounds at the verified service quanta (`GsBatchClock.VERIFIED_BATCH`: matcher
2048, flags 32768):

* `startupFast_all`: the matcher's startup (`Decompose` and site 0) reaches site 3 within
  `1698·|x| + 230 ≤ 2013·|x| + 32·s + 2063` steps (`ScaMatcherStart.start_pre`);
* `flagsFast`: a flags job on `y` (`|y| = (r+1)·S ≤ 4S`) halts within `8098·|y| + 10 < 32768·S`
  steps (`ScaFlagsHead.flags_head_gs_palindromes`; the halting time is unique,
  `ScaFlagsLife.halt_unique`).
-/
set_option autoImplicit false
namespace PalPeg.PalInPeg
open PalPeg.ScaHeadVM PalPeg.ScaMatcherLoop PalPeg.ScaMatcherLifeSafe PalPeg.ScaWindowFast

/-- **The matcher's startup fits the verified matcher quantum**, for every nonempty pattern. -/
theorem startupFast_all (x : List (Fin 2)) (hx : ∃ j, 1 ≤ j ∧ x.length = 2 ^ j) :
    StartupFast x rho0 := by
  obtain ⟨j, hj, hlen⟩ := hx
  have hne : x ≠ [] := by
    intro h; rw [h] at hlen; have := Nat.two_pow_pos j; simp at hlen; omega
  obtain ⟨s, p, r, hdec⟩ : ∃ s p r, PalPeg.decompose x 8 = (s, p, r) := ⟨_, _, _, rfl⟩
  obtain ⟨hctl, hw, -, -, hO, hT⟩ := ScaMatcherStart.initial_facts x []
  simp only [List.foldl_nil] at hctl hw hO hT
  obtain ⟨n, π', hn, hrun, -⟩ :=
    ScaMatcherStart.start_pre hdec hne rho0_startOrient (matchInitial x ScaWorkerLink.startCtl)
      hctl hw hO hT
  refine ⟨n, π', ?_, ?_⟩
  · simp only [hdec]; omega
  · simp only [hdec]; exact hrun

/-- **Every flags job fits the verified flags quantum.** -/
theorem flagsFast : ScaFlagsJob.FlagsFast := by
  intro y i r hr hlen n w hrun hdone
  obtain ⟨n', w', hn', hrun', hdone', -⟩ := ScaFlagsHead.flags_head_gs_palindromes y
    (ScaFlagsJob.stageOK_bdec y) (r * 2 ^ i) ((r + 1) * 2 ^ i) (by rw [hlen])
  rw [ScaFlagsJob.iterFlags_eq] at hrun'
  have hrun'' : ScaFlagsLink.iterFlags n' (ScaFlagsLife.jobStart y (2 ^ i) r) = some w' := hrun'
  have heq : n = n' := (ScaFlagsLife.halt_unique hrun'' hdone' hrun).2 hdone
  subst heq
  have hS : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  have h4 : (r + 1) * 2 ^ i ≤ 4 * 2 ^ i := Nat.mul_le_mul_right _ (by omega)
  rw [hlen] at hn'
  omega

/-- **`PAL ∈ PEG`.** -/
theorem unconditional : PegSeparation.RecognizedByTotalPEG PalPeg.PAL :=
  pal_in_peg_of_fast startupFast_all flagsFast

/-- info: 'PalPeg.PalInPeg.unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unconditional

/-- **Loff–Moreira–Reis (2020), Conjecture 7, refuted**: the even-length palindromes
`{ w wᴿ | w ∈ {0,1}* }` are recognized by a total PEG (intersect `PAL` with the regular language of
even-length words; PEG languages are closed under intersection and contain the regular languages). -/
theorem evenPal_in_peg : PegSeparation.RecognizedByTotalPEG PalPeg.EvenPal :=
  PalPeg.evenPal_ww_reverse_of_pal unconditional

/-- info: 'PalPeg.PalInPeg.evenPal_in_peg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evenPal_in_peg

end PalPeg.PalInPeg
