import PalPeg.ScaFlagsLife
import PalPeg.ScaFlagsHead
import PalPeg.GSDecomposeL1

/-!
# The per-job promise of the flag workers, from the flags head program

`ScaFlagsLife.flagsContract` needs `JobHalts y (2^i) r` for every word `y` of length
`(r+1)·2^i`, `r < 4`: `DualFlagVM(y, rS, (r+1)S)` halts after `N < 32768·S` steps with the job's
bits. `ScaFlagsHead.flags_head_gs_palindromes` runs the flags head program to a halt with the
palindrome bits of the prefixes of lengths `up - 1` down to `lo`, in at most `8098·|y| + 10`
steps, given `StageOK` for the program's own decomposition at every stage.

* **The bits** (`flags_bits`): `lensDown (rS) ((r+1)S)` lists the lengths `(r+1)S - 1, …, rS`, so
  the halted VM's flags, reversed, are `segBits y S r`.
* **The stages** (`stageOK_bdec`): for `L ≤ |y|`, the program's decomposition `bdec y gsDec8 L`
  (the stand-in period `L - s + 1` when there is none) is `GSDecomposeL1.gsDecN y 8 L`, whose
  `StageOK` is `GSDecomposeL1.decOK_normalized`.
* **The budget** is not implied by `8098·|y| + 10` (`|y|` is up to `4S`). It is kept as one
  hypothesis, `FlagsFast`: every halting run of a job VM takes fewer than `32768·S` steps.
  `iterFlags` is deterministic, so this is a statement about the job's unique halting time.

`jobHalts_of_fast`: `FlagsFast → ∀ y i r, … → JobHalts y (2^i) r`, and the flag workers' promise
and their freedom from faults follow (`flagsContract_of_fast`, `flags_never_fault_of_fast`).
-/

set_option autoImplicit false

namespace PalPeg.ScaFlagsJob

open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWorkerCoroutine PalPeg.ScaHeadVM
  PalPeg.ScaFlagsLink PalPeg.ScaFlagsLife PalPeg.ScaWindowInstance PalPeg.ScaWindowPal
  PalPeg.ScaWindowPlumbing

/-- `ScaFlagsHead.iterFlags` is `ScaFlagsLink.iterFlags` (the same recursion). -/
theorem iterFlags_eq (n : ℕ) (v : HVM) : ScaFlagsHead.iterFlags n v = ScaFlagsLink.iterFlags n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [ScaFlagsHead.iterFlags, ScaFlagsLink.iterFlags]
    cases stepFlags v with
    | none => rfl
    | some w => simp only [Option.bind_some, ih]

/-! ## The stages -/

/-- On stages inside the word, the program's decomposition is the normalized `decompose`. -/
theorem bdec_eq_gsDecN (y : List (Fin 2)) {L : ℕ} (hL : L ≤ y.length) :
    ScaFlagsHead.bdec y ScaFlagsHead.gsDec8 L = GSDecomposeL1.gsDecN y 8 L := by
  unfold ScaFlagsHead.bdec GSDecomposeL1.gsDecN ScaFlagsHead.gsDec8
  split_ifs with h
  · rw [List.length_drop, List.length_take, Nat.min_eq_left hL]
  · rfl

/-- **`StageOK` for the program's own decomposition**, at every stage. -/
theorem stageOK_bdec (y : List (Fin 2)) :
    ∀ L, 1 ≤ L → L ≤ y.length →
      StageOK y 8 L (ScaFlagsHead.bdec y ScaFlagsHead.gsDec8 L).1
        (ScaFlagsHead.bdec y ScaFlagsHead.gsDec8 L).2.1
        (ScaFlagsHead.bdec y ScaFlagsHead.gsDec8 L).2.2 := by
  intro L h1 h2
  rw [bdec_eq_gsDecN y h2]
  exact GSDecomposeL1.decOK_normalized y L h1

/-! ## The bits -/

theorem lensDown_reverse (lo : ℕ) :
    ∀ n, (BorderJobHead.lensDown lo (lo + n)).reverse = (List.range n).map (lo + ·)
  | 0 => by rw [Nat.add_zero, BorderJobHead.lensDown_of_le le_rfl]; rfl
  | n + 1 => by
    rw [show lo + (n + 1) = (lo + n) + 1 by omega, BorderJobHead.lensDown,
      if_neg (by omega), List.reverse_cons, lensDown_reverse lo n, List.range_succ, List.map_append]
    rfl

theorem decide_isPal (x : List (Fin 2)) : decide (IsPal x) = (x.reverse == x) := by
  apply Bool.eq_iff_iff.mpr
  simp [IsPal]

/-- **The bits**: the halted VM's flags (descending lengths), reversed, are `segBits`. -/
theorem flags_bits (y : List (Fin 2)) (S r : ℕ) {w : HVM}
    (h : w.flags = (BorderJobHead.lensDown (r * S) ((r + 1) * S)).map
      (fun m => decide (IsPal (y.take m)))) :
    w.flags.reverse = segBits y S r := by
  rw [h, ← List.map_reverse, show (r + 1) * S = r * S + S by ring, lensDown_reverse,
    List.map_map]
  unfold segBits
  apply List.map_congr_left
  intro i _
  exact decide_isPal _

/-! ## The budget, and the promise -/

/-- **The step budget of the flags jobs**: every halting run of the job VM on a word of length
`(r+1)·2^i` (`r < 4`) takes fewer than `32768·2^i` steps. -/
def FlagsFast : Prop :=
  ∀ (y : List (Fin 2)) (i r : ℕ), r < 4 → y.length = (r + 1) * 2 ^ i →
    ∀ n w, ScaFlagsLink.iterFlags n (jobStart y (2 ^ i) r) = some w → w.flagsDone →
      n < 32768 * 2 ^ i

/-- **The per-job promise from the step budget.** -/
theorem jobHalts_of_fast (hfast : FlagsFast) :
    ∀ (y : List (Fin 2)) (i r : ℕ), r < 4 → y.length = (r + 1) * 2 ^ i → JobHalts y (2 ^ i) r := by
  intro y i r hr hlen
  obtain ⟨n, w, -, hrun, hdone, hflags⟩ := ScaFlagsHead.flags_head_gs_palindromes y
    (stageOK_bdec y) (r * 2 ^ i) ((r + 1) * 2 ^ i) (by rw [hlen])
  rw [iterFlags_eq] at hrun
  have hrun' : ScaFlagsLink.iterFlags n (jobStart y (2 ^ i) r) = some w := hrun
  exact ⟨n, w, hfast y i r hr hlen n w hrun' hdone, hrun', hdone, flags_bits y (2 ^ i) r hflags⟩

/-- **The flag workers' promise**, from the step budget alone. -/
theorem flagsContract_of_fast {Wm : Type} (mOps : WorkerOps Wm) (m0 : Wm) (hfast : FlagsFast)
    (W : List (Fin 2)) : FlagsContract mOps flagsOps m0 flagsInit W :=
  flagsContract mOps m0 (jobHalts_of_fast hfast) W

/-- **The flag workers never fault**, from the step budget alone. -/
theorem flags_never_fault_of_fast {Wm : Type} (mOps : WorkerOps Wm) (m0 : Wm)
    (hfast : FlagsFast) (u : List (Fin 2)) (i : Fin 2) :
    flagsOps.faulted ((run mOps flagsOps m0 flagsInit u).flags i) = false :=
  flags_never_fault mOps m0 (jobHalts_of_fast hfast) u i

end PalPeg.ScaFlagsJob
