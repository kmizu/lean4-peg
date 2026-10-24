import MacroPeg.CBV.SequentialSeqReturn

/-! Compile a bounded-time four-stack local numeric operation into the local
registers, preserving the binary continuation and the other registers. -/

namespace Shallot.MacroPeg.CBV.SequentialNumericBlock

open Complexity SequentialSeqReturn
open SequentialFrontRead (locals)

def scratchSpace (M T N : Nat) : Nat := M * (N + 1) + grow N T + 2

theorem scratchSpace_linear (M T N : Nat) :
    scratchSpace M T N = (M + T) * N + (M + T * (T + 1) + 2) := by
  simp only [scratchSpace, grow, Nat.mul_add, Nat.add_mul, Nat.mul_one]
  omega

theorem compiled_runs (p : NProg 4) (input output : List Nat) {M T N B : Nat}
    (hr : NRuns p (st input [] [] []) (st output [] [] []) T)
    (hlen : input.length ≤ M) (hb : ∀ v ∈ input, v ≤ N) (hspace : scratchSpace M T N ≤ B) :
    Complexity.Runs (LenOK B) p.compile (encL (st input [] [] [])) (encL (st output [] [] [])) (T * ncost B) := by
  have hcells : (encS input).length ≤ M * (N + 1) :=
    Nat.le_trans (SequentialFrontRead.locals_length _ N hb) (Nat.mul_le_mul_right _ hlen)
  have hBnd : Bnd N (M * (N + 1)) (st input [] [] []) := by
    constructor
    · intro i v hv
      by_cases hi : i = 0
      · exact hb v (by simpa [st, hi] using hv)
      · simp [st, hi] at hv
    · intro i
      by_cases hi : i = 0
      · simpa [st, hi] using hcells
      · simp [st, hi, encS]
  obtain ⟨t, ht, hx⟩ := hr
  have hxB := (nexec_space hx N (M * (N + 1)) hBnd).2 B (by
    have hg := grow_mono (m := N) ht
    unfold scratchSpace at hspace
    omega)
  obtain ⟨t', ht', he⟩ := nexec_compile (fun _ h => h) hxB
  exact ⟨t', Nat.le_trans ht' (Nat.mul_le_mul_right _ ht), he⟩

/-- Embed an already space-annotated run, including runs whose time depends on
input positions, without converting their time bound into extra workspace. -/
theorem frame_runs (p : NProg 4) (input output : List Nat) {T B width held : Nat} (tail : List Bool)
    (hr : Complexity.Runs (LenOK B) p.compile (encL (st input [] [] []))
      (encL (st output [] [] [])) T)
    (hR : LenOK B (SequentialFieldFetch.start width [] tail (locals input) held [])) :
    Complexity.Runs (LenOK B) (p.compile.rename reg)
      (SequentialFieldFetch.start width [] tail (locals input) held [])
      (SequentialFieldFetch.start width [] tail (locals output) held []) T := by
  let R := SequentialFieldFetch.start width [] tail (locals input) held []
  let R' := SequentialFieldFetch.start width [] tail (locals output) held []
  have hproj : ∀ i, R (reg i) = encL (st input [] [] []) i := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      simp [R, reg, SequentialFieldFetch.start, encL, encS, st, SequentialFrontRead.locals] <;> rfl
  obtain ⟨t, ht, hx⟩ := hr
  have he := hx.rename_frame reg_injective R hR
  rw [Lists.frame_eq reg_injective R _ hproj] at he
  have hout : (encL (st output [] [] [])).frame reg R = R' := by
    funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [Lists.frame_get reg_injective]
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl <;>
        simp [R', reg, SequentialFieldFetch.start, encL, encS, st, SequentialFrontRead.locals] <;> rfl
    · rw [Lists.frame_outside R _ j hj]
      have h9 : j ≠ 9 := by intro hh; subst j; exact hj ⟨0, rfl⟩
      simp [R, R', SequentialFieldFetch.start, h9]
  change LExec (LenOK B) (p.compile.rename reg) R t (.cont ((encL (st output [] [] [])).frame reg R)) at he
  rw [hout] at he
  exact ⟨t, ht, he⟩

theorem local_runs (p : NProg 4) (input output : List Nat) {M T N B width held : Nat} (tail : List Bool)
    (hr : NRuns p (st input [] [] []) (st output [] [] []) T)
    (hlen : input.length ≤ M) (hb : ∀ v ∈ input, v ≤ N) (hspace : scratchSpace M T N ≤ B)
    (hR : LenOK B (SequentialFieldFetch.start width [] tail (locals input) held [])) :
    Complexity.Runs (LenOK B) (p.compile.rename reg)
      (SequentialFieldFetch.start width [] tail (locals input) held [])
      (SequentialFieldFetch.start width [] tail (locals output) held []) (T * ncost B) := by
  exact frame_runs p input output tail (compiled_runs p input output hr hlen hb hspace) hR

/-- Compile a local numeric run with its direct intermediate space invariant. -/
theorem annotated_local_runs (p : NProg 4) (input output : List Nat)
    {T B width held : Nat} (tail : List Bool)
    (hr : ∃ t, t ≤ T ∧ NExec (NFits B) p (st input [] [] []) t (.cont (st output [] [] [])))
    (hR : LenOK B (SequentialFieldFetch.start width [] tail (locals input) held [])) :
    Complexity.Runs (LenOK B) (p.compile.rename reg)
      (SequentialFieldFetch.start width [] tail (locals input) held [])
      (SequentialFieldFetch.start width [] tail (locals output) held []) (T * ncost B) := by
  apply frame_runs p input output tail _ hR
  obtain ⟨t, ht, he⟩ := hr
  obtain ⟨t', ht', he'⟩ := nexec_compile (fun _ h => h) he
  exact ⟨t', Nat.le_trans ht' (Nat.mul_le_mul_right _ ht), he'⟩

end Shallot.MacroPeg.CBV.SequentialNumericBlock
