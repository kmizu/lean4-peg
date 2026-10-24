import MacroPeg.CBV.SequentialLocalPipeline
import MacroPeg.CBV.SequentialAtomSelect

/-! Extend the binary evaluator's eleven list registers with an original-input
register and disjoint numeric workspace. -/
namespace Shallot.MacroPeg.CBV.SequentialInputHost
open Complexity

/-- The original-input encoding is retained on register eleven. -/
def extend (L : Lists 11) (X : List Nat) : Lists 20 := fun i =>
  if h : i.val < 11 then L ⟨i.val,h⟩ else if i=11 then X else []

def old (i : Fin 11) : Fin 20 := ⟨i.val,by omega⟩
theorem old_injective : Function.Injective old := by
  intro a b h; apply Fin.ext; exact congrArg (fun i : Fin 20 => i.val) h

theorem extend_get (L : Lists 11) (X : List Nat) (i : Fin 11) : extend L X (old i) = L i := by
  unfold extend old
  rw [dif_pos i.isLt]

theorem extend_project {B : Nat} {L : Lists 11} {X : List Nat} (h : LenOK B (extend L X)) : LenOK B L := by
  intro i
  simpa only [extend_get] using h (old i)

theorem extend_fits {B : Nat} {L : Lists 11} {X : List Nat}
    (hL : LenOK B L) (hX : X.length+2 ≤ B) : LenOK B (extend L X) := by
  intro j
  by_cases hj : j.val < 11
  · change (if h : j.val < 11 then L ⟨j.val,h⟩ else _).length+2 ≤ B
    rw [dif_pos hj]
    exact hL ⟨j.val,hj⟩
  · simp only [extend,dif_neg hj]
    split
    · exact hX
    · simp; omega

private theorem old_frame (L L' : Lists 11) (X : List Nat) :
    L'.frame old (extend L X) = extend L' X := by
  funext j
  by_cases hj : j.val < 11
  · let i : Fin 11 := ⟨j.val,hj⟩
    have he : old i=j := rfl
    rw [← he,Lists.frame_get old_injective,extend_get]
  · rw [Lists.frame_outside _ _ j (by
      intro ⟨i,hi⟩
      have hh := congrArg Fin.val hi
      simp only [old] at hh
      omega)]
    simp [extend,hj]

theorem old_runs {B T : Nat} (p : LProg 11) (L L' : Lists 11) (X : List Nat)
    (hr : Complexity.Runs (LenOK B) p L L' T) (hX : X.length+2 ≤ B) :
    Complexity.Runs (LenOK B) (p.rename old) (extend L X) (extend L' X) T := by
  obtain ⟨t,ht,he⟩ := hr
  have hh := he.rename_frame old_injective (extend L X) (extend_fits he.q_start hX)
  change LExec (LenOK B) (p.rename old) (L.frame old (extend L X)) t (.cont (L'.frame old (extend L X))) at hh
  rw [old_frame,old_frame] at hh
  exact ⟨t,ht,hh⟩

/-- The sixteen list registers produced by the numeric atom compiler. The
binary continuation, held value, two-marker, and width occupy the complement. -/
def atomReg (i : Fin 16) : Fin 20 :=
  if i=0 then 11 else if i=1 then 1 else if i=2 then 2 else if i=3 then 5 else
  if i=4 then 7 else if i=5 then 12 else if i=6 then 13 else if i=7 then 14 else
  if i=8 then 6 else if i=9 then 15 else if i=10 then 16 else if i=11 then 10 else
  if i=12 then 9 else if i=13 then 17 else if i=14 then 18 else 19

theorem atomReg_injective : Function.Injective atomReg := by unfold Function.Injective; decide

private theorem projection (X D : List Nat) (width held : Nat) (bits : List Bool) :
    ∀ i, extend (SequentialFieldFetch.start width [] bits (SequentialFrontRead.locals D) held [])
      (Complexity.encS X) (atomReg i) = encL (SequentialAtomSelect.state X D [] [] []) i := by
  intro i
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

private theorem atom_frame (X D D' : List Nat) (width held : Nat) (bits : List Bool) :
    (encL (SequentialAtomSelect.state X D' [] [] [])).frame atomReg
      (extend (SequentialFieldFetch.start width [] bits (SequentialFrontRead.locals D) held []) (Complexity.encS X)) =
    extend (SequentialFieldFetch.start width [] bits (SequentialFrontRead.locals D') held []) (Complexity.encS X) := by
  funext j
  by_cases hj : ∃ i, atomReg i=j
  · obtain ⟨i,rfl⟩ := hj
    rw [Lists.frame_get atomReg_injective,projection]
  · rw [Lists.frame_outside _ _ j hj]
    have hslots : j=0 ∨ j=3 ∨ j=4 ∨ j=8 := by
      have h0 : j ≠ 11 := by intro h; exact hj ⟨0,h.symm⟩
      have h1 : j ≠ 1 := by intro h; exact hj ⟨1,h.symm⟩
      have h2 : j ≠ 2 := by intro h; exact hj ⟨2,h.symm⟩
      have h3 : j ≠ 5 := by intro h; exact hj ⟨3,h.symm⟩
      have h4 : j ≠ 7 := by intro h; exact hj ⟨4,h.symm⟩
      have h5 : j ≠ 12 := by intro h; exact hj ⟨5,h.symm⟩
      have h6 : j ≠ 13 := by intro h; exact hj ⟨6,h.symm⟩
      have h7 : j ≠ 14 := by intro h; exact hj ⟨7,h.symm⟩
      have h8 : j ≠ 6 := by intro h; exact hj ⟨8,h.symm⟩
      have h9 : j ≠ 15 := by intro h; exact hj ⟨9,h.symm⟩
      have h10 : j ≠ 16 := by intro h; exact hj ⟨10,h.symm⟩
      have h11 : j ≠ 10 := by intro h; exact hj ⟨11,h.symm⟩
      have h12 : j ≠ 9 := by intro h; exact hj ⟨12,h.symm⟩
      have h13 : j ≠ 17 := by intro h; exact hj ⟨13,h.symm⟩
      have h14 : j ≠ 18 := by intro h; exact hj ⟨14,h.symm⟩
      have h15 : j ≠ 19 := by intro h; exact hj ⟨15,h.symm⟩
      omega
    rcases hslots with rfl | rfl | rfl | rfl <;> rfl

theorem atom_runs (p : NProg 15) (X D D' : List Nat) (width held : Nat) (bits : List Bool) {B T : Nat}
    (hr : Complexity.Runs (LenOK B) p.compile (encL (SequentialAtomSelect.state X D [] [] []))
      (encL (SequentialAtomSelect.state X D' [] [] [])) T)
    (hR : LenOK B (extend (SequentialFieldFetch.start width [] bits (SequentialFrontRead.locals D) held []) (Complexity.encS X))) :
    Complexity.Runs (LenOK B) (p.compile.rename atomReg)
      (extend (SequentialFieldFetch.start width [] bits (SequentialFrontRead.locals D) held []) (Complexity.encS X))
      (extend (SequentialFieldFetch.start width [] bits (SequentialFrontRead.locals D') held []) (Complexity.encS X)) T := by
  let R := extend (SequentialFieldFetch.start width [] bits (SequentialFrontRead.locals D) held []) (Complexity.encS X)
  obtain ⟨t,ht,he⟩ := hr
  have hh := he.rename_frame atomReg_injective R hR
  rw [Lists.frame_eq atomReg_injective R _ (projection X D width held bits)] at hh
  change LExec (LenOK B) (p.compile.rename atomReg) R t
    (.cont ((encL (SequentialAtomSelect.state X D' [] [] [])).frame atomReg R)) at hh
  rw [atom_frame] at hh
  exact ⟨t,ht,hh⟩

end Shallot.MacroPeg.CBV.SequentialInputHost
