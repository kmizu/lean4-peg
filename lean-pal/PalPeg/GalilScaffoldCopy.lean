import PalPeg.GalilScaffoldLoading

set_option autoImplicit false
namespace PalPeg.GalilScaffoldCopy
open GalilScaffoldTape GalilScaffoldLoad

/-- Logical view of the copy loop: rest is the stream seen while walking
left, work is its bounded copy counter, tape is the SOURCE under construction.
The physical walker and counter representations are separate refinements. -/
structure Cursor where
  rest : List (Fin 3)
  work : ℕ
  tape : Tape

inductive Copy : Cursor → ℕ → Cursor → Bool → Prop
  | stop (x : Cursor) (h : x.rest = [] ∨ x.work = 0) :
      Copy x 1 { x with tape := write x.tape 5 } x.rest.isEmpty
  | next (a : Fin 3) (xs : List (Fin 3)) (k n : ℕ) (t : Tape) (y : Cursor) (final : Bool)
      (hr : Copy ⟨xs,k,moveRight (write t (GalilFppPreparation.symbol a))⟩ n y final) :
      Copy ⟨a :: xs,k+1,t⟩ (n+1) y final

/-- Exact copy-loop behavior, including simultaneous budget exhaustion
and end of input. finalStage is true precisely when the remaining stream
is empty, not merely when work reaches zero. -/
theorem copy_exact (xs : List (Fin 3)) (work : ℕ) (t : Tape) :
    Copy ⟨xs,work,t⟩ ((xs.take work).length+1)
      ⟨xs.drop work, work-xs.length,
        write (fill ((xs.take work).map GalilFppPreparation.symbol) t) 5⟩
      (xs.drop work).isEmpty := by
  induction work generalizing xs t with
  | zero => simpa [fill] using Copy.stop ⟨xs,0,t⟩ (Or.inr rfl)
  | succ k ih =>
    cases xs with
    | nil => simpa [fill] using Copy.stop ⟨[],k+1,t⟩ (Or.inl rfl)
    | cons a xs =>
      simpa [fill, Nat.add_assoc] using Copy.next a xs k _ t _ _
        (ih xs (moveRight (write t (GalilFppPreparation.symbol a))))

theorem copy_positive {x y : Cursor} {n : ℕ} {final : Bool} (hr : Copy x n y final) :
    0 < n := by cases hr <;> omega

/-- Each copying iteration is write+right; the final iteration writes
END. Thus the guarded loop refines the existing primitive tape operations. -/
theorem copy_ops {x y : Cursor} {n : ℕ} {final : Bool} (hr : Copy x n y final) :
    GalilScaffoldLoad.Run x.tape (2*n-1) y.tape := by
  induction hr with
  | stop x h => exact .write x.tape _ 5 0 (.nil _)
  | next a xs k n t y final hr ih =>
    have hn := copy_positive hr
    have hs := GalilScaffoldLoad.Run.write t _ (GalilFppPreparation.symbol a) _
      (GalilScaffoldLoad.Run.right _ _ _ ih)
    convert hs using 1; omega

theorem final_iff (xs : List (Fin 3)) (work : ℕ) :
    (xs.drop work).isEmpty = true ↔ xs.length ≤ work := by
  simp

/-- The resulting tape is exactly at the right sentinel, ready for the
marker-driven home loop already proved for the loader. -/
theorem copy_layout (xs : List (Fin 3)) (work : ℕ) :
    write (fill ((xs.take work).map GalilFppPreparation.symbol) ⟨[4],6,[]⟩) 5 =
      (⟨((xs.take work).map GalilFppPreparation.symbol).reverse ++ [4],5,[]⟩ : Tape) := by
  rw [fill_stack]
  rfl

theorem copy_home (xs : List (Fin 3)) (work : ℕ) :
    Home (write (fill ((xs.take work).map GalilFppPreparation.symbol) ⟨[4],6,[]⟩) 5)
      ((xs.take work).length+1)
      (GalilScaffoldPreload.bounded ((xs.take work).map GalilFppPreparation.symbol)) := by
  have hn : (4 : Fin 9) ∉ (xs.take work).map GalilFppPreparation.symbol := by
    intro hm
    obtain ⟨a, _, ha⟩ := List.mem_map.mp hm
    have hv := congrArg Fin.val ha
    have := a.isLt
    simp [GalilFppPreparation.symbol] at hv
    omega
  rw [copy_layout]
  simpa [GalilScaffoldPreload.bounded] using
    home_exact ((xs.take work).map GalilFppPreparation.symbol).reverse 5 [] (by decide) (by simpa using hn)

#print axioms copy_exact
#print axioms copy_ops
#print axioms final_iff
#print axioms copy_home
end PalPeg.GalilScaffoldCopy
