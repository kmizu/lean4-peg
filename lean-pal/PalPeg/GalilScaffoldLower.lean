import PalPeg.GalilScaffoldCounter

set_option autoImplicit false
namespace PalPeg.GalilScaffoldLower
open GalilScaffoldCounter GalilScaffoldTape GalilScaffoldLoad

structure Cursor where
  work : Counter
  tape : Tape

/-- One LOWER controller tick writes a bit, moves right and decrements work;
the zero-work tick writes END and changes mode. -/
inductive Load : Cursor → ℕ → Cursor → Prop
  | stop (x : Cursor) (h : positive x.work = false) :
      Load x 1 ⟨x.work,write x.tape 5⟩
  | next (x y : Cursor) (n : ℕ) (h : positive x.work = true)
      (hr : Load ⟨dec x.work,moveRight (write x.tape 8)⟩ n y) : Load x (n+1) y

theorem load_exact (r : ℕ) (t : Tape) :
    Load ⟨ofNat r,t⟩ (r+1)
      ⟨ofNat 0,write (fill (List.replicate r 8) t) 5⟩ := by
  induction r generalizing t with
  | zero => exact .stop _ (by simp [positive,ofNat])
  | succ r ih =>
    refine .next _ _ _ (by simp [positive,ofNat,List.replicate_succ]) ?_
    simpa [dec_ofNat_succ,List.replicate_succ,fill] using ih (moveRight (write t 8))

/-- Unlike primitive Home, this counts the final LEFT test/dispatch tick. -/
inductive Rewind : Tape → ℕ → Tape → Prop
  | done (x : Tape) (h : x.focus = 4) : Rewind x 1 x
  | left (x y : Tape) (n : ℕ) (hc : x.focus ≠ 4) (hp : x.left ≠ [])
      (hr : Rewind (moveLeft x) n y) : Rewind x (n+1) y

theorem rewind_home {x y : Tape} {n : ℕ} (hr : Home x n y) : Rewind x (n+1) y := by
  induction hr with
  | done x h => exact .done x h
  | left x y n hc hp hr ih => exact .left x y (n+1) hc hp ih

/-- From prepare's LEFT/right setup, lower and lower_home take 2r+3 ticks
and produce exactly the bounded unary preload used by DP. -/
theorem lower_ready (r : ℕ) :
    ∃ t, Load ⟨ofNat r,moveRight (write reset 4)⟩ (r+1) ⟨ofNat 0,t⟩ ∧
      Rewind t (r+2) (GalilScaffoldPreload.bounded (List.replicate r 8)) := by
  refine ⟨_,load_exact r _,?_⟩
  have hh := home_exact (List.replicate r (8 : Fin 9)).reverse 5 []
    (by decide) (by simp)
  have hrew := rewind_home hh
  change Rewind (write (fill (List.replicate r 8) ⟨[4],6,[]⟩) 5) (r+2) _
  rw [fill_stack]
  simpa [write,GalilScaffoldPreload.bounded,Nat.add_assoc] using hrew

/-- SOURCE copy and marker-driven home, including both transition ticks.
The copied length is min(input length, span+1); finalStage depends on input end. -/
theorem source_ready (xs : List (Fin 3)) (span : ℕ) :
    ∃ t, GalilScaffoldCounter.Copy
      ⟨xs,ofNat (span+1),moveRight (write GalilScaffoldTape.reset 4)⟩
      ((xs.take (span+1)).length+1)
      ⟨xs.drop (span+1),ofNat (span+1-xs.length),t⟩
      (xs.drop (span+1)).isEmpty ∧
      Rewind t ((xs.take (span+1)).length+2)
        (GalilScaffoldPreload.bounded ((xs.take (span+1)).map GalilFppPreparation.symbol)) ∧
      ((xs.drop (span+1)).isEmpty = true ↔ xs.length ≤ span+1) := by
  refine ⟨_,GalilScaffoldCounter.copy_exact xs (span+1) _,?_,by simp⟩
  have hh := rewind_home (GalilScaffoldCopy.copy_home xs (span+1))
  simpa only [Nat.add_assoc,GalilScaffoldTape.reset,write,moveRight] using hh

/-- Forget controller grouping but retain the very same tape execution. -/
theorem load_ops {x y : Cursor} {n : ℕ} (hr : Load x n y) :
    GalilScaffoldLoad.Run x.tape (2*n-1) y.tape := by
  induction hr with
  | stop x h => exact .write x.tape _ 5 0 (.nil _)
  | next x y n h hr ih =>
    have hn : 0 < n := by cases hr <;> omega
    have hs := GalilScaffoldLoad.Run.write x.tape _ 8 _
      (GalilScaffoldLoad.Run.right _ _ _ ih)
    convert hs using 1 <;> omega

theorem rewind_ops {x y : Tape} {n : ℕ} (hr : Rewind x n y) :
    GalilScaffoldLoad.Run x (n-1) y := by
  induction hr with
  | done x h => exact .nil _
  | left x y n hc hp hr ih =>
    have hn : 0 < n := by cases hr <;> omega
    have hs := GalilScaffoldLoad.Run.left x y _ hp ih
    convert hs using 1 <;> omega

#print axioms load_ops
#print axioms rewind_ops
#print axioms source_ready
#print axioms lower_ready
end PalPeg.GalilScaffoldLower
