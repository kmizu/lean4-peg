import PalPeg.GalilDpPrepared

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PalPeg.GalilDpSearch
open GalilFppWide

/-- The three actual tests that accept a candidate: the lower bound has
been exhausted and both mark cells are one. No tape is modified. -/
theorem candidate_found (x : Config 12) (hp : x.pc = 348)
    (hl : x.tape 10 (x.pos 10) = 5)
    (hm : x.tape 8 (x.pos 8) = 8) (hs : x.tape 9 (x.pos 9) = 8) :
    Completed GalilDpCode.code x [348,365,364,346] { x with pc := 346 } := by
  let a : Config 12 := { x with pc := 365 }
  let b : Config 12 := { x with pc := 364 }
  let y : Config 12 := { x with pc := 346 }
  have hrun : Completed GalilDpCode.code x [x.pc,365,364,346] y := by
    refine .step x a y (.read 10 [(8,366),(5,365)]) _ (by rw [hp]; rfl)
      (.read _ _ _ _ (by simp [hl])) ?_
    refine .step a b y (.read 9 [(7,363),(8,364),(5,347)]) _ rfl
      (.read _ _ _ _ (by simp [a, hs])) ?_
    refine .step b y y (.read 8 [(7,363),(8,346),(5,347)]) _ rfl
      (.read _ _ _ _ (by simp [b, hm])) ?_
    exact .halt y rfl
  simpa only [hp] using hrun

/-- A remaining unary lower-bound cell skips this candidate by advancing
only LOWER, before the shared next-h block. -/
theorem skip_lower (x : Config 12) (hp : x.pc = 348)
    (hl : x.tape 10 (x.pos 10) = 8) :
    Steps GalilDpCode.code x [348,366]
      { x with pc := 363, pos := Function.update x.pos 10 (x.pos 10+1) } := by
  let a : Config 12 := { x with pc := 366 }
  let y : Config 12 := { x with
    pc := 363
    pos := Function.update x.pos 10 (x.pos 10+1) }
  have hrun : Steps GalilDpCode.code x [x.pc,366] y := by
    refine .step x a y (.read 10 [(8,366),(5,365)]) _ (by rw [hp]; rfl)
      (.read _ _ _ _ (by simp [hl])) ?_
    exact .step a y y (.move 10 true 363) [] rfl (.right _ _ _) (.nil _)
  simpa only [hp] using hrun

/-- Reaching the end on SECOND terminates unsuccessfully at the guard,
rather than performing an out-of-bounds move. -/
theorem end_guard (x : Config 12) (hp : x.pc = 349)
    (hs : x.tape 9 (x.pos 9) = 5) :
    Completed GalilDpCode.code x [349,347] { x with pc := 347 } := by
  let y : Config 12 := { x with pc := 347 }
  have hrun : Completed GalilDpCode.code x [x.pc,347] y := by
    exact .step x y y (.read 9 [(7,348),(8,348),(5,347)]) _ (by rw [hp]; rfl)
      (.read _ _ _ _ (by simp [hs])) (.halt y rfl)
  simpa only [hp] using hrun

/-- A zero on SECOND rejects the candidate after the lower-bound test. -/
theorem skip_second (x : Config 12) (hp : x.pc = 348)
    (hl : x.tape 10 (x.pos 10) = 5) (hs : x.tape 9 (x.pos 9) = 7) :
    Steps GalilDpCode.code x [348,365] { x with pc := 363 } := by
  let a : Config 12 := { x with pc := 365 }
  let y : Config 12 := { x with pc := 363 }
  have hrun : Steps GalilDpCode.code x [x.pc,365] y := by
    refine .step x a y (.read 10 [(8,366),(5,365)]) _ (by rw [hp]; rfl)
      (.read _ _ _ _ (by simp [hl])) ?_
    exact .step a y y (.read 9 [(7,363),(8,364),(5,347)]) [] rfl
      (.read _ _ _ _ (by simp [a, hs])) (.nil _)
  simpa only [hp] using hrun

/-- If SECOND is one but MARKS is zero, all three tests run before rejection. -/
theorem skip_first (x : Config 12) (hp : x.pc = 348)
    (hl : x.tape 10 (x.pos 10) = 5) (hs : x.tape 9 (x.pos 9) = 8)
    (hm : x.tape 8 (x.pos 8) = 7) :
    Steps GalilDpCode.code x [348,365,364] { x with pc := 363 } := by
  let a : Config 12 := { x with pc := 365 }
  let b : Config 12 := { x with pc := 364 }
  let y : Config 12 := { x with pc := 363 }
  have hrun : Steps GalilDpCode.code x [x.pc,365,364] y := by
    refine .step x a y (.read 10 [(8,366),(5,365)]) _ (by rw [hp]; rfl)
      (.read _ _ _ _ (by simp [hl])) ?_
    refine .step a b y (.read 9 [(7,363),(8,364),(5,347)]) _ rfl
      (.read _ _ _ _ (by simp [a, hs])) ?_
    exact .step b y y (.read 8 [(7,363),(8,346),(5,347)]) [] rfl
      (.read _ _ _ _ (by simp [b, hm])) (.nil _)
  simpa only [hp] using hrun

#print axioms candidate_found
#print axioms skip_lower
#print axioms end_guard
#print axioms skip_second
#print axioms skip_first
end PalPeg.GalilDpSearch
