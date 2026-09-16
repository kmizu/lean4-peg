import PalPeg.GalilFppPrepareCells

set_option autoImplicit false
namespace PalPeg.GalilFppPrepareInit
open GalilFppWide GalilFppPreparation GalilFppPrepareCopy GalilFppPrepareCells

/-- Scala runMarked starts with SOURCE bounded, eight blank tapes, and all heads zero. -/
def initial (w : List (Fin 3)) : Config 9 where
  pc := 320
  tape := fun t => if t = 7 then source w else fun _ => 6
  pos := fun _ => 0

/-- Literal sequence of the eighteen setup instructions, including C=010. -/
def boot (x : Config 9) : Config 9 :=
  let x := written 6 4 319 x
  let x := written 5 4 318 x
  let x := written 4 4 317 x
  let x := written 3 4 316 x
  let x := written 8 4 315 x
  let x := written 1 4 314 x
  let x := written 0 4 313 x
  let x := written 2 7 312 x
  let x := right 2 311 x
  let x := written 2 8 310 x
  let x := right 2 309 x
  let x := written 2 7 308 x
  let x := left 2 307 x
  let x := left 2 306 x
  let x := right 0 305 x
  let x := right 1 304 x
  let x := right 8 303 x
  right 7 259 x

set_option maxHeartbeats 2000000 in
theorem boot_step (x : Config 9) (hp : x.pc = 320) (hC : x.pos 2 = 0) :
    ∃ qs, Steps GalilFppMarkedCode.code x qs (boot x) ∧ qs.length = 18 := by
  let s1 := written 6 4 319 x
  let s2 := written 5 4 318 s1
  let s3 := written 4 4 317 s2
  let s4 := written 3 4 316 s3
  let s5 := written 8 4 315 s4
  let s6 := written 1 4 314 s5
  let s7 := written 0 4 313 s6
  let s8 := written 2 7 312 s7
  let s9 := right 2 311 s8
  let s10 := written 2 8 310 s9
  let s11 := right 2 309 s10
  let s12 := written 2 7 308 s11
  let s13 := left 2 307 s12
  let s14 := left 2 306 s13
  let s15 := right 0 305 s14
  let s16 := right 1 304 s15
  let s17 := right 8 303 s16
  let s18 := right 7 259 s17
  have h0 := write_step 6 4 319 x (by rw [hp]; rfl)
  have h1 := write_step 5 4 318 s1 rfl
  have h2 := write_step 4 4 317 s2 rfl
  have h3 := write_step 3 4 316 s3 rfl
  have h4 := write_step 8 4 315 s4 rfl
  have h5 := write_step 1 4 314 s5 rfl
  have h6 := write_step 0 4 313 s6 rfl
  have h7 := write_step 2 7 312 s7 rfl
  have h8 := right_step 2 311 s8 rfl
  have h9 := write_step 2 8 310 s9 rfl
  have h10 := right_step 2 309 s10 rfl
  have h11 := write_step 2 7 308 s11 rfl
  have h12 : Steps GalilFppMarkedCode.code s12 [s12.pc] s13 :=
    .step _ _ _ _ [] rfl (.left _ _ _ (by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, written, right, left, hC])) (.nil _)
  have h13 : Steps GalilFppMarkedCode.code s13 [s13.pc] s14 :=
    .step _ _ _ _ [] rfl (.left _ _ _ (by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, written, right, left, hC])) (.nil _)
  have h14 := right_step 0 305 s14 rfl
  have h15 := right_step 1 304 s15 rfl
  have h16 := right_step 8 303 s16 rfl
  have h17 := right_step 7 259 s17 rfl
  exact ⟨_, steps_append (steps_append (steps_append (steps_append (steps_append (steps_append (steps_append (steps_append (steps_append (steps_append (steps_append (steps_append (steps_append (steps_append (steps_append (steps_append (steps_append (h0) h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17, rfl⟩

/-- Explicit copy-entry configuration computed from the real fresh start. -/
def copyEntry (w : List (Fin 3)) : Config 9 where
  pc := 259
  tape := fun t => if t = 7 then source w else if t = 2 then GalilFppFrontier.initialC
    else fun i => if i = 0 then 4 else 6
  pos := fun t => if t = 0 ∨ t = 1 ∨ t = 7 ∨ t = 8 then 1 else 0

theorem config_ext {x y : Config 9} (hpc : x.pc = y.pc) (ht : x.tape = y.tape)
    (hp : x.pos = y.pos) : x = y := by
  cases x; cases y; simp_all

set_option maxHeartbeats 2000000 in
theorem boot_eq (w : List (Fin 3)) : boot (initial w) = copyEntry w := by
  apply config_ext
  · rfl
  · funext t i
    fin_cases t <;>
      simp [boot, initial, copyEntry, written, right, left, Function.update_apply,
        GalilFppFrontier.initialC] <;>
      split_ifs <;> simp_all <;> omega
  · funext t
    fin_cases t <;> simp [boot, initial, copyEntry, written, right, left]

/-- Preparation from Scala's actual fresh nine-tape initial state. No
intermediate read, character-layout or initialized-head premise remains. -/
theorem fresh_prepare (w : List (Fin 3)) :
    ∃ y qs, Steps GalilFppMarkedCode.code (initial w) qs y ∧
      qs.length = 24*w.length+42 ∧ y.pc = 227 ∧
      y.tape = (copied w (copyEntry w)).tape ∧
      y.pos = fun t => if t = 1 then 1 else 0 := by
  obtain ⟨qs, hs, hl⟩ := boot_step (initial w) rfl rfl
  rw [boot_eq] at hs
  obtain ⟨y, rs, hr, hrl, hypc, hyt, _, _, _, _, hyp⟩ :=
    copy_rewind w (copyEntry w) rfl rfl rfl
      (by intro j; fin_cases j <;> simp [GalilFppPrepareRewind.tape, copyEntry])
      (by intro j; fin_cases j <;> simp [GalilFppPrepareRewind.tape, copyEntry])
  refine ⟨y, qs ++ rs, steps_append hs hr, ?_, hypc, hyt, ?_⟩
  · simp only [List.length_append]; omega
  · rw [hyp]
    funext t
    fin_cases t <;> simp [copied, finish, written, backward_many_pos, turn, left, right,
      forward_many_pos, copyEntry]

#print axioms fresh_prepare
#print axioms boot_step
#print axioms boot_eq
end PalPeg.GalilFppPrepareInit
