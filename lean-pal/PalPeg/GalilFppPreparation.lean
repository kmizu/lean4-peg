import PalPeg.GalilFppMarkSimulation

set_option autoImplicit false
namespace PalPeg.GalilFppPreparation
open GalilFppWide

def symbol (a : Fin 3) : Fin 9 := ⟨a.val, by omega⟩

def written (t : Fin 9) (s : Fin 9) (pc : ℕ) (x : Config 9) : Config 9 :=
  { x with pc := pc, tape := Function.update x.tape t (Function.update (x.tape t) (x.pos t) s) }

def right (t : Fin 9) (pc : ℕ) (x : Config 9) : Config 9 :=
  { x with pc := pc, pos := Function.update x.pos t (x.pos t+1) }

theorem write_step (t : Fin 9) (s : Fin 9) (pc : ℕ) (x : Config 9)
    (hi : GalilFppMarkedCode.code[x.pc]? = some (.write t s pc)) :
    Steps GalilFppMarkedCode.code x [x.pc] (written t s pc x) :=
  .step _ _ _ _ [] hi (.write _ _ _ _) (.nil _)

theorem right_step (t : Fin 9) (pc : ℕ) (x : Config 9)
    (hi : GalilFppMarkedCode.code[x.pc]? = some (.move t true pc)) :
    Steps GalilFppMarkedCode.code x [x.pc] (right t pc x) :=
  .step _ _ _ _ [] hi (.right _ _ _) (.nil _)

/-- One literal forward-copy block in FppSubroutine: two letter writes,
one zero mark, then advance A, B, MARKS and SOURCE. -/
def forward (a : Fin 3) (x : Config 9) : Config 9 :=
  let q := 288+7*a.val
  let z := { x with pc := q }
  right 7 259 (right 8 (q-6) (right 1 (q-5) (right 0 (q-4)
    (written 8 7 (q-3) (written 1 (symbol a) (q-2) (written 0 (symbol a) (q-1) z))))))

theorem forward_step (a : Fin 3) (x : Config 9) (hp : x.pc = 259)
    (hc : x.tape 7 (x.pos 7) = symbol a) :
    ∃ qs, Steps GalilFppMarkedCode.code x qs (forward a x) ∧ qs.length = 8 := by
  let q := 288+7*a.val
  let z : Config 9 := { x with pc := q }
  let u := written 0 (symbol a) (q-1) z
  let v := written 1 (symbol a) (q-2) u
  let w := written 8 7 (q-3) v
  let b := right 0 (q-4) w
  let c := right 1 (q-5) b
  let d := right 8 (q-6) c
  have hread : Steps GalilFppMarkedCode.code x [259] z := by
    have hm : (x.tape 7 (x.pos 7), q) ∈
        ([(5,281),(0,288),(1,295),(2,302)] : List (Fin 9 × ℕ)) := by
      rw [hc]; fin_cases a <;> decide
    simpa only [hp] using
      (Steps.step x z z _ [] (by rw [hp]; rfl) (.read _ _ _ _ hm) (.nil _))
  have h0 := write_step 0 (symbol a) (q-1) z (by fin_cases a <;> rfl)
  have h1 := write_step 1 (symbol a) (q-2) u (by fin_cases a <;> rfl)
  have h8 := write_step 8 7 (q-3) v (by fin_cases a <;> rfl)
  have hA := right_step 0 (q-4) w (by fin_cases a <;> rfl)
  have hB := right_step 1 (q-5) b (by fin_cases a <;> rfl)
  have hM := right_step 8 (q-6) c (by fin_cases a <;> rfl)
  have hS := right_step 7 259 d (by fin_cases a <;> rfl)
  exact ⟨_, steps_append (steps_append (steps_append (steps_append
    (steps_append (steps_append (steps_append hread h0) h1) h8) hA) hB) hM) hS, rfl⟩

theorem forward_pos (a : Fin 3) (x : Config 9) (t : Fin 9) :
    (forward a x).pos t = x.pos t + (if t = 0 ∨ t = 1 ∨ t = 7 ∨ t = 8 then 1 else 0) := by
  fin_cases t <;> simp [forward, right, written]

theorem forward_tape (a : Fin 3) (x : Config 9) (t : Fin 9) (i : ℕ) :
    (forward a x).tape t i =
      if (t = 0 ∨ t = 1) ∧ i = x.pos t then symbol a
      else if t = 8 ∧ i = x.pos 8 then 7 else x.tape t i := by
  fin_cases t <;> simp [forward, right, written, Function.update_apply]

def forwardMany : List (Fin 3) → Config 9 → Config 9
  | [], x => x
  | a :: rest, x => forwardMany rest (forward a x)

/-- Exact cells written by a finite sequence of consecutive writes. -/
def fill : List (Fin 9) → ℕ → (ℕ → Fin 9) → (ℕ → Fin 9)
  | [], _, t => t
  | a :: rest, p, t => fill rest (p+1) (Function.update t p a)

theorem forward_many_pos (as : List (Fin 3)) (x : Config 9) (t : Fin 9) :
    (forwardMany as x).pos t = x.pos t +
      (if t = 0 ∨ t = 1 ∨ t = 7 ∨ t = 8 then as.length else 0) := by
  induction as generalizing x with
  | nil => simp [forwardMany]
  | cons a as ih =>
    rw [forwardMany, ih, forward_pos]
    split <;> simp_all <;> omega

theorem forward_many_tape (as : List (Fin 3)) (x : Config 9) (t : Fin 9) :
    (forwardMany as x).tape t =
      if t = 0 ∨ t = 1 then fill (as.map symbol) (x.pos t) (x.tape t)
      else if t = 8 then fill (List.replicate as.length 7) (x.pos 8) (x.tape 8)
      else x.tape t := by
  induction as generalizing x with
  | nil => fin_cases t <;> simp [forwardMany, fill]
  | cons a as ih =>
    rw [forwardMany, ih]
    have hf : ∀ u, (forward a x).tape u =
        if u = 0 ∨ u = 1 then Function.update (x.tape u) (x.pos u) (symbol a)
        else if u = 8 then Function.update (x.tape 8) (x.pos 8) 7 else x.tape u := by
      intro u
      funext i
      fin_cases u <;> simp [forward_tape, Function.update_apply]
    fin_cases t <;> simp [hf, forward_pos, List.replicate_succ, fill]

/-- The complete forward loop executes exactly eight instructions per
source letter, preserving the original SOURCE while reading it. -/
theorem forward_run (as : List (Fin 3)) (x : Config 9) (hp : x.pc = 259)
    (hc : ∀ k (hk : k < as.length), x.tape 7 (x.pos 7+k) = symbol as[k]) :
    ∃ qs, Steps GalilFppMarkedCode.code x qs (forwardMany as x) ∧
      qs.length = 8*as.length ∧ (forwardMany as x).pc = 259 := by
  induction as generalizing x with
  | nil => exact ⟨[], .nil _, rfl, hp⟩
  | cons a as ih =>
    obtain ⟨qs, hs, hl⟩ := forward_step a x hp (hc 0 (by simp))
    have htail : ∀ k (hk : k < as.length),
        (forward a x).tape 7 ((forward a x).pos 7+k) = symbol as[k] := by
      intro k hk
      have hh := hc (k+1) (by simp; omega)
      simpa [forward_tape, forward_pos, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    obtain ⟨rs, hr, hrl, hpc⟩ := ih (forward a x) rfl htail
    refine ⟨qs ++ rs, steps_append hs hr, ?_, hpc⟩
    simp only [List.length_append, List.length_cons]; omega

def left (t : Fin 9) (pc : ℕ) (x : Config 9) : Config 9 :=
  { x with pc := pc, pos := Function.update x.pos t (x.pos t-1) }

def backward (a : Fin 3) (x : Config 9) : Config 9 :=
  let q := 265+5*a.val
  let z := { x with pc := q }
  left 7 260 (right 1 (q-4) (right 0 (q-3)
    (written 1 (symbol a) (q-2) (written 0 (symbol a) (q-1) z))))

theorem backward_step (a : Fin 3) (x : Config 9) (hp : x.pc = 260)
    (hc : x.tape 7 (x.pos 7) = symbol a) (hpos : 0 < x.pos 7) :
    ∃ qs, Steps GalilFppMarkedCode.code x qs (backward a x) ∧ qs.length = 6 := by
  let q := 265+5*a.val
  let z : Config 9 := { x with pc := q }
  let u := written 0 (symbol a) (q-1) z
  let v := written 1 (symbol a) (q-2) u
  let b := right 0 (q-3) v
  let c := right 1 (q-4) b
  have hread : Steps GalilFppMarkedCode.code x [260] z := by
    have hm : (x.tape 7 (x.pos 7), q) ∈
        ([(4,258),(0,265),(1,270),(2,275)] : List (Fin 9 × ℕ)) := by
      rw [hc]; fin_cases a <;> decide
    simpa only [hp] using
      (Steps.step x z z _ [] (by rw [hp]; rfl) (.read _ _ _ _ hm) (.nil _))
  have h0 := write_step 0 (symbol a) (q-1) z (by fin_cases a <;> rfl)
  have h1 := write_step 1 (symbol a) (q-2) u (by fin_cases a <;> rfl)
  have hA := right_step 0 (q-3) v (by fin_cases a <;> rfl)
  have hB := right_step 1 (q-4) b (by fin_cases a <;> rfl)
  have hS : Steps GalilFppMarkedCode.code c [c.pc] (backward a x) := by
    exact .step _ _ _ _ [] (by fin_cases a <;> rfl)
      (.left _ _ _ (by simpa [c, b, v, u, z, right, written] using hpos)) (.nil _)
  exact ⟨_, steps_append (steps_append (steps_append (steps_append (steps_append hread h0) h1) hA) hB) hS, rfl⟩

theorem backward_pos (a : Fin 3) (x : Config 9) (t : Fin 9) :
    (backward a x).pos t =
      if t = 0 ∨ t = 1 then x.pos t+1 else if t = 7 then x.pos t-1 else x.pos t := by
  fin_cases t <;> simp [backward, right, left, written]

theorem backward_tape (a : Fin 3) (x : Config 9) (t : Fin 9) :
    (backward a x).tape t =
      if t = 0 ∨ t = 1 then Function.update (x.tape t) (x.pos t) (symbol a) else x.tape t := by
  fin_cases t <;> simp [backward, right, left, written]

def backwardMany : List (Fin 3) → Config 9 → Config 9
  | [], x => x
  | a :: rest, x => backwardMany rest (backward a x)

theorem backward_many_pos (as : List (Fin 3)) (x : Config 9) (t : Fin 9) :
    (backwardMany as x).pos t =
      if t = 0 ∨ t = 1 then x.pos t+as.length
      else if t = 7 then x.pos t-as.length else x.pos t := by
  induction as generalizing x with
  | nil => fin_cases t <;> simp [backwardMany]
  | cons a as ih =>
    rw [backwardMany, ih, backward_pos]
    fin_cases t <;> simp <;> omega

theorem backward_many_tape (as : List (Fin 3)) (x : Config 9) (t : Fin 9) :
    (backwardMany as x).tape t =
      if t = 0 ∨ t = 1 then fill (as.map symbol) (x.pos t) (x.tape t) else x.tape t := by
  induction as generalizing x with
  | nil => fin_cases t <;> simp [backwardMany, fill]
  | cons a as ih =>
    rw [backwardMany, ih]
    fin_cases t <;> simp [backward_tape, backward_pos, fill]

/-- The reverse-copy loop writes the encountered source letters in order
to A/B, consumes SOURCE leftward, and does not alter MARKS. -/
theorem backward_run (as : List (Fin 3)) (x : Config 9) (hp : x.pc = 260)
    (hpos : as.length ≤ x.pos 7)
    (hc : ∀ k (hk : k < as.length), x.tape 7 (x.pos 7-k) = symbol as[k]) :
    ∃ qs, Steps GalilFppMarkedCode.code x qs (backwardMany as x) ∧
      qs.length = 6*as.length ∧ (backwardMany as x).pc = 260 := by
  induction as generalizing x with
  | nil => exact ⟨[], .nil _, rfl, hp⟩
  | cons a as ih =>
    obtain ⟨qs, hs, hl⟩ := backward_step a x hp (hc 0 (by simp))
      (by simp only [List.length_cons] at hpos; omega)
    have htpos : as.length ≤ (backward a x).pos 7 := by
      simp only [List.length_cons] at hpos
      simp [backward_pos]; omega
    have htail : ∀ k (hk : k < as.length),
        (backward a x).tape 7 ((backward a x).pos 7-k) = symbol as[k] := by
      intro k hk
      have hh := hc (k+1) (by simp; omega)
      have he : x.pos 7-1-k = x.pos 7-(k+1) := by omega
      simpa [backward_tape, backward_pos, he] using hh
    obtain ⟨rs, hr, hrl, hpc⟩ := ih (backward a x) rfl htpos htail
    refine ⟨qs ++ rs, steps_append hs hr, ?_, hpc⟩
    simp only [List.length_append, List.length_cons]; omega

/-- At SOURCE's right marker, terminate MARKS and insert the private
separator in A/B before reversing the direction of source traversal. -/
def turn (x : Config 9) : Config 9 :=
  left 7 260 (right 1 276 (right 0 277
    (written 1 3 278 (written 0 3 279 (written 8 5 280 { x with pc := 281 })))))

theorem turn_step (x : Config 9) (hp : x.pc = 259)
    (hc : x.tape 7 (x.pos 7) = 5) (hpos : 0 < x.pos 7) :
    Steps GalilFppMarkedCode.code x [259,281,280,279,278,277,276] (turn x) := by
  let a : Config 9 := { x with pc := 281 }
  let b := written 8 5 280 a
  let c := written 0 3 279 b
  let d := written 1 3 278 c
  let e := right 0 277 d
  let f := right 1 276 e
  have hs : Steps GalilFppMarkedCode.code x [259] a := by
    simpa only [hp] using (Steps.step x a a _ [] (by rw [hp]; rfl)
      (.read _ _ _ _ (by simp [hc])) (.nil _))
  have hm : Steps GalilFppMarkedCode.code f [276] (turn x) :=
    .step _ _ _ _ [] rfl (.left _ _ _ (by simpa [f, e, d, c, b, a, right, written] using hpos)) (.nil _)
  exact steps_append (steps_append (steps_append (steps_append (steps_append
    (steps_append hs (write_step 8 5 280 a rfl)) (write_step 0 3 279 b rfl))
      (write_step 1 3 278 c rfl)) (right_step 0 277 d rfl)) (right_step 1 276 e rfl)) hm

def finish (x : Config 9) : Config 9 :=
  written 1 5 251 (written 0 5 257 { x with pc := 258 })

/-- The left source marker ends reverse copying and starts the rewind
phase with both prepared input tapes explicitly terminated. -/
theorem finish_step (x : Config 9) (hp : x.pc = 260)
    (hc : x.tape 7 (x.pos 7) = 4) :
    Steps GalilFppMarkedCode.code x [260,258,257] (finish x) := by
  let a : Config 9 := { x with pc := 258 }
  let b := written 0 5 257 a
  have hs : Steps GalilFppMarkedCode.code x [260] a := by
    simpa only [hp] using (Steps.step x a a _ [] (by rw [hp]; rfl)
      (.read _ _ _ _ (by simp [hc])) (.nil _))
  exact steps_append (steps_append hs (write_step 0 5 257 a rfl)) (write_step 1 5 251 b rfl)

#print axioms turn_step
#print axioms finish_step
#print axioms backward_run
#print axioms backward_many_tape
#print axioms forward_run
#print axioms forward_many_tape
#print axioms forward_step
end PalPeg.GalilFppPreparation
