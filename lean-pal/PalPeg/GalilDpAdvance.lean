import PalPeg.GalilDpSearch

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PalPeg.GalilDpAdvance
open GalilFppWide

def tape (q : Fin 6) : Fin 12 := if q.val < 4 then 9 else 8
def choices (q : Fin 6) : List (Fin 9 × ℕ) :=
  [(4,350+2*q.val),(7,350+2*q.val),(8,350+2*q.val),(5,347)]

theorem rows : ∀ q : Fin 6,
    GalilDpCode.code[351+2*q.val]? = some (.read (tape q) (choices q)) ∧
    GalilDpCode.code[350+2*q.val]? = some (.move (tape q) true (349+2*q.val)) := by decide

def advance (q : Fin 6) (x : Config 12) : Config 12 :=
  { x with
    pc := 349+2*q.val
    pos := Function.update x.pos (tape q) (x.pos (tape q)+1) }

/-- Each skipped cell is checked before its head is advanced. -/
theorem guard_move (q : Fin 6) (x : Config 12) (hp : x.pc = 351+2*q.val)
    (hs : x.tape (tape q) (x.pos (tape q)) ∈ ([4,7,8] : List (Fin 9))) :
    Steps GalilDpCode.code x [351+2*q.val,350+2*q.val] (advance q x) := by
  let a : Config 12 := { x with pc := 350+2*q.val }
  have hm : (x.tape (tape q) (x.pos (tape q)),350+2*q.val) ∈ choices q := by
    simp at hs
    rcases hs with h | h | h <;> simp [choices, h]
  have hrun : Steps GalilDpCode.code x [x.pc,350+2*q.val] (advance q x) := by
    refine .step x a (advance q x) _ _ (by rw [hp]; exact (rows q).1)
      (.read _ _ _ _ hm) ?_
    exact .step a (advance q x) (advance q x) _ [] (rows q).2 (.right _ _ _) (.nil _)
  simpa only [hp] using hrun

/-- All six guards terminate at END without moving any head. -/
theorem guard_end (q : Fin 6) (x : Config 12) (hp : x.pc = 351+2*q.val)
    (hs : x.tape (tape q) (x.pos (tape q)) = 5) :
    Completed GalilDpCode.code x [351+2*q.val,347] { x with pc := 347 } := by
  let y : Config 12 := { x with pc := 347 }
  have hrun : Completed GalilDpCode.code x [x.pc,347] y := by
    exact .step x y y _ _ (by rw [hp]; exact (rows q).1)
      (.read _ _ _ _ (by simp [choices, hs])) (.halt y rfl)
  simpa only [hp] using hrun

def bump (x : Config 12) : Config 12 :=
  { x with
    pc := 361
    pos := Function.update x.pos 11 (x.pos 11+1)
    tape := Function.update x.tape 11 (Function.update (x.tape 11) (x.pos 11+1) 8) }

theorem bump_run (x : Config 12) (hp : x.pc = 363) :
    Steps GalilDpCode.code x [363,362] (bump x) := by
  let a : Config 12 := { x with
    pc := 362
    pos := Function.update x.pos 11 (x.pos 11+1) }
  have hrun : Steps GalilDpCode.code x [x.pc,362] (bump x) := by
    refine .step x a (bump x) (.move 11 true 362) _ (by rw [hp]; rfl) (.right _ _ _) ?_
    exact .step a (bump x) (bump x) (.write 11 8 361) [] rfl (.write _ _ _ _) (.nil _)
  simpa only [hp] using hrun

def next (x : Config 12) : Config 12 :=
  advance 0 (advance 1 (advance 2 (advance 3 (advance 4 (advance 5 (bump x))))))

/-- The complete next-h block: append one output bit, move MARKS by two,
and SECOND by four, with an actual guard at every traversed cell. -/
theorem next_run (x : Config 12) (hp : x.pc = 363)
    (hm : ∀ k < 2, x.tape 8 (x.pos 8+k) ∈ ([4,7,8] : List (Fin 9)))
    (hs : ∀ k < 4, x.tape 9 (x.pos 9+k) ∈ ([4,7,8] : List (Fin 9))) :
    ∃ qs, Steps GalilDpCode.code x qs (next x) ∧ qs.length = 14 := by
  have h5 := guard_move 5 (bump x) rfl (by simpa [bump, tape] using hm 0 (by omega))
  have h4 := guard_move 4 (advance 5 (bump x)) rfl
    (by simpa [advance, bump, tape] using hm 1 (by omega))
  have h3 := guard_move 3 (advance 4 (advance 5 (bump x))) rfl
    (by simpa [advance, bump, tape] using hs 0 (by omega))
  have h2 := guard_move 2 (advance 3 (advance 4 (advance 5 (bump x)))) rfl
    (by simpa [advance, bump, tape] using hs 1 (by omega))
  have h1 := guard_move 1 (advance 2 (advance 3 (advance 4 (advance 5 (bump x))))) rfl
    (by simpa [advance, bump, tape, Nat.add_assoc] using hs 2 (by omega))
  have h0 := guard_move 0 (advance 1 (advance 2 (advance 3 (advance 4 (advance 5 (bump x)))))) rfl
    (by simpa [advance, bump, tape, Nat.add_assoc] using hs 3 (by omega))
  exact ⟨_, steps_append (bump_run x hp) (steps_append h5 (steps_append h4
    (steps_append h3 (steps_append h2 (steps_append h1 h0))))), rfl⟩

theorem next_pc (x : Config 12) : (next x).pc = 349 := rfl

theorem next_pos (x : Config 12) (t : Fin 12) :
    (next x).pos t = if t = 8 then x.pos t+2 else if t = 9 then x.pos t+4
      else if t = 11 then x.pos t+1 else x.pos t := by
  by_cases h8 : t = 8
  · subst t; simp [next, advance, bump, tape, Nat.add_assoc]
  · by_cases h9 : t = 9
    · subst t; simp [next, advance, bump, tape, Nat.add_assoc]
    · by_cases h11 : t = 11
      · subst t; simp [next, advance, bump, tape]
      · simp [next, advance, bump, tape, h8, h9, h11]

theorem next_tape (x : Config 12) :
    (next x).tape = Function.update x.tape 11 (Function.update (x.tape 11) (x.pos 11+1) 8) := rfl

theorem marks_body (w : List (Fin 3)) (i : ℕ) (hi : 0 < i) (hn : i ≤ w.length) :
    GalilFppMarkedLayout.marks w i ∈ ([4,7,8] : List (Fin 9)) := by
  by_cases hpal : (w.take i).reverse = w.take i <;>
    simp [GalilFppMarkedLayout.marks, Nat.ne_of_gt hi, hn, hpal]

/-- Actual marked-tape contents discharge every skipped-cell premise for
an in-range successor candidate; the heads encode the next pair of lengths. -/
theorem marked_next (w : List (Fin 3)) (h : ℕ) (x : Config 12)
    (hp : x.pc = 363) (hm : x.tape 8 = GalilFppMarkedLayout.marks w)
    (hs : x.tape 9 = GalilFppMarkedLayout.marks w)
    (h8 : x.pos 8 = 2*h+1) (h9 : x.pos 9 = 4*h+1)
    (hn : 4*(h+1)+1 ≤ w.length) :
    ∃ qs, Steps GalilDpCode.code x qs (next x) ∧ qs.length = 14 ∧
      (next x).pos 8 = 2*(h+1)+1 ∧ (next x).pos 9 = 4*(h+1)+1 ∧
      (next x).tape 8 = GalilFppMarkedLayout.marks w ∧
      (next x).tape 9 = GalilFppMarkedLayout.marks w := by
  obtain ⟨qs, hrun, hlen⟩ := next_run x hp
    (by intro k hk; rw [hm, h8]; exact marks_body w _ (by omega) (by omega))
    (by intro k hk; rw [hs, h9]; exact marks_body w _ (by omega) (by omega))
  refine ⟨qs, hrun, hlen, ?_, ?_, ?_, ?_⟩
  · simp [next_pos, h8]; omega
  · simp [next_pos, h9]; omega
  · rw [next_tape]; simpa using hm
  · rw [next_tape]; simpa using hs

theorem check_candidate (x : Config 12) (hp : x.pc = 349)
    (hs : x.tape 9 (x.pos 9) ∈ ([7,8] : List (Fin 9))) :
    Steps GalilDpCode.code x [349] { x with pc := 348 } := by
  have hm : (x.tape 9 (x.pos 9),348) ∈ ([(7,348),(8,348),(5,347)] : List (Fin 9 × ℕ)) := by
    simpa using hs
  simpa only [hp] using
    (Steps.step x { x with pc := 348 } { x with pc := 348 }
      (.read 9 [(7,348),(8,348),(5,347)]) [] (by rw [hp]; rfl)
      (.read _ _ _ _ hm) (.nil _))

/-- The full successful successor path reaches the candidate test in
exactly fifteen instructions. A following iteration can reuse this entry. -/
theorem next_candidate (w : List (Fin 3)) (h : ℕ) (x : Config 12)
    (hp : x.pc = 363) (hm : x.tape 8 = GalilFppMarkedLayout.marks w)
    (hs : x.tape 9 = GalilFppMarkedLayout.marks w)
    (h8 : x.pos 8 = 2*h+1) (h9 : x.pos 9 = 4*h+1)
    (hn : 4*(h+1)+1 ≤ w.length) :
    ∃ qs, Steps GalilDpCode.code x qs { next x with pc := 348 } ∧ qs.length = 15 := by
  obtain ⟨qs, hr, hlen, hp8, hp9, ht8, ht9⟩ := marked_next w h x hp hm hs h8 h9 hn
  have hb : (next x).tape 9 ((next x).pos 9) ∈ ([7,8] : List (Fin 9)) := by
    rw [hp9, ht9]
    by_cases hpal : (w.take (4*(h+1)+1)).reverse = w.take (4*(h+1)+1) <;>
      simp [GalilFppMarkedLayout.marks, hn, hpal]
  exact ⟨qs ++ [349], steps_append hr (check_candidate (next x) rfl hb), by simp [hlen]⟩

#print axioms next_run
#print axioms guard_end
#print axioms marked_next
#print axioms next_candidate
end PalPeg.GalilDpAdvance
