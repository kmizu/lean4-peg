import PalPeg.GalilDpLoop

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PalPeg.GalilDpStart
open GalilFppWide GalilDpAdvance GalilDpExhaustion GalilDpLoop

def start (x : Config 12) : Config 12 :=
  { x with
    pc := 363
    tape := Function.update x.tape 11 (Function.update (x.tape 11) (x.pos 11) 4)
    pos := Function.update (Function.update (Function.update x.pos 10 (x.pos 10+1))
      8 (x.pos 8+1)) 9 (x.pos 9+1) }

/-- The literal six instructions before next-h: initialize OUTPUT's
left marker and move LOWER, MARKS and SECOND past their left markers. -/
theorem start_run (x : Config 12) (hp : x.pc = 372)
    (hm : x.tape 8 (x.pos 8) = 4) (hs : x.tape 9 (x.pos 9) = 4) :
    Steps GalilDpCode.code x [372,371,370,369,368,367] (start x) := by
  let a : Config 12 := { x with
    pc := 371
    tape := Function.update x.tape 11 (Function.update (x.tape 11) (x.pos 11) 4) }
  let b : Config 12 := { a with pc := 370, pos := Function.update a.pos 10 (a.pos 10+1) }
  let c : Config 12 := { b with pc := 369 }
  let d : Config 12 := { c with pc := 368, pos := Function.update c.pos 8 (c.pos 8+1) }
  let e : Config 12 := { d with pc := 367 }
  have hr : Steps GalilDpCode.code x [x.pc,371,370,369,368,367] (start x) := by
    refine .step x a (start x) (.write 11 4 371) _ (by rw [hp]; rfl) (.write _ _ _ _) ?_
    refine .step a b (start x) (.move 10 true 370) _ rfl (.right _ _ _) ?_
    refine .step b c (start x) (.read 8 [(4,369),(7,369),(8,369),(5,347)]) _ rfl
      (.read _ _ _ _ (by simp [b, a, hm])) ?_
    refine .step c d (start x) (.move 8 true 368) _ rfl (.right _ _ _) ?_
    refine .step d e (start x) (.read 9 [(4,367),(7,367),(8,367),(5,347)]) _ rfl
      (.read _ _ _ _ (by simp [d, c, b, a, hs])) ?_
    exact .step e (start x) (start x) (.move 9 true 363) [] rfl (.right _ _ _) (.nil _)
  simpa only [hp] using hr

theorem start_state (w : List (Fin 3)) (lower : ℕ) (x : Config 12)
    (hm : x.tape 8 = GalilFppMarkedLayout.marks w)
    (hs : x.tape 9 = GalilFppMarkedLayout.marks w)
    (hl : x.tape 10 = GalilDpPrepared.lowerTape lower)
    (h8 : x.pos 8 = 0) (h9 : x.pos 9 = 0) (h10 : x.pos 10 = 0) :
    State w lower 0 (start x) := by
  constructor
  · simpa [start] using hm
  · simpa [start] using hs
  · simp [start, h8]
  · simp [start, h9]
  · simpa [start] using hl
  · simp [start, h10]
  · simp [start, h10]

/-- Fresh DP executions on inputs admitting a first candidate reach an
actual halt. This statement does not yet identify the unary result. -/
theorem long_terminates (w : List (Fin 3)) (lower : ℕ) (hn : 5 ≤ w.length) :
    ∃ y qs, Completed GalilDpCode.code (GalilDpPrepared.initial w lower) qs y ∧
      (y.pc = 346 ∨ y.pc = 347) := by
  obtain ⟨x, qs, hr, hp, h8, h9, h7, ht7, hm, hs, h10, h11, hl, ht11⟩ :=
    GalilDpPrepared.prepared w lower
  have hb := start_run x hp
    (by rw [hm, h8]; simp [GalilFppMarkedLayout.marks])
    (by rw [hs, h9]; simp [GalilFppMarkedLayout.marks])
  have hx := start_state w lower x hm hs hl h8 h9 h10
  obtain ⟨rs, hs', _⟩ := next_candidate w 0 (start x) rfl hx.marks hx.second hx.firstPos hx.secondPos hn
  obtain ⟨y, ts, ht, _, hy⟩ := GalilDpLoop.terminates w lower 1 { next (start x) with pc := 348 }
    (next_state w lower 0 (start x) hx) rfl (by decide) hn
  exact ⟨y, _, steps_completed (steps_append hr (steps_append hb hs')) ht, hy⟩

/-- There is no positive double-palindrome candidate on fewer than five
symbols. The initial next-h block stops at a physical end guard. -/
theorem short_next (w : List (Fin 3)) (x : Config 12) (hn : w.length < 5)
    (hp : x.pc = 363) (hm : x.tape 8 = GalilFppMarkedLayout.marks w)
    (hs : x.tape 9 = GalilFppMarkedLayout.marks w)
    (h8 : x.pos 8 = 1) (h9 : x.pos 9 = 1) :
    ∃ y qs, Completed GalilDpCode.code x qs y ∧ qs.length ≤ 16 ∧ y.pc = 347 := by
  by_cases hroom : 2 ≤ w.length
  · exact exhausted_of_room w 0 x hroom hp hm hs h8 h9 (by omega) hn
  by_cases hz : w.length = 0
  · have hend : (bump x).tape (tape 5) ((bump x).pos (tape 5)) = 5 := by
      simpa [bump, tape, hm, h8, hz] using marks_end w
    exact ⟨_, _, steps_completed (bump_run x hp) (guard_end 5 (bump x) rfl hend), by decide, rfl⟩
  have hn1 : w.length = 1 := by omega
  have h5 := guard_move 5 (bump x) rfl
    (by simpa [bump, tape, hm, h8] using marks_body w 1 (by decide) (by omega))
  have hend : (advance 5 (bump x)).tape (tape 4) ((advance 5 (bump x)).pos (tape 4)) = 5 := by
    simpa [advance, bump, tape, hm, h8, hn1] using marks_end w
  exact ⟨_, _, steps_completed (steps_append (bump_run x hp) h5)
    (guard_end 4 (advance 5 (bump x)) rfl hend), by decide, rfl⟩

theorem short_terminates (w : List (Fin 3)) (lower : ℕ) (hn : w.length < 5) :
    ∃ y qs, Completed GalilDpCode.code (GalilDpPrepared.initial w lower) qs y ∧ y.pc = 347 := by
  obtain ⟨x, qs, hr, hp, h8, h9, h7, ht7, hm, hs, h10, h11, hl, ht11⟩ :=
    GalilDpPrepared.prepared w lower
  have hb := start_run x hp
    (by rw [hm, h8]; simp [GalilFppMarkedLayout.marks])
    (by rw [hs, h9]; simp [GalilFppMarkedLayout.marks])
  have hx := start_state w lower x hm hs hl h8 h9 h10
  obtain ⟨y, rs, hs', _, hy⟩ := short_next w (start x) hn rfl hx.marks hx.second hx.firstPos hx.secondPos
  exact ⟨y, _, steps_completed (steps_append hr hb) hs', hy⟩

/-- The actual exported twelve-tape DP program terminates on every fresh
input and every unary lower bound, including empty and short inputs.
Correct decoding and minimality of a successful output are not asserted. -/
theorem initial_terminates (w : List (Fin 3)) (lower : ℕ) :
    ∃ y qs, Completed GalilDpCode.code (GalilDpPrepared.initial w lower) qs y ∧
      (y.pc = 346 ∨ y.pc = 347) := by
  by_cases hn : 5 ≤ w.length
  · exact long_terminates w lower hn
  · obtain ⟨y, qs, hs, hy⟩ := short_terminates w lower (by omega)
    exact ⟨y, qs, hs, Or.inr hy⟩

#print axioms long_terminates
#print axioms initial_terminates
end PalPeg.GalilDpStart
