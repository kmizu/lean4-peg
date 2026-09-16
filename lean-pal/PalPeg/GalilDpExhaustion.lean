import PalPeg.GalilDpAdvance

set_option autoImplicit false
namespace PalPeg.GalilDpExhaustion
open GalilFppWide GalilDpAdvance

theorem steps_completed {n : ℕ} {code : List (Instruction n)}
    {x y z : Config n} {qs rs : List ℕ}
    (hs : Steps code x qs y) (hr : Completed code y rs z) :
    Completed code x (qs ++ rs) z := by
  induction hs with
  | nil => exact hr
  | step x y z i qs hi he hs ih => exact .step _ _ _ _ _ hi he (ih hr)

theorem marks_end (w : List (Fin 3)) :
    GalilFppMarkedLayout.marks w (w.length+1) = 5 := by
  simp [GalilFppMarkedLayout.marks]

/-- With room for the two MARKS guards, an out-of-range successor reaches
the real failure halt in at most sixteen instructions. This also covers
the initial h=0 search when the source has at least two symbols. -/
theorem exhausted_of_room (w : List (Fin 3)) (h : ℕ) (x : Config 12)
    (hroom : 2*h+2 ≤ w.length) (hp : x.pc = 363)
    (hm : x.tape 8 = GalilFppMarkedLayout.marks w)
    (hs : x.tape 9 = GalilFppMarkedLayout.marks w)
    (h8 : x.pos 8 = 2*h+1) (h9 : x.pos 9 = 4*h+1)
    (hin : 4*h+1 ≤ w.length) (hout : w.length < 4*(h+1)+1) :
    ∃ y qs, Completed GalilDpCode.code x qs y ∧ qs.length ≤ 16 ∧ y.pc = 347 := by
  let a := advance 4 (advance 5 (bump x))
  let b := advance 3 a
  let c := advance 2 b
  let d := advance 1 c
  let e := advance 0 d
  have h5 := guard_move 5 (bump x) rfl
    (by simpa [bump, tape, hm, h8] using marks_body w (2*h+1) (by omega) (by omega))
  have h4 := guard_move 4 (advance 5 (bump x)) rfl
    (by simpa [advance, bump, tape, hm, h8, Nat.add_assoc] using
      marks_body w (2*h+2) (by omega) (by omega))
  have h3 := guard_move 3 a rfl
    (by simpa [a, advance, bump, tape, hs, h9] using marks_body w (4*h+1) (by omega) hin)
  have hb : Steps GalilDpCode.code x [363,362,361,360,359,358,357,356] b :=
    steps_append (bump_run x hp) (steps_append h5 (steps_append h4 h3))
  by_cases hn1 : w.length = 4*h+1
  · have hend : b.tape 9 (b.pos 9) = 5 := by
      simpa [b, a, advance, bump, tape, hs, h9, hn1, Nat.add_assoc] using marks_end w
    exact ⟨_, _, steps_completed hb (guard_end 2 b rfl hend), by decide, rfl⟩
  have h2 := guard_move 2 b rfl
    (by simpa [b, a, advance, bump, tape, hs, h9, Nat.add_assoc] using
      marks_body w (4*h+2) (by omega) (by omega))
  have hc : Steps GalilDpCode.code x [363,362,361,360,359,358,357,356,355,354] c :=
    steps_append hb h2
  by_cases hn2 : w.length = 4*h+2
  · have hend : c.tape 9 (c.pos 9) = 5 := by
      simpa [c, b, a, advance, bump, tape, hs, h9, hn2, Nat.add_assoc] using marks_end w
    exact ⟨_, _, steps_completed hc (guard_end 1 c rfl hend), by decide, rfl⟩
  have h1 := guard_move 1 c rfl
    (by simpa [c, b, a, advance, bump, tape, hs, h9, Nat.add_assoc] using
      marks_body w (4*h+3) (by omega) (by omega))
  have hd : Steps GalilDpCode.code x [363,362,361,360,359,358,357,356,355,354,353,352] d :=
    steps_append hc h1
  by_cases hn3 : w.length = 4*h+3
  · have hend : d.tape 9 (d.pos 9) = 5 := by
      simpa [d, c, b, a, advance, bump, tape, hs, h9, hn3, Nat.add_assoc] using marks_end w
    exact ⟨_, _, steps_completed hd (guard_end 0 d rfl hend), by decide, rfl⟩
  have hn4 : w.length = 4*h+4 := by omega
  have h0 := guard_move 0 d rfl
    (by simpa [d, c, b, a, advance, bump, tape, hs, h9, Nat.add_assoc] using
      marks_body w (4*h+4) (by omega) (by omega))
  have he : Steps GalilDpCode.code x [363,362,361,360,359,358,357,356,355,354,353,352,351,350] e :=
    steps_append hd h0
  have hend : e.tape 9 (e.pos 9) = 5 := by
    simpa [e, d, c, b, a, advance, bump, tape, hs, h9, hn4, Nat.add_assoc] using marks_end w
  exact ⟨_, _, steps_completed he (GalilDpSearch.end_guard e rfl hend), by decide, rfl⟩

theorem exhausted (w : List (Fin 3)) (h : ℕ) (x : Config 12)
    (hh : 0 < h) (hp : x.pc = 363)
    (hm : x.tape 8 = GalilFppMarkedLayout.marks w)
    (hs : x.tape 9 = GalilFppMarkedLayout.marks w)
    (h8 : x.pos 8 = 2*h+1) (h9 : x.pos 9 = 4*h+1)
    (hin : 4*h+1 ≤ w.length) (hout : w.length < 4*(h+1)+1) :
    ∃ y qs, Completed GalilDpCode.code x qs y ∧ qs.length ≤ 16 ∧ y.pc = 347 :=
  exhausted_of_room w h x (by omega) hp hm hs h8 h9 hin hout

#print axioms exhausted
end PalPeg.GalilDpExhaustion
