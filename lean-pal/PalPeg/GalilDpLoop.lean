import PalPeg.GalilDpExhaustion

set_option autoImplicit false
namespace PalPeg.GalilDpLoop
open GalilFppWide GalilDpSearch GalilDpAdvance GalilDpExhaustion

/-- Physical invariants needed for progress. Output decoding and minimality
are separate obligations: they are not inferred from mere termination. -/
structure State (w : List (Fin 3)) (lower h : ℕ) (x : Config 12) : Prop where
  marks : x.tape 8 = GalilFppMarkedLayout.marks w
  second : x.tape 9 = GalilFppMarkedLayout.marks w
  firstPos : x.pos 8 = 2*h+1
  secondPos : x.pos 9 = 4*h+1
  lowerTape : x.tape 10 = GalilDpPrepared.lowerTape lower
  lowerPositive : 0 < x.pos 10
  lowerBound : x.pos 10 ≤ lower+1

theorem State.set_pc {w : List (Fin 3)} {lower h : ℕ} {x : Config 12}
    (hx : State w lower h x) (pc : ℕ) : State w lower h { x with pc := pc } :=
  ⟨hx.marks, hx.second, hx.firstPos, hx.secondPos, hx.lowerTape, hx.lowerPositive, hx.lowerBound⟩

theorem marks_bit (w : List (Fin 3)) (i : ℕ) (hi : 0 < i) (hn : i ≤ w.length) :
    GalilFppMarkedLayout.marks w i = 7 ∨ GalilFppMarkedLayout.marks w i = 8 := by
  by_cases hpal : (w.take i).reverse = w.take i <;>
    simp [GalilFppMarkedLayout.marks, Nat.ne_of_gt hi, hn, hpal]

theorem branch (w : List (Fin 3)) (lower h : ℕ) (x : Config 12)
    (hx : State w lower h x) (hp : x.pc = 348) (hin : 4*h+1 ≤ w.length) :
    (∃ y qs, Completed GalilDpCode.code x qs y ∧ qs.length ≤ 4 ∧ y.pc = 346) ∨
    (∃ y qs, Steps GalilDpCode.code x qs y ∧ qs.length ≤ 3 ∧ y.pc = 363 ∧ State w lower h y) := by
  by_cases hl : x.pos 10 ≤ lower
  · have hc : x.tape 10 (x.pos 10) = 8 := by
      rw [hx.lowerTape]
      simp [GalilDpPrepared.lowerTape, Nat.ne_of_gt hx.lowerPositive, hl]
    let y : Config 12 := { x with
      pc := 363
      pos := Function.update x.pos 10 (x.pos 10+1) }
    right
    refine ⟨y, _, skip_lower x hp hc, by decide, rfl, ?_⟩
    refine ⟨hx.marks, hx.second, ?_, ?_, hx.lowerTape, ?_, ?_⟩
    · simpa [y] using hx.firstPos
    · simpa [y] using hx.secondPos
    · simp [y]
    · simp [y]; omega
  · have he : x.pos 10 = lower+1 := by have := hx.lowerBound; omega
    have hc : x.tape 10 (x.pos 10) = 5 := by
      rw [hx.lowerTape, he]; simp [GalilDpPrepared.lowerTape]
    have hb9 : x.tape 9 (x.pos 9) = 7 ∨ x.tape 9 (x.pos 9) = 8 := by
      rw [hx.second, hx.secondPos]; exact marks_bit w _ (by omega) hin
    rcases hb9 with hs | hs
    · exact Or.inr ⟨_, _, skip_second x hp hc hs, by decide, rfl, hx.set_pc 363⟩
    · have hb8 : x.tape 8 (x.pos 8) = 7 ∨ x.tape 8 (x.pos 8) = 8 := by
        rw [hx.marks, hx.firstPos]; exact marks_bit w _ (by omega) (by omega)
      rcases hb8 with hm | hm
      · exact Or.inr ⟨_, _, skip_first x hp hc hs hm, by decide, rfl, hx.set_pc 363⟩
      · exact Or.inl ⟨_, _, candidate_found x hp hc hm hs, by decide, rfl⟩

theorem next_state (w : List (Fin 3)) (lower h : ℕ) (x : Config 12)
    (hx : State w lower h x) : State w lower (h+1) { next x with pc := 348 } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [next_tape] using hx.marks
  · simpa [next_tape] using hx.second
  · simp [next_pos, hx.firstPos]; omega
  · simp [next_pos, hx.secondPos]; omega
  · simpa [next_tape] using hx.lowerTape
  · simpa [next_pos] using hx.lowerPositive
  · simpa [next_pos] using hx.lowerBound

/-- Every valid positive candidate eventually reaches one of the actual
halt states. The bound is for the search loop alone, not FPP preparation. -/
theorem terminates (w : List (Fin 3)) (lower h : ℕ) (x : Config 12)
    (hx : State w lower h x) (hp : x.pc = 348) (hh : 0 < h)
    (hin : 4*h+1 ≤ w.length) :
    ∃ y qs, Completed GalilDpCode.code x qs y ∧
      qs.length ≤ 18*(w.length-h)+19 ∧ (y.pc = 346 ∨ y.pc = 347) := by
  suffices hall : ∀ fuel h (x : Config 12), w.length-h < fuel →
      State w lower h x → x.pc = 348 → 0 < h → 4*h+1 ≤ w.length →
      ∃ y qs, Completed GalilDpCode.code x qs y ∧
        qs.length ≤ 18*(w.length-h)+19 ∧ (y.pc = 346 ∨ y.pc = 347) by
    exact hall (w.length-h+1) h x (by omega) hx hp hh hin
  intro fuel
  induction fuel with
  | zero => intro h x hf; omega
  | succ fuel ih =>
    intro h x hf hx hp hh hin
    rcases branch w lower h x hx hp hin with done | skip
    · obtain ⟨y, qs, hs, hl, hy⟩ := done
      exact ⟨y, qs, hs, by omega, Or.inl hy⟩
    · obtain ⟨v, rs, hr, hrl, hvpc, hv⟩ := skip
      by_cases hn : 4*(h+1)+1 ≤ w.length
      · obtain ⟨ts, ht, htl⟩ := next_candidate w h v hvpc hv.marks hv.second hv.firstPos hv.secondPos hn
        obtain ⟨y, us, hu, hul, hy⟩ := ih (h+1) { next v with pc := 348 }
          (by omega) (next_state w lower h v hv) rfl (by omega) hn
        refine ⟨y, rs ++ ts ++ us, steps_completed (steps_append hr ht) hu, ?_, hy⟩
        simp only [List.length_append]
        omega
      · obtain ⟨y, ts, ht, htl, hy⟩ := exhausted w h v hh hvpc hv.marks hv.second
          hv.firstPos hv.secondPos hin (by omega)
        refine ⟨y, rs ++ ts, steps_completed hr ht, ?_, Or.inr hy⟩
        simp only [List.length_append]
        omega

#print axioms terminates
end PalPeg.GalilDpLoop
