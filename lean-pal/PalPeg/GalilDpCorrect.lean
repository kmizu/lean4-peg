import PalPeg.GalilDpCounters

set_option autoImplicit false
namespace PalPeg.GalilDpCorrect
open GalilFppWide GalilDpLoop GalilDpCounters GalilDpSearch

def Candidate (w : List (Fin 3)) (lower h : ℕ) : Prop :=
  lower < h ∧ 4*h+1 ≤ w.length ∧
    (w.take (2*h+1)).reverse = w.take (2*h+1) ∧
    (w.take (4*h+1)).reverse = w.take (4*h+1)

theorem accepts_candidate (w : List (Fin 3)) (lower h : ℕ) (x : Config 12)
    (hx : State w lower h x) (ht : Tracked lower h h x)
    (hp : x.pc = 348) (hc : Candidate w lower h) :
    Completed GalilDpCode.code x [348,365,364,346] { x with pc := 346 } ∧
      x.tape 11 = output h := by
  obtain ⟨hl, hn, hm, hs⟩ := hc
  have hlow : x.tape 10 (x.pos 10) = 5 := by
    rw [hx.lowerTape, ht.lowerPos, Nat.min_eq_right (by omega)]
    simp [GalilDpPrepared.lowerTape]
  have hmark : x.tape 8 (x.pos 8) = 8 := by
    rw [hx.marks, hx.firstPos]
    simp [GalilFppMarkedLayout.marks, hm, show 2*h+1 ≤ w.length by omega]
  have hsecond : x.tape 9 (x.pos 9) = 8 := by
    rw [hx.second, hx.secondPos]
    simp [GalilFppMarkedLayout.marks, hs, hn]
  exact ⟨candidate_found x hp hlow hmark hsecond, ht.outputTape⟩

/-- Every mathematically invalid in-range candidate is skipped by the
actual branch, preserving the exact output and advancing the lower cursor
precisely when required. -/
theorem rejects_candidate (w : List (Fin 3)) (lower h : ℕ) (x : Config 12)
    (hx : State w lower h x) (ht : Tracked lower h h x)
    (hp : x.pc = 348) (hh : 0 < h) (hn : 4*h+1 ≤ w.length)
    (hc : ¬ Candidate w lower h) :
    ∃ y qs, Steps GalilDpCode.code x qs y ∧ qs.length ≤ 3 ∧ y.pc = 363 ∧
      State w lower h y ∧ Tracked lower (h+1) h y := by
  by_cases hl : h ≤ lower
  · have hpos : x.pos 10 = h := by rw [ht.lowerPos, Nat.min_eq_left (by omega)]
    have hlow : x.tape 10 (x.pos 10) = 8 := by
      rw [hx.lowerTape, hpos]
      simp [GalilDpPrepared.lowerTape, Nat.ne_of_gt hh, hl]
    let y : Config 12 := { x with
      pc := 363
      pos := Function.update x.pos 10 (x.pos 10+1) }
    refine ⟨y, _, skip_lower x hp hlow, by decide, rfl, ?_, tracked_skip_lower ht hl⟩
    constructor
    · exact hx.marks
    · exact hx.second
    · simpa [y] using hx.firstPos
    · simpa [y] using hx.secondPos
    · exact hx.lowerTape
    · simp [y]
    · simp [y, hpos]; omega
  · have hl' : lower < h := by omega
    have hlow : x.tape 10 (x.pos 10) = 5 := by
      rw [hx.lowerTape, ht.lowerPos, Nat.min_eq_right (by omega)]
      simp [GalilDpPrepared.lowerTape]
    by_cases hs : (w.take (4*h+1)).reverse = w.take (4*h+1)
    · have hm : (w.take (2*h+1)).reverse ≠ w.take (2*h+1) := by
        intro he; exact hc ⟨hl', hn, he, hs⟩
      have hsecond : x.tape 9 (x.pos 9) = 8 := by
        rw [hx.second, hx.secondPos]; simp [GalilFppMarkedLayout.marks, hs, hn]
      have hmark : x.tape 8 (x.pos 8) = 7 := by
        rw [hx.marks, hx.firstPos]
        simp [GalilFppMarkedLayout.marks, hm, show 2*h+1 ≤ w.length by omega]
      exact ⟨_, _, skip_first x hp hlow hsecond hmark, by decide, rfl,
        hx.set_pc 363, tracked_skip_mark ht hl'⟩
    · have hsecond : x.tape 9 (x.pos 9) = 7 := by
        rw [hx.second, hx.secondPos]; simp [GalilFppMarkedLayout.marks, hs, hn]
      exact ⟨_, _, skip_second x hp hlow hsecond, by decide, rfl,
        hx.set_pc 363, tracked_skip_mark ht hl'⟩

/-- Either OUTPUT encodes the least valid candidate at or after first,
or failure is justified by absence of every such candidate. -/
def Result (w : List (Fin 3)) (lower first : ℕ) (y : Config 12) : Prop :=
  (∃ k, first ≤ k ∧ Candidate w lower k ∧
    (∀ j, first ≤ j → j < k → ¬ Candidate w lower j) ∧
    y.pc = 346 ∧ y.tape 11 = output k ∧ y.pos 11 = k) ∨
  (y.pc = 347 ∧ ∀ k, first ≤ k → ¬ Candidate w lower k)

theorem result_previous {w : List (Fin 3)} {lower h : ℕ} {y : Config 12}
    (hn : ¬ Candidate w lower h) (hr : Result w lower (h+1) y) : Result w lower h y := by
  rcases hr with ⟨k, hk, hc, hmin, hp, ht⟩ | ⟨hp, hnone⟩
  · left
    refine ⟨k, by omega, hc, ?_, hp, ht⟩
    intro j hj hjk
    by_cases he : j = h
    · simpa [he] using hn
    · exact hmin j (by omega) hjk
  · right
    refine ⟨hp, ?_⟩
    intro k hk
    by_cases he : k = h
    · simpa [he] using hn
    · exact hnone k (by omega)

/-- Full search-loop correctness, including minimality and exact unary
OUTPUT, from a valid positive candidate entry. -/
theorem correct_loop (w : List (Fin 3)) (lower h : ℕ) (x : Config 12)
    (hx : State w lower h x) (ht : Tracked lower h h x)
    (hp : x.pc = 348) (hh : 0 < h) (hin : 4*h+1 ≤ w.length) :
    ∃ y qs, Completed GalilDpCode.code x qs y ∧ Result w lower h y := by
  classical
  suffices hall : ∀ fuel h (x : Config 12), w.length-h < fuel →
      State w lower h x → Tracked lower h h x → x.pc = 348 → 0 < h →
      4*h+1 ≤ w.length → ∃ y qs, Completed GalilDpCode.code x qs y ∧ Result w lower h y by
    exact hall (w.length-h+1) h x (by omega) hx ht hp hh hin
  intro fuel
  induction fuel with
  | zero => intro h x hf; omega
  | succ fuel ih =>
    intro h x hf hx ht hp hh hin
    by_cases hc : Candidate w lower h
    · obtain ⟨hr, hout⟩ := accepts_candidate w lower h x hx ht hp hc
      exact ⟨_, _, hr, Or.inl ⟨h, le_refl _, hc, by intro j hj hjh; omega, rfl, hout, ht.outputPos⟩⟩
    · obtain ⟨v, rs, hr, _, hvpc, hv, hvt⟩ := rejects_candidate w lower h x hx ht hp hh hin hc
      by_cases hn : 4*(h+1)+1 ≤ w.length
      · obtain ⟨ts, hts, _⟩ := GalilDpAdvance.next_candidate w h v hvpc
          hv.marks hv.second hv.firstPos hv.secondPos hn
        obtain ⟨y, us, hus, hy⟩ := ih (h+1) { GalilDpAdvance.next v with pc := 348 }
          (by omega) (next_state w lower h v hv) (tracked_next hvt) rfl (by omega) hn
        exact ⟨y, _, GalilDpExhaustion.steps_completed (steps_append hr hts) hus,
          result_previous hc hy⟩
      · obtain ⟨y, ts, hts, _, hy⟩ := GalilDpExhaustion.exhausted w h v hh hvpc
          hv.marks hv.second hv.firstPos hv.secondPos hin (by omega)
        refine ⟨y, _, GalilDpExhaustion.steps_completed hr hts, Or.inr ⟨hy, ?_⟩⟩
        intro k hk hgood
        by_cases he : k = h
        · exact hc (by simpa [he] using hgood)
        · have := hgood.2.1
          omega

/-- The actual Scala DP program computes the least h above lower whose
two prefix lengths are palindromes, or correctly reports absence. This
starts at the fresh physical preload, not at an assumed search state. -/
theorem initial_correct (w : List (Fin 3)) (lower : ℕ) :
    ∃ y qs, Completed GalilDpCode.code (GalilDpPrepared.initial w lower) qs y ∧
      Result w lower 0 y := by
  by_cases hn : 5 ≤ w.length
  · obtain ⟨x, qs, hr, hp, h8, h9, h7, ht7, hm, hs, h10, h11, hl, ht11⟩ :=
      GalilDpPrepared.prepared w lower
    have hb := GalilDpStart.start_run x hp
      (by rw [hm, h8]; simp [GalilFppMarkedLayout.marks])
      (by rw [hs, h9]; simp [GalilFppMarkedLayout.marks])
    have hx := GalilDpStart.start_state w lower x hm hs hl h8 h9 h10
    have htrack := tracked_start lower x h10 h11 ht11
    obtain ⟨rs, hrs, _⟩ := GalilDpAdvance.next_candidate w 0 (GalilDpStart.start x) rfl
      hx.marks hx.second hx.firstPos hx.secondPos hn
    obtain ⟨y, ts, hts, hy⟩ := correct_loop w lower 1
      { GalilDpAdvance.next (GalilDpStart.start x) with pc := 348 }
      (next_state w lower 0 _ hx) (tracked_next htrack) rfl (by decide) hn
    have hn0 : ¬ Candidate w lower 0 := by intro hc; have := hc.1; omega
    exact ⟨y, _, GalilDpExhaustion.steps_completed (steps_append hr (steps_append hb hrs)) hts,
      result_previous hn0 hy⟩
  · obtain ⟨y, qs, hr, hy⟩ := GalilDpStart.short_terminates w lower (by omega)
    refine ⟨y, qs, hr, Or.inr ⟨hy, ?_⟩⟩
    intro k hk hc
    have := hc.1
    have := hc.2.1
    omega

#print axioms accepts_candidate
#print axioms rejects_candidate
#print axioms correct_loop
#print axioms initial_correct
end PalPeg.GalilDpCorrect
