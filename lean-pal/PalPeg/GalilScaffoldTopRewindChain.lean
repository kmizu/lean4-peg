import PalPeg.GalilScaffoldTopFallbackChain

/-!
# The fallback chain: Choose → Rewind → ReplayStart

From the state left by `fpp_then_markEnd` (choose mode, `odd = false`,
MARKS = `marks w` with FIRST at cell 1, head on cell `|w|`, `|w|` even), the
choose walk selects cell `2r+1` with `r = chosenRadius w` — the longest odd
palindromic prefix of the reversed window — and the rewind walk brings L
back `2r` places and C back `r` places from R, with `length = 2r+1` and
`radius = r`, then resets the FPP program and enters `replayStart`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

theorem iterate_inc_ofNat (n k : ℕ) :
    GalilScaffoldCounter.inc^[n] (GalilScaffoldCounter.ofNat k) = GalilScaffoldCounter.ofNat (k+n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, GalilScaffoldCounter.inc_ofNat]; rfl

theorem reset_eq_ofNat : GalilScaffoldCounter.reset = GalilScaffoldCounter.ofNat 0 := rfl

theorem oddAt_false (j : ℕ) : oddAt false j = true ↔ j % 2 = 1 := by
  unfold oddAt
  by_cases h : j % 2 = 0
  · rw [if_pos h]
    constructor
    · intro h'; cases h'
    · intro h'; omega
  · rw [if_neg h]
    constructor
    · intro _; omega
    · intro _; rfl

theorem marks_val (w : List (Fin 3)) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    GalilFppMarkedLayout.marks w i = 7 ∨ GalilFppMarkedLayout.marks w i = 8 := by
  unfold GalilFppMarkedLayout.marks
  have : i ≠ 0 := by omega
  simp only [this, ite_false, h2, ite_true]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem choose_then_rewind (P : Shared) (q : ℕ) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8)
    (delay : ℕ) (c : Control) (hm : c.mode = .choose) (ho : c.odd = false) (s : GalilVM) (hi : ShiftIdle s)
    (w : List (Fin 3)) (hw : 1 ≤ w.length) (heven : w.length % 2 = 0) (r : ℕ) (hr : r = chosenRadius w)
    (hden : GalilScaffoldTape.denote (marksTape s.fpp) = Function.update (GalilFppMarkedLayout.marks w) 1 first)
    (hhead : GalilScaffoldTape.head (marksTape s.fpp) = w.length) :
    ∃ y : RewindVM, Steps (galilFrame P q first) delay ((w.length - (2*r+1) + 1) + (2*r + 1)) ⟨c, s⟩
        ⟨{c with mode := .replayStart, odd := oddAt c.odd (w.length - (2*r+1)), pair := pairAt (2*r)},
          rewindLens.set s y⟩ ∧
      y.left = GalilScaffoldInputHead.left^[2*r] s.right ∧
      y.center = GalilScaffoldInputHead.left^[r] s.right ∧ y.right = s.right ∧
      y.length = GalilScaffoldCounter.ofNat (2*r+1) ∧ y.radius = GalilScaffoldCounter.ofNat r ∧
      y.fpp.program = GalilScaffoldControl.reset 320 y.fpp.program ∧ ShiftIdle (rewindLens.set s y) := by
  have hne : w ≠ [] := by intro h; rw [h] at hw; simp at hw
  have hspec := chosen_spec w hne
  rw [← hr] at hspec
  obtain ⟨hr1, hpal⟩ := hspec
  have hcell : ∀ i, 2 ≤ i → GalilScaffoldTape.denote (marksTape s.fpp) i = GalilFppMarkedLayout.marks w i := by
    intro i hi
    rw [hden, Function.update_of_ne (by omega)]
  have hcell1 : GalilScaffoldTape.denote (marksTape s.fpp) 1 = first := by
    rw [hden, Function.update_self]
  have hget : (rewindLens.get s).marks = marksTape s.fpp := rfl
  have hnotfirst : ∀ i, 2 ≤ i → i ≤ w.length → GalilScaffoldTape.denote (marksTape s.fpp) i ≠ first := by
    intro i hi2 hiw h
    rw [hcell i hi2] at h
    rcases marks_val w i (by omega) hiw with hv | hv
    · rw [hv] at h; exact h7 h.symm
    · rw [hv] at h; exact h8 h.symm
  -- ## choose
  have hkle : w.length - (2*r+1) ≤ GalilScaffoldTape.head (rewindLens.get s).marks := by
    rw [hget, hhead]; omega
  have hno : ∀ j, j < w.length - (2*r+1) → ¬ (oddAt c.odd j = true ∧ SetAt first (rewindLens.get s) j) := by
    intro j hj ⟨hoj, hset⟩
    rw [ho, oddAt_false] at hoj
    unfold SetAt at hset
    rw [hget, hhead] at hset
    have hi2 : 2 ≤ w.length - j := by omega
    have hiw : w.length - j ≤ w.length := by omega
    rcases hset with hset | hset
    · rw [hcell _ hi2, marks_cell] at hset
      obtain ⟨_, _, hp⟩ := hset
      -- the cell `|w|-j` is odd: `|w|-j = 2r'+1` with `r' > r`
      have hodd' : (w.length - j) % 2 = 1 := by omega
      have hr' := chosen_greatest w ((w.length - j - 1)/2) (by omega) (by
        rw [show 2*((w.length - j - 1)/2)+1 = w.length - j by omega]; exact hp)
      rw [← hr] at hr'
      omega
    · exact hnotfirst _ hi2 hiw hset
  have hodd : oddAt c.odd (w.length - (2*r+1)) = true := by
    rw [ho, oddAt_false]; omega
  have hset : SetAt first (rewindLens.get s) (w.length - (2*r+1)) := by
    unfold SetAt
    rw [hget, hhead, show w.length - (w.length - (2*r+1)) = 2*r+1 by omega]
    by_cases hr0 : r = 0
    · subst hr0
      right
      simpa using hcell1
    · left
      rw [hcell _ (by omega), marks_cell]
      exact ⟨by omega, hr1, hpal⟩
  obtain ⟨y1, hs1, hsame1, hl1, hc1, hr1', hlen1, hrad1, hhead1⟩ :=
    choose_phase_vm first (fun _ => True) (fun _ => True) delay c hm s (w.length - (2*r+1)) hkle hno hodd hset
  obtain ⟨hg1, hi1⟩ := steps_transfer_rewind P q first delay _ (Or.inl hm) hi hs1
  -- ## rewind
  have hm1 : ({c with odd := oddAt c.odd (w.length - (2*r+1)), mode := .rewind, pair := false} : Control).mode = .rewind := rfl
  have hp1 : ({c with odd := oddAt c.odd (w.length - (2*r+1)), mode := .rewind, pair := false} : Control).pair = false := rfl
  have hget1 : rewindLens.get (rewindLens.set s y1) = y1 := rewindLens.get_set s y1
  have hden1 : GalilScaffoldTape.denote y1.marks = GalilScaffoldTape.denote (marksTape s.fpp) := hsame1.denote
  have hhead1' : GalilScaffoldTape.head y1.marks = 2*r+1 := by
    rw [hhead1, hget, hhead]; omega
  have hk2 : 2*r ≤ GalilScaffoldTape.head (rewindLens.get (rewindLens.set s y1)).marks := by
    rw [hget1, hhead1']; omega
  have hno2 : ∀ j, j < 2*r → GalilScaffoldTape.denote (rewindLens.get (rewindLens.set s y1)).marks
      (GalilScaffoldTape.head (rewindLens.get (rewindLens.set s y1)).marks - j) ≠ first := by
    intro j hj
    rw [hget1, hden1, hhead1']
    exact hnotfirst _ (by omega) (by omega)
  have hfirst2 : GalilScaffoldTape.denote (rewindLens.get (rewindLens.set s y1)).marks
      (GalilScaffoldTape.head (rewindLens.get (rewindLens.set s y1)).marks - 2*r) = first := by
    rw [hget1, hden1, hhead1', show 2*r+1 - 2*r = 1 by omega]
    exact hcell1
  obtain ⟨y2, hs2, hl2, hc2, hr2, hlen2, hrad2, hprog2⟩ :=
    rewind_phase_vm first (fun _ => True) (fun _ => True) delay _ hm1 hp1 (rewindLens.set s y1) (2*r) hk2 hno2 hfirst2
  obtain ⟨hg2, hi2⟩ := steps_transfer_rewind P q first delay _ (Or.inr rfl) hi1 hs2
  rw [rewindLens.set_set] at hg2 hi2
  refine ⟨y2, ?_, ?_, ?_, ?_, ?_, ?_, hprog2, hi2⟩
  · exact steps_trans hg1 hg2
  · rw [hl2]
    show GalilScaffoldInputHead.left^[2*r] y1.left = _
    rw [hl1]
  · rw [hc2]
    show GalilScaffoldInputHead.left^[2*r/2] y1.center = _
    rw [hc1, show 2*r/2 = r by omega]
  · rw [hr2]; exact hr1'
  · rw [hlen2]
    show GalilScaffoldCounter.inc^[2*r] y1.length = _
    rw [hlen1, iterate_inc_ofNat, Nat.add_comm]
  · rw [hrad2]
    show GalilScaffoldCounter.inc^[2*r/2] y1.radius = _
    rw [hrad1, reset_eq_ofNat, iterate_inc_ofNat, show 2*r/2 = r by omega, Nat.zero_add]

#print axioms choose_then_rewind

end PalPeg.GalilScaffoldChainInputSupply
