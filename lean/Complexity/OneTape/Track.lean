import Complexity.OneTape.Sweep

/-!
# Updating one track of the tape

When the simulator writes `M`'s new symbol `v` of tape `i` at head `i` (cell `p`), clears the flag there and sets it
at the cell `p1` where head `i` moves, the tape (`track2`) holds the columns of the tapes in which only tape `i` has
changed, in the way one step of `M` changes it (`trackRep`).
-/

namespace Complexity
namespace OneTape

variable {k : Nat} (M : TM k)

/-- The tape after writing `v` on track `i` at cell `p`, then setting the flag of track `i` at cell `p1`. -/
def track2 (T : Nat → Nat) (i : Fin k) (p p1 v : Nat) : Nat → Nat :=
  upd (upd T p (setDig M (T p) i.val (2 * v))) p1
    (setDig M (upd T p (setDig M (T p) i.val (2 * v)) p1) i.val
      (cdig M (upd T p (setDig M (T p) i.val (2 * v)) p1) i.val + 1))

variable {T : Nat → Nat} {pos pos' : Fin k → Nat} {cells cells' : Fin k → Nat → Nat} {i : Fin k} {v : Nat}

theorem two_v_lt (hv : v < M.na) : 2 * v < base M := by unfold base; omega

/-- The digit of track `i` where its flag lands is even before the flag is set, so setting it stays in range. -/
theorem setFlag_lt (hT : TapeRep M T pos cells) (hv : v < M.na) (p1 : Nat) :
    cdig M (upd T (pos i) (setDig M (T (pos i)) i.val (2 * v)) p1) i.val + 1 < base M := by
  have h2 := cdig_lt M (upd T (pos i) (setDig M (T (pos i)) i.val (2 * v)) p1) i.val
  have hb : base M = 2 * M.na := rfl
  have h1 : cdig M (upd T (pos i) (setDig M (T (pos i)) i.val (2 * v)) p1) i.val % 2 = 0 := by
    by_cases h : p1 = pos i
    · rw [h, upd_eq, cdig_setDig M _ i.isLt (two_v_lt M hv), if_pos rfl]; omega
    · rw [upd_ne _ _ h, (hT p1).2.2 i]
      unfold flag; rw [if_neg (Ne.symm h)]; omega
  omega

/-- The four shapes of a cell of `track2`. -/
theorem track2_cell (p p1 v j : Nat) :
    (j = p1 ∧ j = p ∧ track2 M T i p p1 v j =
        setDig M (setDig M (T j) i.val (2 * v)) i.val (cdig M (setDig M (T j) i.val (2 * v)) i.val + 1)) ∨
    (j = p1 ∧ j ≠ p ∧ track2 M T i p p1 v j = setDig M (T j) i.val (cdig M (T j) i.val + 1)) ∨
    (j ≠ p1 ∧ j = p ∧ track2 M T i p p1 v j = setDig M (T j) i.val (2 * v)) ∨
    (j ≠ p1 ∧ j ≠ p ∧ track2 M T i p p1 v j = T j) := by
  unfold track2
  by_cases h1 : j = p1
  · by_cases h : j = p
    · subst h1; subst h; left; exact ⟨rfl, rfl, by rw [upd_eq, upd_eq]⟩
    · subst h1; right; left; exact ⟨rfl, h, by rw [upd_eq, upd_ne _ _ h]⟩
  · by_cases h : j = p
    · subst h; right; right; left; exact ⟨h1, rfl, by rw [upd_ne _ _ h1, upd_eq]⟩
    · right; right; right; exact ⟨h1, h, by rw [upd_ne _ _ h1, upd_ne _ _ h]⟩

/-- **One track updated**: writing `v` at head `i` and moving its flag gives the columns of the new tapes. -/
theorem trackRep (hT : TapeRep M T pos cells) (hv : v < M.na)
    (hpos : ∀ i', i' ≠ i → pos' i' = pos i') (hcells : ∀ i', i' ≠ i → cells' i' = cells i')
    (hci : ∀ j, cells' i j = if j = pos i then v else cells i j) :
    TapeRep M (track2 M T i (pos i) (pos' i) v) pos' cells' := by
  have h2v := two_v_lt M hv
  have hfl := setFlag_lt M hT hv (pos' i) (i := i)
  intro j
  obtain ⟨hlt, hlf, hdig⟩ := hT j
  have hfp : flag pos i j = if pos i = j then 1 else 0 := rfl
  have hfp' : flag pos' i j = if pos' i = j then 1 else 0 := rfl
  -- digits of the other tracks are untouched
  have hother : ∀ a w, w < base M → ∀ i' : Fin k, i' ≠ i → cdig M (setDig M a i.val w) i'.val = cdig M a i'.val :=
    fun a w hw i' hi' => by rw [cdig_setDig M _ i.isLt hw, if_neg (fun h => hi' (Fin.ext h))]
  have hrest : ∀ i' : Fin k, i' ≠ i → cdig M (T j) i'.val = 2 * cells' i' j + flag pos' i' j := by
    intro i' hi'
    rw [hdig i', hcells i' hi']; unfold flag; rw [hpos i' hi']
  rcases track2_cell M (T := T) (i := i) (pos i) (pos' i) v j with
    ⟨hj1, hj, e⟩ | ⟨hj1, hj, e⟩ | ⟨hj1, hj, e⟩ | ⟨hj1, hj, e⟩ <;> rw [e]
  · have hb : cdig M (setDig M (T j) i.val (2 * v)) i.val + 1 < base M := by
      rw [cdig_setDig M _ i.isLt h2v, if_pos rfl]; unfold base; omega
    refine ⟨setDig_lt M _ _ hb, by rw [clft_setDig, clft_setDig]; exact hlf, fun i' => ?_⟩
    by_cases hi' : i' = i
    · subst hi'
      rw [cdig_setDig M _ i'.isLt hb, if_pos rfl, cdig_setDig M _ i'.isLt h2v, if_pos rfl, hci, if_pos hj, hfp',
        if_pos hj1.symm]
    · rw [hother _ _ hb i' hi', hother _ _ h2v i' hi', hrest i' hi']
  · have hb : cdig M (T j) i.val + 1 < base M := by
      have := hfl; rw [← hj1, upd_ne _ _ hj] at this; exact this
    refine ⟨setDig_lt M _ _ hb, by rw [clft_setDig]; exact hlf, fun i' => ?_⟩
    by_cases hi' : i' = i
    · subst hi'
      rw [cdig_setDig M _ i'.isLt hb, if_pos rfl, hdig, hci, if_neg hj, hfp', if_pos hj1.symm, hfp,
        if_neg (Ne.symm hj)]
    · rw [hother _ _ hb i' hi', hrest i' hi']
  · refine ⟨setDig_lt M _ _ h2v, by rw [clft_setDig]; exact hlf, fun i' => ?_⟩
    by_cases hi' : i' = i
    · subst hi'
      rw [cdig_setDig M _ i'.isLt h2v, if_pos rfl, hci, if_pos hj, hfp', if_neg (Ne.symm hj1)]; rfl
    · rw [hother _ _ h2v i' hi', hrest i' hi']
  · refine ⟨hlt, hlf, fun i' => ?_⟩
    by_cases hi' : i' = i
    · subst hi'
      rw [hdig, hci, if_neg hj, hfp', if_neg (Ne.symm hj1), hfp, if_neg (Ne.symm hj)]
    · exact hrest i' hi'

end OneTape
end Complexity
