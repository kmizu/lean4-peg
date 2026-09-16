import PalPeg.GalilScaffoldChainInputSupply

set_option autoImplicit false
namespace PalPeg.GalilEndOfInput
open GalilScaffoldInputHead GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply (position)
open GalilScaffoldInputTrace (Represents moveRight)

/-! ## End-of-input geometry for the online input head

`position p` is the index of the currently focused cell of the encoded word
`encoded w` (odd indices are letters, even indices are gap markers).  The
encoded word has length `2 * w.length + 1`, so `2 * w.length` is its last
index.  The lemmas below say that the head can no longer move right exactly
when it sits on that last gap, and that the move which consumes the final
arrived letter lands on index `2 * w.length - 1`. -/

/-- The left stack of a laid-out head records exactly the consumed prefix. -/
theorem layout_left_length (xs : List (Fin 2)) (rs : List (Option (Fin 2)))
    (q : List (Fin 2)) : (layout xs rs q).left.length = xs.length := by
  cases xs <;> simp [layout]

theorem layout_right (xs : List (Fin 2)) (rs : List (Option (Fin 2)))
    (q : List (Fin 2)) : (layout xs rs q).right = rs := by
  cases xs <;> rfl

theorem layout_incoming (xs : List (Fin 2)) (rs : List (Option (Fin 2)))
    (q : List (Fin 2)) : (layout xs rs q).incoming = q := by
  cases xs <;> rfl

/-- Rightward movement is blocked exactly on the final gap cell of `encoded w`. -/
theorem not_canRight_iff (p : PlaceHead) (w : List (Fin 2))
    (hrep : Represents p.head w) (hfocus : p.head.focus ≠ none) :
    ¬ canRight p ↔ position p = 2 * w.length := by
  obtain ⟨xs, rs, q, hh, hw⟩ := hrep
  cases xs with
  | nil => rw [hh] at hfocus; simp [layout] at hfocus
  | cons a xs =>
    have hlen : p.head.left.length = xs.length + 1 := by
      rw [hh]; simpa using layout_left_length (a :: xs) (rs.map some) q
    have hright : p.head.right = rs.map some := by rw [hh]; exact layout_right _ _ _
    have hinc : p.head.incoming = q := by rw [hh]; exact layout_incoming _ _ _
    have hwlen : w.length = (xs.length + 1) + (rs.length + q.length) := by
      rw [hw]; simp; omega
    constructor
    · intro hnc
      have hg : p.gap = true := by
        by_cases hgap : p.gap
        · exact hgap
        · exact absurd (Or.inl (by simpa using hgap)) hnc
      have hrs : rs = [] := by
        by_contra hr
        exact hnc (Or.inr (Or.inl (by rw [hright]; simpa using hr)))
      have hq : q = [] := by
        by_contra hq'
        exact hnc (Or.inr (Or.inr (by rw [hinc]; exact hq')))
      have hz : rs.length = 0 ∧ q.length = 0 := by simp [hrs, hq]
      simp only [position, hg, if_true, hlen]
      omega
    · intro hpos hc
      cases hgap : p.gap with
      | false =>
        simp only [position, hgap, Bool.false_eq_true, if_false, hlen] at hpos
        omega
      | true =>
        simp only [position, hgap, if_true, hlen] at hpos
        rw [hwlen] at hpos
        have hrs : rs = [] := by
          have hz : rs.length = 0 := by omega
          exact List.eq_nil_of_length_eq_zero hz
        have hq : q = [] := by
          have hz : q.length = 0 := by omega
          exact List.eq_nil_of_length_eq_zero hz
        rcases hc with h | h | h
        · rw [hgap] at h; exact absurd h (by simp)
        · rw [hright, hrs] at h; exact absurd rfl h
        · rw [hinc, hq] at h; exact absurd rfl h

/-- The rightward move that consumes the very last arrived letter lands on the
final letter cell `2 * w.length - 1` of `encoded w`. -/
theorem last_letter_position (p : PlaceHead) (w : List (Fin 2))
    (hrep : Represents p.head w) (hav : canRight p)
    (hlast : (right p).head.right = [] ∧ (right p).head.incoming = [] ∧
      (right p).gap = false) :
    position (right p) = 2 * w.length - 1 := by
  obtain ⟨hr0, hi0, hg0⟩ := hlast
  have hg : p.gap = true := by
    have hgg : (!p.gap) = false := hg0
    simpa using hgg
  obtain ⟨xs, rs, q, hh, hw⟩ := hrep
  have hrp : right p = ⟨moveRight p.head, false⟩ := by
    simp only [right, hg, if_true, headRight]; rfl
  have hright : p.head.right = rs.map some := by rw [hh]; exact layout_right _ _ _
  have hinc : p.head.incoming = q := by rw [hh]; exact layout_incoming _ _ _
  have hleft : p.head.left.length = xs.length := by
    rw [hh]; exact layout_left_length xs (rs.map some) q
  have hwlen : w.length = xs.length + (rs.length + q.length) := by
    rw [hw]; simp
  rcases hrs : p.head.right with _ | ⟨b, rs'⟩
  · rcases hq : p.head.incoming with _ | ⟨c, q'⟩
    · rcases hav with h | h | h
      · rw [hg] at h; exact absurd h (by simp)
      · exact absurd hrs h
      · exact absurd hq h
    · have hmv : moveRight p.head =
          ⟨some c, p.head.focus :: p.head.left, [], q'⟩ := by
        simp only [moveRight, hrs, hq]
      have hq'0 : q' = [] := by
        rw [hrp, hmv] at hi0; simpa using hi0
      have hqlen : q.length = 1 := by
        rw [← hinc, hq, hq'0]; simp
      have hrslen : rs.length = 0 := by
        have hm : rs.map some = [] := by rw [← hright]; exact hrs
        simpa using hm
      have hpos : position (right p) = 2 * (xs.length + 1) - 1 := by
        rw [hrp]
        simp only [position, Bool.false_eq_true, if_false, hmv, List.length_cons, hleft]
      omega
  · have hmv : moveRight p.head =
        ⟨b, p.head.focus :: p.head.left, rs', p.head.incoming⟩ := by
      simp only [moveRight, hrs]
    have hrs'0 : rs' = [] := by
      rw [hrp, hmv] at hr0; simpa using hr0
    have hrslen : rs.length = 1 := by
      have hmap : rs.map some = b :: rs' := by rw [← hright]; exact hrs
      have hlen1 : (rs.map some).length = 1 := by rw [hmap, hrs'0]; simp
      simpa using hlen1
    have hq0 : q.length = 0 := by
      have hi : p.head.incoming = [] := by rw [hrp, hmv] at hi0; simpa using hi0
      rw [hinc] at hi; simp [hi]
    have hpos : position (right p) = 2 * (xs.length + 1) - 1 := by
      rw [hrp]
      simp only [position, Bool.false_eq_true, if_false, hmv, List.length_cons, hleft]
    omega

/-- The head never runs past the last cell of `encoded w`. -/
theorem position_le (p : PlaceHead) (w : List (Fin 2))
    (hrep : Represents p.head w) : position p ≤ 2 * w.length := by
  obtain ⟨xs, rs, q, hh, hw⟩ := hrep
  have hleft : p.head.left.length = xs.length := by
    rw [hh]; exact layout_left_length xs (rs.map some) q
  have hwlen : w.length = xs.length + (rs.length + q.length) := by
    rw [hw]; simp
  cases hgap : p.gap with
  | false => simp only [position, hgap, Bool.false_eq_true, if_false, hleft]; omega
  | true => simp only [position, hgap, if_true, hleft]; omega

#print axioms layout_left_length
#print axioms not_canRight_iff
#print axioms last_letter_position
#print axioms position_le
end PalPeg.GalilEndOfInput
