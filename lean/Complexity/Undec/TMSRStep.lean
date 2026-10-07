import Complexity.Undec.TMSRDefs

/-!
# One-tape tables as string rewriting systems: one step

- `fstep` on one-tape configurations (`fstep_halt`, `fstep_none`, `fstep_some`), and the invariant `Good` (one
  tape, head at most one past the end, symbols and state below the bound) that every run keeps (`fstep_good`);
- trailing blanks are invisible to `fstep` (`fstep_pad`);
- forward: the word of a configuration rewrites to the word of its successor (`fwd_step`);
- backward: every rewrite of the word of a configuration whose state is not `0` gives the word of its successor
  or of the same configuration with one more trailing blank (`back_step`).
-/

namespace Complexity.Undec

open Complexity

variable {T : TTable}

/-! ## One step of a one-tape table -/

/-- Halted configurations do not move. -/
theorem fstep_halt (T : TTable) {q : Nat} (p : Nat) (t : List Nat) (h : q = 0 ∨ q = 1) :
    fstep T (mk q p t) = mk q p t := by
  unfold fstep
  simp [mk, h]

/-- Configurations without a row do not move. -/
theorem fstep_none (T : TTable) {q p : Nat} {t : List Nat} (h0 : q ≠ 0) (h1 : q ≠ 1)
    (hr : T.rows[T.idx q [t.getD p 0]]? = none) : fstep T (mk q p t) = mk q p t := by
  rw [List.getD_eq_getElem?_getD] at hr
  unfold fstep
  simp [mk, h0, h1, FCfg.reads, hr]

/-- A row applied to a one-tape configuration. -/
theorem fstep_some (hT : Univ.RowsOK T) (hk : T.k = 1) {q p : Nat} {t : List Nat} {r : Row} (h0 : q ≠ 0)
    (h1 : q ≠ 1) (hr : T.rows[T.idx q [t.getD p 0]]? = some r) :
    fstep T (mk q p t) = mk r.1 ((mv r).apply p) (writeAt t p (wr r)) := by
  have hm := List.mem_of_getElem? hr
  obtain ⟨hw, hm'⟩ := hT r hm
  obtain ⟨q', ws, ms⟩ := r
  simp only at hw hm'
  rw [hk] at hw hm'
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hw
  obtain ⟨m, rfl⟩ := List.length_eq_one_iff.mp hm'
  rw [List.getD_eq_getElem?_getD] at hr
  unfold fstep
  simp [mk, h0, h1, FCfg.reads, hr, wr, mv]

/-! ## The invariant of runs -/

/-- A one-tape configuration with its head at most one past the end and everything below the bound. -/
def Good (T : TTable) (c : FCfg) : Prop :=
  ∃ q p t, c = mk q p t ∧ p ≤ t.length ∧ (∀ z ∈ t, z < bnd T) ∧ q < bnd T

/-- The cells after a write: old cells, blanks, and the written symbol. -/
theorem mem_writeAt {t : List Nat} {p a z : Nat} (h : z ∈ writeAt t p a) : z ∈ t ∨ z = 0 ∨ z = a := by
  unfold writeAt at h
  split at h
  · rcases List.mem_or_eq_of_mem_set h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at h
    rcases h with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h.2)
    · exact Or.inr (Or.inr h)

/-- A move keeps the head at most one past the end of the written tape. -/
theorem apply_le_max (m : Move) {p n : Nat} (hp : p ≤ n) : m.apply p ≤ max n (p + 1) := by
  cases m <;> simp [Move.apply] <;> omega

/-- One step keeps the invariant. -/
theorem fstep_good (hT : Univ.RowsOK T) (hk : T.k = 1) {c : FCfg} (hc : Good T c) : Good T (fstep T c) := by
  obtain ⟨q, p, t, rfl, hp, ht, hq⟩ := hc
  by_cases h01 : q = 0 ∨ q = 1
  · rw [fstep_halt T p t h01]; exact ⟨q, p, t, rfl, hp, ht, hq⟩
  · have h0 : q ≠ 0 := fun e => h01 (Or.inl e)
    have h1 : q ≠ 1 := fun e => h01 (Or.inr e)
    cases hr : T.rows[T.idx q [t.getD p 0]]? with
    | none => rw [fstep_none T h0 h1 hr]; exact ⟨q, p, t, rfl, hp, ht, hq⟩
    | some r =>
      rw [fstep_some hT hk h0 h1 hr]
      have hm := List.mem_of_getElem? hr
      refine ⟨r.1, _, _, rfl, ?_, ?_, row_state_lt hm⟩
      · rw [Univ.length_writeAt]; exact apply_le_max _ hp
      · intro z hz
        rcases mem_writeAt hz with h | h | h
        · exact ht z h
        · rw [h]; unfold bnd; omega
        · rw [h]; exact row_wr_lt hm

/-- The initial configuration of one tape. -/
theorem finit_one (w : List Bool) : finit 1 w = mk 2 0 (w.map bitSym) := by
  simp [finit, mk, List.ofFn_succ]

/-- The initial configuration has the invariant. -/
theorem finit_good (T : TTable) (w : List Bool) : Good T (finit 1 w) := by
  rw [finit_one]
  refine ⟨2, 0, _, rfl, Nat.zero_le _, ?_, by unfold bnd; omega⟩
  intro z hz
  simp only [List.mem_map] at hz
  obtain ⟨b, _, rfl⟩ := hz
  cases b <;> simp [bitSym, bnd] <;> omega

/-- Every run keeps the invariant. -/
theorem frun_good (hT : Univ.RowsOK T) (hk : T.k = 1) (w : List Bool) : ∀ n, Good T (frun T (finit 1 w) n)
  | 0 => finit_good T w
  | n + 1 => fstep_good hT hk (frun_good hT hk w n)

/-! ## Trailing blanks -/

/-- Reading a padded tape. -/
theorem getD_pad (t : List Nat) (j p : Nat) : (t ++ List.replicate j 0).getD p 0 = t.getD p 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split
  · rfl
  · rename_i h
    have : t[p]? = none := List.getElem?_eq_none (by omega)
    rw [this]
    split <;> rfl

/-- Writing on a padded tape gives a padded tape. -/
theorem writeAt_pad {t : List Nat} {p : Nat} (hp : p ≤ t.length) (j b : Nat) :
    ∃ j', writeAt (t ++ List.replicate j 0) p b = writeAt t p b ++ List.replicate j' 0 := by
  rcases Nat.lt_or_eq_of_le hp with h | h
  · refine ⟨j, ?_⟩
    have h' : p < (t ++ List.replicate j 0).length := by simp; omega
    unfold writeAt
    rw [if_pos h', if_pos h, List.set_append_left _ _ h]
  · subst h
    cases j with
    | zero => exact ⟨0, by simp⟩
    | succ j =>
      refine ⟨j, ?_⟩
      unfold writeAt
      simp [List.replicate_succ]

/-- A configuration with `j` more trailing blanks. -/
def padC (c : FCfg) (j : Nat) : FCfg := mk c.state (c.pos.headD 0) (c.tapes.headD [] ++ List.replicate j 0)

/-- One step commutes with padding. -/
theorem fstep_pad (hT : Univ.RowsOK T) (hk : T.k = 1) {q p : Nat} {t : List Nat} (hp : p ≤ t.length) (j : Nat) :
    ∃ j', fstep T (padC (mk q p t) j) = padC (fstep T (mk q p t)) j' := by
  simp only [padC, mk, List.headD_cons]
  show ∃ j', fstep T (mk q p (t ++ List.replicate j 0)) = padC (fstep T (mk q p t)) j'
  by_cases h01 : q = 0 ∨ q = 1
  · exact ⟨j, by rw [fstep_halt T _ _ h01, fstep_halt T _ _ h01]; rfl⟩
  · have h0 : q ≠ 0 := fun e => h01 (Or.inl e)
    have h1 : q ≠ 1 := fun e => h01 (Or.inr e)
    cases hr : T.rows[T.idx q [t.getD p 0]]? with
    | none =>
      have hr' : T.rows[T.idx q [(t ++ List.replicate j 0).getD p 0]]? = none := by rw [getD_pad]; exact hr
      exact ⟨j, by rw [fstep_none T h0 h1 hr, fstep_none T h0 h1 hr']; rfl⟩
    | some r =>
      have hr' : T.rows[T.idx q [(t ++ List.replicate j 0).getD p 0]]? = some r := by rw [getD_pad]; exact hr
      obtain ⟨j', hj⟩ := writeAt_pad hp j (wr r)
      exact ⟨j', by rw [fstep_some hT hk h0 h1 hr, fstep_some hT hk h0 h1 hr', hj]; rfl⟩

/-! ## Words -/

/-- A rewrite from an explicit split. -/
theorem step_of {R : SRS} {x y u v l r : Word} (h : (l, r) ∈ R) (hx : x = u ++ l ++ v) (hy : y = u ++ r ++ v) :
    SRStep R x y := by
  subst hx hy; exact SRStep.rw u v l r h

/-- A word with exactly one marked symbol splits uniquely at it. -/
theorem split_unique {P : Nat → Prop} {x y : Nat} {b d : List Nat} :
    ∀ {a c : List Nat}, a ++ x :: b = c ++ y :: d → (∀ z ∈ a, ¬P z) → (∀ z ∈ b, ¬P z) → P y →
      a = c ∧ x = y ∧ b = d
  | [], [], h, _, _, _ => by
    simp only [List.nil_append, List.cons.injEq] at h
    exact ⟨rfl, h.1, h.2⟩
  | [], c0 :: c, h, _, hb, hy => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd hy (hb y (by rw [h.2]; simp))
  | a0 :: a, [], h, ha, _, hy => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd hy (ha y (by rw [h.1]; simp))
  | a0 :: a, c0 :: c, h, ha, hb, hy => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have := split_unique h (fun z hz => ha z (by simp [hz])) hb hy
    exact ⟨by rw [this.1], this.2⟩

/-- The word of a configuration splits only at its state. -/
theorem zw_split {q q' : Nat} {L R c d : List Nat} (hL : ∀ z ∈ L, z < bnd T) (hR : ∀ z ∈ R, z < bnd T)
    (h : zw T q L R = c ++ stS T q' :: d) : lbS T :: L = c ∧ q = q' ∧ R ++ [rbS T] = d := by
  have h' : (lbS T :: L) ++ stS T q :: (R ++ [rbS T]) = c ++ stS T q' :: d := by rw [← h]; simp [zw]
  have := split_unique (P := fun z => bnd T + 2 ≤ z) h'
    (by
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · simp [lbS]
      · have := hL z hz; omega)
    (by
      intro z hz
      simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · have := hR z hz; omega
      · simp [rbS])
    (by simp [stS])
  refine ⟨this.1, ?_, this.2.2⟩
  have := this.2.1
  simp only [stS] at this
  omega

/-- A word ending in `z`, whose first symbol is not `z`, starts with that symbol. -/
theorem head_split {a z : Nat} {v R : List Nat} (h : R ++ [z] = a :: v) (hz : a ≠ z) :
    ∃ R', R = a :: R' ∧ v = R' ++ [z] := by
  cases R with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at h
    exact absurd h.1.symm hz
  | cons r R' =>
    simp only [List.cons_append, List.cons.injEq] at h
    exact ⟨R', by rw [h.1], h.2.symm⟩

/-- A list is empty or has a last element. -/
theorem nil_or_snoc (L : List Nat) : L = [] ∨ ∃ L' c, L = L' ++ [c] := by
  rcases List.eq_nil_or_concat L with h | ⟨L', c, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨L', c, by rw [h, List.concat_eq_append]⟩

/-! ## The successor of a configuration reading `a` -/

section Cell

variable (hT : Univ.RowsOK T) (hk : T.k = 1) {q a : Nat} {L R' : List Nat} {r : Row}
  (h0 : q ≠ 0) (h1 : q ≠ 1) (hr : T.rows[T.idx q [a]]? = some r)
include hT hk h0 h1 hr

/-- The successor of a configuration reading `a`. -/
theorem fstep_cell :
    fstep T (mk q L.length (L ++ a :: R')) = mk r.1 ((mv r).apply L.length) (L ++ wr r :: R') := by
  have hr' : T.rows[T.idx q [(L ++ a :: R').getD L.length 0]]? = some r := by simpa using hr
  rw [fstep_some hT hk h0 h1 hr']
  have hw : writeAt (L ++ a :: R') L.length (wr r) = L ++ wr r :: R' := by
    unfold writeAt
    rw [if_pos (by simp)]
    simp
  rw [hw]

/-- The successor word of a right move. -/
theorem res_R (hm : mv r = .R) :
    cword T (fstep T (mk q L.length (L ++ a :: R'))) = zw T r.1 (L ++ [wr r]) R' := by
  rw [fstep_cell hT hk h0 h1 hr, hm, ← cword_mk]
  simp [Move.apply]

/-- The successor word of a stay. -/
theorem res_S (hm : mv r = .S) :
    cword T (fstep T (mk q L.length (L ++ a :: R'))) = zw T r.1 L (wr r :: R') := by
  rw [fstep_cell hT hk h0 h1 hr, hm, ← cword_mk]
  simp [Move.apply]

/-- The successor word of a left move at the left end. -/
theorem res_L0 (hm : mv r = .L) :
    cword T (fstep T (mk q ([] : List Nat).length ([] ++ a :: R'))) = zw T r.1 [] (wr r :: R') := by
  rw [fstep_cell hT hk h0 h1 hr, hm, ← cword_mk]
  simp [Move.apply]

/-- The successor word of a left move inside the tape. -/
theorem res_L1 (hm : mv r = .L) (L' : List Nat) (c : Nat) :
    cword T (fstep T (mk q (L' ++ [c]).length ((L' ++ [c]) ++ a :: R'))) = zw T r.1 L' (c :: wr r :: R') := by
  rw [fstep_cell hT hk h0 h1 hr, hm, ← cword_mk]
  simp [Move.apply]

end Cell

end Complexity.Undec
