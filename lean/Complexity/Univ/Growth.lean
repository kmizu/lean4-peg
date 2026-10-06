import Complexity.Univ.SimSpec

/-!
# How fast a finite configuration grows

One step of a table `T` on a well-shaped configuration (`CfgOK`) whose heads are at most one past the end of their
tapes (`Nice`) keeps both properties and adds at most `growth T` to the size `csz` (`fstep_csz`); so `t` steps add
at most `t · growth T` (`frun_csz`).
-/

namespace Complexity.Univ

open Complexity

/-- Every head is at most one past the end of its tape. -/
def Nice (c : FCfg) : Prop := ∀ i (hp : i < c.pos.length) (ht : i < c.tapes.length), c.pos[i] ≤ c.tapes[i].length

/-- The growth of the size in one step. -/
def growth (T : TTable) : Nat := (T.k + 1) * (tsz T + 3)

/-! ## Small facts about lists -/

/-- A member of a list of numbers is at most its sum. -/
theorem le_sum_of_mem_nat : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum
  | [], _, h => by simp at h
  | a :: l, x, h => by
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := le_sum_of_mem_nat h; omega

/-- Every entry of a row of `T` is at most the sum of the encoded rows. -/
theorem row_entry_le {T : TTable} {r : Row} (hr : r ∈ T.rows) :
    r.1 ≤ (encRows T.rows).sum ∧ ∀ a ∈ r.2.1, a ≤ (encRows T.rows).sum := by
  have hsub : ∀ x ∈ r.1 :: r.2.1 ++ r.2.2, x ∈ encRows T.rows := by
    intro x hx
    simp only [encRows, List.mem_flatMap]
    exact ⟨r, hr, hx⟩
  refine ⟨le_sum_of_mem_nat (hsub _ (by simp)), fun a ha => le_sum_of_mem_nat (hsub _ (by simp [ha]))⟩

/-- Every entry of a row of `T` is at most `tsz T`. -/
theorem row_entry_le_tsz {T : TTable} {r : Row} (hr : r ∈ T.rows) :
    r.1 ≤ tsz T ∧ ∀ a ∈ r.2.1, a ≤ tsz T := by
  have h := row_entry_le hr
  have : (encRows T.rows).sum ≤ tsz T := by unfold tsz; omega
  exact ⟨Nat.le_trans h.1 this, fun a ha => Nat.le_trans (h.2 a ha) this⟩

/-- Setting an entry adds at most the new value to the sum. -/
theorem sum_set_le : ∀ (t : List Nat) (p a : Nat), (t.set p a).sum ≤ t.sum + a
  | [], _, _ => by simp
  | b :: t, 0, a => by simp [List.sum_cons]; omega
  | b :: t, p + 1, a => by
    have := sum_set_le t p a
    simp [List.sum_cons]; omega

/-- The length of a tape after a write. -/
theorem length_writeAt (t : List Nat) (p a : Nat) : (writeAt t p a).length = max t.length (p + 1) := by
  unfold writeAt
  split
  · simp; omega
  · simp; omega

/-- A write at most one past the end adds at most the written value to the sum. -/
theorem sum_writeAt_le {t : List Nat} {p : Nat} (hp : p ≤ t.length) (a : Nat) :
    (writeAt t p a).sum ≤ t.sum + a := by
  unfold writeAt
  split
  · exact sum_set_le t p a
  · have : p - t.length = 0 := by omega
    simp [this]

/-- Each move changes a head by at most one to the right. -/
theorem apply_le (m : Move) (p : Nat) : m.apply p ≤ p + 1 := by
  cases m <;> simp [Move.apply] <;> omega

/-- The heads after the moves: no longer list, sum grows by at most the length. -/
theorem pos_bounds : ∀ (ps ms : List Nat),
    ((ps.zip ms).map fun x : Nat × Nat => (Move.ofCode x.2).apply x.1).length ≤ ps.length ∧
    ((ps.zip ms).map fun x : Nat × Nat => (Move.ofCode x.2).apply x.1).sum ≤ ps.sum + ps.length
  | [], _ => by simp
  | _ :: _, [] => by simp
  | p :: ps, m :: ms => by
    have ih := pos_bounds ps ms
    have := apply_le (Move.ofCode m) p
    simp only [List.zip_cons_cons, List.map_cons, List.length_cons, List.sum_cons] at ih ⊢
    omega

/-- The tapes after the writes: the encoding grows by at most one length entry per tape and by at most one length
unit plus one written value per tape. -/
theorem tape_bounds (B : Nat) : ∀ (ts : List (List Nat)) (ps ws : List Nat),
    (∀ i (hp : i < ps.length) (ht : i < ts.length), ps[i] ≤ ts[i].length) → (∀ a ∈ ws, a ≤ B) →
    (encTapes (((ts.zip ps).zip ws).map fun x : (List Nat × Nat) × Nat => writeAt x.1.1 x.1.2 x.2)).length ≤
        (encTapes ts).length + ts.length ∧
      (encTapes (((ts.zip ps).zip ws).map fun x : (List Nat × Nat) × Nat => writeAt x.1.1 x.1.2 x.2)).sum ≤
        (encTapes ts).sum + ts.length * (B + 1)
  | [], _, _, _, _ => by simp [encTapes]
  | _ :: _, [], _, _, _ => by simp [encTapes]
  | _ :: _, _ :: _, [], _, _ => by simp [encTapes]
  | t :: ts, p :: ps, a :: ws, hn, hw => by
    have hn' : ∀ i (hp : i < ps.length) (ht : i < ts.length), ps[i] ≤ ts[i].length := fun i hp ht =>
      hn (i + 1) (by simp; omega) (by simp; omega)
    have ih := tape_bounds B ts ps ws hn' (fun b hb => hw b (by simp [hb]))
    have h0 : p ≤ t.length := hn 0 (by simp) (by simp)
    have ha : a ≤ B := hw a (by simp)
    have hl := length_writeAt t p a
    have hs := sum_writeAt_le h0 a
    simp only [encTapes, List.zip_cons_cons, List.map_cons, List.flatMap_cons, List.length_append,
      List.length_cons, List.sum_append, List.sum_cons] at ih ⊢
    rw [Nat.succ_mul]
    have : max t.length (p + 1) ≤ t.length + 1 := by omega
    omega

/-! ## One step -/

/-- The cases of one step: unchanged, or a row of `T` applied. -/
theorem fstep_cases (T : TTable) (c : FCfg) :
    fstep T c = c ∨ ∃ q ws ms, (q, ws, ms) ∈ T.rows ∧ fstep T c =
      { state := q
        pos := (c.pos.zip ms).map fun x : Nat × Nat => (Move.ofCode x.2).apply x.1
        tapes := ((c.tapes.zip c.pos).zip ws).map fun x : (List Nat × Nat) × Nat => writeAt x.1.1 x.1.2 x.2 } := by
  unfold fstep
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · rename_i q ws ms h
      exact Or.inr ⟨q, ws, ms, List.mem_of_getElem? h, rfl⟩

theorem fstep_cfgOK {T : TTable} (hT : RowsOK T) {c : FCfg} (hc : CfgOK T c) : CfgOK T (fstep T c) := by
  rcases fstep_cases T c with h | ⟨q, ws, ms, hr, h⟩
  · rw [h]; exact hc
  · rw [h]
    have hr' := hT _ hr
    simp only at hr'
    obtain ⟨hp, ht⟩ := hc
    constructor
    · simp [hp, hr'.2]
    · simp [hp, ht, hr'.1]

theorem fstep_nice {T : TTable} (hT : RowsOK T) {c : FCfg} (hc : CfgOK T c) (hn : Nice c) : Nice (fstep T c) := by
  rcases fstep_cases T c with h | ⟨q, ws, ms, hr, h⟩
  · rw [h]; exact hn
  · rw [h]
    have hr' := hT _ hr
    simp only at hr'
    obtain ⟨hp, ht⟩ := hc
    intro i hi1 hi2
    simp only [List.length_map, List.length_zip] at hi1 hi2
    simp only [List.getElem_map, List.getElem_zip]
    rw [length_writeAt]
    have := apply_le (Move.ofCode ms[i]) c.pos[i]
    omega

theorem fstep_csz {T : TTable} (hT : RowsOK T) {c : FCfg} (hc : CfgOK T c) (hn : Nice c) :
    csz (fstep T c) ≤ csz c + growth T := by
  rcases fstep_cases T c with h | ⟨q, ws, ms, hr, h⟩
  · rw [h]; exact Nat.le_add_right _ _
  · rw [h]
    have hr' := hT _ hr
    simp only at hr'
    obtain ⟨hp, ht⟩ := hc
    have he := row_entry_le_tsz hr
    simp only at he
    have hpos := pos_bounds c.pos ms
    have htp := tape_bounds (tsz T) c.tapes c.pos ws (fun i h1 h2 => hn i h1 h2) he.2
    unfold csz growth
    simp only
    rw [hp] at hpos
    rw [ht] at htp
    have e1 : (T.k + 1) * (tsz T + 3) = T.k * (tsz T + 1) + 2 * T.k + tsz T + 3 := by
      rw [Nat.succ_mul, Nat.mul_add, Nat.mul_add]; omega
    rw [e1]
    omega

theorem frun_csz {T : TTable} (hT : RowsOK T) {c : FCfg} (hc : CfgOK T c) (hn : Nice c) (t : Nat) :
    csz (frun T c t) ≤ csz c + t * growth T ∧ CfgOK T (frun T c t) ∧ Nice (frun T c t) := by
  induction t with
  | zero => exact ⟨by simp [frun], hc, hn⟩
  | succ t ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [frun]
    refine ⟨?_, fstep_cfgOK hT h2, fstep_nice hT h2 h3⟩
    have := fstep_csz hT h2 h3
    rw [Nat.succ_mul]; omega

/-! ## The initial configuration -/

theorem finit_nice (k : Nat) (w : List Bool) : Nice (finit k w) := by
  intro i hp ht
  simp [finit]

theorem finit_cfgOK (T : TTable) (w : List Bool) : CfgOK T (finit T.k w) := by
  constructor <;> simp [finit]

/-- The sum of the input symbols is at most twice the length. -/
theorem sum_bitSym_le : ∀ w : List Bool, (w.map bitSym).sum ≤ 2 * w.length
  | [] => by simp
  | b :: w => by
    have := sum_bitSym_le w
    have : bitSym b ≤ 2 := by cases b <;> simp [bitSym]
    simp [List.sum_cons]; omega

/-- The encoding of the initial tapes. -/
theorem encTapes_finit : ∀ (k : Nat) (w : List Bool),
    (encTapes (finit k w).tapes).length ≤ k + w.length ∧ (encTapes (finit k w).tapes).sum ≤ 3 * w.length
  | 0, w => by simp [finit, encTapes]
  | k + 1, w => by
    have e : (finit (k + 1) w).tapes = w.map bitSym :: List.replicate k [] := by
      simp only [finit]
      rw [List.ofFn_succ]
      simp only [Fin.val_zero, if_pos, Fin.val_succ, Nat.succ_ne_zero, if_false]
      simp only [List.cons.injEq, true_and]
      exact List.ext_getElem (by simp) (fun i h1 h2 => by simp)
    have hz : ∀ n : Nat, encTapes (List.replicate n ([] : List Nat)) = List.replicate n 0 := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => simp [encTapes, List.replicate_succ] at ih ⊢; exact ih
    rw [e]
    have := sum_bitSym_le w
    simp only [encTapes, List.flatMap_cons] at hz ⊢
    rw [hz]
    simp [List.sum_cons]; omega

/-- The size of the initial configuration. The bound `2 + k + 3 * (w.length + 1) + k` is false (for `k = 1` and
`w = [true, true, true, true]` the size is `20`, the bound `19`); the length entry and the cells of tape `0` add
`w.length` to the length and up to `3 * w.length` to the sum of the tapes. -/
theorem finit_csz (k : Nat) (w : List Bool) : csz (finit k w) ≤ 2 + k + 4 * w.length + k := by
  have h := encTapes_finit k w
  unfold csz
  have hs : (finit k w).pos.sum = 0 := by
    simp only [finit]
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ]
  have hl : (finit k w).pos.length = k := by simp [finit]
  have hst : (finit k w).state = 2 := rfl
  omega

end Complexity.Univ
