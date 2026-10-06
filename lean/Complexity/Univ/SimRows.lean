import Complexity.Univ.SimSpec

/-!
# Facts about the encodings used by the simulator

* the rows of a table are chunks of `2k+1` numbers (`length_encRows`, `encRows_getD`);
* the numbers the simulator handles are at most the sizes (`tsz`, `csz`).
-/

namespace Complexity.Univ

open Complexity

/-! ## Chunks -/

theorem length_flatMap_const {α : Type} (f : α → List Nat) (m : Nat) :
    ∀ L : List α, (∀ a ∈ L, (f a).length = m) → (L.flatMap f).length = L.length * m
  | [], _ => by simp
  | a :: L, h => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    rw [length_flatMap_const f m L (fun b hb => h b (by simp [hb])), h a (by simp)]
    omega

theorem getD_flatMap_chunk {α : Type} (f : α → List Nat) (m : Nat) :
    ∀ L : List α, (∀ a ∈ L, (f a).length = m) → ∀ r (hr : r < L.length) j, j < m →
      (L.flatMap f).getD (r * m + j) 0 = (f L[r]).getD j 0
  | [], _, r, hr, _, _ => by simp at hr
  | a :: L, h, 0, _, j, hj => by
    have ha := h a (by simp)
    simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
  | a :: L, h, r + 1, hr, j, hj => by
    have ha := h a (by simp)
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [ha, Nat.succ_mul]; omega), ha,
      show (r + 1) * m + j - m = r * m + j by rw [Nat.succ_mul]; omega, ← List.getD_eq_getElem?_getD]
    exact getD_flatMap_chunk f m L (fun b hb => h b (by simp [hb])) r (by simp at hr; omega) j hj

/-- A row as numbers. -/
def rowEnc (r : Row) : List Nat := r.1 :: r.2.1 ++ r.2.2

theorem encRows_eq (rows : List Row) : encRows rows = rows.flatMap rowEnc := rfl

theorem length_rowEnc {T : TTable} (hT : RowsOK T) {r : Row} (hr : r ∈ T.rows) :
    (rowEnc r).length = 2 * T.k + 1 := by
  have := hT r hr; simp [rowEnc, this.1, this.2]; omega

theorem length_encRows {T : TTable} (hT : RowsOK T) :
    (encRows T.rows).length = T.rows.length * (2 * T.k + 1) := by
  rw [encRows_eq]; exact length_flatMap_const _ _ _ (fun r hr => length_rowEnc hT hr)

theorem encRows_getD {T : TTable} (hT : RowsOK T) {r : Nat} (hr : r < T.rows.length) {j : Nat}
    (hj : j < 2 * T.k + 1) :
    (encRows T.rows).getD (r * (2 * T.k + 1) + j) 0 = (rowEnc T.rows[r]).getD j 0 := by
  rw [encRows_eq]; exact getD_flatMap_chunk _ _ _ (fun r hr => length_rowEnc hT hr) r hr j hj

theorem rowEnc_getD_zero (r : Row) : (rowEnc r).getD 0 0 = r.1 := rfl

theorem rowEnc_getD_ws {T : TTable} (hT : RowsOK T) {r : Row} (hr : r ∈ T.rows) {i : Nat} (hi : i < T.k) :
    (rowEnc r).getD (1 + i) 0 = r.2.1.getD i 0 := by
  have := hT r hr
  simp only [rowEnc, List.getD_eq_getElem?_getD, List.cons_append]
  rw [show 1 + i = i + 1 by omega, List.getElem?_cons_succ, List.getElem?_append_left (by omega)]

theorem rowEnc_getD_ms {T : TTable} (hT : RowsOK T) {r : Row} (hr : r ∈ T.rows) {i : Nat} (hi : i < T.k) :
    (rowEnc r).getD (1 + T.k + i) 0 = r.2.2.getD i 0 := by
  have := hT r hr
  simp only [rowEnc, List.getD_eq_getElem?_getD, List.cons_append]
  rw [show 1 + T.k + i = (T.k + i) + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by omega), show T.k + i - r.2.1.length = i by omega]

/-! ## Bounds -/

theorem le_sum_of_mem : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum
  | [], _, h => by simp at h
  | a :: l, x, h => by
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := le_sum_of_mem h; omega

theorem getD_le_sum (l : List Nat) (i : Nat) : l.getD i 0 ≤ l.sum := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => simp
  | some x => simp only [Option.getD_some]; exact le_sum_of_mem (List.mem_of_getElem? h)

theorem length_le_encTapes : ∀ {ts : List (List Nat)} {t : List Nat}, t ∈ ts →
    t.length + 1 ≤ (encTapes ts).length
  | [], _, h => by simp at h
  | a :: ts, t, h => by
    simp only [List.mem_cons] at h
    have e : (encTapes (a :: ts)).length = a.length + 1 + (encTapes ts).length := by
      simp [encTapes]; omega
    rw [e]
    rcases h with rfl | h
    · omega
    · have := length_le_encTapes h; omega

theorem mem_encTapes {ts : List (List Nat)} {t : List Nat} (ht : t ∈ ts) {x : Nat} (hx : x ∈ t) :
    x ∈ encTapes ts := by
  simp only [encTapes, List.mem_flatMap]; exact ⟨t, ht, by simp [hx]⟩

theorem getD_mem_of_lt {α : Type} {l : List α} {i : Nat} (d : α) (h : i < l.length) : l.getD i d ∈ l := by
  rw [← List.getElem_eq_getD (h := h)]; exact List.getElem_mem h

theorem tape_len_le (c : FCfg) {i : Nat} (hi : i < c.tapes.length) : (c.tapes.getD i []).length ≤ csz c := by
  have := length_le_encTapes (getD_mem_of_lt [] hi); simp only [csz]; omega

theorem pos_le (c : FCfg) (i : Nat) : c.pos.getD i 0 ≤ csz c := by
  have := getD_le_sum c.pos i; simp only [csz]; omega

theorem cell_le (c : FCfg) {i : Nat} (hi : i < c.tapes.length) (p : Nat) : (c.tapes.getD i []).getD p 0 ≤ csz c := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (c.tapes.getD i [])[p]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    have := le_sum_of_mem (mem_encTapes (getD_mem_of_lt [] hi) (List.mem_of_getElem? h))
    simp only [csz]; omega

theorem reads_le (c : FCfg) {r : Nat} (hr : r ∈ c.reads) : r ≤ csz c := by
  simp only [FCfg.reads, List.mem_map] at hr
  obtain ⟨⟨p, t⟩, hm, rfl⟩ := hr
  rw [List.getD_eq_getElem?_getD]
  cases h : t[p]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    have := le_sum_of_mem (mem_encTapes (List.of_mem_zip hm).2 (List.mem_of_getElem? h))
    simp only [csz]; omega

theorem length_reads {T : TTable} {c : FCfg} (hc : CfgOK T c) : c.reads.length = T.k := by
  simp [FCfg.reads, hc.1, hc.2]

end Complexity.Univ
