import MacroPeg.HigherOrder.Mach.EvalStacks

/-!
# The tables of rows on stacks

`rowsTableP j` builds, for every type number `k = 0, …, tt.length` in order, the tabulated rows `rowsT j cap N tt k`:
it decides whether `k` is small from the tables `ORD` and `SZ`, and if so enumerates the candidate rows with an
odometer (digits on `D`, least significant on top) and appends the kept ones to `ROWS`, their number to `CNT` and
the old length of `ROWS` to `ROFF` (`rowsTableP_runs`).

* the rows of `p` are the digit vectors of length `N + 1` over `0, …, N + 2`;
* the candidates of an arrow `a ⇒ b` are the digit vectors over the row indices of `b`, one digit per row of `a`; a
  candidate is kept when it is monotone (`monoC`), checked pair by pair on the rows already in `ROWS`.

Lean-level facts first (digits: `rt_allVecs_range`, `rt_incr_dig`; rows: `rt_rowsT_arrow`, `rt_seg`), then the
machine, bottom up.
-/

namespace Shallot.MacroPeg.Mach

open Complexity
open Shallot.MacroPeg.HO

/-- All candidate tables enumerated for the rows of type number `k`. -/
def candNum (j cap N : Nat) (tt : List (Nat × Nat)) : Nat → Nat
  | 0 => (N + 3) ^ (N + 1)
  | k + 1 =>
    match tt[k]? with
    | some (a, b) => if small j cap tt (k + 1) then (rowsT j cap N tt b).length ^ (rowsT j cap N tt a).length else 0
    | none => 0
def rowsZ (j cap N : Nat) (tt : List (Nat × Nat)) : Nat :=
  2 + N + cap + tt.length + (rowsFlat j cap N tt).length + ((List.range (tt.length + 1)).map (candNum j cap N tt)).sum
def rowsCost (j cap N : Nat) (tt : List (Nat × Nat)) : Nat :=
  1000 * (rowsZ j cap N tt * rowsZ j cap N tt * rowsZ j cap N tt * rowsZ j cap N tt * rowsZ j cap N tt *
    rowsZ j cap N tt)

/-- The length of the rows of type number `k` (`0` when they are not tabulated). -/
def rt_lenE (j cap N : Nat) (tt : List (Nat × Nat)) (k : Nat) : Nat := if small j cap tt k then valT j cap N tt k else 0

/-- The flattened rows of the type numbers below `k`. -/
def rt_pre (j cap N : Nat) (tt : List (Nat × Nat)) (k : Nat) : List Nat :=
  ((List.range k).map (fun t => (rowsT j cap N tt t).flatten)).flatten

/-! ## The odometer: digits of a number -/

/-- The `m` lowest digits of `q` in base `B`, least significant first. -/
def rt_dig (B : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | m + 1, q => q % B :: rt_dig B m (q / B)

/-- The digit vector of `q`: most significant first (on a stack: the least significant digit on top). -/
def rt_vec (B m q : Nat) : List Nat := (rt_dig B m q).reverse

theorem rt_dig_length (B : Nat) : ∀ m q, (rt_dig B m q).length = m
  | 0, _ => rfl
  | m + 1, q => by simp [rt_dig, rt_dig_length B m]

theorem rt_vec_length (B m q : Nat) : (rt_vec B m q).length = m := by simp [rt_vec, rt_dig_length]

theorem rt_dig_zero (B : Nat) : ∀ m, rt_dig B m 0 = List.replicate m 0
  | 0 => rfl
  | m + 1 => by simp [rt_dig, rt_dig_zero B m, List.replicate_succ]

theorem rt_vec_zero (B m : Nat) : rt_vec B m 0 = List.replicate m 0 := by simp [rt_vec, rt_dig_zero]

theorem rt_dig_lt {B : Nat} (hB : 0 < B) : ∀ m q, ∀ d ∈ rt_dig B m q, d < B
  | 0, _, d, h => by simp [rt_dig] at h
  | m + 1, q, d, h => by
    simp only [rt_dig, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.mod_lt _ hB
    · exact rt_dig_lt hB m _ d h

/-- The last (most significant) digit. -/
theorem rt_dig_succ (B : Nat) : ∀ m q, rt_dig B (m + 1) q = rt_dig B m q ++ [q / B ^ m % B]
  | 0, q => by simp [rt_dig]
  | m + 1, q => by
    rw [rt_dig, rt_dig_succ B m (q / B), rt_dig, Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    rfl

/-- The digits see `q` only modulo `B ^ m`. -/
theorem rt_dig_add (B : Nat) : ∀ m q a, rt_dig B m (q + B ^ m * a) = rt_dig B m q
  | 0, _, _ => rfl
  | m + 1, q, a => by
    rcases Nat.eq_zero_or_pos B with rfl | hB
    · simp
    · rw [rt_dig, rt_dig, Nat.pow_succ', Nat.mul_assoc, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hB,
        rt_dig_add B m]

theorem rt_vec_block (B m a q : Nat) (ha : a < B) (hq : q < B ^ m) :
    rt_vec B (m + 1) (a * B ^ m + q) = a :: rt_vec B m q := by
  have hP : 0 < B ^ m := by omega
  have e : a * B ^ m + q = q + B ^ m * a := by rw [Nat.mul_comm]; omega
  have hd : (q + B ^ m * a) / B ^ m = a := by
    rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hq, Nat.zero_add]
  simp only [rt_vec, rt_dig_succ, e, rt_dig_add, hd, Nat.mod_eq_of_lt ha, List.reverse_append,
    List.reverse_singleton, List.singleton_append]

theorem rt_range_mul (P : Nat) : ∀ B, List.range (B * P) = (List.range B).flatMap (fun a => (List.range P).map (a * P + ·))
  | 0 => by simp
  | B + 1 => by
    rw [Nat.succ_mul, List.range_add, rt_range_mul P B, List.range_succ, List.flatMap_append]
    simp

/-- **The vectors in order are the digit vectors of `0, 1, …`.** -/
theorem rt_allVecs_range (B : Nat) : ∀ m, allVecs (List.range B) m = (List.range (B ^ m)).map (rt_vec B m)
  | 0 => rfl
  | m + 1 => by
    rw [allVecs, Nat.pow_succ', rt_range_mul, List.map_flatMap, rt_allVecs_range B m]
    rw [List.flatMap_def, List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro a ha
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro q hq
    simp only [Function.comp_apply]
    rw [rt_vec_block B m a q (List.mem_range.1 ha) (List.mem_range.1 hq)]

/-! ## One step of the odometer -/

/-- Add one to digits, least significant first (wrapping around). -/
def rt_incr (B : Nat) : List Nat → List Nat
  | [] => []
  | d :: r => if d + 1 = B then 0 :: rt_incr B r else (d + 1) :: r

theorem rt_incr_dig {B : Nat} (hB : 0 < B) : ∀ m q, rt_incr B (rt_dig B m q) = rt_dig B m (q + 1)
  | 0, _ => rfl
  | m + 1, q => by
    have hq : q + 1 = B * (q / B) + (q % B + 1) := by have := Nat.div_add_mod q B; omega
    simp only [rt_dig, rt_incr]
    split
    · rename_i h
      have h' : q + 1 = B * (q / B + 1) := by rw [hq, h, Nat.mul_succ]
      rw [rt_incr_dig hB m, h', Nat.mul_mod_right, Nat.mul_div_cancel_left _ hB]
    · rename_i h
      have hl : q % B + 1 < B := by have := Nat.mod_lt q hB; omega
      rw [hq, Nat.mul_add_mod, Nat.mod_eq_of_lt hl, Nat.mul_add_div hB, Nat.div_eq_of_lt hl]; rfl

/-- The number of digits `B - 1` at the bottom (they wrap to `0`). -/
def rt_lead (B : Nat) : List Nat → Nat
  | [] => 0
  | d :: r => if d + 1 = B then rt_lead B r + 1 else 0

/-- Add one to the lowest digit. -/
def rt_bump : List Nat → List Nat
  | [] => []
  | d :: r => (d + 1) :: r

/-- The flag the machine computes: the lowest digit is `B - 1`. -/
def rt_topF (B : Nat) : List Nat → Nat
  | [] => 0
  | d :: _ => if d + 1 = B then 1 else 0

theorem rt_incr_eq (B : Nat) : ∀ ds : List Nat, rt_incr B ds = List.replicate (rt_lead B ds) 0 ++ rt_bump (ds.drop (rt_lead B ds))
  | [] => rfl
  | d :: r => by
    simp only [rt_incr, rt_lead]
    split
    · rw [rt_incr_eq B r]; simp [List.replicate_succ]
    · rfl

theorem rt_lead_le (B : Nat) : ∀ ds : List Nat, rt_lead B ds ≤ ds.length
  | [] => Nat.le_refl _
  | d :: r => by
    simp only [rt_lead]; split
    · have := rt_lead_le B r; simp; omega
    · exact Nat.zero_le _

theorem rt_topF_lt (B : Nat) : ∀ (ds : List Nat) (i : Nat), i < rt_lead B ds → rt_topF B (ds.drop i) = 1
  | [], i, h => by simp [rt_lead] at h
  | d :: r, i, h => by
    simp only [rt_lead] at h
    split at h
    · rename_i hd
      cases i with
      | zero => simp [rt_topF, hd]
      | succ i => simp only [List.drop_succ_cons]; exact rt_topF_lt B r i (by omega)
    · omega

theorem rt_topF_lead (B : Nat) : ∀ ds : List Nat, rt_topF B (ds.drop (rt_lead B ds)) = 0
  | [] => rfl
  | d :: r => by
    simp only [rt_lead]
    split
    · simp only [List.drop_succ_cons]; exact rt_topF_lead B r
    · rename_i hd; simp [rt_topF, hd]

/-! ## Lists of lists -/

theorem rt_length_allVecs {α : Type} (xs : List α) : ∀ m, (allVecs xs m).length = xs.length ^ m
  | 0 => rfl
  | m + 1 => by
    rw [allVecs, Nat.pow_succ', ← rt_length_allVecs xs m]
    generalize allVecs xs m = L
    induction xs with
    | nil => simp
    | cons a xs ih => simp [List.flatMap_cons, ih, Nat.succ_mul, Nat.add_comm]

theorem rt_length_flatten {α : Type} (n : Nat) : ∀ L : List (List α), (∀ x ∈ L, x.length = n) →
    L.flatten.length = L.length * n
  | [], _ => by simp
  | x :: L, h => by
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.succ_mul]
    rw [h x List.mem_cons_self, rt_length_flatten n L (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    omega

/-- A row inside the flattened rows. -/
theorem rt_seg_flatten {α : Type} (n : Nat) : ∀ (L : List (List α)) (rest : List α) (i : Nat) (hi : i < L.length),
    (∀ x ∈ L, x.length = n) → ((L.flatten ++ rest).drop (i * n)).take n = L[i]
  | [], _, i, hi, _ => by simp at hi
  | x :: L, rest, 0, _, h => by simp [← h x List.mem_cons_self]
  | x :: L, rest, i + 1, hi, h => by
    have hx := h x List.mem_cons_self
    have e : (i + 1) * n = x.length + i * n := by rw [hx, Nat.succ_mul]; omega
    rw [List.flatten_cons, List.append_assoc, e, List.drop_append, List.getElem_cons_succ,
      List.drop_eq_nil_of_le (by omega), Nat.add_sub_cancel_left, List.nil_append]
    exact rt_seg_flatten n L rest i (by simpa using hi) (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem rt_pwB_self {α : Type} {f : α → α → Bool} (hf : ∀ a, f a a = true) : ∀ l : List α, pwB f l l = true
  | [] => rfl
  | a :: l => by simp [pwB, hf a, rt_pwB_self hf l]

theorem rt_leC_refl (c : List Nat) : leC c c = true := rt_pwB_self (by simp) c

theorem rt_monoC_const (A : List (List Nat)) (r : List Nat) : monoC A (List.replicate A.length r) = true := by
  unfold monoC
  simp only [List.all_eq_true]
  intro p hp p' hp'
  rw [List.eq_of_mem_replicate (List.of_mem_zip hp').2, List.eq_of_mem_replicate (List.of_mem_zip hp).2,
    rt_leC_refl]
  simp

/-! ## The rows of the types -/

section RowsFacts

variable {j cap N : Nat} {tt : List (Nat × Nat)}

theorem rt_getElem? {tt : List (Nat × Nat)} {k : Nat} (hk : k < tt.length) : tt[k]? = some (tt[k].1, tt[k].2) := by
  simp [hk]

theorem rt_small_arrow (hw : TTWF tt) {k : Nat} (hk : k < tt.length) (h : small j cap tt (k + 1)) :
    small j cap tt tt[k].1 ∧ small j cap tt tt[k].2 := by
  have hab := hw.2 k hk
  obtain ⟨h₁, h₂⟩ := h
  rw [ordNum] at h₁; rw [sizeNum] at h₂
  simp only [rt_getElem? hk, if_pos hab] at h₁ h₂
  have h₃ : sizeNum cap tt tt[k].1 + sizeNum cap tt tt[k].2 + 1 < cap := by
    rcases Nat.le_total cap (sizeNum cap tt tt[k].1 + sizeNum cap tt tt[k].2 + 1) with hc | hc
    · rw [Nat.min_eq_left hc] at h₂; omega
    · rw [Nat.min_eq_right hc] at h₂; exact h₂
  have h₄ := Nat.max_lt.1 h₁
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

theorem rt_rowsNum_succ (hw : TTWF tt) {k : Nat} (hk : k < tt.length) :
    rowsNum N tt (k + 1) = ((allVecs (rowsNum N tt tt[k].2) (rowsNum N tt tt[k].1).length).filter
      (monoC (rowsNum N tt tt[k].1))).map List.flatten := by
  rw [rowsNum]; simp only [rt_getElem? hk, if_pos (hw.2 k hk)]

theorem rt_rowsNum_ne (hw : TTWF tt) : ∀ k, k ≤ tt.length → rowsNum N tt k ≠ []
  | 0, _ => by
    rw [rowsNum]
    exact List.ne_nil_of_mem ((mem_allVecs _ _ (List.replicate (N + 1) 0)).2
      ⟨by simp, fun a ha => by rw [List.eq_of_mem_replicate ha]; simp⟩)
  | k + 1, hk => by
    have hlt : k < tt.length := by omega
    have hab := hw.2 k hlt
    rw [rt_rowsNum_succ hw hlt]
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ (rt_rowsNum_ne hw tt[k].2 (by omega))
    refine List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_filter.2 ⟨(mem_allVecs _ _ _).2 ⟨?_, ?_⟩,
      rt_monoC_const _ r⟩))
    · simp
    · intro a ha; rw [List.eq_of_mem_replicate ha]; exact hr
termination_by k => k
decreasing_by all_goals omega

end RowsFacts

section RowsFacts2

variable {j cap N : Nat} {tt : List (Nat × Nat)}

theorem rt_map_getD {α : Type} (L : List α) (d : α) : (List.range L.length).map (fun x => L.getD x d) = L := by
  apply List.ext_getElem
  · simp
  · intro i _ h; simp [List.getElem?_eq_getElem h]

theorem rt_rowsT_small {k : Nat} (h : small j cap tt k) : rowsT j cap N tt k = rowsNum N tt k := by
  rw [rowsT, if_pos h]

theorem rt_valT_succ (hw : TTWF tt) {k : Nat} (hk : k < tt.length) :
    valT j cap N tt (k + 1) = (rowsT j cap N tt tt[k].1).length * valT j cap N tt tt[k].2 := by
  rw [valT]; simp only [rt_getElem? hk, if_pos (hw.2 k hk)]

theorem rt_row_length (hw : TTWF tt) : ∀ k, k ≤ tt.length → small j cap tt k →
    ∀ r ∈ rowsNum N tt k, r.length = valT j cap N tt k
  | 0, _, _, r, hr => by
    rw [rowsNum] at hr; rw [valT]; exact ((mem_allVecs _ _ _).1 hr).1
  | k + 1, hk, hs, r, hr => by
    have hlt : k < tt.length := by omega
    have hab := hw.2 k hlt
    obtain ⟨ha, hb⟩ := rt_small_arrow hw hlt hs
    rw [rt_rowsNum_succ hw hlt] at hr
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
    obtain ⟨hcl, hcm⟩ := (mem_allVecs _ _ _).1 (List.mem_filter.1 hc).1
    rw [rt_valT_succ hw hlt, rt_rowsT_small ha, ← hcl]
    exact rt_length_flatten _ c (fun x hx => rt_row_length hw tt[k].2 (by omega) hb x (hcm x hx))
termination_by k => k
decreasing_by omega

theorem rt_rowsT_len (hw : TTWF tt) {k : Nat} (hk : k ≤ tt.length) :
    ∀ r ∈ rowsT j cap N tt k, r.length = rt_lenE j cap N tt k := by
  intro r hr
  unfold rowsT at hr; unfold rt_lenE
  split at hr
  · rename_i hs; rw [if_pos hs]; exact rt_row_length hw k hk hs r hr
  · simp at hr

theorem rt_flat_len (hw : TTWF tt) {k : Nat} (hk : k ≤ tt.length) :
    (rowsT j cap N tt k).flatten.length = (rowsT j cap N tt k).length * rt_lenE j cap N tt k :=
  rt_length_flatten _ _ (rt_rowsT_len hw hk)

theorem rt_lenE_le (hw : TTWF tt) {k : Nat} (hk : k ≤ tt.length) :
    rt_lenE j cap N tt k ≤ (rowsT j cap N tt k).flatten.length := by
  rw [rt_flat_len hw hk]
  unfold rt_lenE
  split
  · rename_i hs
    have : (rowsT j cap N tt k).length ≠ 0 := by
      rw [rt_rowsT_small hs]; simpa using rt_rowsNum_ne (N := N) hw k hk
    exact Nat.le_mul_of_pos_left _ (by omega)
  · exact Nat.zero_le _

theorem rt_count_le (hw : TTWF tt) : ∀ k, k ≤ tt.length → (rowsT j cap N tt k).length ≤ candNum j cap N tt k
  | 0, _ => by
    unfold rowsT; rw [candNum]
    split
    · rw [rowsNum, rt_length_allVecs, List.length_range]; exact Nat.le_refl _
    · simp
  | k + 1, hk => by
    have hlt : k < tt.length := by omega
    unfold rowsT; rw [candNum]
    simp only [rt_getElem? hlt]
    split
    · rename_i hs
      obtain ⟨ha, hb⟩ := rt_small_arrow hw hlt hs
      rw [rt_rowsNum_succ hw hlt, List.length_map, rt_rowsT_small ha, rt_rowsT_small hb, ← rt_length_allVecs]
      exact List.length_filter_le _ _
    · simp

/-- The candidates of an arrow, in the order of their digit vectors. -/
theorem rt_rowsT_arrow (hw : TTWF tt) {k : Nat} (hk : k < tt.length) (hs : small j cap tt (k + 1)) :
    rowsT j cap N tt (k + 1) =
      (((List.range ((rowsT j cap N tt tt[k].2).length ^ (rowsT j cap N tt tt[k].1).length)).map
        (fun q => (rt_vec (rowsT j cap N tt tt[k].2).length (rowsT j cap N tt tt[k].1).length q).map
          (fun x => (rowsT j cap N tt tt[k].2).getD x []))).filter
        (monoC (rowsT j cap N tt tt[k].1))).map List.flatten := by
  obtain ⟨ha, hb⟩ := rt_small_arrow hw hk hs
  rw [rt_rowsT_small hs, rt_rowsNum_succ hw hk, rt_rowsT_small (N := N) ha, rt_rowsT_small (N := N) hb]
  generalize rowsNum N tt tt[k].1 = A
  generalize rowsNum N tt tt[k].2 = Bs
  conv => lhs; rw [← rt_map_getD Bs [], allVecs_map, rt_allVecs_range, List.map_map]
  rfl

/-- The rows of `p`, in the order of their digit vectors. -/
theorem rt_rowsT_zero (hs : small j cap tt 0) :
    rowsT j cap N tt 0 = (List.range ((N + 3) ^ (N + 1))).map (rt_vec (N + 3) (N + 1)) := by
  rw [rt_rowsT_small hs, rowsNum, rt_allVecs_range]

theorem rt_pre_succ (k : Nat) : rt_pre j cap N tt (k + 1) = rt_pre j cap N tt k ++ (rowsT j cap N tt k).flatten := by
  simp [rt_pre, List.range_succ]

theorem rt_pre_add (k : Nat) : ∀ d, ∃ X, rt_pre j cap N tt (k + d) = rt_pre j cap N tt k ++ X
  | 0 => ⟨[], by simp⟩
  | d + 1 => by
    obtain ⟨X, hX⟩ := rt_pre_add k d
    exact ⟨X ++ (rowsT j cap N tt (k + d)).flatten, by rw [← Nat.add_assoc, rt_pre_succ, hX, List.append_assoc]⟩

/-- **A row read from the rows written so far.** -/
theorem rt_seg (hw : TTWF tt) {t k : Nat} (htk : t < k) (ht : t ≤ tt.length) {i : Nat}
    (hi : i < (rowsT j cap N tt t).length) (e : List Nat) :
    (((rt_pre j cap N tt k ++ e).drop ((rt_pre j cap N tt t).length + i * rt_lenE j cap N tt t)).take
      (rt_lenE j cap N tt t)) = (rowsT j cap N tt t)[i] := by
  obtain ⟨X, hX⟩ := rt_pre_add (j := j) (cap := cap) (N := N) (tt := tt) (t + 1) (k - (t + 1))
  rw [show t + 1 + (k - (t + 1)) = k by omega, rt_pre_succ] at hX
  rw [hX, List.append_assoc, List.append_assoc, List.drop_append, List.drop_eq_nil_of_le (by omega),
    Nat.add_sub_cancel_left, List.nil_append]
  exact rt_seg_flatten _ _ _ i hi (rt_rowsT_len hw ht)

theorem rt_pre_le (k : Nat) (hk : k ≤ tt.length + 1) :
    (rt_pre j cap N tt k).length ≤ (rowsFlat j cap N tt).length := by
  obtain ⟨X, hX⟩ := rt_pre_add (j := j) (cap := cap) (N := N) (tt := tt) k (tt.length + 1 - k)
  rw [show k + (tt.length + 1 - k) = tt.length + 1 by omega] at hX
  have e : rowsFlat j cap N tt = rt_pre j cap N tt (tt.length + 1) := rfl
  rw [e, hX, List.length_append]; omega

end RowsFacts2

/-! ## Scratch stacks -/

/-- The loop counter over the arrow type numbers. -/
abbrev rt_KC : Fin NK := 18
/-- The current type number. -/
abbrev rt_KU : Fin NK := 19
/-- The row lengths of the type numbers done. -/
abbrev rt_LEN : Fin NK := 20
/-- The parameters of the type being tabulated. -/
abbrev rt_PAR : Fin NK := 21
/-- The digits of the odometer. -/
abbrev rt_D : Fin NK := 22
/-- The odometer counter. -/
abbrev rt_QC : Fin NK := 23
/-- Flags. -/
abbrev rt_MF : Fin NK := 24
abbrev rt_I : Fin NK := 25
abbrev rt_I2 : Fin NK := 26
abbrev rt_P : Fin NK := 27
abbrev rt_O1 : Fin NK := 28
abbrev rt_O2 : Fin NK := 29
/-- The index popped by `peekAt`. -/
abbrev rt_IX : Fin NK := 30
/-- The scratch of `peekAt`. -/
abbrev rt_T : Fin NK := 31
abbrev rt_V1 : Fin NK := 32
abbrev rt_V2 : Fin NK := 33

open Lean in
/-- Equality of stacks updated at the given (numeral) places: compare at each place, then elsewhere. -/
macro "rt_ext" "[" ts:term,* "]" : tactic => do
  let mut tac ← `(tactic| simp_all [Lists.set])
  for t in ts.getElems.reverse do
    tac ← `(tactic| (by_cases hx : x = $t
                     next => subst hx; simp (config := { decide := true }) [Lists.set, -List.getD_eq_getElem?_getD]
                     next => ($tac:tactic)))
  `(tactic| (funext x; $tac))

open Lean in
/-- `rt_ext`, using the given facts at the places. -/
macro "rt_extU" "[" ts:term,* "]" "[" ls:term,* "]" : tactic => do
  let ls' ← ls.getElems.mapM (fun t => `(Lean.Parser.Tactic.simpLemma| $t:term))
  let mut tac ← `(tactic| simp_all [Lists.set])
  for t in ts.getElems.reverse do
    tac ← `(tactic| (by_cases hx : x = $t
                     next => subst hx; simp (config := { decide := true }) [Lists.set, -List.getD_eq_getElem?_getD, $ls',*]
                     next => ($tac:tactic)))
  `(tactic| (funext x; $tac))

/-- The value of updated stacks at a numeral place. -/
macro "rt_at" : tactic => `(tactic| simp (config := { decide := true }) only [Lists.set, ↓reduceIte, List.nil_append])

/-! ## Counted loops -/

/-- Run `body` `n` times, `n` popped from `c` (the body sees the count left, lowered). -/
def rt_for (c : Fin NK) (body : NProg NK) : NProg NK := .seq (.loop c .pos (.seq (.prim (.dec c)) body)) (.prim (.pop c))

theorem rt_for_runs {c : Fin NK} {body : NProg NK} (F : Nat → Lists NK) (lc : List Nat) (n T : Nat)
    (hc : ∀ m, m ≤ n → F m c = lc ++ [n - m])
    (hbody : ∀ m, m < n → NRuns body ((F m).set c (lc ++ [n - m - 1])) (F (m + 1)) T) :
    NRuns (rt_for c body) (F 0) ((F n).set c lc) (n * (T + 2) + 2) := by
  have hl := nruns_family_const (i := c) (c := .pos) (p := .seq (.prim (.dec c)) body) F n (T + 1)
    (fun m hm => by rw [hc m (by omega), show n - m = (n - m - 1) + 1 by omega]; simp)
    (by rw [hc n (Nat.le_refl _), Nat.sub_self]; simp)
    (fun m hm => ((nruns_dec c (F m) (hc m (by omega))).seq (hbody m hm)).mono (by omega))
  have hp := nruns_pop c (F n) (l := lc) (v := 0) (by rw [hc n (Nat.le_refl _), Nat.sub_self])
  have e : n * (T + 1 + 1) = n * (T + 2) := rfl
  exact (hl.seq hp).mono (by omega)

theorem rt_for_cost {n T c W Z : Nat} (hn : n ≤ Z) (hT : T ≤ c * W) : n * (T + 2) + 2 ≤ c * (Z * W) + 2 * Z + 2 := by
  have h₁ : n * (T + 2) ≤ Z * (c * W + 2) := Nat.mul_le_mul hn (by omega)
  have h₂ : Z * (c * W + 2) = c * (Z * W) + 2 * Z := by rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm Z 2]
  omega

/-! ## Arithmetic on the tops -/

/-- Lower the tops of `V` (by `x`, to `0`) and `W` (to `y - x`). -/
def rt_sub (V W : Fin NK) : NProg NK := .loop V .pos (.seq (.prim (.dec V)) (.prim (.dec W)))

theorem rt_sub_runs {V W : Fin NK} (hVW : V ≠ W) (S : Lists NK) {lv lw : List Nat} {x y : Nat}
    (hV : S V = lv ++ [x]) (hW : S W = lw ++ [y]) :
    NRuns (rt_sub V W) S ((S.set V (lv ++ [0])).set W (lw ++ [y - x])) (3 * x + 1) := by
  let F : Nat → Lists NK := fun m => (S.set V (lv ++ [x - m])).set W (lw ++ [y - m])
  have h0 : F 0 = S := by
    simp only [F, Nat.sub_zero, ← hV, ← hW, Lists.set_get_self]
  have hFV : ∀ m, F m V = lv ++ [x - m] := fun m => by simp only [F]; rw [Lists.set_ne _ _ hVW, Lists.set_same]
  have hl := nruns_family_const (i := V) (c := .pos) (p := .seq (.prim (.dec V)) (.prim (.dec W))) F x 2
    (fun m hm => by rw [hFV, show x - m = (x - m - 1) + 1 by omega]; simp)
    (by rw [hFV, Nat.sub_self]; simp)
    (fun m hm => by
      have h₁ := nruns_dec V (F m) (hFV m)
      have h₂ := nruns_dec W ((F m).set V (lv ++ [x - m - 1])) (l := lw) (v := y - m)
        (by rw [Lists.set_ne _ _ (Ne.symm hVW)]; simp only [F, Lists.set_same])
      have e : ((F m).set V (lv ++ [x - m - 1])).set W (lw ++ [y - m - 1]) = F (m + 1) := by
        simp only [F]; rw [show x - m - 1 = x - (m + 1) by omega, show y - m - 1 = y - (m + 1) by omega]; lists_eq
      rw [e] at h₂; exact h₁.seq h₂)
  rw [h0] at hl
  rw [show (S.set V (lv ++ [0])).set W (lw ++ [y - x]) = F x by simp only [F, Nat.sub_self]]
  exact hl.mono (by omega)

/-- Pop the tops `x` of `V` and `y` of `W`, and push on `O` whether they are equal. -/
def rt_eqF (V W O : Fin NK) : NProg NK :=
  .seq (.prim (.inc W)) (.seq (rt_sub V W) (.seq (.prim (.pop V))
    (.ite W .zero (.seq (.prim (.pop W)) (.prim (.pushZ O)))
      (.seq (.prim (.dec W)) (.ite W .zero (.seq (.prim (.pop W)) (npushC O 1))
        (.seq (.prim (.pop W)) (.prim (.pushZ O))))))))

theorem rt_eqF_runs {V W O : Fin NK} (hVW : V ≠ W) (hVO : V ≠ O) (hWO : W ≠ O) (S : Lists NK) {lv lw : List Nat}
    {x y : Nat} (hV : S V = lv ++ [x]) (hW : S W = lw ++ [y]) :
    NRuns (rt_eqF V W O) S (((S.set V lv).set W lw).set O (S O ++ [if x = y then 1 else 0])) (3 * x + 12) := by
  have x₁ := nruns_inc W S hW
  have x₂ := rt_sub_runs hVW (S.set W (lw ++ [y + 1])) (lv := lv) (lw := lw) (x := x) (y := y + 1)
    (by rw [Lists.set_ne _ _ hVW]; exact hV) (by simp)
  have x₃ := nruns_pop V (((S.set W (lw ++ [y + 1])).set V (lv ++ [0])).set W (lw ++ [y + 1 - x])) (l := lv) (v := 0)
    (by rw [Lists.set_ne _ _ hVW, Lists.set_same])
  let S₃ := (((S.set W (lw ++ [y + 1])).set V (lv ++ [0])).set W (lw ++ [y + 1 - x])).set V lv
  have hS₃W : S₃ W = lw ++ [y + 1 - x] := by simp only [S₃]; rw [Lists.set_ne _ _ (Ne.symm hVW), Lists.set_same]
  have hS₃O : S₃ O = S O := by simp only [S₃]; lists_at
  have hfin : ∀ r, ((S₃.set W lw).set O (S O ++ [r])) = ((S.set V lv).set W lw).set O (S O ++ [r]) := by
    intro r; simp only [S₃]; lists_eq
  rcases hd : y + 1 - x with _ | _ | d
  · -- `x > y`
    have hne : x ≠ y := by omega
    have p₁ := nruns_pop W S₃ (l := lw) (v := 0) (by rw [hS₃W, hd])
    have p₂ := nruns_pushZ O (S₃.set W lw)
    rw [Lists.set_ne _ _ (Ne.symm hWO), hS₃O, hfin] at p₂
    rw [if_neg hne]
    have ip : NRuns (.ite W .zero (.seq (.prim (.pop W)) (.prim (.pushZ O)))
      (.seq (.prim (.dec W)) (.ite W .zero (.seq (.prim (.pop W)) (npushC O 1))
        (.seq (.prim (.pop W)) (.prim (.pushZ O)))))) S₃ (((S.set V lv).set W lw).set O (S O ++ [0])) 3 :=
      (p₁.seq p₂).iteT (by rw [hS₃W, hd]; simp)
    exact (x₁.seq (x₂.seq (x₃.seq ip))).mono (by omega)
  · -- `x = y`
    have he : x = y := by omega
    have p₀ := nruns_dec W S₃ (by rw [hS₃W, hd])
    have p₁ := nruns_pop W (S₃.set W (lw ++ [0 + 1 - 1])) (l := lw) (v := 0) (by simp)
    rw [Lists.set_set_u] at p₁
    have p₂ := nruns_pushC O (S₃.set W lw) 1
    rw [Lists.set_ne _ _ (Ne.symm hWO), hS₃O, hfin] at p₂
    rw [if_pos he]
    have ip : NRuns (.ite W .zero (.seq (.prim (.pop W)) (.prim (.pushZ O)))
      (.seq (.prim (.dec W)) (.ite W .zero (.seq (.prim (.pop W)) (npushC O 1))
        (.seq (.prim (.pop W)) (.prim (.pushZ O)))))) S₃ (((S.set V lv).set W lw).set O (S O ++ [1])) 7 :=
      ((p₀.seq ((p₁.seq p₂).iteT (by simp))).iteF (by rw [hS₃W, hd]; simp)).mono (by omega)
    exact (x₁.seq (x₂.seq (x₃.seq ip))).mono (by omega)
  · -- `x < y`
    have hne : x ≠ y := by omega
    have p₀ := nruns_dec W S₃ (by rw [hS₃W, hd])
    have p₁ := nruns_pop W (S₃.set W (lw ++ [d + 1 + 1 - 1])) (l := lw) (v := d + 1) (by simp)
    rw [Lists.set_set_u] at p₁
    have p₂ := nruns_pushZ O (S₃.set W lw)
    rw [Lists.set_ne _ _ (Ne.symm hWO), hS₃O, hfin] at p₂
    rw [if_neg hne]
    have ip : NRuns (.ite W .zero (.seq (.prim (.pop W)) (.prim (.pushZ O)))
      (.seq (.prim (.dec W)) (.ite W .zero (.seq (.prim (.pop W)) (npushC O 1))
        (.seq (.prim (.pop W)) (.prim (.pushZ O)))))) S₃ (((S.set V lv).set W lw).set O (S O ++ [0])) 7 :=
      ((p₀.seq ((p₁.seq p₂).iteF (by simp))).iteF (by rw [hS₃W, hd]; simp)).mono (by omega)
    exact (x₁.seq (x₂.seq (x₃.seq ip))).mono (by omega)

/-- Pop the top `x` of `v` and push on `f` whether `x < j` (constant `j`), in time linear in `x`. -/
def rt_ltC (v f : Fin NK) : Nat → NProg NK
  | 0 => .seq (.prim (.pop v)) (.prim (.pushZ f))
  | j + 1 => .ite v .zero (.seq (.prim (.pop v)) (npushC f 1)) (.seq (.prim (.dec v)) (rt_ltC v f j))

theorem rt_ltC_runs {v f : Fin NK} (hvf : v ≠ f) : ∀ (j : Nat) (S : Lists NK) (l : List Nat) (x : Nat),
    S v = l ++ [x] → NRuns (rt_ltC v f j) S ((S.set v l).set f (S f ++ [if x < j then 1 else 0])) (2 * x + 4)
  | 0, S, l, x, h => by
    have p₁ := nruns_pop v S h
    have p₂ := nruns_pushZ f (S.set v l)
    rw [Lists.set_ne _ _ (Ne.symm hvf)] at p₂
    simp only [Nat.not_lt_zero, if_false]
    exact (p₁.seq p₂).mono (by omega)
  | j + 1, S, l, 0, h => by
    have p₁ := nruns_pop v S h
    have p₂ := nruns_pushC f (S.set v l) 1
    rw [Lists.set_ne _ _ (Ne.symm hvf)] at p₂
    rw [if_pos (by omega)]
    exact ((p₁.seq p₂).iteT (by rw [h]; simp)).mono (by omega)
  | j + 1, S, l, x + 1, h => by
    have p₁ := nruns_dec v S h
    have p₂ := rt_ltC_runs hvf j (S.set v (l ++ [x + 1 - 1])) l x (by simp)
    rw [Lists.set_set_u, Lists.set_ne _ _ (Ne.symm hvf)] at p₂
    rw [show (if x + 1 < j + 1 then 1 else 0) = (if x < j then 1 else 0) by simp]
    exact ((p₁.seq p₂).iteF (by rw [h]; simp)).mono (by omega)

/-- Pop the top `x` of `X` and add `x * y` to the top of `A` (`y`: the top of `Y`, kept; `TM`: scratch). -/
def rt_mul (X Y A TM : Fin NK) (h : Y ≠ TM) : NProg NK := rt_for X (.seq (.prim (.dup Y TM h)) (addTo TM A))

theorem rt_mul_runs {X Y A TM : Fin NK} {h : Y ≠ TM} (hXY : X ≠ Y) (hXA : X ≠ A) (hXT : X ≠ TM) (hYA : Y ≠ A)
    (hAT : A ≠ TM) (S : Lists NK)
    {lx ly la : List Nat} {x y a : Nat} (hX : S X = lx ++ [x]) (hY : S Y = ly ++ [y]) (hA : S A = la ++ [a])
    (hT : S TM = []) :
    NRuns (rt_mul X Y A TM h) S ((S.set X lx).set A (la ++ [a + x * y])) (x * (3 * y + 7) + 2) := by
  have hYT := h
  let F : Nat → Lists NK := fun m => (S.set X (lx ++ [x - m])).set A (la ++ [a + m * y])
  have h0 : F 0 = S := by simp only [F, Nat.sub_zero, Nat.zero_mul, Nat.add_zero, ← hX, ← hA, Lists.set_get_self]
  have hl := rt_for_runs (c := X) (body := .seq (.prim (.dup Y TM h)) (addTo TM A)) F lx x (3 * y + 3)
    (fun m _ => by simp only [F]; rw [Lists.set_ne _ _ hXA, Lists.set_same])
    (fun m hm => by
      let G := (F m).set X (lx ++ [x - m - 1])
      have hGY : G Y = ly ++ [y] := by simp only [G, F]; lists_at
      have hGT : G TM = [] := by simp only [G, F]; lists_at
      have hGA : G A = la ++ [a + m * y] := by simp only [G, F]; lists_at
      have p₁ := nruns_dup Y TM h G hGY
      rw [hGT, List.nil_append] at p₁
      have p₂ := nruns_addTo TM A (Ne.symm hAT) (G.set TM [y]) (l := []) (l' := la) (a := y) (b := a + m * y)
        (by simp) (by rw [Lists.set_ne _ _ hAT]; exact hGA)
      have e : ((G.set TM [y]).set TM []).set A (la ++ [a + m * y + y]) = F (m + 1) := by
        simp only [G, F]
        rw [show x - m - 1 = x - (m + 1) by omega, show a + m * y + y = a + (m + 1) * y by rw [Nat.succ_mul]; omega]
        lists_eq
      rw [e] at p₂
      exact (p₁.seq p₂).mono (by omega))
  rw [h0] at hl
  rw [show (S.set X lx).set A (la ++ [a + x * y]) = (F x).set X lx by simp only [F]; lists_eq]
  exact hl.mono (by rw [show 3 * y + 3 + 2 = 3 * y + 5 by omega]; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _)

/-! ## Reading tables -/

/-- Push entry `k` (a constant) of the table `i` on `o`. -/
def rt_get (i o : Fin NK) (k : Nat) (h₁ : i ≠ rt_T) (h₂ : rt_T ≠ o) : NProg NK :=
  .seq (npushC rt_IX k) (peekAt i rt_T rt_IX o h₁ h₂)

theorem rt_get_runs {i o : Fin NK} {h₁ : i ≠ rt_T} {h₂ : rt_T ≠ o} (hd : [i, rt_T, rt_IX, o].Nodup)
    (hiX : i ≠ rt_IX) (hoX : o ≠ rt_IX) (S : Lists NK) (k : Nat)
    (hIX : S rt_IX = []) (hT : S rt_T = []) (hk : k < (S i).length) :
    NRuns (rt_get i o k h₁ h₂) S (S.set o (S o ++ [(S i).getD k 0])) (6 * (S i).length + 5 * k + 7) := by
  have x₁ := nruns_pushC rt_IX S k
  rw [hIX, List.nil_append] at x₁
  have x₂ := nruns_peekAt i rt_T rt_IX o h₁ h₂ hd (S.set rt_IX [k]) (by rw [Lists.set_ne _ _ (by decide)]; exact hT)
    (lc := []) (k := k) (by simp) (by rw [Lists.set_ne _ _ hiX]; exact hk)
  rw [List.getElem_eq_getD 0] at x₂
  simp only [Lists.set_ne _ _ hiX, Lists.set_ne _ _ hoX, Lists.set_set_u] at x₂
  rw [set_nil_self hIX] at x₂
  exact (x₁.seq x₂).mono (by omega)

/-- Push entry `k` of the table `i` on `o`, where `k` is the top of `c` (kept). -/
def rt_getAt (i c o : Fin NK) (h₀ : c ≠ rt_IX) (h₁ : i ≠ rt_T) (h₂ : rt_T ≠ o) : NProg NK :=
  .seq (.prim (.dup c rt_IX h₀)) (peekAt i rt_T rt_IX o h₁ h₂)

theorem rt_getAt_runs {i c o : Fin NK} {h₀ : c ≠ rt_IX} {h₁ : i ≠ rt_T} {h₂ : rt_T ≠ o}
    (hd : [i, rt_T, rt_IX, o].Nodup) (hiX : i ≠ rt_IX) (hoX : o ≠ rt_IX) (S : Lists NK) {lc : List Nat} {k : Nat}
    (hc : S c = lc ++ [k]) (hIX : S rt_IX = []) (hT : S rt_T = []) (hk : k < (S i).length) :
    NRuns (rt_getAt i c o h₀ h₁ h₂) S (S.set o (S o ++ [(S i).getD k 0])) (6 * (S i).length + 4 * k + 7) := by
  have x₁ := nruns_dup c rt_IX h₀ S hc
  rw [hIX, List.nil_append] at x₁
  have x₂ := nruns_peekAt i rt_T rt_IX o h₁ h₂ hd (S.set rt_IX [k]) (by rw [Lists.set_ne _ _ (by decide)]; exact hT)
    (lc := []) (k := k) (by simp) (by rw [Lists.set_ne _ _ hiX]; exact hk)
  rw [List.getElem_eq_getD 0] at x₂
  simp only [Lists.set_ne _ _ hiX, Lists.set_ne _ _ hoX, Lists.set_set_u] at x₂
  rw [set_nil_self hIX] at x₂
  exact (x₁.seq x₂).mono (by omega)

/-! ## The order of two rows of `ROWS` -/

/-- One position of the order: `x = 0` or `x = y`. -/
def rt_ok (x y : Nat) : Bool := x == 0 || x == y

theorem rt_leC_range : ∀ (c c' : List Nat), c.length = c'.length →
    leC c c' = (List.range c.length).all (fun r => rt_ok (c.getD r 0) (c'.getD r 0))
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: c, b :: c', h => by
    have ih := rt_leC_range c c' (by simpa using h)
    unfold leC at ih ⊢
    simp only [Shallot.MacroPeg.HO.pwB, List.length_cons, List.range_succ_eq_map, List.all_cons, List.all_map]
    rw [ih]
    simp [rt_ok, Function.comp_def]

theorem rt_all_rev (L : Nat) (g : Nat → Bool) :
    (List.range L).all (fun t => g (L - 1 - t)) = (List.range L).all g := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h r hr
    have := h (L - 1 - r) (by omega)
    rwa [show L - 1 - (L - 1 - r) = r by omega] at this
  · intro h t ht
    exact h _ (by omega)

/-- The order of two segments of `w`, position by position. -/
theorem rt_leC_seg (w : List Nat) (o₁ o₂ L : Nat) (h₁ : o₁ + L ≤ w.length) (h₂ : o₂ + L ≤ w.length) :
    leC ((w.drop o₁).take L) ((w.drop o₂).take L) =
      (List.range L).all (fun t => rt_ok (w.getD (o₁ + (L - 1 - t)) 0) (w.getD (o₂ + (L - 1 - t)) 0)) := by
  rw [rt_leC_range _ _ (by simp; omega), rt_all_rev L (fun r => rt_ok (w.getD (o₁ + r) 0) (w.getD (o₂ + r) 0))]
  rw [show ((w.drop o₁).take L).length = L by simp; omega]
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_range]
  have e : ∀ o r, r < L → ((w.drop o).take L).getD r 0 = w.getD (o + r) 0 := by
    intro o r hr
    simp [List.getD_eq_getElem?_getD, hr, List.getElem?_drop]
  constructor
  · intro h r hr; rw [← e o₁ r hr, ← e o₂ r hr]; exact h r hr
  · intro h r hr; rw [e o₁ r hr, e o₂ r hr]; exact h r hr

/-- Update the flag on `MF` with the order at one position (`V1`: `x`, `V2`: `y`, both popped). -/
def rt_okUpd : NProg NK :=
  .ite rt_V1 .zero (.seq (.prim (.pop rt_V1)) (.prim (.pop rt_V2)))
    (.seq (rt_eqF rt_V1 rt_V2 rt_MF) (.ite rt_MF .pos (.prim (.pop rt_MF))
      (.seq (.prim (.pop rt_MF)) (.seq (.prim (.pop rt_MF)) (.prim (.pushZ rt_MF))))))

theorem rt_okUpd_runs (S : Lists NK) {x y f : Nat} {l : List Nat} (hV1 : S rt_V1 = [x]) (hV2 : S rt_V2 = [y])
    (hM : S rt_MF = l ++ [f]) :
    NRuns rt_okUpd S (((S.set rt_V1 []).set rt_V2 []).set rt_MF (l ++ [if rt_ok x y then f else 0])) (3 * x + 17) := by
  rcases x with _ | x
  · have p₁ := nruns_pop rt_V1 S (l := []) (v := 0) hV1
    have p₂ := nruns_pop rt_V2 (S.set rt_V1 []) (l := []) (v := y) (by rw [Lists.set_ne _ _ (by decide)]; exact hV2)
    have e : ((S.set rt_V1 []).set rt_V2 []).set rt_MF (l ++ [if rt_ok 0 y then f else 0]) =
        (S.set rt_V1 []).set rt_V2 [] := by
      simp only [rt_ok, BEq.rfl, Bool.true_or, if_true]
      rw [← hM]; rt_ext [rt_V1, rt_V2, rt_MF]
    rw [e]
    exact ((p₁.seq p₂).iteT (by rw [hV1]; rfl)).mono (by omega)
  · have p₁ := rt_eqF_runs (V := rt_V1) (W := rt_V2) (O := rt_MF) (by decide) (by decide) (by decide) S
      (lv := []) (lw := []) (x := x + 1) (y := y) hV1 hV2
    rw [hM] at p₁
    let S₁ := ((S.set rt_V1 []).set rt_V2 [])
    by_cases hxy : x + 1 = y
    · have hok : rt_ok (x + 1) y = true := by simp [rt_ok, hxy]
      rw [if_pos hxy] at p₁
      have p₂ := nruns_pop rt_MF (S₁.set rt_MF (l ++ [f] ++ [1])) (l := l ++ [f]) (v := 1) (by simp)
      rw [Lists.set_set_u] at p₂
      rw [hok, if_pos rfl]
      exact ((p₁.seq (p₂.iteT (by simp [NTest.eval]))).iteF (by rw [hV1]; rfl)).mono (by omega)
    · have hok : rt_ok (x + 1) y = false := by simp [rt_ok, hxy]
      rw [if_neg hxy] at p₁
      have p₂ := nruns_pop rt_MF (S₁.set rt_MF (l ++ [f] ++ [0])) (l := l ++ [f]) (v := 0) (by simp)
      have p₃ := nruns_pop rt_MF ((S₁.set rt_MF (l ++ [f] ++ [0])).set rt_MF (l ++ [f])) (l := l) (v := f) (by simp)
      have p₄ := nruns_pushZ rt_MF (((S₁.set rt_MF (l ++ [f] ++ [0])).set rt_MF (l ++ [f])).set rt_MF l)
      simp only [Lists.set_set_u, Lists.set_same] at p₄
      simp only [Lists.set_set_u] at p₂ p₃
      rw [hok]
      simp only [Bool.false_eq_true, if_false]
      exact ((p₁.seq ((p₂.seq (p₃.seq p₄)).iteF (by simp [NTest.eval]))).iteF (by rw [hV1]; rfl)).mono (by omega)

/-- Push `w[o + r]` on `V` (`O`: `o`, `P`: `r`, both kept). -/
def rt_fetch (O V : Fin NK) (h₀ : O ≠ rt_IX) (h₁ : rt_P ≠ V) (h₂ : rt_T ≠ V) : NProg NK :=
  .seq (.prim (.dup O rt_IX h₀)) (.seq (.prim (.dup rt_P V h₁)) (.seq (addTo V rt_IX)
    (peekAt ROWS rt_T rt_IX V (by decide) h₂)))

theorem rt_fetch_runs {O V : Fin NK} {h₀ : O ≠ rt_IX} {h₁ : rt_P ≠ V} {h₂ : rt_T ≠ V}
    (hd : [O, V, rt_P, rt_IX, rt_T, ROWS].Nodup) (hd' : [ROWS, rt_T, rt_IX, V].Nodup) (S : Lists NK) {o r : Nat}
    (hO : S O = [o]) (hP : S rt_P = [r]) (hV : S V = []) (hIX : S rt_IX = []) (hT : S rt_T = [])
    (hr : o + r < (S ROWS).length) :
    NRuns (rt_fetch O V h₀ h₁ h₂) S (S.set V [(S ROWS).getD (o + r) 0]) (6 * (S ROWS).length + 4 * o + 7 * r + 10) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨hOV, hOP, hOX, hOT, hOR⟩, ⟨hVP, hVX, hVT, hVR⟩, -, -, -⟩ := hd
  have x₁ := nruns_dup O rt_IX h₀ S (l := []) (v := o) hO
  rw [hIX, List.nil_append] at x₁
  have x₂ := nruns_dup rt_P V h₁ (S.set rt_IX [o]) (l := []) (v := r) (by rw [Lists.set_ne _ _ (by decide)]; exact hP)
  rw [Lists.set_ne _ _ hVX, hV, List.nil_append] at x₂
  have x₃ := nruns_addTo V rt_IX hVX ((S.set rt_IX [o]).set V [r]) (l := []) (l' := []) (a := r) (b := o)
    (by simp) (by rw [Lists.set_ne _ _ (Ne.symm hVX)]; simp)
  let S₃ := (((S.set rt_IX [o]).set V [r]).set V []).set rt_IX [o + r]
  have x₄ := nruns_peekAt ROWS rt_T rt_IX V (by decide) h₂ hd' S₃
    (by simp only [S₃]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (Ne.symm hVT), Lists.set_ne _ _ (Ne.symm hVT),
      Lists.set_ne _ _ (by decide)]; exact hT) (lc := []) (k := o + r) (by simp [S₃])
    (by simp only [S₃]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (Ne.symm hVR), Lists.set_ne _ _ (Ne.symm hVR),
      Lists.set_ne _ _ (by decide)]; exact hr)
  rw [List.getElem_eq_getD 0] at x₄
  have eR : S₃ ROWS = S ROWS := by
    simp only [S₃]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (Ne.symm hVR), Lists.set_ne _ _ (Ne.symm hVR),
      Lists.set_ne _ _ (by decide)]
  have eV : S₃ V = [] := by simp only [S₃]; rw [Lists.set_ne _ _ hVX, Lists.set_same]
  rw [eR, eV, List.nil_append] at x₄
  have e : (S₃.set rt_IX []).set V [(S ROWS).getD (o + r) 0] = S.set V [(S ROWS).getD (o + r) 0] := by
    simp only [S₃]; rw [← hIX]; lists_eq
  rw [e] at x₄
  exact (x₁.seq (x₂.seq (x₃.seq x₄))).mono (by omega)

theorem rt_getD_le {w : List Nat} {Z : Nat} (hE : ∀ v ∈ w, v ≤ Z) (i : Nat) : w.getD i 0 ≤ Z := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : w[i]? with _ | v
  · simp
  · simp only [Option.getD_some]; exact hE v (List.mem_of_getElem? h)

/-- One position of the order of the segments at `O1` and `O2`, for the position `P`. -/
def rt_leBody : NProg NK :=
  .seq (rt_fetch rt_O1 rt_V1 (by decide) (by decide) (by decide))
    (.seq (rt_fetch rt_O2 rt_V2 (by decide) (by decide) (by decide)) rt_okUpd)

theorem rt_leBody_runs (S : Lists NK) {o₁ o₂ r f Z : Nat} {l w : List Nat} (hO1 : S rt_O1 = [o₁])
    (hO2 : S rt_O2 = [o₂]) (hP : S rt_P = [r]) (hV1 : S rt_V1 = []) (hV2 : S rt_V2 = []) (hIX : S rt_IX = [])
    (hT : S rt_T = []) (hM : S rt_MF = l ++ [f]) (hR : S ROWS = w) (h₁ : o₁ + r < w.length)
    (h₂ : o₂ + r < w.length) (hZ : w.length ≤ Z) (hE : ∀ v ∈ w, v ≤ Z) :
    NRuns rt_leBody S (S.set rt_MF (l ++ [if rt_ok (w.getD (o₁ + r) 0) (w.getD (o₂ + r) 0) then f else 0]))
      (40 * Z + 40) := by
  have x₁ := rt_fetch_runs (O := rt_O1) (V := rt_V1) (h₀ := by decide) (h₁ := by decide) (h₂ := by decide)
    (by decide) (by decide) S hO1 hP hV1 hIX hT (by rw [hR]; exact h₁)
  rw [hR] at x₁
  have x₂ := rt_fetch_runs (O := rt_O2) (V := rt_V2) (h₀ := by decide) (h₁ := by decide) (h₂ := by decide)
    (by decide) (by decide) (S.set rt_V1 [w.getD (o₁ + r) 0]) (by rt_at; exact hO2) (by rt_at; exact hP)
    (by rt_at; exact hV2) (by rt_at; exact hIX) (by rt_at; exact hT) (by rt_at; rw [hR]; exact h₂)
  have eR : (S.set rt_V1 [w.getD (o₁ + r) 0]) ROWS = w := by rt_at; exact hR
  rw [eR] at x₂
  have x₃ := rt_okUpd_runs ((S.set rt_V1 [w.getD (o₁ + r) 0]).set rt_V2 [w.getD (o₂ + r) 0]) (l := l) (f := f)
    (x := w.getD (o₁ + r) 0) (y := w.getD (o₂ + r) 0)
    (by rt_at) (by rt_at) (by rt_at; exact hM)
  have e : ((((S.set rt_V1 [w.getD (o₁ + r) 0]).set rt_V2 [w.getD (o₂ + r) 0]).set rt_V1 []).set rt_V2 []).set rt_MF
      (l ++ [if rt_ok (w.getD (o₁ + r) 0) (w.getD (o₂ + r) 0) then f else 0]) =
      S.set rt_MF (l ++ [if rt_ok (w.getD (o₁ + r) 0) (w.getD (o₂ + r) 0) then f else 0]) := by
    rt_extU [rt_V1, rt_V2, rt_MF] [hV1, hV2]
  rw [e] at x₃
  have hx := rt_getD_le hE (o₁ + r)
  exact (x₁.seq (x₂.seq x₃)).mono (by omega)

/-- **The order of two rows**: `O1`, `O2` hold the starts, `P` the length (all popped); push the order on `MF`. -/
def rt_leC : NProg NK :=
  .seq (npushC rt_MF 1) (.seq (rt_for rt_P rt_leBody) (.seq (.prim (.pop rt_O1)) (.prim (.pop rt_O2))))

theorem rt_leC_runs (S : Lists NK) {o₁ o₂ L Z : Nat} {l w : List Nat} (hO1 : S rt_O1 = [o₁])
    (hO2 : S rt_O2 = [o₂]) (hP : S rt_P = [L]) (hV1 : S rt_V1 = []) (hV2 : S rt_V2 = []) (hIX : S rt_IX = [])
    (hT : S rt_T = []) (hM : S rt_MF = l) (hR : S ROWS = w) (h₁ : o₁ + L ≤ w.length)
    (h₂ : o₂ + L ≤ w.length) (hZ : w.length ≤ Z) (hE : ∀ v ∈ w, v ≤ Z) :
    NRuns rt_leC S ((((S.set rt_P []).set rt_O1 []).set rt_O2 []).set rt_MF
      (l ++ [if leC ((w.drop o₁).take L) ((w.drop o₂).take L) then 1 else 0])) (L * (40 * Z + 42) + 6) := by
  let g : Nat → Bool := fun t => rt_ok (w.getD (o₁ + (L - 1 - t)) 0) (w.getD (o₂ + (L - 1 - t)) 0)
  let F : Nat → Lists NK := fun m =>
    (S.set rt_MF (l ++ [if (List.range m).all g then 1 else 0])).set rt_P [L - m]
  have x₁ := nruns_pushC rt_MF S 1
  rw [hM] at x₁
  have h0 : S.set rt_MF (l ++ [1]) = F 0 := by
    simp only [F, List.range_zero, List.all_nil, if_true, Nat.sub_zero]; rw [← hP]; rt_ext [rt_MF, rt_P]
  rw [h0] at x₁
  have x₂ := rt_for_runs (c := rt_P) (body := rt_leBody) F [] L (40 * Z + 40)
    (fun m _ => by simp [F])
    (fun m hm => by
      have hb := rt_leBody_runs ((F m).set rt_P [L - m - 1]) (o₁ := o₁) (o₂ := o₂) (r := L - m - 1) (Z := Z)
        (l := l) (w := w) (f := if (List.range m).all g then 1 else 0)
        (by simp only [F]; rt_at; exact hO1) (by simp only [F]; rt_at; exact hO2) (by simp only [F]; rt_at)
        (by simp only [F]; rt_at; exact hV1) (by simp only [F]; rt_at; exact hV2) (by simp only [F]; rt_at; exact hIX)
        (by simp only [F]; rt_at; exact hT) (by simp only [F]; rt_at) (by simp only [F]; rt_at; exact hR)
        (by omega) (by omega) hZ hE
      have e : ((F m).set rt_P [L - m - 1]).set rt_MF (l ++ [if rt_ok (w.getD (o₁ + (L - m - 1)) 0)
          (w.getD (o₂ + (L - m - 1)) 0) then (if (List.range m).all g then 1 else 0) else 0]) = F (m + 1) := by
        have hg : ((List.range (m + 1)).all g) = ((List.range m).all g && g m) := by
          rw [List.range_succ, List.all_append]; simp
        have hgm : g m = rt_ok (w.getD (o₁ + (L - m - 1)) 0) (w.getD (o₂ + (L - m - 1)) 0) := by
          simp only [g]; rw [show L - 1 - m = L - m - 1 by omega]
        simp only [F, hg, ← hgm]
        rw [show L - (m + 1) = L - m - 1 by omega]
        cases g m <;> cases (List.range m).all g <;> rt_ext [rt_MF, rt_P]
      rw [e] at hb
      exact hb)
  let S₂ := (F L).set rt_P []
  have x₃ := nruns_pop rt_O1 S₂ (l := []) (v := o₁) (by simp only [S₂, F]; rt_at; exact hO1)
  have x₄ := nruns_pop rt_O2 (S₂.set rt_O1 []) (l := []) (v := o₂) (by simp only [S₂, F]; rt_at; exact hO2)
  have e : (S₂.set rt_O1 []).set rt_O2 [] = (((S.set rt_P []).set rt_O1 []).set rt_O2 []).set rt_MF
      (l ++ [if leC ((w.drop o₁).take L) ((w.drop o₂).take L) then 1 else 0]) := by
    rw [rt_leC_seg w o₁ o₂ L h₁ h₂]
    simp only [S₂, F, g]
    rt_ext [rt_MF, rt_P, rt_O1, rt_O2]
  rw [e] at x₄
  exact (x₁.seq (x₂.seq (x₃.seq x₄))).mono (by rw [show 40 * Z + 40 + 2 = 40 * Z + 42 by omega]; omega)

/-! ## Offsets of rows -/

/-- The stacks of `L` are empty. -/
def rt_FreeOn (L : List (Fin NK)) (S : Lists NK) : Prop := ∀ y ∈ L, S y = []

theorem rt_FreeOn_set {L : List (Fin NK)} {S : Lists NK} (h : rt_FreeOn L S) {x : Fin NK} (hx : x ∉ L)
    (v : List Nat) : rt_FreeOn L (S.set x v) := by
  intro y hy
  have hyx : y ≠ x := fun e => hx (e ▸ hy)
  rw [Lists.set_ne _ _ hyx]
  exact h y hy

theorem rt_FreeOn_get {L : List (Fin NK)} {S : Lists NK} (h : rt_FreeOn L S) {y : Fin NK}
    (hy : y ∈ L := by decide) : S y = [] := h y hy

theorem rt_FreeOn_mono {L L' : List (Fin NK)} {S : Lists NK} (h : rt_FreeOn L S) (hL : ∀ y ∈ L', y ∈ L) :
    rt_FreeOn L' S := fun y hy => h y (hL y hy)

/-- The scratch stacks of a pair of positions. -/
abbrev rt_fr2 : List (Fin NK) := [rt_P, rt_O1, rt_O2, rt_IX, rt_T, rt_V1, rt_V2]
/-- The scratch stacks of an offset. -/
abbrev rt_fr3 : List (Fin NK) := [rt_P, rt_IX, rt_T, rt_V1, rt_V2]

/-- `O` := entry `base` of `PAR` plus `x` times entry `base + 1`, where `fetch` pushes `x` on `V1`. -/
def rt_off (base : Nat) (fetch : NProg NK) (O : Fin NK) (h : rt_T ≠ O) : NProg NK :=
  .seq (rt_get rt_PAR O base (by decide) h) (.seq fetch (.seq (rt_get rt_PAR rt_V2 (base + 1) (by decide) (by decide))
    (.seq (rt_mul rt_V1 rt_V2 O rt_P (by decide)) (.prim (.pop rt_V2)))))

theorem rt_off_runs {base : Nat} {fetch : NProg NK} {O : Fin NK} {h : rt_T ≠ O} (hO : O ∈ [rt_O1, rt_O2])
    (S : Lists NK) {par : List Nat} (hfree : rt_FreeOn rt_fr3 S) (hOf : S O = []) (hpar : S rt_PAR = par)
    (hpl : par.length = 6) (hb : base < 5) {x Tf : Nat}
    (hf : NRuns fetch (S.set O [par.getD base 0]) ((S.set O [par.getD base 0]).set rt_V1 [x]) Tf) :
    NRuns (rt_off base fetch O h) S (S.set O [par.getD base 0 + x * par.getD (base + 1) 0])
      (Tf + x * (3 * par.getD (base + 1) 0 + 7) + 10 * base + 160) := by
  have hO' : O = rt_O1 ∨ O = rt_O2 := by simpa using hO
  have hOX : O ≠ rt_IX := by rcases hO' with rfl | rfl <;> decide
  have hOV1 : O ≠ rt_V1 := by rcases hO' with rfl | rfl <;> decide
  have hOV2 : O ≠ rt_V2 := by rcases hO' with rfl | rfl <;> decide
  have hOP : O ≠ rt_P := by rcases hO' with rfl | rfl <;> decide
  have hOT : O ≠ rt_T := by rcases hO' with rfl | rfl <;> decide
  have hOPar : O ≠ rt_PAR := by rcases hO' with rfl | rfl <;> decide
  have x₁ := rt_get_runs (i := rt_PAR) (o := O) (h₁ := by decide) (h₂ := h)
    (by rcases hO' with rfl | rfl <;> decide) (by decide) hOX S base (rt_FreeOn_get hfree) (rt_FreeOn_get hfree)
    (by rw [hpar, hpl]; omega)
  rw [hOf, List.nil_append, hpar] at x₁
  let S₂ := (S.set O [par.getD base 0]).set rt_V1 [x]
  have x₃ := rt_get_runs (i := rt_PAR) (o := rt_V2) (h₁ := by decide) (h₂ := by decide)
    (by decide) (by decide) (by decide) S₂ (base + 1)
    (by simp only [S₂]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (Ne.symm hOX)]; exact rt_FreeOn_get hfree)
    (by simp only [S₂]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (Ne.symm hOT)]; exact rt_FreeOn_get hfree)
    (by simp only [S₂]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (Ne.symm hOPar), hpar, hpl]; omega)
  have eP : S₂ rt_PAR = par := by
    simp only [S₂]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (Ne.symm hOPar), hpar]
  have eV2 : S₂ rt_V2 = [] := by
    simp only [S₂]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (Ne.symm hOV2)]; exact rt_FreeOn_get hfree
  rw [eP, eV2, List.nil_append, hpl] at x₃
  let S₃ := S₂.set rt_V2 [par.getD (base + 1) 0]
  have x₄ := rt_mul_runs (X := rt_V1) (Y := rt_V2) (A := O) (TM := rt_P) (h := by decide) (by decide)
    (Ne.symm hOV1) (by decide) (Ne.symm hOV2) hOP S₃ (lx := []) (ly := []) (la := []) (x := x)
    (y := par.getD (base + 1) 0) (a := par.getD base 0)
    (by simp only [S₃, S₂]; rw [Lists.set_ne _ _ (by decide), Lists.set_same]; rfl)
    (by simp only [S₃]; rw [Lists.set_same]; rfl)
    (by simp only [S₃, S₂]; rw [Lists.set_ne _ _ hOV2, Lists.set_ne _ _ hOV1, Lists.set_same]; rfl)
    (by simp only [S₃, S₂]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide),
      Lists.set_ne _ _ (Ne.symm hOP)]; exact rt_FreeOn_get hfree)
  have x₅ := nruns_pop rt_V2 ((S₃.set rt_V1 []).set O ([] ++ [par.getD base 0 + x * par.getD (base + 1) 0]))
    (l := []) (v := par.getD (base + 1) 0)
    (by rw [Lists.set_ne _ _ (Ne.symm hOV2), Lists.set_ne _ _ (by decide)]; simp only [S₃, Lists.set_same]; rfl)
  have e : (((S₃.set rt_V1 []).set O ([] ++ [par.getD base 0 + x * par.getD (base + 1) 0])).set rt_V2 []) =
      S.set O [par.getD base 0 + x * par.getD (base + 1) 0] := by
    have h1 := rt_FreeOn_get hfree (y := rt_V1)
    have h2 := rt_FreeOn_get hfree (y := rt_V2)
    simp only [S₃, S₂, List.nil_append]
    funext z
    simp only [Lists.set]
    by_cases hz : z = O
    · subst hz; simp [hOV2]
    · by_cases h1' : z = rt_V1
      · subst h1'; simp [hz, h1]
      · by_cases h2' : z = rt_V2
        · subst h2'; simp [hz, h2]
        · simp [hz, h1', h2']
  rw [e] at x₅
  exact (x₁.seq (hf.seq (x₃.seq (x₄.seq x₅)))).mono (by omega)

/-- `O` := the start of row `i` of the domain type (`i`: the top of `src`). -/
def rt_offA (src O : Fin NK) (h₀ : src ≠ rt_V1) (h : rt_T ≠ O) : NProg NK := rt_off 0 (.prim (.dup src rt_V1 h₀)) O h

/-- `O` := the start of the row of the codomain type named by entry `i` of `D` (`i`: the top of `src`). -/
def rt_offB (src O : Fin NK) (h₀ : src ≠ rt_IX) (h : rt_T ≠ O) : NProg NK :=
  rt_off 3 (rt_getAt rt_D src rt_V1 h₀ (by decide) (by decide)) O h

theorem rt_offA_runs {src O : Fin NK} {h₀ : src ≠ rt_V1} {h : rt_T ≠ O} (hO : O ∈ [rt_O1, rt_O2])
    (hs : src ∈ [rt_I, rt_I2]) (S : Lists NK) {par : List Nat} {i : Nat} (hfree : rt_FreeOn rt_fr3 S) (hOf : S O = [])
    (hpar : S rt_PAR = par) (hpl : par.length = 6) (hsrc : S src = [i]) :
    NRuns (rt_offA src O h₀ h) S (S.set O [par.getD 0 0 + i * par.getD 1 0]) (i * (3 * par.getD 1 0 + 7) + 161) := by
  have hO' : O = rt_O1 ∨ O = rt_O2 := by simpa using hO
  have hs' : src = rt_I ∨ src = rt_I2 := by simpa using hs
  have hf := nruns_dup src rt_V1 h₀ (S.set O [par.getD 0 0]) (l := []) (v := i)
    (by rw [Lists.set_ne _ _ (by rcases hO' with rfl | rfl <;> rcases hs' with rfl | rfl <;> decide)]; exact hsrc)
  rw [Lists.set_ne _ _ (by rcases hO' with rfl | rfl <;> decide), rt_FreeOn_get hfree, List.nil_append] at hf
  have x := rt_off_runs (h := h) hO S hfree hOf hpar hpl (by decide) hf
  rw [show (0 + 1 : Nat) = 1 from rfl] at x
  exact x.mono (by omega)

theorem rt_offB_runs {src O : Fin NK} {h₀ : src ≠ rt_IX} {h : rt_T ≠ O} (hO : O ∈ [rt_O1, rt_O2])
    (hs : src ∈ [rt_I, rt_I2]) (S : Lists NK) {par d : List Nat} {i : Nat} (hfree : rt_FreeOn rt_fr3 S) (hOf : S O = [])
    (hpar : S rt_PAR = par) (hpl : par.length = 6) (hsrc : S src = [i]) (hD : S rt_D = d) (hi : i < d.length) :
    NRuns (rt_offB src O h₀ h) S (S.set O [par.getD 3 0 + d.getD i 0 * par.getD 4 0])
      (6 * d.length + 4 * i + d.getD i 0 * (3 * par.getD 4 0 + 7) + 197) := by
  have hO' : O = rt_O1 ∨ O = rt_O2 := by simpa using hO
  have hs' : src = rt_I ∨ src = rt_I2 := by simpa using hs
  have hf := rt_getAt_runs (i := rt_D) (c := src) (o := rt_V1) (h₀ := h₀) (h₁ := by decide) (h₂ := by decide)
    (by decide) (by decide) (by decide) (S.set O [par.getD 3 0]) (lc := []) (k := i)
    (by rw [Lists.set_ne _ _ (by rcases hO' with rfl | rfl <;> rcases hs' with rfl | rfl <;> decide)]; exact hsrc)
    (by rw [Lists.set_ne _ _ (by rcases hO' with rfl | rfl <;> decide)]; exact rt_FreeOn_get hfree)
    (by rw [Lists.set_ne _ _ (by rcases hO' with rfl | rfl <;> decide)]; exact rt_FreeOn_get hfree)
    (by rw [Lists.set_ne _ _ (by rcases hO' with rfl | rfl <;> decide), hD]; exact hi)
  rw [Lists.set_ne _ _ (by rcases hO' with rfl | rfl <;> decide), Lists.set_ne _ _ (by rcases hO' with rfl | rfl <;> decide),
    rt_FreeOn_get hfree, List.nil_append, hD] at hf
  have x := rt_off_runs (h := h) hO S hfree hOf hpar hpl (by decide) hf
  rw [show (3 + 1 : Nat) = 4 from rfl] at x
  exact x.mono (by omega)

theorem rt_mul_bound {x y Z : Nat} (hx : x ≤ Z) (hy : y ≤ Z) (a b : Nat) : x * (a * y + b) ≤ a * (Z * Z) + b * Z := by
  calc x * (a * y + b) ≤ Z * (a * Z + b) :=
        Nat.mul_le_mul hx (show a * y + b ≤ a * Z + b by have := Nat.mul_le_mul_left a hy; omega)
    _ = a * (Z * Z) + b * Z := by rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm Z b]

/-! ## A pair of positions of the monotonicity check -/

/-- The second half of a pair: the order of the entries at positions `I` and `I2` of the candidate (on `MF`, the
running flag is cleared when they are not in order). -/
def rt_pairB : NProg NK :=
  .seq (rt_offB rt_I rt_O1 (by decide) (by decide)) (.seq (rt_offB rt_I2 rt_O2 (by decide) (by decide))
    (.seq (rt_get rt_PAR rt_P 4 (by decide) (by decide)) (.seq rt_leC
      (.ite rt_MF .pos (.prim (.pop rt_MF)) (.seq (.prim (.pop rt_MF)) (.seq (.prim (.pop rt_MF)) (.prim (.pushZ rt_MF))))))))

/-- A pair of positions `I`, `I2`: when the rows of the domain are in order, check the entries are. -/
def rt_pair : NProg NK :=
  .seq (rt_offA rt_I rt_O1 (by decide) (by decide)) (.seq (rt_offA rt_I2 rt_O2 (by decide) (by decide))
    (.seq (rt_get rt_PAR rt_P 1 (by decide) (by decide)) (.seq rt_leC
      (.ite rt_MF .pos (.seq (.prim (.pop rt_MF)) rt_pairB) (.prim (.pop rt_MF))))))

/-- The rows read for the check: a segment of `w`. -/
def rt_segOf (w : List Nat) (o len i : Nat) : List Nat := (w.drop (o + i * len)).take len

theorem rt_pairB_runs (S : Lists NK) {par d w l : List Nat} {i i' f Z : Nat} (hfree : rt_FreeOn rt_fr2 S)
    (hpar : S rt_PAR = par) (hpl : par.length = 6) (hI : S rt_I = [i]) (hI2 : S rt_I2 = [i']) (hD : S rt_D = d)
    (hR : S ROWS = w) (hM : S rt_MF = l ++ [f]) (hi : i < d.length) (hi' : i' < d.length)
    (hB : par.getD 3 0 + d.getD i 0 * par.getD 4 0 + par.getD 4 0 ≤ w.length)
    (hB' : par.getD 3 0 + d.getD i' 0 * par.getD 4 0 + par.getD 4 0 ≤ w.length)
    (hwZ : w.length ≤ Z) (hE : ∀ v ∈ w, v ≤ Z) (hb1 : par.getD 4 0 ≤ Z) (hdZ : d.length ≤ Z) (hdE : ∀ v ∈ d, v ≤ Z) :
    NRuns rt_pairB S (S.set rt_MF (l ++ [if leC (rt_segOf w (par.getD 3 0) (par.getD 4 0) (d.getD i 0))
      (rt_segOf w (par.getD 3 0) (par.getD 4 0) (d.getD i' 0)) then f else 0])) (46 * (Z * Z) + 76 * Z + 467) := by
  have hfr3 : rt_FreeOn rt_fr3 S := rt_FreeOn_mono hfree (by decide)
  have x₁ := rt_offB_runs (src := rt_I) (O := rt_O1) (h₀ := by decide) (h := by decide) (by decide) (by decide) S hfr3
    (rt_FreeOn_get hfree) hpar hpl hI hD hi
  let S₁ := S.set rt_O1 [par.getD 3 0 + d.getD i 0 * par.getD 4 0]
  have x₂ := rt_offB_runs (src := rt_I2) (O := rt_O2) (h₀ := by decide) (h := by decide) (by decide) (by decide) S₁
    (rt_FreeOn_set hfr3 (by decide) _) (by simp only [S₁]; rt_at; exact rt_FreeOn_get hfree)
    (by simp only [S₁]; rt_at; exact hpar) hpl (by simp only [S₁]; rt_at; exact hI2) (by simp only [S₁]; rt_at; exact hD) hi'
  let S₂ := S₁.set rt_O2 [par.getD 3 0 + d.getD i' 0 * par.getD 4 0]
  have x₃ := rt_get_runs (i := rt_PAR) (o := rt_P) (h₁ := by decide) (h₂ := by decide) (by decide) (by decide)
    (by decide) S₂ 4 (by simp only [S₂, S₁]; rt_at; exact rt_FreeOn_get hfree)
    (by simp only [S₂, S₁]; rt_at; exact rt_FreeOn_get hfree) (by simp only [S₂, S₁]; rt_at; rw [hpar, hpl]; omega)
  have eP : S₂ rt_PAR = par := by simp only [S₂, S₁]; rt_at; exact hpar
  have eP2 : S₂ rt_P = [] := by simp only [S₂, S₁]; rt_at; exact rt_FreeOn_get hfree
  rw [eP, eP2, List.nil_append] at x₃
  let S₃ := S₂.set rt_P [par.getD 4 0]
  have x₄ := rt_leC_runs S₃ (o₁ := par.getD 3 0 + d.getD i 0 * par.getD 4 0)
    (o₂ := par.getD 3 0 + d.getD i' 0 * par.getD 4 0) (L := par.getD 4 0) (Z := Z) (l := l ++ [f]) (w := w)
    (by simp only [S₃, S₂, S₁]; rt_at) (by simp only [S₃, S₂, S₁]; rt_at) (by simp only [S₃]; rt_at)
    (by simp only [S₃, S₂, S₁]; rt_at; exact rt_FreeOn_get hfree)
    (by simp only [S₃, S₂, S₁]; rt_at; exact rt_FreeOn_get hfree)
    (by simp only [S₃, S₂, S₁]; rt_at; exact rt_FreeOn_get hfree)
    (by simp only [S₃, S₂, S₁]; rt_at; exact rt_FreeOn_get hfree)
    (by simp only [S₃, S₂, S₁]; rt_at; exact hM) (by simp only [S₃, S₂, S₁]; rt_at; exact hR)
    (by omega) (by omega) hwZ hE
  have e₄ : ∀ v, (((S₃.set rt_P []).set rt_O1 []).set rt_O2 []).set rt_MF (l ++ [f] ++ [v]) = S.set rt_MF (l ++ [f, v]) := by
    intro v
    have h1 : S rt_P = [] := rt_FreeOn_get hfree
    have h2 : S rt_O1 = [] := rt_FreeOn_get hfree
    have h3 : S rt_O2 = [] := rt_FreeOn_get hfree
    simp only [S₃, S₂, S₁]
    rt_extU [rt_P, rt_O1, rt_O2, rt_MF] [h1, h2, h3]
  rw [e₄] at x₄
  have hd₁ : d.getD i 0 ≤ Z := rt_getD_le hdE i
  have hd₂ : d.getD i' 0 ≤ Z := rt_getD_le hdE i'
  have c₁ := rt_mul_bound hd₁ hb1 3 7
  have c₂ := rt_mul_bound hd₂ hb1 3 7
  have c₃ : par.getD 4 0 * (40 * Z + 42) ≤ 40 * (Z * Z) + 42 * Z := rt_mul_bound hb1 (Nat.le_refl Z) 40 42
  by_cases hle : leC (rt_segOf w (par.getD 3 0) (par.getD 4 0) (d.getD i 0))
      (rt_segOf w (par.getD 3 0) (par.getD 4 0) (d.getD i' 0)) = true
  · have hle' := hle
    simp only [rt_segOf] at hle'
    rw [if_pos hle'] at x₄
    have p₁ := nruns_pop rt_MF (S.set rt_MF (l ++ [f, 1])) (l := l ++ [f]) (v := 1) (by simp)
    rw [Lists.set_set_u, ← hM, Lists.set_get_self] at p₁
    rw [if_pos hle, ← hM, Lists.set_get_self]
    exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq (p₁.iteT (by simp [NTest.eval])))))).mono (by omega)
  · have hle' := hle
    simp only [rt_segOf] at hle'
    rw [if_neg hle'] at x₄
    have p₁ := nruns_pop rt_MF (S.set rt_MF (l ++ [f, 0])) (l := l ++ [f]) (v := 0) (by simp)
    have p₂ := nruns_pop rt_MF ((S.set rt_MF (l ++ [f, 0])).set rt_MF (l ++ [f])) (l := l) (v := f) (by simp)
    have p₃ := nruns_pushZ rt_MF (((S.set rt_MF (l ++ [f, 0])).set rt_MF (l ++ [f])).set rt_MF l)
    simp only [Lists.set_set_u, Lists.set_same] at p₁ p₂ p₃
    rw [if_neg hle]
    exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq ((p₁.seq (p₂.seq p₃)).iteF (by simp [NTest.eval])))))).mono (by omega)

theorem rt_pair_runs (S : Lists NK) {par d w l : List Nat} {i i' f Z : Nat} (hfree : rt_FreeOn rt_fr2 S)
    (hpar : S rt_PAR = par) (hpl : par.length = 6) (hI : S rt_I = [i]) (hI2 : S rt_I2 = [i']) (hD : S rt_D = d)
    (hR : S ROWS = w) (hM : S rt_MF = l ++ [f]) (hi : i < d.length) (hi' : i' < d.length)
    (hA : par.getD 0 0 + i * par.getD 1 0 + par.getD 1 0 ≤ w.length)
    (hA' : par.getD 0 0 + i' * par.getD 1 0 + par.getD 1 0 ≤ w.length)
    (hB : par.getD 3 0 + d.getD i 0 * par.getD 4 0 + par.getD 4 0 ≤ w.length)
    (hB' : par.getD 3 0 + d.getD i' 0 * par.getD 4 0 + par.getD 4 0 ≤ w.length)
    (hwZ : w.length ≤ Z) (hE : ∀ v ∈ w, v ≤ Z) (ha1 : par.getD 1 0 ≤ Z) (hb1 : par.getD 4 0 ≤ Z)
    (hiZ : i ≤ Z) (hiZ' : i' ≤ Z) (hdZ : d.length ≤ Z) (hdE : ∀ v ∈ d, v ≤ Z) :
    NRuns rt_pair S (S.set rt_MF (l ++ [if (!leC (rt_segOf w (par.getD 0 0) (par.getD 1 0) i)
        (rt_segOf w (par.getD 0 0) (par.getD 1 0) i') ||
      leC (rt_segOf w (par.getD 3 0) (par.getD 4 0) (d.getD i 0))
        (rt_segOf w (par.getD 3 0) (par.getD 4 0) (d.getD i' 0))) then f else 0])) (92 * (Z * Z) + 132 * Z + 845) := by
  have hfr3 : rt_FreeOn rt_fr3 S := rt_FreeOn_mono hfree (by decide)
  have x₁ := rt_offA_runs (src := rt_I) (O := rt_O1) (h₀ := by decide) (h := by decide) (by decide) (by decide) S hfr3
    (rt_FreeOn_get hfree) hpar hpl hI
  let S₁ := S.set rt_O1 [par.getD 0 0 + i * par.getD 1 0]
  have x₂ := rt_offA_runs (src := rt_I2) (O := rt_O2) (h₀ := by decide) (h := by decide) (by decide) (by decide) S₁
    (rt_FreeOn_set hfr3 (by decide) _) (by simp only [S₁]; rt_at; exact rt_FreeOn_get hfree)
    (by simp only [S₁]; rt_at; exact hpar) hpl (by simp only [S₁]; rt_at; exact hI2)
  let S₂ := S₁.set rt_O2 [par.getD 0 0 + i' * par.getD 1 0]
  have x₃ := rt_get_runs (i := rt_PAR) (o := rt_P) (h₁ := by decide) (h₂ := by decide) (by decide) (by decide)
    (by decide) S₂ 1 (by simp only [S₂, S₁]; rt_at; exact rt_FreeOn_get hfree)
    (by simp only [S₂, S₁]; rt_at; exact rt_FreeOn_get hfree) (by simp only [S₂, S₁]; rt_at; rw [hpar, hpl]; omega)
  have eP : S₂ rt_PAR = par := by simp only [S₂, S₁]; rt_at; exact hpar
  have eP2 : S₂ rt_P = [] := by simp only [S₂, S₁]; rt_at; exact rt_FreeOn_get hfree
  rw [eP, eP2, List.nil_append] at x₃
  let S₃ := S₂.set rt_P [par.getD 1 0]
  have x₄ := rt_leC_runs S₃ (o₁ := par.getD 0 0 + i * par.getD 1 0)
    (o₂ := par.getD 0 0 + i' * par.getD 1 0) (L := par.getD 1 0) (Z := Z) (l := l ++ [f]) (w := w)
    (by simp only [S₃, S₂, S₁]; rt_at) (by simp only [S₃, S₂, S₁]; rt_at) (by simp only [S₃]; rt_at)
    (by simp only [S₃, S₂, S₁]; rt_at; exact rt_FreeOn_get hfree)
    (by simp only [S₃, S₂, S₁]; rt_at; exact rt_FreeOn_get hfree)
    (by simp only [S₃, S₂, S₁]; rt_at; exact rt_FreeOn_get hfree)
    (by simp only [S₃, S₂, S₁]; rt_at; exact rt_FreeOn_get hfree)
    (by simp only [S₃, S₂, S₁]; rt_at; exact hM) (by simp only [S₃, S₂, S₁]; rt_at; exact hR)
    (by omega) (by omega) hwZ hE
  have e₄ : ∀ v, (((S₃.set rt_P []).set rt_O1 []).set rt_O2 []).set rt_MF (l ++ [f] ++ [v]) = S.set rt_MF (l ++ [f, v]) := by
    intro v
    have h1 : S rt_P = [] := rt_FreeOn_get hfree
    have h2 : S rt_O1 = [] := rt_FreeOn_get hfree
    have h3 : S rt_O2 = [] := rt_FreeOn_get hfree
    simp only [S₃, S₂, S₁]
    rt_extU [rt_P, rt_O1, rt_O2, rt_MF] [h1, h2, h3]
  rw [e₄] at x₄
  have c₁ := rt_mul_bound hiZ ha1 3 7
  have c₂ := rt_mul_bound hiZ' ha1 3 7
  have c₃ : par.getD 1 0 * (40 * Z + 42) ≤ 40 * (Z * Z) + 42 * Z := rt_mul_bound ha1 (Nat.le_refl Z) 40 42
  by_cases hle : leC (rt_segOf w (par.getD 0 0) (par.getD 1 0) i) (rt_segOf w (par.getD 0 0) (par.getD 1 0) i') = true
  · have hle' := hle
    simp only [rt_segOf] at hle'
    rw [if_pos hle'] at x₄
    have p₁ := nruns_pop rt_MF (S.set rt_MF (l ++ [f, 1])) (l := l ++ [f]) (v := 1) (by simp)
    rw [Lists.set_set_u, ← hM, Lists.set_get_self] at p₁
    have p₂ := rt_pairB_runs S hfree hpar hpl hI hI2 hD hR hM hi hi' hB hB' hwZ hE hb1 hdZ hdE
    rw [hle]
    simp only [Bool.not_true, Bool.false_or]
    exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq ((p₁.seq p₂).iteT (by simp [NTest.eval])))))).mono (by omega)
  · have hle' := hle
    simp only [rt_segOf] at hle'
    rw [if_neg hle'] at x₄
    have p₁ := nruns_pop rt_MF (S.set rt_MF (l ++ [f, 0])) (l := l ++ [f]) (v := 0) (by simp)
    rw [Lists.set_set_u] at p₁
    simp only [Bool.not_eq_true] at hle
    rw [hle]
    simp only [Bool.not_false, Bool.true_or, if_true]
    exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq (p₁.iteF (by simp [NTest.eval])))))).mono (by omega)

theorem rt_for_cost' {n T Z : Nat} (hn : n ≤ Z) : n * (T + 2) + 2 ≤ Z * T + 2 * Z + 2 := by
  have h₁ : n * (T + 2) ≤ Z * (T + 2) := Nat.mul_le_mul_right _ hn
  have h₂ : Z * (T + 2) = Z * T + 2 * Z := by rw [Nat.mul_add, Nat.mul_comm Z 2]
  omega

theorem rt_dist3 (Z a b c W V : Nat) : Z * (a * W + b * V + c) = a * (Z * W) + b * (Z * V) + c * Z := by
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_left_comm Z a, Nat.mul_left_comm Z b, Nat.mul_comm Z c]

theorem rt_dist4 (Z a b c e W V U : Nat) :
    Z * (a * W + b * V + c * U + e) = a * (Z * W) + b * (Z * V) + c * (Z * U) + e * Z := by
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_left_comm Z a, Nat.mul_left_comm Z b, Nat.mul_left_comm Z c,
    Nat.mul_comm Z e]

theorem rt_mono_cost {n Z : Nat} (hn : n ≤ Z) :
    1 + 1 + (6 * 6 + 5 * 2 + 7 + (n * (53 + (n * (92 * (Z * Z) + 132 * Z + 845 + 2) + 2) + 2) + 2)) ≤
      92 * (Z * (Z * (Z * Z))) + 132 * (Z * (Z * Z)) + 847 * (Z * Z) + 57 * Z + 57 := by
  rw [show 92 * (Z * Z) + 132 * Z + 845 + 2 = 92 * (Z * Z) + 132 * Z + 847 by omega]
  have h₀ := Nat.mul_le_mul_right (92 * (Z * Z) + 132 * Z + 847) hn
  rw [rt_dist3 Z] at h₀
  generalize n * (92 * (Z * Z) + 132 * Z + 847) = A at *
  have h₁ := Nat.mul_le_mul hn (show 53 + (A + 2) + 2 ≤ 92 * (Z * (Z * Z)) + 132 * (Z * Z) + 847 * Z + 57 by omega)
  rw [rt_dist4 Z] at h₁
  generalize n * (53 + (A + 2) + 2) = B at *
  generalize Z * (Z * (Z * Z)) = Z4 at *
  generalize Z * (Z * Z) = Z3 at *
  generalize Z * Z = Z2 at *
  omega

/-! ## The monotonicity check of a candidate -/

/-- Whether a candidate is monotone, from the rows in `ROWS` and the digits in `D`; push it on `MF`. -/
def rt_mono : NProg NK :=
  .seq (npushC rt_MF 1) (.seq (rt_get rt_PAR rt_I 2 (by decide) (by decide))
    (rt_for rt_I (.seq (rt_get rt_PAR rt_I2 2 (by decide) (by decide)) (rt_for rt_I2 rt_pair))))

/-- The scratch stacks of a candidate. -/
abbrev rt_frC : List (Fin NK) := [rt_I, rt_I2, rt_P, rt_O1, rt_O2, rt_IX, rt_T, rt_V1, rt_V2]

/-- The check at a pair of positions, on the rows of `w`. -/
def rt_pairOK (w par d : List Nat) (i i' : Nat) : Bool :=
  !leC (rt_segOf w (par.getD 0 0) (par.getD 1 0) i) (rt_segOf w (par.getD 0 0) (par.getD 1 0) i') ||
    leC (rt_segOf w (par.getD 3 0) (par.getD 4 0) (d.getD i 0)) (rt_segOf w (par.getD 3 0) (par.getD 4 0) (d.getD i' 0))

/-- Whether the candidate in `D` is monotone. -/
def rt_monoOK (w par d : List Nat) : Bool :=
  (List.range d.length).all (fun i => (List.range d.length).all (fun i' => rt_pairOK w par d i i'))

theorem rt_mono_runs (S : Lists NK) {par d w l : List Nat} {Z : Nat} (hfree : rt_FreeOn rt_frC S)
    (hpar : S rt_PAR = par) (hpl : par.length = 6) (hD : S rt_D = d) (hR : S ROWS = w) (hM : S rt_MF = l)
    (hdl : d.length = par.getD 2 0)
    (hA : ∀ i, i < d.length → par.getD 0 0 + i * par.getD 1 0 + par.getD 1 0 ≤ w.length)
    (hB : ∀ i, i < d.length → par.getD 3 0 + d.getD i 0 * par.getD 4 0 + par.getD 4 0 ≤ w.length)
    (hwZ : w.length ≤ Z) (hE : ∀ v ∈ w, v ≤ Z) (ha1 : par.getD 1 0 ≤ Z) (hb1 : par.getD 4 0 ≤ Z)
    (hdZ : d.length ≤ Z) (hdE : ∀ v ∈ d, v ≤ Z) :
    NRuns rt_mono S (S.set rt_MF (l ++ [if rt_monoOK w par d then 1 else 0]))
      (92 * (Z * (Z * (Z * Z))) + 132 * (Z * (Z * Z)) + 847 * (Z * Z) + 57 * Z + 57) := by
  let rowAll : Nat → Bool := fun i => (List.range d.length).all (fun i' => rt_pairOK w par d i i')
  let accO : Nat → Bool := fun m => (List.range m).all (fun t => rowAll (d.length - 1 - t))
  let F : Nat → Lists NK := fun m => (S.set rt_MF (l ++ [if accO m then 1 else 0])).set rt_I [d.length - m]
  have x₁ := nruns_pushC rt_MF S 1
  rw [hM] at x₁
  have x₂ := rt_get_runs (i := rt_PAR) (o := rt_I) (h₁ := by decide) (h₂ := by decide) (by decide) (by decide)
    (by decide) (S.set rt_MF (l ++ [1])) 2 (by rt_at; exact rt_FreeOn_get hfree) (by rt_at; exact rt_FreeOn_get hfree)
    (by rt_at; rw [hpar, hpl]; omega)
  have e₂ : (S.set rt_MF (l ++ [1])).set rt_I ((S.set rt_MF (l ++ [1])) rt_I ++ [((S.set rt_MF (l ++ [1])) rt_PAR).getD 2 0])
      = F 0 := by
    have h1 : S rt_I = [] := rt_FreeOn_get hfree
    simp only [F, accO, List.range_zero, List.all_nil, if_true, Nat.sub_zero]
    rt_extU [rt_MF, rt_I] [h1, hpar, hdl.symm]
  rw [e₂] at x₂
  have eG : (S.set rt_MF (l ++ [1])) rt_PAR = par := by rt_at; exact hpar
  rw [eG, hpl] at x₂
  have hpc : 92 * (Z * Z) + 132 * Z + 845 ≤ 92 * (Z * Z) + 132 * Z + 845 := Nat.le_refl _
  have x₃ := rt_for_runs (c := rt_I) (body := .seq (rt_get rt_PAR rt_I2 2 (by decide) (by decide)) (rt_for rt_I2 rt_pair))
    F [] d.length (53 + (d.length * (92 * (Z * Z) + 132 * Z + 845 + 2) + 2))
    (fun m _ => by simp only [F]; rt_at)
    (fun m hm => by
      let i := d.length - m - 1
      let G := (F m).set rt_I [i]
      let accI : Nat → Bool := fun m' => (List.range m').all (fun t => rt_pairOK w par d i (d.length - 1 - t))
      let H : Nat → Lists NK := fun m' =>
        (G.set rt_MF (l ++ [if (accO m && accI m') then 1 else 0])).set rt_I2 [d.length - m']
      have y₁ := rt_get_runs (i := rt_PAR) (o := rt_I2) (h₁ := by decide) (h₂ := by decide) (by decide) (by decide)
        (by decide) G 2 (by simp only [G, F]; rt_at; exact rt_FreeOn_get hfree)
        (by simp only [G, F]; rt_at; exact rt_FreeOn_get hfree) (by simp only [G, F]; rt_at; rw [hpar, hpl]; omega)
      have e₁ : G.set rt_I2 (G rt_I2 ++ [(G rt_PAR).getD 2 0]) = H 0 := by
        have h1 : S rt_I2 = [] := rt_FreeOn_get hfree
        simp only [H, G, F, accI, List.range_zero, List.all_nil, Bool.and_true, Nat.sub_zero]
        rt_extU [rt_MF, rt_I, rt_I2] [h1, hpar, hdl.symm]
      rw [e₁] at y₁
      have eG : G rt_PAR = par := by simp only [G, F]; rt_at; exact hpar
      rw [eG, hpl] at y₁
      have y₂ := rt_for_runs (c := rt_I2) (body := rt_pair) H [] d.length (92 * (Z * Z) + 132 * Z + 845)
        (fun m' _ => by simp only [H]; rt_at)
        (fun m' hm' => by
          have hp := rt_pair_runs ((H m').set rt_I2 [d.length - m' - 1]) (par := par) (d := d) (w := w)
            (l := l) (i := i) (i' := d.length - m' - 1) (f := if (accO m && accI m') then 1 else 0) (Z := Z)
            (by
              intro y hy
              have hy' : y ∈ rt_frC := by revert hy; decide +revert
              simp only [H, G, F]
              have : y ≠ rt_I2 ∧ y ≠ rt_I ∧ y ≠ rt_MF := by revert hy; decide +revert
              rw [Lists.set_ne _ _ this.1, Lists.set_ne _ _ this.1, Lists.set_ne _ _ this.2.2,
                Lists.set_ne _ _ this.2.1, Lists.set_ne _ _ this.2.1, Lists.set_ne _ _ this.2.2]
              exact hfree y hy')
            (by simp only [H, G, F]; rt_at; exact hpar) hpl (by simp only [H, G, F]; rt_at) (by simp only [H]; rt_at)
            (by simp only [H, G, F]; rt_at; exact hD) (by simp only [H, G, F]; rt_at; exact hR)
            (by simp only [H, G]; rt_at) (by omega) (by omega) (hA i (by omega)) (hA _ (by omega))
            (hB i (by omega)) (hB _ (by omega)) hwZ hE ha1 hb1 (by omega) (by omega) hdZ hdE
          have e : ((H m').set rt_I2 [d.length - m' - 1]).set rt_MF (l ++ [if rt_pairOK w par d i (d.length - m' - 1) then
              (if (accO m && accI m') then 1 else 0) else 0]) = H (m' + 1) := by
            have hg : accI (m' + 1) = (accI m' && rt_pairOK w par d i (d.length - m' - 1)) := by
              simp only [accI]; rw [List.range_succ, List.all_append]
              simp only [List.all_cons, List.all_nil, Bool.and_true]
              rw [show d.length - 1 - m' = d.length - m' - 1 by omega]
            simp only [H, hg, show d.length - (m' + 1) = d.length - m' - 1 by omega]
            cases rt_pairOK w par d i (d.length - m' - 1) <;> cases accI m' <;> cases accO m <;> rt_ext [rt_MF, rt_I2]
          unfold rt_pairOK at e
          rw [e] at hp
          exact hp)
      have e₂ : (H d.length).set rt_I2 [] = F (m + 1) := by
        have h1 : S rt_I2 = [] := rt_FreeOn_get hfree
        have hg : accO (m + 1) = (accO m && accI d.length) := by
          simp only [accO, accI]; rw [List.range_succ, List.all_append]
          simp only [List.all_cons, List.all_nil, Bool.and_true]
          rw [show d.length - 1 - m = i by omega]
          congr 1
          exact (rt_all_rev d.length _).symm
        simp only [H, G, F, hg, show d.length - (m + 1) = i by omega, Nat.sub_self]
        rt_extU [rt_MF, rt_I, rt_I2] [h1]
      rw [e₂] at y₂
      exact (y₁.seq y₂).mono (by omega))
  have e₃ : (F d.length).set rt_I [] = S.set rt_MF (l ++ [if rt_monoOK w par d then 1 else 0]) := by
    have h1 : S rt_I = [] := rt_FreeOn_get hfree
    have hacc : accO d.length = rt_monoOK w par d := rt_all_rev d.length rowAll
    simp only [F, hacc]
    rt_extU [rt_MF, rt_I] [h1]
  rw [e₃] at x₃
  have c := rt_mono_cost hdZ
  exact (x₁.seq (x₂.seq x₃)).mono (by omega)

/-! ## Writing rows -/

/-- Copy `L` (popped from `P`) entries of `src` from position `o` (popped from `O1`) onto `ROWS`. -/
def rt_copy (src : Fin NK) (h₁ : src ≠ rt_T) : NProg NK :=
  .seq (rt_for rt_P (.seq (rt_getAt src rt_O1 rt_V1 (by decide) h₁ (by decide))
    (.seq (nmv rt_V1 ROWS (by decide)) (.prim (.inc rt_O1))))) (.prim (.pop rt_O1))

theorem rt_take_succ_getD (seg : List Nat) {m : Nat} (hm : m < seg.length) :
    seg.take (m + 1) = seg.take m ++ [seg.getD m 0] := by
  rw [List.take_succ_eq_append_getElem hm, List.getElem_eq_getD 0]

theorem rt_copy_runs {src : Fin NK} {h₁ : src ≠ rt_T} (hs : src ∉ [rt_P, rt_O1, rt_IX, rt_T, rt_V1])
    (S : Lists NK) {w seg : List Nat} {o L B : Nat} (hP : S rt_P = [L]) (hO : S rt_O1 = [o]) (hIX : S rt_IX = [])
    (hT : S rt_T = []) (hV : S rt_V1 = []) (hR : S ROWS = w) (hL : seg.length = L)
    (hread : ∀ m, m < L → o + m < ((S.set ROWS (w ++ seg.take m)) src).length ∧
      ((S.set ROWS (w ++ seg.take m)) src).getD (o + m) 0 = seg.getD m 0)
    (hB : ∀ m, m < L → ((S.set ROWS (w ++ seg.take m)) src).length ≤ B) (hoB : o + L ≤ B) :
    NRuns (rt_copy src h₁) S (((S.set ROWS (w ++ seg)).set rt_P []).set rt_O1 []) (L * (10 * B + 12) + 3) := by
  have hsP : src ≠ rt_P := by intro e; exact hs (by simp [e])
  have hsO : src ≠ rt_O1 := by intro e; exact hs (by simp [e])
  have hsX : src ≠ rt_IX := by intro e; exact hs (by simp [e])
  have hsV : src ≠ rt_V1 := by intro e; exact hs (by simp [e])
  let F : Nat → Lists NK := fun m => ((S.set ROWS (w ++ seg.take m)).set rt_O1 [o + m]).set rt_P [L - m]
  have h0 : F 0 = S := by
    simp only [F, List.take_zero, List.append_nil, Nat.add_zero, Nat.sub_zero]
    rt_extU [ROWS, rt_O1, rt_P] [hR, hO, hP]
  have x₁ := rt_for_runs (c := rt_P)
    (body := .seq (rt_getAt src rt_O1 rt_V1 (by decide) h₁ (by decide)) (.seq (nmv rt_V1 ROWS (by decide))
      (.prim (.inc rt_O1)))) F [] L (10 * B + 10)
    (fun m _ => by simp only [F]; rt_at)
    (fun m hm => by
      let G := (F m).set rt_P [L - m - 1]
      have hGs : G src = (S.set ROWS (w ++ seg.take m)) src := by
        simp only [G, F]; rw [Lists.set_ne _ _ hsP, Lists.set_ne _ _ hsP, Lists.set_ne _ _ hsO]
      have y₁ := rt_getAt_runs (i := src) (c := rt_O1) (o := rt_V1) (h₀ := by decide) (h₁ := h₁) (h₂ := by decide)
        (List.nodup_cons.2 ⟨by simp [h₁, hsX, hsV], by decide⟩)
        hsX (by decide) G (lc := []) (k := o + m)
        (by simp only [G, F]; rt_at) (by simp only [G, F]; rt_at; exact hIX) (by simp only [G, F]; rt_at; exact hT)
        (by rw [hGs]; exact (hread m hm).1)
      rw [hGs, (hread m hm).2] at y₁
      have hGV : G rt_V1 = [] := by simp only [G, F]; rt_at; exact hV
      rw [hGV, List.nil_append] at y₁
      have y₂ := nruns_mv rt_V1 ROWS (by decide) (G.set rt_V1 [seg.getD m 0]) (l := []) (v := seg.getD m 0)
        (by rt_at)
      have y₃ := nruns_inc rt_O1 (((G.set rt_V1 [seg.getD m 0]).set ROWS ((G.set rt_V1 [seg.getD m 0]) ROWS ++
        [seg.getD m 0])).set rt_V1 []) (l := []) (v := o + m) (by simp only [G, F]; rt_at)
      have e : ((((G.set rt_V1 [seg.getD m 0]).set ROWS ((G.set rt_V1 [seg.getD m 0]) ROWS ++ [seg.getD m 0])).set
          rt_V1 []).set rt_O1 ([] ++ [o + m + 1])) = F (m + 1) := by
        have hk := rt_take_succ_getD seg (m := m) (by omega)
        simp only [G, F, show L - (m + 1) = L - m - 1 by omega, hk, ← List.append_assoc, ← Nat.add_assoc]
        rt_extU [rt_V1, ROWS, rt_O1, rt_P] [hV]
      rw [e] at y₃
      have hl := hB m hm
      exact (y₁.seq (y₂.seq y₃)).mono (by omega))
  rw [h0] at x₁
  have x₂ := nruns_pop rt_O1 ((F L).set rt_P []) (l := []) (v := o + L) (by simp only [F]; rt_at)
  have e : (((F L).set rt_P []).set rt_O1 []) = ((S.set ROWS (w ++ seg)).set rt_P []).set rt_O1 [] := by
    simp only [F, Nat.sub_self, ← hL, List.take_length]
    rt_ext [ROWS, rt_O1, rt_P]
  rw [e] at x₂
  rw [show 10 * B + 10 + 2 = 10 * B + 12 by omega] at x₁
  exact (x₁.seq x₂).mono (by omega)

theorem rt_segOf_length {w : List Nat} {o len i : Nat} (h : o + i * len + len ≤ w.length) :
    (rt_segOf w o len i).length = len := by
  simp only [rt_segOf, List.length_take, List.length_drop]; omega

theorem rt_segOf_getD {w : List Nat} {o len i p : Nat} (h : o + i * len + len ≤ w.length) (hp : p < len) (e : List Nat) :
    (w ++ e).getD (o + i * len + p) 0 = (rt_segOf w o len i).getD p 0 := by
  have h₁ : o + i * len + p < w.length := by omega
  simp [rt_segOf, List.getD_eq_getElem?_getD, List.getElem?_append_left h₁, hp, List.getElem?_drop]

theorem rt_flatMap_length (f : Nat → List Nat) (len : Nat) (hf : ∀ i, (f i).length = len) :
    ∀ m, ((List.range m).flatMap f).length = m * len
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, rt_flatMap_length f len hf m]
    simp [hf, Nat.succ_mul]

/-- Append the candidate in `D` (the rows of the codomain it names, in order) to `ROWS`, and count it. -/
def rt_emitA : NProg NK :=
  .seq (.prim (.pushZ rt_I2)) (.seq (rt_get rt_PAR rt_I 2 (by decide) (by decide))
    (.seq (rt_for rt_I (.seq (rt_offB rt_I2 rt_O1 (by decide) (by decide))
      (.seq (rt_get rt_PAR rt_P 4 (by decide) (by decide)) (.seq (rt_copy ROWS (by decide)) (.prim (.inc rt_I2))))))
    (.seq (.prim (.pop rt_I2)) (.prim (.inc CNT)))))

/-- The rows written for a candidate: the rows of the codomain named by its digits. -/
def rt_out (w par d : List Nat) : List Nat :=
  (List.range d.length).flatMap (fun i => rt_segOf w (par.getD 3 0) (par.getD 4 0) (d.getD i 0))

theorem rt_emitA_cost {n Z : Nat} (hn : n ≤ Z) {T : Nat} (hT : T ≤ 13 * (Z * Z) + 29 * Z + 264) :
    1 + (6 * 6 + 5 * 2 + 7 + (n * (T + 2) + 2 + (1 + 1))) ≤ 13 * (Z * (Z * Z)) + 29 * (Z * Z) + 266 * Z + 58 := by
  have h₁ := Nat.mul_le_mul hn (show T + 2 ≤ 13 * (Z * Z) + 29 * Z + 266 by omega)
  rw [rt_dist3 Z] at h₁
  generalize n * (T + 2) = A at *
  generalize Z * (Z * Z) = Z3 at *
  generalize Z * Z = Z2 at *
  omega

theorem rt_emitA_runs (S : Lists NK) {par d w lc : List Nat} {c Z : Nat} (hfree : rt_FreeOn rt_frC S)
    (hpar : S rt_PAR = par) (hpl : par.length = 6) (hD : S rt_D = d) (hR : S ROWS = w) (hC : S CNT = lc ++ [c])
    (hdl : d.length = par.getD 2 0)
    (hB : ∀ i, i < d.length → (par.getD 3 0) + d.getD i 0 * (par.getD 4 0) + (par.getD 4 0) ≤ w.length)
    (hwZ : (w ++ rt_out w par d).length ≤ Z) (hb1 : (par.getD 4 0) ≤ Z) (hdZ : d.length ≤ Z) (hdE : ∀ v ∈ d, v ≤ Z) :
    NRuns rt_emitA S ((S.set ROWS (w ++ rt_out w par d)).set CNT (lc ++ [c + 1]))
      (13 * (Z * (Z * Z)) + 29 * (Z * Z) + 266 * Z + 58) := by
  let sg : Nat → List Nat := fun i => rt_segOf w (par.getD 3 0) (par.getD 4 0) (d.getD i 0)
  have hsg : ∀ i, i < d.length → (sg i).length = (par.getD 4 0) := fun i hi => rt_segOf_length (hB i hi)
  let X : Nat → List Nat := fun m => (List.range m).flatMap sg
  have hX : ∀ m, m ≤ d.length → (X m).length = m * (par.getD 4 0) := by
    intro m hm
    have : ∀ m', m' ≤ d.length → (X m').length = m' * (par.getD 4 0) := by
      intro m' hm'
      induction m' with
      | zero => simp [X]
      | succ m' ih =>
        simp only [X, List.range_succ, List.flatMap_append, List.length_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil]
        rw [show ((List.range m').flatMap sg).length = m' * (par.getD 4 0) from ih (by omega), hsg m' (by omega), Nat.succ_mul]
    exact this m hm
  have hout : rt_out w par d = X d.length := rfl
  have hol : (rt_out w par d).length = d.length * (par.getD 4 0) := by rw [hout]; exact hX _ (Nat.le_refl _)
  have hwl : w.length + d.length * (par.getD 4 0) ≤ Z := by rw [← hol]; simpa using hwZ
  let F : Nat → Lists NK := fun m => ((S.set ROWS (w ++ X m)).set rt_I2 [m]).set rt_I [d.length - m]
  have x₁ := nruns_pushZ rt_I2 S
  rw [rt_FreeOn_get hfree, List.nil_append] at x₁
  have x₂ := rt_get_runs (i := rt_PAR) (o := rt_I) (h₁ := by decide) (h₂ := by decide) (by decide) (by decide)
    (by decide) (S.set rt_I2 [0]) 2 (by rt_at; exact rt_FreeOn_get hfree) (by rt_at; exact rt_FreeOn_get hfree)
    (by rt_at; rw [hpar, hpl]; omega)
  have e₂ : (S.set rt_I2 [0]).set rt_I ((S.set rt_I2 [0]) rt_I ++ [((S.set rt_I2 [0]) rt_PAR).getD 2 0]) = F 0 := by
    have h1 : S rt_I = [] := rt_FreeOn_get hfree
    simp only [F, X, List.range_zero, List.flatMap_nil, List.append_nil, Nat.sub_zero]
    rt_extU [rt_I2, rt_I, ROWS] [h1, hpar, hdl.symm, hR]
  have eP : (S.set rt_I2 [0]) rt_PAR = par := by rt_at; exact hpar
  rw [e₂, eP, hpl] at x₂
  have x₃ := rt_for_runs (c := rt_I) (body := .seq (rt_offB rt_I2 rt_O1 (by decide) (by decide))
      (.seq (rt_get rt_PAR rt_P 4 (by decide) (by decide)) (.seq (rt_copy ROWS (by decide)) (.prim (.inc rt_I2)))))
    F [] d.length (13 * (Z * Z) + 29 * Z + 264)
    (fun m _ => by simp only [F]; rt_at)
    (fun m hm => by
      let G := (F m).set rt_I [d.length - m - 1]
      have hGf : rt_FreeOn rt_fr3 G := by
        intro y hy
        have : y ≠ rt_I ∧ y ≠ rt_I2 ∧ y ≠ ROWS := by revert hy; decide +revert
        simp only [G, F]
        rw [Lists.set_ne _ _ this.1, Lists.set_ne _ _ this.1, Lists.set_ne _ _ this.2.1, Lists.set_ne _ _ this.2.2]
        exact hfree y (by revert hy; decide +revert)
      have y₁ := rt_offB_runs (src := rt_I2) (O := rt_O1) (h₀ := by decide) (h := by decide) (by decide) (by decide) G
        (i := m) hGf (by simp only [G, F]; rt_at; exact rt_FreeOn_get hfree) (by simp only [G, F]; rt_at; exact hpar) hpl
        (by simp only [G, F]; rt_at) (by simp only [G, F]; rt_at; exact hD) (by omega)
      let G₁ := G.set rt_O1 [(par.getD 3 0) + d.getD m 0 * (par.getD 4 0)]
      have y₂ := rt_get_runs (i := rt_PAR) (o := rt_P) (h₁ := by decide) (h₂ := by decide) (by decide) (by decide)
        (by decide) G₁ 4 (by simp only [G₁, G, F]; rt_at; exact rt_FreeOn_get hfree)
        (by simp only [G₁, G, F]; rt_at; exact rt_FreeOn_get hfree) (by simp only [G₁, G, F]; rt_at; rw [hpar, hpl]; omega)
      have eG₁ : G₁ rt_PAR = par := by simp only [G₁, G, F]; rt_at; exact hpar
      have eG₂ : G₁ rt_P = [] := by simp only [G₁, G, F]; rt_at; exact rt_FreeOn_get hfree
      rw [eG₁, eG₂, List.nil_append, hpl] at y₂
      let G₂ := G₁.set rt_P [(par.getD 4 0)]
      have hBm := hB m hm
      have y₃ := rt_copy_runs (src := ROWS) (h₁ := by decide) (by decide) G₂ (w := w ++ X m) (seg := sg m)
        (o := par.getD 3 0 + d.getD m 0 * par.getD 4 0) (L := par.getD 4 0) (B := Z) (by simp only [G₂]; rt_at) (by simp only [G₂, G₁]; rt_at)
        (by simp only [G₂, G₁, G, F]; rt_at; exact rt_FreeOn_get hfree)
        (by simp only [G₂, G₁, G, F]; rt_at; exact rt_FreeOn_get hfree)
        (by simp only [G₂, G₁, G, F]; rt_at; exact rt_FreeOn_get hfree)
        (by simp only [G₂, G₁, G, F]; rt_at) (hsg m hm)
        (fun p hp => by
          rw [Lists.set_same]
          refine ⟨by simp only [List.length_append]; omega, ?_⟩
          rw [List.append_assoc]
          exact rt_segOf_getD hBm hp _)
        (fun p hp => by
          rw [Lists.set_same]
          have := hX m (by omega)
          have hpm : m * (par.getD 4 0) + p + 1 ≤ d.length * (par.getD 4 0) := by
            have := Nat.mul_le_mul_right (par.getD 4 0) (show m + 1 ≤ d.length by omega); rw [Nat.succ_mul] at this; omega
          simp only [List.length_append, List.length_take]
          have := Nat.min_le_left p (sg m).length
          omega)
        (by omega)
      let G₃ := ((G₂.set ROWS (w ++ X m ++ sg m)).set rt_P []).set rt_O1 []
      have y₄ := nruns_inc rt_I2 G₃ (l := []) (v := m) (by simp only [G₃, G₂, G₁, G, F]; rt_at)
      have e : G₃.set rt_I2 ([] ++ [m + 1]) = F (m + 1) := by
        have h1 : S rt_P = [] := rt_FreeOn_get hfree
        have h2 : S rt_O1 = [] := rt_FreeOn_get hfree
        have hXs : X (m + 1) = X m ++ sg m := by simp [X, List.range_succ, List.flatMap_append]
        simp only [G₃, G₂, G₁, G, F, hXs, show d.length - (m + 1) = d.length - m - 1 by omega, List.append_assoc]
        rt_extU [rt_I2, rt_I, ROWS, rt_P, rt_O1] [h1, h2]
      rw [e] at y₄
      have c₁ := rt_getD_le hdE m
      have c₂ := rt_mul_bound c₁ hb1 3 7
      have c₃ : (par.getD 4 0) * (10 * Z + 12) ≤ 10 * (Z * Z) + 12 * Z := rt_mul_bound hb1 (Nat.le_refl Z) 10 12
      exact (y₁.seq (y₂.seq (y₃.seq y₄))).mono (by omega))
  have x₄ := nruns_pop rt_I2 ((F d.length).set rt_I []) (l := []) (v := d.length) (by simp only [F]; rt_at)
  have x₅ := nruns_inc CNT (((F d.length).set rt_I []).set rt_I2 []) (l := lc) (v := c)
    (by simp only [F]; rt_at; exact hC)
  have e : (((F d.length).set rt_I []).set rt_I2 []).set CNT (lc ++ [c + 1]) =
      (S.set ROWS (w ++ rt_out w par d)).set CNT (lc ++ [c + 1]) := by
    have h1 : S rt_I = [] := rt_FreeOn_get hfree
    have h2 : S rt_I2 = [] := rt_FreeOn_get hfree
    simp only [F, Nat.sub_self, hout]
    rt_extU [rt_I2, rt_I, ROWS, CNT] [h1, h2]
  rw [e] at x₅
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq x₅)))).mono (rt_emitA_cost hdZ (Nat.le_refl _))

/-- Append the digits in `D` (a row of `p`) to `ROWS`, and count it. -/
def rt_emitP : NProg NK :=
  .seq (rt_get rt_PAR rt_P 2 (by decide) (by decide)) (.seq (.prim (.pushZ rt_O1))
    (.seq (rt_copy rt_D (by decide)) (.prim (.inc CNT))))

theorem rt_emitP_runs (S : Lists NK) {par d w lc : List Nat} {c Z : Nat} (hfree : rt_FreeOn rt_frC S)
    (hpar : S rt_PAR = par) (hpl : par.length = 6) (hD : S rt_D = d) (hR : S ROWS = w) (hC : S CNT = lc ++ [c])
    (hdl : d.length = par.getD 2 0) (hdZ : d.length ≤ Z) :
    NRuns rt_emitP S ((S.set ROWS (w ++ d)).set CNT (lc ++ [c + 1])) (10 * (Z * Z) + 12 * Z + 58) := by
  have x₁ := rt_get_runs (i := rt_PAR) (o := rt_P) (h₁ := by decide) (h₂ := by decide) (by decide) (by decide)
    (by decide) S 2 (rt_FreeOn_get hfree) (rt_FreeOn_get hfree) (by rw [hpar, hpl]; omega)
  rw [rt_FreeOn_get hfree, List.nil_append, hpar, hpl, ← hdl] at x₁
  have x₂ := nruns_pushZ rt_O1 (S.set rt_P [d.length])
  have eO : (S.set rt_P [d.length]) rt_O1 = [] := by rt_at; exact rt_FreeOn_get hfree
  rw [eO, List.nil_append] at x₂
  let S₂ := (S.set rt_P [d.length]).set rt_O1 [0]
  have x₃ := rt_copy_runs (src := rt_D) (h₁ := by decide) (by decide) S₂ (w := w) (seg := d) (o := 0) (L := d.length)
    (B := Z) (by simp only [S₂]; rt_at) (by simp only [S₂]; rt_at) (by simp only [S₂]; rt_at; exact rt_FreeOn_get hfree)
    (by simp only [S₂]; rt_at; exact rt_FreeOn_get hfree) (by simp only [S₂]; rt_at; exact rt_FreeOn_get hfree)
    (by simp only [S₂]; rt_at; exact hR) rfl
    (fun m hm => by simp only [S₂]; rt_at; rw [hD]; exact ⟨by omega, by rw [Nat.zero_add]⟩)
    (fun m hm => by simp only [S₂]; rt_at; rw [hD]; exact hdZ) (by omega)
  have x₄ := nruns_inc CNT (((S₂.set ROWS (w ++ d)).set rt_P []).set rt_O1 []) (l := lc) (v := c)
    (by simp only [S₂]; rt_at; exact hC)
  have e : (((S₂.set ROWS (w ++ d)).set rt_P []).set rt_O1 []).set CNT (lc ++ [c + 1]) =
      (S.set ROWS (w ++ d)).set CNT (lc ++ [c + 1]) := by
    have h1 : S rt_P = [] := rt_FreeOn_get hfree
    have h2 : S rt_O1 = [] := rt_FreeOn_get hfree
    simp only [S₂]
    rt_extU [rt_P, rt_O1, ROWS, CNT] [h1, h2]
  rw [e] at x₄
  have c₁ : d.length * (10 * Z + 12) ≤ 10 * (Z * Z) + 12 * Z := rt_mul_bound hdZ (Nat.le_refl Z) 10 12
  exact (x₁.seq (x₂.seq (x₃.seq x₄))).mono (by omega)

/-- A candidate of an arrow: when monotone, append it and count it. -/
def rt_aBody : NProg NK :=
  .seq rt_mono (.ite rt_MF .pos (.seq (.prim (.pop rt_MF)) rt_emitA) (.prim (.pop rt_MF)))

theorem rt_aBody_runs (S : Lists NK) {par d w lc : List Nat} {c Z : Nat} (hfree : rt_FreeOn rt_frC S)
    (hpar : S rt_PAR = par) (hpl : par.length = 6) (hD : S rt_D = d) (hR : S ROWS = w) (hC : S CNT = lc ++ [c])
    (hM : S rt_MF = []) (hdl : d.length = par.getD 2 0)
    (hA : ∀ i, i < d.length → par.getD 0 0 + i * par.getD 1 0 + par.getD 1 0 ≤ w.length)
    (hB : ∀ i, i < d.length → par.getD 3 0 + d.getD i 0 * par.getD 4 0 + par.getD 4 0 ≤ w.length)
    (hw : w.length ≤ Z) (hwZ : rt_monoOK w par d = true → (w ++ rt_out w par d).length ≤ Z) (hE : ∀ v ∈ w, v ≤ Z)
    (ha1 : par.getD 1 0 ≤ Z) (hb1 : par.getD 4 0 ≤ Z) (hdZ : d.length ≤ Z) (hdE : ∀ v ∈ d, v ≤ Z) :
    NRuns rt_aBody S ((S.set ROWS (w ++ if rt_monoOK w par d then rt_out w par d else [])).set CNT
      (lc ++ [c + if rt_monoOK w par d then 1 else 0]))
      (92 * (Z * (Z * (Z * Z))) + 145 * (Z * (Z * Z)) + 876 * (Z * Z) + 323 * Z + 117) := by
  have x₁ := rt_mono_runs S hfree hpar hpl hD hR hM hdl hA hB hw hE ha1 hb1 hdZ hdE
  rw [List.nil_append] at x₁
  have x₂ := nruns_pop rt_MF (S.set rt_MF [if rt_monoOK w par d then 1 else 0]) (l := [])
    (v := if rt_monoOK w par d then 1 else 0) (by simp)
  rw [Lists.set_set_u, set_nil_self hM] at x₂
  cases hok : rt_monoOK w par d
  · simp only [hok, Bool.false_eq_true, if_false, List.append_nil, Nat.add_zero] at x₁ x₂ ⊢
    rw [← hR, ← hC, Lists.set_get_self, Lists.set_get_self]
    exact (x₁.seq (x₂.iteF (by simp [NTest.eval]))).mono (by omega)
  · simp only [hok, if_true] at x₁ x₂ ⊢
    have x₃ := rt_emitA_runs S hfree hpar hpl hD hR hC hdl hB (hwZ hok) hb1 hdZ hdE
    exact (x₁.seq ((x₂.seq x₃).iteT (by simp [NTest.eval]))).mono (by omega)

/-! ## The odometer step -/

/-- Push on `MF` whether the top digit of `D` is the last one (`B - 1`, `B` = entry `5` of `PAR`). -/
def rt_flagTop : NProg NK :=
  .ite rt_D .nonempty (.seq (.prim (.dup rt_D rt_V1 (by decide))) (.seq (.prim (.inc rt_V1))
    (.seq (rt_get rt_PAR rt_V2 5 (by decide) (by decide)) (rt_eqF rt_V1 rt_V2 rt_MF)))) (.prim (.pushZ rt_MF))

theorem rt_flagTop_runs (S : Lists NK) {par ds l : List Nat} (hfree : rt_FreeOn rt_fr3 S) (hpar : S rt_PAR = par)
    (hpl : par.length = 6) (hD : S rt_D = ds.reverse) (hM : S rt_MF = l) (hds : ∀ v ∈ ds, v ≤ par.getD 5 0) :
    NRuns rt_flagTop S (S.set rt_MF (l ++ [rt_topF (par.getD 5 0) ds])) (3 * par.getD 5 0 + 90) := by
  rcases ds with _ | ⟨d, r⟩
  · have x := nruns_pushZ rt_MF S
    rw [hM] at x
    exact (x.iteF (by rw [hD]; rfl)).mono (by omega)
  · have hD' : S rt_D = r.reverse ++ [d] := by rw [hD, List.reverse_cons]
    have x₁ := nruns_dup rt_D rt_V1 (by decide) S hD'
    rw [rt_FreeOn_get hfree, List.nil_append] at x₁
    have x₂ := nruns_inc rt_V1 (S.set rt_V1 [d]) (l := []) (v := d) (by simp)
    rw [Lists.set_set_u] at x₂
    have x₃ := rt_get_runs (i := rt_PAR) (o := rt_V2) (h₁ := by decide) (h₂ := by decide) (by decide) (by decide)
      (by decide) (S.set rt_V1 [d + 1]) 5 (by rt_at; exact rt_FreeOn_get hfree) (by rt_at; exact rt_FreeOn_get hfree)
      (by rt_at; rw [hpar, hpl]; omega)
    have eP : (S.set rt_V1 [d + 1]) rt_PAR = par := by rt_at; exact hpar
    have eV : (S.set rt_V1 [d + 1]) rt_V2 = [] := by rt_at; exact rt_FreeOn_get hfree
    rw [eP, eV, List.nil_append, hpl] at x₃
    have x₄ := rt_eqF_runs (V := rt_V1) (W := rt_V2) (O := rt_MF) (by decide) (by decide) (by decide)
      ((S.set rt_V1 [d + 1]).set rt_V2 [par.getD 5 0]) (lv := []) (lw := []) (x := d + 1) (y := par.getD 5 0)
      (by rt_at) (by rt_at)
    have e : ((((S.set rt_V1 [d + 1]).set rt_V2 [par.getD 5 0]).set rt_V1 []).set rt_V2 []).set rt_MF
        (((S.set rt_V1 [d + 1]).set rt_V2 [par.getD 5 0]) rt_MF ++ [if d + 1 = par.getD 5 0 then 1 else 0]) =
        S.set rt_MF (l ++ [rt_topF (par.getD 5 0) (d :: r)]) := by
      have h1 : S rt_V1 = [] := rt_FreeOn_get hfree
      have h2 : S rt_V2 = [] := rt_FreeOn_get hfree
      simp only [rt_topF]
      rt_extU [rt_V1, rt_V2, rt_MF] [h1, h2, hM]
    rw [e] at x₄
    have hd := hds d List.mem_cons_self
    exact ((x₁.seq (x₂.seq (x₃.seq x₄))).iteT (by rw [hD']; simp)).mono (by omega)


/-- **One step of the odometer**: add one to the digits on `D` (least significant on top). -/
def rt_incrP : NProg NK :=
  .seq (.prim (.pushZ rt_I)) (.seq rt_flagTop
    (.seq (.loop rt_MF .pos (.seq (.prim (.pop rt_MF)) (.seq (.prim (.pop rt_D)) (.seq (.prim (.inc rt_I)) rt_flagTop))))
      (.seq (.prim (.pop rt_MF)) (.seq (.prim (.inc rt_D)) (rt_for rt_I (.prim (.pushZ rt_D)))))))

theorem rt_inc_bump (S : Lists NK) (X : List Nat) (hD : S rt_D = X.reverse) :
    NRuns (.prim (.inc rt_D)) S (S.set rt_D (rt_bump X).reverse) 1 := by
  rcases X with _ | ⟨x, r⟩
  · have := nruns_prim (.inc rt_D) S
    simp only [NPrim.apply, hD, List.reverse_nil, mapTop_nil] at this
    exact this
  · have := nruns_inc rt_D S (l := r.reverse) (v := x) (by rw [hD, List.reverse_cons])
    simp only [rt_bump, List.reverse_cons]
    exact this

theorem rt_incr_cost {c B Z : Nat} (hc : c ≤ Z) (hB : B ≤ Z) :
    1 + (3 * B + 90 + (c * (1 + (1 + (1 + (3 * B + 90))) + 1) + 1 + (1 + (1 + (c * (1 + 2) + 2))))) ≤
      3 * (Z * Z) + 100 * Z + 100 := by
  have h₁ := Nat.mul_le_mul hc (show 1 + (1 + (1 + (3 * B + 90))) + 1 ≤ 3 * Z + 94 by omega)
  have h₂ : Z * (3 * Z + 94) = 3 * (Z * Z) + 94 * Z := by rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm Z 94]
  have h₃ := Nat.mul_le_mul_right 3 hc
  generalize c * (1 + (1 + (1 + (3 * B + 90))) + 1) = A at *
  generalize Z * Z = Z2 at *
  omega

theorem rt_incr_runs (S : Lists NK) {par ds : List Nat} {Z : Nat} (hfree : rt_FreeOn rt_frC S)
    (hpar : S rt_PAR = par) (hpl : par.length = 6) (hD : S rt_D = ds.reverse) (hM : S rt_MF = [])
    (hds : ∀ v ∈ ds, v ≤ par.getD 5 0) (hB : par.getD 5 0 ≤ Z) (hdl : ds.length ≤ Z) :
    NRuns rt_incrP S (S.set rt_D (rt_incr (par.getD 5 0) ds).reverse) (3 * (Z * Z) + 100 * Z + 100) := by
  have hdsd : ∀ i, ∀ v ∈ ds.drop i, v ≤ par.getD 5 0 := fun i v hv => hds v (List.mem_of_mem_drop hv)
  have hc : rt_lead (par.getD 5 0) ds ≤ ds.length := rt_lead_le _ ds
  let G : Nat → Lists NK := fun i =>
    ((S.set rt_I [i]).set rt_D (ds.drop i).reverse).set rt_MF [rt_topF (par.getD 5 0) (ds.drop i)]
  have hG3 : ∀ i, rt_FreeOn rt_fr3 ((S.set rt_I [i]).set rt_D (ds.drop i).reverse) := fun i =>
    rt_FreeOn_set (rt_FreeOn_set (rt_FreeOn_mono hfree (by decide)) (by decide) _) (by decide) _
  have x₁ := nruns_pushZ rt_I S
  rw [rt_FreeOn_get hfree, List.nil_append] at x₁
  have x₂ := rt_flagTop_runs ((S.set rt_I [0]).set rt_D (ds.drop 0).reverse) (ds := ds.drop 0) (l := []) (hG3 0)
    (by rt_at; exact hpar) hpl (by rt_at) (by rt_at; exact hM) (hdsd 0)
  have e₁ : (S.set rt_I [0]).set rt_D (ds.drop 0).reverse = S.set rt_I [0] := by
    rw [List.drop_zero, ← hD]; rt_ext [rt_I, rt_D]
  rw [List.nil_append] at x₂
  rw [← e₁] at x₁
  have x₃ := nruns_family_const (i := rt_MF) (c := .pos)
    (p := .seq (.prim (.pop rt_MF)) (.seq (.prim (.pop rt_D)) (.seq (.prim (.inc rt_I)) rt_flagTop)))
    G (rt_lead (par.getD 5 0) ds) (1 + (1 + (1 + (3 * par.getD 5 0 + 90))))
    (fun m hm => by simp only [G]; rt_at; rw [rt_topF_lt _ ds m hm]; rfl)
    (by simp only [G]; rt_at; rw [rt_topF_lead]; rfl)
    (fun m hm => by
      have hml : m < ds.length := by omega
      have hdrop : ds.drop m = ds[m] :: ds.drop (m + 1) := List.drop_eq_getElem_cons hml
      have y₁ := nruns_pop rt_MF (G m) (l := []) (v := rt_topF (par.getD 5 0) (ds.drop m)) (by simp only [G]; rt_at)
      have y₂ := nruns_pop rt_D ((G m).set rt_MF []) (l := (ds.drop (m + 1)).reverse) (v := ds[m])
        (by simp only [G]; rt_at; rw [hdrop, List.reverse_cons])
      have y₃ := nruns_inc rt_I (((G m).set rt_MF []).set rt_D (ds.drop (m + 1)).reverse) (l := []) (v := m)
        (by simp only [G]; rt_at)
      let G' := (((G m).set rt_MF []).set rt_D (ds.drop (m + 1)).reverse).set rt_I ([] ++ [m + 1])
      have eG' : G' = ((S.set rt_I [m + 1]).set rt_D (ds.drop (m + 1)).reverse).set rt_MF [] := by
        simp only [G', G, List.nil_append]; rt_ext [rt_I, rt_D, rt_MF]
      have y₄ := rt_flagTop_runs G' (ds := ds.drop (m + 1)) (l := [])
        (by rw [eG']; exact rt_FreeOn_set (hG3 (m + 1)) (by decide) _)
        (by simp only [G', G]; rt_at; exact hpar) hpl (by simp only [G']; rt_at) (by simp only [G']; rt_at)
        (hdsd (m + 1))
      have e : G'.set rt_MF ([] ++ [rt_topF (par.getD 5 0) (ds.drop (m + 1))]) = G (m + 1) := by
        rw [eG']; simp only [G, List.nil_append]; rt_ext [rt_MF]
      rw [e] at y₄
      exact (y₁.seq (y₂.seq (y₃.seq y₄))).mono (by omega))
  obtain ⟨c, hcdef⟩ : ∃ c, c = rt_lead (par.getD 5 0) ds := ⟨_, rfl⟩
  rw [← hcdef] at x₃ hc
  have x₄ := nruns_pop rt_MF (G c) (l := []) (v := 0) (by simp only [G]; rt_at; rw [hcdef, rt_topF_lead])
  have x₅ := rt_inc_bump ((G c).set rt_MF []) (ds.drop c) (by simp only [G]; rt_at)
  let H : Nat → Lists NK := fun t =>
    (((S.set rt_I [c - t]).set rt_D ((rt_bump (ds.drop c)).reverse ++ List.replicate t 0)).set rt_MF [])
  have e₅ : ((G c).set rt_MF []).set rt_D (rt_bump (ds.drop c)).reverse = H 0 := by
    simp only [G, H, Nat.sub_zero, List.replicate_zero, List.append_nil]; rt_ext [rt_I, rt_D, rt_MF]
  rw [e₅] at x₅
  have x₆ := rt_for_runs (c := rt_I) (body := .prim (.pushZ rt_D)) H [] c 1
    (fun t _ => by simp only [H]; rt_at)
    (fun t ht => by
      have := nruns_pushZ rt_D ((H t).set rt_I [c - t - 1])
      have e : ((H t).set rt_I [c - t - 1]).set rt_D (((H t).set rt_I [c - t - 1]) rt_D ++ [0]) = H (t + 1) := by
        simp only [H, List.replicate_succ', ← List.append_assoc, show c - (t + 1) = c - t - 1 by omega]
        rt_ext [rt_I, rt_D, rt_MF]
      rw [e] at this; exact this)
  have e₆ : (H c).set rt_I [] = S.set rt_D (rt_incr (par.getD 5 0) ds).reverse := by
    have h1 : S rt_I = [] := rt_FreeOn_get hfree
    rw [rt_incr_eq, ← hcdef]
    simp only [H, List.reverse_append, List.reverse_replicate]
    rt_extU [rt_I, rt_D, rt_MF] [h1, hM]
  rw [e₆] at x₆
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq x₆))))).mono
    (rt_incr_cost (Nat.le_trans hc hdl) hB)

/-! ## The odometer -/

/-- Run `body` on every digit vector (`PAR`: `m` at entry `2`, `B` at entry `5`; `QC`: the count `B ^ m`, popped). -/
def rt_odo (body : NProg NK) : NProg NK :=
  .seq (rt_get rt_PAR rt_I 2 (by decide) (by decide)) (.seq (rt_for rt_I (.prim (.pushZ rt_D)))
    (.seq (rt_for rt_QC (.seq body rt_incrP)) (nclr rt_D)))

theorem rt_vec_le {B m q : Nat} (hB : 1 ≤ B ∨ m = 0) : ∀ v ∈ (rt_dig B m q), v ≤ B := by
  intro v hv
  rcases hB with hB | rfl
  · exact Nat.le_of_lt (rt_dig_lt (by omega) m q v hv)
  · simp [rt_dig] at hv

theorem rt_incr_dig' {B m : Nat} (hB : 1 ≤ B ∨ m = 0) (q : Nat) : rt_incr B (rt_dig B m q) = rt_dig B m (q + 1) := by
  rcases hB with hB | rfl
  · exact rt_incr_dig (by omega) m q
  · rfl

theorem rt_odo_cost {cnt m Tb Z : Nat} (hm : m ≤ Z) :
    6 * 6 + 5 * 2 + 7 + (m * (1 + 2) + 2 + (cnt * (Tb + (3 * (Z * Z) + 100 * Z + 100) + 2) + 2 + (2 * m + 1))) ≤
      cnt * (Tb + 3 * (Z * Z) + 100 * Z + 102) + 5 * Z + 58 := by
  rw [show Tb + (3 * (Z * Z) + 100 * Z + 100) + 2 = Tb + 3 * (Z * Z) + 100 * Z + 102 by omega]
  generalize cnt * (Tb + 3 * (Z * Z) + 100 * Z + 102) = A
  omega

theorem rt_odo_runs {body : NProg NK} (S0 : Lists NK) (R C : Nat → List Nat) {par : List Nat} {cnt Tb Z : Nat}
    (hfree : rt_FreeOn rt_frC S0) (hM : S0 rt_MF = []) (hD : S0 rt_D = []) (hQ : S0 rt_QC = [])
    (hpar : S0 rt_PAR = par) (hpl : par.length = 6)
    (hB : 1 ≤ par.getD 5 0 ∨ par.getD 2 0 = 0) (hBZ : par.getD 5 0 ≤ Z) (hmZ : par.getD 2 0 ≤ Z)
    (hbody : ∀ q, q < cnt → NRuns body
      ((((S0.set ROWS (R q)).set CNT (C q)).set rt_D (rt_vec (par.getD 5 0) (par.getD 2 0) q)).set rt_QC [cnt - q - 1])
      ((((S0.set ROWS (R (q + 1))).set CNT (C (q + 1))).set rt_D (rt_vec (par.getD 5 0) (par.getD 2 0) q)).set rt_QC
        [cnt - q - 1]) Tb) :
    NRuns (rt_odo body) (((S0.set ROWS (R 0)).set CNT (C 0)).set rt_QC [cnt]) ((S0.set ROWS (R cnt)).set CNT (C cnt))
      (cnt * (Tb + 3 * (Z * Z) + 100 * Z + 102) + 5 * Z + 58) := by
  let St0 := ((S0.set ROWS (R 0)).set CNT (C 0)).set rt_QC [cnt]
  have x₁ := rt_get_runs (i := rt_PAR) (o := rt_I) (h₁ := by decide) (h₂ := by decide) (by decide) (by decide)
    (by decide) St0 2 (by simp only [St0]; rt_at; exact rt_FreeOn_get hfree)
    (by simp only [St0]; rt_at; exact rt_FreeOn_get hfree) (by simp only [St0]; rt_at; rw [hpar, hpl]; omega)
  have eP : St0 rt_PAR = par := by simp only [St0]; rt_at; exact hpar
  have eI : St0 rt_I = [] := by simp only [St0]; rt_at; exact rt_FreeOn_get hfree
  rw [eP, eI, List.nil_append, hpl] at x₁
  let Hh : Nat → Lists NK := fun t => (St0.set rt_D (List.replicate t 0)).set rt_I [(par.getD 2 0) - t]
  have x₂ := rt_for_runs (c := rt_I) (body := .prim (.pushZ rt_D)) Hh [] (par.getD 2 0) 1
    (fun t _ => by simp only [Hh]; rt_at)
    (fun t ht => by
      have := nruns_pushZ rt_D ((Hh t).set rt_I [(par.getD 2 0) - t - 1])
      have e : ((Hh t).set rt_I [(par.getD 2 0) - t - 1]).set rt_D (((Hh t).set rt_I [(par.getD 2 0) - t - 1]) rt_D ++ [0]) = Hh (t + 1) := by
        simp only [Hh, List.replicate_succ', show (par.getD 2 0) - (t + 1) = (par.getD 2 0) - t - 1 by omega]
        rt_ext [rt_I, rt_D]
      rw [e] at this; exact this)
  have e₀ : Hh 0 = St0.set rt_I [(par.getD 2 0)] := by
    have hD' : St0 rt_D = [] := by simp only [St0]; rt_at; exact hD
    simp only [Hh, List.replicate_zero, Nat.sub_zero]; rt_extU [rt_D, rt_I] [hD']
  rw [e₀] at x₂
  let F : Nat → Lists NK := fun q =>
    (((S0.set ROWS (R q)).set CNT (C q)).set rt_D (rt_vec (par.getD 5 0) (par.getD 2 0) q)).set rt_QC [cnt - q]
  have e₁ : (Hh (par.getD 2 0)).set rt_I [] = F 0 := by
    have h1 : S0 rt_I = [] := rt_FreeOn_get hfree
    simp only [Hh, F, St0, rt_vec_zero, Nat.sub_self, Nat.sub_zero]
    rt_extU [rt_D, rt_I, rt_QC, ROWS, CNT] [h1]
  rw [e₁] at x₂
  have x₃ := rt_for_runs (c := rt_QC) (body := .seq body rt_incrP) F [] cnt (Tb + (3 * (Z * Z) + 100 * Z + 100))
    (fun q _ => by simp only [F]; rt_at)
    (fun q hq => by
      have y₁ := hbody q hq
      have e : (F q).set rt_QC [cnt - q - 1] =
          (((S0.set ROWS (R q)).set CNT (C q)).set rt_D (rt_vec (par.getD 5 0) (par.getD 2 0) q)).set rt_QC [cnt - q - 1] := by
        simp only [F, Lists.set_set_u]
      rw [← e] at y₁
      let Y := (((S0.set ROWS (R (q + 1))).set CNT (C (q + 1))).set rt_D (rt_vec (par.getD 5 0) (par.getD 2 0) q)).set rt_QC [cnt - q - 1]
      have y₂ := rt_incr_runs Y (ds := rt_dig (par.getD 5 0) (par.getD 2 0) q) (Z := Z)
        (rt_FreeOn_set (rt_FreeOn_set (rt_FreeOn_set (rt_FreeOn_set hfree (by decide) _) (by decide) _)
          (by decide) _) (by decide) _)
        (by simp only [Y]; rt_at; exact hpar) hpl (by simp only [Y]; rt_at; rfl) (by simp only [Y]; rt_at; exact hM)
        (rt_vec_le hB) hBZ (by rw [rt_dig_length]; exact hmZ)
      have e₂ : Y.set rt_D (rt_incr (par.getD 5 0) (rt_dig (par.getD 5 0) (par.getD 2 0) q)).reverse = F (q + 1) := by
        rw [rt_incr_dig' hB q]
        simp only [Y, F, show cnt - (q + 1) = cnt - q - 1 by omega, rt_vec]
        rt_ext [rt_D, rt_QC, ROWS, CNT]
      rw [e₂] at y₂
      exact y₁.seq y₂)
  have x₄ := nruns_clr rt_D ((F cnt).set rt_QC [])
  have e₄ : ((F cnt).set rt_QC []).set rt_D [] = (S0.set ROWS (R cnt)).set CNT (C cnt) := by
    simp only [F]; rt_extU [rt_D, rt_QC, ROWS, CNT] [hD, hQ]
  have eL : ((F cnt).set rt_QC []) rt_D = rt_vec (par.getD 5 0) (par.getD 2 0) cnt := by simp only [F]; rt_at
  rw [e₄, eL, rt_vec_length] at x₄
  exact (x₁.seq (x₂.seq (x₃.seq x₄))).mono (rt_odo_cost hmZ)

/-! ## The number of candidates -/

/-- Push `B ^ m` on `QC` (`PAR`: `m` at entry `2`, `B` at entry `5`). -/
def rt_pow : NProg NK :=
  .seq (npushC rt_QC 1) (.seq (rt_get rt_PAR rt_I 2 (by decide) (by decide))
    (rt_for rt_I (.seq (nmv rt_QC rt_V1 (by decide)) (.seq (.prim (.pushZ rt_O1))
      (.seq (rt_get rt_PAR rt_V2 5 (by decide) (by decide)) (.seq (rt_mul rt_V1 rt_V2 rt_O1 rt_P (by decide))
        (.seq (.prim (.pop rt_V2)) (nmv rt_O1 rt_QC (by decide)))))))))

theorem rt_pow_cost {m Z : Nat} (hm : m ≤ Z) {T : Nat} (hT : T ≤ 3 * (Z * Z) + 7 * Z + 76) :
    1 + 1 + (6 * 6 + 5 * 2 + 7 + (m * (T + 2) + 2)) ≤ 3 * (Z * (Z * Z)) + 7 * (Z * Z) + 78 * Z + 57 := by
  have h₁ := Nat.mul_le_mul hm (show T + 2 ≤ 3 * (Z * Z) + 7 * Z + 78 by omega)
  rw [rt_dist3 Z] at h₁
  generalize m * (T + 2) = A at *
  generalize Z * (Z * Z) = Z3 at *
  generalize Z * Z = Z2 at *
  omega

theorem rt_pow_runs (S : Lists NK) {par : List Nat} {Z : Nat} (hfree : rt_FreeOn rt_frC S) (hQ : S rt_QC = [])
    (hpar : S rt_PAR = par) (hpl : par.length = 6) (hBZ : par.getD 5 0 ≤ Z) (hmZ : par.getD 2 0 ≤ Z)
    (hpZ : ∀ t, t ≤ par.getD 2 0 → par.getD 5 0 ^ t ≤ Z) :
    NRuns rt_pow S (S.set rt_QC [par.getD 5 0 ^ par.getD 2 0]) (3 * (Z * (Z * Z)) + 7 * (Z * Z) + 78 * Z + 57) := by
  have x₁ := nruns_pushC rt_QC S 1
  rw [hQ, List.nil_append] at x₁
  have x₂ := rt_get_runs (i := rt_PAR) (o := rt_I) (h₁ := by decide) (h₂ := by decide) (by decide) (by decide)
    (by decide) (S.set rt_QC [1]) 2 (by rt_at; exact rt_FreeOn_get hfree) (by rt_at; exact rt_FreeOn_get hfree)
    (by rt_at; rw [hpar, hpl]; omega)
  have eP : (S.set rt_QC [1]) rt_PAR = par := by rt_at; exact hpar
  have eI : (S.set rt_QC [1]) rt_I = [] := by rt_at; exact rt_FreeOn_get hfree
  rw [eP, eI, List.nil_append, hpl] at x₂
  let F : Nat → Lists NK := fun t => (S.set rt_QC [(par.getD 5 0) ^ t]).set rt_I [(par.getD 2 0) - t]
  have e₀ : (S.set rt_QC [1]).set rt_I [(par.getD 2 0)] = F 0 := by simp only [F, Nat.pow_zero, Nat.sub_zero]
  rw [e₀] at x₂
  have x₃ := rt_for_runs (c := rt_I) (body := .seq (nmv rt_QC rt_V1 (by decide)) (.seq (.prim (.pushZ rt_O1))
      (.seq (rt_get rt_PAR rt_V2 5 (by decide) (by decide)) (.seq (rt_mul rt_V1 rt_V2 rt_O1 rt_P (by decide))
        (.seq (.prim (.pop rt_V2)) (nmv rt_O1 rt_QC (by decide)))))))
    F [] (par.getD 2 0) (3 * (Z * Z) + 7 * Z + 76)
    (fun t _ => by simp only [F]; rt_at)
    (fun t ht => by
      let G := (F t).set rt_I [(par.getD 2 0) - t - 1]
      have y₁ := nruns_mv rt_QC rt_V1 (by decide) G (l := []) (v := (par.getD 5 0) ^ t) (by simp only [G, F]; rt_at)
      have eV : G rt_V1 = [] := by simp only [G, F]; rt_at; exact rt_FreeOn_get hfree
      rw [eV, List.nil_append] at y₁
      let G₁ := (G.set rt_V1 [(par.getD 5 0) ^ t]).set rt_QC []
      have y₂ := nruns_pushZ rt_O1 G₁
      have eO : G₁ rt_O1 = [] := by simp only [G₁, G, F]; rt_at; exact rt_FreeOn_get hfree
      rw [eO, List.nil_append] at y₂
      let G₂ := G₁.set rt_O1 [0]
      have y₃ := rt_get_runs (i := rt_PAR) (o := rt_V2) (h₁ := by decide) (h₂ := by decide) (by decide) (by decide)
        (by decide) G₂ 5 (by simp only [G₂, G₁, G, F]; rt_at; exact rt_FreeOn_get hfree)
        (by simp only [G₂, G₁, G, F]; rt_at; exact rt_FreeOn_get hfree)
        (by simp only [G₂, G₁, G, F]; rt_at; rw [hpar, hpl]; omega)
      have eP₂ : G₂ rt_PAR = par := by simp only [G₂, G₁, G, F]; rt_at; exact hpar
      have eV₂ : G₂ rt_V2 = [] := by simp only [G₂, G₁, G, F]; rt_at; exact rt_FreeOn_get hfree
      rw [eP₂, eV₂, List.nil_append, hpl] at y₃
      let G₃ := G₂.set rt_V2 [(par.getD 5 0)]
      have y₄ := rt_mul_runs (X := rt_V1) (Y := rt_V2) (A := rt_O1) (TM := rt_P) (h := by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) G₃ (lx := []) (ly := []) (la := []) (x := (par.getD 5 0) ^ t) (y := (par.getD 5 0)) (a := 0)
        (by simp only [G₃, G₂, G₁]; rt_at) (by simp only [G₃]; rt_at) (by simp only [G₃, G₂]; rt_at)
        (by simp only [G₃, G₂, G₁, G, F]; rt_at; exact rt_FreeOn_get hfree)
      let G₄ := (G₃.set rt_V1 []).set rt_O1 ([] ++ [0 + (par.getD 5 0) ^ t * (par.getD 5 0)])
      have y₅ := nruns_pop rt_V2 G₄ (l := []) (v := (par.getD 5 0)) (by simp only [G₄, G₃]; rt_at)
      have y₆ := nruns_mv rt_O1 rt_QC (by decide) (G₄.set rt_V2 []) (l := []) (v := 0 + (par.getD 5 0) ^ t * (par.getD 5 0))
        (by simp only [G₄]; rt_at)
      have e : (((G₄.set rt_V2 []).set rt_QC ((G₄.set rt_V2 []) rt_QC ++ [0 + (par.getD 5 0) ^ t * (par.getD 5 0)])).set rt_O1 []) = F (t + 1) := by
        have h1 : S rt_V1 = [] := rt_FreeOn_get hfree
        have h2 : S rt_V2 = [] := rt_FreeOn_get hfree
        have h3 : S rt_O1 = [] := rt_FreeOn_get hfree
        simp only [G₄, G₃, G₂, G₁, G, F, Nat.zero_add, Nat.pow_succ, show (par.getD 2 0) - (t + 1) = (par.getD 2 0) - t - 1 by omega]
        rt_extU [rt_V1, rt_V2, rt_O1, rt_QC, rt_I] [h1, h2, h3]
      rw [e] at y₆
      have c₁ := rt_mul_bound (hpZ t (by omega)) hBZ 3 7
      exact (y₁.seq (y₂.seq (y₃.seq (y₄.seq (y₅.seq y₆))))).mono (by omega))
  have e₃ : (F (par.getD 2 0)).set rt_I [] = S.set rt_QC [(par.getD 5 0) ^ (par.getD 2 0)] := by
    have h1 : S rt_I = [] := rt_FreeOn_get hfree
    simp only [F]; rt_extU [rt_QC, rt_I] [h1]
  rw [e₃] at x₃
  exact (x₁.seq (x₂.seq x₃)).mono (rt_pow_cost hmZ (Nat.le_refl _))

/-! ## Whether a type number is small -/

/-- Run `p` when the type number on `KU` is small (from the tables `ORD`, `SZ` and the cap on `CAP`), else `q`. -/
def rt_ifSmall (j : Nat) (p q : NProg NK) : NProg NK :=
  .seq (rt_getAt ORD rt_KU rt_V1 (by decide) (by decide) (by decide)) (.seq (rt_ltC rt_V1 rt_V2 j) (.ite rt_V2 .pos
    (.seq (.prim (.pop rt_V2)) (.seq (rt_getAt SZ rt_KU rt_V1 (by decide) (by decide) (by decide))
      (.seq (.prim (.dup CAP rt_V2 (by decide))) (.seq (rt_sub rt_V1 rt_V2) (.seq (.prim (.pop rt_V1))
        (.ite rt_V2 .pos (.seq (.prim (.pop rt_V2)) p) (.seq (.prim (.pop rt_V2)) q)))))))
    (.seq (.prim (.pop rt_V2)) q)))

theorem rt_ifSmall_runs (j : Nat) {p q : NProg NK} (S S' : Lists NK) {k o z cap T : Nat} (hKU : S rt_KU = [k])
    (hko : k < (S ORD).length) (ho : (S ORD).getD k 0 = o) (hkz : k < (S SZ).length) (hz : (S SZ).getD k 0 = z)
    (hC : S CAP = [cap]) (hV1 : S rt_V1 = []) (hV2 : S rt_V2 = []) (hIX : S rt_IX = []) (hT : S rt_T = [])
    (hp : o < j ∧ z < cap → NRuns p S S' T) (hq : ¬ (o < j ∧ z < cap) → NRuns q S S' T) :
    NRuns (rt_ifSmall j p q) S S' (T + 6 * (S ORD).length + 6 * (S SZ).length + 8 * k + 2 * o + 3 * z + 40) := by
  have x₁ := rt_getAt_runs (i := ORD) (c := rt_KU) (o := rt_V1) (h₀ := by decide) (h₁ := by decide) (h₂ := by decide)
    (by decide) (by decide) (by decide) S (lc := []) (k := k) hKU hIX hT hko
  rw [hV1, List.nil_append, ho] at x₁
  have x₂ := rt_ltC_runs (v := rt_V1) (f := rt_V2) (by decide) j (S.set rt_V1 [o]) [] o (by simp)
  have e₂ : ∀ b, ((S.set rt_V1 [o]).set rt_V1 []).set rt_V2 ((S.set rt_V1 [o]) rt_V2 ++ [b]) = S.set rt_V2 [b] := by
    intro b; rt_extU [rt_V1, rt_V2] [hV1, hV2]
  rw [e₂] at x₂
  have back : ∀ b, NRuns (.prim (.pop rt_V2)) (S.set rt_V2 [b]) S 1 := by
    intro b
    have := nruns_pop rt_V2 (S.set rt_V2 [b]) (l := []) (v := b) (by simp)
    rwa [Lists.set_set_u, set_nil_self hV2] at this
  by_cases hoj : o < j
  · rw [if_pos hoj] at x₂
    have y₁ := rt_getAt_runs (i := SZ) (c := rt_KU) (o := rt_V1) (h₀ := by decide) (h₁ := by decide) (h₂ := by decide)
      (by decide) (by decide) (by decide) S (lc := []) (k := k) hKU hIX hT hkz
    rw [hV1, List.nil_append, hz] at y₁
    have y₂ := nruns_dup CAP rt_V2 (by decide) (S.set rt_V1 [z]) (l := []) (v := cap) (by rt_at; exact hC)
    have eV : (S.set rt_V1 [z]) rt_V2 = [] := by rt_at; exact hV2
    rw [eV, List.nil_append] at y₂
    have y₃ := rt_sub_runs (V := rt_V1) (W := rt_V2) (by decide) ((S.set rt_V1 [z]).set rt_V2 [cap]) (lv := [])
      (lw := []) (x := z) (y := cap) (by rt_at) (by rt_at)
    have y₄ := nruns_pop rt_V1 ((((S.set rt_V1 [z]).set rt_V2 [cap]).set rt_V1 ([] ++ [0])).set rt_V2 ([] ++ [cap - z]))
      (l := []) (v := 0) (by rt_at)
    have e₄ : (((((S.set rt_V1 [z]).set rt_V2 [cap]).set rt_V1 ([] ++ [0])).set rt_V2 ([] ++ [cap - z])).set rt_V1 []) =
        S.set rt_V2 [cap - z] := by rt_extU [rt_V1, rt_V2] [hV1]
    rw [e₄] at y₄
    have hb1 : NTest.pos.eval ((S.set rt_V2 [1]) rt_V2) = true := by simp [NTest.eval]
    by_cases hzc : z < cap
    · have r := hp ⟨hoj, hzc⟩
      have hc : NTest.pos.eval ((S.set rt_V2 [cap - z]) rt_V2) = true := by
        rw [Lists.set_same, show cap - z = (cap - z - 1) + 1 by omega]; simp [NTest.eval]
      have inner := NRuns.iteT (i := rt_V2) (c := .pos) (q := .seq (.prim (.pop rt_V2)) q) hc ((back (cap - z)).seq r)
      have outer := NRuns.iteT (i := rt_V2) (c := .pos) (q := .seq (.prim (.pop rt_V2)) q) hb1
        ((back 1).seq (y₁.seq (y₂.seq (y₃.seq (y₄.seq inner)))))
      exact (x₁.seq (x₂.seq outer)).mono (by omega)
    · have r := hq (fun h => hzc h.2)
      have hc : NTest.pos.eval ((S.set rt_V2 [cap - z]) rt_V2) = false := by
        rw [Lists.set_same, show cap - z = 0 by omega]; simp [NTest.eval]
      have inner := NRuns.iteF (i := rt_V2) (c := .pos) (p := .seq (.prim (.pop rt_V2)) p) hc ((back (cap - z)).seq r)
      have outer := NRuns.iteT (i := rt_V2) (c := .pos) (q := .seq (.prim (.pop rt_V2)) q) hb1
        ((back 1).seq (y₁.seq (y₂.seq (y₃.seq (y₄.seq inner)))))
      exact (x₁.seq (x₂.seq outer)).mono (by omega)
  · rw [if_neg hoj] at x₂
    have r := hq (fun h => hoj h.1)
    have hc : NTest.pos.eval ((S.set rt_V2 [0]) rt_V2) = false := by simp [NTest.eval]
    have outer := NRuns.iteF (i := rt_V2) (c := .pos) (p := .seq (.prim (.pop rt_V2)) (.seq (rt_getAt SZ rt_KU rt_V1
      (by decide) (by decide) (by decide)) (.seq (.prim (.dup CAP rt_V2 (by decide))) (.seq (rt_sub rt_V1 rt_V2)
        (.seq (.prim (.pop rt_V1)) (.ite rt_V2 .pos (.seq (.prim (.pop rt_V2)) p) (.seq (.prim (.pop rt_V2)) q)))))))
      hc ((back 0).seq r)
    exact (x₁.seq (x₂.seq outer)).mono (by omega)

/-! ## The bound `rowsZ` -/

section Bounds

variable {j cap N : Nat} {tt : List (Nat × Nat)}

theorem rt_le_sum : ∀ (L : List Nat) (x : Nat), x ∈ L → x ≤ L.sum
  | [], _, h => by simp at h
  | a :: L, x, h => by
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := rt_le_sum L x h; omega

theorem rt_Z_ge : 2 + N + cap + tt.length + (rowsFlat j cap N tt).length ≤ rowsZ j cap N tt := by
  unfold rowsZ; omega

theorem rt_cand_le_Z {k : Nat} (hk : k ≤ tt.length) : candNum j cap N tt k ≤ rowsZ j cap N tt := by
  have := rt_le_sum ((List.range (tt.length + 1)).map (candNum j cap N tt)) (candNum j cap N tt k)
    (List.mem_map.2 ⟨k, List.mem_range.2 (by omega), rfl⟩)
  unfold rowsZ; omega

theorem rt_N3_le_Z : N + 3 ≤ rowsZ j cap N tt := by
  have h₁ := rt_cand_le_Z (j := j) (cap := cap) (N := N) (tt := tt) (k := 0) (Nat.zero_le _)
  rw [candNum] at h₁
  have h₂ : N + 3 ≤ (N + 3) ^ (N + 1) := by
    rw [Nat.pow_succ]; exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
  omega

/-- The rows written before type number `k` are an initial part of all the rows. -/
theorem rt_pre_prefix {k : Nat} (hk : k ≤ tt.length + 1) : ∃ X, rt_pre j cap N tt k ++ X = rowsFlat j cap N tt := by
  obtain ⟨X, hX⟩ := rt_pre_add (j := j) (cap := cap) (N := N) (tt := tt) k (tt.length + 1 - k)
  rw [show k + (tt.length + 1 - k) = tt.length + 1 by omega] at hX
  exact ⟨X, hX.symm⟩

theorem rt_flat_le {k : Nat} (hk : k ≤ tt.length) :
    (rowsT j cap N tt k).flatten.length ≤ (rowsFlat j cap N tt).length := by
  obtain ⟨X, hX⟩ := rt_pre_prefix (j := j) (cap := cap) (N := N) (tt := tt) (k := k + 1) (by omega)
  rw [rt_pre_succ] at hX
  rw [← hX]; simp only [List.length_append]; omega

theorem rt_lenE_le_Z (hw : TTWF tt) {k : Nat} (hk : k ≤ tt.length) : rt_lenE j cap N tt k ≤ rowsZ j cap N tt := by
  have := rt_lenE_le (j := j) (cap := cap) (N := N) hw hk
  have := rt_flat_le (j := j) (cap := cap) (N := N) (tt := tt) hk
  have := rt_Z_ge (j := j) (cap := cap) (N := N) (tt := tt)
  omega

theorem rt_cnt_le_Z (hw : TTWF tt) {k : Nat} (hk : k ≤ tt.length) : (rowsT j cap N tt k).length ≤ rowsZ j cap N tt :=
  Nat.le_trans (rt_count_le hw k hk) (rt_cand_le_Z hk)

theorem rt_rowsNum_entries (hw : TTWF tt) : ∀ k, k ≤ tt.length → ∀ r ∈ rowsNum N tt k, ∀ v ∈ r, v ≤ N + 2
  | 0, _, r, hr, v, hv => by
    rw [rowsNum] at hr
    have := ((mem_allVecs _ _ _).1 hr).2 v hv
    simp at this; omega
  | k + 1, hk, r, hr, v, hv => by
    have hlt : k < tt.length := by omega
    have hab := hw.2 k hlt
    rw [rt_rowsNum_succ hw hlt] at hr
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
    obtain ⟨x, hx, hvx⟩ := List.mem_flatten.1 hv
    exact rt_rowsNum_entries hw tt[k].2 (by omega) x (((mem_allVecs _ _ _).1 (List.mem_filter.1 hc).1).2 x hx) v hvx
termination_by k => k
decreasing_by omega

theorem rt_rowsFlat_entries (hw : TTWF tt) : ∀ v ∈ rowsFlat j cap N tt, v ≤ N + 2 := by
  intro v hv
  simp only [rowsFlat, List.mem_flatten, List.mem_map, List.mem_range] at hv
  obtain ⟨l, ⟨k, hk, rfl⟩, hv⟩ := hv
  obtain ⟨r, hr, hvr⟩ := List.mem_flatten.1 hv
  unfold rowsT at hr
  split at hr
  · exact rt_rowsNum_entries hw k (by omega) r hr v hvr
  · simp at hr

/-- An initial part of the rows is short and has small entries. -/
theorem rt_prefix_bounds (hw : TTWF tt) {w X : List Nat} (h : w ++ X = rowsFlat j cap N tt) :
    w.length ≤ rowsZ j cap N tt ∧ ∀ v ∈ w, v ≤ rowsZ j cap N tt := by
  have hZ := rt_Z_ge (j := j) (cap := cap) (N := N) (tt := tt)
  refine ⟨?_, fun v hv => ?_⟩
  · have := congrArg List.length h; simp only [List.length_append] at this; omega
  · have := rt_rowsFlat_entries (j := j) (cap := cap) hw v (by rw [← h]; exact List.mem_append_left _ hv)
    omega

end Bounds

/-! ## The tables, entry by entry -/

/-- The entries of a table below `k`. -/
def rt_tb (f : Nat → Nat) (k : Nat) : List Nat := (List.range k).map f

theorem rt_tb_succ (f : Nat → Nat) (k : Nat) : rt_tb f (k + 1) = rt_tb f k ++ [f k] := by
  simp [rt_tb, List.range_succ]

theorem rt_tb_length (f : Nat → Nat) (k : Nat) : (rt_tb f k).length = k := by simp [rt_tb]

theorem rt_tb_getD (f : Nat → Nat) {k t : Nat} (h : t < k) : (rt_tb f k).getD t 0 = f t := by
  simp [rt_tb, List.getD_eq_getElem?_getD, h]

/-! ## The states between type numbers -/

section States

variable (j cap N : Nat) (tt : List (Nat × Nat))

/-- Before type number `k`: the tables of the type numbers below `k`, and the start of the rows of `k` on `ROFF`. -/
def rt_Pre (S : Lists NK) (kc : List Nat) (k : Nat) : Lists NK :=
  (((((S.set rt_KC kc).set rt_KU [k]).set CNT (rt_tb (fun t => (rowsT j cap N tt t).length) k)).set ROWS
    (rt_pre j cap N tt k)).set ROFF (rt_tb (fun t => (rt_pre j cap N tt t).length) (k + 1))).set rt_LEN
    (rt_tb (rt_lenE j cap N tt) k)

/-- After type number `k`. -/
def rt_Out (S : Lists NK) (kc : List Nat) (k : Nat) : Lists NK :=
  (((((S.set rt_KC kc).set rt_KU [k]).set CNT (rt_tb (fun t => (rowsT j cap N tt t).length) (k + 1))).set ROWS
    (rt_pre j cap N tt (k + 1))).set ROFF (rt_tb (fun t => (rt_pre j cap N tt t).length) (k + 1))).set rt_LEN
    (rt_tb (rt_lenE j cap N tt) (k + 1))

end States

theorem rt_scratch_free {S : Lists NK} (hs : ScratchEmpty S) : rt_FreeOn rt_frC S := by
  intro y hy
  have h : 18 ≤ y.val ∧ y.val ≤ 33 := by revert hy; decide +revert
  exact hs y h.1 h.2

theorem rt_scratch_get {S : Lists NK} (hs : ScratchEmpty S) (y : Fin NK) (h : 18 ≤ y.val ∧ y.val ≤ 33 := by decide) :
    S y = [] := hs y h.1 h.2

/-- No rows for a type that is not small. -/
def rt_noRows : NProg NK := .seq (.prim (.pushZ CNT)) (.prim (.pushZ rt_LEN))

theorem rt_noRows_runs {j cap N : Nat} {tt : List (Nat × Nat)} (S : Lists NK) (kc : List Nat) {k : Nat}
    (hs : ¬ small j cap tt k) :
    NRuns rt_noRows (rt_Pre j cap N tt S kc k) (rt_Out j cap N tt S kc k) 2 := by
  have x₁ := nruns_pushZ CNT (rt_Pre j cap N tt S kc k)
  have x₂ := nruns_pushZ rt_LEN ((rt_Pre j cap N tt S kc k).set CNT ((rt_Pre j cap N tt S kc k) CNT ++ [0]))
  have e : ((rt_Pre j cap N tt S kc k).set CNT ((rt_Pre j cap N tt S kc k) CNT ++ [0])).set rt_LEN
      (((rt_Pre j cap N tt S kc k).set CNT ((rt_Pre j cap N tt S kc k) CNT ++ [0])) rt_LEN ++ [0]) =
      rt_Out j cap N tt S kc k := by
    have h₁ : rowsT j cap N tt k = [] := by rw [rowsT, if_neg hs]
    have h₂ : rt_lenE j cap N tt k = 0 := by rw [rt_lenE, if_neg hs]
    unfold rt_Pre rt_Out
    rw [rt_tb_succ (fun t => (rowsT j cap N tt t).length) k, rt_tb_succ (rt_lenE j cap N tt) k, rt_pre_succ, h₁, h₂]
    rt_ext [CNT, rt_LEN, ROWS, ROFF, rt_KU, rt_KC]
  rw [e] at x₂
  exact x₁.seq x₂

/-- The parameters of `p`: `m = N + 1` digits below `B = N + 3`. -/
def rt_parP : NProg NK :=
  .seq (.prim (.pushZ rt_PAR)) (.seq (.prim (.pushZ rt_PAR)) (.seq (.prim (.dup NX rt_PAR (by decide)))
    (.seq (.prim (.inc rt_PAR)) (.seq (.prim (.pushZ rt_PAR)) (.seq (.prim (.pushZ rt_PAR))
      (.seq (.prim (.dup NX rt_PAR (by decide))) (.seq (.prim (.inc rt_PAR)) (.seq (.prim (.inc rt_PAR))
        (.prim (.inc rt_PAR))))))))))

theorem rt_parP_runs (S : Lists NK) {N : Nat} (hP : S rt_PAR = []) (hX : S NX = [N]) :
    NRuns rt_parP S (S.set rt_PAR [0, 0, N + 1, 0, 0, N + 3]) 10 := by
  have hX' : ∀ l, (S.set rt_PAR l) NX = [] ++ [N] := fun l => by rt_at; exact hX
  have x₁ := nruns_pushZ rt_PAR S
  rw [hP] at x₁
  have x₂ := nruns_pushZ rt_PAR (S.set rt_PAR ([] ++ [0]))
  have x₃ := nruns_dup NX rt_PAR (by decide) ((S.set rt_PAR ([] ++ [0])).set rt_PAR
    ((S.set rt_PAR ([] ++ [0])) rt_PAR ++ [0])) (by rw [Lists.set_set_u]; exact hX' _)
  simp only [Lists.set_set_u, Lists.set_same, List.nil_append, List.cons_append] at x₂ x₃
  have x₄ := nruns_inc rt_PAR (S.set rt_PAR [0, 0, N]) (l := [0, 0]) (v := N) (by simp)
  have x₅ := nruns_pushZ rt_PAR ((S.set rt_PAR [0, 0, N]).set rt_PAR ([0, 0] ++ [N + 1]))
  have x₆ := nruns_pushZ rt_PAR (((S.set rt_PAR [0, 0, N]).set rt_PAR ([0, 0] ++ [N + 1])).set rt_PAR
    (((S.set rt_PAR [0, 0, N]).set rt_PAR ([0, 0] ++ [N + 1])) rt_PAR ++ [0]))
  simp only [Lists.set_set_u, Lists.set_same, List.cons_append, List.nil_append] at x₄ x₅ x₆
  have x₇ := nruns_dup NX rt_PAR (by decide) (S.set rt_PAR [0, 0, N + 1, 0, 0]) (hX' _)
  simp only [Lists.set_set_u, Lists.set_same, List.cons_append, List.nil_append] at x₇
  have x₈ := nruns_inc rt_PAR (S.set rt_PAR [0, 0, N + 1, 0, 0, N]) (l := [0, 0, N + 1, 0, 0]) (v := N) (by simp)
  have x₉ := nruns_inc rt_PAR ((S.set rt_PAR [0, 0, N + 1, 0, 0, N]).set rt_PAR ([0, 0, N + 1, 0, 0] ++ [N + 1]))
    (l := [0, 0, N + 1, 0, 0]) (v := N + 1) (by simp)
  have x₁₀ := nruns_inc rt_PAR (((S.set rt_PAR [0, 0, N + 1, 0, 0, N]).set rt_PAR ([0, 0, N + 1, 0, 0] ++ [N + 1])).set
    rt_PAR ([0, 0, N + 1, 0, 0] ++ [N + 1 + 1])) (l := [0, 0, N + 1, 0, 0]) (v := N + 1 + 1) (by simp)
  simp only [Lists.set_set_u, List.cons_append, List.nil_append] at x₈ x₉ x₁₀
  exact x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq (x₇.seq (x₈.seq (x₉.seq x₁₀))))))))

/-! ## The rows of `p` -/

/-- Tabulate the rows of `p` (type number `0`, small). -/
def rt_pRows : NProg NK :=
  .seq (.prim (.pushZ CNT)) (.seq rt_parP (.seq rt_pow (.seq (rt_odo rt_emitP) (.seq (nclr rt_PAR)
    (.seq (.prim (.dup NX rt_LEN (by decide))) (.prim (.inc rt_LEN)))))))

theorem rt_pRows_cost {c Z : Nat} (hc : c ≤ Z) :
    1 + (10 + (3 * (Z * (Z * Z)) + 7 * (Z * Z) + 78 * Z + 57 +
      (c * (10 * (Z * Z) + 12 * Z + 58 + 3 * (Z * Z) + 100 * Z + 102) + 5 * Z + 58 + (2 * 6 + 1 + (1 + 1))))) ≤
      16 * (Z * (Z * Z)) + 119 * (Z * Z) + 243 * Z + 141 := by
  have h₁ := Nat.mul_le_mul hc (show 10 * (Z * Z) + 12 * Z + 58 + 3 * (Z * Z) + 100 * Z + 102 ≤
    13 * (Z * Z) + 112 * Z + 160 by omega)
  rw [rt_dist3 Z] at h₁
  generalize c * (10 * (Z * Z) + 12 * Z + 58 + 3 * (Z * Z) + 100 * Z + 102) = A at *
  generalize Z * (Z * Z) = Z3 at *
  generalize Z * Z = Z2 at *
  omega

theorem rt_pRows_runs {j cap N : Nat} {tt : List (Nat × Nat)} (S : Lists NK) (hs0 : small j cap tt 0)
    (hsc : ScratchEmpty S) (hX : S NX = [N]) :
    NRuns rt_pRows (rt_Pre j cap N tt S [] 0) (rt_Out j cap N tt S [] 0)
      (16 * (rowsZ j cap N tt * (rowsZ j cap N tt * rowsZ j cap N tt)) + 119 * (rowsZ j cap N tt * rowsZ j cap N tt) +
        243 * rowsZ j cap N tt + 141) := by
  have hN3 : N + 3 ≤ rowsZ j cap N tt := rt_N3_le_Z
  have hc0 : (N + 3) ^ (N + 1) ≤ rowsZ j cap N tt := by
    have := rt_cand_le_Z (j := j) (cap := cap) (N := N) (tt := tt) (k := 0) (Nat.zero_le _); rwa [candNum] at this
  generalize rowsZ j cap N tt = Z at *
  let par : List Nat := [0, 0, N + 1, 0, 0, N + 3]
  let P0 := rt_Pre j cap N tt S [] 0
  have hfree : rt_FreeOn rt_frC P0 := by
    simp only [P0, rt_Pre]
    exact rt_FreeOn_set (rt_FreeOn_set (rt_FreeOn_set (rt_FreeOn_set (rt_FreeOn_set (rt_FreeOn_set
      (rt_scratch_free hsc) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _
  have x₁ := nruns_pushZ CNT P0
  have eC : P0 CNT = [] := by simp only [P0, rt_Pre]; rt_at; rfl
  rw [eC, List.nil_append] at x₁
  have x₂ := rt_parP_runs (P0.set CNT [0]) (N := N) (by simp only [P0, rt_Pre]; rt_at; exact rt_scratch_get hsc _)
    (by simp only [P0, rt_Pre]; rt_at; exact hX)
  let P2 := (P0.set CNT [0]).set rt_PAR par
  have hfree2 : rt_FreeOn rt_frC P2 := rt_FreeOn_set (rt_FreeOn_set hfree (by decide) _) (by decide) _
  have x₃ := rt_pow_runs P2 (par := par) (Z := Z) hfree2 (by simp only [P2, P0, rt_Pre]; rt_at; exact rt_scratch_get hsc _)
    (by simp only [P2]; rt_at) rfl (by show N + 3 ≤ Z; omega) (by show N + 1 ≤ Z; omega)
    (fun t ht => by show (N + 3) ^ t ≤ Z; exact Nat.le_trans (Nat.pow_le_pow_right (by omega) ht) hc0)
  simp only [par, List.getD_cons_succ, List.getD_cons_zero] at x₃
  let R : Nat → List Nat := fun q => ((List.range q).map (rt_vec (N + 3) (N + 1))).flatten
  let C : Nat → List Nat := fun q => [q]
  have x₄ := rt_odo_runs (body := rt_emitP) P2 R C (par := par) (cnt := (N + 3) ^ (N + 1))
    (Tb := 10 * (Z * Z) + 12 * Z + 58) (Z := Z) hfree2
    (by simp only [P2, P0, rt_Pre]; rt_at; exact rt_scratch_get hsc _)
    (by simp only [P2, P0, rt_Pre]; rt_at; exact rt_scratch_get hsc _)
    (by simp only [P2, P0, rt_Pre]; rt_at; exact rt_scratch_get hsc _) (by simp only [P2]; rt_at) rfl
    (by simp [par]) (by show N + 3 ≤ Z; omega) (by show N + 1 ≤ Z; omega)
    (fun q hq => by
      let St := (((P2.set ROWS (R q)).set CNT (C q)).set rt_D (rt_vec (N + 3) (N + 1) q)).set rt_QC
        [(N + 3) ^ (N + 1) - q - 1]
      have hb := rt_emitP_runs St (par := par) (d := rt_vec (N + 3) (N + 1) q) (w := R q) (lc := []) (c := q) (Z := Z)
        (rt_FreeOn_set (rt_FreeOn_set (rt_FreeOn_set (rt_FreeOn_set hfree2 (by decide) _) (by decide) _)
          (by decide) _) (by decide) _)
        (by simp only [St, P2]; rt_at) rfl (by simp only [St]; rt_at) (by simp only [St]; rt_at)
        (by simp only [St, C]; rt_at) (by rw [rt_vec_length]; rfl)
        (by rw [rt_vec_length]; omega)
      have e : (St.set ROWS (R q ++ rt_vec (N + 3) (N + 1) q)).set CNT ([] ++ [q + 1]) =
          (((P2.set ROWS (R (q + 1))).set CNT (C (q + 1))).set rt_D (rt_vec (N + 3) (N + 1) q)).set rt_QC
            [(N + 3) ^ (N + 1) - q - 1] := by
        have hR : R (q + 1) = R q ++ rt_vec (N + 3) (N + 1) q := by
          simp [R, List.range_succ, List.map_append, List.flatten_append]
        simp only [St, hR, C, List.nil_append]
        rt_ext [ROWS, CNT, rt_D, rt_QC]
      rw [e] at hb
      exact hb)
  have e₃ : P2.set rt_QC [(N + 3) ^ (N + 1)] = ((P2.set ROWS (R 0)).set CNT (C 0)).set rt_QC [(N + 3) ^ (N + 1)] := by
    have hR0 : P2 ROWS = R 0 := by simp only [P2, P0, rt_Pre, R]; rt_at; rfl
    have hC0 : P2 CNT = C 0 := by simp only [P2, C]; rt_at
    rt_extU [ROWS, CNT, rt_QC] [hR0, hC0]
  rw [e₃] at x₃
  let P4 := (P2.set ROWS (R ((N + 3) ^ (N + 1)))).set CNT (C ((N + 3) ^ (N + 1)))
  have x₅ := nruns_clr rt_PAR P4
  have eP : P4 rt_PAR = par := by simp only [P4, P2]; rt_at
  rw [eP] at x₅
  have x₆ := nruns_dup NX rt_LEN (by decide) (P4.set rt_PAR []) (l := []) (v := N)
    (by simp only [P4, P2, P0, rt_Pre]; rt_at; exact hX)
  have eL : (P4.set rt_PAR []) rt_LEN = [] := by simp only [P4, P2, P0, rt_Pre]; rt_at; rfl
  rw [eL, List.nil_append] at x₆
  have x₇ := nruns_inc rt_LEN ((P4.set rt_PAR []).set rt_LEN [N]) (l := []) (v := N) (by simp)
  have e₇ : ((P4.set rt_PAR []).set rt_LEN [N]).set rt_LEN ([] ++ [N + 1]) = rt_Out j cap N tt S [] 0 := by
    have hz := rt_rowsT_zero (N := N) hs0
    have hlen : rt_lenE j cap N tt 0 = N + 1 := by rw [rt_lenE, if_pos hs0, valT]
    have hP : S rt_PAR = [] := rt_scratch_get hsc _
    have hl0 : (rowsT j cap N tt 0).length = (N + 3) ^ (N + 1) := by rw [hz]; simp
    simp only [P4, P2, P0, rt_Pre, rt_Out, R, C]
    rw [rt_pre_succ, ← hz]
    have hp0 : rt_pre j cap N tt 0 = [] := rfl
    simp only [rt_tb]
    rt_extU [rt_LEN, rt_PAR, CNT, ROWS, rt_KU, rt_KC, ROFF] [hP, hlen, hl0, hp0]
  rw [e₇] at x₇
  have hpl : par.length = 6 := rfl
  rw [hpl] at x₅
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq x₇)))))).mono (rt_pRows_cost hc0)

/-! ## The start of an arrow: the start of its rows -/

/-- Move to the next type number and push the start of its rows (`ROFF` + `CNT` × `LEN` of the previous one). -/
def rt_head : NProg NK :=
  .seq (.prim (.inc rt_KU)) (.seq (.prim (.dup ROFF rt_O1 (by decide))) (.seq (.prim (.dup CNT rt_V1 (by decide)))
    (.seq (.prim (.dup rt_LEN rt_V2 (by decide))) (.seq (rt_mul rt_V1 rt_V2 rt_O1 rt_P (by decide))
      (.seq (.prim (.pop rt_V2)) (nmv rt_O1 ROFF (by decide)))))))

theorem rt_tb_last (f : Nat → Nat) (k : Nat) : rt_tb f (k + 1) = rt_tb f k ++ [f k] := rt_tb_succ f k

theorem rt_head_runs {j cap N : Nat} {tt : List (Nat × Nat)} (S : Lists NK) (hw : TTWF tt) (hsc : ScratchEmpty S)
    (kc : List Nat) {m : Nat} (hm : m < tt.length) :
    NRuns rt_head (rt_Out j cap N tt S kc m) (rt_Pre j cap N tt S kc (m + 1))
      ((rowsT j cap N tt m).length * (3 * rt_lenE j cap N tt m + 7) + 9) := by
  let c := (rowsT j cap N tt m).length
  let l := rt_lenE j cap N tt m
  let o := (rt_pre j cap N tt m).length
  let O := rt_Out j cap N tt S kc m
  have hC : O CNT = rt_tb (fun t => (rowsT j cap N tt t).length) m ++ [c] := by
    simp only [O, rt_Out]; rt_at; rw [rt_tb_last]
  have hL : O rt_LEN = rt_tb (rt_lenE j cap N tt) m ++ [l] := by simp only [O, rt_Out]; rt_at; rw [rt_tb_last]
  have hR : O ROFF = rt_tb (fun t => (rt_pre j cap N tt t).length) m ++ [o] := by
    simp only [O, rt_Out]; rt_at; rw [rt_tb_last]
  have x₀ := nruns_inc rt_KU O (l := []) (v := m) (by simp only [O, rt_Out]; rt_at)
  let O₀ := O.set rt_KU ([] ++ [m + 1])
  have x₁ := nruns_dup ROFF rt_O1 (by decide) O₀ (by simp only [O₀]; rt_at; exact hR)
  have e₁ : O₀ rt_O1 = [] := by simp only [O₀, O, rt_Out]; rt_at; exact rt_scratch_get hsc _
  rw [e₁, List.nil_append] at x₁
  have x₂ := nruns_dup CNT rt_V1 (by decide) (O₀.set rt_O1 [o]) (by simp only [O₀]; rt_at; exact hC)
  have e₂ : (O₀.set rt_O1 [o]) rt_V1 = [] := by simp only [O₀, O, rt_Out]; rt_at; exact rt_scratch_get hsc _
  rw [e₂, List.nil_append] at x₂
  have x₃ := nruns_dup rt_LEN rt_V2 (by decide) ((O₀.set rt_O1 [o]).set rt_V1 [c]) (by simp only [O₀]; rt_at; exact hL)
  have e₃ : ((O₀.set rt_O1 [o]).set rt_V1 [c]) rt_V2 = [] := by
    simp only [O₀, O, rt_Out]; rt_at; exact rt_scratch_get hsc _
  rw [e₃, List.nil_append] at x₃
  let O₃ := ((O₀.set rt_O1 [o]).set rt_V1 [c]).set rt_V2 [l]
  have x₄ := rt_mul_runs (X := rt_V1) (Y := rt_V2) (A := rt_O1) (TM := rt_P) (h := by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) O₃ (lx := []) (ly := []) (la := []) (x := c) (y := l) (a := o)
    (by simp only [O₃]; rt_at) (by simp only [O₃]; rt_at) (by simp only [O₃]; rt_at)
    (by simp only [O₃, O₀, O, rt_Out]; rt_at; exact rt_scratch_get hsc _)
  let O₄ := (O₃.set rt_V1 []).set rt_O1 ([] ++ [o + c * l])
  have x₅ := nruns_pop rt_V2 O₄ (l := []) (v := l) (by simp only [O₄, O₃]; rt_at)
  have x₆ := nruns_mv rt_O1 ROFF (by decide) (O₄.set rt_V2 []) (l := []) (v := o + c * l) (by simp only [O₄]; rt_at)
  have e : ((O₄.set rt_V2 []).set ROFF ((O₄.set rt_V2 []) ROFF ++ [o + c * l])).set rt_O1 [] =
      rt_Pre j cap N tt S kc (m + 1) := by
    have hpre : (rt_pre j cap N tt (m + 1)).length = o + c * l := by
      rw [rt_pre_succ, List.length_append, rt_flat_len hw (by omega)]
    have h1 : S rt_O1 = [] := rt_scratch_get hsc _
    have h2 : S rt_V1 = [] := rt_scratch_get hsc _
    have h3 : S rt_V2 = [] := rt_scratch_get hsc _
    simp only [O₄, O₃, O₀, O, rt_Out, rt_Pre]
    rw [rt_tb_last (fun t => (rt_pre j cap N tt t).length) (m + 1), hpre]
    rt_extU [rt_O1, ROFF, rt_V2, rt_V1, rt_KU, CNT, ROWS, rt_LEN, rt_KC] [h1, h2, h3]
  rw [e] at x₆
  have hx := x₀.seq (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq x₆)))))
  simp only [c, l] at hx
  exact hx.mono (by omega)

/-! ## The parameters of an arrow -/

theorem rt_encPairs_fst (P : List (Nat × Nat)) {k : Nat} (h : k < P.length) : (encPairs P).getD (2 * k) 0 = P[k].1 := by
  rw [List.getD_eq_getElem?_getD, encPairs_fst P k h]; rfl

theorem rt_encPairs_snd (P : List (Nat × Nat)) {k : Nat} (h : k < P.length) :
    (encPairs P).getD (2 * k + 1) 0 = P[k].2 := by
  rw [List.getD_eq_getElem?_getD, encPairs_snd P k h]; rfl

/-- Read the components `a`, `b` of the arrow on `KU` from `TTs`, and push on `PAR` the start, row length and number of
rows of `a`, then of `b`. -/
def rt_parA : NProg NK :=
  .seq (.prim (.dup rt_KU rt_V1 (by decide))) (.seq (.prim (.dec rt_V1)) (.seq (.prim (.dup rt_V1 rt_V2 (by decide)))
  (.seq (addTo rt_V2 rt_V1) (.seq (rt_getAt TTs rt_V1 rt_O1 (by decide) (by decide) (by decide))
  (.seq (.prim (.inc rt_V1)) (.seq (rt_getAt TTs rt_V1 rt_O2 (by decide) (by decide) (by decide))
  (.seq (.prim (.pop rt_V1))
  (.seq (rt_getAt ROFF rt_O1 rt_PAR (by decide) (by decide) (by decide))
  (.seq (rt_getAt rt_LEN rt_O1 rt_PAR (by decide) (by decide) (by decide))
  (.seq (rt_getAt CNT rt_O1 rt_PAR (by decide) (by decide) (by decide))
  (.seq (rt_getAt ROFF rt_O2 rt_PAR (by decide) (by decide) (by decide))
  (.seq (rt_getAt rt_LEN rt_O2 rt_PAR (by decide) (by decide) (by decide))
  (.seq (rt_getAt CNT rt_O2 rt_PAR (by decide) (by decide) (by decide))
  (.seq (.prim (.pop rt_O1)) (.prim (.pop rt_O2))))))))))))))))

/-- The parameters of the arrow `k + 1`. -/
def rt_parOf (j cap N : Nat) (tt : List (Nat × Nat)) (a b : Nat) : List Nat :=
  [(rt_pre j cap N tt a).length, rt_lenE j cap N tt a, (rowsT j cap N tt a).length,
    (rt_pre j cap N tt b).length, rt_lenE j cap N tt b, (rowsT j cap N tt b).length]

theorem rt_parA_runs {j cap N : Nat} {tt : List (Nat × Nat)} (S : Lists NK) (hw : TTWF tt) (hsc : ScratchEmpty S)
    (hT : S TTs = encPairs tt) (kc : List Nat) {m : Nat} (hm : m < tt.length) :
    NRuns rt_parA (rt_Pre j cap N tt S kc (m + 1))
      ((rt_Pre j cap N tt S kc (m + 1)).set rt_PAR (rt_parOf j cap N tt tt[m].1 tt[m].2))
      (103 * tt.length + 81) := by
  have hab := hw.2 m hm
  let a := tt[m].1
  let b := tt[m].2
  let P := rt_Pre j cap N tt S kc (m + 1)
  have hTl : (encPairs tt).length = 2 * tt.length := encPairs_length tt
  have x₁ := nruns_dup rt_KU rt_V1 (by decide) P (l := []) (v := m + 1) (by simp only [P, rt_Pre]; rt_at)
  have eV1 : P rt_V1 = [] := by simp only [P, rt_Pre]; rt_at; exact rt_scratch_get hsc _
  rw [eV1, List.nil_append] at x₁
  have x₂ := nruns_dec rt_V1 (P.set rt_V1 [m + 1]) (l := []) (v := m + 1) (by simp)
  rw [Lists.set_set_u, Nat.add_sub_cancel] at x₂
  have x₃ := nruns_dup rt_V1 rt_V2 (by decide) (P.set rt_V1 ([] ++ [m])) (l := []) (v := m) (by simp)
  have eV2 : (P.set rt_V1 ([] ++ [m])) rt_V2 = [] := by simp only [P, rt_Pre]; rt_at; exact rt_scratch_get hsc _
  rw [eV2, List.nil_append] at x₃
  have x₄ := nruns_addTo rt_V2 rt_V1 (by decide) ((P.set rt_V1 ([] ++ [m])).set rt_V2 [m]) (l := []) (l' := [])
    (a := m) (b := m) (by simp) (by rt_at)
  let P₄ := ((((P.set rt_V1 ([] ++ [m])).set rt_V2 [m]).set rt_V2 []).set rt_V1 ([] ++ [m + m]))
  have eP₄ : P₄ = P.set rt_V1 [2 * m] := by
    simp only [P₄, P, rt_Pre, show m + m = 2 * m by omega, List.nil_append]
    rt_extU [rt_V1, rt_V2] [rt_scratch_get hsc rt_V2]
  rw [show ((((P.set rt_V1 ([] ++ [m])).set rt_V2 [m]).set rt_V2 []).set rt_V1 ([] ++ [m + m])) = P₄ from rfl, eP₄] at x₄
  have x₅ := rt_getAt_runs (i := TTs) (c := rt_V1) (o := rt_O1) (h₀ := by decide) (h₁ := by decide) (h₂ := by decide)
    (by decide) (by decide) (by decide) (P.set rt_V1 [2 * m]) (lc := []) (k := 2 * m) (by simp)
    (by simp only [P, rt_Pre]; rt_at; exact rt_scratch_get hsc _) (by simp only [P, rt_Pre]; rt_at; exact rt_scratch_get hsc _)
    (by simp only [P, rt_Pre]; rt_at; rw [hT, hTl]; omega)
  have eT₅ : (P.set rt_V1 [2 * m]) TTs = encPairs tt := by simp only [P, rt_Pre]; rt_at; exact hT
  have eO₅ : (P.set rt_V1 [2 * m]) rt_O1 = [] := by simp only [P, rt_Pre]; rt_at; exact rt_scratch_get hsc _
  rw [eT₅, eO₅, List.nil_append, rt_encPairs_fst tt hm, hTl] at x₅
  let P₅ := (P.set rt_V1 [2 * m]).set rt_O1 [a]
  have x₆ := nruns_inc rt_V1 P₅ (l := []) (v := 2 * m) (by simp only [P₅]; rt_at)
  let P₆ := P₅.set rt_V1 ([] ++ [2 * m + 1])
  have x₇ := rt_getAt_runs (i := TTs) (c := rt_V1) (o := rt_O2) (h₀ := by decide) (h₁ := by decide) (h₂ := by decide)
    (by decide) (by decide) (by decide) P₆ (lc := []) (k := 2 * m + 1) (by simp only [P₆]; rt_at)
    (by simp only [P₆, P₅, P, rt_Pre]; rt_at; exact rt_scratch_get hsc _)
    (by simp only [P₆, P₅, P, rt_Pre]; rt_at; exact rt_scratch_get hsc _)
    (by simp only [P₆, P₅, P, rt_Pre]; rt_at; rw [hT, hTl]; omega)
  have eT₇ : P₆ TTs = encPairs tt := by simp only [P₆, P₅, P, rt_Pre]; rt_at; exact hT
  have eO₇ : P₆ rt_O2 = [] := by simp only [P₆, P₅, P, rt_Pre]; rt_at; exact rt_scratch_get hsc _
  rw [eT₇, eO₇, List.nil_append, rt_encPairs_snd tt hm, hTl] at x₇
  have x₈ := nruns_pop rt_V1 (P₆.set rt_O2 [b]) (l := []) (v := 2 * m + 1) (by simp only [P₆]; rt_at)
  let Q := ((P₆.set rt_O2 [b]).set rt_V1 [])
  have eQ : Q = (P.set rt_O1 [a]).set rt_O2 [b] := by
    simp only [Q, P₆, P₅, P, rt_Pre, List.nil_append]
    rt_extU [rt_V1, rt_O1, rt_O2] [rt_scratch_get hsc rt_V1]
  rw [show (P₆.set rt_O2 [b]).set rt_V1 [] = Q from rfl, eQ] at x₈
  -- the six entries
  let R₀ := (P.set rt_O1 [a]).set rt_O2 [b]
  have hROFF : R₀ ROFF = rt_tb (fun t => (rt_pre j cap N tt t).length) (m + 2) := by
    simp only [R₀, P, rt_Pre]; rt_at
  have hLEN : R₀ rt_LEN = rt_tb (rt_lenE j cap N tt) (m + 1) := by simp only [R₀, P, rt_Pre]; rt_at
  have hCNT : R₀ CNT = rt_tb (fun t => (rowsT j cap N tt t).length) (m + 1) := by simp only [R₀, P, rt_Pre]; rt_at
  have hPAR : R₀ rt_PAR = [] := by simp only [R₀, P, rt_Pre]; rt_at; exact rt_scratch_get hsc _
  have hIX : ∀ v : List Nat, (R₀.set rt_PAR v) rt_IX = [] := fun v => by
    simp only [R₀, P, rt_Pre]; rt_at; exact rt_scratch_get hsc _
  have hTT : ∀ v : List Nat, (R₀.set rt_PAR v) rt_T = [] := fun v => by
    simp only [R₀, P, rt_Pre]; rt_at; exact rt_scratch_get hsc _
  have get : ∀ (i : Fin NK) (c : Fin NK) (h₀ : c ≠ rt_IX) (h₁ : i ≠ rt_T) (t : Nat) (v : List Nat),
      [i, rt_T, rt_IX, rt_PAR].Nodup → i ≠ rt_IX → i ≠ rt_PAR → c ≠ rt_PAR → R₀ c = [t] →
      t < (R₀ i).length →
      NRuns (rt_getAt i c rt_PAR h₀ h₁ (by decide)) (R₀.set rt_PAR v) (R₀.set rt_PAR (v ++ [(R₀ i).getD t 0]))
        (6 * (R₀ i).length + 4 * t + 7) := by
    intro i c h₀ h₁ t v hd hiX hiP hcP hc ht
    have := rt_getAt_runs (i := i) (c := c) (o := rt_PAR) (h₀ := h₀) (h₁ := h₁) (h₂ := by decide) hd hiX (by decide)
      (R₀.set rt_PAR v) (lc := []) (k := t) (by rw [Lists.set_ne _ _ hcP]; exact hc) (hIX v) (hTT v)
      (by rw [Lists.set_ne _ _ hiP]; exact ht)
    rw [Lists.set_ne _ _ hiP, Lists.set_set_u, Lists.set_same] at this
    exact this
  have hO1 : R₀ rt_O1 = [a] := by simp only [R₀]; rt_at
  have hO2 : R₀ rt_O2 = [b] := by simp only [R₀]; rt_at
  have lR := rt_tb_length (fun t => (rt_pre j cap N tt t).length) (m + 2)
  have lL := rt_tb_length (rt_lenE j cap N tt) (m + 1)
  have lC := rt_tb_length (fun t => (rowsT j cap N tt t).length) (m + 1)
  have y₁ := get ROFF rt_O1 (by decide) (by decide) a [] (by decide) (by decide) (by decide) (by decide) hO1
    (by rw [hROFF, lR]; omega)
  rw [hROFF, rt_tb_getD _ (by omega), lR, List.nil_append] at y₁
  have y₂ := get rt_LEN rt_O1 (by decide) (by decide) a [(rt_pre j cap N tt a).length] (by decide) (by decide)
    (by decide) (by decide) hO1 (by rw [hLEN, lL]; omega)
  rw [hLEN, rt_tb_getD _ (by omega), lL] at y₂
  have y₃ := get CNT rt_O1 (by decide) (by decide) a [(rt_pre j cap N tt a).length, rt_lenE j cap N tt a] (by decide)
    (by decide) (by decide) (by decide) hO1 (by rw [hCNT, lC]; omega)
  rw [hCNT, rt_tb_getD _ (by omega), lC] at y₃
  have y₄ := get ROFF rt_O2 (by decide) (by decide) b [(rt_pre j cap N tt a).length, rt_lenE j cap N tt a,
    (rowsT j cap N tt a).length] (by decide) (by decide) (by decide) (by decide) hO2 (by rw [hROFF, lR]; omega)
  rw [hROFF, rt_tb_getD _ (by omega), lR] at y₄
  have y₅ := get rt_LEN rt_O2 (by decide) (by decide) b [(rt_pre j cap N tt a).length, rt_lenE j cap N tt a,
    (rowsT j cap N tt a).length, (rt_pre j cap N tt b).length] (by decide) (by decide) (by decide) (by decide) hO2
    (by rw [hLEN, lL]; omega)
  rw [hLEN, rt_tb_getD _ (by omega), lL] at y₅
  have y₆ := get CNT rt_O2 (by decide) (by decide) b [(rt_pre j cap N tt a).length, rt_lenE j cap N tt a,
    (rowsT j cap N tt a).length, (rt_pre j cap N tt b).length, rt_lenE j cap N tt b] (by decide) (by decide)
    (by decide) (by decide) hO2 (by rw [hCNT, lC]; omega)
  rw [hCNT, rt_tb_getD _ (by omega), lC] at y₆
  simp only [List.cons_append, List.nil_append] at y₂ y₃ y₄ y₅ y₆
  have x₈' : NRuns (.prim (.pop rt_V1)) (P₆.set rt_O2 [b]) (R₀.set rt_PAR []) 1 := by
    rw [set_nil_self hPAR]; exact x₈
  have z₁ := nruns_pop rt_O1 (R₀.set rt_PAR (rt_parOf j cap N tt a b)) (l := []) (v := a) (by rt_at; exact hO1)
  have z₂ := nruns_pop rt_O2 ((R₀.set rt_PAR (rt_parOf j cap N tt a b)).set rt_O1 []) (l := []) (v := b)
    (by rt_at; exact hO2)
  have e : ((R₀.set rt_PAR (rt_parOf j cap N tt a b)).set rt_O1 []).set rt_O2 [] =
      P.set rt_PAR (rt_parOf j cap N tt a b) := by
    simp only [R₀, P, rt_Pre]
    rt_extU [rt_O1, rt_O2, rt_PAR] [rt_scratch_get hsc rt_O1, rt_scratch_get hsc rt_O2]
  rw [e] at z₂
  have hy := y₁.seq (y₂.seq (y₃.seq (y₄.seq (y₅.seq (y₆.seq (z₁.seq z₂))))))
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq (x₇.seq (x₈'.seq hy)))))))).mono (by omega)

/-! ## The candidates of an arrow, as lists -/

/-- Candidate `q` of an arrow whose domain has `ca` rows and codomain has the rows `Bs`. -/
def rt_cand (Bs : List (List Nat)) (ca q : Nat) : List (List Nat) :=
  (rt_vec Bs.length ca q).map (fun x => Bs.getD x [])

/-- All candidates, in order. -/
def rt_cands (Bs : List (List Nat)) (ca : Nat) : List (List (List Nat)) :=
  (List.range (Bs.length ^ ca)).map (rt_cand Bs ca)

/-- The candidates kept among the first `q`. -/
def rt_kept (A Bs : List (List Nat)) (q : Nat) : List (List (List Nat)) :=
  ((rt_cands Bs A.length).take q).filter (monoC A)

theorem rt_kept_succ (A Bs : List (List Nat)) {q : Nat} (hq : q < Bs.length ^ A.length) :
    rt_kept A Bs (q + 1) = rt_kept A Bs q ++ (if monoC A (rt_cand Bs A.length q) then [rt_cand Bs A.length q] else []) := by
  have hl : q < (rt_cands Bs A.length).length := by simp [rt_cands, hq]
  unfold rt_kept
  rw [List.take_succ_eq_append_getElem hl, List.filter_append]
  congr 1
  have : (rt_cands Bs A.length)[q] = rt_cand Bs A.length q := by simp [rt_cands]
  rw [this]
  simp only [List.filter_cons, List.filter_nil]

theorem rt_kept_prefix (A Bs : List (List Nat)) (q : Nat) :
    ∃ Y, rt_kept A Bs q ++ Y = (rt_cands Bs A.length).filter (monoC A) := by
  refine ⟨((rt_cands Bs A.length).drop q).filter (monoC A), ?_⟩
  unfold rt_kept
  rw [← List.filter_append, List.take_append_drop]

theorem rt_kept_full (A Bs : List (List Nat)) :
    rt_kept A Bs (Bs.length ^ A.length) = (rt_cands Bs A.length).filter (monoC A) := by
  unfold rt_kept
  rw [List.take_of_length_le (by simp [rt_cands])]

theorem rt_cand_length (Bs : List (List Nat)) (ca q : Nat) : (rt_cand Bs ca q).length = ca := by
  simp [rt_cand, rt_vec_length]

theorem rt_cand_getD (Bs : List (List Nat)) (ca q : Nat) {i : Nat} (hi : i < ca) :
    (rt_cand Bs ca q).getD i [] = Bs.getD ((rt_vec Bs.length ca q).getD i 0) [] := by
  have hl : i < (rt_vec Bs.length ca q).length := by rw [rt_vec_length]; exact hi
  simp [rt_cand, List.getD_eq_getElem?_getD, hl]

theorem rt_monoC_range (A F : List (List Nat)) {n : Nat} (hA : A.length = n) (hF : F.length = n) :
    monoC A F = (List.range n).all (fun i => (List.range n).all (fun i' =>
      !leC (A.getD i []) (A.getD i' []) || leC (F.getD i []) (F.getD i' []))) := by
  have hz : A.zip F = (List.range n).map (fun i => (A.getD i [], F.getD i [])) := by
    apply List.ext_getElem
    · simp [hA, hF]
    · intro i h₁ h₂
      have hi : i < n := by simpa using h₂
      simp [List.getElem_zip, List.getD_eq_getElem?_getD, hA, hF, hi]
  unfold monoC
  rw [hz, List.all_map]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [List.all_map]
  rfl

theorem rt_flatMap_getD (F : List (List Nat)) : (List.range F.length).flatMap (fun i => F.getD i []) = F.flatten := by
  rw [List.flatMap_def, rt_map_getD]

theorem rt_all_congr {f g : Nat → Bool} {n : Nat} (h : ∀ i, i < n → f i = g i) :
    (List.range n).all f = (List.range n).all g :=
  all_congr_mem _ (fun i hi => h i (List.mem_range.1 hi))

theorem rt_flatMap_congr {f g : Nat → List Nat} {n : Nat} (h : ∀ i, i < n → f i = g i) :
    (List.range n).flatMap f = (List.range n).flatMap g := by
  rw [List.flatMap_def, List.flatMap_def, List.map_congr_left (fun i hi => h i (List.mem_range.1 hi))]

/-- Push on `LEN` the row length of the arrow: entry `2` times entry `4` of `PAR`. -/
def rt_lenA : NProg NK :=
  .seq (rt_get rt_PAR rt_V1 2 (by decide) (by decide)) (.seq (rt_get rt_PAR rt_V2 4 (by decide) (by decide))
    (.seq (.prim (.pushZ rt_O1)) (.seq (rt_mul rt_V1 rt_V2 rt_O1 rt_P (by decide)) (.seq (.prim (.pop rt_V2))
      (nmv rt_O1 rt_LEN (by decide))))))

theorem rt_lenA_runs (S : Lists NK) {par l : List Nat} (hfree : rt_FreeOn rt_frC S) (hpar : S rt_PAR = par)
    (hpl : par.length = 6) (hL : S rt_LEN = l) :
    NRuns rt_lenA S (S.set rt_LEN (l ++ [par.getD 2 0 * par.getD 4 0]))
      (par.getD 2 0 * (3 * par.getD 4 0 + 7) + 122) := by
  have x₁ := rt_get_runs (i := rt_PAR) (o := rt_V1) (h₁ := by decide) (h₂ := by decide) (by decide) (by decide)
    (by decide) S 2 (rt_FreeOn_get hfree) (rt_FreeOn_get hfree) (by rw [hpar, hpl]; omega)
  rw [rt_FreeOn_get hfree, List.nil_append, hpar, hpl] at x₁
  let S₁ := S.set rt_V1 [par.getD 2 0]
  have x₂ := rt_get_runs (i := rt_PAR) (o := rt_V2) (h₁ := by decide) (h₂ := by decide) (by decide) (by decide)
    (by decide) S₁ 4 (by simp only [S₁]; rt_at; exact rt_FreeOn_get hfree)
    (by simp only [S₁]; rt_at; exact rt_FreeOn_get hfree) (by simp only [S₁]; rt_at; rw [hpar, hpl]; omega)
  have e₂ : S₁ rt_PAR = par := by simp only [S₁]; rt_at; exact hpar
  have e₂' : S₁ rt_V2 = [] := by simp only [S₁]; rt_at; exact rt_FreeOn_get hfree
  rw [e₂, e₂', List.nil_append, hpl] at x₂
  let S₂ := S₁.set rt_V2 [par.getD 4 0]
  have x₃ := nruns_pushZ rt_O1 S₂
  have e₃ : S₂ rt_O1 = [] := by simp only [S₂, S₁]; rt_at; exact rt_FreeOn_get hfree
  rw [e₃, List.nil_append] at x₃
  let S₃ := S₂.set rt_O1 [0]
  have x₄ := rt_mul_runs (X := rt_V1) (Y := rt_V2) (A := rt_O1) (TM := rt_P) (h := by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) S₃ (lx := []) (ly := []) (la := []) (x := par.getD 2 0) (y := par.getD 4 0) (a := 0)
    (by simp only [S₃, S₂, S₁]; rt_at) (by simp only [S₃, S₂]; rt_at) (by simp only [S₃]; rt_at)
    (by simp only [S₃, S₂, S₁]; rt_at; exact rt_FreeOn_get hfree)
  let S₄ := (S₃.set rt_V1 []).set rt_O1 ([] ++ [0 + par.getD 2 0 * par.getD 4 0])
  have x₅ := nruns_pop rt_V2 S₄ (l := []) (v := par.getD 4 0) (by simp only [S₄, S₃, S₂]; rt_at)
  have x₆ := nruns_mv rt_O1 rt_LEN (by decide) (S₄.set rt_V2 []) (l := []) (v := 0 + par.getD 2 0 * par.getD 4 0)
    (by simp only [S₄]; rt_at)
  have e : ((S₄.set rt_V2 []).set rt_LEN ((S₄.set rt_V2 []) rt_LEN ++ [0 + par.getD 2 0 * par.getD 4 0])).set rt_O1 [] =
      S.set rt_LEN (l ++ [par.getD 2 0 * par.getD 4 0]) := by
    have h1 : S rt_V1 = [] := rt_FreeOn_get hfree
    have h2 : S rt_V2 = [] := rt_FreeOn_get hfree
    have h3 : S rt_O1 = [] := rt_FreeOn_get hfree
    simp only [S₄, S₃, S₂, S₁, Nat.zero_add]
    rt_extU [rt_V1, rt_V2, rt_O1, rt_LEN] [h1, h2, h3, hL]
  rw [e] at x₆
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq x₆))))).mono (by omega)

/-! ## Reading the rows of an arrow's components -/

section ArrowRead

variable {j cap N : Nat} {tt : List (Nat × Nat)}

theorem rt_vec_getD_lt {B m q i : Nat} (hB : 1 ≤ B) (hi : i < m) : (rt_vec B m q).getD i 0 < B := by
  have hl : i < (rt_vec B m q).length := by rw [rt_vec_length]; exact hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  exact rt_dig_lt (by omega) m q _ (List.mem_reverse.1 (List.getElem_mem hl))

theorem rt_vec_mem_lt {B m q v : Nat} (hB : 1 ≤ B) (hv : v ∈ rt_vec B m q) : v < B :=
  rt_dig_lt (by omega) m q v (List.mem_reverse.1 hv)

theorem rt_pre_len_mono {t k : Nat} (h : t ≤ k) : (rt_pre j cap N tt t).length ≤ (rt_pre j cap N tt k).length := by
  obtain ⟨X, hX⟩ := rt_pre_add (j := j) (cap := cap) (N := N) (tt := tt) t (k - t)
  rw [show t + (k - t) = k by omega] at hX
  rw [hX, List.length_append]; omega

/-- The rows of type `t`, all inside the rows written before `k`. -/
theorem rt_rows_inside (hw : TTWF tt) {t k i : Nat} (htk : t < k) (ht : t ≤ tt.length)
    (hi : i < (rowsT j cap N tt t).length) (e : List Nat) :
    (rt_pre j cap N tt t).length + i * rt_lenE j cap N tt t + rt_lenE j cap N tt t ≤ (rt_pre j cap N tt k ++ e).length := by
  have h₁ := rt_pre_len_mono (j := j) (cap := cap) (N := N) (tt := tt) (show t + 1 ≤ k by omega)
  rw [rt_pre_succ, List.length_append, rt_flat_len hw ht] at h₁
  have h₂ := Nat.mul_le_mul_right (rt_lenE j cap N tt t) (show i + 1 ≤ (rowsT j cap N tt t).length by omega)
  rw [Nat.succ_mul] at h₂
  simp only [List.length_append]
  omega

theorem rt_segA (hw : TTWF tt) {t k i : Nat} (htk : t < k) (ht : t ≤ tt.length) (hi : i < (rowsT j cap N tt t).length)
    (e : List Nat) :
    rt_segOf (rt_pre j cap N tt k ++ e) (rt_pre j cap N tt t).length (rt_lenE j cap N tt t) i =
      (rowsT j cap N tt t).getD i [] := by
  unfold rt_segOf
  rw [rt_seg hw htk ht hi e, List.getElem_eq_getD []]

theorem rt_monoOK_eq (hw : TTWF tt) {k a b : Nat} (hak : a < k) (hbk : b < k) (han : a ≤ tt.length)
    (hbn : b ≤ tt.length) (hcb : 1 ≤ (rowsT j cap N tt b).length) (e : List Nat) (q : Nat) :
    rt_monoOK (rt_pre j cap N tt k ++ e) (rt_parOf j cap N tt a b)
      (rt_vec (rowsT j cap N tt b).length (rowsT j cap N tt a).length q) =
      monoC (rowsT j cap N tt a) (rt_cand (rowsT j cap N tt b) (rowsT j cap N tt a).length q) := by
  unfold rt_monoOK
  rw [rt_vec_length, rt_monoC_range _ _ rfl (rt_cand_length _ _ _)]
  apply rt_all_congr; intro i hi
  apply rt_all_congr; intro i' hi'
  unfold rt_pairOK
  simp only [rt_parOf, List.getD_cons_succ, List.getD_cons_zero]
  rw [rt_segA hw hak han hi, rt_segA hw hak han hi', rt_cand_getD _ _ _ hi, rt_cand_getD _ _ _ hi',
    rt_segA hw hbk hbn (rt_vec_getD_lt hcb hi), rt_segA hw hbk hbn (rt_vec_getD_lt hcb hi')]

theorem rt_out_eq (hw : TTWF tt) {k a b : Nat} (hbk : b < k) (hbn : b ≤ tt.length)
    (hcb : 1 ≤ (rowsT j cap N tt b).length) (e : List Nat) (q : Nat) :
    rt_out (rt_pre j cap N tt k ++ e) (rt_parOf j cap N tt a b)
      (rt_vec (rowsT j cap N tt b).length (rowsT j cap N tt a).length q) =
      (rt_cand (rowsT j cap N tt b) (rowsT j cap N tt a).length q).flatten := by
  unfold rt_out
  rw [rt_vec_length, ← rt_flatMap_getD, rt_cand_length]
  apply rt_flatMap_congr; intro i hi
  simp only [rt_parOf, List.getD_cons_succ, List.getD_cons_zero]
  rw [rt_cand_getD _ _ _ hi, rt_segA hw hbk hbn (rt_vec_getD_lt hcb hi)]

end ArrowRead

/-! ## The rows of an arrow -/

/-- Tabulate the rows of the arrow on `KU` (small). -/
def rt_aRows : NProg NK :=
  .seq rt_parA (.seq (.prim (.pushZ CNT)) (.seq rt_pow (.seq (rt_odo rt_aBody) (.seq rt_lenA (nclr rt_PAR)))))

theorem rt_dist5 (Z a b c d e W V U T : Nat) :
    Z * (a * W + b * V + c * U + d * T + e) = a * (Z * W) + b * (Z * V) + c * (Z * U) + d * (Z * T) + e * Z := by
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_left_comm Z a, Nat.mul_left_comm Z b,
    Nat.mul_left_comm Z c, Nat.mul_left_comm Z d, Nat.mul_comm Z e]

theorem rt_aRows_cost {c ca lb n Z : Nat} (hc : c ≤ Z) (hca : ca ≤ Z) (hlb : lb ≤ Z) (hn : n ≤ Z) :
    103 * n + 81 + (1 + (3 * (Z * (Z * Z)) + 7 * (Z * Z) + 78 * Z + 57 +
      (c * (92 * (Z * (Z * (Z * Z))) + 145 * (Z * (Z * Z)) + 876 * (Z * Z) + 323 * Z + 117 + 3 * (Z * Z) + 100 * Z +
        102) + 5 * Z + 58 + (ca * (3 * lb + 7) + 122 + (2 * 6 + 1))))) ≤
      92 * (Z * (Z * (Z * (Z * Z)))) + 145 * (Z * (Z * (Z * Z))) + 882 * (Z * (Z * Z)) + 433 * (Z * Z) + 412 * Z + 332 := by
  have h₁ := Nat.mul_le_mul hc (show 92 * (Z * (Z * (Z * Z))) + 145 * (Z * (Z * Z)) + 876 * (Z * Z) + 323 * Z + 117 +
    3 * (Z * Z) + 100 * Z + 102 ≤ 92 * (Z * (Z * (Z * Z))) + 145 * (Z * (Z * Z)) + 879 * (Z * Z) + 423 * Z + 219 by omega)
  have h₂ : Z * (92 * (Z * (Z * (Z * Z))) + 145 * (Z * (Z * Z)) + 879 * (Z * Z) + 423 * Z + 219) =
      92 * (Z * (Z * (Z * (Z * Z)))) + 145 * (Z * (Z * (Z * Z))) + 879 * (Z * (Z * Z)) + 423 * (Z * Z) + 219 * Z := by
    rw [rt_dist5 Z]
  have h₃ := rt_mul_bound hca hlb 3 7
  generalize c * (92 * (Z * (Z * (Z * Z))) + 145 * (Z * (Z * Z)) + 876 * (Z * Z) + 323 * Z + 117 + 3 * (Z * Z) +
    100 * Z + 102) = A at *
  generalize ca * (3 * lb + 7) = B at *
  generalize Z * (Z * (Z * (Z * Z))) = Z5 at *
  generalize Z * (Z * (Z * Z)) = Z4 at *
  generalize Z * (Z * Z) = Z3 at *
  generalize Z * Z = Z2 at *
  omega

theorem rt_aRows_runs {j cap N : Nat} {tt : List (Nat × Nat)} (S : Lists NK) (hw : TTWF tt) (hsc : ScratchEmpty S)
    (hT : S TTs = encPairs tt) (kc : List Nat) {m : Nat} (hm : m < tt.length) (hs : small j cap tt (m + 1)) :
    NRuns rt_aRows (rt_Pre j cap N tt S kc (m + 1)) (rt_Out j cap N tt S kc (m + 1))
      (92 * (rowsZ j cap N tt * (rowsZ j cap N tt * (rowsZ j cap N tt * (rowsZ j cap N tt * rowsZ j cap N tt)))) +
        145 * (rowsZ j cap N tt * (rowsZ j cap N tt * (rowsZ j cap N tt * rowsZ j cap N tt))) +
        882 * (rowsZ j cap N tt * (rowsZ j cap N tt * rowsZ j cap N tt)) + 433 * (rowsZ j cap N tt * rowsZ j cap N tt) +
        412 * rowsZ j cap N tt + 332) := by
  have hab := hw.2 m hm
  obtain ⟨ha, hb⟩ := rt_small_arrow hw hm hs
  -- the data of the arrow
  have hcb : 1 ≤ (rowsT j cap N tt tt[m].2).length := by
    rw [rt_rowsT_small hb]
    have := rt_rowsNum_ne (N := N) hw tt[m].2 (by omega)
    cases h : rowsNum N tt tt[m].2 with
    | nil => exact absurd h this
    | cons _ _ => simp
  have hcand : candNum j cap N tt (m + 1) =
      (rowsT j cap N tt tt[m].2).length ^ (rowsT j cap N tt tt[m].1).length := by
    rw [candNum]; simp only [rt_getElem? hm, if_pos hs]
  have hcZ := rt_cand_le_Z (j := j) (cap := cap) (N := N) (tt := tt) (k := m + 1) (by omega)
  rw [hcand] at hcZ
  have hcaZ := rt_cnt_le_Z (j := j) (cap := cap) (N := N) hw (k := tt[m].1) (by omega)
  have hcbZ := rt_cnt_le_Z (j := j) (cap := cap) (N := N) hw (k := tt[m].2) (by omega)
  have hlaZ := rt_lenE_le_Z (j := j) (cap := cap) (N := N) hw (k := tt[m].1) (by omega)
  have hlbZ := rt_lenE_le_Z (j := j) (cap := cap) (N := N) hw (k := tt[m].2) (by omega)
  have hnZ : tt.length ≤ rowsZ j cap N tt := by have := rt_Z_ge (j := j) (cap := cap) (N := N) (tt := tt); omega
  have hpre : ∀ w X, w ++ X = rowsFlat j cap N tt → w.length ≤ rowsZ j cap N tt ∧ ∀ v ∈ w, v ≤ rowsZ j cap N tt :=
    fun w X h => rt_prefix_bounds hw h
  generalize rowsZ j cap N tt = Z at *
  let A := rowsT j cap N tt tt[m].1
  let Bs := rowsT j cap N tt tt[m].2
  let par := rt_parOf j cap N tt tt[m].1 tt[m].2
  have hpl : par.length = 6 := rfl
  have hp2 : par.getD 2 0 = A.length := rfl
  have hp5 : par.getD 5 0 = Bs.length := rfl
  let P := rt_Pre j cap N tt S kc (m + 1)
  have hfree : rt_FreeOn rt_frC P := by
    simp only [P, rt_Pre]
    exact rt_FreeOn_set (rt_FreeOn_set (rt_FreeOn_set (rt_FreeOn_set (rt_FreeOn_set (rt_FreeOn_set
      (rt_scratch_free hsc) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _
  -- parameters, count, and the number of candidates
  have x₁ := rt_parA_runs (j := j) (cap := cap) (N := N) S hw hsc hT kc hm
  let P₁ := P.set rt_PAR par
  have hfree₁ : rt_FreeOn rt_frC P₁ := rt_FreeOn_set hfree (by decide) _
  have x₂ := nruns_pushZ CNT P₁
  have eC : P₁ CNT = rt_tb (fun t => (rowsT j cap N tt t).length) (m + 1) := by simp only [P₁, P, rt_Pre]; rt_at
  rw [eC] at x₂
  let P₂ := P₁.set CNT (rt_tb (fun t => (rowsT j cap N tt t).length) (m + 1) ++ [0])
  have x₃ := rt_pow_runs P₂ (par := par) (Z := Z) (rt_FreeOn_set hfree₁ (by decide) _)
    (by simp only [P₂, P₁, P, rt_Pre]; rt_at; exact rt_scratch_get hsc _) (by simp only [P₂, P₁]; rt_at) hpl
    (by rw [hp5]; exact hcbZ) (by rw [hp2]; exact hcaZ)
    (fun t ht => by
      rw [hp5]; rw [hp2] at ht
      exact Nat.le_trans (Nat.pow_le_pow_right hcb ht) hcZ)
  rw [hp5, hp2] at x₃
  -- the odometer
  let R : Nat → List Nat := fun q => rt_pre j cap N tt (m + 1) ++ ((rt_kept A Bs q).map List.flatten).flatten
  let C : Nat → List Nat := fun q => rt_tb (fun t => (rowsT j cap N tt t).length) (m + 1) ++ [(rt_kept A Bs q).length]
  have hRpre : ∀ q, ∃ X, R q ++ X = rowsFlat j cap N tt := by
    intro q
    obtain ⟨Y, hY⟩ := rt_kept_prefix A Bs q
    obtain ⟨X, hX⟩ := rt_pre_prefix (j := j) (cap := cap) (N := N) (tt := tt) (k := m + 2) (by omega)
    refine ⟨(Y.map List.flatten).flatten ++ X, ?_⟩
    have harr := rt_rowsT_arrow (j := j) (cap := cap) (N := N) hw hm hs
    calc R q ++ ((Y.map List.flatten).flatten ++ X)
        = rt_pre j cap N tt (m + 1) ++ (((rt_kept A Bs q ++ Y).map List.flatten).flatten ++ X) := by
          simp only [R, List.map_append, List.flatten_append, List.append_assoc]
      _ = rt_pre j cap N tt (m + 1) ++ ((rowsT j cap N tt (m + 1)).flatten ++ X) := by rw [hY, harr]; rfl
      _ = rowsFlat j cap N tt := by rw [← List.append_assoc, ← rt_pre_succ, hX]
  have x₄ := rt_odo_runs (body := rt_aBody) P₁ R C (par := par) (cnt := Bs.length ^ A.length)
    (Tb := 92 * (Z * (Z * (Z * Z))) + 145 * (Z * (Z * Z)) + 876 * (Z * Z) + 323 * Z + 117) (Z := Z) hfree₁
    (by simp only [P₁, P, rt_Pre]; rt_at; exact rt_scratch_get hsc _)
    (by simp only [P₁, P, rt_Pre]; rt_at; exact rt_scratch_get hsc _)
    (by simp only [P₁, P, rt_Pre]; rt_at; exact rt_scratch_get hsc _) (by simp only [P₁]; rt_at) hpl
    (Or.inl (by rw [hp5]; exact hcb)) (by rw [hp5]; exact hcbZ) (by rw [hp2]; exact hcaZ)
    (fun q hq => by
      rw [hp5, hp2]
      let d := rt_vec Bs.length A.length q
      let St := (((P₁.set ROWS (R q)).set CNT (C q)).set rt_D d).set rt_QC [Bs.length ^ A.length - q - 1]
      have hok := rt_monoOK_eq (j := j) (cap := cap) (N := N) hw (k := m + 1) (a := tt[m].1) (b := tt[m].2)
        (by omega) (by omega) (by omega) (by omega) hcb ((rt_kept A Bs q).map List.flatten).flatten q
      have hout := rt_out_eq (j := j) (cap := cap) (N := N) hw (k := m + 1) (a := tt[m].1) (b := tt[m].2)
        (by omega) (by omega) hcb ((rt_kept A Bs q).map List.flatten).flatten q
      have hsucc := rt_kept_succ A Bs hq
      have hRs : R (q + 1) = R q ++ (if monoC A (rt_cand Bs A.length q) then (rt_cand Bs A.length q).flatten else []) := by
        simp only [R, hsucc, List.map_append, List.flatten_append, List.append_assoc]
        split <;> simp
      have hCs : C (q + 1) = rt_tb (fun t => (rowsT j cap N tt t).length) (m + 1) ++
          [(rt_kept A Bs q).length + if monoC A (rt_cand Bs A.length q) then 1 else 0] := by
        simp only [C, hsucc, List.length_append]
        split <;> simp
      obtain ⟨X, hX⟩ := hRpre q
      obtain ⟨X', hX'⟩ := hRpre (q + 1)
      have hb := rt_aBody_runs St (par := par) (d := d) (w := R q)
        (lc := rt_tb (fun t => (rowsT j cap N tt t).length) (m + 1)) (c := (rt_kept A Bs q).length) (Z := Z)
        (rt_FreeOn_set (rt_FreeOn_set (rt_FreeOn_set (rt_FreeOn_set hfree₁ (by decide) _) (by decide) _)
          (by decide) _) (by decide) _)
        (by simp only [St, P₁]; rt_at) hpl (by simp only [St]; rt_at) (by simp only [St]; rt_at)
        (by simp only [St]; rt_at; rfl) (by simp only [St, P₁, P, rt_Pre]; rt_at; exact rt_scratch_get hsc _)
        (by rw [hp2]; exact rt_vec_length _ _ _)
        (fun i hi => by
          rw [rt_vec_length] at hi
          exact rt_rows_inside hw (k := m + 1) (by omega) (by omega) hi _)
        (fun i hi => by
          rw [rt_vec_length] at hi
          exact rt_rows_inside hw (k := m + 1) (by omega) (by omega) (rt_vec_getD_lt hcb hi) _)
        (hpre _ _ hX).1
        (fun hm' => by
          have : R q ++ rt_out (R q) par d = R (q + 1) := by
            rw [hRs]; simp only [R] at hm' ⊢; rw [hok] at hm'; rw [hout, if_pos hm']
          rw [this]; exact (hpre _ _ hX').1)
        (hpre _ _ hX).2 (by show rt_lenE j cap N tt tt[m].1 ≤ Z; exact hlaZ)
        (by show rt_lenE j cap N tt tt[m].2 ≤ Z; exact hlbZ) (by rw [rt_vec_length]; exact hcaZ)
        (fun v hv => Nat.le_of_lt (Nat.lt_of_lt_of_le (rt_vec_mem_lt hcb hv) hcbZ))
      have e : (St.set ROWS (R q ++ if rt_monoOK (R q) par d then rt_out (R q) par d else [])).set CNT
          (rt_tb (fun t => (rowsT j cap N tt t).length) (m + 1) ++
            [(rt_kept A Bs q).length + if rt_monoOK (R q) par d then 1 else 0]) =
          (((P₁.set ROWS (R (q + 1))).set CNT (C (q + 1))).set rt_D d).set rt_QC [Bs.length ^ A.length - q - 1] := by
        have h₁ : rt_monoOK (R q) par d = monoC A (rt_cand Bs A.length q) := hok
        have h₂ : rt_out (R q) par d = (rt_cand Bs A.length q).flatten := hout
        rw [h₁, h₂, hRs, hCs]
        simp only [St]
        rt_ext [ROWS, CNT, rt_D, rt_QC]
      rw [e] at hb
      exact hb)
  have e₃ : P₂.set rt_QC [Bs.length ^ A.length] = ((P₁.set ROWS (R 0)).set CNT (C 0)).set rt_QC [Bs.length ^ A.length] := by
    have hk0 : rt_kept A Bs 0 = [] := by simp [rt_kept]
    have hR0 : P₁ ROWS = R 0 := by simp only [P₁, P, rt_Pre, R, hk0]; rt_at; simp
    simp only [P₂, C, hk0, List.length_nil]
    rt_extU [ROWS, CNT, rt_QC] [hR0]
  rw [e₃] at x₃
  -- after the odometer
  let P₄ := (P₁.set ROWS (R (Bs.length ^ A.length))).set CNT (C (Bs.length ^ A.length))
  have x₅ := rt_lenA_runs P₄ (par := par) (l := rt_tb (rt_lenE j cap N tt) (m + 1))
    (rt_FreeOn_set (rt_FreeOn_set hfree₁ (by decide) _) (by decide) _) (by simp only [P₄, P₁]; rt_at) hpl
    (by simp only [P₄, P₁, P, rt_Pre]; rt_at)
  rw [hp2] at x₅
  let P₅ := P₄.set rt_LEN (rt_tb (rt_lenE j cap N tt) (m + 1) ++ [A.length * par.getD 4 0])
  have x₆ := nruns_clr rt_PAR P₅
  have eP₅ : P₅ rt_PAR = par := by simp only [P₅, P₄, P₁]; rt_at
  rw [eP₅, hpl] at x₆
  have e₆ : P₅.set rt_PAR [] = rt_Out j cap N tt S kc (m + 1) := by
    have harr := rt_rowsT_arrow (j := j) (cap := cap) (N := N) hw hm hs
    have hfull := rt_kept_full A Bs
    have hlen : rt_lenE j cap N tt (m + 1) = A.length * par.getD 4 0 := by
      show rt_lenE j cap N tt (m + 1) = A.length * rt_lenE j cap N tt tt[m].2
      rw [rt_lenE, if_pos hs, rt_valT_succ hw hm, rt_lenE, if_pos hb]
    have hP : S rt_PAR = [] := rt_scratch_get hsc _
    have hRf : R (Bs.length ^ A.length) = rt_pre j cap N tt (m + 1 + 1) := by
      simp only [R]; rw [hfull, rt_pre_succ (k := m + 1), harr]; rfl
    have hCf : C (Bs.length ^ A.length) = rt_tb (fun t => (rowsT j cap N tt t).length) (m + 1 + 1) := by
      simp only [C]
      rw [hfull, show rt_tb (fun t => (rowsT j cap N tt t).length) (m + 1 + 1) =
        rt_tb (fun t => (rowsT j cap N tt t).length) (m + 1) ++ [(rowsT j cap N tt (m + 1)).length] from rt_tb_succ _ _,
        harr, List.length_map]
      rfl
    simp only [P₅, P₄, P₁, P, rt_Pre, rt_Out, hRf, hCf]
    rw [rt_tb_succ (rt_lenE j cap N tt) (m + 1), hlen]
    rt_extU [rt_PAR, rt_LEN, CNT, ROWS, ROFF, rt_KU, rt_KC] [hP]
  rw [e₆] at x₆
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq x₆))))).mono (rt_aRows_cost hcZ hcaZ hlbZ hnZ)

/-! ## The whole table -/

/-- **The tables of rows**: for every type number in order, its rows (when small), their number and their start. -/
def rowsTableP (j : Nat) : NProg NK :=
  .seq (.prim (.pushZ ROFF)) (.seq (.prim (.pushZ rt_KU)) (.seq (rt_ifSmall j rt_pRows rt_noRows)
    (.seq (.prim (.dup NTT rt_KC (by decide))) (.seq (rt_for rt_KC (.seq rt_head (rt_ifSmall j rt_aRows rt_noRows)))
      (.seq (.prim (.pop rt_KU)) (nclr rt_LEN))))))

theorem rt_ordNum_le (tt : List (Nat × Nat)) : ∀ k, ordNum tt k ≤ k
  | 0 => by rw [ordNum]; exact Nat.le_refl _
  | k + 1 => by
    rw [ordNum]
    split
    · rename_i a b _
      split
      · rename_i hab
        have h₁ := rt_ordNum_le tt a
        have h₂ := rt_ordNum_le tt b
        exact Nat.max_le.2 ⟨by omega, by omega⟩
      · omega
    · omega
termination_by k => k
decreasing_by all_goals omega

theorem rt_sizeNum_le (cap : Nat) (tt : List (Nat × Nat)) (k : Nat) : sizeNum cap tt k ≤ cap + 1 := by
  cases k with
  | zero => rw [sizeNum]; omega
  | succ k =>
    rw [sizeNum]
    split
    · split
      · exact Nat.le_trans (Nat.min_le_left _ _) (by omega)
      · omega
    · omega

theorem rt_typeTable_getD (tt : List (Nat × Nat)) (f : Nat → Nat) {k : Nat} (hk : k ≤ tt.length) :
    (typeTable tt f).getD k 0 = f k := rt_tb_getD f (k := tt.length + 1) (by omega)

theorem rt_typeTable_length (tt : List (Nat × Nat)) (f : Nat → Nat) : (typeTable tt f).length = tt.length + 1 := by
  simp [typeTable]

theorem rt_total_cost {n Z : Nat} (hZ : 2 ≤ Z) (hn : n ≤ Z) {T₀ T : Nat}
    (h₀ : T₀ ≤ 16 * (Z * (Z * Z)) + 119 * (Z * Z) + 268 * Z + 181)
    (h₁ : T ≤ 92 * (Z * (Z * (Z * (Z * Z)))) + 145 * (Z * (Z * (Z * Z))) + 882 * (Z * (Z * Z)) + 436 * (Z * Z) +
      444 * Z + 381) :
    1 + (1 + (T₀ + (1 + (n * (T + 2) + 2 + (1 + (2 * (n + 1) + 1)))))) ≤ 1000 * (Z * Z * Z * Z * Z * Z) := by
  have hm := Nat.mul_le_mul hn (show T + 2 ≤ 92 * (Z * (Z * (Z * (Z * Z)))) + 145 * (Z * (Z * (Z * Z))) +
    882 * (Z * (Z * Z)) + 436 * (Z * Z) + 444 * Z + 383 by omega)
  have hd : Z * (92 * (Z * (Z * (Z * (Z * Z)))) + 145 * (Z * (Z * (Z * Z))) + 882 * (Z * (Z * Z)) + 436 * (Z * Z) +
      444 * Z + 383) = 92 * (Z * (Z * (Z * (Z * (Z * Z))))) + 145 * (Z * (Z * (Z * (Z * Z)))) +
      882 * (Z * (Z * (Z * Z))) + 436 * (Z * (Z * Z)) + 444 * (Z * Z) + 383 * Z := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_left_comm Z 92, Nat.mul_left_comm Z 145,
      Nat.mul_left_comm Z 882, Nat.mul_left_comm Z 436, Nat.mul_left_comm Z 444, Nat.mul_comm Z 383]
  have e6 : Z * Z * Z * Z * Z * Z = Z * (Z * (Z * (Z * (Z * Z)))) := by simp only [Nat.mul_assoc]
  rw [e6]
  have p2 := Nat.mul_le_mul_right Z hZ
  have p3 := Nat.mul_le_mul_right (Z * Z) hZ
  have p4 := Nat.mul_le_mul_right (Z * (Z * Z)) hZ
  have p5 := Nat.mul_le_mul_right (Z * (Z * (Z * Z))) hZ
  have p6 := Nat.mul_le_mul_right (Z * (Z * (Z * (Z * Z)))) hZ
  generalize n * (T + 2) = A at *
  generalize Z * (Z * (Z * (Z * (Z * Z)))) = Z6 at *
  generalize Z * (Z * (Z * (Z * Z))) = Z5 at *
  generalize Z * (Z * (Z * Z)) = Z4 at *
  generalize Z * (Z * Z) = Z3 at *
  generalize Z * Z = Z2 at *
  omega

/-- The decision of smallness, at the state before type number `k`. -/
theorem rt_small_step (j : Nat) (S : Lists NK) {tt : List (Nat × Nat)} {cap N : Nat}
    (hO : S ORD = typeTable tt (ordNum tt)) (hZ : S SZ = typeTable tt (sizeNum cap tt)) (hC : S CAP = [cap])
    (hs : ScratchEmpty S) (kc : List Nat) (k : Nat) (p : NProg NK) (T : Nat) (S' : Lists NK) (hk : k ≤ tt.length)
    (hp : small j cap tt k → NRuns p (rt_Pre j cap N tt S kc k) S' T)
    (hq : ¬ small j cap tt k → NRuns rt_noRows (rt_Pre j cap N tt S kc k) S' T) :
    NRuns (rt_ifSmall j p rt_noRows) (rt_Pre j cap N tt S kc k) S' (T + 25 * rowsZ j cap N tt + 40) := by
  have hZge := rt_Z_ge (j := j) (cap := cap) (N := N) (tt := tt)
  have eO : (rt_Pre j cap N tt S kc k) ORD = typeTable tt (ordNum tt) := by simp only [rt_Pre]; rt_at; exact hO
  have eZ : (rt_Pre j cap N tt S kc k) SZ = typeTable tt (sizeNum cap tt) := by simp only [rt_Pre]; rt_at; exact hZ
  have x := rt_ifSmall_runs j (p := p) (q := rt_noRows) (rt_Pre j cap N tt S kc k) S' (k := k) (o := ordNum tt k)
    (z := sizeNum cap tt k) (cap := cap) (T := T) (by simp only [rt_Pre]; rt_at)
    (by rw [eO, rt_typeTable_length]; omega) (by rw [eO, rt_typeTable_getD _ _ hk])
    (by rw [eZ, rt_typeTable_length]; omega) (by rw [eZ, rt_typeTable_getD _ _ hk])
    (by simp only [rt_Pre]; rt_at; exact hC) (by simp only [rt_Pre]; rt_at; exact rt_scratch_get hs _)
    (by simp only [rt_Pre]; rt_at; exact rt_scratch_get hs _) (by simp only [rt_Pre]; rt_at; exact rt_scratch_get hs _)
    (by simp only [rt_Pre]; rt_at; exact rt_scratch_get hs _) hp hq
  rw [eO, eZ, rt_typeTable_length, rt_typeTable_length] at x
  have h₁ := rt_ordNum_le tt k
  have h₂ := rt_sizeNum_le cap tt k
  exact x.mono (by omega)

/-- One arrow: from the state after type number `m` to the state after `m + 1`. -/
theorem rt_arrow_step (j : Nat) (S : Lists NK) {tt : List (Nat × Nat)} {cap N : Nat} (hw : TTWF tt)
    (hT : S TTs = encPairs tt) (hO : S ORD = typeTable tt (ordNum tt)) (hZ : S SZ = typeTable tt (sizeNum cap tt))
    (hC : S CAP = [cap]) (hs : ScratchEmpty S) (kc : List Nat) {m : Nat} (hm : m < tt.length) :
    NRuns (.seq rt_head (rt_ifSmall j rt_aRows rt_noRows)) (rt_Out j cap N tt S kc m) (rt_Out j cap N tt S kc (m + 1))
      (92 * (rowsZ j cap N tt * (rowsZ j cap N tt * (rowsZ j cap N tt * (rowsZ j cap N tt * rowsZ j cap N tt)))) +
        145 * (rowsZ j cap N tt * (rowsZ j cap N tt * (rowsZ j cap N tt * rowsZ j cap N tt))) +
        882 * (rowsZ j cap N tt * (rowsZ j cap N tt * rowsZ j cap N tt)) + 436 * (rowsZ j cap N tt * rowsZ j cap N tt) +
        444 * rowsZ j cap N tt + 381) := by
  have y₁ := rt_head_runs (j := j) (cap := cap) (N := N) S hw hs kc hm
  have y₂ := rt_small_step j S (N := N) hO hZ hC hs kc (m + 1) rt_aRows _ (rt_Out j cap N tt S kc (m + 1)) (by omega)
    (fun h => rt_aRows_runs S hw hs hT kc hm h) (fun h => (rt_noRows_runs S _ h).mono (by omega))
  have hc1 := rt_cnt_le_Z (j := j) (cap := cap) (N := N) hw (k := m) (by omega)
  have hl1 := rt_lenE_le_Z (j := j) (cap := cap) (N := N) hw (k := m) (by omega)
  have hb := rt_mul_bound hc1 hl1 3 7
  have hy := y₁.seq y₂
  generalize rowsZ j cap N tt = Z at *
  generalize (rowsT j cap N tt m).length * (3 * rt_lenE j cap N tt m + 7) = A at *
  generalize Z * (Z * (Z * (Z * Z))) = Z5 at *
  generalize Z * (Z * (Z * Z)) = Z4 at *
  generalize Z * (Z * Z) = Z3 at *
  generalize Z * Z = Z2 at *
  exact hy.mono (by omega)

/-- All the arrows. -/
theorem rt_arrows (j : Nat) (S : Lists NK) {tt : List (Nat × Nat)} {cap N : Nat} (hw : TTWF tt)
    (hT : S TTs = encPairs tt) (hO : S ORD = typeTable tt (ordNum tt)) (hZ : S SZ = typeTable tt (sizeNum cap tt))
    (hC : S CAP = [cap]) (hs : ScratchEmpty S) :
    NRuns (rt_for rt_KC (.seq rt_head (rt_ifSmall j rt_aRows rt_noRows))) (rt_Out j cap N tt S [tt.length - 0] 0)
      ((rt_Out j cap N tt S [tt.length - tt.length] tt.length).set rt_KC [])
      (tt.length * (92 * (rowsZ j cap N tt * (rowsZ j cap N tt * (rowsZ j cap N tt * (rowsZ j cap N tt * rowsZ j cap N tt)))) +
        145 * (rowsZ j cap N tt * (rowsZ j cap N tt * (rowsZ j cap N tt * rowsZ j cap N tt))) +
        882 * (rowsZ j cap N tt * (rowsZ j cap N tt * rowsZ j cap N tt)) + 436 * (rowsZ j cap N tt * rowsZ j cap N tt) +
        444 * rowsZ j cap N tt + 381 + 2) + 2) :=
  rt_for_runs (c := rt_KC) (body := .seq rt_head (rt_ifSmall j rt_aRows rt_noRows))
    (fun m => rt_Out j cap N tt S [tt.length - m] m) [] tt.length _
    (fun m _ => by simp only [rt_Out]; rt_at)
    (fun m hm => by
      have e : (rt_Out j cap N tt S [tt.length - m] m).set rt_KC ([] ++ [tt.length - m - 1]) =
          rt_Out j cap N tt S [tt.length - (m + 1)] m := by
        simp only [rt_Out, show tt.length - (m + 1) = tt.length - m - 1 by omega]; rt_ext [rt_KC]
      rw [e]
      exact rt_arrow_step j S hw hT hO hZ hC hs _ hm)

theorem rowsTableP_runs (j : Nat) (S : Lists NK) {tt : List (Nat × Nat)} {cap N : Nat} (hw : TTWF tt)
    (hT : S TTs = encPairs tt) (hN : S NTT = [tt.length]) (hO : S ORD = typeTable tt (ordNum tt))
    (hZ : S SZ = typeTable tt (sizeNum cap tt)) (hC : S CAP = [cap]) (hX : S NX = [N]) (hcnt : S CNT = [])
    (hrows : S ROWS = []) (hroff : S ROFF = []) (hs : ScratchEmpty S) :
    NRuns (rowsTableP j) S (((S.set CNT (cntTable j cap N tt)).set ROWS (rowsFlat j cap N tt)).set ROFF
      (roffTable j cap N tt)) (rowsCost j cap N tt) := by
  have hZge := rt_Z_ge (j := j) (cap := cap) (N := N) (tt := tt)
  -- start
  have x₁ := nruns_pushZ ROFF S
  rw [hroff, List.nil_append] at x₁
  have x₂ := nruns_pushZ rt_KU (S.set ROFF [0])
  have e₂ : (S.set ROFF [0]).set rt_KU ((S.set ROFF [0]) rt_KU ++ [0]) = rt_Pre j cap N tt S [] 0 := by
    have h1 : S rt_KC = [] := rt_scratch_get hs _
    have h2 : S rt_KU = [] := rt_scratch_get hs _
    have h3 : S rt_LEN = [] := rt_scratch_get hs _
    have hp0 : rt_pre j cap N tt 0 = [] := rfl
    simp only [rt_Pre, rt_tb, List.range_zero, List.map_nil]
    rt_extU [ROFF, rt_KU, rt_KC, CNT, ROWS, rt_LEN] [h1, h2, h3, hcnt, hrows, hp0]
  rw [e₂] at x₂
  -- type number `0`
  have x₃ := rt_small_step j S (N := N) hO hZ hC hs [] 0 rt_pRows _ (rt_Out j cap N tt S [] 0) (Nat.zero_le _)
    (fun h => rt_pRows_runs S h hs hX) (fun h => (rt_noRows_runs S [] h).mono (by omega))
  -- the arrows
  have x₄ := nruns_dup NTT rt_KC (by decide) (rt_Out j cap N tt S [] 0) (l := []) (v := tt.length)
    (by simp only [rt_Out]; rt_at; exact hN)
  have e₄ : (rt_Out j cap N tt S [] 0).set rt_KC ((rt_Out j cap N tt S [] 0) rt_KC ++ [tt.length]) =
      rt_Out j cap N tt S [tt.length - 0] 0 := by
    simp only [rt_Out, Nat.sub_zero]; rt_ext [rt_KC]
  rw [e₄] at x₄
  have x₅ := rt_arrows j S (N := N) hw hT hO hZ hC hs
  -- the end
  have x₆ := nruns_pop rt_KU ((rt_Out j cap N tt S [tt.length - tt.length] tt.length).set rt_KC []) (l := [])
    (v := tt.length) (by simp only [rt_Out]; rt_at)
  have x₇ := nruns_clr rt_LEN (((rt_Out j cap N tt S [tt.length - tt.length] tt.length).set rt_KC []).set rt_KU [])
  have eL : (((rt_Out j cap N tt S [tt.length - tt.length] tt.length).set rt_KC []).set rt_KU []) rt_LEN =
      rt_tb (rt_lenE j cap N tt) (tt.length + 1) := by simp only [rt_Out]; rt_at
  rw [eL, rt_tb_length] at x₇
  have e₇ : ((((rt_Out j cap N tt S [tt.length - tt.length] tt.length).set rt_KC []).set rt_KU []).set rt_LEN []) =
      ((S.set CNT (cntTable j cap N tt)).set ROWS (rowsFlat j cap N tt)).set ROFF (roffTable j cap N tt) := by
    have h1 : S rt_KC = [] := rt_scratch_get hs _
    have h2 : S rt_KU = [] := rt_scratch_get hs _
    have h3 : S rt_LEN = [] := rt_scratch_get hs _
    have ec : cntTable j cap N tt = rt_tb (fun t => (rowsT j cap N tt t).length) (tt.length + 1) := rfl
    have er : rowsFlat j cap N tt = rt_pre j cap N tt (tt.length + 1) := rfl
    have eo : roffTable j cap N tt = rt_tb (fun t => (rt_pre j cap N tt t).length) (tt.length + 1) := rfl
    rw [ec, er, eo]
    simp only [rt_Out]
    rt_extU [rt_LEN, rt_KU, rt_KC, CNT, ROWS, ROFF] [h1, h2, h3]
  rw [e₇] at x₇
  have hall := x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq x₇)))))
  have hc := rt_total_cost (n := tt.length) (Z := rowsZ j cap N tt) (by omega) (by omega)
    (T₀ := 16 * (rowsZ j cap N tt * (rowsZ j cap N tt * rowsZ j cap N tt)) + 119 * (rowsZ j cap N tt * rowsZ j cap N tt) +
      243 * rowsZ j cap N tt + 141 + 25 * rowsZ j cap N tt + 40)
    (T := 92 * (rowsZ j cap N tt * (rowsZ j cap N tt * (rowsZ j cap N tt * (rowsZ j cap N tt * rowsZ j cap N tt)))) +
      145 * (rowsZ j cap N tt * (rowsZ j cap N tt * (rowsZ j cap N tt * rowsZ j cap N tt))) +
      882 * (rowsZ j cap N tt * (rowsZ j cap N tt * rowsZ j cap N tt)) + 436 * (rowsZ j cap N tt * rowsZ j cap N tt) +
      444 * rowsZ j cap N tt + 381) (by omega) (Nat.le_refl _)
  exact hall.mono (by unfold rowsCost; exact hc)

end Shallot.MacroPeg.Mach
