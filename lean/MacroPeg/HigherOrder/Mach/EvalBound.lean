import MacroPeg.HigherOrder.Mach.EvalLoopSpec

/-!
# How much an item can push

Whatever the stack, one item adds at most `pushBound` numbers to the evaluation stack (`stepT_size`): at most one
vector, of at most `n` blocks (`n` environments), each at most the length of a value or of a rule value.
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

/-! ## Lengths of lists of blocks -/

theorem length_flatten_le {L : List (List Nat)} {B : Nat} (h : ∀ c ∈ L, c.length ≤ B) :
    L.flatten.length ≤ L.length * B := by
  induction L with
  | nil => simp
  | cons c L ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := h c List.mem_cons_self
    have := ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
    omega

theorem length_chunksN {α : Type} (k : Nat) : ∀ (n : Nat) (l : List α), (chunksN k n l).length = n
  | 0, _ => rfl
  | n + 1, l => by simp [chunksN, length_chunksN k n]

theorem zipWith_flatten_le {f : List Nat → List Nat → List Nat} {B : Nat} (hf : ∀ a b, (f a b).length ≤ B) :
    ∀ (L₁ L₂ : List (List Nat)), (List.zipWith f L₁ L₂).flatten.length ≤ L₁.length * B
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: L₁, b :: L₂ => by
    simp only [List.zipWith_cons_cons, List.flatten_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := hf a b
    have := zipWith_flatten_le hf L₁ L₂
    omega

theorem map_flatten_le {α : Type} {f : α → List Nat} {B : Nat} (hf : ∀ a, (f a).length ≤ B) (L : List α) :
    (L.map f).flatten.length ≤ L.length * B :=
  by
    have := length_flatten_le (L := L.map f) (B := B) (fun c hc => by
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hc; exact hf a)
    simpa using this

theorem replicate_flatten_length (n : Nat) (v : List Nat) : (List.replicate n v).flatten.length = n * v.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

theorem le_sum_of_mem {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem sum_replicate' (n a : Nat) : (List.replicate n a).sum = n * a := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

/-! ## Entries of the tables are below their sums -/

variable {j cap N : Nat} {tt ct : List (Nat × Nat)}

theorem envT_le_sum (c : Nat) : envT j cap N tt ct c ≤ (envTable j cap N tt ct).sum := by
  by_cases hc : c ≤ ct.length
  · exact le_sum_of_mem (List.mem_map.2 ⟨c, List.mem_range.2 (by omega), rfl⟩)
  · obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
    rw [envT, List.getElem?_eq_none (by omega)]; exact Nat.zero_le _

theorem valT_le_sum (k : Nat) : valT j cap N tt k ≤ (valTable j cap N tt).sum := by
  by_cases hk : k ≤ tt.length
  · exact le_sum_of_mem (List.mem_map.2 ⟨k, List.mem_range.2 (by omega), rfl⟩)
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [valT, List.getElem?_eq_none (by omega)]; exact Nat.zero_le _

theorem varVecT_length_le : ∀ (c i : Nat), (varVecT j cap N tt ct c i).length ≤ envT j cap N tt ct c
  | 0, _ => by rw [varVecT]; exact Nat.zero_le _
  | k + 1, i => by
    rw [varVecT, envT]
    rcases hk : ct[k]? with _ | ⟨par, t⟩
    · exact Nat.le_refl _
    · simp only []
      split
      · cases i with
        | zero => simp
        | succ i =>
          dsimp only
          have := varVecT_length_le par i
          rw [List.length_flatMap]
          have h₂ : ((varVecT j cap N tt ct par i).map
              (fun v => (List.replicate (rowsT j cap N tt t).length v).length)).sum =
              (varVecT j cap N tt ct par i).length * (rowsT j cap N tt t).length := by
            simp only [List.length_replicate, List.map_const', sum_replicate']
          rw [h₂]; exact Nat.mul_le_mul_right _ this
      · exact Nat.le_refl _

/-! ## Lengths of codes and rows -/

theorem length_codes (N : Nat) (f : Nat → Res) : (flatVal N .p ((List.range (N + 1)).map f)).length = N + 1 := by
  simp [flatVal]

theorem leafCodes_length (x : List Char) (e : HExp) : (leafCodes x e).length = x.length + 1 := by
  simp [leafCodes, flatVal, baseVec]
theorem seqCodes_length (x : List Char) (a b : List Nat) : (seqCodes x a b).length = x.length + 1 := by
  simp [seqCodes, flatVal, baseVec]
theorem altCodes_length (x : List Char) (a b : List Nat) : (altCodes x a b).length = x.length + 1 := by
  simp [altCodes, flatVal, baseVec]
theorem starCodes_length (x : List Char) (a : List Nat) : (starCodes x a).length = x.length + 1 := by
  simp [starCodes, flatVal, baseVec]
theorem notCodes_length (x : List Char) (a : List Nat) : (notCodes x a).length = x.length + 1 := by
  simp [notCodes, flatVal, baseVec]

theorem rowsT_row_length (hw : TTWF tt) {t : Nat} (ht : t ≤ tt.length) :
    ∀ r ∈ rowsT j cap N tt t, r.length = valT j cap N tt t := by
  intro r hr
  unfold rowsT at hr
  split at hr
  · rename_i hs
    obtain ⟨τ, hτ⟩ := tyOf_some hw t ht
    rw [rowsNum_eq N t hτ, eRows] at hr
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
    rw [length_flatVal τ hd, valT_eq t (small_need hs), valNum_eq t hτ]
  · simp at hr

theorem rowsT_getD_le (hw : TTWF tt) {t : Nat} (ht : t ≤ tt.length) (k : Nat) :
    ((rowsT j cap N tt t).getD k []).length ≤ valT j cap N tt t := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : (rowsT j cap N tt t)[k]? with _ | r
  · simp
  · simp only [Option.getD_some]
    exact Nat.le_of_eq (rowsT_row_length hw ht r (List.mem_of_getElem? h))

theorem getD_length_le_flatten (Tf : List (List Nat)) (a : Nat) : (Tf.getD a []).length ≤ Tf.flatten.length := by
  induction Tf generalizing a with
  | nil => simp
  | cons v Tf ih =>
    cases a with
    | zero => simp
    | succ a => have := ih a; simp only [List.getD_cons_succ, List.flatten_cons, List.length_append]; omega

/-! ## One item pushes at most `pushBound` -/

/-- A bound on the length of a vector one item pushes. -/
def pushBound (j cap : Nat) (x : List Char) (tt ct : List (Nat × Nat)) (Tf : List (List Nat)) : Nat :=
  (envTable j cap x.length tt ct).sum * (x.length + 1 + (valTable j cap x.length tt).sum + Tf.flatten.length)

theorem varTy_type_le (hc : CTWF tt ct) {c : Nat} (hcl : c ≤ ct.length) (i : Nat) :
    (varTy ct c i).getD 0 ≤ tt.length := by
  rw [varTy_walk hc i c hcl]
  split
  · simp
  · rename_i hne
    have := walkCtx_le hc c hcl i
    rw [List.getElem?_eq_getElem (by omega)]
    simp only [Option.map_some, Option.getD_some]
    exact (hc _ (by omega)).2

theorem evFlat_length_cons (v : List Nat) (st : List (List Nat)) :
    (evFlat (v :: st)).length = (evFlat st).length + v.length := by
  rw [evFlat_cons, List.length_append]

theorem zip_out_le {f : List Nat → List Nat → List Nat} {B : Nat} (hf : ∀ a b, (f a b).length ≤ B) (m m' n : Nat)
    (va vb : List Nat) : (List.zipWith f (chunksN m n va) (chunksN m' n vb)).flatten.length ≤ n * B := by
  have := zipWith_flatten_le hf (chunksN m n va) (chunksN m' n vb)
  rwa [length_chunksN] at this

theorem map_out_le {f : List Nat → List Nat} {B : Nat} (hf : ∀ a, (f a).length ≤ B) (m n : Nat) (va : List Nat) :
    ((chunksN m n va).map f).flatten.length ≤ n * B := by
  have := map_flatten_le hf (chunksN m n va)
  rwa [length_chunksN] at this

/-- **One item adds at most `pushBound` numbers to the stack.** -/
theorem stepT_size {x : List Char} {lt : List (List Nat)} {Tf : List (List Nat)} (hw : TTWF tt) (hc : CTWF tt ct)
    {it : MItem} (hcx : it.ctx ≤ ct.length) (vs : List (List Nat)) :
    (evFlat (stepT j cap x tt ct lt Tf it vs)).length ≤ (evFlat vs).length + pushBound j cap x tt ct Tf := by
  have hn := envT_le_sum (j := j) (cap := cap) (N := x.length) (tt := tt) (ct := ct) it.ctx
  have hV : x.length + 1 ≤ x.length + 1 + (valTable j cap x.length tt).sum + Tf.flatten.length := by omega
  have hnV : ∀ m, m ≤ x.length + 1 + (valTable j cap x.length tt).sum + Tf.flatten.length →
      envT j cap x.length tt ct it.ctx * m ≤ pushBound j cap x tt ct Tf :=
    fun m hm => Nat.mul_le_mul hn hm
  have hN := hnV _ hV
  have ht := varTy_type_le hc hcx it.a
  have hvt := valT_le_sum (j := j) (cap := cap) (N := x.length) (tt := tt) ((varTy ct it.ctx it.a).getD 0)
  have hvb := valT_le_sum (j := j) (cap := cap) (N := x.length) (tt := tt) it.b
  have hvar := hnV _ (show valT j cap x.length tt ((varTy ct it.ctx it.a).getD 0) ≤ _ by omega)
  have happ := hnV _ (show valT j cap x.length tt it.b ≤ _ by omega)
  have hrule := hnV _ (show (Tf.getD it.a []).length ≤ _ by have := getD_length_le_flatten Tf it.a; omega)
  have hvv := Nat.mul_le_mul_right (valT j cap x.length tt ((varTy ct it.ctx it.a).getD 0))
    (varVecT_length_le (j := j) (cap := cap) (N := x.length) (tt := tt) (ct := ct) it.ctx it.a)
  unfold stepT
  dsimp only
  split
  · simp only [evFlat_length_cons]
    exact Nat.le_trans (Nat.add_le_add_left
      (zip_out_le (B := x.length + 1) (fun a b => Nat.le_of_eq (seqCodes_length x a b)) _ _ _ _ _) _) (by omega)
  · simp only [evFlat_length_cons]
    exact Nat.le_trans (Nat.add_le_add_left
      (zip_out_le (B := x.length + 1) (fun a b => Nat.le_of_eq (altCodes_length x a b)) _ _ _ _ _) _) (by omega)
  · simp only [evFlat_length_cons]
    exact Nat.le_trans (Nat.add_le_add_left
      (map_out_le (B := x.length + 1) (fun a => Nat.le_of_eq (starCodes_length x a)) _ _ _) _) (by omega)
  · simp only [evFlat_length_cons]
    exact Nat.le_trans (Nat.add_le_add_left
      (map_out_le (B := x.length + 1) (fun a => Nat.le_of_eq (notCodes_length x a)) _ _ _) _) (by omega)
  · simp only [evFlat_length_cons]
    have h := map_flatten_le (B := valT j cap x.length tt ((varTy ct it.ctx it.a).getD 0))
      (fun k => rowsT_getD_le hw ht k) (varVecT j cap x.length tt ct it.ctx it.a)
    omega
  · rw [evFlat_length_cons, replicate_flatten_length]; omega
  · omega
  · simp only [evFlat_length_cons]
    exact Nat.le_trans (Nat.add_le_add_left
      (zip_out_le (B := valT j cap x.length tt it.b) (fun fv yv => by simp only [block]; exact List.length_take_le _ _)
        _ _ _ _ _) _) (by omega)
  · split
    · rw [evFlat_length_cons, replicate_flatten_length, leafCodes_length]; omega
    · omega

end Shallot.MacroPeg.Mach
