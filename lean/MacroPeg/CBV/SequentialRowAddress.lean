import MacroPeg.CBV.SequentialTupleKeys

namespace Shallot.MacroPeg.CBV.SequentialRowAddress

open SequentialTupleKeys (Key keys paths cuts values cursor)

/-- Big-endian base-(n+1) address of an endpoint vector. -/
def rank (n : Nat) : List Nat → Nat
  | [] => 0
  | j :: rest => j * (n + 1) ^ rest.length + rank n rest

private theorem flatMap_get_uniform {α β : Type} (xs : List α) (f : α → List β)
    (width : Nat) (hw : ∀ a ∈ xs, (f a).length = width)
    {i j : Nat} {a : α} (hi : xs[i]? = some a) (hj : j < width) :
    (xs.flatMap f)[i * width + j]? = (f a)[j]? := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons b xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst a
      simp only [Nat.zero_mul, Nat.zero_add, List.flatMap_cons]
      exact List.getElem?_append_left (by rw [hw b (by simp)]; exact hj)
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      rw [List.flatMap_cons, List.getElem?_append_right (by
        rw [hw b (by simp), Nat.succ_mul]; omega)]
      have he : (i + 1) * width + j - (f b).length = i * width + j := by
        rw [hw b (by simp), Nat.succ_mul]; omega
      rw [he]
      exact ih (fun a ha => hw a (by simp [ha])) hi

theorem rank_lt {n : Nat} {path : List Nat} (hb : ∀ j ∈ path, j ≤ n) :
    rank n path < (n + 1) ^ path.length := by
  induction path with
  | nil => simp [rank]
  | cons j rest ih =>
    have hj := hb j (by simp)
    have ht := ih (fun a ha => hb a (by simp [ha]))
    have hmul := Nat.mul_le_mul_right ((n + 1) ^ rest.length) (show j + 1 ≤ n + 1 by omega)
    calc
      rank n (j :: rest) < j * (n + 1) ^ rest.length + (n + 1) ^ rest.length :=
        Nat.add_lt_add_left ht _
      _ = (j + 1) * (n + 1) ^ rest.length := (Nat.succ_mul _ _).symm
      _ ≤ (n + 1) * (n + 1) ^ rest.length := hmul
      _ = (n + 1) ^ (j :: rest).length := by simp [Nat.pow_succ, Nat.mul_comm]

theorem paths_get_rank {n : Nat} {path : List Nat} (hb : ∀ j ∈ path, j ≤ n) :
    (paths n path.length)[rank n path]? = some path := by
  induction path with
  | nil => rfl
  | cons j rest ih =>
    have ht := fun a ha => hb a (List.mem_cons_of_mem j ha)
    simp only [List.length_cons, paths, rank]
    rw [flatMap_get_uniform _ _ ((n + 1) ^ rest.length)
      (by intro a ha; simp [SequentialTupleKeys.paths_length])
      (List.getElem?_range (show j < n + 1 by have := hb j (by simp); omega))
      (rank_lt ht)]
    simp [ih ht]

/-- Offset of a block in a variable-width concatenation. No word comparisons. -/
def offset {α β : Type} (xs : List α) (f : α → List β) (i : Nat) : Nat :=
  ((xs.take i).map (fun a => (f a).length)).sum

private theorem flatMap_get_offset {α β : Type} (xs : List α) (f : α → List β)
    {i j : Nat} {a : α} (hi : xs[i]? = some a) (hj : j < (f a).length) :
    (xs.flatMap f)[offset xs f i + j]? = (f a)[j]? := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons b xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst a
      simpa [offset] using (List.getElem?_append_left (l₂ := xs.flatMap f) hj)
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      simp only [offset, List.take_succ_cons, List.map_cons, List.sum_cons,
        List.flatMap_cons]
      rw [List.getElem?_append_right (by omega)]
      have he : (f b).length + ((xs.take i).map (fun a => (f a).length)).sum + j -
          (f b).length = offset xs f i + j := by unfold offset; omega
      rw [he]
      exact ih hi

def block (g : MGrammar) (n : Nat) (i : Fin g.rules.length) : List Key :=
  (paths n (g.rules[i].arity + 1)).map (fun path => ⟨i.val, path⟩)

def address (g : MGrammar) (n i : Nat) (path : List Nat) : Nat :=
  (((List.finRange g.rules.length).take i).map
    (fun j => (n + 1) ^ (g.rules[j].arity + 1))).sum + rank n path

private theorem address_eq_offset (g : MGrammar) (n i : Nat) (path : List Nat) :
    address g n i path = offset (List.finRange g.rules.length) (block g n) i + rank n path := by
  simp [address, offset, block, SequentialTupleKeys.paths_length]

theorem keys_get_address {g : MGrammar} {n i : Nat} {r : MRule}
    (hr : ruleAtM g.rules i = some r) {path : List Nat}
    (hlen : path.length = r.arity + 1) (hb : ∀ j ∈ path, j ≤ n) :
    (keys g n)[address g n i path]? = some ⟨i, path⟩ := by
  let idx : Fin g.rules.length := ⟨i, ruleAtM_lt hr⟩
  have he : g.rules[idx] = r := by
    have hh : g.rules[i]? = some r := by simpa only [ruleAtM_eq_getElem?] using hr
    simp only [List.getElem?_eq_getElem (ruleAtM_lt hr), Option.some.injEq] at hh
    exact hh
  have hi : (List.finRange g.rules.length)[i]? = some idx := by
    rw [List.getElem?_eq_getElem (by simpa using ruleAtM_lt hr)]
    simp [idx]
  have hj : rank n path < (block g n idx).length := by
    simpa [block, SequentialTupleKeys.paths_length, he, ← hlen] using rank_lt hb
  change ((List.finRange g.rules.length).flatMap (block g n))[_]? = _
  rw [address_eq_offset, flatMap_get_offset _ _ hi hj]
  simp only [block, he, ← hlen, List.getElem?_map, paths_get_rank hb, Option.map_some]
  rfl

theorem address_lt {g : MGrammar} {n i : Nat} {r : MRule}
    (hr : ruleAtM g.rules i = some r) {path : List Nat}
    (hlen : path.length = r.arity + 1) (hb : ∀ j ∈ path, j ≤ n) :
    address g n i path < (keys g n).length :=
  List.getElem?_eq_some_iff.mp (keys_get_address hr hlen hb) |>.1

end Shallot.MacroPeg.CBV.SequentialRowAddress
