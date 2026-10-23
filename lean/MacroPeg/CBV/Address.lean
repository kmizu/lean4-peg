import MacroPeg.CBV.Indexed

namespace Shallot.MacroPeg.CBV

/-- Mixed-radix rank of the argument tuple, with the first argument most significant. -/
def wordRank (B : Nat) : List Nat → Nat
  | [] => 0
  | a :: as => a * B ^ as.length + wordRank B as

/-- Index one block of a flattened list using the actual length of all preceding blocks. -/
theorem get_flatMap_at {α β : Type} (F : α → List β) :
    ∀ (xs : List α) (i : Nat) (hi : i < xs.length) (j : Nat), j < (F xs[i]).length →
      (xs.flatMap F)[((xs.take i).flatMap F).length + j]? = (F xs[i])[j]?
  | [], i, hi, _, _ => by simp at hi
  | a :: xs, 0, hi, j, hj => by
    simp only [List.flatMap_cons, List.take_zero, List.flatMap_nil, List.length_nil, Nat.zero_add,
      List.getElem_cons_zero]
    exact List.getElem?_append_left hj
  | a :: xs, i + 1, hi, j, hj => by
    have hi' : i < xs.length := by simp at hi; omega
    have hh := get_flatMap_at F xs i hi' j hj
    simp only [List.flatMap_cons, List.take_succ_cons, List.length_append, List.getElem_cons_succ]
    rw [List.getElem?_append_right (by omega)]
    simpa [Nat.add_assoc] using hh

theorem wordRank_lt {B : Nat} (hB : 0 < B) : ∀ ids : List Nat,
    (∀ d ∈ ids, d < B) → wordRank B ids < B ^ ids.length
  | [], _ => by simp [wordRank]
  | d :: ids, hd => by
    have ht := wordRank_lt hB ids (fun a ha => hd a (List.mem_cons_of_mem d ha))
    have hD : d + 1 ≤ B := by have := hd d (by simp); omega
    have hm := Nat.mul_le_mul_right (B ^ ids.length) hD
    have hh : d * B ^ ids.length + wordRank B ids < (d + 1) * B ^ ids.length := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    simpa [wordRank, Nat.pow_succ, Nat.mul_comm] using Nat.lt_of_lt_of_le hh hm

/-- Tuple enumeration can be indexed arithmetically, avoiding a search through table keys. -/
theorem words_get_rank {B : Nat} (hB : 0 < B) : ∀ ids : List Nat,
    (∀ d ∈ ids, d < B) → (words (List.range B) ids.length)[wordRank B ids]? = some ids
  | [], _ => rfl
  | d :: ids, hd => by
    have hD : d < B := hd d (by simp)
    have hds : ∀ a ∈ ids, a < B := fun a ha => hd a (List.mem_cons_of_mem d ha)
    have hRank := wordRank_lt hB ids hds
    have hg := get_flatMap_at (fun a => (words (List.range B) ids.length).map (List.cons a))
      (List.range B) d (by simpa using hD) (wordRank B ids) (by simpa [length_words] using hRank)
    have hlen : (((List.range B).take d).flatMap
        (fun a => (words (List.range B) ids.length).map (List.cons a))).length = d * B ^ ids.length := by
      simp only [List.length_flatMap, List.length_map, length_words, List.length_range]
      rw [List.map_const', List.sum_replicate_nat, List.length_take, List.length_range,
        Nat.min_eq_left (Nat.le_of_lt hD)]
    rw [hlen] at hg
    change ((List.range B).flatMap (fun a => (words (List.range B) ids.length).map (List.cons a)))[d * B ^ ids.length + wordRank B ids]? = some (d :: ids)
    rw [hg]
    simp only [List.getElem_range, List.getElem?_map, words_get_rank hB ids hds, Option.map_some]

def ruleKeys (g : MGrammar) (x : List Char) (i : Nat) : List Key :=
  match ruleAtM g.rules i with
  | none => []
  | some r => (words (List.range (subStrs x).length) r.arity).flatMap (fun ids =>
      (List.range (x.length + 1)).map (fun p => (i, ids, p)))

def ruleWidth (g : MGrammar) (x : List Char) (i : Nat) : Nat :=
  match ruleAtM g.rules i with
  | none => 0
  | some r => (subStrs x).length ^ r.arity * (x.length + 1)

def ruleOffset (g : MGrammar) (x : List Char) (i : Nat) : Nat :=
  ((List.range i).map (ruleWidth g x)).sum

def address (g : MGrammar) (x : List Char) (i : Nat) (ids : List Nat) (p : Nat) : Nat :=
  ruleOffset g x i + wordRank (subStrs x).length ids * (x.length + 1) + p

theorem ruleKeys_length (g : MGrammar) (x : List Char) (i : Nat) :
    (ruleKeys g x i).length = ruleWidth g x i := by
  unfold ruleKeys ruleWidth
  cases ruleAtM g.rules i with
  | none => rfl
  | some r =>
    simp only [List.length_flatMap, List.length_map, List.length_range]
    rw [List.map_const', List.sum_replicate_nat, length_words, List.length_range]

theorem dictionary_pos (x : List Char) : 0 < (subStrs x).length := by
  have h := literalId_lt (pre_mem (x := x) (p := 0) (j := 0) (by omega))
  omega

theorem ruleKeys_get {g : MGrammar} {x : List Char} {i : Nat} {r : MRule} {ids : List Nat} {p : Nat}
    (hr : ruleAtM g.rules i = some r)
    (hids : ids ∈ words (List.range (subStrs x).length) r.arity) (hp : p ≤ x.length) :
    (ruleKeys g x i)[wordRank (subStrs x).length ids * (x.length + 1) + p]? = some (i, ids, p) := by
  have ⟨hL, hD⟩ := (mem_words _ _ _).mp hids
  have hds : ∀ a ∈ ids, a < (subStrs x).length := fun a ha => List.mem_range.mp (hD a ha)
  have hw := words_get_rank (dictionary_pos x) ids hds
  rw [hL] at hw
  have hRank := (List.getElem?_eq_some_iff.mp hw).1
  have hWord := (List.getElem?_eq_some_iff.mp hw).2
  have hg := get_flatMap_at (fun js : List Nat => (List.range (x.length + 1)).map (fun q => (i, js, q)))
    (words (List.range (subStrs x).length) r.arity) (wordRank (subStrs x).length ids) hRank p (by simp; omega)
  have hlen : (((words (List.range (subStrs x).length) r.arity).take (wordRank (subStrs x).length ids)).flatMap
      (fun js => (List.range (x.length + 1)).map (fun q => (i, js, q)))).length =
      wordRank (subStrs x).length ids * (x.length + 1) := by
    simp only [List.length_flatMap, List.length_map, List.length_range]
    rw [List.map_const', List.sum_replicate_nat, List.length_take, Nat.min_eq_left (Nat.le_of_lt hRank)]
  rw [hlen] at hg
  unfold ruleKeys
  rw [hr, hg, hWord, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

theorem ruleOffset_length {g : MGrammar} {x : List Char} {i : Nat} (hi : i ≤ g.rules.length) :
    (((List.range g.rules.length).take i).flatMap (ruleKeys g x)).length = ruleOffset g x i := by
  rw [List.take_range, Nat.min_eq_left hi, List.length_flatMap]
  unfold ruleOffset
  congr 1
  apply List.map_congr_left
  intro j _
  exact ruleKeys_length g x j

/-- Every relevant table entry has the advertised arithmetic address. -/
theorem keys_get_address {g : MGrammar} {x : List Char} {i : Nat} {r : MRule} {ids : List Nat} {p : Nat}
    (hr : ruleAtM g.rules i = some r)
    (hids : ids ∈ words (List.range (subStrs x).length) r.arity) (hp : p ≤ x.length) :
    (keys g x)[address g x i ids p]? = some (i, ids, p) := by
  have hi := ruleAtM_lt hr
  have hinner := ruleKeys_get hr hids hp
  have hj := (List.getElem?_eq_some_iff.mp hinner).1
  have hg := get_flatMap_at (ruleKeys g x) (List.range g.rules.length) i (by simpa using hi)
    (wordRank (subStrs x).length ids * (x.length + 1) + p) (by simpa using hj)
  rw [ruleOffset_length (Nat.le_of_lt hi)] at hg
  change (keys g x)[ruleOffset g x i + (wordRank (subStrs x).length ids * (x.length + 1) + p)]? = _ at hg
  simp only [List.getElem_range] at hg
  simpa only [address, Nat.add_assoc] using hg.trans hinner

/-- Arithmetic-address lookup agrees with the semantic table, including interval aliases. -/
theorem pack_get_address {g : MGrammar} {x : List Char} {T : Nat → List (List Char) → Val}
    {i : Nat} {r : MRule} {ids : List Nat} {p : Nat}
    (hr : ruleAtM g.rules i = some r)
    (hids : ids ∈ words (List.range (subStrs x).length) r.arity) (hp : p ≤ x.length) :
    resultDecode ((pack g x T).getD (address g x i ids p) 0) = valAt (T i (ids.map (literalAt x))) p := by
  simp only [pack, List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [keys_get_address hr hids hp]
  exact resultDecode_code _

end Shallot.MacroPeg.CBV
