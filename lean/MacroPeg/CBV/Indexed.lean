import MacroPeg.Properties.DecideCBV
import MacroPeg.Properties.DecideCost

namespace Shallot.MacroPeg.CBV

/-- A partial result has one numeric code: bottom, failure, or a remaining length. -/
def resultCode : Res → Nat
  | none => 0
  | some none => 1
  | some (some p) => p + 2

def resultDecode : Nat → Res
  | 0 => none
  | 1 => some none
  | p + 2 => some (some p)

theorem resultDecode_code (r : Res) : resultDecode (resultCode r) = r := by
  cases r with
  | none => rfl
  | some r => cases r <;> rfl

theorem get_idxOf {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α} (h : a ∈ l) :
    l[l.idxOf a]? = some a := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    by_cases he : b = a
    · subst b; simp
    · have hm : a ∈ l := by simpa [Ne.symm he] using h
      have hb : (b == a) = false := Bool.eq_false_iff.mpr (fun hb => he (eq_of_beq hb))
      simpa [List.idxOf_cons, hb] using ih hm

/-- Canonical identifiers for the finite dictionary of input substrings. -/
def literalId (x w : List Char) : Nat := (subStrs x).idxOf w

def literalAt (x : List Char) (i : Nat) : List Char := (subStrs x).getD i []

theorem literalAt_id {x w : List Char} (h : w ∈ subStrs x) : literalAt x (literalId x w) = w := by
  simp only [literalAt, literalId, List.getD_eq_getElem?_getD]
  rw [get_idxOf h]
  rfl

theorem literalId_lt {x w : List Char} (h : w ∈ subStrs x) : literalId x w < (subStrs x).length :=
  List.idxOf_lt_length_iff.mpr h

/-- A table address consists of a rule, argument identifiers, and a position. -/
abbrev Key := Nat × List Nat × Nat

def keys (g : MGrammar) (x : List Char) : List Key :=
  (List.range g.rules.length).flatMap (fun i =>
    match ruleAtM g.rules i with
    | none => []
    | some r => (words (List.range (subStrs x).length) r.arity).flatMap (fun ids =>
        (List.range (x.length + 1)).map (fun p => (i, ids, p))))

def pack (g : MGrammar) (x : List Char) (T : Nat → List (List Char) → Val) : List Nat :=
  (keys g x).map (fun k => resultCode (valAt (T k.1 (k.2.1.map (literalAt x))) k.2.2))

def lookup (g : MGrammar) (x : List Char) (row : List Nat) (i : Nat) (ids : List Nat) (p : Nat) : Res :=
  resultDecode (row.getD ((keys g x).idxOf (i, ids, p)) 0)

def unpack (g : MGrammar) (x : List Char) (row : List Nat) (i : Nat) (W : List (List Char)) : Val :=
  (List.range (x.length + 1)).map (fun p => lookup g x row i (W.map (literalId x)) p)

theorem mem_keys {g : MGrammar} {x : List Char} {i : Nat} {r : MRule} {ids : List Nat} {p : Nat}
    (hr : ruleAtM g.rules i = some r) (hi : i < g.rules.length)
    (hids : ids ∈ words (List.range (subStrs x).length) r.arity) (hp : p ≤ x.length) :
    (i, ids, p) ∈ keys g x := by
  unfold keys
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  rw [hr]
  exact List.mem_flatMap.mpr ⟨ids, hids, List.mem_map.mpr ⟨p, List.mem_range.mpr (by omega), rfl⟩⟩

theorem ruleAtM_lt {rs : List MRule} {i : Nat} {r : MRule} (h : ruleAtM rs i = some r) : i < rs.length := by
  induction rs generalizing i with
  | nil => cases i <;> simp [ruleAtM] at h
  | cons a rs ih => cases i with
    | zero => simp
    | succ i => exact Nat.succ_lt_succ (ih h)

theorem ids_mem_words {x : List Char} {k : Nat} {W : List (List Char)}
    (h : W ∈ words (subStrs x) k) : W.map (literalId x) ∈ words (List.range (subStrs x).length) k := by
  have ⟨hl, hm⟩ := (mem_words _ _ _).mp h
  apply (mem_words _ _ _).mpr
  refine ⟨by simpa using hl, ?_⟩
  intro v hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  exact List.mem_range.mpr (literalId_lt (hm w hw))

theorem lookup_pack {g : MGrammar} {x : List Char} {T : Nat → List (List Char) → Val}
    {i : Nat} {r : MRule} {W : List (List Char)} {p : Nat}
    (hr : ruleAtM g.rules i = some r) (hW : W ∈ words (subStrs x) r.arity) (hp : p ≤ x.length) :
    lookup g x (pack g x T) i (W.map (literalId x)) p = valAt (T i W) p := by
  have hk := mem_keys hr (ruleAtM_lt hr) (ids_mem_words hW) hp
  have hm : (W.map (literalId x)).map (literalAt x) = W := by
    rw [List.map_map]
    apply Eq.trans (b := W.map id)
    · apply List.map_congr_left
      intro w hw
      exact literalAt_id (((mem_words _ _ _).mp hW).2 w hw)
    · exact List.map_id _
  simp only [lookup, pack, List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [get_idxOf hk]
  simp only [Option.map_some, Option.getD_some, hm, resultDecode_code]

theorem unpack_pack (g : MGrammar) (x : List Char) (T : Nat → List (List Char) → Val) :
    AgreeV g x (unpack g x (pack g x T)) T := by
  intro i r W hr hW p hp
  have hl : p < x.length + 1 := by omega
  simp only [unpack, valAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hl, Option.map_some, Option.getD_some]
  exact lookup_pack hr hW hp

theorem key_valid {g : MGrammar} {x : List Char} {k : Key} (h : k ∈ keys g x) :
    ∃ r, ruleAtM g.rules k.1 = some r ∧ k.2.1 ∈ words (List.range (subStrs x).length) r.arity ∧ k.2.2 ≤ x.length := by
  obtain ⟨i, hi, hk⟩ := List.mem_flatMap.mp h
  cases hr : ruleAtM g.rules i with
  | none => simp only [hr, List.not_mem_nil] at hk
  | some r =>
    rw [hr] at hk
    obtain ⟨ids, hids, hk⟩ := List.mem_flatMap.mp hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
    exact ⟨r, hr, hids, by change p ≤ x.length; have := List.mem_range.mp hp; omega⟩

/-- The numeric row contains exactly the finite number of entries already used by the saturation proof. -/
theorem keys_length (g : MGrammar) (x : List Char) : (keys g x).length = iterBoundV g x := by
  unfold keys iterBoundV
  rw [List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  cases hr : ruleAtM g.rules i with
  | none => rfl
  | some r =>
    simp only [List.length_flatMap, List.length_map, List.length_range]
    rw [List.map_const', List.sum_replicate_nat, length_words, List.length_range, length_words]

theorem pack_length (g : MGrammar) (x : List Char) (T : Nat → List (List Char) → Val) :
    (pack g x T).length = iterBoundV g x := by simp [pack, keys_length]

theorem resultCode_bound {n : Nat} {r : Res} (h : OkR n r) : resultCode r ≤ n + 2 := by
  cases r with
  | none => simp [resultCode]
  | some r => cases r with
    | none => simp [resultCode]
    | some p => have hp := h p rfl; simp only [resultCode]; omega

theorem pack_bound {g : MGrammar} {x : List Char} {T : Nat → List (List Char) → Val}
    (hT : OkTV x.length T) : ∀ v ∈ pack g x T, v ≤ x.length + 2 := by
  intro v hv
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hv
  exact resultCode_bound (hT _ _ _)

/-- Construct a finite next row using only the preceding numeric row for rule calls. -/
def round (s : Strategy) (g : MGrammar) (x : List Char) (row : List Nat) : List Nat :=
  (keys g x).map (fun k => match ruleAtM g.rules k.1 with
    | none => 0
    | some r => resultCode (evV g x s (unpack g x row) (k.2.1.map (literalAt x)) r.body k.2.2))

/-- One finite-row step is exactly one round of the existing CBV semantics. -/
theorem round_pack (s : Strategy) (g : MGrammar) (x : List Char) (m : Nat) :
    round s g x (pack g x (tblV g x s m)) = pack g x (tblV g x s (m + 1)) := by
  unfold round
  change (keys g x).map _ = (keys g x).map _
  apply List.map_congr_left
  intro k hk
  obtain ⟨r, hr, _, hp⟩ := key_valid hk
  simp only [hr]
  have ht : valAt (tblV g x s (m + 1) k.1 (k.2.1.map (literalAt x))) k.2.2 =
      evV g x s (tblV g x s m) (k.2.1.map (literalAt x)) r.body k.2.2 := by
    simp only [tblV, hr, valAt_rangeMap, if_pos hp]
  rw [ht]
  congr 1
  exact (evV_agree (unpack_pack g x (tblV g x s m)).symm (tblV_ok g x s m) r.body k.2.2 hp).symm

def iterate (s : Strategy) (g : MGrammar) (x : List Char) : Nat → List Nat
  | 0 => List.replicate (keys g x).length 0
  | m + 1 => round s g x (iterate s g x m)

theorem iterate_pack (s : Strategy) (g : MGrammar) (x : List Char) (m : Nat) :
    iterate s g x m = pack g x (tblV g x s m) := by
  induction m with
  | zero => simp [iterate, pack, tblV, valAt, resultCode, List.map_const']
  | succ m ih => rw [iterate, ih, round_pack]

/-- The entire indexed iteration stays within polynomially many polynomial-size numeric entries. -/
theorem iterate_size (s : Strategy) (g : MGrammar) (x : List Char) (m : Nat) {K : Nat}
    (hK : ∀ r ∈ g.rules, r.arity ≤ K) :
    (iterate s g x m).length ≤ g.rules.length * (((x.length + 1) * (x.length + 1)) ^ K * (x.length + 1)) ∧
    (∀ v ∈ iterate s g x m, v ≤ x.length + 2) := by
  rw [iterate_pack]
  exact ⟨by rw [pack_length]; exact iterBoundV_le g x hK, pack_bound (tblV_ok g x s m)⟩

end Shallot.MacroPeg.CBV
