import MacroPeg.CBV.Indexed

namespace Shallot.MacroPeg.CBV

/-- The dictionary's entries have explicit source intervals, including repeated strings. -/
def spans (n : Nat) : List (Nat × Nat) :=
  (List.range (n + 1)).flatMap (fun p => (List.range (p + 1)).map (fun j => (p, j)))

def spanId (n p j : Nat) : Nat := (spans n).idxOf (p, min j p)

theorem spans_subStrs (x : List Char) :
    (spans x.length).map (fun pj => pre x pj.1 pj.2) = subStrs x := by
  simp [spans, subStrs, List.map_flatMap, List.map_map, Function.comp_def]

theorem span_mem {n p j : Nat} (hp : p ≤ n) : (p, min j p) ∈ spans n := by
  apply List.mem_flatMap.mpr
  refine ⟨p, List.mem_range.mpr (by omega), ?_⟩
  exact List.mem_map.mpr ⟨min j p, List.mem_range.mpr (by omega), rfl⟩

theorem spans_length (x : List Char) : (spans x.length).length = (subStrs x).length := by
  rw [← spans_subStrs]
  simp

theorem spanId_lt {x : List Char} {p j : Nat} (hp : p ≤ x.length) :
    spanId x.length p j < (subStrs x).length := by
  rw [← spans_length]
  exact List.idxOf_lt_length_iff.mpr (span_mem hp)

/-- A freshly consumed prefix is registered by its interval, without searching string values. -/
theorem literalAt_spanId {x : List Char} {p j : Nat} (hp : p ≤ x.length) :
    literalAt x (spanId x.length p j) = pre x p j := by
  unfold literalAt
  rw [← spans_subStrs]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  unfold spanId
  rw [get_idxOf (span_mem (j := j) hp)]
  change pre x p (min j p) = pre x p j
  unfold pre
  congr 1
  omega

/-- Row lookup accepts every valid dictionary identifier, including duplicate interval values. -/
theorem lookup_pack_ids {g : MGrammar} {x : List Char} {T : Nat → List (List Char) → Val}
    {i : Nat} {r : MRule} {ids : List Nat} {p : Nat}
    (hr : ruleAtM g.rules i = some r)
    (hids : ids ∈ words (List.range (subStrs x).length) r.arity) (hp : p ≤ x.length) :
    lookup g x (pack g x T) i ids p = valAt (T i (ids.map (literalAt x))) p := by
  have hk := mem_keys hr (ruleAtM_lt hr) hids hp
  simp only [lookup, pack, List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [get_idxOf hk]
  exact resultDecode_code _

end Shallot.MacroPeg.CBV
