import MacroPeg.CBV.ParTableau.FirstOrder

namespace Shallot.MacroPeg.CBV.ParTableau

open PrefixCounters
open Complexity (TM)

theorem nodeRules_length {k : Nat} (M : TM k) (digits base : Nat) (node : Node k) :
    (nodeRules M digits base node).length = slotSize digits := by simp [nodeRules]

theorem rawRules_bound {k : Nat} (M : TM k) (digits base : Nat) (node : Node k) :
    (rawRules M digits base node).length < slotSize digits := by
  cases node <;> simp only [rawRules, timeRules, List.length_append, List.length_cons,
    List.length_nil, clockBlock_length, tupleRules_length, slotSize] <;> omega

theorem state_mem {k : Nat} (M : TM k) (q : Nat) (hq : q < M.nq) : Node.state q ∈ nodes M := by
  simp only [nodes, List.mem_append, List.mem_map]
  exact .inl (.inl (.inl (.inl (.inl ⟨q, List.mem_range.mpr hq, rfl⟩))))

theorem head_mem {k : Nat} (M : TM k) (i : Fin k) : Node.head i ∈ nodes M := by
  simp only [nodes, List.mem_append, List.mem_map]
  exact .inl (.inl (.inl (.inl (.inr ⟨i, List.mem_finRange i, rfl⟩))))

theorem cell_mem {k : Nat} (M : TM k) (i : Fin k) (s : Nat) (hs : s < M.na) :
    Node.cell i s ∈ nodes M := by
  simp only [nodes, List.mem_append]
  exact .inl (.inl (.inl (.inr (List.mem_flatMap.mpr
    ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩⟩))))

theorem read_mem {k : Nat} (M : TM k) (i : Fin k) (s : Nat) (hs : s < M.na) :
    Node.read i s ∈ nodes M := by
  simp only [nodes, List.mem_append]
  exact .inl (.inl (.inr (List.mem_flatMap.mpr
    ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩⟩)))

theorem incHead_mem {k : Nat} (M : TM k) (i : Fin k) : Node.incHead i ∈ nodes M := by
  simp only [nodes, List.mem_append]
  exact .inl (.inr (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))

theorem decHead_mem {k : Nat} (M : TM k) (i : Fin k) : Node.decHead i ∈ nodes M := by
  simp only [nodes, List.mem_append]
  exact .inr (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

/-- Every physical address resolves to the exact generated source rule.
This includes the predecessor helpers and every tuple-search layer. -/
theorem compile_at {k : Nat} (M : TM k) (digits : Nat) (node : Node k) (hn : node ∈ nodes M)
    (j : Nat) (hj : j < slotSize digits) :
    ruleAtM (compile M digits).rules (address M digits node + j) =
      some (((rawRules M digits (address M digits node) node)[j]?).getD failRule) := by
  let blocks := (nodes M).map (fun node => nodeRules M digits (address M digits node) node)
  have hb : ∀ b ∈ blocks, b.length = slotSize digits := by
    intro b hm
    obtain ⟨node, _, rfl⟩ := List.mem_map.mp hm
    exact nodeRules_length _ _ _ _
  have hi : (nodes M).idxOf node < blocks.length := by
    simpa only [blocks, List.length_map] using List.idxOf_lt_length_iff.mpr hn
  have hh := CBVtoCBN.ruleAtM_fixedBlocks blocks (slotSize digits) hb ((nodes M).idxOf node) j hi hj
  have hget := get_idxOf hn
  simp only [blocks, List.getElem?_map, hget, Option.map_some, Option.getD_some] at hh
  change ruleAtM ([_ , _] ++ blocks.flatten) _ = _
  rw [show address M digits node + j = [MRule.mk 2 (equalBody 0),
      MRule.mk digits MExp.failAlways].length + (slotSize digits * (nodes M).idxOf node + j) by
        simp only [address, List.length_cons, List.length_nil]; omega,
    CBVtoCBN.ruleAtM_append_offset, hh]
  simp only [nodeRules, ruleAtM_eq_getElem?, List.getElem?_map, List.getElem?_range hj,
    Option.map_some]

theorem compile_raw_at {k : Nat} (M : TM k) (digits : Nat) (node : Node k)
    (hn : node ∈ nodes M) (j : Nat) (hj : j < (rawRules M digits (address M digits node) node).length) :
    ruleAtM (compile M digits).rules (address M digits node + j) =
      (rawRules M digits (address M digits node) node)[j]? := by
  rw [compile_at M digits node hn j (Nat.lt_trans hj (rawRules_bound _ _ _ _)),
    List.getElem?_eq_getElem hj]
  rfl

theorem equal_rule {k : Nat} (M : TM k) (digits : Nat) :
    ruleAtM (compile M digits).rules 0 = some ⟨2, equalBody 0⟩ := rfl

theorem overflow_rule {k : Nat} (M : TM k) (digits : Nat) :
    ruleAtM (compile M digits).rules 1 = some ⟨digits, MExp.failAlways⟩ := rfl

end Shallot.MacroPeg.CBV.ParTableau
