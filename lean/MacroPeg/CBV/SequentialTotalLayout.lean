import MacroPeg.CBV.SequentialTotalSyntax
import MacroPeg.CBVtoCBN.CompilerLayout

namespace Shallot.MacroPeg.CBV.SequentialTotalSyntax

theorem mode_code_bound (m : Mode) : m.code<4 := by cases m <;> decide

theorem block_lookup (g : MGrammar) (i : Nat) (r : MRule)
    (hr : ruleAtM g.rules i=some r) (slot : Nat) (hs : slot<blockSize g) :
    ruleAtM (target g).rules (blockSize g*i+slot)=ruleAtM (ruleBlock g r) slot := by
  have hh := CBVtoCBN.ruleAtM_fixedBlocks (g.rules.map (ruleBlock g)) (blockSize g)
    (by intro b hb; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hb; exact block_length g r)
    i slot (by simp only [List.length_map]; exact ruleAtM_lt hr) hs
  have hi : (g.rules.map (ruleBlock g))[i]?=some (ruleBlock g r) := by
    simp only [List.getElem?_map,←ruleAtM_eq_getElem?,hr,Option.map_some]
  simpa only [target,List.flatMap_def,hi,Option.getD_some] using hh

theorem ordinary_rule (g : MGrammar) (i : Nat) (r : MRule)
    (hr : ruleAtM g.rules i=some r) (m : Mode) :
    ruleAtM (target g).rules (ordinaryIndex g i m)=
      some ⟨r.arity,(compile g g.rules.length r.body).get m⟩ := by
  rw [ordinaryIndex,block_lookup g i r hr m.code
    (by have := mode_code_bound m; unfold blockSize; omega)]
  cases m <;> rfl

theorem empty_rule (g : MGrammar) (i : Nat) (r : MRule)
    (hr : ruleAtM g.rules i=some r) (j : Nat) (hj : j≤g.rules.length) (m : Mode) :
    ruleAtM (target g).rules (emptyIndex g i j m)=some ⟨0,match j with
      | 0 => MExp.failAlways
      | k+1 => (compile g k (SequentialResultSyntax.emptyBody r)).get m⟩ := by
  simp only [emptyIndex,Nat.add_assoc]
  rw [block_lookup g i r hr (4*(j+1)+m.code)
    (by have := mode_code_bound m; unfold blockSize; omega)]
  have hh := CBVtoCBN.ruleAtM_fixedBlocks
    ((List.range (g.rules.length+1)).map (emptyRules g r)) 4
    (by intro b hb; obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hb; rfl)
    j m.code (by simp; omega) (mode_code_bound m)
  have hi : ((List.range (g.rules.length+1)).map (emptyRules g r))[j]?=some (emptyRules g r j) := by
    rw [List.getElem?_map,List.getElem?_range (by omega)]; rfl
  simp only [hi,Option.getD_some] at hh
  have hpos : 4*(j+1)+m.code=(ordinaryRules g r).length+(4*j+m.code) := by
    have : (ordinaryRules g r).length=4 := rfl
    omega
  rw [ruleBlock,hpos,CBVtoCBN.ruleAtM_append_offset,List.flatMap_def,hh]
  cases j <;> cases m <;> rfl

end Shallot.MacroPeg.CBV.SequentialTotalSyntax
