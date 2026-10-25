import MacroPeg.CBV.MutualFieldSyntax
import MacroPeg.CBVtoCBN.Routing

namespace Shallot.MacroPeg.CBV.MutualFieldSyntax

theorem transfer_rules_length (arity : Nat) (d : Char) (js : List Nat) (e : MExp) :
    (TupleFieldTransfer.rules arity d js e).length=arity+1 := by simp [TupleFieldTransfer.rules]

theorem flatMap_rule {α : Type} (ss : List α) (F : α → List MRule) (i : Nat) (s : α)
    (hs : ss[i]?=some s) (slot : Nat) (hslot : slot<(F s).length) :
    ruleAtM (ss.flatMap F) (((ss.take i).flatMap F).length + slot)=ruleAtM (F s) slot := by
  induction ss generalizing i with
  | nil => simp at hs
  | cons a ss ih =>
    cases i with
    | zero =>
      have he : a=s := by simpa using hs
      subst s
      simp only [List.take_zero,List.flatMap_nil,List.length_nil,Nat.zero_add,List.flatMap_cons,
        ruleAtM_eq_getElem?,List.getElem?_append_left hslot]
    | succ i =>
      have ht : ss[i]?=some s := by simpa only [List.getElem?_cons_succ] using hs
      simp only [List.take_succ_cons,List.flatMap_cons,List.length_append]
      rw [Nat.add_assoc,CBVtoCBN.ruleAtM_append_offset]
      exact ih i ht

theorem source_installed (bodies : List MExp) (headers : List Header) (d : Char) :
    RecursiveParserStability.Installed bodies (source bodies headers d) :=
  DelimitedCopySyntax.installed_append _ _

theorem target_installed (bodies : List MExp) (headers : List Header) (d : Char) :
    RecursiveParserStability.Installed bodies (target bodies headers d) :=
  DelimitedCopySyntax.installed_append _ _

theorem source_row (bodies : List MExp) (headers : List Header) (d : Char) (i : Nat) (s : Header)
    (hs : headers[i]?=some s) :
    ruleAtM (source bodies headers d).rules (bodies.length+i)=
      some ⟨s.arity,TupleFieldTransfer.sourceBody d s.pattern s.body⟩ := by
  simp [source,ruleAtM_eq_getElem?,List.getElem?_append_right,List.getElem?_map,hs]

theorem target_block (bodies : List MExp) (headers : List Header) (d : Char) (i : Nat) (s : Header)
    (hs : headers[i]?=some s) (slot : Nat) (hslot : slot<s.arity+1) :
    ruleAtM (target bodies headers d).rules (address bodies.length headers i+slot)=
      ruleAtM (TupleFieldTransfer.rules s.arity d s.pattern (emit bodies.length headers d s.body)) slot := by
  have hl : ((headers.take i).flatMap (fun s =>
      TupleFieldTransfer.rules s.arity d s.pattern (emit bodies.length headers d s.body))).length=
      ((headers.take i).map (fun s => s.arity+1)).sum := by simp [List.length_flatMap,transfer_rules_length]
  unfold target address
  rw [show bodies.length+((headers.take i).map (fun s => s.arity+1)).sum+slot=
      (bodies.map (fun b => MRule.mk 0 b)).length+
        (((headers.take i).flatMap (fun s => TupleFieldTransfer.rules s.arity d s.pattern
          (emit bodies.length headers d s.body))).length+slot) by simp only [List.length_map,hl]; omega,
    CBVtoCBN.ruleAtM_append_offset]
  exact flatMap_rule headers _ i s hs slot (by rw [transfer_rules_length]; exact hslot)

theorem target_rows (bodies : List MExp) (headers : List Header) (d : Char) (i : Nat) (s : Header)
    (hs : headers[i]?=some s) :
    TupleFieldTransfer.Installed (target bodies headers d) (address bodies.length headers i)
      s.arity d s.pattern (emit bodies.length headers d s.body) := by
  constructor
  · intro j hj
    exact (target_block bodies headers d i s hs j (by omega)).trans
      (TupleFieldTransfer.rules_projection _ _ _ _ j hj)
  · exact (target_block bodies headers d i s hs s.arity (by omega)).trans
      (TupleFieldTransfer.rules_entry _ _ _ _)

theorem source_firstOrder_grammar (bodies : List MExp) (headers : List Header) (d : Char)
    (hv : Valid bodies headers d) : (source bodies headers d).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hr
    exact RecursiveParserStability.lexical_firstOrder _ b (hv.library b hb)
  · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    exact ⟨DelimiterTemplate.compile_firstOrder _ _,source_firstOrder _ _ _ _ _ (hv.headers s hs).body⟩

theorem target_firstOrder_grammar (bodies : List MExp) (headers : List Header) (d : Char)
    (hv : Valid bodies headers d) : (target bodies headers d).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hr
    exact RecursiveParserStability.lexical_firstOrder _ b (hv.library b hb)
  · obtain ⟨s,hs,hr⟩ := List.mem_flatMap.mp hr
    exact TupleFieldTransfer.rules_firstOrder _ _ _ _ (emit_firstOrder _ _ _ _) r hr

theorem rule_count (bodies : List MExp) (headers : List Header) (d : Char) :
    (target bodies headers d).rules.length=bodies.length+(headers.map (fun s => s.arity+1)).sum := by
  simp [target,List.length_flatMap,transfer_rules_length]

end Shallot.MacroPeg.CBV.MutualFieldSyntax
