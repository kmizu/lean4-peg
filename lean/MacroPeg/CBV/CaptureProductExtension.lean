import MacroPeg.CBV.PeriodicCaptureMachine

/-! The generated product is an independent zero-arity PEG component and
can be installed before actual parameter-bearing caller rules. -/
namespace Shallot.MacroPeg.CBV.RegularCaptureProduct
open ClockFreezing (Table)
open RecursiveParserStability (Lexical Installed)

def component (nodes : List Node) (D : Machine) : List MExp :=
  (grammar nodes D).rules.map MRule.body

theorem key_bound (nodes : List Node) (D : Machine) (hD : 0<D.width)
    (i q r : Nat) (hi : i<nodes.length) (hq : q<D.width) (hr : r<D.width) :
    key nodes D i q r<(grammar nodes D).rules.length := by
  have hh := filter_rule nodes D hD i q r hi hq hr
  rw [ruleAtM_eq_getElem?] at hh
  exact (List.getElem?_eq_some_iff.mp hh).1

theorem lexical_mono {n m : Nat} (h : n≤m) : ∀ e, Lexical n e → Lexical m e
  | .call _ [], he => Nat.lt_of_lt_of_le he h
  | .seq a b, he | .alt a b, he => ⟨lexical_mono h a he.1,lexical_mono h b he.2⟩
  | .star a, he | .notP a, he => lexical_mono h a he
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
  | .param _, he | .call _ (_::_), he | .dbg _, he | .lam _ _, he
  | .callParam _ _, he | .invoke _ _ _, he => False.elim he

theorem choice_lexical (n : Nat) : ∀ es, (∀ e ∈ es, Lexical n e) → Lexical n (choice es)
  | [], _ => trivial
  | e::es, h => ⟨h e (by simp),choice_lexical n es (fun e he => h e (by simp [he]))⟩

theorem core_lexical (nodes : List Node) (hNodes : Valid nodes) (D : Machine) (hD : 0<D.width)
    (i q r : Nat) (hi : i<nodes.length) (hq : q<D.width) (hr : r<D.width) :
    Lexical (grammar nodes D).rules.length (core nodes D i nodes[i] q r) := by
  have hlen : nodes.length≤(grammar nodes D).rules.length := by simp [grammar]
  have hvalid := hNodes nodes[i] (List.getElem_mem hi)
  have hc (a q r : Nat) (ha : a<nodes.length) (hq : q<D.width) (hr : r<D.width) :
      Lexical (grammar nodes D).rules.length (call nodes D a q r) := key_bound nodes D hD a q r ha hq hr
  have hs (a b : Nat) (ha : a<nodes.length) (hb : b<nodes.length) :
      Lexical (grammar nodes D).rules.length (select nodes D a b q r) := by
    apply choice_lexical
    intro e he
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp he
    exact ⟨hc a q t ha hq (List.mem_range.mp ht),hc b t r hb (List.mem_range.mp ht) hr⟩
  cases he : nodes[i] with
  | lit w => simp only [core]; split <;> trivial
  | seq a b =>
    simp only [he] at hvalid
    exact hs a b hvalid.1 hvalid.2
  | alt a b =>
    simp only [he] at hvalid
    have ha := hvalid.1
    have hb := hvalid.2
    exact ⟨⟨Nat.lt_of_lt_of_le ha hlen,hc a q r ha hq hr⟩,
      Nat.lt_of_lt_of_le ha hlen,hc b q r hb hq hr⟩
  | star a =>
    have ha : a<nodes.length := by simpa [he] using hvalid
    simp only [core]
    split <;> exact ⟨⟨Nat.lt_of_lt_of_le ha hlen,hs a i ha hi⟩,
      Nat.lt_of_lt_of_le ha hlen,True.intro⟩
  | notP a => simp only [core]; split <;> trivial

/-- Every generated filter reference stays inside the component. -/
theorem component_valid (nodes : List Node) (hNodes : Valid nodes)
    (D : Machine) (hD : 0<D.width) : RecursiveParserStability.Valid (component nodes D) := by
  intro e he
  obtain ⟨rule,hr,rfl⟩ := List.mem_map.mp he
  simp only [component,List.length_map]
  change Lexical (grammar nodes D).rules.length rule.body
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hr
    exact lexical_mono (by simp [grammar]) (body n) (helper_valid hNodes (body n) (List.mem_map.mpr ⟨n,hn,rfl⟩))
  · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hr
    have hi : (k.val/D.width)/D.width<nodes.length := by
      apply (Nat.div_lt_iff_lt_mul hD).mpr
      apply (Nat.div_lt_iff_lt_mul hD).mpr
      exact k.isLt
    have hq := Nat.mod_lt (k.val/D.width) hD
    have hr := Nat.mod_lt k.val hD
    have hn := List.getElem?_eq_getElem hi
    simp only [Option.getD_some,hn]
    exact ⟨Nat.lt_of_lt_of_le hi (by simp [grammar]),core_lexical nodes hNodes D hD _ _ _ hi hq hr⟩

/-- Parameter-bearing rules can be appended without changing any original
or product helper computation, at any physical round. -/
theorem component_installed (nodes : List Node) (D : Machine) (extra : List MRule) :
    Installed (component nodes D) ⟨(grammar nodes D).rules++extra⟩ := by
  intro i e hi
  have hl : i<(grammar nodes D).rules.length := by
    simpa [component] using (List.getElem?_eq_some_iff.mp hi).1
  have hr := List.getElem?_eq_getElem hl
  have he : ((grammar nodes D).rules[i]).body=e := by
    simpa only [component,List.getElem?_map,hr,Option.map_some,Option.some.injEq] using hi
  have hz : ∀ rule ∈ (grammar nodes D).rules, rule.arity=0 := by
    intro rule hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · obtain ⟨n,_,rfl⟩ := List.mem_map.mp hmem; rfl
    · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hmem; rfl
  have hzero := hz _ (List.getElem_mem hl)
  change ruleAtM ((grammar nodes D).rules++extra) i=some ⟨0,e⟩
  rw [ruleAtM_eq_getElem?,List.getElem?_append_left hl,hr]
  congr 1
  cases hn : (grammar nodes D).rules[i]
  simp_all

/-- Canonical helper queries are unchanged by appended caller rules or by
the caller's CBV strategy. -/
theorem extension_call_eq (nodes : List Node) (hNodes : Valid nodes)
    (D : Machine) (hD : 0<D.width) (extra : List MRule) (x : List Char)
    (s t : Strategy) (i p : Nat) (hi : i<(grammar nodes D).rules.length) (hp : p≤x.length)
    (E F : List (List Char)) :
    let g : MGrammar := ⟨(grammar nodes D).rules++extra⟩
    evV g x s (tblV g x s (iterBoundV g x)) E (.call i []) p =
      evV (grammar nodes D) x t
        (tblV (grammar nodes D) x t (iterBoundV (grammar nodes D) x)) F (.call i []) p := by
  have hi' : i<(component nodes D).length := by simpa [component] using hi
  have hn := List.getElem?_eq_getElem hi'
  have hg := component_installed nodes D extra
  have hb : Installed (component nodes D) (grammar nodes D) := by
    simpa using component_installed nodes D []
  have hrows := canonical_helpers_eq (component_valid nodes hNodes D hD) hg hb x s t i p hi' hp
  have hr := hg i (component nodes D)[i] hn
  have hs := hb i (component nodes D)[i] hn
  dsimp only []
  cases s <;> cases t <;> simpa only [evV,hr,hs,List.length_nil,ite_true,evSeqArgs,evParArgs] using hrows

/-- The same full filter specification holds inside actual caller grammars. -/
theorem extension_product_correct (nodes : List Node) (hNodes : Valid nodes)
    (D : Machine) (hD : D.Valid) (extra : List MRule) (x : List Char)
    (i q r p : Nat) (hi : i<nodes.length) (hq : q<D.width) (hr : r<D.width) (hp : p≤x.length) :
    let g : MGrammar := ⟨(grammar nodes D).rules++extra⟩
    let T := tblV g x .callByValueSeq (iterBoundV g x)
    evV g x .callByValueSeq T [] (call nodes D i q r) p =
      filtered D x q r p (evV g x .callByValueSeq T [] (.call i []) p) := by
  dsimp only []
  unfold call
  rw [extension_call_eq nodes hNodes D hD.1 extra x .callByValueSeq .callByValueSeq
      (key nodes D i q r) p (key_bound nodes D hD.1 i q r hi hq hr) hp [] [],
    extension_call_eq nodes hNodes D hD.1 extra x .callByValueSeq .callByValueSeq
      i p (Nat.lt_of_lt_of_le hi (by simp [grammar])) hp [] []]
  exact product_correct nodes hNodes D hD x i q r p hi hq hr hp

end Shallot.MacroPeg.CBV.RegularCaptureProduct
