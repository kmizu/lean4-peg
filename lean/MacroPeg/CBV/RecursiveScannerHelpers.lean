import MacroPeg.CBV.FrozenCaptureControl
import MacroPeg.CBV.RecursiveCaptureSafety
import MacroPeg.CBV.DynamicScannerCapture

namespace Shallot.MacroPeg.CBV.RecursiveScannerHelpers
open RegularCaptureProduct (Node component)
open RecursiveParserStability (Lexical Installed)
open DynamicScannerCapture (observer)

def base {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) : Nat :=
  (RegularCaptureProduct.grammar nodes (observer M)).rules.length

def rules {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) : List MRule :=
  (RegularCaptureProduct.grammar nodes (observer M)).rules ++
    StatefulScanner.block M (fun _ => true) (base M nodes)

def bodies {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) : List MExp :=
  (rules M nodes).map MRule.body

def grammar {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node)
    (extra : List MRule) : MGrammar := ⟨rules M nodes++extra⟩

theorem length {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) :
    (bodies M nodes).length=base M nodes+n := by
  simp [bodies,rules,base,StatefulScanner.block_length]

theorem branches_lexical {n : Nat} (base : Nat) (arcs : List (Char × Fin n)) :
    Lexical (base+n) (StatefulScanner.branches base (.eps) arcs) := by
  induction arcs with
  | nil => trivial
  | cons arc arcs ih =>
    exact ⟨⟨True.intro,⟨True.intro,by dsimp [Lexical]; omega⟩⟩,True.intro,ih⟩

theorem valid {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node)
    (hNodes : RegularCaptureProduct.Valid nodes) : RecursiveParserStability.Valid (bodies M nodes) := by
  intro e he
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp he
  rcases List.mem_append.mp hr with hr | hr
  · have h := RegularCaptureProduct.component_valid nodes hNodes (observer M) (DynamicScannerCapture.observer_valid M).1
      r.body (List.mem_map.mpr ⟨r,hr,rfl⟩)
    apply RegularCaptureProduct.lexical_mono (show (component nodes (observer M)).length≤(bodies M nodes).length by
      simp [component,length,base]) _ h
  · obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hr
    simpa only [length,StatefulScanner.terminal,if_true] using branches_lexical (base M nodes) (M.arcs q)

theorem nullary {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) :
    ∀ r∈rules M nodes, r.arity=0 := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨v,_,rfl⟩ := List.mem_map.mp hr; rfl
    · obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hr; rfl
  · obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hr; rfl

theorem installed {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node)
    (extra : List MRule) : Installed (bodies M nodes) (grammar M nodes extra) := by
  intro i e hi
  have hl : i<(rules M nodes).length := by
    simpa [bodies] using (List.getElem?_eq_some_iff.mp hi).1
  have hr := List.getElem?_eq_getElem hl
  have he : ((rules M nodes)[i]).body=e := by
    simpa only [bodies,List.getElem?_map,hr,Option.map_some,Option.some.injEq] using hi
  have hz := nullary M nodes _ (List.getElem_mem hl)
  simp only [grammar,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left hl,hr]
  congr 1
  cases h : (rules M nodes)[i]
  simp only [h] at hz he
  simp_all

theorem product_installed {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node)
    (extra : List MRule) : Installed (component nodes (observer M)) (grammar M nodes extra) := by
  simpa only [grammar,rules,List.append_assoc] using
    RegularCaptureProduct.component_installed nodes (observer M)
      (StatefulScanner.block M (fun _ => true) (base M nodes)++extra)

theorem originals_installed {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node)
    (extra : List MRule) : Installed (nodes.map RegularCaptureProduct.body) (grammar M nodes extra) := by
  simpa only [grammar,rules,List.append_assoc,FilteredOverlapCaller.extend] using
    RecursiveCaptureSafety.nodes_installed nodes (observer M)
      (StatefulScanner.block M (fun _ => true) (base M nodes)++extra)

theorem scanner_rule {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node)
    (extra : List MRule) (q : Fin n) :
    ruleAtM (grammar M nodes extra).rules (base M nodes+q.val)=
      some ⟨0,StatefulScanner.branches (base M nodes) (.eps) (M.arcs q)⟩ := by
  have hb : base M nodes+q.val<(rules M nodes).length := by
    simp only [rules,List.length_append,StatefulScanner.block_length]
    dsimp [base]; omega
  simp only [grammar,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left hb]
  unfold rules
  rw [List.getElem?_append_right (by dsimp [base]; omega)]
  simpa only [base,Nat.add_sub_cancel_left,ruleAtM_eq_getElem?,StatefulScanner.terminal,if_true] using
    StatefulScanner.block_rule M (fun _ => true) (base M nodes) q

/-- A real residual scanner contributes at least input-length-plus-one
entries to the helper component's physical stabilization bound. -/
theorem floor_bound {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node)
    (state : Fin n) (x : List Char) : x.length+1≤RecursiveParserStability.floor (bodies M nodes) x := by
  let g := RecursiveParserStability.grammar (bodies M nodes)
  have hi : base M nodes+state.val<(bodies M nodes).length := by rw [length]; omega
  have he := RecursiveParserStability.installed (bodies M nodes) _ _ (List.getElem?_eq_getElem hi)
  change ruleAtM g.rules (base M nodes+state.val)=some ⟨0,(bodies M nodes)[base M nodes+state.val]⟩ at he
  have hmem : x.length+1 ∈ (List.range g.rules.length).map (fun i =>
      match ruleAtM g.rules i with
      | some r => (words (subStrs x) r.arity).length*(x.length+1)
      | none => 0) := by
    apply List.mem_map.mpr
    refine ⟨base M nodes+state.val,List.mem_range.mpr ?_,?_⟩
    · simpa [g,RecursiveParserStability.grammar] using hi
    · simp [he,words]
  have le_sum : ∀ (xs : List Nat) (a : Nat), a∈xs → a≤xs.sum := by
    intro xs
    induction xs with
    | nil => intro a h; cases h
    | cons b xs ih =>
      intro a h
      rcases List.mem_cons.mp h with rfl | h
      · simp only [List.sum_cons]; omega
      · have := ih a h; simp only [List.sum_cons]; omega
  have hh : x.length+1≤iterBoundV g x := le_sum _ _ hmem
  exact Nat.le_trans hh (by dsimp [g,RecursiveParserStability.floor]; omega)

/-- Recursive captures and product observers share the actual frozen
prefix with relocated scanner rules; the scan still runs on original input. -/
theorem scanner_eval {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node)
    (extra : List MRule) (q : Fin n) (x : List Char) (s : Strategy) (k p : Nat)
    (E : List (List Char)) (hp : p≤x.length) :
    let g := grammar M nodes extra
    evV g x s (RecursiveParserStability.frozen (bodies M nodes) g x s k) E
      (.call (base M nodes+q.val) []) p=some (some (StatefulScanner.run M q (sfx x p)).2.length) := by
  dsimp only []
  have hr := scanner_rule M nodes extra q
  have hcall (T : ClockFreezing.Table) :
      evV (grammar M nodes extra) x s T E (.call (base M nodes+q.val) []) p=
        valAt (T (base M nodes+q.val) []) p := by
    cases s <;> simp [evV,hr,evParArgs,evSeqArgs]
  rw [hcall]
  unfold RecursiveParserStability.frozen
  rw [ClockFreezing.frozen_rows _ _ _ _ _ k _ (by simp [RecursiveParserStability.pick,length,q.isLt]) []]
  simpa only [StatefulScanner.terminal,if_true] using
    StatefulScanner.query_eval M (fun _ => true) (grammar M nodes extra) (base M nodes)
      (fun q => by simpa only [StatefulScanner.terminal,if_true] using scanner_rule M nodes extra q)
      x s p hp (RecursiveParserStability.floor (bodies M nodes) x)
      (by have := floor_bound M nodes q x; omega) q

end Shallot.MacroPeg.CBV.RecursiveScannerHelpers
