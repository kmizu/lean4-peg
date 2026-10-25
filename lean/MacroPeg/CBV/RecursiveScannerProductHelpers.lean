import MacroPeg.CBV.RecursiveScannerProductCompiler

namespace Shallot.MacroPeg.CBV.RecursiveScannerProductHelpers
open StatefulScanner (Machine)
open RecursiveScannerProductCompiler (helpers helperBodies offset valid)
open RecursiveParserStability (Lexical Installed)
open StatefulScannerProduct (pack)

abbrev grammar {n : Nat} (M : Machine n) (extra : List MRule) : MGrammar := ⟨helpers M++extra⟩

theorem helperBodies_length {n : Nat} (M : Machine n) :
    (helperBodies M).length=n+(n*(DynamicScannerCapture.observer M).width)*(n*(DynamicScannerCapture.observer M).width) := by
  simpa [helperBodies,offset] using RecursiveScannerProductCompiler.helpers_length M

private theorem branches_lexical {n : Nat} (size base : Nat) (hbase : base+n≤size)
    (terminal : MExp) (ht : Lexical size terminal) (arcs : List (Char × Fin n)) :
    Lexical size (StatefulScanner.branches base terminal arcs) := by
  induction arcs with
  | nil => exact ht
  | cons arc arcs ih =>
    exact ⟨⟨True.intro,⟨True.intro,by dsimp [Lexical]; have := arc.2.isLt; omega⟩⟩,True.intro,ih⟩

theorem lexical {n : Nat} (M : Machine n) : RecursiveParserStability.Valid (helperBodies M) := by
  intro e he
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp he
  have hl : (helperBodies M).length=offset M := by simp [helperBodies,offset]
  rw [hl]
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hr
    apply branches_lexical (offset M) 0 (by rw [RecursiveScannerProductCompiler.helpers_length]; omega)
    simp [StatefulScanner.terminal,Lexical]
  · obtain ⟨block,hblock,hr⟩ := List.mem_flatten.mp hr
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hblock
    obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hr
    apply branches_lexical (offset M) (n+t.val*(n*(DynamicScannerCapture.observer M).width))
    · have hb := Nat.mul_le_mul_right (n*(DynamicScannerCapture.observer M).width) (Nat.succ_le_of_lt t.isLt)
      rw [RecursiveScannerProductCompiler.helpers_length]
      simp only [Nat.succ_mul] at hb
      omega
    · unfold StatefulScanner.terminal
      split <;> trivial

theorem nullary {n : Nat} (M : Machine n) : ∀ r∈helpers M, r.arity=0 := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hr; rfl
  · obtain ⟨block,hblock,hr⟩ := List.mem_flatten.mp hr
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hblock
    obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hr; rfl

theorem installed {n : Nat} (M : Machine n) (extra : List MRule) :
    Installed (helperBodies M) (grammar M extra) := by
  intro i e hi
  have hl : i<(helpers M).length := by simpa [helperBodies] using (List.getElem?_eq_some_iff.mp hi).1
  have hr := List.getElem?_eq_getElem hl
  have he : ((helpers M)[i]).body=e := by
    simpa only [helperBodies,List.getElem?_map,hr,Option.map_some,Option.some.injEq] using hi
  have hz := nullary M _ (List.getElem_mem hl)
  simp only [grammar,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left hl,hr]
  congr 1
  cases h : (helpers M)[i]
  simp only [h] at hz he
  simp_all

theorem scanner_rule {n : Nat} (M : Machine n) (extra : List MRule) (q : Fin n) :
    ruleAtM (grammar M extra).rules q.val=some ⟨0,StatefulScanner.branches 0 .eps (M.arcs q)⟩ := by
  have hr := StatefulScanner.block_rule M (fun _ => true) 0 q
  simp only [Nat.zero_add,StatefulScanner.terminal,if_true] at hr
  exact SequentialRecursiveObserver.rule_append _ extra _ _
    (SequentialRecursiveObserver.rule_append _ _ _ _ hr)

theorem observed_grammar {n : Nat} (M : Machine n) (extra : List MRule) :
    grammar M extra=ObservedScannerDispatch.grammar M (DynamicScannerCapture.observer M) (valid M)
      (StatefulScanner.block M (fun _ => true) 0) extra := by
  simp only [grammar,helpers,ObservedScannerDispatch.grammar,StatefulScanner.block_length]

theorem floor_bound {n : Nat} (M : Machine n) (state : Fin n) (x : List Char) :
    x.length+1≤RecursiveParserStability.floor (helperBodies M) x := by
  let g := RecursiveParserStability.grammar (helperBodies M)
  have hi : state.val<(helperBodies M).length := by
    simp only [helperBodies_length]
    omega
  have he := RecursiveParserStability.installed (helperBodies M) _ _ (List.getElem?_eq_getElem hi)
  change ruleAtM g.rules state.val=some ⟨0,(helperBodies M)[state.val]⟩ at he
  have hmem : x.length+1 ∈ (List.range g.rules.length).map (fun i =>
      match ruleAtM g.rules i with
      | some r => (words (subStrs x) r.arity).length*(x.length+1)
      | none => 0) := by
    apply List.mem_map.mpr
    refine ⟨state.val,List.mem_range.mpr ?_,?_⟩
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

theorem scanner_eval {n : Nat} (M : Machine n) (extra : List MRule) (q : Fin n)
    (x : List Char) (s : Strategy) (k p : Nat) (E : List (List Char)) (hp : p≤x.length) :
    evV (grammar M extra) x s (RecursiveParserStability.frozen (helperBodies M) (grammar M extra) x s k) E
      (.call q.val []) p=some (some (StatefulScanner.run M q (sfx x p)).2.length) := by
  have hr := scanner_rule M extra q
  have hcall (T : ClockFreezing.Table) :
      evV (grammar M extra) x s T E (.call q.val []) p=valAt (T q.val []) p := by
    cases s <;> simp [evV,hr,evParArgs,evSeqArgs]
  rw [hcall]
  unfold RecursiveParserStability.frozen
  rw [ClockFreezing.frozen_rows _ _ _ _ _ k _ (by
    simp only [RecursiveParserStability.pick,helperBodies_length,decide_eq_true_eq]; omega) []]
  simpa only [Nat.zero_add,StatefulScanner.terminal,if_true] using
    StatefulScanner.query_eval M (fun _ => true) (grammar M extra) 0
      (fun r => by simpa only [Nat.zero_add,StatefulScanner.terminal,if_true] using scanner_rule M extra r)
      x s p hp (RecursiveParserStability.floor (helperBodies M) x)
      (by have := floor_bound M q x; omega) q

/-- Real selector entries are frozen actual helper rows. Continuations
remain at the current user round, rather than being physically frozen. -/
theorem entry_eval {n : Nat} (M : Machine n) (extra : List MRule) (q : Fin n)
    (a : Fin (DynamicScannerCapture.observer M).width)
    (target : Fin (n*(DynamicScannerCapture.observer M).width))
    (x : List Char) (s : Strategy) (k p : Nat) (E : List (List Char)) (hp : p≤x.length) :
    evV (grammar M extra) x s (RecursiveParserStability.frozen (helperBodies M) (grammar M extra) x s k) E
      (ObservedScannerDispatch.entry n q a target) p=
      some (if target=pack (StatefulScanner.run M q (sfx x p)).1
        (ObservedScanner.finish (DynamicScannerCapture.observer M) (valid M) a (ObservedScanner.consumed M q (sfx x p)))
        then some (StatefulScanner.run M q (sfx x p)).2.length else none) := by
  let D := DynamicScannerCapture.observer M
  let before := StatefulScanner.block M (fun _ => true) 0
  let index := n+target.val*(n*D.width)+(pack q a).val
  have hindex : index<(helperBodies M).length := by
    have ht := Nat.mul_le_mul_right (n*D.width) (Nat.succ_le_of_lt target.isLt)
    have hq := (pack q a).isLt
    simp only [Nat.succ_mul] at ht
    simp only [helperBodies_length]
    dsimp [index,D] at *
    omega
  have hr := installed M extra index (helperBodies M)[index] (List.getElem?_eq_getElem hindex)
  have hrow := ClockFreezing.frozen_rows (grammar M extra) x s
    (RecursiveParserStability.pick (helperBodies M)) (RecursiveParserStability.floor (helperBodies M) x) k
    index (by simp [RecursiveParserStability.pick,hindex]) []
  dsimp only [index,D] at hr hrow
  have he : evV (grammar M extra) x s (RecursiveParserStability.frozen (helperBodies M) (grammar M extra) x s k) E
      (ObservedScannerDispatch.entry n q a target) p=
      evV (grammar M extra) x s (tblV (grammar M extra) x s (RecursiveParserStability.floor (helperBodies M) x)) E
        (ObservedScannerDispatch.entry n q a target) p := by
    cases s <;> simpa only [ObservedScannerDispatch.entry,evV,hr,evParArgs,evSeqArgs,List.length_nil,ite_true]
      using congrArg (fun row => valAt row p) hrow
  rw [he,observed_grammar]
  simpa only [before,StatefulScanner.block_length] using
    ObservedScannerDispatch.entry_eval M D (valid M) before extra q a target x s E p
      (RecursiveParserStability.floor (helperBodies M) x) hp (by have := floor_bound M q x; omega)

theorem dispatch_eval {n : Nat} (M : Machine n) (extra : List MRule) (q : Fin n)
    (a : Fin (DynamicScannerCapture.observer M).width)
    (K : Fin (n*(DynamicScannerCapture.observer M).width) → MExp)
    (x : List Char) (s : Strategy) (k p : Nat) (E : List (List Char)) (hp : p≤x.length) :
    evV (grammar M extra) x s (RecursiveParserStability.frozen (helperBodies M) (grammar M extra) x s k) E
      (ObservedScannerDispatch.dispatch n q a K) p=
      evV (grammar M extra) x s (RecursiveParserStability.frozen (helperBodies M) (grammar M extra) x s k) E
        (K (pack (StatefulScanner.run M q (sfx x p)).1
          (ObservedScanner.finish (DynamicScannerCapture.observer M) (valid M) a (ObservedScanner.consumed M q (sfx x p)))))
        (StatefulScanner.run M q (sfx x p)).2.length := by
  unfold ObservedScannerDispatch.dispatch
  rw [CaptureTransitionProfile.choice_unique
    (chosen := pack (StatefulScanner.run M q (sfx x p)).1
      (ObservedScanner.finish (DynamicScannerCapture.observer M) (valid M) a (ObservedScanner.consumed M q (sfx x p))))]
  · rw [if_pos (by simp [ObservedScanner.states])]
  · intro target _
    have hv := entry_eval M extra q a target x s k p E hp
    by_cases ht : target=pack (StatefulScanner.run M q (sfx x p)).1
        (ObservedScanner.finish (DynamicScannerCapture.observer M) (valid M) a (ObservedScanner.consumed M q (sfx x p)))
    · rw [if_pos ht] at hv
      rw [evV_seq_ok hv,if_pos ht,ht]
    · rw [if_neg ht] at hv
      rw [evV_seq_fail hv,if_neg ht]

theorem dispatch_product_eval {n : Nat} (M : Machine n) (extra : List MRule) (q : Fin n)
    (a : Fin (DynamicScannerCapture.observer M).width)
    (K : Fin (n*(DynamicScannerCapture.observer M).width) → MExp)
    (x : List Char) (s : Strategy) (k p : Nat) (E : List (List Char)) (hp : p≤x.length) :
    evV (grammar M extra) x s (RecursiveParserStability.frozen (helperBodies M) (grammar M extra) x s k) E
      (ObservedScannerDispatch.dispatch n q a K) p=
      evV (grammar M extra) x s (RecursiveParserStability.frozen (helperBodies M) (grammar M extra) x s k) E
        (K (StatefulScanner.run (ObservedScanner.machine M (DynamicScannerCapture.observer M) (valid M)) (pack q a) (sfx x p)).1)
        (StatefulScanner.run (ObservedScanner.machine M (DynamicScannerCapture.observer M) (valid M)) (pack q a) (sfx x p)).2.length := by
  rw [dispatch_eval M extra q a K x s k p E hp,ObservedScanner.run_observed]

/-- The product header observes from the source's original position,
including the whole argument that Seq has already consumed. -/
theorem dispatch_handoff {n : Nat} (M : Machine n) (extra : List MRule) (q r : Fin n)
    (a : Fin (DynamicScannerCapture.observer M).width)
    (w x : List Char) (p j k : Nat) (hp : p≤x.length) (hj : j≤x.length)
    (hcap : sfx x p=w++sfx x j) (hstep : StatefulScanner.advance M q w=some r)
    (s : Strategy) (E : List (List Char)) (K : Fin (n*(DynamicScannerCapture.observer M).width) → MExp) :
    evV (grammar M extra) x s (RecursiveParserStability.frozen (helperBodies M) (grammar M extra) x s k) E
      (ObservedScannerDispatch.dispatch n q a K) p=
      evV (grammar M extra) x s (RecursiveParserStability.frozen (helperBodies M) (grammar M extra) x s k) E
        (ObservedScannerDispatch.dispatch n r (ObservedScanner.finish (DynamicScannerCapture.observer M) (valid M) a w) K) j := by
  rw [dispatch_product_eval M extra q a K x s k p E hp,
    dispatch_product_eval M extra r _ K x s k j E hj,hcap,ObservedScanner.residual_run M _ (valid M) q r a w (sfx x j) hstep]

end Shallot.MacroPeg.CBV.RecursiveScannerProductHelpers
