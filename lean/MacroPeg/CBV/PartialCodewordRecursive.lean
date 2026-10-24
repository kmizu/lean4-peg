import MacroPeg.CBV.PartialCodewordEntry
import MacroPeg.CBV.ArgumentGuard

/-! A fixed inverse compiler for mutually recursive users whose actual
argument is (A;&A)*;a*, optionally preceded by a caller-dependent
recursive lookaheads before and after capture, and whose body begins
A;param0. This is a restricted
family, not a normal form for all first-order Par grammars. -/
namespace Shallot.MacroPeg.CBV.PartialCodewordRecursive
open PartialCodewordCapture (argument runA look restArgument)
open PartialCodewordPreflight (checkBody)
open RuntimeShiftFilter (scanner)
open ClockFreezing (Table)

/-- Template calls `call i []` capture B; `call i [test]` capture
`&render(test);B`. The test has the caller environment and original position.
`call i [before,after]` captures `&render(before);B;&render(after)`.
The after test runs at the actual B endpoint in the caller environment.
These template arguments are not passed to the source callee as values. -/
def render (tails : List MExp) (par : Bool) : MExp → MExp
  | .call i [] => match tails[i]? with
    | none => MExp.failAlways
    | some _ => if par then .call i [argument] else PartialCodewordEntry.entry (2*i+1) (2*i+2)
  | .call i [test] => match tails[i]? with
    | none => MExp.failAlways
    | some _ => if par then .call i [.seq (look (render tails par test)) argument]
      else .seq (look (render tails par test)) (PartialCodewordEntry.entry (2*i+1) (2*i+2))
  | .call i [before,after] => match tails[i]? with
    | none => MExp.failAlways
    | some _ => if par then .call i [.seq (look (render tails par before))
        (.seq argument (look (render tails par after)))]
      else .seq (look (render tails par before))
        (.seq (look (.seq argument (render tails par after))) (PartialCodewordEntry.entry (2*i+1) (2*i+2)))
  | .seq a b => .seq (render tails par a) (render tails par b)
  | .alt a b => .alt (render tails par a) (render tails par b)
  | .star a => .star (render tails par a)
  | .notP a => .notP (render tails par a)
  | .param k => .param k
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w
  | _ => MExp.failAlways

def source (tails : List MExp) : MGrammar :=
  ⟨tails.map (fun b => ⟨1,.seq scanner (.seq (.param 0) (render tails true b))⟩)⟩
def pair (b : MExp) : List MRule :=
  [⟨2,.seq (.lit ['#']) (.seq (.param 0) (CodewordControlFilter.wholeView b))⟩,
    ⟨1,.seq (.lit ['#']) (.seq (.param 0) b)⟩]
def target (tails : List MExp) : MGrammar :=
  ⟨⟨1,checkBody⟩::tails.flatMap (fun b => pair (render tails false b))⟩

theorem entry_firstOrder (binary unary : Nat) :
    (PartialCodewordEntry.entry binary unary).FirstOrder := by
  simp [PartialCodewordEntry.entry,PartialCodewordEntry.branches,
    PartialCodewordCapture.longTest,argument,runA,restArgument,look,scanner,
    NestedScannerArguments.scan,NestedScannerArguments.choice,MExp.failAlways,
    MExp.FirstOrder,MExp.FirstOrderArgs]

theorem render_firstOrder (tails : List MExp) (par : Bool) :
    ∀ e, (render tails par e).FirstOrder
  | .call i [] => by
    simp only [render]
    cases tails[i]? with
    | none => trivial
    | some b =>
      cases par
      · simp [PartialCodewordEntry.entry,PartialCodewordEntry.branches,
          PartialCodewordCapture.longTest,argument,runA,restArgument,look,scanner,
          NestedScannerArguments.scan,NestedScannerArguments.choice,MExp.failAlways,
          MExp.FirstOrder,MExp.FirstOrderArgs]
      · exact ⟨ParserPrefixFusion.pure_firstOrder argument PartialCodewordTotality.argument_pure,True.intro⟩
  | .call i [test] => by
    have ht := render_firstOrder tails par test
    simp only [render]
    cases hr : tails[i]? with
    | none => trivial
    | some b =>
      cases par
      · exact ⟨ht,entry_firstOrder _ _⟩
      · exact ⟨⟨ht,ParserPrefixFusion.pure_firstOrder argument PartialCodewordTotality.argument_pure⟩,
          True.intro⟩
  | .call i [before,after] => by
    have hpre := render_firstOrder tails par before
    have hpost := render_firstOrder tails par after
    have hb := ParserPrefixFusion.pure_firstOrder argument PartialCodewordTotality.argument_pure
    simp only [render]
    cases hr : tails[i]? with
    | none => trivial
    | some b =>
      cases par
      · exact ⟨hpre,⟨hb,hpost⟩,entry_firstOrder _ _⟩
      · exact ⟨⟨hpre,hb,hpost⟩,True.intro⟩
  | .seq a b | .alt a b => ⟨render_firstOrder tails par a,render_firstOrder tails par b⟩
  | .star a | .notP a => render_firstOrder tails par a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .call _ (_::_::_::_) | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem source_firstOrder (tails : List MExp) : (source tails).FirstOrder := by
  intro r hr
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
  exact ⟨ParserPrefixFusion.pure_firstOrder scanner (by
    simp [scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,
      MExp.failAlways,ParserPrefixFusion.Pure]),True.intro,render_firstOrder tails true b⟩

theorem target_firstOrder (tails : List MExp) : (target tails).FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with he | hr
  · subst r
    simp [checkBody,scanner,look,NestedScannerArguments.scan,NestedScannerArguments.choice,
      MExp.failAlways,MExp.FirstOrder]
  · obtain ⟨b,_,hr⟩ := List.mem_flatMap.mp hr
    rcases List.mem_cons.mp hr with he | hr
    · subst r
      exact ⟨True.intro,True.intro,CodewordControlFilter.wholeView_firstOrder _ (render_firstOrder tails false b)⟩
    · rcases List.mem_cons.mp hr with he | hr
      · subst r
        exact ⟨True.intro,True.intro,render_firstOrder tails false b⟩
      · cases hr

theorem source_rule (tails : List MExp) (i : Nat) (b : MExp) (hr : tails[i]?=some b) :
    ruleAtM (source tails).rules i=some ⟨1,.seq scanner (.seq (.param 0) (render tails true b))⟩ := by
  simp [source,ruleAtM_eq_getElem?,List.getElem?_map,hr]

private theorem pair_even (f : MExp → MExp) (tails : List MExp) : ∀ i b, tails[i]?=some b →
    (tails.flatMap (fun b => pair (f b)))[2*i]?=
      some ⟨2,.seq (.lit ['#']) (.seq (.param 0) (CodewordControlFilter.wholeView (f b)))⟩ := by
  induction tails with
  | nil => intro i b hr; simp at hr
  | cons a tails ih =>
    intro i b hr
    cases i with
    | zero => simp at hr; subst b; rfl
    | succ i =>
      have hi := ih i b (by simpa using hr)
      simpa [pair,Nat.mul_add,Nat.add_assoc] using hi

private theorem pair_odd (f : MExp → MExp) (tails : List MExp) : ∀ i b, tails[i]?=some b →
    (tails.flatMap (fun b => pair (f b)))[2*i+1]?=
      some ⟨1,.seq (.lit ['#']) (.seq (.param 0) (f b))⟩ := by
  induction tails with
  | nil => intro i b hr; simp at hr
  | cons a tails ih =>
    intro i b hr
    cases i with
    | zero => simp at hr; subst b; rfl
    | succ i =>
      have hi := ih i b (by simpa using hr)
      simpa [pair,Nat.mul_add,Nat.add_assoc] using hi

theorem checker_rule (tails : List MExp) : ruleAtM (target tails).rules 0=some ⟨1,checkBody⟩ := rfl

theorem binary_rule (tails : List MExp) (i : Nat) (b : MExp) (hr : tails[i]?=some b) :
    ruleAtM (target tails).rules (2*i+1)=some ⟨2,.seq (.lit ['#'])
      (.seq (.param 0) (CodewordControlFilter.wholeView (render tails false b)))⟩ := by
  simpa only [target,ruleAtM_eq_getElem?,List.getElem?_cons_succ] using pair_even (render tails false) tails i b hr

theorem unary_rule (tails : List MExp) (i : Nat) (b : MExp) (hr : tails[i]?=some b) :
    ruleAtM (target tails).rules (2*i+2)=some ⟨1,.seq (.lit ['#']) (.seq (.param 0) (render tails false b))⟩ := by
  simpa only [target,ruleAtM_eq_getElem?,List.getElem?_cons_succ] using pair_odd (render tails false) tails i b hr

def CallsAgree (tails : List MExp) (x : List Char) (m : Nat) : Prop :=
  ∀ i b, tails[i]?=some b → ∀ E p, p≤x.length →
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E (.call i [argument]) p=
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq m) E
        (PartialCodewordEntry.entry (2*i+1) (2*i+2)) p

theorem evaluator_of_calls (tails : List MExp) (x : List Char) (m : Nat) (hc : CallsAgree tails x m) :
    ∀ e E p, p≤x.length →
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E (render tails true e) p=
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq m) E (render tails false e) p
  | .call i [], E, p, hp => by
    simp only [render]
    cases hr : tails[i]? with
    | none => rfl
    | some b => exact hc i b hr E p hp
  | .call i [test], E, p, hp => by
    have ht := evaluator_of_calls tails x m hc test E p hp
    simp only [render]
    cases hr : tails[i]? with
    | none => rfl
    | some b =>
      change evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E
        (.call i [.seq (look (render tails true test)) argument]) p=
        evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq m) E
          (.seq (look (render tails false test)) (PartialCodewordEntry.entry (2*i+1) (2*i+2))) p
      rw [ArgumentGuard.call_eq _ _ _ _ _ _ _ _ _ (source_rule tails i b hr)]
      exact ArgumentGuard.look_sequence_congr _ _ _ _ _ _ _ _ _ _ _ _ _ p ht (hc i b hr E p hp)
  | .call i [before,after], E, p, hp => by
    have hpre := evaluator_of_calls tails x m hc before E p hp
    have hB := PartialCodewordTotality.argument_context (source tails) (target tails) x
      .callByValuePar .callByValueSeq (tblV (source tails) x .callByValuePar m)
      (tblV (target tails) x .callByValueSeq m) E E p
    have hpreview :
        evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E
          (.seq argument (render tails true after)) p=
        evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq m) E
          (.seq argument (render tails false after)) p := by
      cases ha : evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E argument p with
      | none => rw [evV_seq_none ha,evV_seq_none (hB.symm.trans ha)]
      | some r => cases r with
        | none => rw [evV_seq_fail ha,evV_seq_fail (hB.symm.trans ha)]
        | some q =>
          rw [evV_seq_ok ha,evV_seq_ok (hB.symm.trans ha)]
          exact evaluator_of_calls tails x m hc after E q (evV_ok (tblV_ok _ _ _ m) _ p hp q ha)
    simp only [render]
    cases hr : tails[i]? with
    | none => rfl
    | some b =>
      change evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E
        (.call i [.seq (look (render tails true before)) (.seq argument (look (render tails true after)))]) p=
        evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq m) E
          (.seq (look (render tails false before))
            (.seq (look (.seq argument (render tails false after))) (PartialCodewordEntry.entry (2*i+1) (2*i+2)))) p
      rw [ArgumentGuard.call_eq _ _ _ _ _ _ _ _ _ (source_rule tails i b hr)]
      apply ArgumentGuard.look_sequence_congr _ _ _ _ _ _ _ _ _ _ _ _ _ p hpre
      rw [ArgumentGuard.suffix_call_eq _ _ _ _ _ _ _ _ _ (source_rule tails i b hr)]
      exact ArgumentGuard.look_sequence_congr _ _ _ _ _ _ _ _ _ _ _ _ _ p hpreview (hc i b hr E p hp)
  | .seq a b, E, p, hp => by
    have hh := evaluator_of_calls tails x m hc a E p hp
    simp only [render]
    cases hv : evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E (render tails true a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_calls tails x m hc b E q (evV_ok (tblV_ok _ _ _ m) _ p hp q hv)
  | .alt a b, E, p, hp => by
    have hh := evaluator_of_calls tails x m hc a E p hp
    simp only [render]
    cases hv : evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E (render tails true a) p with
    | none => rw [evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some result => cases result with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]
        exact evaluator_of_calls tails x m hc b E p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | .star a, E, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_calls tails x m hc a E q (by omega))
  | .notP a, E, p, hp => by
    simp only [render,evV]
    rw [evaluator_of_calls tails x m hc a E p hp]
  | .param _, _, _, _ | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _
  | .range _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .call _ (_::_::_::_), _, _, _ | .dbg _, _, _, _ | .lam _ _, _, _, _
  | .callParam _ _, _, _, _ | .invoke _ _ _, _, _, _ => rfl

/-- The real ordinary clocks align exactly. Each source call is matched
with both generated capture rows, and the checker is ready after one step. -/
theorem calls_agree (tails : List MExp) (x : List Char) (m : Nat) : CallsAgree tails x m := by
  induction m with
  | zero =>
    intro i b hr E p hp
    exact PartialCodewordEntry.zero (source tails) (target tails) x i (2*i+1) (2*i+2) p E E
      (render tails true b) hp (source_rule tails i b hr) (checker_rule tails)
  | succ m ih =>
    intro i b hr E p hp
    apply PartialCodewordEntry.transfer (source tails) (target tails) (source_firstOrder tails)
      x m m i (2*i+1) (2*i+2) p E E (render tails true b) (render tails false b)
      (render_firstOrder tails false b) hp (source_rule tails i b hr) (checker_rule tails)
      (binary_rule tails i b hr) (unary_rule tails i b hr)
    intro w q hq
    exact evaluator_of_calls tails x m ih b [w] q hq

theorem evaluator_eq (tails : List MExp) (x : List Char) (m : Nat)
    (e : MExp) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E (render tails true e) p=
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq m) E (render tails false e) p :=
  evaluator_of_calls tails x m (calls_agree tails x m) e E p hp

theorem stable_eq (tails : List MExp) (x : List Char) (e : MExp) :
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar (iterBoundV (source tails) x))
      [] (render tails true e) x.length=
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq (iterBoundV (target tails) x))
      [] (render tails false e) x.length := by
  have hdefined (v : Option Nat) :
      evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar (iterBoundV (source tails) x))
        [] (render tails true e) x.length=some v ↔
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq (iterBoundV (target tails) x))
        [] (render tails false e) x.length=some v := by
    rw [←tblV_stable (source tails) x .callByValuePar (Nat.le_refl _),
      ←tblV_stable (target tails) x .callByValueSeq (Nat.le_refl _)]
    exact exists_congr (fun m => by rw [evaluator_eq tails x m e [] x.length (Nat.le_refl _)])
  cases hs : evV (source tails) x .callByValuePar
      (tblV (source tails) x .callByValuePar (iterBoundV (source tails) x)) [] (render tails true e) x.length with
  | none =>
    cases ht : evV (target tails) x .callByValueSeq
        (tblV (target tails) x .callByValueSeq (iterBoundV (target tails) x)) [] (render tails false e) x.length with
    | none => rfl
    | some v => have hh := (hdefined v).mpr ht; rw [hs] at hh; cases hh
  | some v => exact ((hdefined v).mp hs).symm

/-- One fixed recursive Seq grammar preserves all finite observations on
unchanged strings, including failures and absence of finite observations. -/
theorem observations_iff (tails : List MExp) (e : MExp) (x : List Char) (r : Option (List Char)) :
    SObs (source tails) .callByValuePar (render tails true e) x r ↔
      SObs (target tails) .callByValueSeq (render tails false e) x r := by
  rw [←decideObsV_iff (source_firstOrder tails) (by decide) (render_firstOrder tails true e),
    ←decideObsV_iff (target_firstOrder tails) (by decide) (render_firstOrder tails false e)]
  unfold decideObsV
  rw [stable_eq]

theorem language_translation (tails : List MExp) (e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (source tails) .callByValuePar (render tails true e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target tails,render tails false e,target_firstOrder tails,render_firstOrder tails false e,
    fun x => observations_iff tails e x (some [])⟩

end Shallot.MacroPeg.CBV.PartialCodewordRecursive
