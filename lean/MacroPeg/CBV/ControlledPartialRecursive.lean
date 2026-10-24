import MacroPeg.CBV.ControlledPartialEntry

/-! A fixed recursive compiler with caller-dependent tests controlling
actual partial-capture lengths. This remains a restricted source family. -/
namespace Shallot.MacroPeg.CBV.ControlledPartialRecursive
open ControlledPartialCapture (argument)
open RuntimeShiftFilter (scanner)

/-- A singleton template argument is a stopping test, rendered in the
caller environment. It is not an independently captured argument. -/
def render (tails : List MExp) (par : Bool) : MExp → MExp
  | .call i [] => match tails[i]? with
    | none => MExp.failAlways
    | some _ => if par then .call i [argument .eps]
      else ControlledPartialEntry.entry (2*i+2) (2*i+3) .eps
  | .call i [test] => match tails[i]? with
    | none => MExp.failAlways
    | some _ => if par then .call i [argument (render tails par test)]
      else ControlledPartialEntry.entry (2*i+2) (2*i+3) (render tails par test)
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
  ⟨⟨1,.param 0⟩::⟨1,.seq (.lit ['#']) (.param 0)⟩::
    tails.flatMap (fun b => pair (render tails false b))⟩

theorem render_firstOrder (tails : List MExp) (par : Bool) :
    ∀ e, (render tails par e).FirstOrder
  | .call i [] => by
    simp only [render]
    cases tails[i]? with
    | none => trivial
    | some b =>
      cases par
      · exact ControlledPartialEntry.entry_firstOrder _ _ _ True.intro
      · exact ⟨ControlledPartialCapture.argument_firstOrder .eps True.intro,True.intro⟩
  | .call i [test] => by
    have ht := render_firstOrder tails par test
    simp only [render]
    cases tails[i]? with
    | none => trivial
    | some b =>
      cases par
      · exact ControlledPartialEntry.entry_firstOrder _ _ _ ht
      · exact ⟨ControlledPartialCapture.argument_firstOrder _ ht,True.intro⟩
  | .seq a b | .alt a b => ⟨render_firstOrder tails par a,render_firstOrder tails par b⟩
  | .star a | .notP a => render_firstOrder tails par a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .call _ (_::_::_) | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem source_firstOrder (tails : List MExp) : (source tails).FirstOrder := by
  intro r hr
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
  exact ⟨ParserPrefixFusion.pure_firstOrder scanner (by
    simp [scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,
      MExp.failAlways,ParserPrefixFusion.Pure]),True.intro,render_firstOrder tails true b⟩

theorem target_firstOrder (tails : List MExp) : (target tails).FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with he | hr
  · subst r; trivial
  · rcases List.mem_cons.mp hr with he | hr
    · subst r; exact ⟨True.intro,True.intro⟩
    · obtain ⟨b,_,hr⟩ := List.mem_flatMap.mp hr
      simp only [pair,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨True.intro,True.intro,CodewordControlFilter.wholeView_firstOrder _ (render_firstOrder tails false b)⟩
      · exact ⟨True.intro,True.intro,render_firstOrder tails false b⟩

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

theorem compare_rule (tails : List MExp) : ruleAtM (target tails).rules 0=some ⟨1,.param 0⟩ := rfl
theorem tail_compare_rule (tails : List MExp) :
    ruleAtM (target tails).rules 1=some ⟨1,.seq (.lit ['#']) (.param 0)⟩ := rfl

theorem binary_rule (tails : List MExp) (i : Nat) (b : MExp) (hr : tails[i]?=some b) :
    ruleAtM (target tails).rules (2*i+2)=some ⟨2,.seq (.lit ['#'])
      (.seq (.param 0) (CodewordControlFilter.wholeView (render tails false b)))⟩ := by
  simpa only [target,ruleAtM_eq_getElem?,Nat.add_assoc,List.getElem?_cons_succ]
    using pair_even (render tails false) tails i b hr

theorem unary_rule (tails : List MExp) (i : Nat) (b : MExp) (hr : tails[i]?=some b) :
    ruleAtM (target tails).rules (2*i+3)=some ⟨1,.seq (.lit ['#'])
      (.seq (.param 0) (render tails false b))⟩ := by
  simpa only [target,ruleAtM_eq_getElem?,Nat.add_assoc,List.getElem?_cons_succ]
    using pair_odd (render tails false) tails i b hr

/-- The previous user stage handles callee continuations. Structural
recursion handles the caller's stopping test at this same stage. -/
theorem evaluator_of_previous (tails : List MExp) (x : List Char) (m : Nat)
    (hprev : ∀ k, m=k+1 → ∀ e E p, p≤x.length →
      evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar k) E (render tails true e) p=
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq k) E (render tails false e) p) :
    ∀ e E p, p≤x.length →
      evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E (render tails true e) p=
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq m) E (render tails false e) p
  | .call i [], E, p, hp => by
    cases hr : tails[i]? with
    | none => simp only [render,hr]; rfl
    | some b =>
      simp only [render,hr,Bool.false_eq_true,↓reduceIte]
      cases m with
      | zero =>
        exact ControlledPartialEntry.zero _ _ x i (2*i+2) (2*i+3) p E E .eps .eps
          (render tails true b) hp (source_rule tails i b hr) (compare_rule tails) (tail_compare_rule tails)
      | succ k =>
        apply ControlledPartialEntry.transfer _ _ (target_firstOrder tails) x k k i
          (2*i+2) (2*i+3) p E E .eps .eps (render tails true b) (render tails false b)
          True.intro (render_firstOrder tails false b) hp (source_rule tails i b hr)
          (compare_rule tails) (tail_compare_rule tails) (binary_rule tails i b hr) (unary_rule tails i b hr)
        · intro q hq; rfl
        · intro w q hq; exact hprev k rfl b [w] q hq
  | .call i [test], E, p, hp => by
    cases hr : tails[i]? with
    | none => simp only [render,hr]; rfl
    | some b =>
      simp only [render,hr,Bool.false_eq_true,↓reduceIte]
      cases m with
      | zero =>
        exact ControlledPartialEntry.zero _ _ x i (2*i+2) (2*i+3) p E E
          (render tails true test) (render tails false test) (render tails true b) hp
          (source_rule tails i b hr) (compare_rule tails) (tail_compare_rule tails)
      | succ k =>
        apply ControlledPartialEntry.transfer _ _ (target_firstOrder tails) x k k i
          (2*i+2) (2*i+3) p E E (render tails true test) (render tails false test)
          (render tails true b) (render tails false b) (render_firstOrder tails false test)
          (render_firstOrder tails false b) hp (source_rule tails i b hr)
          (compare_rule tails) (tail_compare_rule tails) (binary_rule tails i b hr) (unary_rule tails i b hr)
        · intro q hq; exact evaluator_of_previous tails x (k+1) hprev test E q hq
        · intro w q hq; exact hprev k rfl b [w] q hq
  | .seq a b, E, p, hp => by
    have hh := evaluator_of_previous tails x m hprev a E p hp
    simp only [render]
    cases hv : evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E (render tails true a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_previous tails x m hprev b E q (evV_ok (tblV_ok _ _ _ m) _ p hp q hv)
  | .alt a b, E, p, hp => by
    have hh := evaluator_of_previous tails x m hprev a E p hp
    simp only [render]
    cases hv : evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E (render tails true a) p with
    | none => rw [evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some result => cases result with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]
        exact evaluator_of_previous tails x m hprev b E p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | .star a, E, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_previous tails x m hprev a E q (by omega))
  | .notP a, E, p, hp => by
    simp only [render,evV]
    rw [evaluator_of_previous tails x m hprev a E p hp]
  | .param _, _, _, _ | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _
  | .range _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .call _ (_::_::_), _, _, _ | .dbg _, _, _, _ | .lam _ _, _, _, _
  | .callParam _ _, _, _, _ | .invoke _ _ _, _, _, _ => rfl

theorem evaluator_eq (tails : List MExp) (x : List Char) (m : Nat)
    (e : MExp) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E (render tails true e) p=
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq m) E (render tails false e) p := by
  induction m generalizing e E p with
  | zero => exact evaluator_of_previous tails x 0 (by intro k hk; omega) e E p hp
  | succ m ih =>
    apply evaluator_of_previous tails x (m+1) _ e E p hp
    intro k hk e E p hp
    have he : k=m := by omega
    subst k
    exact ih e E p hp

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

end Shallot.MacroPeg.CBV.ControlledPartialRecursive
