import MacroPeg.CBV.FragmentConsumingEntry

/-! Recursive call transfer with consuming final-fragment control. -/
namespace Shallot.MacroPeg.CBV.FragmentConsumingRecursive
open RuntimeShiftFilter (scanner)
open ControlledFragmentReplay (argument)

private theorem scanner_firstOrder : scanner.FirstOrder := by
  simp [scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,MExp.FirstOrder,MExp.failAlways]

/-- A literal a-word, represented using the certified consuming leaves. -/
def aWord : Nat → MExp
  | 0 => .eps
  | n+1 => .seq (.chr 'a') (aWord n)

theorem aWord_syntax : ∀ n, FragmentConsumingSyntax.Syntax (aWord n)
  | 0 => .eps
  | n+1 => .seq .char (aWord_syntax n)

def call (tails : List MExp) (par : Bool) (i : Nat) (G H : MExp) : MExp :=
  match tails[i]? with
  | none => MExp.failAlways
  | some _ => if par then .call i [argument G H]
    else FragmentConsumingEntry.entry (2*i+2) (2*i+3) G H

/-- In fragment mode only a-consuming syntax is generated. Tests switch
back to normal mode so they may inspect parents or invoke recursive users.
The second template of a normal call describes H itself, not its star test. -/
def render (tails : List MExp) (par : Bool) : Bool → MExp → MExp
  | false,.call i [] => call tails par i .eps .eps
  | false,.call i [G] => call tails par i (render tails par false G) .eps
  | false,.call i [G,H] => call tails par i (render tails par false G) (render tails par true H)
  | f,.seq a b => .seq (render tails par f a) (render tails par f b)
  | f,.alt a b => .alt (render tails par f a) (render tails par f b)
  | f,.star a => .star (render tails par f a)
  | _,.notP a => .notP (render tails par false a)
  | _,.eps => .eps
  | true,.chr c => if c='a' then .chr 'a' else MExp.failAlways
  | true,.lit w => if ∀ c∈w, c='a' then aWord w.length else MExp.failAlways
  | false,.param k => .param k
  | false,.any => .any | false,.chr c => .chr c
  | false,.range a b => .range a b | false,.lit w => .lit w
  | _,_ => MExp.failAlways

private theorem call_firstOrder (tails : List MExp) (par : Bool) (i : Nat)
    (G H : MExp) (hG : G.FirstOrder) (hH : H.FirstOrder) : (call tails par i G H).FirstOrder := by
  unfold call
  cases tails[i]? with
  | none => trivial
  | some b =>
    cases par
    · simpa using FragmentConsumingEntry.entry_firstOrder (2*i+2) (2*i+3) G H hG hH
    · exact ⟨⟨⟨scanner_firstOrder,scanner_firstOrder,hG⟩,hH⟩,True.intro⟩

theorem render_firstOrder (tails : List MExp) (par : Bool) : ∀ f e, (render tails par f e).FirstOrder
  | false,.call i [] => call_firstOrder tails par i .eps .eps True.intro True.intro
  | false,.call i [G] => call_firstOrder tails par i _ .eps (render_firstOrder tails par false G) True.intro
  | false,.call i [G,H] => call_firstOrder tails par i _ _
      (render_firstOrder tails par false G) (render_firstOrder tails par true H)
  | f,.seq a b | f,.alt a b => by
      have ha := render_firstOrder tails par f a
      have hb := render_firstOrder tails par f b
      cases f <;> exact ⟨ha,hb⟩
  | f,.star a => by
      have ha := render_firstOrder tails par f a
      cases f <;> exact ha
  | f,.notP a => by cases f <;> exact render_firstOrder tails par false a
  | true,.chr c => by simp only [render]; split <;> trivial
  | true,.lit w => by
      simp only [render]; split
      · exact FragmentConsumingSyntax.firstOrder (aWord_syntax _)
      · trivial
  | f,.eps => by cases f <;> trivial
  | false,.param _ | false,.any | false,.chr _ | false,.range _ _ | false,.lit _ => trivial
  | true,.param _ | true,.any | true,.range _ _ | true,.call _ _
  | false,.call _ (_::_::_::_) => trivial
  | f,.dbg _ | f,.lam _ _ | f,.callParam _ _ | f,.invoke _ _ _ => by cases f <;> trivial

theorem render_fragment_syntax (tails : List MExp) (par : Bool) :
    ∀ e, FragmentConsumingSyntax.Syntax (render tails par true e)
  | .seq a b => .seq (render_fragment_syntax tails par a) (render_fragment_syntax tails par b)
  | .alt a b => .alt (render_fragment_syntax tails par a) (render_fragment_syntax tails par b)
  | .star a => .star (render_fragment_syntax tails par a)
  | .notP a => .reject _ (render_firstOrder tails par false a)
  | .eps => .eps
  | .chr c => by
      simp only [render]; split
      · exact .char
      · exact .reject .eps True.intro
  | .lit w => by
      simp only [render]; split
      · exact aWord_syntax _
      · exact .reject .eps True.intro
  | .param _ | .any | .range _ _ | .call _ _ | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ =>
      .reject .eps True.intro

def source (tails : List MExp) : MGrammar :=
  ⟨tails.map (fun b => ⟨1,.seq scanner (.seq (.param 0) (render tails true false b))⟩)⟩
def pair (b : MExp) : List MRule :=
  [⟨3,.seq scanner (.seq (.param 2) (ControlledFragmentReplay.wholeView b))⟩,
    ⟨1,.seq scanner (.seq (.param 0) b)⟩]
def target (tails : List MExp) : MGrammar :=
  ⟨⟨1,.param 0⟩::⟨1,ControlledFragmentReplay.tailBody⟩::
    tails.flatMap (fun b => pair (render tails false false b))⟩

theorem source_firstOrder (tails : List MExp) : (source tails).FirstOrder := by
  intro r hr
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
  exact ⟨scanner_firstOrder,True.intro,render_firstOrder tails true false b⟩

theorem target_firstOrder (tails : List MExp) : (target tails).FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with he | hr
  · subst r; trivial
  · rcases List.mem_cons.mp hr with he | hr
    · subst r; exact ⟨scanner_firstOrder,True.intro⟩
    · obtain ⟨b,_,hr⟩ := List.mem_flatMap.mp hr
      simp only [pair,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scanner_firstOrder,True.intro,firstOrder_subst (args:=[CaptureViews.prefixExpr 3])
          ⟨CaptureViews.prefixExpr_firstOrder 3,True.intro⟩ _ (render_firstOrder tails false false b)⟩
      · exact ⟨scanner_firstOrder,True.intro,render_firstOrder tails false false b⟩

theorem source_rule (tails : List MExp) (i : Nat) (b : MExp) (hr : tails[i]?=some b) :
    ruleAtM (source tails).rules i=some ⟨1,.seq scanner (.seq (.param 0) (render tails true false b))⟩ := by
  simp [source,ruleAtM_eq_getElem?,List.getElem?_map,hr]

private theorem pair_even (f : MExp → MExp) (tails : List MExp) : ∀ i b, tails[i]?=some b →
    (tails.flatMap (fun b => pair (f b)))[2*i]?=
      some ⟨3,.seq scanner (.seq (.param 2) (ControlledFragmentReplay.wholeView (f b)))⟩ := by
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
      some ⟨1,.seq scanner (.seq (.param 0) (f b))⟩ := by
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
    ruleAtM (target tails).rules 1=some ⟨1,ControlledFragmentReplay.tailBody⟩ := rfl

theorem ternary_rule (tails : List MExp) (i : Nat) (b : MExp) (hr : tails[i]?=some b) :
    ruleAtM (target tails).rules (2*i+2)=some ⟨3,.seq scanner
      (.seq (.param 2) (ControlledFragmentReplay.wholeView (render tails false false b)))⟩ := by
  simpa only [target,ruleAtM_eq_getElem?,Nat.add_assoc,List.getElem?_cons_succ]
    using pair_even (render tails false false) tails i b hr

theorem unary_rule (tails : List MExp) (i : Nat) (b : MExp) (hr : tails[i]?=some b) :
    ruleAtM (target tails).rules (2*i+3)=some ⟨1,.seq scanner
      (.seq (.param 0) (render tails false false b))⟩ := by
  simpa only [target,ruleAtM_eq_getElem?,Nat.add_assoc,List.getElem?_cons_succ]
    using pair_odd (render tails false false) tails i b hr

private theorem call_eq (tails : List MExp) (x : List Char) (m i p : Nat)
    (E : List (List Char)) (G G' H H' : MExp) (hH' : FragmentConsumingSyntax.Syntax H') (hp : p≤x.length)
    (hG : ∀ q, q≤x.length → evV (source tails) x .callByValuePar
        (tblV (source tails) x .callByValuePar m) E G q=
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq m) E G' q)
    (hH : ∀ q, q≤x.length → evV (source tails) x .callByValuePar
        (tblV (source tails) x .callByValuePar m) E H q=
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq m) E H' q)
    (hprev : ∀ k, m=k+1 → ∀ e E p, p≤x.length →
      evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar k) E (render tails true false e) p=
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq k) E (render tails false false e) p) :
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E (call tails true i G H) p=
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq m) E (call tails false i G' H') p := by
  cases hr : tails[i]? with
  | none => simp only [call,hr]; rfl
  | some b =>
    simp only [call,hr,Bool.false_eq_true,↓reduceIte]
    cases m with
    | zero =>
      exact FragmentConsumingEntry.zero _ _ x i (2*i+2) (2*i+3) p E E G G' H H'
        (render tails true false b) (source_rule tails i b hr) (compare_rule tails) (tail_compare_rule tails)
        (FragmentConsumingEntry.argument_congr _ _ x .callByValuePar .callByValueSeq _ _
          (tblV_ok _ _ _ 0) E E G G' H H' hG hH p hp)
    | succ k =>
      apply FragmentConsumingEntry.transfer _ _ (target_firstOrder tails) x k k i
        (2*i+2) (2*i+3) p E E G G' H H' (render tails true false b) (render tails false false b)
        hH' (render_firstOrder tails false false b) hp (source_rule tails i b hr)
        (compare_rule tails) (tail_compare_rule tails) (ternary_rule tails i b hr) (unary_rule tails i b hr) hG hH
      intro w q hq; exact hprev k rfl b [w] q hq


private theorem render_seq (tails : List MExp) (par f : Bool) (a b : MExp) :
    render tails par f (.seq a b)=.seq (render tails par f a) (render tails par f b) := by
  cases f <;> rfl

private theorem render_alt (tails : List MExp) (par f : Bool) (a b : MExp) :
    render tails par f (.alt a b)=.alt (render tails par f a) (render tails par f b) := by
  cases f <;> rfl

private theorem render_star (tails : List MExp) (par f : Bool) (a : MExp) :
    render tails par f (.star a)=.star (render tails par f a) := by
  cases f <;> rfl

private theorem render_notP (tails : List MExp) (par f : Bool) (a : MExp) :
    render tails par f (.notP a)=.notP (render tails par false a) := by
  cases f <;> rfl
/-- Current-clock structural induction handles normal expressions and
consuming fragments together, switching to normal mode inside tests.
Previous-clock induction handles the actual callee continuation. -/
theorem evaluator_of_previous (tails : List MExp) (x : List Char) (m : Nat)
    (hprev : ∀ k, m=k+1 → ∀ e E p, p≤x.length →
      evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar k) E (render tails true false e) p=
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq k) E (render tails false false e) p) :
    ∀ f e E p, p≤x.length →
      evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E (render tails true f e) p=
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq m) E (render tails false f e) p
  | false,.call i [], E, p, hp => call_eq tails x m i p E .eps .eps .eps .eps .eps hp
      (by intro q hq; rfl) (by intro q hq; rfl) hprev
  | false,.call i [G], E, p, hp => call_eq tails x m i p E _ _ .eps .eps .eps hp
      (fun q hq => evaluator_of_previous tails x m hprev false G E q hq) (by intro q hq; rfl) hprev
  | false,.call i [G,H], E, p, hp => call_eq tails x m i p E _ _ _ _ (render_fragment_syntax tails false H) hp
      (fun q hq => evaluator_of_previous tails x m hprev false G E q hq)
      (fun q hq => evaluator_of_previous tails x m hprev true H E q hq) hprev
  | f,.seq a b, E, p, hp => by
    have hh := evaluator_of_previous tails x m hprev f a E p hp
    simp only [render_seq]
    cases hv : evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E (render tails true f a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_previous tails x m hprev f b E q (evV_ok (tblV_ok _ _ _ m) _ p hp q hv)
  | f,.alt a b, E, p, hp => by
    have hh := evaluator_of_previous tails x m hprev f a E p hp
    simp only [render_alt]
    cases hv : evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E (render tails true f a) p with
    | none => rw [evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some result => cases result with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]
        exact evaluator_of_previous tails x m hprev f b E p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | f,.star a, E, p, hp => by
    simp only [render_star,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_previous tails x m hprev f a E q (by omega))
  | f,.notP a, E, p, hp => by
    simp only [render_notP,evV]
    rw [evaluator_of_previous tails x m hprev false a E p hp]
  | false,.param _, _, _, _ | false,.any, _, _, _ | false,.chr _, _, _, _
  | false,.range _ _, _, _, _ | false,.lit _, _, _, _ => rfl
  | true,.chr c, _, _, _ => by simp only [render]; split <;> rfl
  | true,.lit w, _, _, _ => by
    simp only [render]; split
    · exact ParserPrefixFusion.pure_eval _ _ x .callByValuePar .callByValueSeq _ _ _ _ (aWord w.length)
        (by induction w.length with | zero => trivial | succ n ih => exact ⟨True.intro,ih⟩) _
    · rfl
  | f,.eps, _, _, _ => by cases f <;> rfl
  | true,.param _, _, _, _ | true,.any, _, _, _ | true,.range _ _, _, _, _ | true,.call _ _, _, _, _
  | false,.call _ (_::_::_::_), _, _, _ => rfl
  | f,.dbg _, _, _, _ | f,.lam _ _, _, _, _ | f,.callParam _ _, _, _, _
  | f,.invoke _ _ _, _, _, _ => by cases f <;> rfl

theorem evaluator_eq (tails : List MExp) (x : List Char) (m : Nat)
    (f : Bool) (e : MExp) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar m) E (render tails true f e) p=
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq m) E (render tails false f e) p := by
  induction m generalizing f e E p with
  | zero => exact evaluator_of_previous tails x 0 (by intro k hk; omega) f e E p hp
  | succ m ih =>
    apply evaluator_of_previous tails x (m+1) _ f e E p hp
    intro k hk e E p hp
    have he : k=m := by omega
    subst k
    exact ih false e E p hp

theorem stable_eq (tails : List MExp) (x : List Char) (e : MExp) :
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar (iterBoundV (source tails) x))
      [] (render tails true false e) x.length=
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq (iterBoundV (target tails) x))
      [] (render tails false false e) x.length := by
  have hdefined (v : Option Nat) :
      evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar (iterBoundV (source tails) x))
        [] (render tails true false e) x.length=some v ↔
      evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq (iterBoundV (target tails) x))
        [] (render tails false false e) x.length=some v := by
    rw [←tblV_stable (source tails) x .callByValuePar (Nat.le_refl _),
      ←tblV_stable (target tails) x .callByValueSeq (Nat.le_refl _)]
    exact exists_congr (fun m => by rw [evaluator_eq tails x m false e [] x.length (Nat.le_refl _)])
  cases hs : evV (source tails) x .callByValuePar
      (tblV (source tails) x .callByValuePar (iterBoundV (source tails) x)) [] (render tails true false e) x.length with
  | none =>
    cases ht : evV (target tails) x .callByValueSeq
        (tblV (target tails) x .callByValueSeq (iterBoundV (target tails) x)) [] (render tails false false e) x.length with
    | none => rfl
    | some v => have hh := (hdefined v).mpr ht; rw [hs] at hh; cases hh
  | some v => exact ((hdefined v).mp hs).symm

/-- One fixed recursive Seq grammar preserves all finite observations on
unchanged strings, including failures and absence of finite observations. -/
theorem observations_iff (tails : List MExp) (e : MExp) (x : List Char) (r : Option (List Char)) :
    SObs (source tails) .callByValuePar (render tails true false e) x r ↔
      SObs (target tails) .callByValueSeq (render tails false false e) x r := by
  rw [←decideObsV_iff (source_firstOrder tails) (by decide) (render_firstOrder tails true false e),
    ←decideObsV_iff (target_firstOrder tails) (by decide) (render_firstOrder tails false false e)]
  unfold decideObsV
  rw [stable_eq]

theorem language_translation (tails : List MExp) (e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (source tails) .callByValuePar (render tails true false e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target tails,render tails false false e,target_firstOrder tails,render_firstOrder tails false false e,
    fun x => observations_iff tails e x (some [])⟩

end Shallot.MacroPeg.CBV.FragmentConsumingRecursive
