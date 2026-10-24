import MacroPeg.CBV.FragmentConsumingRecursive
import MacroPeg.CBV.MixedOriginControl
import MacroPeg.CBV.ArgumentGuard

/-! Recursive call transfer with consuming final-fragment control. -/
namespace Shallot.MacroPeg.CBV.FragmentOriginRecursive
open ReplayControlFusion (Plan)
open RuntimeShiftFilter (scanner)
open ControlledFragmentReplay (argument)

private theorem scanner_firstOrder : scanner.FirstOrder := by
  simp [scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,MExp.FirstOrder,MExp.failAlways]

open FragmentConsumingRecursive (aWord aWord_syntax)

def call (plans : List Plan) (par : Bool) (i : Nat) (G H : MExp) : MExp :=
  match plans[i]? with
  | none => MExp.failAlways
  | some P => if par then .call i [argument G H]
    else .seq (PartialCodewordCapture.look (argument G H))
      (P.exp (fun j => FragmentConsumingEntry.entry (2*j+2) (2*j+3) G H))

/-- In fragment mode only a-consuming syntax is generated. Tests switch
back to normal mode so they may inspect parents or invoke recursive users.
The second template of a normal call describes H itself, not its star test. -/
def render (plans : List Plan) (par : Bool) : Bool → MExp → MExp
  | false,.call i [] => call plans par i .eps .eps
  | false,.call i [G] => call plans par i (render plans par false G) .eps
  | false,.call i [G,H] => call plans par i (render plans par false G) (render plans par true H)
  | f,.seq a b => .seq (render plans par f a) (render plans par f b)
  | f,.alt a b => .alt (render plans par f a) (render plans par f b)
  | f,.star a => .star (render plans par f a)
  | _,.notP a => .notP (render plans par false a)
  | _,.eps => .eps
  | true,.chr c => if c='a' then .chr 'a' else MExp.failAlways
  | true,.lit w => if ∀ c∈w, c='a' then aWord w.length else MExp.failAlways
  | false,.param k => .param k
  | false,.any => .any | false,.chr c => .chr c
  | false,.range a b => .range a b | false,.lit w => .lit w
  | _,_ => MExp.failAlways

private theorem call_firstOrder (plans : List Plan) (par : Bool) (i : Nat)
    (G H : MExp) (hG : G.FirstOrder) (hH : H.FirstOrder) : (call plans par i G H).FirstOrder := by
  unfold call
  cases plans[i]? with
  | none => trivial
  | some b =>
    cases par
    · exact ⟨⟨⟨scanner_firstOrder,scanner_firstOrder,hG⟩,hH⟩,
        Plan.exp_firstOrder (fun j => FragmentConsumingEntry.entry_firstOrder (2*j+2) (2*j+3) G H hG hH) b⟩
    · exact ⟨⟨⟨scanner_firstOrder,scanner_firstOrder,hG⟩,hH⟩,True.intro⟩

theorem render_firstOrder (plans : List Plan) (par : Bool) : ∀ f e, (render plans par f e).FirstOrder
  | false,.call i [] => call_firstOrder plans par i .eps .eps True.intro True.intro
  | false,.call i [G] => call_firstOrder plans par i _ .eps (render_firstOrder plans par false G) True.intro
  | false,.call i [G,H] => call_firstOrder plans par i _ _
      (render_firstOrder plans par false G) (render_firstOrder plans par true H)
  | f,.seq a b | f,.alt a b => by
      have ha := render_firstOrder plans par f a
      have hb := render_firstOrder plans par f b
      cases f <;> exact ⟨ha,hb⟩
  | f,.star a => by
      have ha := render_firstOrder plans par f a
      cases f <;> exact ha
  | f,.notP a => by cases f <;> exact render_firstOrder plans par false a
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

theorem render_fragment_syntax (plans : List Plan) (par : Bool) :
    ∀ e, FragmentConsumingSyntax.Syntax (render plans par true e)
  | .seq a b => .seq (render_fragment_syntax plans par a) (render_fragment_syntax plans par b)
  | .alt a b => .alt (render_fragment_syntax plans par a) (render_fragment_syntax plans par b)
  | .star a => .star (render_fragment_syntax plans par a)
  | .notP a => .reject _ (render_firstOrder plans par false a)
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


/-- Logical users may branch, test, and guard at the caller origin.
The appended leaf rows support the ordinary Par normalization proof. -/
def leaf (plans : List Plan) (tails : List MExp) (j : Nat) : MExp :=
  match tails[j]? with
  | none => MExp.failAlways
  | some b => .seq scanner (.seq (.param 0) (render plans true false b))
def source (plans : List Plan) (tails : List MExp) : MGrammar :=
  ⟨plans.map (fun P => ⟨1,P.exp (leaf plans tails)⟩)++
    tails.map (fun b => ⟨1,.seq scanner (.seq (.param 0) (render plans true false b))⟩)⟩
abbrev target (plans : List Plan) (tails : List MExp) : MGrammar :=
  ⟨⟨1,.param 0⟩::⟨1,ControlledFragmentReplay.tailBody⟩::
    tails.flatMap (fun b => FragmentConsumingRecursive.pair (render plans false false b))⟩
/-- A finite syntax check on every logical user's leaf indices. -/
def Valid (plans : List Plan) (tails : List MExp) : Prop :=
  ∀ P∈plans, P.All (fun j => j<tails.length)

theorem leaf_firstOrder (plans : List Plan) (tails : List MExp) (j : Nat) :
    (leaf plans tails j).FirstOrder := by
  unfold leaf
  cases tails[j]? with
  | none => trivial
  | some b => exact ⟨scanner_firstOrder,True.intro,render_firstOrder plans true false b⟩
theorem source_firstOrder (plans : List Plan) (tails : List MExp) : (source plans tails).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨P,_,rfl⟩ := List.mem_map.mp hr
    exact Plan.exp_firstOrder (leaf_firstOrder plans tails) P
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨scanner_firstOrder,True.intro,render_firstOrder plans true false b⟩
theorem target_firstOrder (plans : List Plan) (tails : List MExp) : (target plans tails).FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with he | hr
  · subst r; trivial
  · rcases List.mem_cons.mp hr with he | hr
    · subst r; exact ⟨scanner_firstOrder,True.intro⟩
    · obtain ⟨b,_,hr⟩ := List.mem_flatMap.mp hr
      simp only [FragmentConsumingRecursive.pair,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scanner_firstOrder,True.intro,firstOrder_subst (args:=[CaptureViews.prefixExpr 3])
          ⟨CaptureViews.prefixExpr_firstOrder 3,True.intro⟩ _ (render_firstOrder plans false false b)⟩
      · exact ⟨scanner_firstOrder,True.intro,render_firstOrder plans false false b⟩
theorem source_rule (plans : List Plan) (tails : List MExp) (i : Nat) (P : Plan) (hr : plans[i]?=some P) :
    ruleAtM (source plans tails).rules i=some ⟨1,P.exp (leaf plans tails)⟩ := by
  have hi : i<plans.length := (List.getElem?_eq_some_iff.mp hr).choose
  simp only [source,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hi)]
  simp only [List.getElem?_map,hr,Option.map_some]
theorem leaf_rule (plans : List Plan) (tails : List MExp) (j : Nat) (b : MExp) (hr : tails[j]?=some b) :
    ruleAtM (source plans tails).rules (plans.length+j)=
      some ⟨1,.seq scanner (.seq (.param 0) (render plans true false b))⟩ := by
  simp [source,ruleAtM_eq_getElem?,List.getElem?_append_right,List.getElem?_map,hr]

private theorem pair_even (f : MExp → MExp) (tails : List MExp) : ∀ i b, tails[i]?=some b →
    (tails.flatMap (fun b => FragmentConsumingRecursive.pair (f b)))[2*i]?=
      some ⟨3,.seq scanner (.seq (.param 2) (ControlledFragmentReplay.wholeView (f b)))⟩ := by
  induction tails with
  | nil => intro i b hr; simp at hr
  | cons a tails ih =>
    intro i b hr
    cases i with
    | zero => simp at hr; subst b; rfl
    | succ i =>
      have hi := ih i b (by simpa using hr)
      simpa [FragmentConsumingRecursive.pair,Nat.mul_add,Nat.add_assoc] using hi

private theorem pair_odd (f : MExp → MExp) (tails : List MExp) : ∀ i b, tails[i]?=some b →
    (tails.flatMap (fun b => FragmentConsumingRecursive.pair (f b)))[2*i+1]?=
      some ⟨1,.seq scanner (.seq (.param 0) (f b))⟩ := by
  induction tails with
  | nil => intro i b hr; simp at hr
  | cons a tails ih =>
    intro i b hr
    cases i with
    | zero => simp at hr; subst b; rfl
    | succ i =>
      have hi := ih i b (by simpa using hr)
      simpa [FragmentConsumingRecursive.pair,Nat.mul_add,Nat.add_assoc] using hi

theorem compare_rule (plans : List Plan) (tails : List MExp) : ruleAtM (target plans tails).rules 0=some ⟨1,.param 0⟩ := rfl
theorem tail_compare_rule (plans : List Plan) (tails : List MExp) :
    ruleAtM (target plans tails).rules 1=some ⟨1,ControlledFragmentReplay.tailBody⟩ := rfl

theorem ternary_rule (plans : List Plan) (tails : List MExp) (i : Nat) (b : MExp) (hr : tails[i]?=some b) :
    ruleAtM (target plans tails).rules (2*i+2)=some ⟨3,.seq scanner
      (.seq (.param 2) (ControlledFragmentReplay.wholeView (render plans false false b)))⟩ := by
  simpa only [target,ruleAtM_eq_getElem?,Nat.add_assoc,List.getElem?_cons_succ]
    using pair_even (render plans false false) tails i b hr

theorem unary_rule (plans : List Plan) (tails : List MExp) (i : Nat) (b : MExp) (hr : tails[i]?=some b) :
    ruleAtM (target plans tails).rules (2*i+3)=some ⟨1,.seq scanner
      (.seq (.param 0) (render plans false false b))⟩ := by
  simpa only [target,ruleAtM_eq_getElem?,Nat.add_assoc,List.getElem?_cons_succ]
    using pair_odd (render plans false false) tails i b hr


/-- Expose the actual source body control at the caller origin. The
argument preview runs before any negative leaf can turn failure into success. -/
theorem source_call (plans : List Plan) (tails : List MExp) (hValid : Valid plans tails)
    (x : List Char) (m i p : Nat) (P : Plan) (hr : plans[i]?=some P)
    (E : List (List Char)) (a : MExp) (hp : p≤x.length) :
    evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E
      (.call i [a]) p=
    evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E
      (.seq (.andP a) (P.exp (fun j => .call (plans.length+j) [a]))) p := by
  let g := source plans tails
  let T := tblV g x .callByValuePar m
  have hbounded := hValid P (List.mem_of_getElem? hr)
  apply MixedOriginControl.call_plan_eq g g x T T i P
    (fun j => .call (plans.length+j) [a])
    (fun w j => valAt (T (plans.length+j) [w]) p) E a a p
    ⟨_,source_rule plans tails i P hr⟩ rfl
  · intro w
    cases m with
    | zero =>
      change none=P.eval (fun _ => none) p
      exact (Plan.eval_none P (Plan.all_of_forall (fun _ => rfl) P)).symm
    | succ k =>
      change valAt (tblV g x .callByValuePar (k+1) i [w]) p=_
      rw [valAt_tblV_succ (source_rule plans tails i P hr) [w] hp,Plan.exp_eval]
      apply Plan.eval_congr
      apply Plan.all_imp (t:=P) _ hbounded
      intro j hj
      have hj' := List.getElem?_eq_getElem hj
      rw [valAt_tblV_succ (leaf_rule plans tails j tails[j] hj') [w] hp]
      simp only [leaf,hj']
  · intro q ha
    apply Plan.all_imp (t:=P) _ hbounded
    intro j hj
    have hj' := List.getElem?_eq_getElem hj
    rw [evV_call_par (leaf_rule plans tails j tails[j] hj') rfl (by decide)]
    change (match (match evV g x .callByValuePar T E a p with
      | some (some z) => some (some [pre x p z]) | some none => some none | none => none) with
      | some (some W) => valAt (T (plans.length+j) W) p | some none => some none | none => none)=_
    rw [ha]


private theorem call_eq (plans : List Plan) (tails : List MExp) (hValid : Valid plans tails)
    (x : List Char) (m i p : Nat) (E : List (List Char))
    (G G' H H' : MExp) (hH' : FragmentConsumingSyntax.Syntax H') (hp : p≤x.length)
    (hG : ∀ q, q≤x.length → evV (source plans tails) x .callByValuePar
        (tblV (source plans tails) x .callByValuePar m) E G q=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E G' q)
    (hH : ∀ q, q≤x.length → evV (source plans tails) x .callByValuePar
        (tblV (source plans tails) x .callByValuePar m) E H q=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E H' q)
    (hprev : ∀ k, m=k+1 → ∀ e E p, p≤x.length →
      evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar k) E (render plans true false e) p=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq k) E (render plans false false e) p) :
    evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E (call plans true i G H) p=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E (call plans false i G' H') p := by
  cases hr : plans[i]? with
  | none => simp only [call,hr]; rfl
  | some P =>
    simp only [call,hr,Bool.false_eq_true,↓reduceIte]
    rw [source_call plans tails hValid x m i p P hr E (argument G H) hp]
    have harg := FragmentConsumingEntry.argument_congr _ _ x .callByValuePar .callByValueSeq _ _
      (tblV_ok _ _ _ m) E E G G' H H' hG hH p hp
    have hleaves : P.All (fun j =>
        evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E
          (.call (plans.length+j) [argument G H]) p=
        evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E
          (FragmentConsumingEntry.entry (2*j+2) (2*j+3) G' H') p) := by
      apply Plan.all_imp (t:=P) _ (hValid P (List.mem_of_getElem? hr))
      intro j hj
      have hj' := List.getElem?_eq_getElem hj
      cases m with
      | zero =>
        exact FragmentConsumingEntry.zero _ _ x (plans.length+j) (2*j+2) (2*j+3) p E E G G' H H'
          (render plans true false tails[j]) (leaf_rule plans tails j tails[j] hj')
          (compare_rule plans tails) (tail_compare_rule plans tails) harg
      | succ k =>
        apply FragmentConsumingEntry.transfer _ _ (target_firstOrder plans tails) x k k
          (plans.length+j) (2*j+2) (2*j+3) p E E G G' H H'
          (render plans true false tails[j]) (render plans false false tails[j])
          hH' (render_firstOrder plans false false tails[j]) hp (leaf_rule plans tails j tails[j] hj')
          (compare_rule plans tails) (tail_compare_rule plans tails)
          (ternary_rule plans tails j tails[j] hj') (unary_rule plans tails j tails[j] hj') hG hH
        intro w q hq; exact hprev k rfl tails[j] [w] q hq
    have hplans : evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E
        (P.exp (fun j => .call (plans.length+j) [argument G H])) p=
        evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E
          (P.exp (fun j => FragmentConsumingEntry.entry (2*j+2) (2*j+3) G' H')) p := by
      rw [Plan.exp_eval,Plan.exp_eval]
      exact Plan.eval_congr P hleaves
    exact ArgumentGuard.look_sequence_congr _ _ x .callByValuePar .callByValueSeq _ _ E E
      _ _ _ _ p harg hplans

private theorem render_seq (plans : List Plan) (par f : Bool) (a b : MExp) :
    render plans par f (.seq a b)=.seq (render plans par f a) (render plans par f b) := by
  cases f <;> rfl

private theorem render_alt (plans : List Plan) (par f : Bool) (a b : MExp) :
    render plans par f (.alt a b)=.alt (render plans par f a) (render plans par f b) := by
  cases f <;> rfl

private theorem render_star (plans : List Plan) (par f : Bool) (a : MExp) :
    render plans par f (.star a)=.star (render plans par f a) := by
  cases f <;> rfl

private theorem render_notP (plans : List Plan) (par f : Bool) (a : MExp) :
    render plans par f (.notP a)=.notP (render plans par false a) := by
  cases f <;> rfl
/-- Current-clock structural induction handles normal expressions and
consuming fragments together, switching to normal mode inside tests.
Previous-clock induction handles the actual callee continuation. -/
theorem evaluator_of_previous (plans : List Plan) (tails : List MExp) (hValid : Valid plans tails) (x : List Char) (m : Nat)
    (hprev : ∀ k, m=k+1 → ∀ e E p, p≤x.length →
      evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar k) E (render plans true false e) p=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq k) E (render plans false false e) p) :
    ∀ f e E p, p≤x.length →
      evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E (render plans true f e) p=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E (render plans false f e) p
  | false,.call i [], E, p, hp => call_eq plans tails hValid x m i p E .eps .eps .eps .eps .eps hp
      (by intro q hq; rfl) (by intro q hq; rfl) hprev
  | false,.call i [G], E, p, hp => call_eq plans tails hValid x m i p E _ _ .eps .eps .eps hp
      (fun q hq => evaluator_of_previous plans tails hValid x m hprev false G E q hq) (by intro q hq; rfl) hprev
  | false,.call i [G,H], E, p, hp => call_eq plans tails hValid x m i p E _ _ _ _ (render_fragment_syntax plans false H) hp
      (fun q hq => evaluator_of_previous plans tails hValid x m hprev false G E q hq)
      (fun q hq => evaluator_of_previous plans tails hValid x m hprev true H E q hq) hprev
  | f,.seq a b, E, p, hp => by
    have hh := evaluator_of_previous plans tails hValid x m hprev f a E p hp
    simp only [render_seq]
    cases hv : evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E (render plans true f a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_previous plans tails hValid x m hprev f b E q (evV_ok (tblV_ok _ _ _ m) _ p hp q hv)
  | f,.alt a b, E, p, hp => by
    have hh := evaluator_of_previous plans tails hValid x m hprev f a E p hp
    simp only [render_alt]
    cases hv : evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E (render plans true f a) p with
    | none => rw [evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some result => cases result with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]
        exact evaluator_of_previous plans tails hValid x m hprev f b E p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | f,.star a, E, p, hp => by
    simp only [render_star,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_previous plans tails hValid x m hprev f a E q (by omega))
  | f,.notP a, E, p, hp => by
    simp only [render_notP,evV]
    rw [evaluator_of_previous plans tails hValid x m hprev false a E p hp]
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

theorem evaluator_eq (plans : List Plan) (tails : List MExp) (hValid : Valid plans tails) (x : List Char) (m : Nat)
    (f : Bool) (e : MExp) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E (render plans true f e) p=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E (render plans false f e) p := by
  induction m generalizing f e E p with
  | zero => exact evaluator_of_previous plans tails hValid x 0 (by intro k hk; omega) f e E p hp
  | succ m ih =>
    apply evaluator_of_previous plans tails hValid x (m+1) _ f e E p hp
    intro k hk e E p hp
    have he : k=m := by omega
    subst k
    exact ih false e E p hp

theorem stable_eq (plans : List Plan) (tails : List MExp) (hValid : Valid plans tails) (x : List Char) (e : MExp) :
    evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar (iterBoundV (source plans tails) x))
      [] (render plans true false e) x.length=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq (iterBoundV (target plans tails) x))
      [] (render plans false false e) x.length := by
  have hdefined (v : Option Nat) :
      evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar (iterBoundV (source plans tails) x))
        [] (render plans true false e) x.length=some v ↔
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq (iterBoundV (target plans tails) x))
        [] (render plans false false e) x.length=some v := by
    rw [←tblV_stable (source plans tails) x .callByValuePar (Nat.le_refl _),
      ←tblV_stable (target plans tails) x .callByValueSeq (Nat.le_refl _)]
    exact exists_congr (fun m => by rw [evaluator_eq plans tails hValid x m false e [] x.length (Nat.le_refl _)])
  cases hs : evV (source plans tails) x .callByValuePar
      (tblV (source plans tails) x .callByValuePar (iterBoundV (source plans tails) x)) [] (render plans true false e) x.length with
  | none =>
    cases ht : evV (target plans tails) x .callByValueSeq
        (tblV (target plans tails) x .callByValueSeq (iterBoundV (target plans tails) x)) [] (render plans false false e) x.length with
    | none => rfl
    | some v => have hh := (hdefined v).mpr ht; rw [hs] at hh; cases hh
  | some v => exact ((hdefined v).mp hs).symm

/-- One fixed recursive Seq grammar preserves all finite observations on
unchanged strings, including failures and absence of finite observations. -/
theorem observations_iff (plans : List Plan) (tails : List MExp) (hValid : Valid plans tails) (e : MExp) (x : List Char) (r : Option (List Char)) :
    SObs (source plans tails) .callByValuePar (render plans true false e) x r ↔
      SObs (target plans tails) .callByValueSeq (render plans false false e) x r := by
  rw [←decideObsV_iff (source_firstOrder plans tails) (by decide) (render_firstOrder plans true false e),
    ←decideObsV_iff (target_firstOrder plans tails) (by decide) (render_firstOrder plans false false e)]
  unfold decideObsV
  rw [stable_eq plans tails hValid]

theorem language_translation (plans : List Plan) (tails : List MExp) (hValid : Valid plans tails) (e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (source plans tails) .callByValuePar (render plans true false e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target plans tails,render plans false false e,target_firstOrder plans tails,render_firstOrder plans false false e,
    fun x => observations_iff plans tails hValid e x (some [])⟩

end Shallot.MacroPeg.CBV.FragmentOriginRecursive
