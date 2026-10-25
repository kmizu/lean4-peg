import MacroPeg.CBV.FragmentConsumingRecursive
import MacroPeg.CBV.MixedOriginControl
import MacroPeg.CBV.ArgumentGuard

/-! Recursive call transfer with consuming final-fragment control. -/
namespace Shallot.MacroPeg.CBV.FragmentMixedRecursive
open ReplayControlFusion (Plan)
open RuntimeShiftFilter (scanner)
open ControlledFragmentReplay (argument)
open MixedOriginControl (stuck_eval)
abbrev Part := Bool × MExp
def head (split : Bool) : MExp := if split then scanner else .eps
def triple (split : Bool) (b : MExp) : MExp :=
  if split then .seq scanner (.seq (.param 2) (ControlledFragmentReplay.wholeView b)) else MExp.failAlways
def single (split : Bool) (b : MExp) : MExp :=
  if split then .seq scanner (.seq (.param 0) b) else b
def pair (split : Bool) (b : MExp) : List MRule := [⟨3,triple split b⟩,⟨1,single split b⟩]

def stuck : MExp := .star .eps
def entry (kinds : List Bool) (n j : Nat) (G H : MExp) : MExp :=
  if j=n then .seq (.andP (argument G H)) stuck
  else if j=n+1 then .seq (.andP (argument G H)) (.call (2*n+2) [.eps])
  else if kinds[j]?.getD true then FragmentConsumingEntry.entry (2*j+2) (2*j+3) G H
  else .call (2*j+3) [argument G H]

private theorem scanner_firstOrder : scanner.FirstOrder := by
  simp [scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,MExp.FirstOrder,MExp.failAlways]

theorem entry_firstOrder (kinds : List Bool) (n j : Nat) (G H : MExp) (hG : G.FirstOrder) (hH : H.FirstOrder) :
    (entry kinds n j G H).FirstOrder := by
  unfold entry; split
  · exact ⟨⟨⟨scanner_firstOrder,scanner_firstOrder,hG⟩,hH⟩,True.intro⟩
  · split
    · exact ⟨⟨⟨scanner_firstOrder,scanner_firstOrder,hG⟩,hH⟩,⟨True.intro,True.intro⟩⟩
    · split
      · exact FragmentConsumingEntry.entry_firstOrder _ _ G H hG hH
      · exact ⟨⟨⟨scanner_firstOrder,scanner_firstOrder,hG⟩,hH⟩,True.intro⟩

open FragmentConsumingRecursive (aWord aWord_syntax)

def call (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool) (i : Nat) (G H : MExp) : MExp :=
  match plans[i]? with
  | none => MExp.failAlways
  | some P => if par then .call i [argument G H]
    else .seq (PartialCodewordCapture.look (argument G H))
      (P.exp (fun j => entry kinds n j G H))

/-- Four templates describe before, fragment controls G/H, and after.
The source has one actual capture, guarded at its real two endpoints. -/
def guardedCall (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool)
    (i : Nat) (before G H after : MExp) : MExp :=
  match plans[i]? with
  | none => MExp.failAlways
  | some _ => if par then
      .call i [.seq (PartialCodewordCapture.look before) (.seq (argument G H) (PartialCodewordCapture.look after))]
    else .seq (PartialCodewordCapture.look before) (.seq (PartialCodewordCapture.look (.seq (argument G H) after))
      (call kinds n plans false i G H))

private theorem guarded_firstOrder (kinds : List Bool) (n : Nat) (plans : List Plan)
    (par : Bool) (i : Nat) (before G H after : MExp)
    (hb : before.FirstOrder) (hG : G.FirstOrder) (hH : H.FirstOrder) (ha : after.FirstOrder)
    (hc : (call kinds n plans false i G H).FirstOrder) :
    (guardedCall kinds n plans par i before G H after).FirstOrder := by
  unfold guardedCall
  cases plans[i]? with
  | none => trivial
  | some P =>
    cases par
    · exact ⟨hb,⟨⟨⟨scanner_firstOrder,scanner_firstOrder,hG⟩,hH⟩,ha⟩,hc⟩
    · exact ⟨⟨hb,⟨⟨scanner_firstOrder,scanner_firstOrder,hG⟩,hH⟩,ha⟩,True.intro⟩

/-- Direct argument fusion is available only when every source body query
and output uses ordinary replay or the capture-independent stuck leaf. -/
def replayOnly (kinds : List Bool) (n : Nat) : Plan → Bool
  | .leaf j => (j==n) || !(kinds[j]?.getD true)
  | .alt a b | .guard a b => replayOnly kinds n a && replayOnly kinds n b
  | .notP a => replayOnly kinds n a

def eligible (kinds : List Bool) (n : Nat) (plans : List Plan) (i : Nat) : Bool :=
  match plans[i]? with | none => false | some P => replayOnly kinds n P

theorem replayOnly_sound (kinds : List Bool) (n : Nat) : ∀ P,
    replayOnly kinds n P=true → P.All (fun j => j=n ∨ kinds[j]?=some false)
  | .leaf j, h => by
    change j=n ∨ kinds[j]?=some false
    by_cases he : j=n
    · exact Or.inl he
    · right
      cases hk : kinds[j]? with
      | none => simp [replayOnly,he,hk] at h
      | some v => cases v with
        | false => rfl
        | true => simp [replayOnly,he,hk] at h
  | .alt a b, h | .guard a b, h =>
    ⟨replayOnly_sound kinds n a (Bool.and_eq_true_iff.mp h).1,
      replayOnly_sound kinds n b (Bool.and_eq_true_iff.mp h).2⟩
  | .notP a, h => replayOnly_sound kinds n a h

def directEntry (n j : Nat) (a : MExp) : MExp :=
  if j=n then .seq (.andP a) stuck else .call (2*j+3) [a]
def directCall (n : Nat) (plans : List Plan) (par : Bool) (i : Nat) (a : MExp) : MExp :=
  match plans[i]? with
  | none => MExp.failAlways
  | some P => if par then .call i [a] else .seq (.andP a) (P.exp (fun j => directEntry n j a))

private theorem direct_firstOrder (n : Nat) (plans : List Plan) (par : Bool) (i : Nat)
    (a : MExp) (ha : a.FirstOrder) : (directCall n plans par i a).FirstOrder := by
  unfold directCall
  cases plans[i]? with
  | none => trivial
  | some P =>
    cases par
    · refine ⟨ha,Plan.exp_firstOrder ?_ P⟩
      intro j; unfold directEntry; split
      · exact ⟨ha,True.intro⟩
      · exact ⟨ha,True.intro⟩
    · exact ⟨ha,True.intro⟩

/-- In fragment mode only a-consuming syntax is generated. Tests switch
back to normal mode so they may inspect parents or invoke recursive users.
The second template of a two-template normal call describes H itself,
not its star test. Four-template calls also carry origin/endpoint tests. -/
def render (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool) : Bool → MExp → MExp
  | false,.call i [] => call kinds n plans par i .eps .eps
  | false,.call i [G] => if eligible kinds n plans i then directCall n plans par i (render kinds n plans par false G)
    else call kinds n plans par i (render kinds n plans par false G) .eps
  | false,.call i [G,H] => call kinds n plans par i (render kinds n plans par false G) (render kinds n plans par true H)
  | false,.call i [before,G,H,after] => guardedCall kinds n plans par i
      (render kinds n plans par false before) (render kinds n plans par false G)
      (render kinds n plans par true H) (render kinds n plans par false after)
  | f,.seq a b => .seq (render kinds n plans par f a) (render kinds n plans par f b)
  | f,.alt a b => .alt (render kinds n plans par f a) (render kinds n plans par f b)
  | f,.star a => .star (render kinds n plans par f a)
  | _,.notP a => .notP (render kinds n plans par false a)
  | _,.eps => .eps
  | true,.chr c => if c='a' then .chr 'a' else MExp.failAlways
  | true,.lit w => if ∀ c∈w, c='a' then aWord w.length else MExp.failAlways
  | false,.param k => .param k
  | false,.any => .any | false,.chr c => .chr c
  | false,.range a b => .range a b | false,.lit w => .lit w
  | _,_ => MExp.failAlways

private theorem call_firstOrder (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool) (i : Nat)
    (G H : MExp) (hG : G.FirstOrder) (hH : H.FirstOrder) : (call kinds n plans par i G H).FirstOrder := by
  unfold call
  cases plans[i]? with
  | none => trivial
  | some b =>
    cases par
    · exact ⟨⟨⟨scanner_firstOrder,scanner_firstOrder,hG⟩,hH⟩,
        Plan.exp_firstOrder (fun j => entry_firstOrder kinds n j G H hG hH) b⟩
    · exact ⟨⟨⟨scanner_firstOrder,scanner_firstOrder,hG⟩,hH⟩,True.intro⟩

theorem render_firstOrder (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool) : ∀ f e, (render kinds n plans par f e).FirstOrder
  | false,.call i [] => call_firstOrder kinds n plans par i .eps .eps True.intro True.intro
  | false,.call i [G] => by
      simp only [render]; split
      · exact direct_firstOrder n plans par i _ (render_firstOrder kinds n plans par false G)
      · exact call_firstOrder kinds n plans par i _ .eps (render_firstOrder kinds n plans par false G) True.intro
  | false,.call i [G,H] => call_firstOrder kinds n plans par i _ _
      (render_firstOrder kinds n plans par false G) (render_firstOrder kinds n plans par true H)
  | false,.call i [before,G,H,after] => guarded_firstOrder kinds n plans par i _ _ _ _
      (render_firstOrder kinds n plans par false before) (render_firstOrder kinds n plans par false G)
      (render_firstOrder kinds n plans par true H) (render_firstOrder kinds n plans par false after)
      (call_firstOrder kinds n plans false i _ _ (render_firstOrder kinds n plans par false G)
        (render_firstOrder kinds n plans par true H))
  | f,.seq a b | f,.alt a b => by
      have ha := render_firstOrder kinds n plans par f a
      have hb := render_firstOrder kinds n plans par f b
      cases f <;> exact ⟨ha,hb⟩
  | f,.star a => by
      have ha := render_firstOrder kinds n plans par f a
      cases f <;> exact ha
  | f,.notP a => by cases f <;> exact render_firstOrder kinds n plans par false a
  | true,.chr c => by simp only [render]; split <;> trivial
  | true,.lit w => by
      simp only [render]; split
      · exact FragmentConsumingSyntax.firstOrder (aWord_syntax _)
      · trivial
  | f,.eps => by cases f <;> trivial
  | false,.param _ | false,.any | false,.chr _ | false,.range _ _ | false,.lit _ => trivial
  | true,.param _ | true,.any | true,.range _ _ | true,.call _ _
  | false,.call _ [_,_,_] | false,.call _ (_::_::_::_::_::_) => trivial
  | f,.dbg _ | f,.lam _ _ | f,.callParam _ _ | f,.invoke _ _ _ => by cases f <;> trivial

/-- The single argument of a replay-only source call is the actual parser
argument itself, rather than the G test of a fragment-capture template. -/
theorem direct_source_syntax (kinds : List Bool) (n : Nat) (plans : List Plan) (i : Nat) (a : MExp)
    (he : eligible kinds n plans i=true) :
    render kinds n plans true false (.call i [a])=.call i [render kinds n plans true false a] := by
  simp only [render,he,ite_true,directCall]
  cases hr : plans[i]? with
  | none => simp [eligible,hr] at he
  | some P => rfl

/-- The four surface templates become one actual unary Par argument,
with the second test at the endpoint selected by G/H. -/
theorem guarded_source_syntax (kinds : List Bool) (n : Nat) (plans : List Plan)
    (i : Nat) (P : Plan) (hr : plans[i]?=some P) (before G H after : MExp) :
    render kinds n plans true false (.call i [before,G,H,after])=
      .call i [.seq (PartialCodewordCapture.look (render kinds n plans true false before))
        (.seq (argument (render kinds n plans true false G) (render kinds n plans true true H))
          (PartialCodewordCapture.look (render kinds n plans true false after)))] := by
  simp only [render,guardedCall,hr,ite_true]

theorem render_fragment_syntax (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool) :
    ∀ e, FragmentConsumingSyntax.Syntax (render kinds n plans par true e)
  | .seq a b => .seq (render_fragment_syntax kinds n plans par a) (render_fragment_syntax kinds n plans par b)
  | .alt a b => .alt (render_fragment_syntax kinds n plans par a) (render_fragment_syntax kinds n plans par b)
  | .star a => .star (render_fragment_syntax kinds n plans par a)
  | .notP a => .reject _ (render_firstOrder kinds n plans par false a)
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
def leaf (plans : List Plan) (tails : List Part) (j : Nat) : MExp :=
  if j=tails.length+1 then scanner else match tails[j]? with
  | none => stuck
  | some b => .seq (head b.1) (.seq (.param 0) (render (tails.map Prod.fst) tails.length plans true false b.2))
def source (plans : List Plan) (tails : List Part) : MGrammar :=
  ⟨plans.map (fun P => ⟨1,P.exp (leaf plans tails)⟩)++
    (tails.map (fun b => ⟨1,.seq (head b.1) (.seq (.param 0) (render (tails.map Prod.fst) tails.length plans true false b.2))⟩)++[⟨1,stuck⟩,⟨1,scanner⟩])⟩
abbrev target (plans : List Plan) (tails : List Part) : MGrammar :=
  ⟨⟨1,.param 0⟩::⟨1,ControlledFragmentReplay.tailBody⟩::
    (tails.flatMap (fun b => pair b.1 (render (tails.map Prod.fst) tails.length plans false false b.2))++[⟨1,scanner⟩])⟩
/-- A finite syntax check on every logical user's leaf indices. -/
def Valid (plans : List Plan) (tails : List Part) : Prop :=
  ∀ P∈plans, P.All (fun j => j≤tails.length+1)

theorem leaf_firstOrder (plans : List Plan) (tails : List Part) (j : Nat) :
    (leaf plans tails j).FirstOrder := by
  unfold leaf
  split
  · exact scanner_firstOrder
  · cases tails[j]? with
    | none => trivial
    | some b => exact ⟨by cases b.1 <;> trivial,True.intro,render_firstOrder (tails.map Prod.fst) tails.length plans true false b.2⟩
theorem source_firstOrder (plans : List Plan) (tails : List Part) : (source plans tails).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨P,_,rfl⟩ := List.mem_map.mp hr
    exact Plan.exp_firstOrder (leaf_firstOrder plans tails) P
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
      exact ⟨by cases b.1 <;> trivial,True.intro,render_firstOrder (tails.map Prod.fst) tails.length plans true false b.2⟩
    · rcases List.mem_cons.mp hr with rfl | hr
      · trivial
      · have he : r=⟨1,scanner⟩ := by simpa using hr
        subst r; exact scanner_firstOrder
theorem target_firstOrder (plans : List Plan) (tails : List Part) : (target plans tails).FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with he | hr
  · subst r; trivial
  · rcases List.mem_cons.mp hr with he | hr
    · subst r; exact ⟨scanner_firstOrder,True.intro⟩
    · rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨b,_,hr⟩ := List.mem_flatMap.mp hr
        have hf := render_firstOrder (tails.map Prod.fst) tails.length plans false false b.2
        simp only [pair,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl
        · cases he : b.1 <;> simp only [triple,Bool.false_eq_true,ite_false,ite_true]
          · trivial
          · exact ⟨scanner_firstOrder,True.intro,firstOrder_subst (args:=[CaptureViews.prefixExpr 3])
              ⟨CaptureViews.prefixExpr_firstOrder 3,True.intro⟩ _ hf⟩
        · cases he : b.1 <;> simp only [single,Bool.false_eq_true,ite_false,ite_true]
          · exact hf
          · exact ⟨scanner_firstOrder,True.intro,hf⟩
      · have he : r=⟨1,scanner⟩ := by simpa using hr
        subst r; exact scanner_firstOrder

theorem source_rule (plans : List Plan) (tails : List Part) (i : Nat) (P : Plan) (hr : plans[i]?=some P) :
    ruleAtM (source plans tails).rules i=some ⟨1,P.exp (leaf plans tails)⟩ := by
  have hi : i<plans.length := (List.getElem?_eq_some_iff.mp hr).choose
  simp only [source,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hi)]
  simp only [List.getElem?_map,hr,Option.map_some]
theorem leaf_rule (plans : List Plan) (tails : List Part) (j : Nat) (b : Part) (hr : tails[j]?=some b) :
    ruleAtM (source plans tails).rules (plans.length+j)=
      some ⟨1,.seq (head b.1) (.seq (.param 0) (render (tails.map Prod.fst) tails.length plans true false b.2))⟩ := by
  have hj : j<tails.length := (List.getElem?_eq_some_iff.mp hr).choose
  simp only [source,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_map,Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa using hj)]
  simp only [List.getElem?_map,hr,Option.map_some]

theorem stuck_rule (plans : List Plan) (tails : List Part) :
    ruleAtM (source plans tails).rules (plans.length+tails.length)=some ⟨1,stuck⟩ := by
  simp [source,ruleAtM_eq_getElem?]

theorem scanner_rule (plans : List Plan) (tails : List Part) :
    ruleAtM (source plans tails).rules (plans.length+tails.length+1)=some ⟨1,scanner⟩ := by
  simp only [source,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_map]
  rw [show plans.length+tails.length+1-plans.length=tails.length+1 from by omega]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem source_leaf_rule (plans : List Plan) (tails : List Part) (j : Nat) (hj : j≤tails.length+1) :
    ruleAtM (source plans tails).rules (plans.length+j)=some ⟨1,leaf plans tails j⟩ := by
  by_cases hs : j=tails.length+1
  · subst j; simpa [leaf,Nat.add_assoc] using scanner_rule plans tails
  by_cases he : j=tails.length
  · subst j; simpa [leaf] using stuck_rule plans tails
  have hj' : j<tails.length := by omega
  simpa [leaf,hs,List.getElem?_eq_getElem hj'] using
    leaf_rule plans tails j tails[j] (List.getElem?_eq_getElem hj')

/-- The distinguished leaf ignores the captured value at every clock,
including the initial empty table. Argument evaluation still comes first. -/
theorem stuck_call (plans : List Plan) (tails : List Part) (x : List Char)
    (m p : Nat) (hp : p≤x.length) (E : List (List Char)) (a : MExp) :
    evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E
      (.call (plans.length+tails.length) [a]) p=
    evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E
      (.seq (.andP a) stuck) p := by
  have hrow : ∀ w, valAt (tblV (source plans tails) x .callByValuePar m
      (plans.length+tails.length) [w]) p=none := by
    intro w
    cases m with
    | zero => simp only [tblV,valAt_nil]
    | succ k => rw [valAt_tblV_succ (stuck_rule plans tails) [w] hp]; exact stuck_eval _ _ _ _ _ _
  rw [evV_call_par (stuck_rule plans tails) rfl (by decide)]
  simp only [evParArgs]
  simp only [evV]
  rw [CallLookahead.evV_peek]
  unfold CallLookahead.peek
  change (match (match evV (source plans tails) x .callByValuePar
    (tblV (source plans tails) x .callByValuePar m) E a p with
      | some (some q) => some (some [pre x p q]) | some none => some none | none => none) with
      | some (some W) => valAt (tblV (source plans tails) x .callByValuePar m (plans.length+tails.length) W) p
      | some none => some none | none => none)=
    (match (match evV (source plans tails) x .callByValuePar
      (tblV (source plans tails) x .callByValuePar m) E a p with
        | some (some _) => some (some p) | other => other) with
        | some (some q) => evV (source plans tails) x .callByValuePar
          (tblV (source plans tails) x .callByValuePar m) E stuck q
        | other => other)
  cases ha : evV (source plans tails) x .callByValuePar
    (tblV (source plans tails) x .callByValuePar m) E a p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some q => exact (hrow _).trans (stuck_eval _ _ _ _ _ _).symm


private theorem pair_even (f : MExp → MExp) (tails : List Part) : ∀ i b, tails[i]?=some b →
    (tails.flatMap (fun b => pair b.1 (f b.2)))[2*i]?=some ⟨3,triple b.1 (f b.2)⟩ := by
  induction tails with
  | nil => intro i b hr; simp at hr
  | cons a tails ih =>
    intro i b hr
    cases i with
    | zero => simp at hr; subst b; rfl
    | succ i =>
      have hi := ih i b (by simpa using hr)
      simpa [pair,Nat.mul_add,Nat.add_assoc] using hi
private theorem pair_odd (f : MExp → MExp) (tails : List Part) : ∀ i b, tails[i]?=some b →
    (tails.flatMap (fun b => pair b.1 (f b.2)))[2*i+1]?=some ⟨1,single b.1 (f b.2)⟩ := by
  induction tails with
  | nil => intro i b hr; simp at hr
  | cons a tails ih =>
    intro i b hr
    cases i with
    | zero => simp at hr; subst b; rfl
    | succ i =>
      have hi := ih i b (by simpa using hr)
      simpa [pair,Nat.mul_add,Nat.add_assoc] using hi

theorem pairs_length (f : MExp → MExp) (tails : List Part) :
    (tails.flatMap (fun b => pair b.1 (f b.2))).length=2*tails.length := by
  induction tails with
  | nil => simp
  | cons b tails ih =>
    rw [List.flatMap_cons,List.length_append,ih]
    change 2+2*tails.length=2*(tails.length+1)
    omega

theorem target_scanner_rule (plans : List Plan) (tails : List Part) :
    ruleAtM (target plans tails).rules (2*tails.length+2)=some ⟨1,scanner⟩ := by
  simp only [ruleAtM_eq_getElem?,List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by rw [pairs_length]; exact Nat.le_refl _)]
  rw [pairs_length]
  simp

theorem compare_rule (plans : List Plan) (tails : List Part) : ruleAtM (target plans tails).rules 0=some ⟨1,.param 0⟩ := rfl
theorem tail_compare_rule (plans : List Plan) (tails : List Part) :
    ruleAtM (target plans tails).rules 1=some ⟨1,ControlledFragmentReplay.tailBody⟩ := rfl

theorem ternary_rule (plans : List Plan) (tails : List Part) (i : Nat) (b : Part) (hr : tails[i]?=some b) :
    ruleAtM (target plans tails).rules (2*i+2)=some ⟨3,triple b.1 (render (tails.map Prod.fst) tails.length plans false false b.2)⟩ := by
  have hi : i<tails.length := (List.getElem?_eq_some_iff.mp hr).choose
  simp only [ruleAtM_eq_getElem?,List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by rw [pairs_length]; omega)]
  exact pair_even (render (tails.map Prod.fst) tails.length plans false false) tails i b hr

theorem unary_rule (plans : List Plan) (tails : List Part) (i : Nat) (b : Part) (hr : tails[i]?=some b) :
    ruleAtM (target plans tails).rules (2*i+3)=some ⟨1,single b.1 (render (tails.map Prod.fst) tails.length plans false false b.2)⟩ := by
  have hi : i<tails.length := (List.getElem?_eq_some_iff.mp hr).choose
  simp only [ruleAtM_eq_getElem?,List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by rw [pairs_length]; omega)]
  exact pair_odd (render (tails.map Prod.fst) tails.length plans false false) tails i b hr

/-- Expose the actual source body control at the caller origin. The
argument preview runs before any negative leaf can turn failure into success. -/
theorem source_call (plans : List Plan) (tails : List Part) (hValid : Valid plans tails)
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
      rw [valAt_tblV_succ (source_leaf_rule plans tails j hj) [w] hp]
  · intro q ha
    apply Plan.all_imp (t:=P) _ hbounded
    intro j hj
    rw [evV_call_par (source_leaf_rule plans tails j hj) rfl (by decide)]
    change evV (source plans tails) x .callByValuePar T E a p=some (some q) at ha
    simp only [evParArgs,ha]


/-- Ordinary replay absorbs the argument endpoint into Seq evaluation while
retaining the complete captured value for the callee continuation. -/
theorem bare_transfer (g h : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m i j p : Nat) (E : List (List Char)) (a a' b b' : MExp) (ha : a.FirstOrder)
    (hr : ruleAtM g.rules i=some ⟨1,.seq .eps (.seq (.param 0) b)⟩)
    (ht : ruleAtM h.rules j=some ⟨1,b'⟩) (hp : p≤x.length)
    (he : evV g x .callByValuePar (tblV g x .callByValuePar m) E a p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq m) E a' p)
    (hc : ∀ k, m=k+1 → ∀ w q, q≤x.length →
      evV g x .callByValuePar (tblV g x .callByValuePar k) [w] b q=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) [w] b' q) :
    evV g x .callByValuePar (tblV g x .callByValuePar m) E (.call i [a]) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq m) E (.call j [a']) p := by
  rw [evV_call_par hr rfl (by decide),evV_call_seq ht rfl p]
  simp only [evParArgs,evSeqArgs]
  rw [←he]
  cases hv : evV g x .callByValuePar (tblV g x .callByValuePar m) E a p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some q =>
      obtain ⟨hq,hpre⟩ := ReplayFusion.success_prefix (tblV_sound hg (by decide) m) E a ha p q hp hv
      have hstrip : Shallot.stripPrefix? (pre x p q) (sfx x p)=some (sfx x q) :=
        (CBVtoCBN.stripPrefix_exact _ _ _).mpr hpre
      change valAt (tblV g x .callByValuePar m i [pre x p q]) p=
        valAt (tblV h x .callByValueSeq m j [pre x p q]) q
      cases m with
      | zero => simp only [tblV,valAt_nil]
      | succ k =>
        rw [valAt_tblV_succ hr [pre x p q] hp,valAt_tblV_succ ht [pre x p q] hq]
        change evV g x .callByValuePar (tblV g x .callByValuePar k) [pre x p q] (.seq (.param 0) b) p=_
        have hvp : evV g x .callByValuePar (tblV g x .callByValuePar k) [pre x p q] (.param 0) p=some (some q) := by
          simp only [evV,List.getElem?_cons_zero,hstrip,length_sfx x hq]
        rw [evV_seq_ok hvp]
        exact hc k rfl _ q hq

private theorem all_pair {A B : Nat → Prop} : ∀ (P : Plan), P.All A → P.All B → P.All (fun i => A i ∧ B i)
  | .leaf _, ha, hb => ⟨ha,hb⟩
  | .alt a b, ha, hb | .guard a b, ha, hb => ⟨all_pair a ha.1 hb.1,all_pair b ha.2 hb.2⟩
  | .notP a, ha, hb => all_pair a ha hb

theorem direct_call_eq (plans : List Plan) (tails : List Part) (hValid : Valid plans tails)
    (x : List Char) (m i p : Nat) (E : List (List Char)) (a a' : MExp) (ha : a.FirstOrder)
    (hp : p≤x.length) (hEligible : eligible (tails.map Prod.fst) tails.length plans i=true)
    (harg : evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E a p=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E a' p)
    (hprev : ∀ k, m=k+1 → ∀ e E p, p≤x.length →
      evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar k) E
        (render (tails.map Prod.fst) tails.length plans true false e) p=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq k) E
        (render (tails.map Prod.fst) tails.length plans false false e) p) :
    evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E
      (directCall tails.length plans true i a) p=
    evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E
      (directCall tails.length plans false i a') p := by
  cases hr : plans[i]? with
  | none => simp [eligible,hr] at hEligible
  | some P =>
    have hOrd := replayOnly_sound (tails.map Prod.fst) tails.length P
      (by simpa only [eligible,hr] using hEligible)
    have hb := all_pair P (hValid P (List.mem_of_getElem? hr)) hOrd
    simp only [directCall,hr,Bool.false_eq_true,ite_false,ite_true]
    rw [source_call plans tails hValid x m i p P hr E a hp]
    have hleaves : P.All (fun j =>
        evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E
          (.call (plans.length+j) [a]) p=
        evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E
          (directEntry tails.length j a') p) := by
      apply Plan.all_imp (t:=P) _ hb
      intro j hj
      rcases hj with ⟨hj,hkind⟩
      by_cases he : j=tails.length
      · subst j
        rw [stuck_call plans tails x m p hp E a]
        simp only [directEntry,ite_true]
        exact ArgumentGuard.look_sequence_congr _ _ x .callByValuePar .callByValueSeq _ _ E E
          _ _ _ _ p harg ((stuck_eval _ _ _ _ _ _).trans (stuck_eval _ _ _ _ _ _).symm)
      have hk := hkind.resolve_left he
      have hj : j<tails.length := by
        have hb := (List.getElem?_eq_some_iff.mp hk).choose
        simpa using hb
      have hj' := List.getElem?_eq_getElem hj
      have hsplit : tails[j].1=false := by
        simpa only [List.getElem?_map,hj',Option.map_some,Option.some.injEq] using hk
      simp only [directEntry,he,ite_false]
      apply bare_transfer _ _ (source_firstOrder plans tails) x m (plans.length+j) (2*j+3) p E a a'
        (render (tails.map Prod.fst) tails.length plans true false tails[j].2)
        (render (tails.map Prod.fst) tails.length plans false false tails[j].2) ha
        (by simpa only [head,hsplit,Bool.false_eq_true,ite_false] using leaf_rule plans tails j tails[j] hj')
        (by simpa only [single,hsplit,Bool.false_eq_true,ite_false] using unary_rule plans tails j tails[j] hj') hp harg
      intro k hkm w q hq; exact hprev k hkm tails[j].2 [w] q hq
    have hplans : evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E
        (P.exp (fun j => .call (plans.length+j) [a])) p=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E
        (P.exp (fun j => directEntry tails.length j a')) p := by
      rw [Plan.exp_eval,Plan.exp_eval]
      exact Plan.eval_congr P hleaves
    exact ArgumentGuard.look_sequence_congr _ _ x .callByValuePar .callByValueSeq _ _ E E
      _ _ _ _ p harg hplans

/-- The source capture is evaluated before an independent scanner leaf.
The target passes an empty value at the old origin, preserving clock zero. -/
theorem scanner_transfer (g h : MGrammar) (x : List Char) (m i j p : Nat)
    (E : List (List Char)) (a a' : MExp) (hp : p≤x.length)
    (hr : ruleAtM g.rules i=some ⟨1,scanner⟩)
    (ht : ruleAtM h.rules j=some ⟨1,scanner⟩)
    (he : evV g x .callByValuePar (tblV g x .callByValuePar m) E a p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq m) E a' p) :
    evV g x .callByValuePar (tblV g x .callByValuePar m) E (.call i [a]) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq m) E
        (.seq (.andP a') (.call j [.eps])) p := by
  have hrow (w : List Char) :
      valAt (tblV g x .callByValuePar m i [w]) p=
      valAt (tblV h x .callByValueSeq m j [[]]) p := by
    cases m with
    | zero => rfl
    | succ k =>
      rw [valAt_tblV_succ hr [w] hp,valAt_tblV_succ ht [[]] hp]
      exact ParserPrefixFusion.pure_eval g h x .callByValuePar .callByValueSeq _ _ [w] [[]] scanner
        (by simp [scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,MExp.failAlways,ParserPrefixFusion.Pure]) p
  have hempty : evV h x .callByValueSeq (tblV h x .callByValueSeq m) E (.call j [.eps]) p=
      valAt (tblV h x .callByValueSeq m j [[]]) p := by
    rw [evV_call_seq ht rfl p]
    simp [evSeqArgs,evV,pre]
  have hlook : evV h x .callByValueSeq (tblV h x .callByValueSeq m) E (.andP a') p=
      CallLookahead.peek p (evV g x .callByValuePar (tblV g x .callByValuePar m) E a p) := by
    rw [CallLookahead.evV_peek,←he]
  rw [evV_call_par hr rfl (by decide)]
  change (match evParArgs g x .callByValuePar (tblV g x .callByValuePar m) E [a] p with
    | some (some W) => valAt (tblV g x .callByValuePar m i W) p
    | some none => some none | none => none)=
    (match evV h x .callByValueSeq (tblV h x .callByValueSeq m) E (.andP a') p with
    | some (some q) => evV h x .callByValueSeq (tblV h x .callByValueSeq m) E (.call j [.eps]) q
    | other => other)
  rw [hlook]
  cases hv : evV g x .callByValuePar (tblV g x .callByValuePar m) E a p with
  | none => simp [evParArgs,hv,CallLookahead.peek]
  | some v => cases v with
    | none => simp [evParArgs,hv,CallLookahead.peek]
    | some q => simp only [evParArgs,hv,CallLookahead.peek]; exact (hrow _).trans hempty.symm

private theorem call_eq (plans : List Plan) (tails : List Part) (hValid : Valid plans tails)
    (x : List Char) (m i p : Nat) (E : List (List Char))
    (G G' H H' : MExp) (hH' : FragmentConsumingSyntax.Syntax H') (hp : p≤x.length)
    (hGFO : G.FirstOrder) (hHFO : H.FirstOrder)
    (hG : ∀ q, q≤x.length → evV (source plans tails) x .callByValuePar
        (tblV (source plans tails) x .callByValuePar m) E G q=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E G' q)
    (hH : ∀ q, q≤x.length → evV (source plans tails) x .callByValuePar
        (tblV (source plans tails) x .callByValuePar m) E H q=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E H' q)
    (hprev : ∀ k, m=k+1 → ∀ e E p, p≤x.length →
      evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar k) E (render (tails.map Prod.fst) tails.length plans true false e) p=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq k) E (render (tails.map Prod.fst) tails.length plans false false e) p) :
    evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E (call (tails.map Prod.fst) tails.length plans true i G H) p=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E (call (tails.map Prod.fst) tails.length plans false i G' H') p := by
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
          (entry (tails.map Prod.fst) tails.length j G' H') p) := by
      apply Plan.all_imp (t:=P) _ (hValid P (List.mem_of_getElem? hr))
      intro j hj
      by_cases he : j=tails.length
      · subst j
        rw [stuck_call plans tails x m p hp E (argument G H)]
        simp only [entry,ite_true]
        exact ArgumentGuard.look_sequence_congr _ _ x .callByValuePar .callByValueSeq _ _ E E
          _ _ _ _ p harg ((stuck_eval _ _ _ _ _ _).trans (stuck_eval _ _ _ _ _ _).symm)
      by_cases hs : j=tails.length+1
      · subst j
        simp only [entry,he,ite_false,ite_true]
        exact scanner_transfer _ _ x m (plans.length+(tails.length+1)) (2*tails.length+2) p E
          (argument G H) (argument G' H') hp
          (by simpa [Nat.add_assoc] using scanner_rule plans tails) (target_scanner_rule plans tails) harg
      have hj : j<tails.length := by omega
      simp only [entry,he,hs,ite_false]
      have hj' := List.getElem?_eq_getElem hj
      have hkinds : (tails.map Prod.fst)[j]?=some tails[j].1 := by simp only [List.getElem?_map,hj',Option.map_some]
      simp only [hkinds,Option.getD_some]
      cases hsplit : tails[j].1 with
      | false =>
        simp only [Bool.false_eq_true,ite_false]
        apply bare_transfer _ _ (source_firstOrder plans tails) x m (plans.length+j) (2*j+3) p E
          (argument G H) (argument G' H')
          (render (tails.map Prod.fst) tails.length plans true false tails[j].2)
          (render (tails.map Prod.fst) tails.length plans false false tails[j].2)
          ⟨⟨scanner_firstOrder,scanner_firstOrder,hGFO⟩,hHFO⟩
          (by simpa only [head,hsplit,Bool.false_eq_true,ite_false] using leaf_rule plans tails j tails[j] hj')
          (by simpa only [single,hsplit,Bool.false_eq_true,ite_false] using unary_rule plans tails j tails[j] hj') hp harg
        intro k hkm w q hq
        exact hprev k hkm tails[j].2 [w] q hq
      | true =>
        simp only [ite_true]
        cases m with
        | zero =>
          exact FragmentConsumingEntry.zero _ _ x (plans.length+j) (2*j+2) (2*j+3) p E E G G' H H'
            (render (tails.map Prod.fst) tails.length plans true false tails[j].2) (by simpa only [head,hsplit,ite_true] using leaf_rule plans tails j tails[j] hj')
            (compare_rule plans tails) (tail_compare_rule plans tails) harg
        | succ k =>
          apply FragmentConsumingEntry.transfer _ _ (target_firstOrder plans tails) x k k
            (plans.length+j) (2*j+2) (2*j+3) p E E G G' H H'
            (render (tails.map Prod.fst) tails.length plans true false tails[j].2) (render (tails.map Prod.fst) tails.length plans false false tails[j].2)
            hH' (render_firstOrder (tails.map Prod.fst) tails.length plans false false tails[j].2) hp (by simpa only [head,hsplit,ite_true] using leaf_rule plans tails j tails[j] hj')
            (compare_rule plans tails) (tail_compare_rule plans tails)
            (by simpa only [triple,hsplit,ite_true] using ternary_rule plans tails j tails[j] hj') (by simpa only [single,hsplit,ite_true] using unary_rule plans tails j tails[j] hj') hG hH
          intro w q hq; exact hprev k rfl tails[j].2 [w] q hq
    have hplans : evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E
        (P.exp (fun j => .call (plans.length+j) [argument G H])) p=
        evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E
          (P.exp (fun j => entry (tails.map Prod.fst) tails.length j G' H')) p := by
      rw [Plan.exp_eval,Plan.exp_eval]
      exact Plan.eval_congr P hleaves
    exact ArgumentGuard.look_sequence_congr _ _ x .callByValuePar .callByValueSeq _ _ E E
      _ _ _ _ p harg hplans

theorem guarded_call_eq (plans : List Plan) (tails : List Part) (hValid : Valid plans tails)
    (x : List Char) (m i p : Nat) (E : List (List Char))
    (before before' after after' G G' H H' : MExp) (hH' : FragmentConsumingSyntax.Syntax H') (hp : p≤x.length)
    (hGFO : G.FirstOrder) (hHFO : H.FirstOrder)
    (hG : ∀ q, q≤x.length → evV (source plans tails) x .callByValuePar
        (tblV (source plans tails) x .callByValuePar m) E G q=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E G' q)
    (hH : ∀ q, q≤x.length → evV (source plans tails) x .callByValuePar
        (tblV (source plans tails) x .callByValuePar m) E H q=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E H' q)
    (hbefore : evV (source plans tails) x .callByValuePar
        (tblV (source plans tails) x .callByValuePar m) E before p=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E before' p)
    (hafter : ∀ q, q≤x.length → evV (source plans tails) x .callByValuePar
        (tblV (source plans tails) x .callByValuePar m) E after q=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E after' q)
    (hprev : ∀ k, m=k+1 → ∀ e E p, p≤x.length →
      evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar k) E (render (tails.map Prod.fst) tails.length plans true false e) p=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq k) E (render (tails.map Prod.fst) tails.length plans false false e) p) :
    evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E (guardedCall (tails.map Prod.fst) tails.length plans true i before G H after) p=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E (guardedCall (tails.map Prod.fst) tails.length plans false i before' G' H' after') p := by
  cases hr : plans[i]? with
  | none => simp only [guardedCall,hr]; rfl
  | some P =>
    simp only [guardedCall,hr,Bool.false_eq_true,ite_false,ite_true]
    rw [ArgumentGuard.window_call_eq _ x _ E i p _ (argument G H) before after
      (source_rule plans tails i P hr)]
    apply ArgumentGuard.look_sequence_congr _ _ x .callByValuePar .callByValueSeq _ _ E E
      before before' _ _ p hbefore
    apply ArgumentGuard.look_sequence_congr _ _ x .callByValuePar .callByValueSeq _ _ E E
      (.seq (argument G H) after) (.seq (argument G' H') after') _ _ p
    · have harg := FragmentConsumingEntry.argument_congr _ _ x .callByValuePar .callByValueSeq _ _
        (tblV_ok _ _ _ m) E E G G' H H' hG hH p hp
      cases hv : evV (source plans tails) x .callByValuePar
          (tblV (source plans tails) x .callByValuePar m) E (argument G H) p with
      | none => rw [evV_seq_none hv,evV_seq_none (harg.symm.trans hv)]
      | some r => cases r with
        | none => rw [evV_seq_fail hv,evV_seq_fail (harg.symm.trans hv)]
        | some q =>
          rw [evV_seq_ok hv,evV_seq_ok (harg.symm.trans hv)]
          exact hafter q (evV_ok (tblV_ok _ _ _ m) _ p hp q hv)
    · have hc := call_eq plans tails hValid x m i p E G G' H H' hH' hp hGFO hHFO hG hH hprev
      simpa only [call,hr,ite_true] using hc

private theorem render_seq (kinds : List Bool) (n : Nat) (plans : List Plan) (par f : Bool) (a b : MExp) :
    render kinds n plans par f (.seq a b)=.seq (render kinds n plans par f a) (render kinds n plans par f b) := by
  cases f <;> rfl

private theorem render_alt (kinds : List Bool) (n : Nat) (plans : List Plan) (par f : Bool) (a b : MExp) :
    render kinds n plans par f (.alt a b)=.alt (render kinds n plans par f a) (render kinds n plans par f b) := by
  cases f <;> rfl

private theorem render_star (kinds : List Bool) (n : Nat) (plans : List Plan) (par f : Bool) (a : MExp) :
    render kinds n plans par f (.star a)=.star (render kinds n plans par f a) := by
  cases f <;> rfl

private theorem render_notP (kinds : List Bool) (n : Nat) (plans : List Plan) (par f : Bool) (a : MExp) :
    render kinds n plans par f (.notP a)=.notP (render kinds n plans par false a) := by
  cases f <;> rfl
/-- Current-clock structural induction handles normal expressions and
consuming fragments together, switching to normal mode inside tests.
Previous-clock induction handles the actual callee continuation. -/
theorem evaluator_of_previous (plans : List Plan) (tails : List Part) (hValid : Valid plans tails) (x : List Char) (m : Nat)
    (hprev : ∀ k, m=k+1 → ∀ e E p, p≤x.length →
      evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar k) E (render (tails.map Prod.fst) tails.length plans true false e) p=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq k) E (render (tails.map Prod.fst) tails.length plans false false e) p) :
    ∀ f e E p, p≤x.length →
      evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E (render (tails.map Prod.fst) tails.length plans true f e) p=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E (render (tails.map Prod.fst) tails.length plans false f e) p
  | false,.call i [], E, p, hp => call_eq plans tails hValid x m i p E .eps .eps .eps .eps .eps hp True.intro True.intro
      (by intro q hq; rfl) (by intro q hq; rfl) hprev
  | false,.call i [G], E, p, hp => by
      simp only [render]
      split
      · rename_i helig
        exact direct_call_eq plans tails hValid x m i p E _ _
          (render_firstOrder _ _ _ true false G) hp helig
          (evaluator_of_previous plans tails hValid x m hprev false G E p hp) hprev
      · exact call_eq plans tails hValid x m i p E _ _ .eps .eps .eps hp (render_firstOrder _ _ _ true false G) True.intro
          (fun q hq => evaluator_of_previous plans tails hValid x m hprev false G E q hq) (by intro q hq; rfl) hprev
  | false,.call i [G,H], E, p, hp => call_eq plans tails hValid x m i p E _ _ _ _ (render_fragment_syntax (tails.map Prod.fst) tails.length plans false H) hp
      (render_firstOrder _ _ _ true false G) (render_firstOrder _ _ _ true true H)
      (fun q hq => evaluator_of_previous plans tails hValid x m hprev false G E q hq)
      (fun q hq => evaluator_of_previous plans tails hValid x m hprev true H E q hq) hprev
  | false,.call i [before,G,H,after], E, p, hp => guarded_call_eq plans tails hValid x m i p E _ _ _ _ _ _ _ _
      (render_fragment_syntax (tails.map Prod.fst) tails.length plans false H) hp
      (render_firstOrder _ _ _ true false G) (render_firstOrder _ _ _ true true H)
      (fun q hq => evaluator_of_previous plans tails hValid x m hprev false G E q hq)
      (fun q hq => evaluator_of_previous plans tails hValid x m hprev true H E q hq)
      (evaluator_of_previous plans tails hValid x m hprev false before E p hp)
      (fun q hq => evaluator_of_previous plans tails hValid x m hprev false after E q hq) hprev
  | f,.seq a b, E, p, hp => by
    have hh := evaluator_of_previous plans tails hValid x m hprev f a E p hp
    simp only [render_seq]
    cases hv : evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E (render (tails.map Prod.fst) tails.length plans true f a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_previous plans tails hValid x m hprev f b E q (evV_ok (tblV_ok _ _ _ m) _ p hp q hv)
  | f,.alt a b, E, p, hp => by
    have hh := evaluator_of_previous plans tails hValid x m hprev f a E p hp
    simp only [render_alt]
    cases hv : evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E (render (tails.map Prod.fst) tails.length plans true f a) p with
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
  | false,.call _ [_,_,_], _, _, _ | false,.call _ (_::_::_::_::_::_), _, _, _ => rfl
  | f,.dbg _, _, _, _ | f,.lam _ _, _, _, _ | f,.callParam _ _, _, _, _
  | f,.invoke _ _ _, _, _, _ => by cases f <;> rfl

theorem evaluator_eq (plans : List Plan) (tails : List Part) (hValid : Valid plans tails) (x : List Char) (m : Nat)
    (f : Bool) (e : MExp) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar m) E (render (tails.map Prod.fst) tails.length plans true f e) p=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq m) E (render (tails.map Prod.fst) tails.length plans false f e) p := by
  induction m generalizing f e E p with
  | zero => exact evaluator_of_previous plans tails hValid x 0 (by intro k hk; omega) f e E p hp
  | succ m ih =>
    apply evaluator_of_previous plans tails hValid x (m+1) _ f e E p hp
    intro k hk e E p hp
    have he : k=m := by omega
    subst k
    exact ih false e E p hp

theorem stable_eq (plans : List Plan) (tails : List Part) (hValid : Valid plans tails) (x : List Char) (e : MExp) :
    evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar (iterBoundV (source plans tails) x))
      [] (render (tails.map Prod.fst) tails.length plans true false e) x.length=
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq (iterBoundV (target plans tails) x))
      [] (render (tails.map Prod.fst) tails.length plans false false e) x.length := by
  have hdefined (v : Option Nat) :
      evV (source plans tails) x .callByValuePar (tblV (source plans tails) x .callByValuePar (iterBoundV (source plans tails) x))
        [] (render (tails.map Prod.fst) tails.length plans true false e) x.length=some v ↔
      evV (target plans tails) x .callByValueSeq (tblV (target plans tails) x .callByValueSeq (iterBoundV (target plans tails) x))
        [] (render (tails.map Prod.fst) tails.length plans false false e) x.length=some v := by
    rw [←tblV_stable (source plans tails) x .callByValuePar (Nat.le_refl _),
      ←tblV_stable (target plans tails) x .callByValueSeq (Nat.le_refl _)]
    exact exists_congr (fun m => by rw [evaluator_eq plans tails hValid x m false e [] x.length (Nat.le_refl _)])
  cases hs : evV (source plans tails) x .callByValuePar
      (tblV (source plans tails) x .callByValuePar (iterBoundV (source plans tails) x)) [] (render (tails.map Prod.fst) tails.length plans true false e) x.length with
  | none =>
    cases ht : evV (target plans tails) x .callByValueSeq
        (tblV (target plans tails) x .callByValueSeq (iterBoundV (target plans tails) x)) [] (render (tails.map Prod.fst) tails.length plans false false e) x.length with
    | none => rfl
    | some v => have hh := (hdefined v).mpr ht; rw [hs] at hh; cases hh
  | some v => exact ((hdefined v).mp hs).symm

/-- One fixed recursive Seq grammar preserves all finite observations on
unchanged strings, including failures and absence of finite observations. -/
theorem observations_iff (plans : List Plan) (tails : List Part) (hValid : Valid plans tails) (e : MExp) (x : List Char) (r : Option (List Char)) :
    SObs (source plans tails) .callByValuePar (render (tails.map Prod.fst) tails.length plans true false e) x r ↔
      SObs (target plans tails) .callByValueSeq (render (tails.map Prod.fst) tails.length plans false false e) x r := by
  rw [←decideObsV_iff (source_firstOrder plans tails) (by decide) (render_firstOrder (tails.map Prod.fst) tails.length plans true false e),
    ←decideObsV_iff (target_firstOrder plans tails) (by decide) (render_firstOrder (tails.map Prod.fst) tails.length plans false false e)]
  unfold decideObsV
  rw [stable_eq plans tails hValid]

theorem language_translation (plans : List Plan) (tails : List Part) (hValid : Valid plans tails) (e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (source plans tails) .callByValuePar (render (tails.map Prod.fst) tails.length plans true false e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target plans tails,render (tails.map Prod.fst) tails.length plans false false e,target_firstOrder plans tails,render_firstOrder (tails.map Prod.fst) tails.length plans false false e,
    fun x => observations_iff plans tails hValid e x (some [])⟩

end Shallot.MacroPeg.CBV.FragmentMixedRecursive
