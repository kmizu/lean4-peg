import MacroPeg.CBV.OriginPrefixControl

/-! One recursive compiler combines fresh captures at origin-control rules
with consuming sequence/repetition using retained Word-valued arguments. -/
namespace Shallot.MacroPeg.CBV.ConsumingPrefixControl
open ReplayControlFusion (Part)
open WordControlFusion (Plan)
open MixedControlFusion (AtOrigin origin_congr)
open WordArguments (Word value word_eval value_of_success)
open ReplayFallbackFusion (closed_env)
abbrev Closed := ReplayFallbackFusion.Closed
open RecursiveParserStability (Lexical Installed pick floor frozen lexical_firstOrder frozen_lexical_eval)
open ClockFreezing (Table)

/-- Existing caller-position controls embed without changing their body
expressions, using double negation for the restoring guard. -/
def originPlan : ReplayControlFusion.Plan → Plan
  | .leaf i => .leaf i
  | .alt a b => .alt (originPlan a) (originPlan b)
  | .notP a => .notP (originPlan a)
  | .guard a b => .seq (.notP (.notP (originPlan a))) (originPlan b)

theorem originPlan_atOrigin : ∀ P, AtOrigin (originPlan P)
  | .leaf i => .leaf i
  | .alt a b => .alt (originPlan_atOrigin a) (originPlan_atOrigin b)
  | .notP a => .notP (originPlan_atOrigin a)
  | .guard a b => .guard (originPlan_atOrigin a) (originPlan_atOrigin b)

theorem originPlan_exp (L : Nat → MExp) : ∀ P, (originPlan P).exp L = P.exp L
  | .leaf _ => rfl
  | .alt a b | .guard a b => by simp only [originPlan,Plan.exp,ReplayControlFusion.Plan.exp,originPlan_exp L a,originPlan_exp L b,MExp.andP]
  | .notP a => by simp only [originPlan,Plan.exp,ReplayControlFusion.Plan.exp,originPlan_exp L a]

structure Spec where
  head : Option MExp
  plan : Plan

def entry (r : Spec) : MExp := r.head.getD (.param 0)

def Heads (bodies : List MExp) (specs : List Spec) : Prop :=
  ∀ r ∈ specs, ∀ a, r.head = some a → Lexical bodies.length a

def Supported (specs : List Spec) : MExp → Prop
  | .call _ [] => True
  | .call i [a] => Supported specs a ∧ ∀ r, specs[i]? = some r → r.head = none → Word a ∨ AtOrigin r.plan
  | .call _ (_::_::_) => False
  | .seq a b | .alt a b => Supported specs a ∧ Supported specs b
  | .star a | .notP a => Supported specs a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True
  | _ => False

structure Valid (bodies : List MExp) (parts : List Part) (specs : List Spec) : Prop where
  helpers : RecursiveParserStability.Valid bodies
  heads : Heads bodies specs
  locals : ∀ r ∈ parts, r.replay = false → Closed r.body
  originHeads : ∀ r ∈ specs, ∀ a, r.head = some a → AtOrigin r.plan
  supported : ∀ r ∈ parts, Supported specs r.body

def callLeaf (bodies : List MExp) (parts : List Part) (a : MExp) (i : Nat) : MExp :=
  match parts[i]? with
  | none => MExp.failAlways
  | some r => if r.replay then .call (bodies.length+1+i) [a] else .call (bodies.length+1+i) []

def gate (bodies : List MExp) : MExp := .call bodies.length []
def enter (bodies : List MExp) (parts : List Part) (P : Plan) (a : MExp) : MExp :=
  .seq (gate bodies) (P.exp (callLeaf bodies parts a))

def invoke (bodies : List MExp) (parts : List Part) (parallel : Bool) (i : Nat) (r : Spec) (a : MExp) : MExp :=
  if parallel then .call (bodies.length+i) [a]
  else .seq (.andP a) (enter bodies parts r.plan a)

def render (bodies : List MExp) (parts : List Part) (specs : List Spec) (parallel : Bool) : MExp → MExp
  | .call i [] => match specs[i]? with
    | some r => match r.head with
      | some a => invoke bodies parts parallel i r a
      | none => MExp.failAlways
    | none => MExp.failAlways
  | .call i [a] => match specs[i]? with
    | some r => match r.head with
      | none => invoke bodies parts parallel i r (render bodies parts specs parallel a)
      | some _ => MExp.failAlways
    | none => MExp.failAlways
  | .call _ (_::_::_) => MExp.failAlways
  | .seq a b => .seq (render bodies parts specs parallel a) (render bodies parts specs parallel b)
  | .alt a b => .alt (render bodies parts specs parallel a) (render bodies parts specs parallel b)
  | .star a => .star (render bodies parts specs parallel a)
  | .notP a => .notP (render bodies parts specs parallel a)
  | .param k => .param k
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit w => .lit w
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

theorem lexical_closed (n : Nat) : ∀ a, Lexical n a → Closed a
  | .call _ [], _ => trivial
  | .seq a b, h | .alt a b, h => ⟨lexical_closed n a h.1,lexical_closed n b h.2⟩
  | .star a, h | .notP a, h => lexical_closed n a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
  | .call _ (_::_), h | .param _, h | .dbg _, h | .lam _ _, h
  | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem callLeaf_firstOrder (bodies : List MExp) (parts : List Part) (a : MExp) (ha : a.FirstOrder) (i : Nat) :
    (callLeaf bodies parts a i).FirstOrder := by
  unfold callLeaf
  cases parts[i]? with
  | none => trivial
  | some r =>
    dsimp only []
    cases r.replay <;> simp only [Bool.false_eq_true,if_false,if_true] <;> first | trivial | exact ⟨ha,True.intro⟩

theorem invoke_firstOrder (bodies : List MExp) (parts : List Part) (s : Bool) (i : Nat) (r : Spec)
    (a : MExp) (ha : a.FirstOrder) : (invoke bodies parts s i r a).FirstOrder := by
  cases s
  · exact ⟨ha,True.intro,Plan.firstOrder (callLeaf_firstOrder bodies parts a ha) r.plan⟩
  · exact ⟨ha,True.intro⟩

theorem render_firstOrder {bodies : List MExp} {parts : List Part} {specs : List Spec}
    (hf : Heads bodies specs) (s : Bool) : ∀ e, (render bodies parts specs s e).FirstOrder
  | .call i [] => by
    simp only [render]
    cases hr : specs[i]? with
    | none => trivial
    | some r =>
      dsimp only []
      cases ha : r.head with
      | none => trivial
      | some a => exact invoke_firstOrder bodies parts s i r a (lexical_firstOrder _ _ (hf r (List.mem_of_getElem? hr) a ha))
  | .call i [a] => by
    simp only [render]
    cases specs[i]? with
    | none => trivial
    | some r =>
      dsimp only []
      cases r.head with
      | none => exact invoke_firstOrder bodies parts s i r _ (render_firstOrder hf s a)
      | some _ => trivial
  | .call _ (_::_::_) => trivial
  | .seq a b | .alt a b => ⟨render_firstOrder hf s a,render_firstOrder hf s b⟩
  | .star a | .notP a => render_firstOrder hf s a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem plan_closed {L : Nat → MExp} (h : ∀ i, Closed (L i)) : ∀ P : Plan, Closed (P.exp L)
  | .leaf i => h i
  | .alt a b | .seq a b => ⟨plan_closed h a,plan_closed h b⟩
  | .notP a | .star a => plan_closed h a

theorem callLeaf_closed (bodies : List MExp) (parts : List Part) (a : MExp) (ha : Closed a) (i : Nat) :
    Closed (callLeaf bodies parts a i) := by
  unfold callLeaf
  cases parts[i]? with
  | none => trivial
  | some r =>
    dsimp only []
    cases r.replay <;> simp only [Bool.false_eq_true,if_false,if_true] <;> first | trivial | exact ⟨ha,True.intro⟩

theorem invoke_closed (bodies : List MExp) (parts : List Part) (s : Bool) (i : Nat) (r : Spec)
    (a : MExp) (ha : Closed a) : Closed (invoke bodies parts s i r a) := by
  cases s
  · exact ⟨ha,True.intro,plan_closed (callLeaf_closed bodies parts a ha) r.plan⟩
  · exact ⟨ha,True.intro⟩

theorem render_closed {bodies : List MExp} {parts : List Part} {specs : List Spec}
    (hf : Heads bodies specs) (s : Bool) : ∀ e, Closed e → Closed (render bodies parts specs s e)
  | .call i [], _ => by
    simp only [render]
    cases hr : specs[i]? with
    | none => trivial
    | some r =>
      dsimp only []
      cases ha : r.head with
      | none => trivial
      | some a => exact invoke_closed bodies parts s i r a (lexical_closed _ _ (hf r (List.mem_of_getElem? hr) a ha))
  | .call i [a], he => by
    simp only [render]
    cases specs[i]? with
    | none => trivial
    | some r =>
      dsimp only []
      cases r.head with
      | none => exact invoke_closed bodies parts s i r _ (render_closed hf s a he.1)
      | some _ => trivial
  | .call _ (_::_::_), _ => trivial
  | .seq a b, h | .alt a b, h => ⟨render_closed hf s a h.1,render_closed hf s b h.2⟩
  | .star a, h | .notP a, h => render_closed hf s a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
  | .param _, h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

def sourceLeaf (bodies : List MExp) (parts : List Part) (specs : List Spec) (r : Spec) (i : Nat) : MExp :=
  match parts[i]? with
  | none => MExp.failAlways
  | some part => if part.replay then .seq (entry r) (render bodies parts specs true part.body)
    else render bodies parts specs true part.body

def parGrammar (bodies : List MExp) (parts : List Part) (specs : List Spec) : MGrammar :=
  ⟨bodies.map (fun e => ⟨0,e⟩) ++ specs.map (fun r => ⟨1,r.plan.exp (sourceLeaf bodies parts specs r)⟩)⟩

def targetRule (bodies : List MExp) (parts : List Part) (specs : List Spec) (r : Part) : MRule :=
  ⟨if r.replay then 1 else 0,render bodies parts specs false r.body⟩

def seqGrammar (bodies : List MExp) (parts : List Part) (specs : List Spec) : MGrammar :=
  ⟨bodies.map (fun e => ⟨0,e⟩) ++ (⟨0,.eps⟩ :: parts.map (targetRule bodies parts specs))⟩
theorem par_installed (bodies : List MExp) (parts : List Part) (specs : List Spec) : Installed bodies (parGrammar bodies parts specs) := by
  intro i e hi
  have hb : i<bodies.length := List.getElem?_eq_some_iff.mp hi |>.1
  simp only [parGrammar,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hb)]
  simp [hi]

theorem seq_installed (bodies : List MExp) (parts : List Part) (specs : List Spec) : Installed bodies (seqGrammar bodies parts specs) := by
  intro i e hi
  have hb : i<bodies.length := List.getElem?_eq_some_iff.mp hi |>.1
  simp only [seqGrammar,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hb)]
  simp [hi]

theorem par_rule (bodies : List MExp) (parts : List Part) (specs : List Spec) (i : Nat) :
    ruleAtM (parGrammar bodies parts specs).rules (bodies.length+i) =
      (specs[i]?).map (fun r => ⟨1,r.plan.exp (sourceLeaf bodies parts specs r)⟩) := by
  simp [parGrammar,ruleAtM_eq_getElem?,List.getElem?_append_right]

theorem seq_rule (bodies : List MExp) (parts : List Part) (specs : List Spec) (i : Nat) :
    ruleAtM (seqGrammar bodies parts specs).rules (bodies.length+1+i) =
      (parts[i]?).map (targetRule bodies parts specs) := by
  simp only [seqGrammar,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_map]
  rw [show bodies.length+1+i-bodies.length = i+1 from by omega]
  simp

theorem entry_firstOrder {bodies : List MExp} {specs : List Spec} (hf : Heads bodies specs)
    (r : Spec) (hr : r ∈ specs) : (entry r).FirstOrder := by
  cases ha : r.head with
  | none => simp only [entry,ha,Option.getD_none]; trivial
  | some a => simpa only [entry,ha,Option.getD_some] using lexical_firstOrder _ a (hf r hr a ha)

theorem sourceLeaf_firstOrder {bodies : List MExp} {parts : List Part} {specs : List Spec}
    (hf : Heads bodies specs) (r : Spec) (hr : r ∈ specs) (i : Nat) :
    (sourceLeaf bodies parts specs r i).FirstOrder := by
  unfold sourceLeaf
  cases parts[i]? with
  | none => trivial
  | some part =>
    dsimp only []
    cases part.replay
    · exact render_firstOrder hf true part.body
    · exact ⟨entry_firstOrder hf r hr,render_firstOrder hf true part.body⟩

theorem par_firstOrder {bodies : List MExp} {parts : List Part} {specs : List Spec}
    (hf : Valid bodies parts specs) : (parGrammar bodies parts specs).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    exact lexical_firstOrder _ e (hf.helpers e he)
  · obtain ⟨r,hr',rfl⟩ := List.mem_map.mp hr
    exact Plan.firstOrder (sourceLeaf_firstOrder hf.heads r hr') r.plan

theorem seq_firstOrder {bodies : List MExp} {parts : List Part} {specs : List Spec}
    (hf : Valid bodies parts specs) : (seqGrammar bodies parts specs).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    exact lexical_firstOrder _ e (hf.helpers e he)
  · rcases List.mem_cons.mp hr with rfl | hr
    · trivial
    · obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
      exact render_firstOrder hf.heads false r.body
abbrev parTable (bodies : List MExp) (parts : List Part) (specs : List Spec) (x : List Char) (k : Nat) : Table :=
  frozen bodies (parGrammar bodies parts specs) x .callByValuePar k
abbrev seqTable (bodies : List MExp) (parts : List Part) (specs : List Spec) (x : List Char) (k : Nat) : Table :=
  frozen bodies (seqGrammar bodies parts specs) x .callByValueSeq k

def Ready (bodies : List MExp) (parts : List Part) (specs : List Spec) (x : List Char) (T : Table)
    (r : Spec) (w : List Char) (p : Nat) : Prop := match r.head with
  | none => True
  | some a => ∃ q, q ≤ x.length ∧ w = pre x p q ∧
      evV (parGrammar bodies parts specs) x .callByValuePar T [] a p = some (some q)

def Shifted (bodies : List MExp) (parts : List Part) (specs : List Spec) (x : List Char) (T U : Table) : Prop :=
  ∀ i r, specs[i]? = some r → ∀ w p, p ≤ x.length → Ready bodies parts specs x T r w p →
    valAt (T (bodies.length+i) [w]) p =
      evV (seqGrammar bodies parts specs) x .callByValueSeq U [] (enter bodies parts r.plan (.lit w)) p

theorem gate_rule (bodies : List MExp) (parts : List Part) (specs : List Spec) :
    ruleAtM (seqGrammar bodies parts specs).rules bodies.length = some ⟨0,.eps⟩ := by
  simp only [seqGrammar,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp)]
  simp

def GateOK (bodies : List MExp) (x : List Char) (U : Table) : Prop :=
  ∀ p, p ≤ x.length → ∀ q, valAt (U bodies.length []) p = some (some q) → q=p

theorem frozen_gate_ok (bodies : List MExp) (parts : List Part) (specs : List Spec)
    (x : List Char) (k : Nat) : GateOK bodies x (seqTable bodies parts specs x k) := by
  intro p hp q hq
  cases k with
  | zero =>
    have hu : pick bodies bodies.length = false := by simp [pick]
    simp only [seqTable,frozen,ClockFreezing.frozen,hu,Bool.false_eq_true,if_false,valAt_nil] at hq
    cases hq
  | succ k =>
    have hu : pick bodies bodies.length = false := by simp [pick]
    change valAt (ClockFreezing.frozen (seqGrammar bodies parts specs) x .callByValueSeq
      (pick bodies) (floor bodies x) (k+1) bodies.length []) p = _ at hq
    rw [ClockFreezing.frozen_user_step _ _ _ _ _ k _ hu _ (gate_rule bodies parts specs) [] p hp] at hq
    simpa only [evV,Option.some.injEq] using hq.symm

theorem render_word (bodies : List MExp) (parts : List Part) (specs : List Spec) (s : Bool) :
    ∀ a, Word a → render bodies parts specs s a = a
  | .lit _, _ | .param _, _ => rfl
  | .seq a b, h => by simp only [render,render_word bodies parts specs s a h.1,render_word bodies parts specs s b h.2]
  | .eps, h | .any, h | .chr _, h | .range _ _, h | .call _ _, h | .alt _ _, h | .star _, h
  | .notP _, h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem origin_eval_congr (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Table) (E F : List (List Char)) (L R : Nat → MExp) (p : Nat)
    (he : ∀ i, evV g x s T E (L i) p = evV h x t U F (R i) p) :
    ∀ P, AtOrigin P → evV g x s T E (P.exp L) p = evV h x t U F (P.exp R) p := by
  intro P ho
  induction ho with
  | leaf i => exact he i
  | alt ha hb ia ib => simp only [Plan.exp,evV,ia,ib]
  | notP ha ia => simp only [Plan.exp,evV,ia]
  | @guard a b ha hb ia ib =>
    change (match evV g x s T E (.andP (a.exp L)) p with
      | some (some q) => evV g x s T E (b.exp L) q | other => other) =
      (match evV h x t U F (.andP (a.exp R)) p with
      | some (some q) => evV h x t U F (b.exp R) q | other => other)
    rw [CallLookahead.evV_peek,CallLookahead.evV_peek,ia]
    cases hv : evV h x t U F (a.exp R) p with
    | none => rfl
    | some r => cases r with
      | none => rfl
      | some q => exact ib
theorem callLeaf_congr (bodies : List MExp) (parts : List Part) (specs : List Spec) (x : List Char)
    (U : Nat → List (List Char) → Val) (E F : List (List Char)) (a b : MExp) (p : Nat)
    (ha : evV (seqGrammar bodies parts specs) x .callByValueSeq U E a p =
      evV (seqGrammar bodies parts specs) x .callByValueSeq U F b p) (i : Nat) :
    evV (seqGrammar bodies parts specs) x .callByValueSeq U E (callLeaf bodies parts a i) p =
      evV (seqGrammar bodies parts specs) x .callByValueSeq U F (callLeaf bodies parts b i) p := by
  unfold callLeaf
  cases hr : parts[i]? with
  | none => simp [MExp.failAlways,evV]
  | some r =>
    have hh : ruleAtM (seqGrammar bodies parts specs).rules (bodies.length+1+i) = some (targetRule bodies parts specs r) := by
      rw [seq_rule,hr]; rfl
    dsimp only []
    cases hb : r.replay
    · simp only [Bool.false_eq_true,if_false]
      rw [evV_call_seq hh (by simp [targetRule,hb]),evV_call_seq hh (by simp [targetRule,hb])]
      rfl
    · simp only [if_true]
      rw [evV_call_seq hh (by simp [targetRule,hb]),evV_call_seq hh (by simp [targetRule,hb])]
      simp only [evSeqArgs]
      rw [ha]

theorem enter_origin (bodies : List MExp) (parts : List Part) (specs : List Spec) (x : List Char)
    (U : Nat → List (List Char) → Val) (hG : GateOK bodies x U)
    (E : List (List Char)) (a : MExp) (w : List Char) (P : Plan) (hP : AtOrigin P)
    (p : Nat) (hp : p ≤ x.length)
    (ha : evV (seqGrammar bodies parts specs) x .callByValueSeq U E a p =
      evV (seqGrammar bodies parts specs) x .callByValueSeq U [] (.lit w) p) :
    evV (seqGrammar bodies parts specs) x .callByValueSeq U E (enter bodies parts P a) p =
      evV (seqGrammar bodies parts specs) x .callByValueSeq U [] (enter bodies parts P (.lit w)) p := by
  have hg (E : List (List Char)) : evV (seqGrammar bodies parts specs) x .callByValueSeq U E (gate bodies) p = valAt (U bodies.length []) p := by
    rw [gate,evV_call_seq (gate_rule bodies parts specs) rfl]
    rfl
  unfold enter
  change (match evV (seqGrammar bodies parts specs) x .callByValueSeq U E (gate bodies) p with
    | some (some q) => evV (seqGrammar bodies parts specs) x .callByValueSeq U E (P.exp (callLeaf bodies parts a)) q
    | other => other) = (match evV (seqGrammar bodies parts specs) x .callByValueSeq U [] (gate bodies) p with
    | some (some q) => evV (seqGrammar bodies parts specs) x .callByValueSeq U [] (P.exp (callLeaf bodies parts (.lit w))) q
    | other => other)
  rw [hg E,hg []]
  cases hh : valAt (U bodies.length []) p with
  | none => rfl
  | some r => cases r with
    | none => rfl
    | some q =>
      have hq := hG p hp q hh
      subst q
      exact origin_congr _ _ _ _ _ _ _ _ p (callLeaf_congr bodies parts specs x U E [] a (.lit w) p ha) P hP

theorem callLeaf_word (bodies : List MExp) (parts : List Part) (specs : List Spec) (x : List Char)
    (U : Nat → List (List Char) → Val) (E : List (List Char)) (a : MExp) (w : List Char)
    (ha : Word a) (hv : value E a = some w) (i p : Nat) :
    evV (seqGrammar bodies parts specs) x .callByValueSeq U E (callLeaf bodies parts a i) p =
      evV (seqGrammar bodies parts specs) x .callByValueSeq U [] (callLeaf bodies parts (.lit w) i) p := by
  apply callLeaf_congr
  rw [word_eval _ _ _ _ E a ha p,hv]
  rfl

theorem enter_word (bodies : List MExp) (parts : List Part) (specs : List Spec) (x : List Char)
    (U : Nat → List (List Char) → Val) (hU : OkTV x.length U)
    (E : List (List Char)) (a : MExp) (w : List Char) (ha : Word a) (hv : value E a = some w)
    (P : Plan) (p : Nat) :
    evV (seqGrammar bodies parts specs) x .callByValueSeq U E (enter bodies parts P a) p =
      evV (seqGrammar bodies parts specs) x .callByValueSeq U [] (enter bodies parts P (.lit w)) p := by
  unfold enter
  change (match evV (seqGrammar bodies parts specs) x .callByValueSeq U E (gate bodies) p with
    | some (some q) => evV (seqGrammar bodies parts specs) x .callByValueSeq U E (P.exp (callLeaf bodies parts a)) q
    | other => other) = _
  have hg (E : List (List Char)) : evV (seqGrammar bodies parts specs) x .callByValueSeq U E (gate bodies) p = valAt (U bodies.length []) p := by
    rw [gate,evV_call_seq (gate_rule bodies parts specs) rfl]
    rfl
  change _ = match evV (seqGrammar bodies parts specs) x .callByValueSeq U [] (gate bodies) p with
    | some (some q) => evV (seqGrammar bodies parts specs) x .callByValueSeq U [] (P.exp (callLeaf bodies parts (.lit w))) q
    | other => other
  rw [hg E,hg []]
  cases hh : valAt (U bodies.length []) p with
  | none => rfl
  | some r => cases r with
    | none => rfl
    | some q =>
      exact Plan.eval_congr _ _ _ _ _ _ _ _ _ _ _ hU
        (fun i p _ => callLeaf_word bodies parts specs x U E a w ha hv i p) P q (hU bodies.length [] p q hh)


theorem call_eval {bodies : List MExp} {parts : List Part} {specs : List Spec} (x : List Char)
    (T U : Table) (hShift : Shifted bodies parts specs x T U) (i : Nat) (r : Spec) (hr : specs[i]? = some r)
    (E : List (List Char)) (a b : MExp) (p : Nat) (hp : p ≤ x.length)
    (hEq : evV (parGrammar bodies parts specs) x .callByValuePar T E a p =
      evV (seqGrammar bodies parts specs) x .callByValueSeq U E b p)
    (hReady : ∀ q, evV (parGrammar bodies parts specs) x .callByValuePar T E a p = some (some q) →
      Ready bodies parts specs x T r (pre x p q) p)
    (hCont : ∀ q, evV (parGrammar bodies parts specs) x .callByValuePar T E a p = some (some q) →
      evV (seqGrammar bodies parts specs) x .callByValueSeq U E (enter bodies parts r.plan b) p =
        evV (seqGrammar bodies parts specs) x .callByValueSeq U [] (enter bodies parts r.plan (.lit (pre x p q))) p) :
    evV (parGrammar bodies parts specs) x .callByValuePar T E (.call (bodies.length+i) [a]) p =
      evV (seqGrammar bodies parts specs) x .callByValueSeq U E
        (.seq (.andP b) (enter bodies parts r.plan b)) p := by
  have hpar : ruleAtM (parGrammar bodies parts specs).rules (bodies.length+i) =
      some ⟨1,r.plan.exp (sourceLeaf bodies parts specs r)⟩ := by rw [par_rule,hr]; rfl
  rw [evV_call_par hpar rfl (by decide)]
  have hguard : evV (seqGrammar bodies parts specs) x .callByValueSeq U E (.andP b) p =
      CallLookahead.peek p (evV (parGrammar bodies parts specs) x .callByValuePar T E a p) := by
    rw [CallLookahead.evV_peek,← hEq]
  cases hv : evV (parGrammar bodies parts specs) x .callByValuePar T E a p with
  | none => rw [evPar_cons_none hv,evV_seq_none (hguard.trans (by rw [hv]; rfl))]
  | some result => cases result with
    | none => rw [evPar_cons_fail hv,evV_seq_fail (hguard.trans (by rw [hv]; rfl))]
    | some q =>
      rw [evPar_cons_ok hv,evV_seq_ok (hguard.trans (by rw [hv]; rfl))]
      exact (hShift i r hr _ p hp (hReady q hv)).trans (hCont q hv).symm

theorem enter_of_success {bodies : List MExp} {parts : List Part} {specs : List Spec}
    (x : List Char) (T U : Table) (hT : SoundTV (parGrammar bodies parts specs) x .callByValuePar T)
    (hG : GateOK bodies x U) (E : List (List Char)) (a b : MExp) (ha : a.FirstOrder)
    (P : Plan) (ho : AtOrigin P) (p q : Nat) (hp : p ≤ x.length)
    (hEq : evV (parGrammar bodies parts specs) x .callByValuePar T E a p =
      evV (seqGrammar bodies parts specs) x .callByValueSeq U E b p)
    (hv : evV (parGrammar bodies parts specs) x .callByValuePar T E a p = some (some q)) :
    evV (seqGrammar bodies parts specs) x .callByValueSeq U E (enter bodies parts P b) p =
      evV (seqGrammar bodies parts specs) x .callByValueSeq U [] (enter bodies parts P (.lit (pre x p q))) p := by
  obtain ⟨hq,hs⟩ := ReplayFusion.success_prefix hT E a ha p q hp hv
  have hlit : evV (seqGrammar bodies parts specs) x .callByValueSeq U [] (.lit (pre x p q)) p = some (some q) := by
    simp only [evV,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hs,length_sfx x hq]
  exact enter_origin bodies parts specs x U hG E b (pre x p q) P ho p hp ((hEq.symm.trans hv).trans hlit.symm)

theorem evaluator_of_shift {bodies : List MExp} {parts : List Part} {specs : List Spec}
    (hf : Valid bodies parts specs) (x : List Char) (T U : Table)
    (hT : SoundTV (parGrammar bodies parts specs) x .callByValuePar T)
    (hOk : OkTV x.length T) (hU : OkTV x.length U) (hG : GateOK bodies x U)
    (hLex : ∀ E F a, Lexical bodies.length a → ∀ p, p ≤ x.length →
      evV (parGrammar bodies parts specs) x .callByValuePar T E a p =
        evV (seqGrammar bodies parts specs) x .callByValueSeq U F a p)
    (hShift : Shifted bodies parts specs x T U) :
    ∀ e, Supported specs e → ∀ E p, p ≤ x.length →
      evV (parGrammar bodies parts specs) x .callByValuePar T E (render bodies parts specs true e) p =
        evV (seqGrammar bodies parts specs) x .callByValueSeq U E (render bodies parts specs false e) p
  | .call i [], _, E, p, hp => by
    cases hr : specs[i]? with
    | none => simp only [render,hr]; rfl
    | some r =>
      cases ha : r.head with
      | none => simp only [render,hr,ha]; rfl
      | some a =>
        have hA := hf.heads r (List.mem_of_getElem? hr) a ha
        have ho := hf.originHeads r (List.mem_of_getElem? hr) a ha
        simp only [render,hr,ha,invoke,if_true,Bool.false_eq_true,if_false]
        apply call_eval x T U hShift i r hr E a a p hp (hLex E E a hA p hp)
        · intro q hv
          simp only [Ready,ha]
          exact ⟨q,evV_ok hOk a p hp q hv,rfl,
            ((hLex [] E a hA p hp).trans (hLex E E a hA p hp).symm).trans hv⟩
        · intro q hv
          exact enter_of_success x T U hT hG E a a (lexical_firstOrder _ _ hA) r.plan ho p q hp (hLex E E a hA p hp) hv
  | .call i [a], he, E, p, hp => by
    cases hr : specs[i]? with
    | none => simp only [render,hr]; rfl
    | some r =>
      cases ha : r.head with
      | some _ => simp only [render,hr,ha]; rfl
      | none =>
        have hEq := evaluator_of_shift hf x T U hT hOk hU hG hLex hShift a he.1 E p hp
        simp only [render,hr,ha,invoke,if_true,Bool.false_eq_true,if_false]
        apply call_eval x T U hShift i r hr E (render bodies parts specs true a) (render bodies parts specs false a) p hp hEq
        · intro q hv
          simp only [Ready,ha]
        · intro q hv
          rcases he.2 r hr ha with hw | ho
          · have hval := value_of_success (parGrammar bodies parts specs) x .callByValuePar T E a hw p q hp
              (by simpa only [render_word bodies parts specs true a hw] using hv)
            rw [render_word bodies parts specs false a hw]
            exact enter_word bodies parts specs x U hU E a _ hw hval r.plan p
          · exact enter_of_success x T U hT hG E _ _ (render_firstOrder hf.heads true a) r.plan ho p q hp hEq hv
  | .seq a b, he, E, p, hp => by
    have hh := evaluator_of_shift hf x T U hT hOk hU hG hLex hShift a he.1 E p hp
    cases hv : evV (parGrammar bodies parts specs) x .callByValuePar T E (render bodies parts specs true a) p with
    | none => simp only [render,evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => simp only [render,evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        simp only [render,evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_shift hf x T U hT hOk hU hG hLex hShift b he.2 E q (evV_ok hOk _ p hp q hv)
  | .alt a b, he, E, p, hp => by
    have hh := evaluator_of_shift hf x T U hT hOk hU hG hLex hShift a he.1 E p hp
    cases hv : evV (parGrammar bodies parts specs) x .callByValuePar T E (render bodies parts specs true a) p with
    | none => simp only [render,evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some result => cases result with
      | none =>
        simp only [render,evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]
        exact evaluator_of_shift hf x T U hT hOk hU hG hLex hShift b he.2 E p hp
      | some q => simp only [render,evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | .star a, he, E, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift hf x T U hT hOk hU hG hLex hShift a he E q (by omega))
  | .notP a, he, E, p, hp => by simp only [render,evV]; rw [evaluator_of_shift hf x T U hT hOk hU hG hLex hShift a he E p hp]
  | .param _, _, _, _, _ | .eps, _, _, _, _ | .any, _, _, _, _ | .chr _, _, _, _, _ | .range _ _, _, _, _, _ | .lit _, _, _, _, _ => rfl
  | .call _ (_::_::_), he, _, _, _ | .dbg _, he, _, _, _ | .lam _ _, he, _, _, _
  | .callParam _ _, he, _, _, _ | .invoke _ _ _, he, _, _, _ => False.elim he
theorem lexical_eq {bodies : List MExp} {parts : List Part} {specs : List Spec}
    (hf : Valid bodies parts specs) (x : List Char) (k l : Nat) (E F : List (List Char)) (a : MExp)
    (ha : Lexical bodies.length a) (p : Nat) (hp : p ≤ x.length) :
    evV (parGrammar bodies parts specs) x .callByValuePar (parTable bodies parts specs x k) E a p =
      evV (seqGrammar bodies parts specs) x .callByValueSeq (seqTable bodies parts specs x l) F a p :=
  frozen_lexical_eval hf.helpers (par_installed bodies parts specs) (seq_installed bodies parts specs) x
    .callByValuePar .callByValueSeq k l E F a ha p hp

theorem seq_user_step (bodies : List MExp) (parts : List Part) (specs : List Spec)
    (x : List Char) (k i : Nat) (r : Part) (hr : parts[i]? = some r)
    (W : List (List Char)) (p : Nat) (hp : p ≤ x.length) :
    valAt (seqTable bodies parts specs x (k+1) (bodies.length+1+i) W) p =
      evV (seqGrammar bodies parts specs) x .callByValueSeq (seqTable bodies parts specs x k)
        W (render bodies parts specs false r.body) p := by
  have hlookup : ruleAtM (seqGrammar bodies parts specs).rules (bodies.length+1+i) =
      some (targetRule bodies parts specs r) := by rw [seq_rule,hr]; rfl
  exact ClockFreezing.frozen_user_step _ _ _ _ _ k _ (by simp [pick]; omega) _ hlookup W p hp

theorem leaf_step {bodies : List MExp} {parts : List Part} {specs : List Spec}
    (hf : Valid bodies parts specs) (x : List Char) (k : Nat)
    (hEval : ∀ e, Supported specs e → ∀ E z, z ≤ x.length →
      evV (parGrammar bodies parts specs) x .callByValuePar (parTable bodies parts specs x k) E (render bodies parts specs true e) z =
        evV (seqGrammar bodies parts specs) x .callByValueSeq (seqTable bodies parts specs x k) E (render bodies parts specs false e) z)
    (r : Spec) (w : List Char) (z : Nat) (hz : z ≤ x.length)
    (hEntry : evV (parGrammar bodies parts specs) x .callByValuePar (parTable bodies parts specs x k) [w] (entry r) z =
      evV (seqGrammar bodies parts specs) x .callByValueSeq (seqTable bodies parts specs x (k+1)) [] (.lit w) z)
    (j : Nat) :
    evV (parGrammar bodies parts specs) x .callByValuePar (parTable bodies parts specs x k) [w] (sourceLeaf bodies parts specs r j) z =
      evV (seqGrammar bodies parts specs) x .callByValueSeq (seqTable bodies parts specs x (k+1)) [] (callLeaf bodies parts (.lit w) j) z := by
  cases hj : parts[j]? with
  | none => simp [sourceLeaf,callLeaf,hj,MExp.failAlways,evV]
  | some part =>
    have hlookup : ruleAtM (seqGrammar bodies parts specs).rules (bodies.length+1+j) =
        some (targetRule bodies parts specs part) := by rw [seq_rule,hj]; rfl
    have he := hf.supported part (List.mem_of_getElem? hj)
    simp only [sourceLeaf,callLeaf,hj]
    cases hb : part.replay
    · simp only [Bool.false_eq_true,if_false]
      rw [evV_call_seq hlookup (by simp [targetRule,hb])]
      change _ = valAt (seqTable bodies parts specs x (k+1) (bodies.length+1+j) []) z
      rw [seq_user_step bodies parts specs x k j part hj [] z hz,
        closed_env _ _ _ _ (render bodies parts specs true part.body)
          (render_closed hf.heads true part.body (hf.locals part (List.mem_of_getElem? hj) hb)) [w] z]
      exact hEval part.body he [] z hz
    · simp only [if_true]
      rw [evV_call_seq hlookup (by simp [targetRule,hb])]
      cases ht : evV (seqGrammar bodies parts specs) x .callByValueSeq (seqTable bodies parts specs x (k+1)) [] (.lit w) z with
      | none => rw [evV_seq_none (hEntry.trans ht),evSeq_cons_none ht]
      | some result => cases result with
        | none => rw [evV_seq_fail (hEntry.trans ht),evSeq_cons_fail ht]
        | some q =>
          have hq := evV_ok (ClockFreezing.frozen_ok _ _ _ _ _ (k+1)) (.lit w) z hz q ht
          have hword : pre x z q = w := by
            have h := value_of_success (seqGrammar bodies parts specs) x .callByValueSeq
              (seqTable bodies parts specs x (k+1)) [] (.lit w) True.intro z q hz ht
            simpa only [value,Option.some.injEq] using h.symm
          rw [evV_seq_ok (hEntry.trans ht),evSeq_cons_ok ht]
          change _ = valAt (seqTable bodies parts specs x (k+1) (bodies.length+1+j) [pre x z q]) q
          rw [hword,seq_user_step bodies parts specs x k j part hj [w] q hq]
          exact hEval part.body he [w] q hq

theorem tables_shifted {bodies : List MExp} {parts : List Part} {specs : List Spec}
    (hf : Valid bodies parts specs) (x : List Char) (k : Nat) :
    Shifted bodies parts specs x (parTable bodies parts specs x k) (seqTable bodies parts specs x k) := by
  induction k with
  | zero =>
    intro i r hr w p hp hv
    have hgate : evV (seqGrammar bodies parts specs) x .callByValueSeq
        (seqTable bodies parts specs x 0) [] (gate bodies) p = none := by
      rw [gate,evV_call_seq (gate_rule bodies parts specs) rfl]
      have hu : pick bodies bodies.length = false := by simp [pick]
      simp only [evSeqArgs,seqTable,frozen,ClockFreezing.frozen,hu,Bool.false_eq_true,if_false,valAt_nil]
    rw [enter,evV_seq_none hgate]
    have hu : pick bodies (bodies.length+i) = false := by simp [pick]
    simp only [parTable,frozen,ClockFreezing.frozen,hu,Bool.false_eq_true,if_false,valAt_nil]
  | succ k ih =>
    intro i r hr w p hp hv
    have hpar : ruleAtM (parGrammar bodies parts specs).rules (bodies.length+i) =
        some ⟨1,r.plan.exp (sourceLeaf bodies parts specs r)⟩ := by rw [par_rule,hr]; rfl
    have hgate : evV (seqGrammar bodies parts specs) x .callByValueSeq
        (seqTable bodies parts specs x (k+1)) [] (gate bodies) p = some (some p) := by
      rw [gate,evV_call_seq (gate_rule bodies parts specs) rfl]
      change valAt (ClockFreezing.frozen (seqGrammar bodies parts specs) x .callByValueSeq
        (pick bodies) (floor bodies x) (k+1) bodies.length []) p = _
      rw [ClockFreezing.frozen_user_step _ _ _ _ _ k _ (by simp [pick]) _ (gate_rule bodies parts specs) [] p hp]
      rfl
    have hEval := evaluator_of_shift hf x _ _
      (ClockFreezing.frozen_sound (par_firstOrder hf) x .callByValuePar (by decide) _ _ k)
      (ClockFreezing.frozen_ok _ _ _ _ _ k) (ClockFreezing.frozen_ok _ _ _ _ _ k)
      (frozen_gate_ok bodies parts specs x k)
      (fun E F a ha p hp => lexical_eq hf x k k E F a ha p hp) ih
    change valAt (ClockFreezing.frozen (parGrammar bodies parts specs) x .callByValuePar
      (pick bodies) (floor bodies x) (k+1) (bodies.length+i) [w]) p = _
    rw [ClockFreezing.frozen_user_step _ _ _ _ _ k _ (by simp [pick]) _ hpar [w] p hp,enter,evV_seq_ok hgate]
    cases ha : r.head with
    | none =>
      apply Plan.eval_congr _ _ _ _ _ _ _ _ _ _ _ (ClockFreezing.frozen_ok _ _ _ _ _ k) _ r.plan p hp
      intro j z hz
      apply leaf_step hf x k hEval r w z hz _ j
      simp only [entry,ha,Option.getD_none,evV,List.getElem?_cons_zero]
    | some a =>
      obtain ⟨q,hq,hw,hv⟩ := (show ∃ q, q ≤ x.length ∧ w=pre x p q ∧ _ from (by simpa only [Ready,ha] using hv))
      have hA := hf.heads r (List.mem_of_getElem? hr) a ha
      have hentry : evV (parGrammar bodies parts specs) x .callByValuePar
          (parTable bodies parts specs x k) [w] (entry r) p = some (some q) := by
        simp only [entry,ha,Option.getD_some]
        rw [frozen_lexical_eval hf.helpers (par_installed bodies parts specs) (par_installed bodies parts specs) x
          .callByValuePar .callByValuePar k (k+1) [w] [] a hA p hp]
        exact hv
      have hs := (ReplayFusion.success_prefix
        (ClockFreezing.frozen_sound (par_firstOrder hf) x .callByValuePar (by decide) _ _ (k+1))
        [] a (lexical_firstOrder _ _ hA) p q hp hv).2
      have hlit : evV (seqGrammar bodies parts specs) x .callByValueSeq
          (seqTable bodies parts specs x (k+1)) [] (.lit w) p = some (some q) := by
        simp only [hw,evV,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hs,length_sfx x hq]
      exact origin_eval_congr _ _ _ _ _ _ _ _ _ _ _ p
        (fun j => leaf_step hf x k hEval r w p hp (hentry.trans hlit.symm) j)
        r.plan (hf.originHeads r (List.mem_of_getElem? hr) a ha)

theorem evaluator_eq {bodies : List MExp} {parts : List Part} {specs : List Spec}
    (hf : Valid bodies parts specs) (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp)
    (he : Supported specs e) (p : Nat) (hp : p ≤ x.length) :
    evV (parGrammar bodies parts specs) x .callByValuePar (parTable bodies parts specs x k) E (render bodies parts specs true e) p =
      evV (seqGrammar bodies parts specs) x .callByValueSeq (seqTable bodies parts specs x k) E (render bodies parts specs false e) p :=
  evaluator_of_shift hf x _ _
    (ClockFreezing.frozen_sound (par_firstOrder hf) x .callByValuePar (by decide) _ _ k)
    (ClockFreezing.frozen_ok _ _ _ _ _ k) (ClockFreezing.frozen_ok _ _ _ _ _ k)
    (frozen_gate_ok bodies parts specs x k)
    (fun E F a ha p hp => lexical_eq hf x k k E F a ha p hp) (tables_shifted hf x k) e he E p hp
theorem observations_iff {bodies : List MExp} {parts : List Part} {specs : List Spec}
    (hf : Valid bodies parts specs) (e : MExp) (he : Supported specs e) (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar bodies parts specs) .callByValuePar (render bodies parts specs true e) x r ↔
      SObs (seqGrammar bodies parts specs) .callByValueSeq (render bodies parts specs false e) x r := by
  rw [ClockFreezing.observations_iff (par_firstOrder hf) x .callByValuePar (by decide)
      (pick bodies) (floor bodies x) (RecursiveParserStability.helpers_stable hf.helpers (par_installed bodies parts specs) x .callByValuePar)
      (render bodies parts specs true e) (render_firstOrder hf.heads true e) r,
    ClockFreezing.observations_iff (seq_firstOrder hf) x .callByValueSeq (by decide)
      (pick bodies) (floor bodies x) (RecursiveParserStability.helpers_stable hf.helpers (seq_installed bodies parts specs) x .callByValueSeq)
      (render bodies parts specs false e) (render_firstOrder hf.heads false e) r]
  constructor
  · rintro ⟨k,v,hv,hr⟩
    exact ⟨k,v,(evaluator_eq hf x k [] e he x.length (Nat.le_refl _)).symm.trans hv,hr⟩
  · rintro ⟨k,v,hv,hr⟩
    exact ⟨k,v,(evaluator_eq hf x k [] e he x.length (Nat.le_refl _)).trans hv,hr⟩

theorem language_translation {bodies : List MExp} {parts : List Part} {specs : List Spec}
    (hf : Valid bodies parts specs) (e : MExp) (he : Supported specs e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (parGrammar bodies parts specs) .callByValuePar (render bodies parts specs true e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar bodies parts specs,render bodies parts specs false e,seq_firstOrder hf,render_firstOrder hf.heads false e,
    fun x => observations_iff hf e he x (some [])⟩
def exampleParts : List Part := [
  ⟨true,.seq (.chr '#') (.call 1 [.param 0])⟩,
  ⟨false,.seq (NestedScannerArguments.scan ['a','b']) (.chr '!')⟩,
  ⟨true,.chr ';'⟩,
  ⟨false,.seq (.chr '?') (.call 0 [])⟩,
  ⟨false,.notP .any⟩]

def exampleSpecs : List Spec := [
  ⟨some (.call 0 []),.leaf 0⟩,
  ⟨none,.seq (.leaf 1) (.seq (.star (.leaf 2)) (.alt (.leaf 3) (.leaf 4)))⟩]

theorem example_valid : Valid [RecursivePrefixFusion.balancedBody] exampleParts exampleSpecs := by
  constructor
  · exact RecursivePrefixFusion.balanced_valid.1
  · intro r hr a ha
    simp only [exampleSpecs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · cases ha
      simp [Lexical]
    · cases ha
  · intro r hr hb
    simp only [exampleParts,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp_all [Closed,ReplayFallbackFusion.Closed,ReplayFallbackFusion.ClosedArgs,
        NestedScannerArguments.scan,NestedScannerArguments.choice,MExp.failAlways]
  · intro r hr a ha
    simp only [exampleSpecs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact AtOrigin.leaf 0
    · cases ha
  · intro r hr
    simp only [exampleParts,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [Supported,NestedScannerArguments.scan,NestedScannerArguments.choice,MExp.failAlways]
    intro r hr ha
    simp only [exampleSpecs,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at hr
    subst r
    exact Or.inl True.intro

/-- A fresh balanced capture enters consuming control: a local prefix is
consumed before a loop replays the retained word repeatedly. It can then
recursively obtain a different fresh word and repeat the same process. -/
theorem fresh_capture_consuming_execution :
    let bodies := [RecursivePrefixFusion.balancedBody]
    let ep := render bodies exampleParts exampleSpecs true (.call 0 [])
    let es := render bodies exampleParts exampleSpecs false (.call 0 [])
    let good := "ab#ab!ab;ab;?aabb#aabb!aabb;".toList
    let bad := "ab#ab!ab;ab;?aabb#aabb!ab;".toList
    (evV (parGrammar bodies exampleParts exampleSpecs) good .callByValuePar
      (tblV (parGrammar bodies exampleParts exampleSpecs) good .callByValuePar 8) [] ep good.length = some (some 0)) ∧
    (evV (seqGrammar bodies exampleParts exampleSpecs) good .callByValueSeq
      (tblV (seqGrammar bodies exampleParts exampleSpecs) good .callByValueSeq 8) [] es good.length = some (some 0)) ∧
    (evV (parGrammar bodies exampleParts exampleSpecs) bad .callByValuePar
      (tblV (parGrammar bodies exampleParts exampleSpecs) bad .callByValuePar 8) [] ep bad.length = some none) ∧
    (evV (seqGrammar bodies exampleParts exampleSpecs) bad .callByValueSeq
      (tblV (seqGrammar bodies exampleParts exampleSpecs) bad .callByValueSeq 8) [] es bad.length = some none) := by
  decide +kernel

end Shallot.MacroPeg.CBV.ConsumingPrefixControl
