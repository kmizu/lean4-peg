import MacroPeg.CBV.SelectedPrefixGrammar
import MacroPeg.CBV.HelperArgument

/-! Translate runtime prefix-code captures with an installed independent
recursive PEG component. The header may call any helper; argument parsers
may also inspect and consume retained parameters through duplicated views;
successful arguments consist of two header codewords. Actual finite helper
rows and prefix-failure seeds synchronize user calls, and cofinality removes
both from the final ordinary-grammar observation theorem. -/
namespace Shallot.MacroPeg.CBV.RecursiveCodeGrammar
open ClockFreezing (Table)
open PrefixCodeCapture (PrefixFree duplicate view)

open RecursiveParserStability (Lexical Installed pick floor)

def canonical (bodies : List MExp) (x : List Char) : Table :=
  tblV (RecursiveParserStability.grammar bodies) x .callByValuePar (floor bodies x)

structure Header where
  bodies : List MExp
  valid : RecursiveParserStability.Valid bodies
  head : MExp
  lexical : Lexical bodies.length head
  code : List Char → Prop
  prefixFree : PrefixFree code
  captured : ∀ (x : List Char) (p q : Nat), p≤x.length →
    evV (RecursiveParserStability.grammar bodies) x .callByValuePar (canonical bodies x) [] head p=some (some q) →
    code (pre x p q)

structure User (H : Header) where
  arg : MExp
  allowed : HelperArgument.Syntax H.bodies.length arg
  captured : ∀ (x : List Char) (E : List (List Char)) (p q : Nat), p≤x.length →
    evV (RecursiveParserStability.grammar H.bodies) x .callByValuePar (canonical H.bodies x) E arg p=some (some q) →
    ∃ u v, H.code u ∧ H.code v ∧ pre x p q=u++v
  body : MExp

def lexical (H : Header) (e : MExp) (x : List Char) (p : Nat) : Res :=
  evV (RecursiveParserStability.grammar H.bodies) x .callByValuePar (canonical H.bodies x) [] e p

def argument (H : Header) (r : User H) (x : List Char) (E : List (List Char)) (p : Nat) : Res :=
  evV (RecursiveParserStability.grammar H.bodies) x .callByValuePar (canonical H.bodies x) E r.arg p
abbrev headValue (H : Header) (x : List Char) (p : Nat) : Res := lexical H H.head x p

theorem helpers_firstOrder (H : Header) : (RecursiveParserStability.grammar H.bodies).FirstOrder := by
  intro r hr
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
  exact RecursiveParserStability.lexical_firstOrder _ e (H.valid e he)

theorem lexical_success (H : Header) (e : MExp) (he : Lexical H.bodies.length e)
    (x : List Char) (p q : Nat) (hp : p≤x.length)
    (h : lexical H e x p=some (some q)) :
    q≤x.length ∧ sfx x p=pre x p q++sfx x q :=
  ReplayFusion.success_prefix (tblV_sound (helpers_firstOrder H) (by decide) _)
    [] e (RecursiveParserStability.lexical_firstOrder _ e he) p q hp h

def LexicalTable (H : Header) (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) : Prop :=
  ∀ E e, Lexical H.bodies.length e → ∀ p, p≤x.length → evV g x s T E e p=lexical H e x p

/-- Installed helper rows are actual finite computations, independent of
user rules, environments, and the choice of CBV strategy. -/
theorem frozen_lexical (H : Header) (g : MGrammar) (hg : Installed H.bodies g)
    (x : List Char) (s : Strategy) (k : Nat) :
    LexicalTable H g x s (RecursiveParserStability.frozen H.bodies g x s k) := by
  intro E e he p hp
  apply RecursiveParserStability.lexical_eval hg (RecursiveParserStability.installed H.bodies)
    x s .callByValuePar _ _ (ClockFreezing.frozen_ok g x s _ _ k) _ E [] e he p hp
  intro i hi q hq
  rw [ClockFreezing.frozen_rows g x s _ _ k i (by simp [pick,hi]) []]
  exact congrArg (fun row => valAt row q)
    (RecursiveParserStability.helper_rows_eq H.valid hg (RecursiveParserStability.installed H.bodies)
      x s .callByValuePar (floor H.bodies x) i hi [] [])

theorem seeded_lexical (H : Header) (g : MGrammar) (hg : Installed H.bodies g)
    (x : List Char) (s : Strategy) (k : Nat) :
    LexicalTable H g x s (SeededClock.rounds H.bodies g x s k) := by
  intro E e he p hp
  apply RecursiveParserStability.lexical_eval hg (RecursiveParserStability.installed H.bodies)
    x s .callByValuePar _ _ (SeededClock.rounds_ok H.bodies g x s k) _ E [] e he p hp
  intro i hi q hq
  unfold SeededClock.rounds
  rw [SeededClock.rows g x s _ _ _ (SeededClock.prefixSeed_rows g x s _ _) k i
    (by simp [pick,hi]) []]
  exact congrArg (fun row => valAt row q)
    (RecursiveParserStability.helper_rows_eq H.valid hg (RecursiveParserStability.installed H.bodies)
      x s .callByValuePar (floor H.bodies x) i hi [] [])

/-- A retained-value-dependent argument is evaluated in its actual source
environment; only independent helper rows are frozen. -/
theorem argument_eval (H : Header) (g : MGrammar) (hg : Installed H.bodies g)
    (x : List Char) (s : Strategy) (T : Table) (hOk : OkTV x.length T)
    (hLex : LexicalTable H g x s T) (b : User H) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) : evV g x s T E b.arg p=argument H b x E p := by
  apply HelperArgument.eval_eq hg (RecursiveParserStability.installed H.bodies)
    x s .callByValuePar T _ hOk _ E b.arg b.allowed p hp
  intro i hi q hq
  have hh := hLex [] (.call i []) hi q hq
  have hs := hg i H.bodies[i] (List.getElem?_eq_getElem hi)
  have ht := RecursiveParserStability.installed H.bodies i H.bodies[i] (List.getElem?_eq_getElem hi)
  cases s <;> simpa only [lexical,evV,hs,ht,evParArgs,evSeqArgs,List.length_nil,ite_true] using hh

theorem view_firstOrder (b : MExp) (hb : b.FirstOrder) : (view b).FirstOrder := by
  exact firstOrder_subst (args:=[duplicate]) ⟨⟨True.intro,True.intro⟩,True.intro⟩ b hb

def render (H : Header) (tails : List (User H)) (par : Bool) : MExp → MExp
  | .call i [] => match tails[i]? with
    | none => MExp.failAlways
    | some r => if par then .call (H.bodies.length+i) [r.arg]
      else .seq (.andP (view r.arg)) (.call (H.bodies.length+i) [H.head])
  | .seq a b => .seq (render H tails par a) (render H tails par b)
  | .alt a b => .alt (render H tails par a) (render H tails par b)
  | .star a => .star (render H tails par a)
  | .notP a => .notP (render H tails par a)
  | .param k => if par then .param k else view (.param k)
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w
  | _ => MExp.failAlways

def source (H : Header) (tails : List (User H)) : MGrammar :=
  ⟨H.bodies.map (fun e => ⟨0,e⟩)++tails.map (fun b => ⟨1,.seq H.head (.seq (.param 0) (render H tails true b.body))⟩)⟩
def target (H : Header) (tails : List (User H)) : MGrammar :=
  ⟨H.bodies.map (fun e => ⟨0,e⟩)++tails.map (fun b => ⟨1,.seq duplicate (render H tails false b.body)⟩)⟩

theorem view_param_firstOrder (k : Nat) : (view (.param k)).FirstOrder := by
  cases k <;> simp [view,MExp.subst,argAt,duplicate,MExp.FirstOrder,MExp.failAlways]

theorem render_firstOrder (H : Header) (tails : List (User H)) (par : Bool) :
    ∀ e, (render H tails par e).FirstOrder
  | .call i [] => by
    simp only [render]
    cases tails[i]? with
    | none => trivial
    | some b =>
      cases par
      · exact ⟨view_firstOrder b.arg (HelperArgument.firstOrder _ b.arg b.allowed),RecursiveParserStability.lexical_firstOrder _ H.head H.lexical,True.intro⟩
      · exact ⟨HelperArgument.firstOrder _ b.arg b.allowed,True.intro⟩
  | .seq a b | .alt a b => ⟨render_firstOrder H tails par a,render_firstOrder H tails par b⟩
  | .star a | .notP a => render_firstOrder H tails par a
  | .param k => by cases par <;> first | exact view_param_firstOrder k | trivial
  | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .call _ (_::_) | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem source_installed (H : Header) (tails : List (User H)) : Installed H.bodies (source H tails) := by
  intro i e hi
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  simp only [source,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hb)]
  simp [hi]

theorem target_installed (H : Header) (tails : List (User H)) : Installed H.bodies (target H tails) := by
  intro i e hi
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  simp only [target,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hb)]
  simp [hi]

theorem source_firstOrder (H : Header) (tails : List (User H)) : (source H tails).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    exact RecursiveParserStability.lexical_firstOrder _ e (H.valid e he)
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨RecursiveParserStability.lexical_firstOrder _ H.head H.lexical,True.intro,render_firstOrder H tails true b.body⟩
theorem target_firstOrder (H : Header) (tails : List (User H)) : (target H tails).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    exact RecursiveParserStability.lexical_firstOrder _ e (H.valid e he)
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨⟨True.intro,True.intro⟩,render_firstOrder H tails false b.body⟩

theorem source_rule (H : Header) (tails : List (User H)) (i : Nat) :
    ruleAtM (source H tails).rules (H.bodies.length+i)=(tails[i]?).map
      (fun b => ⟨1,.seq H.head (.seq (.param 0) (render H tails true b.body))⟩) := by
  simp [source,ruleAtM_eq_getElem?,List.getElem?_append_right]
theorem target_rule (H : Header) (tails : List (User H)) (i : Nat) :
    ruleAtM (target H tails).rules (H.bodies.length+i)=(tails[i]?).map
      (fun b => ⟨1,.seq duplicate (render H tails false b.body)⟩) := by
  simp [target,ruleAtM_eq_getElem?,List.getElem?_append_right]

def Parameters (H : Header) (tails : List (User H)) (x : List Char) (T U : Table)
    (E F : List (List Char)) : Prop := ∀ k p,
  evV (source H tails) x .callByValuePar T E (.param k) p=
    evV (target H tails) x .callByValueSeq U F (view (.param k)) p

theorem parameters_empty (H : Header) (tails : List (User H)) (x : List Char) (T U : Table) :
    Parameters H tails x T U [] [] := by
  intro k p
  cases k <;> simp [view,MExp.subst,argAt,duplicate,evV,MExp.failAlways]

theorem parameters_double (H : Header) (tails : List (User H)) (x : List Char) (T U : Table)
    (u : List Char) : Parameters H tails x T U [u++u] [u] := by
  intro k p
  cases k with
  | zero =>
    change evV (source H tails) x .callByValuePar T [u++u] (.param 0) p=
      evV (target H tails) x .callByValueSeq U [u] duplicate p
    rw [WordArguments.word_eval _ x _ U [u] duplicate ⟨True.intro,True.intro⟩ p]
    rfl
  | succ k => simp [view,MExp.subst,argAt,evV,MExp.failAlways]

abbrev sourceTable (H : Header) (tails : List (User H)) (x : List Char) (k : Nat) : Table :=
  SeededClock.rounds H.bodies (source H tails) x .callByValuePar k

abbrev targetTable (H : Header) (tails : List (User H)) (x : List Char) (k : Nat) : Table :=
  RecursiveParserStability.frozen H.bodies (target H tails) x .callByValueSeq k

def Shifted (H : Header) (tails : List (User H)) (x : List Char) (T U : Table) : Prop :=
  ∀ i b, tails[i]?=some b → ∀ E p q, p≤x.length →
    argument H b x E p=some (some q) →
    valAt (T (H.bodies.length+i) [pre x p q]) p=
      match headValue H x p with
      | some (some j) => valAt (U (H.bodies.length+i) [pre x p j]) j
      | other => other

/-- The original argument selection is committed using the duplicated view
of the retained Seq value, including every predicate and helper call. -/
theorem argument_view_eval (H : Header) (tails : List (User H)) (x : List Char)
    (T U : Table) (hOk : OkTV x.length T)
    (hLexT : LexicalTable H (source H tails) x .callByValuePar T)
    (hLexU : LexicalTable H (target H tails) x .callByValueSeq U)
    (E F : List (List Char)) (hEF : Parameters H tails x T U E F)
    (b : User H) (p : Nat) (hp : p≤x.length) :
    evV (source H tails) x .callByValuePar T E b.arg p=
      evV (target H tails) x .callByValueSeq U F (view b.arg) p := by
  have hv : evV (target H tails) x .callByValueSeq U F (view b.arg) p=
      evV (target H tails) x .callByValueSeq U E b.arg p :=
    CaptureViews.evV_rebind [duplicate] E (fun k q => (hEF k q).symm)
      b.arg (HelperArgument.firstOrder _ b.arg b.allowed) p
  rw [hv]
  apply HelperArgument.eval_eq (source_installed H tails) (target_installed H tails)
    x .callByValuePar .callByValueSeq T U hOk _ E b.arg b.allowed p hp
  intro i hi q hq
  have hs := source_installed H tails i H.bodies[i] (List.getElem?_eq_getElem hi)
  have ht := target_installed H tails i H.bodies[i] (List.getElem?_eq_getElem hi)
  have hh := (hLexT [] (.call i []) hi q hq).trans (hLexU [] (.call i []) hi q hq).symm
  simpa only [evV,hs,ht,evParArgs,evSeqArgs,List.length_nil,ite_true] using hh

theorem evaluator_of_shift (H : Header) (tails : List (User H)) (x : List Char)
    (T U : Table) (hOk : OkTV x.length T)
    (hLexT : LexicalTable H (source H tails) x .callByValuePar T)
    (hLexU : LexicalTable H (target H tails) x .callByValueSeq U) (hShift : Shifted H tails x T U) :
    ∀ e E F, Parameters H tails x T U E F → ∀ p, p≤x.length →
      evV (source H tails) x .callByValuePar T E (render H tails true e) p=
        evV (target H tails) x .callByValueSeq U F (render H tails false e) p
  | .call i [], E, F, hEF, p, hp => by
    cases hr : tails[i]? with
    | none => simp only [render,hr]; rfl
    | some b =>
      have hs : ruleAtM (source H tails).rules (H.bodies.length+i)=some ⟨1,.seq H.head (.seq (.param 0) (render H tails true b.body))⟩ := by
        rw [source_rule,hr]; rfl
      have ht : ruleAtM (target H tails).rules (H.bodies.length+i)=some ⟨1,.seq duplicate (render H tails false b.body)⟩ := by
        rw [target_rule,hr]; rfl
      simp only [render,hr,ite_true]
      rw [evV_call_par hs rfl (by decide)]
      have hg := CallLookahead.evV_peek (target H tails) x .callByValueSeq U F (view b.arg) p
      change _=(match evV (target H tails) x .callByValueSeq U F (.andP (view b.arg)) p with
        | some (some j) => evV (target H tails) x .callByValueSeq U F (.call (H.bodies.length+i) [H.head]) j
        | other => other)
      rw [hg]
      simp only [evParArgs]
      rw [←argument_view_eval H tails x T U hOk hLexT hLexU E F hEF b p hp,
        argument_eval H _ (source_installed H tails) x .callByValuePar T hOk hLexT b E p hp]
      cases ha : argument H b x E p with
      | none => simp [CallLookahead.peek]
      | some result => cases result with
        | none => simp [CallLookahead.peek]
        | some q =>
          simp only [CallLookahead.peek]
          rw [evV_call_seq ht rfl]
          simp only [evSeqArgs]
          rw [hLexU F H.head H.lexical p hp]
          have he := hShift i b hr E p q hp ha
          cases hl : lexical H H.head x p with
          | none => simpa only [headValue,hl] using he
          | some result => cases result <;> simpa only [headValue,hl] using he
  | .seq a b, E, F, hEF, p, hp => by
    have hh := evaluator_of_shift H tails x T U hOk hLexT hLexU hShift a E F hEF p hp
    simp only [render]
    cases hv : evV (source H tails) x .callByValuePar T E (render H tails true a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_shift H tails x T U hOk hLexT hLexU hShift b E F hEF q (evV_ok hOk _ p hp q hv)
  | .alt a b, E, F, hEF, p, hp => by
    have hh := evaluator_of_shift H tails x T U hOk hLexT hLexU hShift a E F hEF p hp
    simp only [render]
    cases hv : evV (source H tails) x .callByValuePar T E (render H tails true a) p with
    | none => rw [evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some result => cases result with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]
        exact evaluator_of_shift H tails x T U hOk hLexT hLexU hShift b E F hEF p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | .star a, E, F, hEF, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift H tails x T U hOk hLexT hLexU hShift a E F hEF q (by omega))
  | .notP a, E, F, hEF, p, hp => by
    simp only [render,evV]
    rw [evaluator_of_shift H tails x T U hOk hLexT hLexU hShift a E F hEF p hp]
  | .param k, E, F, hEF, p, hp => hEF k p
  | .eps, _, _, _, _, _ | .any, _, _, _, _, _ | .chr _, _, _, _, _, _
  | .range _ _, _, _, _, _, _ | .lit _, _, _, _, _, _ => rfl
  | .call _ (_::_), _, _, _, _, _ | .dbg _, _, _, _, _, _ | .lam _ _, _, _, _, _, _
  | .callParam _ _, _, _, _, _, _ | .invoke _ _ _, _, _, _, _, _ => rfl


theorem source_step (H : Header) (tails : List (User H)) (x : List Char) (k i : Nat)
    (r : MRule) (hr : ruleAtM (source H tails).rules (H.bodies.length+i)=some r)
    (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (sourceTable H tails x (k+1) (H.bodies.length+i) W) p=
      evV (source H tails) x .callByValuePar (sourceTable H tails x k) W r.body p :=
  SeededClock.user_step _ x _ _ _ _ k _ (by simp [pick]) r hr W p hp

theorem target_step (H : Header) (tails : List (User H)) (x : List Char) (k i : Nat)
    (r : MRule) (hr : ruleAtM (target H tails).rules (H.bodies.length+i)=some r)
    (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (targetTable H tails x (k+1) (H.bodies.length+i) W) p=
      evV (target H tails) x .callByValueSeq (targetTable H tails x k) W r.body p :=
  ClockFreezing.frozen_user_step _ x _ _ _ k _ (by simp [pick]) r hr W p hp

theorem tables_shifted (H : Header) (tails : List (User H)) (x : List Char) (k : Nat) :
    Shifted H tails x (sourceTable H tails x k) (targetTable H tails x k) := by
  induction k with
  | zero =>
    intro i b hr E p q hp harg
    have hs : ruleAtM (source H tails).rules (H.bodies.length+i)=some ⟨1,.seq H.head (.seq (.param 0) (render H tails true b.body))⟩ := by
      rw [source_rule,hr]; rfl
    rw [show sourceTable H tails x 0=SeededClock.prefixSeed (source H tails) x .callByValuePar
      (pick H.bodies) (floor H.bodies x) from rfl]
    rw [SeededClock.prefixSeed_query _ x _ _ _ (H.bodies.length+i) (by simp [pick]) 1 _ _ hs _ p hp,
      frozen_lexical H _ (source_installed H tails) x .callByValuePar 0 _ H.head H.lexical p hp]
    have hn : ¬H.bodies.length+i<H.bodies.length := by omega
    cases h : lexical H H.head x p with
    | none => simp [headValue,h]
    | some result => cases result <;> simp [targetTable,RecursiveParserStability.frozen,ClockFreezing.frozen,pick,valAt_nil,headValue,h,hn]
  | succ k ih =>
    intro i b hr E p q hp harg
    let T := sourceTable H tails x k
    let U := targetTable H tails x k
    have hs : ruleAtM (source H tails).rules (H.bodies.length+i)=some ⟨1,.seq H.head (.seq (.param 0) (render H tails true b.body))⟩ := by
      rw [source_rule,hr]; rfl
    rw [source_step H tails x k i _ hs _ p hp]
    have hh := seeded_lexical H _ (source_installed H tails) x .callByValuePar k [pre x p q] H.head H.lexical p hp
    change (match evV (source H tails) x .callByValuePar T [pre x p q] H.head p with
      | some (some j) => evV (source H tails) x .callByValuePar T [pre x p q] (.seq (.param 0) (render H tails true b.body)) j
      | other => other)=_
    rw [hh]
    cases hj : lexical H H.head x p with
    | none => simp only [headValue,hj]
    | some result => cases result with
      | none => simp only [headValue,hj]
      | some j =>
        simp only [headValue,hj]
        have hfirst0 := lexical_success H H.head H.lexical x p j hp hj
        have hfirst := And.intro hfirst0.1 (And.intro hfirst0.2 (H.captured x p j hp hj))
        have hselected0 := ReplayFusion.success_prefix (tblV_sound (helpers_firstOrder H) (by decide) _)
          E b.arg (HelperArgument.firstOrder _ b.arg b.allowed) p q hp harg
        have hselected := And.intro hselected0.1 (And.intro hselected0.2 (b.captured x E p q hp harg))
        obtain ⟨a,v,ha,hv,hw⟩ := hselected.2.2
        let u := pre x p j
        have hua : u=a := PrefixCodeCapture.prefix_identifies H.prefixFree hfirst.2.2 ha
          ⟨sfx x j,by rw [←hfirst.2.1,hselected.2.1,hw,List.append_assoc]⟩
        rw [←hua] at hw
        have hrest : sfx x j=v++sfx x q := by
          apply (List.append_right_inj u).mp
          simpa only [hw,List.append_assoc] using hfirst.2.1.symm.trans hselected.2.1
        have ht : ruleAtM (target H tails).rules (H.bodies.length+i)=some ⟨1,.seq duplicate (render H tails false b.body)⟩ := by
          rw [target_rule,hr]; rfl
        rw [target_step H tails x k i _ ht _ j hfirst.1,hw]
        rw [PrefixCodeCapture.collapse (source H tails) x .callByValuePar T H.prefixFree
          u v (sfx x q) hfirst.2.2 hv j hrest (render H tails true b.body) (render_firstOrder H tails true b.body)]
        have hd : evV (source H tails) x .callByValuePar T [u] duplicate j=
            evV (target H tails) x .callByValueSeq U [u] duplicate j :=
          SeededClock.word_eval_eq _ _ x _ _ T U [u] duplicate ⟨True.intro,True.intro⟩ j
        change (match evV (source H tails) x .callByValuePar T [u] duplicate j with
          | some (some z) => evV (source H tails) x .callByValuePar T [u] (view (render H tails true b.body)) z
          | other => other)=
          (match evV (target H tails) x .callByValueSeq U [u] duplicate j with
          | some (some z) => evV (target H tails) x .callByValueSeq U [u] (render H tails false b.body) z
          | other => other)
        rw [←hd]
        cases hz : evV (source H tails) x .callByValuePar T [u] duplicate j with
        | none => rfl
        | some result => cases result with
          | none => rfl
          | some z =>
            dsimp only []
            rw [PrefixCodeCapture.view_eval _ x _ T u _ (render_firstOrder H tails true b.body) z]
            exact evaluator_of_shift H tails x T U (SeededClock.rounds_ok H.bodies _ x _ k)
              (seeded_lexical H _ (source_installed H tails) x .callByValuePar k)
              (frozen_lexical H _ (target_installed H tails) x .callByValueSeq k) ih b.body [u++u] [u]
              (parameters_double H tails x T U u) z
              (evV_ok (SeededClock.rounds_ok H.bodies _ x _ k) duplicate j hfirst.1 z hz)


theorem evaluator_eq (H : Header) (tails : List (User H)) (x : List Char) (k : Nat)
    (e : MExp) (p : Nat) (hp : p≤x.length) :
    evV (source H tails) x .callByValuePar (sourceTable H tails x k) [] (render H tails true e) p=
    evV (target H tails) x .callByValueSeq (targetTable H tails x k) [] (render H tails false e) p :=
  evaluator_of_shift H tails x _ _ (SeededClock.rounds_ok H.bodies _ x _ k)
    (seeded_lexical H _ (source_installed H tails) x .callByValuePar k)
    (frozen_lexical H _ (target_installed H tails) x .callByValueSeq k)
    (tables_shifted H tails x k) e [] [] (parameters_empty H tails x _ _) p hp

theorem observations_iff (H : Header) (tails : List (User H)) (e : MExp)
    (x : List Char) (r : Option (List Char)) :
    SObs (source H tails) .callByValuePar (render H tails true e) x r ↔
      SObs (target H tails) .callByValueSeq (render H tails false e) x r := by
  rw [SeededClock.observations_iff H.valid (source_installed H tails) (source_firstOrder H tails)
    x .callByValuePar (by decide) _ (render_firstOrder H tails true e),
    ClockFreezing.observations_iff (target_firstOrder H tails) x .callByValueSeq (by decide)
      (pick H.bodies) (floor H.bodies x)
      (RecursiveParserStability.helpers_stable H.valid (target_installed H tails) x .callByValueSeq)
      _ (render_firstOrder H tails false e)]
  exact exists_congr (fun k => exists_congr (fun v => by rw [evaluator_eq H tails x k e x.length (Nat.le_refl _)]))

theorem language_translation (H : Header) (tails : List (User H)) (e : MExp) :
    ∃ (g : MGrammar) (entry : MExp), g.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs (source H tails) .callByValuePar (render H tails true e) x (some []) ↔
        SObs g .callByValueSeq entry x (some []) :=
  ⟨target H tails,render H tails false e,target_firstOrder H tails,render_firstOrder H tails false e,
    fun x => observations_iff H tails e x (some [])⟩




/-- An undefined dependent argument stays undefined before header entry
and table queries on both sides of the generated call. -/
theorem undefined_argument (H : Header) (tails : List (User H)) (i : Nat) (b : User H)
    (hr : tails[i]?=some b) (x : List Char) (p : Nat) (hp : p≤x.length)
    (k : Nat) (E F : List (List Char))
    (hEF : Parameters H tails x (sourceTable H tails x k) (targetTable H tails x k) E F)
    (harg : argument H b x E p=none) :
    evV (source H tails) x .callByValuePar (sourceTable H tails x k) E
      (render H tails true (.call i [])) p=none ∧
    evV (target H tails) x .callByValueSeq (targetTable H tails x k) F
      (render H tails false (.call i [])) p=none := by
  have hs : ruleAtM (source H tails).rules (H.bodies.length+i)=
      some ⟨1,.seq H.head (.seq (.param 0) (render H tails true b.body))⟩ := by
    rw [source_rule,hr]; rfl
  have ha : evV (source H tails) x .callByValuePar (sourceTable H tails x k) E b.arg p=none :=
    (argument_eval H _ (source_installed H tails) x .callByValuePar _
      (SeededClock.rounds_ok H.bodies _ x _ k)
      (seeded_lexical H _ (source_installed H tails) x .callByValuePar k) b E p hp).trans harg
  constructor
  · simp only [render,hr,ite_true]
    rw [evV_call_par hs rfl (by decide)]
    simp only [evParArgs,ha]
  · simp only [render,hr]
    have hg : evV (target H tails) x .callByValueSeq (targetTable H tails x k) F (.andP (view b.arg)) p=none := by
      rw [CallLookahead.evV_peek,←argument_view_eval H tails x _ _
        (SeededClock.rounds_ok H.bodies _ x _ k)
        (seeded_lexical H _ (source_installed H tails) x .callByValuePar k)
        (frozen_lexical H _ (target_installed H tails) x .callByValueSeq k) E F hEF b p hp,ha]
      rfl
    exact evV_seq_none hg

end Shallot.MacroPeg.CBV.RecursiveCodeGrammar
