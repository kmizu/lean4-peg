import MacroPeg.CBV.RuntimePrefixGrammar

/-! Preserve the result selected by an arbitrary closed argument parser
whose captures consist of two prefix codewords. Prefix-failure seeds
synchronize the independently parsed argument and advanced Seq entry. -/
namespace Shallot.MacroPeg.CBV.SelectedPrefixGrammar
open ClockFreezing (Table)
open ParserPrefixFusion (Pure pure_eval pure_firstOrder)
open PrefixCodeCapture (PrefixFree duplicate view)

open RuntimePrefixGrammar (Header lexical head_eval lexical_success)

structure User (H : Header) where
  arg : MExp
  pure : Pure arg
  captured : ∀ (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p q : Nat), p≤x.length →
    evV g x s T E arg p=some (some q) →
    ∃ u v, H.code u ∧ H.code v ∧ pre x p q=u++v
  body : MExp

def argument (H : Header) (r : User H) (x : List Char) (p : Nat) : Res :=
  evV ⟨[]⟩ x .callByValuePar (fun _ _ => []) [] r.arg p

theorem argument_eval (H : Header) (r : User H) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E r.arg p=argument H r x p :=
  pure_eval g ⟨[]⟩ x s .callByValuePar T (fun _ _ => []) E [] r.arg r.pure p

theorem argument_success (H : Header) (r : User H) (x : List Char) (p q : Nat) (hp : p≤x.length)
    (h : argument H r x p=some (some q)) :
    q≤x.length ∧ sfx x p=pre x p q++sfx x q ∧
      ∃ u v, H.code u ∧ H.code v ∧ pre x p q=u++v := by
  have hs : SoundTV (⟨[]⟩ : MGrammar) x .callByValuePar (fun _ _ => []) := by
    intro i r E hr
    cases i <;> cases hr
  have hh := ReplayFusion.success_prefix hs [] r.arg (pure_firstOrder _ r.pure) p q hp h
  exact ⟨hh.1,hh.2,r.captured _ x _ _ [] p q hp h⟩

def render (H : Header) (tails : List (User H)) (par : Bool) : MExp → MExp
  | .call i [] => match tails[i]? with
    | none => MExp.failAlways
    | some r => if par then .call i [r.arg]
      else .seq (.andP r.arg) (.call i [H.head])
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
  ⟨tails.map (fun b => ⟨1,.seq H.head (.seq (.param 0) (render H tails true b.body))⟩)⟩
def target (H : Header) (tails : List (User H)) : MGrammar :=
  ⟨tails.map (fun b => ⟨1,.seq duplicate (render H tails false b.body)⟩)⟩

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
      · exact ⟨pure_firstOrder _ b.pure,pure_firstOrder _ H.pure,True.intro⟩
      · exact ⟨pure_firstOrder _ b.pure,True.intro⟩
  | .seq a b | .alt a b => ⟨render_firstOrder H tails par a,render_firstOrder H tails par b⟩
  | .star a | .notP a => render_firstOrder H tails par a
  | .param k => by cases par <;> first | exact view_param_firstOrder k | trivial
  | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .call _ (_::_) | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem source_firstOrder (H : Header) (tails : List (User H)) : (source H tails).FirstOrder := by
  intro r hr
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
  exact ⟨pure_firstOrder _ H.pure,True.intro,render_firstOrder H tails true b.body⟩
theorem target_firstOrder (H : Header) (tails : List (User H)) : (target H tails).FirstOrder := by
  intro r hr
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
  exact ⟨⟨True.intro,True.intro⟩,render_firstOrder H tails false b.body⟩

theorem source_rule (H : Header) (tails : List (User H)) (i : Nat) :
    ruleAtM (source H tails).rules i=(tails[i]?).map
      (fun b => ⟨1,.seq H.head (.seq (.param 0) (render H tails true b.body))⟩) := by
  simp [source,ruleAtM_eq_getElem?]
theorem target_rule (H : Header) (tails : List (User H)) (i : Nat) :
    ruleAtM (target H tails).rules i=(tails[i]?).map
      (fun b => ⟨1,.seq duplicate (render H tails false b.body)⟩) := by
  simp [target,ruleAtM_eq_getElem?]

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
  SeededClock.rounds [] (source H tails) x .callByValuePar k

def Shifted (H : Header) (tails : List (User H)) (x : List Char) (T U : Table) : Prop :=
  ∀ i b, tails[i]?=some b → ∀ p q, p≤x.length →
    argument H b x p=some (some q) →
    valAt (T i [pre x p q]) p=
      match lexical H x p with
      | some (some j) => valAt (U i [pre x p j]) j
      | other => other

theorem evaluator_of_shift (H : Header) (tails : List (User H)) (x : List Char)
    (T U : Table) (hOk : OkTV x.length T) (hShift : Shifted H tails x T U) :
    ∀ e E F, Parameters H tails x T U E F → ∀ p, p≤x.length →
      evV (source H tails) x .callByValuePar T E (render H tails true e) p=
        evV (target H tails) x .callByValueSeq U F (render H tails false e) p
  | .call i [], E, F, hEF, p, hp => by
    cases hr : tails[i]? with
    | none => simp only [render,hr]; rfl
    | some b =>
      have hs : ruleAtM (source H tails).rules i=some ⟨1,.seq H.head (.seq (.param 0) (render H tails true b.body))⟩ := by
        rw [source_rule,hr]; rfl
      have ht : ruleAtM (target H tails).rules i=some ⟨1,.seq duplicate (render H tails false b.body)⟩ := by
        rw [target_rule,hr]; rfl
      simp only [render,hr,ite_true]
      rw [evV_call_par hs rfl (by decide)]
      have hg := CallLookahead.evV_peek (target H tails) x .callByValueSeq U F b.arg p
      change _=(match evV (target H tails) x .callByValueSeq U F (.andP b.arg) p with
        | some (some j) => evV (target H tails) x .callByValueSeq U F (.call i [H.head]) j
        | other => other)
      rw [hg]
      simp only [evParArgs,argument_eval]
      cases ha : argument H b x p with
      | none => simp [CallLookahead.peek]
      | some result => cases result with
        | none => simp [CallLookahead.peek]
        | some q =>
          simp only [CallLookahead.peek]
          rw [evV_call_seq ht rfl]
          simp only [evSeqArgs,head_eval]
          have he := hShift i b hr p q hp ha
          cases hl : lexical H x p with
          | none => simpa only [hl] using he
          | some result => cases result <;> simpa only [hl] using he
  | .seq a b, E, F, hEF, p, hp => by
    have hh := evaluator_of_shift H tails x T U hOk hShift a E F hEF p hp
    simp only [render]
    cases hv : evV (source H tails) x .callByValuePar T E (render H tails true a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_shift H tails x T U hOk hShift b E F hEF q (evV_ok hOk _ p hp q hv)
  | .alt a b, E, F, hEF, p, hp => by
    have hh := evaluator_of_shift H tails x T U hOk hShift a E F hEF p hp
    simp only [render]
    cases hv : evV (source H tails) x .callByValuePar T E (render H tails true a) p with
    | none => rw [evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some result => cases result with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]
        exact evaluator_of_shift H tails x T U hOk hShift b E F hEF p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | .star a, E, F, hEF, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift H tails x T U hOk hShift a E F hEF q (by omega))
  | .notP a, E, F, hEF, p, hp => by
    simp only [render,evV]
    rw [evaluator_of_shift H tails x T U hOk hShift a E F hEF p hp]
  | .param k, E, F, hEF, p, hp => hEF k p
  | .eps, _, _, _, _, _ | .any, _, _, _, _, _ | .chr _, _, _, _, _, _
  | .range _ _, _, _, _, _, _ | .lit _, _, _, _, _, _ => rfl
  | .call _ (_::_), _, _, _, _, _ | .dbg _, _, _, _, _, _ | .lam _ _, _, _, _, _, _
  | .callParam _ _, _, _, _, _, _ | .invoke _ _ _, _, _, _, _, _ => rfl

theorem source_step (H : Header) (tails : List (User H)) (x : List Char) (k i : Nat)
    (r : MRule) (hr : ruleAtM (source H tails).rules i=some r)
    (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (sourceTable H tails x (k+1) i W) p=
      evV (source H tails) x .callByValuePar (sourceTable H tails x k) W r.body p :=
  SeededClock.user_step _ x _ _ _ _ k i (by simp [RecursiveParserStability.pick]) r hr W p hp

theorem tables_shifted (H : Header) (tails : List (User H)) (x : List Char) (k : Nat) :
    Shifted H tails x (sourceTable H tails x k) (tblV (target H tails) x .callByValueSeq k) := by
  induction k with
  | zero =>
    intro i b hr p q hp harg
    have hs : ruleAtM (source H tails).rules i=some ⟨1,.seq H.head (.seq (.param 0) (render H tails true b.body))⟩ := by
      rw [source_rule,hr]; rfl
    rw [show sourceTable H tails x 0=SeededClock.prefixSeed (source H tails) x .callByValuePar
      (RecursiveParserStability.pick []) (RecursiveParserStability.floor [] x) from rfl]
    rw [SeededClock.prefixSeed_query _ x _ _ _ i (by simp [RecursiveParserStability.pick]) 1 _ _ hs _ p hp,
      head_eval]
    cases h : lexical H x p with
    | none => simp
    | some result => cases result <;> simp [tblV,valAt_nil]
  | succ k ih =>
    intro i b hr p q hp harg
    let T := sourceTable H tails x k
    let U := tblV (target H tails) x .callByValueSeq k
    have hs : ruleAtM (source H tails).rules i=some ⟨1,.seq H.head (.seq (.param 0) (render H tails true b.body))⟩ := by
      rw [source_rule,hr]; rfl
    rw [source_step H tails x k i _ hs _ p hp]
    have hh := head_eval H (source H tails) x .callByValuePar T [pre x p q] p
    change (match evV (source H tails) x .callByValuePar T [pre x p q] H.head p with
      | some (some j) => evV (source H tails) x .callByValuePar T [pre x p q] (.seq (.param 0) (render H tails true b.body)) j
      | other => other)=_
    rw [hh]
    cases hj : lexical H x p with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some j =>
        dsimp only []
        have hfirst := lexical_success H x p j hp hj
        have hselected := argument_success H b x p q hp harg
        obtain ⟨a,v,ha,hv,hw⟩ := hselected.2.2
        let u := pre x p j
        have hua : u=a := PrefixCodeCapture.prefix_identifies H.prefixFree hfirst.2.2 ha
          ⟨sfx x j,by rw [←hfirst.2.1,hselected.2.1,hw,List.append_assoc]⟩
        rw [←hua] at hw
        have hrest : sfx x j=v++sfx x q := by
          apply (List.append_right_inj u).mp
          simpa only [hw,List.append_assoc] using hfirst.2.1.symm.trans hselected.2.1
        have ht : ruleAtM (target H tails).rules i=some ⟨1,.seq duplicate (render H tails false b.body)⟩ := by
          rw [target_rule,hr]; rfl
        rw [valAt_tblV_succ ht _ hfirst.1,hw]
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
            exact evaluator_of_shift H tails x T U (SeededClock.rounds_ok [] _ x _ k) ih b.body [u++u] [u]
              (parameters_double H tails x T U u) z
              (evV_ok (SeededClock.rounds_ok [] _ x _ k) duplicate j hfirst.1 z hz)

theorem evaluator_eq (H : Header) (tails : List (User H)) (x : List Char) (k : Nat)
    (e : MExp) (p : Nat) (hp : p≤x.length) :
    evV (source H tails) x .callByValuePar (sourceTable H tails x k) [] (render H tails true e) p=
    evV (target H tails) x .callByValueSeq (tblV (target H tails) x .callByValueSeq k)
      [] (render H tails false e) p :=
  evaluator_of_shift H tails x _ _ (SeededClock.rounds_ok [] _ x _ k) (tables_shifted H tails x k) e [] []
    (parameters_empty H tails x _ _) p hp

theorem stable_eq (H : Header) (tails : List (User H)) (e : MExp) (x : List Char) :
    evV (source H tails) x .callByValuePar (tblV (source H tails) x .callByValuePar (iterBoundV (source H tails) x))
      [] (render H tails true e) x.length=
    evV (target H tails) x .callByValueSeq (tblV (target H tails) x .callByValueSeq (iterBoundV (target H tails) x))
      [] (render H tails false e) x.length := by
  have hdefined (v : Option Nat) :
      evV (source H tails) x .callByValuePar (tblV (source H tails) x .callByValuePar (iterBoundV (source H tails) x))
        [] (render H tails true e) x.length=some v ↔
      evV (target H tails) x .callByValueSeq (tblV (target H tails) x .callByValueSeq (iterBoundV (target H tails) x))
        [] (render H tails false e) x.length=some v := by
    rw [←SeededClock.stable_defined_iff (bodies:=[]) (by intro b hb; cases hb)
      (by intro i b hb; simp at hb) x .callByValuePar _ x.length (Nat.le_refl _) v,
      ←tblV_stable (target H tails) x .callByValueSeq (Nat.le_refl _) ]
    exact exists_congr (fun k => by rw [evaluator_eq H tails x k e x.length (Nat.le_refl _)])
  cases hs : evV (source H tails) x .callByValuePar
      (tblV (source H tails) x .callByValuePar (iterBoundV (source H tails) x)) [] (render H tails true e) x.length with
  | none =>
    cases ht : evV (target H tails) x .callByValueSeq
        (tblV (target H tails) x .callByValueSeq (iterBoundV (target H tails) x)) [] (render H tails false e) x.length with
    | none => rfl
    | some v => have hh := (hdefined v).mpr ht; rw [hs] at hh; cases hh
  | some v => exact ((hdefined v).mp hs).symm

theorem observations_iff (H : Header) (tails : List (User H)) (e : MExp)
    (x : List Char) (r : Option (List Char)) :
    SObs (source H tails) .callByValuePar (render H tails true e) x r ↔
      SObs (target H tails) .callByValueSeq (render H tails false e) x r := by
  rw [←decideObsV_iff (source_firstOrder H tails) (by decide) (render_firstOrder H tails true e),
    ←decideObsV_iff (target_firstOrder H tails) (by decide) (render_firstOrder H tails false e)]
  unfold decideObsV
  rw [stable_eq]

theorem language_translation (H : Header) (tails : List (User H)) (e : MExp) :
    ∃ (g : MGrammar) (entry : MExp), g.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs (source H tails) .callByValuePar (render H tails true e) x (some []) ↔
        SObs g .callByValueSeq entry x (some []) :=
  ⟨target H tails,render H tails false e,target_firstOrder H tails,render_firstOrder H tails false e,
    fun x => observations_iff H tails e x (some [])⟩

/-- An undefined selected argument stays undefined before either body or
table query, even when the header itself would finitely fail. -/
theorem undefined_argument (H : Header) (tails : List (User H)) (i : Nat) (b : User H)
    (hr : tails[i]?=some b) (x : List Char) (p : Nat)
    (harg : argument H b x p=none) (T U : Table) (E F : List (List Char)) :
    evV (source H tails) x .callByValuePar T E (render H tails true (.call i [])) p=none ∧
    evV (target H tails) x .callByValueSeq U F (render H tails false (.call i [])) p=none := by
  have hs : ruleAtM (source H tails).rules i=some ⟨1,.seq H.head (.seq (.param 0) (render H tails true b.body))⟩ := by
    rw [source_rule,hr]; rfl
  constructor
  · simp only [render,hr,ite_true]
    rw [evV_call_par hs rfl (by decide)]
    simp only [evParArgs,argument_eval,harg]
  · simp only [render,hr]
    have hg : evV (target H tails) x .callByValueSeq U F (.andP b.arg) p=none := by
      rw [CallLookahead.evV_peek,argument_eval,harg]
      rfl
    exact evV_seq_none hg

end Shallot.MacroPeg.CBV.SelectedPrefixGrammar
