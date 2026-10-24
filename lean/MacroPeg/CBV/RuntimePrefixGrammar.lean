import MacroPeg.CBV.PrefixCodeCapture

/-! A recursive grammar translation retaining a runtime prefix codeword.
Calls capture two complete codewords in Par and one in Seq; a preflight
keeps argument failure and undefinedness before the table query. -/
namespace Shallot.MacroPeg.CBV.RuntimePrefixGrammar
open ClockFreezing (Table)
open ParserPrefixFusion (Pure pure_eval pure_firstOrder)
open PrefixCodeCapture (PrefixFree duplicate view)

structure Header where
  head : MExp
  pure : Pure head
  code : List Char → Prop
  prefixFree : PrefixFree code
  captured : ∀ (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p q : Nat), p≤x.length →
    evV g x s T E head p=some (some q) → code (pre x p q)

def lexical (H : Header) (x : List Char) (p : Nat) : Res :=
  evV ⟨[]⟩ x .callByValuePar (fun _ _ => []) [] H.head p
def argument (H : Header) : MExp := .seq H.head H.head

theorem head_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E H.head p=lexical H x p :=
  pure_eval g ⟨[]⟩ x s .callByValuePar T (fun _ _ => []) E [] H.head H.pure p

theorem lexical_success (H : Header) (x : List Char) (p q : Nat) (hp : p≤x.length)
    (h : lexical H x p=some (some q)) :
    q≤x.length ∧ sfx x p=pre x p q++sfx x q ∧ H.code (pre x p q) := by
  have hs : SoundTV (⟨[]⟩ : MGrammar) x .callByValuePar (fun _ _ => []) := by
    intro i r E hr
    cases i <;> cases hr
  have hh := ReplayFusion.success_prefix hs [] H.head (pure_firstOrder _ H.pure) p q hp h
  exact ⟨hh.1,hh.2,H.captured _ x _ _ [] p q hp h⟩

theorem argument_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (argument H) p=
      match lexical H x p with | some (some j) => lexical H x j | other => other := by
  simp only [argument,evV,head_eval]
  rfl

def render (H : Header) (tails : List MExp) (par : Bool) : MExp → MExp
  | .call i [] => match tails[i]? with
    | none => MExp.failAlways
    | some _ => if par then .call i [argument H]
      else .seq (.andP (argument H)) (.call i [H.head])
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

def source (H : Header) (tails : List MExp) : MGrammar :=
  ⟨tails.map (fun b => ⟨1,.seq H.head (.seq (.param 0) (render H tails true b))⟩)⟩
def target (H : Header) (tails : List MExp) : MGrammar :=
  ⟨tails.map (fun b => ⟨1,.seq duplicate (render H tails false b)⟩)⟩

theorem view_param_firstOrder (k : Nat) : (view (.param k)).FirstOrder := by
  cases k <;> simp [view,MExp.subst,argAt,duplicate,MExp.FirstOrder,MExp.failAlways]

theorem render_firstOrder (H : Header) (tails : List MExp) (par : Bool) :
    ∀ e, (render H tails par e).FirstOrder
  | .call i [] => by
    simp only [render]
    cases tails[i]? with
    | none => trivial
    | some b =>
      cases par
      · exact ⟨⟨pure_firstOrder _ H.pure,pure_firstOrder _ H.pure⟩,pure_firstOrder _ H.pure,True.intro⟩
      · exact ⟨⟨pure_firstOrder _ H.pure,pure_firstOrder _ H.pure⟩,True.intro⟩
  | .seq a b | .alt a b => ⟨render_firstOrder H tails par a,render_firstOrder H tails par b⟩
  | .star a | .notP a => render_firstOrder H tails par a
  | .param k => by cases par <;> first | exact view_param_firstOrder k | trivial
  | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .call _ (_::_) | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem source_firstOrder (H : Header) (tails : List MExp) : (source H tails).FirstOrder := by
  intro r hr
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
  exact ⟨pure_firstOrder _ H.pure,True.intro,render_firstOrder H tails true b⟩
theorem target_firstOrder (H : Header) (tails : List MExp) : (target H tails).FirstOrder := by
  intro r hr
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
  exact ⟨⟨True.intro,True.intro⟩,render_firstOrder H tails false b⟩

theorem source_rule (H : Header) (tails : List MExp) (i : Nat) :
    ruleAtM (source H tails).rules i=(tails[i]?).map
      (fun b => ⟨1,.seq H.head (.seq (.param 0) (render H tails true b))⟩) := by
  simp [source,ruleAtM_eq_getElem?]
theorem target_rule (H : Header) (tails : List MExp) (i : Nat) :
    ruleAtM (target H tails).rules i=(tails[i]?).map
      (fun b => ⟨1,.seq duplicate (render H tails false b)⟩) := by
  simp [target,ruleAtM_eq_getElem?]

def Parameters (H : Header) (tails : List MExp) (x : List Char) (T U : Table)
    (E F : List (List Char)) : Prop := ∀ k p,
  evV (source H tails) x .callByValuePar T E (.param k) p=
    evV (target H tails) x .callByValueSeq U F (view (.param k)) p

theorem parameters_empty (H : Header) (tails : List MExp) (x : List Char) (T U : Table) :
    Parameters H tails x T U [] [] := by
  intro k p
  cases k <;> simp [view,MExp.subst,argAt,duplicate,evV,MExp.failAlways]

theorem parameters_double (H : Header) (tails : List MExp) (x : List Char) (T U : Table)
    (u : List Char) : Parameters H tails x T U [u++u] [u] := by
  intro k p
  cases k with
  | zero =>
    change evV (source H tails) x .callByValuePar T [u++u] (.param 0) p=
      evV (target H tails) x .callByValueSeq U [u] duplicate p
    rw [WordArguments.word_eval _ x _ U [u] duplicate ⟨True.intro,True.intro⟩ p]
    rfl
  | succ k => simp [view,MExp.subst,argAt,evV,MExp.failAlways]

def Shifted (H : Header) (tails : List MExp) (x : List Char) (T U : Table) : Prop :=
  ∀ i b, tails[i]?=some b → ∀ p j q, p≤x.length →
    lexical H x p=some (some j) → lexical H x j=some (some q) →
    valAt (T i [pre x p q]) p=valAt (U i [pre x p j]) j

theorem evaluator_of_shift (H : Header) (tails : List MExp) (x : List Char)
    (T U : Table) (hOk : OkTV x.length T) (hShift : Shifted H tails x T U) :
    ∀ e E F, Parameters H tails x T U E F → ∀ p, p≤x.length →
      evV (source H tails) x .callByValuePar T E (render H tails true e) p=
        evV (target H tails) x .callByValueSeq U F (render H tails false e) p
  | .call i [], E, F, hEF, p, hp => by
    cases hr : tails[i]? with
    | none => simp only [render,hr]; rfl
    | some b =>
      have hs : ruleAtM (source H tails).rules i=some ⟨1,.seq H.head (.seq (.param 0) (render H tails true b))⟩ := by
        rw [source_rule,hr]; rfl
      have ht : ruleAtM (target H tails).rules i=some ⟨1,.seq duplicate (render H tails false b)⟩ := by
        rw [target_rule,hr]; rfl
      simp only [render,hr,ite_true]
      rw [evV_call_par hs rfl (by decide)]
      have hg := CallLookahead.evV_peek (target H tails) x .callByValueSeq U F (argument H) p
      change _=(match evV (target H tails) x .callByValueSeq U F (.andP (argument H)) p with
        | some (some j) => evV (target H tails) x .callByValueSeq U F (.call i [H.head]) j
        | other => other)
      rw [hg]
      simp only [evParArgs,argument_eval]
      cases ha : lexical H x p with
      | none => simp [CallLookahead.peek]
      | some first => cases first with
        | none => simp [CallLookahead.peek]
        | some j =>
          cases hb : lexical H x j with
          | none => simp [hb,CallLookahead.peek]
          | some second => cases second with
            | none => simp [hb,CallLookahead.peek]
            | some q =>
              simp only [hb,CallLookahead.peek]
              rw [evV_call_seq ht rfl]
              simp only [evSeqArgs,head_eval,ha]
              exact hShift i b hr p j q hp ha hb
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

theorem tables_shifted (H : Header) (tails : List MExp) (x : List Char) (k : Nat) :
    Shifted H tails x (tblV (source H tails) x .callByValuePar k)
      (tblV (target H tails) x .callByValueSeq k) := by
  induction k with
  | zero => intro i b hr p j q hp hj hq; simp [tblV,valAt_nil]
  | succ k ih =>
    intro i b hr p j q hp hj hq
    let T := tblV (source H tails) x .callByValuePar k
    let U := tblV (target H tails) x .callByValueSeq k
    have hfirst := lexical_success H x p j hp hj
    have hsecond := lexical_success H x j q hfirst.1 hq
    let u := pre x p j
    let v := pre x j q
    have hcap : pre x p q=u++v :=
      SequenceArguments.pre_concat hp hsecond.1 hfirst.2.1 hsecond.2.1
    have hs : ruleAtM (source H tails).rules i=some ⟨1,.seq H.head (.seq (.param 0) (render H tails true b))⟩ := by
      rw [source_rule,hr]; rfl
    have ht : ruleAtM (target H tails).rules i=some ⟨1,.seq duplicate (render H tails false b)⟩ := by
      rw [target_rule,hr]; rfl
    rw [valAt_tblV_succ hs _ hp,valAt_tblV_succ ht _ hfirst.1]
    have hh : evV (source H tails) x .callByValuePar T [pre x p q] H.head p=some (some j) := by
      rw [head_eval]; exact hj
    rw [evV_seq_ok hh,hcap]
    rw [PrefixCodeCapture.collapse (source H tails) x .callByValuePar T H.prefixFree
      u v (sfx x q) hfirst.2.2 hsecond.2.2 j hsecond.2.1 (render H tails true b) (render_firstOrder H tails true b)]
    have hd : evV (source H tails) x .callByValuePar T [u] duplicate j=
        evV (target H tails) x .callByValueSeq U [u] duplicate j := by
      rw [WordArguments.word_eval _ x _ T [u] duplicate ⟨True.intro,True.intro⟩ j,
        WordArguments.word_eval _ x _ U [u] duplicate ⟨True.intro,True.intro⟩ j]
      rfl
    change (match evV (source H tails) x .callByValuePar T [u] duplicate j with
      | some (some z) => evV (source H tails) x .callByValuePar T [u] (view (render H tails true b)) z
      | other => other)=
      (match evV (target H tails) x .callByValueSeq U [u] duplicate j with
      | some (some z) => evV (target H tails) x .callByValueSeq U [u] (render H tails false b) z
      | other => other)
    rw [←hd]
    cases hv : evV (source H tails) x .callByValuePar T [u] duplicate j with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some z =>
        dsimp only []
        rw [PrefixCodeCapture.view_eval _ x _ T u _ (render_firstOrder H tails true b) z]
        exact evaluator_of_shift H tails x T U (tblV_ok _ _ _ k) ih b [u++u] [u]
          (parameters_double H tails x T U u) z
          (evV_ok (tblV_ok _ _ _ k) duplicate j hfirst.1 z hv)

theorem evaluator_eq (H : Header) (tails : List MExp) (x : List Char) (k : Nat)
    (e : MExp) (p : Nat) (hp : p≤x.length) :
    evV (source H tails) x .callByValuePar (tblV (source H tails) x .callByValuePar k)
      [] (render H tails true e) p=
    evV (target H tails) x .callByValueSeq (tblV (target H tails) x .callByValueSeq k)
      [] (render H tails false e) p :=
  evaluator_of_shift H tails x _ _ (tblV_ok _ _ _ k) (tables_shifted H tails x k) e [] []
    (parameters_empty H tails x _ _) p hp

theorem decide_eq (H : Header) (tails : List MExp) (e : MExp) (x : List Char) :
    decideObsV .callByValuePar (source H tails) x (render H tails true e)=
      decideObsV .callByValueSeq (target H tails) x (render H tails false e) := by
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq (source H tails) (target H tails) x .callByValuePar .callByValueSeq
    (render H tails true e) (render H tails false e)
    (fun k => evaluator_eq H tails x k e x.length (Nat.le_refl _))]

theorem observations_iff (H : Header) (tails : List MExp) (e : MExp)
    (x : List Char) (r : Option (List Char)) :
    SObs (source H tails) .callByValuePar (render H tails true e) x r ↔
      SObs (target H tails) .callByValueSeq (render H tails false e) x r := by
  rw [←decideObsV_iff (source_firstOrder H tails) (by decide) (render_firstOrder H tails true e),
    ←decideObsV_iff (target_firstOrder H tails) (by decide) (render_firstOrder H tails false e),decide_eq]

theorem language_translation (H : Header) (tails : List MExp) (e : MExp) :
    ∃ (g : MGrammar) (entry : MExp), g.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs (source H tails) .callByValuePar (render H tails true e) x (some []) ↔
        SObs g .callByValueSeq entry x (some []) :=
  ⟨target H tails,render H tails false e,target_firstOrder H tails,render_firstOrder H tails false e,
    fun x => observations_iff H tails e x (some [])⟩

end Shallot.MacroPeg.CBV.RuntimePrefixGrammar
