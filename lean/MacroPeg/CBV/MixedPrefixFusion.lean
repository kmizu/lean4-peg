import MacroPeg.CBV.RecursivePrefixFusion

/-! Mix fresh independent recursive captures with unrestricted replay-call
arguments, including captured parameters and recursive argument computations. -/
namespace Shallot.MacroPeg.CBV.MixedPrefixFusion
open RecursiveParserStability (Lexical Installed pick floor frozen lexical_firstOrder frozen_lexical_eval)
open ClockFreezing (Table)

structure Spec where
  head : Option MExp
  tail : MExp

/-- No parser head means ordinary replay of the actual captured parameter. -/
def entry (r : Spec) : MExp := r.head.getD (.param 0)

def Valid (bodies : List MExp) (specs : List Spec) : Prop :=
  RecursiveParserStability.Valid bodies ∧
    ∀ r ∈ specs, ∀ a, r.head = some a → Lexical bodies.length a

/-- A raw empty argument list invokes a fixed-parser rule. A raw unary
argument invokes a replay rule and can be an arbitrary recursive expression. -/
def render (bodies : List MExp) (specs : List Spec) : MExp → MExp
  | .call i [] => match specs[i]? with
    | some r => match r.head with
      | some a => .call (bodies.length+i) [a]
      | none => MExp.failAlways
    | none => MExp.failAlways
  | .call i [a] => match specs[i]? with
    | some r => match r.head with
      | none => .call (bodies.length+i) [render bodies specs a]
      | some _ => MExp.failAlways
    | none => MExp.failAlways
  | .call _ (_::_::_) => MExp.failAlways
  | .seq a b => .seq (render bodies specs a) (render bodies specs b)
  | .alt a b => .alt (render bodies specs a) (render bodies specs b)
  | .star a => .star (render bodies specs a)
  | .notP a => .notP (render bodies specs a)
  | .param k => .param k
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit w => .lit w
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

theorem render_firstOrder {bodies : List MExp} {specs : List Spec} (hf : Valid bodies specs) :
    ∀ e, (render bodies specs e).FirstOrder
  | .call i [] => by
    simp only [render]
    cases hr : specs[i]? with
    | none => trivial
    | some r =>
      dsimp only []
      cases ha : r.head with
      | none => trivial
      | some a => exact ⟨lexical_firstOrder _ _ (hf.2 r (List.mem_of_getElem? hr) a ha),True.intro⟩
  | .call i [a] => by
    simp only [render]
    cases hr : specs[i]? with
    | none => trivial
    | some r =>
      dsimp only []
      cases r.head with
      | none => exact ⟨render_firstOrder hf a,True.intro⟩
      | some _ => trivial
  | .call _ (_::_::_) => trivial
  | .seq a b | .alt a b => ⟨render_firstOrder hf a,render_firstOrder hf b⟩
  | .star a | .notP a => render_firstOrder hf a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

def parGrammar (bodies : List MExp) (specs : List Spec) : MGrammar :=
  ⟨bodies.map (fun e => ⟨0,e⟩) ++ specs.map (fun r => ⟨1,.seq (entry r) (render bodies specs r.tail)⟩)⟩

def seqGrammar (bodies : List MExp) (specs : List Spec) : MGrammar :=
  ⟨bodies.map (fun e => ⟨0,e⟩) ++ specs.map (fun r => ⟨1,render bodies specs r.tail⟩)⟩

def lift (specs : List ParserPrefixFusion.Spec) : List Spec :=
  specs.map (fun r => ⟨some r.head,r.tail⟩)

theorem render_lift (bodies : List MExp) (specs : List ParserPrefixFusion.Spec) :
    ∀ e, render bodies (lift specs) e = RecursivePrefixFusion.render bodies specs e
  | .call i [] | .call i [_] => by
    simp only [render,RecursivePrefixFusion.render,lift,List.getElem?_map]
    cases specs[i]? <;> rfl
  | .seq a b | .alt a b => by simp only [render,RecursivePrefixFusion.render,render_lift bodies specs a,render_lift bodies specs b]
  | .star a | .notP a => by simp only [render,RecursivePrefixFusion.render,render_lift bodies specs a]
  | .call _ (_::_::_) | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ | .dbg _
  | .lam _ _ | .callParam _ _ | .invoke _ _ _ => rfl

theorem grammars_lift (bodies : List MExp) (specs : List ParserPrefixFusion.Spec) :
    parGrammar bodies (lift specs) = RecursivePrefixFusion.parGrammar bodies specs ∧
      seqGrammar bodies (lift specs) = RecursivePrefixFusion.seqGrammar bodies specs := by
  have hrender := render_lift bodies specs
  simp only [lift] at hrender
  simp only [parGrammar,seqGrammar,RecursivePrefixFusion.parGrammar,RecursivePrefixFusion.seqGrammar,
    lift,List.map_map,Function.comp_def,entry,Option.getD_some,hrender,and_self]

theorem valid_lift (bodies : List MExp) (specs : List ParserPrefixFusion.Spec) :
    Valid bodies (lift specs) ↔ RecursivePrefixFusion.Valid bodies specs := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    intro r hr
    exact h.2 ⟨some r.head,r.tail⟩ (List.mem_map.mpr ⟨r,hr,rfl⟩) r.head rfl
  · intro h
    refine ⟨h.1,?_⟩
    intro r hr a ha
    obtain ⟨r,hr',rfl⟩ := List.mem_map.mp hr
    cases ha
    exact h.2 r hr'

theorem par_installed (bodies : List MExp) (specs : List Spec) : Installed bodies (parGrammar bodies specs) := by
  intro i e hi
  have hb : i<bodies.length := List.getElem?_eq_some_iff.mp hi |>.1
  simp only [parGrammar,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hb)]
  simp [hi]

theorem seq_installed (bodies : List MExp) (specs : List Spec) : Installed bodies (seqGrammar bodies specs) := by
  intro i e hi
  have hb : i<bodies.length := List.getElem?_eq_some_iff.mp hi |>.1
  simp only [seqGrammar,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hb)]
  simp [hi]

theorem par_rule (bodies : List MExp) (specs : List Spec) (i : Nat) :
    ruleAtM (parGrammar bodies specs).rules (bodies.length+i) =
      (specs[i]?).map (fun r => ⟨1,.seq (entry r) (render bodies specs r.tail)⟩) := by
  simp [parGrammar,ruleAtM_eq_getElem?,List.getElem?_append_right]

theorem seq_rule (bodies : List MExp) (specs : List Spec) (i : Nat) :
    ruleAtM (seqGrammar bodies specs).rules (bodies.length+i) =
      (specs[i]?).map (fun r => ⟨1,render bodies specs r.tail⟩) := by
  simp [seqGrammar,ruleAtM_eq_getElem?,List.getElem?_append_right]

theorem par_firstOrder {bodies : List MExp} {specs : List Spec} (hf : Valid bodies specs) :
    (parGrammar bodies specs).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    exact lexical_firstOrder _ e (hf.1 e he)
  · obtain ⟨r,hr',rfl⟩ := List.mem_map.mp hr
    refine ⟨?_,render_firstOrder hf r.tail⟩
    cases ha : r.head with
    | none => simp only [entry,ha,Option.getD_none]; trivial
    | some a => simpa only [entry,ha,Option.getD_some] using lexical_firstOrder _ a (hf.2 r hr' a ha)

theorem seq_firstOrder {bodies : List MExp} {specs : List Spec} (hf : Valid bodies specs) :
    (seqGrammar bodies specs).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    exact lexical_firstOrder _ e (hf.1 e he)
  · obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    exact render_firstOrder hf r.tail

abbrev parTable (bodies : List MExp) (specs : List Spec) (x : List Char) (k : Nat) : Table :=
  frozen bodies (parGrammar bodies specs) x .callByValuePar k
abbrev seqTable (bodies : List MExp) (specs : List Spec) (x : List Char) (k : Nat) : Table :=
  frozen bodies (seqGrammar bodies specs) x .callByValueSeq k

def Ready (bodies : List MExp) (specs : List Spec) (x : List Char) (T : Table)
    (r : Spec) (w : List Char) (p q : Nat) : Prop := match r.head with
  | none => sfx x p = w ++ sfx x q
  | some a => w = pre x p q ∧ evV (parGrammar bodies specs) x .callByValuePar T [] a p = some (some q)

def Shifted (bodies : List MExp) (specs : List Spec) (x : List Char) (T U : Table) : Prop :=
  ∀ i r, specs[i]? = some r → ∀ w p q, p ≤ x.length → q ≤ x.length → Ready bodies specs x T r w p q →
    valAt (T (bodies.length+i) [w]) p = valAt (U (bodies.length+i) [w]) q

theorem evaluator_of_shift {bodies : List MExp} {specs : List Spec} (hf : Valid bodies specs) (x : List Char)
    (T U : Nat → List (List Char) → Val) (hT : SoundTV (parGrammar bodies specs) x .callByValuePar T) (hOk : OkTV x.length T)
    (hLex : ∀ E F a, Lexical bodies.length a → ∀ p, p ≤ x.length →
      evV (parGrammar bodies specs) x .callByValuePar T E a p =
        evV (seqGrammar bodies specs) x .callByValueSeq U F a p)
    (hShift : Shifted bodies specs x T U) :
    ∀ e E p, p ≤ x.length →
      evV (parGrammar bodies specs) x .callByValuePar T E (render bodies specs e) p =
        evV (seqGrammar bodies specs) x .callByValueSeq U E (render bodies specs e) p
  | .call i [], E, p, hp => by
    cases hr : specs[i]? with
    | none => simp only [render,hr]; rfl
    | some r =>
      cases ha : r.head with
      | none => simp only [render,hr,ha]; rfl
      | some a =>
        have hPure := hf.2 r (List.mem_of_getElem? hr) a ha
        have hpar : ruleAtM (parGrammar bodies specs).rules (bodies.length+i) = some ⟨1,.seq (entry r) (render bodies specs r.tail)⟩ := by
          rw [par_rule,hr]; rfl
        have hseq : ruleAtM (seqGrammar bodies specs).rules (bodies.length+i) = some ⟨1,render bodies specs r.tail⟩ := by
          rw [seq_rule,hr]; rfl
        simp only [render,hr,ha]
        rw [evV_call_par hpar rfl (by decide),evV_call_seq hseq rfl]
        simp only [evParArgs,evSeqArgs]
        rw [← hLex E E a hPure p hp]
        cases hv : evV (parGrammar bodies specs) x .callByValuePar T E a p with
        | none => rfl
        | some result => cases result with
          | none => rfl
          | some q =>
            dsimp only []
            apply hShift i r hr (pre x p q) p q hp (evV_ok hOk a p hp q hv)
            simp only [Ready,ha]
            exact ⟨True.intro,((hLex [] E a hPure p hp).trans (hLex E E a hPure p hp).symm).trans hv⟩
  | .call i [a], E, p, hp => by
    cases hr : specs[i]? with
    | none => simp only [render,hr]; rfl
    | some r =>
      cases ha : r.head with
      | some _ => simp only [render,hr,ha]; rfl
      | none =>
        have hpar : ruleAtM (parGrammar bodies specs).rules (bodies.length+i) = some ⟨1,.seq (entry r) (render bodies specs r.tail)⟩ := by
          rw [par_rule,hr]; rfl
        have hseq : ruleAtM (seqGrammar bodies specs).rules (bodies.length+i) = some ⟨1,render bodies specs r.tail⟩ := by
          rw [seq_rule,hr]; rfl
        have heq := evaluator_of_shift hf x T U hT hOk hLex hShift a E p hp
        simp only [render,hr,ha]
        rw [evV_call_par hpar rfl (by decide),evV_call_seq hseq rfl]
        simp only [evParArgs,evSeqArgs]
        rw [← heq]
        cases hv : evV (parGrammar bodies specs) x .callByValuePar T E (render bodies specs a) p with
        | none => rfl
        | some result => cases result with
          | none => rfl
          | some q =>
            dsimp only []
            obtain ⟨hq,hpre⟩ := ReplayFusion.success_prefix hT E (render bodies specs a) (render_firstOrder hf a) p q hp hv
            apply hShift i r hr (pre x p q) p q hp hq
            simpa only [Ready,ha] using hpre
  | .seq a b, E, p, hp => by
    have hh := evaluator_of_shift hf x T U hT hOk hLex hShift a E p hp
    cases hv : evV (parGrammar bodies specs) x .callByValuePar T E (render bodies specs a) p with
    | none => simp only [render,evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => simp only [render,evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        simp only [render,evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_shift hf x T U hT hOk hLex hShift b E q (evV_ok hOk _ p hp q hv)
  | .alt a b, E, p, hp => by
    have hh := evaluator_of_shift hf x T U hT hOk hLex hShift a E p hp
    cases hv : evV (parGrammar bodies specs) x .callByValuePar T E (render bodies specs a) p with
    | none => simp only [render,evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some result => cases result with
      | none =>
        simp only [render,evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]
        exact evaluator_of_shift hf x T U hT hOk hLex hShift b E p hp
      | some q => simp only [render,evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | .star a, E, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift hf x T U hT hOk hLex hShift a E q (by omega))
  | .notP a, E, p, hp => by simp only [render,evV]; rw [evaluator_of_shift hf x T U hT hOk hLex hShift a E p hp]
  | .param _, _, _, _ | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _ | .range _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .call _ (_::_::_), _, _, _ | .dbg _, _, _, _ | .lam _ _, _, _, _
  | .callParam _ _, _, _, _ | .invoke _ _ _, _, _, _ => rfl

theorem lexical_eq {bodies : List MExp} {specs : List Spec} (hf : Valid bodies specs)
    (x : List Char) (k l : Nat) (E F : List (List Char)) (a : MExp)
    (ha : Lexical bodies.length a) (p : Nat) (hp : p ≤ x.length) :
    evV (parGrammar bodies specs) x .callByValuePar (parTable bodies specs x k) E a p =
      evV (seqGrammar bodies specs) x .callByValueSeq (seqTable bodies specs x l) F a p :=
  frozen_lexical_eval hf.1 (par_installed bodies specs) (seq_installed bodies specs) x
    .callByValuePar .callByValueSeq k l E F a ha p hp

theorem tables_shifted {bodies : List MExp} {specs : List Spec} (hf : Valid bodies specs)
    (x : List Char) (k : Nat) :
    Shifted bodies specs x (parTable bodies specs x k) (seqTable bodies specs x k) := by
  induction k with
  | zero =>
    intro i r hr w p q hp hq hv
    have huser : pick bodies (bodies.length+i) = false := by simp [pick]
    simp only [parTable,seqTable,frozen,ClockFreezing.frozen,huser,Bool.false_eq_true,if_false,valAt_nil]
  | succ k ih =>
    intro i r hr w p q hp hq hv
    have hpar : ruleAtM (parGrammar bodies specs).rules (bodies.length+i) =
        some ⟨1,.seq (entry r) (render bodies specs r.tail)⟩ := by rw [par_rule,hr]; rfl
    have hseq : ruleAtM (seqGrammar bodies specs).rules (bodies.length+i) =
        some ⟨1,render bodies specs r.tail⟩ := by rw [seq_rule,hr]; rfl
    have huser : pick bodies (bodies.length+i) = false := by simp [pick]
    change valAt (ClockFreezing.frozen (parGrammar bodies specs) x .callByValuePar
        (pick bodies) (floor bodies x) (k+1) (bodies.length+i) [w]) p =
      valAt (ClockFreezing.frozen (seqGrammar bodies specs) x .callByValueSeq
        (pick bodies) (floor bodies x) (k+1) (bodies.length+i) [w]) q
    rw [ClockFreezing.frozen_user_step _ _ _ _ _ k _ huser _ hpar _ _ hp,
      ClockFreezing.frozen_user_step _ _ _ _ _ k _ huser _ hseq _ _ hq]
    have hpref : evV (parGrammar bodies specs) x .callByValuePar
        (parTable bodies specs x k) [w] (entry r) p = some (some q) := by
      cases ha : r.head with
      | none =>
        have hs : sfx x p = w ++ sfx x q := by simpa only [Ready,ha] using hv
        simp only [entry,ha,Option.getD_none,evV,List.getElem?_cons_zero,
          (CBVtoCBN.stripPrefix_exact w _ _).mpr hs,length_sfx x hq]
      | some a =>
        have hh : evV (parGrammar bodies specs) x .callByValuePar
            (parTable bodies specs x (k+1)) [] a p = some (some q) := by
          exact (show w=pre x p q ∧ _ from (by simpa only [Ready,ha] using hv)).2
        simp only [entry,ha,Option.getD_some]
        rw [frozen_lexical_eval hf.1 (par_installed bodies specs) (par_installed bodies specs) x
          .callByValuePar .callByValuePar k (k+1) [w] [] a
          (hf.2 r (List.mem_of_getElem? hr) a ha) p hp]
        exact hh
    rw [evV_seq_ok hpref]
    exact evaluator_of_shift hf x _ _
      (ClockFreezing.frozen_sound (par_firstOrder hf) x .callByValuePar (by decide) _ _ k)
      (ClockFreezing.frozen_ok _ _ _ _ _ k)
      (fun E F a ha p hp => lexical_eq hf x k k E F a ha p hp) ih r.tail [w] q hq

theorem evaluator_eq {bodies : List MExp} {specs : List Spec} (hf : Valid bodies specs)
    (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp) (p : Nat) (hp : p ≤ x.length) :
    evV (parGrammar bodies specs) x .callByValuePar (parTable bodies specs x k) E (render bodies specs e) p =
      evV (seqGrammar bodies specs) x .callByValueSeq (seqTable bodies specs x k) E (render bodies specs e) p :=
  evaluator_of_shift hf x _ _
    (ClockFreezing.frozen_sound (par_firstOrder hf) x .callByValuePar (by decide) _ _ k)
    (ClockFreezing.frozen_ok _ _ _ _ _ k)
    (fun E F a ha p hp => lexical_eq hf x k k E F a ha p hp) (tables_shifted hf x k) e E p hp

/-- The lexical floor is only a proof device. This theorem concerns actual
finite observations of the two installed grammars on the original strings. -/
theorem observations_iff {bodies : List MExp} {specs : List Spec} (hf : Valid bodies specs)
    (e : MExp) (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar bodies specs) .callByValuePar (render bodies specs e) x r ↔
      SObs (seqGrammar bodies specs) .callByValueSeq (render bodies specs e) x r := by
  rw [ClockFreezing.observations_iff (par_firstOrder hf) x .callByValuePar (by decide)
      (pick bodies) (floor bodies x) (RecursiveParserStability.helpers_stable hf.1 (par_installed bodies specs) x .callByValuePar)
      (render bodies specs e) (render_firstOrder hf e) r,
    ClockFreezing.observations_iff (seq_firstOrder hf) x .callByValueSeq (by decide)
      (pick bodies) (floor bodies x) (RecursiveParserStability.helpers_stable hf.1 (seq_installed bodies specs) x .callByValueSeq)
      (render bodies specs e) (render_firstOrder hf e) r]
  constructor
  · rintro ⟨k,v,hv,hr⟩
    exact ⟨k,v,(evaluator_eq hf x k [] e x.length (Nat.le_refl _)).symm.trans hv,hr⟩
  · rintro ⟨k,v,hv,hr⟩
    exact ⟨k,v,(evaluator_eq hf x k [] e x.length (Nat.le_refl _)).trans hv,hr⟩

theorem language_translation {bodies : List MExp} {specs : List Spec} (hf : Valid bodies specs) (e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (parGrammar bodies specs) .callByValuePar (render bodies specs e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar bodies specs,render bodies specs e,seq_firstOrder hf,render_firstOrder hf e,
    fun x => observations_iff hf e x (some [])⟩

def exampleSpecs : List Spec := [
  ⟨some (.call 0 []),.seq (.chr '#')
    (.call 1 [.seq (.notP (.call 2 [.param 0]))
      (.alt (.seq (.param 0) (.param 0)) (.param 0))])⟩,
  ⟨none,RootObservation.branch (.andP (.chr '!')) (.seq (.chr '!') (.call 0 [])) .eps⟩,
  ⟨none,.chr '?'⟩]

theorem example_valid : Valid [RecursivePrefixFusion.balancedBody] exampleSpecs := by
  constructor
  · exact RecursivePrefixFusion.balanced_valid.1
  · intro r hr a ha
    simp only [exampleSpecs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · cases ha
      simp [Lexical]
    · cases ha
    · cases ha

/-- Fresh recursive captures feed parameter-dependent, user-recursive
arguments; those replay calls then re-enter a fresh-parser rule. The probe
inside negation must retain the caller's capture and position as well. -/
theorem mixed_recursive_capture_execution :
    let bodies := [RecursivePrefixFusion.balancedBody]
    let e := render bodies exampleSpecs (.call 0 [])
    let good := "ab#abab!aabb#aabbaabb".toList
    let bad := "ab#abab!aabb#babbaabb".toList
    (evV (parGrammar bodies exampleSpecs) good .callByValuePar
      (tblV (parGrammar bodies exampleSpecs) good .callByValuePar 8) [] e good.length = some (some 0)) ∧
    (evV (seqGrammar bodies exampleSpecs) good .callByValueSeq
      (tblV (seqGrammar bodies exampleSpecs) good .callByValueSeq 8) [] e good.length = some (some 0)) ∧
    (evV (parGrammar bodies exampleSpecs) bad .callByValuePar
      (tblV (parGrammar bodies exampleSpecs) bad .callByValuePar 8) [] e bad.length = some none) ∧
    (evV (seqGrammar bodies exampleSpecs) bad .callByValueSeq
      (tblV (seqGrammar bodies exampleSpecs) bad .callByValueSeq 8) [] e bad.length = some none) := by
  decide +kernel

/-- An undefined user-recursive query inside an argument predicate cannot
fall through to the next argument choice, under either actual grammar. -/
theorem recursive_argument_choice_undefined (x : List Char) (k : Nat) :
    let specs : List Spec := [⟨none,.call 0 [.param 0]⟩]
    let raw := MExp.call 0 [.alt (.notP (.call 0 [.eps])) (.lit [])]
    let e := render [] specs raw
    evV (parGrammar [] specs) x .callByValuePar (tblV (parGrammar [] specs) x .callByValuePar k) [] e x.length = none ∧
    evV (seqGrammar [] specs) x .callByValueSeq (tblV (seqGrammar [] specs) x .callByValueSeq k) [] e x.length = none := by
  let specs : List Spec := [⟨none,.call 0 [.param 0]⟩]
  let gp := parGrammar [] specs
  let gs := seqGrammar [] specs
  have hp : ruleAtM gp.rules 0 = some ⟨1,.seq (.param 0) (.call 0 [.param 0])⟩ := rfl
  have hs : ruleAtM gs.rules 0 = some ⟨1,.call 0 [.param 0]⟩ := rfl
  have hrows : ∀ j p, p ≤ x.length →
      valAt (tblV gp x .callByValuePar j 0 [[]]) p = none ∧
        valAt (tblV gs x .callByValueSeq j 0 [[]]) p = none := by
    intro j
    induction j with
    | zero => intro p hp'; exact ⟨rfl,rfl⟩
    | succ j ih =>
      intro p hp'
      rw [valAt_tblV_succ hp [[]] hp',valAt_tblV_succ hs [[]] hp']
      simpa only [evV,hp,hs,List.getElem?_cons_zero,Shallot.stripPrefix?,length_sfx x hp',
        List.length_cons,List.length_nil,ite_true,evParArgs,evSeqArgs,pre,Nat.sub_self,List.take_zero]
        using ih p hp'
  have hloopP : evV gp x .callByValuePar (tblV gp x .callByValuePar k) [] (.call 0 [.eps]) x.length = none := by
    simpa only [evV,hp,List.length_cons,List.length_nil,ite_true,evParArgs,pre,Nat.sub_self,List.take_zero]
      using (hrows k x.length (Nat.le_refl _)).1
  have hloopS : evV gs x .callByValueSeq (tblV gs x .callByValueSeq k) [] (.call 0 [.eps]) x.length = none := by
    simpa only [evV,hs,List.length_cons,List.length_nil,ite_true,evSeqArgs,pre,Nat.sub_self,List.take_zero]
      using (hrows k x.length (Nat.le_refl _)).2
  change evV gp x .callByValuePar (tblV gp x .callByValuePar k) []
      (.call 0 [.alt (.notP (.call 0 [.eps])) (.lit [])]) x.length = none ∧
    evV gs x .callByValueSeq (tblV gs x .callByValueSeq k) []
      (.call 0 [.alt (.notP (.call 0 [.eps])) (.lit [])]) x.length = none
  rw [evV_call_par hp rfl (by decide),evV_call_seq hs rfl]
  have hargP : evV gp x .callByValuePar (tblV gp x .callByValuePar k) []
      (.alt (.notP (.call 0 [.eps])) (.lit [])) x.length = none :=
    evV_alt_none (evV_not_none hloopP)
  have hargS : evV gs x .callByValueSeq (tblV gs x .callByValueSeq k) []
      (.alt (.notP (.call 0 [.eps])) (.lit [])) x.length = none :=
    evV_alt_none (evV_not_none hloopS)
  rw [evPar_cons_none hargP,evSeq_cons_none hargS]
  exact ⟨rfl,rfl⟩

end Shallot.MacroPeg.CBV.MixedPrefixFusion
