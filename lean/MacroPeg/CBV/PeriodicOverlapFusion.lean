import MacroPeg.CBV.BlockCapture
import MacroPeg.CBV.RecursivePrefixFusion

/-! Shift a periodic capture by a fixed word and rotate the target residual.
The capture and source prefix need not commute. -/
namespace Shallot.MacroPeg.CBV.PeriodicOverlapFusion
open NestedScannerArguments (scan scan_eval accepts)
structure Spec where
  core : MExp
  left : List Char
  right : List Char
  tail : MExp
def head (r : Spec) : MExp := .seq r.core (.lit r.left)
def before (r : Spec) : List Char := r.left ++ r.right
def after (r : Spec) : List Char := r.right ++ r.left
open RecursiveParserStability (Lexical Installed pick floor frozen lexical_firstOrder frozen_lexical_eval)
open ClockFreezing (Table)

structure Valid (bodies : List MExp) (specs : List Spec) : Prop where
  helpers : RecursiveParserStability.Valid bodies
  heads : ∀ r ∈ specs, Lexical bodies.length (head r)
  safeHeads : ∀ r ∈ specs, BlockCapture.Safe bodies.length (before r) r.core
  safeHelpers : ∀ r ∈ specs, ∀ e ∈ bodies, BlockCapture.Safe bodies.length (before r) e

/-- Raw zero-argument calls denote calls capturing the callee's fixed parser.
The actual source and target are ordinary arity-one first-order grammars. -/
def render (bodies : List MExp) (specs : List Spec) : MExp → MExp
  | .call i [] => match specs[i]? with
    | none => MExp.failAlways
    | some r => .call (bodies.length+i) [(head r)]
  | .call _ (_::_) => MExp.failAlways
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
    | some r => exact ⟨lexical_firstOrder _ _ (hf.heads r (List.mem_of_getElem? hr)),True.intro⟩
  | .call _ (_::_) => trivial
  | .seq a b | .alt a b => ⟨render_firstOrder hf a,render_firstOrder hf b⟩
  | .star a | .notP a => render_firstOrder hf a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

def parGrammar (bodies : List MExp) (specs : List Spec) : MGrammar :=
  ⟨bodies.map (fun e => ⟨0,e⟩) ++ specs.map (fun r => ⟨1,.seq (.seq (.lit (before r)) (.param 0)) (render bodies specs r.tail)⟩)⟩

def seqGrammar (bodies : List MExp) (specs : List Spec) : MGrammar :=
  ⟨bodies.map (fun e => ⟨0,e⟩) ++ specs.map (fun r => ⟨1,.seq (.lit (after r)) (render bodies specs r.tail)⟩)⟩

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
      (specs[i]?).map (fun r => ⟨1,.seq (.seq (.lit (before r)) (.param 0)) (render bodies specs r.tail)⟩) := by
  simp [parGrammar,ruleAtM_eq_getElem?,List.getElem?_append_right]

theorem seq_rule (bodies : List MExp) (specs : List Spec) (i : Nat) :
    ruleAtM (seqGrammar bodies specs).rules (bodies.length+i) =
      (specs[i]?).map (fun r => ⟨1,.seq (.lit (after r)) (render bodies specs r.tail)⟩) := by
  simp [seqGrammar,ruleAtM_eq_getElem?,List.getElem?_append_right]

theorem par_firstOrder {bodies : List MExp} {specs : List Spec} (hf : Valid bodies specs) :
    (parGrammar bodies specs).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    exact lexical_firstOrder _ e (hf.helpers e he)
  · obtain ⟨r,hr',rfl⟩ := List.mem_map.mp hr
    exact ⟨⟨True.intro,True.intro⟩,render_firstOrder hf r.tail⟩

theorem seq_firstOrder {bodies : List MExp} {specs : List Spec} (hf : Valid bodies specs) :
    (seqGrammar bodies specs).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    exact lexical_firstOrder _ e (hf.helpers e he)
  · obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨True.intro,render_firstOrder hf r.tail⟩

abbrev parTable (bodies : List MExp) (specs : List Spec) (x : List Char) (k : Nat) : Table :=
  frozen bodies (parGrammar bodies specs) x .callByValuePar k
abbrev seqTable (bodies : List MExp) (specs : List Spec) (x : List Char) (k : Nat) : Table :=
  frozen bodies (seqGrammar bodies specs) x .callByValueSeq k

def Shifted (bodies : List MExp) (specs : List Spec) (x : List Char) (T U : Table) : Prop :=
  ∀ i r, specs[i]? = some r → ∀ p q, p ≤ x.length → q ≤ x.length →
    evV (parGrammar bodies specs) x .callByValuePar T [] (head r) p = some (some q) →
    valAt (T (bodies.length+i) [pre x p q]) p = valAt (U (bodies.length+i) [pre x p q]) q

theorem evaluator_of_shift {bodies : List MExp} {specs : List Spec} (hf : Valid bodies specs) (x : List Char)
    (T U : Nat → List (List Char) → Val) (hOk : OkTV x.length T)
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
      have hPure := hf.heads r (List.mem_of_getElem? hr)
      have hpar : ruleAtM (parGrammar bodies specs).rules (bodies.length+i) = some ⟨1,.seq (.seq (.lit (before r)) (.param 0)) (render bodies specs r.tail)⟩ := by
        rw [par_rule,hr]; rfl
      have hseq : ruleAtM (seqGrammar bodies specs).rules (bodies.length+i) = some ⟨1,.seq (.lit (after r)) (render bodies specs r.tail)⟩ := by
        rw [seq_rule,hr]; rfl
      simp only [render,hr]
      rw [evV_call_par hpar rfl (by decide),evV_call_seq hseq rfl]
      simp only [evParArgs,evSeqArgs]
      rw [← hLex E E (head r) hPure p hp]
      cases hv : evV (parGrammar bodies specs) x .callByValuePar T E (head r) p with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some q =>
          dsimp only []
          apply hShift i r hr p q hp (evV_ok hOk (head r) p hp q hv)
          exact ((hLex [] E (head r) hPure p hp).trans (hLex E E (head r) hPure p hp).symm).trans hv
  | .seq a b, E, p, hp => by
    have hh := evaluator_of_shift hf x T U hOk hLex hShift a E p hp
    cases hv : evV (parGrammar bodies specs) x .callByValuePar T E (render bodies specs a) p with
    | none => simp only [render,evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => simp only [render,evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        simp only [render,evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_shift hf x T U hOk hLex hShift b E q (evV_ok hOk _ p hp q hv)
  | .alt a b, E, p, hp => by
    have hh := evaluator_of_shift hf x T U hOk hLex hShift a E p hp
    cases hv : evV (parGrammar bodies specs) x .callByValuePar T E (render bodies specs a) p with
    | none => simp only [render,evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some result => cases result with
      | none =>
        simp only [render,evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]
        exact evaluator_of_shift hf x T U hOk hLex hShift b E p hp
      | some q => simp only [render,evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | .star a, E, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift hf x T U hOk hLex hShift a E q (by omega))
  | .notP a, E, p, hp => by simp only [render,evV]; rw [evaluator_of_shift hf x T U hOk hLex hShift a E p hp]
  | .param _, _, _, _ | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _ | .range _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .call _ (_::_), _, _, _ | .dbg _, _, _, _ | .lam _ _, _, _, _
  | .callParam _ _, _, _, _ | .invoke _ _ _, _, _, _ => rfl

theorem lexical_eq {bodies : List MExp} {specs : List Spec} (hf : Valid bodies specs)
    (x : List Char) (k l : Nat) (E F : List (List Char)) (a : MExp)
    (ha : Lexical bodies.length a) (p : Nat) (hp : p ≤ x.length) :
    evV (parGrammar bodies specs) x .callByValuePar (parTable bodies specs x k) E a p =
      evV (seqGrammar bodies specs) x .callByValueSeq (seqTable bodies specs x l) F a p :=
  frozen_lexical_eval hf.helpers (par_installed bodies specs) (seq_installed bodies specs) x
    .callByValuePar .callByValueSeq k l E F a ha p hp

theorem tables_shifted {bodies : List MExp} {specs : List Spec} (hf : Valid bodies specs)
    (x : List Char) (k : Nat) :
    Shifted bodies specs x (parTable bodies specs x k) (seqTable bodies specs x k) := by
  induction k with
  | zero =>
    intro i r hr p q hp hq hv
    have huser : pick bodies (bodies.length+i) = false := by simp [pick]
    simp only [parTable,seqTable,frozen,ClockFreezing.frozen,huser,Bool.false_eq_true,if_false,valAt_nil]
  | succ k ih =>
    intro i r hr p q hp hq hv
    have hpar : ruleAtM (parGrammar bodies specs).rules (bodies.length+i) =
        some ⟨1,.seq (.seq (.lit (before r)) (.param 0)) (render bodies specs r.tail)⟩ := by rw [par_rule,hr]; rfl
    have hseq : ruleAtM (seqGrammar bodies specs).rules (bodies.length+i) =
        some ⟨1,.seq (.lit (after r)) (render bodies specs r.tail)⟩ := by rw [seq_rule,hr]; rfl
    have huser : pick bodies (bodies.length+i) = false := by simp [pick]
    change valAt (ClockFreezing.frozen (parGrammar bodies specs) x .callByValuePar
        (pick bodies) (floor bodies x) (k+1) (bodies.length+i) [pre x p q]) p =
      valAt (ClockFreezing.frozen (seqGrammar bodies specs) x .callByValueSeq
        (pick bodies) (floor bodies x) (k+1) (bodies.length+i) [pre x p q]) q
    rw [ClockFreezing.frozen_user_step _ _ _ _ _ k _ huser _ hpar _ _ hp,
      ClockFreezing.frozen_user_step _ _ _ _ _ k _ huser _ hseq _ _ hq]
    have hpref : evV (parGrammar bodies specs) x .callByValuePar
        (parTable bodies specs x k) [] (head r) p = some (some q) := by
      rw [frozen_lexical_eval hf.helpers (par_installed bodies specs) (par_installed bodies specs) x
        .callByValuePar .callByValuePar k (k+1) [] [] (head r)
        (hf.heads r (List.mem_of_getElem? hr)) p hp]
      exact hv
    obtain ⟨n,hform⟩ := BlockCapture.head_capture (par_installed bodies specs) (before r) r.left x
      (parTable bodies specs x k)
      (BlockCapture.frozen_rows_safe (par_installed bodies specs) (before r)
        (hf.safeHelpers r (List.mem_of_getElem? hr)) x .callByValuePar k)
      (ClockFreezing.frozen_ok _ _ _ _ _ k)
      (ClockFreezing.frozen_sound (par_firstOrder hf) x .callByValuePar (by decide) _ _ k)
      r.core (lexical_firstOrder _ _ (hf.heads r (List.mem_of_getElem? hr)).1)
      (hf.safeHeads r (List.mem_of_getElem? hr)) p q hp hpref
    have hrotate : before r ++ pre x p q = pre x p q ++ after r := by
      rw [hform]
      exact BlockCapture.rotate r.left r.right n
    have hword := (ReplayFusion.success_prefix
      (ClockFreezing.frozen_sound (par_firstOrder hf) x .callByValuePar (by decide) _ _ k)
      [] (head r) (lexical_firstOrder _ _ (hf.heads r (List.mem_of_getElem? hr))) p q hp hpref).2
    have hparam : evV (parGrammar bodies specs) x .callByValuePar
        (parTable bodies specs x k) [pre x p q] (.param 0) p = some (some q) := by
      simp only [evV,List.getElem?_cons_zero,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hword,length_sfx x hq]
    have hs : evV (parGrammar bodies specs) x .callByValuePar (parTable bodies specs x k) [pre x p q]
        (.seq (.lit (before r)) (.param 0)) p =
      evV (seqGrammar bodies specs) x .callByValueSeq (seqTable bodies specs x k) [pre x p q]
        (.lit (after r)) q := by
      rw [BlockCapture.prefix_rotate _ _ _ _ _ _ _ hrotate p,
        evV_seq_ok hparam]
      rfl
    change (match evV (parGrammar bodies specs) x .callByValuePar (parTable bodies specs x k) [pre x p q]
        (.seq (.lit (before r)) (.param 0)) p with
      | some (some z) => evV (parGrammar bodies specs) x .callByValuePar (parTable bodies specs x k)
          [pre x p q] (render bodies specs r.tail) z
      | other => other) = _
    rw [hs]
    cases hu : evV (seqGrammar bodies specs) x .callByValueSeq (seqTable bodies specs x k) [pre x p q]
        (.lit (after r)) q with
    | none => simp only [evV_seq_none hu]
    | some result => cases result with
      | none => simp only [evV_seq_fail hu]
      | some z =>
        rw [evV_seq_ok hu]
        exact evaluator_of_shift hf x _ _ (ClockFreezing.frozen_ok _ _ _ _ _ k)
          (fun E F a ha p hp => lexical_eq hf x k k E F a ha p hp) ih r.tail [pre x p q] z
          (evV_ok (ClockFreezing.frozen_ok _ _ _ _ _ k) _ q hq z hu)

theorem evaluator_eq {bodies : List MExp} {specs : List Spec} (hf : Valid bodies specs)
    (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp) (p : Nat) (hp : p ≤ x.length) :
    evV (parGrammar bodies specs) x .callByValuePar (parTable bodies specs x k) E (render bodies specs e) p =
      evV (seqGrammar bodies specs) x .callByValueSeq (seqTable bodies specs x k) E (render bodies specs e) p :=
  evaluator_of_shift hf x _ _ (ClockFreezing.frozen_ok _ _ _ _ _ k)
    (fun E F a ha p hp => lexical_eq hf x k k E F a ha p hp) (tables_shifted hf x k) e E p hp

/-- The lexical floor is only a proof device. This theorem concerns actual
finite observations of the two installed grammars on the original strings. -/
theorem observations_iff {bodies : List MExp} {specs : List Spec} (hf : Valid bodies specs)
    (e : MExp) (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar bodies specs) .callByValuePar (render bodies specs e) x r ↔
      SObs (seqGrammar bodies specs) .callByValueSeq (render bodies specs e) x r := by
  rw [ClockFreezing.observations_iff (par_firstOrder hf) x .callByValuePar (by decide)
      (pick bodies) (floor bodies x) (RecursiveParserStability.helpers_stable hf.helpers (par_installed bodies specs) x .callByValuePar)
      (render bodies specs e) (render_firstOrder hf e) r,
    ClockFreezing.observations_iff (seq_firstOrder hf) x .callByValueSeq (by decide)
      (pick bodies) (floor bodies x) (RecursiveParserStability.helpers_stable hf.helpers (seq_installed bodies specs) x .callByValueSeq)
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

def blockBody : MExp := .alt (.seq (.lit ['a','b']) (.seq (.call 0 []) (.lit ['a','b']))) (.lit ['a','b'])

def exampleSpec : Spec := ⟨.call 0 [],['a'],['b'],
  .seq (.chr '#') (.seq (.param 0)
    (.alt (.seq (.chr '!') (.call 0 [])) (.notP .any)))⟩

theorem example_valid : Valid [blockBody] [exampleSpec] := by
  constructor
  · intro e he
    simp only [List.mem_singleton] at he
    subst e
    simp [blockBody,Lexical]
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    simp [exampleSpec,head,Lexical]
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    simp [exampleSpec,before,BlockCapture.Safe]
  · intro r hr e he
    simp only [List.mem_singleton] at hr he
    subst r; subst e
    have hb : BlockCapture.Safe 1 ['a','b'] (.lit ['a','b']) := ⟨1,rfl⟩
    exact ⟨⟨hb,⟨by change 0 < 1; decide,hb⟩⟩,hb⟩

/-- A real 27-character capture starts replay two characters into its old
interval. Seq must use ba, rather than ab, after capturing it. The retained
word is reused after #, then recursion obtains an 11-character fresh capture. -/
theorem rotated_overlap_execution :
    let bodies := [blockBody]
    let specs := [exampleSpec]
    let e := render bodies specs (.call 0 [])
    let w := BlockCapture.copies ['a','b'] 13 ++ ['a']
    let good := BlockCapture.copies ['a','b'] 14 ++ 'a'::'#'::(w ++ '!'::
      (BlockCapture.copies ['a','b'] 6 ++ 'a'::'#'::(BlockCapture.copies ['a','b'] 5 ++ ['a'])))
    let bad := BlockCapture.copies ['a','b'] 14 ++ 'b'::'#'::w
    (evParArgs (parGrammar bodies specs) good .callByValuePar
      (tblV (parGrammar bodies specs) good .callByValuePar 18) [] [head exampleSpec] good.length = some (some [w])) ∧
    (evV (parGrammar bodies specs) good .callByValuePar
      (tblV (parGrammar bodies specs) good .callByValuePar 18) [] e good.length = some (some 0)) ∧
    (evV (seqGrammar bodies specs) good .callByValueSeq
      (tblV (seqGrammar bodies specs) good .callByValueSeq 18) [] e good.length = some (some 0)) ∧
    (evV (seqGrammar bodies specs) good .callByValueSeq
      (tblV (seqGrammar bodies specs) good .callByValueSeq 18) [w]
      (.lit ['a','b']) (good.length-w.length) = some none) ∧
    (evV (parGrammar bodies specs) bad .callByValuePar
      (tblV (parGrammar bodies specs) bad .callByValuePar 18) [] e bad.length = some none) ∧
    (evV (seqGrammar bodies specs) bad .callByValueSeq
      (tblV (seqGrammar bodies specs) bad .callByValueSeq 18) [] e bad.length = some none) := by
  decide +kernel

end Shallot.MacroPeg.CBV.PeriodicOverlapFusion
