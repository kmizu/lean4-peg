import MacroPeg.CBV.WordSelectionBoundary

/-! Recomputing a closed argument parser at the start of the Par body can
be fused with Seq argument evaluation. Fresh captures need no Word palette. -/
namespace Shallot.MacroPeg.CBV.ParserPrefixFusion

/-- Closed call-free PEGs may contain arbitrary choice, predicates, and
consuming repetition. Nullable repetition is allowed and remains undefined. -/
def Pure : MExp → Prop
  | .seq a b | .alt a b => Pure a ∧ Pure b
  | .star a | .notP a => Pure a
  | .eps | .any | .chr _ | .range _ _ | .lit _ => True
  | _ => False

theorem pure_firstOrder : ∀ a, Pure a → a.FirstOrder
  | .seq a b, h | .alt a b, h => ⟨pure_firstOrder a h.1,pure_firstOrder b h.2⟩
  | .star a, h | .notP a, h => pure_firstOrder a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
  | .param _, h | .call _ _, h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem pure_eval (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E F : List (List Char)) :
    ∀ a, Pure a → ∀ p, evV g x s T E a p = evV h x t U F a p
  | .seq a b, ha, p | .alt a b, ha, p => by
    simp only [evV,pure_eval g h x s t T U E F a ha.1 p]
    split <;> first | rfl | exact pure_eval g h x s t T U E F b ha.2 _
  | .notP a, ha, p => by simp only [evV,pure_eval g h x s t T U E F a ha p]
  | .star a, ha, p => by
    rw [evV_star,evV_star]
    exact evStar_congr p (fun q _ => pure_eval g h x s t T U E F a ha q)
  | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _ => rfl
  | .param _, h, _ | .call _ _, h, _ | .dbg _, h, _ | .lam _ _, h, _
  | .callParam _ _, h, _ | .invoke _ _ _, h, _ => False.elim h

structure Spec where
  head : MExp
  tail : MExp

/-- Raw zero-argument calls denote calls capturing the callee's fixed parser.
The actual source and target are ordinary arity-one first-order grammars. -/
def render (specs : List Spec) : MExp → MExp
  | .call i [] => match specs[i]? with
    | none => MExp.failAlways
    | some r => .call i [r.head]
  | .call _ (_::_) => MExp.failAlways
  | .seq a b => .seq (render specs a) (render specs b)
  | .alt a b => .alt (render specs a) (render specs b)
  | .star a => .star (render specs a)
  | .notP a => .notP (render specs a)
  | .param k => .param k
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit w => .lit w
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

def Valid (specs : List Spec) : Prop := ∀ r ∈ specs, Pure r.head

theorem render_firstOrder {specs : List Spec} (hf : Valid specs) :
    ∀ e, (render specs e).FirstOrder
  | .call i [] => by
    simp only [render]
    cases hr : specs[i]? with
    | none => trivial
    | some r => exact ⟨pure_firstOrder _ (hf r (List.mem_of_getElem? hr)),True.intro⟩
  | .call _ (_::_) => trivial
  | .seq a b | .alt a b => ⟨render_firstOrder hf a,render_firstOrder hf b⟩
  | .star a | .notP a => render_firstOrder hf a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

def parGrammar (specs : List Spec) : MGrammar :=
  ⟨specs.map (fun r => ⟨1,.seq r.head (render specs r.tail)⟩)⟩

def seqGrammar (specs : List Spec) : MGrammar :=
  ⟨specs.map (fun r => ⟨1,render specs r.tail⟩)⟩

theorem par_rule (specs : List Spec) (i : Nat) :
    ruleAtM (parGrammar specs).rules i =
      (specs[i]?).map (fun r => ⟨1,.seq r.head (render specs r.tail)⟩) := by
  simp [parGrammar,ruleAtM_eq_getElem?]

theorem seq_rule (specs : List Spec) (i : Nat) :
    ruleAtM (seqGrammar specs).rules i = (specs[i]?).map (fun r => ⟨1,render specs r.tail⟩) := by
  simp [seqGrammar,ruleAtM_eq_getElem?]

theorem par_firstOrder {specs : List Spec} (hf : Valid specs) : (parGrammar specs).FirstOrder := by
  intro r hr
  obtain ⟨r,hr',rfl⟩ := List.mem_map.mp hr
  exact ⟨pure_firstOrder _ (hf r hr'),render_firstOrder hf r.tail⟩

theorem seq_firstOrder {specs : List Spec} (hf : Valid specs) : (seqGrammar specs).FirstOrder := by
  intro r hr
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
  exact render_firstOrder hf r.tail

def Shifted (specs : List Spec) (x : List Char)
    (T U : Nat → List (List Char) → Val) : Prop :=
  ∀ i r, specs[i]? = some r → ∀ p q, p ≤ x.length → q ≤ x.length →
    evV (parGrammar specs) x .callByValuePar T [] r.head p = some (some q) →
    valAt (T i [pre x p q]) p = valAt (U i [pre x p q]) q

theorem evaluator_of_shift {specs : List Spec} (hf : Valid specs) (x : List Char)
    (T U : Nat → List (List Char) → Val) (hOk : OkTV x.length T)
    (hShift : Shifted specs x T U) :
    ∀ e E p, p ≤ x.length →
      evV (parGrammar specs) x .callByValuePar T E (render specs e) p =
        evV (seqGrammar specs) x .callByValueSeq U E (render specs e) p
  | .call i [], E, p, hp => by
    cases hr : specs[i]? with
    | none => simp only [render,hr]; rfl
    | some r =>
      have hPure := hf r (List.mem_of_getElem? hr)
      have hpar : ruleAtM (parGrammar specs).rules i = some ⟨1,.seq r.head (render specs r.tail)⟩ := by
        rw [par_rule,hr]; rfl
      have hseq : ruleAtM (seqGrammar specs).rules i = some ⟨1,render specs r.tail⟩ := by
        rw [seq_rule,hr]; rfl
      simp only [render,hr]
      rw [evV_call_par hpar rfl (by decide),evV_call_seq hseq rfl]
      simp only [evParArgs,evSeqArgs]
      rw [← pure_eval (parGrammar specs) (seqGrammar specs) x .callByValuePar .callByValueSeq T U E E r.head hPure p]
      cases hv : evV (parGrammar specs) x .callByValuePar T E r.head p with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some q =>
          dsimp only []
          apply hShift i r hr p q hp (evV_ok hOk r.head p hp q hv)
          rw [← pure_eval (parGrammar specs) (parGrammar specs) x .callByValuePar .callByValuePar T T E [] r.head hPure p]
          exact hv
  | .seq a b, E, p, hp => by
    have hh := evaluator_of_shift hf x T U hOk hShift a E p hp
    cases hv : evV (parGrammar specs) x .callByValuePar T E (render specs a) p with
    | none => simp only [render,evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => simp only [render,evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        simp only [render,evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_shift hf x T U hOk hShift b E q (evV_ok hOk _ p hp q hv)
  | .alt a b, E, p, hp => by
    have hh := evaluator_of_shift hf x T U hOk hShift a E p hp
    cases hv : evV (parGrammar specs) x .callByValuePar T E (render specs a) p with
    | none => simp only [render,evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some result => cases result with
      | none =>
        simp only [render,evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]
        exact evaluator_of_shift hf x T U hOk hShift b E p hp
      | some q => simp only [render,evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | .star a, E, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift hf x T U hOk hShift a E q (by omega))
  | .notP a, E, p, hp => by simp only [render,evV]; rw [evaluator_of_shift hf x T U hOk hShift a E p hp]
  | .param _, _, _, _ | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _ | .range _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .call _ (_::_), _, _, _ | .dbg _, _, _, _ | .lam _ _, _, _, _
  | .callParam _ _, _, _, _ | .invoke _ _ _, _, _, _ => rfl

theorem tables_shifted {specs : List Spec} (hf : Valid specs) (x : List Char) (k : Nat) :
    Shifted specs x (tblV (parGrammar specs) x .callByValuePar k)
      (tblV (seqGrammar specs) x .callByValueSeq k) := by
  induction k with
  | zero => intro i r hr p q hp hq hv; simp [tblV,valAt_nil]
  | succ k ih =>
    intro i r hr p q hp hq hv
    have hpar : ruleAtM (parGrammar specs).rules i = some ⟨1,.seq r.head (render specs r.tail)⟩ := by
      rw [par_rule,hr]; rfl
    have hseq : ruleAtM (seqGrammar specs).rules i = some ⟨1,render specs r.tail⟩ := by
      rw [seq_rule,hr]; rfl
    rw [valAt_tblV_succ hpar [pre x p q] hp,valAt_tblV_succ hseq [pre x p q] hq]
    have hpref : evV (parGrammar specs) x .callByValuePar
        (tblV (parGrammar specs) x .callByValuePar k) [pre x p q] r.head p = some (some q) := by
      rw [pure_eval (parGrammar specs) (parGrammar specs) x .callByValuePar .callByValuePar
        (tblV (parGrammar specs) x .callByValuePar k) (tblV (parGrammar specs) x .callByValuePar (k+1))
        [pre x p q] [] r.head (hf r (List.mem_of_getElem? hr)) p]
      exact hv
    rw [evV_seq_ok hpref]
    exact evaluator_of_shift hf x _ _ (tblV_ok _ _ _ k) ih r.tail [pre x p q] q hq

theorem evaluator_eq {specs : List Spec} (hf : Valid specs) (x : List Char) (k : Nat)
    (E : List (List Char)) (e : MExp) (p : Nat) (hp : p ≤ x.length) :
    evV (parGrammar specs) x .callByValuePar (tblV (parGrammar specs) x .callByValuePar k) E (render specs e) p =
      evV (seqGrammar specs) x .callByValueSeq (tblV (seqGrammar specs) x .callByValueSeq k) E (render specs e) p :=
  evaluator_of_shift hf x _ _ (tblV_ok _ _ _ k) (tables_shifted hf x k) e E p hp

theorem decide_eq {specs : List Spec} (hf : Valid specs) (e : MExp) (x : List Char) :
    decideObsV .callByValuePar (parGrammar specs) x (render specs e) =
      decideObsV .callByValueSeq (seqGrammar specs) x (render specs e) := by
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq (parGrammar specs) (seqGrammar specs) x .callByValuePar .callByValueSeq
    (render specs e) (render specs e) (fun k => evaluator_eq hf x k [] e x.length (Nat.le_refl _))]

theorem observations_iff {specs : List Spec} (hf : Valid specs) (e : MExp)
    (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar specs) .callByValuePar (render specs e) x r ↔
      SObs (seqGrammar specs) .callByValueSeq (render specs e) x r := by
  rw [← decideObsV_iff (par_firstOrder hf) (by decide) (render_firstOrder hf e),
    ← decideObsV_iff (seq_firstOrder hf) (by decide) (render_firstOrder hf e),decide_eq hf e x]

theorem language_translation {specs : List Spec} (hf : Valid specs) (e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (parGrammar specs) .callByValuePar (render specs e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar specs,render specs e,seq_firstOrder hf,render_firstOrder hf e,
    fun x => observations_iff hf e x (some [])⟩

def copySpec : Spec :=
  ⟨NestedScannerArguments.scan ['a','b'],.seq (.chr '#') (.param 0)⟩

theorem copy_valid : Valid [copySpec] := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  simp [copySpec,NestedScannerArguments.scan,NestedScannerArguments.choice,Pure,MExp.failAlways]

/-- A single fixed pair of grammars captures any a/b word freshly, consumes
a delimiter, and then replays that same unbounded word in both strategies. -/
theorem copy_word (w : List Char) (hw : ∀ c ∈ w, c='a' ∨ c='b') :
    let x := w ++ '#'::w
    let e := render [copySpec] (.call 0 [])
    evParArgs (parGrammar [copySpec]) x .callByValuePar
      (tblV (parGrammar [copySpec]) x .callByValuePar 1) [] [copySpec.head] x.length = some (some [w]) ∧
    evV (parGrammar [copySpec]) x .callByValuePar
      (tblV (parGrammar [copySpec]) x .callByValuePar 1) [] e x.length = some (some 0) ∧
    evV (seqGrammar [copySpec]) x .callByValueSeq
      (tblV (seqGrammar [copySpec]) x .callByValueSeq 1) [] e x.length = some (some 0) := by
  let x := w ++ '#'::w
  have hpref (g : MGrammar) (s : Strategy) (T : Nat → List (List Char) → Val) (E : List (List Char)) :
      evV g x s T E copySpec.head x.length = some (some ('#'::w).length) := by
    rw [show copySpec.head = NestedScannerArguments.scan ['a','b'] from rfl,
      NestedScannerArguments.scan_eval _ _ _ _ _ _ _ (Nat.le_refl _)]
    have hc : ∀ c ∈ w, NestedScannerArguments.accepts ['a','b'] c = true := by
      intro c hc
      rcases hw c hc with rfl | rfl <;> decide
    simp only [sfx,Nat.sub_self,List.drop_zero]
    rw [show x = w ++ '#'::w from rfl,List.dropWhile_append_of_pos hc]
    rfl
  have hpre : pre x x.length ('#'::w).length = w := by
    have hl : x.length-('#'::w).length = w.length := by simp [x]
    simp only [pre,hl,sfx,Nat.sub_self,List.drop_zero]
    exact List.take_left
  have hsuffix : sfx x ('#'::w).length = '#'::w := sfx_suffix (show x = w ++ '#'::w from rfl)
  have hlast : sfx x w.length = w := by
    apply sfx_suffix (pre := w++['#'])
    simp [x,List.append_assoc]
  have htarget : evV (seqGrammar [copySpec]) x .callByValueSeq
      (tblV (seqGrammar [copySpec]) x .callByValueSeq 1) []
      (render [copySpec] (.call 0 [])) x.length = some (some 0) := by
    have hr : ruleAtM (seqGrammar [copySpec]).rules 0 = some ⟨1,render [copySpec] copySpec.tail⟩ := by
      rw [seq_rule]; rfl
    simp only [render,List.getElem?_cons_zero]
    rw [evV_call_seq hr rfl]
    simp only [evSeqArgs,hpref,hpre]
    rw [valAt_tblV_succ hr [w] (by simp [x])]
    change evV (seqGrammar [copySpec]) x .callByValueSeq
      (tblV (seqGrammar [copySpec]) x .callByValueSeq 0) [w] (.seq (.chr '#') (.param 0)) ('#'::w).length = _
    simp only [evV,hsuffix]
    simp [Shallot.beqChar,hlast,(CBVtoCBN.stripPrefix_exact w w []).mpr (by simp)]
  dsimp only []
  refine ⟨?_,?_,htarget⟩
  · change evParArgs (parGrammar [copySpec]) x .callByValuePar
      (tblV (parGrammar [copySpec]) x .callByValuePar 1) [] [copySpec.head] x.length = _
    simp only [evParArgs,hpref,hpre]
  · rw [evaluator_eq copy_valid x 1 [] (.call 0 []) x.length (Nat.le_refl _)]
    exact htarget

/-- Unlike a fixed Word selector, the new fixed grammars realize captures
outside any supplied finite candidate family with a fixed environment. -/
theorem beyond_finite_word_selection (E : List (List Char)) (C : List MExp) :
    ∃ w, (∀ a ∈ C, WordArguments.value E a ≠ some w) ∧
      let x := w ++ '#'::w
      let e := render [copySpec] (.call 0 [])
      evParArgs (parGrammar [copySpec]) x .callByValuePar
        (tblV (parGrammar [copySpec]) x .callByValuePar 1) [] [copySpec.head] x.length = some (some [w]) ∧
      evV (parGrammar [copySpec]) x .callByValuePar
        (tblV (parGrammar [copySpec]) x .callByValuePar 1) [] e x.length = some (some 0) ∧
      evV (seqGrammar [copySpec]) x .callByValueSeq
        (tblV (seqGrammar [copySpec]) x .callByValueSeq 1) [] e x.length = some (some 0) := by
  obtain ⟨n,hn⟩ := WordSelectionBoundary.no_finite_word_family E C 'a'
  refine ⟨List.replicate n 'a',hn,copy_word _ ?_⟩
  intro c hc
  exact Or.inl (List.mem_replicate.mp hc).2

def nestedSpec : Spec :=
  ⟨NestedScannerArguments.scan ['a','b'],
    .seq (.chr '#') (.seq (.alt (.call 0 []) .eps) (.param 0))⟩

theorem nested_valid : Valid [nestedSpec] := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  simp [nestedSpec,NestedScannerArguments.scan,NestedScannerArguments.choice,Pure,MExp.failAlways]

/-- Three nested calls retain different fresh captures, including an empty
one; the outer captures are replayed after the recursive calls consume input. -/
theorem nested_captures :
    let e := render [nestedSpec] (.call 0 [])
    let good := "ab#ba##baab".toList
    let bad := "ab#ba##bbab".toList
    (evV (parGrammar [nestedSpec]) good .callByValuePar
      (tblV (parGrammar [nestedSpec]) good .callByValuePar 4) [] e good.length = some (some 0)) ∧
    (evV (seqGrammar [nestedSpec]) good .callByValueSeq
      (tblV (seqGrammar [nestedSpec]) good .callByValueSeq 4) [] e good.length = some (some 0)) ∧
    (evV (parGrammar [nestedSpec]) bad .callByValuePar
      (tblV (parGrammar [nestedSpec]) bad .callByValuePar 4) [] e bad.length = some none) ∧
    (evV (seqGrammar [nestedSpec]) bad .callByValueSeq
      (tblV (seqGrammar [nestedSpec]) bad .callByValueSeq 4) [] e bad.length = some none) := by
  decide +kernel

/-- An argument whose nullable repetition never returns must not become
a failed capture, an empty capture, or a successful entry to the body. -/
theorem nullable_repetition_keeps_undefined (x : List Char) (k : Nat) :
    let specs : List Spec := [⟨.star .eps,.any⟩]
    let e := render specs (.call 0 [])
    evV (parGrammar specs) x .callByValuePar (tblV (parGrammar specs) x .callByValuePar k) [] e x.length = none ∧
    evV (seqGrammar specs) x .callByValueSeq (tblV (seqGrammar specs) x .callByValueSeq k) [] e x.length = none := by
  let specs : List Spec := [⟨.star .eps,.any⟩]
  have hloop (g : MGrammar) (s : Strategy) (T : Nat → List (List Char) → Val)
      (E : List (List Char)) (p : Nat) : evV g x s T E (.star .eps) p = none := by
    rw [evV_star]
    exact evStar_stuck rfl (Nat.lt_irrefl p)
  have hpar : ruleAtM (parGrammar specs).rules 0 = some ⟨1,.seq (.star .eps) (render specs .any)⟩ := by
    rw [par_rule]; rfl
  have hseq : ruleAtM (seqGrammar specs).rules 0 = some ⟨1,render specs .any⟩ := by
    rw [seq_rule]; rfl
  change evV (parGrammar specs) x .callByValuePar (tblV (parGrammar specs) x .callByValuePar k)
      [] (.call 0 [.star .eps]) x.length = none ∧
    evV (seqGrammar specs) x .callByValueSeq (tblV (seqGrammar specs) x .callByValueSeq k)
      [] (.call 0 [.star .eps]) x.length = none
  rw [evV_call_par hpar rfl (by decide),evV_call_seq hseq rfl]
  simp only [evParArgs,evSeqArgs,hloop,and_self]

end Shallot.MacroPeg.CBV.ParserPrefixFusion
