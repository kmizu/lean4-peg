import MacroPeg.CBV.SequenceArgumentDomain
import MacroPeg.CBV.LiteralSpecialization

/-! Static specialization of sequential and ordered-choice arguments under a
finite, checked capture domain. Input positions are restored by shifted probes. -/
namespace Shallot.MacroPeg.CBV.SequenceSpecialization
open SequenceArguments SequenceArgumentDomain
open LiteralSpecialization (specs mem_specs specs_valid)

def compile (g : MGrammar) (S : List (Nat × List (List Char))) (E : List (List Char)) : MExp → MExp
  | .param k => match E[k]? with | some w => .lit w | none => MExp.failAlways
  | .call i args => match ruleAtM g.rules i with
    | none => MExp.failAlways
    | some r => if r.arity=args.length then
      selectArgs E args (fun W => .call (indexIn (i,W) S) [])
      else MExp.failAlways
  | .seq a b => .seq (compile g S E a) (compile g S E b)
  | .alt a b => .alt (compile g S E a) (compile g S E b)
  | .star a => .star (compile g S E a)
  | .notP a => .notP (compile g S E a)
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit w => .lit w
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

theorem compile_firstOrder (g : MGrammar) (S : List (Nat × List (List Char))) (E : List (List Char)) :
    ∀ e, (compile g S E e).FirstOrder
  | .param k => by simp only [compile]; split <;> trivial
  | .call i args => by
    simp only [compile]
    split
    · trivial
    · split
      · exact selectArgs_firstOrder E args _ (fun _ => trivial)
      · trivial
  | .seq a b | .alt a b => ⟨compile_firstOrder g S E a,compile_firstOrder g S E b⟩
  | .star a | .notP a => compile_firstOrder g S E a
  | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

def target (g : MGrammar) (V : List (List Char)) : MGrammar :=
  ⟨(specs g V).map (fun q => ⟨0,match ruleAtM g.rules q.1 with
    | some r => compile g (specs g V) q.2 r.body
    | none => MExp.failAlways⟩)⟩

theorem target_firstOrder (g : MGrammar) (V : List (List Char)) : (target g V).FirstOrder := by
  intro r hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  split
  · exact compile_firstOrder _ _ _ _
  · trivial

theorem target_zero_arity (g : MGrammar) (V : List (List Char)) :
    ∀ r ∈ (target g V).rules, r.arity=0 := by
  intro r hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  rfl

theorem target_rule {g : MGrammar} {V W : List (List Char)} {i : Nat} {r : MRule}
    (hr : ruleAtM g.rules i = some r) (h : (i,W) ∈ specs g V) :
    ruleAtM (target g V).rules (indexIn (i,W) (specs g V)) =
      some ⟨0,compile g (specs g V) W r.body⟩ := by
  rw [ruleAtM_eq_getElem?] at hr
  simp [target,ruleAtM_eq_getElem?,List.getElem?_map,getElem?_indexIn _ _ h,hr]

def Related (g : MGrammar) (V : List (List Char)) (x : List Char)
    (T U : Nat → List (List Char) → Val) : Prop :=
  ∀ i W, (i,W) ∈ specs g V → ∀ p, p ≤ x.length →
    valAt (T i W) p = valAt (U (indexIn (i,W) (specs g V)) []) p

theorem evaluator_of_related {g : MGrammar} {V : List (List Char)} {x : List Char}
    {T U : Nat → List (List Char) → Val} (hOk : OkTV x.length T) (hrel : Related g V x T U) :
    ∀ e, Supported V e → ∀ E, (∀ w ∈ E, w ∈ V) → ∀ p, p ≤ x.length →
      evV g x .callByValuePar T E e p =
        evV (target g V) x .callByValueSeq U [] (compile g (specs g V) E e) p
  | .eps, _, _, _, _, _ | .any, _, _, _, _, _ | .chr _, _, _, _, _, _
  | .range _ _, _, _, _, _, _ | .lit _, _, _, _, _, _ => rfl
  | .param k, _, E, _, p, _ => by
    cases hh : E[k]? <;> simp [compile,evV,hh,MExp.failAlways]
  | .dbg _, hf, _, _, _, _ | .lam _ _, hf, _, _, _, _
  | .callParam _ _, hf, _, _, _, _ | .invoke _ _ _, hf, _, _, _, _ => False.elim hf
  | .call i args, hf, E, hE, p, hp => by
    cases hr : ruleAtM g.rules i with
    | none => simp [compile,evV,hr,MExp.failAlways]
    | some r =>
      by_cases ha : r.arity=args.length
      · rw [evV_call_par hr ha (by decide)]
        simp only [compile,hr,if_pos ha]
        rw [selectArgs_eval g (target g V) x .callByValuePar .callByValueSeq T U E p hp args (fun a ha => (hf a ha).1)]
        cases hv : evParArgs g x .callByValuePar T E args p with
        | none => rfl
        | some v =>
          cases v with
          | none => rfl
          | some W =>
            have hb := arguments_bounds hE g x .callByValuePar T p hp args hf W hv
            have hm := mem_specs hr (hb.1.trans ha.symm) hb.2
            have htr := target_rule hr hm
            simp only []
            rw [evV_call_seq htr (by rfl)]
            simpa only [evSeqArgs] using hrel i W hm p hp
      · simp [compile,hr,ha,evV,MExp.failAlways]
  | .seq a b, hf, E, hE, p, hp => by
    simp only [compile]
    have heq := evaluator_of_related hOk hrel a hf.1 E hE p hp
    cases hv : evV g x .callByValuePar T E a p with
    | none => rw [evV_seq_none hv,evV_seq_none (heq.symm.trans hv)]
    | some v =>
      cases v with
      | none => rw [evV_seq_fail hv,evV_seq_fail (heq.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
        exact evaluator_of_related hOk hrel b hf.2 E hE q (evV_ok hOk a p hp q hv)
  | .alt a b, hf, E, hE, p, hp => by
    simp only [compile]
    have heq := evaluator_of_related hOk hrel a hf.1 E hE p hp
    cases hv : evV g x .callByValuePar T E a p with
    | none => rw [evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
    | some v =>
      cases v with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
        exact evaluator_of_related hOk hrel b hf.2 E hE p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
  | .notP a, hf, E, hE, p, hp => by
    simp only [compile,evV]
    rw [evaluator_of_related hOk hrel a hf E hE p hp]
  | .star a, hf, E, hE, p, hp => by
    simp only [compile]
    rw [evV_star,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_related hOk hrel a hf E hE q (by omega))

def GrammarSupported (V : List (List Char)) (g : MGrammar) : Prop := ∀ r ∈ g.rules, Supported V r.body

theorem grammar_firstOrder {g : MGrammar} {V : List (List Char)} (hg : GrammarSupported V g) : g.FirstOrder :=
  fun r hr => supported_firstOrder _ (hg r hr)

theorem tables_related {g : MGrammar} {V : List (List Char)} (hg : GrammarSupported V g)
    (x : List Char) (m : Nat) :
    Related g V x (tblV g x .callByValuePar m) (tblV (target g V) x .callByValueSeq m) := by
  induction m with
  | zero => intro i E hm p hp; rfl
  | succ m ih =>
    intro i E hm p hp
    obtain ⟨r,hr,hn,hE⟩ := specs_valid hm
    rw [valAt_tblV_succ hr E hp,valAt_tblV_succ (target_rule hr hm) [] hp]
    exact evaluator_of_related (tblV_ok _ _ _ m) ih r.body (hg r (ruleAtM_mem hr)) E hE p hp

theorem evaluator_eq {g : MGrammar} {V : List (List Char)} (hg : GrammarSupported V g)
    {e : MExp} (he : Supported V e) (x : List Char) (m : Nat) :
    evV g x .callByValuePar (tblV g x .callByValuePar m) [] e x.length =
      evV (target g V) x .callByValueSeq (tblV (target g V) x .callByValueSeq m) []
        (compile g (specs g V) [] e) x.length :=
  evaluator_of_related (tblV_ok _ _ _ m) (tables_related hg x m) e he [] (by simp) _ (Nat.le_refl _)

theorem limit_eq {g : MGrammar} {V : List (List Char)} (hg : GrammarSupported V g)
    {e : MExp} (he : Supported V e) (x : List Char) :
    evV g x .callByValuePar (tblV g x .callByValuePar (iterBoundV g x)) [] e x.length =
      evV (target g V) x .callByValueSeq
        (tblV (target g V) x .callByValueSeq (iterBoundV (target g V) x)) []
        (compile g (specs g V) [] e) x.length := by
  cases hs : evV g x .callByValuePar (tblV g x .callByValuePar (iterBoundV g x)) [] e x.length with
  | none =>
    cases ht : evV (target g V) x .callByValueSeq
        (tblV (target g V) x .callByValueSeq (iterBoundV (target g V) x)) []
        (compile g (specs g V) [] e) x.length with
    | none => rfl
    | some v =>
      have hh := (tblV_stable g x .callByValuePar (Nat.le_refl _)).mp
        ⟨iterBoundV (target g V) x,(evaluator_eq hg he x _).trans ht⟩
      rw [hs] at hh
      cases hh
  | some v =>
    have hh := (tblV_stable (target g V) x .callByValueSeq (Nat.le_refl _)).mp
      ⟨iterBoundV g x,(evaluator_eq hg he x _).symm.trans hs⟩
    exact hh.symm

theorem decide_eq {g : MGrammar} {V : List (List Char)} (hg : GrammarSupported V g)
    {e : MExp} (he : Supported V e) (x : List Char) :
    decideObsV .callByValuePar g x e =
      decideObsV .callByValueSeq (target g V) x (compile g (specs g V) [] e) := by
  unfold decideObsV
  rw [limit_eq hg he x]

theorem observations_iff {g : MGrammar} {V : List (List Char)} (hg : GrammarSupported V g)
    {e : MExp} (he : Supported V e) (x : List Char) (r : Option (List Char)) :
    SObs g .callByValuePar e x r ↔
      SObs (target g V) .callByValueSeq (compile g (specs g V) [] e) x r := by
  rw [← decideObsV_iff (grammar_firstOrder hg) (by decide) (supported_firstOrder _ he),
    ← decideObsV_iff (target_firstOrder g V) (by decide) (compile_firstOrder _ _ _ _),decide_eq hg he x]

theorem language_translation {g : MGrammar} {V : List (List Char)} (hg : GrammarSupported V g)
    {e : MExp} (he : Supported V e) :
    ∃ (out : MGrammar) (start : MExp), out.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs g .callByValuePar e x (some []) ↔ SObs out .callByValueSeq start x (some []) :=
  ⟨target g V,compile g (specs g V) [] e,target_firstOrder g V,compile_firstOrder _ _ _ _,
    fun x => observations_iff hg he x (some [])⟩

/-- Finite executable eligibility check for the supplied capture palette. -/
def check (g : MGrammar) (V : List (List Char)) (e : MExp) : Bool :=
  g.rules.all (fun r => supportedB V r.body) && supportedB V e

theorem check_iff (g : MGrammar) (V : List (List Char)) (e : MExp) :
    check g V e = true ↔ GrammarSupported V g ∧ Supported V e := by
  simp [check,GrammarSupported,List.all_eq_true,supportedB_iff]

/-- Once the syntactic finite-domain check succeeds, this fixed target
preserves every original character-input observation. -/
theorem checked_observations {g : MGrammar} {V : List (List Char)} {e : MExp}
    (h : check g V e = true) (x : List Char) (r : Option (List Char)) :
    SObs g .callByValuePar e x r ↔
      SObs (target g V) .callByValueSeq (compile g (specs g V) [] e) x r := by
  obtain ⟨hg,he⟩ := (check_iff g V e).mp h
  exact observations_iff hg he x r

theorem checked_language_translation {g : MGrammar} {V : List (List Char)} {e : MExp}
    (h : check g V e = true) :
    ∃ (out : MGrammar) (start : MExp), out.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs g .callByValuePar e x (some []) ↔ SObs out .callByValueSeq start x (some []) := by
  obtain ⟨hg,he⟩ := (check_iff g V e).mp h
  exact language_translation hg he

end Shallot.MacroPeg.CBV.SequenceSpecialization
