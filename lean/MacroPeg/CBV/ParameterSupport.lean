import MacroPeg.Properties.DecideCBV

/-! Parameter views only need to agree on the indices actually read by a
first-order expression, including reads inside predicates and actuals. -/
namespace Shallot.MacroPeg.CBV.ParameterSupport

mutual
  def Supports (A : Nat → Prop) : MExp → Prop
    | .eps | .any | .chr _ | .range _ _ | .lit _ => True
    | .param i => A i
    | .call _ as => SupportsArgs A as
    | .seq a b | .alt a b => Supports A a ∧ Supports A b
    | .notP a | .star a => Supports A a
    | _ => False
  def SupportsArgs (A : Nat → Prop) : List MExp → Prop
    | [] => True
    | a::as => Supports A a ∧ SupportsArgs A as
end

mutual
  def check (A : Nat → Bool) : MExp → Bool
    | .eps | .any | .chr _ | .range _ _ | .lit _ => true
    | .param i => A i
    | .call _ as => checkArgs A as
    | .seq a b | .alt a b => check A a && check A b
    | .notP a | .star a => check A a
    | _ => false
  def checkArgs (A : Nat → Bool) : List MExp → Bool
    | [] => true
    | a::as => check A a && checkArgs A as
end

mutual
  theorem check_iff (A : Nat → Bool) : ∀ e, check A e=true ↔ Supports (fun i => A i=true) e
    | .eps | .any | .chr _ | .range _ _ | .lit _ => by simp [check,Supports]
    | .param _ => Iff.rfl
    | .call _ as => checkArgs_iff A as
    | .seq a b | .alt a b => by simp only [check,Supports,Bool.and_eq_true,check_iff A a,check_iff A b]
    | .notP a | .star a => check_iff A a
    | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => by simp [check,Supports]
  theorem checkArgs_iff (A : Nat → Bool) : ∀ as, checkArgs A as=true ↔ SupportsArgs (fun i => A i=true) as
    | [] => by simp [checkArgs,SupportsArgs]
    | a::as => by simp only [checkArgs,SupportsArgs,Bool.and_eq_true,check_iff A a,checkArgs_iff A as]
end

mutual
  theorem mono {A B : Nat → Prop} (h : ∀ i, A i → B i) : ∀ e, Supports A e → Supports B e
    | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ => trivial
    | .param i,he => h i he
    | .call _ as,he => args_mono h as he
    | .seq a b,he | .alt a b,he => ⟨mono h a he.1,mono h b he.2⟩
    | .notP a,he | .star a,he => mono h a he
    | .dbg _,he | .lam _ _,he | .callParam _ _,he | .invoke _ _ _,he => False.elim he
  theorem args_mono {A B : Nat → Prop} (h : ∀ i, A i → B i) : ∀ as, SupportsArgs A as → SupportsArgs B as
    | [],_ => trivial
    | a::as,he => ⟨mono h a he.1,args_mono h as he.2⟩
end

mutual
  theorem all_of_firstOrder : ∀ e, e.FirstOrder → Supports (fun _ => True) e
    | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ | .param _,_ => trivial
    | .call _ as,he => all_args_of_firstOrder as he
    | .seq a b,he | .alt a b,he => ⟨all_of_firstOrder a he.1,all_of_firstOrder b he.2⟩
    | .notP a,he | .star a,he => all_of_firstOrder a he
    | .dbg _,he | .lam _ _,he | .callParam _ _,he | .invoke _ _ _,he => False.elim he
  theorem all_args_of_firstOrder : ∀ as, MExp.FirstOrderArgs as → SupportsArgs (fun _ => True) as
    | [],_ => trivial
    | a::as,he => ⟨all_of_firstOrder a he.1,all_args_of_firstOrder as he.2⟩
end

mutual
  theorem evV_rebind {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      {E : List (List Char)} (A : Nat → Prop) (P : List MExp) (W : List (List Char))
      (hparam : ∀ k, A k → ∀ p, evV g x s T E (MExp.subst P (.param k)) p = evV g x s T W (.param k) p) :
      ∀ (b : MExp), Supports A b → ∀ p, evV g x s T E (MExp.subst P b) p = evV g x s T W b p
    | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _ => by simp only [MExp.subst, evV]
    | .param k, hb, p => hparam k hb p
    | .call j ms, hb, p => by
      simp only [MExp.subst]
      cases hr : ruleAtM g.rules j with
      | none => simp only [evV, hr]
      | some r =>
        by_cases ha : r.arity = ms.length
        · have ha' : r.arity = (MExp.substArgs P ms).length := by rw [length_substArgs]; exact ha
          by_cases hs : s = .callByValueSeq
          · subst hs
            rw [evV_call_seq hr ha', evV_call_seq hr ha, evSeqArgs_rebind A P W hparam ms hb]
          · rw [evV_call_par hr ha' hs, evV_call_par hr ha hs, evParArgs_rebind A P W hparam ms hb]
        · have ha' : ¬ r.arity = (MExp.substArgs P ms).length := by rw [length_substArgs]; exact ha
          simp only [evV, hr, if_neg ha, if_neg ha']
    | .seq a c, hb, p => by
      simp only [MExp.subst]
      have ha := evV_rebind (g := g) (x := x) (s := s) (T := T) (E := E) A P W hparam a hb.1 p
      cases h : evV g x s T W a p with
      | none => rw [evV_seq_none (ha.trans h), evV_seq_none h]
      | some r =>
        cases r with
        | none => rw [evV_seq_fail (ha.trans h), evV_seq_fail h]
        | some j => rw [evV_seq_ok (ha.trans h), evV_seq_ok h]; exact evV_rebind A P W hparam c hb.2 j
    | .alt a c, hb, p => by
      simp only [MExp.subst]
      have ha := evV_rebind (g := g) (x := x) (s := s) (T := T) (E := E) A P W hparam a hb.1 p
      cases h : evV g x s T W a p with
      | none => rw [evV_alt_none (ha.trans h), evV_alt_none h]
      | some r =>
        cases r with
        | none => rw [evV_alt_fail (ha.trans h), evV_alt_fail h]; exact evV_rebind A P W hparam c hb.2 p
        | some j => rw [evV_alt_ok (ha.trans h), evV_alt_ok h]
    | .notP a, hb, p => by
      simp only [MExp.subst]
      have ha := evV_rebind (g := g) (x := x) (s := s) (T := T) (E := E) A P W hparam a hb p
      cases h : evV g x s T W a p with
      | none => rw [evV_not_none (ha.trans h), evV_not_none h]
      | some r =>
        cases r with
        | none => rw [evV_not_fail (ha.trans h), evV_not_fail h]
        | some j => rw [evV_not_ok (ha.trans h), evV_not_ok h]
    | .star a, hb, p => by
      simp only [MExp.subst]
      rw [evV_star, evV_star]
      exact evStar_congr p (fun q _ => evV_rebind A P W hparam a hb q)
    | .dbg _, hb, _ | .lam _ _, hb, _ | .callParam _ _, hb, _ | .invoke _ _ _, hb, _ => absurd hb id

  theorem evParArgs_rebind {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      {E : List (List Char)} (A : Nat → Prop) (P : List MExp) (W : List (List Char))
      (hparam : ∀ k, A k → ∀ p, evV g x s T E (MExp.subst P (.param k)) p = evV g x s T W (.param k) p) :
      ∀ (ms : List MExp), SupportsArgs A ms → ∀ p,
        evParArgs g x s T E (MExp.substArgs P ms) p = evParArgs g x s T W ms p
    | [], _, p => by simp only [MExp.substArgs, evPar_nil]
    | m :: ms, hm, p => by
      simp only [MExp.substArgs]
      have hh := evV_rebind (g := g) (x := x) (s := s) (T := T) (E := E) A P W hparam m hm.1 p
      cases h : evV g x s T W m p with
      | none => rw [evPar_cons_none (hh.trans h), evPar_cons_none h]
      | some r =>
        cases r with
        | none => rw [evPar_cons_fail (hh.trans h), evPar_cons_fail h]
        | some j => rw [evPar_cons_ok (hh.trans h), evPar_cons_ok h, evParArgs_rebind A P W hparam ms hm.2 p]

  theorem evSeqArgs_rebind {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      {E : List (List Char)} (A : Nat → Prop) (P : List MExp) (W : List (List Char))
      (hparam : ∀ k, A k → ∀ p, evV g x s T E (MExp.subst P (.param k)) p = evV g x s T W (.param k) p) :
      ∀ (ms : List MExp), SupportsArgs A ms → ∀ p,
        evSeqArgs g x s T E (MExp.substArgs P ms) p = evSeqArgs g x s T W ms p
    | [], _, p => by simp only [MExp.substArgs, evSeq_nil]
    | m :: ms, hm, p => by
      simp only [MExp.substArgs]
      have hh := evV_rebind (g := g) (x := x) (s := s) (T := T) (E := E) A P W hparam m hm.1 p
      cases h : evV g x s T W m p with
      | none => rw [evSeq_cons_none (hh.trans h), evSeq_cons_none h]
      | some r =>
        cases r with
        | none => rw [evSeq_cons_fail (hh.trans h), evSeq_cons_fail h]
        | some j => rw [evSeq_cons_ok (hh.trans h), evSeq_cons_ok h, evSeqArgs_rebind A P W hparam ms hm.2 j]
end

end Shallot.MacroPeg.CBV.ParameterSupport
