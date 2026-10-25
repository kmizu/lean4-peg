import MacroPeg.CBV.RecursiveProducedCompiler

namespace Shallot.MacroPeg.CBV.RecursiveProducedSimulation
open RecursiveProducedCompiler
open ClockFreezing (Table)

def Declared (g : MGrammar) (es : List Entry) :=
  ∀ i, (ruleAtM g.rules i).map MRule.arity=(es[i]?).map (fun _ => 1)

theorem known (g : MGrammar) (es : List Entry) (h : Declared g es) (i : Nat) (e : Entry)
    (hi : es[i]?=some e) : ∃ r, ruleAtM g.rules i=some r ∧ r.arity=1 := by
  have hh := h i
  cases hr : ruleAtM g.rules i with
  | none => simp [hr,hi] at hh
  | some r => exact ⟨r,rfl,by simpa [hr,hi] using hh⟩

theorem missing (g : MGrammar) (es : List Entry) (h : Declared g es) (i : Nat)
    (hi : es[i]?=none) : ruleAtM g.rules i=none := by
  have hh := h i
  cases hr : ruleAtM g.rules i with
  | none => rfl
  | some r => simp [hr,hi] at hh

def Captured (g : MGrammar) (x : List Char) (S : Table) (D : MExp) (w : List Char) (p j : Nat) :=
  GuardedReplayControl.Aligned x w p j ∧ evV g x .callByValuePar S [] D p=some (some j)

def Rows (es : List Entry) (g : MGrammar) (x : List Char) (S T U : Table) : Prop :=
  ∀ (i : Nat) (e : Entry), es[i]?=some e → ∀ w, w∈subStrs x → ∀ p, p≤x.length →
    match e with
    | .produced D _ => ∀ j, Captured g x S D w p j → RLe (valAt (T i [w]) p) (valAt (U i [w]) p)
    | _ => RLe (valAt (T i [w]) p) (valAt (U i [w]) p)

/-- A structural simulation whose only conditional rows are justified by an
actual successful argument evaluation. Both argument results are available
when establishing its capture invariant; no invariant is assumed at entry. -/
theorem evaluator (es : List Entry) (src g h : MGrammar) (x : List Char) (S T U : Table)
    (hg : Declared g es) (hh : Declared h es) (hT : OkTV x.length T)
    (hSound : SoundTV g x .callByValuePar T) (rows : Rows es src x S T U)
    (captures : ∀ (i : Nat) (D B : MExp), es[i]?=some (.produced D B) → ∀ E p j, p≤x.length →
      evV g x .callByValuePar T E D p=some (some j) →
      evV h x .callByValuePar U E D p=some (some j) →
      evV src x .callByValuePar S [] D p=some (some j))
    (E : List (List Char)) : ∀ e, e.FirstOrder → conforms es e=true → ∀ p, p≤x.length →
      RLe (evV g x .callByValuePar T E e p) (evV h x .callByValuePar U E e p)
  | .call i [a],he,hc,p,hp => by
    cases hi : es[i]? with
    | none => simp only [evV,missing g es hg i hi,missing h es hh i hi]; exact RLe.refl _
    | some e =>
      obtain ⟨r,hr,har⟩ := known g es hg i e hi
      obtain ⟨r',hr',har'⟩ := known h es hh i e hi
      rw [evV_call_par hr (by simpa using har) (by decide),evV_call_par hr' (by simpa using har') (by decide)]
      have hcA := (Bool.and_eq_true_iff.mp hc).1
      have hcI := (Bool.and_eq_true_iff.mp hc).2
      have harg := evaluator es src g h x S T U hg hh hT hSound rows captures E a he.1 hcA p hp
      simp only [evParArgs]
      cases ha : evV g x .callByValuePar T E a p with
      | none => simp only [ha]; exact Or.inl rfl
      | some v =>
        have hb := harg.eq_of_some ha
        cases v with
        | none => simp only [ha,hb]; exact RLe.refl _
        | some j =>
          simp only [ha,hb]
          have hprefix := ReplayFusion.success_prefix hSound E a he.1 p j hp ha
          cases e with
          | growth r => exact rows i (.growth r) hi _ (pre_mem hp j) p hp
          | origin P => exact rows i (.origin P) hi _ (pre_mem hp j) p hp
          | produced D B =>
            have had : a=D := (MExp.beqE_iff _ _).mp (by simpa only [callCheck,hi] using hcI)
            subst a
            exact rows i (.produced D B) hi _ (pre_mem hp j) p hp j
              ⟨⟨hp,hprefix.1,hprefix.2⟩,captures i D B hi E p j hp ha hb⟩
  | .call i [],_,_,p,_ | .call i (_::_::_),_,_,p,_ => by
    cases hi : es[i]? with
    | none => simp only [evV,missing g es hg i hi,missing h es hh i hi]; exact RLe.refl _
    | some e =>
      obtain ⟨r,hr,har⟩ := known g es hg i e hi
      obtain ⟨r',hr',har'⟩ := known h es hh i e hi
      simp [evV,hr,hr',har,har',RLe]
  | .seq a b,he,hc,p,hp => by
    have ih := evaluator es src g h x S T U hg hh hT hSound rows captures E a he.1 (Bool.and_eq_true_iff.mp hc).1 p hp
    cases ha : evV g x .callByValuePar T E a p with
    | none => rw [evV_seq_none ha]; exact Or.inl rfl
    | some v =>
      have hb := ih.eq_of_some ha
      cases v with
      | none => rw [evV_seq_fail ha,evV_seq_fail hb]; exact RLe.refl _
      | some j =>
        rw [evV_seq_ok ha,evV_seq_ok hb]
        exact evaluator es src g h x S T U hg hh hT hSound rows captures E b he.2
          (Bool.and_eq_true_iff.mp hc).2 j (evV_ok hT a p hp j ha)
  | .alt a b,he,hc,p,hp => by
    have ih := evaluator es src g h x S T U hg hh hT hSound rows captures E a he.1 (Bool.and_eq_true_iff.mp hc).1 p hp
    cases ha : evV g x .callByValuePar T E a p with
    | none => rw [evV_alt_none ha]; exact Or.inl rfl
    | some v =>
      have hb := ih.eq_of_some ha
      cases v with
      | none =>
        rw [evV_alt_fail ha,evV_alt_fail hb]
        exact evaluator es src g h x S T U hg hh hT hSound rows captures E b he.2 (Bool.and_eq_true_iff.mp hc).2 p hp
      | some j => rw [evV_alt_ok ha,evV_alt_ok hb]; exact RLe.refl _
  | .notP a,he,hc,p,hp => by
    have ih := evaluator es src g h x S T U hg hh hT hSound rows captures E a he hc p hp
    cases ha : evV g x .callByValuePar T E a p with
    | none => rw [evV_not_none ha]; exact Or.inl rfl
    | some v =>
      have hb := ih.eq_of_some ha
      cases v with
      | none => rw [evV_not_fail ha,evV_not_fail hb]; exact RLe.refl _
      | some j => rw [evV_not_ok ha,evV_not_ok hb]; exact RLe.refl _
  | .star a,he,hc,p,hp => by
    rw [evV_star,evV_star]
    exact evStar_mono p (fun q hq => evaluator es src g h x S T U hg hh hT hSound rows captures E a he hc q (Nat.le_trans hq hp))
  | .eps,_,_,_,_ | .any,_,_,_,_ | .chr _,_,_,_,_ | .range _ _,_,_,_,_ | .lit _,_,_,_,_ | .param _,_,_,_,_ => RLe.refl _
  | .dbg _,he,_,_,_ | .lam _ _,he,_,_,_ | .callParam _ _,he,_,_,_ | .invoke _ _ _,he,_,_,_ => False.elim he

end Shallot.MacroPeg.CBV.RecursiveProducedSimulation
