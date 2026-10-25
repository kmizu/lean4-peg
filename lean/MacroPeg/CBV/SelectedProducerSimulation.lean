import MacroPeg.CBV.SelectedProducerNormalization

namespace Shallot.MacroPeg.CBV.SelectedProducerSimulation
open SelectedProducerNormalization
open ClockFreezing (Table)
open RecursiveProducedSimulation (Captured)

structure Rows (orig : MGrammar) (ps : Selection) (x : List Char) (S T U : Table) : Prop where
  ordinary : ∀ i r, ruleAtM orig.rules i=some r → selected ps i=none → ∀ W, W∈words (subStrs x) r.arity →
    ∀ p, p≤x.length → RLe (valAt (T i W) p) (valAt (U i W) p)
  producer : ∀ i r, ruleAtM orig.rules i=some r → ∀ d, selected ps i=some d →
    ∀ w, w∈subStrs x → ∀ p j, Captured orig x S d.head w p j →
      RLe (valAt (T i [w]) p) (valAt (U i [w]) p)

structure Simulation (orig : MGrammar) (ps : Selection) (g h : MGrammar) (x : List Char) (S T U : Table) : Prop where
  sourceArity : SemanticBodyRewrite.ArityEq orig g
  targetArity : SemanticBodyRewrite.ArityEq orig h
  ok : OkTV x.length T
  sound : SoundTV g x .callByValuePar T
  rows : Rows orig ps x S T U
  captures : ∀ i r, ruleAtM orig.rules i=some r → ∀ d, selected ps i=some d → ∀ E p j, p≤x.length →
    evV g x .callByValuePar T E d.head p=some (some j) →
    evV h x .callByValuePar U E d.head p=some (some j) →
    evV orig x .callByValuePar S [] d.head p=some (some j)

theorem declaration (orig g : MGrammar) (ha : SemanticBodyRewrite.ArityEq orig g) (i : Nat) (r : MRule)
    (hr : ruleAtM orig.rules i=some r) : ∃ a, ruleAtM g.rules i=some a ∧ a.arity=r.arity := by
  have h := ha i
  cases hg : ruleAtM g.rules i with
  | none => simp [hr,hg] at h
  | some a => exact ⟨a,rfl,by simpa [hr,hg] using h.symm⟩

theorem missing (orig g : MGrammar) (ha : SemanticBodyRewrite.ArityEq orig g) (i : Nat)
    (hr : ruleAtM orig.rules i=none) : ruleAtM g.rules i=none := by
  have h := ha i
  cases hg : ruleAtM g.rules i with
  | none => rfl
  | some a => simp [hr,hg] at h

mutual
  /-- Ordinary rules retain arbitrary arity. Only the finitely selected unary
  producers require the capture invariant, established from their arguments. -/
  theorem evaluator (orig : MGrammar) (ps : Selection) (hc : check orig ps=true)
      (g h : MGrammar) (x : List Char) (S T U : Table) (sim : Simulation orig ps g h x S T U)
      (E : List (List Char)) : ∀ e, e.FirstOrder → conforms ps e=true → ∀ p, p≤x.length →
      RLe (evV g x .callByValuePar T E e p) (evV h x .callByValuePar U E e p)
    | .call i args,he,hcon,p,hp => by
      cases hr : ruleAtM orig.rules i with
      | none =>
        simp only [evV,missing orig g sim.sourceArity i hr,missing orig h sim.targetArity i hr]
        exact RLe.refl _
      | some r =>
        obtain ⟨a,ha,haa⟩ := declaration orig g sim.sourceArity i r hr
        obtain ⟨b,hb,hba⟩ := declaration orig h sim.targetArity i r hr
        cases hs : selected ps i with
        | none =>
          by_cases hlen : r.arity=args.length
          · rw [evV_call_par ha (haa.trans hlen) (by decide),evV_call_par hb (hba.trans hlen) (by decide)]
            have ih := argument_results orig ps hc g h x S T U sim E args he (Bool.and_eq_true_iff.mp hcon).1 p hp
            cases hv : evParArgs g x .callByValuePar T E args p with
            | none => exact Or.inl rfl
            | some v =>
              have hu := ih.eq_of_some hv
              rw [hu]
              cases v with
              | none => exact RLe.refl _
              | some W =>
                exact sim.rows.ordinary i r hr hs W ((mem_words _ _ _).mpr
                  ⟨(evPar_length args W hv).trans hlen.symm,evPar_mem hp args W hv⟩) p hp
          · have hga : a.arity≠args.length := by omega
            have hhb : b.arity≠args.length := by omega
            simp only [evV,ha,hb,if_neg hga,if_neg hhb]; exact RLe.refl _
        | some d =>
          have hsel := checked orig ps hc i r hr d hs
          have hga : a.arity=1 := haa.trans hsel.1
          have hhb : b.arity=1 := hba.trans hsel.1
          cases args with
          | nil => simp [evV,ha,hb,hga,hhb,RLe]
          | cons arg args => cases args with
            | cons arg2 args => simp [evV,ha,hb,hga,hhb,RLe]
            | nil =>
              rw [evV_call_par ha (by simpa using hga) (by decide),evV_call_par hb (by simpa using hhb) (by decide)]
              have harg := evaluator orig ps hc g h x S T U sim E arg he.1 (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcon).1).1 p hp
              simp only [evParArgs]
              cases ea : evV g x .callByValuePar T E arg p with
              | none => exact Or.inl rfl
              | some v =>
                have eb := harg.eq_of_some ea
                rw [eb]
                cases v with
                | none => exact RLe.refl _
                | some j =>
                  have hprefix := ReplayFusion.success_prefix sim.sound E arg he.1 p j hp ea
                  have heq : arg=d.head := (MExp.beqE_iff _ _).mp (by
                    simpa only [hs] using (Bool.and_eq_true_iff.mp hcon).2)
                  subst arg
                  exact sim.rows.producer i r hr d hs _ (pre_mem hp j) p j
                    ⟨⟨hp,hprefix.1,hprefix.2⟩,sim.captures i r hr d hs E p j hp ea eb⟩
    | .seq a b,he,hcon,p,hp => by
      have ih := evaluator orig ps hc g h x S T U sim E a he.1 (Bool.and_eq_true_iff.mp hcon).1 p hp
      cases ea : evV g x .callByValuePar T E a p with
      | none => rw [evV_seq_none ea]; exact Or.inl rfl
      | some v =>
        have eb := ih.eq_of_some ea
        cases v with
        | none => rw [evV_seq_fail ea,evV_seq_fail eb]; exact RLe.refl _
        | some j =>
          rw [evV_seq_ok ea,evV_seq_ok eb]
          exact evaluator orig ps hc g h x S T U sim E b he.2 (Bool.and_eq_true_iff.mp hcon).2 j (evV_ok sim.ok a p hp j ea)
    | .alt a b,he,hcon,p,hp => by
      have ih := evaluator orig ps hc g h x S T U sim E a he.1 (Bool.and_eq_true_iff.mp hcon).1 p hp
      cases ea : evV g x .callByValuePar T E a p with
      | none => rw [evV_alt_none ea]; exact Or.inl rfl
      | some v =>
        have eb := ih.eq_of_some ea
        cases v with
        | none =>
          rw [evV_alt_fail ea,evV_alt_fail eb]
          exact evaluator orig ps hc g h x S T U sim E b he.2 (Bool.and_eq_true_iff.mp hcon).2 p hp
        | some j => rw [evV_alt_ok ea,evV_alt_ok eb]; exact RLe.refl _
    | .notP a,he,hcon,p,hp => by
      have ih := evaluator orig ps hc g h x S T U sim E a he hcon p hp
      cases ea : evV g x .callByValuePar T E a p with
      | none => rw [evV_not_none ea]; exact Or.inl rfl
      | some v =>
        have eb := ih.eq_of_some ea
        cases v with
        | none => rw [evV_not_fail ea,evV_not_fail eb]; exact RLe.refl _
        | some j => rw [evV_not_ok ea,evV_not_ok eb]; exact RLe.refl _
    | .star a,he,hcon,p,hp => by
      rw [evV_star,evV_star]
      exact evStar_mono p (fun q hq => evaluator orig ps hc g h x S T U sim E a he hcon q (Nat.le_trans hq hp))
    | .eps,_,_,_,_ | .any,_,_,_,_ | .chr _,_,_,_,_ | .range _ _,_,_,_,_ | .lit _,_,_,_,_ | .param _,_,_,_,_ => RLe.refl _
    | .dbg _,he,_,_,_ | .lam _ _,he,_,_,_ | .invoke _ _ _,he,_,_,_ | .callParam _ _,he,_,_,_ => False.elim he

  theorem argument_results (orig : MGrammar) (ps : Selection) (hc : check orig ps=true)
      (g h : MGrammar) (x : List Char) (S T U : Table) (sim : Simulation orig ps g h x S T U)
      (E : List (List Char)) : ∀ args, MExp.FirstOrderArgs args → arguments ps args=true → ∀ p, p≤x.length →
      OLe (evParArgs g x .callByValuePar T E args p) (evParArgs h x .callByValuePar U E args p)
    | [],_,_,_,_ => OLe.refl _
    | a::args,he,hcon,p,hp => by
      have ih := evaluator orig ps hc g h x S T U sim E a he.1 (Bool.and_eq_true_iff.mp hcon).1 p hp
      cases ea : evV g x .callByValuePar T E a p with
      | none => rw [evPar_cons_none ea]; exact Or.inl rfl
      | some v =>
        have eb := ih.eq_of_some ea
        cases v with
        | none => rw [evPar_cons_fail ea,evPar_cons_fail eb]; exact OLe.refl _
        | some j =>
          rw [evPar_cons_ok ea,evPar_cons_ok eb]
          rcases argument_results orig ps hc g h x S T U sim E args he.2 (Bool.and_eq_true_iff.mp hcon).2 p hp with hh|hh
          · rw [hh]; exact Or.inl rfl
          · rw [hh]; exact OLe.refl _
end

end Shallot.MacroPeg.CBV.SelectedProducerSimulation
