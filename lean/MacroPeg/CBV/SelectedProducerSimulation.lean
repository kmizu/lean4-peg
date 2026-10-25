import MacroPeg.CBV.SelectedProducerNormalization

namespace Shallot.MacroPeg.CBV.SelectedProducerSimulation
open SelectedProducerNormalization
open ClockFreezing (Table)
open RecursiveProducedSimulation (Captured)

structure Rows (orig : MGrammar) (ps : Selection) (x : List Char) (S T U : Table) : Prop where
  ordinary : ∀ i r, ruleAtM orig.rules i=some r → selected ps i=none → ∀ W, W∈words (subStrs x) r.arity →
    ∀ p, p≤x.length → RLe (valAt (T i W) p) (valAt (U i W) p)
  producer : ∀ i r, ruleAtM orig.rules i=some r → ∀ d, selected ps i=some d →
    ∀ W, W∈words (subStrs x) r.arity → ∀ w, W[r.arity-1]?=some w →
    ∀ p j, Captured orig x S d.head w p j → RLe (valAt (T i W) p) (valAt (U i W) p)

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
  /-- Ordinary rules retain arbitrary arity. Only the finitely selected nonempty-arity
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
              have hW : W∈words (subStrs x) r.arity := (mem_words _ _ _).mpr
                ⟨(evPar_length args W hv).trans hlen.symm,evPar_mem hp args W hv⟩
              cases hs : selected ps i with
              | none => exact sim.rows.ordinary i r hr hs W hW p hp
              | some d =>
                have hsel := checked orig ps hc i r hr d hs
                have hargBound : r.arity-1<args.length := by omega
                have hargGet := List.getElem?_eq_getElem hargBound
                have heq : args[r.arity-1]=d.head := (MExp.beqE_iff _ _).mp (by
                  have hh := (Bool.and_eq_true_iff.mp hcon).2
                  simpa only [hs,show args.length-1=r.arity-1 by omega,hargGet] using hh)
                have hD : args[r.arity-1]?=some d.head := by rw [hargGet,heq]
                have hWlen := evPar_length args W hv
                have hWBound : r.arity-1<W.length := by omega
                have hWGet := List.getElem?_eq_getElem hWBound
                obtain ⟨j,ea,eb,hw⟩ := argument_capture orig ps hc g h x S T U sim E args he
                  (Bool.and_eq_true_iff.mp hcon).1 p hp W hv (r.arity-1) d.head W[r.arity-1] hD hWGet
                have hprefix := ReplayFusion.success_prefix sim.sound E d.head
                  (ReplayFallbackFusion.closed_firstOrder _ hsel.2.2) p j hp ea
                exact sim.rows.producer i r hr d hs W hW _ hWGet p j
                  ⟨⟨hp,hprefix.1,by simpa only [hw] using hprefix.2⟩,sim.captures i r hr d hs E p j hp ea eb⟩
        · have hga : a.arity≠args.length := by omega
          have hhb : b.arity≠args.length := by omega
          simp only [evV,ha,hb,if_neg hga,if_neg hhb]; exact RLe.refl _
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

  /-- A successful full Par argument list supplies the selected captured
  word and both simulated evaluations of its actual argument expression. -/
  theorem argument_capture (orig : MGrammar) (ps : Selection) (hc : check orig ps=true)
      (g h : MGrammar) (x : List Char) (S T U : Table) (sim : Simulation orig ps g h x S T U)
      (E : List (List Char)) : ∀ args, MExp.FirstOrderArgs args → arguments ps args=true →
      ∀ p, p≤x.length → ∀ W, evParArgs g x .callByValuePar T E args p=some (some W) →
      ∀ (k : Nat) (a : MExp) (w : List Char), args[k]?=some a → W[k]?=some w → ∃ j,
        evV g x .callByValuePar T E a p=some (some j) ∧
        evV h x .callByValuePar U E a p=some (some j) ∧ w=pre x p j
    | [],_,_,_,_,_,_,_,_,_,hi,_ => by cases hi
    | b::args,he,hcon,p,hp,W,hv,k,a,w,hi,hw => by
      cases eb : evV g x .callByValuePar T E b p with
      | none => rw [evPar_cons_none eb] at hv; cases hv
      | some v => cases v with
        | none => rw [evPar_cons_fail eb] at hv; cases hv
        | some j =>
          rw [evPar_cons_ok eb] at hv
          cases ht : evParArgs g x .callByValuePar T E args p with
          | none => simp [ht] at hv
          | some v => cases v with
            | none => simp [ht] at hv
            | some V =>
              have hW : pre x p j::V=W := by simpa only [ht,Option.some.injEq] using hv
              subst W
              cases k with
              | zero =>
                simp only [List.getElem?_cons_zero,Option.some.injEq] at hi hw
                subst a; subst w
                exact ⟨j,eb,(evaluator orig ps hc g h x S T U sim E b he.1
                  (Bool.and_eq_true_iff.mp hcon).1 p hp).eq_of_some eb,rfl⟩
              | succ k =>
                exact argument_capture orig ps hc g h x S T U sim E args he.2
                  (Bool.and_eq_true_iff.mp hcon).2 p hp V ht k a w hi hw

end

end Shallot.MacroPeg.CBV.SelectedProducerSimulation
