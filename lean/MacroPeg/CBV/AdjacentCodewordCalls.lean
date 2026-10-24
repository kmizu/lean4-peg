import MacroPeg.CBV.AdjacentCodewordControl

/-! Actual Par and Seq calls agree while all parent-dependent control
stays in the original caller environment. -/
namespace Shallot.MacroPeg.CBV.AdjacentCodewordCalls
open ClockFreezing (Table)
open CodewordControlFilter (wholeView)
open LastCodewordGrammar (syntax_eval pure_syntax)

def argument (A : MExp) (d : CodewordControlFilter.Expr) : MExp :=
  .seq A (CodewordControlFilter.render A d)
def translated (user compare : Nat) (A : MExp) (d : CodewordControlFilter.Expr) : MExp :=
  .seq (.andP (argument A d))
    (.seq (.andP (AdjacentCodewordControl.filter A (.call compare [A]) (.seq .token d)))
      (.call user [A,CodewordControlFilter.render A d]))

/-- The caller environment is arbitrary; control tests can read any of its
parameters. The codeword header is independent, and control/tail have no
calls. The surrounding grammars may contain arbitrary other first-order rows. -/
theorem physical_agreement (g h : MGrammar) (hg : g.FirstOrder) (hh : h.FirstOrder)
    (sourceUser targetUser compare : Nat) (A b : MExp) (d : CodewordControlFilter.Expr)
    (hs : ruleAtM g.rules sourceUser=some ⟨1,.seq A (.seq (.param 0) b)⟩)
    (ht : ruleAtM h.rules targetUser=some ⟨2,.seq (.param 0) (wholeView b)⟩)
    (hv : ruleAtM h.rules compare=some ⟨1,.param 0⟩)
    (hA : ParserPrefixFusion.Pure A)
    (hd : HelperArgument.Syntax 0 (CodewordControlFilter.render A d))
    (hb : HelperArgument.Syntax 0 b)
    {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (hcode : ∀ (x : List Char) p q, p≤x.length →
      evV g x .callByValuePar (tblV g x .callByValuePar 0) [] A p=some (some q) → C (pre x p q))
    (x : List Char) (E : List (List Char)) (n m p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar (tblV g x .callByValuePar (n+1)) E (.call sourceUser [argument A d]) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq (m+1)) E (translated targetUser compare A d) p := by
  let T := tblV g x .callByValuePar n
  let U := tblV h x .callByValueSeq m
  let TS := tblV g x .callByValuePar (n+1)
  let US := tblV h x .callByValueSeq (m+1)
  let D := CodewordControlFilter.render A d
  let B := argument A d
  have hAF := ParserPrefixFusion.pure_firstOrder A hA
  have hDF := HelperArgument.firstOrder 0 D hd
  have hB : HelperArgument.Syntax 0 B := ⟨pure_syntax A hA,hd⟩
  have hT : SoundTV g x .callByValuePar T := tblV_sound hg (by decide : Strategy.callByValuePar≠.callByName) n
  have hOk := tblV_ok g x .callByValuePar n
  have transfer (F : List (List Char)) (e : MExp) (he : HelperArgument.Syntax 0 e)
      (z : Nat) (hz : z≤x.length) :
      evV g x .callByValuePar T F e z=evV h x .callByValueSeq US F e z :=
    syntax_eval g h x _ _ T US hOk F e he z hz
  have hraw : evV g x .callByValuePar TS E B p=evV g x .callByValuePar T E B p :=
    syntax_eval g g x _ _ TS T (tblV_ok _ _ _ _) E B hB p hp
  change evV g x .callByValuePar TS E (.call sourceUser [B]) p=
    evV h x .callByValueSeq US E (.seq (.andP B)
      (.seq (.andP (AdjacentCodewordControl.filter A (.call compare [A]) (.seq .token d)))
        (.call targetUser [A,D]))) p
  rw [evV_call_par hs rfl (by decide)]
  simp only [evParArgs]
  rw [hraw]
  cases harg : evV g x .callByValuePar T E B p with
  | none =>
    apply Eq.symm
    apply evV_seq_none
    rw [CallLookahead.evV_peek,←transfer E B hB p hp,harg]
    rfl
  | some result => cases result with
    | none =>
      apply Eq.symm
      apply evV_seq_fail
      rw [CallLookahead.evV_peek,←transfer E B hB p hp,harg]
      rfl
    | some q =>
      have hq := evV_ok hOk B p hp q harg
      have hargH := (transfer E B hB p hp).symm.trans harg
      have hpre : evV h x .callByValueSeq US E (.andP B) p=some (some p) := by
        rw [CallLookahead.evV_peek,hargH]; rfl
      dsimp only []
      rw [valAt_tblV_succ hs _ hp,evV_seq_ok hpre]
      change evV g x .callByValuePar T [pre x p q] (.seq A (.seq (.param 0) b)) p=_
      change evV g x .callByValuePar T E (.seq A D) p=some (some q) at harg
      cases ha : evV g x .callByValuePar T E A p with
      | none => rw [evV_seq_none ha] at harg; cases harg
      | some result => cases result with
        | none => rw [evV_seq_fail ha] at harg; cases harg
        | some j =>
          rw [evV_seq_ok ha] at harg
          have hj := evV_ok hOk A p hp j ha
          have haH := (transfer E A (pure_syntax A hA) p hp).symm.trans ha
          have hdH := (transfer E D hd j hj).symm.trans harg
          have hcH (z k : Nat) (hz : z≤x.length)
              (hk : evV h x .callByValueSeq US E A z=some (some k)) : C (pre x z k) :=
            hcode x z k hz ((ParserPrefixFusion.pure_eval g h x _ _
              (tblV g x .callByValuePar 0) US [] E A hA z).trans hk)
          have heq := AdjacentCodewordControl.physical_entry h hh x compare m hv A hAF hc E hcH
            d p j q hp haH hdH b (HelperArgument.firstOrder 0 b hb)
          have hconcat : pre x p q=pre x p j++pre x j q := SequenceArguments.pre_concat hp hq
            (WordStarFilter.success_prefix (by decide) hT E A hAF p j hp ha).2
            (WordStarFilter.success_prefix (by decide) hT E D hDF j q hj harg).2
          have haE : evV g x .callByValuePar T [pre x p q] A p=some (some j) :=
            (ParserPrefixFusion.pure_eval g g x _ _ T T [pre x p q] E A hA p).trans ha
          rw [evV_seq_ok haE]
          rw [transfer [pre x p q] (.seq (.param 0) b) ⟨True.intro,hb⟩ j hj,hconcat,heq]
          have hcall : evV h x .callByValueSeq US E (.call targetUser [A,D]) p=
              evV h x .callByValueSeq US [pre x p j,pre x j q]
                (.seq (.param 0) (wholeView b)) q := by
            rw [evV_call_seq ht rfl]
            simp only [evSeqArgs,haH]
            rw [hdH]
            dsimp only []
            rw [valAt_tblV_succ ht _ hq]
            exact syntax_eval h h x _ _ U US (tblV_ok _ _ _ _) [pre x p j,pre x j q]
              (.seq (.param 0) (wholeView b)) ⟨True.intro,CodewordControlFilter.wholeView_syntax b hb⟩ q hq
          change _=(match evV h x .callByValueSeq US E
              (.andP (AdjacentCodewordControl.filter A (.call compare [A]) (.seq .token d))) p with
            | some (some z) => evV h x .callByValueSeq US E (.call targetUser [A,D]) z | other => other)
          rw [CallLookahead.evV_peek]
          cases evV h x .callByValueSeq US E
              (AdjacentCodewordControl.filter A (.call compare [A]) (.seq .token d)) p with
          | none => rfl
          | some result => cases result with
            | none => rfl
            | some z => exact hcall.symm

/-- Agreement beyond any fixed ordinary-stage offset determines the same
stable partial result; early stages need not agree. -/
theorem stable_result_eq (g h : MGrammar) (x : List Char) (s t : Strategy) (a b : MExp)
    (offset : Nat)
    (heq : ∀ n m, evV g x s (tblV g x s (n+offset)) [] a x.length=
      evV h x t (tblV h x t (m+offset)) [] b x.length) :
    evV g x s (tblV g x s (iterBoundV g x)) [] a x.length=
      evV h x t (tblV h x t (iterBoundV h x)) [] b x.length := by
  cases ha : evV g x s (tblV g x s (iterBoundV g x)) [] a x.length with
  | some v =>
    have hl := evV_lift (show iterBoundV g x≤iterBoundV g x+offset by omega) ha
    have hb := (tblV_stable h x t (Nat.le_refl x.length)).mp
      ⟨offset,by simpa only [Nat.zero_add] using (heq (iterBoundV g x) 0).symm.trans hl⟩
    exact hb.symm
  | none =>
    cases hb : evV h x t (tblV h x t (iterBoundV h x)) [] b x.length with
    | none => rfl
    | some v =>
      have hl := evV_lift (show iterBoundV h x≤iterBoundV h x+offset by omega) hb
      have hh := (tblV_stable g x s (Nat.le_refl x.length)).mp
        ⟨offset,by simpa only [Nat.zero_add] using (heq 0 (iterBoundV h x)).trans hl⟩
      rw [ha] at hh
      cases hh

end Shallot.MacroPeg.CBV.AdjacentCodewordCalls
