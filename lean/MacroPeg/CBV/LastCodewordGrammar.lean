import MacroPeg.CBV.LastCodewordVerification
import MacroPeg.CBV.HelperArgument

/-! A fixed ordinary Seq grammar for last-preserving captures. The count
of captured headers is selected by the input, without a fixed bound. -/
namespace Shallot.MacroPeg.CBV.LastCodewordGrammar
open ClockFreezing (Table)
open LastCodewordVerification (verifier probe)

def source (A b : MExp) : MGrammar := ⟨[⟨1,.seq A (.seq (.param 0) b)⟩]⟩
def target (A b : MExp) : MGrammar := ⟨[⟨1,.seq A b⟩,⟨1,verifier A⟩]⟩
def sourceEntry (A : MExp) : MExp := .call 0 [LastCodewordRotation.argument A]
def targetEntry (A : MExp) : MExp :=
  .seq (.andP (LastCodewordRotation.argument A))
    (.seq (.andP (.call 1 [A])) (.call 0 [LastCodewordRotation.argument A]))

theorem pure_syntax : ∀ e, ParserPrefixFusion.Pure e → HelperArgument.Syntax 0 e
  | .seq a b, h | .alt a b, h => ⟨pure_syntax a h.1,pure_syntax b h.2⟩
  | .star a, h | .notP a, h => pure_syntax a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
  | .param _, h | .call _ _, h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem syntax_eval (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Table) (hOk : OkTV x.length T) (E : List (List Char))
    (e : MExp) (he : HelperArgument.Syntax 0 e) (p : Nat) (hp : p≤x.length) :
    evV g x s T E e p=evV h x t U E e p := by
  exact HelperArgument.eval_eq (bodies:=[]) (by intro i e hi; simp at hi)
    (by intro i e hi; simp at hi) x s t T U hOk (by intro i hi; simp at hi) E e he p hp

theorem source_firstOrder (A b : MExp) (hA : ParserPrefixFusion.Pure A)
    (hb : HelperArgument.Syntax 0 b) : (source A b).FirstOrder := by
  intro r hr
  simp only [source,List.mem_singleton] at hr
  subst r
  exact ⟨ParserPrefixFusion.pure_firstOrder A hA,True.intro,HelperArgument.firstOrder 0 b hb⟩

theorem target_firstOrder (A b : MExp) (hA : ParserPrefixFusion.Pure A)
    (hb : HelperArgument.Syntax 0 b) : (target A b).FirstOrder := by
  intro r hr
  simp only [target,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨ParserPrefixFusion.pure_firstOrder A hA,HelperArgument.firstOrder 0 b hb⟩
  · exact ⟨⟨ParserPrefixFusion.pure_firstOrder A hA,True.intro⟩,ParserPrefixFusion.pure_firstOrder A hA⟩

/-- Complete partial agreement at every positive physical stage, on every
original input suffix. Failed and undefined arguments are included. -/
theorem physical_agreement (A b : MExp) (hA : ParserPrefixFusion.Pure A)
    (hb : HelperArgument.Syntax 0 b) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (hcode : ∀ (x : List Char) p q, p≤x.length →
      evV (source A b) x .callByValuePar (tblV (source A b) x .callByValuePar 0) [] A p=some (some q) → C (pre x p q))
    (x : List Char) (n m p : Nat) (hp : p≤x.length) :
    evV (source A b) x .callByValuePar (tblV (source A b) x .callByValuePar (n+1)) [] (sourceEntry A) p=
      evV (target A b) x .callByValueSeq (tblV (target A b) x .callByValueSeq (m+1)) [] (targetEntry A) p := by
  let g := source A b
  let h := target A b
  let T := tblV g x .callByValuePar n
  let U := tblV h x .callByValueSeq m
  let TS := tblV g x .callByValuePar (n+1)
  let US := tblV h x .callByValueSeq (m+1)
  let B := LastCodewordRotation.argument A
  have hB : ParserPrefixFusion.Pure B := ⟨hA,hA⟩
  have hr : ruleAtM g.rules 0=some ⟨1,.seq A (.seq (.param 0) b)⟩ := rfl
  have hf : ruleAtM h.rules 0=some ⟨1,.seq A b⟩ := rfl
  have hv : ruleAtM h.rules 1=some ⟨1,verifier A⟩ := rfl
  have hpure (E F : List (List Char)) (e : MExp) (he : ParserPrefixFusion.Pure e) (z : Nat) :
      evV g x .callByValuePar TS E e z=evV h x .callByValueSeq US F e z :=
    ParserPrefixFusion.pure_eval g h x _ _ TS US E F e he z
  change evV g x .callByValuePar TS [] (.call 0 [B]) p=
    evV h x .callByValueSeq US [] (.seq (.andP B) (.seq (.andP (.call 1 [A])) (.call 0 [B]))) p
  rw [evV_call_par hr rfl (by decide)]
  simp only [evParArgs]
  cases ha : evV g x .callByValuePar TS [] B p with
  | none =>
    rw [evV_seq_none (show evV h x .callByValueSeq US [] (.andP B) p=none by
      rw [CallLookahead.evV_peek,←hpure [] [] B hB p,ha]; rfl)]
  | some result => cases result with
    | none =>
      rw [evV_seq_fail (show evV h x .callByValueSeq US [] (.andP B) p=some none by
        rw [CallLookahead.evV_peek,←hpure [] [] B hB p,ha]; rfl)]
    | some q =>
      have hq : q≤x.length := evV_ok (tblV_ok g x _ (n+1)) B p hp q ha
      have harg : evV h x .callByValueSeq US [] B p=some (some q) := (hpure [] [] B hB p).symm.trans ha
      have hpre : evV h x .callByValueSeq US [] (.andP B) p=some (some p) := by
        rw [CallLookahead.evV_peek,harg]; rfl
      dsimp only []
      rw [valAt_tblV_succ hr _ hp,evV_seq_ok hpre]
      have hcall : evV h x .callByValueSeq US [] (.call 1 [A]) p=probe g x .callByValuePar T A p := by
        rw [evV_call_seq hv rfl]
        simp only [evSeqArgs]
        have he : evV h x .callByValueSeq US [] A p=evV g x .callByValuePar T [] A p :=
          ParserPrefixFusion.pure_eval h g x _ _ US T [] [] A hA p
        rw [he]
        unfold probe
        cases hz : evV g x .callByValuePar T [] A p with
        | none => rfl
        | some result => cases result with
          | none => rfl
          | some j =>
            have hj : j≤x.length := evV_ok (tblV_ok g x _ n) A p hp j hz
            dsimp only []
            rw [valAt_tblV_succ hv _ hj]
            exact (syntax_eval g h x _ _ T U (tblV_ok g x _ n) [pre x p j]
              (verifier A) ⟨⟨pure_syntax A hA,True.intro⟩,pure_syntax A hA⟩ j hj).symm
      have hbody : evV h x .callByValueSeq US [] (.call 0 [B]) p=
          evV g x .callByValuePar T [pre x p q] (.seq A b) q := by
        rw [evV_call_seq hf rfl]
        simp only [evSeqArgs,harg]
        rw [valAt_tblV_succ hf _ hq]
        exact (syntax_eval g h x _ _ T U (tblV_ok g x _ n) [pre x p q]
          (.seq A b) ⟨pure_syntax A hA,hb⟩ q hq).symm
      have hlocal := LastCodewordVerification.actual_entry g x .callByValuePar (by decide) T
        (tblV_sound (source_firstOrder A b hA hb) (by decide) n) A
        (ParserPrefixFusion.pure_firstOrder A hA)
        (fun E z => ParserPrefixFusion.pure_eval g g x _ _ T T E [] A hA z) hc
        (fun z j hz he => hcode x z j hz ((ParserPrefixFusion.pure_eval g g x _ _
          (tblV g x .callByValuePar 0) T [] [] A hA z).trans he)) p q hp
        ((ParserPrefixFusion.pure_eval g g x _ _ T TS [] [] B hB p).trans ha) b
      rw [hlocal]
      change _=(match evV h x .callByValueSeq US [] (.andP (.call 1 [A])) p with
        | some (some j) => evV h x .callByValueSeq US [] (.call 0 [B]) j | other => other)
      rw [CallLookahead.evV_peek,hcall]
      cases probe g x .callByValuePar T A p with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some j => exact hbody.symm

theorem entries_firstOrder (A : MExp) (hA : ParserPrefixFusion.Pure A) :
    (sourceEntry A).FirstOrder ∧ (targetEntry A).FirstOrder := by
  have ha := ParserPrefixFusion.pure_firstOrder A hA
  have hb : (LastCodewordRotation.argument A).FirstOrder := ⟨ha,ha⟩
  exact ⟨⟨hb,True.intro⟩,hb,⟨ha,True.intro⟩,hb,True.intro⟩

/-- Positive-stage agreement suffices even when stage zero can fail early
on one side before reaching an uninitialized rule row on the other. -/
theorem stable_positive_result_eq (g h : MGrammar) (x : List Char) (s t : Strategy) (a b : MExp)
    (heq : ∀ n m, evV g x s (tblV g x s (n+1)) [] a x.length=
      evV h x t (tblV h x t (m+1)) [] b x.length) :
    evV g x s (tblV g x s (iterBoundV g x)) [] a x.length=
      evV h x t (tblV h x t (iterBoundV h x)) [] b x.length := by
  cases ha : evV g x s (tblV g x s (iterBoundV g x)) [] a x.length with
  | some v =>
    have hl := evV_lift (Nat.le_succ (iterBoundV g x)) ha
    have hb := (tblV_stable h x t (Nat.le_refl x.length)).mp
      ⟨1,(heq (iterBoundV g x) 0).symm.trans hl⟩
    exact hb.symm
  | none =>
    cases hb : evV h x t (tblV h x t (iterBoundV h x)) [] b x.length with
    | none => rfl
    | some v =>
      have hl := evV_lift (Nat.le_succ (iterBoundV h x)) hb
      have hh := (tblV_stable g x s (Nat.le_refl x.length)).mp
        ⟨1,(heq 0 (iterBoundV h x)).trans hl⟩
      rw [ha] at hh
      cases hh

theorem observations_iff (A b : MExp) (hA : ParserPrefixFusion.Pure A)
    (hb : HelperArgument.Syntax 0 b) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (hcode : ∀ (x : List Char) p q, p≤x.length →
      evV (source A b) x .callByValuePar (tblV (source A b) x .callByValuePar 0) [] A p=some (some q) → C (pre x p q))
    (x : List Char) (r : Option (List Char)) :
    SObs (source A b) .callByValuePar (sourceEntry A) x r ↔
      SObs (target A b) .callByValueSeq (targetEntry A) x r := by
  have heq := stable_positive_result_eq (source A b) (target A b) x .callByValuePar .callByValueSeq
    (sourceEntry A) (targetEntry A) (fun n m => physical_agreement A b hA hb hc hcode x n m x.length (Nat.le_refl _))
  rw [←decideObsV_iff (source_firstOrder A b hA hb) (by decide) (entries_firstOrder A hA).1,
    ←decideObsV_iff (target_firstOrder A b hA hb) (by decide) (entries_firstOrder A hA).2]
  simp only [decideObsV,heq]

theorem language_translation (A b : MExp) (hA : ParserPrefixFusion.Pure A)
    (hb : HelperArgument.Syntax 0 b) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (hcode : ∀ (x : List Char) p q, p≤x.length →
      evV (source A b) x .callByValuePar (tblV (source A b) x .callByValuePar 0) [] A p=some (some q) → C (pre x p q)) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (source A b) .callByValuePar (sourceEntry A) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target A b,targetEntry A,target_firstOrder A b hA hb,(entries_firstOrder A hA).2,
    fun x => observations_iff A b hA hb hc hcode x (some [])⟩

end Shallot.MacroPeg.CBV.LastCodewordGrammar
