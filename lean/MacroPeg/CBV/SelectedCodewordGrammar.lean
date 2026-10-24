import MacroPeg.CBV.SelectedCodewordVerification
import MacroPeg.CBV.LastCodewordGrammar
import MacroPeg.CBV.HelperArgument

/-! A fixed ordinary Seq grammar preserving the guarded repetition endpoint. -/
namespace Shallot.MacroPeg.CBV.SelectedCodewordGrammar
open ClockFreezing (Table)
open SelectedCodewordVerification (step argument verifier probe)
open LastCodewordGrammar (pure_syntax syntax_eval stable_positive_result_eq)

def source (A b : MExp) : MGrammar := LastCodewordGrammar.source A b
def target (A G b : MExp) : MGrammar := ⟨[⟨1,.seq A b⟩,⟨1,verifier (step A G)⟩]⟩
def sourceEntry (A G : MExp) : MExp := .call 0 [argument A G]
def guard (A G : MExp) : MExp := .alt (.notP (step A G)) (.andP (.call 1 [A]))
def targetEntry (A G : MExp) : MExp :=
  .seq (.andP (argument A G)) (.seq (guard A G) (.call 0 [argument A G]))

theorem source_firstOrder (A b : MExp) (hA : ParserPrefixFusion.Pure A)
    (hb : HelperArgument.Syntax 0 b) : (source A b).FirstOrder := by
  intro r hr
  simp only [source,LastCodewordGrammar.source,List.mem_singleton] at hr
  subst r
  exact ⟨ParserPrefixFusion.pure_firstOrder A hA,True.intro,HelperArgument.firstOrder 0 b hb⟩

theorem target_firstOrder (A G b : MExp) (hA : ParserPrefixFusion.Pure A)
    (hG : ParserPrefixFusion.Pure G)
    (hb : HelperArgument.Syntax 0 b) : (target A G b).FirstOrder := by
  intro r hr
  simp only [target,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨ParserPrefixFusion.pure_firstOrder A hA,HelperArgument.firstOrder 0 b hb⟩
  · have hs : (step A G).FirstOrder := ⟨ParserPrefixFusion.pure_firstOrder A hA,
      ParserPrefixFusion.pure_firstOrder A hA,ParserPrefixFusion.pure_firstOrder G hG⟩
    exact ⟨⟨⟨hs,True.intro⟩,hs⟩,True.intro⟩

/-- Complete partial agreement at every positive physical stage, on every
original input suffix. Failed and undefined arguments are included. -/
theorem physical_agreement (A G b : MExp) (hA : ParserPrefixFusion.Pure A)
    (hG : ParserPrefixFusion.Pure G)
    (hb : HelperArgument.Syntax 0 b) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (hcode : ∀ (x : List Char) p q, p≤x.length →
      evV (source A b) x .callByValuePar (tblV (source A b) x .callByValuePar 0) [] A p=some (some q) → C (pre x p q))
    (x : List Char) (n m p : Nat) (hp : p≤x.length) :
    evV (source A b) x .callByValuePar (tblV (source A b) x .callByValuePar (n+1)) [] (sourceEntry A G) p=
      evV (target A G b) x .callByValueSeq (tblV (target A G b) x .callByValueSeq (m+1)) [] (targetEntry A G) p := by
  let g := source A b
  let h := target A G b
  let T := tblV g x .callByValuePar n
  let U := tblV h x .callByValueSeq m
  let TS := tblV g x .callByValuePar (n+1)
  let US := tblV h x .callByValueSeq (m+1)
  let B := argument A G
  let S := step A G
  have hS : ParserPrefixFusion.Pure S := ⟨hA,hA,hG⟩
  have hB : ParserPrefixFusion.Pure B := hS
  have hr : ruleAtM g.rules 0=some ⟨1,.seq A (.seq (.param 0) b)⟩ := rfl
  have hf : ruleAtM h.rules 0=some ⟨1,.seq A b⟩ := rfl
  have hv : ruleAtM h.rules 1=some ⟨1,verifier S⟩ := rfl
  have hpure (E F : List (List Char)) (e : MExp) (he : ParserPrefixFusion.Pure e) (z : Nat) :
      evV g x .callByValuePar TS E e z=evV h x .callByValueSeq US F e z :=
    ParserPrefixFusion.pure_eval g h x _ _ TS US E F e he z
  change evV g x .callByValuePar TS [] (.call 0 [B]) p=
    evV h x .callByValueSeq US [] (.seq (.andP B) (.seq (guard A G) (.call 0 [B]))) p
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
      have hcall : evV h x .callByValueSeq US [] (.call 1 [A]) p=
          match evV g x .callByValuePar T [] A p with
          | some (some j) => evV g x .callByValuePar T [pre x p j] (verifier S) j
          | other => other := by
        rw [evV_call_seq hv rfl]
        simp only [evSeqArgs]
        have he : evV h x .callByValueSeq US [] A p=evV g x .callByValuePar T [] A p :=
          ParserPrefixFusion.pure_eval h g x _ _ US T [] [] A hA p
        rw [he]
        cases hz : evV g x .callByValuePar T [] A p with
        | none => rfl
        | some result => cases result with
          | none => rfl
          | some j =>
            have hj : j≤x.length := evV_ok (tblV_ok g x _ n) A p hp j hz
            dsimp only []
            rw [valAt_tblV_succ hv _ hj]
            exact (syntax_eval g h x _ _ T U (tblV_ok g x _ n) [pre x p j]
              (verifier S) ⟨⟨⟨pure_syntax S hS,True.intro⟩,pure_syntax S hS⟩,True.intro⟩ j hj).symm
      have hbody : evV h x .callByValueSeq US [] (.call 0 [B]) p=
          evV g x .callByValuePar T [pre x p q] (.seq A b) q := by
        rw [evV_call_seq hf rfl]
        simp only [evSeqArgs,harg]
        rw [valAt_tblV_succ hf _ hq]
        exact (syntax_eval g h x _ _ T U (tblV_ok g x _ n) [pre x p q]
          (.seq A b) ⟨pure_syntax A hA,hb⟩ q hq).symm
      have hlocal := SelectedCodewordVerification.actual_entry g x .callByValuePar (by decide) T
        (tblV_sound (source_firstOrder A b hA hb) (by decide) n) A G
        (ParserPrefixFusion.pure_firstOrder A hA) (ParserPrefixFusion.pure_firstOrder G hG)
        (fun E z => ParserPrefixFusion.pure_eval g g x _ _ T T E [] A hA z)
        (fun E z => ParserPrefixFusion.pure_eval g g x _ _ T T E [] S hS z) hc
        (fun z j hz he => hcode x z j hz ((ParserPrefixFusion.pure_eval g g x _ _
          (tblV g x .callByValuePar 0) T [] [] A hA z).trans he)) p q hp
        ((ParserPrefixFusion.pure_eval g g x _ _ T TS [] [] B hB p).trans ha) b
      have hguard : evV h x .callByValueSeq US [] (guard A G) p=
          CallLookahead.peek p (probe g x .callByValuePar T A G p) := by
        have he : evV h x .callByValueSeq US [] S p=evV g x .callByValuePar T [] S p :=
          ParserPrefixFusion.pure_eval h g x _ _ US T [] [] S hS p
        change evV h x .callByValueSeq US [] (.alt (.notP S) (.andP (.call 1 [A]))) p=_
        cases hz : evV g x .callByValuePar T [] S p with
        | none =>
          rw [evV_alt_none (evV_not_none (he.trans hz))]
          simp [probe,S,hz,CallLookahead.peek]
        | some result => cases result with
          | none =>
            rw [evV_alt_ok (evV_not_fail (he.trans hz))]
            simp [probe,S,hz,CallLookahead.peek]
          | some j =>
            rw [evV_alt_fail (evV_not_ok (he.trans hz)),CallLookahead.evV_peek,hcall]
            simp only [probe,show evV g x .callByValuePar T [] (step A G) p=some (some j) from hz]
            rfl
      rw [hlocal]
      change _=(match evV h x .callByValueSeq US [] (guard A G) p with
        | some (some j) => evV h x .callByValueSeq US [] (.call 0 [B]) j | other => other)
      rw [hguard]
      cases probe g x .callByValuePar T A G p with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some j => exact hbody.symm

theorem entries_firstOrder (A G : MExp) (hA : ParserPrefixFusion.Pure A)
    (hG : ParserPrefixFusion.Pure G) :
    (sourceEntry A G).FirstOrder ∧ (targetEntry A G).FirstOrder := by
  have ha := ParserPrefixFusion.pure_firstOrder A hA
  have hg := ParserPrefixFusion.pure_firstOrder G hG
  have hs : (step A G).FirstOrder := ⟨ha,ha,hg⟩
  exact ⟨⟨hs,True.intro⟩,hs,⟨hs,ha,True.intro⟩,hs,True.intro⟩

theorem observations_iff (A G b : MExp) (hA : ParserPrefixFusion.Pure A)
    (hG : ParserPrefixFusion.Pure G)
    (hb : HelperArgument.Syntax 0 b) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (hcode : ∀ (x : List Char) p q, p≤x.length →
      evV (source A b) x .callByValuePar (tblV (source A b) x .callByValuePar 0) [] A p=some (some q) → C (pre x p q))
    (x : List Char) (r : Option (List Char)) :
    SObs (source A b) .callByValuePar (sourceEntry A G) x r ↔
      SObs (target A G b) .callByValueSeq (targetEntry A G) x r := by
  have heq := stable_positive_result_eq (source A b) (target A G b) x .callByValuePar .callByValueSeq
    (sourceEntry A G) (targetEntry A G) (fun n m => physical_agreement A G b hA hG hb hc hcode x n m x.length (Nat.le_refl _))
  rw [←decideObsV_iff (source_firstOrder A b hA hb) (by decide) (entries_firstOrder A G hA hG).1,
    ←decideObsV_iff (target_firstOrder A G b hA hG hb) (by decide) (entries_firstOrder A G hA hG).2]
  simp only [decideObsV,heq]

theorem language_translation (A G b : MExp) (hA : ParserPrefixFusion.Pure A)
    (hG : ParserPrefixFusion.Pure G)
    (hb : HelperArgument.Syntax 0 b) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (hcode : ∀ (x : List Char) p q, p≤x.length →
      evV (source A b) x .callByValuePar (tblV (source A b) x .callByValuePar 0) [] A p=some (some q) → C (pre x p q)) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (source A b) .callByValuePar (sourceEntry A G) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target A G b,targetEntry A G,target_firstOrder A G b hA hG hb,(entries_firstOrder A G hA hG).2,
    fun x => observations_iff A G b hA hG hb hc hcode x (some [])⟩

end Shallot.MacroPeg.CBV.SelectedCodewordGrammar
