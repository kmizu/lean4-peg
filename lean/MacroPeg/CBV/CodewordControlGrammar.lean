import MacroPeg.CBV.CodewordControlFilter

/-! Split a control-selected codeword capture into consecutive Seq arguments.
The original control, rather than a maximal header scan, selects the capture. -/
namespace Shallot.MacroPeg.CBV.CodewordControlGrammar
open ClockFreezing (Table)
open CodewordControlFilter (Expr render filter wholeView)
open LastCodewordGrammar (pure_syntax syntax_eval stable_positive_result_eq)

def argument (A : MExp) (d : CodewordControlFilter.Expr) : MExp := .seq A (render A d)
def source (A b : MExp) : MGrammar := LastCodewordGrammar.source A b
def target (A : MExp) (d : CodewordControlFilter.Expr) (b : MExp) : MGrammar :=
  ⟨[⟨2,.seq (.param 0) (wholeView b)⟩,⟨1,filter A d⟩]⟩
def sourceEntry (A : MExp) (d : CodewordControlFilter.Expr) : MExp := .call 0 [argument A d]
def targetEntry (A : MExp) (d : CodewordControlFilter.Expr) : MExp :=
  .seq (.andP (argument A d)) (.seq (.andP (.call 1 [A])) (.call 0 [A,render A d]))

theorem source_firstOrder (A b : MExp) (ha : ParserPrefixFusion.Pure A)
    (hb : HelperArgument.Syntax 0 b) : (source A b).FirstOrder :=
  SelectedCodewordGrammar.source_firstOrder A b ha hb

theorem target_firstOrder (A : MExp) (d : CodewordControlFilter.Expr) (b : MExp) (ha : ParserPrefixFusion.Pure A)
    (hd : CodewordControlFilter.Pure d) (hb : HelperArgument.Syntax 0 b) :
    (target A d b).FirstOrder := by
  intro r hr
  simp only [target,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨True.intro,CodewordControlFilter.wholeView_firstOrder b (HelperArgument.firstOrder 0 b hb)⟩
  · exact HelperArgument.firstOrder 0 _ (CodewordControlFilter.filter_syntax A ha d hd)

theorem physical_agreement (A : MExp) (d : CodewordControlFilter.Expr) (b : MExp)
    (hA : ParserPrefixFusion.Pure A) (hd : CodewordControlFilter.Pure d)
    (hb : HelperArgument.Syntax 0 b) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (hcode : ∀ (x : List Char) p q, p≤x.length →
      evV (source A b) x .callByValuePar (tblV (source A b) x .callByValuePar 0) [] A p=some (some q) → C (pre x p q))
    (x : List Char) (n m p : Nat) (hp : p≤x.length) :
    evV (source A b) x .callByValuePar (tblV (source A b) x .callByValuePar (n+1)) [] (sourceEntry A d) p=
      evV (target A d b) x .callByValueSeq (tblV (target A d b) x .callByValueSeq (m+1)) [] (targetEntry A d) p := by
  let g := source A b
  let h := target A d b
  let T := tblV g x .callByValuePar n
  let U := tblV h x .callByValueSeq m
  let TS := tblV g x .callByValuePar (n+1)
  let US := tblV h x .callByValueSeq (m+1)
  let D := render A d
  let B := argument A d
  have hD : ParserPrefixFusion.Pure D := CodewordControlFilter.render_pure A hA d hd
  have hB : ParserPrefixFusion.Pure B := ⟨hA,hD⟩
  have hg := source_firstOrder A b hA hb
  have hT : SoundTV g x .callByValuePar T := tblV_sound hg (by decide : Strategy.callByValuePar≠.callByName) n
  have hOk := tblV_ok g x .callByValuePar n
  have hr : ruleAtM g.rules 0=some ⟨1,.seq A (.seq (.param 0) b)⟩ := rfl
  have hf : ruleAtM h.rules 0=some ⟨2,.seq (.param 0) (wholeView b)⟩ := rfl
  have hv : ruleAtM h.rules 1=some ⟨1,filter A d⟩ := rfl
  have hpure (E F : List (List Char)) (e : MExp) (he : ParserPrefixFusion.Pure e) (z : Nat) :
      evV g x .callByValuePar T E e z=evV h x .callByValueSeq US F e z :=
    ParserPrefixFusion.pure_eval g h x _ _ T US E F e he z
  have hraw : evV g x .callByValuePar TS [] B p=evV g x .callByValuePar T [] B p :=
    ParserPrefixFusion.pure_eval g g x _ _ TS T [] [] B hB p
  change evV g x .callByValuePar TS [] (.call 0 [B]) p=
    evV h x .callByValueSeq US [] (.seq (.andP B) (.seq (.andP (.call 1 [A])) (.call 0 [A,D]))) p
  rw [evV_call_par hr rfl (by decide)]
  simp only [evParArgs]
  rw [hraw]
  cases ha : evV g x .callByValuePar T [] B p with
  | none =>
    rw [evV_seq_none (show evV h x .callByValueSeq US [] (.andP B) p=none by
      rw [CallLookahead.evV_peek,←hpure [] [] B hB p,ha]; rfl)]
  | some result => cases result with
    | none =>
      rw [evV_seq_fail (show evV h x .callByValueSeq US [] (.andP B) p=some none by
        rw [CallLookahead.evV_peek,←hpure [] [] B hB p,ha]; rfl)]
    | some q =>
      have hq := evV_ok hOk B p hp q ha
      have harg := (hpure [] [] B hB p).symm.trans ha
      have hpre : evV h x .callByValueSeq US [] (.andP B) p=some (some p) := by
        rw [CallLookahead.evV_peek,harg]; rfl
      dsimp only []
      rw [valAt_tblV_succ hr _ hp,evV_seq_ok hpre]
      change evV g x .callByValuePar T [pre x p q] (.seq A (.seq (.param 0) b)) p=_
      change evV g x .callByValuePar T [] (.seq A D) p=some (some q) at ha
      cases ha0 : evV g x .callByValuePar T [] A p with
      | none => rw [evV_seq_none ha0] at ha; cases ha
      | some rr => cases rr with
        | none => rw [evV_seq_fail ha0] at ha; cases ha
        | some j =>
          rw [evV_seq_ok ha0] at ha
          have hj := evV_ok hOk A p hp j ha0
          let u := pre x p j
          let v := pre x j q
          have hconcat : pre x p q=u++v := SequenceArguments.pre_concat hp hq
            (WordStarFilter.success_prefix (by decide) hT [] A (ParserPrefixFusion.pure_firstOrder A hA) p j hp ha0).2
            (WordStarFilter.success_prefix (by decide) hT [] D (ParserPrefixFusion.pure_firstOrder D hD) j q hj ha).2
          have haE : evV g x .callByValuePar T [pre x p q] A p=some (some j) :=
            (ParserPrefixFusion.pure_eval g g x _ _ T T [pre x p q] [] A hA p).trans ha0
          rw [evV_seq_ok haE]
          have hu : C u := hcode x p j hp ((ParserPrefixFusion.pure_eval g g x _ _
            (tblV g x .callByValuePar 0) T [] [] A hA p).trans ha0)
          have hdE : evV g x .callByValuePar T [u] D j=some (some q) :=
            (ParserPrefixFusion.pure_eval g g x _ _ T T [u] [] D hD j).trans ha
          have heq := CodewordControlFilter.replay_success g x .callByValuePar (by decide) T hT hOk
            A (ParserPrefixFusion.pure_firstOrder A hA) hc u hu
            (fun z k hz hk => hcode x z k hz ((ParserPrefixFusion.pure_eval g g x _ _
              (tblV g x .callByValuePar 0) T [] [u] A hA z).trans hk))
            d j q hj hdE b (HelperArgument.firstOrder 0 b hb)
          rw [hconcat]
          change evV g x .callByValuePar T [u++v] (.seq (.param 0) b) j=_
          rw [heq]
          have hvcall : evV h x .callByValueSeq US [] (.call 1 [A]) p=
              evV g x .callByValuePar T [u] (filter A d) j := by
            rw [evV_call_seq hv rfl]
            simp only [evSeqArgs]
            rw [←hpure [] [] A hA p,ha0]
            dsimp only []
            rw [valAt_tblV_succ hv _ hj]
            exact (syntax_eval g h x _ _ T U hOk [u] (filter A d)
              (CodewordControlFilter.filter_syntax A hA d hd) j hj).symm
          have hfcall : evV h x .callByValueSeq US [] (.call 0 [A,D]) p=
              evV g x .callByValuePar T [u,v] (.seq (.param 0) (wholeView b)) q := by
            rw [evV_call_seq hf rfl]
            simp only [evSeqArgs]
            rw [←hpure [] [] A hA p,ha0]
            dsimp only []
            rw [←hpure [] [] D hD j,ha]
            dsimp only []
            rw [valAt_tblV_succ hf _ hq]
            exact (syntax_eval g h x _ _ T U hOk [u,v] (.seq (.param 0) (wholeView b))
              ⟨True.intro,CodewordControlFilter.wholeView_syntax b hb⟩ q hq).symm
          change _=(match evV h x .callByValueSeq US [] (.andP (.call 1 [A])) p with
            | some (some z) => evV h x .callByValueSeq US [] (.call 0 [A,D]) z | other => other)
          rw [CallLookahead.evV_peek,hvcall]
          cases evV g x .callByValuePar T [u] (filter A d) j with
          | none => rfl
          | some rr => cases rr with
            | none => rfl
            | some z => exact hfcall.symm

theorem entries_firstOrder (A : MExp) (d : CodewordControlFilter.Expr)
    (hA : ParserPrefixFusion.Pure A) (hd : CodewordControlFilter.Pure d) :
    (sourceEntry A d).FirstOrder ∧ (targetEntry A d).FirstOrder := by
  have ha := ParserPrefixFusion.pure_firstOrder A hA
  have hD := ParserPrefixFusion.pure_firstOrder _ (CodewordControlFilter.render_pure A hA d hd)
  exact ⟨⟨⟨ha,hD⟩,True.intro⟩,⟨ha,hD⟩,⟨ha,True.intro⟩,ha,hD,True.intro⟩

/-- Complete finite observations agree on the unchanged original string. -/
theorem observations_iff (A : MExp) (d : CodewordControlFilter.Expr) (b : MExp)
    (hA : ParserPrefixFusion.Pure A) (hd : CodewordControlFilter.Pure d)
    (hb : HelperArgument.Syntax 0 b) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (hcode : ∀ (x : List Char) p q, p≤x.length →
      evV (source A b) x .callByValuePar (tblV (source A b) x .callByValuePar 0) [] A p=some (some q) → C (pre x p q))
    (x : List Char) (r : Option (List Char)) :
    SObs (source A b) .callByValuePar (sourceEntry A d) x r ↔
      SObs (target A d b) .callByValueSeq (targetEntry A d) x r := by
  have heq := stable_positive_result_eq (source A b) (target A d b) x .callByValuePar .callByValueSeq
    (sourceEntry A d) (targetEntry A d)
    (fun n m => physical_agreement A d b hA hd hb hc hcode x n m x.length (Nat.le_refl _))
  rw [←decideObsV_iff (source_firstOrder A b hA hb) (by decide) (entries_firstOrder A d hA hd).1,
    ←decideObsV_iff (target_firstOrder A d b hA hd hb) (by decide) (entries_firstOrder A d hA hd).2]
  simp only [decideObsV,heq]

theorem language_translation (A : MExp) (d : CodewordControlFilter.Expr) (b : MExp)
    (hA : ParserPrefixFusion.Pure A) (hd : CodewordControlFilter.Pure d)
    (hb : HelperArgument.Syntax 0 b) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (hcode : ∀ (x : List Char) p q, p≤x.length →
      evV (source A b) x .callByValuePar (tblV (source A b) x .callByValuePar 0) [] A p=some (some q) → C (pre x p q)) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (source A b) .callByValuePar (sourceEntry A d) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target A d b,targetEntry A d,target_firstOrder A d b hA hd hb,(entries_firstOrder A d hA hd).2,
    fun x => observations_iff A d b hA hd hb hc hcode x (some [])⟩

end Shallot.MacroPeg.CBV.CodewordControlGrammar
