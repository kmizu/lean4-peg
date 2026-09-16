import PalPeg.TextFeedPipelineMacroFit

/-! Apply the generic refinement to the actual zigzag step program. The
compiled endpoint has the old GS program's exact tapes and direction. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineMacroResult
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineCoupled
open PalPeg.TextFeedPipelineIdealEngine PalPeg.GSVTapes PalPeg.GSVTapesZ
open PalPeg.GSVerifierZ
variable {k : ℕ}

/-- Physical tape views determine both macro head indices; no alignment
assumption on the refinement witness is required. -/
theorem initial_encoding {e : Env k} {u : Snapshot k}
    {leftPat rightPat Text : List (Fin k)} {rate p r n : ℕ} {z : VStateZ}
    (hr : VerifierFeedRefinement.Refines e Text n u.model u.ideal u.i1 u.i2)
    (hf : VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
      leftPat rightPat Text rate p r n u.model)
    (hz : u.model.z = (z.1, z.2.head)) :
    VEncodesZ' e.blank e.startSym e.endSym e.mark leftPat rightPat
      (TextFeed.padW e.blank Text Text.length) rate p r u.ideal z ∧
      z.1.q ≤ rightPat.length ∧ z.2.head ≤ leftPat.length ∧ leftPat.length ≤ z.1.pos := by
  have hi1 := VerifierFeedRefinement.seq_index_eq hr.feed.one.view hf.scan.txt
  have hi2 := VerifierFeedRefinement.seq_index_eq hr.feed.two.view hf.txt2
  have he := (hi1 ▸ hi2 ▸ hr).encodes hf
  rw [hz] at he
  refine ⟨⟨he.scan, he.pat, he.txt2⟩, ?_, ?_, ?_⟩
  · simpa only [hz] using hf.qle
  · simpa only [hz] using hf.cle
  · simpa only [hz] using hf.posle

theorem bundle_injective {I J : VTapes' k} {d e : STape (Fin k)}
    (h : bundle I d = bundle J e) : I = J ∧ d = e := by
  have ht : GSVProg.vTS I = GSVProg.vTS J := by
    funext j
    have hj := congrFun h (Fin.castAdd 1 j)
    simpa only [bundle, Fin.append_left] using hj
  have hi := congrArg VerifierFeedPrimitive.fromTapes ht
  have hd := congrFun h (Fin.natAdd 10 (0 : Fin 1))
  exact ⟨by simpa only [VerifierFeedPrimitive.fromTapes_vTS] using hi,
    by simpa only [bundle, Fin.append_right] using hd⟩

theorem step_result {e : Env k} {u v : Snapshot k} {ws : List Event}
    {pattern Word : List (Fin k)} {rate p r : ℕ} {st : ScanState}
    (hrate : 0 < rate) (hmb : e.mark ≠ e.blank) (hstart : e.startSym ∉ pattern)
    (hE : GSTapes.Encodes' e.blank e.startSym e.endSym e.mark pattern Word rate p r u.ideal.1 st)
    (hq : st.q ≤ pattern.length) (up : Bool)
    (hdir : u.dir = GSVProgZLoop.dirTape e.blank e.mark up 0)
    (hcode : erase u.frames = [GSVProgZLoop.stepProg rate])
    (hend : Ends e (semanticInputs ws) (erase u.frames) (bundle u.ideal u.dir) [] (bundle v.ideal v.dir)) :
    v.ideal = vApplyActs' e.blank (vprogramZ' e.blank e.startSym e.endSym e.mark rate up u.ideal) u.ideal ∧
      v.dir = GSVProgZLoop.dirTape e.blank e.mark (vDirZ e.blank e.startSym e.endSym up u.ideal) 0 := by
  rw [semanticInputs_replicate, hcode, hdir] at hend
  have hr := GSVProgZLoop.stepProg_runsTo (Terminal := Unit) hrate hmb hstart hE hq up
  have he := hend.result_of_runsTo hr
  exact bundle_injective he

/-- A completed real compiled step has the concrete GS endpoint, with no
assumption relating its feed/idle overhead to the old program's cost. -/
theorem macro_return {e : Env k} (leftSym : Fin k) (R rate : ℕ)
    {Text : List (Fin k)} {n : ℕ} (x : Config e leftSym R rate) (u v : Snapshot k)
    (caller : Stack (TaskAct k) (TaskCond k)) (hv : Valid e leftSym R rate Text n x v caller)
    (hmb : e.mark ≠ e.blank) (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    {ws : List Event} (h : Follows e u ws v)
    (hw : (next (taskEval e (fun j => (x.2 j).focus)) v.frames).2 = .halt)
    {pattern Word : List (Fin k)} {p r : ℕ} {st : ScanState}
    (hrate : 0 < rate) (hstart : e.startSym ∉ pattern)
    (hE : GSTapes.Encodes' e.blank e.startSym e.endSym e.mark pattern Word rate p r u.ideal.1 st)
    (hq : st.q ≤ pattern.length) (up : Bool)
    (hdir : u.dir = GSVProgZLoop.dirTape e.blank e.mark up 0)
    (hcode : u.frames = [.code (GSVProgZLoop.stepProg rate)]) :
    v.ideal = vApplyActs' e.blank (vprogramZ' e.blank e.startSym e.endSym e.mark rate up u.ideal) u.ideal ∧
      v.dir = GSVProgZLoop.dirTape e.blank e.mark (vDirZ e.blank e.startSym e.endSym up u.ideal) 0 := by
  have he := follows_halted leftSym R rate x u v caller hv hmb hb hm hn h hw
  apply step_result hrate hmb hstart hE hq up hdir _ he
  simp only [hcode, erase, eraseFrame, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem encoding_of_result {e : Env k} {u v : Snapshot k}
    {leftPat rightPat Word : List (Fin k)} {rate p r : ℕ} {z : VStateZ}
    (hrate : 0 < rate) (hp : 0 < p) (hmb : e.mark ≠ e.blank)
    (hend : e.endSym ∉ rightPat) (hendu : e.endSym ∉ leftPat)
    (hstartu : e.startSym ∉ leftPat) (hse : e.startSym ≠ e.endSym)
    (hE : VEncodesZ' e.blank e.startSym e.endSym e.mark leftPat rightPat Word rate p r u.ideal z)
    (hwf : ZWf leftPat.length z.2) (hq : z.1.q ≤ rightPat.length) (hpos : leftPat.length ≤ z.1.pos)
    (hfit : (scanStep rightPat rate p r Word z.1).pos +
      (scanStep rightPat rate p r Word z.1).q < Word.length)
    (hresult : v.ideal = vApplyActs' e.blank
        (vprogramZ' e.blank e.startSym e.endSym e.mark rate z.2.up u.ideal) u.ideal ∧
      v.dir = GSVProgZLoop.dirTape e.blank e.mark (vDirZ e.blank e.startSym e.endSym z.2.up u.ideal) 0) :
    VEncodesZ' e.blank e.startSym e.endSym e.mark leftPat rightPat Word rate p r v.ideal
      (vStepZ leftPat rightPat rate p r Word z) ∧
    v.dir = GSVProgZLoop.dirTape e.blank e.mark (vStepZ leftPat rightPat rate p r Word z).2.up 0 := by
  obtain ⟨he, hd⟩ := vencodes_stepZ hrate hp hmb hend hendu hstartu hse hE hwf hq hpos hfit
  exact ⟨hresult.1 ▸ he, hresult.2.trans (congrArg (fun up => GSVProgZLoop.dirTape e.blank e.mark up 0) hd)⟩

/-- Restore the streaming macro invariant from its zigzag endpoint. Only
the ghost annotation changes; the real 39-tape bundle is literally equal. -/
theorem feed_of_zencoding {e : Env k} {leftPat rightPat Text : List (Fin k)}
    {rate p r n : ℕ} {v : Snapshot k} {z : VStateZ}
    (hf : VerifierFeedRefinement.Refines e Text n v.model v.ideal v.i1 v.i2)
    (he : VEncodesZ' e.blank e.startSym e.endSym e.mark leftPat rightPat
      (TextFeed.padW e.blank Text Text.length) rate p r v.ideal z)
    (hq : z.1.q ≤ rightPat.length) (hc : z.2.head ≤ leftPat.length) (hp : leftPat.length ≤ z.1.pos) :
    VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark leftPat rightPat Text rate p r n
      { v.model with z := (z.1, z.2.head) } ∧
    TextFeedPipelineVerifier.tapes e v.qt1 v.mode1 v.qt2 v.mode2
      { v.model with z := (z.1, z.2.head) } v.aux v.old v.dir =
      TextFeedPipelineVerifier.tapes e v.qt1 v.mode1 v.qt2 v.mode2 v.model v.aux v.old v.dir :=
  ⟨hf.feed_of_encodes ⟨he.scan, he.pat, he.txt2⟩ hq hc hp, rfl⟩

/-- End-to-end compiled macro correctness starting from the streaming
invariant, not an independently assumed ideal GS encoding. -/
theorem compiled_encoding {e : Env k} (leftSym : Fin k) (R rate : ℕ)
    {Text leftPat rightPat : List (Fin k)} {n₀ n p r : ℕ} {z : VStateZ}
    (x y : Config e leftSym R rate) (u v : Snapshot k)
    (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n₀ x u caller)
    (hv : Valid e leftSym R rate Text n y v caller)
    (hf : VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
      leftPat rightPat Text rate p r n₀ u.model)
    (hz : u.model.z = (z.1, z.2.head))
    (hmb : e.mark ≠ e.blank) (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    {ws : List Event} (h : Follows e u ws v)
    (hhalt : (next (taskEval e (fun j => (y.2 j).focus)) v.frames).2 = .halt)
    (hrate : 0 < rate) (hp : 0 < p)
    (hstart : e.startSym ∉ rightPat) (hend : e.endSym ∉ rightPat)
    (hendu : e.endSym ∉ leftPat) (hstartu : e.startSym ∉ leftPat)
    (hse : e.startSym ≠ e.endSym) (hwf : ZWf leftPat.length z.2)
    (hdir : u.dir = GSVProgZLoop.dirTape e.blank e.mark z.2.up 0)
    (hcode : u.frames = [.code (GSVProgZLoop.stepProg rate)]) :
    VEncodesZ' e.blank e.startSym e.endSym e.mark leftPat rightPat
      (TextFeed.padW e.blank Text Text.length) rate p r v.ideal
      (vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) z) ∧
    v.dir = GSVProgZLoop.dirTape e.blank e.mark
      (vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) z).2.up 0 := by
  obtain ⟨he, hq, _, hpos⟩ := initial_encoding hu.refines hf hz
  have hfinish := follows_halted leftSym R rate y u v caller hv hmb hb hm hn h hhalt
  rw [semanticInputs_replicate] at hfinish
  have hprog : erase u.frames = [GSVProgZLoop.stepProg rate] := by
    simp only [hcode, erase, eraseFrame, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hprog] at hfinish
  have hfit := TextFeedPipelineMacroFit.completed_fit hrate hp hmb hstart hend hendu hstartu hse
    he hwf hq hpos hv.refines hn hdir hfinish
  have hresult := macro_return leftSym R rate y u v caller hv hmb hb hm hn h hhalt
    hrate hstart he.scan hq z.2.up hdir hcode
  exact encoding_of_result hrate hp hmb hend hendu hstartu hse he hwf hq hpos hfit hresult

/-- info: 'PalPeg.TextFeedPipelineMacroResult.compiled_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compiled_encoding

/-- info: 'PalPeg.TextFeedPipelineMacroResult.macro_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms macro_return

/-- info: 'PalPeg.TextFeedPipelineMacroResult.encoding_of_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms encoding_of_result

/-- info: 'PalPeg.TextFeedPipelineMacroResult.feed_of_zencoding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms feed_of_zencoding

end PalPeg.TextFeedPipelineMacroResult
