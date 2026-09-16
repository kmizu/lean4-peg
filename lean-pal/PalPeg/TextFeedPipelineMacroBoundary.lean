import PalPeg.TextFeedPipelineMacroResult

/-! Restore a reusable streaming boundary without changing the physical
configuration or assuming bounds on the next verifier state. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineMacroBoundary
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineCoupled
open PalPeg.TextFeedPipelineMacroResult PalPeg.GSVTapesZ PalPeg.GSVerifierZ
variable {k : ℕ}

theorem step_wf {leftPat rightPat Word : List (Fin k)} {rate p r : ℕ} {z : VStateZ}
    (hw : ZWf leftPat.length z.2) :
    ZWf leftPat.length (vStepZ leftPat rightPat rate p r Word z).2 := by
  have hr : ZWf leftPat.length (zReset z.2) :=
    ⟨hw.1, hw.1, by simp [zReset]⟩
  unfold vStepZ
  split_ifs
  · exact hr
  · exact zMoves_wf zQuota hw
  · exact hr

theorem step_bounds {leftPat rightPat Word : List (Fin k)} {rate p r : ℕ} {z : VStateZ}
    (hw : ZWf leftPat.length z.2) (hq : z.1.q ≤ rightPat.length)
    (hp : leftPat.length ≤ z.1.pos) :
    (vStepZ leftPat rightPat rate p r Word z).1.q ≤ rightPat.length ∧
      (vStepZ leftPat rightPat rate p r Word z).2.head ≤ leftPat.length ∧
      leftPat.length ≤ (vStepZ leftPat rightPat rate p r Word z).1.pos := by
  refine ⟨?_, (step_wf hw).1, ?_⟩
  · simpa only [vStepZ_fst] using scanStep_q_le (k := rate) (p₁ := p) (r := r) (T := Word) hq
  · simpa only [vStepZ_fst] using hp.trans (scanStep_pos_le rightPat rate p r Word z.1)

def annotate (v : Snapshot k) (z : VStateZ) : Snapshot k :=
  { v with model := { v.model with z := (z.1, z.2.head) } }

/-- Every operational field is preserved, including both FIFO states and
the live call stack. Only the mathematical verifier annotation changes. -/
theorem annotate_valid {e : Env k} {leftSym : Fin k} {R rate n : ℕ}
    {Text : List (Fin k)} {x : Config e leftSym R rate} {v : Snapshot k}
    {caller : Stack (TaskAct k) (TaskCond k)} (hv : Valid e leftSym R rate Text n x v caller)
    (z : VStateZ) : Valid e leftSym R rate Text n x (annotate v z) caller := by
  refine ⟨hv.boundary, hv.safe, hv.control, hv.physical, hv.ready1, hv.ready2, ?_⟩
  refine ⟨?_, hv.refines.one, hv.refines.two, hv.refines.other⟩
  have h1 := hv.refines.feed.one
  have h2 := hv.refines.feed.two
  exact ⟨⟨h1.view, h1.buf, h1.qinv, h1.qlist, h1.m2le, h1.hle⟩,
    ⟨h2.view, h2.buf, h2.qinv, h2.qlist, h2.m2le, h2.hle⟩⟩

theorem restore {e : Env k} {leftSym : Fin k} {R rate n₀ n p r : ℕ}
    {Text leftPat rightPat : List (Fin k)} {x : Config e leftSym R rate}
    {u v : Snapshot k} {caller : Stack (TaskAct k) (TaskCond k)} {z : VStateZ}
    (hv : Valid e leftSym R rate Text n x v caller)
    (hf : VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
      leftPat rightPat Text rate p r n₀ u.model)
    (hz : u.model.z = (z.1, z.2.head)) (hw : ZWf leftPat.length z.2)
    (he : VEncodesZ' e.blank e.startSym e.endSym e.mark leftPat rightPat
      (TextFeed.padW e.blank Text Text.length) rate p r v.ideal
      (vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) z)) :
    let z' := vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) z
    Valid e leftSym R rate Text n x (annotate v z') caller ∧
      VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
        leftPat rightPat Text rate p r n (annotate v z').model ∧
      ZWf leftPat.length z'.2 := by
  have hq : z.1.q ≤ rightPat.length := by simpa only [hz] using hf.qle
  have hp : leftPat.length ≤ z.1.pos := by simpa only [hz] using hf.posle
  obtain ⟨hq', hc', hp'⟩ := step_bounds (rate := rate) (p := p) (r := r)
    (Word := TextFeed.padW e.blank Text Text.length) hw hq hp
  exact ⟨annotate_valid hv _, (feed_of_zencoding hv.refines he hq' hc' hp').1, step_wf hw⟩

/-- A finished compiled macro returns the full boundary invariant for
the next macro, while retaining the actual endpoint configuration. -/
theorem compiled_boundary {e : Env k} (leftSym : Fin k) (R rate : ℕ)
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
    let z' := vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) z
    Valid e leftSym R rate Text n y (annotate v z') caller ∧
      VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
        leftPat rightPat Text rate p r n (annotate v z').model ∧
      ZWf leftPat.length z'.2 ∧
      (annotate v z').dir = GSVProgZLoop.dirTape e.blank e.mark z'.2.up 0 ∧
      (annotate v z').model.z = (z'.1, z'.2.head) := by
  obtain ⟨he, hd⟩ := compiled_encoding leftSym R rate x y u v caller hu hv hf hz
    hmb hb hm hn h hhalt hrate hp hstart hend hendu hstartu hse hwf hdir hcode
  obtain ⟨hv', hf', hw'⟩ := restore hv hf hz hwf he
  exact ⟨hv', hf', hw', hd, rfl⟩

/-- info: 'PalPeg.TextFeedPipelineMacroBoundary.compiled_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compiled_boundary

/-- info: 'PalPeg.TextFeedPipelineMacroBoundary.restore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms restore

end PalPeg.TextFeedPipelineMacroBoundary
