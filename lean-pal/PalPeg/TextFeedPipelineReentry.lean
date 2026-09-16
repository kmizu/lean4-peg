import PalPeg.TextFeedPipelineResumeCredit

/-! Reenter the real outer verifier loop after a macro return. The loop
commit and its two startup feeds run on the existing physical configuration. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineReentry
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineVerifier PalPeg.TextFeedPipelineHandoff
open PalPeg.TextFeedPipelineBank
open PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineCoupled
open PalPeg.TextFeedPipelineSourceSafety PalPeg.VerifierFeedRefinement PalPeg.VerifierFeedRawPrimitive
open PalPeg.TextFeedPipelineInputMacro PalPeg.TextFeedPipelineMacroBoundary
open PalPeg.VerifierFeedSupplyProgress
variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _
attribute [local irreducible] ProgLangBank.runChunk

def second (rate : ℕ) : Task k :=
  .seq feedHead2 (liftVerify (GSVProgZLoop.stepProg rate))

/-- A source return dispatches the actual enclosing loop's idle, including
its physical queue maintenance. Residual skip frames need not be empty. -/
theorem return_idle {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) {Text : List (Fin k)} {n : ℕ}
    (x : Config e leftSym R rate) (u : Snapshot k)
    (hu : Valid e leftSym R rate Text n x u [verifyLoop rate]) (hz : x.1.1.1 ≠ 0)
    (hh : (next (taskEval e (fun j => (x.2 j).focus)) u.frames).2 = .halt) :
    ∃ v, Valid e leftSym R rate Text n
        (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) v
        [verifyBody rate, verifyLoop rate] ∧
      v.frames = [] ∧ v.model = u.model ∧ v.ideal = u.ideal ∧ v.dir = u.dir := by
  have hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      ([verifyBody rate, verifyLoop rate], some (.inr (.inl .idle))) := by
    rw [hu.control, next_render_suffix, hh]
    exact verify_start e _ rate
  obtain ⟨ticks, q, m, hn', ⟨tr, he, ht, hlen⟩, hr⟩ :=
    TextFeedPrefixBank.work_matches (Terminal := Terminal) hc hmb .idle
      (prefixModel u.model) u.qt1 u.mode1 u.qt2 u.mode2 u.model.vt.2.Txt2
      u.aux u.old u.dir hu.ready1
  have he' := exec_prefix he
  change Exec _ _ _ (tapes e u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir) tr at he'
  rw [← hu.physical] at he'
  obtain ⟨hyt, hby, hcy⟩ := run_selected e leftSym R rate x hu.boundary hz
    [verifyBody rate, verifyLoop rate] (.inr (.inl .idle)) hs tr he' (by omega)
  change applyTrace e.blank (tapes e u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir) tr =
    tapes e q m u.qt2 u.mode2 u.model u.aux u.old u.dir at ht
  rw [← hu.physical] at ht
  let v : Snapshot k := { u with qt1 := q, mode1 := m, frames := [] }
  exact ⟨v, ⟨hby, run_safe e leftSym R rate x hu.safe, hcy, hyt.trans ht,
    hr, hu.ready2, hu.refines⟩, rfl, rfl, rfl, rfl⟩

/-- Execute the mandatory stationary Txt2 feed, then expose precisely the
next macro's source frame, rather than assigning a fresh controller. -/
theorem second_feed {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) {Text : List (Fin k)} {n : ℕ}
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (x : Config e leftSym R rate) (u : Snapshot k)
    (hu : Valid e leftSym R rate Text n x u [second rate, verifyLoop rate])
    (hf : u.frames = []) (hz : x.1.1.1 ≠ 0) :
    ∃ v, Valid e leftSym R rate Text n
        (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) v [verifyLoop rate] ∧
      v.frames = [.code (GSVProgZLoop.stepProg rate)] ∧
      v.ideal = u.ideal ∧ v.dir = u.dir ∧ filled u.model ≤ filled v.model := by
  have hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      ([liftVerify (GSVProgZLoop.stepProg rate), verifyLoop rate],
        some (.inr (.inr (.inl (GSVProg.tX, true, .stay))))) := by
    rw [hu.control, hf]
    simp only [render, List.flatMap_nil, List.nil_append, second, feedHead2,
      stepStack_seq, stepStack_act]
  obtain ⟨q, m, ht, hby, hcy, h1, h2, hi, hs'⟩ :=
    TextFeedPipelineSourceSafety.run_instruction (Terminal := Terminal) hc hmb leftSym R rate x
      hu.safe hu.boundary hz [liftVerify (GSVProgZLoop.stepProg rate), verifyLoop rate]
      (GSVProg.tX, true, .stay) hs u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir
      hu.physical hu.ready1 hu.ready2 hb hm hn hu.refines
  simp only [stepTapes_stay, nextIndex, moveIndex, ite_self] at hi
  let v : Snapshot k := { u with
    qt2 := q
    mode2 := m
    model := VerifierFeedPrimitive.effect e (GSVProg.tX, true, .stay) u.model
    frames := [.code (GSVProgZLoop.stepProg rate)] }
  exact ⟨v, ⟨hby, hs', hcy, ht, h1, h2, hi⟩, rfl, rfl, rfl, effect_mono e _ u.model⟩

/-- The optional Q1 feed consumes one source action only when the cell is
blank. Otherwise the same source call proceeds directly to the Q2 feed. -/
theorem body_feed {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) {Text : List (Fin k)} {n : ℕ}
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (x : Config e leftSym R rate) (u : Snapshot k)
    (hu : Valid e leftSym R rate Text n x u [verifyBody rate, verifyLoop rate])
    (hf : u.frames = []) (hz : x.1.1.1 ≠ 0) :
    ∃ v, v.ideal = u.ideal ∧ v.dir = u.dir ∧
      ((Valid e leftSym R rate Text n
          (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) v
          [second rate, verifyLoop rate] ∧ v.frames = []) ∨
        (Valid e leftSym R rate Text n
          (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) v
          [verifyLoop rate] ∧ v.frames = [.code (GSVProgZLoop.stepProg rate)])) ∧
      filled u.model ≤ filled v.model := by
  by_cases hcell : (x.2 12).focus = e.blank
  · have hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
        stepStack (taskEval e (fun j => (x.2 j).focus))
          (feedHead :: [second rate, verifyLoop rate]) := by
      rw [hu.control, hf]
      simp only [render, List.flatMap_nil, List.nil_append, verifyBody, second, stepStack_seq]
    obtain ⟨q, m, ht, hby, hcy, h1, h2, hi, _⟩ :=
      TextFeedPipelineRefinement.run_feed1 (Terminal := Terminal) hc hmb leftSym R rate x
        hu.boundary hz [second rate, verifyLoop rate] hs hcell
        u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir
        hu.physical hu.ready1 hu.ready2 hb hm hn hu.refines
    let v : Snapshot k := { u with
      qt1 := q
      mode1 := m
      model := VerifierFeedRaw.fill1 e.blank e.mark u.model
      frames := [] }
    exact ⟨v, rfl, rfl, Or.inl ⟨⟨hby, run_safe e leftSym R rate x hu.safe,
      hcy, ht, h1, h2, hi⟩, rfl⟩, fill1_mono e.blank e.mark u.model⟩
  · have hg : taskEval e (fun j => (x.2 j).focus) (.inr (.inl .blankText)) = false :=
      decide_eq_false hcell
    have hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
        ([liftVerify (GSVProgZLoop.stepProg rate), verifyLoop rate],
          some (.inr (.inr (.inl (GSVProg.tX, true, .stay))))) := by
      rw [hu.control, hf]
      simp only [render, List.flatMap_nil, List.nil_append, verifyBody, feedHead, feedHead2,
        stepStack_seq, stepStack_ite, hg, Bool.false_eq_true, if_false, stepStack_skip, stepStack_act]
    obtain ⟨q, m, ht, hby, hcy, h1, h2, hi, hs'⟩ :=
      TextFeedPipelineSourceSafety.run_instruction (Terminal := Terminal) hc hmb leftSym R rate x
        hu.safe hu.boundary hz [liftVerify (GSVProgZLoop.stepProg rate), verifyLoop rate]
        (GSVProg.tX, true, .stay) hs u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir
        hu.physical hu.ready1 hu.ready2 hb hm hn hu.refines
    simp only [stepTapes_stay, nextIndex, moveIndex, ite_self] at hi
    let v : Snapshot k := { u with
      qt2 := q
      mode2 := m
      model := VerifierFeedPrimitive.effect e (GSVProg.tX, true, .stay) u.model
      frames := [.code (GSVProgZLoop.stepProg rate)] }
    exact ⟨v, rfl, rfl, Or.inr ⟨⟨hby, hs', hcy, ht, h1, h2, hi⟩, rfl⟩, effect_mono e _ u.model⟩

/-- The ideal encoding survives startup feeds. Its tape views restore
the same macro ghost state at the new physical endpoint. -/
theorem restart {e : Env k} {leftSym : Fin k} {R rate p r n₀ n : ℕ}
    {Text leftPat rightPat : List (Fin k)} {z : GSVerifierZ.VStateZ}
    {x y : Config e leftSym R rate} {u v : Snapshot k}
    {caller : Stack (TaskAct k) (TaskCond k)}
    (hu : Valid e leftSym R rate Text n₀ x u caller)
    (hfeed : VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
      leftPat rightPat Text rate p r n₀ u.model)
    (hghost : u.model.z = (z.1, z.2.head)) (hwf : GSVerifierZ.ZWf leftPat.length z.2)
    (hdir : u.dir = GSVProgZLoop.dirTape e.blank e.mark z.2.up 0)
    (hv : Valid e leftSym R rate Text n y v [verifyLoop rate])
    (hcode : v.frames = [.code (GSVProgZLoop.stepProg rate)])
    (hi : v.ideal = u.ideal) (hd : v.dir = u.dir) :
    Valid e leftSym R rate Text n y (annotate v z) [verifyLoop rate] ∧
      Start e Text leftPat rightPat rate p r n (annotate v z) z := by
  obtain ⟨he, hq, hh, hp⟩ := TextFeedPipelineMacroResult.initial_encoding hu.refines hfeed hghost
  have he' := hi.symm ▸ he
  have hf := (TextFeedPipelineMacroResult.feed_of_zencoding hv.refines he' hq hh hp).1
  exact ⟨annotate_valid hv z, ⟨hf, rfl, hwf, hd.trans hdir, hcode⟩⟩

/-- Without an intervening arrival slot, reentry takes exactly two or
three real worker calls. This includes both the outer-loop action and feeds. -/
theorem reenter {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) {Text : List (Fin k)} {n : ℕ}
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (x : Config e leftSym R rate) (u : Snapshot k)
    (hu : Valid e leftSym R rate Text n x u [verifyLoop rate])
    (hh : (next (taskEval e (fun j => (x.2 j).focus)) u.frames).2 = .halt)
    (hz : ∀ j < 3,
      ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[j] x).1.1.1 ≠ 0) :
    ∃ m v, (m = 2 ∨ m = 3) ∧
      Valid e leftSym R rate Text n
        ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m] x) v [verifyLoop rate] ∧
      v.frames = [.code (GSVProgZLoop.stepProg rate)] ∧ v.ideal = u.ideal ∧ v.dir = u.dir ∧
      filled u.model ≤ filled v.model := by
  let f := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
  obtain ⟨v, hv, hf, hmodel, hi, hd⟩ := return_idle hc hmb leftSym R rate x u hu (hz 0 (by omega)) hh
  have hmono : filled u.model ≤ filled v.model := by rw [hmodel]
  obtain ⟨w, hwi, hwd, hw, hwm⟩ := body_feed hc hmb leftSym R rate hb hm hn (f x) v hv hf
    (by simpa only [Function.iterate_one] using hz 1 (by omega))
  rcases hw with ⟨hw, hwf⟩ | ⟨hw, hwf⟩
  · obtain ⟨v', hv', hf', hi', hd', hm'⟩ := second_feed hc hmb leftSym R rate hb hm hn
      (f (f x)) w hw hwf
      (by simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using hz 2 (by omega))
    refine ⟨3, v', Or.inr rfl, ?_, hf', hi'.trans (hwi.trans hi), hd'.trans (hwd.trans hd),
      hmono.trans (hwm.trans hm')⟩
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using hv'
  · refine ⟨2, w, Or.inl rfl, ?_, hwf, hwi.trans hi, hwd.trans hd, hmono.trans hwm⟩
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using hw

/-- info: 'PalPeg.TextFeedPipelineReentry.reenter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reenter

/-- info: 'PalPeg.TextFeedPipelineReentry.restart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms restart

theorem reenter_macro {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) {Text leftPat rightPat : List (Fin k)} {n p r : ℕ}
    {z : GSVerifierZ.VStateZ}
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (x : Config e leftSym R rate) (u : Snapshot k)
    (hu : Valid e leftSym R rate Text n x u [verifyLoop rate])
    (hfeed : VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
      leftPat rightPat Text rate p r n u.model)
    (hghost : u.model.z = (z.1, z.2.head)) (hwf : GSVerifierZ.ZWf leftPat.length z.2)
    (hdir : u.dir = GSVProgZLoop.dirTape e.blank e.mark z.2.up 0)
    (hh : (next (taskEval e (fun j => (x.2 j).focus)) u.frames).2 = .halt)
    (hz : ∀ j < 3,
      ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[j] x).1.1.1 ≠ 0) :
    ∃ m v, (m = 2 ∨ m = 3) ∧
      Valid e leftSym R rate Text n
        ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m] x) v [verifyLoop rate] ∧
      Start e Text leftPat rightPat rate p r n v z ∧ filled u.model ≤ filled v.model := by
  obtain ⟨m, v, hm, hv, hcode, hi, hd, hmono⟩ := reenter hc hmb leftSym R rate hb hm hn x u hu hh hz
  obtain ⟨hv', hs⟩ := restart hu hfeed hghost hwf hdir hv hcode hi hd
  exact ⟨m, annotate v z, hm, hv', hs, hmono⟩

/-- info: 'PalPeg.TextFeedPipelineReentry.reenter_macro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reenter_macro

end PalPeg.TextFeedPipelineReentry
