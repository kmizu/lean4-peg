import PalPeg.TextFeedPipelineReport
import PalPeg.TextFeedPipelineReentry

/-! Integrate the physical report reader into the finite pipeline control.
Every source call uses 94 existing microsteps followed by two observation
slots. Only the outer verifier-loop boundary is sampled. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineOutput
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2
open PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelineCoupled PalPeg.TextFeedPipelineReport
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl
variable {k : ℕ} {Terminal : Type}

private theorem phaseRun_append {Ctrl Γ : Type} {t B : ℕ}
    (blank : Γ) (body : PhaseBody Terminal Ctrl Γ t B)
    (as bs : List (Option Terminal)) (p : Fin B) (x : Ctrl × (Fin t → STape Γ)) :
    phaseRun blank body (as ++ bs) p x =
      phaseRun blank body bs (nextPhase^[as.length] p) (phaseRun blank body as p x) := by
  induction as generalizing p x with
  | nil => rfl
  | cons a as ih =>
    simp only [List.cons_append, phaseRun_cons, List.length_cons, Function.iterate_succ_apply, ih]

abbrev Core (e : Env k) (leftSym : Fin k) (R rate : ℕ) :=
  CallCtrl (programs e) (Outer e leftSym R rate)

abbrev State (e : Env k) (leftSym : Fin k) (R rate : ℕ) :=
  Core e leftSym R rate × Role × Bool

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

/-- This finite continuation is reached by the enclosing loop's idle.
No source-frame ghost or unbounded input position is inspected. -/
noncomputable def atBoundary (rate : ℕ) {e : Env k} {leftSym : Fin k} {R : ℕ}
    (c : Core e leftSym R rate) : Bool :=
  decide (c.1.2.2.val = [verifyBody rate, verifyLoop rate])

theorem atBoundary_of_valid {e : Env k} {leftSym : Fin k} {R rate n : ℕ}
    {Text : List (Fin k)} {x : Config e leftSym R rate} {u : Snapshot k}
    (hu : Valid e leftSym R rate Text n x u [verifyBody rate, verifyLoop rate])
    (hf : u.frames = []) : atBoundary rate x.1 = true := by
  apply decide_eq_true
  simpa only [hf, TextFeedPipelineFrames.render, List.flatMap_nil, List.nil_append] using hu.control

noncomputable def baseBody (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    PhaseBody Terminal (Core e leftSym R rate) (Fin k) 39 94 :=
  callBody (programs e) (fun _ => interp e) (choose e leftSym R rate) (by decide)

noncomputable def body (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    PhaseBody Terminal (State e leftSym R rate) (Fin k) 39 96 := fun q a ph σ =>
  if h : ph.val < 94 then
    let r := baseBody e leftSym R rate q.1 a ⟨ph.val, h⟩ σ
    ((r.1, q.2.1, if ph.val = 0 ∧ q.1.1.1 = 0 then false else q.2.2), r.2)
  else if atBoundary rate q.1 then
    let r := (reader e).micro (decide (ph.val = 95), q.2.1, false) none σ
    ((q.1, r.1.2.1, q.2.2 || r.1.2.2), r.2)
  else (q, fun j => (σ j, .stay))

noncomputable def initial (e : Env k) (leftSym : Fin k) (R rate : ℕ) : State e leftSym R rate :=
  (((0, true, startCtrlS (task e leftSym rate)), encode (.prefix .idle),
    initialBank (programs e), false), .front, false)

noncomputable def call (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    StructuredMachine Terminal (State e leftSym R rate × Fin 96) (Fin k) 39 96 :=
  ofPhases (by decide) (by decide) e.blank (initial e leftSym R rate)
    (fun q => q.2.2) (body e leftSym R rate)

/-- One real symbol is captured once; no symbol is repeated internally. -/
noncomputable def machine (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ) :=
  frameMachine (call e leftSym R rate) (DualQueueShared.capture enc) ((R + 1) * 96)

theorem body_work (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (ph : Fin 96) (hp : ph.val < 94) (a : Option Terminal)
    (c : Core e leftSym R rate) (ρ : Role) (b : Bool) (T : Fin 39 → STape (Fin k)) :
    bodyStep e.blank (body e leftSym R rate) ph a ((c, ρ, b), T) =
      let y := bodyStep e.blank (baseBody e leftSym R rate) ⟨ph.val, hp⟩ a (c, T)
      ((y.1, ρ, if ph.val = 0 ∧ c.1.1 = 0 then false else b), y.2) := by
  simp only [bodyStep, body, dif_pos hp]

/-- The existing worker is unchanged in the first 94 slots. -/
theorem work_tail (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (as : List (Option Terminal)) (ph : Fin 96) (hp : ph.val < 94)
    (hpos : 0 < ph.val) (hlen : ph.val + as.length ≤ 94)
    (c : Core e leftSym R rate) (ρ : Role) (b : Bool) (T : Fin 39 → STape (Fin k)) :
    phaseRun e.blank (body e leftSym R rate) as ph ((c, ρ, b), T) =
      let y := phaseRun e.blank (baseBody e leftSym R rate) as ⟨ph.val, hp⟩ (c, T)
      ((y.1, ρ, b), y.2) := by
  induction as generalizing ph c T with
  | nil => rfl
  | cons a as ih =>
    have hnz : ¬ (ph.val = 0 ∧ c.1.1 = 0) := by omega
    rw [phaseRun_cons, body_work e leftSym R rate ph hp, if_neg hnz]
    by_cases he : as = []
    · subst as
      rfl
    have hstep : ph.val + 1 < 94 := by
      have hl := List.length_pos_iff.mpr he
      simp only [List.length_cons] at hlen
      omega
    have hn96 : ph.val + 1 < 96 := by omega
    have hnext : (nextPhase ph).val < 94 := by simp only [nextPhase, dif_pos hn96]; exact hstep
    rw [ih (nextPhase ph) hnext (by simp only [nextPhase, dif_pos hn96]; omega)
      (by simp only [nextPhase, dif_pos hn96]; simp only [List.length_cons] at hlen; omega)]
    simp only [phaseRun_cons, nextPhase, dif_pos hstep, dif_pos hn96]

theorem work_block (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (c : Core e leftSym R rate) (ρ : Role) (b : Bool) (T : Fin 39 → STape (Fin k)) :
    phaseRun e.blank (body e leftSym R rate) (List.replicate 94 (none : Option Terminal)) 0 ((c, ρ, b), T) =
      let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate (c, T)
      ((y.1, ρ, if c.1.1 = 0 then false else b), y.2) := by
  have hbase := callBody_block (programs e) (fun _ => interp (Terminal := Terminal) e)
    (choose e leftSym R rate) 93 e.blank (c, T)
  change phaseRun e.blank (baseBody e leftSym R rate) (none :: List.replicate 93 none) 0 (c, T) = _ at hbase
  rw [List.replicate_succ, phaseRun_cons, body_work e leftSym R rate 0 (by decide)]
  have hn96 : nextPhase (0 : Fin 96) = 1 := by decide
  have hn94 : nextPhase (0 : Fin 94) = 1 := by decide
  simp only [Fin.val_zero, true_and, hn96]
  rw [work_tail e leftSym R rate (List.replicate 93 none) 1 (by decide) (by decide) (by simp)]
  rw [phaseRun_cons] at hbase
  rw [hn94] at hbase
  exact congrArg (fun y => ((y.1, ρ, if c.1.1 = 0 then false else b), y.2)) hbase

/-- Observation changes neither source control nor input time. -/
noncomputable def sample (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : State e leftSym R rate × (Fin 39 → STape (Fin k))) :=
  if atBoundary rate x.1.1 then
    let y := (reader e).sRound ⟨(false, x.1.2.1, false), x.2⟩ ()
    ((x.1.1, y.state.2.1, x.1.2.2 || y.state.2.2), y.tape)
  else x

theorem body_probe (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (c : Core e leftSym R rate) (ρ : Role) (b : Bool) (T : Fin 39 → STape (Fin k))
    (hc : atBoundary rate c = true) :
    bodyStep e.blank (body (Terminal := Terminal) e leftSym R rate) 94 none ((c, ρ, b), T) =
      ((c, frontRole e (T 10).focus, b), probe e (frontRole e (T 10).focus) T) := by
  have h := reader_probe e ρ false T none
  have hh := congrArg (fun y => ((c, y.state.2.1, b || y.state.2.2), y.tape)) h
  simp only [bodyStep, body, dif_neg (show ¬ (94 : Fin 96).val < 94 by decide), hc, ↓reduceIte]
  rw [show decide ((94 : Fin 96).val = 95) = false by decide]
  simp only [Bool.or_false] at hh
  exact hh

theorem body_restore (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (c : Core e leftSym R rate) (ρ : Role) (b : Bool) (T : Fin 39 → STape (Fin k))
    (hc : atBoundary rate c = true) :
    bodyStep e.blank (body (Terminal := Terminal) e leftSym R rate) 95 none ((c, ρ, b), T) =
      ((c, ρ, b || report e (fun j => (T j).focus) (T (frontIdx ρ)).focus), restore e ρ T) := by
  have h := reader_restore e ρ false T none
  have hh := congrArg (fun y => ((c, y.state.2.1, b || y.state.2.2), y.tape)) h
  simp only [bodyStep, body, dif_neg (show ¬ (95 : Fin 96).val < 94 by decide), hc, ↓reduceIte]
  exact hh

theorem body_no_sample (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (ph : Fin 96) (hp : ¬ ph.val < 94) (c : Core e leftSym R rate)
    (ρ : Role) (b : Bool) (T : Fin 39 → STape (Fin k)) (hc : atBoundary rate c = false) :
    bodyStep e.blank (body (Terminal := Terminal) e leftSym R rate) ph none ((c, ρ, b), T) =
      ((c, ρ, b), T) := by
  simp [bodyStep, body, dif_neg hp, hc, STape.applyAction]

theorem read_slots (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (c : Core e leftSym R rate) (ρ : Role) (b : Bool) (T : Fin 39 → STape (Fin k)) :
    phaseRun e.blank (body (Terminal := Terminal) e leftSym R rate) [none, none] 94 ((c, ρ, b), T) =
      sample e leftSym R rate ((c, ρ, b), T) := by
  simp only [phaseRun_cons, phaseRun_nil]
  have hn : nextPhase (94 : Fin 96) = 95 := by decide
  rw [hn]
  cases hc : atBoundary rate c with
  | false =>
    rw [body_no_sample e leftSym R rate 94 (by decide) c ρ b T hc,
      body_no_sample e leftSym R rate 95 (by decide) c ρ b T hc]
    simp only [sample, hc, Bool.false_eq_true, ↓reduceIte]
  | true =>
    rw [body_probe e leftSym R rate c ρ b T hc, body_restore e leftSym R rate _ _ _ _ hc]
    simp only [sample, hc, ↓reduceIte, reader_round]

noncomputable def step (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : State e leftSym R rate × (Fin 39 → STape (Fin k))) :=
  let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate (x.1.1, x.2)
  sample e leftSym R rate ((y.1, x.1.2.1, if x.1.1.1.1 = 0 then false else x.1.2.2), y.2)

theorem step_counter (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : State e leftSym R rate × (Fin 39 → STape (Fin k))) :
    (step (Terminal := Terminal) e leftSym R rate x).1.1.1.1 = nextPhase x.1.1.1.1 := by
  simp only [step, sample]
  split <;> exact TextFeedPipelineControl.run_counter e leftSym R rate _

theorem step_counter_iterate (e : Env k) (leftSym : Fin k) (R rate N : ℕ)
    (x : State e leftSym R rate × (Fin 39 → STape (Fin k))) :
    ((step (Terminal := Terminal) e leftSym R rate)^[N] x).1.1.1.1 =
      nextPhase^[N] x.1.1.1.1 := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', step_counter, ih, Function.iterate_succ_apply']

theorem call_noneBlock (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : State e leftSym R rate × (Fin 39 → STape (Fin k))) :
    (List.replicate 96 none).foldl (call (Terminal := Terminal) e leftSym R rate).sMicroStep
      ⟨(x.1, 0), x.2⟩ =
      let y := step (Terminal := Terminal) e leftSym R rate x
      ⟨(y.1, 0), y.2⟩ := by
  rw [call, ofPhases_foldl]
  have h96 : nextPhase^[96] (0 : Fin 96) = 0 := nextPhase_iterate_round (by decide)
  have h94 : nextPhase^[94] (0 : Fin 96) = 94 := nextPhase_iterate (by decide) 94 (by decide)
  simp only [List.length_replicate, h96]
  have hl : List.replicate 96 (none : Option Terminal) = List.replicate 94 none ++ [none, none] := by
    rw [show 96 = 94 + 2 from rfl, List.replicate_add]
    rfl
  rw [hl, phaseRun_append, List.length_replicate, h94, work_block, read_slots]
  rfl

theorem call_noneBlocks (e : Env k) (leftSym : Fin k) (R rate N : ℕ)
    (x : State e leftSym R rate × (Fin 39 → STape (Fin k))) :
    (List.replicate (N * 96) none).foldl (call (Terminal := Terminal) e leftSym R rate).sMicroStep
      ⟨(x.1, 0), x.2⟩ =
      let y := (step (Terminal := Terminal) e leftSym R rate)^[N] x
      ⟨(y.1, 0), y.2⟩ := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Nat.succ_mul, List.replicate_add, List.foldl_append, ih, call_noneBlock,
      Function.iterate_succ_apply']

/-- Exact real-input semantics of the reporting pipeline: one capture,
R+1 source calls, gated observations, and both clocks back at zero. -/
theorem machine_round (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (q : State e leftSym R rate) (T : Fin 39 → STape (Fin k)) (a : Terminal) :
    (machine e leftSym enc R rate).sRound ⟨((q, 0), 0), T⟩ a =
      let y := (step (Terminal := Terminal) e leftSym R rate)^[R + 1]
        (q, arriveA e.blank (DualQueueShared.capture enc) (some a) T)
      ⟨((y.1, 0), 0), y.2⟩ := by
  have hf := frameMachine_round (call e leftSym R rate) (DualQueueShared.capture enc)
    ((R + 1) * 96) a (q, 0) T
  have hb : (call (Terminal := Terminal) e leftSym R rate).blank = e.blank := rfl
  have hs := call_noneBlocks (Terminal := Terminal) e leftSym R rate (R + 1)
    (q, arriveA e.blank (DualQueueShared.capture enc) (some a) T)
  rw [hb, hs] at hf
  exact hf

/-- At the actual loop-return boundary the integrated observer reads
the ideal GS report and restores all 39 physical tapes. -/
theorem sample_report {e : Env k} (hc : Function.Injective e.code)
    {leftSym : Fin k} {R rate p r n : ℕ} {Text leftPat rightPat : List (Fin k)}
    {x : Config e leftSym R rate} {u : Snapshot k} {z : GSVerifierZ.VStateZ}
    (hu : Valid e leftSym R rate Text n x u [verifyBody rate, verifyLoop rate])
    (hf : u.frames = [])
    (hfeed : VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
      leftPat rightPat Text rate p r n u.model)
    (hghost : u.model.z = (z.1, z.2.head))
    (hdir : u.dir = GSVProgZLoop.dirTape e.blank e.mark z.2.up 0)
    (hb : e.blank ∉ Text) (hn : n ≤ Text.length) (hmb : e.mark ≠ e.blank)
    (hel : e.endSym ∉ leftPat) (her : e.endSym ∉ rightPat) (ρ : Role) (b : Bool) :
    sample e leftSym R rate ((x.1, ρ, b), x.2) =
      ((x.1, u.mode1.roles .front, b || GSVerifierZ.zReportFlag leftPat rightPat n z), x.2) := by
  have hgate := atBoundary_of_valid hu hf
  simp only [sample, hgate, ↓reduceIte]
  rw [hu.physical, reader_report hc hfeed hghost hdir hu.ready1 hb hn hmb hel her]

/-- Erasing the observer recovers the existing physical state. This is
valid throughout a verifier execution, not just at macro boundaries. -/
theorem sample_preserves {e : Env k} (hc : Function.Injective e.code)
    {leftSym : Fin k} {R rate n : ℕ} {Text : List (Fin k)}
    {x : Config e leftSym R rate} {u : Snapshot k} {caller : Stack (TaskAct k) (TaskCond k)}
    (hu : Valid e leftSym R rate Text n x u caller) (ρ : Role) (b : Bool) :
    let y := sample e leftSym R rate ((x.1, ρ, b), x.2)
    (y.1.1, y.2) = x := by
  unfold sample
  split
  · rw [hu.physical, reader_queue hc u hu.ready1]
    rw [← hu.physical]
  · rfl

theorem step_preserves {e : Env k} (hc : Function.Injective e.code)
    {leftSym : Fin k} {R rate n : ℕ} {Text : List (Fin k)}
    (x : State e leftSym R rate × (Fin 39 → STape (Fin k)))
    {u : Snapshot k} {caller : Stack (TaskAct k) (TaskCond k)}
    (hu : Valid e leftSym R rate Text n
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate (x.1.1, x.2)) u caller) :
    let y := step (Terminal := Terminal) e leftSym R rate x
    (y.1.1, y.2) = TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate (x.1.1, x.2) :=
  sample_preserves hc hu _ _

/-- The existing macro-return/reentry theorem triggers the integrated
observer on the very next source call; it is not a ghost reset. -/
theorem return_report {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) {Text leftPat rightPat : List (Fin k)} {n p r : ℕ}
    {x : Config e leftSym R rate} {u : Snapshot k} {z : GSVerifierZ.VStateZ}
    (hr : TextFeedPipelineInputMacro.Restored e leftSym R rate Text leftPat rightPat p r n
      x u [verifyLoop rate] z)
    (hb : e.blank ∉ Text) (hn : n ≤ Text.length)
    (hel : e.endSym ∉ leftPat) (her : e.endSym ∉ rightPat)
    (hz : x.1.1.1 ≠ 0) (ρ : Role) (b : Bool) :
    ∃ v, let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
      Valid e leftSym R rate Text n y v [verifyBody rate, verifyLoop rate] ∧ v.frames = [] ∧
      step (Terminal := Terminal) e leftSym R rate ((x.1, ρ, b), x.2) =
        ((y.1, v.mode1.roles .front, b || GSVerifierZ.zReportFlag leftPat rightPat n z), y.2) := by
  obtain ⟨hhalt, hv, hfeed, _, hdir, hghost⟩ := hr
  obtain ⟨v, hv', hf, hmodel, _, hdir'⟩ := TextFeedPipelineReentry.return_idle
    (Terminal := Terminal) hc hmb leftSym R rate x
      (TextFeedPipelineMacroBoundary.annotate u z) hv hz hhalt
  refine ⟨v, hv', hf, ?_⟩
  have hs := sample_report hc hv' hf (hmodel.symm ▸ hfeed)
    (by rw [hmodel]; exact hghost) (hdir'.trans hdir) hb hn hmb hel her ρ b
  simpa only [step, if_neg hz] using hs

/-- info: 'PalPeg.TextFeedPipelineOutput.machine_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms machine_round

/-- info: 'PalPeg.TextFeedPipelineOutput.sample_report' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sample_report

/-- info: 'PalPeg.TextFeedPipelineOutput.return_report' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms return_report

end PalPeg.TextFeedPipelineOutput
