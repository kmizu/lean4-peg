import PalPeg.TextFeedPipelineControl

/-! Physical bounded-call handoffs in the single pipeline controller.
The returned source continuation is retained by the machine itself. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineHandoff
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.PrepInstance
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

attribute [local irreducible] ProgLangBank.runChunk

/-- The generic worker call takes its instruction only from the current
finite continuation and tape symbols. -/
theorem run_selected (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (s' : Stack (TaskAct k) (TaskCond k)) (a : TaskAct k)
    (hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val = (s', some a))
    (tr : List (Fin 39 → Fin k × Move))
    (he : Exec (TextFeedPipelineBank.interp (Terminal := Terminal) e) e.blank (low e (taskLabel a)) x.2 tr)
    (hn : tr.length < 93) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    y.2 = applyTrace e.blank x.2 tr ∧ AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = s' := by
  have hsel : decode (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2 = taskLabel a := by
    simp only [TextFeedPipelineControl.choose, if_neg hz, hs, Option.getD_some, decode_encode]
  have hex : Exec (TextFeedPipelineControl.interp (Terminal := Terminal) e).toInterp e.blank
      (programs e (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2) x.2 tr := by
    change Exec (TextFeedPipelineBank.interp e) e.blank (low e (decode _)) x.2 tr
    rw [hsel]
    exact he
  obtain ⟨ht, hb', _, _⟩ := callRun_exec (programs e)
    (fun _ => TextFeedPipelineControl.interp (Terminal := Terminal) e) (choose e leftSym R rate) 93 e.blank x hb tr hex hn
  refine ⟨ht, hb', ?_⟩
  simp only [TextFeedPipelineControl.run, callRun, TextFeedPipelineControl.choose, if_neg hz, stepCtrlS_val, hs]

/-- Preparation resumes one primitive step on the actual shared view.
The continuation suffix may contain the entire prefix/verifier pipeline. -/
theorem run_prep_step (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (taskEval e (fun j => (x.2 j).focus)) (s.map liftPrep ++ r)) (a : PrepAct k)
    (ha : (stepStack (evalConds (TextFeedPrepResume.source e) (fun j => (prepView x.2 j).focus)) s).2 = some a) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    let z := TextFeedPrepResume.sourceStep e s (prepView x.2)
    y.2 = extend prepSlot z.2 x.2 ∧ AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = z.1.map liftPrep ++ r := by
  have hc := prep_step e x.2 s r a ha
  rw [← hs] at hc
  obtain ⟨tr, he, hn, ht⟩ := prep_exec (Terminal := Terminal) e a x.2
  obtain ⟨hyt, hby, hcy⟩ := run_selected e leftSym R rate x hb hz _ (.inl a) hc tr he (by omega)
  rw [TextFeedPrepResume.source_step_tapes e s (prepView x.2) a ha] at ht
  exact ⟨hyt.trans ht, hby, hcy⟩

theorem run_start (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (hs : x.1.1.2.2.val = [task e leftSym rate]) (a : PrepAct k)
    (ha : (stepStack (evalConds (TextFeedPrepResume.source e) (fun j => (prepView x.2 j).focus))
      [finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate]).2 = some a) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    let z := TextFeedPrepResume.sourceStep e
      [finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate] (prepView x.2)
    y.2 = extend prepSlot z.2 x.2 ∧ AtBoundary (programs e) y.1.2.2.1 ∧
      y.1.1.2.2.val = z.1.map liftPrep ++ [afterPrep rate] := by
  apply run_prep_step e leftSym R rate x hb hz _ _ ?_ a ha
  rw [hs, task, stepStack_seq]
  rfl

theorem run_prefix_step (e : Env k) (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (s : Stack TextFeedPrefixAtomic.Act TextFeedPrefixAtomic.Cond) (r : Stack (TaskAct k) (TaskCond k))
    (hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (taskEval e (fun j => (x.2 j).focus)) (s.map liftPrefix ++ r))
    (a : TextFeedPrefixAtomic.Act)
    (ha : (stepStack (TextFeedPrefixAtomic.eval e (fun j => (x.2 (Fin.castAdd 19 j)).focus)) s).2 = some a)
    (D : TextFeedPrefixAtomic.Model k) (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (X : TapeConfiguration k) (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = TextFeedPrefixBank.tapes e qt₁ m₁ qt₂ m₂ D X aux old dir)
    (hq : Ready e.blank e.mark qt₁ m₁ D.q) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    ∃ qt₁' m₁', y.2 = TextFeedPrefixBank.tapes e qt₁' m₁' qt₂ m₂ (TextFeedPrefixAtomic.effect e a D) X aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ Ready e.blank e.mark qt₁' m₁' (TextFeedPrefixAtomic.effect e a D).q ∧
      y.1.1.2.2.val =
        (stepStack (TextFeedPrefixAtomic.eval e (fun j => (x.2 (Fin.castAdd 19 j)).focus)) s).1.map liftPrefix ++ r := by
  have hs' := prefix_step e (fun j => (x.2 j).focus) s r a ha
  rw [← hs] at hs'
  obtain ⟨ticks, qt₁', m₁', hn, ⟨tr, he, ht, hlen⟩, hr⟩ :=
    TextFeedPrefixBank.work_matches (Terminal := Terminal) hc hmb a D qt₁ m₁ qt₂ m₂ X aux old dir hq
  have he' := exec_prefix he
  rw [← hx] at he' ht
  obtain ⟨hyt, hby, hcy⟩ := run_selected e leftSym R rate x hb hz _ (.inr (.inl a)) hs' tr he' (by omega)
  exact ⟨qt₁', m₁', hyt.trans ht, hby, hr, hcy⟩

/-- The first prefix action runs immediately after the finite prep
continuation returns, on the same physical tapes. -/
theorem run_prep_handoff (e : Env k) (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (s : Stack (PrepAct k) (PrepCond k))
    (hs : x.1.1.2.2.val = s.map liftPrep ++ [afterPrep rate])
    (hreturn : (stepStack (evalConds (TextFeedPrepResume.source e) (fun j => (prepView x.2 j).focus)) s).2 = none)
    (a : TextFeedPrefixAtomic.Act)
    (ha : (stepStack (TextFeedPrefixAtomic.eval e (fun j => (x.2 (Fin.castAdd 19 j)).focus))
      [TextFeedPrefixAtomic.source]).2 = some a)
    (D : TextFeedPrefixAtomic.Model k) (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (X : TapeConfiguration k) (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = TextFeedPrefixBank.tapes e qt₁ m₁ qt₂ m₂ D X aux old dir)
    (hq : Ready e.blank e.mark qt₁ m₁ D.q) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    ∃ qt₁' m₁', y.2 = TextFeedPrefixBank.tapes e qt₁' m₁' qt₂ m₂ (TextFeedPrefixAtomic.effect e a D) X aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ Ready e.blank e.mark qt₁' m₁' (TextFeedPrefixAtomic.effect e a D).q ∧
      y.1.1.2.2.val =
        (stepStack (TextFeedPrefixAtomic.eval e (fun j => (x.2 (Fin.castAdd 19 j)).focus))
          [TextFeedPrefixAtomic.source]).1.map liftPrefix ++ [afterPrefix rate] := by
  apply run_prefix_step e hc hmb leftSym R rate x hb hz [TextFeedPrefixAtomic.source] [afterPrefix rate]
    ?_ a ha D qt₁ m₁ qt₂ m₂ X aux old dir hx hq
  rw [hs]
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] using prep_return e x.2 s rate hreturn

/-- The actual call after prefix return initializes the direction tape
and resumes the verifier loop. All 38 other tapes stay unchanged. -/
theorem run_prefix_return (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (taskEval e (fun j => (x.2 j).focus)) [afterPrefix rate]) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    y.2 = writeDir e true x.2 ∧ AtBoundary (programs e) y.1.2.2.1 ∧
      y.1.1.2.2.val = [verifyLoop rate] ∧ (y.2 38).focus = e.mark ∧
      ∀ j, j ≠ 38 → y.2 j = x.2 j := by
  have hc : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      ([verifyLoop rate], some (.inr (.inr (.inr true)))) := by
    simpa only [afterPrefix, stepStack_seq, stepStack_act] using hs
  obtain ⟨tr, he, hn, ht⟩ := dir_exec (Terminal := Terminal) e true x.2
  obtain ⟨hyt, hby, hcy⟩ := run_selected e leftSym R rate x hb hz _ (.inr (.inr (.inr true))) hc tr he (by omega)
  have hout := hyt.trans ht
  refine ⟨hout, hby, hcy, ?_, ?_⟩
  · rw [hout]
    simp [writeDir, GSVProgZLoop.dirSymbol, STape.applyAction]
  · intro j hj
    rw [hout]
    exact Function.update_of_ne hj _ _

/-- The verifier loop enters its guarded supply body with a stationary
call. The following feedHead checks the current cell before dequeuing. -/
theorem run_verify_start (e : Env k) (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (hs : x.1.1.2.2.val = [verifyLoop rate])
    (D : TextFeedPrefixAtomic.Model k) (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (X : TapeConfiguration k) (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = TextFeedPrefixBank.tapes e qt₁ m₁ qt₂ m₂ D X aux old dir)
    (hq : Ready e.blank e.mark qt₁ m₁ D.q) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    ∃ qt₁' m₁', y.2 = TextFeedPrefixBank.tapes e qt₁' m₁' qt₂ m₂ D X aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ Ready e.blank e.mark qt₁' m₁' D.q ∧
      y.1.1.2.2.val = [verifyBody rate, verifyLoop rate] := by
  have hs' := verify_start e (fun j => (x.2 j).focus) rate
  rw [← hs] at hs'
  obtain ⟨ticks, qt₁', m₁', hn, ⟨tr, he, ht, hlen⟩, hr⟩ :=
    TextFeedPrefixBank.work_matches (Terminal := Terminal) hc hmb .idle D qt₁ m₁ qt₂ m₂ X aux old dir hq
  have he' := exec_prefix he
  rw [← hx] at he' ht
  obtain ⟨hyt, hby, hcy⟩ := run_selected e leftSym R rate x hb hz _ (.inr (.inl .idle)) hs' tr he' (by omega)
  exact ⟨qt₁', m₁', hyt.trans ht, hby, hr, by simpa only [hs] using hcy⟩

/-- Input calls neither advance nor reset the suspended source, even
while it is crossing a phase boundary. -/
theorem run_enqueue_exec (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 = 0)
    (tr : List (Fin 39 → Fin k × Move))
    (he : Exec (TextFeedPipelineBank.interp (Terminal := Terminal) e) e.blank
      (low e (.enqueue x.1.1.2.1)) x.2 tr) (hn : tr.length < 93) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    y.2 = applyTrace e.blank x.2 tr ∧ AtBoundary (programs e) y.1.2.2.1 ∧
      y.1.1.2.2 = x.1.1.2.2 ∧ y.1.1.2.1 = false := by
  have hsel : decode (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2 = .enqueue x.1.1.2.1 := by
    simp only [TextFeedPipelineControl.choose, if_pos hz, decode_encode]
  have hex : Exec (TextFeedPipelineControl.interp (Terminal := Terminal) e).toInterp e.blank
      (programs e (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2) x.2 tr := by
    change Exec (TextFeedPipelineBank.interp e) e.blank (low e (decode _)) x.2 tr
    rw [hsel]
    exact he
  obtain ⟨ht, hb', _, _⟩ := callRun_exec (programs e)
    (fun _ => TextFeedPipelineControl.interp (Terminal := Terminal) e) (choose e leftSym R rate) 93 e.blank x hb tr hex hn
  refine ⟨ht, hb', ?_, ?_⟩ <;>
    simp only [TextFeedPipelineControl.run, callRun, TextFeedPipelineControl.choose, if_pos hz]

/-- info: 'PalPeg.TextFeedPipelineHandoff.run_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_start

/-- info: 'PalPeg.TextFeedPipelineHandoff.run_prep_handoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_prep_handoff

/-- info: 'PalPeg.TextFeedPipelineHandoff.run_verify_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_verify_start

/-- info: 'PalPeg.TextFeedPipelineHandoff.run_prefix_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_prefix_return

end PalPeg.TextFeedPipelineHandoff
