import PalPeg.TextFeedPipelinePrepReady

/-! A live prefix phase in the single pipeline. The control relation is
evaluated on the actual tapes, and arrivals preserve every source guard. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrefixLink
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelineHandoff PalPeg.TextFeedPrefixRank

variable {k : ℕ} {Terminal : Type}

abbrev State (k : ℕ) := Stack TextFeedPrefixAtomic.Act TextFeedPrefixAtomic.Cond × TextFeedPrefixMachine.Data k
abbrev Phys (e : Env k) (leftSym : Fin k) (R rate : ℕ) :=
  CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k))

def erase (z : State k) := (z.1, z.2.worker)
def work (e : Env k) (z : State k) : State k :=
  let t := TextFeedPrefixCycle.tick e (erase z)
  (t.1, { z.2 with worker := t.2 })
def arrival (a : Fin k) (z : State k) : State k :=
  (z.1, TextFeedPrefixMachine.enqueue (TextFeedPrefixMachine.capture z.2 a))

def Link (e : Env k) (leftSym : Fin k) (R rate : ℕ) (z : State k) (x : Phys e leftSym R rate) : Prop :=
  ∃ qt₁ m₁ qt₂ m₂,
    x.2 = TextFeedPrefixMachine.tapes e qt₁ m₁ qt₂ m₂ z.2 ∧ AtBoundary (programs e) x.1.2.2.1 ∧
    x.1.1.2.1 = false ∧ Ready e.blank e.mark qt₁ m₁ z.2.worker.q ∧ Ready e.blank e.mark qt₂ m₂ z.2.q₂ ∧
    stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (taskEval e (fun j => (x.2 j).focus)) (z.1.map liftPrefix ++ [afterPrefix rate])

theorem taskEval_eq (e : Env k) (T U : Fin 39 → STape (Fin k))
    (h : ∀ j, DualQueueShared.Reserved j → T j = U j) :
    taskEval e (fun j => (T j).focus) = taskEval e (fun j => (U j).focus) := by
  funext c
  rcases c with c | c
  · change (PrepInstance.prepInterp (Terminal := Unit) e.blank e.endSym e.mark).condOf c _ = _
    congr 1
    funext j
    exact congrArg STape.focus (h _ (TextFeedPipelineArrival.prep_reserved j))
  rcases c with c | c
  · have h12 := h (Fin.castAdd 19 (12 : Fin 20)) (by unfold DualQueueShared.Reserved; decide)
    have h19 := h (Fin.castAdd 19 (19 : Fin 20)) (by unfold DualQueueShared.Reserved; decide)
    cases c <;> simp only [taskEval, TextFeedPrefixAtomic.eval, h12, h19]
  rcases c with c | c
  · change GSVProg.condOf10 e.endSym e.mark e.startSym c _ = _
    congr 1
    funext j
    have hj : DualQueueShared.Reserved (verifySlot (VerifierFeedShared.verifierSlot j)) := by
      fin_cases j <;> unfold DualQueueShared.Reserved <;> decide
    exact congrArg STape.focus (h _ hj)
  · cases c with
    | up => change decide ((T 38).focus = e.mark) = decide ((U 38).focus = e.mark); rw [h 38 (by unfold DualQueueShared.Reserved; decide)]
    | always => rfl
    | scanWait =>
      change decide ((T 11).focus ≠ e.endSym ∧ (T 12).focus = e.blank) = _
      rw [h 11 (by unfold DualQueueShared.Reserved; decide), h 12 (by unfold DualQueueShared.Reserved; decide)]
      simp only [taskEval]
    | verifyWait =>
      change decide ((T 19).focus ≠ e.endSym ∧ (T 20).focus = e.blank) = _
      rw [h 19 (by unfold DualQueueShared.Reserved; decide), h 20 (by unfold DualQueueShared.Reserved; decide)]
      simp only [taskEval]
    | blankX =>
      change decide ((T 20).focus = e.blank) = _
      rw [h 20 (by unfold DualQueueShared.Reserved; decide)]
      simp only [taskEval]

theorem has_action {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {z : Stack TextFeedPrefixAtomic.Act TextFeedPrefixAtomic.Cond × TextFeedPrefixAtomic.Model k}
    (h : Good e u v Text d p r n fuel z) (hf : 0 < fuel)
    (hend : e.endSym ∉ u) (hse : e.startSym ≠ e.endSym) :
    ∃ a, (stepStack (TextFeedPrefixAtomic.modelEval e z.2) z.1).2 = some a := by
  cases h with
  | @loop M U i h hm hi =>
    by_cases he : U.focus = e.endSym
    · exact ⟨_, congrArg Prod.snd (TextFeedPrefixCycle.end_step e _ he hse)⟩
    · exact ⟨_, congrArg Prod.snd (TextFeedPrefixCycle.loop_step e _ he)⟩
  | fill h hm hi => exact ⟨_, congrArg Prod.snd (TextFeedPrefixCycle.fill_step e _)⟩
  | @gateReady M U i h hm hi =>
    by_cases ht : ((TextFeedPrefixFinish.data M U).S GSTapes.tT).focus = e.blank
    · exact ⟨_, congrArg Prod.snd (TextFeedPrefixCycle.gate_wait_step e _ ht (h.notEnd hend hi))⟩
    · exact ⟨_, congrArg Prod.snd (TextFeedPrefixCycle.gate_ready_step e _ ht)⟩
  | @gateEmpty M U i h hm hi =>
    by_cases ht : ((TextFeedPrefixFinish.data M U).S GSTapes.tT).focus = e.blank
    · exact ⟨_, congrArg Prod.snd (TextFeedPrefixCycle.gate_wait_step e _ ht (h.notEnd hend hi))⟩
    · exact ⟨_, congrArg Prod.snd (TextFeedPrefixCycle.gate_ready_step e _ ht)⟩
  | right h hm hi => exact ⟨_, congrArg Prod.snd (TextFeedPrefixCycle.right_step e _)⟩
  | @rewind M U j h hm hi =>
    by_cases he : U.focus = e.startSym
    · exact ⟨_, congrArg Prod.snd (TextFeedPrefixCycle.rewind_end_step e _ he)⟩
    · exact ⟨_, congrArg Prod.snd (TextFeedPrefixCycle.rewind_more_step e _ he)⟩
  | done h hm => omega

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

attribute [local irreducible] ProgLangBank.runChunk

theorem Link.step {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Link e leftSym R rate z x) (hz : x.1.1.1 ≠ 0) {a : TextFeedPrefixAtomic.Act}
    (ha : (stepStack (TextFeedPrefixAtomic.modelEval e z.2.worker) z.1).2 = some a) :
    Link e leftSym R rate (work e z) (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) := by
  obtain ⟨qt₁, m₁, qt₂, m₂, hx, hb, hf, h₁, h₂, hs⟩ := h
  have heval : TextFeedPrefixAtomic.eval e (fun j => (x.2 (Fin.castAdd 19 j)).focus) =
      TextFeedPrefixAtomic.modelEval e z.2.worker := by
    rw [hx]
    exact TextFeedPrefixMachine.eval_tapes e qt₁ m₁ qt₂ m₂ z.2
  obtain ⟨qt₁', m₁', ht, hb', hr, hctrl⟩ := run_prefix_step (Terminal := Terminal) e hc hmb leftSym R rate x hb hz
    z.1 [afterPrefix rate] hs a (by rwa [heval]) z.2.worker qt₁ m₁ qt₂ m₂ z.2.X z.2.aux z.2.old z.2.dir hx h₁
  have hw : work e z = ((stepStack (TextFeedPrefixAtomic.modelEval e z.2.worker) z.1).1,
      { z.2 with worker := TextFeedPrefixAtomic.effect e a z.2.worker }) := by
    simp only [work, erase, TextFeedPrefixCycle.tick, ha, Option.getD_some]
  rw [hw]
  refine ⟨qt₁', m₁', qt₂, m₂, ht, hb', TextFeedPipelinePrepFrames.run_false e leftSym R rate x hf, hr, h₂, ?_⟩
  rw [heval] at hctrl
  rw [hctrl]

set_option maxHeartbeats 1000000 in
theorem Link.arrival {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Link e leftSym R rate z x) (hz : x.1.1.1 = 0) (a : Terminal) (ha : enc a ≠ e.mark) :
    Link e leftSym R rate (arrival (enc a) z)
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
        (x.1, arriveA e.blank (DualQueueShared.capture enc) (some a) x.2)) := by
  obtain ⟨qt₁, m₁, qt₂, m₂, hx, hb, hf, h₁, h₂, hs⟩ := h
  let xc := (x.1, arriveA e.blank (DualQueueShared.capture enc) (some a) x.2)
  have hxc : xc.2 = TextFeedPrefixBank.tapes e qt₁ m₁ qt₂ m₂ z.2.worker z.2.X z.2.aux (enc a) z.2.dir := by
    dsimp only [xc]
    rw [hx]
    exact TextFeedPrefixBank.capture_some e enc a qt₁ m₁ qt₂ m₂ z.2.worker z.2.X z.2.aux z.2.old z.2.dir
  obtain ⟨qt₁', m₁', qt₂', m₂', ht, hb', hctrl, hf', hr₁, hr₂⟩ :=
    TextFeedPipelineArrival.run_enqueue (Terminal := Terminal) e hc hmb leftSym R rate xc hb hz hf
      z.2.worker z.2.q₂ qt₁ m₁ qt₂ m₂ z.2.X z.2.aux (enc a) z.2.dir hxc h₁ h₂ ha
  refine ⟨qt₁', m₁', qt₂', m₂', ht, hb', hf', hr₁, hr₂, ?_⟩
  have hev : taskEval e (fun j => ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate xc).2 j).focus) =
      taskEval e (fun j => (x.2 j).focus) := by
    apply taskEval_eq
    intro j hj
    rw [ht, hx]
    fin_cases j <;> first | rfl | (simp [DualQueueShared.Reserved] at hj)
  rw [hev, hctrl]
  exact hs

theorem Link.finished {e : Env k} {u v Text : List (Fin k)} {d p r n : ℕ}
    {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Link e leftSym R rate z x) (hg : Good e u v Text d p r n 0 (erase z)) :
    stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (taskEval e (fun j => (x.2 j).focus)) [afterPrefix rate] ∧
      ∃ M U, z.2.worker = TextFeedPrefixFinish.data M U ∧
        Rep e u v Text d p r n M U u.length 1 ∧ M.m = u.length := by
  obtain ⟨hz, hrep⟩ := hg.finished
  obtain ⟨_, _, _, _, _, _, _, _, _, hs⟩ := h
  refine ⟨?_, hrep⟩
  change z.1 = [] at hz
  simpa only [hz, List.map_nil, List.nil_append] using hs

/-- info: 'PalPeg.TextFeedPipelinePrefixLink.Link.arrival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Link.arrival

/-- info: 'PalPeg.TextFeedPipelinePrefixLink.Link.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Link.step

end PalPeg.TextFeedPipelinePrefixLink
