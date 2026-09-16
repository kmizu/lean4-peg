import PalPeg.TextFeedPipelineVerifier

/-! The initial Txt2 cell is supplied in place before the first comparison. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineFeed2
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelineVerifier PalPeg.VerifierFeed

variable {k : ℕ} {Terminal : Type}

theorem effect_stay (e : Env k) (M : VMachine' k) :
    VerifierFeedPrimitive.effect e (GSVProg.tX, true, .stay) M = vfillHead2 e.blank e.mark M := by
  simp [VerifierFeedPrimitive.effect, VerifierFeedPrimitive.isXR, VerifierFeedPrimitive.isXS]

theorem feed2_step (ev : TaskCond k → Bool) (s : Stack (TaskAct k) (TaskCond k)) :
    stepStack ev (feedHead2 :: s) = (s, some (.inr (.inr (.inl (GSVProg.tX, true, .stay))))) := by
  rw [feedHead2, stepStack_act]

theorem body_before_scan (e : Env k) (σ : Fin 39 → Fin k) (rate : ℕ) (h : σ 12 ≠ e.blank) :
    stepStack (taskEval e σ) [verifyBody rate] =
      ([liftVerify (GSVProgZLoop.stepProg rate)], some (.inr (.inr (.inl (GSVProg.tX, true, .stay))))) := by
  have he : taskEval e σ (.inr (.inl .blankText)) = false := by
    change decide (σ 12 = e.blank) = false
    exact decide_eq_false h
  simp only [verifyBody, stepStack_seq, feedHead, stepStack_ite, he, Bool.false_eq_true,
    if_false, stepStack_skip, feedHead2, stepStack_act]

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem run_feed2 {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (s : Stack (TaskAct k) (TaskCond k))
    (hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (taskEval e (fun j => (x.2 j).focus)) (feedHead2 :: s))
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ M aux old dir)
    (h₁ : Ready e.blank e.mark qt₁ m₁ M.Q1) (h₂ : Ready e.blank e.mark qt₂ m₂ M.Q2)
    {u v Text : List (Fin k)} {d p r n : ℕ}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hf : VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n M) :
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    let M' := vfillHead2 e.blank e.mark M
    ∃ qt₂' m₂', y.2 = tapes e qt₁ m₁ qt₂' m₂' M' aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = s ∧
      Ready e.blank e.mark qt₁ m₁ M'.Q1 ∧ Ready e.blank e.mark qt₂' m₂' M'.Q2 ∧
      VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n M' ∧
      Ok2 n M' (M'.z.1.pos - u.length + M'.z.2) := by
  have hstep := hs.trans (feed2_step _ s)
  obtain ⟨qt₂', m₂', ht, hby, hcy, hr₁, hr₂, _⟩ := run_instruction e hc hmb leftSym R rate x hb hz s
    (GSVProg.tX, true, .stay) hstep qt₁ m₁ qt₂ m₂ M aux old dir hx h₁ h₂ hf.buf2
  simp only [effect_stay] at ht hr₁ hr₂
  obtain ⟨hi, hok⟩ := vfillHead2_feedInv hmb hblank hmark hn hf
  exact ⟨qt₂', m₂', ht, hby, hcy, hr₁, hr₂, hi, hok⟩

/-- At the genuine prefix endpoint, any arrived symbol makes the first
Txt2 cell readable; no preliminary right move is needed. -/
theorem initial_readable {e : Env k} {u v Text : List (Fin k)} {d p r n : ℕ} {M : VMachine' k}
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hn : n ≤ Text.length) (hn0 : 0 < n)
    (hf : VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n M)
    (hpos : M.z.1.pos = u.length) (hchecked : M.z.2 = 0) :
    Tape.read (vfillHead2 e.blank e.mark M).vt.2.Txt2 ≠ e.blank := by
  obtain ⟨hi, hok⟩ := vfillHead2_feedInv hmb hblank hmark hn hf
  have hz : (vfillHead2 e.blank e.mark M).z.1.pos - u.length +
      (vfillHead2 e.blank e.mark M).z.2 = 0 := by
    simp only [vfillHead2_z, hpos, hchecked, Nat.sub_self, Nat.zero_add]
  intro hb
  have he := (read_Txt2_blank_iff hblank hn hi.txt2Inv).mp hb
  rw [hz] at he hok
  rcases hok with hk | hk <;> omega

/-- info: 'PalPeg.TextFeedPipelineFeed2.initial_readable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initial_readable

/-- info: 'PalPeg.TextFeedPipelineFeed2.run_feed2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_feed2

end PalPeg.TextFeedPipelineFeed2
