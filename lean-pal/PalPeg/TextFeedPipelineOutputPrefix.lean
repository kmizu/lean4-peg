import PalPeg.TextFeedPipelineOutputPrep
import PalPeg.TextFeedPipelinePrefixWindow
import PalPeg.TextFeedPipelinePrefixFedPhysical
import PalPeg.TextFeedPipelineOutputPrepFinish

/-! Prefix alignment on the observation-enabled pipeline. The existing
physical link supplies FIFO readiness before and after each actual call. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineOutputPrefix
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist2
open PalPeg.TextFeedControl PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelinePrefixLink PalPeg.TextFeedPipelinePrepInput
open PalPeg.TextFeedPipelineOutputPrep PalPeg.RTQueueTapes

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem link_ready {e : Env k} {leftSym : Fin k} {R rate : ℕ}
    {z : State k} {x : Phys e leftSym R rate} (h : Link e leftSym R rate z x) :
    ReadyAt e x.2 z.2.worker.q z.2.q₂ z.2.old := by
  obtain ⟨qt₁, m₁, qt₂, m₂, ht, _, _, h₁, h₂, _⟩ := h
  refine ⟨qt₁, m₁, qt₂, m₂, ?_, h₁, h₂⟩
  rw [ht]
  exact TextFeedPrefixBank.pair_view e qt₁ m₁ qt₂ m₂ z.2.worker z.2.X z.2.aux z.2.old z.2.dir

theorem worker {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : Link e leftSym R rate z x) (hz : x.1.1.1 ≠ 0) {a : TextFeedPrefixAtomic.Act}
    (ha : (stepStack (TextFeedPrefixAtomic.modelEval e z.2.worker) z.1).2 = some a)
    (ρ : Role) (bit : Bool) :
    let y := TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate ((x.1, ρ, bit), x.2)
    (y.1.1, y.2) = TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x ∧
      Link e leftSym R rate (work e z) (y.1.1, y.2) := by
  have hnext := h.step (Terminal := Terminal) hc hmb hz ha
  have he := step_ready (Terminal := Terminal) hc ((x.1, ρ, bit), x.2) (link_ready hnext)
  exact ⟨he, he.symm ▸ hnext⟩

theorem arrival_step {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ}
    {z : State k} {x : Phys e leftSym R rate}
    (h : Link e leftSym R rate z x) (hz : x.1.1.1 = 0)
    (a : Terminal) (ha : enc a ≠ e.mark) (ρ : Role) (bit : Bool) :
    let xc := (x.1, arriveA e.blank (DualQueueShared.capture enc) (some a) x.2)
    let y := TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate ((xc.1, ρ, bit), xc.2)
    (y.1.1, y.2) = TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate xc ∧
      Link e leftSym R rate (arrival (enc a) z) (y.1.1, y.2) := by
  have hnext := h.arrival hc hmb enc hz a ha
  have he := step_ready (Terminal := Terminal) hc
    ((x.1, ρ, bit), arriveA e.blank (DualQueueShared.capture enc) (some a) x.2) (link_ready hnext)
  exact ⟨he, he.symm ▸ hnext⟩

/-- Productive alignment windows retain the existing rank descent even
with the physical reader enabled after every call. Stops exactly at return. -/
theorem window_progress {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : TextFeedPipelinePrefixWindow.Safe e u Text) (hl : Link e leftSym R rate z x)
    (hg : TextFeedPrefixRank.Good e u v Text d p r n fuel (erase z))
    (hn : n ≤ Text.length) (hroom : u.length ≤ n) (N : ℕ) (hN : N ≤ fuel)
    (hpos : N ≠ 0 → 0 < x.1.1.1.val) (hlen : x.1.1.1.val + N ≤ R + 1)
    (ρ : Role) (bit : Bool) :
    let y := (TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate)^[N]
      ((x.1, ρ, bit), x.2)
    (y.1.1, y.2) = (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] x ∧
      Link e leftSym R rate ((work e)^[N] z) (y.1.1, y.2) ∧
      TextFeedPrefixRank.Good e u v Text d p r n (fuel - N) (erase ((work e)^[N] z)) := by
  have hready : ∀ j < N, ∃ q₁ q₂ old, ReadyAt e
      ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[j + 1] x).2 q₁ q₂ old := by
    intro j hj
    have hh := TextFeedPipelinePrefixWindow.window_progress (Terminal := Terminal)
      h hl hg hn hroom (j + 1) (by omega) (by intro _; exact hpos (by omega)) (by omega)
    exact ⟨_, _, _, link_ready hh.1⟩
  have he := steps_ready (Terminal := Terminal) h.code ((x.1, ρ, bit), x.2) N hready
  have hh := TextFeedPipelinePrefixWindow.window_progress (Terminal := Terminal)
    h hl hg hn hroom N hN hpos hlen
  exact ⟨he, he.symm ▸ hh.1, hh.2⟩

private theorem core_window {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : TextFeedPipelinePrefixWindow.Safe e u Text) (hl : Link e leftSym R rate z x)
    (hg : TextFeedPrefixRank.Good e u v Text d p r n fuel (erase z))
    (hn : n ≤ Text.length) (N : ℕ)
    (hpos : N ≠ 0 → 0 < x.1.1.1.val) (hlen : x.1.1.1.val + N ≤ R + 1) :
    ∃ J f, J ≤ N ∧ (J = N ∨ f = 0) ∧
      Link e leftSym R rate ((work e)^[J] z)
        ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J] x) ∧
      TextFeedPrefixRank.Good e u v Text d p r n f (erase ((work e)^[J] z)) ∧
      ∀ j < J, ∃ q₁ q₂ old, ReadyAt e
        ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[j + 1] x).2 q₁ q₂ old := by
  induction N generalizing z x fuel with
  | zero => exact ⟨0, fuel, by omega, Or.inl rfl, hl, hg, by intro j hj; omega⟩
  | succ N ih =>
    by_cases hf : fuel = 0
    · subst fuel
      exact ⟨0, 0, by omega, Or.inr rfl, hl, hg, by intro j hj; omega⟩
    have hz : x.1.1.1 ≠ 0 := by
      have hh := hpos (by omega)
      intro he
      rw [he] at hh
      simp at hh
    obtain ⟨f, hl', hg'⟩ := TextFeedPipelinePrefixWindow.step_preserve (Terminal := Terminal)
      h hl hg (by omega) hz hn
    obtain ⟨hp, hlen'⟩ := TextFeedPipelinePrefixWindow.next_window (Terminal := Terminal) hlen
    obtain ⟨J, f', hJ, hend, hL, hG, hready⟩ := ih hl' hg' hp hlen'
    refine ⟨J + 1, f', by omega, by rcases hend with he | he; exact Or.inl (by omega); exact Or.inr he,
      ?_, ?_, ?_⟩
    · simpa only [Function.iterate_succ_apply] using hL
    · simpa only [Function.iterate_succ_apply] using hG
    · intro j hj
      cases j with
      | zero => exact ⟨_, _, _, link_ready hl'⟩
      | succ j =>
        obtain ⟨q₁, q₂, old, hr⟩ := hready j (by omega)
        refine ⟨q₁, q₂, old, ?_⟩
        simpa only [Function.iterate_succ_apply] using hr

/-- During input waiting the observed machine either uses the whole
window or stops at the real prefix return. Future text is not assumed. -/
theorem window_preserve_or_hit {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : TextFeedPipelinePrefixWindow.Safe e u Text) (hl : Link e leftSym R rate z x)
    (hg : TextFeedPrefixRank.Good e u v Text d p r n fuel (erase z))
    (hn : n ≤ Text.length) (N : ℕ)
    (hpos : N ≠ 0 → 0 < x.1.1.1.val) (hlen : x.1.1.1.val + N ≤ R + 1)
    (ρ : Role) (bit : Bool) :
    ∃ J f, J ≤ N ∧ (J = N ∨ f = 0) ∧
      let y := (TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate)^[J]
        ((x.1, ρ, bit), x.2)
      (y.1.1, y.2) = (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J] x ∧
      Link e leftSym R rate ((work e)^[J] z) (y.1.1, y.2) ∧
      TextFeedPrefixRank.Good e u v Text d p r n f (erase ((work e)^[J] z)) := by
  obtain ⟨J, f, hJ, hend, hL, hG, hready⟩ := core_window (Terminal := Terminal) h hl hg hn N hpos hlen
  have he := steps_ready (Terminal := Terminal) h.code ((x.1, ρ, bit), x.2) J hready
  exact ⟨J, f, hJ, hend, he, he.symm ▸ hL, hG⟩

/-- Finish the current worker window on the observed machine, retaining
the reserve FIFO and returning the real input counter to zero. -/
theorem resume_cases {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : TextFeedPipelinePrefixWindow.Safe e u Text) (hl : Link e leftSym R rate z x)
    (hg : TextFeedPrefixRank.Good e u v Text d p r n fuel (erase z))
    (hr : TextFeedPipelinePrefixReserve.Reserve e Text n z) (hn : n ≤ Text.length)
    (ρ : Role) (bit : Bool) :
    (∃ J ≤ TextFeedPipelinePrefixResume.remaining x,
      let y := (TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate)^[J]
        ((x.1, ρ, bit), x.2)
      TextFeedPipelinePrefixFedPhysical.Complete e leftSym R rate u v Text d p r n (y.1.1, y.2)) ∨
    (∃ f,
      let N := TextFeedPipelinePrefixResume.remaining x
      let y := (TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate)^[N]
        ((x.1, ρ, bit), x.2)
      Link e leftSym R rate ((work e)^[N] z) (y.1.1, y.2) ∧
      TextFeedPrefixRank.Good e u v Text d p r n f (erase ((work e)^[N] z)) ∧
      TextFeedPipelinePrefixReserve.Reserve e Text n ((work e)^[N] z) ∧ y.1.1.1.1 = 0) := by
  obtain ⟨hp, hlen, hz⟩ := TextFeedPipelinePrefixResume.remaining_window (Terminal := Terminal) x
  obtain ⟨J, f, hJ, hend, he, hL, hG⟩ := window_preserve_or_hit (Terminal := Terminal)
    h hl hg hn (TextFeedPipelinePrefixResume.remaining x) hp hlen ρ bit
  by_cases hf : f = 0
  · exact Or.inl ⟨J, hJ, (work e)^[J] z, hL, hf ▸ hG, hr.works J⟩
  · have hfull := hend.resolve_right hf
    subst J
    right
    refine ⟨f, hL, hG, hr.works _, ?_⟩
    exact (congrArg (fun t : Phys e leftSym R rate => t.1.1.1) he).trans hz

/-- info: 'PalPeg.TextFeedPipelineOutputPrefix.resume_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resume_cases

/-- Once enough text is present, the remaining alignment calls establish
the exact Complete predicate consumed by the verifier's startup theorem. -/
theorem window_complete {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (h : TextFeedPipelinePrefixWindow.Safe e u Text) (hl : Link e leftSym R rate z x)
    (hg : TextFeedPrefixRank.Good e u v Text d p r n fuel (erase z))
    (hr : TextFeedPipelinePrefixReserve.Reserve e Text n z)
    (hn : n ≤ Text.length) (hroom : u.length ≤ n)
    (hpos : fuel ≠ 0 → 0 < x.1.1.1.val) (hlen : x.1.1.1.val + fuel ≤ R + 1)
    (ρ : Role) (bit : Bool) :
    let y := (TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate)^[fuel]
      ((x.1, ρ, bit), x.2)
    TextFeedPipelinePrefixFedPhysical.Complete e leftSym R rate u v Text d p r n (y.1.1, y.2) := by
  obtain ⟨_, hL, hG⟩ := window_progress (Terminal := Terminal) h hl hg hn hroom fuel
    (Nat.le_refl _) hpos hlen ρ bit
  exact ⟨(work e)^[fuel] z, hL, by simpa only [Nat.sub_self] using hG, hr.works fuel⟩

/-- A real arrival followed by a possibly waiting alignment window.
The second FIFO reserve follows the actual arrival and is retained at
either the next frame boundary or an earlier alignment return. -/
theorem arrival_window {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ}
    {z : State k} {x : Phys e leftSym R rate}
    (h : TextFeedPipelinePrefixWindow.Safe e u Text) (hl : Link e leftSym R rate z x)
    (hg : TextFeedPrefixRank.Good e u v Text d p r n fuel (erase z))
    (hr : TextFeedPipelinePrefixReserve.Reserve e Text n z)
    (hz : x.1.1.1 = 0) (hR : 0 < R) (hn : n < Text.length)
    (a : Terminal) (ha : Text[n]? = some (enc a)) (ρ : Role) (bit : Bool) :
    ∃ J f, J ≤ R ∧ (J = R ∨ f = 0) ∧
      let y := (TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate)^[J + 1]
        ((x.1, ρ, bit), arriveA e.blank (DualQueueShared.capture enc) (some a) x.2)
      (y.1.1, y.2) = (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J + 1]
        (x.1, arriveA e.blank (DualQueueShared.capture enc) (some a) x.2) ∧
      Link e leftSym R rate ((work e)^[J] (arrival (enc a) z)) (y.1.1, y.2) ∧
      TextFeedPrefixRank.Good e u v Text d p r (n + 1) f (erase ((work e)^[J] (arrival (enc a) z))) ∧
      TextFeedPipelinePrefixReserve.Reserve e Text (n + 1) ((work e)^[J] (arrival (enc a) z)) := by
  let y0 := TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate
    ((x.1, ρ, bit), arriveA e.blank (DualQueueShared.capture enc) (some a) x.2)
  obtain ⟨he0, hl0⟩ := arrival_step h.code h.mark_blank enc hl hz a (h.symbol ha) ρ bit
  have hg0 := hg.arrive h.mark_blank hn ha
  have hr0 := hr.arrival hn ha
  have hphase : (y0.1.1, y0.2).1.1.1.val = 1 := by
    have hh := congrArg (fun t => t.1.1.1.val) he0
    exact hh.trans (TextFeedPipelinePrefixFrames.input_counter enc hz hR a)
  obtain ⟨J, f, hJ, hend, he, hL, hG⟩ := window_preserve_or_hit (Terminal := Terminal)
    h hl0 hg0 (by omega) R (by intro _; rw [hphase]; omega)
    (by rw [hphase]; omega) y0.1.2.1 y0.1.2.2
  refine ⟨J, f, hJ, hend, ?_⟩
  have hcore := he.trans (congrArg
    ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J]) he0)
  have hout := And.intro hcore (And.intro hL (And.intro hG (hr0.works J)))
  simpa only [Function.iterate_succ_apply] using hout

/-- With enough text already present, the observed arrival window pays
exactly N units of alignment work. Input enqueue does not spend that budget. -/
theorem productive_arrival {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ}
    {z : State k} {x : Phys e leftSym R rate}
    (h : TextFeedPipelinePrefixWindow.Safe e u Text) (hl : Link e leftSym R rate z x)
    (hg : TextFeedPrefixRank.Good e u v Text d p r n fuel (erase z))
    (hr : TextFeedPipelinePrefixReserve.Reserve e Text n z)
    (hz : x.1.1.1 = 0) (hR : 0 < R) (hn : n < Text.length) (hroom : u.length ≤ n + 1)
    (a : Terminal) (ha : Text[n]? = some (enc a)) (N : ℕ) (hN : N ≤ fuel) (hNR : N ≤ R)
    (ρ : Role) (bit : Bool) :
    let y := (TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate)^[N + 1]
      ((x.1, ρ, bit), arriveA e.blank (DualQueueShared.capture enc) (some a) x.2)
    (y.1.1, y.2) = (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N + 1]
      (x.1, arriveA e.blank (DualQueueShared.capture enc) (some a) x.2) ∧
    Link e leftSym R rate ((work e)^[N] (arrival (enc a) z)) (y.1.1, y.2) ∧
    TextFeedPrefixRank.Good e u v Text d p r (n + 1) (fuel - N)
      (erase ((work e)^[N] (arrival (enc a) z))) ∧
    TextFeedPipelinePrefixReserve.Reserve e Text (n + 1) ((work e)^[N] (arrival (enc a) z)) := by
  let y0 := TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate
    ((x.1, ρ, bit), arriveA e.blank (DualQueueShared.capture enc) (some a) x.2)
  obtain ⟨he0, hl0⟩ := arrival_step h.code h.mark_blank enc hl hz a (h.symbol ha) ρ bit
  have hg0 := hg.arrive h.mark_blank hn ha
  have hr0 := hr.arrival hn ha
  have hphase : (y0.1.1, y0.2).1.1.1.val = 1 :=
    (congrArg (fun t => t.1.1.1.val) he0).trans
      (TextFeedPipelinePrefixFrames.input_counter enc hz hR a)
  obtain ⟨he, hL, hG⟩ := window_progress (Terminal := Terminal) h hl0 hg0 (by omega) hroom N hN
    (by intro _; rw [hphase]; omega) (by rw [hphase]; omega) y0.1.2.1 y0.1.2.2
  have hcore := he.trans (congrArg
    ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N]) he0)
  simpa only [Function.iterate_succ_apply] using
    And.intro hcore (And.intro hL (And.intro hG (hr0.works N)))

/-- The waiting/return alternative on the real 96-step input machine,
not merely the call-level interpreter. A zero rank gives startup Complete. -/
theorem frame_or_complete {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ}
    {z : State k} {x : Phys e leftSym R rate}
    (h : TextFeedPipelinePrefixWindow.Safe e u Text) (hl : Link e leftSym R rate z x)
    (hg : TextFeedPrefixRank.Good e u v Text d p r n fuel (erase z))
    (hr : TextFeedPipelinePrefixReserve.Reserve e Text n z)
    (hz : x.1.1.1 = 0) (hR : 0 < R) (hn : n < Text.length)
    (a : Terminal) (ha : Text[n]? = some (enc a)) (ρ : Role) (bit : Bool) :
    ∃ J f, J ≤ R ∧ (J = R ∨ f = 0) ∧
      let y := TextFeedPipelineOutputPrepFinish.finishAt e leftSym enc R rate [] a J
        ⟨(((x.1, ρ, bit), 0), 0), x.2⟩
      Link e leftSym R rate ((work e)^[J] (arrival (enc a) z)) (y.state.1.1.1, y.tape) ∧
      TextFeedPrefixRank.Good e u v Text d p r (n + 1) f (erase ((work e)^[J] (arrival (enc a) z))) ∧
      TextFeedPipelinePrefixReserve.Reserve e Text (n + 1) ((work e)^[J] (arrival (enc a) z)) ∧
      (f = 0 → TextFeedPipelinePrefixFedPhysical.Complete e leftSym R rate u v Text d p r
        (n + 1) (y.state.1.1.1, y.tape)) := by
  obtain ⟨J, f, hJ, hend, he, hL, hG, hreserve⟩ := arrival_window enc h hl hg hr hz hR hn a ha ρ bit
  refine ⟨J, f, hJ, hend, ?_⟩
  simp only [TextFeedPipelineOutputPrepFinish.finishAt, List.foldl_nil,
    TextFeedPipelineOutputPrepFinish.machine_partial e leftSym enc R rate J hJ]
  refine ⟨hL, hG, hreserve, ?_⟩
  intro hf
  subst f
  exact ⟨(work e)^[J] (arrival (enc a) z), hL, hG, hreserve⟩

/-- Either the actual machine reaches Complete inside this frame, or its
full sRound result carries every invariant and all clocks for the next input. -/
theorem frame_cases {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ}
    {z : State k} {x : Phys e leftSym R rate}
    (h : TextFeedPipelinePrefixWindow.Safe e u Text) (hl : Link e leftSym R rate z x)
    (hg : TextFeedPrefixRank.Good e u v Text d p r n fuel (erase z))
    (hr : TextFeedPipelinePrefixReserve.Reserve e Text n z)
    (hz : x.1.1.1 = 0) (hR : 0 < R) (hn : n < Text.length)
    (a : Terminal) (ha : Text[n]? = some (enc a)) (ρ : Role) (bit : Bool) :
    (∃ J ≤ R,
      let y := TextFeedPipelineOutputPrepFinish.finishAt e leftSym enc R rate [] a J
        ⟨(((x.1, ρ, bit), 0), 0), x.2⟩
      TextFeedPipelinePrefixFedPhysical.Complete e leftSym R rate u v Text d p r (n + 1)
        (y.state.1.1.1, y.tape)) ∨
    (∃ z' f,
      let y := (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound
        ⟨(((x.1, ρ, bit), 0), 0), x.2⟩ a
      Link e leftSym R rate z' (y.state.1.1.1, y.tape) ∧
      TextFeedPrefixRank.Good e u v Text d p r (n + 1) f (erase z') ∧
      TextFeedPipelinePrefixReserve.Reserve e Text (n + 1) z' ∧
      y.state.1.1.1.1.1 = 0 ∧ y.state.1.2 = 0 ∧ y.state.2 = 0) := by
  obtain ⟨J, f, hJ, hend, he, hL, hG, hreserve⟩ := arrival_window enc h hl hg hr hz hR hn a ha ρ bit
  by_cases hf : f = 0
  · subst f
    left
    refine ⟨J, hJ, ?_⟩
    simp only [TextFeedPipelineOutputPrepFinish.finishAt, List.foldl_nil,
      TextFeedPipelineOutputPrepFinish.machine_partial e leftSym enc R rate J hJ]
    exact ⟨(work e)^[J] (arrival (enc a) z), hL, hG, hreserve⟩
  · have hJR : J = R := hend.resolve_right hf
    subst J
    right
    refine ⟨(work e)^[R] (arrival (enc a) z), f, ?_⟩
    simp only [TextFeedPipelineOutput.machine_round]
    have hclock := congrArg (fun t => t.1.1.1) he
    have hz' := TextFeedPipelinePrefixFrames.frame_counter enc hz a
    exact ⟨hL, hG, hreserve, hclock.trans hz', by trivial, by trivial⟩

/-- The productive counterpart of frame_cases: every continuing full
frame removes R units of rank, giving the deadline induction its measure. -/
theorem productive_cases {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    (enc : Terminal → Fin k) {leftSym : Fin k} {R rate : ℕ}
    {z : State k} {x : Phys e leftSym R rate}
    (h : TextFeedPipelinePrefixWindow.Safe e u Text) (hl : Link e leftSym R rate z x)
    (hg : TextFeedPrefixRank.Good e u v Text d p r n fuel (erase z))
    (hr : TextFeedPipelinePrefixReserve.Reserve e Text n z)
    (hz : x.1.1.1 = 0) (hR : 0 < R) (hn : n < Text.length) (hroom : u.length ≤ n + 1)
    (a : Terminal) (ha : Text[n]? = some (enc a)) (ρ : Role) (bit : Bool) :
    (∃ J ≤ R,
      let y := TextFeedPipelineOutputPrepFinish.finishAt e leftSym enc R rate [] a J
        ⟨(((x.1, ρ, bit), 0), 0), x.2⟩
      TextFeedPipelinePrefixFedPhysical.Complete e leftSym R rate u v Text d p r (n + 1)
        (y.state.1.1.1, y.tape)) ∨
    (R < fuel ∧ ∃ z',
      let y := (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound
        ⟨(((x.1, ρ, bit), 0), 0), x.2⟩ a
      Link e leftSym R rate z' (y.state.1.1.1, y.tape) ∧
      TextFeedPrefixRank.Good e u v Text d p r (n + 1) (fuel - R) (erase z') ∧
      TextFeedPipelinePrefixReserve.Reserve e Text (n + 1) z' ∧
      y.state.1.1.1.1.1 = 0 ∧ y.state.1.2 = 0 ∧ y.state.2 = 0) := by
  by_cases hf : fuel ≤ R
  · obtain ⟨_, hL, hG, hreserve⟩ := productive_arrival enc h hl hg hr hz hR hn hroom a ha
      fuel (Nat.le_refl _) hf ρ bit
    left
    refine ⟨fuel, hf, ?_⟩
    simp only [TextFeedPipelineOutputPrepFinish.finishAt, List.foldl_nil,
      TextFeedPipelineOutputPrepFinish.machine_partial e leftSym enc R rate fuel hf]
    exact ⟨(work e)^[fuel] (arrival (enc a) z), hL, by simpa only [Nat.sub_self] using hG, hreserve⟩
  · obtain ⟨he, hL, hG, hreserve⟩ := productive_arrival enc h hl hg hr hz hR hn hroom a ha
      R (by omega) (Nat.le_refl _) ρ bit
    right
    refine ⟨by omega, (work e)^[R] (arrival (enc a) z), ?_⟩
    simp only [TextFeedPipelineOutput.machine_round]
    have hclock := congrArg (fun t => t.1.1.1) he
    exact ⟨hL, hG, hreserve,
      hclock.trans (TextFeedPipelinePrefixFrames.frame_counter enc hz a), by trivial, by trivial⟩

/-- info: 'PalPeg.TextFeedPipelineOutputPrefix.productive_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms productive_cases

/-- info: 'PalPeg.TextFeedPipelineOutputPrefix.frame_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frame_cases

/-- info: 'PalPeg.TextFeedPipelineOutputPrefix.frame_or_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frame_or_complete

/-- info: 'PalPeg.TextFeedPipelineOutputPrefix.arrival_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arrival_window

/-- info: 'PalPeg.TextFeedPipelineOutputPrefix.window_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms window_complete

/-- info: 'PalPeg.TextFeedPipelineOutputPrefix.window_preserve_or_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms window_preserve_or_hit

/-- info: 'PalPeg.TextFeedPipelineOutputPrefix.window_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms window_progress

/-- info: 'PalPeg.TextFeedPipelineOutputPrefix.worker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms worker

/-- info: 'PalPeg.TextFeedPipelineOutputPrefix.arrival_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arrival_step

end PalPeg.TextFeedPipelineOutputPrefix
