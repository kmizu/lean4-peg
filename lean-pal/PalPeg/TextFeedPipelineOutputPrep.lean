import PalPeg.TextFeedPipelineOutput
import PalPeg.TextFeedPipelinePrepInput
import PalPeg.TextFeedPipelinePrepFrames

/-! Output observation preserves the preparation machine too. Only the
physical FIFO invariant is required, not an initialized verifier snapshot. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineOutputPrep
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.RTQueueProg
open PalPeg.TextFeedPipelinePrepInput PalPeg.TextFeedPipelineReport
open PalPeg.TextFeedPipelineOutput PalPeg.TextFeedPipelineControl
open PalPeg.ProgLangBank PalPeg.PrepInstance
open PalPeg.ProgLangPersist2

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem reader_ready {e : Env k} (hc : Function.Injective e.code)
    {T : Fin 39 → STape (Fin k)} {q₁ q₂ : Queue (Fin k)} {old : Fin k}
    (h : ReadyAt e T q₁ q₂ old) (ρ : Role) (bit : Bool) :
    ((reader e).sRound ⟨(false, ρ, bit), T⟩ ()).tape = T := by
  obtain ⟨qt₁, m₁, qt₂, m₂, hv, h₁, _⟩ := h
  have htag : (T 10).focus = e.code m₁ := by
    have hh := congrArg (fun U => (U 10).focus) hv
    exact hh
  have hview : ∀ ρ' : Role, T (frontIdx ρ') = toS (qt₁ ρ') := by
    intro ρ'
    have hh := congrArg (fun U => U (Fin.castAdd 13 (ridx ρ'))) hv
    cases ρ' <;> exact hh
  rw [reader_front hc T qt₁ m₁ q₁ htag hview h₁ ρ bit]

theorem sample_ready {e : Env k} (hc : Function.Injective e.code)
    {leftSym : Fin k} {R rate : ℕ}
    (c : Core e leftSym R rate) {T : Fin 39 → STape (Fin k)}
    {q₁ q₂ : Queue (Fin k)} {old : Fin k}
    (h : ReadyAt e T q₁ q₂ old) (ρ : Role) (bit : Bool) :
    let y := sample e leftSym R rate ((c, ρ, bit), T)
    (y.1.1, y.2) = (c, T) := by
  unfold sample
  split
  · exact Prod.ext rfl (reader_ready hc h _ _)
  · rfl

theorem step_ready {e : Env k} (hc : Function.Injective e.code)
    {leftSym : Fin k} {R rate : ℕ}
    (x : State e leftSym R rate × (Fin 39 → STape (Fin k)))
    {q₁ q₂ : Queue (Fin k)} {old : Fin k}
    (h : ReadyAt e
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate (x.1.1, x.2)).2 q₁ q₂ old) :
    let y := step (Terminal := Terminal) e leftSym R rate x
    (y.1.1, y.2) = TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate (x.1.1, x.2) :=
  sample_ready hc _ h _ _

/-- Actual enqueue, including the first blank-FIFO bootstrap, supplies
the observer's invariant itself. No post-call readiness premise is needed. -/
theorem enqueue_step {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {leftSym : Fin k} {R rate : ℕ}
    (x : State e leftSym R rate × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.1.2.2.1) (hz : x.1.1.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {a : Fin k} (ha : a ≠ e.mark)
    (h : QueuesAt e x.1.1.1.2.1 x.2 q₁ q₂ a) :
    let y := step (Terminal := Terminal) e leftSym R rate x
    (y.1.1, y.2) = TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate (x.1.1, x.2) ∧
      ReadyAt e y.2 (snoc q₁ a) (snoc q₂ a) a := by
  obtain ⟨hr, _⟩ := run_queue (Terminal := Terminal) e hc hmb leftSym R rate
    (x.1.1, x.2) hb hz ha h
  have he := step_ready (Terminal := Terminal) hc x hr
  exact ⟨he, (congrArg Prod.snd he).symm ▸ hr⟩

/-- A real preparation instruction leaves the FIFO slots untouched, so
its following observation also restores every tape. -/
theorem prep_step {e : Env k} (hc : Function.Injective e.code)
    {leftSym : Fin k} {R rate : ℕ}
    (x : State e leftSym R rate × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.1.2.2.1) (hz : x.1.1.1.1 ≠ 0)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (hq : ReadyAt e x.2 q₁ q₂ old)
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (hs : TextFeedPipelinePrepWindow.ControlEq x.1.1.1.2.2.val s r)
    (a : PrepAct k)
    (ha : (stepStack (evalConds (TextFeedPrepResume.source e)
      (fun j => (TextFeedPipelineBank.prepView x.2 j).focus)) s).2 = some a) :
    let y := step (Terminal := Terminal) e leftSym R rate x
    (y.1.1, y.2) = TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate (x.1.1, x.2) ∧
      ReadyAt e y.2 q₁ q₂ old := by
  obtain ⟨ht, _⟩ := TextFeedPipelineHandoff.run_prep_step (Terminal := Terminal)
    e leftSym R rate (x.1.1, x.2) hb hz s r (hs _) a ha
  have hr := ready_prep hq (TextFeedPrepResume.sourceStep e s (TextFeedPipelineBank.prepView x.2)).2
  rw [← ht] at hr
  have he := step_ready (Terminal := Terminal) hc x hr
  exact ⟨he, (congrArg Prod.snd he).symm ▸ hr⟩

/-- Every finite preparation run is preserved when its actual post-call
queues are ready. Observation slots may run, but all core tapes are restored. -/
theorem steps_ready {e : Env k} (hc : Function.Injective e.code)
    {leftSym : Fin k} {R rate : ℕ}
    (x : State e leftSym R rate × (Fin 39 → STape (Fin k))) (N : ℕ)
    (h : ∀ j < N, ∃ q₁ q₂ old, ReadyAt e
      ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[j + 1]
        (x.1.1, x.2)).2 q₁ q₂ old) :
    let y := (step (Terminal := Terminal) e leftSym R rate)^[N] x
    (y.1.1, y.2) =
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] (x.1.1, x.2) := by
  have hall : ∀ i, i ≤ N →
      let y := (step (Terminal := Terminal) e leftSym R rate)^[i] x
      (y.1.1, y.2) =
        (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[i] (x.1.1, x.2) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have he := ih (by omega)
      obtain ⟨q₁, q₂, old, hready⟩ := h i (by omega)
      rw [Function.iterate_succ_apply'] at hready
      have ht := step_ready (Terminal := Terminal) hc
        ((step (Terminal := Terminal) e leftSym R rate)^[i] x)
        (q₁ := q₁) (q₂ := q₂) (old := old) (by rw [he]; exact hready)
      rw [he] at ht
      simpa only [Function.iterate_succ_apply'] using ht
  exact hall N (Nat.le_refl _)

/-- The preservation statement holds for the actual 96-microstep call
machine, not just its call-level description. -/
theorem microsteps_ready {e : Env k} (hc : Function.Injective e.code)
    {leftSym : Fin k} {R rate : ℕ}
    (x : State e leftSym R rate × (Fin 39 → STape (Fin k))) (N : ℕ)
    (h : ∀ j < N, ∃ q₁ q₂ old, ReadyAt e
      ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[j + 1]
        (x.1.1, x.2)).2 q₁ q₂ old) :
    let y := (List.replicate (N * 96) none).foldl
      (call (Terminal := Terminal) e leftSym R rate).sMicroStep ⟨(x.1, 0), x.2⟩
    (y.state.1.1, y.tape) =
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] (x.1.1, x.2) := by
  rw [call_noneBlocks]
  exact steps_ready hc x N h

/-- A productive physical prep window supplies every intermediate FIFO
invariant from its initial one, including the actual observation microsteps. -/
theorem prep_window {e : Env k} (hc : Function.Injective e.code)
    {leftSym : Fin k} {R rate : ℕ}
    (x : State e leftSym R rate × (Fin 39 → STape (Fin k))) (N : ℕ)
    (hb : AtBoundary (programs e) x.1.1.2.2.1)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (hq : ReadyAt e x.2 q₁ q₂ old)
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (hs : TextFeedPipelinePrepWindow.ControlEq x.1.1.1.2.2.val s r)
    (htrace : (trace (TextFeedPrepResume.source e) e.blank (List.replicate N none)
      (s, TextFeedPipelineBank.prepView x.2)).length = N)
    (hpos : N ≠ 0 → 0 < x.1.1.1.1.val) (hlen : x.1.1.1.1.val + N ≤ R + 1) :
    let y := (List.replicate (N * 96) none).foldl
      (call (Terminal := Terminal) e leftSym R rate).sMicroStep ⟨(x.1, 0), x.2⟩
    (y.state.1.1, y.tape) =
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] (x.1.1, x.2) := by
  apply microsteps_ready hc x N
  intro j hj
  have he : List.replicate N (none : Option Unit) =
      List.replicate (j + 1) none ++ List.replicate (N - (j + 1)) none := by
    rw [← List.replicate_add]
    congr 1
    omega
  have ht := htrace
  rw [he, trace_append, List.length_append] at ht
  have h₁ := trace_length_le (TextFeedPrepResume.source e) e.blank
    (List.replicate (j + 1) none) (s, TextFeedPipelineBank.prepView x.2)
  have h₂ := trace_length_le (TextFeedPrepResume.source e) e.blank
    (List.replicate (N - (j + 1)) none)
    (runInputs (TextFeedPrepResume.source e) e.blank (List.replicate (j + 1) none)
      (s, TextFeedPipelineBank.prepView x.2))
  simp only [List.length_replicate] at h₁ h₂
  obtain ⟨hout, _⟩ := TextFeedPipelinePrepWindow.run_window (Terminal := Terminal)
    e leftSym R rate (j + 1) (x.1.1, x.2) hb s r
    (TextFeedPipelineBank.prepView x.2) rfl hs (by omega)
    (by intro _; exact hpos (by omega))
    (by change x.1.1.1.1.val + (j + 1) ≤ R + 1; omega)
  refine ⟨q₁, q₂, old, ?_⟩
  rw [hout]
  exact ready_prep hq _

/-- One real input capture followed by a productive partial prep frame.
The initial FIFO bootstrap and all observer calls are included. -/
theorem busy_observed {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {leftSym : Fin k} {R rate : ℕ} (enc : Terminal → Fin k) (J : ℕ) (hJR : J ≤ R)
    (c : Core e leftSym R rate) (T : Fin 39 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hz : c.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (hq : QueuesAt e c.1.2.1 T q₁ q₂ old)
    (a : Terminal) (ha : enc a ≠ e.mark)
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (hs : TextFeedPipelinePrepWindow.ControlEq c.1.2.2.val s r)
    (htrace : (trace (TextFeedPrepResume.source e) e.blank (List.replicate J none)
      (s, TextFeedPipelineBank.prepView T)).length = J) (ρ : Role) (bit : Bool) :
    let U := arriveA e.blank (DualQueueShared.capture enc) (some a) T
    let y := (step (Terminal := Terminal) e leftSym R rate)^[J + 1] ((c, ρ, bit), U)
    (y.1.1, y.2) = (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J + 1] (c, U) := by
  apply steps_ready hc _ (J + 1)
  intro j hj
  have he : List.replicate J (none : Option Unit) =
      List.replicate j none ++ List.replicate (J - j) none := by
    rw [← List.replicate_add]
    congr 1
    omega
  have ht := htrace
  rw [he, trace_append, List.length_append] at ht
  have h₁ := trace_length_le (TextFeedPrepResume.source e) e.blank
    (List.replicate j none) (s, TextFeedPipelineBank.prepView T)
  have h₂ := trace_length_le (TextFeedPrepResume.source e) e.blank
    (List.replicate (J - j) none)
    (runInputs (TextFeedPrepResume.source e) e.blank (List.replicate j none)
      (s, TextFeedPipelineBank.prepView T))
  simp only [List.length_replicate] at h₁ h₂
  obtain ⟨c', T', hy, _, _, hr, _⟩ := TextFeedPipelinePrepFrames.busy_calls
    hc hmb leftSym enc R rate j (by omega) c T hb hz hq a ha s r
    (TextFeedPipelineBank.prepView T) rfl hs (by omega)
  refine ⟨snoc q₁ (enc a), snoc q₂ (enc a), enc a, ?_⟩
  change ReadyAt e ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[j + 1]
    (c, arriveA e.blank (DualQueueShared.capture enc) (some a) T)).2 _ _ _
  rw [hy]
  exact hr

/-- A complete input round of the actual output machine agrees with the
existing core preparation execution, with the input captured exactly once. -/
theorem prep_round {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {leftSym : Fin k} {R rate : ℕ} (enc : Terminal → Fin k)
    (c : Core e leftSym R rate) (T : Fin 39 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hz : c.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (hq : QueuesAt e c.1.2.1 T q₁ q₂ old)
    (a : Terminal) (ha : enc a ≠ e.mark)
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (hs : TextFeedPipelinePrepWindow.ControlEq c.1.2.2.val s r)
    (htrace : (trace (TextFeedPrepResume.source e) e.blank (List.replicate R none)
      (s, TextFeedPipelineBank.prepView T)).length = R) (ρ : Role) (bit : Bool) :
    let y := (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound ⟨(((c, ρ, bit), 0), 0), T⟩ a
    (y.state.1.1.1, y.tape) =
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[R + 1]
        (c, arriveA e.blank (DualQueueShared.capture enc) (some a) T) := by
  rw [TextFeedPipelineOutput.machine_round]
  exact busy_observed hc hmb enc R (Nat.le_refl _) c T hb hz hq a ha s r hs htrace ρ bit

/-- Productive preparation over an arbitrary real input word on the
output machine, preserving source control, FIFO contents and both clocks. -/
theorem prep_frames {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {leftSym : Fin k} {R rate : ℕ} (enc : Terminal → Fin k) (word : List Terminal)
    (c : Core e leftSym R rate) (T : Fin 39 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hz : c.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (hq : QueuesAt e c.1.2.1 T q₁ q₂ old)
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (P : Fin 15 → STape (Fin k)) (hv : TextFeedPipelineBank.prepView T = P)
    (hs : TextFeedPipelinePrepWindow.ControlEq c.1.2.2.val s r)
    (htrace : (trace (TextFeedPrepResume.source e) e.blank
      (List.replicate (word.length * R) none) (s, P)).length = word.length * R)
    (hall : ∀ a ∈ word, enc a ≠ e.mark) (ρ : Role) (bit : Bool) :
    let z := word.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound
      ⟨(((c, ρ, bit), 0), 0), T⟩
    let u := runInputs (TextFeedPrepResume.source e) e.blank
      (List.replicate (word.length * R) none) (s, P)
    ∃ c' T' ρ' bit', z = ⟨(((c', ρ', bit'), 0), 0), T'⟩ ∧
      TextFeedPipelineBank.prepView T' = u.2 ∧ AtBoundary (programs e) c'.2.2.1 ∧
      QueuesAt e c'.1.2.1 T' (word.foldl (fun q a => snoc q (enc a)) q₁)
        (word.foldl (fun q a => snoc q (enc a)) q₂) (word.foldl (fun _ a => enc a) old) ∧
      TextFeedPipelinePrepWindow.ControlEq c'.1.2.2.val u.1 r ∧ c'.1.1 = 0 := by
  induction word generalizing c T q₁ q₂ old s P ρ bit with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul, List.replicate_zero, runInputs_nil, List.foldl_nil]
    exact ⟨c, T, ρ, bit, rfl, hv, hb, hq, hs, hz⟩
  | cons a word ih =>
    have hsize : (a :: word).length * R = R + word.length * R := by
      simp only [List.length_cons, Nat.succ_mul]; omega
    rw [hsize] at htrace
    obtain ⟨hpre, htail⟩ := TextFeedPrepFrames.live_split e s P R (word.length * R) htrace
    obtain ⟨c1, T1, hz1, hv1, hb1, hr1, hs1, hc1, hf1⟩ :=
      TextFeedPipelinePrepFrames.busy_frame hc hmb leftSym enc R rate c T hb hz hq
        a (hall a List.mem_cons_self) s r P hv hs hpre
    have hcore := congrArg (fun z => (z.state.1.1, z.tape)) hz1
    simp only [TextFeedPipelineControl.machine_round] at hcore
    have hp := prep_round hc hmb enc c T hb hz hq a (hall a List.mem_cons_self)
      s r hs (by rw [hv]; exact hpre) ρ bit
    have hp' := hp.trans hcore
    let y := (step (Terminal := Terminal) e leftSym R rate)^[R + 1]
      ((c, ρ, bit), arriveA e.blank (DualQueueShared.capture enc) (some a) T)
    have hy : (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound
        ⟨(((c, ρ, bit), 0), 0), T⟩ a =
        ⟨(((c1, y.1.2.1, y.1.2.2), 0), 0), T1⟩ := by
      rw [TextFeedPipelineOutput.machine_round]
      rw [TextFeedPipelineOutput.machine_round] at hp'
      change (y.1.1, y.2) = (c1, T1) at hp'
      have hcy := congrArg Prod.fst hp'
      have hty := congrArg Prod.snd hp'
      change _ = _ at hcy hty
      change (⟨(((y.1.1, y.1.2.1, y.1.2.2), 0), 0), y.2⟩ :
        SConfig ((State e leftSym R rate × Fin 96) × Fin ((R + 1) * 96 + 1)) (Fin k) 39) = _
      rw [hcy, hty]
    have hq1 : QueuesAt e c1.1.2.1 T1 (snoc q₁ (enc a)) (snoc q₂ (enc a)) (enc a) := by
      rw [hf1]; exact hr1
    have hh := ih c1 T1 hb1 hc1 hq1
      (runInputs (TextFeedPrepResume.source e) e.blank (List.replicate R none) (s, P)).1
      (runInputs (TextFeedPrepResume.source e) e.blank (List.replicate R none) (s, P)).2
      hv1 hs1 htail (fun b hb => hall b (List.mem_cons_of_mem a hb)) y.1.2.1 y.1.2.2
    simpa only [List.foldl_cons, hy, hsize, List.replicate_add, runInputs_append, Prod.mk.eta] using hh

/-- info: 'PalPeg.TextFeedPipelineOutputPrep.prep_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prep_frames

/-- info: 'PalPeg.TextFeedPipelineOutputPrep.prep_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prep_round

/-- info: 'PalPeg.TextFeedPipelineOutputPrep.prep_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prep_window

/-- info: 'PalPeg.TextFeedPipelineOutputPrep.enqueue_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms enqueue_step

/-- info: 'PalPeg.TextFeedPipelineOutputPrep.microsteps_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms microsteps_ready

/-- info: 'PalPeg.TextFeedPipelineOutputPrep.steps_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms steps_ready

/-- info: 'PalPeg.TextFeedPipelineOutputPrep.step_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_ready

end PalPeg.TextFeedPipelineOutputPrep
