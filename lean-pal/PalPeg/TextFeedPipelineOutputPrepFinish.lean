import PalPeg.TextFeedPipelineOutputPrep
import PalPeg.TextFeedPipelinePrepFinish
import PalPeg.TextFeedPipelinePrefixEndpoint
import PalPeg.TextFeedPipelinePrefixReserve
import PalPeg.TextFeedPipelinePrefixSetup

/-! Exact preparation completion inside a frame of the output machine. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineOutputPrepFinish
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.PrepInstance
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelinePrepWindow
open PalPeg.TextFeedPipelinePrepInput PalPeg.TextFeedPipelineOutputPrep
open PalPeg.TextFeedPipelineOutput (Core State step call)
open PalPeg.TextFeedPrepResume (source)
open PalPeg.PatternTapes PalPeg.PatternProg

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

abbrev Config (e : Env k) (leftSym : Fin k) (R rate : ℕ) :=
  SConfig ((State e leftSym R rate × Fin 96) × Fin ((R + 1) * 96 + 1)) (Fin k) 39

def phase (R J : ℕ) : Fin ((R + 1) * 96 + 1) := nextPhase^[(J + 1) * 96 + 1] 0

theorem phase_full (R : ℕ) : phase R R = 0 :=
  nextPhase_iterate_round (Nat.zero_lt_succ _)

noncomputable def finishAt (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (word : List Terminal) (a : Terminal) (J : ℕ) (x : Config e leftSym R rate) : Config e leftSym R rate :=
  (some a :: List.replicate ((J + 1) * 96) none).foldl
    (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep
    (word.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound x)

theorem machine_partial (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate J : ℕ) (hJ : J ≤ R) (q : State e leftSym R rate)
    (T : Fin 39 → STape (Fin k)) (a : Terminal) :
    (some a :: List.replicate ((J + 1) * 96) none).foldl
      (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep
      ⟨((q, 0), 0), T⟩ =
      let y := (step (Terminal := Terminal) e leftSym R rate)^[J + 1]
        (q, arriveA e.blank (DualQueueShared.capture enc) (some a) T)
      ⟨((y.1, 0), phase R J), y.2⟩ := by
  have hf := frameMachine_prefix (call e leftSym R rate) (DualQueueShared.capture enc)
    ((R + 1) * 96) ((J + 1) * 96) (by omega) a (q, 0) T
  have hb : (call (Terminal := Terminal) e leftSym R rate).blank = e.blank := rfl
  have hcall := TextFeedPipelineOutput.call_noneBlocks (Terminal := Terminal) e leftSym R rate (J + 1)
    (q, arriveA e.blank (DualQueueShared.capture enc) (some a) T)
  rw [hb, hcall] at hf
  exact hf

theorem finishAt_full (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate : ℕ) (q : State e leftSym R rate) (T : Fin 39 → STape (Fin k)) (a : Terminal) :
    finishAt e leftSym enc R rate [] a R ⟨((q, 0), 0), T⟩ =
      (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound ⟨((q, 0), 0), T⟩ a := by
  rw [finishAt, List.foldl_nil, machine_partial e leftSym enc R rate R (Nat.le_refl _),
    phase_full, TextFeedPipelineOutput.machine_round]

theorem partial_remaining (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate J : ℕ) (hJ : J ≤ R) (q : State e leftSym R rate)
    (T : Fin 39 → STape (Fin k)) (a : Terminal) (hz : q.1.1.1 = 0) :
    let x := finishAt e leftSym enc R rate [] a J ⟨((q, 0), 0), T⟩
    TextFeedPipelinePrefixResume.remaining (x.state.1.1.1, x.tape) = R - J := by
  simp only [finishAt, List.foldl_nil, machine_partial e leftSym enc R rate J hJ]
  unfold TextFeedPipelinePrefixResume.remaining
  rw [TextFeedPipelineOutput.step_counter_iterate, hz]
  by_cases he : J = R
  · subst J
    have hh : nextPhase^[R + 1] (0 : Fin (R + 1)) = 0 :=
      nextPhase_iterate_round (Nat.zero_lt_succ R)
    rw [hh]
    simp
  · have hlt : J + 1 < R + 1 := by omega
    have hh : nextPhase^[J + 1] (0 : Fin (R + 1)) = ⟨J + 1, hlt⟩ :=
      nextPhase_iterate (Nat.zero_lt_succ R) (J + 1) hlt
    rw [hh]
    have hne : (⟨J + 1, hlt⟩ : Fin (R + 1)) ≠ 0 := by
      intro hh
      have hh' := congrArg Fin.val hh
      simp at hh'
    simp only [if_neg hne]
    omega

/-- info: 'PalPeg.TextFeedPipelineOutputPrepFinish.partial_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms partial_remaining

/-- Resume a partial frame using actual microsteps. No capture is repeated,
and the observer state is carried through the remaining calls. -/
theorem partial_extend (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate J K : ℕ) (hJK : J + K ≤ R) (q : State e leftSym R rate)
    (T : Fin 39 → STape (Fin k)) (a : Terminal) :
    let x := finishAt e leftSym enc R rate [] a J ⟨((q, 0), 0), T⟩
    (List.replicate (K * 96) none).foldl
      (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep x =
      let y := (step (Terminal := Terminal) e leftSym R rate)^[K] (x.state.1.1, x.tape)
      ⟨((y.1, 0), phase R (J + K)), y.2⟩ := by
  have hJ : J ≤ R := by omega
  have hsum : (J + 1) * 96 + K * 96 = (J + K + 1) * 96 := by omega
  have hfold : (List.replicate (K * 96) none).foldl
      (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep
      (finishAt e leftSym enc R rate [] a J ⟨((q, 0), 0), T⟩) =
      finishAt e leftSym enc R rate [] a (J + K) ⟨((q, 0), 0), T⟩ := by
    simp only [finishAt, List.foldl_nil, ← List.foldl_append, List.cons_append,
      ← List.replicate_add, hsum]
  dsimp only
  rw [hfold]
  simp only [finishAt, List.foldl_nil, machine_partial e leftSym enc R rate J hJ,
    machine_partial e leftSym enc R rate (J + K) hJK]
  rw [show J + K + 1 = K + (J + 1) by omega, Function.iterate_add_apply]

/-- info: 'PalPeg.TextFeedPipelineOutputPrepFinish.partial_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms partial_extend

/-- The real output machine reaches the finite prep endpoint, including
all captures, observations and the exact final partial-frame phase. -/
theorem finish_at {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (enc : Terminal → Fin k) (R rate J : ℕ) (hJ : J ≤ R)
    (c : Core e leftSym R rate) (T : Fin 39 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hz : c.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (hq : QueuesAt e c.1.2.1 T q₁ q₂ old)
    (p : Prog (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (P : Fin 15 → STape (Fin k)) (hv : prepView T = P) (hs : ControlEq c.1.2.2.val [p] r)
    (tr : List (Fin 15 → Fin k × Move)) (he : Exec (source e) e.blank p P tr)
    (word : List Terminal) (a : Terminal) (hlen : tr.length = word.length * R + J)
    (hall : ∀ b ∈ word ++ [a], enc b ≠ e.mark) (ρ : Role) (bit : Bool) :
    ∃ c' T' ρ' bit', finishAt e leftSym enc R rate word a J ⟨(((c, ρ, bit), 0), 0), T⟩ =
        ⟨(((c', ρ', bit'), 0), phase R J), T'⟩ ∧
      prepView T' = applyTrace e.blank P tr ∧ AtBoundary (programs e) c'.2.2.1 ∧
      ReadyAt e T' (snoc (word.foldl (fun q b => snoc q (enc b)) q₁) (enc a))
        (snoc (word.foldl (fun q b => snoc q (enc b)) q₂) (enc a)) (enc a) ∧ c'.1.2.1 = false ∧
      stepStack (taskEval e (fun j => (T' j).focus)) c'.1.2.2.val =
        stepStack (taskEval e (fun j => (T' j).focus)) r := by
  have hlive := TextFeedPrepHandoff.exec_live_prefix e p P tr he tr.length (Nat.le_refl _)
  rw [hlen] at hlive
  obtain ⟨hpre, htail⟩ := TextFeedPrepFrames.live_split e [p] P (word.length * R) J hlive
  obtain ⟨c1, T1, ρ1, bit1, hz1, hv1, hb1, hr1, hs1, hc1⟩ :=
    prep_frames hc hmb enc word c T hb hz hq [p] r P hv hs hpre
      (fun b hb => hall b (List.mem_append_left _ hb)) ρ bit
  let v := runInputs (source e) e.blank (List.replicate (word.length * R) none) ([p], P)
  have ha := hall a (List.mem_append_right _ List.mem_cons_self)
  obtain ⟨c2, T2, hz2, hv2, hb2, hr2, hs2, _, hf2⟩ :=
    TextFeedPipelinePrepFrames.busy_calls hc hmb leftSym enc R rate J hJ c1 T1 hb1 hc1 hr1
      a ha v.1 r v.2 hv1 hs1 htail
  have hobs := busy_observed hc hmb enc J hJ c1 T1 hb1 hc1 hr1 a ha v.1 r hs1
    (by rw [hv1]; exact htail) ρ1 bit1
  let y := (step (Terminal := Terminal) e leftSym R rate)^[J + 1]
    ((c1, ρ1, bit1), arriveA e.blank (DualQueueShared.capture enc) (some a) T1)
  have hproj : (y.1.1, y.2) = (c2, T2) := hobs.trans hz2
  have hcomp : runInputs (source e) e.blank (List.replicate J none) v =
      runInputs (source e) e.blank (List.replicate tr.length none) ([p], P) := by
    rw [hlen, List.replicate_add, runInputs_append]
  simp only [Prod.mk.eta] at hv2 hs2
  rw [hcomp] at hv2 hs2
  obtain ⟨hout, hreturn⟩ := TextFeedPrepHandoff.exec_endpoint e p P tr he
  refine ⟨c2, T2, y.1.2.1, y.1.2.2, ?_, hv2.trans hout, hb2, hr2, hf2, ?_⟩
  · rw [finishAt, hz1, machine_partial e leftSym enc R rate J hJ]
    have hcy := congrArg Prod.fst hproj
    have hty := congrArg Prod.snd hproj
    change (⟨(((y.1.1, y.1.2.1, y.1.2.2), 0), phase R J), y.2⟩ : Config e leftSym R rate) = _
    rw [hcy, hty]
  · have hreturn' : (stepStack (evalConds (source e) (fun j => (prepView T2 j).focus))
        (runInputs (source e) e.blank (List.replicate tr.length none) ([p], P)).1).2 = none := by
      rw [hv2]
      exact hreturn
    exact (hs2 _).trans ((step_sim_map Sum.inl Sum.inl
      (evalConds (source e) (fun j => (prepView T2 j).focus))
      (taskEval e (fun j => (T2 j).focus)) (fun _ => rfl) _ r).2 hreturn')

/-- Instantiate completion with the concrete finite decomposition/setup
program and its linear cost bound, on the observation-enabled machine. -/
theorem setup_finishes {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (c : Core e leftSym R rate) (T : Fin 39 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hz : c.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (hq : QueuesAt e c.1.2.1 T q₁ q₂ old)
    (hs : c.1.2.2.val = [task e leftSym rate]) {S : PatternTapes.Tapes k}
    (hv : prepView T = TSg S) {w Text : List (Fin k)} {L : ℕ}
    (hpre : StageTapes.PrepPre e.blank e.mark leftSym L w Text S)
    (hstart : e.startSym ∉ PrepInstances.stagePat w L)
    (hend : e.endSym ∉ PrepInstances.stagePat w L) (hne : e.startSym ≠ e.endSym)
    (ρ : Role) (bit : Bool) :
    let d := PrepInstances.prepRes w L
    ∃ ticks S', ticks ≤ (GSPreProg.preprocessSlope + 25 + 7 * rate) * L +
        GSPreProg.preprocessOffset + 37 + 11 * rate ∧
      GSVTapes.VEncodes' e.blank e.startSym e.endSym e.mark
        ((w.take L).reverse.take d.1) ((w.take L).reverse.drop d.1)
        (TextFeed.padW e.blank Text 0) rate d.2.1 d.2.2 (toGS S', toVExt S') (⟨0, 0⟩, 0) ∧
      ∀ (word : List Terminal) (a : Terminal) (J : ℕ), J ≤ R → ticks = word.length * R + J →
        (∀ b ∈ word ++ [a], enc b ≠ e.mark) →
        ∃ c' T' ρ' bit', finishAt e leftSym enc R rate word a J ⟨(((c, ρ, bit), 0), 0), T⟩ =
            ⟨(((c', ρ', bit'), 0), phase R J), T'⟩ ∧
          prepView T' = TSg S' ∧ AtBoundary (programs e) c'.2.2.1 ∧
          ReadyAt e T' (snoc (word.foldl (fun q b => snoc q (enc b)) q₁) (enc a))
            (snoc (word.foldl (fun q b => snoc q (enc b)) q₂) (enc a)) (enc a) ∧ c'.1.2.1 = false ∧
          stepStack (taskEval e (fun j => (T' j).focus)) c'.1.2.2.val =
            stepStack (taskEval e (fun j => (T' j).focus)) [liftPrefix TextFeedPrefixAtomic.source, afterPrefix rate] := by
  dsimp only
  obtain ⟨tr, S', he, ht, hv', hn⟩ := finitePrepSetup_exec (Terminal := Unit) rate hmb hpre hstart hend hne
  refine ⟨tr.length, S', hn, hv', ?_⟩
  intro word a J hJ hlen hall
  have hs' : ControlEq c.1.2.2.val
      [finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate] [afterPrep rate] := by
    rw [hs]
    exact control_initial e leftSym rate
  obtain ⟨c', T', ρ', bit', hz', hp, hb', hq', hf, hctrl⟩ := finish_at hc hmb
    leftSym enc R rate J hJ c T hb hz hq
    (finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate) [afterPrep rate]
    (TSg S) hv hs' tr he word a hlen hall ρ bit
  refine ⟨c', T', ρ', bit', hz', hp.trans ht, hb', hq', hf, ?_⟩
  rw [afterPrep, stepStack_seq] at hctrl
  exact hctrl

/-- The observed preparation endpoint initializes both prefix invariants,
without resetting either machine clock or the observation state. -/
theorem setup_prefix {e : Env k} (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (c : Core e leftSym R rate) (T : Fin 39 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hz : c.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (hq : QueuesAt e c.1.2.1 T q₁ q₂ old)
    (hs : c.1.2.2.val = [task e leftSym rate]) {S : PatternTapes.Tapes k}
    (hv : prepView T = TSg S) {w Text : List (Fin k)} {L n : ℕ}
    (hpre : StageTapes.PrepPre e.blank e.mark leftSym L w Text S)
    (h : TextFeedPipelinePrefixWindow.Safe e (PrepInstances.stagePat w L) Text)
    (hi₁ : Inv q₁) (hl₁ : toList q₁ = Text.take n)
    (hi₂ : Inv q₂) (hl₂ : toList q₂ = Text.take n) (ρ : Role) (bit : Bool) :
    let d := PrepInstances.prepRes w L
    let u := (w.take L).reverse.take d.1
    let v := (w.take L).reverse.drop d.1
    ∃ ticks, ticks ≤ (GSPreProg.preprocessSlope + 25 + 7 * rate) * L +
        GSPreProg.preprocessOffset + 37 + 11 * rate ∧
      ∀ (word : List Terminal) (a : Terminal) (J : ℕ), J ≤ R → ticks = word.length * R + J →
        TextFeedPrefixDeadline.Valid Text n ((word ++ [a]).map enc) →
        let y := finishAt e leftSym enc R rate word a J ⟨(((c, ρ, bit), 0), 0), T⟩
        ∃ z, TextFeedPipelinePrefixLink.Link e leftSym R rate z (y.state.1.1.1, y.tape) ∧
          TextFeedPrefixRank.Good e u v Text rate d.2.1 d.2.2
            (n + word.length + 1) (5 * u.length + 2) (TextFeedPipelinePrefixLink.erase z) ∧
          TextFeedPipelinePrefixReserve.Reserve e Text (n + word.length + 1) z ∧
          y.state.1.2 = 0 ∧ y.state.2 = phase R J := by
  dsimp only
  obtain ⟨ticks, S', ht, hve, hfinish⟩ := setup_finishes h.code h.mark_blank
    leftSym enc R rate c T hb hz hq hs hv hpre h.start_u h.end_u h.start_end ρ bit
  refine ⟨ticks, ht, ?_⟩
  intro word a J hJ he hvalid
  have hall : ∀ b ∈ word ++ [a], enc b ≠ e.mark := by
    intro b hmem heq
    exact h.mark_text (heq ▸ TextFeedPipelinePrefixSetup.valid_mem hvalid
      (enc b) (List.mem_map.mpr ⟨b, hmem, rfl⟩))
  obtain ⟨c', T', ρ', bit', hf, hp, hb', hq', hfirst, hctrl⟩ := hfinish word a J hJ he hall
  have hlist₁ := TextFeedPipelinePrepReady.arrivals_contents enc hi₁ hl₁ word a hvalid
  have hlist₂ := TextFeedPipelinePrepReady.arrivals_contents enc hi₂ hl₂ word a hvalid
  obtain ⟨z, hlink, hg, hQ, hX⟩ := TextFeedPipelinePrefixEndpoint.ready_to_prefix
    (x := (c', T')) hp hq' hlist₁ hb' hfirst hctrl hve
  have hr : TextFeedPipelinePrefixReserve.Reserve e Text (n + word.length + 1) z := by
    obtain ⟨_, _, _, _, _, _, _, _, h₂, _⟩ := hlink
    exact ⟨h₂.inv, hQ ▸ hlist₂, hX⟩
  rw [hf]
  exact ⟨z, hlink, hg, hr, rfl, rfl⟩

/-- info: 'PalPeg.TextFeedPipelineOutputPrepFinish.setup_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms setup_prefix

/-- info: 'PalPeg.TextFeedPipelineOutputPrepFinish.setup_finishes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms setup_finishes

/-- info: 'PalPeg.TextFeedPipelineOutputPrepFinish.finish_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finish_at

end PalPeg.TextFeedPipelineOutputPrepFinish
