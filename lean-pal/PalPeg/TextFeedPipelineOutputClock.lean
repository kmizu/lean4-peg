import PalPeg.TextFeedPipelineOutputInitial

/-! The observed call schedule is an execution of the actual fixed-speed
machine, with the outer input clock synchronized rather than reset. -/
set_option autoImplicit false
namespace PalPeg.TextFeedPipelineOutputClock
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelineObserved (View opStep)

variable {k : ℕ} {Terminal : Type}
noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

def clock {R : ℕ} (p : Fin (R + 1)) : Fin ((R + 1) * 96 + 1) :=
  if p = 0 then 0 else ⟨p.val * 96 + 1, by have := p.isLt; omega⟩

theorem clock_zero (R : ℕ) : clock (0 : Fin (R + 1)) = 0 := by simp [clock]

private theorem advance {B : ℕ} (p : Fin B) (N : ℕ) (h : p.val + N < B) :
    nextPhase^[N] p = ⟨p.val + N, h⟩ := by
  have hB : 0 < B := Nat.zero_lt_of_lt p.isLt
  have hp : nextPhase^[p.val] (⟨0, hB⟩ : Fin B) = p :=
    nextPhase_iterate hB p.val p.isLt
  calc
    nextPhase^[N] p = nextPhase^[N + p.val] ⟨0, hB⟩ := by rw [Function.iterate_add_apply, hp]
    _ = ⟨p.val + N, h⟩ := by
      rw [Nat.add_comm N p.val]
      exact nextPhase_iterate hB _ h

theorem clock_next {R : ℕ} (p : Fin (R + 1)) (hp : p ≠ 0) :
    nextPhase^[96] (clock p) = clock (nextPhase p) := by
  have hb := p.isLt
  rw [clock, if_neg hp]
  by_cases h : p.val + 1 < R + 1
  · have hn : nextPhase p = ⟨p.val + 1, h⟩ := by simp only [nextPhase, dif_pos h]
    have hne : (⟨p.val + 1, h⟩ : Fin (R + 1)) ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp at this
    rw [hn, clock, if_neg hne]
    have hh := advance (⟨p.val * 96 + 1, by omega⟩ : Fin ((R + 1) * 96 + 1)) 96
      (by change p.val * 96 + 1 + 96 < (R + 1) * 96 + 1; omega)
    exact hh.trans (Fin.ext (by simp; omega))
  · have hn : nextPhase p = 0 := by simp only [nextPhase, dif_neg h]; rfl
    rw [hn, clock_zero]
    exact TextFeedPipelinePrefixResume.nextPhase_finish 96 _ (by simp; omega)

def embed {e : Env k} {leftSym : Fin k} {R rate : ℕ} (x : View e leftSym R rate) :
    TextFeedPipelineOutputPrepFinish.Config e leftSym R rate :=
  ⟨((x.1, 0), clock x.1.1.1.1), x.2⟩

theorem worker (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (x : View e leftSym R rate) (hz : x.1.1.1.1 ≠ 0) :
    (List.replicate 96 none).foldl
      (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep (embed x) =
      embed (TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate x) := by
  have hpos : 0 < (clock x.1.1.1.1).val := by simp only [clock, if_neg hz]; omega
  have hlen : (clock x.1.1.1.1).val + (List.replicate 96 (none : Option Terminal)).length ≤
      (R + 1) * 96 + 1 := by
    have := x.1.1.1.1.isLt
    simp only [clock, if_neg hz, List.length_replicate]
    omega
  have ht := frameBody_tail (TextFeedPipelineOutput.call e leftSym R rate)
    (DualQueueShared.capture enc) (Nat.zero_lt_succ ((R + 1) * 96))
    (List.replicate 96 none) (clock x.1.1.1.1) ⟨(x.1, 0), x.2⟩ hlen hpos
  rw [TextFeedPipelineOutput.call_noneBlock] at ht
  unfold embed TextFeedPipelineOutput.machine frameMachine
  rw [ofPhases_foldl, ht]
  simp only [List.length_replicate, TextFeedPipelineOutput.step_counter, clock_next _ hz]

theorem clock_partial (R J : ℕ) (hJ : J ≤ R) :
    clock (nextPhase^[J + 1] (0 : Fin (R + 1))) =
      TextFeedPipelineOutputPrepFinish.phase R J := by
  by_cases he : J = R
  · subst J
    have hh : nextPhase^[R + 1] (0 : Fin (R + 1)) = 0 :=
      nextPhase_iterate_round (Nat.zero_lt_succ R)
    rw [hh, clock_zero, TextFeedPipelineOutputPrepFinish.phase_full]
  · have hlt : J + 1 < R + 1 := by omega
    have hh : nextPhase^[J + 1] (0 : Fin (R + 1)) = ⟨J + 1, hlt⟩ :=
      nextPhase_iterate (Nat.zero_lt_succ R) _ hlt
    have hne : (⟨J + 1, hlt⟩ : Fin (R + 1)) ≠ 0 := by
      intro hh
      have := congrArg Fin.val hh
      simp at this
    rw [hh, clock, if_neg hne]
    exact (nextPhase_iterate (Nat.zero_lt_succ ((R + 1) * 96))
      ((J + 1) * 96 + 1) (by omega)).symm

theorem arrival (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (x : View e leftSym R rate) (hz : x.1.1.1.1 = 0) (a : Terminal) :
    (some a :: List.replicate 96 none).foldl
      (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep (embed x) =
      embed (opStep e leftSym R rate enc x (some a)) := by
  have he : embed x = ⟨((x.1, 0), 0), x.2⟩ := by simp only [embed, hz, clock_zero]
  rw [he]
  have hh := TextFeedPipelineOutputPrepFinish.machine_partial e leftSym enc R rate 0
    (Nat.zero_le _) x.1 x.2 a
  have hc : clock (opStep e leftSym R rate enc x (some a)).1.1.1.1 =
      TextFeedPipelineOutputPrepFinish.phase R 0 := by
    unfold opStep
    rw [TextFeedPipelineOutput.step_counter]
    change clock (nextPhase x.1.1.1.1) = _
    rw [hz]
    exact clock_partial R 0 (Nat.zero_le _)
  rw [embed, hc]
  simpa only [Nat.zero_add, Nat.one_mul, Function.iterate_one, opStep,
    TextFeedPipelineObserved.pack, TextFeedPipelineObserved.project,
    TextFeedPipelineInputRun.captured] using hh

theorem partial_embed (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate J : ℕ)
    (hJ : J ≤ R) (x : View e leftSym R rate) (hz : x.1.1.1.1 = 0) (a : Terminal) :
    let y := TextFeedPipelineOutputPrepFinish.finishAt e leftSym enc R rate [] a J (embed x)
    y = embed (y.state.1.1, y.tape) := by
  have he : embed x = ⟨((x.1, 0), 0), x.2⟩ := by simp only [embed, hz, clock_zero]
  simp only [TextFeedPipelineOutputPrepFinish.finishAt, List.foldl_nil, he,
    TextFeedPipelineOutputPrepFinish.machine_partial e leftSym enc R rate J hJ]
  unfold embed
  rw [TextFeedPipelineOutput.step_counter_iterate]
  change _ = (⟨((_, 0), clock (nextPhase^[J + 1] x.1.1.1.1)), _⟩ :
    TextFeedPipelineOutputPrepFinish.Config e leftSym R rate)
  rw [hz, clock_partial R J hJ]

theorem zero_embed {e : Env k} {leftSym : Fin k} {R rate : ℕ}
    (x : TextFeedPipelineOutputPrepFinish.Config e leftSym R rate)
    (hz : x.state.1.1.1.1.1 = 0) (h96 : x.state.1.2 = 0) (hout : x.state.2 = 0) :
    x = embed (x.state.1.1, x.tape) := by
  rcases x with ⟨⟨⟨q, ph⟩, out⟩, T⟩
  change ph = 0 at h96
  change out = 0 at hout
  subst ph
  subst out
  change q.1.1.1 = 0 at hz
  simp only [embed, hz, clock_zero]

/-- Every actual prep/prefix endpoint has the synchronized clock used by
the startup realization, including the final partial input frame. -/
theorem finishAt_embed (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate J : ℕ)
    (hJ : J ≤ R) (x : TextFeedPipelineOutputPrepFinish.Config e leftSym R rate)
    (hz : x.state.1.1.1.1.1 = 0) (h96 : x.state.1.2 = 0) (hout : x.state.2 = 0)
    (word : List Terminal) (a : Terminal) :
    let y := TextFeedPipelineOutputPrepFinish.finishAt e leftSym enc R rate word a J x
    y = embed (y.state.1.1, y.tape) := by
  let x₁ := word.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound x
  obtain ⟨hz₁, h96₁, hout₁⟩ := TextFeedPipelineOutputPrefixFrames.rounds_clocks enc word x hz h96 hout
  have he := zero_embed x₁ hz₁ h96₁ hout₁
  change let y := TextFeedPipelineOutputPrepFinish.finishAt e leftSym enc R rate [] a J x₁
         y = embed (y.state.1.1, y.tape)
  rw [he]
  exact partial_embed e leftSym enc R rate J hJ (x₁.state.1.1, x₁.tape) hz₁ a

noncomputable def block {e : Env k} {leftSym : Fin k} {R rate : ℕ}
    (z : List Terminal × View e leftSym R rate) : List (Option Terminal) :=
  if z.2.1.1.1.1 = 0 then
    match z.1 with
    | [] => []
    | a :: _ => some a :: List.replicate 96 none
  else List.replicate 96 none

noncomputable def microInputs (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k) :
    ℕ → List Terminal × View e leftSym R rate → List (Option Terminal)
  | 0, _ => []
  | N + 1, z => block z ++ microInputs e leftSym R rate enc N
      (TextFeedPipelineOutputInitial.tick e leftSym R rate enc z)

theorem tick_realize (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (z : List Terminal × View e leftSym R rate) :
    (block z).foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep (embed z.2) =
      embed (TextFeedPipelineOutputInitial.tick e leftSym R rate enc z).2 := by
  rcases z with ⟨as, x⟩
  by_cases hz : x.1.1.1.1 = 0
  · cases as with
    | nil => simp only [block, hz, if_pos, List.foldl_nil, TextFeedPipelineOutputInitial.tick]
    | cons a as =>
      simp only [block, hz, if_pos, TextFeedPipelineOutputInitial.tick]
      exact arrival e leftSym enc R rate x hz a
  · simp only [block, if_neg hz, TextFeedPipelineOutputInitial.tick]
    exact worker e leftSym enc R rate x hz

/-- Every scheduled call is realized by the original machine, with its
outer phase preserved. This theorem does not assume verifier validity. -/
theorem ticks_realize (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate N : ℕ)
    (z : List Terminal × View e leftSym R rate) :
    (microInputs e leftSym R rate enc N z).foldl
      (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep (embed z.2) =
      embed ((TextFeedPipelineOutputInitial.tick e leftSym R rate enc)^[N] z).2 := by
  induction N generalizing z with
  | zero => rfl
  | succ N ih =>
    rw [microInputs, List.foldl_append, tick_realize, ih, Function.iterate_succ_apply]

theorem microInputs_length (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate N : ℕ)
    (z : List Terminal × View e leftSym R rate) :
    (microInputs e leftSym R rate enc N z).length ≤ 97 * N := by
  have hb (z : List Terminal × View e leftSym R rate) : (block z).length ≤ 97 := by
    unfold block
    split
    · split <;> simp
    · simp
  induction N generalizing z with
  | zero => simp [microInputs]
  | succ N ih =>
    simp only [microInputs, List.length_append]
    have := ih (TextFeedPipelineOutputInitial.tick e leftSym R rate enc z)
    have := hb z
    omega

/-- The realized microsteps consume exactly a prefix of the supplied
input, with no duplicated or invented arrivals. -/
theorem microInputs_consumed (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate N : ℕ)
    (z : List Terminal × View e leftSym R rate) :
    z.1 = (microInputs e leftSym R rate enc N z).filterMap id ++
      ((TextFeedPipelineOutputInitial.tick e leftSym R rate enc)^[N] z).1 := by
  have hb (z : List Terminal × View e leftSym R rate) :
      z.1 = (block z).filterMap id ++ (TextFeedPipelineOutputInitial.tick e leftSym R rate enc z).1 := by
    rcases z with ⟨as, x⟩
    by_cases hz : x.1.1.1.1 = 0
    · cases as <;> simp [block, TextFeedPipelineOutputInitial.tick, hz]
    · simp [block, TextFeedPipelineOutputInitial.tick, hz]
  induction N generalizing z with
  | zero => rfl
  | succ N ih =>
    rw [microInputs, List.filterMap_append, Function.iterate_succ_apply, List.append_assoc, ← ih]
    exact hb z

/-- Startup from the synchronized prefix endpoint is a bounded execution
of the original microstep machine, including the physical observer. -/
theorem boot_microsteps {e : Env k} (hcode : Function.Injective e.code)
    {leftSym : Fin k} {R rate p r n : ℕ} (hR : 0 < R)
    (enc : Terminal → Fin k) {leftPat rightPat Text : List (Fin k)}
    (x : View e leftSym R rate)
    (h : TextFeedPipelinePrefixFedPhysical.Complete e leftSym R rate
      leftPat rightPat Text rate p r n (TextFeedPipelineObserved.project x))
    (hs : TextFeedPipelineSourceSafety.SourceSafe e leftSym rate x.1.1.1.2.2)
    (hz : x.1.1.1.1 ≠ 0) (hfirst : x.1.1.1.2.1 = false)
    (hmb : e.mark ≠ e.blank) (hb : e.blank ∉ Text) (hm : e.mark ∉ Text)
    (hdir : (x.2 38).applyAction e.blank (e.mark, .stay) =
      GSVProgZLoop.dirTape e.blank e.mark true 0)
    (as : List Terminal) (hlen : 3 ≤ as.length) (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a)) :
    ∃ (ops : List (Option Terminal)), ∃ pre post y,
      ∃ a : TextFeedPipelineService.Macro e leftSym R rate Text leftPat rightPat p r
          (n + pre.length) (TextFeedPipelineObserved.project y),
      ops.length ≤ 678 ∧ pre.length ≤ 3 ∧ as = pre ++ post ∧ ops.filterMap id = pre ∧
      ops.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep (embed x) = embed y ∧
      a.z.1.pos = leftPat.length ∧ a.z.1.q = 0 ∧ a.z.2 = ⟨0, 0, 0, true⟩ ∧
      a.events = [] ∧ y.1.1.1.2.1 = false ∧
      ((rate + 1) * (n + 3) ≤ (rate + 1) * leftPat.length + rate * rightPat.length →
        TextFeedPipelineService.target rate rightPat (n + pre.length) ≤ a.score) := by
  obtain ⟨m, pre, post, y, a, hm₁, hp, hsplit, hrun, hpos, hq, hz', hevents, hf, hcredit⟩ :=
    TextFeedPipelineOutputInitial.prefix_boot hcode hR enc x h hs hz hfirst hmb hb hm hdir
      as hlen hn ha
  let x₁ := TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate x
  let ops := List.replicate 96 (none : Option Terminal) ++ microInputs e leftSym R rate enc m (as, x₁)
  have hsize := microInputs_length e leftSym enc R rate m (as, x₁)
  have hinput := microInputs_consumed e leftSym enc R rate m (as, x₁)
  rw [hrun] at hinput
  have hpre : (microInputs e leftSym R rate enc m (as, x₁)).filterMap id = pre :=
    List.append_cancel_right (hinput.symm.trans hsplit)
  refine ⟨ops, pre, post, y, a, ?_, hp, hsplit, ?_, ?_, hpos, hq, hz', hevents, hf, hcredit⟩
  · dsimp only [ops]
    simp only [List.length_append, List.length_replicate]
    omega
  · simpa [ops] using hpre
  · dsimp only [ops]
    rw [List.foldl_append, worker e leftSym enc R rate x hz,
      ticks_realize e leftSym enc R rate m (as, x₁), hrun]

theorem arrival_controls {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {leftSym : Fin k} {R rate d p r n : ℕ} {u v Text : List (Fin k)}
    (enc : Terminal → Fin k) (x : View e leftSym R rate)
    (h : TextFeedPipelinePrefixFedPhysical.Complete e leftSym R rate u v Text d p r n
      (TextFeedPipelineObserved.project x))
    (hs : TextFeedPipelineSourceSafety.SourceSafe e leftSym rate x.1.1.1.2.2)
    (hz : x.1.1.1.1 = 0) (a : Terminal) (ham : enc a ≠ e.mark) :
    let y := opStep e leftSym R rate enc x (some a)
    TextFeedPipelineSourceSafety.SourceSafe e leftSym rate y.1.1.1.2.2 ∧
      y.1.1.1.2.1 = false ∧ y.2 38 = x.2 38 := by
  obtain ⟨z, hl, _, _⟩ := h
  obtain ⟨he, hl'⟩ := TextFeedPipelineOutputPrefix.arrival_step hc hmb enc hl hz a ham
    x.1.2.1 x.1.2.2
  have hsafe := TextFeedPipelineSourceSafety.run_safe (Terminal := Terminal) e leftSym R rate
    (TextFeedPipelineInputRun.captured e leftSym R rate enc a (TextFeedPipelineObserved.project x)) hs
  change TextFeedPipelineObserved.project (opStep e leftSym R rate enc x (some a)) = _ at he
  have hs' : TextFeedPipelineSourceSafety.SourceSafe e leftSym rate
      (opStep e leftSym R rate enc x (some a)).1.1.1.2.2 := by
    change TextFeedPipelineSourceSafety.SourceSafe e leftSym rate
      (TextFeedPipelineObserved.project (opStep e leftSym R rate enc x (some a))).1.1.2.2
    rw [he]
    exact hsafe
  obtain ⟨qt₁, m₁, qt₂, m₂, ht, _⟩ := hl
  obtain ⟨qt₁', m₁', qt₂', m₂', ht', _, hf', _⟩ := hl'
  refine ⟨hs', hf', ?_⟩
  change (opStep e leftSym R rate enc x (some a)).2 = _ at ht'
  change x.2 = _ at ht
  rw [ht', ht]
  rfl

/-- Uniform startup from any synchronized completed-prefix phase. The
extra arrival at phase zero is charged and is part of the actual input. -/
theorem boot_any_phase {e : Env k} (hcode : Function.Injective e.code)
    {leftSym : Fin k} {R rate p r n : ℕ} (hR : 0 < R)
    (enc : Terminal → Fin k) {leftPat rightPat Text : List (Fin k)}
    (x : View e leftSym R rate)
    (h : TextFeedPipelinePrefixFedPhysical.Complete e leftSym R rate
      leftPat rightPat Text rate p r n (TextFeedPipelineObserved.project x))
    (hs : TextFeedPipelineSourceSafety.SourceSafe e leftSym rate x.1.1.1.2.2)
    (hmb : e.mark ≠ e.blank) (hb : e.blank ∉ Text) (hm : e.mark ∉ Text)
    (hdir : (x.2 38).applyAction e.blank (e.mark, .stay) =
      GSVProgZLoop.dirTape e.blank e.mark true 0)
    (as : List Terminal) (hlen : 4 ≤ as.length) (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a))
    (hbudget : (rate + 1) * (n + 4) ≤ (rate + 1) * leftPat.length + rate * rightPat.length) :
    ∃ (ops : List (Option Terminal)), ∃ pre post y,
      ops.length ≤ 775 ∧ pre.length ≤ 4 ∧ as = pre ++ post ∧ ops.filterMap id = pre ∧
      ops.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep (embed x) = embed y ∧
      ∃ a : TextFeedPipelineService.Macro e leftSym R rate Text leftPat rightPat p r
          (n + pre.length) (TextFeedPipelineObserved.project y),
        a.z.1.pos = leftPat.length ∧ a.z.1.q = 0 ∧ a.z.2 = ⟨0, 0, 0, true⟩ ∧
        a.events = [] ∧ TextFeedPipelineService.target rate rightPat (n + pre.length) ≤ a.score ∧
        y.1.1.1.2.1 = false := by
  by_cases hz : x.1.1.1.1 = 0
  · cases as with
    | nil => simp at hlen
    | cons b bs =>
      have hn₁ : n < Text.length := by simp only [List.length_cons] at hn; omega
      have hb₁ : Text[n]? = some (enc b) := by simpa using ha 0 b rfl
      have hbm : enc b ≠ e.mark := fun he => hm (he ▸ List.mem_of_getElem? hb₁)
      let x₁ := opStep e leftSym R rate enc x (some b)
      obtain ⟨hc₁, hp₁, _⟩ := TextFeedPipelineOutputInitial.complete_arrival hcode hmb enc x
        h hz hR b hn₁ hb₁ hbm
      obtain ⟨hs₁, hf₁, hd₁⟩ := arrival_controls hcode hmb enc x h hs hz b hbm
      have hdir₁ : (x₁.2 38).applyAction e.blank (e.mark, .stay) =
          GSVProgZLoop.dirTape e.blank e.mark true 0 := by rw [hd₁]; exact hdir
      have htail : ∀ j c, bs[j]? = some c → Text[n + 1 + j]? = some (enc c) := by
        intro j c hj
        have hh := ha (j + 1) c (by simpa using hj)
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hh
      obtain ⟨ops, pre, post, y, a, hsize, hpre, hsplit, hinput, hrun, hpos, hq, hz', hev, hf, hcredit⟩ :=
        boot_microsteps hcode hR enc x₁ hc₁ hs₁ hp₁ hf₁ hmb hb hm hdir₁ bs
          (by simp only [List.length_cons] at hlen; omega)
          (by simp only [List.length_cons] at hn; omega) htail
      let allOps := (some b :: List.replicate 96 none) ++ ops
      refine ⟨allOps, b :: pre, post, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [allOps, List.length_append, List.length_cons, List.length_replicate]; omega
      · simp only [List.length_cons]; omega
      · simp only [List.cons_append, hsplit]
      · simpa [allOps, List.filterMap_append] using congrArg (List.cons b) hinput
      · dsimp only [allOps]
        rw [List.foldl_append, arrival e leftSym enc R rate x hz b]
        exact hrun
      · have he : n + (b :: pre).length = n + 1 + pre.length := by simp only [List.length_cons]; omega
        rw [he]
        exact ⟨a, hpos, hq, hz', hev, hcredit (by simpa only [Nat.add_assoc] using hbudget), hf⟩
  · have hcopy := h
    obtain ⟨_, ⟨_, _, _, _, _, _, hfirst, _⟩, _, _⟩ := hcopy
    obtain ⟨ops, pre, post, y, a, hsize, hpre, hsplit, hinput, hrun, hpos, hq, hz', hev, hf, hcredit⟩ :=
      boot_microsteps hcode hR enc x h hs hz hfirst hmb hb hm hdir as (by omega) hn ha
    refine ⟨ops, pre, post, y, by omega, by omega, hsplit, hinput, hrun,
      a, hpos, hq, hz', hev, ?_, hf⟩
    apply hcredit
    exact (Nat.mul_le_mul_left (rate + 1) (by omega : n + 3 ≤ n + 4)).trans hbudget

/-- info: 'PalPeg.TextFeedPipelineOutputClock.boot_any_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms boot_any_phase
/-- info: 'PalPeg.TextFeedPipelineOutputClock.arrival_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arrival_controls

/-- info: 'PalPeg.TextFeedPipelineOutputClock.boot_microsteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms boot_microsteps
/-- info: 'PalPeg.TextFeedPipelineOutputClock.microInputs_consumed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms microInputs_consumed
/-- info: 'PalPeg.TextFeedPipelineOutputClock.finishAt_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finishAt_embed
/-- info: 'PalPeg.TextFeedPipelineOutputClock.ticks_realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ticks_realize
end PalPeg.TextFeedPipelineOutputClock
