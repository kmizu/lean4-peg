import PalPeg.TextFeedPipelineOutputBoot
import PalPeg.TextFeedPipelineOutputSound

/-! Realize service traces in the actual outer microstep machine, including
traces beginning in the middle of an input frame. -/
set_option autoImplicit false
namespace PalPeg.TextFeedPipelineOutputTrace
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.TextFeedControl PalPeg.TextFeedPipelineCoupled
open PalPeg.TextFeedPipelineService
open PalPeg.TextFeedPipelineObserved (pack opRun opStep)
open PalPeg.TextFeedPipelineOutputClock (embed)
variable {k : ℕ} {Terminal : Type} {e : Env k} {leftSym : Fin k} {R rate p r : ℕ}
variable {Text u v : List (Fin k)} {enc : Terminal → Fin k}

noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (TextFeedPipelineControl.Outer e leftSym R rate) := Classical.decEq _

def expand (ops : List (Option Terminal)) : List (Option Terminal) :=
  ops.flatMap (fun a => match a with
    | none => List.replicate 96 none
    | some a => some a :: List.replicate 96 none)

theorem realize {n₀ n₁ : ℕ} {x₀ x₁ : Config e leftSym R rate}
    {a : State e leftSym R rate Text u v p r n₀ x₀}
    {b : State e leftSym R rate Text u v p r n₁ x₁} {ops : List (Option Terminal)}
    (h : Trace e leftSym R rate enc Text u v p r a ops b)
    (hc : Function.Injective e.code) (ρ : RTQueueTapes.Role) (bit : Bool) :
    (expand ops).foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep
      (embed (pack x₀ ρ bit)) = embed (opRun e leftSym R rate enc ops (pack x₀ ρ bit)) := by
  induction h generalizing ρ bit with
  | refl => rfl
  | worker hz he =>
    simpa only [expand, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      opRun, List.foldl_cons, List.foldl_nil, opStep] using
      TextFeedPipelineOutputClock.worker e leftSym enc R rate (pack _ ρ bit) hz
  | arrival c hz he =>
    simpa only [expand, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      opRun, List.foldl_cons, List.foldl_nil] using
      TextFeedPipelineOutputClock.arrival e leftSym enc R rate (pack _ ρ bit) hz c
  | @trans n₀ n₁ n₂ x₀ x₁ x₂ xs ys a b c h h' ih ih' =>
    obtain ⟨ρ₁, bit₁, hr⟩ := TextFeedPipelineObserved.realize h hc ρ bit
    simp only [expand, List.flatMap_append, opRun, List.foldl_append]
    change (expand ys).foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep
      ((expand xs).foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep
        (embed (pack x₀ ρ bit))) =
      embed (opRun e leftSym R rate enc ys (opRun e leftSym R rate enc xs (pack x₀ ρ bit)))
    rw [ih, hr, ih']

theorem expand_inputs (ops : List (Option Terminal)) :
    (expand ops).filterMap id = ops.filterMap id := by
  induction ops with
  | nil => rfl
  | cons a ops ih =>
    cases a <;> simpa [expand] using ih

theorem output_eq {n₀ n₁ : ℕ} {x₀ x₁ : Config e leftSym R rate}
    {a : State e leftSym R rate Text u v p r n₀ x₀}
    {b : State e leftSym R rate Text u v p r n₁ x₁} {ops : List (Option Terminal)}
    (h : Trace e leftSym R rate enc Text u v p r a ops b)
    (hc : Function.Injective e.code) (ρ : RTQueueTapes.Role) (bit : Bool)
    (actual : TextFeedPipelineOutputPrepFinish.Config e leftSym R rate)
    (hsim : ConfigBlankEq e.blank actual (embed (pack x₀ ρ bit))) :
    (TextFeedPipelineOutput.machine e leftSym enc R rate).accepting
      ((expand ops).foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep actual).state =
      (opRun e leftSym R rate enc ops (pack x₀ ρ bit)).1.2.2 := by
  have hh := StructuredMachine.microSteps_blankEq
    (TextFeedPipelineOutput.machine e leftSym enc R rate) (expand ops) hsim
  rw [realize h hc ρ bit] at hh
  exact congrArg (fun q => q.1.1.2.2) hh.1

/-- The physical observer on unpadded tapes decides raw pattern matches
after any positive-input service trace, including a partial-frame start. -/
theorem output_iff {n₀ n₁ : ℕ} {x₀ x₁ : Config e leftSym R rate}
    {a : State e leftSym R rate Text u v p r n₀ x₀}
    {b : State e leftSym R rate Text u v p r n₁ x₁} {ops : List (Option Terminal)}
    (h : Trace e leftSym R rate enc Text u v p r a ops b)
    (hcode : Function.Injective e.code)
    (hc : ∀ z, TextFeedPipelineInputMacro.Conditions e Text u v rate p r z)
    (hK : KSimple v rate p r) (hd : GSVerifierZ.ZDeadline u v rate p r)
    (hn : n₁ ≤ Text.length) (hmore : n₀ < n₁) (hb : target rate v n₁ ≤ b.score)
    (hs : TextFeedPipelineOutputSound.Semantic (e := e) (Text := Text) (leftPat := u) (rightPat := v) a.z)
    (hstart : a.z.1.pos = u.length) (ρ : RTQueueTapes.Role) (bit : Bool)
    (actual : TextFeedPipelineOutputPrepFinish.Config e leftSym R rate)
    (hsim : ConfigBlankEq e.blank actual (embed (pack x₀ ρ bit))) :
    (TextFeedPipelineOutput.machine e leftSym enc R rate).accepting
      ((expand ops).foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep actual).state = true ↔
      TextFeedPipelineOutputSound.RawMatches (Text := Text) (leftPat := u) (rightPat := v) n₁ := by
  rw [output_eq h hcode ρ bit actual hsim]
  exact TextFeedPipelineOutputSound.trace_iff h hcode hc hK hd hn hmore hb hs hstart ρ bit

/-- info: 'PalPeg.TextFeedPipelineOutputTrace.output_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms output_iff
end PalPeg.TextFeedPipelineOutputTrace
