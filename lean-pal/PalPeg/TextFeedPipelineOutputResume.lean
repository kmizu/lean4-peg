import PalPeg.TextFeedPipelineOutputTrace

/-! The startup-frame suffix is followed by ordinary sRound execution,
without resetting either the reporting bit or the verifier continuation. -/
set_option autoImplicit false
namespace PalPeg.TextFeedPipelineOutputResume
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.TextFeedControl PalPeg.TextFeedPipelineService
open PalPeg.TextFeedPipelineOutputTrace (expand)
open PalPeg.TextFeedPipelinePrefixResume (remaining)
variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (TextFeedPipelineControl.Outer e leftSym R rate) := Classical.decEq _

theorem expand_none (N : ℕ) :
    expand (List.replicate N (none : Option Terminal)) = List.replicate (N * 96) none := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simpa only [expand, List.replicate_succ, List.flatMap_cons, Nat.succ_mul,
      Nat.add_comm (N * 96) 96, List.replicate_add] using congrArg (List.replicate 96 none ++ ·) ih

theorem expand_frame (R : ℕ) (a : Terminal) :
    expand (some a :: List.replicate R none) =
      PalPeg.Speedup.MultiStepMachine.roundInputs ((R + 1) * 96 + 1) a := by
  change (some a :: List.replicate 96 none) ++ expand (List.replicate R none) = _
  rw [expand_none]
  simp only [PalPeg.Speedup.MultiStepMachine.roundInputs, Nat.add_sub_cancel,
    List.cons_append, ← List.replicate_add]
  congr 2
  omega

theorem expand_append (xs ys : List (Option Terminal)) : expand (xs ++ ys) = expand xs ++ expand ys :=
  List.flatMap_append

set_option maxRecDepth 2048 in
theorem schedule_rounds (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (as : List Terminal) (x : TextFeedPipelineOutputPrepFinish.Config e leftSym R rate) :
    (expand (schedule R as)).foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep x =
      as.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound x := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih =>
    change (expand ((some a :: List.replicate R none) ++ schedule R as)).foldl _ x = _
    rw [expand_append, List.foldl_append, expand_frame, ih]
    rfl

theorem pending_run (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate N : ℕ)
    (as : List Terminal) (x : TextFeedPipelineOutputPrepFinish.Config e leftSym R rate) :
    (expand (List.replicate N none ++ schedule R as)).foldl
      (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep x =
    as.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound
      ((List.replicate (N * 96) none).foldl
        (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep x) := by
  rw [expand_append, List.foldl_append, expand_none, schedule_rounds]

theorem phase_no_wrap {B : ℕ} (p : Fin B) (N : ℕ) (h : p.val + N < B) :
    (nextPhase^[N] p).val = p.val + N := by
  induction N generalizing p with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply]
    have hp : p.val + 1 < B := by omega
    have he : (nextPhase p).val = p.val + 1 := by simp only [nextPhase, dif_pos hp]
    rw [ih _ (by rw [he]; omega), he]
    omega

theorem remaining_workers (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : TextFeedPipelineCoupled.Config e leftSym R rate) :
    ∀ j < remaining x,
      ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[j] x).1.1.1 ≠ 0 := by
  intro j hj
  by_cases hz : x.1.1.1 = 0
  · simp only [remaining, hz, ↓reduceIte] at hj
    omega
  · have hp := x.1.1.1.isLt
    have hn : x.1.1.1.val ≠ 0 := fun hh => hz (Fin.ext hh)
    simp only [remaining, if_neg hz] at hj
    intro he
    have hh := congrArg Fin.val he
    rw [TextFeedPipelineControl.run_counter_iterate, phase_no_wrap _ _ (by omega)] at hh
    simp only [Fin.val_zero] at hh
    omega

theorem resumed_iff {e : Env k} (hcode : Function.Injective e.code)
    {leftSym : Fin k} {R rate p r n : ℕ} (enc : Terminal → Fin k)
    {Text u v : List (Fin k)} {x : TextFeedPipelineCoupled.Config e leftSym R rate}
    (a : State e leftSym R rate Text u v p r n x)
    (hc : ∀ z, TextFeedPipelineInputMacro.Conditions e Text u v rate p r z)
    (hK : KSimple v rate p r) (hpat : 0 < v.length) (hd : GSVerifierZ.ZDeadline u v rate p r)
    (as : List Terminal) (hne : as ≠ []) (hn : n + as.length ≤ Text.length)
    (has : ∀ j c, as[j]? = some c → Text[n + j]? = some (enc c))
    (hfirst : x.1.1.2.1 = false)
    (hR : TextFeedPipelineFrontier.progressRate rate * (rate + 1) ≤ R)
    (ha : target rate v n ≤ a.score)
    (hs : TextFeedPipelineOutputSound.Semantic (e := e) (Text := Text) (leftPat := u) (rightPat := v) a.z)
    (hstart : a.z.1.pos = u.length) (ρ : RTQueueTapes.Role) (bit : Bool)
    (actual : TextFeedPipelineOutputPrepFinish.Config e leftSym R rate)
    (hsim : ConfigBlankEq e.blank actual
      (TextFeedPipelineOutputClock.embed (TextFeedPipelineObserved.pack x ρ bit))) :
    (TextFeedPipelineOutput.machine e leftSym enc R rate).accepting
      (as.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound
        ((List.replicate (remaining x * 96) none).foldl
          (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep actual)).state = true ↔
      TextFeedPipelineOutputSound.RawMatches (Text := Text) (leftPat := u) (rightPat := v) (n + as.length) := by
  have hend := (TextFeedPipelinePrefixResume.remaining_window (Terminal := Terminal) x).2.2
  obtain ⟨b, ht, hb⟩ := TextFeedPipelineInitial.pending_frames hcode enc a hc hpat
    (remaining x) as hn has (remaining_workers e leftSym R rate x) hend hfirst hR (by omega)
  have hmore : n < n + as.length := by
    have hl : 0 < as.length := by
      cases as with
      | nil => exact False.elim (hne rfl)
      | cons c cs => exact Nat.zero_lt_succ _
    omega
  have hh := TextFeedPipelineOutputTrace.output_iff ht hcode hc hK hd hn hmore hb hs hstart ρ bit actual hsim
  rwa [pending_run] at hh

theorem initial_semantic (e : Env k) (u v Text : List (Fin k)) (rate p r : ℕ)
    (hd : GSVerifierZ.ZDeadline u v rate p r) (z : GSVerifierZ.VStateZ)
    (hp : z.1.pos = u.length) (hq : z.1.q = 0) (hz : z.2 = ⟨0, 0, 0, true⟩) :
    TextFeedPipelineOutputSound.Semantic (e := e) (Text := Text) (leftPat := u) (rightPat := v) z := by
  have hbound : u.length ≤ GSVerifierZ.zQuota * v.length := by
    have hh := hd 0 (Nat.zero_le _)
    have hle := Nat.mul_le_mul_left GSVerifierZ.zQuota (Nat.sub_le v.length (gsNextQ rate p r 0))
    omega
  constructor
  · change MatchLen v _ z.1.pos z.1.q ∧ z.1.q ≤ v.length
    rw [hq]
    exact ⟨by intro j hj; omega, Nat.zero_le _⟩
  · simp only [GSVerifierZ.ZInv, hp, hq, hz, Nat.sub_zero, Nat.sub_self]
    exact ⟨Nat.le_refl _, by simp [GSVerifierZ.ZWf],
      GSVerifierZ.matchIv_empty _ _ 0 0, fun _ => hbound⟩

/-- Boot's concrete initial position and empty comparison interval supply
the semantic invariant required for all subsequent real input rounds. -/
theorem boot_resumed_iff {e : Env k} (hcode : Function.Injective e.code)
    {leftSym : Fin k} {R rate p r n : ℕ} (enc : Terminal → Fin k)
    {Text u v : List (Fin k)} {x : TextFeedPipelineCoupled.Config e leftSym R rate}
    (a : Macro e leftSym R rate Text u v p r n x)
    (hc : ∀ z, TextFeedPipelineInputMacro.Conditions e Text u v rate p r z)
    (hK : KSimple v rate p r) (hpat : 0 < v.length) (hd : GSVerifierZ.ZDeadline u v rate p r)
    (hp : a.z.1.pos = u.length) (hq : a.z.1.q = 0) (hz : a.z.2 = ⟨0, 0, 0, true⟩)
    (as : List Terminal) (hne : as ≠ []) (hn : n + as.length ≤ Text.length)
    (has : ∀ j c, as[j]? = some c → Text[n + j]? = some (enc c))
    (hfirst : x.1.1.2.1 = false)
    (hR : TextFeedPipelineFrontier.progressRate rate * (rate + 1) ≤ R)
    (ha : target rate v n ≤ a.score) (ρ : RTQueueTapes.Role) (bit : Bool)
    (actual : TextFeedPipelineOutputPrepFinish.Config e leftSym R rate)
    (hsim : ConfigBlankEq e.blank actual
      (TextFeedPipelineOutputClock.embed (TextFeedPipelineObserved.pack x ρ bit))) :
    (TextFeedPipelineOutput.machine e leftSym enc R rate).accepting
      (as.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound
        ((List.replicate (remaining x * 96) none).foldl
          (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep actual)).state = true ↔
      TextFeedPipelineOutputSound.RawMatches (Text := Text) (leftPat := u) (rightPat := v) (n + as.length) :=
  resumed_iff hcode enc (.macro a) hc hK hpat hd as hne hn has hfirst hR ha
    (initial_semantic e u v Text rate p r hd a.z hp hq hz) hp ρ bit actual hsim

/-- info: 'PalPeg.TextFeedPipelineOutputResume.boot_resumed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms boot_resumed_iff
/-- info: 'PalPeg.TextFeedPipelineOutputResume.resumed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resumed_iff
end PalPeg.TextFeedPipelineOutputResume
