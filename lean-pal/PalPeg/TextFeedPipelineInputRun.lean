import PalPeg.TextFeedPipelineIdealEngine

/-! Input capture and enqueue are stuttering steps of the verifier. A
worker segment after them stops only at its frame budget or macro return. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineInputRun
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.ProgLangPersist PalPeg.ProgLangPersist2
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineCoupled
variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

noncomputable def captured (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (a : Terminal) (x : Config e leftSym R rate) : Config e leftSym R rate :=
  (x.1, arriveA e.blank (DualQueueShared.capture enc) (some a) x.2)

noncomputable def frame (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (a : Terminal) (x : Config e leftSym R rate) : Config e leftSym R rate :=
  (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[R + 1]
    (captured e leftSym R rate enc a x)

theorem frame_round (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (a : Terminal) (x : Config e leftSym R rate) :
    (machine e leftSym enc R rate).sRound { state := ((x.1, 0), 0), tape := x.2 } a =
      { state := (((frame e leftSym R rate enc a x).1, 0), 0),
        tape := (frame e leftSym R rate enc a x).2 } :=
  machine_round e leftSym enc R rate x.1 x.2 a

theorem frame_clock {e : Env k} (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (a : Terminal) (x : Config e leftSym R rate) (hz : x.1.1.1 = 0) :
    (frame e leftSym R rate enc a x).1.1.1 = 0 := by
  unfold frame
  rw [run_counter_iterate]
  change nextPhase^[R + 1] x.1.1.1 = 0
  rw [hz]
  exact nextPhase_iterate_round (Nat.zero_lt_succ R)

theorem run_not_first {e : Env k} (leftSym : Fin k) (R rate : ℕ)
    (x : Config e leftSym R rate) (hf : x.1.1.2.1 = false) :
    (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x).1.1.2.1 = false := by
  change (TextFeedPipelineControl.choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).1.2.1 = false
  unfold TextFeedPipelineControl.choose
  split <;> simp_all

theorem frame_not_first {e : Env k} (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (a : Terminal) (x : Config e leftSym R rate) (hf : x.1.1.2.1 = false) :
    (frame e leftSym R rate enc a x).1.1.2.1 = false := by
  have hall : ∀ N (y : Config e leftSym R rate), y.1.1.2.1 = false →
      ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] y).1.1.2.1 = false := by
    intro N
    induction N with
    | zero => intro y hy; exact hy
    | succ N ih =>
      intro y hy
      rw [Function.iterate_succ_apply]
      exact ih _ (run_not_first leftSym R rate y hy)
  exact hall _ _ hf

theorem capture_enqueue {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k) (a : Terminal)
    {Text : List (Fin k)} {n : ℕ} (hm : e.mark ∉ Text) (hn : n < Text.length)
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller) (hz : x.1.1.1 = 0)
    (hfirst : x.1.1.2.1 = false) (ha : Text[n]? = some (enc a)) :
    ∃ v, Valid e leftSym R rate Text (n + 1)
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
        (captured e leftSym R rate enc a x)) v caller ∧ Follows e u [] v ∧
        v.model.m1 = u.model.m1 ∧ v.model.m2 = u.model.m2 ∧
        v.frames = u.frames ∧ v.model.vt = u.model.vt := by
  have hu' := capture_valid e leftSym R rate enc a x u caller hu
  obtain ⟨v, hv, hf, hi, hd, h1, h2, hvt⟩ := arrival_step (Terminal := Terminal) hc hmb leftSym R rate hm hn
    (captured e leftSym R rate enc a x) { u with old := enc a } caller hu' hz hfirst ha
  exact ⟨v, hv, .stutter hf hi hd (.nil v), h1, h2, hf, hvt⟩

theorem arrival_worker {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k) (a : Terminal)
    {Text : List (Fin k)} {n : ℕ} (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n < Text.length)
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller) (hz : x.1.1.1 = 0)
    (hfirst : x.1.1.2.1 = false) (ha : Text[n]? = some (enc a)) :
    ∃ m v ws, m ≤ R ∧ ws.length = m ∧
      let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m + 1]
        (captured e leftSym R rate enc a x)
      Valid e leftSym R rate Text (n + 1) y v caller ∧ Follows e u ws v ∧
      (m = R ∨ (next (taskEval e (fun j => (y.2 j).focus)) v.frames).2 = .halt) := by
  obtain ⟨v, hv, had, _, _⟩ := capture_enqueue hc hmb leftSym R rate enc a hm hn x u caller hu hz hfirst ha
  obtain ⟨m, z, ws, hmR, hlen, hzv, hfollow, hstop⟩ := worker_prefix (Terminal := Terminal)
    hc hmb leftSym R rate hb hm (Nat.succ_le_of_lt hn) R
    (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
      (captured e leftSym R rate enc a x)) v caller hv
  refine ⟨m, z, ws, hmR, hlen, ?_, had.trans hfollow, ?_⟩
  · simpa only [Function.iterate_succ_apply] using hzv
  · rcases hstop with hfull | hclock | hhalt
    · exact Or.inl hfull
    · by_cases hfull : m = R
      · exact Or.inl hfull
      · have hm1 : m + 1 < R + 1 := by omega
        have he := run_enqueues_once (Terminal := Terminal) e leftSym R rate (m + 1) hm1
          (captured e leftSym R rate enc a x) hz
        simp only [Function.iterate_succ_apply, choose_enqueues, hclock] at he
        simp at he
    · exact Or.inr (by simpa only [Function.iterate_succ_apply] using hhalt)

/-- A frame is either complete, or has an actual macro return at a strict
prefix. A clock boundary alone cannot cause premature termination. -/
theorem frame_or_return {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k) (a : Terminal)
    {Text : List (Fin k)} {n : ℕ} (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n < Text.length)
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller) (hz : x.1.1.1 = 0)
    (hfirst : x.1.1.2.1 = false) (ha : Text[n]? = some (enc a)) :
    (∃ v ws, Valid e leftSym R rate Text (n + 1) (frame e leftSym R rate enc a x) v caller ∧
      Follows e u ws v ∧ ws.length = R) ∨
    (∃ m v ws, m < R ∧ ws.length = m ∧
      let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m + 1]
        (captured e leftSym R rate enc a x)
      Valid e leftSym R rate Text (n + 1) y v caller ∧ Follows e u ws v ∧
      (next (taskEval e (fun j => (y.2 j).focus)) v.frames).2 = .halt) := by
  obtain ⟨m, v, ws, hmR, hlen, hv, hfollow, hstop⟩ :=
    arrival_worker hc hmb leftSym R rate enc a hb hm hn x u caller hu hz hfirst ha
  by_cases hmfull : m = R
  · rw [hmfull] at hv hlen
    exact Or.inl ⟨v, ws, hv, hfollow, hlen⟩
  · exact Or.inr ⟨m, v, ws, by omega, hlen, hv, hfollow, hstop.resolve_left hmfull⟩

/-- info: 'PalPeg.TextFeedPipelineInputRun.frame_or_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frame_or_return

/-- info: 'PalPeg.TextFeedPipelineInputRun.arrival_worker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arrival_worker

noncomputable def frames (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (as : List Terminal) (x : Config e leftSym R rate) : Config e leftSym R rate :=
  as.foldl (fun y a => frame e leftSym R rate enc a y) x

def ReturnsIn (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (Text : List (Fin k)) (n : ℕ) (as : List Terminal)
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k)) : Prop :=
  ∃ pre a post m v ws, as = pre ++ a :: post ∧ m < R ∧ ws.length = R * pre.length + m ∧
    let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m + 1]
      (captured e leftSym R rate enc a (frames e leftSym R rate enc pre x))
    Valid e leftSym R rate Text (n + pre.length + 1) y v caller ∧ Follows e u ws v ∧
    (next (taskEval e (fun j => (y.2 j).focus)) v.frames).2 = .halt

/-- Any finite actual input prefix either completes all its rounds, or
contains an explicitly located macro return. Arrivals are absent only
from the GS event count, never from the physical run. -/
theorem frames_or_return {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    {Text : List (Fin k)} (hb : e.blank ∉ Text) (hm : e.mark ∉ Text)
    (as : List Terminal) {n : ℕ} (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a))
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller) (hz : x.1.1.1 = 0)
    (hfirst : x.1.1.2.1 = false) :
    (∃ v ws, Valid e leftSym R rate Text (n + as.length)
      (frames e leftSym R rate enc as x) v caller ∧ Follows e u ws v ∧ ws.length = R * as.length) ∨
    ReturnsIn e leftSym R rate enc Text n as x u caller := by
  induction as generalizing n x u with
  | nil => exact Or.inl ⟨u, [], hu, .nil u, by simp⟩
  | cons a as ih =>
    have hn' : n < Text.length := by simp only [List.length_cons] at hn; omega
    have ha0 : Text[n]? = some (enc a) := by simpa using ha 0 a rfl
    rcases frame_or_return hc hmb leftSym R rate enc a hb hm hn' x u caller hu hz hfirst ha0 with hfull | hret
    · obtain ⟨v, ws, hv, hfollow, hlen⟩ := hfull
      have hnt : n + 1 + as.length ≤ Text.length := by simp only [List.length_cons] at hn; omega
      have hat : ∀ j b, as[j]? = some b → Text[n + 1 + j]? = some (enc b) := by
        intro j b hj
        have he := ha (j + 1) b (by simpa using hj)
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using he
      rcases ih hnt hat (frame e leftSym R rate enc a x) v hv
        (frame_clock leftSym R rate enc a x hz) (frame_not_first leftSym R rate enc a x hfirst) with hall | hret
      · obtain ⟨z, ts, hzv, ht, hts⟩ := hall
        refine Or.inl ⟨z, ws ++ ts, ?_, hfollow.trans ht, ?_⟩
        · simpa only [frames, List.foldl_cons, List.length_cons, Nat.add_assoc, Nat.add_comm 1 as.length] using hzv
        · simp only [List.length_append, hlen, hts, List.length_cons, Nat.mul_add, Nat.mul_one]
          omega
      · obtain ⟨pre, b, post, m, z, ts, hsplit, hmR, hts, hzv, ht, hhalt⟩ := hret
        refine Or.inr ⟨a :: pre, b, post, m, z, ws ++ ts, ?_, hmR, ?_, ?_, hfollow.trans ht, ?_⟩
        · simp only [List.cons_append, hsplit]
        · simp only [List.length_append, hlen, hts, List.length_cons, Nat.mul_add, Nat.mul_one]
          omega
        · simpa only [frames, List.foldl_cons, List.length_cons, Nat.add_assoc, Nat.add_comm 1 pre.length] using hzv
        · exact hhalt
    · obtain ⟨m, v, ws, hmR, hlen, hv, hfollow, hhalt⟩ := hret
      exact Or.inr ⟨[], a, as, m, v, ws, rfl, hmR, by simpa using hlen, hv, hfollow, hhalt⟩

/-- info: 'PalPeg.TextFeedPipelineInputRun.frames_or_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frames_or_return

end PalPeg.TextFeedPipelineInputRun
