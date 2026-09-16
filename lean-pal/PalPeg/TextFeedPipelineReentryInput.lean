import PalPeg.TextFeedPipelineReentry

/-! Input arrivals may interrupt outer-loop reentry. The actual scheduled
calls preserve the pending phase; every worker call lowers a finite rank. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineReentryInput
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineVerifier
open PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineCoupled PalPeg.TextFeedPipelineInputRun
open PalPeg.TextFeedPipelineSourceSafety PalPeg.TextFeedPipelineReentry
open PalPeg.VerifierFeedSupplyProgress
variable {k : ℕ} {Terminal : Type}

/-- Enqueue preserves all source guards, including the macro's already
selected return. Both physical queues are still updated by the real bank. -/
theorem enqueue {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k) (a : Terminal)
    {Text : List (Fin k)} {n : ℕ} (hm : e.mark ∉ Text) (hn : n < Text.length)
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller) (hz : x.1.1.1 = 0)
    (hfirst : x.1.1.2.1 = false) (ha : Text[n]? = some (enc a)) :
    ∃ v,
      let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
        (captured e leftSym R rate enc a x)
      Valid e leftSym R rate Text (n + 1) y v caller ∧
      v.frames = u.frames ∧ v.ideal = u.ideal ∧ v.dir = u.dir ∧
      taskEval e (fun j => (y.2 j).focus) = taskEval e (fun j => (x.2 j).focus) ∧
      filled u.model ≤ filled v.model := by
  have ham : enc a ≠ e.mark := fun he => hm (he ▸ List.mem_of_getElem? ha)
  have hcap := capture_valid e leftSym R rate enc a x u caller hu
  obtain ⟨q1, m1, q2, m2, ht, hby, hcy, _, h1, h2, hfit⟩ :=
    TextFeedPipelineRefinement.run_arrival (Terminal := Terminal) hc hmb leftSym R rate
      (captured e leftSym R rate enc a x) hcap.boundary hz hfirst
      u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux (enc a) u.dir
      hcap.physical hu.ready1 hu.ready2 ham hn ha hu.refines
  let v : Snapshot k := { u with
    qt1 := q1
    mode1 := m1
    qt2 := q2
    mode2 := m2
    old := enc a
    model := VerifierFeed.varrive' e.blank e.mark (enc a) u.model }
  refine ⟨v, ⟨hby, run_safe e leftSym R rate _ hcap.safe, ?_, ht, h1, h2, hfit⟩,
    rfl, rfl, rfl, ?_, Nat.le_refl _⟩
  · rw [hcy]
    exact hu.control
  · apply TextFeedPipelinePrefixLink.taskEval_eq
    intro j hj
    rw [ht, hu.physical]
    fin_cases j <;> first | rfl | (simp [DualQueueShared.Reserved] at hj)

def caller (rate s : ℕ) : Stack (TaskAct k) (TaskCond k) :=
  match s with
  | 1 => [second rate, verifyLoop rate]
  | 2 => [verifyBody rate, verifyLoop rate]
  | _ => [verifyLoop rate]

/-- Rank 3 is a returned macro, 2 the loop body, 1 the remaining Q2
feed, and 0 the next macro. This describes the existing source stack. -/
def Entry (e : Env k) (leftSym : Fin k) (R rate : ℕ) (Text : List (Fin k)) (n : ℕ)
    (x : Config e leftSym R rate) (u : Snapshot k) (s : ℕ) : Prop :=
  Valid e leftSym R rate Text n x u (caller rate s) ∧
    match s with
    | 0 => u.frames = [.code (GSVProgZLoop.stepProg rate)]
    | 1 | 2 => u.frames = []
    | 3 => (next (taskEval e (fun j => (x.2 j).focus)) u.frames).2 = .halt
    | _ => False

theorem Entry.worker {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) {Text : List (Fin k)} {n s : ℕ}
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (x : Config e leftSym R rate) (u : Snapshot k)
    (h : Entry e leftSym R rate Text n x u s) (hpos : 0 < s) (hs : s ≤ 3)
    (hz : x.1.1.1 ≠ 0) :
    ∃ t v, t < s ∧ Entry e leftSym R rate Text n
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) v t ∧
      v.ideal = u.ideal ∧ v.dir = u.dir ∧ filled u.model ≤ filled v.model := by
  interval_cases s
  · obtain ⟨v, hv, hf, hi, hd, hmono⟩ := second_feed hc hmb leftSym R rate hb hm hn x u h.1 h.2 hz
    exact ⟨0, v, by omega, ⟨hv, hf⟩, hi, hd, hmono⟩
  · obtain ⟨v, hi, hd, hv, hmono⟩ := body_feed hc hmb leftSym R rate hb hm hn x u h.1 h.2 hz
    rcases hv with hv | hv
    · exact ⟨1, v, by omega, hv, hi, hd, hmono⟩
    · exact ⟨0, v, by omega, hv, hi, hd, hmono⟩
  · obtain ⟨v, hv, hf, hmodel, hi, hd⟩ := return_idle hc hmb leftSym R rate x u h.1 hz h.2
    exact ⟨2, v, by omega, ⟨hv, hf⟩, hi, hd, by rw [hmodel]⟩

theorem Entry.arrival {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k) (a : Terminal)
    {Text : List (Fin k)} {n s : ℕ} (hm : e.mark ∉ Text) (hn : n < Text.length)
    (x : Config e leftSym R rate) (u : Snapshot k)
    (h : Entry e leftSym R rate Text n x u s) (hs : s ≤ 3) (hz : x.1.1.1 = 0)
    (hfirst : x.1.1.2.1 = false) (ha : Text[n]? = some (enc a)) :
    ∃ v, Entry e leftSym R rate Text (n + 1)
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
        (captured e leftSym R rate enc a x)) v s ∧ v.ideal = u.ideal ∧ v.dir = u.dir ∧
      filled u.model ≤ filled v.model := by
  obtain ⟨v, hv, hf, hi, hd, heval, hmono⟩ := enqueue hc hmb leftSym R rate enc a hm hn
    x u (caller rate s) h.1 hz hfirst ha
  refine ⟨v, ⟨hv, ?_⟩, hi, hd, hmono⟩
  interval_cases s
  · exact hf.trans h.2
  · exact hf.trans h.2
  · exact hf.trans h.2
  · change (next (taskEval e _) v.frames).2 = .halt
    rw [heval, hf]
    exact h.2

/-- A microstep of the existing input schedule: consume the next input
only at phase zero, otherwise run the pending worker. No phase is reset. -/
noncomputable def tick (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (z : List Terminal × Config e leftSym R rate) : List Terminal × Config e leftSym R rate :=
  if z.2.1.1.1 = 0 then
    match z.1 with
    | [] => z
    | a :: as => (as, TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
        (captured e leftSym R rate enc a z.2))
  else (z.1, TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate z.2)

theorem tick_worker (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (as : List Terminal) (x : Config e leftSym R rate) (hz : x.1.1.1 ≠ 0) :
    tick e leftSym R rate enc (as, x) =
      (as, TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) := by
  simp only [tick, if_neg hz]

theorem tick_arrival (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (a : Terminal) (as : List Terminal) (x : Config e leftSym R rate) (hz : x.1.1.1 = 0) :
    tick e leftSym R rate enc (a :: as, x) =
      (as, TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
        (captured e leftSym R rate enc a x)) := by
  simp only [tick, if_pos hz]

theorem after_arrival (e : Env k) (leftSym : Fin k) (R rate : ℕ) (hR : 0 < R)
    (enc : Terminal → Fin k) (a : Terminal) (x : Config e leftSym R rate) (hz : x.1.1.1 = 0) :
    (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
      (captured e leftSym R rate enc a x)).1.1.1 ≠ 0 := by
  rw [run_counter]
  change nextPhase x.1.1.1 ≠ 0
  rw [hz]
  simp [nextPhase, show 1 < R + 1 by omega]

theorem tick_workers (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (N : ℕ) (as : List Terminal) (x : Config e leftSym R rate)
    (hz : ∀ j < N,
      ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[j] x).1.1.1 ≠ 0) :
    (tick e leftSym R rate enc)^[N] (as, x) =
      (as, (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] x) := by
  induction N generalizing x with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply, tick_worker e leftSym R rate enc as x (hz 0 (by omega))]
    rw [ih]
    · rw [Function.iterate_succ_apply]
    · intro j hj
      simpa only [Function.iterate_succ_apply] using hz (j + 1) (by omega)

/-- The microstep schedule is exactly the already-defined real input
frame, not an alternative execution semantics. -/
theorem tick_frame (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (a : Terminal) (as : List Terminal) (x : Config e leftSym R rate) (hz : x.1.1.1 = 0) :
    (tick e leftSym R rate enc)^[R + 1] (a :: as, x) =
      (as, frame e leftSym R rate enc a x) := by
  rw [Function.iterate_succ_apply, tick_arrival e leftSym R rate enc a as x hz]
  rw [tick_workers]
  · rfl
  · intro j hj heq
    have he := run_enqueues_once (Terminal := Terminal) e leftSym R rate (j + 1) (by omega)
      (captured e leftSym R rate enc a x) hz
    simp only [Function.iterate_succ_apply, choose_enqueues, heq] at he
    simp at he

/-- Reentry completes after at most twice its remaining rank in actual
scheduled calls, consuming at most that many input symbols. The available
symbols must really be the next symbols of the same finite word. -/
theorem finish {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (hR : 0 < R) (enc : Terminal → Fin k)
    {Text : List (Fin k)} (hb : e.blank ∉ Text) (hm : e.mark ∉ Text)
    (s n : ℕ) (as : List Terminal) (hs : s ≤ 3) (hlen : s ≤ as.length)
    (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a))
    (x : Config e leftSym R rate) (u : Snapshot k)
    (hu : Entry e leftSym R rate Text n x u s) (hfirst : x.1.1.2.1 = false) :
    ∃ m pre post y v, m ≤ 2 * s ∧ pre.length ≤ s ∧ as = pre ++ post ∧
      (tick e leftSym R rate enc)^[m] (as, x) = (post, y) ∧
      Entry e leftSym R rate Text (n + pre.length) y v 0 ∧ v.ideal = u.ideal ∧ v.dir = u.dir ∧
      filled u.model ≤ filled v.model := by
  induction s using Nat.strong_induction_on generalizing n as x u with
  | h s ih =>
    by_cases hs0 : s = 0
    · subst s
      exact ⟨0, [], as, x, u, by omega, by simp, rfl, rfl, hu, rfl, rfl, Nat.le_refl _⟩
    · by_cases hz : x.1.1.1 = 0
      · cases as with
        | nil => simp only [List.length_nil] at hlen; omega
        | cons a as =>
          have hn' : n < Text.length := by simp only [List.length_cons] at hn; omega
          have ha0 : Text[n]? = some (enc a) := by simpa using ha 0 a rfl
          obtain ⟨v₁, hv₁, hi₁, hd₁, hmono₁⟩ := hu.arrival hc hmb leftSym R rate enc a hm hn'
            x u hs hz hfirst ha0
          let x₁ := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
            (captured e leftSym R rate enc a x)
          have hphase : x₁.1.1.1 ≠ 0 := after_arrival e leftSym R rate hR enc a x hz
          obtain ⟨t, v₂, hts, hv₂, hi₂, hd₂, hmono₂⟩ := hv₁.worker hc hmb leftSym R rate hb hm
            (by omega) x₁ v₁ (by omega) hs hphase
          let x₂ := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x₁
          have hfirst₁ : x₁.1.1.2.1 = false := run_not_first leftSym R rate _ hfirst
          have hfirst₂ : x₂.1.1.2.1 = false := run_not_first leftSym R rate _ hfirst₁
          have htail : ∀ j b, as[j]? = some b → Text[(n + 1) + j]? = some (enc b) := by
            intro j b hj
            have hh := ha (j + 1) b (by simpa using hj)
            simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hh
          obtain ⟨m, pre, post, y, v, hmc, hpc, hsplit, hrun, hv, hi, hd, hmono⟩ :=
            ih t hts (n + 1) as (by omega) (by simp only [List.length_cons] at hlen; omega)
              (by simp only [List.length_cons] at hn; omega) htail x₂ v₂ hv₂ hfirst₂
          have htwo : (tick e leftSym R rate enc)^[2] (a :: as, x) = (as, x₂) := by
            rw [Function.iterate_succ_apply', Function.iterate_one,
              tick_arrival e leftSym R rate enc a as x hz,
              tick_worker e leftSym R rate enc as x₁ hphase]
          refine ⟨m + 2, a :: pre, post, y, v, by omega, ?_, ?_, ?_, ?_,
            hi.trans (hi₂.trans hi₁), hd.trans (hd₂.trans hd₁), hmono₁.trans (hmono₂.trans hmono)⟩
          · simp only [List.length_cons]; omega
          · simp only [List.cons_append, hsplit]
          · rw [Function.iterate_add_apply, htwo]
            exact hrun
          · convert hv using 1
            simp only [List.length_cons]
            omega
      · obtain ⟨t, v₁, hts, hv₁, hi₁, hd₁, hmono₁⟩ := hu.worker hc hmb leftSym R rate hb hm
          (by omega) x u (by omega) hs hz
        let x₁ := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
        obtain ⟨m, pre, post, y, v, hmc, hpc, hsplit, hrun, hv, hi, hd, hmono⟩ :=
          ih t hts n as (by omega) (by omega) hn ha x₁ v₁ hv₁
            (run_not_first leftSym R rate x hfirst)
        refine ⟨m + 1, pre, post, y, v, by omega, by omega, hsplit, ?_, hv,
          hi.trans hi₁, hd.trans hd₁, hmono₁.trans hmono⟩
        rw [Function.iterate_succ_apply, tick_worker e leftSym R rate enc as x hz]
        exact hrun

/-- info: 'PalPeg.TextFeedPipelineReentryInput.finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finish

/-- info: 'PalPeg.TextFeedPipelineReentryInput.tick_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tick_frame

theorem tick_first (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (z : List Terminal × Config e leftSym R rate) (hf : z.2.1.1.2.1 = false) :
    (tick e leftSym R rate enc z).2.1.1.2.1 = false := by
  rcases z with ⟨as, x⟩
  by_cases hz : x.1.1.1 = 0
  · cases as with
    | nil => simpa only [tick, if_pos hz] using hf
    | cons a as =>
      rw [tick_arrival e leftSym R rate enc a as x hz]
      exact run_not_first leftSym R rate _ hf
  · rw [tick_worker e leftSym R rate enc as x hz]
    exact run_not_first leftSym R rate x hf

theorem ticks_first (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (m : ℕ) (z : List Terminal × Config e leftSym R rate) (hf : z.2.1.1.2.1 = false) :
    ((tick e leftSym R rate enc)^[m] z).2.1.1.2.1 = false := by
  induction m generalizing z with
  | zero => exact hf
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ (tick_first e leftSym R rate enc z hf)

/-- Actual outer-loop reentry, including intervening arrivals, establishes
the complete next-macro invariant in at most six bank calls. -/
theorem reenter_macro {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (hR : 0 < R) (enc : Terminal → Fin k)
    {Text leftPat rightPat : List (Fin k)} {n p r : ℕ} {z : GSVerifierZ.VStateZ}
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text)
    (as : List Terminal) (hlen : 3 ≤ as.length) (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a))
    (x : Config e leftSym R rate) (u : Snapshot k)
    (hu : Valid e leftSym R rate Text n x u [verifyLoop rate])
    (hfeed : VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
      leftPat rightPat Text rate p r n u.model)
    (hghost : u.model.z = (z.1, z.2.head)) (hwf : GSVerifierZ.ZWf leftPat.length z.2)
    (hdir : u.dir = GSVProgZLoop.dirTape e.blank e.mark z.2.up 0)
    (hh : (next (taskEval e (fun j => (x.2 j).focus)) u.frames).2 = .halt)
    (hfirst : x.1.1.2.1 = false) :
    ∃ m pre post y v, m ≤ 6 ∧ pre.length ≤ 3 ∧ as = pre ++ post ∧
      (tick e leftSym R rate enc)^[m] (as, x) = (post, y) ∧
      Valid e leftSym R rate Text (n + pre.length) y v [verifyLoop rate] ∧
      TextFeedPipelineInputMacro.Start e Text leftPat rightPat rate p r (n + pre.length) v z ∧
      y.1.1.2.1 = false ∧ filled u.model ≤ filled v.model := by
  obtain ⟨m, pre, post, y, v, hm6, hp3, hsplit, hrun, hv, hi, hd, hmono⟩ :=
    finish hc hmb leftSym R rate hR enc hb hm 3 n as (by omega) hlen hn ha x u ⟨hu, hh⟩ hfirst
  obtain ⟨hv', hs⟩ := restart hu hfeed hghost hwf hdir hv.1 hv.2 hi hd
  have hf := ticks_first e leftSym R rate enc m (as, x) hfirst
  rw [hrun] at hf
  exact ⟨m, pre, post, y, TextFeedPipelineMacroBoundary.annotate v z, hm6, hp3,
    hsplit, hrun, hv', hs, hf, hmono⟩

/-- info: 'PalPeg.TextFeedPipelineReentryInput.reenter_macro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reenter_macro

/-- A restored return certificate is directly reusable: callers do not
need to postulate a fresh halt, ghost update, or control initialization. -/
theorem restored_reenter {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (hR : 0 < R) (enc : Terminal → Fin k)
    {Text leftPat rightPat : List (Fin k)} {n p r : ℕ} {z : GSVerifierZ.VStateZ}
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text)
    (as : List Terminal) (hlen : 3 ≤ as.length) (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a))
    (x : Config e leftSym R rate) (u : Snapshot k)
    (hu : TextFeedPipelineInputMacro.Restored e leftSym R rate Text leftPat rightPat
      p r n x u [verifyLoop rate] z)
    (hfirst : x.1.1.2.1 = false) :
    ∃ m pre post y v, m ≤ 6 ∧ pre.length ≤ 3 ∧ as = pre ++ post ∧
      (tick e leftSym R rate enc)^[m] (as, x) = (post, y) ∧
      Valid e leftSym R rate Text (n + pre.length) y v [verifyLoop rate] ∧
      TextFeedPipelineInputMacro.Start e Text leftPat rightPat rate p r (n + pre.length) v z ∧
      y.1.1.2.1 = false ∧ filled u.model ≤ filled v.model := by
  obtain ⟨hh, hv, hfeed, hwf, hdir, hghost⟩ := hu
  exact reenter_macro hc hmb leftSym R rate hR enc hb hm as hlen hn ha x
    (TextFeedPipelineMacroBoundary.annotate u z) hv hfeed hghost hwf hdir hh hfirst

/-- info: 'PalPeg.TextFeedPipelineReentryInput.restored_reenter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms restored_reenter

end PalPeg.TextFeedPipelineReentryInput
