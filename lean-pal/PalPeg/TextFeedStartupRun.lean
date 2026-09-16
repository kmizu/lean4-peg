import PalPeg.TextFeedStartupSafety

/-! The bounded low-call contracts hold for the actual startup scheduler.
Every future real arrival finishes its queue update before the next arrival,
even while the finite preparation continuation is still active. -/
set_option autoImplicit false

namespace PalPeg.TextFeedStartupRun
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.ProgLangPersist2
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedPrepare
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule PalPeg.TextFeedStartupSafety

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

def normalAllowed (e : Env k) : TextFeedStartupBank.Label k → Prop
  | .first _ => False
  | .feed a => TextFeedAtomic.allowed e.mark a
  | .prep _ => True

theorem task_allowed (e : Env k) (a : TaskAct k) : normalAllowed e (taskLabel a) := by
  rcases a with a | a
  · trivial
  · exact TextFeedSchedule.worker_allowed e.mark a

theorem choose_allowed (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (c : Outer e leftSym R rate) (σ : Fin 27 → Fin k)
    (hf : c.2.1 = false) (ha : σ inputSlot ≠ e.mark) :
    normalAllowed e (decode (choose e leftSym R rate c σ).2) := by
  by_cases hc : c.1 = ⟨0, Nat.zero_lt_succ R⟩
  · rw [TextFeedStartupSchedule.choose, if_pos hc]
    simpa only [hf, Bool.false_eq_true, ↓reduceIte, decode_encode, normalAllowed,
      TextFeedAtomic.allowed] using ha
  · rw [TextFeedStartupSchedule.choose, if_neg hc, decode_encode]
    exact task_allowed e _

theorem choose_false (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (c : Outer e leftSym R rate) (σ : Fin 27 → Fin k) (hf : c.2.1 = false) :
    (choose e leftSym R rate c σ).1.2.1 = false := by
  by_cases hc : c.1 = ⟨0, Nat.zero_lt_succ R⟩
  · rw [TextFeedStartupSchedule.choose, if_pos hc]
  · rw [TextFeedStartupSchedule.choose, if_neg hc]
    exact hf

theorem ready_input {e : Env k} {T : Fin 27 → STape (Fin k)} {q : Queue (Fin k)}
    {old : Fin k} (h : ReadyAt e T q old) : (T inputSlot).focus = old := by
  obtain ⟨qt, m, S, hv, _⟩ := h
  have hi := congrFun hv inputIdx
  exact (congrArg STape.focus hi).trans (TextFeedSchedule.input_focus e qt m S old)

attribute [local irreducible] ProgLangBank.runChunk

/-- The initial call constructs its own Ready queue from blank private
tapes and stores the very first symbol. The task continuation is untouched. -/
theorem run_first {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hf : x.1.1.2.1 = true)
    (hc0 : x.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩) (S : Stage k) (old : Fin k)
    (hx : feedView x.2 = TextFeedInit.unprepared e S old) (ha : old ≠ e.mark) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    ReadyAt e y.2 (snoc empty old) old ∧ AtBoundary (programs e) y.1.2.2.1 ∧
      y.1.1.2.1 = false ∧ y.1.1.2.2 = x.1.1.2.2 := by
  have hi : (x.2 inputSlot).focus = old :=
    congrArg STape.focus (congrFun hx inputIdx)
  have hsel : decode (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2 =
      .first old := by
    rw [TextFeedStartupSchedule.choose, if_pos hc0]
    simp only [hf, ↓reduceIte, decode_encode, hi]
  obtain ⟨tr, qt', m', he, hn, ht, hr⟩ := first_exec (Terminal := Terminal) hc hmb S old old ha x.2
  have hs : extend feedSlot (TextFeedInit.unprepared e S old) x.2 = x.2 := by
    rw [← hx]
    exact extend_restrict feedSlot x.2
  rw [hs] at he ht
  have hex : Exec (TextFeedStartupSchedule.interp (Terminal := Terminal) e).toInterp e.blank
      (programs e (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2) x.2 tr := by
    change Exec (shared e) e.blank (low e (decode _)) x.2 tr
    rw [hsel]
    exact he
  obtain ⟨hyt, hby, _, _⟩ := callRun_exec (programs e)
    (fun _ => TextFeedStartupSchedule.interp (Terminal := Terminal) e)
    (choose e leftSym R rate) 48 e.blank x hb tr hex (by omega)
  refine ⟨?_, hby, ?_, ?_⟩
  · change ReadyAt e (callRun _ _ _ _ _ x).2 _ _
    rw [hyt, ht]
    exact ready_feed hr S old x.2
  · simp only [TextFeedStartupSchedule.run, callRun, TextFeedStartupSchedule.choose, if_pos hc0]
  · simp only [TextFeedStartupSchedule.run, callRun, TextFeedStartupSchedule.choose, if_pos hc0]

/-- No bootstrap is selected after the first input. Every call finishes,
has its exact FIFO effect, and preserves the input register. -/
theorem run_ready {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hf : x.1.1.2.1 = false)
    {q : Queue (Fin k)} {old : Fin k} (h : ReadyAt e x.2 q old) (ha : old ≠ e.mark) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    ReadyAt e y.2
      (queueEffect e (decode (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2) q) old ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.1 = false := by
  have hi : (x.2 inputSlot).focus ≠ e.mark := (ready_input h) ▸ ha
  have hal := choose_allowed e leftSym R rate x.1.1 (fun j => (x.2 j).focus) hf hi
  obtain ⟨tr, he, hn, hr⟩ := normal_bounded (Terminal := Terminal) hc hmb h _ hal
  have hex : Exec (TextFeedStartupSchedule.interp (Terminal := Terminal) e).toInterp e.blank
      (programs e (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2) x.2 tr := he
  obtain ⟨ht, hb', _, _⟩ := callRun_exec (programs e)
    (fun _ => TextFeedStartupSchedule.interp (Terminal := Terminal) e)
    (choose e leftSym R rate) 48 e.blank x hb tr hex (by omega)
  exact ⟨ht ▸ hr, hb', choose_false e leftSym R rate _ _ hf⟩

theorem run_ready_iterate {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate N : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hf : x.1.1.2.1 = false)
    {q : Queue (Fin k)} {old : Fin k} (h : ReadyAt e x.2 q old) (ha : old ≠ e.mark) :
    let y := (run (Terminal := Terminal) e leftSym R rate)^[N] x
    ∃ q', ReadyAt e y.2 q' old ∧ AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.1 = false := by
  induction N with
  | zero => exact ⟨q, h, hb, hf⟩
  | succ N ih =>
    obtain ⟨q', hr, hb', hf'⟩ := ih
    rw [Function.iterate_succ_apply']
    exact ⟨_, run_ready hc hmb leftSym R rate _ hb' hf' hr ha⟩

theorem capture_view (blank : Fin k) (enc : Terminal → Fin k) (a : Terminal)
    (T : Fin 27 → STape (Fin k)) :
    feedView (arriveA blank (TextFeedStartupSchedule.capture enc) (some a) T) =
      arriveA blank (TextFeedInput.capture enc) (some a) (feedView T) := by
  funext j
  fin_cases j <;> rfl

theorem capture_ready {e : Env k} (enc : Terminal → Fin k) (a : Terminal)
    {T : Fin 27 → STape (Fin k)} {q : Queue (Fin k)} {old : Fin k}
    (h : ReadyAt e T q old) :
    ReadyAt e (arriveA e.blank (TextFeedStartupSchedule.capture enc) (some a) T) q (enc a) := by
  obtain ⟨qt, m, S, hv, hr⟩ := h
  refine ⟨qt, m, S, ?_, hr⟩
  rw [capture_view, hv, TextFeedInput.capture_some]

/-- Real-input frames preserve queue safety and return to the enqueue
phase, whether the task is in preprocessing or scanning. -/
theorem machine_round_ready {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (c : CallCtrl (programs e) (Outer e leftSym R rate))
    (hb : AtBoundary (programs e) c.2.2.1) (hf : c.1.2.1 = false)
    (hc0 : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    {T : Fin 27 → STape (Fin k)} {q : Queue (Fin k)} {old : Fin k}
    (h : ReadyAt e T q old) (a : Terminal) (ha : enc a ≠ e.mark) :
    let z := (machine e leftSym enc R rate).sRound
      { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T } a
    ∃ q', ReadyAt e z.tape q' (enc a) ∧ AtBoundary (programs e) z.state.1.1.2.2.1 ∧
      z.state.1.1.1.2.1 = false ∧ z.state.1.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩ := by
  dsimp only
  rw [machine_round]
  obtain ⟨q', hr, hb', hf'⟩ := run_ready_iterate (Terminal := Terminal) hc hmb leftSym R rate
    (R + 1) (c, arriveA e.blank (TextFeedStartupSchedule.capture enc) (some a) T) hb hf
    (capture_ready enc a h) ha
  refine ⟨q', hr, hb', hf', ?_⟩
  rw [run_counter_iterate]
  change nextPhase^[R + 1] c.1.1 = _
  rw [hc0, nextPhase_iterate_round]

/-- info: 'PalPeg.TextFeedStartupRun.machine_round_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms machine_round_ready

/-- info: 'PalPeg.TextFeedStartupRun.run_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_first

end PalPeg.TextFeedStartupRun
