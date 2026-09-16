import PalPeg.TextFeedTiming
import PalPeg.ProgLangPersist2
import PalPeg.ProgLangBank

/-! A real arrival hook and a stationary input register for the closed text
feeder. Arrival and worker execution are separate, as in the persistent bank
machine. The worker never takes the received symbol as a program argument. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.TextFeedInput

open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist2
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg
open PalPeg.RTQueueDispatch PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedTiming

variable {k : ℕ} {Terminal : Type}

abbrev CT (k : ℕ) := (CQ k ⊕ GSProg.Cond8) ⊕ Test
abbrev RP (k : ℕ) := Prog (AP k ⊕ Empty) (CT k ⊕ Fin k)

def IReg : Interp Terminal Empty (Fin k) (Fin k) 1 where
  actOf a := nomatch a
  condOf a σ := decide (σ 0 = a)

noncomputable def IR (e : Env k) := Interp.sum (IT (Terminal := Terminal) e)
  (IReg (Terminal := Terminal) (k := k))

def cell (a : Fin k) : Fin 1 → STape (Fin k) := fun _ => ⟨[], a, []⟩

def rtapes (e : Env k) (qt : QT k) (m : Mode) (S : Stage k) (a : Fin k) :=
  Fin.append (TextFeedControl.tapes e qt m S) (cell a)

def liftWorker (p : TP k) : RP k := Prog.map Sum.inl Sum.inl p

def RExec (e : Env k) (p : RP k) (qt : QT k) (m : Mode) (S : Stage k) (a : Fin k)
    (n : ℕ) (qt' : QT k) (m' : Mode) (S' : Stage k) : Prop :=
  ∃ tr, Exec (IR (Terminal := Terminal) e) e.blank p (rtapes e qt m S a) tr ∧
    tr.length = n ∧ applyTrace e.blank (rtapes e qt m S a) tr = rtapes e qt' m' S' a

theorem rexec_lift {e : Env k} {p : TP k} {qt qt' : QT k} {m m' : Mode}
    {S S' : Stage k} {n : ℕ} (a : Fin k)
    (h : TExec (Terminal := Terminal) e p qt m S n qt' m' S') :
    RExec (Terminal := Terminal) e (liftWorker p) qt m S a n qt' m' S' := by
  obtain ⟨tr, he, hn, ht⟩ := h
  have hh := exec_sum_inl (I2 := IReg (Terminal := Terminal) (k := k)) he (rtapes e qt m S a)
  rw [rtapes, extend_castAdd_append] at hh
  refine ⟨_, hh, by simp [hn], ?_⟩
  have ha := applyTrace_extend (Fin.castAddEmb 1) e.blank (rtapes e qt m S a) tr
    (TextFeedControl.tapes e qt m S)
  simp only [rtapes, extend_castAdd_append, ht] at ha
  exact ha

noncomputable def readInput (body : Fin k → RP k) : RP k := choose Sum.inr body

theorem rexec_read {e : Env k} {body : Fin k → RP k} {qt qt' : QT k} {m m' : Mode}
    {S S' : Stage k} {a : Fin k} {n : ℕ}
    (h : RExec (Terminal := Terminal) e (body a) qt m S a n qt' m' S') :
    RExec (Terminal := Terminal) e (readInput body) qt m S a n qt' m' S' := by
  obtain ⟨tr, he, hn, ht⟩ := h
  refine ⟨tr, exec_choose ?_ he, hn, ht⟩
  intro b
  change decide (a = b) = decide (a = b)
  rfl

/-- One constant program, independently of the current arrival symbol. -/
noncomputable def workerRound (blank mark : Fin k) (rate : ℕ) : RP k :=
  readInput fun a => liftWorker (TextFeedTiming.round blank mark rate a)

theorem workerRound_matches {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {v Text : List (Fin k)} {rate p₁ r n c : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n < Text.length)
    (hb : ∀ st : ScanState, st.q ≤ v.length → TextFeed.stepCost' v rate p₁ r Text st ≤ c)
    {qt : QT k} {m : Mode} {M : TextFeed.Machine' k} {a : Fin k}
    (ha : Text[n]? = some a) (h : Ready e.blank e.mark qt m M.Q)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ r n M) :
    ∃ ticks qt' m', ticks ≤ 34 + gsRate rate * (c + 47) ∧
      RExec (Terminal := Terminal) e (workerRound e.blank e.mark rate)
        qt m (GSProg.TS M.ts) a ticks qt' m'
          (GSProg.TS (TextFeed.roundT' e.blank e.endSym e.mark v rate p₁ r n Text a M).ts) ∧
      Ready e.blank e.mark qt' m'
        (TextFeed.roundT' e.blank e.endSym e.mark v rate p₁ r n Text a M).Q := by
  obtain ⟨ticks, qt', m', hticks, he, hr⟩ := TextFeedTiming.round_matches (Terminal := Terminal)
    hc hmb hk hv hend hstart hblank hmark hn hb ha h hf
  exact ⟨ticks, qt', m', hticks, rexec_read (rexec_lift a he), hr⟩

def inputIdx : Fin 20 := Fin.natAddEmb 19 (0 : Fin 1)

/-- This is an arrival action for the existing persistent-machine interface,
not a fabricated symbol parameter in the worker program. A missing arrival
leaves the register unchanged. -/
def capture (enc : Terminal → Fin k) : ArriveAct Terminal (Fin k) 20 :=
  fun a σ => touchVec inputIdx (a.elim (σ inputIdx) enc) .stay σ

theorem capture_other (blank : Fin k) (enc : Terminal → Fin k) (a : Option Terminal)
    (T : Fin 20 → STape (Fin k)) {j : Fin 20} (hj : j ≠ inputIdx) :
    arriveA blank (capture enc) a T j = T j := by
  simp only [arriveA, capture, touchVec, if_neg hj]
  rfl

theorem capture_none (blank : Fin k) (enc : Terminal → Fin k)
    (T : Fin 20 → STape (Fin k)) : arriveA blank (capture enc) none T = T := by
  funext j
  by_cases hj : j = inputIdx
  · subst j; simp only [arriveA, capture, touchVec, Option.elim]; rfl
  · exact capture_other blank enc none T hj

theorem capture_some (e : Env k) (enc : Terminal → Fin k) (a : Terminal)
    (qt : QT k) (m : Mode) (S : Stage k) (old : Fin k) :
    arriveA e.blank (capture enc) (some a) (rtapes e qt m S old) = rtapes e qt m S (enc a) := by
  funext j
  refine Fin.addCases (m := 19) (n := 1) (fun j => ?_) (fun j => ?_) j
  · have hj : Fin.castAdd 1 j ≠ inputIdx := by
      intro he
      have hv := congrArg Fin.val he
      simp only [inputIdx, Fin.natAddEmb_apply, Fin.val_castAdd, Fin.val_natAdd] at hv
      have := j.isLt
      omega
    rw [capture_other e.blank enc (some a) _ hj]
    simp only [rtapes, Fin.append_left]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp only [arriveA, capture, touchVec, inputIdx, Fin.natAddEmb_apply,
      Option.elim, rtapes, Fin.append_right, cell]
    rfl

/-- Arrival from an actual terminal, followed by the fixed worker. The bound
includes the arrival action. Scheduling a sufficiently large uninterrupted
worker window is a separate global obligation, not hidden in this theorem. -/
theorem arrivalRound_matches {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) (enc : Terminal → Fin k) (a : Terminal)
    {v Text : List (Fin k)} {rate p₁ r n c : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n < Text.length)
    (hb : ∀ st : ScanState, st.q ≤ v.length → TextFeed.stepCost' v rate p₁ r Text st ≤ c)
    {qt : QT k} {m : Mode} {M : TextFeed.Machine' k} (old : Fin k)
    (ha : Text[n]? = some (enc a)) (h : Ready e.blank e.mark qt m M.Q)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ r n M) :
    ∃ (tr : List (Fin 20 → Fin k × Move)) (qt' : QT k) (m' : Mode),
      1 + tr.length ≤ 35 + gsRate rate * (c + 47) ∧
      Exec (IR (Terminal := Terminal) e) e.blank (workerRound e.blank e.mark rate)
        (arriveA e.blank (capture enc) (some a) (rtapes e qt m (GSProg.TS M.ts) old)) tr ∧
      applyTrace e.blank (rtapes e qt m (GSProg.TS M.ts) old)
        (capture enc (some a) (fun j => (rtapes e qt m (GSProg.TS M.ts) old j).focus) :: tr) =
        rtapes e qt' m'
          (GSProg.TS (TextFeed.roundT' e.blank e.endSym e.mark v rate p₁ r n Text (enc a) M).ts)
          (enc a) ∧
      Ready e.blank e.mark qt' m'
        (TextFeed.roundT' e.blank e.endSym e.mark v rate p₁ r n Text (enc a) M).Q := by
  obtain ⟨ticks, qt', m', hticks, hwork, hr⟩ := workerRound_matches (Terminal := Terminal)
    hc hmb hk hv hend hstart hblank hmark hn hb ha h hf
  obtain ⟨tr, he, hlen, hout⟩ := hwork
  refine ⟨tr, qt', m', by omega, ?_, ?_, hr⟩
  · rw [capture_some]; exact he
  · change applyTrace e.blank
      (arriveA e.blank (capture enc) (some a) (rtapes e qt m (GSProg.TS M.ts) old)) tr = _
    rw [capture_some]; exact hout

/-- The arrival register cannot modify even a suspended worker's 19 tapes. -/
theorem capture_worker_frame (e : Env k) (enc : Terminal → Fin k) (a : Terminal)
    (qt : QT k) (m : Mode) (S : Stage k) (old : Fin k) :
    (arriveA e.blank (capture enc) (some a) (rtapes e qt m S old)) ∘ Fin.castAddEmb 1 =
      TextFeedControl.tapes e qt m S := by
  rw [capture_some]
  funext j
  simp only [Function.comp_apply, rtapes, Fin.castAddEmb_apply, Fin.append_left]

/-- info: 'PalPeg.TextFeedInput.workerRound_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms workerRound_matches

/-- info: 'PalPeg.TextFeedInput.arrivalRound_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arrivalRound_matches

/-- info: 'PalPeg.TextFeedInput.capture_worker_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms capture_worker_frame

/-- The feeder is a worker: acceptance-flag updates belong to the surrounding
machine, so its own actions leave that flag unchanged. -/
noncomputable def workerIF (e : Env k) :
    ProgLangPersist.InterpF Terminal (AP k ⊕ Empty) (CT k ⊕ Fin k) (Fin k) 20 where
  toInterp := IR (Terminal := Terminal) e
  flagOf := fun _ => none

/-- Direct use in the existing finite continuation bank. At the actual phase
zero arrival, all suspended controls are retained and only the input register
changes. This statement applies to arbitrary suspended bank states. -/
theorem bank_capture_zero {slots B : ℕ} (e : Env k) (enc : Terminal → Fin k)
    [DecidableEq (AP k ⊕ Empty)] [DecidableEq (CT k ⊕ Fin k)]
    (progs : Fin slots → RP k) (hB : 0 < B) (slot : Fin B → Fin slots)
    (ctrl : ProgLangBank.Bank progs × Bool) (a : Terminal)
    (qt : QT k) (m : Mode) (S : Stage k) (old : Fin k) :
    bodyStep e.blank
      (ProgLangBank.bankBody progs (fun _ => workerIF (Terminal := Terminal) e)
        (capture enc) hB slot) ⟨0, hB⟩ (some a) (ctrl, rtapes e qt m S old) =
      (ctrl, rtapes e qt m S (enc a)) := by
  rw [ProgLangBank.bankBody_zero, capture_some]

/-- info: 'PalPeg.TextFeedInput.bank_capture_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bank_capture_zero

end PalPeg.TextFeedInput
