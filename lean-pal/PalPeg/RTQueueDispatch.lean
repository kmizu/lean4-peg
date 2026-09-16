import PalPeg.RTQueueProg

/-!
# Reading the queue rotation branch from its tapes

Only the four-state phase tag is retained. The unbounded-list and counter
branches formerly packaged in `EShape` are obtained by a read/restore probe.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.RTQueueDispatch

open PegSeparation.RealTimeTM PalPeg.ProgLang PalPeg.RTQueue PalPeg.RTQueueTapes
open PalPeg.RTQueueProg

variable {k : ℕ} {Terminal : Type}

inductive Phase where
  | idle | reversing | appending | done
  deriving DecidableEq, Fintype

def phaseOf : RotationState (Fin k) → Phase
  | .idle => .idle
  | .reversing .. => .reversing
  | .appending .. => .appending
  | .done .. => .done

def selectShape : Phase → Bool → Bool → EShape
  | .idle, _, _ => .nil
  | .done, _, _ => .nil
  | .reversing, fEmpty, _ => if fEmpty then .revNil else .revCons
  | .appending, _, okZero => if okZero then .appZ else .appS

theorem selectShape_eq {front : List (Fin k)} {s : RotationState (Fin k)}
    (h : SInv front s) :
    selectShape (phaseOf s) (decide (stF s = [])) (decide (stOk s = 0)) = eshapeOf s := by
  cases s with
  | idle => rfl
  | done f => rfl
  | reversing ok f fp r rp =>
      have hr := h.2.2.1
      cases f with
      | nil =>
          have hlen : r.length = 1 := by simpa using hr
          cases r with
          | nil => simp at hlen
          | cons a r =>
              have hr0 : r = [] := by simpa using hlen
              subst r
              rfl
      | cons a f =>
          cases r with
          | nil => simp at hr
          | cons b r => rfl
  | appending ok fp rp =>
      cases ok with
      | zero => rfl
      | succ ok =>
          have hlen := congrArg List.length h.2.1
          rw [List.length_reverse, List.length_take_of_le h.1] at hlen
          cases fp with
          | nil => simp at hlen
          | cons a fp => rfl

theorem stack_probe_empty_iff {blank mark : Fin k} {tp : TapeConfiguration k}
    {l : List (Fin k)} (h : SStack blank mark tp l) (hm : mark ∉ l) :
    Tape.read (Tape.step blank tp blank .left) = mark ↔ l = [] := by
  rw [sstack_probe h]
  cases l with
  | nil => simp
  | cons a l =>
      have ha : a ≠ mark := by intro e; subst a; exact hm (List.mem_cons_self ..)
      simp [ha]

/-- Exact restoration, not just preservation of the stack invariant. -/
theorem stack_probe_restore {blank mark : Fin k} {tp : TapeConfiguration k}
    {l : List (Fin k)} (h : SStack blank mark tp l) :
    Tape.step blank (Tape.step blank tp blank .left)
      (Tape.read (Tape.step blank tp blank .left)) .right = tp := by
  obtain ⟨junk, hv⟩ := h
  have hne : tp.left ≠ [] := by rw [hv.left_eq]; simp
  cases hl : tp.left with
  | nil => exact (hne hl).elim
  | cons a rest =>
      rw [Tape.step_left_of_left_cons hl]
      cases tp with
      | mk ls cur rs =>
          simp only at hl
          subst ls
          have hc := hv.focus_blank
          simp only at hc
          subst cur
          rfl

def probeThen (blank : Fin k) (ρ : Role) (body : Fin k → Prog (ActQ k) (CondQ k)) :
    Prog (ActQ k) (CondQ k) :=
  .seq (.act (ρ, blank, .left))
    (caseSym ρ (fun a => .seq (.act (ρ, a, .right)) (body a)))

theorem probeThen_exec {blank mark : Fin k} {ρ : Role} {qt : QT k}
    {l : List (Fin k)} {body : Fin k → Prog (ActQ k) (CondQ k)} {acts : List (Act k)}
    (h : SStack blank mark (qt ρ) l)
    (he : ExecQ Terminal blank (body (l.head?.getD mark)) qt acts) :
    ExecQ Terminal blank (probeThen blank ρ body) qt
      (⟨ρ, blank, .left⟩ :: ⟨ρ, l.head?.getD mark, .right⟩ :: acts) := by
  let qt1 := run blank qt [⟨ρ, blank, .left⟩]
  have hread : (qt1 ρ).focus = l.head?.getD mark := by
    simp only [qt1, run_cons, run_nil, act_apply]
    exact sstack_probe h
  have hrestore : run blank qt1 [⟨ρ, l.head?.getD mark, .right⟩] = qt := by
    funext j
    by_cases hj : j = ρ
    · subst j
      simp only [qt1, run_cons, run_nil, act_apply]
      rw [← sstack_probe h]
      exact stack_probe_restore h
    · simp [qt1, run, act, hj]
  unfold probeThen
  refine execQ_seq (execQ_act ρ blank .left qt) (execQ_caseSym ?_)
  change ExecQ Terminal blank
    (.seq (.act (ρ, (qt1 ρ).focus, .right)) (body (qt1 ρ).focus)) qt1 _
  rw [hread]
  exact execQ_seq (execQ_act ρ _ .right qt1) (hrestore ▸ he)

theorem probePrefix_restore {blank mark : Fin k} {ρ : Role} {qt : QT k}
    {l : List (Fin k)} (h : SStack blank mark (qt ρ) l) :
    run blank qt [⟨ρ, blank, .left⟩, ⟨ρ, l.head?.getD mark, .right⟩] = qt := by
  funext j
  by_cases hj : j = ρ
  · subst j
    simp only [run_cons, run_nil, act_apply]
    rw [← sstack_probe h]
    exact stack_probe_restore h
  · simp [run, act, hj]

theorem probeThen_effect {blank mark : Fin k} {ρ : Role} {qt : QT k}
    {l : List (Fin k)} {body : Fin k → Prog (ActQ k) (CondQ k)} {acts : List (Act k)}
    (h : SStack blank mark (qt ρ) l)
    (he : ExecQ Terminal blank (body (l.head?.getD mark)) qt acts) :
    ∃ trace, ExecQ Terminal blank (probeThen blank ρ body) qt trace ∧
      run blank qt trace = run blank qt acts ∧ trace.length = acts.length + 2 := by
  refine ⟨[⟨ρ, blank, .left⟩, ⟨ρ, l.head?.getD mark, .right⟩] ++ acts,
    probeThen_exec h he, ?_, ?_⟩
  · rw [run_append, probePrefix_restore h]
  · simp

/-- One fixed program per coarse phase and physical role assignment. -/
def dispatchProg (blank mark : Fin k) (π : Role → Role) : Phase → Prog (ActQ k) (CondQ k)
  | .idle => .skip
  | .done => .skip
  | .reversing => probeThen blank (π .f) (fun a =>
      execStepProg blank π (if a = mark then .revNil else .revCons))
  | .appending => probeThen blank (π .ok) (fun a =>
      execStepProg blank π (if a = mark then .appZ else .appS))

theorem dispatchProg_exec {blank mark : Fin k} {π : Role → Role} {qt : QT k}
    {front : List (Fin k)} {s : RotationState (Fin k)}
    (hπ : Function.Injective π) (hmb : mark ≠ blank)
    (hsi : SInv front s) (hs : SEnc blank mark (qt ∘ π) s)
    (hm : mark ∉ stF s) :
    ∃ trace, ExecQ Terminal blank (dispatchProg blank mark π (phaseOf s)) qt trace ∧
      run blank qt trace = run blank qt (renameL π (execProg blank s)) ∧
      trace.length ≤ 11 := by
  have he := execQ_execStep (Terminal := Terminal) hπ hs
  have hshape := selectShape_eq hsi
  have hlen := execProg_length blank s
  cases s with
  | idle => exact ⟨[], execQ_skip qt, rfl, by simp⟩
  | done f => exact ⟨[], execQ_skip qt, rfl, by simp⟩
  | reversing ok f fp r rp =>
      have hf : SStack blank mark (qt (π .f)) f := hs.1
      have hr : f.head?.getD mark = mark ↔ f = [] := by
        rw [← sstack_probe hf]
        exact stack_probe_empty_iff hf hm
      simp only [phaseOf, selectShape, stF, decide_eq_true_eq] at hshape
      have hbody : ExecQ Terminal blank
          (execStepProg blank π (if f.head?.getD mark = mark then .revNil else .revCons))
          qt (renameL π (execProg blank (.reversing ok f fp r rp))) := by
        simp only [hr, hshape]
        exact he
      obtain ⟨tr, ht, hrun, hcost⟩ := probeThen_effect
        (body := fun a => execStepProg blank π (if a = mark then .revNil else .revCons)) hf hbody
      refine ⟨tr, ht, hrun, ?_⟩
      rw [renameL_length] at hcost
      omega
  | appending ok fp rp =>
      have hg : GCount blank mark (qt (π .ok)) ok := hs.2.2.2.2.2
      have hr : (List.replicate ok blank).head?.getD mark = mark ↔ ok = 0 := by
        rw [← sstack_probe hg]
        exact gcount_isZero_iff hmb hg
      simp only [phaseOf, selectShape, stOk, decide_eq_true_eq] at hshape
      have hbody : ExecQ Terminal blank
          (execStepProg blank π (if (List.replicate ok blank).head?.getD mark = mark
            then .appZ else .appS)) qt (renameL π (execProg blank (.appending ok fp rp))) := by
        simp only [hr, hshape]
        exact he
      obtain ⟨tr, ht, hrun, hcost⟩ := probeThen_effect
        (body := fun a => execStepProg blank π (if a = mark then .appZ else .appS)) hg hbody
      refine ⟨tr, ht, hrun, ?_⟩
      rw [renameL_length] at hcost
      omega

def phaseAfter (old : Phase) : EShape → Phase
  | .nil => old
  | .revCons => .reversing
  | .revNil => .appending
  | .appZ => .done
  | .appS => .appending

/-- The next coarse phase is determined by the executed finite branch. -/
theorem phaseAfter_eq (s : RotationState (Fin k)) :
    phaseAfter (phaseOf s) (eshapeOf s) = phaseOf (exec s) := by
  cases s with
  | idle => rfl
  | done f => rfl
  | reversing ok f fp r rp =>
      cases f with
      | nil =>
          cases r with
          | nil => rfl
          | cons a r => cases r <;> rfl
      | cons a f => cases r <;> rfl
  | appending ok fp rp =>
      cases ok with
      | zero => rfl
      | succ ok => cases fp <;> rfl

/-- info: 'PalPeg.RTQueueDispatch.dispatchProg_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dispatchProg_exec

end PalPeg.RTQueueDispatch
