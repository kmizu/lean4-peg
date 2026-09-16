import PalPeg.RTQueueControl

/-! Representation lemmas for the front-pop/invalidation prefix of dequeue.
These lemmas concern tape operations; a runtime dispatcher is a separate step. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.RTQueueDequeue

open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.Tape
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg
open PalPeg.RTQueueDispatch PalPeg.RTQueueControl

variable {k : ℕ} {Terminal : Type}

def tailPrep (blank mark : Fin k) (qt : QT k) (s : RotationState (Fin k)) : QT k :=
  run blank (run blank qt (tailFrontProg blank s)) (invProg blank mark s)

/-- The nonempty dequeue prefix preserves precisely the preconditions of check. -/
theorem tailPrep_encodes {blank mark : Fin k} {Q : QT k} {q : Queue (Fin k)}
    {x : Fin k} {f : List (Fin k)} (hfr : q.front = x :: f)
    (h : Encodes blank mark Q q) (hq : Inv q) :
    CEncodes blank mark (tailPrep blank mark Q q.state) (tailQ q) ∧
    SInv (tailQ q).front (tailQ q).state ∧
    (tailQ q).lenf = (frontList (tailQ q).state (tailQ q).front).length ∧
    (tailQ q).lenr = (tailQ q).rear.length := by
  set q'' : Queue (Fin k) :=
    { q with lenf := q.lenf - 1, front := f, state := invalidate q.state } with hq''
  have htq : tailQ q = q'' := by simp [hq'', tailQ, hfr]
  obtain ⟨hsi', hfl, hrm⟩ := invalidate_spec hfr hq.sinv hq.nd hq.pot_front
  obtain ⟨n, hg, heq, hb⟩ := h.dd
  obtain ⟨ki1, ki2, ki3⟩ := inv_keeps blank mark
    (run blank Q (tailFrontProg blank q.state)) q.state
  obtain ⟨P, hP⟩ := frontList_eq_append hq.sinv hq.nd
  have hlenf : 1 ≤ q.lenf := by rw [hq.lenf_eq, hP, hfr]; simp
  have hCE : CEncodes blank mark (tailPrep blank mark Q q.state) q'' := by
    unfold tailPrep
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show SStack blank mark _ f
      rw [ki1, tailFront_front]
      exact sstack_pop2 (hfr ▸ h.front)
    · show SStack blank mark _ (qFdup _)
      rw [ki2]
      by_cases hi : q.state = RotationState.idle
      · have hidle : invalidate q.state = RotationState.idle := by rw [hi]; rfl
        rw [qFdup_mk_idle hidle, hi, tailFront_fdup_idle]
        have hfd : SStack blank mark (Q .fdup) (x :: f) := by
          rw [← hfr, ← qFdup_eq_front hi]; exact h.fdup
        exact sstack_pop2 hfd
      · rw [qFdup_mk_ne (invalidate_ne_idle hi), tailFront_fdup_ne blank Q hi,
          ← qFdup_eq_nil hi]
        exact h.fdup
    · show SStack blank mark _ q.rear
      rw [ki3, tailFront_rear]
      exact h.rear
    · exact inv_enc (tailFront_senc h.state)
    · by_cases hi : q.state = RotationState.idle
      · have hrem0 : rem q.state = 0 := by rw [hi]; rfl
        have hrem0' : rem (invalidate q.state) = 0 := by rw [hi]; rfl
        have hn1 : 1 ≤ n := dd_pos hq heq hb
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        refine ⟨m, ?_, ?_, ?_⟩
        · have e : run blank (run blank Q (tailFrontProg blank q.state))
              (invProg blank mark q.state) .dd
              = step blank (step blank (Q .dd) blank .left) blank .stay := by
            rw [hi]; exact tailInv_dd_idle blank mark Q
          rw [e]
          exact gcount_dec hg
        · show m + rem (invalidate q.state) + q.lenr = q.lenf - 1 + 1
          omega
        · intro hni
          exact absurd (show invalidate q.state = RotationState.idle by rw [hi]; rfl) hni
      · have hrs : rem q.state ≠ 0 := rem_ne_zero_of_ne_idle hq.nd hi
        have hge := inv_rem_ge q.state
        have hexact : rem (invalidate q.state) + 1 = rem q.state := by omega
        refine ⟨n, ?_, ?_, ?_⟩
        · rw [tailInv_dd_ne blank mark Q hi]
          exact hg
        · show n + rem (invalidate q.state) + q.lenr = q.lenf - 1 + 1
          omega
        · intro _
          have := hb hi
          omega
  have hlf'' : q''.lenf = (frontList q''.state q''.front).length := by
    show q.lenf - 1 = (frontList (invalidate q.state) f).length
    rw [hfl, hq.lenf_eq]; simp
  rw [htq]
  exact ⟨hCE, hsi', hlf'', hq.lenr_eq⟩

theorem runs_of_performs {code : Mode → Fin k} {blank : Fin k}
    {p : Prog (ActQ k) (CondQ k)} {qt qt' : QT k} {n : ℕ} (m : Mode)
    (h : Performs Terminal blank p qt n qt') :
    Runs Terminal code blank (liftQ p) qt m n qt' m := by
  obtain ⟨tr, he, hl, ht⟩ := h
  have hh := runs_lift (code := code) (m := m) he
  rwa [hl, ht] at hh

def invShape (p : Phase) (zero : Bool) : IShape :=
  match p with
  | .idle => .ddDec
  | .done => .nil
  | .reversing => if zero then .okZero else .okDec
  | .appending => if zero then .rpPop else .okDec

/-- When the front is nonempty, appending at zero cannot have an empty rp. -/
theorem invShape_eq {front : List (Fin k)} {s : RotationState (Fin k)}
    (hi : SInv front s) (hf : front ≠ []) :
    invShape (phaseOf s) (decide (stOk s = 0)) = ishapeOf s := by
  cases s with
  | idle => rfl
  | done f => rfl
  | reversing ok f fp r rp => cases ok <;> rfl
  | appending ok fp rp =>
      cases ok with
      | succ n => rfl
      | zero =>
          obtain ⟨_, _, P, hP⟩ := hi
          cases rp with
          | cons x xs => rfl
          | nil =>
              simp only [List.drop_zero] at hP
              exact False.elim (hf (List.append_eq_nil_iff.mp hP.symm).1)

def invPhase (p : Phase) (sh : IShape) : Phase :=
  if sh = .rpPop then .done else p

theorem invPhase_eq (s : RotationState (Fin k)) :
    invPhase (phaseOf s) (ishapeOf s) = phaseOf (invalidate s) := by
  cases s with
  | idle => rfl
  | done f => rfl
  | reversing ok f fp r rp => cases ok <;> rfl
  | appending ok fp rp => cases ok <;> cases rp <;> rfl

def finishInv (blank mark : Fin k) (m : Mode) (sh : IShape) : CP k :=
  .seq (liftQ (invStepProg blank mark m.roles sh))
    (storeMode { m with phase := invPhase m.phase sh })

def invalidateBody (blank mark : Fin k) (m : Mode) : CP k :=
  match m.phase with
  | .idle => finishInv blank mark m .ddDec
  | .done => finishInv blank mark m .nil
  | .reversing => probeC blank (m.roles .ok) fun a =>
      finishInv blank mark m (if a = mark then .okZero else .okDec)
  | .appending => probeC blank (m.roles .ok) fun a =>
      finishInv blank mark m (if a = mark then .rpPop else .okDec)

noncomputable def invalidateQueue (blank mark : Fin k) : CP k :=
  select (invalidateBody blank mark)

theorem runs_finishInv {code : Mode → Fin k} {blank mark : Fin k}
    (qt : QT k) (m : Mode) (s : RotationState (Fin k))
    (hp : m.phase = phaseOf s) :
    Runs Terminal code blank (finishInv blank mark m (ishapeOf s)) qt m
      ((invProg blank mark s).length + 1)
      (run blank qt (renameL m.roles (invProg blank mark s)))
      { m with phase := phaseOf (invalidate s) } := by
  have h1 := runs_of_performs (code := code) m
    (performs_invStep (Terminal := Terminal) (blank := blank) (mark := mark)
      (π := m.roles) qt s)
  have h2 := runs_store (Terminal := Terminal) (code := code) (blank := blank)
    (run blank qt (renameL m.roles (invProg blank mark s))) m
    { m with phase := invPhase m.phase (ishapeOf s) }
  simpa only [finishInv, hp, invPhase_eq] using runs_seq h1 h2

/-- info: 'PalPeg.RTQueueDequeue.tailPrep_encodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tailPrep_encodes

theorem invalidateBody_runs {code : Mode → Fin k} {blank mark : Fin k}
    {qt : QT k} {m : Mode} {s : RotationState (Fin k)} {front : List (Fin k)}
    (hmb : mark ≠ blank) (hi : SInv front s) (hf : front ≠ [])
    (hs : SEnc blank mark (qt ∘ m.roles) s) (hp : m.phase = phaseOf s) :
    ∃ n, n ≤ 7 ∧ Runs Terminal code blank (invalidateBody blank mark m) qt m n
      (run blank qt (renameL m.roles (invProg blank mark s)))
      { m with phase := phaseOf (invalidate s) } := by
  have he := runs_finishInv (Terminal := Terminal) (code := code)
    (blank := blank) (mark := mark) qt m s hp
  have hshape := invShape_eq hi hf
  have hlen := invProg_length blank mark s
  cases s with
  | idle =>
      refine ⟨3, by omega, ?_⟩
      simpa only [invalidateBody, hp, phaseOf, ishapeOf, invProg,
        List.length_cons, List.length_nil] using he
  | done f =>
      refine ⟨1, by omega, ?_⟩
      simpa only [invalidateBody, hp, phaseOf, ishapeOf, invProg,
        List.length_nil, Nat.zero_add] using he
  | reversing ok f fp r rp =>
      have hg : GCount blank mark (qt (m.roles .ok)) ok := hs.2.2.2.2.2
      have hr : (List.replicate ok blank).head?.getD mark = mark ↔ ok = 0 := by
        rw [← sstack_probe hg]
        exact gcount_isZero_iff hmb hg
      simp only [phaseOf, invShape, stOk, decide_eq_true_eq] at hshape
      have hb : Runs Terminal code blank
          (finishInv blank mark m (if (List.replicate ok blank).head?.getD mark = mark
            then .okZero else .okDec)) qt m
          ((invProg blank mark (.reversing ok f fp r rp)).length + 1)
          (run blank qt (renameL m.roles (invProg blank mark (.reversing ok f fp r rp))))
          { m with phase := phaseOf (invalidate (.reversing ok f fp r rp)) } := by
        simp only [hr, hshape]
        exact he
      refine ⟨2 + ((invProg blank mark (.reversing ok f fp r rp)).length + 1), by omega, ?_⟩
      simp only [invalidateBody, hp, phaseOf]
      exact runs_probeC (body := fun a =>
        finishInv blank mark m (if a = mark then .okZero else .okDec)) hg hb
  | appending ok fp rp =>
      have hg : GCount blank mark (qt (m.roles .ok)) ok := hs.2.2.2.2.2
      have hr : (List.replicate ok blank).head?.getD mark = mark ↔ ok = 0 := by
        rw [← sstack_probe hg]
        exact gcount_isZero_iff hmb hg
      simp only [phaseOf, invShape, stOk, decide_eq_true_eq] at hshape
      have hb : Runs Terminal code blank
          (finishInv blank mark m (if (List.replicate ok blank).head?.getD mark = mark
            then .rpPop else .okDec)) qt m
          ((invProg blank mark (.appending ok fp rp)).length + 1)
          (run blank qt (renameL m.roles (invProg blank mark (.appending ok fp rp))))
          { m with phase := phaseOf (invalidate (.appending ok fp rp)) } := by
        simp only [hr, hshape]
        exact he
      refine ⟨2 + ((invProg blank mark (.appending ok fp rp)).length + 1), by omega, ?_⟩
      simp only [invalidateBody, hp, phaseOf]
      exact runs_probeC (body := fun a =>
        finishInv blank mark m (if a = mark then .rpPop else .okDec)) hg hb

/-- The invalidation program reads only its own finite mode and counter tape. -/
theorem invalidateQueue_runs {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark : Fin k} {qt : QT k} {m : Mode} {s : RotationState (Fin k)}
    {front : List (Fin k)} (hmb : mark ≠ blank) (hi : SInv front s) (hf : front ≠ [])
    (hs : SEnc blank mark (qt ∘ m.roles) s) (hp : m.phase = phaseOf s) :
    ∃ n, n ≤ 7 ∧ Runs Terminal code blank (invalidateQueue blank mark) qt m n
      (run blank qt (renameL m.roles (invProg blank mark s)))
      { m with phase := phaseOf (invalidate s) } := by
  obtain ⟨n, hn, he⟩ := invalidateBody_runs (Terminal := Terminal) (code := code)
    hmb hi hf hs hp
  exact ⟨n, hn, runs_select hc he⟩

/-- info: 'PalPeg.RTQueueDequeue.invalidateQueue_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invalidateQueue_runs


def frontBody (blank : Fin k) (m : Mode) : CP k :=
  liftQ (tailFrontP blank m.roles (if m.phase = .idle then .idle else .busy))

noncomputable def popFront (blank : Fin k) : CP k := select (frontBody blank)

theorem popFront_runs {code : Mode → Fin k} (hc : Function.Injective code)
    {blank : Fin k} (qt : QT k) (m : Mode) (s : RotationState (Fin k))
    (hp : m.phase = phaseOf s) :
    Runs Terminal code blank (popFront blank) qt m (tailFrontProg blank s).length
      (run blank qt (renameL m.roles (tailFrontProg blank s))) m := by
  apply runs_select hc
  have hh := runs_of_performs (code := code) m
    (performs_tailFront (Terminal := Terminal) (blank := blank) (π := m.roles) qt s)
  have ht : (if m.phase = Phase.idle then TShape.idle else .busy) = tshapeOf s := by
    rw [hp]; cases s <;> rfl
  simpa only [frontBody, ht] using hh

noncomputable def dequeuePrefix (blank mark : Fin k) : CP k :=
  .seq (popFront blank) (invalidateQueue blank mark)

/-- An actual, queue-independent front-pop/invalidation program, including all
counter probes and the mode write in its eleven-action upper bound. -/
theorem dequeuePrefix_runs {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark : Fin k} {qt : QT k} {m : Mode} {q : Queue (Fin k)}
    (hπ : Function.Injective m.roles) (hmb : mark ≠ blank)
    (h : Encodes blank mark (qt ∘ m.roles) q) (hq : Inv q)
    (hf : q.front ≠ []) (hp : m.phase = phaseOf q.state) :
    ∃ n qt', n ≤ 11 ∧ Runs Terminal code blank (dequeuePrefix blank mark) qt m n qt'
      { m with phase := phaseOf (invalidate q.state) } ∧
      qt' ∘ m.roles = tailPrep blank mark (qt ∘ m.roles) q.state ∧
      CEncodes blank mark (qt' ∘ m.roles) (tailQ q) := by
  let qt1 := run blank qt (renameL m.roles (tailFrontProg blank q.state))
  have h1 := popFront_runs (Terminal := Terminal) hc (blank := blank) qt m q.state hp
  have hqt1 : qt1 ∘ m.roles = run blank (qt ∘ m.roles) (tailFrontProg blank q.state) :=
    run_rename hπ blank _ qt
  have hs1 : SEnc blank mark (qt1 ∘ m.roles) q.state := by
    rw [hqt1]; exact tailFront_senc h.state
  obtain ⟨n, hn, h2⟩ := invalidateQueue_runs (Terminal := Terminal) hc
    hmb hq.sinv hf hs1 hp
  let qt2 := run blank qt1 (renameL m.roles (invProg blank mark q.state))
  have hqt2 : qt2 ∘ m.roles = tailPrep blank mark (qt ∘ m.roles) q.state := by
    change run blank qt1 _ ∘ m.roles = _
    rw [run_rename hπ, hqt1]; rfl
  refine ⟨(tailFrontProg blank q.state).length + n, qt2, ?_, runs_seq h1 h2, hqt2, ?_⟩
  · have := tailFrontProg_length blank q.state; omega
  · rw [hqt2]
    cases hfr : q.front with
    | nil => exact False.elim (hf hfr)
    | cons x f => exact (tailPrep_encodes hfr h hq).1

/-- info: 'PalPeg.RTQueueDequeue.dequeuePrefix_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dequeuePrefix_runs

theorem stF_invalidate (s : RotationState (Fin k)) : stF (invalidate s) = stF s := by
  cases s with
  | idle => rfl
  | done f => rfl
  | reversing ok f fp r rp => rfl
  | appending ok fp rp => cases ok <;> cases rp <;> rfl

noncomputable def dequeueNonempty (blank mark : Fin k) : CP k :=
  .seq (dequeuePrefix blank mark) (checkQueue blank mark)

theorem dequeueNonempty_runs {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark : Fin k} {qt : QT k} {m : Mode} {q : Queue (Fin k)}
    (hπ : Function.Injective m.roles) (hmb : mark ≠ blank)
    (h : Encodes blank mark (qt ∘ m.roles) q) (hq : Inv q)
    (hf : q.front ≠ []) (hp : m.phase = phaseOf q.state)
    (hm : mark ∉ stF q.state) (hmf : mark ∉ q.front) :
    ∃ n qt' m', n ≤ 42 ∧ Runs Terminal code blank (dequeueNonempty blank mark)
      qt m n qt' m' ∧ Function.Injective m'.roles ∧
      m'.phase = phaseOf (RTQueue.tail q).state ∧
      Encodes blank mark (qt' ∘ m'.roles) (RTQueue.tail q) := by
  obtain ⟨n, qt1, hn, h1, heq, hCE⟩ := dequeuePrefix_runs (Terminal := Terminal)
    hc hπ hmb h hq hf hp
  cases hfr : q.front with
  | nil => exact False.elim (hf hfr)
  | cons x f =>
      obtain ⟨_, hi, hlf, hlr⟩ := tailPrep_encodes hfr h hq
      have hmt : mark ∉ stF (tailQ q).state := by
        simpa only [tailQ, stF_invalidate] using hm
      have hmft : mark ∉ (tailQ q).front := by
        simpa only [tailQ, hfr, List.tail_cons] using
          (show mark ∉ f from fun ha => hmf (hfr ▸ List.mem_cons_of_mem x ha))
      obtain ⟨n2, qt2, m2, hn2, h2, hinj, hp2, he2⟩ :=
        checkQueue_runs (Terminal := Terminal) hc (qt := qt1)
          (m := { m with phase := phaseOf (invalidate q.state) })
          (q := tailQ q) hπ hmb hi hCE hmt hmft rfl hlf hlr
      have ht : RTQueue.tail q = check (tailQ q) := by
        simp only [RTQueue.tail, tailQ, hfr, List.tail_cons]
      refine ⟨n + n2, qt2, m2, by omega, runs_seq h1 h2, hinj, ?_, ?_⟩
      · rwa [ht]
      · rwa [ht]

noncomputable def dequeueBody (blank mark : Fin k) (m : Mode) : CP k :=
  probeC blank (m.roles .front) fun a =>
    if a = mark then liftQ .skip else dequeueNonempty blank mark

/-- A fixed dequeue program: no unbounded queue or externally selected shape
is an argument. Even the empty/nonempty branch is read from a restored tape. -/
noncomputable def dequeue (blank mark : Fin k) : CP k :=
  select (dequeueBody blank mark)

theorem dequeue_runs {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark : Fin k} {qt : QT k} {m : Mode} {q : Queue (Fin k)}
    (hπ : Function.Injective m.roles) (hmb : mark ≠ blank)
    (h : Encodes blank mark (qt ∘ m.roles) q) (hq : Inv q)
    (hp : m.phase = phaseOf q.state) (hm : mark ∉ stF q.state) (hmf : mark ∉ q.front) :
    ∃ n qt' m', n ≤ 44 ∧ Runs Terminal code blank (dequeue blank mark)
      qt m n qt' m' ∧ Function.Injective m'.roles ∧
      m'.phase = phaseOf (RTQueue.tail q).state ∧
      Encodes blank mark (qt' ∘ m'.roles) (RTQueue.tail q) := by
  have hs : SStack blank mark (qt (m.roles .front)) q.front := h.front
  have hr : q.front.head?.getD mark = mark ↔ q.front = [] := by
    rw [← sstack_probe hs]
    exact stack_probe_empty_iff hs hmf
  by_cases hf : q.front = []
  · have ht : RTQueue.tail q = q := by simp only [RTQueue.tail, hf]
    have hskip := runs_of_performs (Terminal := Terminal) (code := code) m
      (performs_skip (Terminal := Terminal) (blank := blank) qt)
    have hb : Runs Terminal code blank
        (if q.front.head?.getD mark = mark then liftQ Prog.skip else dequeueNonempty blank mark)
        qt m 0 qt m := by
      rw [if_pos (hr.mpr hf)]; exact hskip
    have he := runs_probeC (qt := qt) (m := m) (ρ := m.roles .front)
      (body := fun a => if a = mark then liftQ Prog.skip else dequeueNonempty blank mark) hs hb
    refine ⟨2, qt, m, by omega, runs_select hc he, hπ, ?_, ?_⟩
    · rwa [ht]
    · rwa [ht]
  · obtain ⟨n, qt', m', hn, hb, hinj, hp', he'⟩ :=
      dequeueNonempty_runs (Terminal := Terminal) hc hπ hmb h hq hf hp hm hmf
    have hb' : Runs Terminal code blank
        (if q.front.head?.getD mark = mark then liftQ Prog.skip else dequeueNonempty blank mark)
        qt m n qt' m' := by
      rw [if_neg (fun ha => hf (hr.mp ha))]; exact hb
    have he := runs_probeC (qt := qt) (m := m) (ρ := m.roles .front)
      (body := fun a => if a = mark then liftQ Prog.skip else dequeueNonempty blank mark) hs hb'
    exact ⟨2 + n, qt', m', by omega, runs_select hc he, hinj, hp', he'⟩

/-- info: 'PalPeg.RTQueueDequeue.dequeue_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dequeue_runs

end PalPeg.RTQueueDequeue
