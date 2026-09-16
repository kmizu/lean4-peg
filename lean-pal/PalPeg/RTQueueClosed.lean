import PalPeg.RTQueueDequeue

/-! Closed contracts for repeated finite-control queue operations. Marker
separation is stated on abstract FIFO contents, not arbitrary tape garbage. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.RTQueueClosed

open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg
open PalPeg.RTQueueDispatch PalPeg.RTQueueControl PalPeg.RTQueueDequeue

variable {k : ℕ} {Terminal : Type}

def Clean (mark : Fin k) (q : Queue (Fin k)) : Prop := mark ∉ toList q

theorem clean_front {mark : Fin k} {q : Queue (Fin k)} (hq : Inv q)
    (h : Clean mark q) : mark ∉ q.front := by
  obtain ⟨P, hP⟩ := frontList_eq_append hq.sinv hq.nd
  intro hm
  apply h
  simp only [toList, hP, List.mem_append]
  exact Or.inl (Or.inl hm)

theorem clean_stF {mark : Fin k} {q : Queue (Fin k)} (hq : Inv q)
    (h : Clean mark q) : mark ∉ stF q.state := by
  have hf := clean_front hq h
  have hs := hq.sinv
  cases he : q.state with
  | idle => simp [stF]
  | done f => simp [stF]
  | appending ok fp rp => simp [stF]
  | reversing ok f fp r rp =>
      rw [he] at hs
      simp only [stF]
      rw [hs.2.1]
      exact fun hm => hf (List.mem_of_mem_drop hm)

theorem clean_snoc {mark a : Fin k} {q : Queue (Fin k)} (hq : Inv q)
    (h : Clean mark q) (ha : a ≠ mark) : Clean mark (snoc q a) := by
  unfold Clean
  rw [toList_snoc hq]
  simp only [List.mem_append, List.mem_singleton]
  exact fun hm => hm.elim h (fun e => ha e.symm)

theorem clean_tail {mark : Fin k} {q : Queue (Fin k)} (hq : Inv q)
    (h : Clean mark q) : Clean mark (RTQueue.tail q) := by
  unfold Clean
  rw [toList_tail hq]
  exact fun hm => h (List.mem_of_mem_tail hm)

/-- All preconditions consumed and restored by either queue operation. -/
structure Ready (blank mark : Fin k) (qt : QT k) (m : Mode) (q : Queue (Fin k)) : Prop where
  inv : Inv q
  clean : Clean mark q
  enc : Encodes blank mark (qt ∘ m.roles) q
  roles : Function.Injective m.roles
  phase : m.phase = phaseOf q.state

theorem enqueue_ready {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark a : Fin k} {qt : QT k} {m : Mode} {q : Queue (Fin k)}
    (hmb : mark ≠ blank) (h : Ready blank mark qt m q) (ha : a ≠ mark) :
    ∃ n qt' m', n ≤ 34 ∧ Runs Terminal code blank (enqueue blank mark a)
      qt m n qt' m' ∧ Ready blank mark qt' m' (snoc q a) := by
  obtain ⟨n, qt', m', hn, he, hr, hp, hs⟩ := enqueue_runs (Terminal := Terminal)
    hc h.roles hmb h.inv h.enc (clean_stF h.inv h.clean) (clean_front h.inv h.clean) h.phase
  exact ⟨n, qt', m', hn, he,
    ⟨inv_snoc h.inv a, clean_snoc h.inv h.clean ha, hs, hr, hp⟩⟩

theorem dequeue_ready {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark : Fin k} {qt : QT k} {m : Mode} {q : Queue (Fin k)}
    (hmb : mark ≠ blank) (h : Ready blank mark qt m q) :
    ∃ n qt' m', n ≤ 44 ∧ Runs Terminal code blank (dequeue blank mark)
      qt m n qt' m' ∧ Ready blank mark qt' m' (RTQueue.tail q) := by
  obtain ⟨n, qt', m', hn, he, hr, hp, hs⟩ := dequeue_runs (Terminal := Terminal)
    hc h.roles hmb h.enc h.inv h.phase (clean_stF h.inv h.clean) (clean_front h.inv h.clean)
  exact ⟨n, qt', m', hn, he,
    ⟨inv_tail h.inv, clean_tail h.inv h.clean, hs, hr, hp⟩⟩

/-- info: 'PalPeg.RTQueueClosed.enqueue_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms enqueue_ready

/-- info: 'PalPeg.RTQueueClosed.dequeue_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dequeue_ready

def initialMode : Mode := ⟨.idle, id⟩

theorem initial_ready (blank mark : Fin k) :
    Ready blank mark (initQT blank mark) initialMode (empty : Queue (Fin k)) := by
  refine ⟨inv_empty, ?_, initQT_encodes blank mark, Function.injective_id, rfl⟩
  exact List.not_mem_nil

/-- Read and restore the head before executing the continuation. The marker
denotes the empty queue because the closed invariant excludes it from data. -/
noncomputable def peek (blank : Fin k) (body : Fin k → CP k) : CP k :=
  select fun m => probeC blank (m.roles .front) body

theorem peek_runs {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark : Fin k} {qt qt' : QT k} {m m' : Mode} {q : Queue (Fin k)}
    {body : Fin k → CP k} {n : ℕ} (h : Ready blank mark qt m q)
    (hb : Runs Terminal code blank (body ((toList q).head?.getD mark)) qt m n qt' m') :
    Runs Terminal code blank (peek blank body) qt m (2 + n) qt' m' := by
  have hh : q.front.head? = (toList q).head? := head?_eq h.inv
  apply runs_select hc
  apply runs_probeC (qt := qt) (m := m) (ρ := m.roles .front) h.enc.front
  simpa only [hh] using hb

theorem peek_marker_iff {blank mark : Fin k} {qt : QT k} {m : Mode}
    {q : Queue (Fin k)} (h : Ready blank mark qt m q) :
    (toList q).head?.getD mark = mark ↔ toList q = [] := by
  cases hl : toList q with
  | nil => simp
  | cons a l =>
      have ha : a ≠ mark := by
        intro he; apply h.clean; rw [hl, he]; exact List.mem_cons_self
      simp [ha]

/-- info: 'PalPeg.RTQueueClosed.peek_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms peek_runs

def allowed (mark : Fin k) : Op k → Prop
  | .snoc a => a ≠ mark
  | .tail => True

noncomputable def operation (blank mark : Fin k) : Op k → CP k
  | .snoc a => enqueue blank mark a
  | .tail => dequeue blank mark

theorem operation_ready {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark : Fin k} {qt : QT k} {m : Mode} {q : Queue (Fin k)}
    (hmb : mark ≠ blank) (h : Ready blank mark qt m q)
    (op : Op k) (ha : allowed mark op) :
    ∃ n qt' m', n ≤ 44 ∧ Runs Terminal code blank (operation blank mark op)
      qt m n qt' m' ∧ Ready blank mark qt' m' (Op.applyQ q op) := by
  cases op with
  | snoc a =>
      obtain ⟨n, qt', m', hn, he, hh⟩ := enqueue_ready (Terminal := Terminal) hc hmb h ha
      exact ⟨n, qt', m', by omega, he, hh⟩
  | tail => exact dequeue_ready hc hmb h

/-- A finite sequence of public queue operations. The list supplies only the
requested operations, never internal queue states, phases or branch choices. -/
noncomputable def operations (blank mark : Fin k) : List (Op k) → CP k
  | [] => liftQ .skip
  | op :: ops => .seq (operation blank mark op) (operations blank mark ops)

theorem operations_ready {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark : Fin k} (hmb : mark ≠ blank) (ops : List (Op k))
    (ha : ∀ op ∈ ops, allowed mark op)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (h : Ready blank mark qt m q) :
    ∃ n qt' m', n ≤ 44 * ops.length ∧ Runs Terminal code blank (operations blank mark ops)
      qt m n qt' m' ∧ Ready blank mark qt' m' (ops.foldl Op.applyQ q) := by
  induction ops generalizing qt m q with
  | nil =>
      exact ⟨0, qt, m, by simp,
        runs_of_performs m (performs_skip qt), h⟩
  | cons op ops ih =>
      obtain ⟨n, qt1, m1, hn, he, h1⟩ := operation_ready (Terminal := Terminal)
        hc hmb h op (ha op (by simp))
      obtain ⟨n2, qt2, m2, hn2, he2, h2⟩ := ih
        (fun o ho => ha o (List.mem_cons_of_mem op ho)) h1
      refine ⟨n + n2, qt2, m2, ?_, runs_seq he he2, h2⟩
      simp only [List.length_cons]; omega

theorem operations_contents (ops : List (Op k)) {q : Queue (Fin k)} (hq : Inv q) :
    toList (ops.foldl Op.applyQ q) = ops.foldl Op.applyL (toList q) := by
  induction ops generalizing q with
  | nil => rfl
  | cons op ops ih =>
      cases op with
      | snoc a =>
          simpa only [List.foldl_cons, Op.applyQ, Op.applyL, toList_snoc hq] using
            ih (inv_snoc hq a)
      | tail =>
          simpa only [List.foldl_cons, Op.applyQ, Op.applyL, toList_tail hq] using
            ih (inv_tail hq)

/-- Arbitrarily many mixed operations from the initial representation, with
all runtime branch reads and mode writes charged to the linear bound. -/
theorem operations_from_empty {code : Mode → Fin k} (hc : Function.Injective code)
    (blank mark : Fin k) (hmb : mark ≠ blank) (ops : List (Op k))
    (ha : ∀ op ∈ ops, allowed mark op) :
    ∃ n qt' m' q', n ≤ 44 * ops.length ∧
      Runs Terminal code blank (operations blank mark ops)
        (initQT blank mark) initialMode n qt' m' ∧
      Ready blank mark qt' m' q' ∧ toList q' = ops.foldl Op.applyL [] := by
  obtain ⟨n, qt', m', hn, he, hh⟩ := operations_ready (Terminal := Terminal)
    hc hmb ops ha (initial_ready blank mark)
  exact ⟨n, qt', m', _, hn, he, hh, operations_contents ops inv_empty⟩

/-- info: 'PalPeg.RTQueueClosed.operations_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms operations_from_empty

end PalPeg.RTQueueClosed
