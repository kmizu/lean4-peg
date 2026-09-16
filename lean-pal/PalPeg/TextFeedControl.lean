import PalPeg.RTQueueClosed
import PalPeg.ProgLangChoice
import PalPeg.GSScanProg
import PalPeg.TextFeed

/-! Text supply using the queue's private finite mode, on 11 + 8 tapes.
The scanner's original instructions are retained alongside literal writes. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.TextFeedControl

open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg
open PalPeg.RTQueueDispatch PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.GSProg (Act8 Cond8 I8)

variable {k : ℕ} {Terminal : Type}

structure Env (k : ℕ) where
  code : Mode → Fin k
  blank : Fin k
  mark : Fin k
  endSym : Fin k
  startSym : Fin k

abbrev Lit8 (k : ℕ) := Fin 8 × Fin k × Move
abbrev AS (k : ℕ) := Act8 ⊕ Lit8 k
abbrev AP (k : ℕ) := (ActQ k ⊕ Mode) ⊕ AS k
abbrev CQ (k : ℕ) := CondQ k ⊕ Mode
abbrev FP (k : ℕ) := Prog (AP k) (CQ k ⊕ Cond8)
abbrev Stage (k : ℕ) := Fin 8 → STape (Fin k)

def IS (e : Env k) : Interp Terminal (AS k) Cond8 (Fin k) 8 where
  actOf
    | .inl a => (I8 e.blank e.endSym e.mark e.startSym).actOf a
    | .inr (i, a, mv) => fun _ σ => touchVec i a mv σ
  condOf := (I8 (Terminal := Terminal) e.blank e.endSym e.mark e.startSym).condOf

noncomputable def IF (e : Env k) := Interp.sum (IC Terminal e.code) (IS (Terminal := Terminal) e)

def tapes (e : Env k) (qt : QT k) (m : Mode) (S : Stage k) :=
  Fin.append (RTQueueControl.tapes e.code qt m) S

def liftQueue (p : CP k) : FP k := Prog.map Sum.inl Sum.inl p
def liftStage (p : Prog (AS k) Cond8) : FP k := Prog.map Sum.inr Sum.inr p
def liftScan (p : Prog Act8 Cond8) : FP k := liftStage (Prog.map Sum.inl id p)

def Executes (e : Env k) (p : FP k) (qt : QT k) (m : Mode) (S : Stage k)
    (n : ℕ) (qt' : QT k) (m' : Mode) (S' : Stage k) : Prop :=
  ∃ tr, Exec (IF (Terminal := Terminal) e) e.blank p (tapes e qt m S) tr ∧
    tr.length = n ∧ applyTrace e.blank (tapes e qt m S) tr = tapes e qt' m' S'

theorem executes_queue {e : Env k} {p : CP k} {qt qt' : QT k} {m m' : Mode}
    {n : ℕ} (S : Stage k) (h : Runs Terminal e.code e.blank p qt m n qt' m') :
    Executes (Terminal := Terminal) e (liftQueue p) qt m S n qt' m' S := by
  obtain ⟨tr, he, hn, ht⟩ := h
  have hh := exec_sum_inl (I2 := IS (Terminal := Terminal) e) he (tapes e qt m S)
  rw [tapes, extend_castAdd_append] at hh
  refine ⟨_, hh, by simp [hn], ?_⟩
  have ha := applyTrace_extend (Fin.castAddEmb 8) e.blank (tapes e qt m S) tr
    (RTQueueControl.tapes e.code qt m)
  simp only [tapes, extend_castAdd_append, ht] at ha
  exact ha

theorem executes_stage {e : Env k} {p : Prog (AS k) Cond8} {S : Stage k}
    {tr : List (Fin 8 → Fin k × Move)} (qt : QT k) (m : Mode)
    (h : Exec (IS (Terminal := Terminal) e) e.blank p S tr) :
    Executes (Terminal := Terminal) e (liftStage p) qt m S tr.length
      qt m (applyTrace e.blank S tr) := by
  have hh := exec_sum_inr (I1 := IC Terminal e.code) h (tapes e qt m S)
  rw [tapes, extend_natAdd_append] at hh
  refine ⟨_, hh, by simp, ?_⟩
  have ha := applyTrace_extend (Fin.natAddEmb 11) e.blank (tapes e qt m S) tr S
  simp only [tapes, extend_natAdd_append] at ha
  exact ha

theorem executes_scan {e : Env k} {p : Prog Act8 Cond8} {S : Stage k}
    {tr : List (Fin 8 → Fin k × Move)} (qt : QT k) (m : Mode)
    (h : Exec (I8 (Terminal := Terminal) e.blank e.endSym e.mark e.startSym) e.blank p S tr) :
    Executes (Terminal := Terminal) e (liftScan p) qt m S tr.length
      qt m (applyTrace e.blank S tr) := by
  apply executes_stage qt m
  exact exec_map (I₂ := IS (Terminal := Terminal) e) (fa := Sum.inl) (fc := id)
    (fun _ _ => rfl) (fun _ _ _ => rfl) h

theorem executes_seq {e : Env k} {p q : FP k} {qt qt' qt'' : QT k}
    {m m' m'' : Mode} {S S' S'' : Stage k} {n n' : ℕ}
    (hp : Executes (Terminal := Terminal) e p qt m S n qt' m' S')
    (hq : Executes (Terminal := Terminal) e q qt' m' S' n' qt'' m'' S'') :
    Executes (Terminal := Terminal) e (.seq p q) qt m S (n + n') qt'' m'' S'' := by
  obtain ⟨a, ha, hna, hta⟩ := hp
  obtain ⟨b, hb, hnb, htb⟩ := hq
  refine ⟨a ++ b, exec_seq ha (hta ▸ hb), by simp [hna, hnb], ?_⟩
  rw [applyTrace_append, hta, htb]

def changeStage (blank : Fin k) (S : Stage k) (i : Fin 8) (a : Fin k) (mv : Move) : Stage k :=
  Function.update S i ((S i).applyAction blank (a, mv))

def writeStage (i : Fin 8) (a : Fin k) (mv : Move) : FP k :=
  liftStage (.act (.inr (i, a, mv)))

theorem executes_write {e : Env k} (qt : QT k) (m : Mode) (S : Stage k)
    (i : Fin 8) (a : Fin k) (mv : Move) :
    Executes (Terminal := Terminal) e (writeStage i a mv) qt m S 1
      qt m (changeStage e.blank S i a mv) := by
  have he := exec_act (I := IS (Terminal := Terminal) e) (blank := e.blank)
    (fun a _ _ => by cases a <;> rfl) (.inr (i, a, mv)) S
  have hh := executes_stage qt m he
  have ht : applyTrace e.blank S [actVec (IS (Terminal := Terminal) e) (.inr (i, a, mv)) S]
      = changeStage e.blank S i a mv := by
    funext j
    by_cases hj : j = i
    · subst j; simp [applyTrace, actVec, IS, touchVec, changeStage]
    · simp [applyTrace, actVec, IS, touchVec, changeStage, hj]
  simpa only [writeStage, List.length_singleton, ht] using hh

noncomputable def selectMode (body : Mode → FP k) : FP k :=
  choose (fun m => .inl (.inr m)) body

theorem executes_select {e : Env k} (hc : Function.Injective e.code)
    {body : Mode → FP k} {qt qt' : QT k} {m m' : Mode} {S S' : Stage k} {n : ℕ}
    (h : Executes (Terminal := Terminal) e (body m) qt m S n qt' m' S') :
    Executes (Terminal := Terminal) e (selectMode body) qt m S n qt' m' S' := by
  obtain ⟨tr, he, hn, ht⟩ := h
  refine ⟨tr, exec_choose ?_ he, hn, ht⟩
  intro a
  change decide (e.code m = e.code a) = decide (m = a)
  simp only [hc.eq_iff]

noncomputable def readQueue (ρ : Role) (body : Fin k → FP k) : FP k :=
  choose (fun a => .inl (.inl (ρ, a))) body

theorem executes_read {e : Env k} {ρ : Role} {body : Fin k → FP k}
    {qt qt' : QT k} {m m' : Mode} {S S' : Stage k} {n : ℕ}
    (h : Executes (Terminal := Terminal) e (body (qt ρ).focus) qt m S n qt' m' S') :
    Executes (Terminal := Terminal) e (readQueue ρ body) qt m S n qt' m' S' := by
  obtain ⟨tr, he, hn, ht⟩ := h
  refine ⟨tr, exec_choose ?_ he, hn, ht⟩
  intro a
  simp only [IF, Interp.sum, Interp.transport, IC, IQ, tapes, RTQueueControl.tapes,
    Fin.castAddEmb_apply, Fin.append_left, TSQ_focus, role_ridx]

noncomputable def probe (blank : Fin k) (ρ : Role) (body : Fin k → FP k) : FP k :=
  .seq (liftQueue (RTQueueControl.liftQ (.act (ρ, blank, .left))))
    (readQueue ρ fun a =>
      .seq (liftQueue (RTQueueControl.liftQ (.act (ρ, a, .right)))) (body a))

theorem executes_probe {e : Env k} {ρ : Role} {body : Fin k → FP k}
    {qt qt' : QT k} {m m' : Mode} {S S' : Stage k} {n : ℕ} {l : List (Fin k)}
    (hs : SStack e.blank e.mark (qt ρ) l)
    (hb : Executes (Terminal := Terminal) e (body (l.head?.getD e.mark)) qt m S n qt' m' S') :
    Executes (Terminal := Terminal) e (probe e.blank ρ body) qt m S (2 + n) qt' m' S' := by
  let qt1 := run e.blank qt [⟨ρ, e.blank, .left⟩]
  have hr : (qt1 ρ).focus = l.head?.getD e.mark := by
    simp only [qt1, run_cons, run_nil, act_apply]
    exact sstack_probe hs
  have hrestore : run e.blank qt1 [⟨ρ, l.head?.getD e.mark, .right⟩] = qt :=
    probePrefix_restore hs
  have h1 := executes_queue S (runs_lift (code := e.code) (m := m)
    (execQ_act (Terminal := Terminal) (blank := e.blank) ρ e.blank .left qt))
  have h2 := executes_queue S (runs_lift (code := e.code) (m := m)
    (execQ_act (Terminal := Terminal) (blank := e.blank) ρ (l.head?.getD e.mark) .right qt1))
  rw [hrestore] at h2
  have hc : Executes (Terminal := Terminal) e
      (readQueue ρ fun a => .seq (liftQueue (RTQueueControl.liftQ (.act (ρ, a, .right))))
        (body a)) qt1 m S (1 + n) qt' m' S' := by
    apply executes_read
    rw [hr]
    exact executes_seq h2 hb
  simpa only [probe, List.length_singleton, ← Nat.add_assoc] using executes_seq h1 hc

noncomputable def peek (blank : Fin k) (body : Fin k → FP k) : FP k :=
  selectMode fun m => probe blank (m.roles .front) body

theorem executes_peek {e : Env k} (hc : Function.Injective e.code)
    {body : Fin k → FP k} {qt qt' : QT k} {m m' : Mode} {S S' : Stage k} {n : ℕ}
    {q : Queue (Fin k)} (h : Ready e.blank e.mark qt m q)
    (hb : Executes (Terminal := Terminal) e (body ((toList q).head?.getD e.mark))
      qt m S n qt' m' S') :
    Executes (Terminal := Terminal) e (peek e.blank body) qt m S (2 + n) qt' m' S' := by
  apply executes_select hc
  apply executes_probe (qt := qt) (m := m) (ρ := m.roles .front) h.enc.front
  have hh : q.front.head? = (toList q).head? := head?_eq h.inv
  simpa only [hh] using hb

/-- Supply the queue head to a scanner tape, then remove it from the queue.
For the empty queue the marker is written; callers that require data prove
nonemptiness through their FIFO invariant. -/
noncomputable def supply (blank mark : Fin k) (out : Fin 8) (mv : Move) : FP k :=
  peek blank fun a => .seq (writeStage out a mv)
    (liftQueue (RTQueueDequeue.dequeue blank mark))

theorem supply_runs {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {qt : QT k} {m : Mode} {q : Queue (Fin k)}
    (h : Ready e.blank e.mark qt m q) (S : Stage k) (out : Fin 8) (mv : Move) :
    ∃ n qt' m', n ≤ 47 ∧ Executes (Terminal := Terminal) e (supply e.blank e.mark out mv)
      qt m S n qt' m' (changeStage e.blank S out ((toList q).head?.getD e.mark) mv) ∧
      Ready e.blank e.mark qt' m' (RTQueue.tail q) := by
  obtain ⟨n, qt', m', hn, he, hh⟩ := dequeue_ready (Terminal := Terminal) hc hmb h
  have hd := executes_queue (e := e)
    (changeStage e.blank S out ((toList q).head?.getD e.mark) mv) he
  have hw := executes_write (Terminal := Terminal) (e := e) qt m S out
    ((toList q).head?.getD e.mark) mv
  have hb := executes_seq hw hd
  exact ⟨2 + (1 + n), qt', m', by omega, executes_peek hc h hb, hh⟩

/-- One arrival followed by supply to the scanner and advance to the right.
Both the post-arrival queue mode and the symbol supplied are read internally. -/
noncomputable def feedRound (blank mark a : Fin k) : FP k :=
  .seq (liftQueue (enqueue blank mark a)) (supply blank mark PalPeg.GSTapes.tT .right)

theorem feedRound_runs {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {qt : QT k} {m : Mode} {q : Queue (Fin k)} {a : Fin k}
    (h : Ready e.blank e.mark qt m q) (ha : a ≠ e.mark) (S : Stage k) :
    ∃ n qt' m', n ≤ 81 ∧ Executes (Terminal := Terminal) e (feedRound e.blank e.mark a)
      qt m S n qt' m'
        (changeStage e.blank S PalPeg.GSTapes.tT ((toList q ++ [a]).head?.getD e.mark) .right) ∧
      Ready e.blank e.mark qt' m' (RTQueue.tail (snoc q a)) := by
  obtain ⟨n, qt1, m1, hn, h1, hh1⟩ := enqueue_ready (Terminal := Terminal) hc hmb h ha
  obtain ⟨n2, qt2, m2, hn2, h2, hh2⟩ := supply_runs (Terminal := Terminal) hc hmb hh1
    S PalPeg.GSTapes.tT .right
  rw [toList_snoc h.inv] at h2
  exact ⟨n + n2, qt2, m2, by omega, executes_seq (executes_queue S h1) h2, hh2⟩

/-- The exposed FIFO effect of one feed round. -/
theorem feedRound_contents {q : Queue (Fin k)} (h : Inv q) (a : Fin k) :
    toList (RTQueue.tail (snoc q a)) = (toList q ++ [a]).tail := by
  rw [toList_tail (inv_snoc h a), toList_snoc h]

/-- info: 'PalPeg.TextFeedControl.executes_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms executes_scan

/-- info: 'PalPeg.TextFeedControl.supply_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms supply_runs

/-- info: 'PalPeg.TextFeedControl.feedRound_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms feedRound_runs

/-- The fused scanner write/right step is exactly the scanner effect of the
existing supply specification, including the symbol obtained after arrival. -/
theorem legacy_round_stage {e : Env k} (hmb : e.mark ≠ e.blank)
    (M : TextFeed.Machine' k) (a : Fin k) (hq : Inv M.Q)
    (hb : Encodes e.blank e.mark M.R.qt M.Q) :
    changeStage e.blank (GSProg.TS M.ts) GSTapes.tT
        ((toList M.Q ++ [a]).head?.getD e.mark) .right =
      GSProg.TS (TextFeed.startRound' e.blank e.mark a M).ts := by
  have hh : TextFeed.peek e.blank (snocT e.blank e.mark M.Q a M.R) =
      (toList M.Q ++ [a]).head?.getD e.mark := by
    have hr := headT_read (snocT_encodes (a := a) hmb hb hq)
    rw [head?_eq (inv_snoc hq a), toList_snoc hq] at hr
    exact hr
  funext j
  by_cases hj : j = GSTapes.tT
  · subst j
    simp only [changeStage, Function.update_self, GSProg.TS,
      TextFeed.startRound', TextFeed.stepRight', TextFeed.fill', TextFeed.arrive',
      GSTapes.upd_self, hh, GSProg.toS_step]
    rfl
  · simp only [changeStage, Function.update_of_ne hj, GSProg.TS,
      TextFeed.startRound', TextFeed.stepRight', TextFeed.fill', TextFeed.arrive',
      GSTapes.upd_ne _ _ hj]

/-- Refinement of the established text-supply specification. Queue tapes need
only encode the same abstract queue; physical role rotation is kept internal. -/
theorem feedRound_matches {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {qt : QT k} {m : Mode} (M : TextFeed.Machine' k)
    (a : Fin k) (ha : a ≠ e.mark) (h : Ready e.blank e.mark qt m M.Q)
    (hb : Encodes e.blank e.mark M.R.qt M.Q) :
    ∃ n qt' m', n ≤ 81 ∧ Executes (Terminal := Terminal) e (feedRound e.blank e.mark a)
      qt m (GSProg.TS M.ts) n qt' m'
        (GSProg.TS (TextFeed.startRound' e.blank e.mark a M).ts) ∧
      Ready e.blank e.mark qt' m' (TextFeed.startRound' e.blank e.mark a M).Q := by
  obtain ⟨n, qt', m', hn, he, hh⟩ := feedRound_runs (Terminal := Terminal)
    hc hmb h ha (GSProg.TS M.ts)
  rw [legacy_round_stage hmb M a h.inv hb] at he
  exact ⟨n, qt', m', hn, he, hh⟩

/-- info: 'PalPeg.TextFeedControl.feedRound_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms feedRound_matches

theorem inputFree_IF (e : Env k) : InputFree (IF (Terminal := Terminal) e) := by
  rintro ((a | m) | (a | lit)) x σ <;> rfl

theorem legacy_supply_stage {e : Env k} (M : TextFeed.Machine' k) (hq : Inv M.Q)
    (hb : Encodes e.blank e.mark M.R.qt M.Q) :
    changeStage e.blank (GSProg.TS M.ts) GSTapes.tT
        ((toList M.Q).head?.getD e.mark) .stay =
      GSProg.TS (TextFeed.fill' e.blank e.mark M).ts := by
  have hh : TextFeed.peek e.blank M.R = (toList M.Q).head?.getD e.mark := by
    have hr := headT_read hb
    rw [head?_eq hq] at hr
    exact hr
  funext j
  by_cases hj : j = GSTapes.tT
  · subst j
    simp only [changeStage, Function.update_self, GSProg.TS, TextFeed.fill',
      GSTapes.upd_self, hh, GSProg.toS_step]
  · simp only [changeStage, Function.update_of_ne hj, GSProg.TS, TextFeed.fill',
      GSTapes.upd_ne _ _ hj]

theorem supply_matches {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {qt : QT k} {m : Mode} (M : TextFeed.Machine' k)
    (h : Ready e.blank e.mark qt m M.Q) (hb : Encodes e.blank e.mark M.R.qt M.Q) :
    ∃ n qt' m', n ≤ 47 ∧
      Executes (Terminal := Terminal) e (supply e.blank e.mark GSTapes.tT .stay)
        qt m (GSProg.TS M.ts) n qt' m' (GSProg.TS (TextFeed.fill' e.blank e.mark M).ts) ∧
      Ready e.blank e.mark qt' m' (TextFeed.fill' e.blank e.mark M).Q := by
  obtain ⟨n, qt', m', hn, he, hh⟩ := supply_runs (Terminal := Terminal)
    hc hmb h (GSProg.TS M.ts) GSTapes.tT .stay
  rw [legacy_supply_stage M h.inv hb] at he
  exact ⟨n, qt', m', hn, he, hh⟩

/-- info: 'PalPeg.TextFeedControl.supply_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms supply_matches

end PalPeg.TextFeedControl
