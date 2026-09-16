import PalPeg.TextFeedControl
import PalPeg.TextFeedProg2

/-! Runtime supply timing on the private-mode 19-tape implementation. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.TextFeedTiming

open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg
open PalPeg.RTQueueDispatch PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl

variable {k : ℕ} {Terminal : Type}

inductive Test where
  | blankText | enabled
  deriving DecidableEq, Fintype

abbrev TP (k : ℕ) := Prog (AP k) ((CQ k ⊕ GSProg.Cond8) ⊕ Test)

noncomputable def IT (e : Env k) : Interp Terminal (AP k) ((CQ k ⊕ GSProg.Cond8) ⊕ Test)
    (Fin k) 19 where
  actOf := (IF (Terminal := Terminal) e).actOf
  condOf
    | .inl c, σ => (IF (Terminal := Terminal) e).condOf c σ
    | .inr .blankText, σ => decide (σ (Fin.natAddEmb 11 GSTapes.tT) = e.blank)
    | .inr .enabled, σ => decide (σ (Fin.natAddEmb 11 GSTapes.tP) = e.endSym ∨
        σ (Fin.natAddEmb 11 GSTapes.tT) ≠ e.blank)

def lift (p : FP k) : TP k := Prog.map id Sum.inl p

def TExec (e : Env k) (p : TP k) (qt : QT k) (m : Mode) (S : Stage k)
    (n : ℕ) (qt' : QT k) (m' : Mode) (S' : Stage k) : Prop :=
  ∃ tr, Exec (IT (Terminal := Terminal) e) e.blank p (TextFeedControl.tapes e qt m S) tr ∧
    tr.length = n ∧ applyTrace e.blank (TextFeedControl.tapes e qt m S) tr =
      TextFeedControl.tapes e qt' m' S'

theorem texec_lift {e : Env k} {p : FP k} {qt qt' : QT k} {m m' : Mode}
    {S S' : Stage k} {n : ℕ}
    (h : Executes (Terminal := Terminal) e p qt m S n qt' m' S') :
    TExec (Terminal := Terminal) e (lift p) qt m S n qt' m' S' := by
  obtain ⟨tr, he, hn, ht⟩ := h
  exact ⟨tr, exec_map (I₂ := IT (Terminal := Terminal) e) (fa := id) (fc := Sum.inl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) he, hn, ht⟩

theorem texec_skip (e : Env k) (qt : QT k) (m : Mode) (S : Stage k) :
    TExec (Terminal := Terminal) e .skip qt m S 0 qt m S :=
  ⟨[], exec_skip _, rfl, rfl⟩

theorem texec_seq {e : Env k} {p q : TP k} {qt qt' qt'' : QT k}
    {m m' m'' : Mode} {S S' S'' : Stage k} {n n' : ℕ}
    (hp : TExec (Terminal := Terminal) e p qt m S n qt' m' S')
    (hq : TExec (Terminal := Terminal) e q qt' m' S' n' qt'' m'' S'') :
    TExec (Terminal := Terminal) e (.seq p q) qt m S (n + n') qt'' m'' S'' := by
  obtain ⟨a, ha, hna, hta⟩ := hp
  obtain ⟨b, hb, hnb, htb⟩ := hq
  refine ⟨a ++ b, exec_seq ha (hta ▸ hb), by simp [hna, hnb], ?_⟩
  rw [applyTrace_append, hta, htb]

noncomputable def supplyNonempty (blank mark : Fin k) : FP k :=
  TextFeedControl.peek blank fun a => if a = mark then liftQueue (RTQueueControl.liftQ .skip)
    else .seq (writeStage GSTapes.tT a .stay) (liftQueue (RTQueueDequeue.dequeue blank mark))

theorem supply_nonempty_runs {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {qt : QT k} {m : Mode} (M : TextFeed.Machine' k)
    (h : Ready e.blank e.mark qt m M.Q) (hb : Encodes e.blank e.mark M.R.qt M.Q)
    (hne : (toList M.Q).head?.getD e.mark ≠ e.mark) :
    ∃ n qt' m', n ≤ 47 ∧ Executes (Terminal := Terminal) e (supplyNonempty e.blank e.mark)
      qt m (GSProg.TS M.ts) n qt' m' (GSProg.TS (TextFeed.fill' e.blank e.mark M).ts) ∧
      Ready e.blank e.mark qt' m' (TextFeed.fill' e.blank e.mark M).Q := by
  obtain ⟨n, qt', m', hn, he, hh⟩ := dequeue_ready (Terminal := Terminal) hc hmb h
  have hd := executes_queue (e := e)
    (changeStage e.blank (GSProg.TS M.ts) GSTapes.tT ((toList M.Q).head?.getD e.mark) .stay) he
  have hw := executes_write (Terminal := Terminal) (e := e) qt m (GSProg.TS M.ts) GSTapes.tT
    ((toList M.Q).head?.getD e.mark) .stay
  have hp := executes_seq hw hd
  have hb' : Executes (Terminal := Terminal) e
      (if (toList M.Q).head?.getD e.mark = e.mark then liftQueue (RTQueueControl.liftQ .skip)
        else .seq (writeStage GSTapes.tT ((toList M.Q).head?.getD e.mark) .stay)
          (liftQueue (RTQueueDequeue.dequeue e.blank e.mark))) qt m (GSProg.TS M.ts) (1 + n)
      qt' m' (changeStage e.blank (GSProg.TS M.ts) GSTapes.tT
        ((toList M.Q).head?.getD e.mark) .stay) := by
    rw [if_neg hne]; exact hp
  have hx := executes_peek (body := fun a => if a = e.mark then
    liftQueue (RTQueueControl.liftQ .skip) else .seq (writeStage GSTapes.tT a .stay)
      (liftQueue (RTQueueDequeue.dequeue e.blank e.mark))) hc h hb'
  rw [legacy_supply_stage M h.inv hb] at hx
  exact ⟨2 + (1 + n), qt', m', by omega, hx, hh⟩

theorem supply_empty_runs {e : Env k} (hc : Function.Injective e.code)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (h : Ready e.blank e.mark qt m q)
    (S : Stage k) (he : (toList q).head?.getD e.mark = e.mark) :
    Executes (Terminal := Terminal) e (supplyNonempty e.blank e.mark) qt m S 2 qt m S := by
  have hs := executes_queue (e := e) S (RTQueueDequeue.runs_of_performs
    (Terminal := Terminal) (code := e.code) m (performs_skip (blank := e.blank) qt))
  unfold supplyNonempty
  apply executes_peek (n := 0) hc h
  rw [if_pos he]
  exact hs

noncomputable def fillIf (blank mark : Fin k) : TP k :=
  .ite (.inr .blankText) (lift (supplyNonempty blank mark)) .skip

theorem blankText_cond (e : Env k) (qt : QT k) (m : Mode) (S : Stage k) :
    (IT (Terminal := Terminal) e).condOf (.inr .blankText)
      (fun j => (TextFeedControl.tapes e qt m S j).focus) =
        decide ((S GSTapes.tT).focus = e.blank) := by
  simp only [IT, TextFeedControl.tapes, Fin.natAddEmb_apply, Fin.append_right]

/-- The old numeric supply predicate is realized entirely by scanner and
queue reads. Neither the arrival count nor the abstract scan state is a
parameter of the program. -/
theorem fillIf_matches {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {qt : QT k} {m : Mode} {M : TextFeed.Machine' k}
    {v Text : List (Fin k)} {rate p₁ r n : ℕ}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (h : Ready e.blank e.mark qt m M.Q)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ r n M) :
    ∃ ticks qt' m', ticks ≤ 47 ∧ TExec (Terminal := Terminal) e (fillIf e.blank e.mark)
      qt m (GSProg.TS M.ts) ticks qt' m'
        (GSProg.TS (TextFeed.fillIf' e.blank e.mark n M).ts) ∧
      Ready e.blank e.mark qt' m' (TextFeed.fillIf' e.blank e.mark n M).Q := by
  have ht : (GSProg.TS M.ts GSTapes.tT).focus = e.blank ↔ M.st.pos + M.st.q = M.m :=
    TextFeedProg2.read_tT_blank_iff hblank hn hf
  have hh : (toList M.Q).head?.getD e.mark ≠ e.mark ↔ M.m < n := by
    rw [← head?_eq h.inv]
    exact TextFeedProg2.head_ne_mark_iff hmark hn hf
  have hcond := blankText_cond (Terminal := Terminal) e qt m (GSProg.TS M.ts)
  by_cases hd : M.st.pos + M.st.q = M.m
  · have hcT : (IT (Terminal := Terminal) e).condOf (.inr .blankText)
        (fun j => (TextFeedControl.tapes e qt m (GSProg.TS M.ts) j).focus) = true := by
      rw [hcond]; exact decide_eq_true (ht.mpr hd)
    by_cases hlt : M.m < n
    · have hM : TextFeed.fillIf' e.blank e.mark n M = TextFeed.fill' e.blank e.mark M := by
        simp only [TextFeed.fillIf', hd, hlt, and_self, if_true]
      obtain ⟨ticks, qt', m', hb, he, hr⟩ := supply_nonempty_runs (Terminal := Terminal)
        hc hmb M h hf.buf (hh.mpr hlt)
      obtain ⟨tr, he, hlen, hend⟩ := texec_lift he
      refine ⟨ticks, qt', m', hb, ?_, ?_⟩
      · rw [hM]; exact ⟨tr, exec_ite_pos hcT he, hlen, hend⟩
      · rwa [hM]
    · have hM : TextFeed.fillIf' e.blank e.mark n M = M := by
        simp only [TextFeed.fillIf', hlt, and_false, if_false]
      have hhead : (toList M.Q).head?.getD e.mark = e.mark :=
        Classical.byContradiction (fun ha => hlt (hh.mp ha))
      obtain ⟨tr, he, hlen, hend⟩ := texec_lift
        (supply_empty_runs (Terminal := Terminal) hc h (GSProg.TS M.ts) hhead)
      refine ⟨2, qt, m, by omega, ?_, ?_⟩
      · rw [hM]; exact ⟨tr, exec_ite_pos hcT he, hlen, hend⟩
      · rwa [hM]
  · have hM : TextFeed.fillIf' e.blank e.mark n M = M := by
      simp only [TextFeed.fillIf', hd, false_and, if_false]
    have hcF : (IT (Terminal := Terminal) e).condOf (.inr .blankText)
        (fun j => (TextFeedControl.tapes e qt m (GSProg.TS M.ts) j).focus) = false := by
      rw [hcond]; exact decide_eq_false (fun ha => hd (ht.mp ha))
    refine ⟨0, qt, m, by omega, ?_, ?_⟩
    · rw [hM]; exact ⟨[], exec_ite_neg hcF (exec_skip _), rfl, rfl⟩
    · rwa [hM]

/-- info: 'PalPeg.TextFeedTiming.fillIf_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fillIf_matches

theorem enabled_cond {e : Env k} {qt : QT k} {m : Mode} {M : TextFeed.Machine' k}
    {v Text : List (Fin k)} {rate p₁ r n : ℕ}
    (hend : e.endSym ∉ v) (hblank : e.blank ∉ Text) (hn : n ≤ Text.length)
    (h : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ r n M)
    (hnf : ¬ (M.st.pos + M.st.q = M.m ∧ M.m < n)) :
    (IT (Terminal := Terminal) e).condOf (.inr .enabled)
      (fun j => (TextFeedControl.tapes e qt m (GSProg.TS M.ts) j).focus) =
        decide (Enabled v n M.st) := by
  have hh := TextFeedProg2.cond_enabled (Terminal := Terminal) (qt := qt) hend hblank hn h hnf
  simpa only [IT, TextFeedControl.tapes, TextFeedProg2.IFO, TextFeedProg2.tPIdx,
    TextFeedProg.tTIdx, Fin.natAddEmb_apply, Fin.append_right] using hh

/-- A single fixed online micro-iteration: fill if necessary, then run the
scanner if its pattern/text cells say that a scan step is enabled. -/
noncomputable def micro (blank mark : Fin k) (rate : ℕ) : TP k :=
  .seq (fillIf blank mark)
    (.ite (.inr .enabled) (lift (liftScan (GSProg.scanProg rate))) .skip)

theorem micro_matches {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {qt : QT k} {m : Mode} {M : TextFeed.Machine' k}
    {v Text : List (Fin k)} {rate p₁ r n : ℕ} (hk : 0 < rate)
    (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (h : Ready e.blank e.mark qt m M.Q)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ r n M) :
    ∃ ticks qt' m',
      ticks ≤ 47 + (if Enabled v n M.st then TextFeed.stepCost' v rate p₁ r Text M.st else 0) ∧
      TExec (Terminal := Terminal) e (micro e.blank e.mark rate)
        qt m (GSProg.TS M.ts) ticks qt' m'
          (GSProg.TS (TextFeed.runInT' e.blank e.endSym e.mark v rate p₁ r n Text 1 M).ts) ∧
      Ready e.blank e.mark qt' m'
        (TextFeed.runInT' e.blank e.endSym e.mark v rate p₁ r n Text 1 M).Q := by
  obtain ⟨ticks, qt1, m1, hticks, h1, hr1⟩ := fillIf_matches (Terminal := Terminal)
    hc hmb hblank hmark hn h hf
  let M1 := TextFeed.fillIf' e.blank e.mark n M
  have hM1st : M1.st = M.st := TextFeed.fillIf'_st e.blank e.mark n M
  have hf1 : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ r n M1 :=
    TextFeed.fillIf'_feedInv hmb hn hf
  have hcond := enabled_cond (Terminal := Terminal) (qt := qt1) (m := m1)
    hend hblank hn hf1 (TextFeedProg2.fillIf'_not_again e.blank e.mark n M)
  rw [hM1st] at hcond
  have hstep : TextFeed.runInT' e.blank e.endSym e.mark v rate p₁ r n Text 1 M =
      if Enabled v n M.st then TextFeed.scanOne' e.blank e.endSym e.mark v rate p₁ r Text M1
      else M1 := by
    simp only [TextFeed.runInT', TextFeed.fillIf'_st]
    rfl
  by_cases he : Enabled v n M.st
  · have hrd : M1.st.q ≠ v.length → M1.st.pos + M1.st.q < M1.m :=
      TextFeed.fillIf'_ready hf he
    have hscanA := GSProg.scanProg_exec (Terminal := Terminal) hk hmb hstart hf1.scan hf1.qle
    have hscan := texec_lift (executes_scan (e := e) qt1 m1 hscanA)
    rw [GSProg.applyTrace_avecs, GSProg.avecs_length] at hscan
    have hcost : (GSTapes.program' e.blank e.endSym e.mark rate M1.ts).length ≤
        TextFeed.stepCost' v rate p₁ r Text M.st := by
      have hx := TextFeed.scanOne'_cost hk hmb hend hn hrd hf1
      change M1.R.cost + (GSTapes.program' e.blank e.endSym e.mark rate M1.ts).length ≤ _ at hx
      rw [hM1st] at hx
      omega
    obtain ⟨tr, htr, hlen, hout⟩ := hscan
    have hs : TExec (Terminal := Terminal) e
        (.ite (.inr .enabled) (lift (liftScan (GSProg.scanProg rate))) .skip)
        qt1 m1 (GSProg.TS M1.ts) (GSTapes.program' e.blank e.endSym e.mark rate M1.ts).length
        qt1 m1 (GSProg.TS (TextFeed.scanOne' e.blank e.endSym e.mark v rate p₁ r Text M1).ts) :=
      ⟨tr, exec_ite_pos (by rw [hcond]; exact decide_eq_true he) htr, hlen, hout⟩
    refine ⟨ticks + (GSTapes.program' e.blank e.endSym e.mark rate M1.ts).length,
      qt1, m1, ?_, ?_, ?_⟩
    · rw [if_pos he]; omega
    · rw [hstep, if_pos he]; exact texec_seq h1 hs
    · rw [hstep, if_pos he]; exact hr1
  · have hs : TExec (Terminal := Terminal) e
        (.ite (.inr .enabled) (lift (liftScan (GSProg.scanProg rate))) .skip)
        qt1 m1 (GSProg.TS M1.ts) 0 qt1 m1 (GSProg.TS M1.ts) :=
      ⟨[], exec_ite_neg (by rw [hcond]; exact decide_eq_false he) (exec_skip _), rfl, rfl⟩
    refine ⟨ticks + 0, qt1, m1, ?_, ?_, ?_⟩
    · rw [if_neg he]; omega
    · rw [hstep, if_neg he]; exact texec_seq h1 hs
    · rw [hstep, if_neg he]; exact hr1

/-- info: 'PalPeg.TextFeedTiming.micro_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms micro_matches

/-- Repeat the same closed micro-program; no list of runtime role maps or
abstract queue states is supplied between iterations. -/
noncomputable def runIn (blank mark : Fin k) (rate : ℕ) : ℕ → TP k
  | 0 => .skip
  | j + 1 => .seq (runIn blank mark rate j) (micro blank mark rate)

theorem runIn_matches {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {v Text : List (Fin k)} {rate p₁ r n c : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hb : ∀ st : ScanState, st.q ≤ v.length → TextFeed.stepCost' v rate p₁ r Text st ≤ c)
    (j : ℕ) {qt : QT k} {m : Mode} {M : TextFeed.Machine' k}
    (h : Ready e.blank e.mark qt m M.Q)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ r n M) :
    ∃ ticks qt' m', ticks ≤ j * (c + 47) ∧ TExec (Terminal := Terminal) e
      (runIn e.blank e.mark rate j) qt m (GSProg.TS M.ts) ticks qt' m'
        (GSProg.TS (TextFeed.runInT' e.blank e.endSym e.mark v rate p₁ r n Text j M).ts) ∧
      Ready e.blank e.mark qt' m'
        (TextFeed.runInT' e.blank e.endSym e.mark v rate p₁ r n Text j M).Q := by
  induction j with
  | zero => exact ⟨0, qt, m, by simp, texec_skip e qt m _, h⟩
  | succ j ih =>
      obtain ⟨ticks, qt1, m1, hticks, h1, hr1⟩ := ih
      let Mj := TextFeed.runInT' e.blank e.endSym e.mark v rate p₁ r n Text j M
      have hfj : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ r n Mj :=
        TextFeed.runInT'_feedInv hmb hk hv hend hn j M hf
      obtain ⟨ticks2, qt2, m2, hticks2, h2, hr2⟩ := micro_matches (Terminal := Terminal)
        hc hmb hk hend hstart hblank hmark hn hr1 hfj
      have hstep : TextFeed.runInT' e.blank e.endSym e.mark v rate p₁ r n Text 1 Mj =
          TextFeed.runInT' e.blank e.endSym e.mark v rate p₁ r n Text (j + 1) M :=
        (TextFeedProg2.runInT'_succ_right j M).symm
      have hb2 : (if Enabled v n Mj.st then TextFeed.stepCost' v rate p₁ r Text Mj.st
          else 0) ≤ c := by
        split <;> first | exact hb _ hfj.qle | exact Nat.zero_le _
      dsimp only [Mj] at hb2
      refine ⟨ticks + ticks2, qt2, m2, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [← hstep]; exact texec_seq h1 h2
      · rw [← hstep]; exact hr2

/-- Arrival plus the fixed number of scanner iterations for a round. -/
noncomputable def round (blank mark : Fin k) (rate : ℕ) (a : Fin k) : TP k :=
  .seq (lift (liftQueue (enqueue blank mark a))) (runIn blank mark rate (gsRate rate))

theorem round_matches {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {v Text : List (Fin k)} {rate p₁ r n c : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n < Text.length)
    (hb : ∀ st : ScanState, st.q ≤ v.length → TextFeed.stepCost' v rate p₁ r Text st ≤ c)
    {qt : QT k} {m : Mode} {M : TextFeed.Machine' k} {a : Fin k}
    (ha : Text[n]? = some a) (h : Ready e.blank e.mark qt m M.Q)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ r n M) :
    ∃ ticks qt' m', ticks ≤ 34 + gsRate rate * (c + 47) ∧
      TExec (Terminal := Terminal) e (round e.blank e.mark rate a)
        qt m (GSProg.TS M.ts) ticks qt' m'
          (GSProg.TS (TextFeed.roundT' e.blank e.endSym e.mark v rate p₁ r n Text a M).ts) ∧
      Ready e.blank e.mark qt' m'
        (TextFeed.roundT' e.blank e.endSym e.mark v rate p₁ r n Text a M).Q := by
  have ham : a ≠ e.mark := fun he => hmark (he ▸ List.mem_of_getElem? ha)
  obtain ⟨ticks, qt1, m1, hticks, h1, hr1⟩ := enqueue_ready (Terminal := Terminal) hc hmb h ham
  have hf1 := TextFeed.arrive'_feedInv hmb hn ha hf
  obtain ⟨ticks2, qt2, m2, hticks2, h2, hr2⟩ := runIn_matches (Terminal := Terminal)
    hc hmb hk hv hend hstart hblank hmark (by omega : n + 1 ≤ Text.length) hb (gsRate rate) hr1 hf1
  exact ⟨ticks + ticks2, qt2, m2, by omega,
    texec_seq (texec_lift (executes_queue (GSProg.TS M.ts) h1)) h2, hr2⟩

/-- info: 'PalPeg.TextFeedTiming.runIn_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runIn_matches

/-- info: 'PalPeg.TextFeedTiming.round_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms round_matches

end PalPeg.TextFeedTiming
