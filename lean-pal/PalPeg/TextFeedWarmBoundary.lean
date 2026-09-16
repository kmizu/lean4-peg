import PalPeg.TextFeedWorkerStream
import PalPeg.TextFeedPrepared

/-! Finish the physical remainder of the startup frame. No arrival is
repeated and the prepared worker is not restarted at a fabricated boundary. -/
set_option autoImplicit false

namespace PalPeg.TextFeedWarmBoundary
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist2
open PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.TextFeedInput
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule PalPeg.TextFeedStartupSafety
open PalPeg.TextFeedRefine

variable {k : ℕ} {Terminal : Type}

theorem remaining_window {R J : ℕ} (hJ : J < R) :
    let c := nextPhase^[J + 2] (⟨0, Nat.zero_lt_succ R⟩ : Fin (R + 1))
    let N := R - J - 1
    (N ≠ 0 → 0 < c.val) ∧ c.val + N ≤ R + 1 ∧
      nextPhase^[N] c = ⟨0, Nat.zero_lt_succ R⟩ := by
  dsimp only
  have hsum : R - J - 1 + (J + 2) = R + 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro hn
    rw [nextPhase_iterate (Nat.zero_lt_succ R) (J + 2) (by omega)]
    exact Nat.zero_lt_succ _
  · by_cases hj : J + 2 = R + 1
    · rw [hj, nextPhase_iterate_round]
      omega
    · rw [nextPhase_iterate (Nat.zero_lt_succ R) (J + 2) (by omega)]
      change J + 2 + (R - J - 1) ≤ R + 1
      omega
  · rw [← Function.iterate_add_apply, hsum, nextPhase_iterate_round]

theorem delay_before_first {rate n len : ℕ} (hlen : 0 < len)
    (hd : (rate + 1) * n ≤ rate * len) : n < len := by
  nlinarith

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _
noncomputable local instance : DecidableEq (AP k ⊕ Empty) := Classical.decEq _
noncomputable local instance : DecidableEq (CT k ⊕ Fin k) := Classical.decEq _

/-- Everything needed to start the continuous deadline theorem is
preserved while finishing the last partial frame, including the fact that
no future occurrence has already been skipped during those worker calls. -/
theorem finish_frame {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {leftSym : Fin k} {v Text : List (Fin k)} {R rate p₁ rem n J : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hK : KSimple v rate p₁ rem) (hJ : J < R) (hearly : n < v.length)
    {M : TextFeed.Machine' k} {ph : Phase}
    {x : TextFeedWorkerBridge.Phys e leftSym R rate} {y : Phys e R rate} {old : Fin k}
    (hl : TextFeedWorkerBridge.Link e leftSym R rate x y)
    {q : RTQueue.Queue (Fin k)} (hq : ReadyAt e x.2 q old) (ha : old ≠ e.mark)
    (hsim : Sim e v Text R rate p₁ rem n M ph y old)
    (hcount : y.1.1.1 = nextPhase^[J + 2] ⟨0, Nat.zero_lt_succ R⟩)
    (hcredit : workScale rate * ((rate + 1) * n) ≤ workCredit v rate (M, ph))
    (hscan : ScanInv v Text M.st) (hpos : M.st.pos = 0) :
    let N := R - J - 1
    let x' := (run (Terminal := Terminal) e leftSym R rate)^[N] x
    let y' := (TextFeedSchedule.run (Terminal := Terminal) e R rate)^[N] y
    let m := modelRun e v Text rate p₁ rem n N M ph
    TextFeedWorkerBridge.Link e leftSym R rate x' y' ∧
      (∃ q', ReadyAt e x'.2 q' old) ∧
      Sim e v Text R rate p₁ rem n m.1 m.2 y' old ∧
      workScale rate * ((rate + 1) * n) ≤ workCredit v rate m ∧
      ScanInv v Text m.1.st ∧ (∀ i, OccAt v Text i → m.1.st.pos ≤ i) ∧
      x'.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩ ∧ y'.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩ := by
  have hw : WorkInv e v Text rate p₁ rem n (M, ph) := ⟨hsim.reference, hsim.work⟩
  obtain ⟨hpositive, hlen, hendphase⟩ := remaining_window hJ
  rw [← hcount] at hpositive hlen hendphase
  have hsim' := worker_steps (Terminal := Terminal) hc hmb hk hv hend hstart hblank hmark hn
    (R - J - 1) hsim hpositive hlen
  obtain ⟨hl', hr⟩ := TextFeedWorkerBridge.run_link_iterate (Terminal := Terminal)
    hc hmb hl hq ha (R - J - 1)
  have hmono := modelRun_work_mono hk hK.period_pos hmb hv hend hstart hblank hn (R - J - 1) hw
  have hcredit' : workScale rate * ((rate + 1) * n) ≤
      workCredit v rate (modelRun e v Text rate p₁ rem n (R - J - 1) M ph) :=
    hcredit.trans (Nat.add_le_add_right hmono _)
  have hycount : ((TextFeedSchedule.run (Terminal := Terminal) e R rate)^[R - J - 1] y).1.1.1 =
      ⟨0, Nat.zero_lt_succ R⟩ := by
    rw [TextFeedSchedule.run_counter_iterate]
    exact hendphase
  refine ⟨hl', hr, hsim', hcredit', modelRun_scanInv hK _ hscan, ?_,
    hl'.ctrl.counter.trans hycount, hycount⟩
  intro i hi
  apply modelRun_no_skip hK hk _ hscan hi (by omega)
  intro j _
  exact workInv_not_hit_before
    (modelRun_workInv hk hmb hv hend hstart hblank hn j hw) (by omega)

/-- info: 'PalPeg.TextFeedWarmBoundary.finish_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finish_frame

end PalPeg.TextFeedWarmBoundary
