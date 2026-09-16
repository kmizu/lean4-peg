import PalPeg.TextFeedDeadline

/-! A deadline witness on the actual finite feeder's stable scanner tapes. -/
set_option autoImplicit false

namespace PalPeg.TextFeedRefine
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.GSProg
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedAtomic
open PalPeg.TextFeedSchedule PalPeg.TextFeedScan

variable {k : ℕ} {Terminal : Type}

/-- Stable reports are visible through the same scanner-symbol projection
used by the implemented finite worker's conditions. -/
theorem sim_fill_report {e : Env k} {v Text : List (Fin k)} {R rate p₁ rem n : ℕ}
    {M : TextFeed.Machine' k} {x : Phys e R rate} {old : Fin k}
    (hend : e.endSym ∉ v) (h : Sim e v Text R rate p₁ rem n M .fill x old) :
    stageSymbols (fun j => (x.2 j).focus) GSTapes.tP = e.endSym ↔ M.st.q = v.length := by
  obtain ⟨qt, m, ht, _⟩ := h.tapes
  rw [ht, stageSymbols_rtapes]
  exact TextFeedProg2.read_tP_end_iff hend h.reference.qle h.reference.scan

/-- Given the proved frontier credit, a real fixed-size worker window
contains a stable occurrence report on its physical scanner tapes. -/
theorem worker_window_deadline {e : Env k} (hcode : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {v Text : List (Fin k)} {R rate p₁ rem n : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hK : KSimple v rate p₁ rem)
    {M : TextFeed.Machine' k} {ph : Phase} {x : Phys e R rate} {old : Fin k} {i : ℕ}
    (h : Sim e v Text R rate p₁ rem n M ph x old) (hcounter : x.1.1.1.val = 1)
    (hs : ScanInv v Text M.st) (hocc : OccAt v Text i) (hpos : M.st.pos ≤ i)
    (hd : i + v.length = n) (hno : ¬ Hit v i M)
    (hc : workScale rate * ((rate + 1) * n) ≤
      workCredit v rate (modelRun e v Text rate p₁ rem n R M ph)) :
    ∃ j, 1 ≤ j ∧ j ≤ R ∧
      stageSymbols (fun t => (((TextFeedSchedule.run (Terminal := Terminal) e R rate)^[j] x).2 t).focus)
        GSTapes.tP = e.endSym ∧
      ∃ M', Hit v i M' ∧ Sim e v Text R rate p₁ rem n M' .fill
        ((TextFeedSchedule.run (Terminal := Terminal) e R rate)^[j] x) old := by
  have hw : WorkInv e v Text rate p₁ rem n (M, ph) := ⟨h.reference, h.work⟩
  have hex := modelRun_reports_of_credit hk hmb hv hend hstart hblank hn hK R hw hs hocc hpos hd hc
  obtain ⟨j, hj1, hjR, hh, hphase⟩ := modelRun_stable_report hno hex
  have hjpos : j ≠ 0 → 0 < x.1.1.1.val := by omega
  have hjlen : x.1.1.1.val + j ≤ R + 1 := by omega
  have hjSim := worker_steps (Terminal := Terminal) hcode hmb hk hv hend hstart hblank hmark hn
    j h hjpos hjlen
  change Sim e v Text R rate p₁ rem n (modelRun e v Text rate p₁ rem n j M ph).1
    (modelRun e v Text rate p₁ rem n j M ph).2 _ old at hjSim
  rw [hphase] at hjSim
  exact ⟨j, hj1, hjR, (sim_fill_report hend hjSim).mpr hh.2, _, hh, hjSim⟩

/-- The macrocall sequence of an actual arrival-bearing frame contains
the physical report by its deadline. The arrival hook captures the real
terminal; the enqueue call is included in the prefix index j+1. -/
theorem frame_deadline {e : Env k} (hcode : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {v Text : List (Fin k)} {R rate p₁ rem n : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n < Text.length)
    (hK : KSimple v rate p₁ rem) (hR : workRate rate ≤ R)
    (enc : Terminal → Fin k) (a : Terminal) (ha : Text[n]? = some (enc a))
    {M : TextFeed.Machine' k} {ph : Phase} {x : Phys e R rate} {old : Fin k} {i : ℕ}
    (h : Sim e v Text R rate p₁ rem n M ph x old)
    (hcounter : x.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    (hs : ScanInv v Text M.st) (hocc : OccAt v Text i) (hpos : M.st.pos ≤ i)
    (hd : i + v.length = n + 1)
    (hc : workScale rate * ((rate + 1) * n) ≤ workCredit v rate (M, ph)) :
    let captured : Phys e R rate :=
      (x.1, ProgLangPersist2.arriveA e.blank (capture enc) (some a) x.2)
    ∃ j, 1 ≤ j ∧ j ≤ R ∧
      stageSymbols (fun t =>
        (((TextFeedSchedule.run (Terminal := Terminal) e R rate)^[j + 1] captured).2 t).focus)
        GSTapes.tP = e.endSym := by
  let captured : Phys e R rate :=
    (x.1, ProgLangPersist2.arriveA e.blank (capture enc) (some a) x.2)
  have hcap := capture_sim h enc a
  have harr := arrival_step (Terminal := Terminal) hcode hmb hmark hn ha hcap hcounter
  have hw : WorkInv e v Text rate p₁ rem n (M, ph) := ⟨h.reference, h.work⟩
  have hcredit := (frame_work_credit hk hK.period_pos hmb hv hend hstart hblank hn hR ha hw hc).2
  have hRpos : 0 < R := by
    have hh : 0 < workRate rate := by unfold workRate workScale; positivity
    omega
  have hcount : (TextFeedSchedule.run (Terminal := Terminal) e R rate captured).1.1.1.val = 1 := by
    rw [run_counter]
    change (nextPhase x.1.1.1).val = 1
    rw [hcounter]
    simp only [nextPhase, dif_pos (show (0 : ℕ) + 1 < R + 1 by omega)]
  have hno : ¬ Hit v i (TextFeed.arrive' e.blank e.mark (enc a) M) :=
    workInv_not_hit_before (M := M) (v := v) (i := i) (n := n) hw (by omega)
  obtain ⟨j, hj1, hjR, hmarker, _⟩ := worker_window_deadline (Terminal := Terminal)
    hcode hmb hk hv hend hstart hblank hmark (by omega : n + 1 ≤ Text.length)
    hK harr hcount hs hocc hpos hd hno hcredit
  refine ⟨j, hj1, hjR, ?_⟩
  simpa only [Function.iterate_succ_apply] using hmarker

/-- The per-frame credit and no-skipping premises follow from the proved
online execution, rather than being fresh deadline assumptions. -/
theorem online_frame_deadline {e : Env k} (hcode : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {v Text : List (Fin k)} {R rate p₁ rem n : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n < Text.length)
    (hK : KSimple v rate p₁ rem) (hR : workRate rate ≤ R)
    (enc : Terminal → Fin k) (a : Terminal) (ha : Text[n]? = some (enc a))
    {M₀ : TextFeed.Machine' k} {ph₀ : Phase} {x : Phys e R rate} {old : Fin k} {i : ℕ}
    (h₀ : WorkInv e v Text rate p₁ rem 0 (M₀, ph₀)) (hs₀ : ScanInv v Text M₀.st)
    (h : Sim e v Text R rate p₁ rem n
      (onlineWork e v Text R rate p₁ rem M₀ ph₀ n).1
      (onlineWork e v Text R rate p₁ rem M₀ ph₀ n).2 x old)
    (hcounter : x.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    (hocc : OccAt v Text i) (hpos₀ : M₀.st.pos ≤ i) (hd : i + v.length = n + 1) :
    let captured : Phys e R rate :=
      (x.1, ProgLangPersist2.arriveA e.blank (capture enc) (some a) x.2)
    ∃ j, 1 ≤ j ∧ j ≤ R ∧
      stageSymbols (fun t =>
        (((TextFeedSchedule.run (Terminal := Terminal) e R rate)^[j + 1] captured).2 t).focus)
        GSTapes.tP = e.endSym := by
  have hs := onlineWork_scanInv (e := e) (ph₀ := ph₀) hK R hs₀ n
  have hpos := onlineWork_no_skip_before hk hmb hv hend hstart hblank hK hR h₀ hs₀
    hocc hpos₀ n (by omega) (by omega)
  have hc := (onlineWork_credit hk hK.period_pos hmb hv hend hstart hblank hR h₀ n (by omega)).2
  exact frame_deadline hcode hmb hk hv hend hstart hblank hmark hn hK hR enc a ha
    h hcounter hs hocc hpos hd hc

/-- info: 'PalPeg.TextFeedRefine.online_frame_deadline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms online_frame_deadline

end PalPeg.TextFeedRefine
