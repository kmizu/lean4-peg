import PalPeg.TextFeedStageUnpadded

/-! Deadline reports are observations of the actual unpadded machine,
not assertions restricted to its padded proof representative. -/
set_option autoImplicit false

namespace PalPeg.TextFeedStageStartup
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist2
open PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedPrepare
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule PalPeg.TextFeedPrepEndpoint
open PalPeg.TextFeedRefine

variable {k : ℕ} {Terminal : Type}
noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem observed_ready_deadline {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {leftSym : Fin k} {v : List (Fin k)} {R rate p₁ rem base : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (enc : Terminal → Fin k) (input : List Terminal)
    (hblank : e.blank ∉ input.map enc) (hmark : e.mark ∉ input.map enc)
    (hK : KSimple v rate p₁ rem) (hR : workRate rate ≤ R)
    {x : TextFeedWorkerBridge.Phys e leftSym R rate}
    (hready : ObservedReady e leftSym R rate v (input.map enc) p₁ rem base x)
    {i n : ℕ} (hn : base + n < input.length) (hocc : OccAt v (input.map enc) i)
    (hd : i + v.length = base + n + 1) (a : Terminal) (ha : input[base + n]? = some a) :
    let u := TextFeedWorkerBridge.workerRun e leftSym enc R rate x ((input.drop base).take n)
    let captured : TextFeedWorkerBridge.Phys e leftSym R rate :=
      (u.state.1.1, arriveA e.blank (TextFeedStartupSchedule.capture enc) (some a) u.tape)
    ∃ j, 1 ≤ j ∧ j ≤ R ∧
      TextFeedSchedule.stageSymbols (fun t =>
        (((run (Terminal := Terminal) e leftSym R rate)^[j + 1] captured).2 (feedSlot t)).focus)
        GSTapes.tP = e.endSym := by
  obtain ⟨y, hctrl, ht, hstream⟩ := hready
  have hy : y = (x.1, y.2) := Prod.ext hctrl.symm rfl
  rw [hy] at hstream
  obtain ⟨yold, M, ph, q, old, hl, hr, hi, hcredit, hs, hp, hyc, _⟩ := hstream
  obtain ⟨j, hj1, hjR, hreport⟩ := TextFeedWorkerBridge.workerRun_offset_deadline hc hmb hk hv
    hend hstart enc input hblank hmark hK hR hl hr hi hyc hcredit hs hn hocc (hp i hocc) hd a ha
  have hh := TextFeedStartupUnpadded.prefixRun_blankEq e leftSym enc R rate x.1 ht
    ((input.drop base).take n) a (j + 1)
  have hheads :
      (fun t => ((prefixRun e leftSym enc R rate x.1 x.2 ((input.drop base).take n) a (j + 1)).2
        (feedSlot t)).focus) =
      (fun t => ((prefixRun e leftSym enc R rate x.1 y.2 ((input.drop base).take n) a (j + 1)).2
        (feedSlot t)).focus) := funext fun t => (hh.2 (feedSlot t)).focus
  refine ⟨j, hj1, hjR, ?_⟩
  change TextFeedSchedule.stageSymbols
    (fun t => ((prefixRun e leftSym enc R rate x.1 x.2 ((input.drop base).take n) a (j + 1)).2
      (feedSlot t)).focus) GSTapes.tP = e.endSym
  rw [hheads]
  exact hreport

/-- info: 'PalPeg.TextFeedStageStartup.observed_ready_deadline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms observed_ready_deadline

end PalPeg.TextFeedStageStartup
