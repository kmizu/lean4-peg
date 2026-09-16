import PalPeg.GSPreprocessProg75

/-! # Finite preparation followed by finite scanner setup -/
set_option autoImplicit false
namespace PalPeg.PrepInstance
open PegSeparation.RealTimeTM PalPeg.PatternTapes PalPeg.PatternProg PalPeg.ProgLang
open PalPeg.PatternProg.Fifteen
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark leftSym : Fin sc}
  {w Text : List (Fin sc)} {L : ℕ} {S : Tapes sc}

theorem setupPre_to_prepPreL {s p r : ℕ}
    (H : SetupPre blank mark leftSym s L p r w Text S) (hf : leftSym ∉ w) :
    PrepPreL blank mark leftSym s L p r (w.take L) Text S where
  hpos := H.hpos
  hle := by rw [List.length_take_of_le H.hle]
  hcut := H.hcut
  hfresh := fun hm => hf (List.mem_of_mem_take hm)
  inb := H.inb
  emptyU := H.emptyU
  emptyP := H.emptyP
  txt := H.txt
  txt2 := H.txt2
  cs := H.cs
  c1 := H.c1
  c2 := H.c2
  ap := H.ap
  an := H.an
  rp := H.rp
  rn := H.rn

theorem prepRes_period_le (hw : L ≤ w.length) :
    (PrepInstances.prepRes w L).2.1 ≤ L + 1 := by
  have hp := PrepInstances.prep_kp_raw hw
  change effPeriod ((PrepInstances.stagePat w L).drop (PrepInstances.rawRes w L).1)
    (PrepInstances.rawRes w L).2.1 ≤ L + 1
  unfold effPeriod
  split_ifs
  · rw [List.length_drop, PrepInstances.stagePat_length hw]
    omega
  · omega

def finitePrepSetup (blank startSym endSym leftSym mark : Fin sc) (k : ℕ) :
    Prog (PrepAct sc) (PrepCond sc) :=
  .seq (finitePrep blank startSym endSym leftSym mark 8)
    ((setupProgL blank startSym endSym mark leftSym k).map Sum.inr Sum.inr)

theorem finitePrepSetup_exec (k : ℕ) (hmb : mark ≠ blank)
    (hpre : StageTapes.PrepPre blank mark leftSym L w Text S)
    (hstart : startSym ∉ PrepInstances.stagePat w L)
    (hend : endSym ∉ PrepInstances.stagePat w L) (hne : startSym ≠ endSym) :
    let d := PrepInstances.prepRes w L
    ∃ trace R,
      Exec (prepInterp (Terminal := Terminal) blank endSym mark) blank
        (finitePrepSetup blank startSym endSym leftSym mark k) (TSg S) trace ∧
      applyTrace blank (TSg S) trace = TSg R ∧
      GSVTapes.VEncodes' blank startSym endSym mark
        ((w.take L).reverse.take d.1) ((w.take L).reverse.drop d.1)
        (TextFeed.padW blank Text 0) k d.2.1 d.2.2
        (toGS R, toVExt R) (⟨0, 0⟩, 0) ∧
      trace.length ≤ (GSPreProg.preprocessSlope + 25 + 7 * k) * L +
        GSPreProg.preprocessOffset + 37 + 11 * k := by
  dsimp only
  obtain ⟨a, R, ea, ha, _hc, _hr, _hp, _hu, H, hlen⟩ :=
    finitePrep_exec_normalized (Terminal := Terminal) hmb hpre hstart hend hne
  have H' := setupPre_to_prepPreL H hpre.hfresh
  have hs : startSym ∉ w.take L := by
    simpa only [PrepInstances.stagePat, List.mem_reverse] using hstart
  obtain ⟨⟨eb, hb⟩, hv⟩ := setupProgL_spec (Terminal := Terminal) (k := k) H' hmb hs hne
  let b := setupProgLActs blank startSym endSym (PrepInstances.prepRes w L).1
    (L - (PrepInstances.prepRes w L).1) k (PrepInstances.prepRes w L).2.1
  refine ⟨a ++ gavecs blank b R,
    setupTapesL blank startSym endSym (PrepInstances.prepRes w L).1
      (L - (PrepInstances.prepRes w L).1) k R, ?_, ?_, ?_, ?_⟩
  · apply exec_seq ea
    rw [ha]
    exact aux_exec_shared eb
  · rw [applyTrace_append, ha, applyTrace_gavecs, hb]
  · simpa only [List.take_take, Nat.min_self] using hv
  · rw [List.length_append, gavecs_length, setupProgL_trace_length]
    have hcut := H.hcut
    have hsub : L - (PrepInstances.prepRes w L).1 + (PrepInstances.prepRes w L).1 = L := by omega
    have hp := Nat.mul_le_mul_left k (prepRes_period_le hpre.hle)
    nlinarith only [hlen, hsub, hp]

/-- info: 'PalPeg.PrepInstance.finitePrepSetup_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finitePrepSetup_exec
end PalPeg.PrepInstance
