import PalPeg.GSPreprocessProg74

/-! # Concrete execution of the finite shared-tape preparation -/
set_option autoImplicit false
namespace PalPeg.PrepInstance
open PegSeparation.RealTimeTM PalPeg.PatternTapes PalPeg.PatternProg PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark leftSym : Fin sc}
  {w Text : List (Fin sc)} {L : ℕ} {S : Tapes sc}

theorem finitePrep_exec_normalized (hmb : mark ≠ blank)
    (hpre : StageTapes.PrepPre blank mark leftSym L w Text S)
    (hstart : startSym ∉ PrepInstances.stagePat w L)
    (hend : endSym ∉ PrepInstances.stagePat w L) (hne : startSym ≠ endSym) :
    let x := PrepInstances.stagePat w L
    let d := decompose2 x 8
    ∃ trace R,
      Exec (prepInterp (Terminal := Terminal) blank endSym mark) blank
        (finitePrep blank startSym endSym leftSym mark 8) (TSg S) trace ∧
      applyTrace blank (TSg S) trace = TSg R ∧
      Tape.CounterView' blank mark (R sC1) (if d.2.1 = 0 then x.length - d.1 + 1 else d.2.1) ∧
      Tape.CounterView' blank mark (R sRp) (if d.2.1 = 0 then 0 else d.2.2) ∧
      Tape.StackView blank (R sP) [] ∧ Tape.StackView blank (R sU) [] ∧
      SetupPre blank mark leftSym (PrepInstances.prepRes w L).1 L
        (PrepInstances.prepRes w L).2.1 (PrepInstances.prepRes w L).2.2 w Text R ∧
      trace.length ≤ (GSPreProg.preprocessSlope + 16) * L +
        GSPreProg.preprocessOffset + 23 := by
  dsimp only
  obtain ⟨ea, hi, ht, hx, hin⟩ :=
    finitePrologue_spec (Terminal := Terminal) hpre hstart hend hne
  obtain ⟨b, eb, he, hb⟩ := GSPreProg.DECOMPOSE_eight_linear (Terminal := Terminal) hend hmb hi
  rw [← prj_run] at he
  obtain ⟨c, ec, hc, hr, hp, hu, hf, hl⟩ :=
    finiteEpilogue_spec (Terminal := Terminal) _ hmb hne hstart hend
      (GSPre.pat_le he.base.v1) he.base.v1 he.base.v2 he.base.cp he.base.cr
  refine ⟨_, _, exec_shared_seq ea eb ec, applyTrace_shared_seq _ _ _ _ _, hc, hr, hp, hu, ?_, ?_⟩
  · refine
      { hpos := hpre.hpos
        hle := hpre.hle
        hcut := PrepInstances.prep_cut_lt hpre.hpos hpre.hle
        inb := ?_
        emptyU := hu
        emptyP := hp
        txt := ?_
        txt2 := ?_
        cs := ?_
        c1 := ?_
        c2 := ?_
        ap := ?_
        an := ?_
        rp := ?_
        rn := ?_ }
    · simp only [PatternTapes.run]
      rw [hf sIn (by decide) (by decide) (by decide) (by decide)]
      have hframe := run_liftActs_other blank b
        (runG blank (finitePrologueActs blank startSym endSym L) S) sIn (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)
      simp only [PatternTapes.run] at hframe
      rw [hframe]
      exact hin
    · simp only [PatternTapes.run]
      rw [hf sT (by decide) (by decide) (by decide) (by decide)]
      have hframe := run_liftActs_other blank b
        (runG blank (finitePrologueActs blank startSym endSym L) S) sT (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)
      simp only [PatternTapes.run] at hframe
      rw [hframe, ht]
      exact hpre.txt
    · simp only [PatternTapes.run]
      rw [hf sX2 (by decide) (by decide) (by decide) (by decide)]
      have hframe := run_liftActs_other blank b
        (runG blank (finitePrologueActs blank startSym endSym L) S) sX2 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)
      simp only [PatternTapes.run] at hframe
      rw [hframe, hx]
      exact hpre.txt2
    · simp only [PatternTapes.run] at *
      rw [hf sCs (by decide) (by decide) (by decide) (by decide)]
      exact he.base.cs
    · simpa only [PrepInstances.prepRes, PrepInstances.rawRes, effPeriod,
        List.length_drop, PatternTapes.run] using hc
    · simp only [PatternTapes.run] at *
      rw [hf sC2 (by decide) (by decide) (by decide) (by decide)]
      exact he.base.cd
    · simp only [PatternTapes.run] at *
      rw [hf sAp (by decide) (by decide) (by decide) (by decide)]
      exact he.base.cq
    · simp only [PatternTapes.run] at *
      rw [hf sAn (by decide) (by decide) (by decide) (by decide)]
      exact he.base.ce
    · simpa only [PrepInstances.prepRes, PrepInstances.rawRes, effReach, PatternTapes.run] using hr
    · simp only [PatternTapes.run] at *
      rw [hf sRn (by decide) (by decide) (by decide) (by decide)]
      exact he.base.cf
  rw [shared_trace_length, finitePrologueActs_length]
  rw [PrepInstances.stagePat_length hpre.hle] at hb hl
  have hreach : (decompose2 (PrepInstances.stagePat w L) 8).2.2 ≤ L := by
    have H := PrepInstances.prep_core w L
    by_cases hz : (PrepInstances.rawRes w L).2.1 = 0
    · have hr0 := (H.none_case hz).1
      change (PrepInstances.rawRes w L).2.2 ≤ L
      omega
    · have hrle := (H.reach hz).1
      rw [List.length_drop, PrepInstances.stagePat_length hpre.hle] at hrle
      change (PrepInstances.rawRes w L).2.2 ≤ L
      omega
  nlinarith only [hb, hl, hreach]

/-- info: 'PalPeg.PrepInstance.finitePrep_exec_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finitePrep_exec_normalized

end PalPeg.PrepInstance
