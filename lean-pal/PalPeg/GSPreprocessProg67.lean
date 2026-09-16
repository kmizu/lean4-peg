import PalPeg.GSPreprocessProg66
import PalPeg.PrepInstance

/-! # Finite decomposition after the stage prologue

The witness is an execution of `DECOMPOSE 8`, not the older `decProg`
trace. Projection transports its result to the fifteen stage tapes.
-/
set_option autoImplicit false
namespace PalPeg.PrepInstance
open PegSeparation.RealTimeTM PalPeg.PatternTapes PalPeg.GSPreProg
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark leftSym : Fin sc}
  {w Text : List (Fin sc)} {L : ℕ} {ts : Tapes sc}

theorem finite_decompose_after_prologue (hmb : mark ≠ blank)
    (hend : endSym ∉ PrepInstances.stagePat w L)
    (hpre : StageTapes.PrepPre blank mark leftSym L w Text ts) :
    let x := PrepInstances.stagePat w L
    let pre := prologueProg blank startSym endSym L ts
    let T1 := run blank pre ts
    ∃ acts : List (GSPre.Act sc),
      ExecA Terminal blank endSym mark (DECOMPOSE 8) (prj T1) acts ∧
      GSPre.EncS blank startSym endSym mark x (decompose2 x 8).1 (decompose2 x 8).1
        ⟨0, 0, 0, (decompose2 x 8).2.1, 0, (decompose2 x 8).1, (decompose2 x 8).2.2⟩
        ⟨0, 0, 0⟩ (prj (run blank (pre ++ acts.map liftAct) ts)) ∧
      run blank (pre ++ acts.map liftAct) ts sT = ts sT ∧
      run blank (pre ++ acts.map liftAct) ts sX2 = ts sX2 ∧
      Tape.SeqView blank (run blank (pre ++ acts.map liftAct) ts sIn)
        (leftSym :: w.take L) L ∧
      (pre ++ acts.map liftAct).length ≤
        (preprocessSlope + 6) * L + (preprocessOffset + 6) := by
  dsimp only
  let pre := prologueProg blank startSym endSym L ts
  let T1 := run blank pre ts
  obtain ⟨he, ht, hx2, hi⟩ := prologue_spec (startSym := startSym) (endSym := endSym) hpre
  obtain ⟨acts, hex, hout, hlen⟩ :=
    DECOMPOSE_eight_linear (Terminal := Terminal) hend hmb he
  have hother (j : Fin 15) (hj : j = sT ∨ j = sX2 ∨ j = sIn) :
      run blank (pre ++ acts.map liftAct) ts j = T1 j := by
    rw [run_append]
    rcases hj with rfl | rfl | rfl <;>
      exact run_liftActs_other blank acts T1 _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  refine ⟨acts, hex, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_append, prj_run]; exact hout
  · rw [hother sT (Or.inl rfl)]; exact ht
  · rw [hother sX2 (Or.inr (Or.inl rfl))]; exact hx2
  · rw [hother sIn (Or.inr (Or.inr rfl))]; exact hi
  · rw [List.length_append, List.length_map, prologueProg_length hpre.hpos]
    rw [PrepInstances.stagePat_length hpre.hle] at hlen
    nlinarith only [hlen]

/-- The finite core can replace the old core in the semantic preparation
contract. This theorem does not yet assert finite syntax for the prologue
or epilogue. -/
theorem finite_decompose_setup (hmb : mark ≠ blank)
    (hend : endSym ∉ PrepInstances.stagePat w L)
    (hpre : StageTapes.PrepPre blank mark leftSym L w Text ts) :
    let pre := prologueProg blank startSym endSym L ts
    ∃ acts : List (GSPre.Act sc),
      ExecA Terminal blank endSym mark (DECOMPOSE 8) (prj (run blank pre ts)) acts ∧
      SetupPre blank mark leftSym (PrepInstances.prepRes w L).1 L
        (PrepInstances.prepRes w L).2.1 (PrepInstances.prepRes w L).2.2 w Text
        (run blank
          (pre ++ acts.map liftAct ++ epilogueProg blank mark L
            (PrepInstances.rawRes w L).1 (run blank (pre ++ acts.map liftAct) ts)) ts) := by
  dsimp only
  obtain ⟨acts, hex, he, ht, hx2, hi, _hlen⟩ :=
    finite_decompose_after_prologue (Terminal := Terminal) hmb hend hpre
  let x := PrepInstances.stagePat w L
  let s := (PrepInstances.rawRes w L).1
  let pre := prologueProg blank startSym endSym L ts
  let T2 := run blank (pre ++ acts.map liftAct) ts
  change T2 sT = ts sT at ht
  change T2 sX2 = ts sX2 at hx2
  have hout : GSPre.Enc blank startSym endSym mark x (decompose2 x 8).1
      (decompose2 x 8).1
      ⟨0, 0, 0, (decompose2 x 8).2.1, 0, (decompose2 x 8).1, (decompose2 x 8).2.2⟩
      (prj T2) := he.base
  have hxlen : x.length = L := PrepInstances.stagePat_length hpre.hle
  have hpwlen : (GSPre.pword startSym endSym x).length = L + 2 := by
    rw [GSPre.pword_length, hxlen]
  obtain ⟨eC1, eRp, eC2, eAp, eAn, eRn, eP, eU, eT, eX2, eIn, eCs, _⟩ :=
    epilogue_spec (blank := blank) (mark := mark) (L := L) (s := s) (ts := T2)
      (decompose2 x 8).2.1 (decompose2 x 8).2.2 0 0 0
      ((decompose2 x 8).1 + 1) ((decompose2 x 8).1 + 1)
      (GSPre.pword startSym endSym x) (GSPre.pword startSym endSym x)
      hout.cp hout.cr hout.cd hout.cq hout.ce hout.cf hout.v1 hpwlen hout.v2 hpwlen
  have hpr : PrepInstances.prepRes w L =
      ((decompose2 x 8).1, effPeriod (x.drop (decompose2 x 8).1) (decompose2 x 8).2.1,
        effReach (decompose2 x 8).2.1 (decompose2 x 8).2.2) := rfl
  refine ⟨acts, hex, ?_⟩
  rw [run_append]
  refine
    { hpos := hpre.hpos
      hle := hpre.hle
      hcut := PrepInstances.prep_cut_lt hpre.hpos hpre.hle
      inb := ?_
      emptyU := eU
      emptyP := eP
      txt := ?_
      txt2 := ?_
      cs := ?_
      c1 := ?_
      c2 := eC2
      ap := eAp
      an := eAn
      rp := ?_
      rn := eRn }
  · rw [eIn]; exact hi
  · rw [eT, ht]; exact hpre.txt
  · rw [eX2, hx2]; exact hpre.txt2
  · rw [eCs, hpr]; exact hout.cs
  · rw [hpr, effPeriod]
    have hvlen : (x.drop (decompose2 x 8).1).length = L - (decompose2 x 8).1 := by
      rw [List.length_drop, hxlen]
    rw [hvlen]; exact eC1
  · rw [hpr, effReach]; exact eRp

/-- info: 'PalPeg.PrepInstance.finite_decompose_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite_decompose_setup
/-- info: 'PalPeg.PrepInstance.finite_decompose_after_prologue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite_decompose_after_prologue
end PalPeg.PrepInstance
