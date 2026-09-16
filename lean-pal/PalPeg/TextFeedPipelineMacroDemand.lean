import PalPeg.GSVerifierDemandZ
import PalPeg.TextFeedPipelineInputMacro

/-! An enabled concrete GS macro cannot encounter a genuine input
barrier, even when its execution began before the current arrival. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineMacroDemand
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.ProgLangDemand PalPeg.ProgLangHeadMoves PalPeg.GSVerifierHeadMoves
open PalPeg.TextFeedPipelineDemand PalPeg.TextFeedPipelineIdealEngine
open PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineCoupled PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelineInputMacro PalPeg.TextFeedPipelineMacroResult
open PalPeg.TextFeedPipelineSupplyCost PalPeg.VerifierFeedRefinement
open PalPeg.GSVTapes PalPeg.GSVTapesZ PalPeg.GSVProgZLoop PalPeg.GSVerifierZ
open PalPeg.GSVerifierDemand PalPeg.GSVerifierDemandZ
variable {k : ℕ}

theorem advance_certified (e : Env k) (n : ℕ) (T : VTapes' k) (up : Bool)
    (h₁ : (T.1 PalPeg.GSTapes.tT).left.length < n) (h₂ : T.2.Txt2.left.length ≤ n) :
    Certified e n [lift (GSVProg.pmap PalPeg.GSProg.advProg)] (tapes e.blank e.mark T up)
      (tapes e.blank e.mark
        (vApplyActs' e.blank ((PalPeg.GSTapes.advActs e.blank e.mark T.1).map VAct'.S) T) up) := by
  obtain ⟨as, he, ht, hc₁, hc₂⟩ := lift_bounded
    (GSVProg.execV_lift (PalPeg.GSProg.advProg_exec (Terminal := Unit) (blank := e.blank)
      (endSym := e.endSym) (mark := e.mark) (startSym := e.startSym) T.1)) up
  simp only [text_map_S, adv_one, verify_map_S] at hc₁ hc₂
  have hp : Allowed (fun _ : A => True) noTextGuard (lift (GSVProg.pmap PalPeg.GSProg.advProg)) := by
    simp [Allowed, noTextGuard, lift, GSVProg.pmap, Prog.map, GSVProg.fc,
      PalPeg.GSProg.advProg, PalPeg.GSProg.KEEP, PalPeg.GSProg.PUT, PalPeg.GSProg.qIncProg,
      PalPeg.GSProg.sUpProg, PalPeg.GSProg.sUpTail]
  have hb : reserve n (tapes e.blank e.mark T up) as := by
    change (T.1 PalPeg.GSTapes.tT).left.length + count txt1 as ≤ n ∧
      T.2.Txt2.left.length + count txt2 as ≤ n
    omega
  simpa only [ht] using counts_certified he hp hb

/-- Source-level demand safety of the entire real step program, not just
its action list. Both match tests and every zigzag comparison are checked. -/
theorem step_certified {e : Env k} {leftPat rightPat Word : List (Fin k)} {rate p r n : ℕ}
    {T : VTapes' k} {z : VStateZ}
    (hrate : 0 < rate) (hmb : e.mark ≠ e.blank) (hstart : e.startSym ∉ rightPat)
    (hpat : 0 < rightPat.length) (hendu : e.endSym ∉ leftPat) (hstartu : e.startSym ∉ leftPat)
    (hse : e.startSym ≠ e.endSym)
    (hE : VEncodesZ' e.blank e.startSym e.endSym e.mark leftPat rightPat Word rate p r T z)
    (hq : z.1.q ≤ rightPat.length) (hwf : ZWf leftPat.length z.2)
    (hpos : leftPat.length ≤ z.1.pos) (hfront : z.1.pos + z.1.q ≤ n)
    (hen : PalPeg.Enabled rightPat n z.1) :
    Certified e n [stepProg rate] (tapes e.blank e.mark T z.2.up)
      (tapes e.blank e.mark (vApplyActs' e.blank
        (vprogramZ' e.blank e.startSym e.endSym e.mark rate z.2.up T) T)
        (vDirZ e.blank e.startSym e.endSym z.2.up T)) := by
  have hi₁ := PalPeg.TextFeedPipelineMacroFit.seq_left_length hE.scan.txt
  have hi₂ := PalPeg.TextFeedPipelineMacroFit.seq_left_length hE.txt2
  have hX : T.2.Txt2.left.length ≤ z.1.pos := by rw [hi₂]; have hh := hwf.1; omega
  have hp : z.1.pos < n := by rcases hen with hen | hen <;> omega
  have hg : condReady e.endSym n (tapes e.blank e.mark T z.2.up) (.inl .matchOk) := by
    rcases hen with hen | hen
    · exact Or.inl (PalPeg.GSTapes.read_P_end' hE.scan hen)
    · exact Or.inr (hi₁ ▸ hen)
  unfold stepProg
  apply Checked.branch hg
  by_cases hadv : Tape.read (T.1 PalPeg.GSTapes.tP) ≠ e.endSym ∧
      Tape.read (T.1 PalPeg.GSTapes.tP) = Tape.read (T.1 PalPeg.GSTapes.tT)
  · have hc : evalConds (engine e) (fun j => (tapes e.blank e.mark T z.2.up j).focus) (.inl .matchOk) = true := by
      change (interp (Terminal := Unit) e.blank e.endSym e.mark e.startSym).condOf _ _ = true
      rw [cond_lift, GSVProg.matchOk_eq]
      exact decide_eq_true hadv
    rw [hc]
    simp only [↓reduceIte]
    have ht : (T.1 PalPeg.GSTapes.tT).left.length < n := hg.resolve_left hadv.1
    let V := vApplyActs' e.blank ((PalPeg.GSTapes.advActs e.blank e.mark T.1).map VAct'.S) T
    have hV2 : V.2 = T.2 := by dsimp only [V]; rw [vApplyActs'_map_S]
    have hscan : Certified e n [lift (GSVProg.pmap (PalPeg.GSProg.scanProg rate))]
        (tapes e.blank e.mark T z.2.up) (tapes e.blank e.mark V z.2.up) := by
      simp only [PalPeg.GSProg.scanProg, GSVProg.pmap, lift, Prog.map]
      apply Checked.branch hg
      rw [hc]
      exact advance_certified e n T z.2.up ht (hX.trans (Nat.le_of_lt hp))
    have hroom : z.1.pos < Word.length := by have hh := hE.scan.txt.lt; omega
    have hu := units_certified hendu hstartu hse hpos hroom hp zQuota z.2 V z.2.up hwf
      (by simpa only [hV2] using hE.pat) (by simpa only [hV2] using hE.txt2)
    have hdir : Certified e n [.ite (.inr .up) (unitsReturn zQuota true) (unitsReturn zQuota false)]
        (tapes e.blank e.mark V z.2.up)
        (tapes e.blank e.mark
          (vApplyActs' e.blank ((zUnits e.blank e.startSym e.endSym zQuota z.2.up V.2).map liftAct) V)
          (zDirN e.blank e.startSym e.endSym zQuota z.2.up V.2)) := by
      apply Checked.branch trivial
      have hd : evalConds (engine e) (fun j => (tapes e.blank e.mark V z.2.up j).focus) (.inr .up) = z.2.up :=
        cond_up e.blank e.endSym e.mark e.startSym hmb V z.2.up
      rw [hd]
      cases he : z.2.up <;> simpa [he] using hu
    have h := Checked.seq (hscan.append hdir)
    rw [hV2] at h
    simpa only [vprogramZ', vDirZ, if_pos hadv, List.map_append, vApplyActs'_append, V] using h
  · have hc : evalConds (engine e) (fun j => (tapes e.blank e.mark T z.2.up j).focus) (.inl .matchOk) = false := by
      change (interp (Terminal := Unit) e.blank e.endSym e.mark e.startSym).condOf _ _ = false
      rw [cond_lift, GSVProg.matchOk_eq]
      exact decide_eq_false hadv
    rw [hc]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hs := shift_certified hrate hmb hstart hpat hE.scan hq hfront hX hen z.2.up
    have hd := direction_certified e n
      (vApplyActs' e.blank (GSVProg.shiftCoreActs e.blank e.mark rate T) T) z.2.up false
    simpa only [PalPeg.GSVProgZ.vprogramZ'_shift e.blank e.startSym e.endSym e.mark rate z.2.up T hadv,
      vDirZ, if_neg hadv] using Checked.seq (hs.append hd)

/-- Enablement is needed at the current frontier, not at macro start.
An earlier input wait may already have been released by intervening arrivals. -/
theorem macro_not_barrier {e : Env k} (leftSym : Fin k) (R rate : ℕ)
    {Text leftPat rightPat : List (Fin k)} {p r n₀ n : ℕ} {z : VStateZ}
    {u v : Snapshot k} {ws : List Event}
    (hu : Refines e Text n₀ u.model u.ideal u.i1 u.i2)
    (hs : Start e Text leftPat rightPat rate p r n₀ u z)
    (hc : Conditions e Text leftPat rightPat rate p r z) (hpat : 0 < rightPat.length)
    (hn₀ : n₀ ≤ n) (hen : PalPeg.Enabled rightPat n z.1) (h : Follows e u ws v)
    (x : Config e leftSym R rate) (caller : Stack (TaskAct k) (TaskCond k))
    (hv : Valid e leftSym R rate Text n x v caller) (hn : n ≤ Text.length) :
    ¬ Barrier n v (next (taskEval e (fun j => (x.2 j).focus)) v.frames).1
      (next (taskEval e (fun j => (x.2 j).focus)) v.frames).2 := by
  obtain ⟨he, hq, _, hp⟩ := initial_encoding hu hs.feed hs.ghost
  have hfront₀ : z.1.pos + z.1.q ≤ n₀ := by
    have hh := hs.feed.hd1.trans hs.feed.m1le
    simpa only [hs.ghost] using hh
  have hcert := step_certified hc.positive_rate hc.mark_blank hc.start_right hpat hc.end_left
    hc.start_left hc.start_end he hq hs.wf hp (hfront₀.trans hn₀) hen
  have heq : tapes e.blank e.mark u.ideal z.2.up = bundle u.ideal u.dir := by rw [hs.direction]; rfl
  rw [heq] at hcert
  have hcode : erase u.frames = [stepProg rate] := by
    simp only [hs.code, erase, eraseFrame, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [← hcode] at hcert
  exact certified_not_barrier leftSym R rate x v caller hv hc.mark_blank hc.blank_text hc.mark_text hn
    (follows_certified hcert h)

/-- info: 'PalPeg.TextFeedPipelineMacroDemand.macro_not_barrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms macro_not_barrier

end PalPeg.TextFeedPipelineMacroDemand
