import PalPeg.GSVerifierDemand

/-! Demand certificates for the zigzag comparison branch. Its Txt2 head
stays in the already arrived left window, including turns within a quota. -/
set_option autoImplicit false

namespace PalPeg.GSVerifierDemandZ
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.ProgLangDemand PalPeg.TextFeedPipelineDemand PalPeg.TextFeedPipelineIdealEngine
open PalPeg.TextFeedPipelineFrames PalPeg.GSVTapes PalPeg.GSVTapesZ PalPeg.GSVProgZLoop
variable {k : ℕ}

theorem atom_certified {e : Env k} {n : ℕ} {a : A} {T U : Fin 11 → STape (Fin k)}
    (hr : RunsTo (engine e) e.blank (.act a) T U 1) (ha : actReady n T a) :
    Certified e n [.act a] T U := by
  obtain ⟨as, he, ht, hl⟩ := hr
  obtain ⟨_, s, hs, _⟩ := he [] [none] (by simp [hl])
  have hh := congrArg Prod.snd hs
  simp only [List.singleton_append, runInputs_cons, runInputs_nil, microStep, stepStack_act] at hh
  change action (engine e) e.blank T a = applyTrace e.blank T as at hh
  rw [← hh] at ht
  rw [← ht]
  exact .act ha (.done _)

theorem keepU_certified (e : Env k) (n : ℕ) (T : VTapes' k) (old : Bool) (m : Move) :
    Certified e n [lift (GSVProg.KEEP10 GSVProg.tU m)] (tapes e.blank e.mark T old)
      (tapes e.blank e.mark (vApplyActs' e.blank [VAct'.U m] T) old) := by
  apply atom_certified (lift_runsTo
    (GSVProg.execV_keepU (Terminal := Unit) (blank := e.blank) (endSym := e.endSym)
      (mark := e.mark) (startSym := e.startSym) m T) old)
  intro _
  exact ⟨fun h => False.elim ((by decide : GSVProg.tU ≠ GSVProg.e8 PalPeg.GSTapes.tT) h),
    fun h => False.elim ((by decide : GSVProg.tU ≠ GSVProg.tX) h)⟩

theorem keepX_certified (e : Env k) (n : ℕ) (T : VTapes' k) (old : Bool) (m : Move)
    (hx : m = .right → T.2.Txt2.left.length < n) :
    Certified e n [lift (GSVProg.KEEP10 GSVProg.tX m)] (tapes e.blank e.mark T old)
      (tapes e.blank e.mark (vApplyActs' e.blank [VAct'.X m] T) old) := by
  apply atom_certified (lift_runsTo
    (GSVProg.execV_keepX (Terminal := Unit) (blank := e.blank) (endSym := e.endSym)
      (mark := e.mark) (startSym := e.startSym) m T) old)
  intro hr
  exact ⟨fun h => False.elim ((by decide : GSVProg.tX ≠ GSVProg.e8 PalPeg.GSTapes.tT) h),
    fun _ => hx hr⟩

theorem direction_certified (e : Env k) (n : ℕ) (T : VTapes' k) (old up : Bool) :
    Certified e n [setDir up] (tapes e.blank e.mark T old) (tapes e.blank e.mark T up) :=
  atom_certified (setDir_runsTo e.blank e.endSym e.mark e.startSym T old up) trivial

theorem comp_certified (e : Env k) (n : ℕ) (T : VTapes' k) (old : Bool)
    (hx : T.2.Txt2.left.length < n) :
    Certified e n [lift GSVProg.vcompProg] (tapes e.blank e.mark T old)
      (tapes e.blank e.mark (vApplyActs' e.blank ((vcompActs e.endSym T.2).map liftAct) T) old) := by
  have hr : condReady e.endSym n (tapes e.blank e.mark T old) (.inl .compOk) := Or.inr hx
  by_cases hc : Tape.read T.2.U ≠ e.endSym ∧ Tape.read T.2.U = Tape.read T.2.Txt2
  · have he : evalConds (engine e) (fun j => (tapes e.blank e.mark T old j).focus) (.inl .compOk) = true := by
      change (interp (Terminal := Unit) e.blank e.endSym e.mark e.startSym).condOf _ _ = true
      rw [cond_lift, GSVProg.compOk_eq]
      exact decide_eq_true hc
    have hU := keepU_certified e n T old .right
    have hX := keepX_certified e n (vApplyActs' e.blank [VAct'.U .right] T) old .right (fun _ => hx)
    have h := Checked.branch (blank := e.blank) (okA := actReady n) hr
      (p := .seq (lift (GSVProg.KEEP10 GSVProg.tU .right))
      (lift (GSVProg.KEEP10 GSVProg.tX .right))) (q := .skip) (s := [])
      (by rw [he]; exact Checked.seq (hU.append hX))
    simpa only [GSVProg.vcompProg, lift, Prog.map, vcompActs, if_pos hc, List.map_cons,
      List.map_nil, liftAct, vApplyActs'_cons, vApplyActs'_nil] using h
  · have he : evalConds (engine e) (fun j => (tapes e.blank e.mark T old j).focus) (.inl .compOk) = false := by
      change (interp (Terminal := Unit) e.blank e.endSym e.mark e.startSym).condOf _ _ = false
      rw [cond_lift, GSVProg.compOk_eq]
      exact decide_eq_false hc
    have h := Checked.branch (blank := e.blank) (okA := actReady n) hr
      (p := .seq (lift (GSVProg.KEEP10 GSVProg.tU .right))
      (lift (GSVProg.KEEP10 GSVProg.tX .right))) (q := .skip) (s := [])
      (by rw [he]; exact Checked.skip (Checked.done (tapes e.blank e.mark T old)))
    simpa only [GSVProg.vcompProg, lift, Prog.map, vcompActs, if_neg hc, List.map_nil, vApplyActs'_nil] using h

open PalPeg.GSVerifierZ

theorem units_certified {e : Env k} {u Word : List (Fin k)} {pos frontier : ℕ}
    (hendu : e.endSym ∉ u) (hstartu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (hpos : u.length ≤ pos) (hroom : pos < Word.length) (hfront : pos < frontier) :
    ∀ (N : ℕ) (zz : ZS) (T : VTapes' k) (old : Bool), ZWf u.length zz →
      Tape.SeqView e.blank T.2.U (e.startSym :: (u ++ [e.endSym])) (zz.head + 1) →
      Tape.SeqView e.blank T.2.Txt2 Word (pos - u.length + zz.head) →
      Certified e frontier [unitsReturn N zz.up] (tapes e.blank e.mark T old)
        (tapes e.blank e.mark
          (vApplyActs' e.blank ((zUnits e.blank e.startSym e.endSym N zz.up T.2).map liftAct) T)
          (zDirN e.blank e.startSym e.endSym N zz.up T.2)) := by
  intro N
  induction N with
  | zero =>
    intro zz T old _ _ _
    exact direction_certified e frontier T old zz.up
  | succ N ih =>
    intro zz T old hwf hU hX
    let V := vApplyActs' e.blank ((zUnitActs e.blank e.startSym e.endSym zz.up T.2).map liftAct) T
    have hV2 : V.2 = extActs e.blank (zUnitActs e.blank e.startSym e.endSym zz.up T.2) T.2 := by
      dsimp only [V]
      rw [vApplyActs'_snd, extActs'_map_liftAct]
    obtain ⟨hU', hX', hd⟩ := zUnitActs_spec hendu hstartu hse hwf hU hX hpos hroom
    have hr := ih (zMove u Word pos zz) V old (zMove_wf hwf)
      (by simpa only [hV2] using hU') (by simpa only [hV2] using hX')
    rw [← hd, hV2] at hr
    have hx : T.2.Txt2.left.length < frontier := by
      rw [PalPeg.TextFeedPipelineMacroFit.seq_left_length hX]
      have hh := hwf.1
      omega
    cases hup : zz.up with
    | true =>
      have hV : V = vApplyActs' e.blank ((vcompActs e.endSym T.2).map liftAct) T := by
        simp only [V, zUnitActs, hup, if_true]
      rw [hup, hV] at hr
      simp only [zNextDir, Bool.true_or, zUnitActs, if_true] at hr
      have h := Checked.seq ((comp_certified e frontier T old hx).append hr)
      simpa only [unitsReturn, hup, zUnits, zDirN, zUnitActs, if_true, zNextDir,
        Bool.true_or, List.map_append, vApplyActs'_append] using h
    | false =>
      let T₁ := vApplyActs' e.blank [VAct'.U .left] T
      have hpk : Tape.read T₁.2.U = zPeekL e.blank T.2 := rfl
      have hleft := keepU_certified e frontier T old .left
      by_cases hp : zPeekL e.blank T.2 = e.startSym
      · have hunit : zUnitActs e.blank e.startSym e.endSym false T.2 =
            [VAct.U .left, VAct.U .right] := by simp [zUnitActs, hp]
        have hV : V = vApplyActs' e.blank [VAct'.U .right] T₁ := by
          simp only [V, hup, hunit, List.map_cons, List.map_nil, liftAct,
            vApplyActs'_cons, vApplyActs'_nil, T₁]
        rw [hup, hV] at hr
        simp only [zNextDir, Bool.false_or, hp, decide_true, hunit] at hr
        have he : evalConds (engine e) (fun j => (tapes e.blank e.mark T₁ old j).focus)
            (.inl .notStartU) = false := by
          change (interp (Terminal := Unit) e.blank e.endSym e.mark e.startSym).condOf _ _ = false
          rw [cond_lift, GSVProg.notStartU_eq, hpk, hp]
          simp
        have hbranch := Checked.branch
          (show condReady e.endSym frontier (tapes e.blank e.mark T₁ old) (.inl .notStartU) from trivial)
          (p := .seq (lift (GSVProg.KEEP10 GSVProg.tX .left)) (unitsReturn N false))
          (q := .seq (lift (GSVProg.KEEP10 GSVProg.tU .right)) (unitsReturn N true)) (s := [])
          (by rw [he]; exact Checked.seq ((keepU_certified e frontier T₁ old .right).append hr))
        have h := Checked.seq (hleft.append hbranch)
        simpa only [unitsReturn, hup, zUnits, zDirN, hunit, zNextDir, Bool.false_or,
          hp, decide_true, List.map_append, List.map_cons, List.map_nil, liftAct,
          vApplyActs'_append, vApplyActs'_cons, vApplyActs'_nil, T₁] using h
      · have hunit : zUnitActs e.blank e.startSym e.endSym false T.2 =
            [VAct.U .left, VAct.X .left] := by simp [zUnitActs, hp]
        have hV : V = vApplyActs' e.blank [VAct'.X .left] T₁ := by
          simp only [V, hup, hunit, List.map_cons, List.map_nil, liftAct,
            vApplyActs'_cons, vApplyActs'_nil, T₁]
        rw [hup, hV] at hr
        simp only [zNextDir, Bool.false_or, decide_eq_false hp, hunit] at hr
        have he : evalConds (engine e) (fun j => (tapes e.blank e.mark T₁ old j).focus)
            (.inl .notStartU) = true := by
          change (interp (Terminal := Unit) e.blank e.endSym e.mark e.startSym).condOf _ _ = true
          rw [cond_lift, GSVProg.notStartU_eq, hpk]
          exact decide_eq_true hp
        have hbranch := Checked.branch
          (show condReady e.endSym frontier (tapes e.blank e.mark T₁ old) (.inl .notStartU) from trivial)
          (p := .seq (lift (GSVProg.KEEP10 GSVProg.tX .left)) (unitsReturn N false))
          (q := .seq (lift (GSVProg.KEEP10 GSVProg.tU .right)) (unitsReturn N true)) (s := [])
          (by rw [he]; exact Checked.seq ((keepX_certified e frontier T₁ old .left (by intro h; cases h)).append hr))
        have h := Checked.seq (hleft.append hbranch)
        simpa only [unitsReturn, hup, zUnits, zDirN, hunit, zNextDir, Bool.false_or,
          decide_eq_false hp, List.map_append, List.map_cons, List.map_nil, liftAct,
          vApplyActs'_append, vApplyActs'_cons, vApplyActs'_nil, T₁] using h

/-- info: 'PalPeg.GSVerifierDemandZ.units_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms units_certified

end PalPeg.GSVerifierDemandZ
