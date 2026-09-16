import PalPeg.ProgLangHeadMoves

/-! Right-move counts of the concrete GS scan and fused verifier traces.
Only moves on the two text tapes matter; counter probes are free here. -/
set_option autoImplicit false

namespace PalPeg.GSVerifierHeadMoves
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.GSVTapes PalPeg.GSVTapesZ PalPeg.ProgLangHeadMoves
variable {k : ℕ}

def scanRight (a : GSTapes.Act' k) : ℕ :=
  if GSTapes.tT = GSTapes.actTape a then right (GSProg.moveOf a) else 0
def scanCount (as : List (GSTapes.Act' k)) : ℕ := (as.map scanRight).sum
def textRight : VAct' k → ℕ
  | .S a => scanRight a
  | _ => 0
def verifyRight : VAct' k → ℕ
  | .X m => right m
  | _ => 0
def textCount (as : List (VAct' k)) : ℕ := (as.map textRight).sum
def verifyCount (as : List (VAct' k)) : ℕ := (as.map verifyRight).sum

@[simp] theorem scan_nil : scanCount (k := k) [] = 0 := rfl
@[simp] theorem scan_cons (a : GSTapes.Act' k) (as : List (GSTapes.Act' k)) :
    scanCount (a :: as) = scanRight a + scanCount as := rfl
@[simp] theorem scan_append (as bs : List (GSTapes.Act' k)) :
    scanCount (as ++ bs) = scanCount as + scanCount bs := by
  simp only [scanCount, List.map_append, List.sum_append]
@[simp] theorem text_nil : textCount (k := k) [] = 0 := rfl
@[simp] theorem text_cons (a : VAct' k) (as : List (VAct' k)) :
    textCount (a :: as) = textRight a + textCount as := rfl
@[simp] theorem text_append (as bs : List (VAct' k)) :
    textCount (as ++ bs) = textCount as + textCount bs := by
  simp only [textCount, List.map_append, List.sum_append]
@[simp] theorem verify_nil : verifyCount (k := k) [] = 0 := rfl
@[simp] theorem verify_cons (a : VAct' k) (as : List (VAct' k)) :
    verifyCount (a :: as) = verifyRight a + verifyCount as := rfl
@[simp] theorem verify_append (as bs : List (VAct' k)) :
    verifyCount (as ++ bs) = verifyCount as + verifyCount bs := by
  simp only [verifyCount, List.map_append, List.sum_append]

@[simp] theorem text_map_S (as : List (GSTapes.Act' k)) : textCount (as.map VAct'.S) = scanCount as := by
  simp only [textCount, scanCount, List.map_map, Function.comp_def, textRight]
@[simp] theorem verify_map_S (as : List (GSTapes.Act' k)) : verifyCount (as.map VAct'.S) = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, verify_cons, verifyRight, ih, Nat.zero_add]

theorem counter_zero (blank mark : Fin k) (i j : Fin 8) (T : TapeConfiguration k)
    (hi : GSTapes.tT ≠ i) (hj : GSTapes.tT ≠ j) :
    scanCount (GSTapes.sUpActs blank mark i j T) = 0 := by
  unfold GSTapes.sUpActs
  split <;> simp [scanRight, GSTapes.actTape, hi, hj]

@[simp] theorem inc_zero (blank mark : Fin k) (T : GSTapes.TapesState' k) :
    scanCount (GSTapes.qIncActs blank mark T) = 0 := by
  simp only [GSTapes.qIncActs, scan_append,
    counter_zero blank mark GSTapes.tAp GSTapes.tAn _ (by decide) (by decide),
    counter_zero blank mark GSTapes.tRn GSTapes.tRp _ (by decide) (by decide), Nat.zero_add]

@[simp] theorem dec_zero (blank mark : Fin k) (T : GSTapes.TapesState' k) :
    scanCount (GSTapes.qDecActs blank mark T) = 0 := by
  simp only [GSTapes.qDecActs, scan_append,
    counter_zero blank mark GSTapes.tAn GSTapes.tAp _ (by decide) (by decide),
    counter_zero blank mark GSTapes.tRp GSTapes.tRn _ (by decide) (by decide), Nat.zero_add]

theorem probe_zero (blank : Fin k) (j : Fin 8) (hj : GSTapes.tT ≠ j) :
    scanCount (GSTapes.probeActs blank j) = 0 := by
  simp [GSTapes.probeActs, scanRight, GSTapes.actTape, hj]

@[simp] theorem adv_one (blank mark : Fin k) (T : GSTapes.TapesState' k) :
    scanCount (GSTapes.advActs blank mark T) = 1 := by
  simp [GSTapes.advActs, GSTapes.advPre, scanRight, GSTapes.actTape, GSProg.moveOf,
    GSTapes.tT, GSTapes.tP, right]

@[simp] theorem perDown_zero (blank mark : Fin k) (T : GSTapes.TapesState' k) :
    scanCount (GSTapes.perDown blank mark T) = 0 := by
  simp [GSTapes.perDown, GSTapes.perPre, scanRight, GSTapes.actTape,
    GSTapes.tT, GSTapes.tP, GSTapes.tC1, GSTapes.tC2]

@[simp] theorem resDown1_zero (blank mark : Fin k) (T : GSTapes.TapesState' k) :
    scanCount (GSTapes.resDown1 blank mark T) = 0 := by
  simp [GSTapes.resDown1, scanRight, GSTapes.actTape, GSTapes.tT, GSTapes.tP]

@[simp] theorem resDown2_zero (blank mark : Fin k) (T : GSTapes.TapesState' k) :
    scanCount (GSTapes.resDown2 blank mark T) = 0 := by
  simp [GSTapes.resDown2, scanRight, GSTapes.actTape, GSProg.moveOf, GSTapes.tT, GSTapes.tP, right]

@[simp] theorem perUp_zero (blank : Fin k) (n : ℕ) : scanCount (GSTapes.perUp blank n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [GSTapes.perUp, scanRight, GSTapes.actTape, GSTapes.tT, GSTapes.tC1, GSTapes.tC2, ih]

@[simp] theorem perLoop_text (blank mark : Fin k) (n : ℕ) (T : VTapes' k) :
    textCount (perLoop1X blank mark n T) = 0 := by
  induction n generalizing T with
  | zero => rfl
  | succ n ih => simp [perLoop1X, perDownX, textRight, ih]

@[simp] theorem perLoop_verify (blank mark : Fin k) (n : ℕ) (T : VTapes' k) :
    verifyCount (perLoop1X blank mark n T) = n := by
  induction n generalizing T with
  | zero => rfl
  | succ n ih => simp [perLoop1X, perDownX, verifyRight, right, ih, Nat.add_comm]

@[simp] theorem resLoop_text (blank mark : Fin k) (rate n c : ℕ) (T : VTapes' k) :
    textCount (resLoopX blank mark rate n c T) = 0 := by
  induction n generalizing c T with
  | zero => rfl
  | succ n ih => cases c <;> simp [resLoopX, resDown1X, resDown2X, textRight, ih]

theorem resLoop_verify (blank mark : Fin k) (rate n c : ℕ) (T : VTapes' k) :
    verifyCount (resLoopX blank mark rate n c T) ≤ n := by
  induction n generalizing c T with
  | zero => rfl
  | succ n ih =>
    cases c with
    | zero =>
      rw [resLoopX, verify_append]
      have hc : verifyCount (resDown1X blank mark T) = 1 := by
        simp [resDown1X, verifyRight, right]
      rw [hc]
      have h := ih (rate - 1) (vApplyActs' blank (resDown1X blank mark T) T)
      omega
    | succ c =>
      simp only [resLoopX, verify_append, resDown2X, verify_map_S, Nat.zero_add]
      exact (ih c _).trans (by omega)

theorem perProgram_counts (blank mark : Fin k) (n : ℕ) (T : VTapes' k) :
    textCount (perProgramX blank mark n T) = 0 ∧ verifyCount (perProgramX blank mark n T) = n := by
  simp [perProgramX, probe_zero blank GSTapes.tC1 (by decide), probe_zero blank GSTapes.tC2 (by decide)]

theorem resProgram_counts (blank mark : Fin k) (rate q : ℕ) (T : VTapes' k) :
    textCount (resProgramX blank mark rate q T) ≤ (if q = 0 then 1 else 0) ∧
      verifyCount (resProgramX blank mark rate q T) ≤ max q 1 := by
  have hc := resLoop_verify blank mark rate q 0 T
  by_cases hq : q = 0
  · simp [resProgramX, hq, textRight, verifyRight, scanRight, GSTapes.actTape,
      GSProg.moveOf, GSTapes.tP, GSTapes.tT, right, resLoopX]
  · simp only [resProgramX, if_neg hq, text_append, resLoop_text, text_cons,
      textRight, text_nil, verify_append, verify_cons, verifyRight, verify_nil]
    norm_num [scanRight, GSTapes.actTape, GSTapes.tT, GSTapes.tP]
    omega

theorem shift_counts {blank mark startSym endSym : Fin k} {pattern Word : List (Fin k)}
    {rate p r : ℕ} {T : VTapes' k} {st : ScanState}
    (hrate : 0 < rate) (hmb : mark ≠ blank)
    (hE : GSTapes.Encodes' blank startSym endSym mark pattern Word rate p r T.1 st) :
    textCount (GSVProg.shiftCoreActs blank mark rate T) ≤ (if st.q = 0 then 1 else 0) ∧
      verifyCount (GSVProg.shiftCoreActs blank mark rate T) ≤ max st.q 1 := by
  simp only [GSVProg.shiftCoreActs, text_append, text_map_S, verify_append, verify_map_S,
    probe_zero blank GSTapes.tAn (by decide), probe_zero blank GSTapes.tRn (by decide), Nat.zero_add]
  unfold GSVProg.shiftBranch
  by_cases hc : Tape.read (Tape.step blank (T.1 GSTapes.tAn) blank .left) = mark ∧
      Tape.read (Tape.step blank (T.1 GSTapes.tRn) blank .left) = mark
  · rw [if_pos hc, GSTapes.p1Of'_eq hE]
    obtain ⟨ht, hv⟩ := perProgram_counts blank mark p T
    have hpq : p ≤ st.q := (Nat.le_mul_of_pos_left p hrate).trans ((GSTapes.period_iff' hmb hE).mp hc).1
    rw [ht, hv]
    split_ifs <;> omega
  · rw [if_neg hc, GSTapes.qOf'_eq hE]
    exact resProgram_counts blank mark rate st.q T

theorem vector_text (T : VTapes' k) (a : VAct' k) :
    right ((GSVProg.vavec T a) (GSVProg.e8 GSTapes.tT)).2 = textRight a := by
  cases a with
  | S a =>
    simp only [GSVProg.vavec, GSVProg.liftVec_e8, GSProg.avec, textRight, scanRight]
    split <;> simp [right]
  | U m => simp [GSVProg.vavec, touchVec, GSVProg.e8, GSTapes.tT, GSVProg.tU, textRight, right]
  | X m => simp [GSVProg.vavec, touchVec, GSVProg.e8, GSTapes.tT, GSVProg.tX, textRight, right]

theorem vector_verify (T : VTapes' k) (a : VAct' k) :
    right ((GSVProg.vavec T a) GSVProg.tX).2 = verifyRight a := by
  cases a with
  | S a => simp [GSVProg.vavec, verifyRight, right]
  | U m => simp [GSVProg.vavec, touchVec, GSVProg.tU, GSVProg.tX, verifyRight, right]
  | X m => simp [GSVProg.vavec, touchVec, verifyRight]

theorem vectors_text (blank : Fin k) (as : List (VAct' k)) (T : VTapes' k) :
    count (GSVProg.e8 GSTapes.tT) (GSVProg.vavecs blank as T) = textCount as := by
  induction as generalizing T with
  | nil => rfl
  | cons a as ih => simp only [GSVProg.vavecs_cons, count_cons, vector_text, ih, text_cons]

theorem vectors_verify (blank : Fin k) (as : List (VAct' k)) (T : VTapes' k) :
    count GSVProg.tX (GSVProg.vavecs blank as T) = verifyCount as := by
  induction as generalizing T with
  | nil => rfl
  | cons a as ih => simp only [GSVProg.vavecs_cons, count_cons, vector_verify, ih, verify_cons]

theorem count_extend {Γ : Type} {s t : ℕ} (ι : Fin s ↪ Fin t) (rest : Fin t → STape Γ)
    (as : List (Fin s → Γ × Move)) (j : Fin s) :
    count (ι j) (as.map (extendVec ι rest)) = count j as := by
  simp only [count, List.map_map, Function.comp_def, extendVec_ι]

def txt1 : Fin 11 := Fin.castAdd 1 (GSVProg.e8 GSTapes.tT)
def txt2 : Fin 11 := Fin.castAdd 1 GSVProg.tX

theorem lift_bounded {Terminal : Type} {blank endSym mark startSym : Fin k}
    {p : Prog GSVProg.Act10 GSVProg.Cond10} {T : VTapes' k} {as : List (VAct' k)}
    (h : GSVProg.ExecV Terminal blank endSym mark startSym p T as) (up : Bool) :
    Bounded (GSVProgZLoop.interp (Terminal := Terminal) blank endSym mark startSym) blank txt1 txt2
      (GSVProgZLoop.lift p) (GSVProgZLoop.tapes blank mark T up)
      (GSVProgZLoop.tapes blank mark (vApplyActs' blank as T) up) (textCount as) (verifyCount as) := by
  have he := exec_sum_inl (I2 := GSVProgZLoop.dirInterp (Terminal := Terminal) blank mark) h
    (GSVProgZLoop.tapes blank mark T up)
  rw [GSVProgZLoop.tapes, extend_castAdd_append] at he
  refine ⟨_, he, ?_, ?_, ?_⟩
  · simpa only [GSVProgZLoop.tapes, extend_castAdd_append, GSVProg.applyTrace_vavecs] using
      (applyTrace_extend (Fin.castAddEmb 1) blank (GSVProgZLoop.tapes blank mark T up)
        (GSVProg.vavecs blank as T) (GSVProg.vTS T))
  · change count ((Fin.castAddEmb 1) (GSVProg.e8 GSTapes.tT)) _ ≤ textCount as
    rw [count_extend, vectors_text]
  · change count ((Fin.castAddEmb 1) GSVProg.tX) _ ≤ verifyCount as
    rw [count_extend, vectors_verify]

/-- A GS macro needs at most ten right moves of Txt1, and at most
q+10 of Txt2. These bounds include the persistent direction instruction. -/
theorem step_bounded {Terminal : Type} {blank endSym mark startSym : Fin k}
    {pattern Word : List (Fin k)} {rate p r : ℕ} {T : VTapes' k} {st : ScanState}
    (hrate : 0 < rate) (hmb : mark ≠ blank) (hstart : startSym ∉ pattern)
    (hE : GSTapes.Encodes' blank startSym endSym mark pattern Word rate p r T.1 st)
    (hq : st.q ≤ pattern.length) (up : Bool) :
    Bounded (GSVProgZLoop.interp (Terminal := Terminal) blank endSym mark startSym) blank txt1 txt2
      (GSVProgZLoop.stepProg rate) (GSVProgZLoop.tapes blank mark T up)
      (GSVProgZLoop.tapes blank mark (vApplyActs' blank (vprogramZ' blank startSym endSym mark rate up T) T)
        (vDirZ blank startSym endSym up T)) 10 (st.q + 10) := by
  unfold GSVProgZLoop.stepProg
  by_cases hadv : Tape.read (T.1 GSTapes.tP) ≠ endSym ∧ Tape.read (T.1 GSTapes.tP) = Tape.read (T.1 GSTapes.tT)
  · have hc : (GSVProgZLoop.interp (Terminal := Terminal) blank endSym mark startSym).condOf
        (.inl .matchOk) (fun j => (GSVProgZLoop.tapes blank mark T up j).focus) = true := by
      rw [GSVProgZLoop.cond_lift, GSVProg.matchOk_eq]
      exact decide_eq_true hadv
    apply Bounded.ite_pos hc
    have hs := GSVProg.execV_lift (Terminal := Terminal) (vt := T)
      (GSProg.scanProg_exec (Terminal := Terminal) (startSym := startSym) hrate hmb hstart hE hq)
    have h1 := lift_bounded hs up
    have hp : GSTapes.program' blank endSym mark rate T.1 = GSTapes.advActs blank mark T.1 := by
      unfold GSTapes.program'
      rw [if_pos hadv]
    have htc : scanCount (GSTapes.program' blank endSym mark rate T.1) = 1 := by rw [hp, adv_one]
    simp only [text_map_S, verify_map_S, htc] at h1
    let T' := vApplyActs' blank ((GSTapes.program' blank endSym mark rate T.1).map VAct'.S) T
    have hsnd : T'.2 = T.2 := by dsimp only [T']; rw [vApplyActs'_map_S]
    have h2 : Bounded (GSVProgZLoop.interp (Terminal := Terminal) blank endSym mark startSym) blank txt1 txt2
        (.ite (.inr .up) (GSVProgZLoop.unitsReturn GSVerifierZ.zQuota true)
          (GSVProgZLoop.unitsReturn GSVerifierZ.zQuota false)) (GSVProgZLoop.tapes blank mark T' up)
        (GSVProgZLoop.tapes blank mark (vApplyActs' blank
          ((zUnits blank startSym endSym GSVerifierZ.zQuota up T'.2).map liftAct) T')
          (zDirN blank startSym endSym GSVerifierZ.zQuota up T'.2)) 9 9 := by
      have hh := Bounded.of_runsTo (j₁ := txt1) (j₂ := txt2)
        (GSVProgZLoop.unitsReturn_runsTo (Terminal := Terminal) blank endSym mark startSym GSVerifierZ.zQuota up up T')
      have hl := zUnits_length_le blank startSym endSym GSVerifierZ.zQuota up T'.2
      change (zUnits blank startSym endSym GSVerifierZ.zQuota up T'.2).length ≤ 8 at hl
      have h9 := hh.mono (by omega : _ ≤ 9) (by omega : _ ≤ 9)
      cases up with
      | false => exact Bounded.ite_neg (GSVProgZLoop.cond_up _ _ _ _ hmb _ false) h9
      | true => exact Bounded.ite_pos (GSVProgZLoop.cond_up _ _ _ _ hmb _ true) h9
    have H := (h1.seq h2).mono (by omega : 1 + 9 ≤ 10) (by omega : 0 + 9 ≤ st.q + 10)
    rw [hsnd] at H
    simpa only [T', hp, vprogramZ', vDirZ, if_pos hadv, vApplyActs'_append, List.map_append] using H
  · have hc : (GSVProgZLoop.interp (Terminal := Terminal) blank endSym mark startSym).condOf
        (.inl .matchOk) (fun j => (GSVProgZLoop.tapes blank mark T up j).focus) = false := by
      rw [GSVProgZLoop.cond_lift, GSVProg.matchOk_eq]
      exact decide_eq_false hadv
    apply Bounded.ite_neg hc
    have h1 := lift_bounded (GSVProg.shiftCore_exec (Terminal := Terminal) (z := (st, 0)) hrate hmb hstart hE hq) up
    have h2 := Bounded.of_runsTo (j₁ := txt1) (j₂ := txt2)
      (GSVProgZLoop.setDir_runsTo (Terminal := Terminal) blank endSym mark startSym
        (vApplyActs' blank (GSVProg.shiftCoreActs blank mark rate T) T) up false)
    obtain ⟨hc₁, hc₂⟩ := shift_counts hrate hmb hE
    have ht : textCount (GSVProg.shiftCoreActs blank mark rate T) ≤ 1 := by
      split_ifs at hc₁ <;> omega
    have H := (h1.seq h2).mono (by omega : _ ≤ 10) (by omega : _ ≤ st.q + 10)
    simpa only [GSVProgZ.vprogramZ'_shift blank startSym endSym mark rate up T hadv,
      vDirZ, if_neg hadv] using H

/-- info: 'PalPeg.GSVerifierHeadMoves.step_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_bounded

end PalPeg.GSVerifierHeadMoves
