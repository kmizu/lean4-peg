import PalPeg.GSVerifierProgZ
import PalPeg.ProgLangSum

/-!
# Persistent direction for the finite zigzag program

The direction is stored on one stationary tape. The continuation-passing units
write it once, at the end of a scan step, rather than after every unit. Thus
remembering direction costs one action per completed scan step.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.GSVProgZLoop

open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.GSVProg PalPeg.GSVProgZ PalPeg.GSVTapes PalPeg.GSVTapesZ

variable {sc : ℕ} {Terminal : Type}

inductive DCond where
  | up | always
  deriving DecidableEq, Fintype

def dirSymbol (blank mark : Fin sc) (up : Bool) : Fin sc := if up then mark else blank

def dirTape (blank mark : Fin sc) (up : Bool) : Fin 1 → STape (Fin sc) :=
  fun _ => ⟨[], dirSymbol blank mark up, []⟩

def dirInterp (blank mark : Fin sc) : Interp Terminal Bool DCond (Fin sc) 1 where
  actOf up _ _ _ := (dirSymbol blank mark up, .stay)
  condOf c σ := match c with
    | .up => decide (σ 0 = mark)
    | .always => true

abbrev DProg := Prog (Act10 ⊕ Bool) (Cond10 ⊕ DCond)

noncomputable def interp (blank endSym mark startSym : Fin sc) :
    Interp Terminal (Act10 ⊕ Bool) (Cond10 ⊕ DCond) (Fin sc) 11 :=
  Interp.sum (I10 blank endSym mark startSym) (dirInterp blank mark)

def tapes (blank mark : Fin sc) (vt : VTapes' sc) (up : Bool) :
    Fin 11 → STape (Fin sc) := Fin.append (vTS vt) (dirTape blank mark up)

def lift (p : Prog Act10 Cond10) : DProg := p.map Sum.inl Sum.inl

def setDir (up : Bool) : DProg := .act (.inr up)

/-- An exact cost and endpoint, with the executable trace existentially hidden. -/
def RunsTo {A C Γ : Type} {t : ℕ} (I : Interp Terminal A C Γ t) (blank : Γ)
    (p : Prog A C) (T U : Fin t → STape Γ) (cost : ℕ) : Prop :=
  ∃ acts, Exec I blank p T acts ∧ applyTrace blank T acts = U ∧ acts.length = cost

theorem RunsTo.seq {A C Γ : Type} {t : ℕ} {I : Interp Terminal A C Γ t} {blank : Γ}
    {p q : Prog A C} {T U V : Fin t → STape Γ} {m n : ℕ}
    (hp : RunsTo I blank p T U m) (hq : RunsTo I blank q U V n) :
    RunsTo I blank (.seq p q) T V (m + n) := by
  obtain ⟨a, ha, ea, la⟩ := hp
  obtain ⟨b, hb, eb, lb⟩ := hq
  refine ⟨a ++ b, exec_seq ha (ea ▸ hb), ?_, ?_⟩
  · rw [applyTrace_append, ea, eb]
  · simp only [List.length_append, la, lb]

theorem RunsTo.ite_pos {A C Γ : Type} {t : ℕ} {I : Interp Terminal A C Γ t} {blank : Γ}
    {p q : Prog A C} {c : C} {T U : Fin t → STape Γ} {m : ℕ}
    (hc : I.condOf c (fun j => (T j).focus) = true)
    (hp : RunsTo I blank p T U m) : RunsTo I blank (.ite c p q) T U m := by
  obtain ⟨a, ha, ea, la⟩ := hp
  exact ⟨a, exec_ite_pos hc ha, ea, la⟩

theorem RunsTo.ite_neg {A C Γ : Type} {t : ℕ} {I : Interp Terminal A C Γ t} {blank : Γ}
    {p q : Prog A C} {c : C} {T U : Fin t → STape Γ} {m : ℕ}
    (hc : I.condOf c (fun j => (T j).focus) = false)
    (hp : RunsTo I blank q T U m) : RunsTo I blank (.ite c p q) T U m := by
  obtain ⟨a, ha, ea, la⟩ := hp
  exact ⟨a, exec_ite_neg hc ha, ea, la⟩

theorem lift_runsTo {blank endSym mark startSym : Fin sc}
    {p : Prog Act10 Cond10} {vt : VTapes' sc} {acts : List (VAct' sc)}
    (h : ExecV Terminal blank endSym mark startSym p vt acts) (up : Bool) :
    RunsTo (interp (Terminal := Terminal) blank endSym mark startSym) blank (lift p) (tapes blank mark vt up)
      (tapes blank mark (vApplyActs' blank acts vt) up) acts.length := by
  have he := exec_sum_inl (I2 := dirInterp (Terminal := Terminal) blank mark) h
    (tapes blank mark vt up)
  rw [tapes, extend_castAdd_append] at he
  refine ⟨_, he, ?_, ?_⟩
  · simpa only [tapes, extend_castAdd_append, applyTrace_vavecs] using
      (applyTrace_extend (Fin.castAddEmb 1) blank (tapes blank mark vt up)
        (vavecs blank acts vt) (vTS vt))
  · rw [List.length_map, vavecs_length]

theorem setDir_runsTo (blank endSym mark startSym : Fin sc) (vt : VTapes' sc)
    (old up : Bool) :
    RunsTo (interp (Terminal := Terminal) blank endSym mark startSym) blank
      (setDir up) (tapes blank mark vt old) (tapes blank mark vt up) 1 := by
  have hd : Exec (dirInterp (Terminal := Terminal) blank mark) blank (.act up)
      (dirTape blank mark old) [fun _ => (dirSymbol blank mark up, .stay)] :=
    exec_act (fun _ _ _ => rfl) up (dirTape blank mark old)
  have he := exec_sum_inr (I1 := I10 (Terminal := Terminal) blank endSym mark startSym) hd
    (tapes blank mark vt old)
  rw [tapes, extend_natAdd_append] at he
  refine ⟨_, he, ?_, rfl⟩
  have hd' : applyTrace blank (dirTape blank mark old)
      [fun _ => (dirSymbol blank mark up, .stay)] = dirTape blank mark up := rfl
  simpa only [tapes, hd', extend_natAdd_append] using
    (applyTrace_extend (Fin.natAddEmb 10) blank (tapes blank mark vt old)
      [fun _ => (dirSymbol blank mark up, .stay)] (dirTape blank mark old))

/-- The final leaf records the resulting direction, including a turn inside the quota. -/
def unitsReturn : ℕ → Bool → DProg
  | 0, up => setDir up
  | n + 1, true => .seq (lift vcompProg) (unitsReturn n true)
  | n + 1, false =>
      .seq (lift (KEEP10 tU .left))
        (.ite (.inl .notStartU)
          (.seq (lift (KEEP10 tX .left)) (unitsReturn n false))
          (.seq (lift (KEEP10 tU .right)) (unitsReturn n true)))

theorem cond_lift (blank endSym mark startSym : Fin sc) (vt : VTapes' sc)
    (up : Bool) (c : Cond10) :
    (interp (Terminal := Terminal) blank endSym mark startSym).condOf (.inl c)
      (fun j => (tapes blank mark vt up j).focus) =
      condOf10 endSym mark startSym c (fun j => (vTS vt j).focus) := by
  change condOf10 endSym mark startSym c
    (fun j => (Fin.append (vTS vt) (dirTape blank mark up) (Fin.castAdd 1 j)).focus) = _
  simp only [Fin.append_left]

theorem unitsReturn_runsTo (blank endSym mark startSym : Fin sc) :
    ∀ (n : ℕ) (up old : Bool) (vt : VTapes' sc),
      RunsTo (interp (Terminal := Terminal) blank endSym mark startSym) blank
        (unitsReturn n up) (tapes blank mark vt old)
        (tapes blank mark
          (vApplyActs' blank ((zUnits blank startSym endSym n up vt.2).map liftAct) vt)
          (zDirN blank startSym endSym n up vt.2))
        ((zUnits blank startSym endSym n up vt.2).length + 1) := by
  intro n
  induction n with
  | zero =>
      intro up old vt
      exact setDir_runsTo blank endSym mark startSym vt old up
  | succ n ih =>
      intro up old vt
      cases up with
      | true =>
          have h1 := lift_runsTo
            (vcompProg_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
              (mark := mark) (startSym := startSym) vt) old
          have h2 := ih true old (vApplyActs' blank ((vcompActs endSym vt.2).map liftAct) vt)
          have hsnd : (vApplyActs' blank ((vcompActs endSym vt.2).map liftAct) vt).2 =
              extActs blank (vcompActs endSym vt.2) vt.2 := by
            rw [vApplyActs'_snd, extActs'_map_liftAct]
          rw [hsnd] at h2
          simpa only [unitsReturn, zUnits, zDirN, zUnitActs, zNextDir, ↓reduceIte,
            Bool.true_or, List.map_append, vApplyActs'_append, List.length_append,
            List.length_map, Nat.add_assoc] using h1.seq h2
      | false =>
          have h1 := lift_runsTo
            (execV_keepU (Terminal := Terminal) (blank := blank) (endSym := endSym)
              (mark := mark) (startSym := startSym) .left vt) old
          let vt1 := vApplyAct' blank vt (VAct'.U .left)
          have hpk : Tape.read vt1.2.U = zPeekL blank vt.2 := rfl
          by_cases hs : zPeekL blank vt.2 = startSym
          · have hunit : zUnitActs blank startSym endSym false vt.2 =
                [VAct.U (sc := sc) .left, VAct.U .right] := by
              unfold zUnitActs
              rw [if_neg (by simp), if_pos hs]
            have hc : (interp (Terminal := Terminal) blank endSym mark startSym).condOf
                (.inl .notStartU) (fun j => (tapes blank mark vt1 old j).focus) = false := by
              rw [cond_lift, notStartU_eq, hpk, hs]
              simp
            have h2 := lift_runsTo
              (execV_keepU (Terminal := Terminal) (blank := blank) (endSym := endSym)
                (mark := mark) (startSym := startSym) .right vt1) old
            have h3 := ih true old (vApplyActs' blank [VAct'.U .right] vt1)
            have hsnd : (vApplyActs' blank [VAct'.U .right] vt1).2 =
                extActs blank (zUnitActs blank startSym endSym false vt.2) vt.2 := by
              rw [hunit]
              rfl
            rw [hsnd] at h3
            have H := h1.seq (RunsTo.ite_neg (p := .seq (lift (KEEP10 tX .left))
              (unitsReturn n false)) hc (h2.seq h3))
            simpa only [unitsReturn, zUnits, zDirN, hunit, zNextDir, Bool.false_or,
              hs, decide_true, List.map_append, List.map_cons, List.map_nil,
              liftAct, List.cons_append, List.nil_append, vApplyActs'_cons, vApplyActs'_nil,
              List.length_cons, List.length_nil, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm, Nat.zero_add, vt1] using H
          · have hunit : zUnitActs blank startSym endSym false vt.2 =
                [VAct.U (sc := sc) .left, VAct.X .left] := by
              unfold zUnitActs
              rw [if_neg (by simp), if_neg hs]
            have hc : (interp (Terminal := Terminal) blank endSym mark startSym).condOf
                (.inl .notStartU) (fun j => (tapes blank mark vt1 old j).focus) = true := by
              rw [cond_lift, notStartU_eq, hpk]
              exact decide_eq_true hs
            have h2 := lift_runsTo
              (execV_keepX (Terminal := Terminal) (blank := blank) (endSym := endSym)
                (mark := mark) (startSym := startSym) .left vt1) old
            have h3 := ih false old (vApplyActs' blank [VAct'.X .left] vt1)
            have hsnd : (vApplyActs' blank [VAct'.X .left] vt1).2 =
                extActs blank (zUnitActs blank startSym endSym false vt.2) vt.2 := by
              rw [hunit]
              rfl
            rw [hsnd] at h3
            have H := h1.seq (RunsTo.ite_pos (q := .seq (lift (KEEP10 tU .right))
              (unitsReturn n true)) hc (h2.seq h3))
            simpa only [unitsReturn, zUnits, zDirN, hunit, zNextDir, Bool.false_or,
              decide_eq_false hs, List.map_append, List.map_cons, List.map_nil,
              liftAct, List.cons_append, List.nil_append, vApplyActs'_cons, vApplyActs'_nil,
              List.length_cons, List.length_nil, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm, Nat.zero_add, vt1] using H

def stepProg (k : ℕ) : DProg :=
  .ite (.inl .matchOk)
    (.seq (lift (pmap (PalPeg.GSProg.scanProg k)))
      (.ite (.inr .up) (unitsReturn PalPeg.GSVerifierZ.zQuota true)
        (unitsReturn PalPeg.GSVerifierZ.zQuota false)))
    (.seq (lift (shiftCore k)) (setDir false))

/-- The mandatory loop action is a stationary self-write, so each iteration
adds exactly one more action besides the direction write in `stepProg`. -/
def loopProg (k : ℕ) : DProg :=
  .loop (.inr .always) (.inl (tU, true, .stay)) (stepProg k)

theorem cond_up (blank endSym mark startSym : Fin sc) (hmb : mark ≠ blank)
    (vt : VTapes' sc) (up : Bool) :
    (interp (Terminal := Terminal) blank endSym mark startSym).condOf (.inr .up)
      (fun j => (tapes blank mark vt up j).focus) = up := by
  change decide ((dirTape blank mark up 0).focus = mark) = up
  cases up <;> simp [dirTape, dirSymbol, Ne.symm hmb]

theorem stepProg_runsTo {blank endSym mark startSym : Fin sc}
    {v Text : List (Fin sc)} {k p₁ r : ℕ} {vt : VTapes' sc} {st : PalPeg.ScanState}
    (hk : 0 < k) (hmb : mark ≠ blank) (hstart : startSym ∉ v)
    (hE : PalPeg.GSTapes.Encodes' blank startSym endSym mark v Text k p₁ r vt.1 st)
    (hq : st.q ≤ v.length) (up : Bool) :
    RunsTo (interp (Terminal := Terminal) blank endSym mark startSym) blank
      (stepProg k) (tapes blank mark vt up)
      (tapes blank mark (vApplyActs' blank (vprogramZ' blank startSym endSym mark k up vt) vt)
        (vDirZ blank startSym endSym up vt))
      ((vprogramZ' blank startSym endSym mark k up vt).length + 1) := by
  unfold stepProg
  by_cases hadv : Tape.read (vt.1 PalPeg.GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 PalPeg.GSTapes.tP) = Tape.read (vt.1 PalPeg.GSTapes.tT)
  · have hc : (interp (Terminal := Terminal) blank endSym mark startSym).condOf
        (.inl .matchOk) (fun j => (tapes blank mark vt up j).focus) = true := by
      rw [cond_lift, matchOk_eq]
      exact decide_eq_true hadv
    apply RunsTo.ite_pos hc
    have hs := execV_lift (Terminal := Terminal) (vt := vt)
      (PalPeg.GSProg.scanProg_exec (Terminal := Terminal) (startSym := startSym)
        hk hmb hstart hE hq)
    have h1 := lift_runsTo hs up
    let vt' := vApplyActs' blank
      ((PalPeg.GSTapes.program' blank endSym mark k vt.1).map VAct'.S) vt
    have hsnd : vt'.2 = vt.2 := by
      dsimp only [vt']
      rw [vApplyActs'_map_S]
    have h2 : RunsTo (interp (Terminal := Terminal) blank endSym mark startSym) blank
        (.ite (.inr .up) (unitsReturn PalPeg.GSVerifierZ.zQuota true)
          (unitsReturn PalPeg.GSVerifierZ.zQuota false)) (tapes blank mark vt' up)
        (tapes blank mark (vApplyActs' blank
          ((zUnits blank startSym endSym PalPeg.GSVerifierZ.zQuota up vt'.2).map liftAct) vt')
          (zDirN blank startSym endSym PalPeg.GSVerifierZ.zQuota up vt'.2))
        ((zUnits blank startSym endSym PalPeg.GSVerifierZ.zQuota up vt'.2).length + 1) := by
      cases up with
      | false =>
          exact RunsTo.ite_neg (cond_up _ _ _ _ hmb _ false)
            (unitsReturn_runsTo _ _ _ _ _ false false vt')
      | true =>
          exact RunsTo.ite_pos (cond_up _ _ _ _ hmb _ true)
            (unitsReturn_runsTo _ _ _ _ _ true true vt')
    have hp : PalPeg.GSTapes.program' blank endSym mark k vt.1 =
        PalPeg.GSTapes.advActs blank mark vt.1 := by
      unfold PalPeg.GSTapes.program'
      rw [if_pos hadv]
    have H := h1.seq h2
    rw [hsnd] at H
    simpa only [vt', hp, vprogramZ', vDirZ, if_pos hadv, vApplyActs'_append,
      List.length_append, List.length_map, Nat.add_assoc] using H
  · have hc : (interp (Terminal := Terminal) blank endSym mark startSym).condOf
        (.inl .matchOk) (fun j => (tapes blank mark vt up j).focus) = false := by
      rw [cond_lift, matchOk_eq]
      exact decide_eq_false hadv
    apply RunsTo.ite_neg hc
    have h1 := lift_runsTo
      (shiftCore_exec (Terminal := Terminal) (z := (st, 0)) hk hmb hstart hE hq) up
    have h2 := setDir_runsTo (Terminal := Terminal) blank endSym mark startSym
      (vApplyActs' blank (shiftCoreActs blank mark k vt) vt) up false
    simpa only [vprogramZ'_shift blank startSym endSym mark k up vt hadv,
      vDirZ, if_neg hadv] using h1.seq h2

def iterationProg (k : ℕ) : DProg := .seq (lift (KEEP10 tU .stay)) (stepProg k)

theorem loop_unfold (blank endSym mark startSym : Fin sc) (k : ℕ)
    (T : Fin 11 → STape (Fin sc)) :
    SEqAt (interp (Terminal := Terminal) blank endSym mark startSym) T
      [loopProg k] [iterationProg k, loopProg k] := by
  unfold SEqAt loopProg iterationProg
  rw [stepStack_loop, stepStack_seq]
  have hc : evalConds (interp (Terminal := Terminal) blank endSym mark startSym)
      (fun j => (T j).focus) (.inr .always) = true := rfl
  rw [if_pos hc]
  simp only [lift, KEEP10, Prog.map, stepStack_act]

theorem RunsTo.runUnder {A C Γ : Type} {t : ℕ} {I : Interp Terminal A C Γ t} {blank : Γ}
    {p : Prog A C} {s r : Stack A C} {T U : Fin t → STape Γ} {m : ℕ}
    (hp : RunsTo I blank p T U m) (hm : 0 < m) (hs : SEqAt I T s (p :: r)) :
    ∃ s', runInputs I blank (List.replicate m none) (s, T) = (s', U) ∧ SEqAt I U s' r := by
  obtain ⟨acts, he, ht, hl⟩ := hp
  obtain ⟨_, s', hr, heq⟩ := he r (List.replicate m none) (by simp only [List.length_replicate, hl])
  refine ⟨s', ?_, ht ▸ heq⟩
  cases m with
  | zero => omega
  | succ m =>
      have hc := runInputs_congr (blank := blank) hs none (List.replicate m none)
      rw [ht] at hr
      exact hc.trans hr

theorem iterationProg_runsTo {blank endSym mark startSym : Fin sc}
    {v Text : List (Fin sc)} {k p₁ r : ℕ} {vt : VTapes' sc} {st : PalPeg.ScanState}
    (hk : 0 < k) (hmb : mark ≠ blank) (hstart : startSym ∉ v)
    (hE : PalPeg.GSTapes.Encodes' blank startSym endSym mark v Text k p₁ r vt.1 st)
    (hq : st.q ≤ v.length) (up : Bool) :
    RunsTo (interp (Terminal := Terminal) blank endSym mark startSym) blank
      (iterationProg k) (tapes blank mark vt up)
      (tapes blank mark (vApplyActs' blank (vprogramZ' blank startSym endSym mark k up vt) vt)
        (vDirZ blank startSym endSym up vt))
      ((vprogramZ' blank startSym endSym mark k up vt).length + 2) := by
  have h1 := lift_runsTo
    (execV_keepU (Terminal := Terminal) (blank := blank) (endSym := endSym)
      (mark := mark) (startSym := startSym) .stay vt) up
  have hstay : vApplyActs' blank [VAct'.U .stay] vt = vt := rfl
  rw [hstay] at h1
  have h2 := stepProg_runsTo (Terminal := Terminal) hk hmb hstart hE hq up
  have H := h1.seq h2
  have hcost : [VAct'.U (sc := sc) .stay].length +
      ((vprogramZ' blank startSym endSym mark k up vt).length + 1) =
      (vprogramZ' blank startSym endSym mark k up vt).length + 2 := by
    simp only [List.length_cons, List.length_nil]
    omega
  rw [hcost] at H
  exact H

/-- One iteration of the same fixed loop, with its continuation preserved.
No program containing an input length or an iteration count is generated. -/
theorem loopProg_chunk {blank endSym mark startSym : Fin sc}
    {v Text : List (Fin sc)} {k p₁ r : ℕ} {vt : VTapes' sc} {st : PalPeg.ScanState}
    (hk : 0 < k) (hmb : mark ≠ blank) (hstart : startSym ∉ v)
    (hE : PalPeg.GSTapes.Encodes' blank startSym endSym mark v Text k p₁ r vt.1 st)
    (hq : st.q ≤ v.length) (up : Bool) (s : Stack (Act10 ⊕ Bool) (Cond10 ⊕ DCond))
    (hs : SEqAt (interp (Terminal := Terminal) blank endSym mark startSym)
      (tapes blank mark vt up) s [loopProg k]) :
    let vt' := vApplyActs' blank (vprogramZ' blank startSym endSym mark k up vt) vt
    let up' := vDirZ blank startSym endSym up vt
    ∃ s', runInputs (interp (Terminal := Terminal) blank endSym mark startSym) blank
        (List.replicate ((vprogramZ' blank startSym endSym mark k up vt).length + 2) none)
        (s, tapes blank mark vt up) = (s', tapes blank mark vt' up') ∧
      SEqAt (interp (Terminal := Terminal) blank endSym mark startSym)
        (tapes blank mark vt' up') s' [loopProg k] := by
  exact (iterationProg_runsTo (Terminal := Terminal) hk hmb hstart hE hq up).runUnder
    (by omega) (hs.trans (loop_unfold blank endSym mark startSym k _))

/-- info: 'PalPeg.GSVProgZLoop.loopProg_chunk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loopProg_chunk

/-- Concrete fixed-loop execution, abstract zigzag simulation, and pointwise
cost in one statement. The former constant 16 becomes 18. -/
theorem loopProg_chunk_spec {blank endSym mark startSym : Fin sc}
    {u v Text : List (Fin sc)} {k p₁ r : ℕ} {vt : VTapes' sc}
    {z : PalPeg.GSVerifierZ.VStateZ}
    (hk : 0 < k) (hp : 0 < p₁) (hmb : mark ≠ blank)
    (hstart : startSym ∉ v) (hend : endSym ∉ v)
    (hendu : endSym ∉ u) (hstartu : startSym ∉ u) (hse : startSym ≠ endSym)
    (hE : VEncodesZ' blank startSym endSym mark u v Text k p₁ r vt z)
    (hwf : PalPeg.GSVerifierZ.ZWf u.length z.2) (hq : z.1.q ≤ v.length)
    (hpos : u.length ≤ z.1.pos)
    (hfit : (PalPeg.scanStep v k p₁ r Text z.1).pos +
      (PalPeg.scanStep v k p₁ r Text z.1).q < Text.length)
    (s : Stack (Act10 ⊕ Bool) (Cond10 ⊕ DCond))
    (hs : SEqAt (interp (Terminal := Terminal) blank endSym mark startSym)
      (tapes blank mark vt z.2.up) s [loopProg k]) :
    let z' := PalPeg.GSVerifierZ.vStepZ u v k p₁ r Text z
    ∃ cost s' vt',
      runInputs (interp (Terminal := Terminal) blank endSym mark startSym) blank
        (List.replicate cost none) (s, tapes blank mark vt z.2.up) =
          (s', tapes blank mark vt' z'.2.up) ∧
      SEqAt (interp (Terminal := Terminal) blank endSym mark startSym)
        (tapes blank mark vt' z'.2.up) s' [loopProg k] ∧
      VEncodesZ' blank startSym endSym mark u v Text k p₁ r vt' z' ∧
      0 < cost ∧
      cost ≤ zA k * (PalPeg.Phi k z'.1 - PalPeg.Phi k z.1) + 18 := by
  obtain ⟨s', hr, hseq⟩ := loopProg_chunk (Terminal := Terminal)
    hk hmb hstart hE.scan hq z.2.up s hs
  obtain ⟨he', hdir⟩ := vencodes_stepZ hk hp hmb hend hendu hstartu hse hE hwf hq hpos hfit
  rw [hdir] at hr hseq
  refine ⟨(vprogramZ' blank startSym endSym mark k z.2.up vt).length + 2,
    s', _, hr, hseq, he', by omega, ?_⟩
  have hcost := vprogramZ'_cost hk hmb hend hE hq
  simp only [zB] at hcost
  simp only [PalPeg.GSVerifierZ.vStepZ_fst]
  omega

/-- info: 'PalPeg.GSVProgZLoop.loopProg_chunk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loopProg_chunk_spec

end PalPeg.GSVProgZLoop
