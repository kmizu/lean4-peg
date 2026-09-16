import PalPeg.GSVerifierProg
import PalPeg.GSVerifierFused

/-!
# 相乗り版ずらし枝の有限制御プログラム化 (`GSVerifierProgX`)

`PalPeg.GSVerifierFused` の `GSVTapes.vprogramX`（走査段のずらしループに `Txt2` の
1 歩を相乗りさせ、最後に `U` と `Txt2` を同時に巻き戻す一歩の動作列）を、
`PalPeg.ProgLang` の構造化プログラム `Prog Act10 Cond10` として実現する。
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace PalPeg.GSVProg

open PegSeparation.RealTimeTM
open PalPeg.Program
open PalPeg.ProgLang
open PalPeg.GSProg
open PalPeg.GSTapes
open PalPeg.GSVTapes (VAct' VTapes' vApplyAct' vApplyActs' perDownX perLoop1X resDown1X
  resDown2X resLoopX perProgramX resProgramX uxWalk uxWalkLoop vprogramX cOf VEncodes')

variable {sc : ℕ}

/-! ## 1. 補助補題 -/

section Aux

variable {Terminal : Type} {blank endSym mark startSym : Fin sc}

/-- 持ち上げた条件の評価は 8 本テープでの評価に一致する。 -/
theorem condV_fc (c : Cond8) (vt : VTapes' sc) :
    condOf10 endSym mark startSym (fc c) (fun j => ((vTS vt) j).focus)
      = condOf8 endSym mark startSym c (fun j => (vt.1 j).focus) := by
  cases c <;> simp only [condOf10, condOf8, fc, vTS_e8, toS]

/-- 持ち上げた動作のベクトルは 8 本テープのベクトルの持ち上げ。 -/
theorem actVec10_of8 (a : Act8) (vt : VTapes' sc) :
    actVec (I10 (Terminal := Terminal) blank endSym mark startSym) (fa a) (vTS vt)
      = liftVec (toS vt.2.U) (toS vt.2.Txt2)
          (actVec (I8 (Terminal := Terminal) blank endSym mark startSym) a (TS vt.1)) :=
  act_agree a none (TS vt.1) _ _

theorem actVec10_put (i : Fin 8) (m : Move) (vt : VTapes' sc) :
    actVec (I10 (Terminal := Terminal) blank endSym mark startSym) (fa (i, false, m)) (vTS vt)
      = vavec vt (VAct'.S (Act'.put i blank m)) := by
  rw [actVec10_of8, actVec_put]
  rfl

theorem execV_loop_stop' {c : Cond10} {a : Act10} {b : Prog Act10 Cond10} {vt : VTapes' sc}
    (hc : condOf10 endSym mark startSym c (fun j => ((vTS vt) j).focus) = false) :
    ExecV Terminal blank endSym mark startSym (Prog.loop c a b) vt [] :=
  exec_loop_stop (by rw [condV_eq]; exact hc)

/-- ループの継続規則（ガード動作が 8 本テープ側の `put`）。 -/
theorem execV_loop_contS {c : Cond10} {i : Fin 8} {m : Move} {b : Prog Act10 Cond10}
    {vt : VTapes' sc} {L₁ L₂ : List (VAct' sc)}
    (hc : condOf10 endSym mark startSym c (fun j => ((vTS vt) j).focus) = true)
    (h1 : ExecV Terminal blank endSym mark startSym b
      (vApplyAct' blank vt (VAct'.S (Act'.put i blank m))) L₁)
    (h2 : ExecV Terminal blank endSym mark startSym (Prog.loop c (fa (i, false, m)) b)
      (vApplyActs' blank L₁ (vApplyAct' blank vt (VAct'.S (Act'.put i blank m)))) L₂) :
    ExecV Terminal blank endSym mark startSym (Prog.loop c (fa (i, false, m)) b) vt
      (VAct'.S (Act'.put i blank m) :: (L₁ ++ L₂)) := by
  unfold ExecV at h1 h2 ⊢
  rw [vavecs_cons, vavecs_append]
  have he : actVec (I10 (Terminal := Terminal) blank endSym mark startSym)
      (fa (i, false, m)) (vTS vt) = vavec vt (VAct'.S (Act'.put i blank m)) :=
    actVec10_put i m vt
  have hT : (fun j => ((vTS vt) j).applyAction blank
      (actVec (I10 (Terminal := Terminal) blank endSym mark startSym) (fa (i, false, m))
        (vTS vt) j)) = vTS (vApplyAct' blank vt (VAct'.S (Act'.put i blank m))) := by
    rw [he]; exact applyTrace_vavec blank vt (VAct'.S (Act'.put i blank m))
  rw [← he]
  refine exec_loop_cont (inputFree_I10 blank endSym mark startSym)
    (by rw [condV_eq]; exact hc) ?_ ?_
  · rw [hT]; exact h1
  · rw [hT, applyTrace_vavecs]; exact h2

theorem execV_keep8 (i : Fin 8) (m : Move) (vt : VTapes' sc) :
    ExecV Terminal blank endSym mark startSym (pmap (KEEP i m)) vt [VAct'.S (Act'.keep i m)] :=
  execV_lift (execA_keep (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) i m vt.1)

theorem execV_put8 (i : Fin 8) (m : Move) (vt : VTapes' sc) :
    ExecV Terminal blank endSym mark startSym (pmap (PUT i m)) vt
      [VAct'.S (Act'.put i blank m)] :=
  execV_lift (execA_put (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) i m vt.1)

/-- `S` で持ち上げた動作列の適用は 8 本テープ側の適用。 -/
theorem vApplyActs'_mapS (blank : Fin sc) (l : List (Act' sc)) (vt : VTapes' sc) :
    vApplyActs' blank (l.map VAct'.S) vt = (applyActs' blank l vt.1, vt.2) :=
  PalPeg.GSVTapes.vApplyActs'_map_S blank l vt

end Aux

/-! ## 2. 周期ずらし枝（相乗り版） -/

section PerX

/-- `perBody` からループ末尾のプローブ `PUT tC1 .left` を除いた前半。 -/
def perBodyPre : Prog Act8 Cond8 :=
  Prog.seq (PUT tC2 .right) (Prog.seq (KEEP tP .left) qDecProg)

/-- 相乗り版の下げループ本体：`perBody` の `qDecProg` の直後に `X .right` を挟む。 -/
def perBodyX : Prog Act10 Cond10 :=
  Prog.seq (pmap perBodyPre) (Prog.seq (KEEP10 tX .right) (pmap (PUT tC1 .left)))

/-- 相乗り版の下げループ。条件・ガード動作は `perDownLoop` と同じ。 -/
def perDownLoopX : Prog Act10 Cond10 :=
  Prog.loop (fc (Cond8.notMark tC1)) (fa (tC1, false, Move.stay)) perBodyX

/-- 相乗り版の周期ずらし枝。上げループは `Txt2` を触らないのでそのまま持ち上げる。 -/
def perProgX : Prog Act10 Cond10 :=
  Prog.seq (pmap (PUT tC1 .left))
    (Prog.seq perDownLoopX
      (Prog.seq (pmap (KEEP tC1 .right))
        (Prog.seq (pmap (PUT tC2 .left))
          (Prog.seq (pmap perUpLoop) (pmap (KEEP tC2 .right))))))

end PerX

section PerXSpec

variable {Terminal : Type} {blank endSym mark startSym : Fin sc}

@[simp] theorem vApplyAct'_S_fst (blank : Fin sc) (vt : VTapes' sc) (a : Act' sc) :
    (vApplyAct' blank vt (VAct'.S a)).1 = applyAct' blank vt.1 a := rfl

@[simp] theorem vApplyAct'_S_snd (blank : Fin sc) (vt : VTapes' sc) (a : Act' sc) :
    (vApplyAct' blank vt (VAct'.S a)).2 = vt.2 := rfl

theorem perBodyPre_exec (ts : TapesState' sc) :
    ExecA Terminal blank endSym mark startSym perBodyPre ts
      ([Act'.put tC2 blank .right, Act'.keep tP .left] ++ qDecActs blank mark ts) := by
  have e1 := execA_put (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tC2 Move.right ts
  set u1 := applyActs' blank [Act'.put tC2 blank (sc := sc) .right] ts with hu1
  have e2 := execA_keep (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tP Move.left u1
  set u2 := applyActs' blank [Act'.keep tP (sc := sc) .left] u1 with hu2
  have hAp : u2 tAp = ts tAp := by
    rw [hu2, hu1]
    exact (applyAct'_keep_ne (i := tP) (j := tAp) blank _ Move.left (by decide)).trans
      (applyAct'_put_ne (i := tC2) (j := tAp) blank ts blank Move.right (by decide))
  have hRn : u2 tRn = ts tRn := by
    rw [hu2, hu1]
    exact (applyAct'_keep_ne (i := tP) (j := tRn) blank _ Move.left (by decide)).trans
      (applyAct'_put_ne (i := tC2) (j := tRn) blank ts blank Move.right (by decide))
  have e3 := qDecProg_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) u2
  rw [qDecActs_congr hAp hRn] at e3
  have := execA_seq e1 (execA_seq e2 e3)
  refine execA_of_eq ?_ this
  simp

theorem perLoop1X_succ_append (blank mark : Fin sc) (m : ℕ) (vt : VTapes' sc)
    (x : VAct' sc) :
    perLoop1X blank mark (m + 1) vt ++ [x] = VAct'.S (Act'.put tC1 blank .left) ::
      ((VAct'.S (Act'.put tC1 blank .stay) ::
          (([Act'.put tC2 blank .right, Act'.keep tP .left] ++
            qDecActs blank mark vt.1).map VAct'.S ++ [VAct'.X .right])) ++
        (perLoop1X blank mark m (vApplyActs' blank (perDownX blank mark vt) vt) ++ [x])) := by
  rw [PalPeg.GSVTapes.perLoop1X]
  unfold PalPeg.GSVTapes.perDownX perDown perPre
  simp

theorem perLoop1X_head (blank mark : Fin sc) (n : ℕ) (vt : VTapes' sc) :
    ∃ L, perLoop1X blank mark n vt ++ [VAct'.S (Act'.put tC1 blank .left)]
      = VAct'.S (Act'.put tC1 blank .left) :: L := by
  cases n with
  | zero => exact ⟨[], rfl⟩
  | succ m => exact ⟨_, perLoop1X_succ_append blank mark m vt _⟩

/-- **相乗り下げループの一致**。 -/
theorem perDownLoopX_exec (hne : mark ≠ blank) :
    ∀ (n : ℕ) (vt : VTapes' sc) (L : List (VAct' sc)),
      Tape.CounterView' blank mark (vt.1 tC1) n →
      perLoop1X blank mark n vt ++ [VAct'.S (Act'.put tC1 blank .left)]
        = VAct'.S (Act'.put tC1 blank .left) :: L →
      ExecV Terminal blank endSym mark startSym perDownLoopX
        (vApplyAct' blank vt (VAct'.S (Act'.put tC1 blank .left))) L := by
  intro n
  induction n with
  | zero =>
      intro vt L hC heq
      have hL : L = [] := by
        have h0 : perLoop1X blank mark 0 vt = [] := rfl
        rw [h0, List.nil_append] at heq
        exact ((List.cons.inj heq).2).symm
      subst hL
      refine execV_loop_stop' ?_
      rw [condV_fc, vApplyAct'_S_fst, counter_probe_cond hne hC]
      simp
  | succ m ih =>
      intro vt L hC heq
      rw [perLoop1X_succ_append] at heq
      have hL := ((List.cons.inj heq).2).symm
      subst hL
      set vt₁ := vApplyActs' blank (perDownX blank mark vt) vt with hvt₁
      obtain ⟨L₂, hL₂⟩ := perLoop1X_head blank mark m vt₁
      set L₁ : List (VAct' sc) :=
        (([Act'.put tC2 blank .right, Act'.keep tP .left] ++
          qDecActs blank mark vt.1).map VAct'.S ++ [VAct'.X .right]) ++
          [VAct'.S (Act'.put tC1 blank .left)] with hL₁
      have hsplit :
          (VAct'.S (Act'.put tC1 blank .stay) ::
              (([Act'.put tC2 blank .right, Act'.keep tP .left] ++
                qDecActs blank mark vt.1).map VAct'.S ++ [VAct'.X .right])) ++
              (perLoop1X blank mark m vt₁ ++ [VAct'.S (Act'.put tC1 blank .left)])
            = VAct'.S (Act'.put tC1 blank .stay) :: (L₁ ++ L₂) := by
        rw [hL₂, hL₁]; simp
      rw [hsplit]
      set w0 := vApplyAct' blank (vApplyAct' blank vt (VAct'.S (Act'.put tC1 blank .left)))
        (VAct'.S (Act'.put tC1 blank .stay)) with hw0
      have hcat : [VAct'.S (Act'.put tC1 blank .left),
            VAct'.S (Act'.put tC1 blank (sc := sc) .stay)] ++ L₁
          = perDownX blank mark vt ++ [VAct'.S (Act'.put tC1 blank .left)] := by
        rw [hL₁]
        unfold PalPeg.GSVTapes.perDownX perDown perPre
        simp
      have hu0 : w0 = vApplyActs' blank [VAct'.S (Act'.put tC1 blank .left),
          VAct'.S (Act'.put tC1 blank (sc := sc) .stay)] vt := rfl
      have hstate : vApplyActs' blank L₁ w0
          = vApplyAct' blank vt₁ (VAct'.S (Act'.put tC1 blank .left)) := by
        rw [hu0, ← PalPeg.GSVTapes.vApplyActs'_append, hcat,
          PalPeg.GSVTapes.vApplyActs'_append, hvt₁]
        rfl
      refine execV_loop_contS ?_ ?_ ?_
      · rw [condV_fc, vApplyAct'_S_fst, counter_probe_cond hne hC]; simp
      · -- 本体
        have hAp : w0.1 tAp = vt.1 tAp := by
          rw [hw0]
          exact (applyAct'_put_ne (i := tC1) (j := tAp) blank _ blank Move.stay (by decide)).trans
            (applyAct'_put_ne (i := tC1) (j := tAp) blank vt.1 blank Move.left (by decide))
        have hRn : w0.1 tRn = vt.1 tRn := by
          rw [hw0]
          exact (applyAct'_put_ne (i := tC1) (j := tRn) blank _ blank Move.stay (by decide)).trans
            (applyAct'_put_ne (i := tC1) (j := tRn) blank vt.1 blank Move.left (by decide))
        have e1 := perBodyPre_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
          (mark := mark) (startSym := startSym) w0.1
        rw [qDecActs_congr hAp hRn] at e1
        have e1' := execV_lift (Terminal := Terminal) (vt := w0) e1
        set w1 := vApplyActs' blank
          (([Act'.put tC2 blank .right, Act'.keep tP .left] ++
            qDecActs blank mark vt.1).map VAct'.S) w0 with hw1
        have e2 := execV_keepX (Terminal := Terminal) (blank := blank) (endSym := endSym)
          (mark := mark) (startSym := startSym) Move.right w1
        set w2 := vApplyActs' blank [VAct'.X (sc := sc) .right] w1 with hw2
        have e3 := execV_put8 (Terminal := Terminal) (blank := blank) (endSym := endSym)
          (mark := mark) (startSym := startSym) tC1 Move.left w2
        have := execV_seq e1' (execV_seq e2 e3)
        refine execV_of_eq ?_ this
        rw [hL₁]; simp
      · rw [hstate]
        refine ih vt₁ L₂ ?_ hL₂
        have h1 : vt₁.1 = applyActs' blank (perDown blank mark vt.1) vt.1 := by
          rw [hvt₁]; exact PalPeg.GSVTapes.perDownX_fst blank mark vt
        rw [h1, perDown_tC1]
        exact Tape.counter'_dec hC

end PerXSpec

section PerProgXSpec

variable {Terminal : Type} {blank endSym mark startSym : Fin sc}

/-- **相乗り版・周期ずらし枝の一致**。 -/
theorem perProgX_exec (hne : mark ≠ blank) {w : List (Fin sc)} {vt : VTapes' sc}
    {p₁ q mm r : ℕ} (hle : p₁ ≤ q)
    (hP : Tape.SeqView blank (vt.1 tP) w (q + 1))
    (hc1 : Tape.CounterView' blank mark (vt.1 tC1) p₁)
    (hc2 : Tape.CounterView' blank mark (vt.1 tC2) 0)
    (hQ : CQuad blank mark vt.1 mm r q) :
    ExecV Terminal blank endSym mark startSym perProgX vt
      (perProgramX blank mark p₁ vt) := by
  obtain ⟨lP, l1, l2, lQ, lT⟩ :=
    perLoop1_spec (w := w) hne p₁ vt.1 q p₁ 0 mm r hle (Nat.le_refl _) hP hc1 hc2 hQ
  rw [show p₁ - p₁ = 0 from by omega] at l1
  rw [show (0 : ℕ) + p₁ = p₁ from by omega] at l2
  obtain ⟨LD, hLD⟩ := perLoop1X_head blank mark p₁ vt
  obtain ⟨LU, hLU⟩ := perUp_head blank p₁
  set v := vApplyActs' blank (perLoop1X blank mark p₁ vt) vt with hv
  have hv1 : v.1 = applyActs' blank (perLoop1 blank mark p₁ vt.1) vt.1 := by
    rw [hv]; exact PalPeg.GSVTapes.perLoop1X_fst blank mark p₁ vt
  rw [← hv1] at l1 l2
  have hchain : vApplyActs' blank [VAct'.S (Act'.keep tC1 (sc := sc) .right)]
      (vApplyActs' blank LD
        (vApplyActs' blank [VAct'.S (Act'.put tC1 blank .left)] vt)) = v := by
    rw [← PalPeg.GSVTapes.vApplyActs'_append, ← PalPeg.GSVTapes.vApplyActs'_append,
      ← List.append_assoc, List.singleton_append, ← hLD]
    have hl : perLoop1X blank mark p₁ vt ++ [VAct'.S (Act'.put tC1 blank .left)] ++
        [VAct'.S (Act'.keep tC1 (sc := sc) .right)]
        = perLoop1X blank mark p₁ vt ++ (probeActs blank tC1).map VAct'.S := by
      unfold probeActs; simp
    rw [hl, PalPeg.GSVTapes.vApplyActs'_append, ← hv, vApplyActs'_mapS, probeActs_id l1]
  have e0 := execV_put8 (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tC1 Move.left vt
  have eDown := perDownLoopX_exec (Terminal := Terminal) (endSym := endSym)
    (startSym := startSym) hne p₁ vt LD hc1 hLD
  have eK1 := execV_keep8 (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tC1 Move.right
    (vApplyActs' blank LD (vApplyActs' blank [VAct'.S (Act'.put tC1 blank .left)] vt))
  have eP2 := execV_put8 (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tC2 Move.left v
  have eUp := execV_lift (Terminal := Terminal)
    (vt := vApplyActs' blank [VAct'.S (Act'.put tC2 blank (sc := sc) .left)] v)
    (perUpLoop_exec (Terminal := Terminal) (endSym := endSym) (startSym := startSym)
      hne p₁ v.1 LU l2 hLU)
  have eK2 := execV_keep8 (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tC2 Move.right
    (vApplyActs' blank (LU.map VAct'.S)
      (vApplyActs' blank [VAct'.S (Act'.put tC2 blank (sc := sc) .left)] v))
  have eRest : ExecV Terminal blank endSym mark startSym
      (Prog.seq (pmap (KEEP tC1 Move.right))
        (Prog.seq (pmap (PUT tC2 Move.left))
          (Prog.seq (pmap perUpLoop) (pmap (KEEP tC2 Move.right)))))
      (vApplyActs' blank LD (vApplyActs' blank [VAct'.S (Act'.put tC1 blank .left)] vt))
      ([VAct'.S (Act'.keep tC1 (sc := sc) .right)] ++
        ([VAct'.S (Act'.put tC2 blank .left)] ++
          (LU.map VAct'.S ++ [VAct'.S (Act'.keep tC2 (sc := sc) .right)]))) := by
    refine execV_seq eK1 ?_
    rw [hchain]
    exact execV_seq eP2 (execV_seq eUp eK2)
  have hbig := execV_seq e0 (execV_seq eDown eRest)
  refine execV_of_eq ?_ hbig
  have hLU' : (perUp blank p₁).map VAct'.S ++ [VAct'.S (Act'.put tC2 blank (sc := sc) .left)]
      = VAct'.S (Act'.put tC2 blank (sc := sc) .left) :: LU.map VAct'.S := by
    rw [← List.map_singleton (f := VAct'.S), ← List.map_append, hLU, List.map_cons]
  have hassoc : [VAct'.S (Act'.put tC1 blank (sc := sc) .left)] ++
        (LD ++ ([VAct'.S (Act'.keep tC1 (sc := sc) .right)] ++
          ([VAct'.S (Act'.put tC2 blank .left)] ++
            (LU.map VAct'.S ++ [VAct'.S (Act'.keep tC2 (sc := sc) .right)]))))
      = (VAct'.S (Act'.put tC1 blank .left) :: LD) ++
          [VAct'.S (Act'.keep tC1 (sc := sc) .right)] ++
        ((VAct'.S (Act'.put tC2 blank .left) :: LU.map VAct'.S) ++
          [VAct'.S (Act'.keep tC2 (sc := sc) .right)]) := by
    simp
  rw [hassoc, ← hLD, ← hLU']
  unfold perProgramX probeActs
  simp

end PerProgXSpec

/-! ## 3. リセットずらし枝（相乗り版） -/

section ResX

/-- 相乗り版のリセットループ。位相 `0` の周（`resDown1X`）だけが `Txt2` を 1 歩進める。 -/
def resLoopProgX (k : ℕ) : Prog Act10 Cond10 :=
  Prog.loop (fc Cond8.notStart) (fa (tAp, false, Move.left))
    (Prog.seq (pmap qDecTail) (Prog.seq (KEEP10 tX .right) (pmap (resChain (k - 1)))))

/-- 相乗り版のリセットずらし枝の全体。 -/
def resProgX (k : ℕ) : Prog Act10 Cond10 :=
  Prog.seq (pmap (KEEP tP .left))
    (Prog.ite (fc Cond8.notStart)
      (Prog.seq (resLoopProgX k) (pmap (KEEP tP .right)))
      (Prog.seq (pmap (KEEP tP .right))
        (Prog.seq (pmap (KEEP tT .right)) (KEEP10 tX .right))))

end ResX

section ResXSpec

variable {Terminal : Type} {blank endSym mark startSym : Fin sc} {v : List (Fin sc)}

/-- 逐次実行の分解（10 本テープ版）。 -/
def SplitExecV (Terminal : Type) (blank endSym mark startSym : Fin sc)
    (P Q : Prog Act10 Cond10) (vt : VTapes' sc) (L : List (VAct' sc)) : Prop :=
  ∃ X Y, L = X ++ Y ∧ ExecV Terminal blank endSym mark startSym P vt X ∧
    ExecV Terminal blank endSym mark startSym Q (vApplyActs' blank X vt) Y

theorem vApplyActs'_singleton (blank : Fin sc) (a : VAct' sc) (vt : VTapes' sc) :
    vApplyActs' blank [a] vt = vApplyAct' blank vt a := rfl

theorem execV_of_split {P Q : Prog Act10 Cond10} {vt : VTapes' sc} {L : List (VAct' sc)}
    (h : SplitExecV Terminal blank endSym mark startSym P Q vt L) :
    ExecV Terminal blank endSym mark startSym (Prog.seq P Q) vt L := by
  obtain ⟨X, Y, rfl, h1, h2⟩ := h
  exact execV_seq h1 h2

theorem resCondV {vt : VTapes' sc} {n : ℕ} (hstart : startSym ∉ v) (hn : n ≤ v.length)
    (hP : Tape.SeqView blank (vt.1 tP) (startSym :: (v ++ [endSym])) (n + 1)) :
    condOf10 endSym mark startSym (fc Cond8.notStart)
        (fun j => ((vTS (vApplyAct' blank vt (VAct'.S (Act'.keep tP .left)))) j).focus)
      = decide (n ≠ 0) := by
  rw [condV_fc, vApplyAct'_S_fst]
  exact resCond hstart hn hP

theorem resDown1X_cons (blank mark : Fin sc) (vt : VTapes' sc) :
    resDown1X blank mark vt = VAct'.S (Act'.keep tP .left) ::
      ((qDecActs blank mark vt.1).map VAct'.S ++ [VAct'.X .right]) := by
  unfold PalPeg.GSVTapes.resDown1X resDown1
  simp

theorem resDown2X_cons (blank mark : Fin sc) (vt : VTapes' sc) :
    resDown2X blank mark vt = VAct'.S (Act'.keep tP .left) ::
      (VAct'.S (Act'.keep tT .left) :: (qDecActs blank mark vt.1).map VAct'.S) := by
  unfold PalPeg.GSVTapes.resDown2X resDown2
  simp

theorem resLoopX_succ_zero (blank mark : Fin sc) (k m : ℕ) (vt : VTapes' sc) :
    resLoopX blank mark k (m + 1) 0 vt ++ [VAct'.S (Act'.keep tP .left)]
      = VAct'.S (Act'.keep tP .left) ::
        (((qDecActs blank mark vt.1).map VAct'.S ++ [VAct'.X .right]) ++
          (resLoopX blank mark k m (k - 1)
              (vApplyActs' blank (resDown1X blank mark vt) vt) ++
            [VAct'.S (Act'.keep tP .left)])) := by
  rw [PalPeg.GSVTapes.resLoopX, resDown1X_cons]
  simp

theorem resLoopX_succ_succ (blank mark : Fin sc) (k m j : ℕ) (vt : VTapes' sc) :
    resLoopX blank mark k (m + 1) (j + 1) vt ++ [VAct'.S (Act'.keep tP .left)]
      = VAct'.S (Act'.keep tP .left) ::
        ((VAct'.S (Act'.keep tT .left) :: (qDecActs blank mark vt.1).map VAct'.S) ++
          (resLoopX blank mark k m j (vApplyActs' blank (resDown2X blank mark vt) vt) ++
            [VAct'.S (Act'.keep tP .left)])) := by
  rw [PalPeg.GSVTapes.resLoopX, resDown2X_cons]
  simp

theorem resLoopX_head (blank mark : Fin sc) (k n c : ℕ) (vt : VTapes' sc) :
    ∃ L, resLoopX blank mark k n c vt ++ [VAct'.S (Act'.keep tP .left)]
      = VAct'.S (Act'.keep tP .left) :: L := by
  cases n with
  | zero => exact ⟨[], rfl⟩
  | succ m =>
      cases c with
      | zero => exact ⟨_, resLoopX_succ_zero blank mark k m vt⟩
      | succ j => exact ⟨_, resLoopX_succ_succ blank mark k m j vt⟩

end ResXSpec

section ResKeyX

variable {Terminal : Type} {blank endSym mark startSym : Fin sc} {v : List (Fin sc)}

/-- **主補題：相乗り版ループと鎖の一致**（`n` に関する強帰納法）。 -/
theorem res_keyX (hstart : startSym ∉ v) (k : ℕ) :
    ∀ n : ℕ,
      (∀ (vt : VTapes' sc) (L : List (VAct' sc)), n ≤ v.length →
        Tape.SeqView blank (vt.1 tP) (startSym :: (v ++ [endSym])) (n + 1) →
        resLoopX blank mark k n 0 vt ++ [VAct'.S (Act'.keep tP .left)]
          = VAct'.S (Act'.keep tP .left) :: L →
        ExecV Terminal blank endSym mark startSym (resLoopProgX k)
          (vApplyAct' blank vt (VAct'.S (Act'.keep tP .left))) L)
      ∧ (∀ (j : ℕ) (vt : VTapes' sc), n ≤ v.length →
        Tape.SeqView blank (vt.1 tP) (startSym :: (v ++ [endSym])) (n + 1) →
        SplitExecV Terminal blank endSym mark startSym (pmap (resChain j)) (resLoopProgX k) vt
          (resLoopX blank mark k n j vt ++ [VAct'.S (Act'.keep tP .left)])) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    cases n with
    | zero =>
        have hloop : ∀ (vt : VTapes' sc) (L : List (VAct' sc)), 0 ≤ v.length →
            Tape.SeqView blank (vt.1 tP) (startSym :: (v ++ [endSym])) (0 + 1) →
            resLoopX blank mark k 0 0 vt ++ [VAct'.S (Act'.keep tP .left)]
              = VAct'.S (Act'.keep tP .left) :: L →
            ExecV Terminal blank endSym mark startSym (resLoopProgX k)
              (vApplyAct' blank vt (VAct'.S (Act'.keep tP .left))) L := by
          intro vt L hn hP heq
          have hL : L = [] := by
            have h0 : resLoopX blank mark k 0 0 vt = [] := rfl
            rw [h0, List.nil_append] at heq
            exact ((List.cons.inj heq).2).symm
          subst hL
          exact execV_loop_stop' (by rw [resCondV hstart hn hP]; simp)
        refine ⟨hloop, ?_⟩
        intro j vt hn hP
        refine ⟨[VAct'.S (Act'.keep tP .left)], [], rfl, ?_, ?_⟩
        · cases j with
          | zero => exact execV_keep8 tP Move.left vt
          | succ i =>
              have hx : ExecV Terminal blank endSym mark startSym (pmap (resChain (i + 1))) vt
                  ([VAct'.S (Act'.keep tP (sc := sc) .left)] ++ []) :=
                execV_seq (execV_keep8 tP Move.left vt)
                  (execV_ite_neg (by rw [vApplyActs'_singleton, resCondV hstart hn hP]; simp)
                    execV_skip)
              simpa using hx
        · exact hloop vt [] hn hP rfl
    | succ m =>
        have hmlt : m < m + 1 := by omega
        have hloop : ∀ (vt : VTapes' sc) (L : List (VAct' sc)), m + 1 ≤ v.length →
            Tape.SeqView blank (vt.1 tP) (startSym :: (v ++ [endSym])) (m + 1 + 1) →
            resLoopX blank mark k (m + 1) 0 vt ++ [VAct'.S (Act'.keep tP .left)]
              = VAct'.S (Act'.keep tP .left) :: L →
            ExecV Terminal blank endSym mark startSym (resLoopProgX k)
              (vApplyAct' blank vt (VAct'.S (Act'.keep tP .left))) L := by
          intro vt L hn hP heq
          rw [resLoopX_succ_zero] at heq
          have hL := ((List.cons.inj heq).2).symm
          subst hL
          set w := vApplyAct' blank vt (VAct'.S (Act'.keep tP (sc := sc) .left)) with hw
          have hAp : w.1 tAp = vt.1 tAp :=
            applyAct'_keep_ne (i := tP) (j := tAp) blank vt.1 Move.left (by decide)
          have hRn : w.1 tRn = vt.1 tRn :=
            applyAct'_keep_ne (i := tP) (j := tRn) blank vt.1 Move.left (by decide)
          have hP' : Tape.SeqView blank (w.1 tP) (startSym :: (v ++ [endSym])) (m + 1) := by
            rw [hw, vApplyAct'_S_fst, applyAct'_keep_self]
            exact Tape.seq_move_left hP
          set vt₁ := vApplyActs' blank (resDown1X blank mark vt) vt with hvt₁
          have hts₁ : vt₁ = vApplyActs' blank
              ((qDecActs blank mark vt.1).map VAct'.S ++ [VAct'.X .right]) w := by
            rw [hvt₁, resDown1X_cons]
            rfl
          have hvt₁1 : vt₁.1 = applyActs' blank (qDecActs blank mark vt.1) w.1 := by
            rw [hts₁, PalPeg.GSVTapes.vApplyActs'_mapS_append_X]
          have hP₁ : Tape.SeqView blank (vt₁.1 tP) (startSym :: (v ++ [endSym])) (m + 1) := by
            rw [hvt₁1,
              qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
            exact hP'
          obtain ⟨Xc, Yc, hXY, hX, hY⟩ := (IH m hmlt).2 (k - 1) vt₁ (by omega) hP₁
          set rest : List (Act' sc) :=
            sUpRest blank mark tAn tAp (vt.1 tAp) ++ sUpActs blank mark tRp tRn (vt.1 tRn)
            with hrest
          have hgoal : ((qDecActs blank mark vt.1).map VAct'.S ++ [VAct'.X .right]) ++
                (resLoopX blank mark k m (k - 1) vt₁ ++ [VAct'.S (Act'.keep tP .left)])
              = VAct'.S (Act'.put tAp blank .left) ::
                ((rest.map VAct'.S ++ ([VAct'.X (sc := sc) .right] ++ Xc)) ++ Yc) := by
            rw [qDecActs_eq_cons, hXY, hrest]
            simp
          rw [hgoal]
          have hstate : vApplyActs' blank (rest.map VAct'.S ++ [VAct'.X (sc := sc) .right])
              (vApplyAct' blank w (VAct'.S (Act'.put tAp blank .left))) = vt₁ := by
            rw [hts₁, qDecActs_eq_cons, hrest]
            rfl
          have hst2 : vApplyActs' blank [VAct'.X (sc := sc) .right]
              (vApplyActs' blank (rest.map VAct'.S)
                (vApplyAct' blank w (VAct'.S (Act'.put tAp blank .left)))) = vt₁ := by
            rw [← PalPeg.GSVTapes.vApplyActs'_append]; exact hstate
          refine execV_loop_contS ?_ ?_ ?_
          · rw [hw, resCondV hstart hn hP]; simp
          · have hd := qDecTail_exec (Terminal := Terminal) (blank := blank)
              (endSym := endSym) (mark := mark) (startSym := startSym) w.1
            rw [hAp, hRn] at hd
            have hd' := execV_lift (Terminal := Terminal)
              (vt := vApplyAct' blank w (VAct'.S (Act'.put tAp blank .left))) hd
            have e2 := execV_keepX (Terminal := Terminal) (blank := blank) (endSym := endSym)
              (mark := mark) (startSym := startSym) Move.right
              (vApplyActs' blank (rest.map VAct'.S)
                (vApplyAct' blank w (VAct'.S (Act'.put tAp blank .left))))
            exact execV_seq hd' (execV_seq e2 (by rw [hst2]; exact hX))
          · rw [PalPeg.GSVTapes.vApplyActs'_append, PalPeg.GSVTapes.vApplyActs'_append, hst2]
            exact hY
        refine ⟨hloop, ?_⟩
        intro j vt hn hP
        cases j with
        | zero =>
            exact ⟨[VAct'.S (Act'.keep tP .left)], _, resLoopX_succ_zero blank mark k m vt,
              execV_keep8 tP Move.left vt,
              hloop vt _ hn hP (resLoopX_succ_zero blank mark k m vt)⟩
        | succ i =>
            set w := vApplyAct' blank vt (VAct'.S (Act'.keep tP (sc := sc) .left)) with hw
            set w2 := vApplyAct' blank w (VAct'.S (Act'.keep tT (sc := sc) .left)) with hw2
            have hAp : w2.1 tAp = vt.1 tAp :=
              (applyAct'_keep_ne (i := tT) (j := tAp) blank w.1 Move.left (by decide)).trans
                (applyAct'_keep_ne (i := tP) (j := tAp) blank vt.1 Move.left (by decide))
            have hRn : w2.1 tRn = vt.1 tRn :=
              (applyAct'_keep_ne (i := tT) (j := tRn) blank w.1 Move.left (by decide)).trans
                (applyAct'_keep_ne (i := tP) (j := tRn) blank vt.1 Move.left (by decide))
            have hP2 : Tape.SeqView blank (w2.1 tP) (startSym :: (v ++ [endSym])) (m + 1) := by
              rw [hw2, vApplyAct'_S_fst,
                applyAct'_keep_ne (i := tT) (j := tP) blank w.1 Move.left (by decide),
                hw, vApplyAct'_S_fst, applyAct'_keep_self]
              exact Tape.seq_move_left hP
            set vt₂ := vApplyActs' blank (resDown2X blank mark vt) vt with hvt₂
            have hts₂ : vt₂ = vApplyActs' blank ((qDecActs blank mark vt.1).map VAct'.S) w2 := by
              rw [hvt₂, resDown2X_cons]
              rfl
            have hvt₂1 : vt₂.1 = applyActs' blank (qDecActs blank mark vt.1) w2.1 := by
              rw [hts₂, vApplyActs'_mapS]
            have hP₂ : Tape.SeqView blank (vt₂.1 tP) (startSym :: (v ++ [endSym])) (m + 1) := by
              rw [hvt₂1,
                qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
              exact hP2
            obtain ⟨Xc, Yc, hXY, hX, hY⟩ := (IH m hmlt).2 i vt₂ (by omega) hP₂
            refine ⟨VAct'.S (Act'.keep tP .left) ::
              ([VAct'.S (Act'.keep tT (sc := sc) .left)] ++
                ((qDecActs blank mark vt.1).map VAct'.S ++ Xc)), Yc, ?_, ?_, ?_⟩
            · rw [resLoopX_succ_succ, hXY]; simp
            · refine execV_seq (execV_keep8 tP Move.left vt) ?_
              rw [vApplyActs'_singleton, ← hw]
              refine execV_ite_pos (by rw [hw, resCondV hstart hn hP]; simp) ?_
              refine execV_seq (execV_keep8 tT Move.left w) ?_
              rw [vApplyActs'_singleton, ← hw2]
              have hq8 := qDecProg_exec (Terminal := Terminal) (blank := blank)
                (endSym := endSym) (mark := mark) (startSym := startSym) w2.1
              rw [qDecActs_congr hAp hRn] at hq8
              have hq := execV_lift (Terminal := Terminal) (vt := w2) hq8
              refine execV_seq hq ?_
              rw [← hts₂]
              exact hX
            · rw [show vApplyActs' blank (VAct'.S (Act'.keep tP .left) ::
                    ([VAct'.S (Act'.keep tT (sc := sc) .left)] ++
                      ((qDecActs blank mark vt.1).map VAct'.S ++ Xc))) vt
                  = vApplyActs' blank Xc vt₂ from by
                    rw [hts₂]
                    simp only [PalPeg.GSVTapes.vApplyActs'_cons,
                      PalPeg.GSVTapes.vApplyActs'_append]
                    rfl]
              exact hY

/-- **相乗り版・リセットずらし枝の一致**。 -/
theorem resProgX_exec (hstart : startSym ∉ v) (k n : ℕ) (vt : VTapes' sc)
    (hn : n ≤ v.length)
    (hP : Tape.SeqView blank (vt.1 tP) (startSym :: (v ++ [endSym])) (n + 1)) :
    ExecV Terminal blank endSym mark startSym (resProgX k) vt
      (resProgramX blank mark k n vt) := by
  cases n with
  | zero =>
      have hlist : resProgramX blank mark k 0 vt
          = [VAct'.S (Act'.keep tP (sc := sc) .left)] ++
            ([VAct'.S (Act'.keep tP (sc := sc) .right)] ++
              ([VAct'.S (Act'.keep tT (sc := sc) .right)] ++ [VAct'.X (sc := sc) .right])) := by
        unfold PalPeg.GSVTapes.resProgramX
        have h0 : resLoopX blank mark k 0 0 vt = [] := rfl
        rw [h0]
        simp
      rw [hlist]
      refine execV_seq (execV_keep8 tP Move.left vt) ?_
      refine execV_ite_neg (by rw [vApplyActs'_singleton, resCondV hstart hn hP]; simp) ?_
      exact execV_seq (execV_keep8 tP Move.right _)
        (execV_seq (execV_keep8 tT Move.right _) (execV_keepX Move.right _))
  | succ m =>
      obtain ⟨L, hL⟩ := resLoopX_head blank mark k (m + 1) 0 vt
      have hlist : resProgramX blank mark k (m + 1) vt
          = [VAct'.S (Act'.keep tP (sc := sc) .left)] ++
            (L ++ [VAct'.S (Act'.keep tP (sc := sc) .right)]) := by
        unfold PalPeg.GSVTapes.resProgramX
        rw [show ((if m + 1 = 0 then
            [VAct'.S (Act'.keep tT (sc := sc) .right), VAct'.X (sc := sc) .right] else [])
            : List (VAct' sc)) = [] from by simp]
        rw [show (VAct'.S (Act'.keep tP (sc := sc) .left) ::
            VAct'.S (Act'.keep tP (sc := sc) .right) :: ([] : List (VAct' sc)))
          = [VAct'.S (Act'.keep tP (sc := sc) .left)] ++
            [VAct'.S (Act'.keep tP (sc := sc) .right)] from rfl,
          ← List.append_assoc, hL]
        simp
      rw [hlist]
      refine execV_seq (execV_keep8 tP Move.left vt) ?_
      refine execV_ite_pos (by rw [vApplyActs'_singleton, resCondV hstart hn hP]; simp) ?_
      refine execV_seq ?_ (execV_keep8 tP Move.right _)
      rw [vApplyActs'_singleton]
      exact (res_keyX (Terminal := Terminal) (endSym := endSym) (mark := mark) hstart
        k (m + 1)).1 vt L hn hP hL

end ResKeyX

/-! ## 4. `U` と `Txt2` の同時巻き戻し -/

section UX

/-- `U` が `startSym` を読むまで `U .left; X .left` を繰り返す。 -/
def uxRewindProg : Prog Act10 Cond10 :=
  Prog.loop Cond10.notStartU (tU, true, .left) (KEEP10 tX .left)

/-- 巻き戻し＋復帰（`U` と `Txt2` を同時に）。 -/
def uxWalkProg : Prog Act10 Cond10 :=
  Prog.seq uxRewindProg (Prog.seq (KEEP10 tU .right) (KEEP10 tX .right))

end UX

section UXSpec

variable {Terminal : Type} {blank endSym mark startSym : Fin sc}

@[simp] theorem vApplyAct'_X_U (blank : Fin sc) (vt : VTapes' sc) (m : Move) :
    (vApplyAct' blank vt (VAct'.X m)).2.U = vt.2.U := rfl

@[simp] theorem vApplyAct'_U_U (blank : Fin sc) (vt : VTapes' sc) (m : Move) :
    (vApplyAct' blank vt (VAct'.U m)).2.U = Tape.step blank vt.2.U vt.2.U.focus m := rfl

/-- **同時巻き戻しループの実現**：ヘッド添字 `i` から `startSym` まで、
ちょうど `2 * i` 動作（`U .left; X .left` を `i` 回）。 -/
theorem uxRewindProg_exec {u : List (Fin sc)} (hsu : startSym ∉ u) (hse : startSym ≠ endSym) :
    ∀ (i : ℕ) (vt : VTapes' sc),
      Tape.SeqView blank vt.2.U (startSym :: (u ++ [endSym])) i →
      ExecV Terminal blank endSym mark startSym uxRewindProg vt (uxWalkLoop i) := by
  intro i
  induction i with
  | zero =>
      intro vt hv
      have hr := hv.read_eq
      simp only [List.getElem?_cons_zero] at hr
      refine execV_loop_stop' ?_
      rw [notStartU_eq]
      simp only [decide_eq_false_iff_not, not_not]
      exact (Option.some.inj hr).symm
  | succ i ih =>
      intro vt hv
      have hr := hv.read_eq
      rw [List.getElem?_cons_succ] at hr
      have hmem : Tape.read vt.2.U ∈ u ++ [endSym] := by
        have : (u ++ [endSym])[i]? = some (Tape.read vt.2.U) := hr
        exact List.mem_of_getElem? this
      have hne : Tape.read vt.2.U ≠ startSym := by
        intro hcon
        rcases List.mem_append.1 hmem with h | h
        · exact hsu (hcon ▸ h)
        · simp only [List.mem_singleton] at h
          exact hse (hcon ▸ h)
      have hv' : Tape.SeqView blank
          (vApplyActs' blank [VAct'.X (sc := sc) .left]
            (vApplyAct' blank vt (VAct'.U .left))).2.U
          (startSym :: (u ++ [endSym])) i := by
        show Tape.SeqView blank (Tape.step blank vt.2.U vt.2.U.focus .left) _ i
        exact Tape.seq_move_left hv
      have h2 := ih (vApplyActs' blank [VAct'.X (sc := sc) .left]
        (vApplyAct' blank vt (VAct'.U .left))) hv'
      refine execV_of_eq ?_
        (execV_loop_contU (b := KEEP10 tX .left) (L₁ := [VAct'.X (sc := sc) .left])
          (L₂ := uxWalkLoop i)
          (by rw [notStartU_eq]; exact decide_eq_true hne)
          (execV_keepX Move.left (vApplyAct' blank vt (VAct'.U .left))) h2)
      rw [PalPeg.GSVTapes.uxWalkLoop]
      simp

/-- **`uxWalkProg` の実現**：動作列はちょうど `uxWalk vt`。 -/
theorem uxWalkProg_exec {u : List (Fin sc)} (hsu : startSym ∉ u) (hse : startSym ≠ endSym)
    (c : ℕ) (vt : VTapes' sc)
    (hv : Tape.SeqView blank vt.2.U (startSym :: (u ++ [endSym])) (c + 1)) :
    ExecV Terminal blank endSym mark startSym uxWalkProg vt (uxWalk vt) := by
  have hc : cOf vt.2 = c := PalPeg.GSVTapes.cOf_eq hv
  have h1 := uxRewindProg_exec (Terminal := Terminal) (endSym := endSym) (mark := mark)
    hsu hse (c + 1) vt hv
  have h2 := execV_keepU (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) Move.right
    (vApplyActs' blank (uxWalkLoop (c + 1)) vt)
  have h3 := execV_keepX (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) Move.right
    (vApplyActs' blank [VAct'.U (sc := sc) .right]
      (vApplyActs' blank (uxWalkLoop (c + 1)) vt))
  refine execV_of_eq ?_ (execV_seq h1 (execV_seq h2 h3))
  unfold PalPeg.GSVTapes.uxWalk
  rw [hc]
  simp

end UXSpec

/-! ## 5. ずらし枝の全体 -/

section Shift

/-- ずらし枝の本体（プローブ＋分岐）。`scanProg` のずらし側と同じ形。 -/
def shiftCore (k : ℕ) : Prog Act10 Cond10 :=
  Prog.seq (pmap (PUT tAn .left))
    (Prog.ite (fc (Cond8.notMark tAn))
      (Prog.seq (pmap (KEEP tAn .right))
        (Prog.seq (pmap (PUT tRn .left)) (Prog.seq (pmap (KEEP tRn .right)) (resProgX k))))
      (Prog.seq (pmap (KEEP tAn .right))
        (Prog.seq (pmap (PUT tRn .left))
          (Prog.ite (fc (Cond8.notMark tRn))
            (Prog.seq (pmap (KEEP tRn .right)) (resProgX k))
            (Prog.seq (pmap (KEEP tRn .right)) perProgX)))))

/-- ずらし枝の全体：プローブ＋分岐＋同時巻き戻し。 -/
def shiftProg (k : ℕ) : Prog Act10 Cond10 := Prog.seq (shiftCore k) uxWalkProg

/-- ずらし枝の分岐部分の動作列。 -/
def shiftBranch (blank mark : Fin sc) (k : ℕ) (vt : VTapes' sc) : List (VAct' sc) :=
  if Tape.read (Tape.step blank (vt.1 tAn) blank .left) = mark ∧
      Tape.read (Tape.step blank (vt.1 tRn) blank .left) = mark then
    perProgramX blank mark (p1Of' vt.1) vt
  else resProgramX blank mark k (qOf' vt.1) vt

/-- `shiftCore` の動作列。 -/
def shiftCoreActs (blank mark : Fin sc) (k : ℕ) (vt : VTapes' sc) : List (VAct' sc) :=
  (probeActs blank tAn).map VAct'.S ++ (probeActs blank tRn).map VAct'.S ++
    shiftBranch blank mark k vt

/-- `shiftProg` の動作列（`vprogramX` のずらし枝そのもの）。 -/
def shiftActs (blank mark : Fin sc) (k : ℕ) (vt : VTapes' sc) : List (VAct' sc) :=
  shiftCoreActs blank mark k vt ++ uxWalk vt

theorem vprogramX_shift (blank endSym mark : Fin sc) (k : ℕ) (vt : VTapes' sc)
    (hadv : ¬ (Tape.read (vt.1 tP) ≠ endSym ∧ Tape.read (vt.1 tP) = Tape.read (vt.1 tT))) :
    vprogramX blank endSym mark k vt = shiftActs blank mark k vt := by
  unfold PalPeg.GSVTapes.vprogramX shiftActs shiftCoreActs shiftBranch
  rw [if_neg hadv]

end Shift

section ShiftSpec

variable {Terminal : Type} {blank endSym mark startSym : Fin sc}
variable {u v Text : List (Fin sc)} {k p₁ r : ℕ} {vt : VTapes' sc} {z : VState}

/-- 分岐部分は `U` を動かさない。 -/
theorem shiftBranch_U (blank mark : Fin sc) (k : ℕ) (vt : VTapes' sc) :
    (vApplyActs' blank (shiftBranch blank mark k vt) vt).2.U = vt.2.U := by
  unfold shiftBranch
  split
  · exact PalPeg.GSVTapes.perProgramX_U blank mark _ vt
  · exact PalPeg.GSVTapes.resProgramX_U blank mark k _ vt

/-- **ずらし枝の本体の一致**。 -/
theorem shiftCore_exec (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v)
    (hE : GSTapes.Encodes' blank startSym endSym mark v Text k p₁ r vt.1 z.1)
    (hq : z.1.q ≤ v.length) :
    ExecV Terminal blank endSym mark startSym (shiftCore k) vt
      (shiftCoreActs blank mark k vt) := by
  have hA : vApplyActs' blank [VAct'.S (Act'.keep tAn (sc := sc) .right)]
      (vApplyActs' blank [VAct'.S (Act'.put tAn blank .left)] vt) = vt := by
    rw [← PalPeg.GSVTapes.vApplyActs'_append,
      show ([VAct'.S (Act'.put tAn blank .left)] ++
          [VAct'.S (Act'.keep tAn (sc := sc) .right)])
        = (probeActs blank tAn).map VAct'.S from by unfold probeActs; simp,
      vApplyActs'_mapS, probeActs_id hE.quad.an]
  have hR : vApplyActs' blank [VAct'.S (Act'.keep tRn (sc := sc) .right)]
      (vApplyActs' blank [VAct'.S (Act'.put tRn blank .left)] vt) = vt := by
    rw [← PalPeg.GSVTapes.vApplyActs'_append,
      show ([VAct'.S (Act'.put tRn blank .left)] ++
          [VAct'.S (Act'.keep tRn (sc := sc) .right)])
        = (probeActs blank tRn).map VAct'.S from by unfold probeActs; simp,
      vApplyActs'_mapS, probeActs_id hE.quad.rn]
  have hsplit : ∀ REST : List (VAct' sc),
      (probeActs blank tAn).map VAct'.S ++ (probeActs blank tRn).map VAct'.S ++ REST
        = [VAct'.S (Act'.put tAn blank .left)] ++
          ([VAct'.S (Act'.keep tAn (sc := sc) .right)] ++
            ([VAct'.S (Act'.put tRn blank .left)] ++
              ([VAct'.S (Act'.keep tRn (sc := sc) .right)] ++ REST))) := by
    intro REST; unfold probeActs; simp
  unfold shiftCoreActs shiftBranch
  by_cases hbAn : Tape.read (Tape.step blank (vt.1 tAn) blank .left) = mark
  · by_cases hbRn : Tape.read (Tape.step blank (vt.1 tRn) blank .left) = mark
    · rw [if_pos ⟨hbAn, hbRn⟩, hsplit]
      refine execV_seq (execV_put8 tAn Move.left vt) ?_
      refine execV_ite_neg (by
        rw [vApplyActs'_singleton, condV_fc, vApplyAct'_S_fst, probe_cond]
        simp only [Tape.read] at hbAn; simp [hbAn]) ?_
      refine execV_seq (execV_keep8 tAn Move.right _) ?_
      rw [hA]
      refine execV_seq (execV_put8 tRn Move.left vt) ?_
      refine execV_ite_neg (by
        rw [vApplyActs'_singleton, condV_fc, vApplyAct'_S_fst, probe_cond]
        simp only [Tape.read] at hbRn; simp [hbRn]) ?_
      refine execV_seq (execV_keep8 tRn Move.right _) ?_
      rw [hR]
      have hper := (period_iff' hne hE).1 ⟨hbAn, hbRn⟩
      have hle : p₁ ≤ z.1.q := le_trans (Nat.le_mul_of_pos_left p₁ hk) hper.1
      rw [p1Of'_eq hE]
      exact perProgX_exec (w := startSym :: (v ++ [endSym])) hne hle hE.pat hE.c1 hE.c2
        hE.quad
    · rw [if_neg (fun h => hbRn h.2), hsplit]
      refine execV_seq (execV_put8 tAn Move.left vt) ?_
      refine execV_ite_neg (by
        rw [vApplyActs'_singleton, condV_fc, vApplyAct'_S_fst, probe_cond]
        simp only [Tape.read] at hbAn; simp [hbAn]) ?_
      refine execV_seq (execV_keep8 tAn Move.right _) ?_
      rw [hA]
      refine execV_seq (execV_put8 tRn Move.left vt) ?_
      refine execV_ite_pos (by
        rw [vApplyActs'_singleton, condV_fc, vApplyAct'_S_fst, probe_cond]
        simp only [Tape.read] at hbRn; simp [hbRn]) ?_
      refine execV_seq (execV_keep8 tRn Move.right _) ?_
      rw [hR, qOf'_eq hE]
      exact resProgX_exec hstart k z.1.q vt hq hE.pat
  · rw [if_neg (fun h => hbAn h.1), hsplit]
    refine execV_seq (execV_put8 tAn Move.left vt) ?_
    refine execV_ite_pos (by
      rw [vApplyActs'_singleton, condV_fc, vApplyAct'_S_fst, probe_cond]
      simp only [Tape.read] at hbAn; simp [hbAn]) ?_
    refine execV_seq (execV_keep8 tAn Move.right _) ?_
    rw [hA]
    refine execV_seq (execV_put8 tRn Move.left vt) ?_
    refine execV_seq (execV_keep8 tRn Move.right _) ?_
    rw [hR, qOf'_eq hE]
    exact resProgX_exec hstart k z.1.q vt hq hE.pat

/-- **ずらし枝の一致**：`shiftProg k` は `vprogramX` のずらし枝の動作列を実行する。 -/
theorem shiftProg_exec (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v)
    (hsu : startSym ∉ u) (hse : startSym ≠ endSym)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length) :
    ExecV Terminal blank endSym mark startSym (shiftProg k) vt
      (shiftActs blank mark k vt) := by
  have hcore := shiftCore_exec (Terminal := Terminal) hk hne hstart hE.scan hq
  set s := vApplyActs' blank (shiftCoreActs blank mark k vt) vt with hs
  have hs' : s = vApplyActs' blank (shiftBranch blank mark k vt) vt := by
    rw [hs]
    unfold shiftCoreActs
    rw [PalPeg.GSVTapes.vApplyActs'_append, PalPeg.GSVTapes.vApplyActs'_append,
      vApplyActs'_mapS, vApplyActs'_mapS, probeActs_id hE.scan.quad.an]
    have h2 : applyActs' blank (probeActs blank tRn) vt.1 = vt.1 :=
      probeActs_id hE.scan.quad.rn
    rw [show ((applyActs' blank (probeActs blank tRn) vt.1, vt.2) : VTapes' sc) = vt from by
      rw [h2]]
  have hsU : s.2.U = vt.2.U := by rw [hs', shiftBranch_U]
  have hv : Tape.SeqView blank s.2.U (startSym :: (u ++ [endSym])) (z.2 + 1) := by
    rw [hsU]; exact hE.pat
  have hcOf : cOf s.2 = cOf vt.2 := by unfold PalPeg.GSVTapes.cOf; rw [hsU]
  have hwalk := uxWalkProg_exec (Terminal := Terminal) (mark := mark) hsu hse z.2 s hv
  have hlist : uxWalk s = uxWalk vt := by
    unfold PalPeg.GSVTapes.uxWalk; rw [hcOf]
  rw [hlist] at hwalk
  exact execV_seq hcore hwalk

end ShiftSpec

/-! ## 6. 1 ラウンドの検証器つきプログラム（ずらし枝込み） -/

/-- 比較枝は `vprogProg` と同じ、ずらし枝は `shiftProg`。**`shift` 引数は不要**。 -/
def vprogX (k : ℕ) : Prog Act10 Cond10 :=
  Prog.ite Cond10.matchOk (Prog.seq (pmap (scanProg k)) vcomp2Prog) (shiftProg k)

section RoundXSpec

variable {Terminal : Type} {blank endSym mark startSym : Fin sc}
variable {u v Text : List (Fin sc)} {k p₁ r : ℕ} {vt : VTapes' sc} {z : VState}

/-- **主定理（1 ラウンドの一致、両枝）**：`vprogX k` は状態 `vt` からちょうど
`vprogramX blank endSym mark k vt` の動作列を実行して継続に戻る。 -/
theorem vprogX_exec (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v)
    (hsu : startSym ∉ u) (hse : startSym ≠ endSym)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length) :
    ExecV Terminal blank endSym mark startSym (vprogX k) vt
      (vprogramX blank endSym mark k vt) := by
  unfold vprogX
  by_cases hadv : Tape.read (vt.1 tP) ≠ endSym ∧ Tape.read (vt.1 tP) = Tape.read (vt.1 tT)
  · have hprog : program' blank endSym mark k vt.1 = advActs blank mark vt.1 := by
      unfold program'; rw [if_pos hadv]
    have hscan := execV_lift (Terminal := Terminal) (vt := vt)
      (scanProg_exec (Terminal := Terminal) (startSym := startSym) hk hne hstart hE.scan hq)
    have hsnd : (vApplyActs' blank
        ((program' blank endSym mark k vt.1).map VAct'.S) vt).2 = vt.2 := by
      rw [PalPeg.GSVTapes.vApplyActs'_map_S]
    have hcomp := vcomp2Prog_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
      (mark := mark) (startSym := startSym)
      (vApplyActs' blank ((program' blank endSym mark k vt.1).map VAct'.S) vt)
    rw [hsnd] at hcomp
    refine execV_ite_pos (by rw [matchOk_eq]; exact decide_eq_true hadv) ?_
    refine execV_of_eq ?_ (execV_seq hscan hcomp)
    unfold PalPeg.GSVTapes.vprogramX
    rw [if_pos hadv, hprog]
  · refine execV_ite_neg (by rw [matchOk_eq]; exact decide_eq_false hadv) ?_
    rw [vprogramX_shift blank endSym mark k vt hadv]
    exact shiftProg_exec (Terminal := Terminal) hk hne hstart hsu hse hE hq

/-- **トレースの一致**。 -/
theorem vprogX_trace (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v)
    (hsu : startSym ∉ u) (hse : startSym ≠ endSym)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length)
    (l : List (Option Terminal))
    (hl : l.length = (vprogramX blank endSym mark k vt).length) :
    trace (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
        ([vprogX k], vTS vt)
      = vavecs blank (vprogramX blank endSym mark k vt) vt := by
  have h := vprogX_exec (Terminal := Terminal) (startSym := startSym) hk hne hstart hsu hse
    hE hq
  have h2 := (h [] l (by rw [vavecs_length]; exact hl)).1
  rw [show ([vprogX k] ++ ([] : Stack Act10 Cond10)) = [vprogX k] from rfl] at h2
  exact h2

/-- トレースの長さは動作列の長さに等しい。 -/
theorem vprogX_trace_length (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v)
    (hsu : startSym ∉ u) (hse : startSym ≠ endSym)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length)
    (l : List (Option Terminal))
    (hl : l.length = (vprogramX blank endSym mark k vt).length) :
    (trace (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
        ([vprogX k], vTS vt)).length
      = (vprogramX blank endSym mark k vt).length := by
  rw [vprogX_trace (Terminal := Terminal) (startSym := startSym) hk hne hstart hsu hse hE hq
    l hl, vavecs_length]

/-- **テープの一致**。 -/
theorem vprogX_tapes (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v)
    (hsu : startSym ∉ u) (hse : startSym ≠ endSym)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length)
    (l : List (Option Terminal))
    (hl : l.length = (vprogramX blank endSym mark k vt).length) :
    (runInputs (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
        ([vprogX k], vTS vt)).2
      = vTS (vApplyActs' blank (vprogramX blank endSym mark k vt) vt) := by
  rw [runInputs_snd_eq_applyTrace,
    vprogX_trace (Terminal := Terminal) (startSym := startSym) hk hne hstart hsu hse hE hq l hl]
  exact applyTrace_vavecs blank _ vt

/-- **停止**。 -/
theorem vprogX_halts (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v)
    (hsu : startSym ∉ u) (hse : startSym ≠ endSym)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length)
    (l : List (Option Terminal))
    (hl : l.length = (vprogramX blank endSym mark k vt).length)
    (x : Option Terminal) :
    (runInputs (I10 (Terminal := Terminal) blank endSym mark startSym) blank (l ++ [x])
      ([vprogX k], vTS vt)).1 = [] :=
  exec_halts (vprogX_exec (Terminal := Terminal) (startSym := startSym) hk hne hstart hsu hse
    hE hq) l (by rw [vavecs_length]; exact hl) x

/-- **符号化の保存**（`GSVerifierFused.vencodes_stepX` の言い換え）。 -/
theorem vprogX_encodes (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank)
    (hstart : startSym ∉ v) (hend : endSym ∉ v) (hendu : endSym ∉ u)
    (hsu : startSym ∉ u) (hse : startSym ≠ endSym)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length) (hc : z.2 ≤ u.length) (hpos : u.length ≤ z.1.pos)
    (hfit : (scanStep v k p₁ r Text z.1).pos + (scanStep v k p₁ r Text z.1).q < Text.length)
    (l : List (Option Terminal))
    (hl : l.length = (vprogramX blank endSym mark k vt).length) :
    ∃ vt' : VTapes' sc,
      (runInputs (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
          ([vprogX k], vTS vt)).2 = vTS vt' ∧
        VEncodes' blank startSym endSym mark u v Text k p₁ r vt'
          (vStep u v k p₁ r Text z) :=
  ⟨vApplyActs' blank (vprogramX blank endSym mark k vt) vt,
    vprogX_tapes (Terminal := Terminal) (startSym := startSym) hk hne hstart hsu hse hE hq l hl,
    PalPeg.GSVTapes.vencodes_stepX hk hp hne hend hendu hE hq hc hpos hfit⟩

end RoundXSpec

/-! ## 7. 公理の確認 -/

#print axioms perDownLoopX_exec
#print axioms perProgX_exec
#print axioms res_keyX
#print axioms resProgX_exec
#print axioms uxWalkProg_exec
#print axioms shiftProg_exec
#print axioms vprogX_exec
#print axioms vprogX_trace
#print axioms vprogX_trace_length
#print axioms vprogX_tapes
#print axioms vprogX_halts
#print axioms vprogX_encodes

end PalPeg.GSVProg
