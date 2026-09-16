import PalPeg.GSScanProg
import PalPeg.GSVerifierTapes

/-!
# 検証器つきラウンド（オラクル無し）の有限制御プログラム化 (`GSVerifierProg`)

`PalPeg.GSVerifierTapes` §9 の `vprogram'`（走査段 8 本＋検証器 2 本＝10 本のテープに
対する動作列）を、`PalPeg.ProgLang` の構造化プログラム `Prog Act10 Cond10` として
書き直す。`PalPeg.GSScanProg` で済んでいる走査段 8 本のプログラム化
（`scanProg` / `scanProg_exec`）は**そのまま再利用**し、テープ本数を 8 から 10 へ
広げる一般の移送補題（§3）で持ち上げる。
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace PalPeg.GSVProg

open PegSeparation.RealTimeTM
open PalPeg.Program
open PalPeg.ProgLang
open PalPeg.GSProg

variable {sc : ℕ}

/-! ## 1. 10 本テープの添字と動作・条件 -/

/-- 走査段の 8 本を先頭に埋め込む。 -/
def e8 (j : Fin 8) : Fin 10 := ⟨j.val, by omega⟩

/-- 接頭辞テープ `U`。 -/
def tU : Fin 10 := ⟨8, by omega⟩

/-- テキストの 2 本目のコピー `Txt2`。 -/
def tX : Fin 10 := ⟨9, by omega⟩

theorem e8_ne_tU (j : Fin 8) : e8 j ≠ tU := by
  intro h
  have := congrArg Fin.val h
  simp only [e8, tU] at this
  omega

theorem e8_ne_tX (j : Fin 8) : e8 j ≠ tX := by
  intro h
  have := congrArg Fin.val h
  simp only [e8, tX] at this
  omega

/-- 動作識別子：`(テープ番号, 読んだ記号を書き戻すか, 移動)`。 -/
abbrev Act10 := Fin 10 × Bool × Move

/-- 条件識別子。 -/
inductive Cond10 where
  /-- テープ `j` の読みが `mark` でない。 -/
  | notMark (j : Fin 10) : Cond10
  /-- パターンテープの読みが `startSym` でない。 -/
  | notStart : Cond10
  /-- 走査の一致枝の条件。 -/
  | matchOk : Cond10
  /-- 検証器の比較枝の条件（`U` の読みが `endSym` でなく `Txt2` の読みと等しい）。 -/
  | compOk : Cond10
  /-- 接頭辞テープ `U` の読みが `startSym` でない。 -/
  | notStartU : Cond10
  deriving DecidableEq

instance : Fintype Cond10 :=
  Fintype.ofList ((List.finRange 10).map Cond10.notMark ++
      [Cond10.notStart, Cond10.matchOk, Cond10.compOk, Cond10.notStartU])
    (by rintro (j | _ | _ | _ | _) <;> simp)

variable {Terminal : Type}

/-- 動作の解釈。入力記号は見ない。 -/
def actOf10 (blank : Fin sc) (a : Act10) (_ : Option Terminal) (σ : Fin 10 → Fin sc) :
    Fin 10 → Fin sc × Move :=
  touchVec a.1 (if a.2.1 then σ a.1 else blank) a.2.2 σ

/-- 条件の解釈。 -/
def condOf10 (endSym mark startSym : Fin sc) : Cond10 → (Fin 10 → Fin sc) → Bool
  | .notMark j, σ => decide (σ j ≠ mark)
  | .notStart, σ => decide (σ (e8 GSTapes.tP) ≠ startSym)
  | .matchOk, σ => decide (σ (e8 GSTapes.tP) ≠ endSym ∧ σ (e8 GSTapes.tP) = σ (e8 GSTapes.tT))
  | .compOk, σ => decide (σ tU ≠ endSym ∧ σ tU = σ tX)
  | .notStartU, σ => decide (σ tU ≠ startSym)

/-- 10 本テープの解釈。 -/
def I10 (blank endSym mark startSym : Fin sc) : Interp Terminal Act10 Cond10 (Fin sc) 10 where
  actOf := actOf10 blank
  condOf := condOf10 endSym mark startSym

theorem inputFree_I10 (blank endSym mark startSym : Fin sc) :
    InputFree (I10 (Terminal := Terminal) blank endSym mark startSym) := fun _ _ _ => rfl

/-! ## 2. テープ束の合成 -/

/-- 8 本＋`U`＋`Txt2` を 10 本に束ねる。 -/
def comb (T : Fin 8 → STape (Fin sc)) (U X : STape (Fin sc)) : Fin 10 → STape (Fin sc) :=
  fun j => if h : j.val < 8 then T ⟨j.val, h⟩ else if j.val = 8 then U else X

@[simp] theorem comb_e8 (T : Fin 8 → STape (Fin sc)) (U X : STape (Fin sc)) (j : Fin 8) :
    comb T U X (e8 j) = T j := by
  simp only [comb, e8]
  rw [dif_pos j.isLt]

@[simp] theorem comb_tU (T : Fin 8 → STape (Fin sc)) (U X : STape (Fin sc)) :
    comb T U X tU = U := rfl

@[simp] theorem comb_tX (T : Fin 8 → STape (Fin sc)) (U X : STape (Fin sc)) :
    comb T U X tX = X := rfl

/-- 8 本分の write+move ベクトルを 10 本へ（残りの 2 本は読み戻して停留）。 -/
def liftVec (U X : STape (Fin sc)) (w : Fin 8 → Fin sc × Move) : Fin 10 → Fin sc × Move :=
  fun j => if h : j.val < 8 then w ⟨j.val, h⟩ else if j.val = 8 then (U.focus, Move.stay)
    else (X.focus, Move.stay)

@[simp] theorem liftVec_e8 (U X : STape (Fin sc)) (w : Fin 8 → Fin sc × Move) (j : Fin 8) :
    liftVec U X w (e8 j) = w j := by
  simp only [liftVec, e8]
  rw [dif_pos j.isLt]

@[simp] theorem liftVec_tU (U X : STape (Fin sc)) (w : Fin 8 → Fin sc × Move) :
    liftVec U X w tU = (U.focus, Move.stay) := rfl

@[simp] theorem liftVec_tX (U X : STape (Fin sc)) (w : Fin 8 → Fin sc × Move) :
    liftVec U X w tX = (X.focus, Move.stay) := rfl

/-- 合成テープに持ち上げたベクトルを適用しても、`U` / `Txt2` は変わらない。 -/
theorem applyAction_liftVec (blank : Fin sc) (T : Fin 8 → STape (Fin sc))
    (U X : STape (Fin sc)) (w : Fin 8 → Fin sc × Move) :
    (fun j => (comb T U X j).applyAction blank (liftVec U X w j))
      = comb (fun j => (T j).applyAction blank (w j)) U X := by
  funext j
  by_cases h : j.val < 8
  · have hj : j = e8 ⟨j.val, h⟩ := by apply Fin.ext; rfl
    rw [hj, comb_e8, liftVec_e8, comb_e8]
  · by_cases h8 : j.val = 8
    · have hj : j = tU := Fin.ext h8
      rw [hj, comb_tU, liftVec_tU, comb_tU]
      rfl
    · have hj : j = tX := by
        apply Fin.ext
        have := j.isLt
        simp only [tX]
        omega
      rw [hj, comb_tX, liftVec_tX, comb_tX]
      rfl

theorem applyTrace_liftVec (blank : Fin sc) (U X : STape (Fin sc)) :
    ∀ (l : List (Fin 8 → Fin sc × Move)) (T : Fin 8 → STape (Fin sc)),
      applyTrace blank (comb T U X) (l.map (liftVec U X))
        = comb (applyTrace blank T l) U X := by
  intro l
  induction l with
  | nil => intro T; rfl
  | cons w l ih =>
      intro T
      rw [List.map_cons, applyTrace_cons, applyTrace_cons, applyAction_liftVec, ih]

/-! ## 3. 8 本テープのプログラムを 10 本へ持ち上げる -/

/-- 動作識別子の持ち上げ。 -/
def fa (a : Act8) : Act10 := (e8 a.1, a.2)

/-- 条件識別子の持ち上げ。 -/
def fc : Cond8 → Cond10
  | .notMark j => .notMark (e8 j)
  | .notStart => .notStart
  | .matchOk => .matchOk

/-- プログラムの持ち上げ（構文木をそのまま写す）。 -/
def pmap : Prog Act8 Cond8 → Prog Act10 Cond10
  | .skip => .skip
  | .act a => .act (fa a)
  | .seq p q => .seq (pmap p) (pmap q)
  | .ite c p q => .ite (fc c) (pmap p) (pmap q)
  | .loop c a b => .loop (fc c) (fa a) (pmap b)

/-- **制御スタックの模倣**。持ち上げたスタックの 1 マイクロステップは、
もとのスタックの 1 マイクロステップを写したもの（もとが尽きたら継続へ落ちる）。 -/
theorem step_sim (ev8 : Cond8 → Bool) (ev10 : Cond10 → Bool)
    (h : ∀ c, ev10 (fc c) = ev8 c) :
    ∀ (s : Stack Act8 Cond8) (r : Stack Act10 Cond10),
      (∀ a, (stepStack ev8 s).2 = some a →
          stepStack ev10 (s.map pmap ++ r)
            = ((stepStack ev8 s).1.map pmap ++ r, some (fa a))) ∧
        ((stepStack ev8 s).2 = none →
          stepStack ev10 (s.map pmap ++ r) = stepStack ev10 r) := by
  intro s
  induction s using stepStack.induct (ev := ev8) with
  | case1 => intro r; exact ⟨by intro a ha; simp at ha, by intro _; simp⟩
  | case2 r' ih =>
      intro r
      have e : (Prog.skip :: r').map pmap ++ r = Prog.skip :: (r'.map pmap ++ r) := rfl
      rw [e, stepStack_skip, stepStack_skip]
      exact ih r
  | case3 a r' =>
      intro r
      have e : (Prog.act a :: r').map pmap ++ r = Prog.act (fa a) :: (r'.map pmap ++ r) := rfl
      rw [e, stepStack_act, stepStack_act]
      exact ⟨by intro b hb; cases hb; rfl, by intro hb; simp at hb⟩
  | case4 p q r' ih =>
      intro r
      have e : (Prog.seq p q :: r').map pmap ++ r
          = Prog.seq (pmap p) (pmap q) :: (r'.map pmap ++ r) := rfl
      rw [e, stepStack_seq, stepStack_seq]
      have e2 : pmap p :: pmap q :: (r'.map pmap ++ r) = (p :: q :: r').map pmap ++ r := rfl
      rw [e2]
      exact ih r
  | case5 c p q r' ih =>
      intro r
      have e : (Prog.ite c p q :: r').map pmap ++ r
          = Prog.ite (fc c) (pmap p) (pmap q) :: (r'.map pmap ++ r) := rfl
      rw [e, stepStack_ite, stepStack_ite, h c]
      have e2 : (if ev8 c then pmap p else pmap q) :: (r'.map pmap ++ r)
          = ((if ev8 c then p else q) :: r').map pmap ++ r := by
        by_cases hc : ev8 c <;> simp [hc]
      rw [e2]
      exact ih r
  | case6 c a b r' hc =>
      intro r
      have e : (Prog.loop c a b :: r').map pmap ++ r
          = Prog.loop (fc c) (fa a) (pmap b) :: (r'.map pmap ++ r) := rfl
      rw [e, stepStack_loop, stepStack_loop, h c]
      simp only [if_pos hc]
      refine ⟨?_, ?_⟩
      · intro x hx
        have e2 : pmap b :: Prog.loop (fc c) (fa a) (pmap b) :: (r'.map pmap ++ r)
            = (b :: Prog.loop c a b :: r').map pmap ++ r := rfl
        rw [e2]
        cases hx
        rfl
      · intro hx; exact absurd hx (by simp)
  | case7 c a b r' hc ih =>
      intro r
      have e : (Prog.loop c a b :: r').map pmap ++ r
          = Prog.loop (fc c) (fa a) (pmap b) :: (r'.map pmap ++ r) := rfl
      rw [e, stepStack_loop, stepStack_loop, h c]
      simp only [if_neg hc]
      exact ih r

/-! ### 解釈の整合 -/

section Sim

variable {blank endSym mark startSym : Fin sc}

theorem cond_agree (c : Cond8) (T : Fin 8 → STape (Fin sc)) (U X : STape (Fin sc)) :
    evalConds (I10 (Terminal := Terminal) blank endSym mark startSym)
        (fun j => (comb T U X j).focus) (fc c)
      = evalConds (I8 (Terminal := Terminal) blank endSym mark startSym)
          (fun j => (T j).focus) c := by
  cases c with
  | notMark j => simp [evalConds, I8, I10, condOf8, condOf10, fc]
  | notStart => simp [evalConds, I8, I10, condOf8, condOf10, fc]
  | matchOk => simp [evalConds, I8, I10, condOf8, condOf10, fc]

theorem act_agree (a : Act8) (x : Option Terminal) (T : Fin 8 → STape (Fin sc))
    (U X : STape (Fin sc)) :
    (I10 (Terminal := Terminal) blank endSym mark startSym).actOf (fa a) x
        (fun j => (comb T U X j).focus)
      = liftVec U X ((I8 (Terminal := Terminal) blank endSym mark startSym).actOf a x
          (fun j => (T j).focus)) := by
  have hL : (I10 (Terminal := Terminal) blank endSym mark startSym).actOf (fa a) x
      (fun j => (comb T U X j).focus)
      = touchVec (e8 a.1) (if a.2.1 then (T a.1).focus else blank) a.2.2
          (fun j => (comb T U X j).focus) := by
    show actOf10 blank (fa a) x (fun j => (comb T U X j).focus) = _
    simp only [actOf10, fa, comb_e8]
  have hR : (I8 (Terminal := Terminal) blank endSym mark startSym).actOf a x
      (fun j => (T j).focus)
      = touchVec a.1 (if a.2.1 then (T a.1).focus else blank) a.2.2
          (fun j => (T j).focus) := rfl
  rw [hL, hR]
  funext j
  by_cases h : j.val < 8
  · have hj : j = e8 ⟨j.val, h⟩ := by apply Fin.ext; rfl
    rw [hj, liftVec_e8]
    by_cases hi : (⟨j.val, h⟩ : Fin 8) = a.1
    · rw [hi]
      simp [touchVec]
    · have hi2 : e8 ⟨j.val, h⟩ ≠ e8 a.1 := by
        intro hcon
        refine hi (Fin.ext ?_)
        have hv : (e8 ⟨j.val, h⟩).val = (e8 a.1).val := congrArg Fin.val hcon
        simpa [e8] using hv
      simp only [touchVec, if_neg hi2, if_neg hi, comb_e8]
  · have hne : ∀ i : Fin 8, j ≠ e8 i := by
      intro i hcon
      have h1 := congrArg Fin.val hcon
      have h2 := i.isLt
      simp only [e8] at h1
      omega
    by_cases h8 : j.val = 8
    · have hj : j = tU := Fin.ext h8
      rw [hj, liftVec_tU]
      simp only [touchVec, if_neg (fun hcon => hne a.1 (hj ▸ hcon)), comb_tU]
    · have hj : j = tX := by
        apply Fin.ext
        have := j.isLt
        simp only [tX]
        omega
      rw [hj, liftVec_tX]
      simp only [touchVec, if_neg (fun hcon => hne a.1 (hj ▸ hcon)), comb_tX]

/-- **実行の模倣**。もとの 8 本テープのプログラムが `l` の間ずっと動作を出し続ける限り、
持ち上げたプログラムはその動作を（`U` / `Txt2` を触らずに）忠実に再現する。 -/
theorem run_sim :
    ∀ (l : List (Option Terminal)) (s : Stack Act8 Cond8) (T : Fin 8 → STape (Fin sc))
      (U X : STape (Fin sc)) (r : Stack Act10 Cond10),
      (trace (I8 (Terminal := Terminal) blank endSym mark startSym) blank l (s, T)).length
          = l.length →
      trace (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
            (s.map pmap ++ r, comb T U X)
          = (trace (I8 (Terminal := Terminal) blank endSym mark startSym) blank l
              (s, T)).map (liftVec U X) ∧
        runInputs (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
            (s.map pmap ++ r, comb T U X)
          = ((runInputs (I8 (Terminal := Terminal) blank endSym mark startSym) blank l
                (s, T)).1.map pmap ++ r,
              comb (runInputs (I8 (Terminal := Terminal) blank endSym mark startSym) blank l
                (s, T)).2 U X) := by
  intro l
  induction l with
  | nil => intro s T U X r _; exact ⟨rfl, rfl⟩
  | cons x l ih =>
    intro s T U X r hlen
    have hsome : ∃ w, (stepStack (evalConds
        (I8 (Terminal := Terminal) blank endSym mark startSym)
        (fun j => (T j).focus)) s).2 = some w := by
      cases hw : (stepStack (evalConds
          (I8 (Terminal := Terminal) blank endSym mark startSym)
          (fun j => (T j).focus)) s).2 with
      | some w => exact ⟨w, rfl⟩
      | none =>
        exfalso
        rw [trace_cons, hw] at hlen
        have hle := trace_length_le (I8 (Terminal := Terminal) blank endSym mark startSym)
          blank l (microStep (I8 (Terminal := Terminal) blank endSym mark startSym) blank x
            (s, T))
        simp only [List.nil_append, List.length_cons] at hlen
        omega
    obtain ⟨w, hw⟩ := hsome
    have hstep10 := (step_sim (evalConds
        (I8 (Terminal := Terminal) blank endSym mark startSym) (fun j => (T j).focus))
      (evalConds (I10 (Terminal := Terminal) blank endSym mark startSym)
        (fun j => (comb T U X j).focus))
      (fun c => cond_agree (Terminal := Terminal) c T U X) s r).1 w hw
    have hact := act_agree (Terminal := Terminal) (blank := blank) (endSym := endSym)
      (mark := mark) (startSym := startSym) w x T U X
    have hmicro : microStep (I10 (Terminal := Terminal) blank endSym mark startSym) blank x
          (s.map pmap ++ r, comb T U X)
        = ((microStep (I8 (Terminal := Terminal) blank endSym mark startSym) blank x
              (s, T)).1.map pmap ++ r,
            comb (microStep (I8 (Terminal := Terminal) blank endSym mark startSym) blank x
              (s, T)).2 U X) := by
      simp only [microStep, hstep10, hw, hact]
      exact Prod.ext rfl (applyAction_liftVec blank T U X _)
    have hlen' : (trace (I8 (Terminal := Terminal) blank endSym mark startSym) blank l
        (microStep (I8 (Terminal := Terminal) blank endSym mark startSym) blank x
          (s, T))).length = l.length := by
      rw [trace_cons, hw] at hlen
      simp only [List.singleton_append, List.length_cons] at hlen
      omega
    obtain ⟨ih1, ih2⟩ := ih
      (microStep (I8 (Terminal := Terminal) blank endSym mark startSym) blank x (s, T)).1
      (microStep (I8 (Terminal := Terminal) blank endSym mark startSym) blank x (s, T)).2
      U X r (by simpa using hlen')
    simp only [Prod.mk.eta] at ih1 ih2
    constructor
    · rw [trace_cons, trace_cons, hstep10, hw, hmicro]
      simp only [hact, List.singleton_append, List.map_cons]
      exact congrArg _ ih1
    · rw [runInputs_cons, runInputs_cons, hmicro]
      exact ih2

end Sim

/-! ## 4. `Exec` の移送 -/

section Lift

variable {blank endSym mark startSym : Fin sc}

/-- **移送定理**：8 本テープのプログラムの `Exec` は、持ち上げたプログラムの
`Exec` になる（`U` / `Txt2` は停留したまま）。 -/
theorem exec_lift {P : Prog Act8 Cond8} {T : Fin 8 → STape (Fin sc)}
    {U X : STape (Fin sc)} {acts : List (Fin 8 → Fin sc × Move)}
    (h : Exec (I8 (Terminal := Terminal) blank endSym mark startSym) blank P T acts) :
    Exec (I10 (Terminal := Terminal) blank endSym mark startSym) blank (pmap P)
      (comb T U X) (acts.map (liftVec U X)) := by
  intro r l hl
  rw [List.length_map] at hl
  obtain ⟨htr, s', hrun, hseq⟩ := h [] l hl
  rw [show ([P] ++ ([] : Stack Act8 Cond8)) = [P] from rfl] at htr hrun
  have hprod : (trace (I8 (Terminal := Terminal) blank endSym mark startSym) blank l
      ([P], T)).length = l.length := by rw [htr, hl]
  obtain ⟨hs1, hs2⟩ := run_sim (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) l [P] T U X r hprod
  have hmapP : ([P] : Stack Act8 Cond8).map pmap ++ r = [pmap P] ++ r := rfl
  rw [hmapP] at hs1 hs2
  rw [hrun] at hs2
  refine ⟨by rw [hs1, htr], ?_⟩
  refine ⟨s'.map pmap ++ r, ?_, ?_⟩
  · rw [hs2, applyTrace_liftVec]
  · show stepStack (evalConds (I10 (Terminal := Terminal) blank endSym mark startSym)
      (fun j => ((applyTrace blank (comb T U X) (acts.map (liftVec U X))) j).focus))
        (s'.map pmap ++ r)
      = stepStack _ r
    rw [applyTrace_liftVec]
    refine (step_sim (evalConds (I8 (Terminal := Terminal) blank endSym mark startSym)
        (fun j => ((applyTrace blank T acts) j).focus))
      (evalConds (I10 (Terminal := Terminal) blank endSym mark startSym)
        (fun j => (comb (applyTrace blank T acts) U X j).focus))
      (fun c => cond_agree (Terminal := Terminal) c _ U X) s' r).2 ?_
    rw [hseq]
    simp

end Lift

/-! ## 5. 検証器つき 10 本テープの動作ベクトル -/

/-- 10 本のテープ束（`GSVerifierTapes` の `VTapes'`）を `Prog` 側の zipper へ。 -/
def vTS (vt : GSVTapes.VTapes' sc) : Fin 10 → STape (Fin sc) :=
  comb (TS vt.1) (toS vt.2.U) (toS vt.2.Txt2)

@[simp] theorem vTS_tU (vt : GSVTapes.VTapes' sc) : vTS vt tU = toS vt.2.U := rfl

@[simp] theorem vTS_tX (vt : GSVTapes.VTapes' sc) : vTS vt tX = toS vt.2.Txt2 := rfl

@[simp] theorem vTS_e8 (vt : GSVTapes.VTapes' sc) (j : Fin 8) :
    vTS vt (e8 j) = toS (vt.1 j) := comb_e8 _ _ _ j

/-- `VAct'` に対応する 10 テープ分の write+move ベクトル。 -/
def vavec (vt : GSVTapes.VTapes' sc) : GSVTapes.VAct' sc → (Fin 10 → Fin sc × Move)
  | .S a => liftVec (toS vt.2.U) (toS vt.2.Txt2) (avec vt.1 a)
  | .U m => touchVec tU vt.2.U.focus m (fun j => (vTS vt j).focus)
  | .X m => touchVec tX vt.2.Txt2.focus m (fun j => (vTS vt j).focus)

/-- 動作列に対応するベクトル列。 -/
def vavecs (blank : Fin sc) :
    List (GSVTapes.VAct' sc) → GSVTapes.VTapes' sc → List (Fin 10 → Fin sc × Move)
  | [], _ => []
  | a :: l, vt => vavec vt a :: vavecs blank l (GSVTapes.vApplyAct' blank vt a)

@[simp] theorem vavecs_nil (blank : Fin sc) (vt : GSVTapes.VTapes' sc) :
    vavecs blank [] vt = [] := rfl

@[simp] theorem vavecs_cons (blank : Fin sc) (a : GSVTapes.VAct' sc)
    (l : List (GSVTapes.VAct' sc)) (vt : GSVTapes.VTapes' sc) :
    vavecs blank (a :: l) vt = vavec vt a :: vavecs blank l (GSVTapes.vApplyAct' blank vt a) :=
  rfl

@[simp] theorem vavecs_length (blank : Fin sc) :
    ∀ (l : List (GSVTapes.VAct' sc)) (vt : GSVTapes.VTapes' sc),
      (vavecs blank l vt).length = l.length := by
  intro l
  induction l with
  | nil => intro vt; rfl
  | cons a l ih => intro vt; simp [ih]

theorem vavecs_append (blank : Fin sc) :
    ∀ (l₁ l₂ : List (GSVTapes.VAct' sc)) (vt : GSVTapes.VTapes' sc),
      vavecs blank (l₁ ++ l₂) vt
        = vavecs blank l₁ vt ++ vavecs blank l₂ (GSVTapes.vApplyActs' blank l₁ vt) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ vt; rfl
  | cons a l ih => intro l₂ vt; simp [ih, GSVTapes.vApplyActs']

/-- 1 動作分：ベクトルの適用は `vApplyAct'` に一致する。 -/
theorem applyTrace_vavec (blank : Fin sc) (vt : GSVTapes.VTapes' sc)
    (a : GSVTapes.VAct' sc) :
    (fun j => (vTS vt j).applyAction blank (vavec vt a j))
      = vTS (GSVTapes.vApplyAct' blank vt a) := by
  cases a with
  | S a8 =>
      show (fun j => (comb (TS vt.1) (toS vt.2.U) (toS vt.2.Txt2) j).applyAction blank
        (liftVec (toS vt.2.U) (toS vt.2.Txt2) (avec vt.1 a8) j)) = _
      rw [applyAction_liftVec, applyTrace_avec]
      rfl
  | U m =>
      funext j
      by_cases h : j.val < 8
      · have hj : j = e8 ⟨j.val, h⟩ := by apply Fin.ext; rfl
        have hne : j ≠ tU := by
          intro hcon
          have := congrArg Fin.val hcon
          simp only [tU] at this
          omega
        rw [hj]
        show (vTS vt (e8 ⟨j.val, h⟩)).applyAction blank
            (touchVec tU vt.2.U.focus m (fun i => (vTS vt i).focus) (e8 ⟨j.val, h⟩)) = _
        rw [touchVec, if_neg (by rw [← hj]; exact hne)]
        simp only [GSVTapes.vApplyAct', vTS_e8]
        exact ProgLang.applyAction_focus_stay (blank := blank) (toS (vt.1 ⟨j.val, h⟩))
      · by_cases h8 : j.val = 8
        · have hj : j = tU := Fin.ext h8
          rw [hj]
          show (toS vt.2.U).applyAction blank
              (touchVec tU vt.2.U.focus m (fun i => (vTS vt i).focus) tU) = _
          rw [touchVec, if_pos rfl]
          exact (toS_step blank vt.2.U vt.2.U.focus m).symm
        · have hj : j = tX := by
            apply Fin.ext
            have := j.isLt
            simp only [tX]
            omega
          have hne : tX ≠ (tU : Fin 10) := by decide
          rw [hj]
          show (vTS vt tX).applyAction blank
              (touchVec tU vt.2.U.focus m (fun i => (vTS vt i).focus) tX) = _
          rw [touchVec, if_neg hne]
          exact ProgLang.applyAction_focus_stay (blank := blank) (vTS vt tX)
  | X m =>
      funext j
      by_cases h : j.val < 8
      · have hj : j = e8 ⟨j.val, h⟩ := by apply Fin.ext; rfl
        have hne : j ≠ tX := by
          intro hcon
          have := congrArg Fin.val hcon
          simp only [tX] at this
          omega
        rw [hj]
        show (vTS vt (e8 ⟨j.val, h⟩)).applyAction blank
            (touchVec tX vt.2.Txt2.focus m (fun i => (vTS vt i).focus) (e8 ⟨j.val, h⟩)) = _
        rw [touchVec, if_neg (by rw [← hj]; exact hne)]
        simp only [GSVTapes.vApplyAct', vTS_e8]
        exact ProgLang.applyAction_focus_stay (blank := blank) (toS (vt.1 ⟨j.val, h⟩))
      · by_cases h8 : j.val = 8
        · have hj : j = tU := Fin.ext h8
          have hne : tU ≠ (tX : Fin 10) := by decide
          rw [hj]
          show (vTS vt tU).applyAction blank
              (touchVec tX vt.2.Txt2.focus m (fun i => (vTS vt i).focus) tU) = _
          rw [touchVec, if_neg hne]
          exact ProgLang.applyAction_focus_stay (blank := blank) (vTS vt tU)
        · have hj : j = tX := by
            apply Fin.ext
            have := j.isLt
            simp only [tX]
            omega
          rw [hj]
          show (toS vt.2.Txt2).applyAction blank
              (touchVec tX vt.2.Txt2.focus m (fun i => (vTS vt i).focus) tX) = _
          rw [touchVec, if_pos rfl]
          exact (toS_step blank vt.2.Txt2 vt.2.Txt2.focus m).symm

theorem applyTrace_vavecs (blank : Fin sc) :
    ∀ (l : List (GSVTapes.VAct' sc)) (vt : GSVTapes.VTapes' sc),
      applyTrace blank (vTS vt) (vavecs blank l vt) = vTS (GSVTapes.vApplyActs' blank l vt) := by
  intro l
  induction l with
  | nil => intro vt; rfl
  | cons a l ih =>
      intro vt
      rw [vavecs_cons, applyTrace_cons]
      show applyTrace blank (fun j => ((vTS vt) j).applyAction blank (vavec vt a j)) _ = _
      rw [applyTrace_vavec, ih]
      rfl

/-- 走査段の動作列を `S` で持ち上げたベクトル列は、8 本のベクトル列の持ち上げ。 -/
theorem vavecs_map_S (blank : Fin sc) :
    ∀ (l : List (GSTapes.Act' sc)) (vt : GSVTapes.VTapes' sc),
      vavecs blank (l.map GSVTapes.VAct'.S) vt
        = (avecs blank l vt.1).map (liftVec (toS vt.2.U) (toS vt.2.Txt2)) := by
  intro l
  induction l with
  | nil => intro vt; rfl
  | cons a l ih =>
      intro vt
      rw [List.map_cons, vavecs_cons, avecs_cons, List.map_cons]
      have hstate : GSVTapes.vApplyAct' blank vt (GSVTapes.VAct'.S a)
          = (GSTapes.applyAct' blank vt.1 a, vt.2) := rfl
      rw [ih, hstate]
      rfl

/-! ## 6. 10 本テープの `Exec` -/

section ExecV

variable (Terminal : Type)

/-- 「プログラム `P` は 10 本テープの状態 `vt` からちょうど動作列 `L` を実行して
継続に戻る」。 -/
def ExecV (blank endSym mark startSym : Fin sc) (P : Prog Act10 Cond10)
    (vt : GSVTapes.VTapes' sc) (L : List (GSVTapes.VAct' sc)) : Prop :=
  Exec (I10 (Terminal := Terminal) blank endSym mark startSym) blank P (vTS vt)
    (vavecs blank L vt)

variable {Terminal}
variable {blank endSym mark startSym : Fin sc}

theorem execV_of_eq {P : Prog Act10 Cond10} {vt : GSVTapes.VTapes' sc}
    {L L' : List (GSVTapes.VAct' sc)} (h : L = L')
    (hE : ExecV Terminal blank endSym mark startSym P vt L) :
    ExecV Terminal blank endSym mark startSym P vt L' := h ▸ hE

theorem execV_skip {vt : GSVTapes.VTapes' sc} :
    ExecV Terminal blank endSym mark startSym Prog.skip vt [] := exec_skip _

theorem execV_seq {P Q : Prog Act10 Cond10} {vt : GSVTapes.VTapes' sc}
    {L₁ L₂ : List (GSVTapes.VAct' sc)}
    (h1 : ExecV Terminal blank endSym mark startSym P vt L₁)
    (h2 : ExecV Terminal blank endSym mark startSym Q
      (GSVTapes.vApplyActs' blank L₁ vt) L₂) :
    ExecV Terminal blank endSym mark startSym (Prog.seq P Q) vt (L₁ ++ L₂) := by
  unfold ExecV at h1 h2 ⊢
  rw [vavecs_append]
  refine exec_seq h1 ?_
  rw [applyTrace_vavecs]
  exact h2

theorem condV_eq (c : Cond10) (vt : GSVTapes.VTapes' sc) :
    (I10 (Terminal := Terminal) blank endSym mark startSym).condOf c
        (fun j => ((vTS vt) j).focus)
      = condOf10 endSym mark startSym c (fun j => ((vTS vt) j).focus) := rfl

theorem execV_ite_pos {c : Cond10} {P Q : Prog Act10 Cond10} {vt : GSVTapes.VTapes' sc}
    {L : List (GSVTapes.VAct' sc)}
    (hc : condOf10 endSym mark startSym c (fun j => ((vTS vt) j).focus) = true)
    (h : ExecV Terminal blank endSym mark startSym P vt L) :
    ExecV Terminal blank endSym mark startSym (Prog.ite c P Q) vt L :=
  exec_ite_pos (by rw [condV_eq]; exact hc) h

theorem execV_ite_neg {c : Cond10} {P Q : Prog Act10 Cond10} {vt : GSVTapes.VTapes' sc}
    {L : List (GSVTapes.VAct' sc)}
    (hc : condOf10 endSym mark startSym c (fun j => ((vTS vt) j).focus) = false)
    (h : ExecV Terminal blank endSym mark startSym Q vt L) :
    ExecV Terminal blank endSym mark startSym (Prog.ite c P Q) vt L :=
  exec_ite_neg (by rw [condV_eq]; exact hc) h

/-- 読んだ記号を書き戻して移動する動作。 -/
def KEEP10 (i : Fin 10) (m : Move) : Prog Act10 Cond10 := Prog.act (i, true, m)

theorem execV_keepU (m : Move) (vt : GSVTapes.VTapes' sc) :
    ExecV Terminal blank endSym mark startSym (KEEP10 tU m) vt [GSVTapes.VAct'.U m] := by
  have h := exec_act (blank := blank) (inputFree_I10 (Terminal := Terminal)
    blank endSym mark startSym) (tU, true, m) (vTS vt)
  have he : actVec (I10 (Terminal := Terminal) blank endSym mark startSym) (tU, true, m)
      (vTS vt) = vavec vt (GSVTapes.VAct'.U m) := rfl
  rw [he] at h
  exact h

theorem execV_keepX (m : Move) (vt : GSVTapes.VTapes' sc) :
    ExecV Terminal blank endSym mark startSym (KEEP10 tX m) vt [GSVTapes.VAct'.X m] := by
  have h := exec_act (blank := blank) (inputFree_I10 (Terminal := Terminal)
    blank endSym mark startSym) (tX, true, m) (vTS vt)
  have he : actVec (I10 (Terminal := Terminal) blank endSym mark startSym) (tX, true, m)
      (vTS vt) = vavec vt (GSVTapes.VAct'.X m) := rfl
  rw [he] at h
  exact h

/-- 走査段のプログラムの持ち上げは、`S` で持ち上げた動作列を実行する。 -/
theorem execV_lift {P : Prog Act8 Cond8} {vt : GSVTapes.VTapes' sc}
    {L : List (GSTapes.Act' sc)}
    (h : ExecA Terminal blank endSym mark startSym P vt.1 L) :
    ExecV Terminal blank endSym mark startSym (pmap P) vt (L.map GSVTapes.VAct'.S) := by
  unfold ExecV
  rw [vavecs_map_S]
  exact exec_lift (U := toS vt.2.U) (X := toS vt.2.Txt2) h

end ExecV

/-! ## 7. 検証器の比較枝のプログラム -/

/-- 1 回の `vComp`：`U` と `Txt2` の読みが一致すれば両ヘッドを右へ 1。 -/
def vcompProg : Prog Act10 Cond10 :=
  Prog.ite Cond10.compOk (Prog.seq (KEEP10 tU .right) (KEEP10 tX .right)) Prog.skip

/-- `quota = 2`。 -/
def vcomp2Prog : Prog Act10 Cond10 := Prog.seq vcompProg vcompProg

section CompSpec

variable {Terminal : Type} {blank endSym mark startSym : Fin sc}

theorem compOk_eq (vt : GSVTapes.VTapes' sc) :
    condOf10 endSym mark startSym Cond10.compOk (fun j => ((vTS vt) j).focus)
      = decide (Tape.read vt.2.U ≠ endSym ∧ Tape.read vt.2.U = Tape.read vt.2.Txt2) := rfl

theorem vcompProg_exec (vt : GSVTapes.VTapes' sc) :
    ExecV Terminal blank endSym mark startSym vcompProg vt
      ((GSVTapes.vcompActs endSym vt.2).map GSVTapes.liftAct) := by
  by_cases hc : Tape.read vt.2.U ≠ endSym ∧ Tape.read vt.2.U = Tape.read vt.2.Txt2
  · have hlist : (GSVTapes.vcompActs endSym vt.2).map GSVTapes.liftAct
        = [GSVTapes.VAct'.U .right] ++ [GSVTapes.VAct'.X (sc := sc) .right] := by
      unfold GSVTapes.vcompActs
      rw [if_pos hc]
      rfl
    refine execV_ite_pos (by rw [compOk_eq]; exact decide_eq_true hc) ?_
    rw [hlist]
    exact execV_seq (execV_keepU Move.right vt)
      (execV_keepX Move.right (GSVTapes.vApplyActs' blank [GSVTapes.VAct'.U .right] vt))
  · have hlist : (GSVTapes.vcompActs endSym vt.2).map GSVTapes.liftAct
        = ([] : List (GSVTapes.VAct' sc)) := by
      unfold GSVTapes.vcompActs
      rw [if_neg hc]
      rfl
    refine execV_ite_neg (by rw [compOk_eq]; exact decide_eq_false hc) ?_
    rw [hlist]
    exact execV_skip

theorem vcomp2Prog_exec (vt : GSVTapes.VTapes' sc) :
    ExecV Terminal blank endSym mark startSym vcomp2Prog vt
      ((GSVTapes.vcomp2Acts blank endSym vt.2).map GSVTapes.liftAct) := by
  have h1 := vcompProg_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) vt
  have hsnd : (GSVTapes.vApplyActs' blank
      ((GSVTapes.vcompActs endSym vt.2).map GSVTapes.liftAct) vt).2
      = GSVTapes.extActs blank (GSVTapes.vcompActs endSym vt.2) vt.2 := by
    rw [GSVTapes.vApplyActs'_snd, GSVTapes.extActs'_map_liftAct]
  have h2 := vcompProg_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym)
    (GSVTapes.vApplyActs' blank ((GSVTapes.vcompActs endSym vt.2).map GSVTapes.liftAct) vt)
  rw [hsnd] at h2
  have := execV_seq h1 h2
  refine execV_of_eq ?_ this
  unfold GSVTapes.vcomp2Acts
  rw [List.map_append]

end CompSpec

/-! ## 8. 1 ラウンドの検証器つきプログラム

`vprogram'` は「走査段の動作列 ++ 検証器の動作列」であり、検証器側の分岐は
**この一歩の開始時の** `P` / `Txt` の読みで決まる。`Prog` の側では走査段を走らせると
`P` / `Txt` のヘッドが動いてしまうので、条件は**先に**見る（外側の `ite`）。
どちらの枝でも走査段のプログラムは同じ `pmap (scanProg k)` なので、
マイクロステップ数は `vprogram'` の長さと完全に一致する。

ずらし枝のプログラムは引数 `shift` として受け取る（§9 の注意を参照）。 -/
def vprogProg (k : ℕ) (shift : Prog Act10 Cond10) : Prog Act10 Cond10 :=
  Prog.ite Cond10.matchOk (Prog.seq (pmap (scanProg k)) vcomp2Prog)
    (Prog.seq (pmap (scanProg k)) shift)

section RoundSpec

variable {Terminal : Type} {blank endSym mark startSym : Fin sc}
variable {u v Text : List (Fin sc)} {k p₁ r : ℕ} {vt : GSVTapes.VTapes' sc} {z : VState}

theorem matchOk_eq (vt : GSVTapes.VTapes' sc) :
    condOf10 endSym mark startSym Cond10.matchOk (fun j => ((vTS vt) j).focus)
      = decide (Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
          Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT)) := rfl

/-- **主定理（1 ラウンドの一致、比較枝）**：`vprogProg k shift` は状態 `vt` から
ちょうど `vprogram' blank endSym mark k vt` の動作列を実行して継続に戻る。 -/
theorem vprog_exec (shift : Prog Act10 Cond10) (hk : 0 < k) (hne : mark ≠ blank)
    (hstart : startSym ∉ v)
    (hE : GSVTapes.VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length)
    (hadv : Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT)) :
    ExecV Terminal blank endSym mark startSym (vprogProg k shift) vt
      (GSVTapes.vprogram' blank endSym mark k vt) := by
  have hext : GSVTapes.vExtActs' blank endSym mark k vt
      = GSVTapes.vcomp2Acts blank endSym vt.2 := by
    unfold GSVTapes.vExtActs'
    rw [if_pos hadv]
  have hscan := execV_lift (Terminal := Terminal) (vt := vt)
    (scanProg_exec (Terminal := Terminal) (startSym := startSym) hk hne hstart hE.scan hq)
  have hsnd : (GSVTapes.vApplyActs' blank
      ((GSTapes.program' blank endSym mark k vt.1).map GSVTapes.VAct'.S) vt).2 = vt.2 := by
    rw [GSVTapes.vApplyActs'_map_S]
  have hcomp := vcomp2Prog_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym)
    (GSVTapes.vApplyActs' blank
      ((GSTapes.program' blank endSym mark k vt.1).map GSVTapes.VAct'.S) vt)
  rw [hsnd] at hcomp
  refine execV_ite_pos (by rw [matchOk_eq]; exact decide_eq_true hadv) ?_
  refine execV_of_eq ?_ (execV_seq hscan hcomp)
  unfold GSVTapes.vprogram'
  rw [hext]

/-! ### トレース・テープ・停止 -/

/-- **トレースの一致**。 -/
theorem vprog_trace (shift : Prog Act10 Cond10) (hk : 0 < k) (hne : mark ≠ blank)
    (hstart : startSym ∉ v)
    (hE : GSVTapes.VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length)
    (hadv : Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT))
    (l : List (Option Terminal))
    (hl : l.length = (GSVTapes.vprogram' blank endSym mark k vt).length) :
    trace (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
        ([vprogProg k shift], vTS vt)
      = vavecs blank (GSVTapes.vprogram' blank endSym mark k vt) vt := by
  have h := vprog_exec (Terminal := Terminal) (startSym := startSym) shift hk hne hstart hE
    hq hadv
  have h2 := (h [] l (by rw [vavecs_length]; exact hl)).1
  rw [show ([vprogProg k shift] ++ ([] : Stack Act10 Cond10)) = [vprogProg k shift] from rfl]
    at h2
  exact h2

/-- トレースの長さは動作列の長さに等しい（追加のマイクロステップは無い）。 -/
theorem vprog_trace_length (shift : Prog Act10 Cond10) (hk : 0 < k) (hne : mark ≠ blank)
    (hstart : startSym ∉ v)
    (hE : GSVTapes.VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length)
    (hadv : Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT))
    (l : List (Option Terminal))
    (hl : l.length = (GSVTapes.vprogram' blank endSym mark k vt).length) :
    (trace (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
        ([vprogProg k shift], vTS vt)).length
      = (GSVTapes.vprogram' blank endSym mark k vt).length := by
  rw [vprog_trace (Terminal := Terminal) (startSym := startSym) shift hk hne hstart hE hq
    hadv l hl, vavecs_length]

/-- **テープの一致**。 -/
theorem vprog_tapes (shift : Prog Act10 Cond10) (hk : 0 < k) (hne : mark ≠ blank)
    (hstart : startSym ∉ v)
    (hE : GSVTapes.VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length)
    (hadv : Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT))
    (l : List (Option Terminal))
    (hl : l.length = (GSVTapes.vprogram' blank endSym mark k vt).length) :
    (runInputs (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
        ([vprogProg k shift], vTS vt)).2
      = vTS (GSVTapes.vApplyActs' blank (GSVTapes.vprogram' blank endSym mark k vt) vt) := by
  rw [runInputs_snd_eq_applyTrace,
    vprog_trace (Terminal := Terminal) (startSym := startSym) shift hk hne hstart hE hq
      hadv l hl]
  exact applyTrace_vavecs blank _ vt

/-- **停止**。 -/
theorem vprog_halts (shift : Prog Act10 Cond10) (hk : 0 < k) (hne : mark ≠ blank)
    (hstart : startSym ∉ v)
    (hE : GSVTapes.VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length)
    (hadv : Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT))
    (l : List (Option Terminal))
    (hl : l.length = (GSVTapes.vprogram' blank endSym mark k vt).length)
    (x : Option Terminal) :
    (runInputs (I10 (Terminal := Terminal) blank endSym mark startSym) blank (l ++ [x])
      ([vprogProg k shift], vTS vt)).1 = [] :=
  exec_halts (vprog_exec (Terminal := Terminal) (startSym := startSym) shift hk hne hstart
    hE hq hadv) l (by rw [vavecs_length]; exact hl) x

/-- **符号化の保存**（`GSVerifierTapes.vencodes_step'` の言い換え）。 -/
theorem vprog_encodes (shift : Prog Act10 Cond10) (hk : 0 < k) (hne : mark ≠ blank)
    (hstart : startSym ∉ v) (hend : endSym ∉ v) (hendu : endSym ∉ u)
    (hE : GSVTapes.VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length) (hc : z.2 ≤ u.length) (hpos : u.length ≤ z.1.pos)
    (hfit : (scanStep v k p₁ r Text z.1).pos + (scanStep v k p₁ r Text z.1).q < Text.length)
    (hadv : Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT))
    (l : List (Option Terminal))
    (hl : l.length = (GSVTapes.vprogram' blank endSym mark k vt).length) :
    ∃ vt' : GSVTapes.VTapes' sc,
      (runInputs (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
          ([vprogProg k shift], vTS vt)).2 = vTS vt' ∧
        GSVTapes.VEncodes' blank startSym endSym mark u v Text k p₁ r vt'
          (vStep u v k p₁ r Text z) :=
  ⟨GSVTapes.vApplyActs' blank (GSVTapes.vprogram' blank endSym mark k vt) vt,
    vprog_tapes (Terminal := Terminal) (startSym := startSym) shift hk hne hstart hE hq hadv
      l hl,
    GSVTapes.vencodes_step' hk hne hend hendu hE hq hc hpos hfit⟩

end RoundSpec

/-! ## 9. ずらし枝について（`walkActs` は有限制御では実現できない）

`vprogram'` のずらし枝の動作列は

  `walkActs c d = replicate c (U .left) ++ (if c ≤ d then replicate (d - c) (X .right)
                                             else replicate (c - d) (X .left))`

であり（`c = checked`, `d = gsShift`）、これは **そのままの形では有限制御で実現できない**：

* `U` を「ちょうど `c` 歩」左へ動かすには、添字 `1` に着いたことを検出する必要があるが、
  `U` の内容は `startSym :: (u ++ [endSym])` であり、添字 `1` のセルの記号
  （`u[0]`, ないし `u = []` なら `endSym`）は他の添字のセルと読みで区別できない。
  検出できるのは左端の `startSym` だけなので、実現できるのは
  「`startSym` を読むまで左へ」＝ `c + 1` 歩＋復帰の `U .right` 1 歩＝ `c + 2` 歩である
  （下の `uRewindProg`）。
* `Txt2` の残りの移動 `|d - c|` に至っては、`Txt2` の内容は `Text` そのもので
  目印が無く、移動量を読みから決める手段が無い。`d = gsShift` は走査段のカウンタ
  テープが持っているので、実現するには**走査段のずらしループに `Txt2` の移動を
  相乗りさせる**（`perDown` / `resDown2` の各周回に `X` の 1 歩を足す）しかない。
  これは `vprogram'` の動作列そのものを組み替えることを意味する。

したがって本ファイルでは、ずらし枝のプログラムを `vprogProg` の引数 `shift` として
外から受け取り、**比較枝（`matchOk` が真のラウンド）について** `vprogram'` との
完全一致（`vprog_exec` / `vprog_trace`）を証明した。以下では、ずらし枝のうち
実現可能な部分（`U` の巻き戻し）を与え、余分な 2 歩を明示する。 -/

/-- `U` のヘッドを、左端の `startSym` を読むまで左へ動かす。 -/
def uRewindProg : Prog Act10 Cond10 :=
  Prog.loop Cond10.notStartU (tU, true, .left) Prog.skip

/-- 巻き戻し＋復帰（`walkActs` の `replicate c (U .left)` の実現可能な代替）。 -/
def uWalkProg : Prog Act10 Cond10 := Prog.seq uRewindProg (KEEP10 tU .right)

section Rewind

variable {Terminal : Type} {blank endSym mark startSym : Fin sc}

theorem notStartU_eq (vt : GSVTapes.VTapes' sc) :
    condOf10 endSym mark startSym Cond10.notStartU (fun j => ((vTS vt) j).focus)
      = decide (Tape.read vt.2.U ≠ startSym) := rfl

theorem execV_loop_contU {c : Cond10} {b : Prog Act10 Cond10} {vt : GSVTapes.VTapes' sc}
    {L₁ L₂ : List (GSVTapes.VAct' sc)}
    (hc : condOf10 endSym mark startSym c (fun j => ((vTS vt) j).focus) = true)
    (h1 : ExecV Terminal blank endSym mark startSym b
      (GSVTapes.vApplyAct' blank vt (GSVTapes.VAct'.U .left)) L₁)
    (h2 : ExecV Terminal blank endSym mark startSym (Prog.loop c (tU, true, .left) b)
      (GSVTapes.vApplyActs' blank L₁ (GSVTapes.vApplyAct' blank vt (GSVTapes.VAct'.U .left)))
      L₂) :
    ExecV Terminal blank endSym mark startSym (Prog.loop c (tU, true, .left) b) vt
      (GSVTapes.VAct'.U .left :: (L₁ ++ L₂)) := by
  unfold ExecV at h1 h2 ⊢
  rw [vavecs_cons, vavecs_append]
  have hT : (fun j => ((vTS vt) j).applyAction blank
      (actVec (I10 (Terminal := Terminal) blank endSym mark startSym) (tU, true, Move.left)
        (vTS vt) j)) = vTS (GSVTapes.vApplyAct' blank vt (GSVTapes.VAct'.U .left)) := by
    have he : actVec (I10 (Terminal := Terminal) blank endSym mark startSym)
        (tU, true, Move.left) (vTS vt) = vavec vt (GSVTapes.VAct'.U .left) := rfl
    rw [he]
    exact applyTrace_vavec blank vt (GSVTapes.VAct'.U .left)
  have he : actVec (I10 (Terminal := Terminal) blank endSym mark startSym)
      (tU, true, Move.left) (vTS vt) = vavec vt (GSVTapes.VAct'.U .left) := rfl
  rw [← he]
  refine exec_loop_cont (inputFree_I10 blank endSym mark startSym)
    (by rw [condV_eq]; exact hc) ?_ ?_
  · rw [hT]; exact h1
  · rw [hT, applyTrace_vavecs]; exact h2

theorem execV_loop_stopU {c : Cond10} {b : Prog Act10 Cond10} {vt : GSVTapes.VTapes' sc}
    (hc : condOf10 endSym mark startSym c (fun j => ((vTS vt) j).focus) = false) :
    ExecV Terminal blank endSym mark startSym (Prog.loop c (tU, true, .left) b) vt [] :=
  exec_loop_stop (by rw [condV_eq]; exact hc)

/-- **巻き戻しの実現**：ヘッド添字 `i` から `startSym` まで、ちょうど `i` 歩。 -/
theorem uRewindProg_exec {u : List (Fin sc)} (hsu : startSym ∉ u) (hse : startSym ≠ endSym) :
    ∀ (i : ℕ) (vt : GSVTapes.VTapes' sc),
      Tape.SeqView blank vt.2.U (startSym :: (u ++ [endSym])) i →
      ExecV Terminal blank endSym mark startSym uRewindProg vt
        (List.replicate i (GSVTapes.VAct'.U (sc := sc) .left)) := by
  intro i
  induction i with
  | zero =>
      intro vt hv
      have hr := hv.read_eq
      simp only [List.getElem?_cons_zero] at hr
      refine execV_loop_stopU ?_
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
          (GSVTapes.vApplyAct' blank vt (GSVTapes.VAct'.U .left)).2.U
          (startSym :: (u ++ [endSym])) i := by
        show Tape.SeqView blank (Tape.step blank vt.2.U vt.2.U.focus .left) _ i
        exact Tape.seq_move_left hv
      have h2 := ih (GSVTapes.vApplyAct' blank vt (GSVTapes.VAct'.U .left)) hv'
      have hstate : GSVTapes.vApplyActs' blank ([] : List (GSVTapes.VAct' sc))
          (GSVTapes.vApplyAct' blank vt (GSVTapes.VAct'.U .left))
          = GSVTapes.vApplyAct' blank vt (GSVTapes.VAct'.U .left) := rfl
      refine execV_of_eq ?_
        (execV_loop_contU (b := Prog.skip) (L₁ := []) (L₂ := List.replicate i _)
          (by rw [notStartU_eq]; exact decide_eq_true hne) execV_skip (by rw [hstate]; exact h2))
      rw [List.replicate_succ, List.nil_append]

/-- 巻き戻し＋復帰の動作数は `i + 1`（`walkActs` の `i` 歩に対して `+2`：
`startSym` を踏むための 1 歩と、添字 `1` へ戻る 1 歩）。 -/
theorem uWalkProg_exec {u : List (Fin sc)} (hsu : startSym ∉ u) (hse : startSym ≠ endSym)
    (c : ℕ) (vt : GSVTapes.VTapes' sc)
    (hv : Tape.SeqView blank vt.2.U (startSym :: (u ++ [endSym])) (c + 1)) :
    ExecV Terminal blank endSym mark startSym uWalkProg vt
      (List.replicate (c + 1) (GSVTapes.VAct'.U (sc := sc) .left)
        ++ [GSVTapes.VAct'.U (sc := sc) .right]) :=
  execV_seq (uRewindProg_exec hsu hse (c + 1) vt hv)
    (execV_keepU Move.right
      (GSVTapes.vApplyActs' blank
        (List.replicate (c + 1) (GSVTapes.VAct'.U (sc := sc) .left)) vt))

end Rewind

/-! ## 10. 公理の確認 -/

#print axioms exec_lift
#print axioms vprog_exec
#print axioms vprog_trace
#print axioms vprog_trace_length
#print axioms vprog_tapes
#print axioms vprog_halts
#print axioms vprog_encodes
#print axioms vcomp2Prog_exec
#print axioms uWalkProg_exec

end PalPeg.GSVProg
