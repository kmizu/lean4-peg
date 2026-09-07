import PalPeg.MiddleTapes
import PalPeg.BorderJobProg
import PalPeg.ProgLang
import PalPeg.ProgLangLib

/-!
# 中央フラグのジョブの有限制御プログラム化 (`MiddleProg`)

`PalPeg.MiddleTapes` の動作列（`homeActs` / `homeF` / `clearF` / `outStep` /
`ovRunActs` / `stageActs` / `jobActs` / `batchActs`）を `PalPeg.ProgLang` の
`Prog (Act15 sc) (Cond15 sc)` として実現する。方針は `PalPeg.BorderJobProg` と同じ。

## 実現の形

* **歩数駆動の歩行**（`mvX` / `mvX2` / `mvF` / `homeActs` / `homeF` / `clearF` /
  `outStep`）は `repProg`（`GSScanProg.resChain` / `TextFeedProg` と同じ ℕ 添字の
  プログラム族）で**逐語的**に実現する。歩数はいずれも段幅 `S` とバッチ番号から
  決まるので、段ごとに固定された有限制御になる。追加仮定・追加マイクロステップは
  どちらもゼロ。
  * `homeActs` の左掃きは `X` / `X2` の左端記号 `leftSym`、`clearF` は `F` の
    空白でも止められる（読める停止条件はある）が、そのループは左端に達したあとの
    「空回りの左移動」を出さないので、動作列は `homeActs` / `clearF` と**逐語には
    一致しない**（`mvX .left n` は左端に着いたあとも `n` 歩ぶんの動作を出す）。
    逐語性を優先して `repProg` を採用した。
* **段の走査** `ovRunActs` は反復回数がデータ依存なので本物の `Prog.loop` にする。
  ただし `Prog.loop c a body` は反復の先頭に 1 動作を強制し、`ovProgram` の先頭動作は
  枝によって変わる（フロンティア枝では `uFwd` が 0 動作のこともある）ので、
  **プローブ末尾形**として恒等動作 `nop = Act.P .stay` を反復の先頭に置く。
  したがって `ovRunActsN` は `ovRunActs` より**反復回数ぶん（≤ `fuel`）だけ長い**
  （`ovRunActsN_length_le`）。テープへの作用は変わらない（`ovRunActsN_apply`）。
* `stageProg` / `jobActsProg` / `batchProg` は上を継ぎ合わせる。`jobActsProg`・
  `batchProg` は `jobActs` / `batchActs` を**逐語的に**実行する。

## 未解決（テープ条件で駆動できない箇所）

`jobLoop` の継ぎ目 `homeActs sc L (L' - stageS D.dec y L') L'` は、右歩きの目標添字
`L' - stageS D.dec y L'` と `L'` が**データ依存**（次段の GS 分解の切り出し位置）で、
現在のテープ配置には対応する目印がない。`jobActs` 先頭の
`homeActs sc |y| (|y| - stageS D.dec y |y|) |y|` も同様に `X` の目標添字がデータ依存。
したがって `jobLoopProg` を「テープ条件だけで駆動する 1 個の `Prog.loop`」として
書くには、段の走査中に次段の切り出し位置を作業テープ（例：`S3`）へ単進で積み、
その pop で右歩きを止める、という**追加のマーカが必要**である。本ファイルは
ループ部分を引数 `JL` として受け取り、その仮定の下で `jobActs` / `batchActs` の
逐語実現を与えるところまでを担当する。
なお `jobLoop` の外側の反復自体は `X2` が左端記号 `leftSym` を読むこと
（`L' = 0`）で止められるので、停止条件そのものは読める。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.MiddleProg

open PegSeparation.RealTimeTM
open PalPeg.BorderTapes
open PalPeg.Program
open PalPeg.ProgLang
open PalPeg.BorderProg
open PalPeg.MiddleTapes

variable {sc : ℕ} {Terminal : Type} {blank : Fin sc}

/-! ## 1. 反復移動 -/

/-- 同じ動作 `a` を `n` 回。 -/
def repProg (a : Act sc) : ℕ → Prog (Act15 sc) (Cond15 sc)
  | 0 => Prog.skip
  | n + 1 => Prog.seq (ACT a) (repProg a n)

theorem repProg_exec (a : Act sc) :
    ∀ (n : ℕ) (ts : OvTapes sc),
      ExecA Terminal blank (repProg a n) ts (List.replicate n a) := by
  intro n
  induction n with
  | zero => intro ts; exact execA_skip
  | succ n ih =>
      intro ts
      refine execA_of_eq ?_ (execA_seq (execA_act (Terminal := Terminal) (blank := blank) a ts)
        (ih (applyActs blank [a] ts)))
      simp [List.replicate_succ]

/-! ## 2. 継ぎ目の歩行 -/

/-- `X` を `m` の向きへ `n` 歩。 -/
def mvXProg (m : Move) (n : ℕ) : Prog (Act15 sc) (Cond15 sc) := repProg (Act.X m) n
/-- `X2` を `m` の向きへ `n` 歩。 -/
def mvX2Prog (m : Move) (n : ℕ) : Prog (Act15 sc) (Cond15 sc) := repProg (Act.X2 m) n
/-- `F` を `m` の向きへ `n` 歩。 -/
def mvFProg (m : Move) (n : ℕ) : Prog (Act15 sc) (Cond15 sc) := repProg (Act.F m) n

theorem mvXProg_exec (m : Move) (n : ℕ) (ts : OvTapes sc) :
    ExecA Terminal blank (mvXProg m n) ts (mvX m n) := repProg_exec _ n ts

theorem mvX2Prog_exec (m : Move) (n : ℕ) (ts : OvTapes sc) :
    ExecA Terminal blank (mvX2Prog m n) ts (mvX2 m n) := repProg_exec _ n ts

theorem mvFProg_exec (m : Move) (n : ℕ) (ts : OvTapes sc) :
    ExecA Terminal blank (mvFProg m n) ts (mvF m n) := repProg_exec _ n ts

/-- `homeActs sc n a b` の有限制御。 -/
def homeActsProg (n a b : ℕ) : Prog (Act15 sc) (Cond15 sc) :=
  Prog.seq (mvXProg .left n) (Prog.seq (mvX2Prog .left n) (Prog.seq (mvFProg .left n)
    (Prog.seq (mvXProg .right a) (Prog.seq (mvX2Prog .right b) (mvFProg .right b)))))

theorem homeActsProg_exec (n a b : ℕ) (ts : OvTapes sc) :
    ExecA Terminal blank (homeActsProg n a b) ts (homeActs sc n a b) := by
  refine execA_of_eq ?_
    (execA_seq (mvXProg_exec (Terminal := Terminal) (blank := blank) .left n ts)
      (execA_seq (mvX2Prog_exec .left n _)
        (execA_seq (mvFProg_exec .left n _)
          (execA_seq (mvXProg_exec .right a _)
            (execA_seq (mvX2Prog_exec .right b _) (mvFProg_exec .right b _))))))
  simp [homeActs]

/-- `homeF sc n m` の有限制御。 -/
def homeFProg (n m : ℕ) : Prog (Act15 sc) (Cond15 sc) :=
  Prog.seq (mvFProg .left n) (mvFProg .right m)

theorem homeFProg_exec (n m : ℕ) (ts : OvTapes sc) :
    ExecA Terminal blank (homeFProg n m) ts (homeF sc n m) :=
  execA_seq (mvFProg_exec (Terminal := Terminal) (blank := blank) .left n ts)
    (mvFProg_exec .right m _)

/-- `outStep sc` の有限制御。 -/
def outStepProg : Prog (Act15 sc) (Cond15 sc) := mvFProg .right 1

theorem outStepProg_exec (ts : OvTapes sc) :
    ExecA Terminal blank (outStepProg : Prog (Act15 sc) (Cond15 sc)) ts (outStep sc) :=
  mvFProg_exec .right 1 ts

/-- `clearF zero n` の有限制御。 -/
def clearFProg (zero : Fin sc) : ℕ → Prog (Act15 sc) (Cond15 sc)
  | 0 => ACT (Act.Fset zero)
  | n + 1 =>
      Prog.seq (ACT (Act.Fset zero)) (Prog.seq (ACT (Act.F .left)) (clearFProg zero n))

theorem clearFProg_exec (zero : Fin sc) :
    ∀ (n : ℕ) (ts : OvTapes sc),
      ExecA Terminal blank (clearFProg zero n) ts (clearF zero n) := by
  intro n
  induction n with
  | zero => intro ts; exact execA_of_eq rfl (execA_act _ ts)
  | succ n ih =>
      intro ts
      refine execA_of_eq ?_
        (execA_seq (execA_act (Terminal := Terminal) (blank := blank) (Act.Fset zero) ts)
          (execA_seq (execA_act (Act.F .left) _) (ih _)))
      simp [clearF]

/-! ## 3. 何もしない 1 動作（ループ頭のプローブ） -/

/-- `P` に読んだ記号を書き戻して停留する 1 動作。テープを変えない。 -/
def nop (sc : ℕ) : Act sc := Act.P .stay

@[simp] theorem applyAct_nop (ts : OvTapes sc) : applyAct blank ts (nop sc) = ts := by
  cases ts with
  | mk P X Cnt U X2 F S1 S2 S3 S4 S5 S6 S7 S8 S9 =>
      cases P with
      | mk l f r => rfl

/-! ## 4. 一般の while ループ -/

/-- 1 反復が「頭のプローブ 1 動作 ＋ 本体」であるような、燃料つきの動作列。 -/
def whileActs (b : Fin sc) (stop : ScanState → Bool) (nxt : ScanState → ScanState)
    (body : ScanState → OvTapes sc → List (Act sc)) :
    ℕ → ScanState → OvTapes sc → List (Act sc)
  | 0, _, _ => []
  | fuel + 1, st, ts =>
      if stop st then []
      else
        nop sc :: (body st ts ++
          whileActs b stop nxt body fuel (nxt st) (applyActs b (body st ts) ts))

/-- 上の動作列のテープへの作用は、頭のプローブが恒等なので本体だけの合成に等しい。 -/
theorem whileActs_apply (stop : ScanState → Bool) (nxt : ScanState → ScanState)
    (body : ScanState → OvTapes sc → List (Act sc))
    (F : ℕ → ScanState → OvTapes sc → OvTapes sc)
    (hF0 : ∀ st ts, F 0 st ts = ts)
    (hFs : ∀ fuel st ts, F (fuel + 1) st ts =
      if stop st then ts else F fuel (nxt st) (applyActs blank (body st ts) ts)) :
    ∀ (fuel : ℕ) (st : ScanState) (ts : OvTapes sc),
      applyActs blank (whileActs blank stop nxt body fuel st ts) ts = F fuel st ts := by
  intro fuel
  induction fuel with
  | zero => intro st ts; rw [hF0]; rfl
  | succ fuel ih =>
      intro st ts
      rw [whileActs, hFs]
      by_cases h : stop st
      · rw [if_pos h, if_pos h]; rfl
      · rw [if_neg h, if_neg h, applyActs_cons, applyAct_nop, applyActs_append, ih]

/-- 長さ：本体の総和に、反復ごとの 1 動作（頭のプローブ）が足される。 -/
theorem whileActs_length_le (stop : ScanState → Bool) (nxt : ScanState → ScanState)
    (body : ScanState → OvTapes sc → List (Act sc))
    (G : ℕ → ScanState → OvTapes sc → ℕ)
    (_hG0 : ∀ st ts, G 0 st ts = 0)
    (hGs : ∀ fuel st ts, G (fuel + 1) st ts =
      if stop st then 0 else (body st ts).length +
        G fuel (nxt st) (applyActs blank (body st ts) ts)) :
    ∀ (fuel : ℕ) (st : ScanState) (ts : OvTapes sc),
      (whileActs blank stop nxt body fuel st ts).length ≤ G fuel st ts + fuel := by
  intro fuel
  induction fuel with
  | zero => intro st ts; simp [whileActs]
  | succ fuel ih =>
      intro st ts
      rw [whileActs, hGs]
      by_cases h : stop st
      · rw [if_pos h, if_pos h]; simp
      · rw [if_neg h, if_neg h]
        have := ih (nxt st) (applyActs blank (body st ts) ts)
        simp only [List.length_cons, List.length_append]
        omega

/-- while ループの有限制御。 -/
def whileProg (c : Cond15 sc) (OV : Prog (Act15 sc) (Cond15 sc)) :
    Prog (Act15 sc) (Cond15 sc) :=
  Prog.loop c (prAct (nop sc)) OV

/-- **while ループの実現**。不変条件 `Inv` は燃料も見る（燃料が尽きたときは
停止していることを要求する）。 -/
theorem whileProg_exec {c : Cond15 sc} {OV : Prog (Act15 sc) (Cond15 sc)}
    {stop : ScanState → Bool} {nxt : ScanState → ScanState}
    {body : ScanState → OvTapes sc → List (Act sc)}
    (Inv : ℕ → ScanState → OvTapes sc → Prop)
    (hcond : ∀ fuel st ts, Inv fuel st ts →
      condOf15 c (fun j => (tapeOf ts j).focus) = !stop st)
    (hzero : ∀ st ts, Inv 0 st ts → stop st = true)
    (hbody : ∀ fuel st ts, Inv (fuel + 1) st ts → stop st = false →
      ExecA Terminal blank OV ts (body st ts))
    (hpres : ∀ fuel st ts, Inv (fuel + 1) st ts → stop st = false →
      Inv fuel (nxt st) (applyActs blank (body st ts) ts)) :
    ∀ (fuel : ℕ) (st : ScanState) (ts : OvTapes sc), Inv fuel st ts →
      ExecA Terminal blank (whileProg c OV) ts
        (whileActs blank stop nxt body fuel st ts) := by
  intro fuel
  induction fuel with
  | zero =>
      intro st ts hinv
      have hs := hzero st ts hinv
      refine execA_of_eq (by simp [whileActs]) (execA_loop_stop ?_)
      rw [hcond 0 st ts hinv, hs]; rfl
  | succ fuel ih =>
      intro st ts hinv
      by_cases h : stop st
      · refine execA_of_eq (by simp [whileActs, h]) (execA_loop_stop ?_)
        rw [hcond _ st ts hinv, h]; rfl
      · have hfalse : stop st = false := by simpa using h
        have hc : condOf15 c (fun j => (tapeOf ts j).focus) = true := by
          rw [hcond _ st ts hinv, hfalse]; rfl
        have h1 : ExecA Terminal blank OV (applyAct blank ts (nop sc)) (body st ts) := by
          rw [applyAct_nop]; exact hbody fuel st ts hinv hfalse
        have h2 : ExecA Terminal blank (Prog.loop c (prAct (nop sc)) OV)
            (applyActs blank (body st ts) (applyAct blank ts (nop sc)))
            (whileActs blank stop nxt body fuel (nxt st)
              (applyActs blank (body st ts) ts)) := by
          rw [applyAct_nop]
          exact ih (nxt st) (applyActs blank (body st ts) ts) (hpres fuel st ts hinv hfalse)
        refine execA_of_eq ?_ (execA_loop_cont hc h1 h2)
        simp [whileActs, hfalse]

/-! ## 5. 段の走査 `ovRun` -/

section OvRun

variable (blank : Fin sc)
variable (leftSym endSym mark one : Fin sc) (u v T : List (Fin sc))
variable (k p₁ r minimum c : ℕ)

/-- 段の走査の停止条件（窓の終端に達したか）。 -/
def ovStopF : ScanState → Bool := fun st => decide (T.length < st.pos + minimum)

/-- 段の一歩の動作列。 -/
def ovBody : ScanState → OvTapes sc → List (Act sc) := fun st ts =>
  ovProgram blank leftSym endSym mark one k c
    (decide (k * p₁ ≤ st.q ∧ st.q ≤ r)) (decide (MatchLen u T st.pos u.length)) ts

/-- 段の走査の動作列（プローブ末尾形：反復ごとに `nop` を 1 個先頭に持つ）。 -/
def ovRunActsN : ℕ → ScanState → OvTapes sc → List (Act sc) :=
  whileActs blank (ovStopF T minimum) (ovStep u v T k p₁ r)
    (ovBody blank leftSym endSym mark one u T k p₁ r c)

/-- テープへの作用は `ovRunTapes` そのもの（`nop` は恒等）。 -/
theorem ovRunActsN_apply :
    ∀ (fuel : ℕ) (st : ScanState) (ts : OvTapes sc),
      applyActs blank (ovRunActsN blank leftSym endSym mark one u v T k p₁ r minimum c
          fuel st ts) ts
        = ovRunTapes blank leftSym endSym mark one u v T k p₁ r minimum c fuel st ts :=
  whileActs_apply (blank := blank) _ _ _
    (ovRunTapes blank leftSym endSym mark one u v T k p₁ r minimum c)
    (fun _ _ => rfl) (fun fuel st ts => by
      by_cases h : T.length < st.pos + minimum <;>
        simp [ovRunTapes, ovStopF, ovBody, h])

/-- 動作数：`ovRunActs` より反復回数（≤ `fuel`）だけ多い。 -/
theorem ovRunActsN_length_le :
    ∀ (fuel : ℕ) (st : ScanState) (ts : OvTapes sc),
      (ovRunActsN blank leftSym endSym mark one u v T k p₁ r minimum c fuel st ts).length
        ≤ (ovRunActs blank leftSym endSym mark one u v T k p₁ r minimum c
            fuel st ts).length + fuel :=
  whileActs_length_le (blank := blank) _ _ _
    (fun fuel st ts => (ovRunActs blank leftSym endSym mark one u v T k p₁ r minimum c
      fuel st ts).length)
    (fun _ _ => rfl) (fun fuel st ts => by
      by_cases h : T.length < st.pos + minimum <;>
        simp [ovRunActs, ovStopF, ovBody, h])

/-- 段の走査の有限制御。`cstop` は「窓の終端をまだ読んでいない」テープ条件、
`OV` は段の一歩（`BorderJobProg.ovStepProg`）。 -/
def ovRunProg (cstop : Cond15 sc) (OV : Prog (Act15 sc) (Cond15 sc)) :
    Prog (Act15 sc) (Cond15 sc) := whileProg cstop OV

end OvRun

/-- **段の走査の実現**。`Inv` は「燃料・走査状態・テープ」の不変条件で、
`hcond`（停止条件がヘッドの読みで決まる）、`hbody`（段の一歩の実現）を要求する。 -/
theorem ovRunProg_exec {leftSym endSym mark one : Fin sc} {u v T : List (Fin sc)}
    {k p₁ r minimum c : ℕ} {cstop : Cond15 sc} {OV : Prog (Act15 sc) (Cond15 sc)}
    (Inv : ℕ → ScanState → OvTapes sc → Prop)
    (hcond : ∀ fuel st ts, Inv fuel st ts →
      condOf15 cstop (fun j => (tapeOf ts j).focus)
        = !(decide (T.length < st.pos + minimum)))
    (hzero : ∀ st ts, Inv 0 st ts → T.length < st.pos + minimum)
    (hbody : ∀ fuel st ts, Inv (fuel + 1) st ts → ¬ (T.length < st.pos + minimum) →
      ExecA Terminal blank OV ts
        (ovProgram blank leftSym endSym mark one k c
          (decide (k * p₁ ≤ st.q ∧ st.q ≤ r))
          (decide (MatchLen u T st.pos u.length)) ts))
    (hpres : ∀ fuel st ts, Inv (fuel + 1) st ts → ¬ (T.length < st.pos + minimum) →
      Inv fuel (ovStep u v T k p₁ r st)
        (applyActs blank (ovProgram blank leftSym endSym mark one k c
          (decide (k * p₁ ≤ st.q ∧ st.q ≤ r))
          (decide (MatchLen u T st.pos u.length)) ts) ts)) :
    ∀ (fuel : ℕ) (st : ScanState) (ts : OvTapes sc), Inv fuel st ts →
      ExecA Terminal blank (ovRunProg cstop OV) ts
        (ovRunActsN blank leftSym endSym mark one u v T k p₁ r minimum c fuel st ts) := by
  refine whileProg_exec (Terminal := Terminal) (blank := blank) Inv hcond ?_ ?_ ?_
  · intro st ts h; simpa [ovStopF] using hzero st ts h
  · intro fuel st ts h hs
    exact hbody fuel st ts h (by simpa [ovStopF] using hs)
  · intro fuel st ts h hs
    exact hpres fuel st ts h (by simpa [ovStopF] using hs)

/-! ## 6. 段・バッチ -/

section Stage

variable {startSym endSym mark leftSym one zero : Fin sc}

/-- `stageActs` のプローブ末尾形（走査の各反復に `nop` が 1 個増える）。 -/
def stageActsN (blank startSym endSym mark leftSym one : Fin sc)
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) (L : ℕ)
    (ts : OvTapes sc) : List (Act sc) :=
  D.acts y L ts ++
    ovRunActsN blank leftSym endSym mark one
      ((y.take L).take (stageS D.dec y L)) ((y.take L).drop (stageS D.dec y L))
      (y.take L).reverse 8 (D.dec y L).2.1 (D.dec y L).2.2
      (max 1 (2 * stageS D.dec y L)) (stageS D.dec y L) ((8 + 2) * L + 1) ⟨0, 0⟩
      (applyActs blank (D.acts y L ts) ts)

/-- 1 段の有限制御：分解器 `DP` のあと段の走査 `OVR`。 -/
def stageProg (DP OVR : Prog (Act15 sc) (Cond15 sc)) : Prog (Act15 sc) (Cond15 sc) :=
  Prog.seq DP OVR

/-- **1 段の実現**。 -/
theorem stageProg_exec {DP OVR : Prog (Act15 sc) (Cond15 sc)}
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) (L : ℕ)
    (ts : OvTapes sc)
    (hDP : ExecA Terminal blank DP ts (D.acts y L ts))
    (hOVR : ExecA Terminal blank OVR (applyActs blank (D.acts y L ts) ts)
      (ovRunActsN blank leftSym endSym mark one
        ((y.take L).take (stageS D.dec y L)) ((y.take L).drop (stageS D.dec y L))
        (y.take L).reverse 8 (D.dec y L).2.1 (D.dec y L).2.2
        (max 1 (2 * stageS D.dec y L)) (stageS D.dec y L) ((8 + 2) * L + 1) ⟨0, 0⟩
        (applyActs blank (D.acts y L ts) ts))) :
    ExecA Terminal blank (stageProg DP OVR) ts
      (stageActsN blank startSym endSym mark leftSym one D y L ts) :=
  execA_seq hDP hOVR

/-- 1 バッチのループ以外の部分の有限制御（`jobActs` の実現）。
`JL` はループ部分（`jobLoop`）のプログラム。 -/
def jobActsProg (n a rd : ℕ) (JL : Prog (Act15 sc) (Cond15 sc)) :
    Prog (Act15 sc) (Cond15 sc) :=
  Prog.seq (homeActsProg n a n) (Prog.seq JL (homeFProg n rd))

/-- **1 バッチの実現（`jobActs` を逐語的に実行する）**。 -/
theorem jobActsProg_exec {JL : Prog (Act15 sc) (Cond15 sc)}
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) (rd : ℕ)
    (ts : OvTapes sc)
    (hJL : ExecA Terminal blank JL
      (applyActs blank (homeActs sc y.length (y.length - stageS D.dec y y.length) y.length) ts)
      (jobLoop blank startSym endSym mark leftSym one D y (y.length + 1) y.length
        (applyActs blank
          (homeActs sc y.length (y.length - stageS D.dec y y.length) y.length) ts))) :
    ExecA Terminal blank
      (jobActsProg y.length (y.length - stageS D.dec y y.length) rd JL) ts
      (jobActs blank startSym endSym mark leftSym one D y rd ts) := by
  refine execA_of_eq ?_
    (execA_seq (homeActsProg_exec (Terminal := Terminal) (blank := blank) _ _ _ ts)
      (execA_seq hJL (homeFProg_exec _ rd _)))
  simp [jobActs]

/-- 1 バッチ全体の有限制御（`batchActs` の実現）。`JA` は `jobActsProg`。 -/
def batchProg (zero : Fin sc) (n : ℕ) (JA : Prog (Act15 sc) (Cond15 sc)) :
    Prog (Act15 sc) (Cond15 sc) :=
  Prog.seq (homeFProg n n) (Prog.seq (clearFProg zero n) JA)

/-- **1 バッチの実現（`batchActs` を逐語的に実行する）**。 -/
theorem batchProg_exec {JA : Prog (Act15 sc) (Cond15 sc)}
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) (rd : ℕ)
    (ts : OvTapes sc)
    (hJA : ExecA Terminal blank JA
      (applyActs blank (clearF zero y.length)
        (applyActs blank (homeF sc y.length y.length) ts))
      (jobActs blank startSym endSym mark leftSym one D y rd
        (applyActs blank (clearF zero y.length)
          (applyActs blank (homeF sc y.length y.length) ts)))) :
    ExecA Terminal blank (batchProg zero y.length JA) ts
      (batchActs blank startSym endSym mark leftSym one zero D y rd ts) := by
  refine execA_of_eq ?_
    (execA_seq (homeFProg_exec (Terminal := Terminal) (blank := blank) y.length y.length ts)
      (execA_seq (clearFProg_exec zero y.length _) hJA))
  simp [batchActs]

end Stage

/-! ## 7. ラウンドのペース配分 (`mround`) -/

section Round

/-- `gsteps` は「動作列の接頭辞を切り取る」ことに他ならない。 -/
theorem gsteps_eq (blank : Fin sc) (r : ℕ) :
    ∀ (n : ℕ) (l : List (Act sc)) (ts : OvTapes sc),
      gsteps blank r n ⟨l, ts⟩
        = ⟨l.drop (n * r), applyActs blank (l.take (n * r)) ts⟩ := by
  intro n
  induction n with
  | zero => intro l ts; simp [gsteps]
  | succ n ih =>
      intro l ts
      rw [gsteps, show gstep blank r ⟨l, ts⟩ = ⟨l.drop r, applyActs blank (l.take r) ts⟩ from rfl,
        ih]
      have hd : (l.drop r).drop (n * r) = l.drop ((n + 1) * r) := by
        rw [List.drop_drop]; congr 1; ring
      have htk : l.take ((n + 1) * r) = l.take r ++ (l.drop r).take (n * r) := by
        rw [show (n + 1) * r = r + n * r by ring, List.take_add]
      rw [hd, htk, applyActs_append]

/-- **ラウンドのペース配分とトレースの一致**：`mround` が 1 ラウンドで実行するのは
バッチの動作列の接頭辞チャンクであり、`batchProg` のトレースは（`batchProg_exec` により）
その動作列そのもののベクトル列なので、チャンク分割はトレースの分割と一致する。 -/
theorem avecs_split (blank : Fin sc) (l : List (Act sc)) (ts : OvTapes sc) (m : ℕ) :
    avecs blank l ts
      = avecs blank (l.take m) ts ++ avecs blank (l.drop m) (applyActs blank (l.take m) ts) := by
  conv_lhs => rw [← List.take_append_drop m l]
  rw [avecs_append]

/-- `mround` の 1 ラウンドが実行する動作列（`n` ラウンド目まで）は
`batchActs` の接頭辞であり、残りはその補集合。 -/
theorem mroundProg_pacing {startSym endSym mark leftSym one zero : Fin sc}
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) (rd : ℕ)
    (ts : OvTapes sc) (n : ℕ) :
    gsteps blank (rateM D) n
        ⟨batchActs blank startSym endSym mark leftSym one zero D y rd ts, ts⟩
      = ⟨(batchActs blank startSym endSym mark leftSym one zero D y rd ts).drop
            (n * rateM D),
         applyActs blank
           ((batchActs blank startSym endSym mark leftSym one zero D y rd ts).take
             (n * rateM D)) ts⟩ :=
  gsteps_eq blank _ n _ ts

/-- **バッチのトレース**：`batchProg` を走らせたときのマイクロステップ列は
`batchActs` のベクトル列そのもの（増減なし）。 -/
theorem batchProg_trace {startSym endSym mark leftSym one zero : Fin sc}
    {JA : Prog (Act15 sc) (Cond15 sc)}
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) (rd : ℕ)
    (ts : OvTapes sc)
    (hJA : ExecA Terminal blank JA
      (applyActs blank (clearF zero y.length)
        (applyActs blank (homeF sc y.length y.length) ts))
      (jobActs blank startSym endSym mark leftSym one D y rd
        (applyActs blank (clearF zero y.length)
          (applyActs blank (homeF sc y.length y.length) ts))))
    (l : List (Option Terminal))
    (hl : l.length
      = (batchActs blank startSym endSym mark leftSym one zero D y rd ts).length) :
    trace (I15 (Terminal := Terminal)) blank l
        ([batchProg zero y.length JA], TS ts)
      = avecs blank (batchActs blank startSym endSym mark leftSym one zero D y rd ts) ts :=
  execA_trace (batchProg_exec (Terminal := Terminal) D y rd ts hJA) l hl

end Round

end PalPeg.MiddleProg

section Axioms
open PalPeg.MiddleProg
#print axioms PalPeg.MiddleProg.repProg_exec
#print axioms PalPeg.MiddleProg.homeActsProg_exec
#print axioms PalPeg.MiddleProg.homeFProg_exec
#print axioms PalPeg.MiddleProg.clearFProg_exec
#print axioms PalPeg.MiddleProg.outStepProg_exec
#print axioms PalPeg.MiddleProg.whileProg_exec
#print axioms PalPeg.MiddleProg.ovRunProg_exec
#print axioms PalPeg.MiddleProg.ovRunActsN_apply
#print axioms PalPeg.MiddleProg.ovRunActsN_length_le
#print axioms PalPeg.MiddleProg.stageProg_exec
#print axioms PalPeg.MiddleProg.jobActsProg_exec
#print axioms PalPeg.MiddleProg.batchProg_exec
#print axioms PalPeg.MiddleProg.mroundProg_pacing
#print axioms PalPeg.MiddleProg.batchProg_trace
end Axioms
