import PalPeg.MiddleTapes
import PalPeg.BorderJobProg
import PalPeg.ProgLang
import PalPeg.ProgLangLib

/-!
# 中央フラグのジョブの有限制御プログラム化 (`MiddleProg`)

`PalPeg.MiddleTapes` の動作列を `PalPeg.ProgLang` の `Prog (Act15 sc) (Cond15 sc)` として
実現する。方針は `PalPeg.BorderJobProg` と同じ。**プログラムは段幅 `S` にも窓長にも
依存しない**（`k = 8` 以外の数値パラメータを持たない）。

## 実現の形

* **左掃き**（`homeActs` / `homeF` の `mv* .left n` 部分）は番人までのループ。
  `X`／`X2` は `leftSym`、`F` はフラグ語の左端番人 `fsent` で止まる
  （`sweepXProg` / `sweepX2Prog` / `sweepFProg` / `homeLeftProg`）。
  逐語一致はしない（番人に着いたら止まるので、左端での空回りの動作を出さない）が、
  * 作用は**同一**（`leftN_clamp_eq`：左端では `step … .left` が恒等なので
    `leftN blank tp n = leftN blank tp i`）— `homeLeft_eff_eq`、
  * 動作数は元以下 — `homeLeft_length_le`。
* **段の走査** `ovRunActs` は反復回数がデータ依存なので本物の `Prog.loop`
  （`ovRunProg` = `whileProg`）。`Prog.loop c a body` は反復の先頭に 1 動作を強制し、
  `ovProgram` の先頭動作は枝によって変わる（フロンティア枝の `uFwd` は 0 動作のことが
  ある）ので、恒等動作 `nop = Act.P .stay` を反復の先頭に置く**プローブ末尾形**とする。
  作用は不変（`ovRunActsN_apply`）、動作数は `+反復回数`（`ovRunActsN_length_le`）。
* **バッチのループ** `jobLoop` は本物の `Prog.loop`（`jobLoopProg`）。停止条件は
  「`X2` が `leftSym` を読む」＝次の段幅が `0`。ここも `nop` 頭で段ごとに `+1`。
* `jobActsProg` / `batchProg` は上を継ぎ合わせる。**数値パラメータなし**。
  作用は `batchProg_effect`、動作数は `batchProg_trace_length_le`。
  ペース配分は `mroundProg_pacing`（`batchProg` 自身の動作列＝トレースの接頭辞チャンク）。

## 右歩きについて（`MiddleTapes` 側に必要な変更）

`homeActs` の右歩き（`X` を `L' - stageS D.dec y L'`、`X2`／`F` を `L'` へ）と
`homeF sc n rd` の右歩き、および `clearF` の停止には、**テープから読める停止条件が
存在しない**。理由は 2 つ：

1. 目標添字 `L' - stageS D.dec y L'` は**次段の GS 切り出し位置**であり、継ぎ目の時点では
   どのテープにも載っていない（`U` に載るのは*現段*の `u`。次段の分解器 `D.acts y L'` は
   継ぎ目の**後**に走る）。
2. フラグ語 `fw`／`ω` には左端番人が無く、テープ模型に「左端に居るか」の判定も無いので、
   `homeF` の左掃きと `clearF` の停止（添字 `0` への到達）も読めない。

したがって本ファイルは、右歩き・`clearF` を含む部分（`SEAM` / `H0` / `HR` / `PRE`）を
**プログラム引数＋実行仮定**として受け取り、その下で `jobLoopProg` を本物のループとして
組み立てる。完全にテープ駆動にするには `MiddleTapes` 側で次の 4 点が要る：

* (a) フラグ語を `fsent :: ω` 型（左端番人つき）にする。`FlagWordOK` / `clearWord` /
  `MEncodes.foutWF` / `out` の添字を 1 ずらす。
* (b) `DecompOnTapes` に「次段の切り出し位置 `stageS D.dec y (nextLen (stageS D.dec y L))`
  と `nextLen (stageS D.dec y L)` の単進コピーを作業テープ（例 `S3`／`S4`）に残す」
  フィールドを足す（`D.acts` は既に `S1 … S9` を使ってよい）。
* (c) その分 `keepS`（`ScratchBlank` の保存）を `S3`／`S4` を除いた形に弱め、
  `stageActs_scratch` / `jobLoop_scratch` / `batchActs_scratch` を貼り直す。
  単進コピーは継ぎ目の右歩きで pop され切るので、継ぎ目の**後**では再び空白になる。
* (d) `clearF` を「(a) の番人まで左へ掃きながら `zero` を書く」形に書き換える。

(b) の単進コピーがあれば、右歩きは `uBackProg` と同じ probe 末尾形
（`while S3 ≠ blank: pop S3; X を 1 右`）で書け、追加マイクロステップは
1 セルにつき 1 個（＝右歩きの歩数と同じ）で済む。
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

/-! ## 1. 何もしない 1 動作（ループ頭のプローブ） -/

/-- `P` に読んだ記号を書き戻して停留する 1 動作。テープを変えない。 -/
def nop (sc : ℕ) : Act sc := Act.P .stay

@[simp] theorem applyAct_nop (ts : OvTapes sc) : applyAct blank ts (nop sc) = ts := by
  cases ts with
  | mk P X Cnt U X2 F S1 S2 S3 S4 S5 S6 S7 S8 S9 =>
      cases P with
      | mk l f r => rfl

/-! ## 2. 番人まで左へ掃く（歩数を持たないループ） -/

/-- **左端でのクランプ**：位置 `i ≤ n` から左へ `n` 歩くのと `i` 歩くのは、
テープとして**同一**（左端では `step … .left` が恒等だから）。 -/
theorem leftN_clamp_eq {w : List (Fin sc)} :
    ∀ (n i : ℕ) (tp : TapeConfiguration sc), Tape.SeqView blank tp w i → i ≤ n →
      GSTapes.leftN blank tp n = GSTapes.leftN blank tp i := by
  intro n
  induction n with
  | zero => intro i tp _ hi; rw [show i = 0 by omega]
  | succ n ih =>
      intro i tp h hi
      cases i with
      | zero =>
          have hnil : tp.left = [] := by rw [h.left_eq]; simp
          have hid : Tape.step blank tp tp.focus .left = tp :=
            Tape.step_left_edge_self blank tp hnil
          show GSTapes.leftN blank (Tape.step blank tp tp.focus .left) n = tp
          rw [hid, ih 0 tp h (Nat.zero_le _)]
          rfl
      | succ j =>
          show GSTapes.leftN blank (Tape.step blank tp tp.focus .left) n
            = GSTapes.leftN blank (Tape.step blank tp tp.focus .left) j
          exact ih j _ (Tape.seq_move_left h) (by omega)

theorem mvX_left_clamp {w : List (Fin sc)} {n i : ℕ} {ts : OvTapes sc}
    (h : Tape.SeqView blank ts.X w i) (hi : i ≤ n) :
    applyActs blank (mvX .left n) ts = applyActs blank (mvX .left i) ts := by
  rw [mvX_eff, mvX_eff, iterM_left, iterM_left, leftN_clamp_eq n i ts.X h hi]

theorem mvX2_left_clamp {w : List (Fin sc)} {n i : ℕ} {ts : OvTapes sc}
    (h : Tape.SeqView blank ts.X2 w i) (hi : i ≤ n) :
    applyActs blank (mvX2 .left n) ts = applyActs blank (mvX2 .left i) ts := by
  rw [mvX2_eff, mvX2_eff, iterM_left, iterM_left, leftN_clamp_eq n i ts.X2 h hi]

theorem mvF_left_clamp {w : List (Fin sc)} {n i : ℕ} {ts : OvTapes sc}
    (h : Tape.SeqView blank ts.F w i) (hi : i ≤ n) :
    applyActs blank (mvF .left n) ts = applyActs blank (mvF .left i) ts := by
  rw [mvF_eff, mvF_eff, iterM_left, iterM_left, leftN_clamp_eq n i ts.F h hi]

/-- `X` を番人 `sent` まで左へ掃くループ（歩数を持たない）。 -/
def sweepXProg (sent : Fin sc) : Prog (Act15 sc) (Cond15 sc) :=
  Prog.loop (Cond15.neq tX sent) (prAct (Act.X (sc := sc) .left)) Prog.skip

/-- `X2` を番人 `sent` まで左へ掃くループ。 -/
def sweepX2Prog (sent : Fin sc) : Prog (Act15 sc) (Cond15 sc) :=
  Prog.loop (Cond15.neq tX2 sent) (prAct (Act.X2 (sc := sc) .left)) Prog.skip

/-- `F` を番人 `sent` まで左へ掃くループ。 -/
def sweepFProg (sent : Fin sc) : Prog (Act15 sc) (Cond15 sc) :=
  Prog.loop (Cond15.neq tF sent) (prAct (Act.F (sc := sc) .left)) Prog.skip

/-- 番人つきの語の中では、位置 `0` でだけ番人が読める。 -/
theorem read_sent_iff {sent : Fin sc} {y : List (Fin sc)} {tp : TapeConfiguration sc}
    {i : ℕ} (hsent : sent ∉ y) (h : Tape.SeqView blank tp (sent :: y) i) :
    (tp.focus = sent) ↔ i = 0 := by
  constructor
  · intro hf
    by_contra hne
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hlt : j < y.length := by have := h.lt; simpa using this
    have := h.focus_eq
    rw [List.getElem?_cons_succ, List.getElem?_eq_getElem hlt, hf] at this
    have hy : y[j] = sent := Option.some_inj.1 this
    exact hsent (hy ▸ List.getElem_mem hlt)
  · rintro rfl
    have := h.focus_eq
    simpa using this.symm

theorem sweepXProg_exec {sent : Fin sc} {y : List (Fin sc)} (hsent : sent ∉ y) :
    ∀ (i : ℕ) (ts : OvTapes sc), Tape.SeqView blank ts.X (sent :: y) i →
      ExecA Terminal blank (sweepXProg sent) ts (mvX .left i) := by
  intro i
  induction i with
  | zero =>
      intro ts h
      refine execA_of_eq (by simp [mvX]) (execA_loop_stop ?_)
      simp only [condOf15, tapeOf_tX, decide_eq_false_iff_not, not_not]
      exact (read_sent_iff hsent h).2 rfl
  | succ i ih =>
      intro ts h
      have hne : ts.X.focus ≠ sent := fun hc => by
        have := (read_sent_iff hsent h).1 hc; omega
      have hc : condOf15 (Cond15.neq tX sent) (fun j => (tapeOf ts j).focus) = true := by
        simp only [condOf15, tapeOf_tX, decide_eq_true_eq]; exact hne
      have h2 := ih (applyAct blank ts (Act.X .left)) (Tape.seq_move_left h)
      refine execA_of_eq ?_ (execA_loop_cont hc execA_skip h2)
      simp [mvX, List.replicate_succ]

theorem sweepX2Prog_exec {sent : Fin sc} {y : List (Fin sc)} (hsent : sent ∉ y) :
    ∀ (i : ℕ) (ts : OvTapes sc), Tape.SeqView blank ts.X2 (sent :: y) i →
      ExecA Terminal blank (sweepX2Prog sent) ts (mvX2 .left i) := by
  intro i
  induction i with
  | zero =>
      intro ts h
      refine execA_of_eq (by simp [mvX2]) (execA_loop_stop ?_)
      simp only [condOf15, tapeOf_tX2, decide_eq_false_iff_not, not_not]
      exact (read_sent_iff hsent h).2 rfl
  | succ i ih =>
      intro ts h
      have hne : ts.X2.focus ≠ sent := fun hc => by
        have := (read_sent_iff hsent h).1 hc; omega
      have hc : condOf15 (Cond15.neq tX2 sent) (fun j => (tapeOf ts j).focus) = true := by
        simp only [condOf15, tapeOf_tX2, decide_eq_true_eq]; exact hne
      have h2 := ih (applyAct blank ts (Act.X2 .left)) (Tape.seq_move_left h)
      refine execA_of_eq ?_ (execA_loop_cont hc execA_skip h2)
      simp [mvX2, List.replicate_succ]

theorem sweepFProg_exec {sent : Fin sc} {y : List (Fin sc)} (hsent : sent ∉ y) :
    ∀ (i : ℕ) (ts : OvTapes sc), Tape.SeqView blank ts.F (sent :: y) i →
      ExecA Terminal blank (sweepFProg sent) ts (mvF .left i) := by
  intro i
  induction i with
  | zero =>
      intro ts h
      refine execA_of_eq (by simp [mvF]) (execA_loop_stop ?_)
      simp only [condOf15, tapeOf_tF, decide_eq_false_iff_not, not_not]
      exact (read_sent_iff hsent h).2 rfl
  | succ i ih =>
      intro ts h
      have hne : ts.F.focus ≠ sent := fun hc => by
        have := (read_sent_iff hsent h).1 hc; omega
      have hc : condOf15 (Cond15.neq tF sent) (fun j => (tapeOf ts j).focus) = true := by
        simp only [condOf15, tapeOf_tF, decide_eq_true_eq]; exact hne
      have h2 := ih (applyAct blank ts (Act.F .left)) (Tape.seq_move_left h)
      refine execA_of_eq ?_ (execA_loop_cont hc execA_skip h2)
      simp [mvF, List.replicate_succ]

/-! ### `homeActs` の左掃き部分（歩数を持たない実現） -/

/-- `homeActs` の左掃き部分：`X`／`X2` は `leftSym`、`F` はフラグ語の左端番人
`fsent` まで掃く。数値パラメータを持たない。 -/
def homeLeftProg (leftSym fsent : Fin sc) : Prog (Act15 sc) (Cond15 sc) :=
  Prog.seq (sweepXProg leftSym) (Prog.seq (sweepX2Prog leftSym) (sweepFProg fsent))

theorem homeLeftProg_exec {leftSym fsent : Fin sc} {y ω : List (Fin sc)}
    (hleft : leftSym ∉ y) (hfs : fsent ∉ ω) {iX iX2 iF : ℕ} {ts : OvTapes sc}
    (hX : Tape.SeqView blank ts.X (leftSym :: y) iX)
    (hX2 : Tape.SeqView blank ts.X2 (leftSym :: y) iX2)
    (hF : Tape.SeqView blank ts.F (fsent :: ω) iF) :
    ExecA Terminal blank (homeLeftProg leftSym fsent) ts
      (mvX .left iX ++ (mvX2 .left iX2 ++ mvF .left iF)) := by
  have h1 := sweepXProg_exec (Terminal := Terminal) (blank := blank) hleft iX ts hX
  have hX2' : Tape.SeqView blank (applyActs blank (mvX (sc := sc) .left iX) ts).X2
      (leftSym :: y) iX2 := by rw [mvX_eff]; exact hX2
  have h2 := sweepX2Prog_exec (Terminal := Terminal) hleft iX2 _ hX2'
  have hF' : Tape.SeqView blank
      (applyActs blank (mvX2 (sc := sc) .left iX2)
        (applyActs blank (mvX (sc := sc) .left iX) ts)).F (fsent :: ω) iF := by
    rw [mvX2_eff, mvX_eff]; exact hF
  have h3 := sweepFProg_exec (Terminal := Terminal) hfs iF _ hF'
  exact execA_seq h1 (execA_seq h2 h3)

/-- **左掃きの作用は `homeActs` の左掃きと同一**（左端でのクランプ）。 -/
theorem homeLeft_eff_eq {w wF : List (Fin sc)} {n iX iX2 iF : ℕ} {ts : OvTapes sc}
    (hX : Tape.SeqView blank ts.X w iX) (hX2 : Tape.SeqView blank ts.X2 w iX2)
    (hF : Tape.SeqView blank ts.F wF iF)
    (h1 : iX ≤ n) (h2 : iX2 ≤ n) (h3 : iF ≤ n) :
    applyActs blank (mvX .left iX ++ (mvX2 .left iX2 ++ mvF .left iF)) ts
      = applyActs blank (mvX .left n ++ (mvX2 .left n ++ mvF .left n)) ts := by
  simp only [applyActs_append, mvX_eff, mvX2_eff, mvF_eff, iterM_left]
  rw [leftN_clamp_eq n iX ts.X hX h1, leftN_clamp_eq n iX2 ts.X2 hX2 h2,
    leftN_clamp_eq n iF ts.F hF h3]

/-- 左掃きの動作数は `homeActs` のそれ以下（早く止まるだけ）。 -/
theorem homeLeft_length_le {n iX iX2 iF : ℕ} (h1 : iX ≤ n) (h2 : iX2 ≤ n) (h3 : iF ≤ n) :
    (mvX (sc := sc) .left iX ++ (mvX2 .left iX2 ++ mvF .left iF)).length
      ≤ (mvX (sc := sc) .left n ++ (mvX2 .left n ++ mvF .left n)).length := by
  simp only [List.length_append, mvX_length, mvX2_length, mvF_length]
  omega

/-! ## 3. 一般の while ループ -/

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


/-! ## 6. 段 -/

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

/-- **段の作用は変わらない**。 -/
theorem stageActsN_apply (D : DecompOnTapes sc blank startSym endSym mark)
    (y : List (Fin sc)) (L : ℕ) (ts : OvTapes sc) :
    applyActs blank (stageActsN blank startSym endSym mark leftSym one D y L ts) ts
      = applyActs blank (stageActs blank startSym endSym mark leftSym one D y L ts) ts := by
  rw [stageActsN, stageActs, applyActs_append, applyActs_append, ovRunActsN_apply,
    ovRunActs_apply]

/-- **段の動作数の増分**は走査の反復回数（`≤ (8+2)*L+1`）だけ。 -/
theorem stageActsN_length_le (D : DecompOnTapes sc blank startSym endSym mark)
    (y : List (Fin sc)) (L : ℕ) (ts : OvTapes sc) :
    (stageActsN blank startSym endSym mark leftSym one D y L ts).length
      ≤ (stageActs blank startSym endSym mark leftSym one D y L ts).length
        + ((8 + 2) * L + 1) := by
  rw [stageActsN, stageActs, List.length_append, List.length_append]
  have := ovRunActsN_length_le blank leftSym endSym mark one
    ((y.take L).take (stageS D.dec y L)) ((y.take L).drop (stageS D.dec y L))
    (y.take L).reverse 8 (D.dec y L).2.1 (D.dec y L).2.2
    (max 1 (2 * stageS D.dec y L)) (stageS D.dec y L) ((8 + 2) * L + 1) ⟨0, 0⟩
    (applyActs blank (D.acts y L ts) ts)
  omega

/-- 1 段の有限制御：分解器 `DP` のあと段の走査 `OVR`。数値パラメータを持たない。 -/
def stageProg (DP OVR : Prog (Act15 sc) (Cond15 sc)) : Prog (Act15 sc) (Cond15 sc) :=
  Prog.seq DP OVR

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

/-! ## 7. バッチのループ（本物の `Prog.loop`） -/

/-- `jobLoop` のプローブ末尾形。 -/
def jobLoopActsN (blank startSym endSym mark leftSym one : Fin sc)
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) :
    ℕ → ℕ → OvTapes sc → List (Act sc)
  | 0, _, _ => []
  | fuel + 1, L, ts =>
      if L = 0 then [] else
        nop sc ::
          (stageActsN blank startSym endSym mark leftSym one D y L ts ++
            homeActs sc L (nextLen (stageS D.dec y L)
                - stageS D.dec y (nextLen (stageS D.dec y L)))
              (nextLen (stageS D.dec y L)) ++
            jobLoopActsN blank startSym endSym mark leftSym one D y fuel
              (nextLen (stageS D.dec y L))
              (applyActs blank
                (homeActs sc L (nextLen (stageS D.dec y L)
                    - stageS D.dec y (nextLen (stageS D.dec y L)))
                  (nextLen (stageS D.dec y L)))
                (applyActs blank
                  (stageActsN blank startSym endSym mark leftSym one D y L ts) ts)))

/-- **ループの作用は変わらない**。 -/
theorem jobLoopActsN_apply (D : DecompOnTapes sc blank startSym endSym mark)
    (y : List (Fin sc)) :
    ∀ (fuel L : ℕ) (ts : OvTapes sc),
      applyActs blank
          (jobLoopActsN blank startSym endSym mark leftSym one D y fuel L ts) ts
        = applyActs blank (jobLoop blank startSym endSym mark leftSym one D y fuel L ts) ts := by
  intro fuel
  induction fuel with
  | zero => intro L ts; rfl
  | succ fuel ih =>
      intro L ts
      rw [jobLoopActsN, jobLoop]
      by_cases h0 : L = 0
      · rw [if_pos h0, if_pos h0]
      · rw [if_neg h0, if_neg h0]
        simp only [applyActs_cons, applyAct_nop, applyActs_append]
        rw [stageActsN_apply, ih]

/-- **ループの動作数の増分**：各段につき `nop` 1 個と走査の反復ぶん。 -/
theorem jobLoopActsN_length_le (D : DecompOnTapes sc blank startSym endSym mark)
    (y : List (Fin sc)) (N : ℕ)
    (hnext : ∀ L, L ≤ N → nextLen (stageS D.dec y L) ≤ N) :
    ∀ (fuel L : ℕ) (ts : OvTapes sc), L ≤ N →
      (jobLoopActsN blank startSym endSym mark leftSym one D y fuel L ts).length
        ≤ (jobLoop blank startSym endSym mark leftSym one D y fuel L ts).length
          + fuel * (10 * N + 2) := by
  intro fuel
  induction fuel with
  | zero => intro L ts _; simp [jobLoopActsN]
  | succ fuel ih =>
      intro L ts hL
      rw [jobLoopActsN, jobLoop]
      by_cases h0 : L = 0
      · rw [if_pos h0, if_pos h0]; simp
      · rw [if_neg h0, if_neg h0]
        simp only [List.length_cons, List.length_append]
        rw [show applyActs blank (stageActs blank startSym endSym mark leftSym one D y L ts) ts
              = applyActs blank (stageActsN blank startSym endSym mark leftSym one D y L ts) ts
            from (stageActsN_apply D y L ts).symm]
        have hst := stageActsN_length_le (leftSym := leftSym) (one := one) D y L ts
        have hrec := ih (nextLen (stageS D.dec y L))
          (applyActs blank
            (homeActs sc L (nextLen (stageS D.dec y L)
                - stageS D.dec y (nextLen (stageS D.dec y L)))
              (nextLen (stageS D.dec y L)))
            (applyActs blank
              (stageActsN blank startSym endSym mark leftSym one D y L ts) ts))
          (hnext L hL)
        have hLN : (8 + 2) * L + 1 ≤ 10 * N + 1 := by
          have : (8 + 2) * L ≤ 10 * N := by omega
          omega
        have hmul : (fuel + 1) * (10 * N + 2) = fuel * (10 * N + 2) + (10 * N + 2) := by ring
        omega

/-- **バッチのループの有限制御**：本物の `Prog.loop`。停止条件は「`X2` が左端記号
`leftSym` を読む」（＝次の段幅が `0`）。数値パラメータを持たない。 -/
def jobLoopProg (leftSym : Fin sc) (STG SEAM : Prog (Act15 sc) (Cond15 sc)) :
    Prog (Act15 sc) (Cond15 sc) :=
  Prog.loop (Cond15.neq tX2 leftSym) (prAct (nop sc)) (Prog.seq STG SEAM)

/-- **ループの実現**。`Inv fuel L ts` は「燃料・段幅・テープ」の不変条件。 -/
theorem jobLoopProg_exec {STG SEAM : Prog (Act15 sc) (Cond15 sc)}
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc))
    (Inv : ℕ → ℕ → OvTapes sc → Prop)
    (hcond : ∀ fuel L ts, Inv fuel L ts →
      condOf15 (Cond15.neq tX2 leftSym) (fun j => (tapeOf ts j).focus) = decide (L ≠ 0))
    (hzero : ∀ L ts, Inv 0 L ts → L = 0)
    (hstg : ∀ fuel L ts, Inv (fuel + 1) L ts → L ≠ 0 →
      ExecA Terminal blank STG ts
        (stageActsN blank startSym endSym mark leftSym one D y L ts))
    (hseam : ∀ fuel L ts, Inv (fuel + 1) L ts → L ≠ 0 →
      ExecA Terminal blank SEAM
        (applyActs blank (stageActsN blank startSym endSym mark leftSym one D y L ts) ts)
        (homeActs sc L (nextLen (stageS D.dec y L)
            - stageS D.dec y (nextLen (stageS D.dec y L))) (nextLen (stageS D.dec y L))))
    (hpres : ∀ fuel L ts, Inv (fuel + 1) L ts → L ≠ 0 →
      Inv fuel (nextLen (stageS D.dec y L))
        (applyActs blank
          (homeActs sc L (nextLen (stageS D.dec y L)
              - stageS D.dec y (nextLen (stageS D.dec y L)))
            (nextLen (stageS D.dec y L)))
          (applyActs blank
            (stageActsN blank startSym endSym mark leftSym one D y L ts) ts))) :
    ∀ (fuel L : ℕ) (ts : OvTapes sc), Inv fuel L ts →
      ExecA Terminal blank (jobLoopProg leftSym STG SEAM) ts
        (jobLoopActsN blank startSym endSym mark leftSym one D y fuel L ts) := by
  intro fuel
  induction fuel with
  | zero =>
      intro L ts hinv
      have hL := hzero L ts hinv
      refine execA_of_eq (by simp [jobLoopActsN]) (execA_loop_stop ?_)
      rw [hcond 0 L ts hinv, hL]; simp
  | succ fuel ih =>
      intro L ts hinv
      by_cases h0 : L = 0
      · refine execA_of_eq (by simp [jobLoopActsN, h0]) (execA_loop_stop ?_)
        rw [hcond _ L ts hinv, h0]; simp
      · have hc : condOf15 (Cond15.neq tX2 leftSym) (fun j => (tapeOf ts j).focus) = true := by
          rw [hcond _ L ts hinv]; simp [h0]
        have hbody : ExecA Terminal blank (Prog.seq STG SEAM) (applyAct blank ts (nop sc))
            (stageActsN blank startSym endSym mark leftSym one D y L ts ++
              homeActs sc L (nextLen (stageS D.dec y L)
                  - stageS D.dec y (nextLen (stageS D.dec y L)))
                (nextLen (stageS D.dec y L))) := by
          rw [applyAct_nop]
          exact execA_seq (hstg fuel L ts hinv h0) (hseam fuel L ts hinv h0)
        have hrest := ih (nextLen (stageS D.dec y L))
          (applyActs blank
            (homeActs sc L (nextLen (stageS D.dec y L)
                - stageS D.dec y (nextLen (stageS D.dec y L)))
              (nextLen (stageS D.dec y L)))
            (applyActs blank
              (stageActsN blank startSym endSym mark leftSym one D y L ts) ts))
          (hpres fuel L ts hinv h0)
        have hrest' : ExecA Terminal blank (jobLoopProg leftSym STG SEAM)
            (applyActs blank
              (stageActsN blank startSym endSym mark leftSym one D y L ts ++
                homeActs sc L (nextLen (stageS D.dec y L)
                    - stageS D.dec y (nextLen (stageS D.dec y L)))
                  (nextLen (stageS D.dec y L)))
              (applyAct blank ts (nop sc)))
            (jobLoopActsN blank startSym endSym mark leftSym one D y fuel
              (nextLen (stageS D.dec y L))
              (applyActs blank
                (homeActs sc L (nextLen (stageS D.dec y L)
                    - stageS D.dec y (nextLen (stageS D.dec y L)))
                  (nextLen (stageS D.dec y L)))
                (applyActs blank
                  (stageActsN blank startSym endSym mark leftSym one D y L ts) ts))) := by
          rw [applyAct_nop, applyActs_append]; exact hrest
        refine execA_of_eq ?_ (execA_loop_cont hc hbody hrest')
        simp [jobLoopActsN, h0]

end Stage

/-! ## 8. バッチ全体（数値パラメータなし） -/

section Batch

variable {startSym endSym mark leftSym one zero : Fin sc}

/-- `jobActs` のプローブ末尾形。 -/
def jobActsN (blank startSym endSym mark leftSym one : Fin sc)
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) (rd : ℕ)
    (ts : OvTapes sc) : List (Act sc) :=
  homeActs sc y.length (y.length - stageS D.dec y y.length) y.length ++
    jobLoopActsN blank startSym endSym mark leftSym one D y (y.length + 1) y.length
      (applyActs blank
        (homeActs sc y.length (y.length - stageS D.dec y y.length) y.length) ts) ++
    homeF sc y.length rd

/-- `batchActs` のプローブ末尾形。 -/
def batchActsN (blank startSym endSym mark leftSym one zero : Fin sc)
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) (rd : ℕ)
    (ts : OvTapes sc) : List (Act sc) :=
  homeF sc y.length y.length ++ clearF zero y.length ++
    jobActsN blank startSym endSym mark leftSym one D y rd
      (applyActs blank (clearF zero y.length)
        (applyActs blank (homeF sc y.length y.length) ts))

/-- 1 バッチのループ以外の部分の有限制御。`H0` は最初のヘッド合わせ、`JL` はループ、
`HR` は読み出し位置への `F` の置き直し。数値パラメータを持たない。 -/
def jobActsProg (H0 JL HR : Prog (Act15 sc) (Cond15 sc)) : Prog (Act15 sc) (Cond15 sc) :=
  Prog.seq H0 (Prog.seq JL HR)

/-- 1 バッチ全体の有限制御。`PRE` は `F` のヘッド合わせ＋フラグ語の初期化。
`k = 8` 以外の数値パラメータを持たない。 -/
def batchProg (PRE JA : Prog (Act15 sc) (Cond15 sc)) : Prog (Act15 sc) (Cond15 sc) :=
  Prog.seq PRE JA

theorem jobActsProg_exec {H0 JL HR : Prog (Act15 sc) (Cond15 sc)}
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) (rd : ℕ)
    (ts : OvTapes sc)
    (hH0 : ExecA Terminal blank H0 ts
      (homeActs sc y.length (y.length - stageS D.dec y y.length) y.length))
    (hJL : ExecA Terminal blank JL
      (applyActs blank
        (homeActs sc y.length (y.length - stageS D.dec y y.length) y.length) ts)
      (jobLoopActsN blank startSym endSym mark leftSym one D y (y.length + 1) y.length
        (applyActs blank
          (homeActs sc y.length (y.length - stageS D.dec y y.length) y.length) ts)))
    (hHR : ExecA Terminal blank HR
      (applyActs blank
        (jobLoopActsN blank startSym endSym mark leftSym one D y (y.length + 1) y.length
          (applyActs blank
            (homeActs sc y.length (y.length - stageS D.dec y y.length) y.length) ts))
        (applyActs blank
          (homeActs sc y.length (y.length - stageS D.dec y y.length) y.length) ts))
      (homeF sc y.length rd)) :
    ExecA Terminal blank (jobActsProg H0 JL HR) ts
      (jobActsN blank startSym endSym mark leftSym one D y rd ts) := by
  refine execA_of_eq ?_ (execA_seq hH0 (execA_seq hJL hHR))
  simp [jobActsN]

theorem batchProg_exec {PRE JA : Prog (Act15 sc) (Cond15 sc)}
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) (rd : ℕ)
    (ts : OvTapes sc)
    (hPRE : ExecA Terminal blank PRE ts
      (homeF sc y.length y.length ++ clearF zero y.length))
    (hJA : ExecA Terminal blank JA
      (applyActs blank (homeF sc y.length y.length ++ clearF zero y.length) ts)
      (jobActsN blank startSym endSym mark leftSym one D y rd
        (applyActs blank (clearF zero y.length)
          (applyActs blank (homeF sc y.length y.length) ts)))) :
    ExecA Terminal blank (batchProg PRE JA) ts
      (batchActsN blank startSym endSym mark leftSym one zero D y rd ts) := by
  rw [← applyActs_append] at hJA
  refine execA_of_eq ?_ (execA_seq hPRE hJA)
  rw [applyActs_append]
  simp [batchActsN]

/-! ### 作用と動作数 -/

theorem jobActsN_apply (D : DecompOnTapes sc blank startSym endSym mark)
    (y : List (Fin sc)) (rd : ℕ) (ts : OvTapes sc) :
    applyActs blank (jobActsN blank startSym endSym mark leftSym one D y rd ts) ts
      = applyActs blank (jobActs blank startSym endSym mark leftSym one D y rd ts) ts := by
  simp only [jobActsN, jobActs, applyActs_append]
  rw [jobLoopActsN_apply]

/-- **バッチの作用は変わらない**（`nop` は恒等、走査の作用は `ovRunTapes`）。 -/
theorem batchProg_effect (D : DecompOnTapes sc blank startSym endSym mark)
    (y : List (Fin sc)) (rd : ℕ) (ts : OvTapes sc) :
    applyActs blank
        (batchActsN blank startSym endSym mark leftSym one zero D y rd ts) ts
      = applyActs blank
        (batchActs blank startSym endSym mark leftSym one zero D y rd ts) ts := by
  simp only [batchActsN, batchActs, applyActs_append]
  rw [jobActsN_apply]

theorem jobActsN_length_le (D : DecompOnTapes sc blank startSym endSym mark)
    (y : List (Fin sc)) (N : ℕ) (hN : y.length ≤ N)
    (hnext : ∀ L, L ≤ N → nextLen (stageS D.dec y L) ≤ N) (rd : ℕ) (ts : OvTapes sc) :
    (jobActsN blank startSym endSym mark leftSym one D y rd ts).length
      ≤ (jobActs blank startSym endSym mark leftSym one D y rd ts).length
        + (y.length + 1) * (10 * N + 2) := by
  have h := jobLoopActsN_length_le (leftSym := leftSym) (one := one) D y N hnext
    (y.length + 1) y.length
    (applyActs blank
      (homeActs sc y.length (y.length - stageS D.dec y y.length) y.length) ts) hN
  simp only [jobActsN, jobActs, List.length_append]
  omega

/-- **バッチの動作数の増分**：段の個数（`≤ |y|+1`）に比例する定数倍のみ。
（内訳：段ごとに `jobLoop` の `nop` 1 個と、段の走査の反復ごとの `nop`。） -/
theorem batchProg_trace_length_le (D : DecompOnTapes sc blank startSym endSym mark)
    (y : List (Fin sc)) (N : ℕ) (hN : y.length ≤ N)
    (hnext : ∀ L, L ≤ N → nextLen (stageS D.dec y L) ≤ N) (rd : ℕ) (ts : OvTapes sc) :
    (batchActsN blank startSym endSym mark leftSym one zero D y rd ts).length
      ≤ (batchActs blank startSym endSym mark leftSym one zero D y rd ts).length
        + (y.length + 1) * (10 * N + 2) := by
  have h := jobActsN_length_le (leftSym := leftSym) (one := one) D y N hN hnext rd
    (applyActs blank (clearF zero y.length)
      (applyActs blank (homeF sc y.length y.length) ts))
  simp only [batchActsN, batchActs, List.length_append]
  omega

end Batch

/-! ## 9. ラウンドのペース配分 (`mround`) -/

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
      rw [gsteps,
        show gstep blank r ⟨l, ts⟩ = ⟨l.drop r, applyActs blank (l.take r) ts⟩ from rfl, ih]
      have hd : (l.drop r).drop (n * r) = l.drop ((n + 1) * r) := by
        rw [List.drop_drop]; congr 1; ring
      have htk : l.take ((n + 1) * r) = l.take r ++ (l.drop r).take (n * r) := by
        rw [show (n + 1) * r = r + n * r by ring, List.take_add]
      rw [hd, htk, applyActs_append]

/-- トレースの分割は動作列の分割に一致する。 -/
theorem avecs_split (blank : Fin sc) (l : List (Act sc)) (ts : OvTapes sc) (m : ℕ) :
    avecs blank l ts
      = avecs blank (l.take m) ts
        ++ avecs blank (l.drop m) (applyActs blank (l.take m) ts) := by
  conv_lhs => rw [← List.take_append_drop m l]
  rw [avecs_append]

/-- **ペース配分**：`mround` の 1 ラウンドは `batchProg` 自身の動作列（＝トレース）の
接頭辞チャンクである。 -/
theorem mroundProg_pacing {startSym endSym mark leftSym one zero : Fin sc}
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) (rd : ℕ)
    (ts : OvTapes sc) (n : ℕ) :
    gsteps blank (rateM D) n
        ⟨batchActsN blank startSym endSym mark leftSym one zero D y rd ts, ts⟩
      = ⟨(batchActsN blank startSym endSym mark leftSym one zero D y rd ts).drop
            (n * rateM D),
         applyActs blank
           ((batchActsN blank startSym endSym mark leftSym one zero D y rd ts).take
             (n * rateM D)) ts⟩ :=
  gsteps_eq blank _ n _ ts

/-- **バッチのトレース**：`batchProg` のマイクロステップ列は `batchActsN` そのもの。 -/
theorem batchProg_trace {startSym endSym mark leftSym one zero : Fin sc}
    {PRE JA : Prog (Act15 sc) (Cond15 sc)}
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) (rd : ℕ)
    (ts : OvTapes sc)
    (hPRE : ExecA Terminal blank PRE ts
      (homeF sc y.length y.length ++ clearF zero y.length))
    (hJA : ExecA Terminal blank JA
      (applyActs blank (homeF sc y.length y.length ++ clearF zero y.length) ts)
      (jobActsN blank startSym endSym mark leftSym one D y rd
        (applyActs blank (clearF zero y.length)
          (applyActs blank (homeF sc y.length y.length) ts))))
    (l : List (Option Terminal))
    (hl : l.length
      = (batchActsN blank startSym endSym mark leftSym one zero D y rd ts).length) :
    trace (I15 (Terminal := Terminal)) blank l ([batchProg PRE JA], TS ts)
      = avecs blank (batchActsN blank startSym endSym mark leftSym one zero D y rd ts) ts :=
  execA_trace (batchProg_exec (Terminal := Terminal) D y rd ts hPRE hJA) l hl

end Round

end PalPeg.MiddleProg

section AxiomCheck
#print axioms PalPeg.MiddleProg.leftN_clamp_eq
#print axioms PalPeg.MiddleProg.sweepXProg_exec
#print axioms PalPeg.MiddleProg.sweepX2Prog_exec
#print axioms PalPeg.MiddleProg.sweepFProg_exec
#print axioms PalPeg.MiddleProg.homeLeftProg_exec
#print axioms PalPeg.MiddleProg.homeLeft_eff_eq
#print axioms PalPeg.MiddleProg.whileProg_exec
#print axioms PalPeg.MiddleProg.ovRunProg_exec
#print axioms PalPeg.MiddleProg.ovRunActsN_apply
#print axioms PalPeg.MiddleProg.ovRunActsN_length_le
#print axioms PalPeg.MiddleProg.stageProg_exec
#print axioms PalPeg.MiddleProg.jobLoopProg_exec
#print axioms PalPeg.MiddleProg.jobLoopActsN_apply
#print axioms PalPeg.MiddleProg.jobLoopActsN_length_le
#print axioms PalPeg.MiddleProg.jobActsProg_exec
#print axioms PalPeg.MiddleProg.batchProg_exec
#print axioms PalPeg.MiddleProg.batchProg_effect
#print axioms PalPeg.MiddleProg.batchProg_trace_length_le
#print axioms PalPeg.MiddleProg.mroundProg_pacing
#print axioms PalPeg.MiddleProg.batchProg_trace
end AxiomCheck
