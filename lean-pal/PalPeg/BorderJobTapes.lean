import PalPeg.BorderJob
import PalPeg.GSScanTapes

/-!
# 境界ジョブ段のテープ実現 (`BorderJobTapes`)

`PalPeg.BorderJob` の添字レベルの一歩 `ovStep`（凍結窓 `x.take L` に対する
Galil–Seiferas 型の重なり走査）を、Kim–Park 成果物のテープ模型
(`PegSeparation.RealTimeTM.TapeConfiguration`, 1 テープ 1 ヘッド) 上の
**1 セル単位のヘッド動作列**として実現し、動作数がポテンシャル `Phi` の増分で
償却されることを示す。`PalPeg.GSScanTapes` の 3 テープ版を、段の枠組み
（フロンティア検出・短い接頭辞 `u` の直接照合・フラグ出力）へ拡張したもの。

## テープ配置（6 本、各 1 ヘッド）

段は「パターン `y = x.take L` を `u ++ v`（`u = y.take s`, `v = y.drop s`）に分け、
テキスト `T = y.reverse` を走る」ものである。`|T| = L`。

* `P`   — パターン `v`。語 `startSym :: (v ++ [endSym])`、ヘッドは添字 `q + 1`。
* `X`   — **テキストは入力窓の左向き読みとして実現する**。語 `leftSym :: x`、
          ヘッドは添字 `L - (pos + |u| + q)`。
          テキスト添字 `i` ↔ `x` の添字 `L - 1 - i` ↔ `X` の添字 `L - i` である
          （`T[i] = (x.take L).reverse[i] = x[L-1-i]`）。
          添字 `0` の番兵 `leftSym` を読むことが、ちょうどフロンティア
          `pos + |u| + q = |T|` の検出になる（`x` に `leftSym` は現れない）。
          **段の窓長 `L` は「`X` のヘッドの初期位置」としてのみ現れる**ので、
          窓の終端マーカは要らない。ヘッドの添字は `pos + |u| + q ≥ 0` より常に `≤ L`。
* `Cnt` — 周期 `p₁` の単進カウンタ（`CounterView'`、底にマーカ `mark`）。
* `U`   — 短い接頭辞 `u`。語 `startSym :: (u ++ [endSym])`、静止時のヘッドは添字 `1`。
* `X2`  — `X` と同じ語 `leftSym :: x` の第 2 コピー。ヘッドは添字 `L - pos`。
          フロンティアでの `u` の直接照合はここを左へ `|u|` 歩いて読む。
* `F`   — フラグテープ。語 `fw`（長さ `|x| + 1`）、ヘッドは添字 `L - pos`。
          報告される重なり長は `ℓ = |T| - pos = L - pos` なので、
          **報告はその場での 1 回の書き込み**（`Act.Fset one`）で済む。
          `pos` は単調増加なので `F` のヘッドは段の中で左へ一方向に掃くだけで、
          総移動量は `≤ L`。`X2` と `F` はずらしのたびに同じだけ左へ動く。

## 3 つの枝（`ovStep`）

1. フロンティア (`Tape.read X = leftSym`) — `U`/`X2` を `|u|` 歩いて戻る
   （`uCheck`, 動作数 `4|u|`）。一致していれば `F` に `one` を書き、そのあとずらす。
2. 一致 (`read P ≠ endSym ∧ read P = read X`) — `P` を右へ 1、`X` を**左へ** 1。動作数 `2`。
3. 不一致 — ずらす。

ずらしは `GSScanTapes` と同じ 2 種類（周期ずらし・リセットずらし）で、
`Txt` の動きだけが左右反転する（`X` の添字はテキスト位置の減少方向）。
ずらしにはさらに `X2`/`F` の左移動 `gsShift` 回（`posMoves`）が付く。

## オラクルビット

`GSScanTapes` と同じく、周期条件 `k*p₁ ≤ q ∧ q ≤ r` はオラクルビット `b`
（`hb : b = decide …`）として与える。加えてフロンティアでの
`MatchLen u T pos |u|` の真偽をオラクルビット `bu` として与える。
`bu` が実際に `U`/`X2` の読み比べから決まることは `uCheck_reads` が保証する
（`uFwd` を `j` 歩進めた時点の 2 つの読みがちょうど `u[j]` と `T[pos+j]` である）。
短い接頭辞の長さ `c = |u|` は「`endSym` を読むまで右へ」で決まるが、
ここでは `GSScanTapes` が `qOf ts` を使うのと同様に、動作列の長さを与える
パラメータ `c`（`hc : c = u.length`）として扱う。
-/

namespace PalPeg.BorderTapes

open PegSeparation.RealTimeTM

variable {sc : ℕ}

/-! ## 0. 右方向の反復移動（`GSScanTapes.leftN` の鏡像） -/

/-- 現在の記号を書き戻しながら右へ `n` セル。 -/
def rightN (blank : Fin sc) : TapeConfiguration sc → ℕ → TapeConfiguration sc
  | tp, 0 => tp
  | tp, n + 1 => rightN blank (Tape.step blank tp tp.focus .right) n

theorem seq_rightN {blank : Fin sc} {w : List (Fin sc)} :
    ∀ (n : ℕ) (tp : TapeConfiguration sc) (i : ℕ), Tape.SeqView blank tp w i →
      i + n < w.length → Tape.SeqView blank (rightN blank tp n) w (i + n) := by
  intro n
  induction n with
  | zero => intro tp i h _; exact h
  | succ n ih =>
    intro tp i h hlt
    have h1 : Tape.SeqView blank (Tape.step blank tp tp.focus .right) w (i + 1) :=
      Tape.seq_move_right h (by omega)
    have h2 := ih (Tape.step blank tp tp.focus .right) (i + 1) h1 (by omega)
    rw [show i + 1 + n = i + (n + 1) from by omega] at h2
    exact h2

/-! ## 1. テープ状態と 1 セル動作 -/

/-- 段が使う 6 本の主テープと、分解器（`GSPreprocessTapes.decProg`）が使う
9 本の作業テープ `S1 … S9`。作業テープは段の境界では空白（`ScratchBlank`）であり、
段の走査（`ovProgram` 系）は作業テープに一切触れない。 -/
structure OvTapes (sc : ℕ) where
  P : TapeConfiguration sc
  X : TapeConfiguration sc
  Cnt : TapeConfiguration sc
  U : TapeConfiguration sc
  X2 : TapeConfiguration sc
  F : TapeConfiguration sc
  S1 : TapeConfiguration sc
  S2 : TapeConfiguration sc
  S3 : TapeConfiguration sc
  S4 : TapeConfiguration sc
  S5 : TapeConfiguration sc
  S6 : TapeConfiguration sc
  S7 : TapeConfiguration sc
  S8 : TapeConfiguration sc
  S9 : TapeConfiguration sc

/-- 1 本のテープに対する 1 個のヘッド動作。`P`/`X`/`U`/`X2`/`F` の移動は読んだ記号を
書き戻す（テープを書き換えない）。`C` はカウンタへの書き込み、`Fset` はフラグの書き込み。 -/
inductive Act (sc : ℕ) where
  | P : Move → Act sc
  | X : Move → Act sc
  | C : Fin sc → Move → Act sc
  | U : Move → Act sc
  | X2 : Move → Act sc
  | F : Move → Act sc
  | Fset : Fin sc → Act sc
  | S1 : Fin sc → Move → Act sc
  | S2 : Fin sc → Move → Act sc
  | S3 : Fin sc → Move → Act sc
  | S4 : Fin sc → Move → Act sc
  | S5 : Fin sc → Move → Act sc
  | S6 : Fin sc → Move → Act sc
  | S7 : Fin sc → Move → Act sc
  | S8 : Fin sc → Move → Act sc
  | S9 : Fin sc → Move → Act sc

def applyAct (blank : Fin sc) (ts : OvTapes sc) : Act sc → OvTapes sc
  | .P m => { ts with P := Tape.step blank ts.P ts.P.focus m }
  | .X m => { ts with X := Tape.step blank ts.X ts.X.focus m }
  | .C a m => { ts with Cnt := Tape.step blank ts.Cnt a m }
  | .U m => { ts with U := Tape.step blank ts.U ts.U.focus m }
  | .X2 m => { ts with X2 := Tape.step blank ts.X2 ts.X2.focus m }
  | .F m => { ts with F := Tape.step blank ts.F ts.F.focus m }
  | .Fset a => { ts with F := Tape.step blank ts.F a .stay }
  | .S1 a m => { ts with S1 := Tape.step blank ts.S1 a m }
  | .S2 a m => { ts with S2 := Tape.step blank ts.S2 a m }
  | .S3 a m => { ts with S3 := Tape.step blank ts.S3 a m }
  | .S4 a m => { ts with S4 := Tape.step blank ts.S4 a m }
  | .S5 a m => { ts with S5 := Tape.step blank ts.S5 a m }
  | .S6 a m => { ts with S6 := Tape.step blank ts.S6 a m }
  | .S7 a m => { ts with S7 := Tape.step blank ts.S7 a m }
  | .S8 a m => { ts with S8 := Tape.step blank ts.S8 a m }
  | .S9 a m => { ts with S9 := Tape.step blank ts.S9 a m }

def applyActs (blank : Fin sc) (l : List (Act sc)) (ts : OvTapes sc) : OvTapes sc :=
  l.foldl (applyAct blank) ts

@[simp] theorem applyActs_nil (blank : Fin sc) (ts : OvTapes sc) :
    applyActs blank [] ts = ts := rfl

@[simp] theorem applyActs_cons (blank : Fin sc) (a : Act sc) (l : List (Act sc))
    (ts : OvTapes sc) :
    applyActs blank (a :: l) ts = applyActs blank l (applyAct blank ts a) := rfl

theorem applyActs_append (blank : Fin sc) (l₁ l₂ : List (Act sc)) (ts : OvTapes sc) :
    applyActs blank (l₁ ++ l₂) ts = applyActs blank l₂ (applyActs blank l₁ ts) := by
  simp [applyActs]

/-! ### 作業テープ（`S1 … S9`）の扱い

段の走査が使う動作は主テープ 6 本にしか触れない（`NoScratch`）。分解器だけが
`Act.S1 … Act.S9` を使い、その前後で作業テープは空白である（`ScratchBlank`）。 -/

/-- 作業テープに触れない動作。 -/
def NoScratch : Act sc → Prop
  | .P _ => True
  | .X _ => True
  | .C _ _ => True
  | .U _ => True
  | .X2 _ => True
  | .F _ => True
  | .Fset _ => True
  | _ => False

/-- 動作列が作業テープに触れないこと。 -/
def NoScratchAll (l : List (Act sc)) : Prop := ∀ a ∈ l, NoScratch a

theorem noScratchAll_nil : NoScratchAll ([] : List (Act sc)) := by
  intro a ha; simp at ha

theorem noScratchAll_cons {a : Act sc} {l : List (Act sc)} (ha : NoScratch a)
    (hl : NoScratchAll l) : NoScratchAll (a :: l) := by
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact ha
  · exact hl b hb

theorem noScratchAll_append {l₁ l₂ : List (Act sc)} (h₁ : NoScratchAll l₁)
    (h₂ : NoScratchAll l₂) : NoScratchAll (l₁ ++ l₂) := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · exact h₁ a h
  · exact h₂ a h

theorem noScratchAll_replicate {a : Act sc} (ha : NoScratch a) (n : ℕ) :
    NoScratchAll (List.replicate n a) := by
  intro b hb; rw [List.eq_of_mem_replicate hb]; exact ha

theorem noScratchAll_of_sublist {l₁ l₂ : List (Act sc)} (h : ∀ a ∈ l₁, a ∈ l₂)
    (h₂ : NoScratchAll l₂) : NoScratchAll l₁ := fun a ha => h₂ a (h a ha)

/-- 2 つのテープ束の作業テープが一致していること。 -/
structure ScratchEq (t u : OvTapes sc) : Prop where
  s1 : t.S1 = u.S1
  s2 : t.S2 = u.S2
  s3 : t.S3 = u.S3
  s4 : t.S4 = u.S4
  s5 : t.S5 = u.S5
  s6 : t.S6 = u.S6
  s7 : t.S7 = u.S7
  s8 : t.S8 = u.S8
  s9 : t.S9 = u.S9

theorem ScratchEq.refl (t : OvTapes sc) : ScratchEq t t :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ScratchEq.trans {t u v : OvTapes sc} (h₁ : ScratchEq t u) (h₂ : ScratchEq u v) :
    ScratchEq t v :=
  ⟨h₁.s1.trans h₂.s1, h₁.s2.trans h₂.s2, h₁.s3.trans h₂.s3, h₁.s4.trans h₂.s4,
    h₁.s5.trans h₂.s5, h₁.s6.trans h₂.s6, h₁.s7.trans h₂.s7, h₁.s8.trans h₂.s8,
    h₁.s9.trans h₂.s9⟩

/-- 作業テープが（ヘッドを原点に置いて）空白であること。 -/
structure ScratchBlank (blank : Fin sc) (ts : OvTapes sc) : Prop where
  s1 : Tape.StackView blank ts.S1 []
  s2 : Tape.StackView blank ts.S2 []
  s3 : Tape.StackView blank ts.S3 []
  s4 : Tape.StackView blank ts.S4 []
  s5 : Tape.StackView blank ts.S5 []
  s6 : Tape.StackView blank ts.S6 []
  s7 : Tape.StackView blank ts.S7 []
  s8 : Tape.StackView blank ts.S8 []
  s9 : Tape.StackView blank ts.S9 []

theorem ScratchEq.blank {blank : Fin sc} {t u : OvTapes sc} (h : ScratchEq t u)
    (hu : ScratchBlank blank u) : ScratchBlank blank t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | (rw [h.s1]; exact hu.s1) | (rw [h.s2]; exact hu.s2) | (rw [h.s3]; exact hu.s3)
      | (rw [h.s4]; exact hu.s4) | (rw [h.s5]; exact hu.s5) | (rw [h.s6]; exact hu.s6)
      | (rw [h.s7]; exact hu.s7) | (rw [h.s8]; exact hu.s8) | (rw [h.s9]; exact hu.s9)

theorem applyAct_scratchEq {blank : Fin sc} {a : Act sc} (ha : NoScratch a)
    (ts : OvTapes sc) : ScratchEq (applyAct blank ts a) ts := by
  cases a <;> first
    | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | exact absurd ha (by simp [NoScratch])

/-- **作業テープの不変性**：作業テープに触れない動作列は作業テープを変えない。 -/
theorem applyActs_scratchEq {blank : Fin sc} :
    ∀ (l : List (Act sc)) (ts : OvTapes sc), NoScratchAll l →
      ScratchEq (applyActs blank l ts) ts := by
  intro l
  induction l with
  | nil => intro ts _; exact ScratchEq.refl _
  | cons a l ih =>
    intro ts h
    rw [applyActs_cons]
    exact (ih _ (fun b hb => h b (List.mem_cons_of_mem _ hb))).trans
      (applyAct_scratchEq (h a List.mem_cons_self) ts)

theorem applyActs_scratchBlank {blank : Fin sc} {l : List (Act sc)} {ts : OvTapes sc}
    (h : NoScratchAll l) (hb : ScratchBlank blank ts) :
    ScratchBlank blank (applyActs blank l ts) :=
  (applyActs_scratchEq l ts h).blank hb

/-! ### `S2` 以外の作業テープの不変性

`uFwd`／`uBack`（ひいては `uCheck`）は `S2` にだけ触れる（マーカの push/pop）。
`S1, S3, …, S9` については引き続き完全に不変なので、`NoScratch`／`ScratchEq` の
`S2` を除いた版を用意する。 -/

/-- 作業テープ `S2` 以外に触れない動作（`S2` への動作は許す）。 -/
def NoScratch2 : Act sc → Prop
  | .S1 _ _ => False
  | .S3 _ _ => False
  | .S4 _ _ => False
  | .S5 _ _ => False
  | .S6 _ _ => False
  | .S7 _ _ => False
  | .S8 _ _ => False
  | .S9 _ _ => False
  | _ => True

/-- 動作列が `S2` 以外の作業テープに触れないこと。 -/
def NoScratchAll2 (l : List (Act sc)) : Prop := ∀ a ∈ l, NoScratch2 a

theorem noScratchAll2_nil : NoScratchAll2 ([] : List (Act sc)) := by
  intro a ha; simp at ha

theorem noScratchAll2_cons {a : Act sc} {l : List (Act sc)} (ha : NoScratch2 a)
    (hl : NoScratchAll2 l) : NoScratchAll2 (a :: l) := by
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact ha
  · exact hl b hb

theorem noScratchAll2_append {l₁ l₂ : List (Act sc)} (h₁ : NoScratchAll2 l₁)
    (h₂ : NoScratchAll2 l₂) : NoScratchAll2 (l₁ ++ l₂) := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · exact h₁ a h
  · exact h₂ a h

/-- 2 つのテープ束が `S2` 以外の作業テープで一致していること。 -/
structure ScratchEq2 (t u : OvTapes sc) : Prop where
  s1 : t.S1 = u.S1
  s3 : t.S3 = u.S3
  s4 : t.S4 = u.S4
  s5 : t.S5 = u.S5
  s6 : t.S6 = u.S6
  s7 : t.S7 = u.S7
  s8 : t.S8 = u.S8
  s9 : t.S9 = u.S9

theorem ScratchEq2.trans {t u v : OvTapes sc} (h₁ : ScratchEq2 t u) (h₂ : ScratchEq2 u v) :
    ScratchEq2 t v :=
  ⟨h₁.s1.trans h₂.s1, h₁.s3.trans h₂.s3, h₁.s4.trans h₂.s4,
    h₁.s5.trans h₂.s5, h₁.s6.trans h₂.s6, h₁.s7.trans h₂.s7, h₁.s8.trans h₂.s8,
    h₁.s9.trans h₂.s9⟩

theorem applyAct_scratchEq2 {blank : Fin sc} {a : Act sc} (ha : NoScratch2 a)
    (ts : OvTapes sc) : ScratchEq2 (applyAct blank ts a) ts := by
  cases a <;> first
    | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | exact absurd ha (by simp [NoScratch2])

theorem applyActs_scratchEq2 {blank : Fin sc} :
    ∀ (l : List (Act sc)) (ts : OvTapes sc), NoScratchAll2 l →
      ScratchEq2 (applyActs blank l ts) ts := by
  intro l
  induction l with
  | nil => intro ts _; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons a l ih =>
    intro ts h
    rw [applyActs_cons]
    exact (ih _ (fun b hb => h b (List.mem_cons_of_mem _ hb))).trans
      (applyAct_scratchEq2 (h a List.mem_cons_self) ts)

/-- `ScratchEq2` と（`S2` 成分を除く）`ScratchBlank` の伝播。 -/
theorem ScratchEq2.blankOthers {blank : Fin sc} {t u : OvTapes sc} (h : ScratchEq2 t u)
    (hu : ScratchBlank blank u) :
    Tape.StackView blank t.S1 [] ∧ Tape.StackView blank t.S3 [] ∧
      Tape.StackView blank t.S4 [] ∧ Tape.StackView blank t.S5 [] ∧
      Tape.StackView blank t.S6 [] ∧ Tape.StackView blank t.S7 [] ∧
      Tape.StackView blank t.S8 [] ∧ Tape.StackView blank t.S9 [] :=
  ⟨by rw [h.s1]; exact hu.s1, by rw [h.s3]; exact hu.s3, by rw [h.s4]; exact hu.s4,
    by rw [h.s5]; exact hu.s5, by rw [h.s6]; exact hu.s6, by rw [h.s7]; exact hu.s7,
    by rw [h.s8]; exact hu.s8, by rw [h.s9]; exact hu.s9⟩

/-! ## 2. 動作列 -/

/-- 周期ずらしの下げループ：`P` を 1 左、カウンタを 1 下げる、を `n` 回。 -/
def perLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => Act.P .left :: Act.C blank .left :: Act.C blank .stay :: perLoop blank n

/-- `pos` の増加に伴う `X2`／`F` の左移動を `n` 回。 -/
def posMoves (sc : ℕ) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => Act.X2 .left :: Act.F .left :: posMoves sc n

/-- 周期ずらしの動作列（下げ `n` 回 → マーカ検出 → 上げ `n` 回 → `X2`/`F` を `n` 左）。 -/
def periodActs (blank mark : Fin sc) (n : ℕ) : List (Act sc) :=
  perLoop blank n ++
    (Act.C blank .left :: Act.C mark .right :: List.replicate n (Act.C blank .right)) ++
    posMoves sc n

/-- リセットずらしの歩行：`P` を `n` 回左へ、位相 `c` が `0` のときだけ `X` を止める。
`X` はテキスト位置の**減少**方向（＝右）へ動く。 -/
def resetWalk (sc k : ℕ) : ℕ → ℕ → List (Act sc)
  | 0, _ => []
  | n + 1, 0 => Act.P .left :: resetWalk sc k n (k - 1)
  | n + 1, c + 1 => Act.P .left :: Act.X .right :: resetWalk sc k n c

/-- リセットずらしの動作列：歩行 → 左端 `startSym` を踏んで 1 歩戻る →
（`q = 0` のときだけ）`X` を 1 左へ → `X2`/`F` を `max 1 ⌈q/k⌉` 左へ。 -/
def resetShift (sc k q : ℕ) : List (Act sc) :=
  resetWalk sc k q 0 ++
    (Act.P .left :: Act.P .right :: (if q = 0 then [Act.X (sc := sc) .left] else [])) ++
    posMoves sc (max 1 (ceilDiv q k))

/-- `u` の直接照合の往路の 1 段（`uFwd` の実質部分）：`U` を右、`X2` を左、
`S2` に `mark` を push する（`n` の単進コピーを積む）。 -/
def uFwdStep (sc : ℕ) (mark : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => Act.U .right :: Act.X2 .left :: Act.S2 mark .right :: uFwdStep sc mark n

/-- `u` の直接照合の往路：`uFwdStep` のあと `S2` を 1 回 pop し、`S2` の読みで
`uBack` の反復回数（`n` が `0` か否か）を判定できるようにする。 -/
def uFwd (sc : ℕ) (blank mark : Fin sc) (n : ℕ) : List (Act sc) :=
  uFwdStep sc mark n ++ [Act.S2 blank .left]

/-- `u` の直接照合の復路：`Prog.loop` の条件が反復の最後の動作
（`S2` の pop）の直後に評価できるよう、各反復を「前回の pop 結果を消す
（`S2 blank .stay`）→ `U` を左・`X2` を右 → 次の pop（`S2 blank .left`）」の
順に組む（`GS_OVERLAP.md` の probe 方式、`BorderJobProg.lean` の `Obstructions`
節を参照）。 -/
def uBack (sc : ℕ) (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 =>
      Act.S2 blank .stay :: Act.U .left :: Act.X2 .right :: Act.S2 blank .left ::
        uBack sc blank n

/-- `u` の直接照合（往復）。ヘッドは元の位置に戻る。`S2` は往復の前後で空
（`ScratchBlank`）。 -/
def uCheck (sc : ℕ) (blank mark : Fin sc) (c : ℕ) : List (Act sc) :=
  uFwd sc blank mark c ++ uBack sc blank c

/-- `P` のヘッド位置から読み取れる一致長 `q`。 -/
def qOf (ts : OvTapes sc) : ℕ := ts.P.left.length - 1

/-- カウンタテープから読み取れる周期 `p₁`。 -/
def p1Of (ts : OvTapes sc) : ℕ := ts.Cnt.left.length - 1

/-- ずらしの動作列。 -/
def shiftActs (blank mark : Fin sc) (k : ℕ) (b : Bool) (ts : OvTapes sc) : List (Act sc) :=
  if b then periodActs blank mark (p1Of ts) else resetShift sc k (qOf ts)

/-- 段の一歩を実現する動作列。 -/
def ovProgram (blank leftSym endSym mark one : Fin sc) (k c : ℕ) (b bu : Bool)
    (ts : OvTapes sc) : List (Act sc) :=
  if Tape.read ts.X = leftSym then
    uCheck sc blank mark c ++ (if bu then [Act.Fset one] else []) ++ shiftActs blank mark k b ts
  else if Tape.read ts.P ≠ endSym ∧ Tape.read ts.P = Tape.read ts.X then
    [Act.P .right, Act.X .left]
  else shiftActs blank mark k b ts

/-! ### 段の動作列は作業テープに触れない -/

theorem noScratch_perLoop (blank : Fin sc) : ∀ n, NoScratchAll (perLoop blank n) := by
  intro n
  induction n with
  | zero => exact noScratchAll_nil
  | succ n ih =>
    exact noScratchAll_cons trivial (noScratchAll_cons trivial (noScratchAll_cons trivial ih))

theorem noScratch_posMoves (sc : ℕ) : ∀ n, NoScratchAll (posMoves sc n) := by
  intro n
  induction n with
  | zero => exact noScratchAll_nil
  | succ n ih => exact noScratchAll_cons trivial (noScratchAll_cons trivial ih)

theorem noScratch_periodActs (blank mark : Fin sc) (n : ℕ) :
    NoScratchAll (periodActs blank mark n) := by
  refine noScratchAll_append (noScratchAll_append (noScratch_perLoop blank n) ?_)
    (noScratch_posMoves sc n)
  exact noScratchAll_cons trivial (noScratchAll_cons trivial
    (noScratchAll_replicate (a := Act.C blank Move.right) trivial n))

theorem noScratch_resetWalk (sc k : ℕ) : ∀ (n c : ℕ), NoScratchAll (resetWalk sc k n c) := by
  intro n
  induction n with
  | zero => intro c; exact noScratchAll_nil
  | succ n ih =>
    intro c
    cases c with
    | zero => exact noScratchAll_cons trivial (ih _)
    | succ c => exact noScratchAll_cons trivial (noScratchAll_cons trivial (ih _))

theorem noScratch_resetShift (sc k q : ℕ) : NoScratchAll (resetShift sc k q) := by
  refine noScratchAll_append (noScratchAll_append (noScratch_resetWalk sc k q 0) ?_)
    (noScratch_posMoves sc _)
  refine noScratchAll_cons trivial (noScratchAll_cons trivial ?_)
  by_cases h : q = 0
  · rw [if_pos h]; exact noScratchAll_cons trivial noScratchAll_nil
  · rw [if_neg h]; exact noScratchAll_nil

/-- `uFwd`／`uBack`／`uCheck` は `S2` に触れるので、もはや `NoScratchAll` ではない
（`S2` は往復の前後でのみ空に戻る：`uCheck_S2`、`ovProgram_scratchBlank` を参照）。 -/
theorem noScratch_shiftActs (blank mark : Fin sc) (k : ℕ) (b : Bool) (ts : OvTapes sc) :
    NoScratchAll (shiftActs blank mark k b ts) := by
  simp only [shiftActs]
  split_ifs
  · exact noScratch_periodActs _ _ _
  · exact noScratch_resetShift _ _ _

/-! ## 3. 動作列の長さ -/

@[simp] theorem posMoves_length (sc n : ℕ) : (posMoves sc n).length = 2 * n := by
  induction n with
  | zero => simp [posMoves]
  | succ n ih => simp only [posMoves, List.length_cons, ih]; omega

@[simp] theorem perLoop_length (blank : Fin sc) (n : ℕ) :
    (perLoop blank n).length = 3 * n := by
  induction n with
  | zero => simp [perLoop]
  | succ n ih => simp only [perLoop, List.length_cons, ih]; omega

theorem periodActs_length (blank mark : Fin sc) (n : ℕ) :
    (periodActs blank mark n).length = 6 * n + 2 := by
  simp only [periodActs, List.length_append, List.length_cons, List.length_replicate,
    perLoop_length, posMoves_length]
  omega

theorem resetWalk_length (sc k : ℕ) : ∀ n c,
    (resetWalk sc k n c).length = n + GSTapes.moves k n c := by
  intro n
  induction n with
  | zero => intro c; simp [resetWalk, GSTapes.moves]
  | succ n ih =>
    intro c
    cases c with
    | zero =>
      have h := ih (k - 1)
      simp only [resetWalk, GSTapes.moves, List.length_cons, h]
      omega
    | succ c =>
      have h := ih c
      simp only [resetWalk, GSTapes.moves, List.length_cons, h]
      omega

theorem resetShift_length (sc k q : ℕ) :
    (resetShift sc k q).length
      = q + GSTapes.moves k q 0 + 2 + (if q = 0 then 1 else 0)
        + 2 * max 1 (ceilDiv q k) := by
  simp only [resetShift, List.length_append, List.length_cons, resetWalk_length,
    posMoves_length]
  split_ifs <;> simp

@[simp] theorem uFwdStep_length (sc : ℕ) (mark : Fin sc) (n : ℕ) :
    (uFwdStep sc mark n).length = 3 * n := by
  induction n with
  | zero => simp [uFwdStep]
  | succ n ih => simp only [uFwdStep, List.length_cons, ih]; omega

/-- `uFwd` の動作数は `3n + 1`（`uFwdStep` の `3n` に閉じの pop `1` を足したもの）。 -/
@[simp] theorem uFwd_length (sc : ℕ) (blank mark : Fin sc) (n : ℕ) :
    (uFwd sc blank mark n).length = 3 * n + 1 := by
  simp only [uFwd, List.length_append, uFwdStep_length, List.length_cons, List.length_nil]

/-- `uBack` の動作数は `4n`（各反復が消去・`U`・`X2`・pop の 4 動作）。 -/
@[simp] theorem uBack_length (sc : ℕ) (blank : Fin sc) (n : ℕ) :
    (uBack sc blank n).length = 4 * n := by
  induction n with
  | zero => simp [uBack]
  | succ n ih => simp only [uBack, List.length_cons, ih]; omega

/-- `uCheck` の動作数は `7c + 1`（旧版の `4c` から、`S2` のマーカ往復のぶん増える）。 -/
@[simp] theorem uCheck_length (sc : ℕ) (blank mark : Fin sc) (c : ℕ) :
    (uCheck sc blank mark c).length = 7 * c + 1 := by
  simp only [uCheck, List.length_append, uFwd_length, uBack_length]
  omega


/-! ## 4. 動作列の効果（テープごとの射影） -/

section Proj

variable (blank mark : Fin sc)

theorem perLoop_P : ∀ n (ts : OvTapes sc),
    (applyActs blank (perLoop blank n) ts).P = GSTapes.leftN blank ts.P n := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih =>
    intro ts
    simp only [perLoop, applyActs_cons, applyAct, GSTapes.leftN]
    exact ih _

theorem perLoop_Cnt : ∀ n (ts : OvTapes sc),
    (applyActs blank (perLoop blank n) ts).Cnt = GSTapes.decN blank ts.Cnt n := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih =>
    intro ts
    simp only [perLoop, applyActs_cons, applyAct, GSTapes.decN]
    exact ih _

theorem perLoop_X : ∀ n (ts : OvTapes sc),
    (applyActs blank (perLoop blank n) ts).X = ts.X := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [perLoop, applyActs_cons, applyAct]; exact ih _

theorem perLoop_U : ∀ n (ts : OvTapes sc),
    (applyActs blank (perLoop blank n) ts).U = ts.U := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [perLoop, applyActs_cons, applyAct]; exact ih _

theorem perLoop_X2 : ∀ n (ts : OvTapes sc),
    (applyActs blank (perLoop blank n) ts).X2 = ts.X2 := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [perLoop, applyActs_cons, applyAct]; exact ih _

theorem perLoop_F : ∀ n (ts : OvTapes sc),
    (applyActs blank (perLoop blank n) ts).F = ts.F := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [perLoop, applyActs_cons, applyAct]; exact ih _

theorem replC_Cnt : ∀ n (ts : OvTapes sc),
    (applyActs blank (List.replicate n (Act.C blank .right)) ts).Cnt
      = GSTapes.incN blank ts.Cnt n := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih =>
    intro ts
    simp only [List.replicate_succ, applyActs_cons, applyAct, GSTapes.incN]
    exact ih _

theorem replC_P (a : Fin sc) : ∀ n (ts : OvTapes sc),
    (applyActs blank (List.replicate n (Act.C a .right)) ts).P = ts.P := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [List.replicate_succ, applyActs_cons, applyAct]; exact ih _

theorem replC_X (a : Fin sc) : ∀ n (ts : OvTapes sc),
    (applyActs blank (List.replicate n (Act.C a .right)) ts).X = ts.X := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [List.replicate_succ, applyActs_cons, applyAct]; exact ih _

theorem replC_U (a : Fin sc) : ∀ n (ts : OvTapes sc),
    (applyActs blank (List.replicate n (Act.C a .right)) ts).U = ts.U := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [List.replicate_succ, applyActs_cons, applyAct]; exact ih _

theorem replC_X2 (a : Fin sc) : ∀ n (ts : OvTapes sc),
    (applyActs blank (List.replicate n (Act.C a .right)) ts).X2 = ts.X2 := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [List.replicate_succ, applyActs_cons, applyAct]; exact ih _

theorem replC_F (a : Fin sc) : ∀ n (ts : OvTapes sc),
    (applyActs blank (List.replicate n (Act.C a .right)) ts).F = ts.F := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [List.replicate_succ, applyActs_cons, applyAct]; exact ih _

theorem posMoves_X2 : ∀ n (ts : OvTapes sc),
    (applyActs blank (posMoves sc n) ts).X2 = GSTapes.leftN blank ts.X2 n := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih =>
    intro ts
    simp only [posMoves, applyActs_cons, applyAct, GSTapes.leftN]
    exact ih _

theorem posMoves_F : ∀ n (ts : OvTapes sc),
    (applyActs blank (posMoves sc n) ts).F = GSTapes.leftN blank ts.F n := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih =>
    intro ts
    simp only [posMoves, applyActs_cons, applyAct, GSTapes.leftN]
    exact ih _

theorem posMoves_P : ∀ n (ts : OvTapes sc),
    (applyActs blank (posMoves sc n) ts).P = ts.P := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [posMoves, applyActs_cons, applyAct]; exact ih _

theorem posMoves_X : ∀ n (ts : OvTapes sc),
    (applyActs blank (posMoves sc n) ts).X = ts.X := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [posMoves, applyActs_cons, applyAct]; exact ih _

theorem posMoves_Cnt : ∀ n (ts : OvTapes sc),
    (applyActs blank (posMoves sc n) ts).Cnt = ts.Cnt := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [posMoves, applyActs_cons, applyAct]; exact ih _

theorem posMoves_U : ∀ n (ts : OvTapes sc),
    (applyActs blank (posMoves sc n) ts).U = ts.U := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [posMoves, applyActs_cons, applyAct]; exact ih _

variable (k : ℕ)

theorem resetWalk_P : ∀ n c (ts : OvTapes sc),
    (applyActs blank (resetWalk sc k n c) ts).P = GSTapes.leftN blank ts.P n := by
  intro n
  induction n with
  | zero => intro c ts; rfl
  | succ n ih =>
    intro c ts
    cases c with
    | zero =>
      simp only [resetWalk, applyActs_cons, applyAct, GSTapes.leftN]
      exact ih _ _
    | succ c =>
      simp only [resetWalk, applyActs_cons, applyAct, GSTapes.leftN]
      exact ih _ _

theorem resetWalk_X : ∀ n c (ts : OvTapes sc),
    (applyActs blank (resetWalk sc k n c) ts).X = rightN blank ts.X (GSTapes.moves k n c) := by
  intro n
  induction n with
  | zero => intro c ts; rfl
  | succ n ih =>
    intro c ts
    cases c with
    | zero =>
      simp only [resetWalk, applyActs_cons, applyAct, GSTapes.moves]
      exact ih _ _
    | succ c =>
      simp only [resetWalk, applyActs_cons, applyAct, GSTapes.moves, rightN]
      exact ih _ _

theorem resetWalk_Cnt : ∀ n c (ts : OvTapes sc),
    (applyActs blank (resetWalk sc k n c) ts).Cnt = ts.Cnt := by
  intro n
  induction n with
  | zero => intro c ts; rfl
  | succ n ih =>
    intro c ts
    cases c with
    | zero => simp only [resetWalk, applyActs_cons, applyAct]; exact ih _ _
    | succ c => simp only [resetWalk, applyActs_cons, applyAct]; exact ih _ _

theorem resetWalk_U : ∀ n c (ts : OvTapes sc),
    (applyActs blank (resetWalk sc k n c) ts).U = ts.U := by
  intro n
  induction n with
  | zero => intro c ts; rfl
  | succ n ih =>
    intro c ts
    cases c with
    | zero => simp only [resetWalk, applyActs_cons, applyAct]; exact ih _ _
    | succ c => simp only [resetWalk, applyActs_cons, applyAct]; exact ih _ _

theorem resetWalk_X2 : ∀ n c (ts : OvTapes sc),
    (applyActs blank (resetWalk sc k n c) ts).X2 = ts.X2 := by
  intro n
  induction n with
  | zero => intro c ts; rfl
  | succ n ih =>
    intro c ts
    cases c with
    | zero => simp only [resetWalk, applyActs_cons, applyAct]; exact ih _ _
    | succ c => simp only [resetWalk, applyActs_cons, applyAct]; exact ih _ _

theorem resetWalk_F : ∀ n c (ts : OvTapes sc),
    (applyActs blank (resetWalk sc k n c) ts).F = ts.F := by
  intro n
  induction n with
  | zero => intro c ts; rfl
  | succ n ih =>
    intro c ts
    cases c with
    | zero => simp only [resetWalk, applyActs_cons, applyAct]; exact ih _ _
    | succ c => simp only [resetWalk, applyActs_cons, applyAct]; exact ih _ _

theorem uFwdStep_U : ∀ n (ts : OvTapes sc),
    (applyActs blank (uFwdStep sc mark n) ts).U = rightN blank ts.U n := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih =>
    intro ts
    simp only [uFwdStep, applyActs_cons, applyAct, rightN]
    exact ih _

theorem uFwdStep_X2 : ∀ n (ts : OvTapes sc),
    (applyActs blank (uFwdStep sc mark n) ts).X2 = GSTapes.leftN blank ts.X2 n := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih =>
    intro ts
    simp only [uFwdStep, applyActs_cons, applyAct, GSTapes.leftN]
    exact ih _

theorem uFwdStep_P : ∀ n (ts : OvTapes sc),
    (applyActs blank (uFwdStep sc mark n) ts).P = ts.P := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [uFwdStep, applyActs_cons, applyAct]; exact ih _

theorem uFwdStep_X : ∀ n (ts : OvTapes sc),
    (applyActs blank (uFwdStep sc mark n) ts).X = ts.X := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [uFwdStep, applyActs_cons, applyAct]; exact ih _

theorem uFwdStep_Cnt : ∀ n (ts : OvTapes sc),
    (applyActs blank (uFwdStep sc mark n) ts).Cnt = ts.Cnt := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [uFwdStep, applyActs_cons, applyAct]; exact ih _

theorem uFwdStep_F : ∀ n (ts : OvTapes sc),
    (applyActs blank (uFwdStep sc mark n) ts).F = ts.F := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [uFwdStep, applyActs_cons, applyAct]; exact ih _

/-- `uFwdStep` は `S2` に `mark` の単進コピー `n` 個を積む（下に元の内容 `l`）。 -/
theorem uFwdStep_S2 : ∀ n (ts : OvTapes sc) (l : List (Fin sc)),
    Tape.StackView blank ts.S2 l →
    Tape.StackView blank (applyActs blank (uFwdStep sc mark n) ts).S2
      (List.replicate n mark ++ l) := by
  intro n
  induction n with
  | zero => intro ts l h; simpa [uFwdStep] using h
  | succ n ih =>
    intro ts l h
    simp only [uFwdStep, applyActs_cons]
    set ts1 := applyAct blank ts (Act.U (sc := sc) .right) with hts1
    set ts2 := applyAct blank ts1 (Act.X2 (sc := sc) .left) with hts2
    set ts3 := applyAct blank ts2 (Act.S2 mark .right) with hts3
    have hts3S2 : ts3.S2 = Tape.step blank ts.S2 mark .right := by
      rw [hts3, hts2, hts1]; rfl
    have h3 : Tape.StackView blank ts3.S2 (mark :: l) := by
      rw [hts3S2]; exact Tape.push_spec h mark
    have h2 := ih ts3 (mark :: l) h3
    rw [show List.replicate (n + 1) mark ++ l = List.replicate n mark ++ (mark :: l) from by
      simp [List.replicate_succ', List.append_assoc]]
    exact h2

theorem uFwd_U (n : ℕ) (ts : OvTapes sc) :
    (applyActs blank (uFwd sc blank mark n) ts).U = rightN blank ts.U n := by
  unfold uFwd
  rw [applyActs_append]
  simp only [applyActs_cons, applyActs_nil, applyAct]
  exact uFwdStep_U blank mark n ts

theorem uFwd_X2 (n : ℕ) (ts : OvTapes sc) :
    (applyActs blank (uFwd sc blank mark n) ts).X2 = GSTapes.leftN blank ts.X2 n := by
  unfold uFwd
  rw [applyActs_append]
  simp only [applyActs_cons, applyActs_nil, applyAct]
  exact uFwdStep_X2 blank mark n ts

theorem uFwd_P (n : ℕ) (ts : OvTapes sc) :
    (applyActs blank (uFwd sc blank mark n) ts).P = ts.P := by
  unfold uFwd
  rw [applyActs_append]
  simp only [applyActs_cons, applyActs_nil, applyAct]
  exact uFwdStep_P blank mark n ts

theorem uFwd_X (n : ℕ) (ts : OvTapes sc) :
    (applyActs blank (uFwd sc blank mark n) ts).X = ts.X := by
  unfold uFwd
  rw [applyActs_append]
  simp only [applyActs_cons, applyActs_nil, applyAct]
  exact uFwdStep_X blank mark n ts

theorem uFwd_Cnt (n : ℕ) (ts : OvTapes sc) :
    (applyActs blank (uFwd sc blank mark n) ts).Cnt = ts.Cnt := by
  unfold uFwd
  rw [applyActs_append]
  simp only [applyActs_cons, applyActs_nil, applyAct]
  exact uFwdStep_Cnt blank mark n ts

theorem uFwd_F (n : ℕ) (ts : OvTapes sc) :
    (applyActs blank (uFwd sc blank mark n) ts).F = ts.F := by
  unfold uFwd
  rw [applyActs_append]
  simp only [applyActs_cons, applyActs_nil, applyAct]
  exact uFwdStep_F blank mark n ts

/-- `uFwd`（push `n` 回 → 1 回 pop）の直後の `S2`：`n = 0` なら空のまま、
`n = m + 1` なら最上段 `mark` が読める状態（残りは `m` 個の `mark`）。 -/
theorem uFwd_S2 (n : ℕ) (ts : OvTapes sc) (h : Tape.StackView blank ts.S2 []) :
    (n = 0 → Tape.StackView blank (applyActs blank (uFwd sc blank mark n) ts).S2 []) ∧
      (∀ m, n = m + 1 →
        Tape.StackTopView blank (applyActs blank (uFwd sc blank mark n) ts).S2 mark
          (List.replicate m mark)) := by
  have hpush := uFwdStep_S2 blank mark n ts [] h
  rw [List.append_nil] at hpush
  unfold uFwd
  rw [applyActs_append]
  simp only [applyActs_cons, applyActs_nil, applyAct]
  constructor
  · intro hn; subst hn; simpa using Tape.pop_empty hpush
  · intro m hm
    subst hm
    rw [List.replicate_succ] at hpush
    exact Tape.pop_spec hpush

theorem uBack_U : ∀ n (ts : OvTapes sc),
    (applyActs blank (uBack sc blank n) ts).U = GSTapes.leftN blank ts.U n := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih =>
    intro ts
    simp only [uBack, applyActs_cons, applyAct, GSTapes.leftN]
    exact ih _

theorem uBack_X2 : ∀ n (ts : OvTapes sc),
    (applyActs blank (uBack sc blank n) ts).X2 = rightN blank ts.X2 n := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih =>
    intro ts
    simp only [uBack, applyActs_cons, applyAct, rightN]
    exact ih _

theorem uBack_P : ∀ n (ts : OvTapes sc), (applyActs blank (uBack sc blank n) ts).P = ts.P := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [uBack, applyActs_cons, applyAct]; exact ih _

theorem uBack_X : ∀ n (ts : OvTapes sc), (applyActs blank (uBack sc blank n) ts).X = ts.X := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [uBack, applyActs_cons, applyAct]; exact ih _

theorem uBack_Cnt : ∀ n (ts : OvTapes sc),
    (applyActs blank (uBack sc blank n) ts).Cnt = ts.Cnt := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [uBack, applyActs_cons, applyAct]; exact ih _

theorem uBack_F : ∀ n (ts : OvTapes sc), (applyActs blank (uBack sc blank n) ts).F = ts.F := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; simp only [uBack, applyActs_cons, applyAct]; exact ih _

/-- `uBack`：開始時の `S2` が「`n = 0` で既に空」または
「`n = m + 1` で最上段 `mark`・残り `m` 個」であれば、`n` 回の
erase-then-pop を経て `S2` は空に戻る。 -/
theorem uBack_S2 : ∀ n (ts : OvTapes sc),
    (n = 0 ∧ Tape.StackView blank ts.S2 []) ∨
      (∃ m, n = m + 1 ∧ Tape.StackTopView blank ts.S2 mark (List.replicate m mark)) →
    Tape.StackView blank (applyActs blank (uBack sc blank n) ts).S2 [] := by
  intro n
  induction n with
  | zero =>
      intro ts h
      rcases h with ⟨_, hv⟩ | ⟨m, hm, _⟩
      · simpa [uBack] using hv
      · omega
  | succ n ih =>
      intro ts h
      rcases h with ⟨hc, _⟩ | ⟨m, hm, htop⟩
      · omega
      · have hmn : m = n := by omega
        rw [hmn] at htop
        simp only [uBack, applyActs_cons]
        set ts1 := applyAct blank ts (Act.S2 blank .stay) with hts1
        set ts2 := applyAct blank ts1 (Act.U (sc := sc) .left) with hts2
        set ts3 := applyAct blank ts2 (Act.X2 (sc := sc) .right) with hts3
        set ts4 := applyAct blank ts3 (Act.S2 blank .left) with hts4
        have hts1S2 : ts1.S2 = Tape.step blank ts.S2 blank .stay := by rw [hts1]; rfl
        have herase : Tape.StackView blank ts1.S2 (List.replicate n mark) := by
          rw [hts1S2]; exact Tape.pop_erase htop
        have hts4S2 : ts4.S2 = Tape.step blank ts1.S2 blank .left := by
          rw [hts4, hts3, hts2]; rfl
        cases n with
        | zero =>
            simp only [List.replicate] at herase
            have : Tape.StackView blank ts4.S2 [] := by
              rw [hts4S2]; exact Tape.pop_empty herase
            exact ih ts4 (Or.inl ⟨rfl, this⟩)
        | succ n =>
            rw [List.replicate_succ] at herase
            have : Tape.StackTopView blank ts4.S2 mark (List.replicate n mark) := by
              rw [hts4S2]; exact Tape.pop_spec herase
            exact ih ts4 (Or.inr ⟨n, rfl, this⟩)

/-- **作業テープの不変性（`uCheck`）**：`uCheck` の前後で `S2` は空のまま
（`ScratchBlank` の `S2` 成分だけを取り出した形）。 -/
theorem uCheck_S2 (c : ℕ) (ts : OvTapes sc) (h : Tape.StackView blank ts.S2 []) :
    Tape.StackView blank (applyActs blank (uCheck sc blank mark c) ts).S2 [] := by
  unfold uCheck
  rw [applyActs_append]
  obtain ⟨h0, hs⟩ := uFwd_S2 blank mark c ts h
  cases c with
  | zero => exact uBack_S2 blank mark 0 _ (Or.inl ⟨rfl, h0 rfl⟩)
  | succ c => exact uBack_S2 blank mark (c + 1) _ (Or.inr ⟨c, rfl, hs c rfl⟩)

theorem noScratch2_uFwdStep (n : ℕ) : NoScratchAll2 (uFwdStep sc mark n) := by
  induction n with
  | zero => exact noScratchAll2_nil
  | succ n ih =>
      exact noScratchAll2_cons trivial (noScratchAll2_cons trivial
        (noScratchAll2_cons trivial ih))

theorem noScratch2_uFwd (n : ℕ) : NoScratchAll2 (uFwd sc blank mark n) :=
  noScratchAll2_append (noScratch2_uFwdStep mark n)
    (noScratchAll2_cons trivial noScratchAll2_nil)

theorem noScratch2_uBack (n : ℕ) : NoScratchAll2 (uBack sc blank n) := by
  induction n with
  | zero => exact noScratchAll2_nil
  | succ n ih =>
      exact noScratchAll2_cons trivial (noScratchAll2_cons trivial
        (noScratchAll2_cons trivial (noScratchAll2_cons trivial ih)))

theorem noScratch2_uCheck (c : ℕ) : NoScratchAll2 (uCheck sc blank mark c) :=
  noScratchAll2_append (noScratch2_uFwd blank mark c) (noScratch2_uBack blank c)

end Proj

/-- **作業テープの不変性（段の一歩）**：`ovProgram` は `ScratchBlank` を保つ。
フロンティア枝は `uCheck` を経由するので `S2` が一時的に触れられるが
（`uCheck_S2`）、他の 2 枝は従来どおり作業テープに一切触れない。 -/
theorem ovProgram_scratchBlank (blank leftSym endSym mark one : Fin sc) (k c : ℕ)
    (b bu : Bool) (ts : OvTapes sc) (hSB : ScratchBlank blank ts) :
    ScratchBlank blank
      (applyActs blank (ovProgram blank leftSym endSym mark one k c b bu ts) ts) := by
  unfold ovProgram
  by_cases h1 : Tape.read ts.X = leftSym
  · rw [if_pos h1, applyActs_append, applyActs_append]
    have hUC : ScratchBlank blank (applyActs blank (uCheck sc blank mark c) ts) := by
      have heq2 := applyActs_scratchEq2 (blank := blank) (uCheck sc blank mark c) ts
        (noScratch2_uCheck blank mark c)
      obtain ⟨o1, o3, o4, o5, o6, o7, o8, o9⟩ := heq2.blankOthers hSB
      exact ⟨o1, uCheck_S2 blank mark c ts hSB.s2, o3, o4, o5, o6, o7, o8, o9⟩
    have hFset : NoScratchAll (if bu then [Act.Fset one] else []) := by
      cases bu
      · exact noScratchAll_nil
      · exact noScratchAll_cons trivial noScratchAll_nil
    have hMid := applyActs_scratchBlank hFset hUC
    exact applyActs_scratchBlank (noScratch_shiftActs _ _ _ _ _) hMid
  · rw [if_neg h1]
    by_cases h2 : Tape.read ts.P ≠ endSym ∧ Tape.read ts.P = Tape.read ts.X
    · rw [if_pos h2]
      exact applyActs_scratchBlank
        (noScratchAll_cons trivial (noScratchAll_cons trivial noScratchAll_nil)) hSB
    · rw [if_neg h2]
      exact applyActs_scratchBlank (noScratch_shiftActs _ _ _ _ _) hSB

/-! ### 合成された動作列の効果 -/

/-- 左端 `startSym` を踏んで 1 歩戻る（リセットずらしの末尾）。 -/
def bounce (blank : Fin sc) (tp : TapeConfiguration sc) : TapeConfiguration sc :=
  Tape.step blank (Tape.step blank tp tp.focus .left)
    (Tape.step blank tp tp.focus .left).focus .right

theorem seq_bounce {blank : Fin sc} {w : List (Fin sc)} {tp : TapeConfiguration sc}
    (h : Tape.SeqView blank tp w 1) (hlt : 1 < w.length) :
    Tape.SeqView blank (bounce blank tp) w 1 :=
  Tape.seq_move_right (Tape.seq_move_left h) hlt

section Composite

variable (blank mark : Fin sc) (k n q : ℕ) (ts : OvTapes sc)

theorem periodActs_P :
    (applyActs blank (periodActs blank mark n) ts).P = GSTapes.leftN blank ts.P n := by
  simp [periodActs, applyActs_append, applyAct, perLoop_P, replC_P, posMoves_P]

theorem periodActs_X :
    (applyActs blank (periodActs blank mark n) ts).X = ts.X := by
  simp [periodActs, applyActs_append, applyAct, perLoop_X, replC_X, posMoves_X]

theorem periodActs_U :
    (applyActs blank (periodActs blank mark n) ts).U = ts.U := by
  simp [periodActs, applyActs_append, applyAct, perLoop_U, replC_U, posMoves_U]

theorem periodActs_Cnt :
    (applyActs blank (periodActs blank mark n) ts).Cnt =
      GSTapes.incN blank (Tape.step blank
        (Tape.step blank (GSTapes.decN blank ts.Cnt n) blank .left) mark .right) n := by
  simp [periodActs, applyActs_append, applyAct, perLoop_Cnt, replC_Cnt, posMoves_Cnt]

theorem periodActs_X2 :
    (applyActs blank (periodActs blank mark n) ts).X2 = GSTapes.leftN blank ts.X2 n := by
  simp [periodActs, applyActs_append, applyAct, perLoop_X2, replC_X2, posMoves_X2]

theorem periodActs_F :
    (applyActs blank (periodActs blank mark n) ts).F = GSTapes.leftN blank ts.F n := by
  simp [periodActs, applyActs_append, applyAct, perLoop_F, replC_F, posMoves_F]

theorem resetShift_P :
    (applyActs blank (resetShift sc k q) ts).P = bounce blank (GSTapes.leftN blank ts.P q) := by
  unfold resetShift
  by_cases h0 : q = 0
  · subst h0
    simp [applyActs_append, applyAct, resetWalk_P, posMoves_P, bounce]
  · rw [if_neg h0]
    simp [applyActs_append, applyAct, resetWalk_P, posMoves_P, bounce]

theorem resetShift_Cnt :
    (applyActs blank (resetShift sc k q) ts).Cnt = ts.Cnt := by
  unfold resetShift
  by_cases h0 : q = 0
  · subst h0; simp [applyActs_append, applyAct, resetWalk_Cnt, posMoves_Cnt]
  · rw [if_neg h0]; simp [applyActs_append, applyAct, resetWalk_Cnt, posMoves_Cnt]

theorem resetShift_U :
    (applyActs blank (resetShift sc k q) ts).U = ts.U := by
  unfold resetShift
  by_cases h0 : q = 0
  · subst h0; simp [applyActs_append, applyAct, resetWalk_U, posMoves_U]
  · rw [if_neg h0]; simp [applyActs_append, applyAct, resetWalk_U, posMoves_U]

theorem resetShift_X2 :
    (applyActs blank (resetShift sc k q) ts).X2
      = GSTapes.leftN blank ts.X2 (max 1 (ceilDiv q k)) := by
  unfold resetShift
  by_cases h0 : q = 0
  · subst h0; simp [applyActs_append, applyAct, resetWalk_X2, posMoves_X2]
  · rw [if_neg h0]; simp [applyActs_append, applyAct, resetWalk_X2, posMoves_X2]

theorem resetShift_F :
    (applyActs blank (resetShift sc k q) ts).F
      = GSTapes.leftN blank ts.F (max 1 (ceilDiv q k)) := by
  unfold resetShift
  by_cases h0 : q = 0
  · subst h0; simp [applyActs_append, applyAct, resetWalk_F, posMoves_F]
  · rw [if_neg h0]; simp [applyActs_append, applyAct, resetWalk_F, posMoves_F]

theorem resetShift_X_pos (h0 : q ≠ 0) :
    (applyActs blank (resetShift sc k q) ts).X
      = rightN blank ts.X (GSTapes.moves k q 0) := by
  unfold resetShift
  rw [if_neg h0]
  simp [applyActs_append, applyAct, resetWalk_X, posMoves_X]

theorem resetShift_X_zero :
    (applyActs blank (resetShift sc k 0) ts).X = Tape.step blank ts.X ts.X.focus .left := by
  unfold resetShift
  simp [applyActs_append, applyAct, resetWalk_X, posMoves_X, GSTapes.moves, rightN]

theorem uCheck_U :
    (applyActs blank (uCheck sc blank mark n) ts).U
      = GSTapes.leftN blank (rightN blank ts.U n) n := by
  simp [uCheck, applyActs_append, uFwd_U, uBack_U]

theorem uCheck_X2 :
    (applyActs blank (uCheck sc blank mark n) ts).X2
      = rightN blank (GSTapes.leftN blank ts.X2 n) n := by
  simp [uCheck, applyActs_append, uFwd_X2, uBack_X2]

theorem uCheck_P : (applyActs blank (uCheck sc blank mark n) ts).P = ts.P := by
  simp [uCheck, applyActs_append, uFwd_P, uBack_P]

theorem uCheck_X : (applyActs blank (uCheck sc blank mark n) ts).X = ts.X := by
  simp [uCheck, applyActs_append, uFwd_X, uBack_X]

theorem uCheck_Cnt : (applyActs blank (uCheck sc blank mark n) ts).Cnt = ts.Cnt := by
  simp [uCheck, applyActs_append, uFwd_Cnt, uBack_Cnt]

theorem uCheck_F : (applyActs blank (uCheck sc blank mark n) ts).F = ts.F := by
  simp [uCheck, applyActs_append, uFwd_F, uBack_F]

end Composite


/-! ## 5. 符号化 -/

/-- テキスト `T = (x.take L).reverse` の添字 `i` は `X` の語 `leftSym :: x` の添字 `L - i`。 -/
theorem revTake_getElem? {xw : List (Fin sc)} (leftSym : Fin sc) {L i : ℕ}
    (hL : L ≤ xw.length) (hi : i < L) :
    ((xw.take L).reverse)[i]? = (leftSym :: xw)[L - i]? := by
  have hlen : (xw.take L).length = L := by simp only [List.length_take]; omega
  have h1 : ((xw.take L).reverse)[i]? = (xw.take L)[(xw.take L).length - 1 - i]? :=
    List.getElem?_reverse (by omega)
  rw [h1, hlen, show (L : ℕ) - 1 - i = L - i - 1 from by omega,
    List.getElem?_take_of_lt (show L - i - 1 < L from by omega),
    show (L : ℕ) - i = (L - i - 1) + 1 from by omega, List.getElem?_cons_succ]
  exact getElem?_congr (by omega)

theorem revTake_length {xw : List (Fin sc)} {L : ℕ} (hL : L ≤ xw.length) :
    ((xw.take L).reverse).length = L := by
  simp only [List.length_reverse, List.length_take]
  exact Nat.min_eq_left hL

/-- テープ状態が段の走査状態 `st` とフラグ語 `fw` を符号化していること。 -/
structure OvEncodes (blank leftSym startSym endSym mark : Fin sc)
    (u v xw fw : List (Fin sc)) (L p₁ : ℕ) (ts : OvTapes sc) (st : ScanState) : Prop where
  pat : Tape.SeqView blank ts.P (startSym :: (v ++ [endSym])) (st.q + 1)
  txt : Tape.SeqView blank ts.X (leftSym :: xw) (L - (st.pos + u.length + st.q))
  cnt : Tape.CounterView' blank mark ts.Cnt p₁
  upat : Tape.SeqView blank ts.U (startSym :: (u ++ [endSym])) 1
  txt2 : Tape.SeqView blank ts.X2 (leftSym :: xw) (L - st.pos)
  flg : Tape.SeqView blank ts.F fw (L - st.pos)

section Reads

variable {blank leftSym startSym endSym mark : Fin sc} {u v xw fw : List (Fin sc)}
  {L p₁ : ℕ} {ts : OvTapes sc} {st : ScanState}

theorem read_X_lt (hE : OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁ ts st)
    (hL : L ≤ xw.length) (hi : st.pos + u.length + st.q < L) :
    ((xw.take L).reverse)[st.pos + u.length + st.q]? = some (Tape.read ts.X) := by
  rw [revTake_getElem? leftSym hL hi]
  exact hE.txt.read_eq

theorem read_X_frontier
    (hE : OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁ ts st)
    (hi : st.pos + u.length + st.q = L) : Tape.read ts.X = leftSym := by
  have h := hE.txt.read_eq
  rw [hi, Nat.sub_self] at h
  simp only [List.getElem?_cons_zero, Option.some.injEq] at h
  exact h.symm

theorem read_X_ne_left (hleft : leftSym ∉ xw)
    (hE : OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁ ts st)
    (_hL : L ≤ xw.length) (hi : st.pos + u.length + st.q < L) :
    Tape.read ts.X ≠ leftSym := by
  intro hcon
  have h := hE.txt.read_eq
  rw [show L - (st.pos + u.length + st.q) = (L - (st.pos + u.length + st.q) - 1) + 1 from
    by omega, List.getElem?_cons_succ] at h
  obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 h
  exact hleft (hcon ▸ h2 ▸ List.getElem_mem h1)

/-- フロンティア判定はテープ読み取りで決まる。 -/
theorem frontier_iff (hleft : leftSym ∉ xw)
    (hE : OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁ ts st)
    (hL : L ≤ xw.length) (hfront : st.pos + u.length + st.q ≤ L) :
    Tape.read ts.X = leftSym ↔ st.pos + u.length + st.q = L := by
  constructor
  · intro h
    by_contra hne
    exact read_X_ne_left hleft hE hL (by omega) h
  · intro h; exact read_X_frontier hE h

theorem read_P_lt (hE : OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁ ts st)
    (hq : st.q < v.length) : v[st.q]? = some (Tape.read ts.P) := by
  have h := hE.pat.read_eq
  rw [List.getElem?_cons_succ, List.getElem?_append_left hq] at h
  exact h

theorem read_P_end (hE : OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁ ts st)
    (hq : st.q = v.length) : Tape.read ts.P = endSym := by
  have h := hE.pat.read_eq
  rw [List.getElem?_cons_succ, hq, List.getElem?_append_right (Nat.le_refl v.length)] at h
  simp at h
  exact h.symm

theorem read_P_ne_end (hend : endSym ∉ v)
    (hE : OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁ ts st)
    (hq : st.q < v.length) : Tape.read ts.P ≠ endSym := by
  intro hcon
  obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 (read_P_lt hE hq)
  exact hend (hcon ▸ h2 ▸ List.getElem_mem h1)

theorem qOf_eq (hE : OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁ ts st) :
    qOf ts = st.q := by
  have h := hE.pat.left_eq
  have hlt := hE.pat.lt
  simp only [List.length_cons, List.length_append] at hlt
  unfold qOf
  rw [h, List.length_reverse, List.length_take]
  simp only [List.length_cons, List.length_append]
  omega

theorem p1Of_eq (hE : OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁ ts st) :
    p1Of ts = p₁ := by
  have h : ts.Cnt.left = List.replicate p₁ blank ++ [mark] :=
    Tape.StackView.left_eq hE.cnt
  unfold p1Of
  rw [h]
  simp

/-- 一致枝の判定もテープ読み取りで決まる（フロンティアでないとき）。 -/
theorem advance_iff (hend : endSym ∉ v)
    (hE : OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁ ts st)
    (hL : L ≤ xw.length) (hi : st.pos + u.length + st.q < L) :
    (Tape.read ts.P ≠ endSym ∧ Tape.read ts.P = Tape.read ts.X) ↔
      ((xw.take L).reverse)[st.pos + u.length + st.q]? = v[st.q]? := by
  have hT := read_X_lt hE hL hi
  have hqle : st.q ≤ v.length := by
    have h := hE.pat.lt
    simp at h
    omega
  constructor
  · rintro ⟨h1, h2⟩
    have hqv : st.q < v.length := by
      rcases Nat.lt_or_ge st.q v.length with h | h
      · exact h
      · exact absurd (read_P_end hE (by omega)) h1
    rw [hT, read_P_lt hE hqv, h2]
  · intro h
    rw [hT] at h
    have hqv : st.q < v.length := by
      rcases Nat.lt_or_ge st.q v.length with h' | h'
      · exact h'
      · rw [show st.q = v.length from by omega, List.getElem?_eq_none (Nat.le_refl _)] at h
        exact absurd h (Option.some_ne_none _)
    refine ⟨read_P_ne_end hend hE hqv, ?_⟩
    rw [read_P_lt hE hqv] at h
    exact (Option.some.inj h).symm

end Reads


/-! ## 6. 一歩の実現 -/

/-- ずらし枝の実現：`P` は `gsShift` だけ左へ（周期ずらし）または左端まで戻り（リセット）、
`X` はテキスト位置の変化に合わせて動き、`X2`/`F` は `gsShift` だけ左へ動く。 -/
theorem shiftActs_encodes
    {blank leftSym startSym endSym mark : Fin sc} {u v xw fw : List (Fin sc)}
    {L p₁ k r : ℕ} {b : Bool} {ts : OvTapes sc} {pos q : ℕ}
    (hk : 0 < k) (hL : L ≤ xw.length)
    (hb : b = decide (k * p₁ ≤ q ∧ q ≤ r))
    (hE : OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁ ts ⟨pos, q⟩)
    (hfront : pos + u.length + q ≤ L)
    (hfit : pos + gsShift k p₁ r q + u.length + gsNextQ k p₁ r q ≤ L) :
    OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁
      (applyActs blank (shiftActs blank mark k b ts) ts)
      ⟨pos + gsShift k p₁ r q, gsNextQ k p₁ r q⟩ := by
  have hqOf : qOf ts = q := qOf_eq hE
  have hp1Of : p1Of ts = p₁ := p1Of_eq hE
  have hvlen : (startSym :: (v ++ [endSym])).length = v.length + 2 := by simp
  have hxlen : (leftSym :: xw).length = xw.length + 1 := by simp
  have hpat : Tape.SeqView blank ts.P (startSym :: (v ++ [endSym])) (q + 1) := hE.pat
  have htxt : Tape.SeqView blank ts.X (leftSym :: xw) (L - (pos + u.length + q)) := hE.txt
  have htxt2 : Tape.SeqView blank ts.X2 (leftSym :: xw) (L - pos) := hE.txt2
  have hflg : Tape.SeqView blank ts.F fw (L - pos) := hE.flg
  rcases Bool.eq_false_or_eq_true b with hbb | hbb
  · -- 周期ずらし
    subst hbb
    have hcond : k * p₁ ≤ q ∧ q ≤ r := of_decide_eq_true hb.symm
    have hle : p₁ ≤ q := le_trans (Nat.le_mul_of_pos_left p₁ hk) hcond.1
    have hgs : gsShift k p₁ r q = p₁ := by unfold gsShift; rw [if_pos hcond]
    have hgq : gsNextQ k p₁ r q = q - p₁ := by unfold gsNextQ; rw [if_pos hcond]
    have hprog : shiftActs blank mark k true ts = periodActs blank mark p₁ := by
      unfold shiftActs; rw [if_pos rfl, hp1Of]
    rw [hgs, hgq] at hfit
    rw [hprog, hgs, hgq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [periodActs_P]
      show Tape.SeqView blank _ (startSym :: (v ++ [endSym])) (q - p₁ + 1)
      refine GSTapes.seq_leftN p₁ ts.P (q - p₁ + 1) ?_
      rw [show q - p₁ + 1 + p₁ = q + 1 from by omega]
      exact hpat
    · rw [periodActs_X]
      show Tape.SeqView blank ts.X (leftSym :: xw) (L - (pos + p₁ + u.length + (q - p₁)))
      rw [show pos + p₁ + u.length + (q - p₁) = pos + u.length + q from by omega]
      exact htxt
    · rw [periodActs_Cnt]
      have c0 : Tape.CounterView' blank mark (GSTapes.decN blank ts.Cnt p₁) 0 :=
        GSTapes.counter'_decN p₁ ts.Cnt 0 (by simpa using hE.cnt)
      have c2 := GSTapes.counter'_incN p₁ _ 0 (Tape.counter'_dec_zero c0)
      simpa using c2
    · rw [periodActs_U]; exact hE.upat
    · rw [periodActs_X2]
      show Tape.SeqView blank _ (leftSym :: xw) (L - (pos + p₁))
      refine GSTapes.seq_leftN p₁ ts.X2 (L - (pos + p₁)) ?_
      rw [show L - (pos + p₁) + p₁ = L - pos from by omega]
      exact htxt2
    · rw [periodActs_F]
      show Tape.SeqView blank _ fw (L - (pos + p₁))
      refine GSTapes.seq_leftN p₁ ts.F (L - (pos + p₁)) ?_
      rw [show L - (pos + p₁) + p₁ = L - pos from by omega]
      exact hflg
  · -- リセットずらし
    subst hbb
    have hcond : ¬ (k * p₁ ≤ q ∧ q ≤ r) := of_decide_eq_false hb.symm
    have hgs : gsShift k p₁ r q = max 1 (ceilDiv q k) := by unfold gsShift; rw [if_neg hcond]
    have hgq : gsNextQ k p₁ r q = 0 := by unfold gsNextQ; rw [if_neg hcond]
    have hprog : shiftActs blank mark k false ts = resetShift sc k q := by
      unfold shiftActs; rw [if_neg (by simp), hqOf]
    rw [hgs, hgq] at hfit
    rw [hprog, hgs, hgq]
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · have hc0 : ceilDiv 0 k = 0 := by unfold ceilDiv; exact Nat.div_eq_of_lt (by omega)
      have hmax : max 1 (ceilDiv 0 k) = 1 := by rw [hc0]; simp
      rw [hmax] at hfit ⊢
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [resetShift_P]
        exact seq_bounce (w := startSym :: (v ++ [endSym])) hpat (by rw [hvlen]; omega)
      · rw [resetShift_X_zero]
        show Tape.SeqView blank _ (leftSym :: xw) (L - (pos + 1 + u.length + 0))
        refine Tape.seq_move_left (i := L - (pos + 1 + u.length + 0)) ?_
        rw [show L - (pos + 1 + u.length + 0) + 1 = L - (pos + u.length + 0) from by omega]
        exact htxt
      · rw [resetShift_Cnt]; exact hE.cnt
      · rw [resetShift_U]; exact hE.upat
      · rw [resetShift_X2, hmax]
        show Tape.SeqView blank _ (leftSym :: xw) (L - (pos + 1))
        refine GSTapes.seq_leftN 1 ts.X2 (L - (pos + 1)) ?_
        rw [show L - (pos + 1) + 1 = L - pos from by omega]
        exact htxt2
      · rw [resetShift_F, hmax]
        show Tape.SeqView blank _ fw (L - (pos + 1))
        refine GSTapes.seq_leftN 1 ts.F (L - (pos + 1)) ?_
        rw [show L - (pos + 1) + 1 = L - pos from by omega]
        exact hflg
    · have hc1 : 1 ≤ ceilDiv q k := GSTapes.ceilDiv_pos hk hq0
      have hc2 : ceilDiv q k ≤ q := GSTapes.ceilDiv_le_self hk
      have hmax : max 1 (ceilDiv q k) = ceilDiv q k := by omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [resetShift_P]
        refine seq_bounce (w := startSym :: (v ++ [endSym])) ?_ (by rw [hvlen]; omega)
        refine GSTapes.seq_leftN q ts.P 1 ?_
        rw [show 1 + q = q + 1 from by omega]
        exact hpat
      · rw [resetShift_X_pos _ _ _ _ (by omega), GSTapes.moves_zero k hk]
        show Tape.SeqView blank _ (leftSym :: xw) (L - (pos + max 1 (ceilDiv q k) + u.length + 0))
        rw [hmax]
        have := seq_rightN (blank := blank) (w := leftSym :: xw) (q - ceilDiv q k) ts.X
          (L - (pos + u.length + q)) htxt (by rw [hxlen]; omega)
        rw [show L - (pos + u.length + q) + (q - ceilDiv q k)
          = L - (pos + ceilDiv q k + u.length + 0) from by omega] at this
        exact this
      · rw [resetShift_Cnt]; exact hE.cnt
      · rw [resetShift_U]; exact hE.upat
      · rw [resetShift_X2]
        show Tape.SeqView blank _ (leftSym :: xw) (L - (pos + max 1 (ceilDiv q k)))
        refine GSTapes.seq_leftN (max 1 (ceilDiv q k)) ts.X2 (L - (pos + max 1 (ceilDiv q k))) ?_
        rw [show L - (pos + max 1 (ceilDiv q k)) + max 1 (ceilDiv q k) = L - pos from by omega]
        exact htxt2
      · rw [resetShift_F]
        show Tape.SeqView blank _ fw (L - (pos + max 1 (ceilDiv q k)))
        refine GSTapes.seq_leftN (max 1 (ceilDiv q k)) ts.F (L - (pos + max 1 (ceilDiv q k))) ?_
        rw [show L - (pos + max 1 (ceilDiv q k)) + max 1 (ceilDiv q k) = L - pos from by omega]
        exact hflg


/-- `shiftActs` は `P` と `Cnt` の内容にしか依らない。 -/
theorem shiftActs_congr (blank mark : Fin sc) (k : ℕ) (b : Bool) (ts ts' : OvTapes sc)
    (hP : ts'.P = ts.P) (hC : ts'.Cnt = ts.Cnt) :
    shiftActs blank mark k b ts' = shiftActs blank mark k b ts := by
  unfold shiftActs qOf p1Of; rw [hP, hC]

/-- フロンティアでの `u` の直接照合が読む記号：`uFwd` を `j` 歩進めた時点で
`U` は `u[j]`、`X2` はテキストの `T[pos + j]` を読む。オラクルビット `bu` が
`MatchLen u T pos |u|` を表しうる根拠。 -/
theorem uCheck_reads {blank leftSym startSym endSym mark : Fin sc} {u xw : List (Fin sc)}
    {L pos : ℕ} {ts : OvTapes sc}
    (hU : Tape.SeqView blank ts.U (startSym :: (u ++ [endSym])) 1)
    (hX2 : Tape.SeqView blank ts.X2 (leftSym :: xw) (L - pos))
    (hL : L ≤ xw.length) {j : ℕ} (hj : j < u.length) (hjL : pos + j < L)
    (hpu : pos + u.length ≤ L) :
    u[j]? = some (Tape.read (applyActs blank (uFwd sc blank mark j) ts).U) ∧
      ((xw.take L).reverse)[pos + j]?
        = some (Tape.read (applyActs blank (uFwd sc blank mark j) ts).X2) := by
  constructor
  · rw [uFwd_U]
    have h := (seq_rightN j ts.U 1 hU (by simp; omega)).read_eq
    rw [show 1 + j = j + 1 from by omega, List.getElem?_cons_succ,
      List.getElem?_append_left hj] at h
    exact h
  · rw [uFwd_X2, revTake_getElem? leftSym hL hjL]
    have h := (GSTapes.seq_leftN j ts.X2 (L - pos - j)
      (by rw [show L - pos - j + j = L - pos from by omega]; exact hX2)).read_eq
    rw [show L - (pos + j) = L - pos - j from by omega]
    exact h

/-- フラグ語の一歩の変化：報告のとき添字 `|T| - pos` に `one` を書く。 -/
def stepFlags (u T : List (Fin sc)) (one : Fin sc) (st : ScanState) (fw : List (Fin sc)) :
    List (Fin sc) :=
  if st.pos + u.length + st.q = T.length ∧ MatchLen u T st.pos u.length then
    fw.set (T.length - st.pos) one
  else fw

/-- **主定理 1（実現）**：`ovProgram` の動作列を適用すると、テープは `ovStep` 後の
走査状態と、更新されたフラグ語を符号化する。 -/
theorem ovEncodes_step
    {blank leftSym startSym endSym mark one : Fin sc}
    {u v xw fw T : List (Fin sc)} {L p₁ k r c : ℕ} {b bu : Bool}
    {ts : OvTapes sc} {st : ScanState}
    (hk : 0 < k) (hL : L ≤ xw.length) (hleft : leftSym ∉ xw) (hend : endSym ∉ v)
    (hT : T = (xw.take L).reverse) (hc : c = u.length)
    (hb : b = decide (k * p₁ ≤ st.q ∧ st.q ≤ r))
    (hbu : bu = decide (MatchLen u T st.pos u.length))
    (hE : OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁ ts st)
    (hfront : st.pos + u.length + st.q ≤ L)
    (hfit : (ovStep u v T k p₁ r st).pos + u.length + (ovStep u v T k p₁ r st).q ≤ L) :
    OvEncodes blank leftSym startSym endSym mark u v xw
      (stepFlags u T one st fw) L p₁
      (applyActs blank (ovProgram blank leftSym endSym mark one k c b bu ts) ts)
      (ovStep u v T k p₁ r st) := by
  subst hT
  have hTlen : ((xw.take L).reverse).length = L := revTake_length hL
  have hxlen : (leftSym :: xw).length = xw.length + 1 := by simp
  have hvlen : (startSym :: (v ++ [endSym])).length = v.length + 2 := by simp
  by_cases hfr : st.pos + u.length + st.q = ((xw.take L).reverse).length
  · -- フロンティア
    have hfrL : st.pos + u.length + st.q = L := by omega
    have hread : Tape.read ts.X = leftSym := read_X_frontier hE hfrL
    have hstep : ovStep u v ((xw.take L).reverse) k p₁ r st
        = ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ := by
      unfold ovStep; rw [if_pos hfr]
    have hprog : ovProgram blank leftSym endSym mark one k c b bu ts
        = uCheck sc blank mark c ++ (if bu then [Act.Fset one] else [])
          ++ shiftActs blank mark k b ts := by
      unfold ovProgram; rw [if_pos hread]
    have hpu : st.pos + u.length ≤ L := by omega
    -- `uCheck` のあと
    have hU1 : Tape.SeqView blank (applyActs blank (uCheck sc blank mark c) ts).U
        (startSym :: (u ++ [endSym])) 1 := by
      rw [uCheck_U]
      exact GSTapes.seq_leftN c _ 1 (seq_rightN c ts.U 1 hE.upat (by simp; omega))
    have hX21 : Tape.SeqView blank (applyActs blank (uCheck sc blank mark c) ts).X2
        (leftSym :: xw) (L - st.pos) := by
      rw [uCheck_X2]
      have h1 : Tape.SeqView blank (GSTapes.leftN blank ts.X2 c) (leftSym :: xw)
          (L - st.pos - c) :=
        GSTapes.seq_leftN c ts.X2 (L - st.pos - c)
          (by rw [show L - st.pos - c + c = L - st.pos from by omega]; exact hE.txt2)
      have h2 := seq_rightN c _ (L - st.pos - c) h1 (by rw [hxlen]; omega)
      rw [show L - st.pos - c + c = L - st.pos from by omega] at h2
      exact h2
    have hE1 : OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁
        (applyActs blank (uCheck sc blank mark c) ts) st :=
      ⟨by rw [uCheck_P]; exact hE.pat, by rw [uCheck_X]; exact hE.txt,
        by rw [uCheck_Cnt]; exact hE.cnt, hU1, hX21, by rw [uCheck_F]; exact hE.flg⟩
    -- フラグ書き込みのあと
    have hE2 : OvEncodes blank leftSym startSym endSym mark u v xw
        (if bu then fw.set (L - st.pos) one else fw) L p₁
        (applyActs blank (if bu then [Act.Fset one] else [])
          (applyActs blank (uCheck sc blank mark c) ts)) st := by
      by_cases hbv : bu = true
      · rw [if_pos hbv, if_pos hbv]
        simp only [applyActs_cons, applyActs_nil, applyAct]
        exact ⟨hE1.pat, hE1.txt, hE1.cnt, hE1.upat, hE1.txt2,
          Tape.seq_write hE1.flg one⟩
      · rw [if_neg hbv, if_neg hbv]
        exact hE1
    have hPeq : (applyActs blank (if bu then [Act.Fset one] else [])
        (applyActs blank (uCheck sc blank mark c) ts)).P = ts.P := by
      by_cases hbv : bu = true
      · rw [if_pos hbv]
        simp only [applyActs_cons, applyActs_nil, applyAct, uCheck_P]
      · rw [if_neg hbv]
        simp only [applyActs_nil, uCheck_P]
    have hCeq : (applyActs blank (if bu then [Act.Fset one] else [])
        (applyActs blank (uCheck sc blank mark c) ts)).Cnt = ts.Cnt := by
      by_cases hbv : bu = true
      · rw [if_pos hbv]
        simp only [applyActs_cons, applyActs_nil, applyAct, uCheck_Cnt]
      · rw [if_neg hbv]
        simp only [applyActs_nil, uCheck_Cnt]
    have hflags : stepFlags u ((xw.take L).reverse) one st fw
        = (if bu then fw.set (L - st.pos) one else fw) := by
      unfold stepFlags
      by_cases hm : MatchLen u ((xw.take L).reverse) st.pos u.length
      · rw [if_pos ⟨hfr, hm⟩, if_pos (show bu = true by rw [hbu]; exact decide_eq_true hm),
          hTlen]
      · rw [if_neg (by tauto),
          if_neg (show ¬ (bu = true) by rw [hbu]; simp [hm])]
    rw [hprog, hstep, hflags, applyActs_append, applyActs_append,
      ← shiftActs_congr blank mark k b ts _ hPeq hCeq]
    exact shiftActs_encodes (pos := st.pos) (q := st.q) hk hL hb hE2 hfront
      (by rw [hstep] at hfit; exact hfit)
  · -- フロンティアでない
    have hlt : st.pos + u.length + st.q < L := by omega
    have hne : Tape.read ts.X ≠ leftSym := read_X_ne_left hleft hE hL hlt
    have hflags : stepFlags u ((xw.take L).reverse) one st fw = fw := by
      unfold stepFlags; rw [if_neg (by tauto)]
    by_cases hadv : Tape.read ts.P ≠ endSym ∧ Tape.read ts.P = Tape.read ts.X
    · -- 一致
      have hmatch : ((xw.take L).reverse)[st.pos + u.length + st.q]? = v[st.q]? :=
        (advance_iff hend hE hL hlt).1 hadv
      have hqv : st.q < v.length := by
        have h1 := read_X_lt hE hL hlt
        rw [h1] at hmatch
        exact (List.getElem?_eq_some_iff.1 hmatch.symm).1
      have hstep : ovStep u v ((xw.take L).reverse) k p₁ r st = ⟨st.pos, st.q + 1⟩ := by
        unfold ovStep; rw [if_neg hfr, if_pos hmatch]
      have hprog : ovProgram blank leftSym endSym mark one k c b bu ts
          = [Act.P .right, Act.X .left] := by
        unfold ovProgram; rw [if_neg hne, if_pos hadv]
      rw [hprog, hstep, hflags]
      simp only [applyActs_cons, applyActs_nil, applyAct]
      refine ⟨?_, ?_, hE.cnt, hE.upat, hE.txt2, hE.flg⟩
      · show Tape.SeqView blank (Tape.step blank ts.P ts.P.focus .right) _ (st.q + 1 + 1)
        exact Tape.seq_move_right hE.pat (by rw [hvlen]; omega)
      · show Tape.SeqView blank (Tape.step blank ts.X ts.X.focus .left)
          (leftSym :: xw) (L - (st.pos + u.length + (st.q + 1)))
        refine Tape.seq_move_left (i := L - (st.pos + u.length + (st.q + 1))) ?_
        rw [show L - (st.pos + u.length + (st.q + 1)) + 1 = L - (st.pos + u.length + st.q) from
          by omega]
        exact hE.txt
    · -- 不一致：ずらし
      have hnm : ¬ (((xw.take L).reverse)[st.pos + u.length + st.q]? = v[st.q]?) :=
        fun hcon => hadv ((advance_iff hend hE hL hlt).2 hcon)
      have hstep : ovStep u v ((xw.take L).reverse) k p₁ r st
          = ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ := by
        unfold ovStep; rw [if_neg hfr, if_neg hnm]
      have hprog : ovProgram blank leftSym endSym mark one k c b bu ts
          = shiftActs blank mark k b ts := by
        unfold ovProgram; rw [if_neg hne, if_neg hadv]
      rw [hprog, hstep, hflags]
      exact shiftActs_encodes (pos := st.pos) (q := st.q) hk hL hb hE hfront
        (by rw [hstep] at hfit; exact hfit)


/-! ## 7. コスト（償却） -/

/-- ずらし枝の動作数。`GSScanTapes.shiftCost` に `X2`/`F` の左移動 `2·gsShift` が加わる。 -/
def ovShiftCost (k p₁ r q : ℕ) : ℕ := GSTapes.shiftCost k p₁ r q + 2 * gsShift k p₁ r q

/-- フロンティア枝の動作数（`u` の往復照合 `uCheck`＝`7|u|+1`（`S2` のマーカ往復込み）
＋ フラグ書き込み ＋ ずらし）。 -/
def ovFrontierCost (u T : List (Fin sc)) (k p₁ r : ℕ) (st : ScanState) : ℕ :=
  (7 * u.length + 1) + (if MatchLen u T st.pos u.length then 1 else 0)
    + ovShiftCost k p₁ r st.q

/-- 一歩の動作数（`ovProgram` の長さ）。 -/
def ovStepCost (u v T : List (Fin sc)) (k p₁ r : ℕ) (st : ScanState) : ℕ :=
  if st.pos + u.length + st.q = T.length then ovFrontierCost u T k p₁ r st
  else if T[st.pos + u.length + st.q]? = v[st.q]? then 2
  else ovShiftCost k p₁ r st.q

theorem shiftActs_length {blank leftSym startSym endSym mark : Fin sc}
    {u v xw fw : List (Fin sc)} {L p₁ k r : ℕ} {b : Bool} {ts : OvTapes sc} {st : ScanState}
    (hk : 0 < k) (hb : b = decide (k * p₁ ≤ st.q ∧ st.q ≤ r))
    (hE : OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁ ts st) :
    (shiftActs blank mark k b ts).length = ovShiftCost k p₁ r st.q := by
  have hqOf : qOf ts = st.q := qOf_eq hE
  have hp1Of : p1Of ts = p₁ := p1Of_eq hE
  rcases Bool.eq_false_or_eq_true b with hbb | hbb
  · subst hbb
    have hcond : k * p₁ ≤ st.q ∧ st.q ≤ r := of_decide_eq_true hb.symm
    have hprog : shiftActs blank mark k true ts = periodActs blank mark p₁ := by
      unfold shiftActs; rw [if_pos rfl, hp1Of]
    rw [hprog, periodActs_length]
    unfold ovShiftCost GSTapes.shiftCost gsShift
    rw [if_pos hcond, if_pos hcond]
    omega
  · subst hbb
    have hcond : ¬ (k * p₁ ≤ st.q ∧ st.q ≤ r) := of_decide_eq_false hb.symm
    have hprog : shiftActs blank mark k false ts = resetShift sc k st.q := by
      unfold shiftActs; rw [if_neg (by simp), hqOf]
    rw [hprog, resetShift_length, GSTapes.moves_zero k hk]
    unfold ovShiftCost GSTapes.shiftCost gsShift
    rw [if_neg hcond, if_neg hcond]

/-- **主定理 2a**：動作列の長さは `ovStepCost`。 -/
theorem ovProgram_length {blank leftSym startSym endSym mark one : Fin sc}
    {u v xw fw T : List (Fin sc)} {L p₁ k r c : ℕ} {b bu : Bool}
    {ts : OvTapes sc} {st : ScanState}
    (hk : 0 < k) (hL : L ≤ xw.length) (hleft : leftSym ∉ xw) (hend : endSym ∉ v)
    (hT : T = (xw.take L).reverse) (hc : c = u.length)
    (hb : b = decide (k * p₁ ≤ st.q ∧ st.q ≤ r))
    (hbu : bu = decide (MatchLen u T st.pos u.length))
    (hE : OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁ ts st)
    (hfront : st.pos + u.length + st.q ≤ L) :
    (ovProgram blank leftSym endSym mark one k c b bu ts).length
      = ovStepCost u v T k p₁ r st := by
  subst hT
  have hTlen : ((xw.take L).reverse).length = L := revTake_length hL
  have hsh := shiftActs_length (mark := mark) (b := b) hk hb hE
  unfold ovProgram ovStepCost
  by_cases hfr : st.pos + u.length + st.q = ((xw.take L).reverse).length
  · have hfrL : st.pos + u.length + st.q = L := by omega
    rw [if_pos (read_X_frontier hE hfrL), if_pos hfr]
    unfold ovFrontierCost
    rw [List.length_append, List.length_append, uCheck_length, hsh, hc]
    have hbueq : (if bu then [Act.Fset (sc := sc) one] else []).length
        = (if MatchLen u ((xw.take L).reverse) st.pos u.length then 1 else 0) := by
      by_cases hm : MatchLen u ((xw.take L).reverse) st.pos u.length
      · rw [if_pos (show bu = true by rw [hbu]; exact decide_eq_true hm), if_pos hm]; rfl
      · rw [if_neg (show ¬ (bu = true) by rw [hbu]; simp [hm]), if_neg hm]; rfl
    rw [hbueq]
  · have hlt : st.pos + u.length + st.q < L := by omega
    rw [if_neg (read_X_ne_left hleft hE hL hlt), if_neg hfr]
    by_cases hadv : Tape.read ts.P ≠ endSym ∧ Tape.read ts.P = Tape.read ts.X
    · rw [if_pos hadv, if_pos ((advance_iff hend hE hL hlt).1 hadv)]
      rfl
    · rw [if_neg hadv,
        if_neg (fun hcon => hadv ((advance_iff hend hE hL hlt).2 hcon))]
      exact hsh

/-! ### 償却 -/

theorem gsShift_le_delta {k p₁ r : ℕ} (hk : 0 < k) (st : ScanState) :
    gsShift k p₁ r st.q ≤
      Phi k ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ - Phi k st := by
  unfold gsShift gsNextQ Phi
  dsimp only
  split_ifs with hc
  · have hle : p₁ ≤ st.q := le_trans (Nat.le_mul_of_pos_left p₁ hk) hc.1
    have hpk : p₁ ≤ k * p₁ := Nat.le_mul_of_pos_left p₁ hk
    obtain ⟨X, hX⟩ : ∃ X, (k + 1) * st.pos = X := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y, k * p₁ = Y := ⟨_, rfl⟩
    have e1 : (k + 1) * (st.pos + p₁) = X + (Y + p₁) := by rw [← hX, ← hY]; ring
    rw [hY] at hpk
    rw [e1, hX]
    clear e1 hX hY hc
    omega
  · have hks : st.q ≤ k * max 1 (ceilDiv st.q k) :=
      le_trans (ceilDiv_bounds hk).1 (Nat.mul_le_mul (Nat.le_refl k) (Nat.le_max_right 1 _))
    obtain ⟨X, hX⟩ : ∃ X, (k + 1) * st.pos = X := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s, max 1 (ceilDiv st.q k) = s := ⟨_, rfl⟩
    obtain ⟨A, hA⟩ : ∃ A, k * s = A := ⟨_, rfl⟩
    rw [hs] at hks
    rw [hA] at hks
    have e1 : (k + 1) * (st.pos + s) = X + (A + s) := by rw [← hX, ← hA]; ring
    rw [hs, e1, hX]
    omega

theorem ovShiftCost_le {k p₁ r : ℕ} (hk : 0 < k) (st : ScanState) :
    ovShiftCost k p₁ r st.q ≤
      (2 * k + 4) *
        (Phi k ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ - Phi k st) + 8 := by
  have h1 := GSTapes.shiftCost_le (k := k) (p₁ := p₁) (r := r) hk st
  have h2 := gsShift_le_delta (k := k) (p₁ := p₁) (r := r) hk st
  obtain ⟨D, hD⟩ : ∃ D,
      Phi k ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ - Phi k st = D := ⟨_, rfl⟩
  rw [hD] at h1 h2 ⊢
  obtain ⟨A, hA⟩ : ∃ A, (2 * k + 2) * D = A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, (2 * k + 4) * D = B := ⟨_, rfl⟩
  have h3 : B = A + 2 * D := by rw [← hA, ← hB]; ring
  rw [hA] at h1
  rw [hB]
  unfold ovShiftCost
  omega

/-- **主定理 2b（償却）**：一歩の動作数はポテンシャルの増分で償却される。
定数は `A = 9k + 11`（`uCheck` が `7|u|+1` になった分、旧 `6k+8` から増加）、`B = 8`。 -/
theorem ovStepCost_le {u v T : List (Fin sc)} {k p₁ r minimum : ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k)
    (hmin : max 1 (2 * u.length) ≤ minimum) (hchg : u.length ≤ k * p₁) {st : ScanState}
    (hrange : st.pos + minimum ≤ T.length) :
    ovStepCost u v T k p₁ r st ≤
      (9 * k + 11) * (Phi k (ovStep u v T k p₁ r st) - Phi k st) + 8 := by
  unfold ovStepCost ovStep
  split_ifs with hfr hadv
  · have hge := front_q_ge (T := T) hmin hrange hfr
    have hch := gs_charge (k := k) (p₁ := p₁) (r := r) (q := st.q) (c := u.length)
      hk hK.period_pos hge.2 hge.1 hchg st.pos
    have hsh := ovShiftCost_le (k := k) (p₁ := p₁) (r := r) hk st
    have hst : (⟨st.pos, st.q⟩ : ScanState) = st := rfl
    rw [hst] at hch
    obtain ⟨D, hD⟩ : ∃ D,
        Phi k ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ - Phi k st = D := ⟨_, rfl⟩
    rw [hD] at hch hsh ⊢
    obtain ⟨A, hA⟩ : ∃ A, (k + 1) * D = A := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, (2 * k + 4) * D = B := ⟨_, rfl⟩
    obtain ⟨C, hC⟩ : ∃ C, (9 * k + 11) * D = C := ⟨_, rfl⟩
    have h3 : C = 7 * A + B := by rw [← hA, ← hB, ← hC]; ring
    rw [hA] at hch
    rw [hB] at hsh
    rw [hC]
    unfold ovFrontierCost
    split_ifs <;> omega
  · have hp : Phi k (⟨st.pos, st.q + 1⟩ : ScanState) - Phi k st = 1 := by
      obtain ⟨X, hX⟩ : ∃ X, (k + 1) * st.pos = X := ⟨_, rfl⟩
      show (k + 1) * st.pos + (st.q + 1) - ((k + 1) * st.pos + st.q) = 1
      rw [hX]
      omega
    rw [hp, Nat.mul_one]
    omega
  · have hsh := ovShiftCost_le (k := k) (p₁ := p₁) (r := r) hk st
    obtain ⟨D, hD⟩ : ∃ D,
        Phi k ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ - Phi k st = D := ⟨_, rfl⟩
    rw [hD] at hsh ⊢
    obtain ⟨B, hB⟩ : ∃ B, (2 * k + 4) * D = B := ⟨_, rfl⟩
    obtain ⟨C, hC⟩ : ∃ C, (9 * k + 11) * D = C := ⟨_, rfl⟩
    have h3 : B ≤ C := by
      rw [← hB, ← hC]
      exact Nat.mul_le_mul (by omega) (Nat.le_refl D)
    rw [hB] at hsh
    rw [hC]
    omega


/-! ### 段全体の動作数 -/

/-- 段全体の動作数（`ovCost` と同じ再帰）。 -/
def ovRunCost (u v T : List (Fin sc)) (k p₁ r minimum : ℕ) : ℕ → ScanState → ℕ
  | 0, _ => 0
  | fuel + 1, st =>
      if T.length < st.pos + minimum then 0
      else ovStepCost u v T k p₁ r st
        + ovRunCost u v T k p₁ r minimum fuel (ovStep u v T k p₁ r st)

/-- **系（段全体のコスト）**：総動作数は `A * (ポテンシャルの残り) + B * ovCost`。
`A = 6k + 8`, `B = 8`。 -/
theorem ovRunCost_le {u v T : List (Fin sc)} {k p₁ r minimum : ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k)
    (hlen : u.length + v.length = T.length)
    (hmin : max 1 (2 * u.length) ≤ minimum) (hchg : u.length ≤ k * p₁) :
    ∀ (fuel : ℕ) (st : ScanState), OvInv u v T st →
      ovRunCost u v T k p₁ r minimum fuel st
        ≤ (9 * k + 11) * ((k + 1) * (2 * T.length) + T.length - Phi k st)
          + 8 * ovCost u v T k p₁ r minimum fuel st := by
  intro fuel
  induction fuel with
  | zero => intro st _; simp [ovRunCost]
  | succ fuel ih =>
    intro st hinv
    simp only [ovRunCost, ovCost]
    by_cases hstop : T.length < st.pos + minimum
    · rw [if_pos hstop, if_pos hstop]; simp
    · rw [if_neg hstop, if_neg hstop]
      have hrange : st.pos + minimum ≤ T.length := by omega
      have hstep := ovStep_inv hK hk hlen hmin hrange hinv
      have hlt := ovStep_phi_lt (u := u) (v := v) (T := T) (p₁ := p₁) (r := r) hk
        hK.period_pos st
      have hcap := ovStep_phi_le (u := u) (v := v) (T := T) (k := k) (p₁ := p₁) (r := r)
        (minimum := minimum) hk hlen hinv (by omega) hrange
      have hself : Phi k st ≤ (k + 1) * (2 * T.length) + T.length := by omega
      have hcost := ovStepCost_le (u := u) (v := v) (T := T) (minimum := minimum)
        hK hk hmin hchg hrange
      have hrec := ih _ hstep
      have key : (9 * k + 11) * ((k + 1) * (2 * T.length) + T.length
              - Phi k (ovStep u v T k p₁ r st))
          + (9 * k + 11) * (Phi k (ovStep u v T k p₁ r st) - Phi k st)
          = (9 * k + 11) * ((k + 1) * (2 * T.length) + T.length - Phi k st) := by
        rw [← Nat.mul_add]; congr 1; omega
      have hc1 : 1 ≤ (if st.pos + u.length + st.q = T.length then 1 + u.length else 1) := by
        split_ifs <;> omega
      have hsum := Nat.add_le_add hcost hrec
      omega

/-! ### 段のコスト（`k = 8`） -/

/-- 一段のテープ動作数（`borderStageCost_le` と同じ設定）。 -/
theorem stageTapeCost_le {x : List (Fin sc)} {dec : ℕ → ℕ × ℕ × ℕ} {k L : ℕ} (hk : 0 < k)
    (hL : L ≤ x.length) (hone : 1 ≤ L)
    (hOK : StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2) :
    ovRunCost ((x.take L).take (dec L).1) ((x.take L).drop (dec L).1)
      (x.take L).reverse k (dec L).2.1 (dec L).2.2 (max 1 (2 * (dec L).1))
      ((k + 2) * L + 1) ⟨0, 0⟩
      ≤ (9 * k + 11) * ((k + 1) * (2 * L) + L)
        + 8 * ((k + 1) * ((k + 1) * (2 * L) + L)) := by
  obtain ⟨hcut, hks, hchg, hshort⟩ := hOK
  have hylen : (x.take L).length = L := by simp only [List.length_take]; omega
  have hut : ((x.take L).take (dec L).1).length = (dec L).1 := by
    simp only [List.length_take]; omega
  have hvt : ((x.take L).drop (dec L).1).length = L - (dec L).1 := by
    simp only [List.length_drop]; omega
  have hTt : ((x.take L).reverse).length = L := by simp only [List.length_reverse]; omega
  have hlen : ((x.take L).take (dec L).1).length + ((x.take L).drop (dec L).1).length
      = ((x.take L).reverse).length := by omega
  have hmin : max 1 (2 * ((x.take L).take (dec L).1).length) ≤ max 1 (2 * (dec L).1) := by
    rw [hut]
  have hinv0 : OvInv ((x.take L).take (dec L).1) ((x.take L).drop (dec L).1)
      (x.take L).reverse ⟨0, 0⟩ :=
    ⟨by simpa using matchLen_zero _ _ _, by simp only []; omega⟩
  have hphi0 : Phi k (⟨0, 0⟩ : ScanState) = 0 := by simp [Phi]
  have h1 := ovRunCost_le (u := (x.take L).take (dec L).1)
    (v := (x.take L).drop (dec L).1) (T := (x.take L).reverse) hks hk hlen hmin
    (by rw [hut]; exact hchg) ((k + 2) * L + 1) ⟨0, 0⟩ hinv0
  have h2 := borderStageCost_le (x := x) (dec := dec) (k := k) (L := L) hk hL hone
    ⟨hcut, hks, hchg, hshort⟩
  rw [hTt, hphi0] at h1
  simp only [Nat.sub_zero] at h1
  have h3 : 8 * ovCost ((x.take L).take (dec L).1) ((x.take L).drop (dec L).1)
      (x.take L).reverse k (dec L).2.1 (dec L).2.2 (max 1 (2 * (dec L).1))
      ((k + 2) * L + 1) ⟨0, 0⟩
      ≤ 8 * ((k + 1) * ((k + 1) * (2 * L) + L)) := Nat.mul_le_mul (Nat.le_refl 8) h2
  omega

/-- **段のテープコスト（`k = 8`）**：一段の動作数は `2945·L` 以下
（旧 `2432·L` から、`uCheck` が `7|u|+1` になった分だけ増加）。 -/
theorem stage_tape_cost_le {x : List (Fin sc)} {dec : ℕ → ℕ × ℕ × ℕ} {L : ℕ}
    (hL : L ≤ x.length) (hone : 1 ≤ L)
    (hOK : StageOK x 8 L (dec L).1 (dec L).2.1 (dec L).2.2) :
    ovRunCost ((x.take L).take (dec L).1) ((x.take L).drop (dec L).1)
      (x.take L).reverse 8 (dec L).2.1 (dec L).2.2 (max 1 (2 * (dec L).1))
      ((8 + 2) * L + 1) ⟨0, 0⟩ ≤ 2945 * L := by
  have h := stageTapeCost_le (k := 8) (by omega) hL hone hOK
  have e1 : (9 * 8 + 11) * ((8 + 1) * (2 * L) + L) = 1577 * L := by ring
  have e2 : 8 * ((8 + 1) * ((8 + 1) * (2 * L) + L)) = 1368 * L := by ring
  omega

/-! ### ジョブ全体のテープコスト -/

/-- ジョブ全体のテープ動作数。段の起動 1 ＋ 次段のために `X`／`X2`／`F` のヘッドを
新しい窓長 `L' = nextLen s` へ戻す掃き（`≤ 2L`）＋ 段の走査。
`P`／`U`／`Cnt` の詰め替え（分解 `dec L` の計算）は `GSDecomp` の担当なので数えない。 -/
def borderJobTapeCost (x : List (Fin sc)) (dec : ℕ → ℕ × ℕ × ℕ) (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, L =>
      if L = 0 then 0
      else 2 * L + 1
        + ovRunCost ((x.take L).take (dec L).1) ((x.take L).drop (dec L).1)
            (x.take L).reverse k (dec L).2.1 (dec L).2.2 (max 1 (2 * (dec L).1))
            ((k + 2) * L + 1) ⟨0, 0⟩
        + borderJobTapeCost x dec k fuel (nextLen (dec L).1)

/-- **主定理 3（線形時間・テープ版）**：`k = 8` のとき総動作数は `4500·|x|` 以下
（旧 `4000·|x|` から、`stage_tape_cost_le` の増加ぶんだけ増加）。 -/
theorem borderJobTapeCost_le {x : List (Fin sc)} {dec : ℕ → ℕ × ℕ × ℕ}
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x 8 L (dec L).1 (dec L).2.1 (dec L).2.2) :
    ∀ (fuel L : ℕ), L ≤ x.length → borderJobTapeCost x dec 8 fuel L ≤ 4500 * L := by
  intro fuel
  induction fuel with
  | zero => intro L _; simp [borderJobTapeCost]
  | succ fuel ih =>
    intro L hL
    simp only [borderJobTapeCost]
    split_ifs with h0
    · exact Nat.zero_le _
    · have hOKL := hOK L (by omega) hL
      have hstage := stage_tape_cost_le (dec := dec) hL (by omega) hOKL
      have hshort := hOKL.cut_short
      have hshrink : 3 * nextLen (dec L).1 + 1 ≤ L := nextLen_shrink (by omega)
      have hrec := ih (nextLen (dec L).1) (by omega)
      have h1500 : 4500 * nextLen (dec L).1 ≤ 1500 * (L - 1) := by
        have h : 1500 * (3 * nextLen (dec L).1) ≤ 1500 * (L - 1) :=
          Nat.mul_le_mul (Nat.le_refl _) (by omega)
        omega
      omega

/-- 総動作数。 -/
def totalTapeSteps (x : List (Fin sc)) (dec : ℕ → ℕ × ℕ × ℕ) (k : ℕ) : ℕ :=
  borderJobTapeCost x dec k (x.length + 1) x.length

/-- **主定理 3（総和形）**：`palPrefixFlagsGS_work` のテープ版。 -/
theorem palPrefixFlagsGS_tape_work {x : List (Fin sc)} {dec : ℕ → ℕ × ℕ × ℕ}
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x 8 L (dec L).1 (dec L).2.1 (dec L).2.2) :
    totalTapeSteps x dec 8 ≤ 4500 * x.length :=
  borderJobTapeCost_le hOK (x.length + 1) x.length (Nat.le_refl _)


/-! ## 8. 段全体の実現とフラグ出力 -/

/-- 段の走査を最後まで走らせたときの走査状態。 -/
def ovRunState (u v T : List (Fin sc)) (k p₁ r minimum : ℕ) : ℕ → ScanState → ScanState
  | 0, st => st
  | fuel + 1, st =>
      if T.length < st.pos + minimum then st
      else ovRunState u v T k p₁ r minimum fuel (ovStep u v T k p₁ r st)

/-- 段の走査を最後まで走らせたときのフラグ語。 -/
def ovRunFlags (u v T : List (Fin sc)) (one : Fin sc) (k p₁ r minimum : ℕ) :
    ℕ → ScanState → List (Fin sc) → List (Fin sc)
  | 0, _, fw => fw
  | fuel + 1, st, fw =>
      if T.length < st.pos + minimum then fw
      else ovRunFlags u v T one k p₁ r minimum fuel (ovStep u v T k p₁ r st)
        (stepFlags u T one st fw)

/-- 段の走査を最後まで走らせたときのテープ状態。オラクルビットは
`decide` で与える（有限制御が別途維持する符号付きカウンタの代用）。 -/
def ovRunTapes (blank leftSym endSym mark one : Fin sc) (u v T : List (Fin sc))
    (k p₁ r minimum c : ℕ) : ℕ → ScanState → OvTapes sc → OvTapes sc
  | 0, _, ts => ts
  | fuel + 1, st, ts =>
      if T.length < st.pos + minimum then ts
      else ovRunTapes blank leftSym endSym mark one u v T k p₁ r minimum c fuel
        (ovStep u v T k p₁ r st)
        (applyActs blank (ovProgram blank leftSym endSym mark one k c
          (decide (k * p₁ ≤ st.q ∧ st.q ≤ r))
          (decide (MatchLen u T st.pos u.length)) ts) ts)

/-- **段の実現**：段を走り切ったあとのテープは、走査状態と更新されたフラグ語を符号化する。 -/
theorem ovRunTapes_encodes
    {blank leftSym startSym endSym mark one : Fin sc}
    {u v xw T : List (Fin sc)} {L p₁ k r minimum c : ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hL : L ≤ xw.length)
    (hleft : leftSym ∉ xw) (hend : endSym ∉ v)
    (hT : T = (xw.take L).reverse) (hc : c = u.length)
    (hlen : u.length + v.length = T.length)
    (hmin : max 1 (2 * u.length) ≤ minimum) :
    ∀ (fuel : ℕ) (st : ScanState) (ts : OvTapes sc) (fw : List (Fin sc)),
      OvInv u v T st →
      OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁ ts st →
      OvEncodes blank leftSym startSym endSym mark u v xw
        (ovRunFlags u v T one k p₁ r minimum fuel st fw) L p₁
        (ovRunTapes blank leftSym endSym mark one u v T k p₁ r minimum c fuel st ts)
        (ovRunState u v T k p₁ r minimum fuel st) := by
  have hTlen : T.length = L := by rw [hT]; exact revTake_length hL
  intro fuel
  induction fuel with
  | zero => intro st ts fw _ hE; exact hE
  | succ fuel ih =>
    intro st ts fw hinv hE
    simp only [ovRunFlags, ovRunTapes, ovRunState]
    by_cases hstop : T.length < st.pos + minimum
    · rw [if_pos hstop, if_pos hstop, if_pos hstop]; exact hE
    · rw [if_neg hstop, if_neg hstop, if_neg hstop]
      have hrange : st.pos + minimum ≤ T.length := by omega
      have hstep := ovStep_inv hK hk hlen hmin hrange hinv
      refine ih _ _ _ hstep ?_
      exact ovEncodes_step hk hL hleft hend hT hc rfl rfl hE
        (by have := hinv.front; omega) (by have := hstep.front; omega)

/-! ### フラグ語の内容 -/

theorem foldl_set_getElem? (one : Fin sc) : ∀ (l : List ℕ) (fw : List (Fin sc)) (j : ℕ),
    j < fw.length →
      (l.foldl (fun w ℓ => w.set ℓ one) fw)[j]? = if j ∈ l then some one else fw[j]? := by
  intro l
  induction l with
  | nil => intro fw j _; simp
  | cons a l ih =>
    intro fw j hj
    have hlen : (fw.set a one).length = fw.length := by simp
    have h := ih (fw.set a one) j (by omega)
    simp only [List.foldl_cons]
    rw [h]
    by_cases hjl : j ∈ l
    · simp [hjl]
    · rw [if_neg hjl]
      by_cases hja : j = a
      · subst hja
        rw [List.getElem?_set_self hj]
        simp
      · rw [List.getElem?_set_ne (Ne.symm hja)]
        simp [hjl, hja]

theorem ovRunFlags_eq_foldl {u v T : List (Fin sc)} {one : Fin sc} {k p₁ r minimum : ℕ} :
    ∀ (fuel : ℕ) (st : ScanState) (fw : List (Fin sc)),
      ovRunFlags u v T one k p₁ r minimum fuel st fw
        = (ovRun u v T k p₁ r minimum fuel st).foldl (fun w ℓ => w.set ℓ one) fw := by
  intro fuel
  induction fuel with
  | zero => intro st fw; simp [ovRunFlags, ovRun]
  | succ fuel ih =>
    intro st fw
    simp only [ovRunFlags, ovRun]
    split_ifs with hstop hrep
    · simp
    · rw [ih, List.foldl_cons]
      congr 1
      unfold stepFlags
      rw [if_pos hrep]
    · rw [ih]
      congr 1
      unfold stepFlags
      rw [if_neg hrep]

/-- 一段のフラグ語。 -/
def stageFlags (y : List (Fin sc)) (one : Fin sc) (k s p₁ r fuel : ℕ)
    (fw : List (Fin sc)) : List (Fin sc) :=
  ovRunFlags (y.take s) (y.drop s) y.reverse one k p₁ r (max 1 (2 * s)) fuel ⟨0, 0⟩ fw

theorem stageFlags_eq_foldl (y : List (Fin sc)) (one : Fin sc) (k s p₁ r fuel : ℕ)
    (fw : List (Fin sc)) :
    stageFlags y one k s p₁ r fuel fw
      = (stageRun y k s p₁ r fuel).foldl (fun w ℓ => w.set ℓ one) fw :=
  ovRunFlags_eq_foldl _ _ _

/-- ジョブ全体のフラグ語（段を縮めながら同じ `F` テープに書き続ける）。 -/
def jobFlags (x : List (Fin sc)) (dec : ℕ → ℕ × ℕ × ℕ) (one : Fin sc) (k : ℕ) :
    ℕ → ℕ → List (Fin sc) → List (Fin sc)
  | 0, _, fw => fw
  | fuel + 1, L, fw =>
      if L = 0 then fw
      else jobFlags x dec one k fuel (nextLen (dec L).1)
        (stageFlags (x.take L) one k (dec L).1 (dec L).2.1 (dec L).2.2 ((k + 2) * L + 1) fw)

theorem jobFlags_eq_foldl (x : List (Fin sc)) (dec : ℕ → ℕ × ℕ × ℕ) (one : Fin sc) (k : ℕ) :
    ∀ (fuel L : ℕ) (fw : List (Fin sc)),
      jobFlags x dec one k fuel L fw
        = (borderJob x dec k fuel L).foldl (fun w ℓ => w.set ℓ one) fw := by
  intro fuel
  induction fuel with
  | zero => intro L fw; simp [jobFlags, borderJob]
  | succ fuel ih =>
    intro L fw
    simp only [jobFlags, borderJob]
    split_ifs with h0
    · simp
    · rw [ih, List.foldl_append, stageFlags_eq_foldl]

/-- **主定理 4（フラグ出力）**：全段を走り終えたあと、`F` テープの添字 `ℓ` は
`x.take ℓ` が回文のときちょうど `one` になる（`palPrefixFlagsGS_spec` のテープ版）。 -/
theorem flags_on_tape {x : List (Fin sc)} {dec : ℕ → ℕ × ℕ × ℕ} {one : Fin sc} {k : ℕ}
    {fw : List (Fin sc)} (hk : 4 ≤ k)
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2)
    (ℓ : ℕ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ x.length) (hfw : ℓ < fw.length) :
    (jobFlags x dec one k (x.length + 1) x.length fw)[ℓ]?
      = if IsPal (x.take ℓ) then some one else fw[ℓ]? := by
  rw [jobFlags_eq_foldl, foldl_set_getElem? one _ fw ℓ hfw]
  have hmem := borderJob_mem_iff hk hOK (x.length + 1) x.length (Nat.le_refl _) (by omega) ℓ
  by_cases hp : IsPal (x.take ℓ)
  · rw [if_pos hp, if_pos (hmem.2 ⟨h1, h2, hp⟩)]
  · rw [if_neg hp, if_neg (fun hc => hp (hmem.1 hc).2.2)]

/-- 初期フラグ語が `zero` で埋まっているときの読み替え。 -/
theorem flags_iff_pal {x : List (Fin sc)} {dec : ℕ → ℕ × ℕ × ℕ} {one zero : Fin sc} {k : ℕ}
    {fw : List (Fin sc)} (hk : 4 ≤ k) (hne : one ≠ zero)
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2)
    (ℓ : ℕ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ x.length) (hfw : ℓ < fw.length)
    (hz : fw[ℓ]? = some zero) :
    (jobFlags x dec one k (x.length + 1) x.length fw)[ℓ]? = some one ↔ IsPal (x.take ℓ) := by
  rw [flags_on_tape hk hOK ℓ h1 h2 hfw]
  by_cases hp : IsPal (x.take ℓ)
  · simp [hp]
  · rw [if_neg hp, hz]
    simp only [hp, iff_false, Option.some.injEq]
    exact fun hc => hne hc.symm

/-- `palPrefixFlagsGS` との対応（`ℓ ≥ 1`）。 -/
theorem flags_on_tape_eq_palPrefixFlagsGS {x : List (Fin sc)} {dec : ℕ → ℕ × ℕ × ℕ}
    {one zero : Fin sc} {k : ℕ} {fw : List (Fin sc)} (hk : 4 ≤ k) (hne : one ≠ zero)
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2)
    (ℓ : ℕ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ x.length) (hfw : ℓ < fw.length)
    (hz : fw[ℓ]? = some zero) :
    ((jobFlags x dec one k (x.length + 1) x.length fw)[ℓ]? = some one)
      ↔ (palPrefixFlagsGS x dec k)[ℓ]? = some true := by
  rw [flags_iff_pal hk hne hOK ℓ h1 h2 hfw hz, palPrefixFlagsGS_spec hk hOK ℓ h2]
  simp


/-! ## 9. 段の継ぎ目（凍結窓の縮小）について

`ovRunTapes_encodes` は**一段**を丸ごと実現する。段 `L` から次段 `L' = nextLen (dec L).1`
へ移るときにテープ側で必要なのは次の 2 つで、コストはどちらも `borderJobTapeCost` の
`2 * L + 1` に含めてある。

* **窓の付け替え**：段の窓は「`X` のヘッドの初期位置」だけで決まる（終端マーカは要らない）。
  段の終わりで `X` のヘッドは添字 `L - (pos + |u| + q) ≤ L` に、`X2` と `F` のヘッドは
  添字 `L - pos ≤ L` にある。次段はこの 3 本のヘッドを添字 `L'` へ置き直せばよく、
  どのヘッドの移動量も `≤ L + L' ≤ 2L` である（`L' < L`）。
  `F` は段の中では左へ一方向に掃くだけなので、段内の `F` の総移動量も `≤ L`。
* **`P` / `U` / `Cnt` の詰め替え**：新しい `v' = (x.take L').drop s'`、
  `u' = (x.take L').take s'`、`p₁'` を載せ直す作業。これは分解 `dec L'` を計算する
  仕事そのものであり、`GSDecomp` の担当なのでここでは数えていない
  （`BorderJob.borderJobCost` が `dec` のコストを数えていないのと同じ約束）。

フラグ語の側の継ぎ目は完全に形式化してある：`jobFlags` は段ごとの `stageFlags`
（＝ `ovRunFlags`、すなわち `ovEncodes_step` が実際に `F` テープに起こす変化）を
そのまま合成したもので、`jobFlags_eq_foldl` と `flags_on_tape` が
`borderJob` / `palPrefixFlagsGS` との一致を与える。
-/

/-! ## 10. 小例による健全性チェック -/

section Examples

example : (periodActs (0 : Fin 3) 1 5).length = 6 * 5 + 2 := by decide
example : (resetShift 3 8 20).length = 20 + (20 - 3) + 2 + 0 + 2 * 3 := by decide
example : (resetShift 3 8 0).length = 0 + 0 + 2 + 1 + 2 * 1 := by decide
example : (uCheck 3 (0 : Fin 3) 1 7).length = 7 * 7 + 1 := by
  rw [uCheck_length]
example : (posMoves 3 6).length = 2 * 6 := by decide
example : ovShiftCost 8 2 40 40 = 6 * 2 + 2 := by decide
example : ovShiftCost 8 2 40 41 = 41 + (41 - 6) + 2 + 0 + 2 * 6 := by decide

end Examples

end PalPeg.BorderTapes
