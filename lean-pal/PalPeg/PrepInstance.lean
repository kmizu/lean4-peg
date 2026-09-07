import PalPeg.PrepInstances
import PalPeg.GSPreprocessTapes
import PalPeg.StageTapes
import PalPeg.PatternTapesPair
import PalPeg.ClearAny

/-!
# `PrepOnTapes` の具体化に向けた埋め込み (`PrepInstance`)

`GSPre.decompose2_on_tapes`（`GSPreprocessTapes.lean`）が与える 9 本テープの分解器を、
`PatternTapes.Tapes sc`（12 本テープ）の中に埋め込み、最終的に
`StageTapes.PrepOnTapes sc blank mark` を組み立てることを目標にする。

## 割り付け

`GSPre.Tapes sc` の 9 本を、`PatternTapes.Tapes sc` の 12 本のうち
`SetupPre` が **前処理の仕事**として空けている 9 本へ写す：

| `GSPre` | `PatternTapes` | 役割 |
|---|---|---|
| `V1` | `sP` | パターンの作業コピー 1（終了後スタック `[]` に掃除） |
| `V2` | `sU` | パターンの作業コピー 2（終了後スタック `[]` に掃除） |
| `Cd` | `sC2` | 内側ループの残余予算（終了後カウンタ `0` に掃除） |
| `Cq` | `sAp` | 一致長（終了後カウンタ `0` に掃除） |
| `Ce` | `sAn` | シフト幅の作業（終了後カウンタ `0` に掃除） |
| `Cf` | `sRn` | `first` の作業（終了後カウンタ `0` に掃除、`Enc` の終値も `0`） |
| `Cp` | `sC1` | 候補周期 → 最終的に `p₁`（`SetupPre.c1` が要求する値そのもの） |
| `Cs` | `sCs` | 切断位置 → 最終的に `s`（`SetupPre.cs` が要求する値そのもの） |
| `Cr` | `sRp` | 到達域 → 最終的に `r`（`SetupPre.rp` が要求する値そのもの） |

残る 3 本 `sT`, `sX2`, `sIn` は分解器が触らない（テキスト 2 本とパターン原本の
入力コピー）。

## 本ファイルで完結して証明できるもの

1. `liftAct` / `prj` — 上表の埋め込みと、その逆に 9 本を読み出す射影。
2. `prj_run` — **模倣補題**：`prj` を通せば `PatternTapes.run` による
   `liftAct` 込みの実行が、`GSPre.applyActs` による素の実行と一致する。
3. `run_liftActs_other` — 割り付け先 9 本以外（`sT`/`sX2`/`sIn`、および `sAp` 等の
   互いの区別）を `liftAct` 実行が動かさないこと。
4. `width_applyActs_le` — `ClearAny.width_step` を `GSPre.Act` 側へ移した、
   分解器プログラム実行によるテープ幅の増分見積り。これは掃除フェーズの
   コスト見積り（`3 * width + 3` 系）を `decProg` の長さで抑えるための道具。
5. **`prologueProg` / `prologue_spec`**（`sorry` なし）：`StageTapes.PrepPre` から
   `x := PrepInstances.stagePat w L = (w.take L).reverse` を `sP`/`sU` 上に
   `GSPre.pword startSym endSym x`（ヘッド添字 `1`）の形で書き込み、`prj` 越しに
   `GSPre.Enc … x 0 0 ⟨0,…,0⟩` を成立させる。`sT`/`sX2` は不変、`sIn` は
   `SeqView blank _ w (L - 1)` に復元される。長さはちょうど `6 * L + 5`
   （`prologueProg_length`）。副産物として `rightWalk`（`leftWalk` の右版）と
   `copyLoop2`（`copyLoop` の 2 目的地版）を用意した。

## 未完成（`sorry` なし、単に未着手）

* **epilogue**：`decompose2_on_tapes` が返す終状態から、`sP`/`sU` を
  `ClearAny.clearAny` でスタック `[]` に、`sC2/sAp/sAn/sRn` を `ClearAny.clearAny`
  ＋ `mark` 書き戻し 1 手で `CounterView' _ _ 0` に戻し、`SetupPre` を満たす配置を作る。
* **`prepInstance` 本体**と `len_le`（`PrepInstances.prep_prog_len_le` 系の線形上界、
  `prologueProg_length` の `6 * L + 5`、epilogue の `O(L)` 上界を合算するだけで
  閉じるはずだが、epilogue が埋まっていないため未接続）。
-/

namespace PalPeg
namespace PrepInstance

open PegSeparation.RealTimeTM
open PalPeg.PatternTapes

variable {sc : ℕ}

/-! ## 1. 割り付け -/

/-- `GSPre.Act.V1` の書き戻し先。 -/
def sV1 : Fin 12 := sP

/-- `GSPre.Act.V2` の書き戻し先。 -/
def sV2 : Fin 12 := sU

/-- `GSPre.Act.Cd` の書き戻し先。 -/
def sCd : Fin 12 := sC2

/-- `GSPre.Act.Cq` の書き戻し先。 -/
def sCq : Fin 12 := sAp

/-- `GSPre.Act.Ce` の書き戻し先。 -/
def sCe : Fin 12 := sAn

/-- `GSPre.Act.Cf` の書き戻し先。 -/
def sCf : Fin 12 := sRn

/-- 9 本の割り付け先はすべて相異なる。 -/
theorem slots_pairwise :
    List.Pairwise (· ≠ ·)
      ([sV1, sV2, sCd, sCq, sCe, sC1, sCf, sCs, sRp] : List (Fin 12)) := by
  unfold sV1 sV2 sCd sCq sCe sCf
  unfold sP sC1 sC2 sAp sAn sRp sRn sU sCs
  decide

/-- `GSPre.Act` の 1 動作を、割り付け先の `PatternTapes.SAct` へ写す。
`V1`/`V2` は「読んだ記号を書き戻す」動作なので `SAct.keep`、カウンタ 7 本は
`SAct.put` にそのまま対応する。 -/
def liftAct : GSPre.Act sc → SAct sc
  | .V1 m => .keep sV1 m
  | .V2 m => .keep sV2 m
  | .Cd a m => .put sCd a m
  | .Cq a m => .put sCq a m
  | .Ce a m => .put sCe a m
  | .Cp a m => .put sC1 a m
  | .Cf a m => .put sCf a m
  | .Cs a m => .put sCs a m
  | .Cr a m => .put sRp a m

/-- 動作が触る `PatternTapes` 側のスロット。 -/
theorem sTape_liftAct (a : GSPre.Act sc) :
    sTape (liftAct a) =
      match a with
      | .V1 _ => sV1
      | .V2 _ => sV2
      | .Cd _ _ => sCd
      | .Cq _ _ => sCq
      | .Ce _ _ => sCe
      | .Cp _ _ => sC1
      | .Cf _ _ => sCf
      | .Cs _ _ => sCs
      | .Cr _ _ => sRp := by
  cases a <;> rfl

/-- `PatternTapes.Tapes` から `GSPre.Tapes` への射影（割り付け先 9 本を読み出す）。 -/
def prj (S : Tapes sc) : GSPre.Tapes sc :=
  { V1 := S sV1, V2 := S sV2, Cd := S sCd, Cq := S sCq, Ce := S sCe
    Cp := S sC1, Cf := S sCf, Cs := S sCs, Cr := S sRp }

/-! ## 2. 模倣補題 -/

/-- 1 動作の模倣：`liftAct a` を 12 本テープ側で実行してから射影するのは、
`a` を 9 本テープ側で実行してから同じ射影を取るのと一致する。 -/
theorem prj_applyAct (blank : Fin sc) (a : GSPre.Act sc) (S : Tapes sc) :
    prj (applyS blank S (liftAct a)) = GSPre.applyAct blank (prj S) a := by
  cases a <;>
    simp [liftAct, prj, applyS, GSPre.applyAct, updT,
      sV1, sV2, sCd, sCq, sCe, sCf,
      sP, sC1, sC2, sAp, sAn, sRp, sRn, sU, sCs]

/-- **模倣補題**：`liftAct` で写した動作列を 12 本テープ側で実行してから射影するのは、
元の動作列を 9 本テープ側でそのまま実行してから射影するのと一致する。 -/
theorem prj_run (blank : Fin sc) (l : List (GSPre.Act sc)) (S : Tapes sc) :
    prj (run blank (l.map liftAct) S) = GSPre.applyActs blank l (prj S) := by
  induction l generalizing S with
  | nil => rfl
  | cons a l ih =>
      simp only [List.map_cons, run_cons, GSPre.applyActs_cons]
      rw [ih (applyS blank S (liftAct a)), prj_applyAct]

/-- 割り付け先以外のスロットは `liftAct` で写した実行によって変化しない。
特に `sT`, `sX2`, `sIn`（前処理が読み書きしないテキスト・入力コピー）を含む。 -/
theorem run_liftActs_other (blank : Fin sc) (l : List (GSPre.Act sc)) (S : Tapes sc)
    (j : Fin 12) (hj : j ≠ sV1) (hj2 : j ≠ sV2) (hj3 : j ≠ sCd) (hj4 : j ≠ sCq)
    (hj5 : j ≠ sCe) (hj6 : j ≠ sC1) (hj7 : j ≠ sCf) (hj8 : j ≠ sCs) (hj9 : j ≠ sRp) :
    run blank (l.map liftAct) S j = S j := by
  induction l generalizing S with
  | nil => rfl
  | cons a l ih =>
      simp only [List.map_cons, run_cons]
      rw [ih]
      cases a <;>
        simp [liftAct, applyS, updT, hj, hj2, hj3, hj4, hj5, hj6, hj7, hj8, hj9]

/-! ## 3. テープ幅の見積り（`ClearAny` を `GSPre.Act` 側へ移す） -/

open PalPeg.Tape in
/-- 1 動作での `GSPre.Tapes` の 1 成分の幅の増分は高々 `1`
（触らない成分は不変、触る成分は `ClearAny.width_step`）。ここでは
`Cd` 成分について例示し、他の成分も同型に成り立つ（`liftAct`/`applyAct` の
定義がすべての成分について同じ形をしているため）。 -/
theorem width_Cd_applyAct_le (blank : Fin sc) (a : GSPre.Act sc) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyAct blank ts a).Cd ≤ ClearAny.width ts.Cd + 1 := by
  cases a with
  | Cd b m => exact ClearAny.width_step blank ts.Cd b m
  | _ => simp [GSPre.applyAct]

/-- `n` 個の動作を経ても `Cd` 成分の幅は高々 `n` しか増えない。 -/
theorem width_Cd_applyActs_le (blank : Fin sc) (l : List (GSPre.Act sc)) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyActs blank l ts).Cd ≤ ClearAny.width ts.Cd + l.length := by
  induction l generalizing ts with
  | nil => simp [GSPre.applyActs]
  | cons a l ih =>
      have h1 := width_Cd_applyAct_le blank a ts
      have h2 := ih (GSPre.applyAct blank ts a)
      simp only [GSPre.applyActs_cons, List.length_cons] at *
      omega

/-! ## 3b. 準備：ヘッドを右へ歩かせる（`leftWalk` の右版） -/

/-- ヘッドを右へ `n` 歩（読んだ記号を書き戻す）。`PatternTapes.leftWalk` の右版。 -/
def rightWalk (i : Fin 12) (n : ℕ) : List (SAct sc) := List.replicate n (SAct.keep i .right)

@[simp] theorem rightWalk_length (i : Fin 12) (n : ℕ) :
    (rightWalk (sc := sc) i n).length = n := by simp [rightWalk]

theorem rightWalk_untouched (blank : Fin sc) {i j : Fin 12} (h : j ≠ i) (n : ℕ) (S : Tapes sc) :
    run blank (rightWalk i n) S j = S j := by
  refine run_untouched blank j _ S (fun a ha => ?_)
  rw [List.eq_of_mem_replicate ha]
  exact Ne.symm h

theorem rightWalk_spec (blank : Fin sc) (i : Fin 12) :
    ∀ (n m : ℕ) (S : Tapes sc) (w : List (Fin sc)), m + n < w.length →
      Tape.SeqView blank (S i) w m →
      Tape.SeqView blank (run blank (rightWalk i n) S i) w (m + n) := by
  intro n
  induction n with
  | zero => intro m S w _ h; simpa [rightWalk] using h
  | succ n ih =>
    intro m S w hlt h
    have hstep : run blank (rightWalk (sc := sc) i (n + 1)) S
        = run blank (rightWalk i n) (applyS blank S (SAct.keep i .right)) := by
      rw [rightWalk, List.replicate_succ, run_cons, rightWalk]
    rw [hstep]
    have h2 : Tape.SeqView blank (run blank (rightWalk i n) (applyS blank S (SAct.keep i .right))
        i) w ((m + 1) + n) := by
      refine ih (m + 1) _ w (by omega) ?_
      rw [applyS_keep_self]
      exact Tape.seq_move_right h (by omega)
    rwa [show (m + 1) + n = m + (n + 1) from by omega] at h2

/-! ## 3c. 同じ読み取りを 2 本に同時に積む（`copyLoop` の 2 目的地版） -/

/-- 1 記号ぶん：`i` が読んでいる記号を `j1`, `j2` の両方に積み、`i` を左へ 1 歩。 -/
def copyRound2 (i j1 j2 : Fin 12) (S : Tapes sc) : List (SAct sc) :=
  [SAct.put j1 (Tape.read (S i)) .right, SAct.put j2 (Tape.read (S i)) .right, SAct.keep i .left]

/-- `n` 記号ぶん。 -/
def copyLoop2 (blank : Fin sc) (i j1 j2 : Fin 12) : ℕ → Tapes sc → List (SAct sc)
  | 0, _ => []
  | n + 1, S =>
      copyRound2 i j1 j2 S ++ copyLoop2 blank i j1 j2 n (run blank (copyRound2 i j1 j2 S) S)

theorem copyLoop2_length (blank : Fin sc) (i j1 j2 : Fin 12) :
    ∀ (n : ℕ) (S : Tapes sc), (copyLoop2 blank i j1 j2 n S).length = 3 * n := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    rw [copyLoop2, List.length_append, ih]
    simp [copyRound2]
    omega

theorem copyLoop2_untouched (blank : Fin sc) {i j1 j2 l : Fin 12} (hi : l ≠ i) (h1 : l ≠ j1)
    (h2 : l ≠ j2) :
    ∀ (n : ℕ) (S : Tapes sc), run blank (copyLoop2 blank i j1 j2 n S) S l = S l := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    rw [copyLoop2, run_append, ih]
    refine run_untouched blank l _ S (fun a ha => ?_)
    rcases List.mem_cons.1 ha with h | h
    · subst h; exact Ne.symm h1
    · rcases List.mem_cons.1 h with h | h
      · subst h; exact Ne.symm h2
      · rcases List.mem_cons.1 h with h | h
        · subst h; exact Ne.symm hi
        · simp at h

/-- **主補題**：`i` のヘッドを添字 `b` から左へ `n` 歩ぶん歩かせながら、読んだ記号を
`j1`, `j2` の両方に積む。`PatternTapes.copyLoop_spec` の 2 目的地版。 -/
theorem copyLoop2_spec (blank : Fin sc) {i j1 j2 : Fin 12} (hij1 : j1 ≠ i) (hij2 : j2 ≠ i)
    (hjj : j1 ≠ j2) :
    ∀ (n b : ℕ) (S : Tapes sc) (w l1 l2 : List (Fin sc)), n ≤ b + 1 →
      Tape.SeqView blank (S i) w b →
      Tape.StackView blank (S j1) l1 → Tape.StackView blank (S j2) l2 →
      Tape.SeqView blank (run blank (copyLoop2 blank i j1 j2 n S) S i) w (b - n) ∧
        Tape.StackView blank (run blank (copyLoop2 blank i j1 j2 n S) S j1)
          (((w.take (b + 1)).drop (b + 1 - n)) ++ l1) ∧
        Tape.StackView blank (run blank (copyLoop2 blank i j1 j2 n S) S j2)
          (((w.take (b + 1)).drop (b + 1 - n)) ++ l2) := by
  intro n
  induction n with
  | zero =>
    intro b S w l1 l2 _ hs hst1 hst2
    have hz : run blank (copyLoop2 blank i j1 j2 0 S) S = S := rfl
    rw [hz]
    have hnil : (w.take (b + 1)).drop (b + 1) = [] := by
      refine List.drop_eq_nil_of_le ?_
      simp
    refine ⟨by simpa using hs, ?_, ?_⟩ <;> simp [hnil]
    exacts [hst1, hst2]
  | succ n ih =>
    intro b S w l1 l2 hn hs hst1 hst2
    have hnb : n ≤ b := by omega
    have hblt : b < w.length := hs.lt
    set S₁ := run blank (copyRound2 i j1 j2 S) S with hS₁
    have hS₁i : S₁ i = Tape.step blank (S i) (S i).focus .left := by
      rw [hS₁, copyRound2]
      show applyS blank
          (applyS blank (applyS blank S (SAct.put j1 (Tape.read (S i)) .right))
            (SAct.put j2 (Tape.read (S i)) .right)) (SAct.keep i .left) i = _
      rw [applyS_keep_self,
        applyS_ne blank _ (SAct.put j2 (Tape.read (S i)) .right) (Ne.symm hij2),
        applyS_ne blank _ (SAct.put j1 (Tape.read (S i)) .right) (Ne.symm hij1)]
    have hS₁j1 : S₁ j1 = Tape.step blank (S j1) (S i).focus .right := by
      rw [hS₁, copyRound2]
      show applyS blank
          (applyS blank (applyS blank S (SAct.put j1 (Tape.read (S i)) .right))
            (SAct.put j2 (Tape.read (S i)) .right)) (SAct.keep i .left) j1 = _
      rw [applyS_ne blank _ (SAct.keep i .left) hij1,
        applyS_ne blank _ (SAct.put j2 (Tape.read (S i)) .right) hjj,
        applyS_put_self]
      rfl
    have hS₁j2 : S₁ j2 = Tape.step blank (S j2) (S i).focus .right := by
      rw [hS₁, copyRound2]
      show applyS blank
          (applyS blank (applyS blank S (SAct.put j1 (Tape.read (S i)) .right))
            (SAct.put j2 (Tape.read (S i)) .right)) (SAct.keep i .left) j2 = _
      rw [applyS_ne blank _ (SAct.keep i .left) hij2, applyS_put_self,
        applyS_ne blank S (SAct.put j1 (Tape.read (S i)) .right) (Ne.symm hjj)]
      rfl
    have hstack1 : Tape.StackView blank (S₁ j1) ((S i).focus :: l1) := by
      rw [hS₁j1]; exact Tape.push_spec hst1 _
    have hstack2 : Tape.StackView blank (S₁ j2) ((S i).focus :: l2) := by
      rw [hS₁j2]; exact Tape.push_spec hst2 _
    have hseq : Tape.SeqView blank (S₁ i) w (b - 1) := by
      rw [hS₁i]
      cases b with
      | zero => exact Tape.seq_move_left_edge hs
      | succ c => exact Tape.seq_move_left hs
    have hrun : run blank (copyLoop2 blank i j1 j2 (n + 1) S) S
        = run blank (copyLoop2 blank i j1 j2 n S₁) S₁ := by
      rw [copyLoop2, run_append]
    obtain ⟨h1, h2, h3⟩ := ih (b - 1) S₁ w ((S i).focus :: l1) ((S i).focus :: l2) (by omega)
      hseq hstack1 hstack2
    rw [hrun]
    have hfocus : w[b]? = some (S i).focus := hs.focus_eq
    have htake : w.take (b + 1) = w.take b ++ [(S i).focus] := by
      rw [List.take_add_one, hfocus]; rfl
    have hlen : (w.take b).length = b := by
      simp only [List.length_take]; omega
    have hdrop : (w.take (b + 1)).drop (b - n) = (w.take b).drop (b - n) ++ [(S i).focus] := by
      rw [htake, List.drop_append_of_le_length (by rw [hlen]; omega)]
    have key : ∀ l : List (Fin sc),
        ((w.take (b - 1 + 1)).drop (b - 1 + 1 - n)) ++ ((S i).focus :: l)
          = ((w.take (b + 1)).drop (b + 1 - (n + 1))) ++ l := by
      intro l
      rcases Nat.eq_zero_or_pos b with rfl | hbpos
      · have hn0 : n = 0 := by omega
        subst hn0
        simp [htake]
      · rw [show b - 1 + 1 = b from by omega, show b + 1 - (n + 1) = b - n from by omega, hdrop]
        simp
    refine ⟨by simpa [Nat.sub_sub, Nat.add_comm] using h1, ?_, ?_⟩
    · rw [← key l1]; exact h2
    · rw [← key l2]; exact h3

/-! ## 3d. 前処理の prologue：`sIn` から `x` を `sP`/`sU` に書く -/

section Prologue

variable {blank startSym endSym mark : Fin sc} {L : ℕ} {w Text : List (Fin sc)} {S : Tapes sc}

/-- **prologue プログラム**：`sIn`（ヘッド `L - 1`）から `x = (w.take L).reverse` を
`sP`/`sU` の両方へ `pword startSym endSym x`（ヘッド添字 `1`）の形で書き、`sIn` のヘッドを
`L - 1` へ戻す。`copyLoop2` を左へ歩くことで書き込む語が自動的に反転するので、
実際に反転操作を別に行う必要はない。 -/
def prologueProg (blank startSym endSym : Fin sc) (L : ℕ) : Tapes sc → List (SAct sc) :=
  seqP blank (fun _ => pushBoth startSym)
    (seqP blank (fun S => copyLoop2 blank sIn sU sP L S)
      (seqP blank (fun _ => pushBoth endSym)
        (seqP blank (fun _ => settle blank sU L)
          (seqP blank (fun _ => settle blank sP L)
            (fun _ => rightWalk sIn (L - 1))))))

/-- **prologue の長さ**：`6 * L + 5` ちょうど（`L ≥ 1`）。 -/
theorem prologueProg_length (hL : 0 < L) (S : Tapes sc) :
    (prologueProg (sc := sc) blank startSym endSym L S).length = 6 * L + 5 := by
  simp only [prologueProg, seqP_length, pushBoth_length, copyLoop2_length, settle_length,
    rightWalk_length]
  omega

theorem prologueProg_length_le (hL : 0 < L) (S : Tapes sc) :
    (prologueProg (sc := sc) blank startSym endSym L S).length ≤ 6 * L + 5 :=
  (prologueProg_length hL S).le

/-- **prologue の正しさ**：`PrepPre` から出発すると、`prj` を通して `GSPre.Enc` が
初期状態（`a = b = 0`, `Ctr` は全 `0`）で成立し、テキスト 2 本 (`sT`/`sX2`) は不変、
`sIn` は元の `SeqView` に戻る。 -/
theorem prologue_spec (hpre : StageTapes.PrepPre blank mark L w Text S) :
    GSPre.Enc blank startSym endSym mark (PrepInstances.stagePat w L) 0 0 ⟨0, 0, 0, 0, 0, 0, 0⟩
        (prj (run blank (prologueProg blank startSym endSym L S) S))
      ∧ run blank (prologueProg blank startSym endSym L S) S sT = S sT
      ∧ run blank (prologueProg blank startSym endSym L S) S sX2 = S sX2
      ∧ Tape.SeqView blank (run blank (prologueProg blank startSym endSym L S) S sIn) w (L - 1) := by
  obtain ⟨hpos, hle, hIn, hU, hP, hT, hX2, hCs, hC1, hC2, hAp, hAn, hRp, hRn⟩ := hpre
  set x := PrepInstances.stagePat w L with hx
  have hxlen : x.length = L := PrepInstances.stagePat_length hle
  -- フェーズ 1：両方に `startSym`。
  obtain ⟨S₁, hS1⟩ : ∃ T, run blank (pushBoth startSym) S = T := ⟨_, rfl⟩
  have hS1U : S₁ sU = Tape.step blank (S sU) startSym .right := by rw [← hS1]; exact pushBoth_U ..
  have hS1P : S₁ sP = Tape.step blank (S sP) startSym .right := by rw [← hS1]; exact pushBoth_P ..
  have hS1st1 : Tape.StackView blank (S₁ sU) [startSym] := by
    rw [hS1U]; simpa using Tape.push_spec hU startSym
  have hS1st2 : Tape.StackView blank (S₁ sP) [startSym] := by
    rw [hS1P]; simpa using Tape.push_spec hP startSym
  have hS1In : Tape.SeqView blank (S₁ sIn) w (L - 1) := by
    rw [← hS1]; rwa [pushBoth_ne blank startSym (show sIn ≠ sU by decide)
      (show sIn ≠ sP by decide)]
  have hS1T : S₁ sT = S sT := by
    rw [← hS1]; exact pushBoth_ne blank startSym (show sT ≠ sU by decide)
      (show sT ≠ sP by decide) S
  have hS1X2 : S₁ sX2 = S sX2 := by
    rw [← hS1]; exact pushBoth_ne blank startSym (show sX2 ≠ sU by decide)
      (show sX2 ≠ sP by decide) S
  have hS1cnt : ∀ j : Fin 12, j ≠ sU → j ≠ sP → S₁ j = S j := by
    intro j hju hjp; rw [← hS1]; exact pushBoth_ne blank startSym hju hjp S
  -- フェーズ 2：`sIn` から両方へ `x` を積む。
  obtain ⟨S₂, hS2⟩ : ∃ T, run blank (copyLoop2 blank sIn sU sP L S₁) S₁ = T := ⟨_, rfl⟩
  have hLb : L ≤ (L - 1) + 1 := by omega
  obtain ⟨h2i, h2u, h2p⟩ := copyLoop2_spec blank (show sU ≠ sIn by decide)
    (show sP ≠ sIn by decide) (show sU ≠ sP by decide) L (L - 1) S₁ w [startSym] [startSym]
    hLb hS1In hS1st1 hS1st2
  rw [hS2] at h2i h2u h2p
  have hb1 : (L - 1) + 1 = L := by omega
  have hdrop0 : L - L = 0 := by omega
  rw [hb1] at h2u h2p
  have h2i' : Tape.SeqView blank (S₂ sIn) w 0 := by
    rwa [show L - 1 - L = 0 from by omega] at h2i
  have h2u' : Tape.StackView blank (S₂ sU) (w.take L ++ [startSym]) := by
    simpa [hdrop0] using h2u
  have h2p' : Tape.StackView blank (S₂ sP) (w.take L ++ [startSym]) := by
    simpa [hdrop0] using h2p
  have h2T : S₂ sT = S sT := by
    rw [← hS2, copyLoop2_untouched blank (show sT ≠ sIn by decide) (show sT ≠ sU by decide)
      (show sT ≠ sP by decide) L S₁, hS1T]
  have h2X2 : S₂ sX2 = S sX2 := by
    rw [← hS2, copyLoop2_untouched blank (show sX2 ≠ sIn by decide) (show sX2 ≠ sU by decide)
      (show sX2 ≠ sP by decide) L S₁, hS1X2]
  have h2cnt : ∀ j : Fin 12, j ≠ sIn → j ≠ sU → j ≠ sP → S₂ j = S₁ j := by
    intro j hji hju hjp
    rw [← hS2]; exact copyLoop2_untouched blank hji hju hjp L S₁
  -- フェーズ 3：両方に `endSym`。
  obtain ⟨S₃, hS3⟩ : ∃ T, run blank (pushBoth endSym) S₂ = T := ⟨_, rfl⟩
  have hS3U : S₃ sU = Tape.step blank (S₂ sU) endSym .right := by rw [← hS3]; exact pushBoth_U ..
  have hS3P : S₃ sP = Tape.step blank (S₂ sP) endSym .right := by rw [← hS3]; exact pushBoth_P ..
  have hS3st1 : Tape.StackView blank (S₃ sU) (endSym :: (w.take L ++ [startSym])) := by
    rw [hS3U]; exact Tape.push_spec h2u' endSym
  have hS3st2 : Tape.StackView blank (S₃ sP) (endSym :: (w.take L ++ [startSym])) := by
    rw [hS3P]; exact Tape.push_spec h2p' endSym
  have hS3In : S₃ sIn = S₂ sIn := by
    rw [← hS3]; exact pushBoth_ne blank endSym (show sIn ≠ sU by decide) (show sIn ≠ sP by decide) S₂
  have hS3T : S₃ sT = S sT := by
    rw [← hS3]
    rw [pushBoth_ne blank endSym (show sT ≠ sU by decide) (show sT ≠ sP by decide) S₂, h2T]
  have hS3X2 : S₃ sX2 = S sX2 := by
    rw [← hS3]
    rw [pushBoth_ne blank endSym (show sX2 ≠ sU by decide) (show sX2 ≠ sP by decide) S₂, h2X2]
  have hS3cnt : ∀ j : Fin 12, j ≠ sU → j ≠ sP → S₃ j = S₂ j := by
    intro j hju hjp; rw [← hS3]; exact pushBoth_ne blank endSym hju hjp S₂
  -- フェーズ 4：ヘッドを添字 `1` へ（`sU`）。
  obtain ⟨S₄, hS4⟩ : ∃ T, run blank (settle blank sU L) S₃ = T := ⟨_, rfl⟩
  have hlenU : (w.take L ++ [startSym]).length = L + 1 := by
    simp [List.length_take]; omega
  have hS4U : Tape.SeqView blank (S₄ sU)
      ((endSym :: (w.take L ++ [startSym])).reverse) 1 := by
    rw [← hS4]; exact settle_spec blank sU hS3st1 hlenU
  have hS4other : ∀ j : Fin 12, j ≠ sU → S₄ j = S₃ j := by
    intro j hj; rw [← hS4]; exact settle_untouched blank hj L S₃
  -- フェーズ 5：ヘッドを添字 `1` へ（`sP`）。
  have hS4P_eq : S₄ sP = S₃ sP := hS4other sP (show sP ≠ sU by decide)
  have hS4st2 : Tape.StackView blank (S₄ sP) (endSym :: (w.take L ++ [startSym])) := by
    rw [hS4P_eq]; exact hS3st2
  obtain ⟨S₅, hS5⟩ : ∃ T, run blank (settle blank sP L) S₄ = T := ⟨_, rfl⟩
  have hS5P : Tape.SeqView blank (S₅ sP)
      ((endSym :: (w.take L ++ [startSym])).reverse) 1 := by
    rw [← hS5]; exact settle_spec blank sP hS4st2 hlenU
  have hS5other : ∀ j : Fin 12, j ≠ sP → S₅ j = S₄ j := by
    intro j hj; rw [← hS5]; exact settle_untouched blank hj L S₄
  have hS5U : Tape.SeqView blank (S₅ sU)
      ((endSym :: (w.take L ++ [startSym])).reverse) 1 := by
    rw [hS5other sU (show sU ≠ sP by decide)]; exact hS4U
  have hS5In : S₅ sIn = S₂ sIn := by
    rw [hS5other sIn (show sIn ≠ sP by decide), hS4other sIn (show sIn ≠ sU by decide), hS3In]
  have hS5T : S₅ sT = S sT := by
    rw [hS5other sT (show sT ≠ sP by decide), hS4other sT (show sT ≠ sU by decide), hS3T]
  have hS5X2 : S₅ sX2 = S sX2 := by
    rw [hS5other sX2 (show sX2 ≠ sP by decide), hS4other sX2 (show sX2 ≠ sU by decide), hS3X2]
  have hS5cnt : ∀ j : Fin 12, j ≠ sU → j ≠ sP → j ≠ sIn → S₅ j = S j := by
    intro j hju hjp hji
    rw [hS5other j hjp, hS4other j hju, hS3cnt j hju hjp, h2cnt j hji hju hjp, hS1cnt j hju hjp]
  -- フェーズ 6：`sIn` を `L - 1` へ戻す。
  have hS5In' : Tape.SeqView blank (S₅ sIn) w 0 := by rw [hS5In]; exact h2i'
  obtain ⟨S₆, hS6⟩ : ∃ T, run blank (rightWalk sIn (L - 1)) S₅ = T := ⟨_, rfl⟩
  have hLlt : (0 : ℕ) + (L - 1) < w.length := by omega
  have hS6In : Tape.SeqView blank (S₆ sIn) w (L - 1) := by
    rw [← hS6]
    have h := rightWalk_spec blank sIn (L - 1) 0 S₅ w hLlt hS5In'
    simpa using h
  have hS6other : ∀ j : Fin 12, j ≠ sIn → S₆ j = S₅ j := by
    intro j hj; rw [← hS6]; exact rightWalk_untouched blank hj (L - 1) S₅
  have hS6U : Tape.SeqView blank (S₆ sU)
      ((endSym :: (w.take L ++ [startSym])).reverse) 1 := by
    rw [hS6other sU (show sU ≠ sIn by decide)]; exact hS5U
  have hS6P : Tape.SeqView blank (S₆ sP)
      ((endSym :: (w.take L ++ [startSym])).reverse) 1 := by
    rw [hS6other sP (show sP ≠ sIn by decide)]; exact hS5P
  have hS6T : S₆ sT = S sT := by
    rw [hS6other sT (show sT ≠ sIn by decide)]; exact hS5T
  have hS6X2 : S₆ sX2 = S sX2 := by
    rw [hS6other sX2 (show sX2 ≠ sIn by decide)]; exact hS5X2
  have hS6cnt : ∀ j : Fin 12, j ≠ sU → j ≠ sP → j ≠ sIn → S₆ j = S j := by
    intro j hju hjp hji
    rw [hS6other j hji]; exact hS5cnt j hju hjp hji
  -- 実行結果は `S₆`。
  have hrun : run blank (prologueProg blank startSym endSym L S) S = S₆ := by
    simp only [prologueProg, seqP_run, hS1, hS2, hS3, hS4, hS5, hS6]
  -- `pword` への書き換え。
  have hpword : (endSym :: (w.take L ++ [startSym])).reverse
      = GSPre.pword startSym endSym x := by
    simp [GSPre.pword, hx, PrepInstances.stagePat, List.reverse_append, List.reverse_cons]
  rw [hpword] at hS6U hS6P
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrun]
    refine
      { v1 := ?_
        v2 := ?_
        cd := ?_
        cq := ?_
        ce := ?_
        cp := ?_
        cf := ?_
        cs := ?_
        cr := ?_ }
    · show Tape.SeqView blank (S₆ sV1) (GSPre.pword startSym endSym x) (0 + 1)
      rw [Nat.zero_add]; show Tape.SeqView blank (S₆ sP) (GSPre.pword startSym endSym x) 1
      exact hS6P
    · show Tape.SeqView blank (S₆ sV2) (GSPre.pword startSym endSym x) (0 + 1)
      rw [Nat.zero_add]; show Tape.SeqView blank (S₆ sU) (GSPre.pword startSym endSym x) 1
      exact hS6U
    · show Tape.CounterView' blank mark (S₆ sCd) 0
      show Tape.CounterView' blank mark (S₆ sC2) 0
      rw [hS6cnt sC2 (by decide) (by decide) (by decide)]; exact hC2
    · show Tape.CounterView' blank mark (S₆ sCq) 0
      show Tape.CounterView' blank mark (S₆ sAp) 0
      rw [hS6cnt sAp (by decide) (by decide) (by decide)]; exact hAp
    · show Tape.CounterView' blank mark (S₆ sCe) 0
      show Tape.CounterView' blank mark (S₆ sAn) 0
      rw [hS6cnt sAn (by decide) (by decide) (by decide)]; exact hAn
    · show Tape.CounterView' blank mark (S₆ sC1) 0
      rw [hS6cnt sC1 (by decide) (by decide) (by decide)]; exact hC1
    · show Tape.CounterView' blank mark (S₆ sCf) 0
      show Tape.CounterView' blank mark (S₆ sRn) 0
      rw [hS6cnt sRn (by decide) (by decide) (by decide)]; exact hRn
    · show Tape.CounterView' blank mark (S₆ sCs) 0
      rw [hS6cnt sCs (by decide) (by decide) (by decide)]; exact hCs
    · show Tape.CounterView' blank mark (S₆ sRp) 0
      rw [hS6cnt sRp (by decide) (by decide) (by decide)]; exact hRp
  · rw [hrun]; exact hS6T
  · rw [hrun]; exact hS6X2
  · rw [hrun]; exact hS6In

end Prologue

/-!
## 4. 残作業（`prologue` は完成済み、`epilogue`/`prepInstance` が未着手）

`prologue` は `prologueProg` / `prologue_spec`（本ファイル ## 3d 節）として
`sorry` なしで完成した。残るのは以下の 2 点のみ。

`epilogue`：`decompose2_on_tapes` の終状態（`∃ a b D Q E, Enc … x a b ⟨D,Q,E,p₁,0,s,r⟩ …`）
から、`ClearAny.clearAny` で `sP`（= `V1`）・`sU`（= `V2`）をスタック `[]` に、
`ClearAny.clearAny` の結果に `SAct.put _ mark .right` を 1 手足すことで
`sC2`（= `Cd`）・`sAp`（= `Cq`）・`sAn`（= `Ce`）・`sRn`（= `Cf`）を
`CounterView' _ _ 0` に戻す（`CounterView' blank mark tp 0 ↔ StackView blank tp [mark]`、
`Tape.push_spec` で最後の 1 手を正当化する）。この 2 つを両方 `run` で連結し、
`SetupPre` の 15 個のフィールドをすべて `prj`/`liftAct` 越しに再構成すれば
`PrepOnTapes.post` が閉じる。

`len_le`：`decProg` の長さは `PrepInstances.prep_prog_len_le`（`hsum` 付き）で
`L` の 1 次式に抑えられる。prologue は `2 * L + O(1)`、epilogue の `clearAny` 部分は
`width_Cd_applyActs_le` 系（4 本のカウンタ）と `V1`/`V2` の `SeqView` から来る
`width ≤ x.length + 1 = L + 1`（一定、`decompose2_on_tapes` の動作でこの 2 本の幅は
`SeqView` の性質上つねに `x.length + 1` — 増えない）という評価から `O(L)`。
これらを合算すれば `Cp * L + Dp` の形に収まるはずだが、epilogue の具体的な動作列と
`post` の証明を書き切っていないため、`prepInstance` 自体は本ファイルにまだ存在しない。

以上より、本ファイルは **模倣層（1〜4）と prologue（5）を `sorry` なしで提供**する
にとどまり、epilogue・`prepInstance` 本体・`prepInstance_res` は未着手であることを
ここに明記する。
-/

end PrepInstance
end PalPeg
