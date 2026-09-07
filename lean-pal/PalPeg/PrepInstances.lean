import PalPeg.StageTapes
import PalPeg.GSDecompose2Work
-- NOTE: `PalPeg.GSPreprocessTapes` は本ファイルの証明には不要（数値定数
-- `193 = 16*8+65` / `48 = 4*8+16` を注記として使うだけ）。同ファイルは現在編集中で
-- olean が無いため、依存を作らないでおく。

/-!
# 前処理インタフェースの具体化に向けた材料 (`PrepInstances`)

`PalPeg.StageTapes.PrepOnTapes` と `PalPeg.MiddleTapes.DecompOnTapes` を
`GSPreprocessTapes` の具体プログラム（`decProg` / `decompose2_on_tapes`）から
埋めるための **指標レベルの材料** を集める。

本ファイルで完結して証明できるのは次の 3 点である。

1. `prepRes` — `PrepOnTapes.res` に載せるべき正規化済み三つ組
   `(s, effPeriod (x.drop s) p₁, effReach p₁ r)`（`x = (w.take L).reverse`,
   `(s,p₁,r) = decompose2 x 8`）と、`stage_tapes_spec'` が要求する
   `hres` / `H : GSCore` / `hs` / `hkp` の各事実（`prep_res_eq`）。
2. `hkp`：`stage_tapes_spec'` が現在要求する予算 `8 * pe ≤ 5 * S` は退化ケース
   `p₁ = 0` も含めて**無条件**に成り立つ（`prep_kp_5S` / `prep_res_eq5`）。
   なお素朴な形 `8 * effPeriod (x.drop s) p₁ ≤ L` は `p₁ = 0` のとき恒偽であり
   （`prep_kp_zero_absurd`）、`rateS` を上げて予算を緩めたのはこのためである。
3. `decompose2` の仕事量の線形上界（周期和の仮説 `hsum` つき）と、そこから出る
   `decProg` の長さの上界（`prep_prog_len_le`）。この上界は
   `decompose2_on_tapes` の第 2 項が `|x|` について **2 次**であるため、
   `PrepOnTapes.len_le` が要求する `Cp * L + Dp` の形にはならない。

また `MiddleTapes.DecompOnTapes` を `EndToEnd2.gsDec2` 版に述べ直した `DecompOnTapes2` を置く
（`EndToEnd2` の経路が必要とするのはこちらである）。
-/

namespace PalPeg
namespace PrepInstances

open PegSeparation.RealTimeTM

variable {sc : ℕ}

/-! ## 1. 段のパターンと分解 -/

/-- 幅 `L` の段のパターン：入力の接頭辞の反転。 -/
def stagePat (w : List (Fin sc)) (L : ℕ) : List (Fin sc) := (w.take L).reverse

theorem stagePat_length {w : List (Fin sc)} {L : ℕ} (hL : L ≤ w.length) :
    (stagePat w L).length = L := by
  rw [stagePat, List.length_reverse, List.length_take]; omega

/-- 正規化前の分解 `decompose2 x 8`。 -/
def rawRes (w : List (Fin sc)) (L : ℕ) : ℕ × ℕ × ℕ := decompose2 (stagePat w L) 8

/-- **`PrepOnTapes.res` に載せる三つ組**：`GSCore` の出力を `KSimple` が要求する
`0 < p₁` に正規化したもの（`EndToEnd2.gsDec2` / `GSDecompL1.stageOK_exists` と同じ形）。 -/
def prepRes (w : List (Fin sc)) (L : ℕ) : ℕ × ℕ × ℕ :=
  ((rawRes w L).1,
    effPeriod ((stagePat w L).drop (rawRes w L).1) (rawRes w L).2.1,
    effReach (rawRes w L).2.1 (rawRes w L).2.2)

/-- `stage_tapes_spec'` の `hres` はこの定義から **定義的に**従う。 -/
theorem prepRes_eq (w : List (Fin sc)) (L : ℕ) :
    prepRes w L
      = ((rawRes w L).1,
          effPeriod ((stagePat w L).drop (rawRes w L).1) (rawRes w L).2.1,
          effReach (rawRes w L).2.1 (rawRes w L).2.2) := rfl

@[simp] theorem prepRes_fst (w : List (Fin sc)) (L : ℕ) :
    (prepRes w L).1 = (rawRes w L).1 := rfl

/-! ## 2. `GSCore` と切断位置 -/

/-- 分解は無条件に `GSDecomp`（したがって `GSCore`）を満たす。 -/
theorem prep_gsDecomp (w : List (Fin sc)) (L : ℕ) :
    GSDecomp (stagePat w L) 8 (rawRes w L).1 (rawRes w L).2.1 (rawRes w L).2.2 :=
  decompose2_gsDecomp (by omega) _

/-- `stage_tapes_spec'` の `H`。 -/
theorem prep_core (w : List (Fin sc)) (L : ℕ) :
    GSCore (stagePat w L) 8 (rawRes w L).1 (rawRes w L).2.1 (rawRes w L).2.2 :=
  (prep_gsDecomp w L).toGSCore

theorem stagePat_ne_nil {w : List (Fin sc)} {L : ℕ} (hL : 0 < L) (hw : L ≤ w.length) :
    stagePat w L ≠ [] := by
  intro h
  have := stagePat_length (w := w) hw
  rw [h] at this
  simp at this
  omega

/-- **`hs`**：切断位置は段幅より真に小さい。 -/
theorem prep_cut_lt {w : List (Fin sc)} {L : ℕ} (hL : 0 < L) (hw : L ≤ w.length) :
    (rawRes w L).1 < L := by
  have h := decompose2_cut_lt (k := 8) (by omega) (stagePat_ne_nil hL hw)
  rwa [stagePat_length hw] at h

/-- 切断位置は L1 の上界を満たす：`7 * s < L`。 -/
theorem prep_cut_bound {w : List (Fin sc)} {L : ℕ} (hL : 0 < L) (hw : L ≤ w.length) :
    7 * (rawRes w L).1 < L := by
  have h := (prep_gsDecomp w L).cut_bound (stagePat_ne_nil hL hw)
  rw [stagePat_length hw] at h
  simpa using h

/-! ## 3. `hkp`：`8 * p₁ ≤ L` -/

/-- 正規化**前**の周期については `8 * p₁ ≤ L` が無条件に成り立つ。 -/
theorem prep_kp_raw {w : List (Fin sc)} {L : ℕ} (hw : L ≤ w.length) :
    8 * (rawRes w L).2.1 ≤ L := by
  by_cases hp : (rawRes w L).2.1 = 0
  · rw [hp]; omega
  · have hleast := (prep_core w L).least hp
    have hlen : 8 * (rawRes w L).2.1
        ≤ ((stagePat w L).drop (rawRes w L).1).length := hleast.1.2.1
    have : ((stagePat w L).drop (rawRes w L).1).length ≤ (stagePat w L).length :=
      by simp [List.length_drop]
    rw [stagePat_length hw] at this
    omega

/-- **`hkp`（非退化ケース）**：`p₁ ≠ 0` なら正規化後も `8 * pe ≤ L`。 -/
theorem prep_kp {w : List (Fin sc)} {L : ℕ} (hw : L ≤ w.length)
    (hp : (rawRes w L).2.1 ≠ 0) :
    8 * effPeriod ((stagePat w L).drop (rawRes w L).1) (rawRes w L).2.1 ≤ L := by
  rw [effPeriod, if_neg hp]
  exact prep_kp_raw hw

/-- **退化ケースの不能性**：`p₁ = 0` のとき `hkp` は恒偽。
（`effPeriod` は `p₁ = 0` を `|v| + 1` に正規化するが、`L1` の切断上界 `7 * s < L` と
合わせると `8 * (L - s + 1) ≤ L` は起こり得ない。） -/
theorem prep_kp_zero_absurd {w : List (Fin sc)} {L : ℕ} (hL : 0 < L) (hw : L ≤ w.length)
    (hp : (rawRes w L).2.1 = 0) :
    ¬ (8 * effPeriod ((stagePat w L).drop (rawRes w L).1) (rawRes w L).2.1 ≤ L) := by
  rw [effPeriod, if_pos hp, List.length_drop, stagePat_length hw]
  have hcut : (rawRes w L).1 < L := prep_cut_lt hL hw
  have hb : 7 * (rawRes w L).1 < L := prep_cut_bound hL hw
  omega

/-- **`hkp`（無条件版）**：`StageTapes.stage_tapes_spec'` が実際に要求する予算
`k * pe ≤ 5 * S`（`k = 8`）は、退化ケース `p₁ = 0` も含めて無条件に成り立つ。
非退化なら `8 * pe ≤ S/2`、退化なら `pe = |v| + 1 ≤ S/2 + 1` なので
`8 * pe ≤ 4 * S + 8 ≤ 5 * S`（`8 ≤ S`）。 -/
theorem prep_kp_5S {w : List (Fin sc)} {S : ℕ} (hS : 8 ≤ S) (hw : S / 2 ≤ w.length) :
    8 * effPeriod ((stagePat w (S / 2)).drop (rawRes w (S / 2)).1)
        (rawRes w (S / 2)).2.1 ≤ 5 * S := by
  by_cases hp : (rawRes w (S / 2)).2.1 = 0
  · rw [effPeriod, if_pos hp, List.length_drop, stagePat_length hw]
    omega
  · have h := prep_kp (w := w) (L := S / 2) hw hp
    omega

/-! ## 4. `stage_tapes_spec'` が要求する事実の束 -/

/-- **主補題 `prep_res_eq`**：`prepRes` を `PrepOnTapes.res` に据えたとき、
`stage_tapes_spec'` の `hres` / `H` / `hs` は成り立ち、`hkp` は `p₁ ≠ 0` と同値。 -/
theorem prep_res_eq (w : List (Fin sc)) (S : ℕ) (hS : 0 < S / 2) (hw : S / 2 ≤ w.length) :
    ∃ s p₁ r,
      prepRes w (S / 2)
          = (s, effPeriod ((stagePat w (S / 2)).drop s) p₁, effReach p₁ r)
        ∧ GSCore (stagePat w (S / 2)) 8 s p₁ r
        ∧ s < S / 2
        ∧ (8 * effPeriod ((stagePat w (S / 2)).drop s) p₁ ≤ S / 2 ↔ p₁ ≠ 0) := by
  refine ⟨(rawRes w (S / 2)).1, (rawRes w (S / 2)).2.1, (rawRes w (S / 2)).2.2,
    rfl, prep_core w (S / 2), prep_cut_lt hS hw, ?_, ?_⟩
  · intro h hp; exact prep_kp_zero_absurd hS hw hp h
  · intro hp; exact prep_kp hw hp

/-- **`prep_res_eq5`**：`StageTapes.stage_tapes_spec'` が現在要求する形の束。
`hkp` は `5 * S` 版なので退化ケースも含めて**無条件**に成り立つ。 -/
theorem prep_res_eq5 (w : List (Fin sc)) (S : ℕ) (hS : 8 ≤ S) (hw : S / 2 ≤ w.length) :
    ∃ s p₁ r,
      prepRes w (S / 2)
          = (s, effPeriod ((stagePat w (S / 2)).drop s) p₁, effReach p₁ r)
        ∧ GSCore (stagePat w (S / 2)) 8 s p₁ r
        ∧ s < S / 2
        ∧ 8 * effPeriod ((stagePat w (S / 2)).drop s) p₁ ≤ 5 * S :=
  ⟨(rawRes w (S / 2)).1, (rawRes w (S / 2)).2.1, (rawRes w (S / 2)).2.2,
    rfl, prep_core w (S / 2), prep_cut_lt (by omega) hw, prep_kp_5S hS hw⟩

/-! ## 5. 仕事量とプログラム長 -/

/-- `decompose2_on_tapes` が与えるプログラム長の上界（`k = 8`）。 -/
def decProgBound (n W : ℕ) : ℕ := 193 * W + (48 * (n + 1)) * (n + 1) + (n + 1)

/-- 周期和の仮説つきの `decompose2Work` の線形上界（`k = 8`）。 -/
theorem prep_work_le {w : List (Fin sc)} {L C₁ : ℕ} (hw : L ≤ w.length)
    (hsum : ∀ b s : ℕ,
      stripLoop2Periods (stagePat w L) 8 b ((stagePat w L).length + 1) s ≤ C₁ * b) :
    decompose2Work (stagePat w L) 8 ≤ (34 * C₁ + 186) * L + 21 := by
  have h := decompose2Work_le (stagePat w L) 8 C₁ (by omega) hsum
  rw [stagePat_length hw] at h
  have : (4 * 8 + 2) * C₁ + 17 * 8 + 50 = 34 * C₁ + 186 := by ring
  omega

/-- **プログラム長**：`decompose2_on_tapes` の上界を `L` と `C₁` で表したもの。
第 2 項が `L` の **2 次**であることに注意（`PrepOnTapes.len_le` の
`Cp * L + Dp` の形にはならない）。 -/
theorem prep_prog_len_le {w : List (Fin sc)} {L C₁ : ℕ} (hw : L ≤ w.length)
    (hsum : ∀ b s : ℕ,
      stripLoop2Periods (stagePat w L) 8 b ((stagePat w L).length + 1) s ≤ C₁ * b) :
    decProgBound L (decompose2Work (stagePat w L) 8)
      ≤ 193 * ((34 * C₁ + 186) * L + 21) + (48 * (L + 1)) * (L + 1) + (L + 1) := by
  have h := prep_work_le hw hsum
  simp only [decProgBound]
  have : 193 * decompose2Work (stagePat w L) 8 ≤ 193 * ((34 * C₁ + 186) * L + 21) :=
    Nat.mul_le_mul_left _ h
  omega

/-! ## 6. `EndToEnd2.gsDec2` 版の分解器インタフェース -/

/-- **`MiddleTapes.DecompOnTapes` の `EndToEnd2.gsDec2` 版**。

`MiddleTapes.DecompOnTapes` は分解 `dec` をパラメータに持つようになったので、本構造は
その `dec := fun y L => EndToEnd2.gsDec2 y 8 L` への特殊化（`toDecompOnTapes` で変換）
にすぎない。`EndToEnd2` の経路（`borderMiddle2` / `EndToEnd2.gsDec2`）が必要とするのは
`decompose2` の**正規化済み**分解である。

`EndToEnd2.gsDec2_fst` により切断位置 `.1` は `decompose2` と一致するので、`pat` / `upat`
の形は素朴版と同一で、`cnt` が載せる周期だけが `(EndToEnd2.gsDec2 y 8 L).2.1` になる。

作業テープ `S1 … S9` は `acts` の前後で空白（`BorderTapes.ScratchBlank`）である。 -/
structure DecompOnTapes2 (sc : ℕ) (blank startSym endSym mark : Fin sc) where
  acts : List (Fin sc) → ℕ → BorderTapes.OvTapes sc → List (BorderTapes.Act sc)
  Cd : ℕ
  Dd : ℕ
  len_le : ∀ (y : List (Fin sc)) (L : ℕ) (ts : BorderTapes.OvTapes sc),
    (acts y L ts).length ≤ Cd * L + Dd
  pat : ∀ (y : List (Fin sc)) (L : ℕ), 1 ≤ L → L ≤ y.length →
    ∀ ts : BorderTapes.OvTapes sc, BorderTapes.ScratchBlank blank ts →
      Tape.SeqView blank (BorderTapes.applyActs blank (acts y L ts) ts).P
        (startSym :: ((y.take L).drop (EndToEnd2.gsDec2 y 8 L).1 ++ [endSym])) 1
  upat : ∀ (y : List (Fin sc)) (L : ℕ), 1 ≤ L → L ≤ y.length →
    ∀ ts : BorderTapes.OvTapes sc, BorderTapes.ScratchBlank blank ts →
      Tape.SeqView blank (BorderTapes.applyActs blank (acts y L ts) ts).U
        (startSym :: ((y.take L).take (EndToEnd2.gsDec2 y 8 L).1 ++ [endSym])) 1
  cnt : ∀ (y : List (Fin sc)) (L : ℕ), 1 ≤ L → L ≤ y.length →
    ∀ ts : BorderTapes.OvTapes sc, BorderTapes.ScratchBlank blank ts →
      Tape.CounterView' blank mark
        (BorderTapes.applyActs blank (acts y L ts) ts).Cnt (EndToEnd2.gsDec2 y 8 L).2.1
  keepX : ∀ (y : List (Fin sc)) (L : ℕ) (ts : BorderTapes.OvTapes sc),
    (BorderTapes.applyActs blank (acts y L ts) ts).X = ts.X
  keepX2 : ∀ (y : List (Fin sc)) (L : ℕ) (ts : BorderTapes.OvTapes sc),
    (BorderTapes.applyActs blank (acts y L ts) ts).X2 = ts.X2
  keepF : ∀ (y : List (Fin sc)) (L : ℕ) (ts : BorderTapes.OvTapes sc),
    (BorderTapes.applyActs blank (acts y L ts) ts).F = ts.F
  keepS : ∀ (y : List (Fin sc)) (L : ℕ) (ts : BorderTapes.OvTapes sc),
    BorderTapes.ScratchBlank blank ts →
      BorderTapes.ScratchBlank blank (BorderTapes.applyActs blank (acts y L ts) ts)

/-- **`DecompOnTapes2` は `DecompOnTapes` の `dec := gsDec2 · 8` への特殊化**。
段の正当性 `decOK` は `EndToEnd2.decOK2` が無条件に与える。 -/
def DecompOnTapes2.toDecompOnTapes {blank startSym endSym mark : Fin sc}
    (D : DecompOnTapes2 sc blank startSym endSym mark) :
    MiddleTapes.DecompOnTapes sc blank startSym endSym mark where
  dec := fun y L => EndToEnd2.gsDec2 y 8 L
  acts := D.acts
  Cd := D.Cd
  Dd := D.Dd
  decOK := fun y L hL => EndToEnd2.decOK2 y L hL
  len_le := D.len_le
  pat := D.pat
  upat := D.upat
  cnt := D.cnt
  keepX := D.keepX
  keepX2 := D.keepX2
  keepF := D.keepF
  keepS := D.keepS

@[simp] theorem DecompOnTapes2.toDecompOnTapes_dec {blank startSym endSym mark : Fin sc}
    (D : DecompOnTapes2 sc blank startSym endSym mark) (y : List (Fin sc)) (L : ℕ) :
    D.toDecompOnTapes.dec y L = EndToEnd2.gsDec2 y 8 L := rfl

/-- 切断位置は正規化で変わらないので、`pat` / `upat` の形は
`MiddleTapes.DecompOnTapes` と同一である。 -/
theorem decomp2_cut_eq (y : List (Fin sc)) (L : ℕ) :
    (EndToEnd2.gsDec2 y 8 L).1 = (decompose2 (y.take L) 8).1 := EndToEnd2.gsDec2_fst y 8 L

/-- 非退化ケースでは `EndToEnd2.gsDec2` と `decompose2` は完全に一致する。 -/
theorem gsDec2_eq_of_ne (y : List (Fin sc)) (L : ℕ)
    (hp : (decompose2 (y.take L) 8).2.1 ≠ 0) :
    EndToEnd2.gsDec2 y 8 L = decompose2 (y.take L) 8 := by
  simp only [EndToEnd2.gsDec2, if_neg hp]

end PrepInstances
end PalPeg
