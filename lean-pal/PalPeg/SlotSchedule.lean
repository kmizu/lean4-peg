import PalPeg.FullMachineTapes

import PalPeg.ProgLang
import PalPeg.ProgLangLib
import PalPeg.TapeLib

/-!
# スロット・スケジュールをテープで駆動する (`SlotSchedule`)

`FullMachineProg.slotSchedule_exec` は仮定

* `hsched : I.condOf cAct (fun j => (Tp j).focus) = (stageInSlot n i).isSome`

を要求し、`FullMachineTapes.stage_birth_pair_sentinel` は再始動スケジュール `rs` に
`hstart` / `hkeep` を要求する。本ファイルはそれらを **テープ駆動の有限制御**
（スロットごとの単進カウンタと相位レジスタ）で与える。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace PalPeg.SlotSchedule

open PalPeg
open PalPeg.FullMachineTapes

/-! ## 1. スロット周期の算術 -/

/-- スロット `i` がラウンド `n` に世話をしている段の指数。
幅 `2 ^ j` の段はスロット `j % 4` を周期 `[2 ^ (j-1), 2 ^ (j+3))` の間占有する
（常駐 `[2^(j-1), 2^(j+2))` ＋ 解放窓 `[2^(j+2), 2^(j+3))`）。 -/
def genExp (n : ℕ) (i : Fin 4) : ℕ :=
  (Nat.log 2 n + 1) - ((Nat.log 2 n + 5 - i.val) % 4)

theorem log_ge_five {n : ℕ} (hn : 32 ≤ n) : 5 ≤ Nat.log 2 n := by
  have h32 : Nat.log 2 32 = 5 := by
    rw [show (32 : ℕ) = 2 ^ 5 from rfl, Nat.log_pow (by omega)]
  have := Nat.log_mono_right (b := 2) hn
  omega

theorem genExp_mod {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) : genExp n i % 4 = i.val := by
  have hL := log_ge_five hn
  have hi := i.isLt
  set L := Nat.log 2 n with hLdef
  have hdm := Nat.div_add_mod (L + 5 - i.val) 4
  set q := (L + 5 - i.val) / 4 with hq
  set d := (L + 5 - i.val) % 4 with hd
  have hd4 : d < 4 := Nat.mod_lt _ (by omega)
  have hq1 : 1 ≤ q := by omega
  have : genExp n i = 4 * (q - 1) + i.val := by
    rw [genExp, ← hLdef, ← hd]
    omega
  rw [this]
  omega

theorem genExp_le {n : ℕ} (i : Fin 4) : genExp n i ≤ Nat.log 2 n + 1 := by
  rw [genExp]; omega

theorem genExp_ge {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) : Nat.log 2 n ≤ genExp n i + 2 := by
  have hd4 : (Nat.log 2 n + 5 - i.val) % 4 < 4 := Nat.mod_lt _ (by omega)
  have hL := log_ge_five hn
  rw [genExp]; omega

theorem genExp_ge_three {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) : 3 ≤ genExp n i := by
  have := genExp_ge hn i
  have := log_ge_five hn
  omega

/-- 冪の窓：`2 ^ (g - 1) ≤ n < 2 ^ (g + 3)`。 -/
theorem genExp_window {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) :
    2 ^ (genExp n i - 1) ≤ n ∧ n < 2 ^ (genExp n i + 3) := by
  have hL := log_ge_five hn
  have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have hle := genExp_le (n := n) i
  have hge := genExp_ge hn i
  constructor
  · exact le_trans (Nat.pow_le_pow_right (by omega) (by omega)) h1
  · exact lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by omega) (by omega))

/-- 窓の一意性：`mod 4` が等しい二つの指数の窓は交わらない。 -/
theorem genExp_unique {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) {g : ℕ}
    (hmod : g % 4 = i.val) (h1 : 2 ^ (g - 1) ≤ n) (h2 : n < 2 ^ (g + 3)) :
    g = genExp n i := by
  have hg := genExp_mod hn i
  have hw := genExp_window hn i
  set g' := genExp n i with hg'
  have key : ∀ a b : ℕ, a + 4 ≤ b → n < 2 ^ (a + 3) → 2 ^ (b - 1) ≤ n → False := by
    intro a b hab ha hb
    have : (2 : ℕ) ^ (a + 3) ≤ 2 ^ (b - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  rcases Nat.lt_trichotomy g g' with h | h | h
  · exact (key g g' (by omega) h2 hw.1).elim
  · exact h
  · exact (key g' g (by omega) hw.2 h1).elim

/-- 現世代の段の幅 `S = 2 ^ g`。 -/
def genWidth (n : ℕ) (i : Fin 4) : ℕ := 2 ^ genExp n i

/-- 四半期 `S / 4 = 2 ^ (g - 2)`（相位の長さ）。 -/
def quarter (n : ℕ) (i : Fin 4) : ℕ := 2 ^ (genExp n i - 2)

/-- 現世代の誕生時刻 `S / 2 = 2 ^ (g - 1)`。 -/
def birth (n : ℕ) (i : Fin 4) : ℕ := 2 ^ (genExp n i - 1)

/-- 誕生からの経過ラウンド数。 -/
def elapsed (n : ℕ) (i : Fin 4) : ℕ := n - birth n i

/-- 相位（四半期の番号、`0 ≤ p < 30`）。 -/
def phaseAt (n : ℕ) (i : Fin 4) : ℕ := elapsed n i / quarter n i

/-- 相位内の残差。 -/
def resAt (n : ℕ) (i : Fin 4) : ℕ := elapsed n i % quarter n i

theorem quarter_pos {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) : 0 < quarter n i :=
  pow_pos (by omega) _

/-- `g = m + 2` の形。 -/
theorem genExp_split {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) : ∃ m, genExp n i = m + 3 :=
  ⟨genExp n i - 3, by have := genExp_ge_three hn i; omega⟩

theorem birth_eq {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) : birth n i = 2 * quarter n i := by
  obtain ⟨m, hm⟩ := genExp_split hn i
  rw [birth, quarter, hm, show m + 3 - 1 = (m + 1) + 1 from by omega,
    show m + 3 - 2 = m + 1 from by omega, Nat.pow_succ]
  ring

theorem width_eq {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) : genWidth n i = 4 * quarter n i := by
  obtain ⟨m, hm⟩ := genExp_split hn i
  rw [genWidth, quarter, hm, show m + 3 - 2 = m + 1 from by omega,
    show m + 3 = (m + 1) + 2 from by omega, Nat.pow_succ, Nat.pow_succ]
  ring

theorem elapsed_lt {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) : elapsed n i < 30 * quarter n i := by
  have h3 := genExp_ge_three hn i
  have hw := genExp_window hn i
  have hb := birth_eq hn i
  obtain ⟨m, hm⟩ := genExp_split hn i
  have h32 : (2 : ℕ) ^ (genExp n i + 3) = 32 * quarter n i := by
    rw [quarter, hm, show m + 3 - 2 = m + 1 from by omega,
      show m + 3 + 3 = (m + 1) + 5 from by omega, Nat.pow_add]
    ring
  rw [elapsed, hb]
  have hb' : 2 * quarter n i ≤ n := by rw [← hb]; exact hw.1
  omega

theorem phase_lt_thirty {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) : phaseAt n i < 30 := by
  have hq := quarter_pos hn i
  have he := elapsed_lt hn i
  rw [phaseAt]
  exact Nat.div_lt_of_lt_mul (by omega)

theorem elapsed_decomp {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) :
    elapsed n i = phaseAt n i * quarter n i + resAt n i := by
  rw [phaseAt, resAt, Nat.div_add_mod' (elapsed n i) (quarter n i)]

theorem res_lt {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) : resAt n i < quarter n i :=
  Nat.mod_lt _ (quarter_pos hn i)

theorem n_eq {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) :
    n = 2 * quarter n i + phaseAt n i * quarter n i + resAt n i := by
  have hb := birth_eq hn i
  have hw := genExp_window hn i
  have hb' : 2 * quarter n i ≤ n := by rw [← hb]; exact hw.1
  have := elapsed_decomp hn i
  rw [elapsed, hb] at this
  omega

/-! ## 2. スロット状態と 1 ラウンドの更新 -/

/-- **スロットの有限制御状態**。実装ではすべて単進カウンタ（`Tape.CounterView'`）と
30 値の相位レジスタである。

* `q` … 四半期 `S / 4`（相位 1 つの長さ）。実装では二本の counter `A`, `B` が
  「残り `q - r`」と「経過 `r`」を持ち、相位境界で役割を交換するので、
  複製なしで保たれる。
* `r` … 相位内の残差（`0 ≤ r < q`）。
* `p` … 相位番号（`0 ≤ p < 30`。`p < 14` が常駐、`14 ≤ p` が解放窓）。
* `nx` … 次世代の四半期を作りかけの counter。解放窓（`14 ≤ p`、16 相位 ＝ `16 * q`
  ラウンド）に毎ラウンド 1 回 `inc` するので、窓の終わりでちょうど `16 * q`
  ＝ 次世代の四半期になる。 -/
structure SlotSt where
  /-- 四半期の長さ。 -/
  q : ℕ
  /-- 相位内の残差。 -/
  r : ℕ
  /-- 相位番号。 -/
  p : ℕ
  /-- 次世代四半期の作りかけ。 -/
  nx : ℕ
deriving DecidableEq, Repr

/-- **1 ラウンドの更新**（毎ラウンド定数動作）。

1. 残差を 1 進める。相位境界（`r + 1 = q`）でなければそれだけ。
2. 境界なら相位を 1 進め、残差を `0` に戻す（counter の役割交換）。
3. 相位が `30` に達したら **世代交代**：四半期を `nx`（＝ `16 * q`）に置き換え、
   相位・残差・`nx` を `0` に戻す。
4. 解放窓（`14 ≤ p`）では毎ラウンド `nx` を 1 つ伸ばす。 -/
def slotStep (s : SlotSt) : SlotSt :=
  let nx' := if 14 ≤ s.p then s.nx + 1 else 0
  if s.r + 1 < s.q then { s with r := s.r + 1, nx := nx' }
  else if s.p + 1 < 30 then { s with r := 0, p := s.p + 1, nx := nx' }
  else { q := nx', r := 0, p := 0, nx := 0 }

/-- ラウンド `n` におけるスロット `i` の正準状態。 -/
def canonSlot (n : ℕ) (i : Fin 4) : SlotSt :=
  { q := quarter n i, r := resAt n i, p := phaseAt n i,
    nx := if 14 ≤ phaseAt n i then (phaseAt n i - 14) * quarter n i + resAt n i else 0 }

/-- 相位・残差の特徴づけ（`m = 2 * Q + P * Q + R`, `R < Q`）。 -/
theorem phase_res_eq {m : ℕ} (hm : 32 ≤ m) (i : Fin 4) {P R : ℕ}
    (h : m = 2 * quarter m i + P * quarter m i + R) (hR : R < quarter m i) :
    phaseAt m i = P ∧ resAt m i = R := by
  have hq := quarter_pos hm i
  have hb := birth_eq hm i
  have he : elapsed m i = quarter m i * P + R := by
    rw [elapsed, hb]
    have : P * quarter m i = quarter m i * P := Nat.mul_comm _ _
    omega
  rw [phaseAt, resAt, he]
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_div hq, Nat.div_eq_of_lt hR]
    omega
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hR]

/-- 四半期が同じ世代のままであることの十分条件。 -/
theorem genExp_same {n : ℕ} (hn : 32 ≤ n) (hn1 : 32 ≤ n + 1) (i : Fin 4)
    (h2 : n + 1 < 2 ^ (genExp n i + 3)) : genExp (n + 1) i = genExp n i := by
  have hw := genExp_window hn i
  exact (genExp_unique hn1 i (genExp_mod hn i) (by omega) h2).symm

/-- **正準状態の 1 ラウンド更新**：`slotStep` はちょうど正準状態を進める。 -/
theorem canonSlot_step {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) :
    slotStep (canonSlot n i) = canonSlot (n + 1) i := by
  have hn1 : 32 ≤ n + 1 := by omega
  have hq := quarter_pos hn i
  have hr := res_lt hn i
  have hp := phase_lt_thirty hn i
  have hne := n_eq hn i
  obtain ⟨m, hm⟩ := genExp_split hn i
  have hq32 : (2 : ℕ) ^ (genExp n i + 3) = 32 * quarter n i := by
    rw [quarter, hm, show m + 3 - 2 = m + 1 from by omega,
      show m + 3 + 3 = (m + 1) + 5 from by omega, Nat.pow_add]
    ring
  by_cases hb : resAt n i + 1 < quarter n i
  · -- 相位内で残差が進むだけ
    have hlt : n + 1 < 2 ^ (genExp n i + 3) := by
      rw [hq32]
      nlinarith [hne, hp, hb, hq]
    have hg := genExp_same hn hn1 i hlt
    have hQ : quarter (n + 1) i = quarter n i := by rw [quarter, quarter, hg]
    have hd := phase_res_eq hn1 i (P := phaseAt n i) (R := resAt n i + 1)
      (by rw [hQ]; omega) (by rw [hQ]; omega)
    simp only [slotStep, canonSlot, hQ, hd.1, hd.2, if_pos hb]
    by_cases h14 : 14 ≤ phaseAt n i
    · simp only [if_pos h14, Nat.add_assoc]
    · simp only [if_neg h14]
  by_cases hp29 : phaseAt n i + 1 < 30
  · -- 相位境界
    have hlt : n + 1 < 2 ^ (genExp n i + 3) := by
      rw [hq32]
      nlinarith [hne, hp29, hr, hq, hb]
    have hg := genExp_same hn hn1 i hlt
    have hQ : quarter (n + 1) i = quarter n i := by rw [quarter, quarter, hg]
    have hd := phase_res_eq hn1 i (P := phaseAt n i + 1) (R := 0)
      (by rw [hQ]; nlinarith [hne, hr, hb]) (by rw [hQ]; omega)
    simp only [slotStep, canonSlot, hQ, hd.1, hd.2, if_neg hb, if_pos hp29]
    by_cases h14 : 14 ≤ phaseAt n i
    · simp only [if_pos h14, if_pos (show 14 ≤ phaseAt n i + 1 from by omega)]
      have hmul : (phaseAt n i + 1 - 14) * quarter n i
          = (phaseAt n i - 14) * quarter n i + quarter n i := by
        rw [show phaseAt n i + 1 - 14 = (phaseAt n i - 14) + 1 from by omega]
        ring
      simp only [hmul]
      congr 1
      omega
    · have h13 : phaseAt n i + 1 ≤ 14 := by omega
      rcases Nat.lt_or_ge (phaseAt n i + 1) 14 with h | h
      · simp only [if_neg h14, if_neg (show ¬ 14 ≤ phaseAt n i + 1 from by omega)]
      · have he : phaseAt n i + 1 = 14 := by omega
        simp only [if_neg h14, he]
        simp
  · -- 世代交代
    have hp29' : phaseAt n i = 29 := by omega
    have hn1eq : n + 1 = 32 * quarter n i := by
      rw [hp29'] at hne; omega
    have hgnew : genExp (n + 1) i = genExp n i + 4 := by
      refine (genExp_unique hn1 i (by rw [Nat.add_mod, genExp_mod hn i]; omega) ?_ ?_).symm
      · rw [show genExp n i + 4 - 1 = genExp n i + 3 from by omega, hq32, hn1eq]
      · have hqm : quarter n i = 2 ^ (m + 1) := by
          rw [quarter, hm, show m + 3 - 2 = m + 1 from by omega]
        have h32q : 32 * quarter n i = 2 ^ (m + 6) := by
          rw [hqm, show m + 6 = (m + 1) + 5 from by omega, Nat.pow_add]; ring
        have hlt2 : (2:ℕ) ^ (m + 6) < 2 ^ (genExp n i + 4 + 3) := by
          refine Nat.pow_lt_pow_right (by omega) ?_
          omega
        omega
    have hQ : quarter (n + 1) i = 16 * quarter n i := by
      rw [quarter, quarter, hgnew, hm, show m + 3 - 2 = m + 1 from by omega,
        show m + 3 + 4 - 2 = (m + 1) + 4 from by omega, Nat.pow_add]
      ring
    have hd := phase_res_eq hn1 i (P := 0) (R := 0)
      (by rw [hQ]; omega) (by rw [hQ]; omega)
    have hnx : (phaseAt n i - 14) * quarter n i + resAt n i + 1 = 16 * quarter n i := by
      rw [hp29']
      have : (29 - 14) * quarter n i = 15 * quarter n i := by norm_num
      omega
    simp only [slotStep, canonSlot, hQ, hd.1, hd.2, if_neg hb, if_neg hp29,
      if_pos (show 14 ≤ phaseAt n i from by omega)]
    refine SlotSt.mk.injEq .. ▸ ?_
    simp only [hnx]
    simp

/-! ## 3. 相位から読む三つの判定 -/

/-- 常駐判定は相位が `14` 未満であること。 -/
def activeAt (n : ℕ) (i : Fin 4) : Bool := decide (phaseAt n i < 14)

theorem resident_iff_phase {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) :
    n < 4 * genWidth n i ↔ phaseAt n i < 14 := by
  have hq := quarter_pos hn i
  have hr := res_lt hn i
  have hne := n_eq hn i
  have hw := width_eq hn i
  rw [hw]
  constructor
  · intro h
    by_contra hc
    have h14 : 14 ≤ phaseAt n i := by omega
    have : 14 * quarter n i ≤ phaseAt n i * quarter n i :=
      Nat.mul_le_mul_right _ h14
    omega
  · intro h
    have h13 : phaseAt n i ≤ 13 := by omega
    have : phaseAt n i * quarter n i ≤ 13 * quarter n i :=
      Nat.mul_le_mul_right _ h13
    omega

theorem residentStages_eq {n : ℕ} (hn : 32 ≤ n) :
    residentStages n = [2 ^ (Nat.log 2 n - 1), 2 ^ Nat.log 2 n, 2 ^ (Nat.log 2 n + 1)] := by
  have hL := log_ge_five hn
  have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by omega) n
  set L := Nat.log 2 n with hLdef
  obtain ⟨m, hm⟩ : ∃ m, L = m + 5 := ⟨L - 5, by omega⟩
  have e1 : (2:ℕ) ^ (L - 1) / 2 = 2 ^ (L - 2) := by
    rw [hm, show m + 5 - 1 = (m + 3) + 1 from by omega,
      show m + 5 - 2 = m + 3 from by omega, Nat.pow_succ]
    omega
  have e2 : (2:ℕ) ^ L / 2 = 2 ^ (L - 1) := by
    rw [hm, show m + 5 = (m + 4) + 1 from by omega,
      show m + 4 + 1 - 1 = m + 4 from by omega, Nat.pow_succ]
    omega
  have e3 : (2:ℕ) ^ (L + 1) / 2 = 2 ^ L := by
    rw [Nat.pow_succ]; omega
  have m1 : (2:ℕ) ^ (L - 2) ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) (by omega)
  have m2 : (2:ℕ) ^ (L - 1) ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) (by omega)
  have f1 : 4 * (2:ℕ) ^ (L - 1) = 2 ^ (L + 1) := by
    rw [hm, show m + 5 - 1 = m + 4 from by omega,
      show m + 5 + 1 = (m + 4) + 2 from by omega, Nat.pow_add]
    ring
  have f2 : (2:ℕ) ^ (L + 1) ≤ 4 * 2 ^ L := by
    rw [Nat.pow_succ]; omega
  have f3 : (2:ℕ) ^ (L + 1) ≤ 4 * 2 ^ (L + 1) := by omega
  have d1 : ((2:ℕ) ^ (L - 1) / 2 ≤ n ∧ n < 4 * 2 ^ (L - 1)) := by omega
  have d2 : ((2:ℕ) ^ L / 2 ≤ n ∧ n < 4 * 2 ^ L) := by omega
  have d3 : ((2:ℕ) ^ (L + 1) / 2 ≤ n ∧ n < 4 * 2 ^ (L + 1)) := by omega
  rw [residentStages]
  simp only [← hLdef]
  rw [List.filter_cons_of_pos (by simpa using d1),
    List.filter_cons_of_pos (by simpa using d2),
    List.filter_cons_of_pos (by simpa using d3), List.filter_nil]

/-- **常駐スロットの判定**：`stageInSlot n i` が `some` であることは、
相位レジスタが `14` 未満を指していることと同値。 -/
theorem stageInSlot_isSome {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) :
    (stageInSlot n i).isSome = activeAt n i := by
  have hL := log_ge_five hn
  have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have hmod := genExp_mod hn i
  have hle := genExp_le (n := n) i
  have hge := genExp_ge hn i
  have hw := genExp_window hn i
  set L := Nat.log 2 n with hLdef
  set g := genExp n i with hgdef
  -- 相位 < 14 ⟺ g ≠ L - 2
  have hphase : phaseAt n i < 14 ↔ L - 1 ≤ g := by
    rw [← resident_iff_phase hn i, genWidth, ← hgdef]
    constructor
    · intro h
      by_contra hc
      have hgL : g ≤ L - 2 := by omega
      have : (4:ℕ) * 2 ^ g ≤ 4 * 2 ^ (L - 2) := by
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hgL)
      have h4 : 4 * (2:ℕ) ^ (L - 2) = 2 ^ L := by
        have hLL : L - 2 + 2 = L := by omega
        calc 4 * (2:ℕ) ^ (L - 2) = 2 ^ (L - 2) * 2 ^ 2 := by ring
          _ = 2 ^ (L - 2 + 2) := (Nat.pow_add 2 (L - 2) 2).symm
          _ = 2 ^ L := by rw [hLL]
      omega
    · intro h
      have : (2:ℕ) ^ (L + 1) ≤ 4 * 2 ^ g := by
        have : (2:ℕ) ^ (L + 1) ≤ 2 ^ (g + 2) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        rw [show g + 2 = g + 1 + 1 from rfl, Nat.pow_succ, Nat.pow_succ] at this
        omega
      omega
  have hpow : ∀ m : ℕ, (decide (slotOf (2 ^ m) = i.val) = true) ↔ m % 4 = i.val := by
    intro m
    rw [slotOf_pow]
    simp
  rw [activeAt, stageInSlot, residentStages_eq hn]
  by_cases hA : (Nat.log 2 n - 1) % 4 = i.val
  · have hgA : g = L - 1 := by rw [hgdef]; exact (genExp_unique hn i hA
      (le_trans (Nat.pow_le_pow_right (by omega) (by omega)) h1)
      (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by omega) (by omega)))).symm
    rw [List.find?_cons_of_pos (p := fun S => decide (slotOf S = i.val)) ((hpow (Nat.log 2 n - 1)).2 hA)]
    symm
    simp only [Option.isSome_some, decide_eq_true_eq]
    rw [hphase]
    omega
  · rw [List.find?_cons_of_neg (p := fun S => decide (slotOf S = i.val)) (by rw [hpow]; exact hA)]
    by_cases hB : Nat.log 2 n % 4 = i.val
    · have hgB : g = L := by rw [hgdef]; exact (genExp_unique hn i hB
        (le_trans (Nat.pow_le_pow_right (by omega) (by omega)) h1)
        (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by omega) (by omega)))).symm
      rw [List.find?_cons_of_pos (p := fun S => decide (slotOf S = i.val)) ((hpow (Nat.log 2 n)).2 hB)]
      symm
      simp only [Option.isSome_some, decide_eq_true_eq]
      rw [hphase]
      omega
    · rw [List.find?_cons_of_neg (p := fun S => decide (slotOf S = i.val)) (by rw [hpow]; exact hB)]
      by_cases hC : (Nat.log 2 n + 1) % 4 = i.val
      · have hgC : g = L + 1 := by rw [hgdef]; exact (genExp_unique hn i hC
          (le_trans (Nat.pow_le_pow_right (by omega) (by omega)) h1)
          (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by omega) (by omega)))).symm
        rw [List.find?_cons_of_pos (p := fun S => decide (slotOf S = i.val)) ((hpow (Nat.log 2 n + 1)).2 hC)]
        symm
        simp only [Option.isSome_some, decide_eq_true_eq]
        rw [hphase]
        omega
      · rw [List.find?_cons_of_neg (p := fun S => decide (slotOf S = i.val)) (by rw [hpow]; exact hC)]
        have hgD : g = L - 2 := by omega
        symm
        simp only [List.find?_nil, Option.isSome_none, decide_eq_false_iff_not]
        rw [hphase]
        omega

/-! ## 4. 再始動スケジュール `rsCanon` -/

/-- **正準の再始動スケジュール**：スロット `i` は、そのスロットに入る段 `S = 2 ^ j`
（`j % 4 = i`）のパターン最前線テープを作り始めるラウンド `S / 4 + 1` に再始動する。 -/
def rsCanon (n : ℕ) (i : Fin 4) : Bool :=
  decide (∃ j ≤ n, 2 ≤ j ∧ j % 4 = i.val ∧ n = 2 ^ j / 4 + 1)

theorem pow_div_four {j : ℕ} (hj : 2 ≤ j) : 2 ^ j / 4 = 2 ^ (j - 2) := by
  obtain ⟨m, hm⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  subst hm
  rw [show m + 2 - 2 = m from by omega, Nat.pow_add]
  omega

theorem self_le_two_pow (m : ℕ) : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self

/-- `stage_birth_pair_sentinel` の `hstart`。 -/
theorem rsCanon_start {j : ℕ} (hj : 2 ≤ j) (i : Fin 4) (hi : slotOf (2 ^ j) = i.val) :
    rsCanon (2 ^ j / 4 + 1) i = true := by
  have hmod : j % 4 = i.val := by rw [← hi, slotOf_pow]
  have hle : j ≤ 2 ^ j / 4 + 1 := by
    rw [pow_div_four hj]
    have := self_le_two_pow (j - 2)
    omega
  rw [rsCanon, decide_eq_true_iff]
  exact ⟨j, hle, hj, hmod, rfl⟩

/-- `stage_birth_pair_sentinel` の `hkeep`。 -/
theorem rsCanon_keep {j : ℕ} (hj : 4 ≤ j) (i : Fin 4) (hi : slotOf (2 ^ j) = i.val) :
    ∀ r, 2 ^ j / 4 + 1 < r → r ≤ 2 ^ j / 2 → rsCanon r i = false := by
  intro r hr1 hr2
  have hmod : j % 4 = i.val := by rw [← hi, slotOf_pow]
  rw [rsCanon, decide_eq_false_iff_not]
  rintro ⟨j', hj'le, hj'2, hj'mod, rfl⟩
  have hd : 2 ^ j' / 4 = 2 ^ (j' - 2) := pow_div_four hj'2
  have hd2 : 2 ^ j / 4 = 2 ^ (j - 2) := pow_div_four (by omega)
  have hhalf : 2 ^ j / 2 = 2 ^ (j - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    subst hm
    rw [show m + 1 - 1 = m from by omega, Nat.pow_succ]
    omega
  rw [hd] at hr1 hr2
  rw [hd2] at hr1
  rw [hhalf] at hr2
  rcases Nat.lt_trichotomy j' j with h | h | h
  · have h4 : j' + 4 ≤ j := by omega
    have : (2:ℕ) ^ (j' - 2) ≤ 2 ^ (j - 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · subst h; omega
  · have h4 : j + 4 ≤ j' := by omega
    have : (2:ℕ) ^ (j - 1) < 2 ^ (j' - 2) := Nat.pow_lt_pow_right (by omega) (by omega)
    omega

/-- **再始動判定は相位から読める**：`rsCanon n i` は「相位 `14` の第 1 ラウンド」。 -/
theorem rsCanon_iff_phase {n : ℕ} (hn : 32 ≤ n) (i : Fin 4) :
    rsCanon n i = decide (phaseAt n i = 14 ∧ resAt n i = 1) := by
  have hq := quarter_pos hn i
  have hr := res_lt hn i
  have hne := n_eq hn i
  have hmodg := genExp_mod hn i
  have h3 := genExp_ge_three hn i
  rw [Bool.eq_iff_iff, rsCanon, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨j, hjle, hj2, hjmod, hnv⟩
    have hd : 2 ^ j / 4 = 2 ^ (j - 2) := pow_div_four hj2
    rw [hd] at hnv
    have hj7 : 7 ≤ j := by
      by_contra hc
      have : (2:ℕ) ^ (j - 2) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hgen : genExp n i = j - 4 := by
      refine (genExp_unique hn i (show (j - 4) % 4 = i.val by
        obtain ⟨m, hm⟩ : ∃ m, j = m + 4 := ⟨j - 4, by omega⟩
        subst hm
        rw [show m + 4 - 4 = m from by omega]
        rw [Nat.add_mod_right] at hjmod
        exact hjmod) ?_ ?_).symm
      · have hstep : (2:ℕ) ^ (j - 4 - 1) ≤ 2 ^ (j - 2) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        omega
      · have hs2 : (2:ℕ) ^ (j - 2) * 2 = 2 ^ (j - 1) := by
          rw [← Nat.pow_succ]; congr 1; omega
        have hs3 : (2:ℕ) ^ (j - 4 + 3) = 2 ^ (j - 1) := by congr 1; omega
        have hs4 : 1 ≤ (2:ℕ) ^ (j - 2) := Nat.one_le_two_pow
        rw [hnv, hs3]
        omega
    have hQ : quarter n i = 2 ^ (j - 6) := by
      rw [quarter, hgen, show j - 4 - 2 = j - 6 from by omega]
    have h16 : (2:ℕ) ^ (j - 2) = 16 * 2 ^ (j - 6) := by
      rw [show j - 2 = (j - 6) + 4 from by omega, Nat.pow_add]; ring
    have hq2 : 2 ≤ quarter n i := by
      rw [hQ]
      have : (2:ℕ) ^ 1 ≤ 2 ^ (j - 6) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hform : n = 2 * quarter n i + 14 * quarter n i + 1 := by
      rw [hQ, hnv, h16]; ring
    have := phase_res_eq hn i (P := 14) (R := 1) hform (by omega)
    exact this
  · rintro ⟨hp, hrr⟩
    refine ⟨genExp n i + 4, ?_, by omega,
      (by rw [Nat.add_mod_right]; exact hmodg), ?_⟩
    · have hqge : (2:ℕ) ^ (genExp n i - 2) ≥ genExp n i - 1 := by
        have := self_le_two_pow (genExp n i - 2)
        omega
      have : quarter n i = 2 ^ (genExp n i - 2) := rfl
      omega
    · have hd : 2 ^ (genExp n i + 4) / 4 = 2 ^ (genExp n i + 2) := by
        rw [pow_div_four (by omega), show genExp n i + 4 - 2 = genExp n i + 2 from by omega]
      have h16 : (2:ℕ) ^ (genExp n i + 2) = 16 * quarter n i := by
        rw [quarter, show genExp n i + 2 = (genExp n i - 2) + 4 from by omega, Nat.pow_add]
        ring
      rw [hp, hrr] at hne
      rw [hd, h16]
      omega

/-- `FullMachineTapes.stage_birth_pair_sentinel` をそのまま `rsCanon` で使える形。 -/
theorem stage_birth_pair_sentinel_canon {sc : ℕ} {w : List (Fin sc)}
    {blank leftSym : Fin sc} {I : StageIface sc w} {init : FullT sc}
    (hb : Tape.StackView blank init.blankT []) {i : Fin 4} {j : ℕ} (hj : 4 ≤ j)
    (hi : slotOf (2 ^ j) = i.val) (hn : 2 ^ j / 2 ≤ w.length)
    {tpFrozen : PegSeparation.RealTimeTM.TapeConfiguration sc}
    (hfrozen : InputCopy.FrontierView blank tpFrozen (leftSym :: w.take (2 ^ j / 4))) :
    InputCopy.FrontierView blank
        ((FullMachineTapes.fullState blank leftSym rsCanon I init (2 ^ j / 2)).cpy i)
        (leftSym :: ((w.take (2 ^ j / 2)).drop (2 ^ j / 4)))
      ∧ InputCopy.FrontierView blank tpFrozen (leftSym :: w.take (2 ^ j / 4))
      ∧ w.take (2 ^ j / 4) ++ (w.take (2 ^ j / 2)).drop (2 ^ j / 4) = w.take (2 ^ j / 2) := by
  have h4 : 4 ≤ 2 ^ j := by
    have : (2:ℕ) ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    simpa using this
  exact stage_birth_pair_sentinel hb h4 (rsCanon_start (by omega) i hi)
    (rsCanon_keep hj i hi) hn hfrozen

/-! ## 5. テープ層：相位レジスタと単進カウンタ -/

section Machine

open PalPeg.Program
open PalPeg.ProgLang

variable {Terminal A C Γ : Type} {t : ℕ}

/-- **スケジューラのテープ実装インタフェース**。

スロット `i` ごとに 5 本、加えて若年テーブル 1 本の計 **21 本**のテープを使う：

* `phase i` … 相位レジスタ（1 セル、`30` 個の記号）。`activeAt` と再始動の判定は
  この記号（と下の再始動印）から読む。
* `ctrA i`, `ctrB i` … 二本の単進カウンタ（`Tape.CounterView'`）。片方が
  「残り `q - r`」、他方が「経過 `r`」を持ち、相位境界（`ctrA` が `0` になる瞬間、
  `Tape.counter'_isZero_iff` で検出）で役割を交換する。複製が要らないので
  1 ラウンド定数動作で済む。
* `ctrN i` … 次世代の四半期を作りかけのカウンタ。解放窓（相位 `14` 以上、
  `16` 相位 ＝ `16 * q` ラウンド）に毎ラウンド 1 回 `inc` するので、
  窓の終わりでちょうど `16 * q`（＝ 次世代の四半期）になり、世代交代で
  `ctrA` の役割へ回る。役割から外れたカウンタは、次世代の相位 `0`–`13`
  （`14 * 16 * q` ラウンド）の間に毎ラウンド 1 歩ずつ左へ戻して空にする。
* `rst i` … 再始動印（1 セル）。
* `young` … 若年ラウンド用の単進カウンタ（`n < 32` の間は `n` を数え、
  `32` に達したら恒久的な印を書く）。

これらのテープ操作（`inc` / `probe` / 記号の書き換え）が動作識別子として
用意されていることが、本構造の仮定である（`StageIface` と同じ層のインタフェース）。 -/
structure SchedOps (I : Interp Terminal A C Γ t) (blank : Γ) where
  /-- スロット `i` の 5 本のテープが状態 `s` を符号化していること。 -/
  slotEnc : Fin 4 → SlotSt → (Fin t → STape Γ) → Prop
  /-- 若年テープがラウンド番号 `m` を符号化していること。 -/
  youngEnc : ℕ → (Fin t → STape Γ) → Prop
  /-- 「スロット `i` に段が常駐している」を読む条件識別子。 -/
  cActive : Fin 4 → C
  /-- 「スロット `i` を再始動する」を読む条件識別子。 -/
  cRestart : Fin 4 → C
  /-- 「まだ若年ラウンド（`n < 32`）」を読む条件識別子。 -/
  cYoung : C
  /-- スロット `i` の 1 ラウンドプログラム。 -/
  slotProg : Fin 4 → Prog A C
  /-- 若年テープの 1 ラウンドプログラム。 -/
  youngProg : Prog A C
  /-- 1 スロット 1 ラウンドのマイクロステップ上界。 -/
  K : ℕ
  /-- 相位レジスタから常駐判定が読める。 -/
  active_read : ∀ (i : Fin 4) (s : SlotSt) (Tp : Fin t → STape Γ), slotEnc i s Tp →
    I.condOf (cActive i) (fun j => (Tp j).focus) = decide (s.p < 14)
  /-- 再始動印から再始動判定が読める。 -/
  restart_read : ∀ (i : Fin 4) (s : SlotSt) (Tp : Fin t → STape Γ), slotEnc i s Tp →
    I.condOf (cRestart i) (fun j => (Tp j).focus) = decide (s.p = 14 ∧ s.r = 1)
  /-- 若年テープから `n < 32` が読める。 -/
  young_read : ∀ (m : ℕ) (Tp : Fin t → STape Γ), youngEnc m Tp →
    I.condOf cYoung (fun j => (Tp j).focus) = decide (m < 32)
  /-- スロットの 1 ラウンド：`slotStep` を実現し、他の区画を壊さない。 -/
  slot_exec : ∀ (i : Fin 4) (s : SlotSt) (Tp : Fin t → STape Γ), slotEnc i s Tp →
    ∃ acts, Exec I blank (slotProg i) Tp acts ∧ acts.length ≤ K ∧
      slotEnc i (slotStep s) (applyTrace blank Tp acts) ∧
      (∀ i' s', i' ≠ i → slotEnc i' s' Tp → slotEnc i' s' (applyTrace blank Tp acts)) ∧
      (∀ m, youngEnc m Tp → youngEnc m (applyTrace blank Tp acts))
  /-- 若年テープの 1 ラウンド：計数を 1 進め、他の区画を壊さない。 -/
  young_exec : ∀ (m : ℕ) (Tp : Fin t → STape Γ), youngEnc m Tp →
    ∃ acts, Exec I blank youngProg Tp acts ∧ acts.length ≤ K ∧
      youngEnc (m + 1) (applyTrace blank Tp acts) ∧
      (∀ i s, slotEnc i s Tp → slotEnc i s (applyTrace blank Tp acts))

variable {I : Interp Terminal A C Γ t} {blank : Γ}

/-- **スケジューラの不変条件**：4 つのスロットの符号化が正準状態であり、
若年テープがラウンド番号を持つ。 -/
def SchedInv (O : SchedOps I blank) (n : ℕ) (Tp : Fin t → STape Γ) : Prop :=
  (∀ i : Fin 4, O.slotEnc i (canonSlot n i) Tp) ∧ O.youngEnc n Tp

/-- **`slotSchedule_exec` の `hsched` を与える**。 -/
theorem sched_stageInSlot (O : SchedOps I blank) {n : ℕ} (hn : 32 ≤ n)
    {Tp : Fin t → STape Γ} (h : SchedInv O n Tp) (i : Fin 4) :
    I.condOf (O.cActive i) (fun j => (Tp j).focus) = (stageInSlot n i).isSome := by
  rw [O.active_read i (canonSlot n i) Tp (h.1 i), stageInSlot_isSome hn i, activeAt]
  rfl

/-- **再始動の判定**：相位から `rsCanon` が読める。 -/
theorem sched_restart (O : SchedOps I blank) {n : ℕ} (hn : 32 ≤ n)
    {Tp : Fin t → STape Γ} (h : SchedInv O n Tp) (i : Fin 4) :
    I.condOf (O.cRestart i) (fun j => (Tp j).focus) = rsCanon n i := by
  rw [O.restart_read i (canonSlot n i) Tp (h.1 i), rsCanon_iff_phase hn i]
  rfl

/-- **若年ラウンドの判定**：`n < 32` の素朴表が使えることを読む。 -/
theorem sched_young (O : SchedOps I blank) {n : ℕ}
    {Tp : Fin t → STape Γ} (h : SchedInv O n Tp) :
    I.condOf O.cYoung (fun j => (Tp j).focus) = decide (n < 32) :=
  O.young_read n Tp h.2

/-- **スケジューラの 1 ラウンドプログラム**（4 スロット ＋ 若年テープ、数値定数なし）。 -/
def schedRoundProg (O : SchedOps I blank) : Prog A C :=
  Prog.seq (O.slotProg 0)
    (Prog.seq (O.slotProg 1)
      (Prog.seq (O.slotProg 2)
        (Prog.seq (O.slotProg 3) O.youngProg)))

/-- 1 ラウンドのマイクロステップ上界。 -/
def Csched (O : SchedOps I blank) : ℕ := 5 * O.K

/-- **スケジューラの 1 ラウンド**：不変条件を保ちながら `Csched` 動作以内で走る。 -/
theorem schedRound_exec (O : SchedOps I blank) {n : ℕ} (hn : 32 ≤ n)
    {Tp : Fin t → STape Γ} (h : SchedInv O n Tp) :
    ∃ acts, Exec I blank (schedRoundProg O) Tp acts ∧ acts.length ≤ Csched O ∧
      SchedInv O (n + 1) (applyTrace blank Tp acts) := by
  obtain ⟨hslot, hyoung⟩ := h
  -- スロット 0
  obtain ⟨a0, hE0, hL0, hS0, hO0, hY0⟩ := O.slot_exec 0 _ Tp (hslot 0)
  set T1 := applyTrace blank Tp a0 with hT1
  have h1slot : ∀ i : Fin 4, i ≠ 0 → O.slotEnc i (canonSlot n i) T1 :=
    fun i hi => hO0 i _ hi (hslot i)
  obtain ⟨a1, hE1, hL1, hS1, hO1, hY1⟩ := O.slot_exec 1 _ T1 (h1slot 1 (by decide))
  set T2 := applyTrace blank T1 a1 with hT2
  obtain ⟨a2, hE2, hL2, hS2, hO2, hY2⟩ := O.slot_exec 2 _ T2
    (hO1 2 _ (by decide) (h1slot 2 (by decide)))
  set T3 := applyTrace blank T2 a2 with hT3
  obtain ⟨a3, hE3, hL3, hS3, hO3, hY3⟩ := O.slot_exec 3 _ T3
    (hO2 3 _ (by decide) (hO1 3 _ (by decide) (h1slot 3 (by decide))))
  set T4 := applyTrace blank T3 a3 with hT4
  obtain ⟨a4, hE4, hL4, hS4, hO4⟩ := O.young_exec n T4
    (hY3 n (hY2 n (hY1 n (hY0 n hyoung))))
  set T5 := applyTrace blank T4 a4 with hT5
  refine ⟨a0 ++ (a1 ++ (a2 ++ (a3 ++ a4))), ?_, ?_, ?_, ?_⟩
  · refine exec_seq hE0 ?_
    rw [← hT1]
    refine exec_seq hE1 ?_
    rw [← hT2]
    refine exec_seq hE2 ?_
    rw [← hT3]
    refine exec_seq hE3 ?_
    rw [← hT4]
    exact hE4
  · simp only [List.length_append, Csched]
    omega
  · intro i
    rw [applyTrace_append, applyTrace_append, applyTrace_append, applyTrace_append,
      ← hT1, ← hT2, ← hT3, ← hT4, ← hT5]
    rw [← canonSlot_step hn i]
    fin_cases i
    · exact hO4 _ _ (hO3 _ _ (by decide) (hO2 _ _ (by decide) (hO1 _ _ (by decide) hS0)))
    · exact hO4 _ _ (hO3 _ _ (by decide) (hO2 _ _ (by decide) hS1))
    · exact hO4 _ _ (hO3 _ _ (by decide) hS2)
    · exact hO4 _ _ hS3
  · rw [applyTrace_append, applyTrace_append, applyTrace_append, applyTrace_append,
      ← hT1, ← hT2, ← hT3, ← hT4, ← hT5]
    exact hS4

end Machine

end PalPeg.SlotSchedule

#print axioms PalPeg.SlotSchedule.canonSlot_step
#print axioms PalPeg.SlotSchedule.stage_birth_pair_sentinel_canon
#print axioms PalPeg.SlotSchedule.schedRound_exec
