import PalPeg.StageMatcherTapes
import PalPeg.GSVerifierProgX
import PalPeg.GSVerifierFused
import PalPeg.Metered
import PalPeg.ProgLang
import PalPeg.ProgLangLib

/-!
# 走査段（matcher フェーズ）の **有限制御プログラム版** (`StageMatcherProg`)

`PalPeg.StageMatcherTapes` は 1 歩の動作列 `GSVTapes.vprogram'` を計量式
スケジューラ（`PalPeg.Metered`）で刻んだ **固定動作数ラウンド** の機械を与えた。
本ファイルは、その 1 歩を **有限制御プログラム** `GSVProg.vprogX`
（`PalPeg.GSVerifierProgX`、動作列は `GSVTapes.vprogramX` そのもの）に置き換えた
版の

1. **償却コスト解析**（`vprogramX_amortized` / `vrunX_tape_cost_init'`）、
2. **照合フェーズのラウンドプログラム**（`matchProg` とそのトレース前置性）、
3. **段の答えの正しさ**（`Metered.metered_answer_correct'` の言い換え）

を与える。

## 1. 償却（`Φ` と `Ψ`）

走査部のポテンシャルは `Φ = (k+1)·pos + q`（`PalPeg.Phi`）、検証器部のポテンシャルは
`Ψ = 2·checked`。`GSVTapes.vprogramX` の枝別コストは

* 比較枝：`|advActs| + |vcomp2Acts| ≤ 8 + 4 = 12`、
* ずらし枝：`probe ×2 (= 4)` ＋（周期なら `perProgramX ≤ 14·p₁+4`、
  リセットなら `resProgramX ≤ 9·q+4`）＋ `uxWalk (= 2·checked+4)`

であり、`gsShift ≤ ΔΦ`（`GSVTapes.gsShift_le_dPhi`）と
`q ≤ k·⌈q/k⌉ ≤ k·gsShift`（周期でない枝）から

* `A'' = 9k + 14`（周期枝の `14·p₁ ≤ 14·ΔΦ`、リセット枝の `9·q ≤ 9k·ΔΦ` を同時に覆う）
* `B'' = 16`（比較枝：`12` ＋ `Ψ` の増分 `≤ 4`）

が取れる（`vprogramX_amortized`）。`vprogram'` の `A'' = 8k+14`, `B''' = 18` に対応する。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg
namespace StageMatcherProg

open PalPeg.GSVTapes

variable {sc : ℕ}

/-! ## 1. 償却コスト定数 -/

/-- 償却係数 `A'' = 9k + 14`。 -/
def xA (k : ℕ) : ℕ := 9 * k + 14

/-- 償却定数 `B'' = 16`。 -/
def xB : ℕ := 16

example : xA 8 = 86 := by norm_num [xA]
example : xB = 16 := rfl

/-! ## 2. 一歩の償却 -/

section Step

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  {vt : VTapes' sc} {z : VState}

/-- **一歩の費用（枝別）**：`|vprogramX| ≤ A''·ΔΦ + 12 + 2·checked`。 -/
theorem vprogramX_cost (hk : 0 < k) (hne : mark ≠ blank) (hend : endSym ∉ v)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length) :
    (vprogramX blank endSym mark k vt).length ≤
      xA k * (Phi k (scanStep v k p₁ r Text z.1) - Phi k z.1) + 12 + 2 * z.2 := by
  obtain ⟨D, hD⟩ : ∃ D, Phi k (scanStep v k p₁ r Text z.1) - Phi k z.1 = D := ⟨_, rfl⟩
  rw [hD]
  have hcc : cOf vt.2 = z.2 := cOf_eq hE.pat
  unfold vprogramX xA
  by_cases hadv : Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT)
  · rw [if_pos hadv]
    simp only [List.length_append, List.length_map]
    have h1 := GSTapes.advActs_length_le blank mark vt.1
    have h2 := vcomp2Acts_length_le (blank := blank) (endSym := endSym) vt.2
    omega
  · rw [if_neg hadv]
    have hna : ¬ (z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) :=
      fun hcon => hadv ((GSTapes.advance_iff' hend hE.scan hq).2 hcon)
    have hss : scanStep v k p₁ r Text z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) :=
      GSTapes.scanStep_shift hna
    have hsh : gsShift k p₁ r z.1.q ≤ D := by
      have h := gsShift_le_dPhi (p₁ := p₁) (r := r) hk z.1
      rw [← hss, hD] at h
      exact h
    have hAn := GSTapes.probeActs_length blank GSTapes.tAn
    have hRn := GSTapes.probeActs_length blank GSTapes.tRn
    have hUXW : (uxWalk vt).length = 2 * cOf vt.2 + 4 := uxWalk_length vt
    simp only [List.length_append, List.length_map]
    by_cases hcond : Tape.read (Tape.step blank (vt.1 GSTapes.tAn) blank .left) = mark ∧
        Tape.read (Tape.step blank (vt.1 GSTapes.tRn) blank .left) = mark
    · rw [if_pos hcond]
      have hp1 : GSTapes.p1Of' vt.1 = p₁ := GSTapes.p1Of'_eq hE.scan
      have hgs : gsShift k p₁ r z.1.q = p₁ := by
        unfold gsShift; rw [if_pos ((GSTapes.period_iff' hne hE.scan).1 hcond)]
      have hle := perProgramX_length_le blank mark (GSTapes.p1Of' vt.1) vt
      have hpD : p₁ ≤ D := by rw [← hgs]; exact hsh
      rw [hp1] at hle
      rw [hp1, hAn, hRn, hUXW, hcc]
      have h14 : 14 * p₁ ≤ (9 * k + 14) * D := by
        have : (9 * k + 14) * D = 9 * k * D + 14 * D := by ring
        have h2 : 14 * p₁ ≤ 14 * D := Nat.mul_le_mul_left 14 hpD
        omega
      omega
    · rw [if_neg hcond]
      have hqz : GSTapes.qOf' vt.1 = z.1.q := GSTapes.qOf'_eq hE.scan
      have hgs : gsShift k p₁ r z.1.q = max 1 (ceilDiv z.1.q k) := by
        unfold gsShift
        rw [if_neg (fun hcon => hcond ((GSTapes.period_iff' hne hE.scan).2 hcon))]
      have hcb : z.1.q ≤ k * ceilDiv z.1.q k := (ceilDiv_bounds hk).1
      have hmax : ceilDiv z.1.q k ≤ max 1 (ceilDiv z.1.q k) := le_max_right _ _
      have hkq : z.1.q ≤ k * D := by
        have h1 : k * ceilDiv z.1.q k ≤ k * gsShift k p₁ r z.1.q := by
          rw [hgs]; exact Nat.mul_le_mul_left k hmax
        have h2 : k * gsShift k p₁ r z.1.q ≤ k * D := Nat.mul_le_mul_left k hsh
        omega
      have hle := resProgramX_length_le blank mark k (GSTapes.qOf' vt.1) vt
      rw [hqz] at hle
      rw [hqz, hAn, hRn, hUXW, hcc]
      have h9 : 9 * z.1.q ≤ 9 * (k * D) := Nat.mul_le_mul_left 9 hkq
      have h9' : 9 * (k * D) ≤ (9 * k + 14) * D := by
        have : (9 * k + 14) * D = 9 * (k * D) + 14 * D := by ring
        omega
      omega

/-- **一歩の償却**（`Ψ = 2·checked` 込み）：`A'' = 9k+14`, `B'' = 16`。
`GSVerifierTapes.vprogram'_amortized`（`A'' = 8k+14`, `B''' = 18`）の `vprogramX` 版。 -/
theorem vprogramX_amortized (hk : 0 < k) (hne : mark ≠ blank) (hend : endSym ∉ v)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length) :
    (vprogramX blank endSym mark k vt).length + 2 * (vStep u v k p₁ r Text z).2 ≤
      xA k * (Phi k (vStep u v k p₁ r Text z).1 - Phi k z.1) + xB + 2 * z.2 := by
  rw [vStep_fst]
  have hcost := vprogramX_cost hk hne hend hE hq
  have hcc : cOf vt.2 = z.2 := cOf_eq hE.pat
  obtain ⟨D, hD⟩ : ∃ D, Phi k (scanStep v k p₁ r Text z.1) - Phi k z.1 = D := ⟨_, rfl⟩
  rw [hD] at hcost ⊢
  unfold xB
  by_cases hadv : z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?
  · -- 比較枝：`|vprogramX| ≤ 12`、`Ψ` の増分は `≤ 4`。
    have hvs : (vStep u v k p₁ r Text z).2
        = vComp u Text z.1.pos (vComp u Text z.1.pos z.2) := vStep_snd_adv hadv
    have h3 := vComp_le_succ u Text z.1.pos z.2
    have h4 := vComp_le_succ u Text z.1.pos (vComp u Text z.1.pos z.2)
    have hlen : (vprogramX blank endSym mark k vt).length ≤ 12 := by
      have hadvT : Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
          Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT) :=
        (GSTapes.advance_iff' hend hE.scan hq).2 hadv
      unfold vprogramX
      rw [if_pos hadvT]
      simp only [List.length_append, List.length_map]
      have h1 := GSTapes.advActs_length_le blank mark vt.1
      have h2 := vcomp2Acts_length_le (blank := blank) (endSym := endSym) vt.2
      omega
    rw [hvs]
    omega
  · -- ずらし枝：`checked := 0`。
    have hvs : (vStep u v k p₁ r Text z).2 = 0 := vStep_snd_shift hadv
    rw [hvs]
    unfold xA at hcost ⊢
    omega

end Step

/-! ## 3. 実行全体の償却 -/

/-- テープ側の実行（`vprogramX` 版）。 -/
def vRunTapesX (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) : ℕ → VTapes' sc × VState → VTapes' sc × VState
  | 0, s => s
  | n + 1, s =>
      vRunTapesX blank endSym mark u v k p₁ r Text n
        (vApplyActs' blank (vprogramX blank endSym mark k s.1) s.1,
          vStep u v k p₁ r Text s.2)

/-- その総動作数（`vprogramX` 版）。 -/
def vRunCostTapesX (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) : ℕ → VTapes' sc × VState → ℕ
  | 0, _ => 0
  | n + 1, s =>
      (vprogramX blank endSym mark k s.1).length +
        vRunCostTapesX blank endSym mark u v k p₁ r Text n
          (vApplyActs' blank (vprogramX blank endSym mark k s.1) s.1,
            vStep u v k p₁ r Text s.2)

@[simp] theorem vRunTapesX_zero (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (s : VTapes' sc × VState) :
    vRunTapesX blank endSym mark u v k p₁ r Text 0 s = s := rfl

theorem vRunTapesX_succ (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (n : ℕ) (s : VTapes' sc × VState) :
    vRunTapesX blank endSym mark u v k p₁ r Text (n + 1) s
      = vRunTapesX blank endSym mark u v k p₁ r Text n
          (vApplyActs' blank (vprogramX blank endSym mark k s.1) s.1,
            vStep u v k p₁ r Text s.2) := rfl

section Run

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}

/-- **実行全体の償却**：`Ψ = 2·checked` 込みの総動作数は
`A''·(Φ_end - Φ_start) + B''·n + 2·checked_start` 以下（`A'' = 9k+14`, `B'' = 16`）。 -/
theorem vrunX_tape_cost_le' (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) :
    ∀ (n : ℕ) (vt : VTapes' sc) (z : VState),
      VEncodes' blank startSym endSym mark u v Text k p₁ r vt z →
      z.1.q ≤ v.length → z.2 ≤ u.length → u.length ≤ z.1.pos →
      VFits v k p₁ r Text n z.1 →
      vRunCostTapesX blank endSym mark u v k p₁ r Text n (vt, z)
          + 2 * (vRunState u v k p₁ r Text n z).2 ≤
        xA k * (Phi k (vRunState u v k p₁ r Text n z).1 - Phi k z.1) + xB * n + 2 * z.2 := by
  intro n
  induction n with
  | zero =>
    intro vt z _ _ _ _ _
    show 0 + 2 * z.2 ≤ xA k * (Phi k z.1 - Phi k z.1) + xB * 0 + 2 * z.2
    rw [Nat.sub_self, Nat.mul_zero]
    omega
  | succ n ih =>
    intro vt z hE hq hc hpos hfits
    obtain ⟨hfit, hfits'⟩ := hfits
    have hE' := vencodes_stepX hk hp hne hend hendu hE hq hc hpos hfit
    have hq' : (vStep u v k p₁ r Text z).1.q ≤ v.length := by
      rw [vStep_fst]; exact scanStep_q_le hq
    have hc' : (vStep u v k p₁ r Text z).2 ≤ u.length := vStep_checked_le hc
    have hpos' : u.length ≤ (vStep u v k p₁ r Text z).1.pos := by
      rw [vStep_fst]; exact le_trans hpos (scanStep_pos_le v k p₁ r Text z.1)
    have hfits'' : VFits v k p₁ r Text n (vStep u v k p₁ r Text z).1 := by
      rw [vStep_fst]; exact hfits'
    have hih := ih _ _ hE' hq' hc' hpos' hfits''
    have hstep := vprogramX_amortized hk hne hend hE hq
    have hm1 := phi_vStep_le (r := r) hk hp u v Text z
    have hm2 := phi_vRunState_le (r := r) hk hp u v Text n (vStep u v k p₁ r Text z)
    obtain ⟨P0, hP0⟩ : ∃ P0, Phi k z.1 = P0 := ⟨_, rfl⟩
    obtain ⟨P1, hP1⟩ : ∃ P1, Phi k (vStep u v k p₁ r Text z).1 = P1 := ⟨_, rfl⟩
    obtain ⟨P2, hP2⟩ : ∃ P2,
        Phi k (vRunState u v k p₁ r Text n (vStep u v k p₁ r Text z)).1 = P2 := ⟨_, rfl⟩
    rw [hP0, hP1] at hstep
    rw [hP0] at hm1
    rw [hP1] at hm1 hih hm2
    rw [hP2] at hih hm2
    have hsum : xA k * (P2 - P1) + xA k * (P1 - P0) = xA k * (P2 - P0) := by
      rw [← Nat.mul_add, show P2 - P1 + (P1 - P0) = P2 - P0 from by omega]
    show (vprogramX blank endSym mark k vt).length
        + vRunCostTapesX blank endSym mark u v k p₁ r Text n
            (vApplyActs' blank (vprogramX blank endSym mark k vt) vt,
              vStep u v k p₁ r Text z)
        + 2 * (vRunState u v k p₁ r Text n (vStep u v k p₁ r Text z)).2 ≤
      xA k * (Phi k (vRunState u v k p₁ r Text n (vStep u v k p₁ r Text z)).1 - Phi k z.1)
        + xB * (n + 1) + 2 * z.2
    rw [hP0, hP2]
    have e : xB * (n + 1) = xB * n + xB := by ring
    omega

/-- **初期状態からの実行**：`|u|` に比例する項は残らない。`A'' = 9k+14`, `B'' = 16`。 -/
theorem vrunX_tape_cost_init' (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (n : ℕ) (vt : VTapes' sc)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt
      ((⟨u.length, 0⟩ : ScanState), 0))
    (hfits : VFits v k p₁ r Text n (⟨u.length, 0⟩ : ScanState)) :
    vRunCostTapesX blank endSym mark u v k p₁ r Text n
        (vt, ((⟨u.length, 0⟩ : ScanState), 0)) ≤
      xA k * (Phi k (vRunState u v k p₁ r Text n ((⟨u.length, 0⟩ : ScanState), 0)).1
          - Phi k (⟨u.length, 0⟩ : ScanState))
        + xB * n := by
  have h := vrunX_tape_cost_le' hk hp hne hend hendu n vt _ hE
    (Nat.zero_le _) (Nat.zero_le _) (Nat.le_refl _) hfits
  have h0 : (((⟨u.length, 0⟩ : ScanState), (0 : ℕ))).2 = 0 := rfl
  have h1 : (((⟨u.length, 0⟩ : ScanState), (0 : ℕ))).1 = (⟨u.length, 0⟩ : ScanState) := rfl
  rw [h0, h1] at h
  omega

end Run

/-! ## 4. 照合フェーズのラウンドプログラム

`Prog` は 1 マイクロステップにつき高々 1 動作しか出さないので、`Metered` の
「1 ラウンド＝固定本数 `B` の動作」というペース配分は、**プログラムの制御を
ラウンドをまたいで保持する**（`ProgLangPersist` の永続制御機械）ことで実現される。
本節はそのための **トレース／動作列レベル** の事実だけを与える：`matchProg k n`
（`vprogX k` を `n` 回並べたもの）のトレースは、各ラウンドの `vprogramX` の
動作列をその順に連結したものにちょうど一致し、しかも前置的である
（`matchActs_append` / `matchProg_trace_prefix`）。したがって、その動作列を
1 ラウンドあたり `B` 本ずつ切り出す任意のペース配分は、各ラウンド境界で
`Metered.metered` の状態を再現する。 -/

/-- `n` ラウンド分の動作列（各ラウンドは `vprogramX` そのもの）。 -/
def matchActs (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) : ℕ → VTapes' sc × VState → List (VAct' sc)
  | 0, _ => []
  | n + 1, s =>
      vprogramX blank endSym mark k s.1 ++
        matchActs blank endSym mark u v k p₁ r Text n
          (vApplyActs' blank (vprogramX blank endSym mark k s.1) s.1,
            vStep u v k p₁ r Text s.2)

/-- `n` ラウンドのプログラム：`vprogX k` の `n` 回の逐次合成。 -/
def matchProg (k : ℕ) : ℕ → PalPeg.ProgLang.Prog PalPeg.GSVProg.Act10 PalPeg.GSVProg.Cond10
  | 0 => PalPeg.ProgLang.Prog.skip
  | n + 1 => PalPeg.ProgLang.Prog.seq (PalPeg.GSVProg.vprogX k) (matchProg k n)

section Acts

variable {blank endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}

@[simp] theorem matchActs_zero (s : VTapes' sc × VState) :
    matchActs blank endSym mark u v k p₁ r Text 0 s = [] := rfl

theorem matchActs_succ (n : ℕ) (s : VTapes' sc × VState) :
    matchActs blank endSym mark u v k p₁ r Text (n + 1) s
      = vprogramX blank endSym mark k s.1 ++
          matchActs blank endSym mark u v k p₁ r Text n
            (vApplyActs' blank (vprogramX blank endSym mark k s.1) s.1,
              vStep u v k p₁ r Text s.2) := rfl

/-- ラウンド `n` 分の動作を適用したテープは `vRunTapesX` の第 1 成分。 -/
theorem vRunTapesX_fst :
    ∀ (n : ℕ) (s : VTapes' sc × VState),
      (vRunTapesX blank endSym mark u v k p₁ r Text n s).1
        = vApplyActs' blank (matchActs blank endSym mark u v k p₁ r Text n s) s.1 := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    rw [vRunTapesX_succ, ih, matchActs_succ, vApplyActs'_append]

theorem vRunTapesX_snd :
    ∀ (n : ℕ) (s : VTapes' sc × VState),
      (vRunTapesX blank endSym mark u v k p₁ r Text n s).2
        = vRunState u v k p₁ r Text n s.2 := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih => intro s; rw [vRunTapesX_succ, ih]; rfl

/-- **動作列の総数はラウンド費用**。 -/
theorem matchActs_length :
    ∀ (n : ℕ) (s : VTapes' sc × VState),
      (matchActs blank endSym mark u v k p₁ r Text n s).length
        = vRunCostTapesX blank endSym mark u v k p₁ r Text n s := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    rw [matchActs_succ, List.length_append, ih]
    rfl

/-- **前置性（ペース配分の基礎）**：`m + n` ラウンドの動作列は、最初の `m`
ラウンドの動作列に、そこから続く `n` ラウンドの動作列を連結したもの。 -/
theorem matchActs_append :
    ∀ (m n : ℕ) (s : VTapes' sc × VState),
      matchActs blank endSym mark u v k p₁ r Text (m + n) s
        = matchActs blank endSym mark u v k p₁ r Text m s ++
            matchActs blank endSym mark u v k p₁ r Text n
              (vRunTapesX blank endSym mark u v k p₁ r Text m s) := by
  intro m
  induction m with
  | zero => intro n s; rw [Nat.zero_add]; rfl
  | succ m ih =>
    intro n s
    rw [show m + 1 + n = (m + n) + 1 from by omega, matchActs_succ, matchActs_succ, ih,
      List.append_assoc, vRunTapesX_succ]

/-- **ラウンド `n` の動作**：`n+1` ラウンド目に実行されるのは、そのラウンド頭の
テープ状態における `vprogramX` そのもの。 -/
theorem matchActs_snoc (n : ℕ) (s : VTapes' sc × VState) :
    matchActs blank endSym mark u v k p₁ r Text (n + 1) s
      = matchActs blank endSym mark u v k p₁ r Text n s ++
          vprogramX blank endSym mark k
            (vRunTapesX blank endSym mark u v k p₁ r Text n s).1 := by
  rw [matchActs_append n 1 s]
  congr 1
  rw [matchActs_succ]
  simp

/-- 最初の `m` ラウンド分は、`m + n` ラウンド分の先頭を切り取ったもの。 -/
theorem matchActs_take (m n : ℕ) (s : VTapes' sc × VState) :
    (matchActs blank endSym mark u v k p₁ r Text (m + n) s).take
        (matchActs blank endSym mark u v k p₁ r Text m s).length
      = matchActs blank endSym mark u v k p₁ r Text m s := by
  rw [matchActs_append m n s]
  simp

end Acts

/-! ## 5. プログラムの実行とトレース -/

section ProgSpec

open PalPeg.ProgLang PalPeg.GSVProg

variable {Terminal : Type} {blank startSym endSym mark : Fin sc}
variable {u v Text : List (Fin sc)} {k p₁ r : ℕ}

/-- **主定理（`n` ラウンドの一致）**：`matchProg k n` は状態 `vt` からちょうど
`matchActs … n (vt, z)`（各ラウンドの `vprogramX` の連結）を実行して継続に戻る。 -/
theorem matchProg_exec (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank)
    (hstart : startSym ∉ v) (hend : endSym ∉ v) (hendu : endSym ∉ u)
    (hsu : startSym ∉ u) (hse : startSym ≠ endSym) :
    ∀ (n : ℕ) (vt : VTapes' sc) (z : VState),
      VEncodes' blank startSym endSym mark u v Text k p₁ r vt z →
      z.1.q ≤ v.length → z.2 ≤ u.length → u.length ≤ z.1.pos →
      VFits v k p₁ r Text n z.1 →
      ExecV Terminal blank endSym mark startSym (matchProg k n) vt
        (matchActs blank endSym mark u v k p₁ r Text n (vt, z)) := by
  intro n
  induction n with
  | zero => intro vt z _ _ _ _ _; exact execV_skip
  | succ n ih =>
    intro vt z hE hq hc hpos hfits
    obtain ⟨hfit, hfits'⟩ := hfits
    have h1 := vprogX_exec (Terminal := Terminal) (startSym := startSym) hk hne hstart hsu hse
      hE hq
    have hE' := vencodes_stepX hk hp hne hend hendu hE hq hc hpos hfit
    have hq' : (vStep u v k p₁ r Text z).1.q ≤ v.length := by
      rw [vStep_fst]; exact scanStep_q_le hq
    have hc' : (vStep u v k p₁ r Text z).2 ≤ u.length := vStep_checked_le hc
    have hpos' : u.length ≤ (vStep u v k p₁ r Text z).1.pos := by
      rw [vStep_fst]; exact le_trans hpos (scanStep_pos_le v k p₁ r Text z.1)
    have hfits'' : VFits v k p₁ r Text n (vStep u v k p₁ r Text z).1 := by
      rw [vStep_fst]; exact hfits'
    have h2 := ih (vApplyActs' blank (vprogramX blank endSym mark k vt) vt)
      (vStep u v k p₁ r Text z) hE' hq' hc' hpos' hfits''
    exact execV_seq h1 h2

/-- **トレースの一致**：`matchProg k n` のトレースは、各ラウンドの `vprogramX` を
順に連結した動作列のベクトル列。 -/
theorem matchProg_trace (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank)
    (hstart : startSym ∉ v) (hend : endSym ∉ v) (hendu : endSym ∉ u)
    (hsu : startSym ∉ u) (hse : startSym ≠ endSym)
    (n : ℕ) (vt : VTapes' sc) (z : VState)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length) (hc : z.2 ≤ u.length) (hpos : u.length ≤ z.1.pos)
    (hfits : VFits v k p₁ r Text n z.1)
    (l : List (Option Terminal))
    (hl : l.length = (matchActs blank endSym mark u v k p₁ r Text n (vt, z)).length) :
    trace (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
        ([matchProg k n], vTS vt)
      = vavecs blank (matchActs blank endSym mark u v k p₁ r Text n (vt, z)) vt := by
  have h := matchProg_exec (Terminal := Terminal) (startSym := startSym) hk hp hne hstart hend
    hendu hsu hse n vt z hE hq hc hpos hfits
  have h2 := (h [] l (by rw [vavecs_length]; exact hl)).1
  rw [show ([matchProg k n] ++ ([] : Stack Act10 Cond10)) = [matchProg k n] from rfl] at h2
  exact h2

/-- **トレースの前置性（ペース配分）**：`m + n` ラウンド走らせたトレースは、
最初の `m` ラウンドのトレースを前置として持つ。したがって、1 ラウンドあたり
`B` 本ずつ動作を切り出す任意のペース配分は、各ラウンド境界でちょうど
`matchActs … m` を実行し終えた状態にいる。 -/
theorem matchProg_trace_prefix (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank)
    (hstart : startSym ∉ v) (hend : endSym ∉ v) (hendu : endSym ∉ u)
    (hsu : startSym ∉ u) (hse : startSym ≠ endSym)
    (m n : ℕ) (vt : VTapes' sc) (z : VState)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length) (hc : z.2 ≤ u.length) (hpos : u.length ≤ z.1.pos)
    (hfits : VFits v k p₁ r Text (m + n) z.1)
    (l : List (Option Terminal))
    (hl : l.length = (matchActs blank endSym mark u v k p₁ r Text (m + n) (vt, z)).length) :
    trace (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
        ([matchProg k (m + n)], vTS vt)
      = vavecs blank (matchActs blank endSym mark u v k p₁ r Text m (vt, z)) vt ++
          vavecs blank
            (matchActs blank endSym mark u v k p₁ r Text n
              (vRunTapesX blank endSym mark u v k p₁ r Text m (vt, z)))
            (vRunTapesX blank endSym mark u v k p₁ r Text m (vt, z)).1 := by
  rw [matchProg_trace (Terminal := Terminal) (startSym := startSym) hk hp hne hstart hend hendu
    hsu hse (m + n) vt z hE hq hc hpos hfits l hl,
    matchActs_append (blank := blank) (endSym := endSym) (mark := mark) (u := u) (v := v)
      (k := k) (p₁ := p₁) (r := r) (Text := Text) m n (vt, z),
    vavecs_append]
  congr 1
  rw [vRunTapesX_fst]

/-- **トレースの長さ**：`n` ラウンドのトレースはちょうど `n` ラウンド分の動作数。 -/
theorem matchProg_trace_length (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank)
    (hstart : startSym ∉ v) (hend : endSym ∉ v) (hendu : endSym ∉ u)
    (hsu : startSym ∉ u) (hse : startSym ≠ endSym)
    (n : ℕ) (vt : VTapes' sc) (z : VState)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length) (hc : z.2 ≤ u.length) (hpos : u.length ≤ z.1.pos)
    (hfits : VFits v k p₁ r Text n z.1)
    (l : List (Option Terminal))
    (hl : l.length = (matchActs blank endSym mark u v k p₁ r Text n (vt, z)).length) :
    (trace (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
        ([matchProg k n], vTS vt)).length
      = vRunCostTapesX blank endSym mark u v k p₁ r Text n (vt, z) := by
  rw [matchProg_trace (Terminal := Terminal) (startSym := startSym) hk hp hne hstart hend hendu
    hsu hse n vt z hE hq hc hpos hfits l hl, vavecs_length, matchActs_length]

/-- **テープの一致**：`n` ラウンド後のテープは `vRunTapesX` の第 1 成分。 -/
theorem matchProg_tapes (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank)
    (hstart : startSym ∉ v) (hend : endSym ∉ v) (hendu : endSym ∉ u)
    (hsu : startSym ∉ u) (hse : startSym ≠ endSym)
    (n : ℕ) (vt : VTapes' sc) (z : VState)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length) (hc : z.2 ≤ u.length) (hpos : u.length ≤ z.1.pos)
    (hfits : VFits v k p₁ r Text n z.1)
    (l : List (Option Terminal))
    (hl : l.length = (matchActs blank endSym mark u v k p₁ r Text n (vt, z)).length) :
    (runInputs (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
        ([matchProg k n], vTS vt)).2
      = vTS (vRunTapesX blank endSym mark u v k p₁ r Text n (vt, z)).1 := by
  rw [runInputs_snd_eq_applyTrace,
    matchProg_trace (Terminal := Terminal) (startSym := startSym) hk hp hne hstart hend hendu
      hsu hse n vt z hE hq hc hpos hfits l hl, applyTrace_vavecs, vRunTapesX_fst]

end ProgSpec

/-! ## 6. ペース配分と段の答え

`Metered` の計量式スケジューラは、1 ステップの費用 `cst st`（計量単位 `U` の個数）を
1 ラウンドあたり `B = mRate A B' k = (k+1)*(A+B')` 個ずつ消化する。`matchProg` を
1 ラウンドあたり `B` 動作のペースで実行する永続制御機械では、`§4` の前置性により
各ラウンド境界の状態がちょうど `Metered.metered` の状態になる。ここでは
`Metered.metered_answer_correct'` の 2 つの義務

* `hcost` … `cst st ≤ (A + B') * ΔΦ`
* `hadvance` … 前進（比較成功）ステップは `cst st ≤ 1`

のうち、`hadvance` を `§2` の枝別評価から直接与える（比較枝の動作数は `≤ 12` なので、
計量単位を `U ≥ 12` に取れば `⌈12/U⌉ = 1`）。`hcost` の係数は `§2` の
`A'' = 9k+14`, `B'' = 16` である。 -/

/-- 1 ラウンドの計量動作数 `B = mRate A'' B'' k = (k+1)*(9k+30)`。 -/
def xRate (k : ℕ) : ℕ := PalPeg.mRate (xA k) xB k

example : xRate 8 = 9 * 102 := by norm_num [xRate, PalPeg.mRate, xA, xB]

section Pacing

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  {vt : VTapes' sc} {z : VState}

/-- **比較枝の動作数**：`|advActs| + |vcomp2Acts| ≤ 8 + 4 = 12`。 -/
theorem vprogramX_adv_le (hend : endSym ∉ v)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length)
    (hadv : z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) :
    (vprogramX blank endSym mark k vt).length ≤ 12 := by
  have hadvT : Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT) :=
    (GSTapes.advance_iff' hend hE.scan hq).2 hadv
  unfold vprogramX
  rw [if_pos hadvT]
  simp only [List.length_append, List.length_map]
  have h1 := GSTapes.advActs_length_le blank mark vt.1
  have h2 := vcomp2Acts_length_le (blank := blank) (endSym := endSym) vt.2
  omega

/-- `x ≤ U` なら `⌈x/U⌉ ≤ 1`。 -/
theorem uceil_le_one {U x : ℕ} (hU : 0 < U) (h : x ≤ U) :
    PalPeg.StageMatcherTapes.uceil U x ≤ 1 := by
  unfold PalPeg.StageMatcherTapes.uceil
  have hlt : x + U - 1 < U * 2 := by omega
  have := Nat.div_lt_of_lt_mul hlt
  omega

/-- **`hadvance` の履行**：計量単位を `U ≥ 12` に取れば、比較枝のステップの
計量費用は `1`（＝ 駐機しない）。 -/
theorem xcst_advance {U : ℕ} (hU : 12 ≤ U) (hend : endSym ∉ v)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length)
    (hadv : z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) :
    PalPeg.StageMatcherTapes.uceil U (vprogramX blank endSym mark k vt).length ≤ 1 :=
  uceil_le_one (by omega) (le_trans (vprogramX_adv_le hend hE hq hadv) hU)

end Pacing

/-! ## 7. 段の答えの正しさ（`A'' = 9k+14`, `B'' = 16` 版） -/

section Answer

variable {α : Type} [DecidableEq α] {w : List α} {S k s p₁ r : ℕ} {cst : ScanState → ℕ}

/-- **段の出力の意味（`vprogramX` 版の定数で）**：`matchProg` を 1 ラウンドあたり
`xRate k` 計量動作のペースで実行する永続制御機械の答えビット `Metered.manswer` は、
`stageMatchH` と同じ真理値を返す。`PalPeg.StageMatcherTapes.stage_answer_stageMatchH`
の `A := xA k`, `B' := xB` インスタンス（`hcost`/`hadvance` は `§2`/`§6` の形）。 -/
theorem stageX_answer_stageMatchH (hk : 0 < k) (hs : s < S / 2)
    (H : GSCore ((w.take (S / 2)).reverse) k s p₁ r)
    (hcost : ∀ st, cst st ≤ (xA k + xB)
      * (Phi k (scanStep ((w.take (S / 2)).reverse.drop s) k
          (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r) (w.drop S) st)
        - Phi k st))
    (hadvance : ∀ st, st.q ≠ ((w.take (S / 2)).reverse.drop s).length →
      (w.drop S)[st.pos + st.q]? = ((w.take (S / 2)).reverse.drop s)[st.q]? → cst st ≤ 1)
    {n : ℕ} (h2S : 2 * S ≤ n) (hn : n ≤ w.length) :
    (PalPeg.manswer ((w.take (S / 2)).reverse.take s) ((w.take (S / 2)).reverse.drop s) k
        (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r) (w.drop S)
        cst (xA k) xB (n - S) = true)
      ↔ occursAt (w.take (S / 2)).reverse (w.take n) :=
  PalPeg.StageMatcherTapes.stage_answer_stageMatchH hk hs H
    (by unfold xB; omega) hcost hadvance h2S hn

end Answer

/-! ## 8. 公理の確認 -/

#print axioms vprogramX_cost
#print axioms vprogramX_amortized
#print axioms vrunX_tape_cost_le'
#print axioms vrunX_tape_cost_init'
#print axioms matchActs_length
#print axioms matchActs_append
#print axioms matchActs_snoc
#print axioms matchActs_take
#print axioms matchProg_exec
#print axioms matchProg_trace
#print axioms matchProg_trace_prefix
#print axioms matchProg_trace_length
#print axioms matchProg_tapes
#print axioms vprogramX_adv_le
#print axioms xcst_advance
#print axioms stageX_answer_stageMatchH

end StageMatcherProg
end PalPeg
