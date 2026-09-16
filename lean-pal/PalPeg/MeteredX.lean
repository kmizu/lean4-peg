import PalPeg.Metered
import PalPeg.GSVerifier

/-!
# `Ψ` 償却つき計量式スケジューラ (`MeteredX`)

`PalPeg.Metered` の計量式スケジューラは、1 ステップの費用を **走査状態だけの関数**
`cst : ScanState → ℕ` として受け取り、義務

  `hcost : ∀ st, cst st ≤ (A + B') * ΔΦ`

を課す。ところが有限制御の一歩（`GSVTapes.vprogramX`、供給つき実現は
`PalPeg.VerifierFeedX.fstepX`）の実費用は

  `fcostX ≤ (8k+47)·ΔΦ + 82 + 2·checked − 2·checked'`（`VerifierFeedX.fcostX_amortized`）

という **`Ψ = 2·checked` 込みの償却形**でしか抑えられず（周期ずらし枝では
`ΔΦ = k·p₁` に対し `checked ≤ 2q`、`q ≤ r` は `k·p₁` よりいくらでも大きい）、
`hcost` の形には収まらない。

本ファイルは、状態に `checked` を持たせた計量式スケジューラ `meteredX` を定義し、
`Metered` の各補題を `Ψ` 込みで再構成する。

## 何が通り、何が通らないか（重要）

* **通る**：`mactX_pot`（1 動作あたりのポテンシャル増加、**両側形**
  `MPotX m + 1 + Ψ(m') ≤ MPotX m' + Ψ(m)`）、その telescoping、
  不変条件、報告の健全性（`mreportedX_sound`）、追い越し禁止（`mactsX_pos_le`）。
* **通らない**：遅れ有界性の **定数**。`mactsX_pot` のフロンティア停止ケースでは
  蓄積したポテンシャルを捨てて `Φ ≥ (k+1)n − k·q` から作り直すため、`Ψ` を
  左辺に残したままにできず、`VCheckedInv`（`checked ≤ 2q`）から得られる
  `Ψ ≤ 4·|v|` を **加法定数として** 足すほかない：

    `meteredX_phi_boundary : (k+1)*n ≤ Φ + k*|v| + 4*|v|`

  ところが `Metered.mreported_complete` / `metered_boundary_of_occ` の最後の算術は

    `(k+1)(n+1) ≤ (k+1)P + Q + k|v|`,  `(k+1)P ≤ (k+1)i`,
    `(k+1)(n+1) = (k+1)i + k|v| + |v|`   ⟹ `|v| ≤ Q`（`Q ≤ |v|` と合わせて `Q = |v|`）

  という **余裕ゼロ** の連鎖であり、`+δ`（`δ > 0`）が入ると `Q ≥ |v| − δ` しか出ず
  結論が失われる。ラウンドあたりの動作数 `B` を増やしても解決しない：フロンティアでは
  `Φ ≤ (k+1)·n` が上限なので（それが `macts_pot` の停止ケースの存在理由）、
  `B > (k+1)(A+B')` にしてもポテンシャル不等式が強くならない。

  したがって `meteredX_answer_correct'` は **本ファイルでは閉じない**。
  残る穴はちょうど `MeteredXTightLag`（下）であり、これを閉じるには
  「フロンティア停止状態では `Ψ` が小さい」か、あるいは締切ラウンドの議論自体を
  `Ψ` 込みに作り直すか、いずれかの新しい議論が要る。**公理も `sorry` も置かない。**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg
namespace MeteredX

universe w
variable {α : Type w}

/-! ## 1. 状態と 1 動作 -/

/-- 計量式スケジューラの状態：**検証器つき**状態 `z = (pos, q, checked)` と、
実行中ステップの残り動作数。 -/
structure MStateX where
  /-- 走査状態と検証済み文字数。 -/
  z : VState
  /-- 実行中ステップの残り動作数（`0` がステップ境界）。 -/
  rem : ℕ

@[simp] theorem MStateX.mk_z (a : VState) (b : ℕ) : (MStateX.mk a b).z = a := rfl
@[simp] theorem MStateX.mk_rem (a : VState) (b : ℕ) : (MStateX.mk a b).rem = b := rfl

/-- 検証器のポテンシャル `Ψ = 2 * checked`。 -/
def Pot (z : VState) : ℕ := 2 * z.2

variable [DecidableEq α]

/-- **1 テープ動作**（`Metered.mact` の `Ψ` 版）。費用関数は `VState` の関数。 -/
def mactX (u v : List α) (k p₁ r : ℕ) (T : List α) (cst : VState → ℕ) (n : ℕ)
    (m : MStateX) : MStateX :=
  if m.rem = 0 then
    (if Enabled v n m.z.1 then
        (if cst m.z ≤ 1 then ⟨vStep u v k p₁ r T m.z, 0⟩ else ⟨m.z, cst m.z - 1⟩)
      else m)
  else if m.rem = 1 then ⟨vStep u v k p₁ r T m.z, 0⟩
  else ⟨m.z, m.rem - 1⟩

/-- `j` 個の動作。 -/
def mactsX (u v : List α) (k p₁ r : ℕ) (T : List α) (cst : VState → ℕ) (n : ℕ) :
    ℕ → MStateX → MStateX
  | 0, m => m
  | j + 1, m => mactsX u v k p₁ r T cst n j (mactX u v k p₁ r T cst n m)

/-- ラウンド `n` 終了時の計量式状態。 -/
def meteredX (u v : List α) (k p₁ r : ℕ) (T : List α) (cst : VState → ℕ) (A B' : ℕ) :
    ℕ → MStateX
  | 0 => ⟨(⟨u.length, 0⟩, 0), 0⟩
  | n + 1 =>
      mactsX u v k p₁ r T cst (n + 1) (mRate A B' k) (meteredX u v k p₁ r T cst A B' n)

/-! ## 2. 償却形の仮定 -/

/-- **`Ψ` 込みの償却費用**（`VerifierFeedX.fcostX_amortized` の形）。 -/
def XAmortized (u v : List α) (k p₁ r : ℕ) (T : List α) (cst : VState → ℕ)
    (A B' B'' : ℕ) : Prop :=
  ∀ z : VState, cst z + Pot (vStep u v k p₁ r T z)
    ≤ (A + B') * (Phi k (vStep u v k p₁ r T z).1 - Phi k z.1) + B'' + Pot z

/-- 償却形は `ΔΦ ≥ 1` より 1 定数形に潰れる（`Metered.cost_le_of_amortized` の `Ψ` 版）。 -/
theorem costX_le_of_amortized {u v T : List α} {k p₁ r A B' B'' : ℕ} {cst : VState → ℕ}
    (hk : 0 < k) (hp : 0 < p₁) (h : XAmortized u v k p₁ r T cst A B' B'') (z : VState) :
    cst z + Pot (vStep u v k p₁ r T z)
      ≤ (A + B' + B'') * (Phi k (vStep u v k p₁ r T z).1 - Phi k z.1) + Pot z := by
  have hlt := phi_step_lt (v := v) (T := T) (p₁ := p₁) (r := r) hk hp z.1
  have h4 := h z
  rw [vStep_fst] at h4 ⊢
  have hd1 : 1 ≤ Phi k (scanStep v k p₁ r T z.1) - Phi k z.1 := by omega
  have h3 : B'' ≤ B'' * (Phi k (scanStep v k p₁ r T z.1) - Phi k z.1) := by
    simpa using Nat.mul_le_mul_left B'' hd1
  have e : (A + B' + B'') * (Phi k (scanStep v k p₁ r T z.1) - Phi k z.1)
      = (A + B') * (Phi k (scanStep v k p₁ r T z.1) - Phi k z.1)
        + B'' * (Phi k (scanStep v k p₁ r T z.1) - Phi k z.1) := by ring
  omega

/-! ## 3. 不変条件 -/

/-- 状態不変条件：`Metered.MInv` に `VCheckedInv`（`checked ≤ 2q`）を足したもの。 -/
def MInvX (v : List α) (n : ℕ) (m : MStateX) : Prop :=
  Fits n m.z.1 ∧ (m.rem ≠ 0 → Enabled v n m.z.1) ∧ m.z.2 ≤ 2 * m.z.1.q

omit [DecidableEq α] in
theorem MInvX.mono {v : List α} {n n' : ℕ} {m : MStateX} (h : MInvX v n m) (hn : n ≤ n') :
    MInvX v n' m :=
  ⟨h.1.mono hn, fun hr => (h.2.1 hr).mono hn, h.2.2⟩

/-- `checked ≤ 2q` は一歩で保たれる（`GSVerifierTapes.vStep_checkedInv` の一般 `α` 版）。 -/
theorem vStep_checked_le_two_q {u v T : List α} {k p₁ r : ℕ} {z : VState}
    (h : z.2 ≤ 2 * z.1.q) :
    (vStep u v k p₁ r T z).2 ≤ 2 * (vStep u v k p₁ r T z).1.q := by
  rw [vStep_fst]
  by_cases hadv : z.1.q ≠ v.length ∧ T[z.1.pos + z.1.q]? = v[z.1.q]?
  · have hss : scanStep v k p₁ r T z.1 = (⟨z.1.pos, z.1.q + 1⟩ : ScanState) := by
      unfold scanStep; rw [if_neg hadv.1, if_pos hadv.2]
    have hvs : (vStep u v k p₁ r T z).2 = vComp u T z.1.pos (vComp u T z.1.pos z.2) := by
      unfold vStep; rw [if_neg hadv.1, if_pos hadv.2]
    have h3 := vComp_le_succ u T z.1.pos z.2
    have h4 := vComp_le_succ u T z.1.pos (vComp u T z.1.pos z.2)
    rw [hvs, hss]
    show vComp u T z.1.pos (vComp u T z.1.pos z.2) ≤ 2 * (z.1.q + 1)
    omega
  · have hvs : (vStep u v k p₁ r T z).2 = 0 := by
      unfold vStep
      by_cases h1 : z.1.q = v.length
      · rw [if_pos h1]
      · rw [if_neg h1, if_neg (fun hc => hadv ⟨h1, hc⟩)]
    rw [hvs]
    exact Nat.zero_le _

/-- 1 動作で走査状態は「不変」か「`Enabled` な状態からの `vStep`」のどちらか。 -/
theorem mactX_z_cases {u v T : List α} {k p₁ r : ℕ} {cst : VState → ℕ} {n : ℕ}
    {m : MStateX} (h : MInvX v n m) :
    (mactX u v k p₁ r T cst n m).z = m.z ∨
      ((mactX u v k p₁ r T cst n m).z = vStep u v k p₁ r T m.z ∧ Enabled v n m.z.1) := by
  unfold mactX
  split_ifs with h0 he hc h1
  · exact Or.inr ⟨rfl, he⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, h.2.1 h0⟩
  · exact Or.inl rfl

theorem mactX_MInvX {u v T : List α} {k p₁ r : ℕ} {cst : VState → ℕ} (hk : 0 < k)
    (hv : 0 < v.length) {n : ℕ} {m : MStateX} (hq : m.z.1.q ≤ v.length) (h : MInvX v n m) :
    MInvX v n (mactX u v k p₁ r T cst n m) := by
  have hc := h.2.2
  unfold mactX
  split_ifs with h0 he hc1 h1
  · exact ⟨by rw [MStateX.mk_z, vStep_fst]; exact scanStep_fits hk hv he h.1, by simp,
      by rw [MStateX.mk_z]; exact vStep_checked_le_two_q hc⟩
  · exact ⟨h.1, fun _ => he, hc⟩
  · exact h
  · exact ⟨by rw [MStateX.mk_z, vStep_fst]; exact scanStep_fits hk hv (h.2.1 h0) h.1, by simp,
      by rw [MStateX.mk_z]; exact vStep_checked_le_two_q hc⟩
  · exact ⟨h.1, fun _ => h.2.1 h0, hc⟩

theorem mactX_inv {u v T : List α} {k p₁ r : ℕ} {cst : VState → ℕ} (hK : KSimple v k p₁ r)
    {n : ℕ} {m : MStateX} (hm : MInvX v n m) (h : ScanInv v T m.z.1) :
    ScanInv v T (mactX u v k p₁ r T cst n m).z.1 := by
  rcases mactX_z_cases (u := u) (k := k) (p₁ := p₁) (r := r) (T := T) (cst := cst) hm with
    he | ⟨he, _⟩
  · rw [he]; exact h
  · rw [he, vStep_fst]; exact scanStep_inv hK h

theorem mactsX_inv {u v T : List α} {k p₁ r : ℕ} {cst : VState → ℕ} (hK : KSimple v k p₁ r)
    (hk : 0 < k) (hv : 0 < v.length) {n : ℕ} :
    ∀ (j : ℕ) (m : MStateX), MInvX v n m → ScanInv v T m.z.1 →
      ScanInv v T (mactsX u v k p₁ r T cst n j m).z.1 := by
  intro j
  induction j with
  | zero => intro m _ h; exact h
  | succ j ih =>
    intro m hm h
    exact ih _ (mactX_MInvX hk hv h.2 hm) (mactX_inv hK hm h)

theorem mactsX_MInvX {u v T : List α} {k p₁ r : ℕ} {cst : VState → ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) {n : ℕ} :
    ∀ (j : ℕ) (m : MStateX), MInvX v n m → ScanInv v T m.z.1 →
      MInvX v n (mactsX u v k p₁ r T cst n j m) := by
  intro j
  induction j with
  | zero => intro m h _; exact h
  | succ j ih =>
    intro m hm h
    exact ih _ (mactX_MInvX hk hv h.2 hm) (mactX_inv hK hm h)

theorem meteredX_inv {u v T : List α} {k p₁ r A B' : ℕ} {cst : VState → ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) :
    ∀ n, ScanInv v T (meteredX u v k p₁ r T cst A B' n).z.1 ∧
      MInvX v n (meteredX u v k p₁ r T cst A B' n) := by
  intro n
  induction n with
  | zero =>
    exact ⟨⟨matchLen_zero v T u.length, Nat.zero_le _⟩,
      ⟨fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd rfl h, Nat.zero_le _⟩⟩
  | succ n ih =>
    exact ⟨mactsX_inv hK hk hv _ _ (ih.2.mono (Nat.le_succ n)) ih.1,
      mactsX_MInvX hK hk hv _ _ (ih.2.mono (Nat.le_succ n)) ih.1⟩

/-! ## 4. `MOkX` / `MParkX` -/

def MOkX (cst : VState → ℕ) (m : MStateX) : Prop := m.rem ≤ cst m.z

theorem mactX_MOkX {u v T : List α} {k p₁ r : ℕ} {cst : VState → ℕ} {n : ℕ} {m : MStateX}
    (h : MOkX cst m) : MOkX cst (mactX u v k p₁ r T cst n m) := by
  unfold MOkX at h ⊢
  unfold mactX
  split_ifs with h0 he hc h1
  · simp
  · simp <;> omega
  · exact h
  · simp
  · simp <;> omega

def MParkX (cst : VState → ℕ) (m : MStateX) : Prop := m.rem ≠ 0 → 2 ≤ cst m.z

theorem mactX_MParkX {u v T : List α} {k p₁ r : ℕ} {cst : VState → ℕ} {n : ℕ} {m : MStateX}
    (h : MParkX cst m) : MParkX cst (mactX u v k p₁ r T cst n m) := by
  unfold MParkX at h ⊢
  unfold mactX
  split_ifs with h0 he hc h1
  · simp
  · simp; omega
  · exact h
  · simp
  · simp only [MStateX.mk_z, MStateX.mk_rem]
    intro _; exact h h0

theorem mactX_q_le {u v T : List α} {k p₁ r : ℕ} {cst : VState → ℕ} {n : ℕ} {m : MStateX}
    (hq : m.z.1.q ≤ v.length) : (mactX u v k p₁ r T cst n m).z.1.q ≤ v.length := by
  unfold mactX
  split_ifs with h0 he hc h1
  · rw [MStateX.mk_z, vStep_fst]; exact scanStep_q_le hq
  · simpa using hq
  · exact hq
  · rw [MStateX.mk_z, vStep_fst]; exact scanStep_q_le hq
  · simpa using hq

theorem meteredX_MOkX {u v T : List α} {k p₁ r A B' : ℕ} {cst : VState → ℕ} :
    ∀ n, MOkX cst (meteredX u v k p₁ r T cst A B' n) := by
  have step : ∀ (j : ℕ) (n : ℕ) (m : MStateX), MOkX cst m →
      MOkX cst (mactsX u v k p₁ r T cst n j m) := by
    intro j
    induction j with
    | zero => intro n m h; exact h
    | succ j ih => intro n m h; exact ih _ _ (mactX_MOkX h)
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact step _ _ _ ih

theorem meteredX_MParkX {u v T : List α} {k p₁ r A B' : ℕ} {cst : VState → ℕ} :
    ∀ n, MParkX cst (meteredX u v k p₁ r T cst A B' n) := by
  have step : ∀ (j : ℕ) (n : ℕ) (m : MStateX), MParkX cst m →
      MParkX cst (mactsX u v k p₁ r T cst n j m) := by
    intro j
    induction j with
    | zero => intro n m h; exact h
    | succ j ih => intro n m h; exact ih _ _ (mactX_MParkX h)
  intro n
  induction n with
  | zero => intro h; exact absurd rfl h
  | succ n ih => exact step _ _ _ ih

/-! ## 5. ポテンシャル（両側形） -/

/-- 計量ポテンシャル（`Metered.MPot` と同形）。 -/
def MPotX (k C : ℕ) (cst : VState → ℕ) (m : MStateX) : ℕ :=
  C * Phi k m.z.1 + (if m.rem = 0 then 0 else cst m.z - m.rem)

theorem MPotX_boundary {k C : ℕ} {cst : VState → ℕ} {m : MStateX} (h : m.rem = 0) :
    MPotX k C cst m = C * Phi k m.z.1 := by
  simp [MPotX, h]

/-- **1 動作でポテンシャルは 1 増える（両側形）**。`Ψ` を引き算せずに表すため、
`Ψ(次) ` を左辺、`Ψ(今)` を右辺に置く。この形は telescoping する。 -/
theorem mactX_pot {u v T : List α} {k p₁ r C : ℕ} {cst : VState → ℕ}
    (hk : 0 < k) (hp : 0 < p₁) (hC : 0 < C) (hpos : ∀ z, 1 ≤ cst z)
    (hcost : ∀ z : VState, cst z + Pot (vStep u v k p₁ r T z)
      ≤ C * (Phi k (vStep u v k p₁ r T z).1 - Phi k z.1) + Pot z)
    {n : ℕ} {m : MStateX} (hok : MOkX cst m) :
    (m.rem = 0 ∧ ¬ Enabled v n m.z.1 ∧ mactX u v k p₁ r T cst n m = m) ∨
      MPotX k C cst m + 1 + Pot ((mactX u v k p₁ r T cst n m).z)
        ≤ MPotX k C cst (mactX u v k p₁ r T cst n m) + Pot m.z := by
  by_cases h0 : m.rem = 0
  · by_cases he : Enabled v n m.z.1
    · refine Or.inr ?_
      unfold mactX MPotX
      rw [if_pos h0, if_pos he]
      by_cases hc : cst m.z ≤ 1
      · rw [if_pos hc]
        simp only [MStateX.mk_z, MStateX.mk_rem, if_pos h0, if_pos (rfl : (0:ℕ) = 0)]
        have h1 := hcost m.z
        have h2 := hpos m.z
        have hkey : C * Phi k m.z.1 + C * (Phi k (vStep u v k p₁ r T m.z).1 - Phi k m.z.1)
            = C * Phi k (vStep u v k p₁ r T m.z).1 := by
          rw [← Nat.mul_add]
          congr 1
          have hlt := phi_step_lt (v := v) (T := T) (p₁ := p₁) (r := r) hk hp m.z.1
          rw [vStep_fst]
          omega
        omega
      · rw [if_neg hc]
        simp only [MStateX.mk_z, MStateX.mk_rem, if_pos h0]
        rw [if_neg (by omega)]
        omega
    · exact Or.inl ⟨h0, he, by unfold mactX; rw [if_pos h0, if_neg he]⟩
  · refine Or.inr ?_
    have hokc : m.rem ≤ cst m.z := hok
    unfold mactX MPotX
    rw [if_neg h0]
    by_cases h1 : m.rem = 1
    · rw [if_pos h1]
      simp only [MStateX.mk_z, MStateX.mk_rem, if_neg h0, if_pos (rfl : (0:ℕ) = 0)]
      have hcst := hcost m.z
      have hlt := phi_step_lt (v := v) (T := T) (p₁ := p₁) (r := r) hk hp m.z.1
      have hkey : C * Phi k m.z.1 + C * (Phi k (vStep u v k p₁ r T m.z).1 - Phi k m.z.1)
          = C * Phi k (vStep u v k p₁ r T m.z).1 := by
        rw [← Nat.mul_add]
        congr 1
        rw [vStep_fst]
        omega
      omega
    · rw [if_neg h1]
      simp only [MStateX.mk_z, MStateX.mk_rem, if_neg h0]
      rw [if_neg (by omega)]
      omega

/-! ## 6. 遅れ有界性（`Ψ ≤ 4|v|` の加法定数つき） -/

section Lag

variable {u v T : List α} {k p₁ r A B' : ℕ} {cst : VState → ℕ}

/-- 1 ラウンド内の評価（`Metered.macts_pot` の `Ψ` 版）。`Ψ` は左辺に載せて
telescoping させ、フロンティア停止ケースでは `MInvX` の `checked ≤ 2q` と
`q ≤ |v|` から `Ψ ≤ 4|v|` として加法定数に落とす。 -/
theorem mactsX_pot (hk : 0 < k) (hp : 0 < p₁) (hv : 0 < v.length) (hC : 0 < A + B')
    (hpos : ∀ z, 1 ≤ cst z)
    (hcost : ∀ z : VState, cst z + Pot (vStep u v k p₁ r T z)
      ≤ (A + B') * (Phi k (vStep u v k p₁ r T z).1 - Phi k z.1) + Pot z)
    {n : ℕ} :
    ∀ (j : ℕ) (m : MStateX) (b : ℕ), m.z.1.q ≤ v.length → MOkX cst m → MInvX v n m →
      b + Pot m.z ≤ MPotX k (A + B') cst m + j + (A + B') * (k * v.length) + 4 * v.length →
      b ≤ (A + B') * ((k + 1) * n) →
      b + Pot ((mactsX u v k p₁ r T cst n j m).z)
        ≤ MPotX k (A + B') cst (mactsX u v k p₁ r T cst n j m)
          + (A + B') * (k * v.length) + 4 * v.length := by
  set C := A + B' with hCdef
  intro j
  induction j with
  | zero => intro m b _ _ _ h _; simpa only [mactsX, Nat.add_zero] using h
  | succ j ih =>
    intro m b hq hok hmi h1 h2
    simp only [mactsX]
    rcases mactX_pot (u := u) (v := v) (T := T) (p₁ := p₁) (r := r) (cst := cst) (n := n)
      hk hp hC hpos hcost hok with ⟨h0, hne, heq⟩ | hgain
    · -- フロンティアで停止：以降の動作もすべて自明
      have hstop : ∀ (i : ℕ), mactsX u v k p₁ r T cst n i m = m := by
        intro i
        induction i with
        | zero => rfl
        | succ i ihi => simp only [mactsX, heq]; exact ihi
      rw [heq, hstop j]
      have hqe : m.z.1.q ≠ v.length := fun h => hne (Or.inl h)
      have hge : n ≤ m.z.1.pos + m.z.1.q := by
        by_contra hc
        exact hne (Or.inr (by omega))
      have e1 : (k + 1) * n ≤ Phi k m.z.1 + k * v.length := by
        have e2 : (k + 1) * n ≤ (k + 1) * (m.z.1.pos + m.z.1.q) := Nat.mul_le_mul_left _ hge
        have e3 : (k + 1) * (m.z.1.pos + m.z.1.q)
            = (k + 1) * m.z.1.pos + (k * m.z.1.q + m.z.1.q) := by ring
        have e4 : k * m.z.1.q ≤ k * v.length := Nat.mul_le_mul_left _ hq
        have e5 : Phi k m.z.1 = (k + 1) * m.z.1.pos + m.z.1.q := rfl
        omega
      have e6 : C * ((k + 1) * n) ≤ C * (Phi k m.z.1 + k * v.length) :=
        Nat.mul_le_mul_left _ e1
      have e7 : C * (Phi k m.z.1 + k * v.length)
          = C * Phi k m.z.1 + C * (k * v.length) := by ring
      have e8 : MPotX k C cst m = C * Phi k m.z.1 := MPotX_boundary h0
      -- `Ψ ≤ 4|v|`
      have e9 : Pot m.z ≤ 4 * v.length := by
        have hc2 := hmi.2.2
        have hq4 : 2 * m.z.1.q ≤ 2 * v.length := Nat.mul_le_mul_left 2 hq
        show 2 * m.z.2 ≤ 4 * v.length
        omega
      omega
    · exact ih _ b (mactX_q_le hq) (mactX_MOkX hok)
        (mactX_MInvX (T := T) (cst := cst) hk hv hq hmi) (by omega) h2

/-- **遅れ有界性（`Ψ` 版）**：加法定数が `Metered.metered_pot` より `4*|v|` 大きい。 -/
theorem meteredX_pot (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    (hC : 0 < A + B') (hpos : ∀ z, 1 ≤ cst z)
    (hcost : ∀ z : VState, cst z + Pot (vStep u v k p₁ r T z)
      ≤ (A + B') * (Phi k (vStep u v k p₁ r T z).1 - Phi k z.1) + Pot z) :
    ∀ n, (A + B') * ((k + 1) * n) + Pot (meteredX u v k p₁ r T cst A B' n).z
        ≤ MPotX k (A + B') cst (meteredX u v k p₁ r T cst A B' n)
          + (A + B') * (k * v.length) + 4 * v.length := by
  intro n
  induction n with
  | zero => simp [meteredX, Pot]
  | succ n ih =>
    have hq : (meteredX u v k p₁ r T cst A B' n).z.1.q ≤ v.length :=
      (meteredX_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst) hK hk hv n).1.2
    have hmi := (meteredX_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst)
      hK hk hv n).2
    have hsplit : (A + B') * ((k + 1) * (n + 1))
        = (A + B') * ((k + 1) * n) + (k + 1) * (A + B') := by ring
    exact mactsX_pot hk hK.period_pos hv hC hpos hcost (mRate A B' k)
      (meteredX u v k p₁ r T cst A B' n) ((A + B') * ((k + 1) * (n + 1))) hq
      (meteredX_MOkX n) (hmi.mono (Nat.le_succ n))
      (by simp only [mRate]; omega) (le_refl _)

/-- **ステップ境界での `Φ` の下界**（`Metered.metered_phi_boundary` の `Ψ` 版）。
`Metered` 版との違いは末尾の `+ 4 * v.length` だけである。 -/
theorem meteredX_phi_boundary (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    (hC : 0 < A + B') (hpos : ∀ z, 1 ≤ cst z)
    (hcost : ∀ z : VState, cst z + Pot (vStep u v k p₁ r T z)
      ≤ (A + B') * (Phi k (vStep u v k p₁ r T z).1 - Phi k z.1) + Pot z) {n : ℕ}
    (hb : (meteredX u v k p₁ r T cst A B' n).rem = 0) :
    (k + 1) * n ≤ Phi k (meteredX u v k p₁ r T cst A B' n).z.1 + k * v.length
      + 4 * v.length := by
  set m := meteredX u v k p₁ r T cst A B' n with hm
  have hpot := meteredX_pot (u := u) hK hk hv hC hpos hcost n
  rw [← hm] at hpot
  rw [MPotX_boundary hb] at hpot
  have h4 : 4 * v.length ≤ (A + B') * (4 * v.length) := Nat.le_mul_of_pos_left _ hC
  have hexp : (A + B') * (Phi k m.z.1 + k * v.length + 4 * v.length)
      = (A + B') * Phi k m.z.1 + (A + B') * (k * v.length)
        + (A + B') * (4 * v.length) := by ring
  have h2 : (A + B') * ((k + 1) * n)
      ≤ (A + B') * (Phi k m.z.1 + k * v.length + 4 * v.length) := by omega
  exact Nat.le_of_mul_le_mul_left h2 hC

end Lag

/-! ## 7. 報告と健全性 -/

section Report

variable {u v T : List α} {k p₁ r A B' : ℕ} {cst : VState → ℕ}

/-- ラウンド `n` の `j` 動作の途中（先頭を含む）に報告状態が現れたか。 -/
def mreportedX (u v : List α) (k p₁ r : ℕ) (T : List α) (cst : VState → ℕ) (n : ℕ) :
    ℕ → MStateX → Bool
  | 0, m => reportFlag v n m.z.1
  | j + 1, m =>
      reportFlag v n m.z.1 || mreportedX u v k p₁ r T cst n j (mactX u v k p₁ r T cst n m)

theorem mreportedX_sound (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) {n : ℕ} :
    ∀ (j : ℕ) (m : MStateX), ScanInv v T m.z.1 → MInvX v n m →
      mreportedX u v k p₁ r T cst n j m = true → ∃ p, p + v.length = n ∧ OccAt v T p := by
  have base : ∀ (m : MStateX), ScanInv v T m.z.1 → reportFlag v n m.z.1 = true →
      ∃ p, p + v.length = n ∧ OccAt v T p := by
    intro m hinv h
    simp only [reportFlag, decide_eq_true_eq] at h
    refine ⟨m.z.1.pos, h.2, ?_⟩
    have hm := hinv.1
    rw [h.1] at hm
    exact hm
  intro j
  induction j with
  | zero => intro m hinv _ h; exact base m hinv h
  | succ j ih =>
    intro m hinv hmi h
    simp only [mreportedX, Bool.or_eq_true] at h
    rcases h with h | h
    · exact base m hinv h
    · exact ih _ (mactX_inv hK hmi hinv) (mactX_MInvX hk hv hinv.2 hmi) h

theorem mreportedX_false_final {n : ℕ} :
    ∀ (j : ℕ) (m : MStateX), mreportedX u v k p₁ r T cst n j m = false →
      reportFlag v n (mactsX u v k p₁ r T cst n j m).z.1 = false := by
  intro j
  induction j with
  | zero => intro m h; exact h
  | succ j ih =>
    intro m h
    simp only [mreportedX, Bool.or_eq_false_iff] at h
    exact ih _ h.2

/-- 追い越し禁止（`Metered.macts_pos_le` の `Ψ` 版）。 -/
theorem mactsX_pos_le (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) {i n : ℕ}
    (hocc : OccAt v T i) (hn : n ≤ i + v.length) :
    ∀ (j : ℕ) (m : MStateX), ScanInv v T m.z.1 → MInvX v n m → m.z.1.pos ≤ i →
      (n < i + v.length ∨ mreportedX u v k p₁ r T cst n j m = false) →
      (mactsX u v k p₁ r T cst n j m).z.1.pos ≤ i := by
  intro j
  induction j with
  | zero => intro m _ _ hp _; exact hp
  | succ j ih =>
    intro m hinv hmi hp hd
    simp only [mactsX]
    have hne : m.z.1.q = v.length → m.z.1.pos ≠ i := by
      intro hqe
      have hle : m.z.1.pos + m.z.1.q ≤ n := hmi.1 (by omega)
      rcases hd with hlt | hrep
      · omega
      · simp only [mreportedX, Bool.or_eq_false_iff] at hrep
        have hf0 := hrep.1
        simp only [reportFlag, decide_eq_false_iff_not, not_and] at hf0
        intro hpi
        exact hf0 hqe (by omega)
    have hstep : (mactX u v k p₁ r T cst n m).z.1.pos ≤ i := by
      rcases mactX_z_cases (u := u) (k := k) (p₁ := p₁) (r := r) (T := T) (cst := cst) hmi with
        he | ⟨he, _⟩
      · rw [he]; exact hp
      · rw [he, vStep_fst]; exact scanStep_pos_le_of_occ hK hk hinv hocc hp hne
    refine ih _ (mactX_inv hK hmi hinv) (mactX_MInvX hk hv hinv.2 hmi) hstep ?_
    rcases hd with hlt | hrep
    · exact Or.inl hlt
    · refine Or.inr ?_
      simp only [mreportedX, Bool.or_eq_false_iff] at hrep
      exact hrep.2

theorem meteredX_pos_le (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) {i : ℕ}
    (hi : u.length ≤ i) (hocc : OccAt v T i) :
    ∀ n, n < i + v.length → (meteredX u v k p₁ r T cst A B' n).z.1.pos ≤ i := by
  intro n
  induction n with
  | zero => intro _; exact hi
  | succ n ih =>
    intro hlt
    have hinv := meteredX_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst) hK hk hv n
    exact mactsX_pos_le hK hk hv hocc (by omega) _ _ hinv.1
      (hinv.2.mono (Nat.le_succ n)) (ih (by omega)) (Or.inl hlt)

/-- 計量式スケジューラのラウンド `n` の出力。 -/
def manswerX (u v : List α) (k p₁ r : ℕ) (T : List α) (cst : VState → ℕ) (A B' : ℕ) :
    ℕ → Bool
  | 0 => false
  | n + 1 =>
      mreportedX u v k p₁ r T cst (n + 1) (mRate A B' k) (meteredX u v k p₁ r T cst A B' n) &&
        decide (MatchLen u T (n + 1 - (u.length + v.length)) u.length)

/-- **答えの健全性**（遅れ有界性を使わない側）。 -/
theorem manswerX_sound (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    (n : ℕ) (hn : (u ++ v).length ≤ n)
    (h : manswerX u v k p₁ r T cst A B' n = true) :
    OccAt (u ++ v) T (n - (u ++ v).length) := by
  simp only [List.length_append] at hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [manswerX, Bool.and_eq_true, decide_eq_true_eq] at h
  have hinvm := meteredX_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst) hK hk hv m
  obtain ⟨p, hp, hocc⟩ := mreportedX_sound hK hk hv _ _ hinvm.1
    (hinvm.2.mono (Nat.le_succ m)) h.1
  have hpos : m + 1 - (u.length + v.length) + u.length = p := by omega
  simp only [List.length_append]
  rw [occAt_append_iff, hpos]
  exact ⟨h.2, hocc⟩

end Report

/-! ## 8. 残る穴：締切ラウンドでの **余裕ゼロ** の遅れ有界性

`Metered.mreported_complete` / `Metered.metered_boundary_of_occ` の最後は

  `(k+1)(n+1) ≤ (k+1)P + Q + k|v|`,  `(k+1)P ≤ (k+1)i`,
  `(k+1)(n+1) = (k+1)i + k|v| + |v|`

から `|v| ≤ Q` を出す **余裕ゼロ** の算術である。`meteredX_phi_boundary` の
`+ 4*|v|` はこの余裕を食い潰すので、完全性はそのままでは移らない。
ラウンドあたりの動作数 `B` を増やしても効かない：フロンティアでは
`Φ ≤ (k+1)*n` が上限なので、ポテンシャル不等式はそれ以上強くならない。

残る穴はちょうど次の 2 つ（`Metered` 版とまったく同じ形の遅れ有界性）である。 -/

section Gap

variable (u v T : List α) (k p₁ r A B' : ℕ) (cst : VState → ℕ)

/-- 締切ラウンドで必要な、**加法定数 `4|v|` なし**の遅れ有界性（ステップ境界）。 -/
def TightLagBoundary : Prop :=
  ∀ n, (meteredX u v k p₁ r T cst A B' n).rem = 0 →
    (k + 1) * n ≤ Phi k (meteredX u v k p₁ r T cst A B' n).z.1 + k * v.length

/-- 同（停留中の仮想ポテンシャル版、`Metered.metered_phi_virtual` に対応）。 -/
def TightLagVirtual : Prop :=
  ∀ n, (k + 1) * n
    ≤ Phi k (vStep u v k p₁ r T (meteredX u v k p₁ r T cst A B' n).z).1 + k * v.length

/-- **停留（フロンティア）状態では遅れ有界性は無条件に成り立つ**（`Ψ` は要らない）。
`¬ Enabled` は `q ≠ |v| ∧ n ≤ pos + q` を与えるので `(k+1)n ≤ Φ + k·q ≤ Φ + k|v|`。 -/
theorem stuck_lag_tight {v : List α} {k n : ℕ} {m : MStateX} (hq : m.z.1.q ≤ v.length)
    (hne : ¬ Enabled v n m.z.1) :
    (k + 1) * n ≤ Phi k m.z.1 + k * v.length := by
  have hge : n ≤ m.z.1.pos + m.z.1.q := by
    by_contra hc
    exact hne (Or.inr (by omega))
  have e2 : (k + 1) * n ≤ (k + 1) * (m.z.1.pos + m.z.1.q) := Nat.mul_le_mul_left _ hge
  have e3 : (k + 1) * (m.z.1.pos + m.z.1.q)
      = (k + 1) * m.z.1.pos + (k * m.z.1.q + m.z.1.q) := by ring
  have e4 : k * m.z.1.q ≤ k * v.length := Nat.mul_le_mul_left _ hq
  have e5 : Phi k m.z.1 = (k + 1) * m.z.1.pos + m.z.1.q := rfl
  omega

/-- **借金と余裕**：`Ψ` を担いだラウンド不変条件を閉じるのに必要な唯一の不等式。
フロンティア停止状態で「未払いの借金 `Ψ` は残りの `q` 余裕で賄える」。 -/
def DebtSlack (v : List α) (k C : ℕ) : Prop :=
  ∀ z : VState, z.2 ≤ 2 * z.1.q → z.1.q ≤ v.length → z.1.q ≠ v.length →
    Pot z ≤ C * (k * (v.length - z.1.q))

/-- **`DebtSlack` は（状態述語としては）偽である**：`q = |v| − 1`, `checked = 2q` は
`VCheckedInv` を満たすが、余裕は `C*k*1` しかない。したがって
「`Ψ` を担いだラウンド不変条件」で `TightLagBoundary` を出す道は塞がっている。 -/
theorem debtSlack_false {k C L : ℕ} (hL : 2 ≤ L) (hbig : C * k + 4 < 4 * L) :
    ¬ DebtSlack (List.replicate L (Classical.arbitrary (α := ℕ))) k C := by
  intro h
  have hlen : (List.replicate L (Classical.arbitrary (α := ℕ))).length = L :=
    List.length_replicate
  have hq : (((⟨0, L - 1⟩ : ScanState), 2 * (L - 1)) : VState).1.q = L - 1 := rfl
  have hc : (((⟨0, L - 1⟩ : ScanState), 2 * (L - 1)) : VState).2 = 2 * (L - 1) := rfl
  have hmain := h ((⟨0, L - 1⟩ : ScanState), 2 * (L - 1))
    (by rw [hq, hc]) (by rw [hq, hlen]; omega) (by rw [hq, hlen]; omega)
  rw [hq, hlen] at hmain
  have hP : Pot (((⟨0, L - 1⟩ : ScanState), 2 * (L - 1)) : VState) = 2 * (2 * (L - 1)) := by
    rw [Pot, hc]
  rw [hP, show L - (L - 1) = 1 from by omega, Nat.mul_one] at hmain
  omega

end Gap

/-! ## 9. 穴を仮定した完全性と主定理

以下は `Metered` の完全性の議論をそのまま `Ψ` 版へ移したもので、**唯一の追加仮定**が
`TightLagBoundary` / `TightLagVirtual`（＝ `§8` の穴）である。`hcost` は
`XAmortized` を `costX_le_of_amortized` で潰した形、`hadvance` は `Metered` と同じ。 -/

section Complete

variable {u v T : List α} {k p₁ r A B' : ℕ} {cst : VState → ℕ}

/-- **完全性（ステップ境界版）**。 -/
theorem mreportedX_complete (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    (hLag : TightLagBoundary u v T k p₁ r A B' cst)
    {i n : ℕ} (hi : u.length ≤ i) (hocc : OccAt v T i) (hin : i + v.length = n + 1)
    (hb : (meteredX u v k p₁ r T cst A B' (n + 1)).rem = 0) :
    mreportedX u v k p₁ r T cst (n + 1) (mRate A B' k) (meteredX u v k p₁ r T cst A B' n)
      = true := by
  by_contra hcon
  rw [Bool.not_eq_true] at hcon
  have hst : mactsX u v k p₁ r T cst (n + 1) (mRate A B' k)
      (meteredX u v k p₁ r T cst A B' n) = meteredX u v k p₁ r T cst A B' (n + 1) := rfl
  have hinvn := meteredX_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst) hK hk hv n
  have hpos0 : (meteredX u v k p₁ r T cst A B' n).z.1.pos ≤ i :=
    meteredX_pos_le hK hk hv hi hocc n (by omega)
  have hposF : (meteredX u v k p₁ r T cst A B' (n + 1)).z.1.pos ≤ i := by
    rw [← hst]
    exact mactsX_pos_le hK hk hv hocc (by omega) _ _ hinvn.1
      (hinvn.2.mono (Nat.le_succ n)) hpos0 (Or.inr hcon)
  have hflagF : reportFlag v (n + 1) (meteredX u v k p₁ r T cst A B' (n + 1)).z.1 = false := by
    rw [← hst]
    exact mreportedX_false_final _ _ hcon
  have hinvF := meteredX_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst) hK hk hv (n + 1)
  have hqF : (meteredX u v k p₁ r T cst A B' (n + 1)).z.1.q ≤ v.length := hinvF.1.2
  have hfitsF : Fits (n + 1) (meteredX u v k p₁ r T cst A B' (n + 1)).z.1 := hinvF.2.1
  have hphi := hLag (n + 1) hb
  set P := (meteredX u v k p₁ r T cst A B' (n + 1)).z.1.pos with hP
  set Q := (meteredX u v k p₁ r T cst A B' (n + 1)).z.1.q with hQdef
  have hphi' : (k + 1) * (n + 1) ≤ (k + 1) * P + Q + k * v.length := by
    have e : Phi k (meteredX u v k p₁ r T cst A B' (n + 1)).z.1 = (k + 1) * P + Q := rfl
    omega
  have h1 : (k + 1) * P ≤ (k + 1) * i := Nat.mul_le_mul_left _ hposF
  have e1 : (k + 1) * (n + 1) = (k + 1) * i + (k + 1) * v.length := by rw [← hin]; ring
  have e2 : (k + 1) * v.length = k * v.length + v.length := by ring
  have hQ : Q = v.length := by omega
  have hfit : P + Q ≤ n + 1 := hfitsF (by omega)
  have h3 : (k + 1) * i ≤ (k + 1) * P := by omega
  have h4 : i ≤ P := Nat.le_of_mul_le_mul_left h3 (by omega)
  have hPi : P = i := by omega
  simp only [reportFlag, decide_eq_false_iff_not, not_and] at hflagF
  exact hflagF hQ (by omega)

/-- **停留しない**（`Metered.metered_boundary_of_occ` の `Ψ` 版）。 -/
theorem meteredX_boundary_of_occ (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    (hLagV : TightLagVirtual u v T k p₁ r A B' cst)
    (hadvance : ∀ z : VState, z.1.q ≠ v.length → T[z.1.pos + z.1.q]? = v[z.1.q]? →
      cst z ≤ 1)
    {i n : ℕ} (hi : u.length ≤ i) (hocc : OccAt v T i) (hin : i + v.length = n + 1)
    (hcon : mreportedX u v k p₁ r T cst (n + 1) (mRate A B' k)
      (meteredX u v k p₁ r T cst A B' n) = false) :
    (meteredX u v k p₁ r T cst A B' (n + 1)).rem = 0 := by
  by_contra hrem
  have hst : mactsX u v k p₁ r T cst (n + 1) (mRate A B' k)
      (meteredX u v k p₁ r T cst A B' n) = meteredX u v k p₁ r T cst A B' (n + 1) := rfl
  have hinvn := meteredX_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst) hK hk hv n
  have hpos0 : (meteredX u v k p₁ r T cst A B' n).z.1.pos ≤ i :=
    meteredX_pos_le hK hk hv hi hocc n (by omega)
  have hposF : (meteredX u v k p₁ r T cst A B' (n + 1)).z.1.pos ≤ i := by
    rw [← hst]
    exact mactsX_pos_le hK hk hv hocc (by omega) _ _ hinvn.1
      (hinvn.2.mono (Nat.le_succ n)) hpos0 (Or.inr hcon)
  have hflagF : reportFlag v (n + 1) (meteredX u v k p₁ r T cst A B' (n + 1)).z.1 = false := by
    rw [← hst]
    exact mreportedX_false_final _ _ hcon
  have hinvF := meteredX_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst) hK hk hv (n + 1)
  have hqF : (meteredX u v k p₁ r T cst A B' (n + 1)).z.1.q ≤ v.length := hinvF.1.2
  have hfitsF : Fits (n + 1) (meteredX u v k p₁ r T cst A B' (n + 1)).z.1 := hinvF.2.1
  have hpark : 2 ≤ cst (meteredX u v k p₁ r T cst A B' (n + 1)).z :=
    meteredX_MParkX (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) (T := T) (A := A) (B' := B')
      (n + 1) hrem
  have hnadv : ¬ ((meteredX u v k p₁ r T cst A B' (n + 1)).z.1.q ≠ v.length ∧
      T[(meteredX u v k p₁ r T cst A B' (n + 1)).z.1.pos
          + (meteredX u v k p₁ r T cst A B' (n + 1)).z.1.q]?
        = v[(meteredX u v k p₁ r T cst A B' (n + 1)).z.1.q]?) := by
    rintro ⟨h1, h2⟩
    have := hadvance _ h1 h2
    omega
  have hq'ne : (scanStep v k p₁ r T (meteredX u v k p₁ r T cst A B' (n + 1)).z.1).q
      ≠ v.length := scanStep_q_ne_of_not_advance hK.period_pos hv hqF hnadv
  have hne : (meteredX u v k p₁ r T cst A B' (n + 1)).z.1.q = v.length →
      (meteredX u v k p₁ r T cst A B' (n + 1)).z.1.pos ≠ i := by
    intro hqe
    have hle : (meteredX u v k p₁ r T cst A B' (n + 1)).z.1.pos
        + (meteredX u v k p₁ r T cst A B' (n + 1)).z.1.q ≤ n + 1 := hfitsF (by omega)
    simp only [reportFlag, decide_eq_false_iff_not, not_and] at hflagF
    intro hpi
    exact hflagF hqe (by omega)
  have hpos' : (scanStep v k p₁ r T (meteredX u v k p₁ r T cst A B' (n + 1)).z.1).pos ≤ i :=
    scanStep_pos_le_of_occ hK hk hinvF.1 hocc hposF hne
  have hq' : (scanStep v k p₁ r T (meteredX u v k p₁ r T cst A B' (n + 1)).z.1).q
      ≤ v.length := scanStep_q_le hqF
  have hvirt := hLagV (n + 1)
  rw [vStep_fst] at hvirt
  set P := (scanStep v k p₁ r T (meteredX u v k p₁ r T cst A B' (n + 1)).z.1).pos with hP
  set Q := (scanStep v k p₁ r T (meteredX u v k p₁ r T cst A B' (n + 1)).z.1).q with hQ
  have hphi' : (k + 1) * (n + 1) ≤ (k + 1) * P + Q + k * v.length := by
    have e : Phi k (scanStep v k p₁ r T (meteredX u v k p₁ r T cst A B' (n + 1)).z.1)
        = (k + 1) * P + Q := rfl
    omega
  have h1 : (k + 1) * P ≤ (k + 1) * i := Nat.mul_le_mul_left _ hpos'
  have e1 : (k + 1) * (n + 1) = (k + 1) * i + (k + 1) * v.length := by rw [← hin]; ring
  have e2 : (k + 1) * v.length = k * v.length + v.length := by ring
  exact hq'ne (by omega)

/-- **`rem = 0` の仮定を外した完全性**。 -/
theorem mreportedX_complete' (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    (hLag : TightLagBoundary u v T k p₁ r A B' cst)
    (hLagV : TightLagVirtual u v T k p₁ r A B' cst)
    (hadvance : ∀ z : VState, z.1.q ≠ v.length → T[z.1.pos + z.1.q]? = v[z.1.q]? →
      cst z ≤ 1)
    {i n : ℕ} (hi : u.length ≤ i) (hocc : OccAt v T i) (hin : i + v.length = n + 1) :
    mreportedX u v k p₁ r T cst (n + 1) (mRate A B' k) (meteredX u v k p₁ r T cst A B' n)
      = true := by
  by_cases hcon : mreportedX u v k p₁ r T cst (n + 1) (mRate A B' k)
      (meteredX u v k p₁ r T cst A B' n) = true
  · exact hcon
  · rw [Bool.not_eq_true] at hcon
    exact mreportedX_complete hK hk hv hLag hi hocc hin
      (meteredX_boundary_of_occ hK hk hv hLagV hadvance hi hocc hin hcon)

/-- **`Ψ` 版の計量式実時間定理**（`Metered.metered_answer_correct'` の対応物）。
追加仮定は `§8` の遅れ有界性 `TightLagBoundary` / `TightLagVirtual` だけである。 -/
theorem meteredX_answer_correct' (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    (hLag : TightLagBoundary u v T k p₁ r A B' cst)
    (hLagV : TightLagVirtual u v T k p₁ r A B' cst)
    (hadvance : ∀ z : VState, z.1.q ≠ v.length → T[z.1.pos + z.1.q]? = v[z.1.q]? →
      cst z ≤ 1)
    (n : ℕ) (hn : (u ++ v).length ≤ n) :
    manswerX u v k p₁ r T cst A B' n = decide (OccAt (u ++ v) T (n - (u ++ v).length)) := by
  simp only [List.length_append] at hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set i := m + 1 - v.length with hi
  have hiv : i + v.length = m + 1 := by omega
  have hiu : u.length ≤ i := by omega
  have hinvm := meteredX_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst) hK hk hv m
  have hrep :
      mreportedX u v k p₁ r T cst (m + 1) (mRate A B' k) (meteredX u v k p₁ r T cst A B' m)
        = decide (OccAt v T i) := by
    refine Bool.eq_iff_iff.mpr ?_
    rw [decide_eq_true_eq]
    constructor
    · intro h
      obtain ⟨p, hp, hocc⟩ :=
        mreportedX_sound hK hk hv _ _ hinvm.1 (hinvm.2.mono (Nat.le_succ m)) h
      have : p = i := by omega
      exact this ▸ hocc
    · intro h
      exact mreportedX_complete' hK hk hv hLag hLagV hadvance hiu h hiv
  simp only [manswerX, hrep, List.length_append]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [occAt_append_iff]
  have hpos : m + 1 - (u.length + v.length) + u.length = i := by omega
  rw [hpos]
  exact and_comm

end Complete

/-! ## 10. 公理の確認 -/

#print axioms costX_le_of_amortized
#print axioms mactX_pot
#print axioms mactsX_pot
#print axioms meteredX_pot
#print axioms meteredX_phi_boundary
#print axioms mreportedX_sound
#print axioms mactsX_pos_le
#print axioms manswerX_sound
#print axioms mreportedX_complete
#print axioms meteredX_boundary_of_occ
#print axioms stuck_lag_tight
#print axioms debtSlack_false
#print axioms meteredX_answer_correct'

end MeteredX
end PalPeg
