import PalPeg.GSRealTime

/-!
# 走査段の **de-amortized（計量式）スケジューラ**

`PalPeg.GSRealTime` のオンライン走査は「1 ラウンドに `gsRate k = k+1` **走査ステップ**」
という粒度だった。しかし実機（チューリング機械）が 1 ラウンドに実行できるのは
**固定本数 `B` のテープ動作**であり、走査ステップ 1 回の動作数は有界ではない
（周期ずらし・巻き戻し歩行・検証歩行はポテンシャル増分 `ΔΦ` に比例する）。

本ファイルは、この差を埋める **計量式スケジューラ** を抽象的に定式化する。

* 走査ステップ `st ↦ scanStep v k p₁ r T st` の動作コストを抽象関数 `cst : ScanState → ℕ`
  で表す。仮定は償却形 `cst st ≤ A * ΔΦ + B'`（`GSVerifierTapes` §9 / `VerifierFeed` §16–19 の
  形）。`ΔΦ ≥ 1`（`phi_step_lt`）なので、これは 1 定数形 `cst st ≤ C * ΔΦ`（`C = A + B'`）に潰れる。
* 状態は `MState = (ScanState, 残り動作数)`。`rem = 0` が **ステップ境界**。
* 1 動作 `mact`：境界にいて `Enabled`（フロンティア規則）なら現ステップを開始し、
  そうでなければ実行中ステップの残りを 1 減らす。残りが尽きた瞬間に `scanStep` を適用する。
* 1 ラウンド＝ちょうど `B = mRate A B' k = (k+1)*(A+B')` 動作。

## 主結果

* `metered_pot` : 計量ポテンシャル `MPot` に対する **遅れ有界性**
  `(k+1)*C*n ≤ MPot(…n) + C*(k*|v|)`（追加定数なし）。
* `metered_phi` : そこから読める `Φ` の形
  `(k+1)*n ≤ Φ(st_n) + k*|v| + D` で `D = cst st_n`（＝実行中ステップのコスト＝
  「途中まで払った借金」）。**境界（`rem = 0`）では `D = 0`**：`metered_phi_boundary` が
  `onlineRun_phi` とまったく同じ不等式を与える。
* `metered_answer_correct` : ラウンド `n+1` の答え `manswer` は
  `decide (OccAt (u ++ v) T (n+1 − |x|))` に等しい（`online_answer_correct` と同じ仮定
  ＋「ラウンド `n+1` の終わりがステップ境界」）。

定数： `B = mRate A B' k = (k+1)*(A+B')`、`D = cst st`（境界では `0`）。
-/

namespace PalPeg

universe u
variable {α : Type u}

/-! ## 計量式の状態と 1 動作 -/

/-- 計量式スケジューラの状態：走査状態と、実行中ステップの残り動作数
（`rem = 0` ⟺ ステップ境界）。 -/
structure MState where
  st : ScanState
  rem : ℕ
deriving DecidableEq, Repr

@[simp] theorem MState.mk_st (a : ScanState) (b : ℕ) : (MState.mk a b).st = a := rfl
@[simp] theorem MState.mk_rem (a : ScanState) (b : ℕ) : (MState.mk a b).rem = b := rfl

theorem Enabled.mono {v : List α} {n n' : ℕ} {st : ScanState}
    (h : Enabled v n st) (hn : n ≤ n') : Enabled v n' st := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

variable [DecidableEq α]

/-- **1 テープ動作**。境界（`rem = 0`）では、フロンティア規則 `Enabled` が成り立つときだけ
現ステップを開始する（コスト `≤ 1` なら即完了）。実行中なら残りを 1 減らし、
尽きた瞬間に `scanStep` を適用する。 -/
def mact (v : List α) (k p₁ r : ℕ) (T : List α) (cst : ScanState → ℕ) (n : ℕ)
    (m : MState) : MState :=
  if m.rem = 0 then
    (if Enabled v n m.st then
        (if cst m.st ≤ 1 then ⟨scanStep v k p₁ r T m.st, 0⟩ else ⟨m.st, cst m.st - 1⟩)
      else m)
  else if m.rem = 1 then ⟨scanStep v k p₁ r T m.st, 0⟩
  else ⟨m.st, m.rem - 1⟩

/-- `j` 個の動作。 -/
def macts (v : List α) (k p₁ r : ℕ) (T : List α) (cst : ScanState → ℕ) (n : ℕ) :
    ℕ → MState → MState
  | 0, m => m
  | j + 1, m => macts v k p₁ r T cst n j (mact v k p₁ r T cst n m)

/-- 1 ラウンドあたりのテープ動作数 `B`。 -/
def mRate (A B' k : ℕ) : ℕ := (k + 1) * (A + B')

/-- ラウンド `n` 終了時の計量式状態。 -/
def metered (u v : List α) (k p₁ r : ℕ) (T : List α) (cst : ScanState → ℕ) (A B' : ℕ) :
    ℕ → MState
  | 0 => ⟨⟨u.length, 0⟩, 0⟩
  | n + 1 =>
      macts v k p₁ r T cst (n + 1) (mRate A B' k) (metered u v k p₁ r T cst A B' n)

/-! ## 1 動作の場合分け -/

/-- 状態不変条件：先読み禁止 `Fits`、および「実行中ステップは `Enabled` な状態から
始まっている」。後者は `Enabled` の単調性でラウンドをまたいでも保たれる。 -/
def MInv (v : List α) (n : ℕ) (m : MState) : Prop :=
  Fits n m.st ∧ (m.rem ≠ 0 → Enabled v n m.st)

omit [DecidableEq α] in
theorem MInv.mono {v : List α} {n n' : ℕ} {m : MState} (h : MInv v n m) (hn : n ≤ n') :
    MInv v n' m :=
  ⟨h.1.mono hn, fun hr => (h.2 hr).mono hn⟩

/-- 1 動作で走査状態は「不変」か「`Enabled` な状態からの `scanStep`」のどちらか。 -/
theorem mact_st_cases {v T : List α} {k p₁ r : ℕ} {cst : ScanState → ℕ} {n : ℕ}
    {m : MState} (h : MInv v n m) :
    (mact v k p₁ r T cst n m).st = m.st ∨
      ((mact v k p₁ r T cst n m).st = scanStep v k p₁ r T m.st ∧ Enabled v n m.st) := by
  unfold mact
  split_ifs with h0 he hc h1
  · exact Or.inr ⟨rfl, he⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, h.2 h0⟩
  · exact Or.inl rfl

theorem mact_MInv {v T : List α} {k p₁ r : ℕ} {cst : ScanState → ℕ} (hk : 0 < k)
    (hv : 0 < v.length) {n : ℕ} {m : MState} (hq : m.st.q ≤ v.length) (h : MInv v n m) :
    MInv v n (mact v k p₁ r T cst n m) := by
  unfold mact
  split_ifs with h0 he hc h1
  · exact ⟨scanStep_fits hk hv he h.1, by simp⟩
  · exact ⟨h.1, fun _ => he⟩
  · exact h
  · exact ⟨scanStep_fits hk hv (h.2 h0) h.1, by simp⟩
  · exact ⟨h.1, fun _ => h.2 h0⟩

theorem mact_inv {v T : List α} {k p₁ r : ℕ} {cst : ScanState → ℕ} (hK : KSimple v k p₁ r)
    {n : ℕ} {m : MState} (hm : MInv v n m) (h : ScanInv v T m.st) :
    ScanInv v T (mact v k p₁ r T cst n m).st := by
  rcases mact_st_cases (k := k) (p₁ := p₁) (r := r) (T := T) (cst := cst) hm with he | ⟨he, _⟩
  · rw [he]; exact h
  · rw [he]; exact scanStep_inv hK h

theorem macts_inv {v T : List α} {k p₁ r : ℕ} {cst : ScanState → ℕ} (hK : KSimple v k p₁ r)
    (hk : 0 < k) (hv : 0 < v.length) {n : ℕ} :
    ∀ (j : ℕ) (m : MState), MInv v n m → ScanInv v T m.st →
      ScanInv v T (macts v k p₁ r T cst n j m).st := by
  intro j
  induction j with
  | zero => intro m _ h; exact h
  | succ j ih =>
    intro m hm h
    exact ih _ (mact_MInv hk hv h.2 hm) (mact_inv hK hm h)

theorem macts_MInv {v T : List α} {k p₁ r : ℕ} {cst : ScanState → ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) {n : ℕ} :
    ∀ (j : ℕ) (m : MState), MInv v n m → ScanInv v T m.st →
      MInv v n (macts v k p₁ r T cst n j m) := by
  intro j
  induction j with
  | zero => intro m h _; exact h
  | succ j ih =>
    intro m hm h
    exact ih _ (mact_MInv hk hv h.2 hm) (mact_inv hK hm h)

/-! ## 計量ポテンシャル -/

/-- 計量ポテンシャル `MPot = C·Φ + (実行中ステップで既に払った動作数)`。
境界（`rem = 0`）では `C·Φ` そのもの。 -/
def MPot (k C : ℕ) (cst : ScanState → ℕ) (m : MState) : ℕ :=
  C * Phi k m.st + (if m.rem = 0 then 0 else cst m.st - m.rem)

theorem MPot_boundary {k C : ℕ} {cst : ScanState → ℕ} {m : MState} (h : m.rem = 0) :
    MPot k C cst m = C * Phi k m.st := by
  simp [MPot, h]

/-- 償却形のコスト評価 `cst ≤ A·ΔΦ + B'` は、`ΔΦ ≥ 1` より 1 定数形
`cst ≤ (A+B')·ΔΦ` に潰れる。 -/
theorem cost_le_of_amortized {v T : List α} {k p₁ r A B' : ℕ} {cst : ScanState → ℕ}
    (hk : 0 < k) (hp : 0 < p₁)
    (h : ∀ st, cst st ≤ A * (Phi k (scanStep v k p₁ r T st) - Phi k st) + B')
    (st : ScanState) :
    cst st ≤ (A + B') * (Phi k (scanStep v k p₁ r T st) - Phi k st) := by
  have hlt := phi_step_lt (v := v) (T := T) (p₁ := p₁) (r := r) hk hp st
  set d := Phi k (scanStep v k p₁ r T st) - Phi k st with hd
  have hd1 : 1 ≤ d := by omega
  have h3 : B' ≤ B' * d := by simpa using Nat.mul_le_mul_left B' hd1
  calc cst st ≤ A * d + B' := h st
    _ ≤ A * d + B' * d := Nat.add_le_add_left h3 _
    _ = (A + B') * d := by ring

/-- 実行中ステップの残りは、そのステップのコストを超えない。 -/
def MOk (cst : ScanState → ℕ) (m : MState) : Prop := m.rem ≤ cst m.st

theorem mact_MOk {v T : List α} {k p₁ r : ℕ} {cst : ScanState → ℕ} {n : ℕ} {m : MState}
    (h : MOk cst m) : MOk cst (mact v k p₁ r T cst n m) := by
  unfold MOk at h ⊢
  unfold mact
  split_ifs with h0 he hc h1
  · simp
  · simp <;> omega
  · exact h
  · simp
  · simp <;> omega

/-- 実行中（`rem ≠ 0`）のステップは、コスト `2` 以上のものしかありえない
（コスト `≤ 1` のステップは開始と同時に完了するので停留しない）。 -/
def MPark (cst : ScanState → ℕ) (m : MState) : Prop := m.rem ≠ 0 → 2 ≤ cst m.st

theorem mact_MPark {v T : List α} {k p₁ r : ℕ} {cst : ScanState → ℕ} {n : ℕ} {m : MState}
    (h : MPark cst m) : MPark cst (mact v k p₁ r T cst n m) := by
  unfold MPark at h ⊢
  unfold mact
  split_ifs with h0 he hc h1
  · simp
  · simp; omega
  · exact h
  · simp
  · simp only [MState.mk_st, MState.mk_rem]
    intro _; exact h h0

theorem mact_q_le {v T : List α} {k p₁ r : ℕ} {cst : ScanState → ℕ} {n : ℕ} {m : MState}
    (hq : m.st.q ≤ v.length) : (mact v k p₁ r T cst n m).st.q ≤ v.length := by
  unfold mact
  split_ifs with h0 he hc h1
  · simpa using scanStep_q_le hq
  · simpa using hq
  · exact hq
  · simpa using scanStep_q_le hq
  · simpa using hq

/-- **1 動作で計量ポテンシャルは 1 増える**（フロンティアで止まっている場合を除く）。 -/
theorem mact_pot {v T : List α} {k p₁ r A B' : ℕ} {cst : ScanState → ℕ}
    (hk : 0 < k) (hp : 0 < p₁) (hC : 0 < A + B')
    (hcost : ∀ st, cst st ≤ (A + B') * (Phi k (scanStep v k p₁ r T st) - Phi k st))
    {n : ℕ} {m : MState} (hok : MOk cst m) :
    (m.rem = 0 ∧ ¬ Enabled v n m.st ∧ mact v k p₁ r T cst n m = m) ∨
      MPot k (A + B') cst m + 1 ≤ MPot k (A + B') cst (mact v k p₁ r T cst n m) := by
  set C := A + B' with hCdef
  by_cases h0 : m.rem = 0
  · by_cases he : Enabled v n m.st
    · refine Or.inr ?_
      have hlt := phi_step_lt (v := v) (T := T) (p₁ := p₁) (r := r) hk hp m.st
      unfold mact MPot
      rw [if_pos h0, if_pos he]
      by_cases hc : cst m.st ≤ 1
      · rw [if_pos hc]
        simp only [MState.mk_st, MState.mk_rem, if_pos h0]
        have : C * Phi k m.st + C * 1 ≤ C * Phi k (scanStep v k p₁ r T m.st) := by
          have := Nat.mul_le_mul_left C (show Phi k m.st + 1 ≤ Phi k (scanStep v k p₁ r T m.st)
            from hlt)
          simpa [Nat.mul_add] using this
        omega
      · rw [if_neg hc]
        simp only [MState.mk_st, MState.mk_rem, if_pos h0]
        rw [if_neg (by omega)]
        omega
    · exact Or.inl ⟨h0, he, by unfold mact; rw [if_pos h0, if_neg he]⟩
  · refine Or.inr ?_
    have hokc : m.rem ≤ cst m.st := hok
    unfold mact MPot
    rw [if_neg h0]
    by_cases h1 : m.rem = 1
    · rw [if_pos h1]
      simp only [MState.mk_st, MState.mk_rem, if_neg h0]
      have hlt := phi_step_lt (v := v) (T := T) (p₁ := p₁) (r := r) hk hp m.st
      have hcst := hcost m.st
      have hkey : C * Phi k m.st + C * (Phi k (scanStep v k p₁ r T m.st) - Phi k m.st)
          = C * Phi k (scanStep v k p₁ r T m.st) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      omega
    · rw [if_neg h1]
      simp only [MState.mk_st, MState.mk_rem, if_neg h0]
      rw [if_neg (by omega)]
      omega

/-! ## 遅れ有界性 -/

/-- 1 ラウンド内の評価（`runIn_phi` の計量版）。 -/
theorem macts_pot {v T : List α} {k p₁ r A B' : ℕ} {cst : ScanState → ℕ}
    (hk : 0 < k) (hp : 0 < p₁) (hC : 0 < A + B')
    (hcost : ∀ st, cst st ≤ (A + B') * (Phi k (scanStep v k p₁ r T st) - Phi k st))
    {n : ℕ} :
    ∀ (j : ℕ) (m : MState) (b : ℕ), m.st.q ≤ v.length → MOk cst m →
      b ≤ MPot k (A + B') cst m + j + (A + B') * (k * v.length) →
      b ≤ (A + B') * ((k + 1) * n) →
      b ≤ MPot k (A + B') cst (macts v k p₁ r T cst n j m) + (A + B') * (k * v.length) := by
  set C := A + B' with hCdef
  intro j
  induction j with
  | zero => intro m b _ _ h _; simpa only [macts, Nat.add_zero] using h
  | succ j ih =>
    intro m b hq hok h1 h2
    simp only [macts]
    rcases mact_pot (v := v) (T := T) (p₁ := p₁) (r := r) (cst := cst) (n := n)
      hk hp hC hcost hok with ⟨h0, hne, heq⟩ | hgain
    on_goal 2 => rw [← hCdef] at hgain
    · -- フロンティアで停止：以降の動作もすべて自明で、`Φ` が既に境界に追いついている
      have hstop : ∀ (i : ℕ), macts v k p₁ r T cst n i m = m := by
        intro i
        induction i with
        | zero => rfl
        | succ i ihi => simp only [macts, heq]; exact ihi
      rw [heq, hstop j]
      have hqe : m.st.q ≠ v.length := fun h => hne (Or.inl h)
      have hge : n ≤ m.st.pos + m.st.q := by
        by_contra hc
        exact hne (Or.inr (by omega))
      have e1 : (k + 1) * n ≤ Phi k m.st + k * v.length := by
        have e2 : (k + 1) * n ≤ (k + 1) * (m.st.pos + m.st.q) := Nat.mul_le_mul_left _ hge
        have e3 : (k + 1) * (m.st.pos + m.st.q)
            = (k + 1) * m.st.pos + (k * m.st.q + m.st.q) := by ring
        have e4 : k * m.st.q ≤ k * v.length := Nat.mul_le_mul_left _ hq
        have e5 : Phi k m.st = (k + 1) * m.st.pos + m.st.q := rfl
        omega
      have e6 : C * ((k + 1) * n) ≤ C * (Phi k m.st + k * v.length) :=
        Nat.mul_le_mul_left _ e1
      have e7 : C * (Phi k m.st + k * v.length)
          = C * Phi k m.st + C * (k * v.length) := by ring
      have e8 : MPot k C cst m = C * Phi k m.st := MPot_boundary h0
      omega
    · exact ih _ b (mact_q_le hq) (mact_MOk hok) (by omega) h2

/-! ## ラウンド列に沿った不変条件 -/

theorem metered_MOk {u v T : List α} {k p₁ r A B' : ℕ} {cst : ScanState → ℕ} :
    ∀ n, MOk cst (metered u v k p₁ r T cst A B' n) := by
  have step : ∀ (j : ℕ) (n : ℕ) (m : MState), MOk cst m →
      MOk cst (macts v k p₁ r T cst n j m) := by
    intro j
    induction j with
    | zero => intro n m h; exact h
    | succ j ih => intro n m h; exact ih _ _ (mact_MOk h)
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact step _ _ _ ih

theorem metered_MPark {u v T : List α} {k p₁ r A B' : ℕ} {cst : ScanState → ℕ} :
    ∀ n, MPark cst (metered u v k p₁ r T cst A B' n) := by
  have step : ∀ (j : ℕ) (n : ℕ) (m : MState), MPark cst m →
      MPark cst (macts v k p₁ r T cst n j m) := by
    intro j
    induction j with
    | zero => intro n m h; exact h
    | succ j ih => intro n m h; exact ih _ _ (mact_MPark h)
  intro n
  induction n with
  | zero => intro h; exact absurd rfl h
  | succ n ih => exact step _ _ _ ih

theorem metered_inv {u v T : List α} {k p₁ r A B' : ℕ} {cst : ScanState → ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) :
    ∀ n, ScanInv v T (metered u v k p₁ r T cst A B' n).st ∧
      MInv v n (metered u v k p₁ r T cst A B' n) := by
  intro n
  induction n with
  | zero =>
    exact ⟨⟨matchLen_zero v T u.length, Nat.zero_le _⟩,
      ⟨fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd rfl h⟩⟩
  | succ n ih =>
    exact ⟨macts_inv hK hk hv _ _ (ih.2.mono (Nat.le_succ n)) ih.1,
      macts_MInv hK hk hv _ _ (ih.2.mono (Nat.le_succ n)) ih.1⟩

/-! ## 遅れ有界性（主定理） -/

/-- **計量ポテンシャルの遅れ有界性**。1 ラウンド `B = mRate A B' k = (k+1)*(A+B')`
テープ動作で、`onlineRun_phi` と同じ形の不変条件が保たれる。 -/
theorem metered_pot {u v T : List α} {k p₁ r A B' : ℕ} {cst : ScanState → ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) (hC : 0 < A + B')
    (hcost : ∀ st, cst st ≤ (A + B') * (Phi k (scanStep v k p₁ r T st) - Phi k st)) :
    ∀ n, (A + B') * ((k + 1) * n)
        ≤ MPot k (A + B') cst (metered u v k p₁ r T cst A B' n) + (A + B') * (k * v.length) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hq : (metered u v k p₁ r T cst A B' n).st.q ≤ v.length :=
      (metered_inv (A := A) (B' := B') (cst := cst) hK hk hv n).1.2
    have hsplit : (A + B') * ((k + 1) * (n + 1))
        = (A + B') * ((k + 1) * n) + (k + 1) * (A + B') := by ring
    have h := macts_pot (v := v) (T := T) (p₁ := p₁) (r := r) (cst := cst) (n := n + 1)
      hk hK.period_pos hC hcost (mRate A B' k) (metered u v k p₁ r T cst A B' n)
      ((A + B') * ((k + 1) * (n + 1))) hq (metered_MOk n)
      (by simp only [mRate]; omega) (le_refl _)
    exact h

/-- 実行中ステップのコストを追加定数 `D` として読んだ `Φ` の形。 -/
theorem metered_phi {u v T : List α} {k p₁ r A B' : ℕ} {cst : ScanState → ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) (hC : 0 < A + B')
    (hcost : ∀ st, cst st ≤ (A + B') * (Phi k (scanStep v k p₁ r T st) - Phi k st)) (n : ℕ) :
    (k + 1) * n ≤ Phi k (metered u v k p₁ r T cst A B' n).st + k * v.length
      + cst (metered u v k p₁ r T cst A B' n).st := by
  set m := metered u v k p₁ r T cst A B' n with hm
  have hpot := metered_pot (u := u) hK hk hv hC hcost n
  rw [← hm] at hpot
  have hle : MPot k (A + B') cst m ≤ (A + B') * Phi k m.st + cst m.st := by
    unfold MPot; split_ifs <;> omega
  have hc : cst m.st ≤ (A + B') * cst m.st := Nat.le_mul_of_pos_left _ hC
  have hexp : (A + B') * (Phi k m.st + k * v.length + cst m.st)
      = (A + B') * Phi k m.st + (A + B') * (k * v.length) + (A + B') * cst m.st := by ring
  have h2 : (A + B') * ((k + 1) * n)
      ≤ (A + B') * (Phi k m.st + k * v.length + cst m.st) := by omega
  exact Nat.le_of_mul_le_mul_left h2 hC

/-- **ステップ境界では `onlineRun_phi` とまったく同じ不等式**（`D = 0`）。 -/
theorem metered_phi_boundary {u v T : List α} {k p₁ r A B' : ℕ} {cst : ScanState → ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) (hC : 0 < A + B')
    (hcost : ∀ st, cst st ≤ (A + B') * (Phi k (scanStep v k p₁ r T st) - Phi k st)) {n : ℕ}
    (hb : (metered u v k p₁ r T cst A B' n).rem = 0) :
    (k + 1) * n ≤ Phi k (metered u v k p₁ r T cst A B' n).st + k * v.length := by
  set m := metered u v k p₁ r T cst A B' n with hm
  have hpot := metered_pot (u := u) hK hk hv hC hcost n
  rw [← hm] at hpot
  rw [MPot_boundary hb] at hpot
  have hexp : (A + B') * (Phi k m.st + k * v.length)
      = (A + B') * Phi k m.st + (A + B') * (k * v.length) := by ring
  have h2 : (A + B') * ((k + 1) * n) ≤ (A + B') * (Phi k m.st + k * v.length) := by omega
  exact Nat.le_of_mul_le_mul_left h2 hC

/-! ## 報告 -/

/-- ラウンド `n` の `j` 動作の途中（先頭を含む）に報告状態が現れたか。 -/
def mreported (v : List α) (k p₁ r : ℕ) (T : List α) (cst : ScanState → ℕ) (n : ℕ) :
    ℕ → MState → Bool
  | 0, m => reportFlag v n m.st
  | j + 1, m => reportFlag v n m.st || mreported v k p₁ r T cst n j (mact v k p₁ r T cst n m)

theorem mreported_sound {v T : List α} {k p₁ r : ℕ} {cst : ScanState → ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) {n : ℕ} :
    ∀ (j : ℕ) (m : MState), ScanInv v T m.st → MInv v n m →
      mreported v k p₁ r T cst n j m = true → ∃ p, p + v.length = n ∧ OccAt v T p := by
  have base : ∀ (m : MState), ScanInv v T m.st → reportFlag v n m.st = true →
      ∃ p, p + v.length = n ∧ OccAt v T p := by
    intro m hinv h
    simp only [reportFlag, decide_eq_true_eq] at h
    refine ⟨m.st.pos, h.2, ?_⟩
    have hm := hinv.1
    rw [h.1] at hm
    exact hm
  intro j
  induction j with
  | zero => intro m hinv _ h; exact base m hinv h
  | succ j ih =>
    intro m hinv hmi h
    simp only [mreported, Bool.or_eq_true] at h
    rcases h with h | h
    · exact base m hinv h
    · exact ih _ (mact_inv hK hmi hinv) (mact_MInv hk hv hinv.2 hmi) h

theorem mreported_false_final {v T : List α} {k p₁ r : ℕ} {cst : ScanState → ℕ} {n : ℕ} :
    ∀ (j : ℕ) (m : MState), mreported v k p₁ r T cst n j m = false →
      reportFlag v n (macts v k p₁ r T cst n j m).st = false := by
  intro j
  induction j with
  | zero => intro m h; exact h
  | succ j ih =>
    intro m h
    simp only [mreported, Bool.or_eq_false_iff] at h
    exact ih _ h.2

/-! ## 追い越し禁止 -/

theorem macts_pos_le {v T : List α} {k p₁ r : ℕ} {cst : ScanState → ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) {i n : ℕ}
    (hocc : OccAt v T i) (hn : n ≤ i + v.length) :
    ∀ (j : ℕ) (m : MState), ScanInv v T m.st → MInv v n m → m.st.pos ≤ i →
      (n < i + v.length ∨ mreported v k p₁ r T cst n j m = false) →
      (macts v k p₁ r T cst n j m).st.pos ≤ i := by
  intro j
  induction j with
  | zero => intro m _ _ hp _; exact hp
  | succ j ih =>
    intro m hinv hmi hp hd
    simp only [macts]
    have hne : m.st.q = v.length → m.st.pos ≠ i := by
      intro hqe
      have hle : m.st.pos + m.st.q ≤ n := hmi.1 (by omega)
      rcases hd with hlt | hrep
      · omega
      · simp only [mreported, Bool.or_eq_false_iff] at hrep
        have hf0 := hrep.1
        simp only [reportFlag, decide_eq_false_iff_not, not_and] at hf0
        intro hpi
        exact hf0 hqe (by omega)
    have hstep : (mact v k p₁ r T cst n m).st.pos ≤ i := by
      rcases mact_st_cases (k := k) (p₁ := p₁) (r := r) (T := T) (cst := cst) hmi with
        he | ⟨he, _⟩
      · rw [he]; exact hp
      · rw [he]; exact scanStep_pos_le_of_occ hK hk hinv hocc hp hne
    refine ih _ (mact_inv hK hmi hinv) (mact_MInv hk hv hinv.2 hmi) hstep ?_
    rcases hd with hlt | hrep
    · exact Or.inl hlt
    · refine Or.inr ?_
      simp only [mreported, Bool.or_eq_false_iff] at hrep
      exact hrep.2

/-! ## 完全性（計量式でも実時間） -/

theorem metered_pos_le {u v T : List α} {k p₁ r A B' : ℕ} {cst : ScanState → ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) {i : ℕ}
    (hi : u.length ≤ i) (hocc : OccAt v T i) :
    ∀ n, n < i + v.length → (metered u v k p₁ r T cst A B' n).st.pos ≤ i := by
  intro n
  induction n with
  | zero => intro _; exact hi
  | succ n ih =>
    intro hlt
    have hinv := metered_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst) hK hk hv n
    exact macts_pos_le hK hk hv hocc (by omega) _ _ hinv.1
      (hinv.2.mono (Nat.le_succ n)) (ih (by omega)) (Or.inl hlt)

/-- **計量式の実時間完全性**：ラウンド `n+1` の終わりがステップ境界なら、
`i + |v| = n + 1` なる出現はまさにそのラウンドで報告される。 -/
theorem mreported_complete {u v T : List α} {k p₁ r A B' : ℕ} {cst : ScanState → ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) (hC : 0 < A + B')
    (hcost : ∀ st, cst st ≤ (A + B') * (Phi k (scanStep v k p₁ r T st) - Phi k st))
    {i n : ℕ} (hi : u.length ≤ i) (hocc : OccAt v T i) (hin : i + v.length = n + 1)
    (hb : (metered u v k p₁ r T cst A B' (n + 1)).rem = 0) :
    mreported v k p₁ r T cst (n + 1) (mRate A B' k) (metered u v k p₁ r T cst A B' n)
      = true := by
  by_contra hcon
  rw [Bool.not_eq_true] at hcon
  have hst : macts v k p₁ r T cst (n + 1) (mRate A B' k) (metered u v k p₁ r T cst A B' n)
      = metered u v k p₁ r T cst A B' (n + 1) := rfl
  have hinvn := metered_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst) hK hk hv n
  have hpos0 : (metered u v k p₁ r T cst A B' n).st.pos ≤ i :=
    metered_pos_le hK hk hv hi hocc n (by omega)
  have hposF : (metered u v k p₁ r T cst A B' (n + 1)).st.pos ≤ i := by
    rw [← hst]
    exact macts_pos_le hK hk hv hocc (by omega) _ _ hinvn.1
      (hinvn.2.mono (Nat.le_succ n)) hpos0 (Or.inr hcon)
  have hflagF : reportFlag v (n + 1) (metered u v k p₁ r T cst A B' (n + 1)).st = false := by
    rw [← hst]
    exact mreported_false_final _ _ hcon
  have hqF : (metered u v k p₁ r T cst A B' (n + 1)).st.q ≤ v.length :=
    (metered_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst) hK hk hv (n + 1)).1.2
  have hfitsF : Fits (n + 1) (metered u v k p₁ r T cst A B' (n + 1)).st :=
    (metered_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst) hK hk hv (n + 1)).2.1
  have hphi := metered_phi_boundary (u := u) hK hk hv hC hcost hb
  set P := (metered u v k p₁ r T cst A B' (n + 1)).st.pos with hP
  set Q := (metered u v k p₁ r T cst A B' (n + 1)).st.q with hQdef
  have hphi' : (k + 1) * (n + 1) ≤ (k + 1) * P + Q + k * v.length := by
    have e : Phi k (metered u v k p₁ r T cst A B' (n + 1)).st = (k + 1) * P + Q := rfl
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

/-! ## 停留中のステップは「ずらし」であること -/

/-- 前進（比較成功）でないステップの行き先は `q' < |v|`：周期ずらしは `q - p₁ < |v|`、
リセットは `q' = 0 < |v|`。 -/
theorem scanStep_q_ne_of_not_advance {v T : List α} {k p₁ r : ℕ} (hp : 0 < p₁)
    (hv : 0 < v.length) {st : ScanState} (hq : st.q ≤ v.length)
    (hadv : ¬ (st.q ≠ v.length ∧ T[st.pos + st.q]? = v[st.q]?)) :
    (scanStep v k p₁ r T st).q ≠ v.length := by
  have hshift : gsNextQ k p₁ r st.q ≠ v.length := by
    unfold gsNextQ; split_ifs with hc <;> simp <;> omega
  unfold scanStep
  split_ifs with h1 h2
  · simpa using hshift
  · exact absurd ⟨h1, h2⟩ hadv
  · simpa using hshift

/-- 停留中でも「仮想的な」ポテンシャル（実行中ステップを完了させた先）は
境界に追いついている。 -/
theorem metered_phi_virtual {u v T : List α} {k p₁ r A B' : ℕ} {cst : ScanState → ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) (hC : 0 < A + B')
    (hcost : ∀ st, cst st ≤ (A + B') * (Phi k (scanStep v k p₁ r T st) - Phi k st)) (n : ℕ) :
    (k + 1) * n
      ≤ Phi k (scanStep v k p₁ r T (metered u v k p₁ r T cst A B' n).st) + k * v.length := by
  set m := metered u v k p₁ r T cst A B' n with hm
  have hpot := metered_pot (u := u) hK hk hv hC hcost n
  rw [← hm] at hpot
  have hlt := phi_step_lt (v := v) (T := T) (p₁ := p₁) (r := r) hk hK.period_pos m.st
  have hcst := hcost m.st
  have hkey : (A + B') * Phi k m.st
      + (A + B') * (Phi k (scanStep v k p₁ r T m.st) - Phi k m.st)
      = (A + B') * Phi k (scanStep v k p₁ r T m.st) := by
    rw [← Nat.mul_add]; congr 1; omega
  have hle : MPot k (A + B') cst m ≤ (A + B') * Phi k (scanStep v k p₁ r T m.st) := by
    unfold MPot; split_ifs <;> omega
  have hexp : (A + B') * (Phi k (scanStep v k p₁ r T m.st) + k * v.length)
      = (A + B') * Phi k (scanStep v k p₁ r T m.st) + (A + B') * (k * v.length) := by ring
  have h2 : (A + B') * ((k + 1) * n)
      ≤ (A + B') * (Phi k (scanStep v k p₁ r T m.st) + k * v.length) := by omega
  exact Nat.le_of_mul_le_mul_left h2 hC

/-- **停留しない**：出現 `i` の締切ラウンド `i + |v|` の終わりでは、機械は必ず
ステップ境界にいる。停留していたとすると、そのステップは「ずらし」（`hadvance` により
前進はコスト `≤ 1` で停留しない）なので行き先の `q' < |v|`、一方で仮想ポテンシャルと
追い越し禁止から `q' = |v|` が強制されて矛盾する。 -/
theorem metered_boundary_of_occ {u v T : List α} {k p₁ r A B' : ℕ} {cst : ScanState → ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) (hC : 0 < A + B')
    (hcost : ∀ st, cst st ≤ (A + B') * (Phi k (scanStep v k p₁ r T st) - Phi k st))
    (hadvance : ∀ st, st.q ≠ v.length → T[st.pos + st.q]? = v[st.q]? → cst st ≤ 1)
    {i n : ℕ} (hi : u.length ≤ i) (hocc : OccAt v T i) (hin : i + v.length = n + 1)
    (hcon : mreported v k p₁ r T cst (n + 1) (mRate A B' k)
      (metered u v k p₁ r T cst A B' n) = false) :
    (metered u v k p₁ r T cst A B' (n + 1)).rem = 0 := by
  by_contra hrem
  have hst : macts v k p₁ r T cst (n + 1) (mRate A B' k) (metered u v k p₁ r T cst A B' n)
      = metered u v k p₁ r T cst A B' (n + 1) := rfl
  have hinvn := metered_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst) hK hk hv n
  have hpos0 : (metered u v k p₁ r T cst A B' n).st.pos ≤ i :=
    metered_pos_le hK hk hv hi hocc n (by omega)
  have hposF : (metered u v k p₁ r T cst A B' (n + 1)).st.pos ≤ i := by
    rw [← hst]
    exact macts_pos_le hK hk hv hocc (by omega) _ _ hinvn.1
      (hinvn.2.mono (Nat.le_succ n)) hpos0 (Or.inr hcon)
  have hflagF : reportFlag v (n + 1) (metered u v k p₁ r T cst A B' (n + 1)).st = false := by
    rw [← hst]
    exact mreported_false_final _ _ hcon
  have hinvF := metered_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst) hK hk hv (n + 1)
  have hqF : (metered u v k p₁ r T cst A B' (n + 1)).st.q ≤ v.length := hinvF.1.2
  have hfitsF : Fits (n + 1) (metered u v k p₁ r T cst A B' (n + 1)).st := hinvF.2.1
  -- 停留中なのでコストは 2 以上、よって前進ではない ⇒ 行き先は `q' < |v|`
  have hpark : 2 ≤ cst (metered u v k p₁ r T cst A B' (n + 1)).st :=
    metered_MPark (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) (T := T) (A := A) (B' := B')
      (n + 1) hrem
  have hnadv : ¬ ((metered u v k p₁ r T cst A B' (n + 1)).st.q ≠ v.length ∧
      T[(metered u v k p₁ r T cst A B' (n + 1)).st.pos
          + (metered u v k p₁ r T cst A B' (n + 1)).st.q]?
        = v[(metered u v k p₁ r T cst A B' (n + 1)).st.q]?) := by
    rintro ⟨h1, h2⟩
    have := hadvance _ h1 h2
    omega
  have hq'ne : (scanStep v k p₁ r T (metered u v k p₁ r T cst A B' (n + 1)).st).q
      ≠ v.length := scanStep_q_ne_of_not_advance hK.period_pos hv hqF hnadv
  -- 追い越し禁止は行き先にも及ぶ
  have hne : (metered u v k p₁ r T cst A B' (n + 1)).st.q = v.length →
      (metered u v k p₁ r T cst A B' (n + 1)).st.pos ≠ i := by
    intro hqe
    have hle : (metered u v k p₁ r T cst A B' (n + 1)).st.pos
        + (metered u v k p₁ r T cst A B' (n + 1)).st.q ≤ n + 1 := hfitsF (by omega)
    simp only [reportFlag, decide_eq_false_iff_not, not_and] at hflagF
    intro hpi
    exact hflagF hqe (by omega)
  have hpos' : (scanStep v k p₁ r T (metered u v k p₁ r T cst A B' (n + 1)).st).pos ≤ i :=
    scanStep_pos_le_of_occ hK hk hinvF.1 hocc hposF hne
  have hq' : (scanStep v k p₁ r T (metered u v k p₁ r T cst A B' (n + 1)).st).q ≤ v.length :=
    scanStep_q_le hqF
  have hvirt := metered_phi_virtual (u := u) hK hk hv hC hcost (n + 1)
  set P := (scanStep v k p₁ r T (metered u v k p₁ r T cst A B' (n + 1)).st).pos with hP
  set Q := (scanStep v k p₁ r T (metered u v k p₁ r T cst A B' (n + 1)).st).q with hQ
  have hphi' : (k + 1) * (n + 1) ≤ (k + 1) * P + Q + k * v.length := by
    have e : Phi k (scanStep v k p₁ r T (metered u v k p₁ r T cst A B' (n + 1)).st)
        = (k + 1) * P + Q := rfl
    omega
  have h1 : (k + 1) * P ≤ (k + 1) * i := Nat.mul_le_mul_left _ hpos'
  have e1 : (k + 1) * (n + 1) = (k + 1) * i + (k + 1) * v.length := by rw [← hin]; ring
  have e2 : (k + 1) * v.length = k * v.length + v.length := by ring
  exact hq'ne (by omega)

/-- **`rem = 0` の仮定を外した完全性**。 -/
theorem mreported_complete' {u v T : List α} {k p₁ r A B' : ℕ} {cst : ScanState → ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) (hC : 0 < A + B')
    (hcost : ∀ st, cst st ≤ (A + B') * (Phi k (scanStep v k p₁ r T st) - Phi k st))
    (hadvance : ∀ st, st.q ≠ v.length → T[st.pos + st.q]? = v[st.q]? → cst st ≤ 1)
    {i n : ℕ} (hi : u.length ≤ i) (hocc : OccAt v T i) (hin : i + v.length = n + 1) :
    mreported v k p₁ r T cst (n + 1) (mRate A B' k) (metered u v k p₁ r T cst A B' n)
      = true := by
  by_cases hcon : mreported v k p₁ r T cst (n + 1) (mRate A B' k)
      (metered u v k p₁ r T cst A B' n) = true
  · exact hcon
  · rw [Bool.not_eq_true] at hcon
    exact mreported_complete hK hk hv hC hcost hi hocc hin
      (metered_boundary_of_occ hK hk hv hC hcost hadvance hi hocc hin hcon)

/-! ## 主定理 -/

/-- 計量式スケジューラのラウンド `n` の出力。 -/
def manswer (u v : List α) (k p₁ r : ℕ) (T : List α) (cst : ScanState → ℕ) (A B' : ℕ) :
    ℕ → Bool
  | 0 => false
  | n + 1 =>
      mreported v k p₁ r T cst (n + 1) (mRate A B' k) (metered u v k p₁ r T cst A B' n) &&
        decide (MatchLen u T (n + 1 - (u.length + v.length)) u.length)

/-- **計量式（de-amortized）実時間定理**：1 ラウンドに固定本数
`B = mRate A B' k = (k+1)*(A+B')` のテープ動作しか実行しなくても、
ラウンドの終わりがステップ境界であるかぎり答えはその場で正しい。 -/
theorem metered_answer_correct {u v T : List α} {k p₁ r A B' : ℕ} {cst : ScanState → ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) (hC : 0 < A + B')
    (hcost : ∀ st, cst st ≤ (A + B') * (Phi k (scanStep v k p₁ r T st) - Phi k st))
    (n : ℕ) (hn : (u ++ v).length ≤ n) (hb : (metered u v k p₁ r T cst A B' n).rem = 0) :
    manswer u v k p₁ r T cst A B' n = decide (OccAt (u ++ v) T (n - (u ++ v).length)) := by
  simp only [List.length_append] at hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set i := m + 1 - v.length with hi
  have hiv : i + v.length = m + 1 := by omega
  have hiu : u.length ≤ i := by omega
  have hinvm := metered_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst) hK hk hv m
  have hrep :
      mreported v k p₁ r T cst (m + 1) (mRate A B' k) (metered u v k p₁ r T cst A B' m)
        = decide (OccAt v T i) := by
    refine Bool.eq_iff_iff.mpr ?_
    rw [decide_eq_true_eq]
    constructor
    · intro h
      obtain ⟨p, hp, hocc⟩ :=
        mreported_sound hK hk hv _ _ hinvm.1 (hinvm.2.mono (Nat.le_succ m)) h
      have : p = i := by omega
      exact this ▸ hocc
    · intro h
      exact mreported_complete hK hk hv hC hcost hiu h hiv hb
  simp only [manswer, hrep, List.length_append]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [occAt_append_iff]
  have hpos : m + 1 - (u.length + v.length) + u.length = i := by omega
  rw [hpos]
  exact and_comm

/-- **仮定 `rem = 0` を外した計量式実時間定理**。
唯一の追加仮定 `hadvance` は「前進（比較成功）ステップは 1 動作で終わる ＝ 停留しない」。
これは前進のコストが定数であることの正規化（1 動作 = 定数機械ステップ）であり、
停留しうるのは（ポテンシャル増分に比例する）ずらしだけになる。 -/
theorem metered_answer_correct' {u v T : List α} {k p₁ r A B' : ℕ} {cst : ScanState → ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) (hC : 0 < A + B')
    (hcost : ∀ st, cst st ≤ (A + B') * (Phi k (scanStep v k p₁ r T st) - Phi k st))
    (hadvance : ∀ st, st.q ≠ v.length → T[st.pos + st.q]? = v[st.q]? → cst st ≤ 1)
    (n : ℕ) (hn : (u ++ v).length ≤ n) :
    manswer u v k p₁ r T cst A B' n = decide (OccAt (u ++ v) T (n - (u ++ v).length)) := by
  simp only [List.length_append] at hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set i := m + 1 - v.length with hi
  have hiv : i + v.length = m + 1 := by omega
  have hiu : u.length ≤ i := by omega
  have hinvm := metered_inv (u := u) (T := T) (A := A) (B' := B') (cst := cst) hK hk hv m
  have hrep :
      mreported v k p₁ r T cst (m + 1) (mRate A B' k) (metered u v k p₁ r T cst A B' m)
        = decide (OccAt v T i) := by
    refine Bool.eq_iff_iff.mpr ?_
    rw [decide_eq_true_eq]
    constructor
    · intro h
      obtain ⟨p, hp, hocc⟩ :=
        mreported_sound hK hk hv _ _ hinvm.1 (hinvm.2.mono (Nat.le_succ m)) h
      have : p = i := by omega
      exact this ▸ hocc
    · intro h
      exact mreported_complete' hK hk hv hC hcost hadvance hiu h hiv
  simp only [manswer, hrep, List.length_append]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [occAt_append_iff]
  have hpos : m + 1 - (u.length + v.length) + u.length = i := by omega
  rw [hpos]
  exact and_comm

end PalPeg
