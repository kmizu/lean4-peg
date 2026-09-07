import PalPeg.GSScan

/-!
# Galil–Seiferas 走査段の **実時間実行**

`PalPeg.GSScan` の走査（`scanStep` / `scanRun`）は「テキスト `T` が全部手元にある」
オフラインの定式化だった。本ファイルはそれを **1 ラウンド 1 文字が到着する
オンライン計算** に載せ替え、固定レート `R = k+1` の走査で **遅延ゼロ**
（ラウンド `n` に終わる出現をラウンド `n` に報告する）が達成できることを証明する。

## モデル

パターンは `x = u ++ v`、`s = |u|`、`KSimple v k p₁ r`。テキストは
1 ラウンド 1 文字。ラウンド `n` の終わりまでに `T.take n` が到着している。

* `Enabled v n st` — 状態 `st` で 1 歩進めるか。比較の一歩は `T[st.pos + st.q]?` を
  要求するので `st.pos + st.q < n` が必要。`st.q = |v|`（報告直後のずらし）は
  入力を読まないので常に可能。
* `runIn v k p₁ r T n m st` — 到着境界 `n` を守りながら **高々 `m` 歩**。
  境界に達したら（`¬ Enabled`）そこで待つ。
* `reportedIn v k p₁ r T n m st` — その `m` 歩の **途中および末尾** に
  「`q = |v|` かつ `pos + |v| = n`」の状態が現れたか（＝ラウンド `n` に終わる
  `v` の出現を報告したか）。
* `gsRate k = k + 1` — 1 ラウンドあたりの走査ステップ数 `R`。
* `onlineRun u v k p₁ r T n` — ラウンド `n` 終了時の状態。初期状態は `⟨s, 0⟩`。
* `answer u v k p₁ r T n` — ラウンド `n` の出力：`v` の報告 ∧ `u` の照合。

## 主定理

`online_answer_correct` : `|x| ≤ n` のとき
`answer u v k p₁ r T n = decide (OccAt x T (n - |x|))`。
レートは `R = gsRate k = k + 1`（`k = 8` なら 9 走査ステップ／ラウンド）。

## 証明の骨格（予測可能性 = ポテンシャルの遅れが有界）

`Φ = (k+1)·pos + q`（`GSScan.Phi`）は 1 歩ごとに真に増える（`phi_step_lt`）。

* **`Fits`（先読み禁止）** `0 < q → pos + q ≤ n`。到着済みの文字としか比較しない
  ことの帰結。
* **`J(n)`（遅れの有界性, `onlineRun_phi`）** `(k+1)·n ≤ Φ(st_n) + k·|v|`、
  すなわち `C = k·|v|` として `Φ ≥ (k+1)n − C`。
  証明：ラウンド内で走査が **境界に達して待った**なら `pos + q ≥ n` かつ `q ≤ |v|`
  なので `Φ + k|v| ≥ (k+1)(pos+q) ≥ (k+1)n` が直接従う。待たなかったなら
  `R = k+1` 歩すべてを実行し `Φ` が `≥ k+1` 増えるので `J(n−1)` から `J(n)`。
  この 2 択が「バーストで遅れても、遅れは次の候補が報告されうる時刻までに
  必ず取り返される」という `DELAYED_PAL.md:36-39` の予測可能性そのもの。
* **追い越し禁止（`runIn_pos_le`）** 出現位置 `i` を報告せずに `pos` が追い越すことは
  ない（`safe_shift` 由来の `scanStep_pos_le_of_occ`）。
* これらを合わせると：ラウンド `n = i + |v|` の終了時に `pos ≤ i`、`q ≤ |v|` かつ
  `J(n)` なら `q = |v|` と `pos = i` が強制され、報告フラグが立つ。

## 短い接頭辞 `u`

本ファイルの `answer` は `u` の照合を `MatchLen u T · s` としてオラクル的に扱う。
それが実時間で間に合うこと（`ALGORITHM_SPEC.md` §2 "Interleaving / predictability",
`DELAYED_PAL.md:36-39`）の算術的核心は `prefix_verifier_deadline`：
`k ≥ 3` と L1 の 2 つの評価 `(k−1)s < |x|`, `(k−2)s < (k−1)p₁` のもとで
`s < 2·(|v| − gsNextQ k p₁ r q)`、すなわち **ずらし直後から次に報告が起きうるまでの
成功比較回数の 2 倍（quota = 2）が `|u|` を超える**。よって
インターリーブ版のレートは `gsRateInterleaved k = 3 * (k + 1)` で足りる。
-/

namespace PalPeg

universe u
variable {α : Type u}

/-! ## オンライン実行のモデル -/

/-- ラウンド `n`（`T.take n` が到着済み）に 1 歩進められるか。
比較の一歩は `T[pos+q]?` を要求するので `pos + q < n`。`q = |v|` の
「報告してずらす」一歩は入力を読まないので常に可能。 -/
def Enabled (v : List α) (n : ℕ) (st : ScanState) : Prop :=
  st.q = v.length ∨ st.pos + st.q < n

instance decEnabled (v : List α) (n : ℕ) (st : ScanState) : Decidable (Enabled v n st) :=
  inferInstanceAs (Decidable (st.q = v.length ∨ st.pos + st.q < n))

/-- 「ラウンド `n` に終わる `v` の出現」をこの状態が報告するか。 -/
def reportFlag (v : List α) (n : ℕ) (st : ScanState) : Bool :=
  decide (st.q = v.length ∧ st.pos + v.length = n)

/-- 到着境界の不変条件：一致済み区間 `[pos, pos+q)` は到着済み。 -/
def Fits (n : ℕ) (st : ScanState) : Prop := 0 < st.q → st.pos + st.q ≤ n

theorem Fits.mono {n n' : ℕ} {st : ScanState} (h : Fits n st) (hn : n ≤ n') : Fits n' st :=
  fun hq => le_trans (h hq) hn

variable [DecidableEq α]

/-- ラウンド `n` の中で高々 `m` 歩。境界に達したら待つ。 -/
def runIn (v : List α) (k p₁ r : ℕ) (T : List α) (n : ℕ) : ℕ → ScanState → ScanState
  | 0, st => st
  | m + 1, st =>
      if Enabled v n st then runIn v k p₁ r T n m (scanStep v k p₁ r T st) else st

/-- その `m` 歩の途中（末尾を含む）に報告状態が現れたか。 -/
def reportedIn (v : List α) (k p₁ r : ℕ) (T : List α) (n : ℕ) : ℕ → ScanState → Bool
  | 0, st => reportFlag v n st
  | m + 1, st =>
      reportFlag v n st ||
        (if Enabled v n st then reportedIn v k p₁ r T n m (scanStep v k p₁ r T st) else false)

/-- 実時間レート：1 ラウンドあたりの走査ステップ数 `R`。 -/
def gsRate (k : ℕ) : ℕ := k + 1

/-- インターリーブ版（`v` の成功比較 1 回につき `u` の比較 2 回）のレート。 -/
def gsRateInterleaved (k : ℕ) : ℕ := 3 * (k + 1)

/-- ラウンド `n` 終了時の走査状態。 -/
def onlineRun (u v : List α) (k p₁ r : ℕ) (T : List α) : ℕ → ScanState
  | 0 => ⟨u.length, 0⟩
  | n + 1 => runIn v k p₁ r T (n + 1) (gsRate k) (onlineRun u v k p₁ r T n)

/-- ラウンド `n` の出力：`v` の報告と `u` の照合。 -/
def answer (u v : List α) (k p₁ r : ℕ) (T : List α) : ℕ → Bool
  | 0 => false
  | n + 1 =>
      reportedIn v k p₁ r T (n + 1) (gsRate k) (onlineRun u v k p₁ r T n) &&
        decide (MatchLen u T (n + 1 - (u.length + v.length)) u.length)

/-! ## 先読み禁止の不変条件 `Fits` -/

theorem fits_shift {k p₁ r n a b : ℕ} (hk : 0 < k) (hle : a + b ≤ n) :
    Fits n ⟨a + gsShift k p₁ r b, gsNextQ k p₁ r b⟩ := by
  show 0 < gsNextQ k p₁ r b → a + gsShift k p₁ r b + gsNextQ k p₁ r b ≤ n
  unfold gsShift gsNextQ
  split_ifs with hc
  · intro _
    have hp : p₁ ≤ b := le_trans (Nat.le_mul_of_pos_left p₁ hk) hc.1
    omega
  · intro h; omega

theorem scanStep_fits {v T : List α} {k p₁ r : ℕ} (hk : 0 < k) (hv : 0 < v.length)
    {n : ℕ} {st : ScanState} (he : Enabled v n st) (hf : Fits n st) :
    Fits n (scanStep v k p₁ r T st) := by
  unfold scanStep
  split_ifs with h1 h2
  · exact fits_shift hk (hf (by omega))
  · have hlt : st.pos + st.q < n := by
      rcases he with h | h
      · exact absurd h h1
      · exact h
    show 0 < st.q + 1 → st.pos + (st.q + 1) ≤ n
    intro _; omega
  · have hlt : st.pos + st.q < n := by
      rcases he with h | h
      · exact absurd h h1
      · exact h
    exact fits_shift hk (by omega)

theorem runIn_qle {v T : List α} {k p₁ r n : ℕ} :
    ∀ (m : ℕ) (st : ScanState), st.q ≤ v.length →
      (runIn v k p₁ r T n m st).q ≤ v.length := by
  intro m
  induction m with
  | zero => intro st h; exact h
  | succ m ih =>
    intro st h
    simp only [runIn]
    split_ifs with he
    · exact ih _ (scanStep_q_le h)
    · exact h

theorem runIn_inv {v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r) {n : ℕ} :
    ∀ (m : ℕ) (st : ScanState), ScanInv v T st →
      ScanInv v T (runIn v k p₁ r T n m st) := by
  intro m
  induction m with
  | zero => intro st h; exact h
  | succ m ih =>
    intro st h
    simp only [runIn]
    split_ifs with he
    · exact ih _ (scanStep_inv hK h)
    · exact h

theorem runIn_fits {v T : List α} {k p₁ r : ℕ} (hk : 0 < k) (hv : 0 < v.length) {n : ℕ} :
    ∀ (m : ℕ) (st : ScanState), st.q ≤ v.length → Fits n st →
      Fits n (runIn v k p₁ r T n m st) := by
  intro m
  induction m with
  | zero => intro st _ h; exact h
  | succ m ih =>
    intro st hq h
    simp only [runIn]
    split_ifs with he
    · exact ih _ (scanStep_q_le hq) (scanStep_fits hk hv he h)
    · exact h

/-! ## `J(n)`：ポテンシャルの遅れが有界（予測可能性） -/

/-- ラウンド内の 1 ラウンド分の評価：`m` 歩でポテンシャルは `m` 増えるか、
そうでなければ **境界に追いついている**（`(k+1)n` に達している）。 -/
theorem runIn_phi {v T : List α} {k p₁ r : ℕ} (hk : 0 < k) (hp : 0 < p₁) {n : ℕ} :
    ∀ (m : ℕ) (st : ScanState) (b : ℕ), st.q ≤ v.length →
      b ≤ Phi k st + m + k * v.length → b ≤ (k + 1) * n →
      b ≤ Phi k (runIn v k p₁ r T n m st) + k * v.length := by
  intro m
  induction m with
  | zero => intro st b _ h _; simpa only [runIn, Nat.add_zero] using h
  | succ m ih =>
    intro st b hq h1 h2
    simp only [runIn]
    split_ifs with he
    · have hlt := phi_step_lt (v := v) (T := T) (p₁ := p₁) (r := r) hk hp st
      exact ih (scanStep v k p₁ r T st) b (scanStep_q_le hq) (by omega) h2
    · have hne : st.q ≠ v.length := fun h => he (Or.inl h)
      have hge : n ≤ st.pos + st.q := by
        by_contra hc
        exact he (Or.inr (by omega))
      have e1 : (k + 1) * n ≤ (k + 1) * (st.pos + st.q) :=
        Nat.mul_le_mul_left _ hge
      have e2 : (k + 1) * (st.pos + st.q) = (k + 1) * st.pos + (k * st.q + st.q) := by ring
      have e3 : k * st.q ≤ k * v.length := Nat.mul_le_mul_left _ hq
      have e4 : Phi k st = (k + 1) * st.pos + st.q := rfl
      omega

/-! ## 状態の基本不変条件 -/

theorem onlineRun_scanInv {u v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r) :
    ∀ n, ScanInv v T (onlineRun u v k p₁ r T n) := by
  intro n
  induction n with
  | zero => exact ⟨matchLen_zero v T u.length, Nat.zero_le _⟩
  | succ n ih => exact runIn_inv hK _ _ ih

/-- **`J(n)`**：`Φ(st_n) ≥ (k+1)·n − k·|v|`。すなわち到着境界からの遅れは
ポテンシャルで測って定数 `C = k·|v|` 以内。 -/
theorem onlineRun_phi {u v T : List α} {k p₁ r : ℕ} (hk : 0 < k) (hp : 0 < p₁)
    (hK : KSimple v k p₁ r) :
    ∀ n, (k + 1) * n ≤ Phi k (onlineRun u v k p₁ r T n) + k * v.length := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hq : (onlineRun u v k p₁ r T n).q ≤ v.length :=
      (onlineRun_scanInv (u := u) (T := T) hK n).2
    have e : (k + 1) * (n + 1) = (k + 1) * n + (k + 1) := by ring
    have hst : runIn v k p₁ r T (n + 1) (gsRate k) (onlineRun u v k p₁ r T n)
        = onlineRun u v k p₁ r T (n + 1) := rfl
    have h := runIn_phi (v := v) (T := T) (p₁ := p₁) (r := r) (n := n + 1) hk hp
      (gsRate k) (onlineRun u v k p₁ r T n) ((k + 1) * (n + 1)) hq
      (by simp only [gsRate]; omega) (le_refl _)
    rw [hst] at h
    exact h

theorem onlineRun_fits {u v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r)
    (hk : 0 < k) (hv : 0 < v.length) :
    ∀ n, Fits n (onlineRun u v k p₁ r T n) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (Nat.lt_irrefl 0)
  | succ n ih =>
    exact runIn_fits hk hv _ _ (onlineRun_scanInv hK n).2 (ih.mono (Nat.le_succ n))

/-! ## 追い越し禁止 -/

theorem runIn_pos_le {v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r) (hk : 0 < k)
    (hv : 0 < v.length) {i n : ℕ} (hocc : OccAt v T i) (hn : n ≤ i + v.length) :
    ∀ (m : ℕ) (st : ScanState), ScanInv v T st → Fits n st → st.pos ≤ i →
      (n < i + v.length ∨ reportedIn v k p₁ r T n m st = false) →
      (runIn v k p₁ r T n m st).pos ≤ i := by
  intro m
  induction m with
  | zero => intro st _ _ hp _; exact hp
  | succ m ih =>
    intro st hinv hfits hp hd
    simp only [runIn]
    split_ifs with he
    · refine ih _ (scanStep_inv hK hinv) (scanStep_fits hk hv he hfits)
        (scanStep_pos_le_of_occ hK hk hinv hocc hp ?_) ?_
      · intro hqe
        have hle : st.pos + st.q ≤ n := hfits (by omega)
        rcases hd with hlt | hrep
        · omega
        · simp only [reportedIn, Bool.or_eq_false_iff] at hrep
          have hf0 := hrep.1
          simp only [reportFlag, decide_eq_false_iff_not, not_and] at hf0
          intro hpi
          exact hf0 hqe (by omega)
      · rcases hd with hlt | hrep
        · exact Or.inl hlt
        · refine Or.inr ?_
          simp only [reportedIn, Bool.or_eq_false_iff] at hrep
          have h2 := hrep.2
          rw [if_pos he] at h2
          exact h2
    · exact hp

theorem onlineRun_pos_le {u v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r) (hk : 0 < k)
    (hv : 0 < v.length) {i : ℕ} (hi : u.length ≤ i) (hocc : OccAt v T i) :
    ∀ n, n < i + v.length → (onlineRun u v k p₁ r T n).pos ≤ i := by
  intro n
  induction n with
  | zero => intro _; exact hi
  | succ n ih =>
    intro hlt
    exact runIn_pos_le hK hk hv hocc (by omega) _ _ (onlineRun_scanInv hK n)
      ((onlineRun_fits hK hk hv n).mono (Nat.le_succ n)) (ih (by omega)) (Or.inl hlt)

/-! ## 健全性 -/

theorem reportedIn_sound {v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r) {n : ℕ} :
    ∀ (m : ℕ) (st : ScanState), ScanInv v T st →
      reportedIn v k p₁ r T n m st = true → ∃ p, p + v.length = n ∧ OccAt v T p := by
  intro m
  induction m with
  | zero =>
    intro st hinv h
    simp only [reportedIn, reportFlag, decide_eq_true_eq] at h
    refine ⟨st.pos, h.2, ?_⟩
    have hm := hinv.1
    rw [h.1] at hm
    exact hm
  | succ m ih =>
    intro st hinv h
    simp only [reportedIn, Bool.or_eq_true] at h
    rcases h with h | h
    · simp only [reportFlag, decide_eq_true_eq] at h
      refine ⟨st.pos, h.2, ?_⟩
      have hm := hinv.1
      rw [h.1] at hm
      exact hm
    · by_cases he : Enabled v n st
      · rw [if_pos he] at h
        exact ih _ (scanStep_inv hK hinv) h
      · rw [if_neg he] at h
        exact absurd h (by simp)

theorem reportedIn_false_final {v T : List α} {k p₁ r n : ℕ} :
    ∀ (m : ℕ) (st : ScanState), reportedIn v k p₁ r T n m st = false →
      reportFlag v n (runIn v k p₁ r T n m st) = false := by
  intro m
  induction m with
  | zero => intro st h; exact h
  | succ m ih =>
    intro st h
    simp only [reportedIn, Bool.or_eq_false_iff] at h
    simp only [runIn]
    split_ifs with he
    · refine ih _ ?_
      have h2 := h.2
      rw [if_pos he] at h2
      exact h2
    · exact h.1

/-! ## 完全性（実時間で間に合う） -/

/-- **実時間完全性**：出現 `i` があり `i + |v| = n + 1` なら、レート `R = k+1` の
オンライン走査はまさにラウンド `n+1` にそれを報告する。 -/
theorem reportedIn_complete {u v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r)
    (hk : 0 < k) (hv : 0 < v.length) {i n : ℕ} (hi : u.length ≤ i) (hocc : OccAt v T i)
    (hin : i + v.length = n + 1) :
    reportedIn v k p₁ r T (n + 1) (gsRate k) (onlineRun u v k p₁ r T n) = true := by
  by_contra hcon
  rw [Bool.not_eq_true] at hcon
  have hst : runIn v k p₁ r T (n + 1) (gsRate k) (onlineRun u v k p₁ r T n)
      = onlineRun u v k p₁ r T (n + 1) := rfl
  have hpos0 : (onlineRun u v k p₁ r T n).pos ≤ i :=
    onlineRun_pos_le hK hk hv hi hocc n (by omega)
  have hposF : (onlineRun u v k p₁ r T (n + 1)).pos ≤ i := by
    rw [← hst]
    exact runIn_pos_le hK hk hv hocc (by omega) _ _ (onlineRun_scanInv hK n)
      ((onlineRun_fits hK hk hv n).mono (Nat.le_succ n)) hpos0 (Or.inr hcon)
  have hflagF : reportFlag v (n + 1) (onlineRun u v k p₁ r T (n + 1)) = false := by
    rw [← hst]
    exact reportedIn_false_final _ _ hcon
  have hqF : (onlineRun u v k p₁ r T (n + 1)).q ≤ v.length :=
    (onlineRun_scanInv hK (n + 1)).2
  have hfitsF : Fits (n + 1) (onlineRun u v k p₁ r T (n + 1)) :=
    onlineRun_fits hK hk hv (n + 1)
  have hphi := onlineRun_phi (u := u) (T := T) (r := r) hk hK.period_pos hK (n + 1)
  set P := (onlineRun u v k p₁ r T (n + 1)).pos with hP
  set Q := (onlineRun u v k p₁ r T (n + 1)).q with hQdef
  have hphi' : (k + 1) * (n + 1) ≤ (k + 1) * P + Q + k * v.length := by
    have e : Phi k (onlineRun u v k p₁ r T (n + 1)) = (k + 1) * P + Q := rfl
    omega
  have h1 : (k + 1) * P ≤ (k + 1) * i := Nat.mul_le_mul_left _ hposF
  have e1 : (k + 1) * (n + 1) = (k + 1) * i + (k + 1) * v.length := by
    rw [← hin]; ring
  have e2 : (k + 1) * v.length = k * v.length + v.length := by ring
  have hQ : Q = v.length := by omega
  have hfit : P + Q ≤ n + 1 := hfitsF (by omega)
  have h3 : (k + 1) * i ≤ (k + 1) * P := by omega
  have h4 : i ≤ P := Nat.le_of_mul_le_mul_left h3 (by omega)
  have hPi : P = i := by omega
  simp only [reportFlag, decide_eq_false_iff_not, not_and] at hflagF
  exact hflagF hQ (by omega)

/-! ## 主定理 -/

/-- **ラウンド `n` の答えは正しい**：レート `R = gsRate k = k + 1` の走査ステップを
1 ラウンドあたり実行するオンライン機械は、`|x| ≤ n` なる各ラウンド `n` に
「`x` が位置 `n − |x|` に出現するか」をその場で答える。 -/
theorem online_answer_correct {u v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r)
    (hk : 0 < k) (hv : 0 < v.length) (n : ℕ) (hn : (u ++ v).length ≤ n) :
    answer u v k p₁ r T n = decide (OccAt (u ++ v) T (n - (u ++ v).length)) := by
  simp only [List.length_append] at hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set i := m + 1 - v.length with hi
  have hiv : i + v.length = m + 1 := by omega
  have hiu : u.length ≤ i := by omega
  have hrep :
      reportedIn v k p₁ r T (m + 1) (gsRate k) (onlineRun u v k p₁ r T m)
        = decide (OccAt v T i) := by
    refine Bool.eq_iff_iff.mpr ?_
    rw [decide_eq_true_eq]
    constructor
    · intro h
      obtain ⟨p, hp, hocc⟩ :=
        reportedIn_sound hK _ _ (onlineRun_scanInv hK m) h
      have : p = i := by omega
      exact this ▸ hocc
    · intro h
      exact reportedIn_complete hK hk hv hiu h hiv
  simp only [answer, hrep, List.length_append]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [occAt_append_iff]
  have hpos : m + 1 - (u.length + v.length) + u.length = i := by omega
  rw [hpos]
  exact and_comm

/-- `u = []`（`s = 0`, `x = v`）の場合。 -/
theorem online_answer_correct_nil {v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r)
    (hk : 0 < k) (hv : 0 < v.length) (n : ℕ) (hn : v.length ≤ n) :
    answer [] v k p₁ r T n = decide (OccAt v T (n - v.length)) := by
  exact online_answer_correct (u := ([] : List α)) (T := T) hK hk hv n (by simpa using hn)

/-! ## 短い接頭辞 `u` の検証：予測可能性（`DELAYED_PAL.md:36-39`） -/

omit [DecidableEq α] in
/-- **予測可能性（接頭辞検証の締切）**：`k ≥ 3` と L1 の 2 評価
`(k−1)·|u| < |x|`（＝`(k−2)·|u| < |v|`）, `(k−2)·|u| < (k−1)·p₁` のもとで、
どのずらしの直後（`q` が `gsNextQ k p₁ r q` にリセットされた直後）からでも、
完全な候補が報告されるまでに `|v| − gsNextQ k p₁ r q` 回の成功比較があり、
quota = 2 で走る接頭辞検証は `2·(|v| − gsNextQ k p₁ r q) > |u|` 回の比較を得る。
すなわち **報告が起きうるより前に `u` の検証は必ず終わる**。 -/
theorem prefix_verifier_deadline {u v : List α} {k p₁ r : ℕ} (hk : 3 ≤ k) (hp : 0 < p₁)
    (hL1a : (k - 1) * u.length < (u ++ v).length)
    (hL1b : (k - 2) * u.length < (k - 1) * p₁)
    {q : ℕ} (hq : q ≤ v.length) :
    u.length < 2 * (v.length - gsNextQ k p₁ r q) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
  simp only [List.length_append] at hL1a
  have e1 : k' + 3 - 1 = k' + 2 := by omega
  have e2 : k' + 3 - 2 = k' + 1 := by omega
  rw [e1] at hL1a
  rw [e2, e1] at hL1b
  -- `(k'+2)*s < s + |v|` から `(k'+1)*s < |v|`、とくに `s < |v|`
  have ha : (k' + 1) * u.length < v.length := by
    have : (k' + 2) * u.length = (k' + 1) * u.length + u.length := by ring
    omega
  have hsv : u.length < v.length :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left u.length (by omega)) ha
  -- `(k'+1)*s < (k'+2)*p₁` から `s < 2*p₁`
  have hsp : u.length < 2 * p₁ := by
    by_contra hcon
    push Not at hcon
    have h1 : (k' + 1) * (2 * p₁) ≤ (k' + 1) * u.length := Nat.mul_le_mul_left _ hcon
    have h2 : (k' + 1) * (2 * p₁) = (2 * k' + 2) * p₁ := by ring
    have h3 : (2 * k' + 2) * p₁ < (k' + 2) * p₁ := by omega
    have h4 : 2 * k' + 2 < k' + 2 := Nat.lt_of_mul_lt_mul_right h3
    omega
  unfold gsNextQ
  split_ifs with hc
  · have hpq : p₁ ≤ q := le_trans (Nat.le_mul_of_pos_left p₁ (by omega)) hc.1
    omega
  · omega

/-- **論文の仮定一式（`k ≥ 3`, L1 の 2 評価）での実時間定理**。
`online_answer_correct` の方が仮定は弱い（`0 < k` で足りる）が、
GS 前処理が実際に保証するのはこの形。あわせて `prefix_verifier_deadline` が
`u` 検証の締切を保証するので、インターリーブ版のレートは
`gsRateInterleaved k = 3*(k+1)` でよい。 -/
theorem online_answer_correct_L1 {u v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r)
    (hk : 3 ≤ k) (hv : 0 < v.length)
    (hL1a : (k - 1) * u.length < (u ++ v).length)
    (hL1b : (k - 2) * u.length < (k - 1) * p₁) :
    (∀ n, (u ++ v).length ≤ n →
        answer u v k p₁ r T n = decide (OccAt (u ++ v) T (n - (u ++ v).length))) ∧
      (∀ q, q ≤ v.length → u.length < 2 * (v.length - gsNextQ k p₁ r q)) :=
  ⟨fun n hn => online_answer_correct hK (by omega) hv n hn,
    fun q hq => prefix_verifier_deadline hk hK.period_pos hL1a hL1b hq⟩

/-! ## 小例による健全性チェック -/

section Examples

/-- `v = [0,1,1]`（周期なし分解）、`T = [0,1,1,0,1,1]`。
`x = v` なので `|x| = 3`。ラウンド 3 と 6 だけ `true`。 -/
example : answer ([] : List ℕ) [0, 1, 1] 8 3 0 [0, 1, 1, 0, 1, 1] 3 = true := by decide
example : answer ([] : List ℕ) [0, 1, 1] 8 3 0 [0, 1, 1, 0, 1, 1] 4 = false := by decide
example : answer ([] : List ℕ) [0, 1, 1] 8 3 0 [0, 1, 1, 0, 1, 1] 5 = false := by decide
example : answer ([] : List ℕ) [0, 1, 1] 8 3 0 [0, 1, 1, 0, 1, 1] 6 = true := by decide

/-- 周期ずらしの枝（`p₁ = 1`, `r = 8`）。 -/
example :
    answer ([] : List ℕ) [0, 0, 0, 0, 0, 0, 0, 0] 8 1 8
      [0, 0, 0, 0, 0, 0, 0, 0, 0] 8 = true := by decide
example :
    answer ([] : List ℕ) [0, 0, 0, 0, 0, 0, 0, 0] 8 1 8
      [0, 0, 0, 0, 0, 0, 0, 0, 0] 9 = true := by decide

/-- `u = [1]` 付きの完全パターン。`|x| = 9`、出現は位置 `0`（ラウンド 9）だけ。 -/
example :
    answer ([1] : List ℕ) [0, 0, 0, 0, 0, 0, 0, 0] 8 1 8
      [1, 0, 0, 0, 0, 0, 0, 0, 0, 0] 9 = true := by decide
example :
    answer ([1] : List ℕ) [0, 0, 0, 0, 0, 0, 0, 0] 8 1 8
      [1, 0, 0, 0, 0, 0, 0, 0, 0, 0] 10 = false := by decide

example : gsRate 8 = 9 := by decide
example : gsRateInterleaved 8 = 27 := by decide

end Examples

end PalPeg
