import PalPeg.Matching

/-!
# Galil–Seiferas のテキスト走査段（添字レベル）

Galil–Seiferas, *Time-Space-Optimal String Matching*, JCSS 26 (1983) 280–294 の
**走査段**（前処理＝分解は別ファイル）を、`List α` 上の添字レベルで定式化する。

パターンは `x = u ++ v`、`s = u.length`。前処理 `decomposition`
(`docs/palindromes-in-peg/gs_events.py:49-71`) は `x` の接頭辞をひとつずつ削り、
`(cut s, period p₁, reach r)` を返す：`_first` が「`k` 回繰り返される最短の基本接頭辞」
`p₁` とその最初の `k` 個のコピーの端 `k*p₁` を見つけ、続く `compare` ループが
その周期が伸びる限界 `reach = r` まで延長し、`_second` が二つ目の
`k`-繰り返し基本接頭辞を探す。見つかればその分だけ `start` を進めてやり直す。
結果として得られる `v = x.drop s` は **`k`-simple**：`k` 回繰り返される基本接頭辞は
高々ひとつ（`v.take (k*p₁)`）で、その周期の到達域が `r`。
`period = None` の場合は `r = 0`（そのような接頭辞が存在しない）。
本ファイルの `KSimple` は、走査の安全性の証明に必要な部分だけを取り出したもの
（過剰制約を避け、存在証明を別エージェントに渡せる形にしてある）。

走査規則（`GS_OVERLAP.md:31-33`, `gs_events.py:210-218`）：候補位置 `pos` で `v` の
`q` 文字が一致しているとき、

* `k*p₁ ≤ q ≤ r` なら `p₁` 進めて `q - p₁` 文字を保持する、
* そうでなければ `max 1 ⌈q/k⌉` 進めて `q := 0` にする。

主定理：

* `safe_shift` (L2) — ずらし幅の内側には出現がない。
* `safe_shift_matchLen` (L2) — 周期ずらしで保持する `q - p₁` 文字は本当に一致している。
* `scan_sound_complete` — 走査が報告する位置の集合＝`v` の出現位置の集合。
* `phi_step_lt` / `scanSteps_le` (L3) — ポテンシャル `Φ = (k+1)·pos + q` は毎ステップ
  真に増加し、`Φ ≤ (k+1)|T| + |v|` なので総ステップ数は `≤ (k+1)|T| + |v| + 1`。

`k` は固定パラメータ（実装では `k = 8`）。ここでは `0 < k` しか使わないので変数のまま残す。
短い接頭辞 `u` の検証は、この段では素朴な `MatchLen u T i s` としてオラクル的に扱う
（インターリーブと予測可能性は別ファイル）。
-/

namespace PalPeg

universe u
variable {α : Type u}

/-! ## 天井除算 -/

/-- `⌈q / k⌉`（`0 < k` のとき）。`gs_overlap.shift_without_period` の内側。 -/
def ceilDiv (q k : ℕ) : ℕ := (q + k - 1) / k

theorem ceilDiv_bounds {q k : ℕ} (hk : 0 < k) :
    q ≤ k * ceilDiv q k ∧ k * ceilDiv q k ≤ q + k - 1 := by
  have hdm : k * ((q + k - 1) / k) + (q + k - 1) % k = q + k - 1 := Nat.div_add_mod _ _
  have hmod : (q + k - 1) % k < k := Nat.mod_lt _ hk
  obtain ⟨d, hd⟩ : ∃ d, k * ((q + k - 1) / k) = d := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, (q + k - 1) % k = e := ⟨_, rfl⟩
  rw [hd, he] at hdm
  rw [he] at hmod
  unfold ceilDiv
  rw [hd]
  omega

/-! ## 添字による部分一致と出現 -/

/-- `v` の長さ `q` の接頭辞が、テキスト `T` の位置 `i` から一致すること。 -/
def MatchLen (v T : List α) (i q : ℕ) : Prop := ∀ j, j < q → T[i + j]? = v[j]?

instance [DecidableEq α] (v T : List α) (i q : ℕ) : Decidable (MatchLen v T i q) :=
  inferInstanceAs (Decidable (∀ j, j < q → T[i + j]? = v[j]?))

/-- `v` がテキスト `T` の位置 `i` から出現すること（開始位置による表現）。 -/
def OccAt (v T : List α) (i : ℕ) : Prop := MatchLen v T i v.length

instance [DecidableEq α] (v T : List α) (i : ℕ) : Decidable (OccAt v T i) :=
  inferInstanceAs (Decidable (MatchLen v T i v.length))

theorem matchLen_zero (v T : List α) (i : ℕ) : MatchLen v T i 0 := by
  intro j hj; omega

theorem matchLen_mono {v T : List α} {i q q' : ℕ} (h : MatchLen v T i q) (hq : q' ≤ q) :
    MatchLen v T i q' := fun j hj => h j (by omega)

theorem matchLen_succ {v T : List α} {i q : ℕ} (h : MatchLen v T i q)
    (ha : T[i + q]? = v[q]?) : MatchLen v T i (q + 1) := by
  intro j hj
  rcases Nat.lt_or_ge j q with h1 | h1
  · exact h j h1
  · have : j = q := by omega
    subst this; exact ha

/-- 出現があればテキストはそこまで長い（`v` が空でないとき）。 -/
theorem occAt_add_le {v T : List α} {i : ℕ} (h : OccAt v T i) (hv : 0 < v.length) :
    i + v.length ≤ T.length := by
  have hj : v.length - 1 < v.length := by omega
  have h1 := h _ hj
  have h2 : v[v.length - 1]? ≠ none := by
    rw [Ne, List.getElem?_eq_none_iff]; omega
  rw [← h1, Ne, List.getElem?_eq_none_iff] at h2
  omega

/-- `Matching.lean` の接尾辞版 `occursAt` との橋渡し。 -/
theorem occAt_iff_occursAt {v T : List α} {i : ℕ} (h : i + v.length ≤ T.length) :
    OccAt v T i ↔ occursAt v (T.take (i + v.length)) := by
  have hlen : (T.take (i + v.length)).length = i + v.length := by
    simp only [List.length_take]; omega
  constructor
  · intro hocc
    refine ⟨by omega, ?_⟩
    rw [hlen, show i + v.length - v.length = i from by omega]
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_drop, List.getElem?_take]
    by_cases hj : j < v.length
    · rw [if_pos (by omega)]; exact (hocc j hj).symm
    · rw [if_neg (by omega), List.getElem?_eq_none (by omega)]
  · rintro ⟨hle, heq⟩
    intro j hj
    have hcong := congrArg (fun l => l[j]?) heq
    simp only [List.getElem?_drop, hlen, show i + v.length - v.length = i from by omega] at hcong
    rw [hcong, List.getElem?_take_of_lt (show i + j < i + v.length by omega)]

/-! ## `k`-simple（分解の出力が満たす性質） -/

/-- `w` の最短の正の周期。 -/
def ShortestPeriod (w : List α) (p : ℕ) : Prop :=
  0 < p ∧ HasPeriod w p ∧ ∀ p', 0 < p' → HasPeriod w p' → p ≤ p'

theorem exists_shortestPeriod (w : List α) : ∃ p, ShortestPeriod w p := by
  classical
  have hne : ∃ p, 0 < p ∧ HasPeriod w p :=
    ⟨w.length + 1, Nat.succ_pos _, hasPeriod_of_length_le (Nat.le_succ _)⟩
  exact ⟨Nat.find hne, (Nat.find_spec hne).1, (Nat.find_spec hne).2,
    fun p' hp' hper => Nat.find_le ⟨hp', hper⟩⟩

/-- **`v` が `(k, p₁, r)` で `k`-simple**。走査の安全性に必要な性質だけを述べる。

* `period_pos` — `0 < p₁`。
* `reach_period` — `p₁` は到達域 `v.take r` の周期。
* `no_small_repeat` — `v` の接頭辞 `v.take q` が `k` 回以上繰り返される周期 `p'`
  （`k * p' ≤ q`）を持つなら、`p₁ ≤ p'` かつ `q ≤ r`。
  すなわち「`k` 回繰り返される基本接頭辞は高々ひとつで、その到達域は `r`」。

`period = None`（`k` 回繰り返される基本接頭辞なし）の場合は
`p₁ := v.length + 1`, `r := 0` が常に満たす（`ksimple_of_no_period`）。
すなわちこの定義は過剰制約ではない。 -/
structure KSimple (v : List α) (k p₁ r : ℕ) : Prop where
  period_pos : 0 < p₁
  reach_period : HasPeriod (v.take r) p₁
  no_small_repeat : ∀ q p', q ≤ v.length → 0 < p' → k * p' ≤ q →
    HasPeriod (v.take q) p' → p₁ ≤ p' ∧ q ≤ r

/-- 「最短周期」で述べた標準的な GS 条件から `KSimple` が従う。 -/
theorem ksimple_of_shortest {v : List α} {k p₁ r : ℕ} (hp : 0 < p₁)
    (hper : HasPeriod (v.take r) p₁)
    (huniq : ∀ q p', q ≤ v.length → ShortestPeriod (v.take q) p' → k * p' ≤ q →
      p' = p₁ ∧ q ≤ r) :
    KSimple v k p₁ r := by
  refine ⟨hp, hper, ?_⟩
  intro q p' hq hp' hkp hper'
  obtain ⟨m, hm⟩ := exists_shortestPeriod (v.take q)
  have hmp : m ≤ p' := hm.2.2 p' hp' hper'
  have hkm : k * m ≤ q := le_trans (Nat.mul_le_mul (Nat.le_refl k) hmp) hkp
  obtain ⟨h1, h2⟩ := huniq q m hq hm hkm
  exact ⟨by omega, h2⟩

/-- 周期のない分解（`decomposition` が `Decomposition(start, None, 0)` を返す場合）でも
`KSimple` は満たされる：この定義は空でない。 -/
theorem ksimple_of_no_period (v : List α) (k : ℕ) (hk : 0 < k) :
    KSimple v k (v.length + 1) 0 := by
  refine ⟨Nat.succ_pos _, by simp [HasPeriod], ?_⟩
  intro q p' hq hp' hkp _
  exfalso
  have hle : p' ≤ k * p' := by
    have := Nat.mul_le_mul hk (Nat.le_refl p')
    simpa using this
  omega

/-! ## 走査の状態と一歩 -/

/-- 走査状態：`v` の候補開始位置 `pos` と、そこで一致済みの長さ `q`。 -/
structure ScanState where
  pos : ℕ
  q : ℕ
deriving DecidableEq, Repr

@[simp] theorem ScanState.mk_pos (a b : ℕ) : (ScanState.mk a b).pos = a := rfl
@[simp] theorem ScanState.mk_q (a b : ℕ) : (ScanState.mk a b).q = b := rfl

/-- 安全なずらし幅（`gs_events.py:210-218`）。 -/
def gsShift (k p₁ r q : ℕ) : ℕ :=
  if k * p₁ ≤ q ∧ q ≤ r then p₁ else max 1 (ceilDiv q k)

/-- ずらした後に保持できる一致長。 -/
def gsNextQ (k p₁ r q : ℕ) : ℕ :=
  if k * p₁ ≤ q ∧ q ≤ r then q - p₁ else 0

theorem gsShift_pos {k p₁ r q : ℕ} (hp : 0 < p₁) : 0 < gsShift k p₁ r q := by
  unfold gsShift; split_ifs <;> omega

variable [DecidableEq α]

/-- 走査の一歩。`q = |v|`（＝出現を報告した直後）と不一致のときはずらす。 -/
def scanStep (v : List α) (k p₁ r : ℕ) (T : List α) (st : ScanState) : ScanState :=
  if st.q = v.length then
    ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩
  else if T[st.pos + st.q]? = v[st.q]? then
    ⟨st.pos, st.q + 1⟩
  else
    ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩

/-- 走査本体：`fuel` 歩まで、または候補が末尾を越えるまで走り、報告位置を集める。 -/
def scanRun (v : List α) (k p₁ r : ℕ) (T : List α) : ℕ → ScanState → List ℕ
  | 0, _ => []
  | fuel + 1, st =>
      if T.length < st.pos + v.length then []
      else if st.q = v.length then
        st.pos :: scanRun v k p₁ r T fuel (scanStep v k p₁ r T st)
      else scanRun v k p₁ r T fuel (scanStep v k p₁ r T st)

/-- 実際に実行された歩数。 -/
def scanSteps (v : List α) (k p₁ r : ℕ) (T : List α) : ℕ → ScanState → ℕ
  | 0, _ => 0
  | fuel + 1, st =>
      if T.length < st.pos + v.length then 0
      else 1 + scanSteps v k p₁ r T fuel (scanStep v k p₁ r T st)

/-- ポテンシャル `Φ = (k+1)·pos + q`（`GS_OVERLAP.md:34-36`）。 -/
def Phi (k : ℕ) (st : ScanState) : ℕ := (k + 1) * st.pos + st.q

/-- 走査の不変条件。 -/
def ScanInv (v T : List α) (st : ScanState) : Prop :=
  MatchLen v T st.pos st.q ∧ st.q ≤ v.length

/-! ## 一歩の基本性質 -/

theorem scanStep_pos_le (v : List α) (k p₁ r : ℕ) (T : List α) (st : ScanState) :
    st.pos ≤ (scanStep v k p₁ r T st).pos := by
  unfold scanStep; split_ifs <;> simp

theorem scanStep_q_le {v T : List α} {k p₁ r : ℕ} {st : ScanState} (h : st.q ≤ v.length) :
    (scanStep v k p₁ r T st).q ≤ v.length := by
  unfold scanStep gsNextQ; split_ifs <;> simp <;> omega

/-- **L2（保持部分の正しさ）**：周期ずらしで残す `q - p₁` 文字は本当に一致している。 -/
theorem safe_shift_matchLen {v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r)
    {pos q : ℕ} (hq : q ≤ v.length) (hqr : q ≤ r) (hm : MatchLen v T pos q) :
    MatchLen v T (pos + p₁) (q - p₁) := by
  have hpre : (v.take r).take q = v.take q := by
    rw [List.take_take]; congr 1; omega
  have hper : HasPeriod (v.take q) p₁ := hpre ▸ hasPeriod_take hK.reach_period
  have hlen : (v.take q).length = q := by simp only [List.length_take]; omega
  intro j hj
  have hjq : j + p₁ < q := by omega
  have h1 : (v.take q)[j]? = (v.take q)[j + p₁]? := hper j (by omega)
  rw [List.getElem?_take_of_lt (show j < q by omega), List.getElem?_take_of_lt hjq] at h1
  have h2 : T[pos + (p₁ + j)]? = v[p₁ + j]? := hm _ (by omega)
  calc T[pos + p₁ + j]? = T[pos + (p₁ + j)]? := getElem?_congr (by omega)
    _ = v[p₁ + j]? := h2
    _ = v[j + p₁]? := getElem?_congr (by omega)
    _ = v[j]? := h1.symm

theorem scanStep_inv {v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r) {st : ScanState}
    (h : ScanInv v T st) : ScanInv v T (scanStep v k p₁ r T st) := by
  obtain ⟨hm, hq⟩ := h
  have hshift : ScanInv v T ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ := by
    unfold ScanInv gsShift gsNextQ
    split_ifs with hc
    · exact ⟨safe_shift_matchLen hK hq hc.2 hm, by simp; omega⟩
    · exact ⟨by simpa using matchLen_zero v T _, by simp⟩
  unfold scanStep
  split_ifs with h1 h2
  · exact hshift
  · exact ⟨by simpa using matchLen_succ hm h2, by simp; omega⟩
  · exact hshift

/-! ## L2：安全なずらし -/

/-- 一致部分の内側にもうひとつ出現があれば、そのずれは一致部分の周期になる。 -/
theorem hasPeriod_of_occ {v T : List α} {pos q δ : ℕ} (hq : q ≤ v.length)
    (hm : MatchLen v T pos q) (hδ : 0 < δ) (hocc : OccAt v T (pos + δ)) :
    HasPeriod (v.take q) δ := by
  have hlen : (v.take q).length = q := by simp only [List.length_take]; omega
  intro i hi
  rw [hlen] at hi
  rw [List.getElem?_take_of_lt (show i < q by omega), List.getElem?_take_of_lt hi]
  have h1 : T[pos + δ + i]? = v[i]? := hocc i (by omega)
  have h2 : T[pos + (i + δ)]? = v[i + δ]? := hm _ hi
  rw [← h1, ← h2]
  exact getElem?_congr (by omega)

/-- **L2（安全なずらし）**：`KSimple` のもとで、`(pos, pos + shift)` には出現がない。 -/
theorem safe_shift {v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r) (hk : 0 < k)
    {pos q : ℕ} (hq : q ≤ v.length) (hm : MatchLen v T pos q)
    {δ : ℕ} (hδ : 0 < δ) (hδ' : δ < gsShift k p₁ r q) :
    ¬ OccAt v T (pos + δ) := by
  intro hocc
  have hper : HasPeriod (v.take q) δ := hasPeriod_of_occ hq hm hδ hocc
  unfold gsShift at hδ'
  split_ifs at hδ' with hc
  · have hkd : k * δ ≤ q :=
      le_trans (Nat.mul_le_mul (Nat.le_refl k) (Nat.le_of_lt hδ')) hc.1
    have := hK.no_small_repeat q δ hq hδ hkd hper
    omega
  · have hkd : k * δ ≤ q := by
      have hδ2 : δ + 1 ≤ ceilDiv q k := by omega
      have h2 : k * (δ + 1) ≤ k * ceilDiv q k := Nat.mul_le_mul (Nat.le_refl k) hδ2
      have h3 : k * ceilDiv q k ≤ q + k - 1 := (ceilDiv_bounds hk).2
      have h4 : k * (δ + 1) = k * δ + k := by ring
      omega
    obtain ⟨h1, h2⟩ := hK.no_small_repeat q δ hq hδ hkd hper
    exact hc ⟨le_trans (Nat.mul_le_mul (Nat.le_refl k) h1) hkd, h2⟩

/-- ずらした先も、出現位置 `i` を追い越さない。 -/
theorem scanStep_pos_le_of_occ {v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r)
    (hk : 0 < k) {st : ScanState} (hinv : ScanInv v T st) {i : ℕ}
    (hocc : OccAt v T i) (hpos : st.pos ≤ i) (hne : st.q = v.length → st.pos ≠ i) :
    (scanStep v k p₁ r T st).pos ≤ i := by
  obtain ⟨hm, hq⟩ := hinv
  have hgap : st.pos < i → st.pos + gsShift k p₁ r st.q ≤ i := by
    intro hlt
    by_contra hcon
    push_neg at hcon
    refine safe_shift hK hk hq hm (δ := i - st.pos) (by omega) (by omega) ?_
    rwa [show st.pos + (i - st.pos) = i from by omega]
  unfold scanStep
  split_ifs with h1 h2
  · exact hgap (Nat.lt_of_le_of_ne hpos (hne h1))
  · simpa using hpos
  · refine hgap ?_
    rcases Nat.eq_or_lt_of_le hpos with heq | hlt
    · exact absurd (heq ▸ hocc st.q (by omega)) h2
    · exact hlt

/-! ## 健全性と完全性 -/

theorem scan_sound {v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r) :
    ∀ (fuel : ℕ) (st : ScanState), ScanInv v T st →
      ∀ i, i ∈ scanRun v k p₁ r T fuel st → st.pos ≤ i ∧ OccAt v T i := by
  intro fuel
  induction fuel with
  | zero => intro st _ i hi; simp [scanRun] at hi
  | succ fuel ih =>
    intro st hinv i hi
    simp only [scanRun] at hi
    split_ifs at hi with hstop hrep
    · simp at hi
    · rcases List.mem_cons.mp hi with rfl | hi
      · refine ⟨Nat.le_refl _, ?_⟩
        have hmm := hinv.1
        rw [hrep] at hmm
        exact hmm
      · obtain ⟨h1, h2⟩ := ih _ (scanStep_inv hK hinv) i hi
        exact ⟨le_trans (scanStep_pos_le v k p₁ r T st) h1, h2⟩
    · obtain ⟨h1, h2⟩ := ih _ (scanStep_inv hK hinv) i hi
      exact ⟨le_trans (scanStep_pos_le v k p₁ r T st) h1, h2⟩

/-- **L3（ポテンシャル）**：一歩ごとに `Φ` は真に増加する。 -/
theorem phi_step_lt {v T : List α} {k p₁ r : ℕ} (hk : 0 < k) (hp : 0 < p₁)
    (st : ScanState) : Phi k st < Phi k (scanStep v k p₁ r T st) := by
  have hpk : p₁ ≤ k * p₁ := by
    have := Nat.mul_le_mul hk (Nat.le_refl p₁); simpa using this
  have hshift : Phi k st < Phi k ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ := by
    simp only [Phi, ScanState.mk_pos, ScanState.mk_q]
    unfold gsShift gsNextQ
    split_ifs with hc
    · have e1 : (k + 1) * (st.pos + p₁) = (k + 1) * st.pos + (k * p₁ + p₁) := by ring
      have e2 : 0 < k * p₁ := Nat.mul_pos hk hp
      omega
    · have hcm : st.q ≤ k * ceilDiv st.q k := (ceilDiv_bounds hk).1
      have hle : k * ceilDiv st.q k ≤ k * max 1 (ceilDiv st.q k) :=
        Nat.mul_le_mul (Nat.le_refl k) (Nat.le_max_right _ _)
      have e1 : (k + 1) * (st.pos + max 1 (ceilDiv st.q k))
          = (k + 1) * st.pos + (k * max 1 (ceilDiv st.q k) + max 1 (ceilDiv st.q k)) := by
        ring
      have e2 : 1 ≤ max 1 (ceilDiv st.q k) := Nat.le_max_left _ _
      omega
  unfold scanStep
  split_ifs with h1 h2
  · exact hshift
  · simp only [Phi, ScanState.mk_pos, ScanState.mk_q]; omega
  · exact hshift

theorem scan_complete {v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r) (hk : 0 < k)
    (hv : 0 < v.length) :
    ∀ (fuel : ℕ) (st : ScanState), ScanInv v T st →
      ∀ i, OccAt v T i → st.pos ≤ i →
      (k + 1) * T.length + v.length + 1 ≤ Phi k st + fuel →
      i ∈ scanRun v k p₁ r T fuel st := by
  intro fuel
  induction fuel with
  | zero =>
    intro st hinv i hocc hpos hf
    exfalso
    have h1 : i + v.length ≤ T.length := occAt_add_le hocc hv
    have h2 : st.q ≤ v.length := hinv.2
    have h3 : (k + 1) * st.pos ≤ (k + 1) * T.length :=
      Nat.mul_le_mul (Nat.le_refl _) (by omega)
    have h4 : Phi k st = (k + 1) * st.pos + st.q := rfl
    omega
  | succ fuel ih =>
    intro st hinv i hocc hpos hf
    have hiT : i + v.length ≤ T.length := occAt_add_le hocc hv
    have hfuel' : (k + 1) * T.length + v.length + 1 ≤
        Phi k (scanStep v k p₁ r T st) + fuel := by
      have := phi_step_lt (v := v) (T := T) (r := r) hk hK.period_pos st
      omega
    simp only [scanRun]
    rw [if_neg (by omega : ¬ (T.length < st.pos + v.length))]
    by_cases hrep : st.q = v.length
    · rw [if_pos hrep]
      by_cases hi : i = st.pos
      · simp [hi]
      · refine List.mem_cons_of_mem _ ?_
        exact ih _ (scanStep_inv hK hinv) i hocc
          (scanStep_pos_le_of_occ hK hk hinv hocc hpos (fun _ h => hi h.symm)) hfuel'
    · rw [if_neg hrep]
      exact ih _ (scanStep_inv hK hinv) i hocc
        (scanStep_pos_le_of_occ hK hk hinv hocc hpos (fun h => absurd h hrep)) hfuel'

/-- **走査の健全性と完全性**：報告される位置の集合はちょうど `v` の出現位置の集合。 -/
theorem scan_sound_complete {v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r)
    (hk : 0 < k) (hv : 0 < v.length) {fuel : ℕ}
    (hfuel : (k + 1) * T.length + v.length + 1 ≤ fuel) (i : ℕ) :
    i ∈ scanRun v k p₁ r T fuel ⟨0, 0⟩ ↔ OccAt v T i := by
  have hinv : ScanInv v T ⟨0, 0⟩ := ⟨by simpa using matchLen_zero v T 0, by simp⟩
  constructor
  · intro h; exact (scan_sound hK fuel _ hinv i h).2
  · intro h
    refine scan_complete hK hk hv fuel _ hinv i h (by simp) ?_
    simp only [Phi, ScanState.mk_pos, ScanState.mk_q]
    omega

/-- 出現の接尾辞版（`Matching.occursAt`）での言い換え。 -/
theorem scan_sound_complete_occursAt {v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r)
    (hk : 0 < k) (hv : 0 < v.length) {fuel : ℕ}
    (hfuel : (k + 1) * T.length + v.length + 1 ≤ fuel) (i : ℕ)
    (hi : i + v.length ≤ T.length) :
    i ∈ scanRun v k p₁ r T fuel ⟨0, 0⟩ ↔ occursAt v (T.take (i + v.length)) :=
  (scan_sound_complete hK hk hv hfuel i).trans (occAt_iff_occursAt hi)

/-! ## 短い接頭辞 `u` の検査（この段ではオラクル） -/

theorem occAt_append_iff {u v T : List α} {i : ℕ} :
    OccAt (u ++ v) T i ↔ MatchLen u T i u.length ∧ OccAt v T (i + u.length) := by
  constructor
  · intro h
    constructor
    · intro j hj
      have hjj := h j (by simp; omega)
      rwa [List.getElem?_append_left hj] at hjj
    · intro j hj
      have hjj := h (u.length + j) (by simp; omega)
      rw [List.getElem?_append_right (by omega),
        show u.length + j - u.length = j from by omega] at hjj
      rw [← hjj]
      exact getElem?_congr (by omega)
  · rintro ⟨h1, h2⟩ j hj
    simp only [List.length_append] at hj
    by_cases hju : j < u.length
    · rw [List.getElem?_append_left hju]; exact h1 j hju
    · rw [List.getElem?_append_right (by omega)]
      have hjj := h2 (j - u.length) (by omega)
      rw [← hjj]
      exact getElem?_congr (by omega)

/-- パターン `x = u ++ v` の走査：`v` を GS 規則で探し、見つけた位置で `u` を直接検査する。 -/
def gsScan (u v : List α) (k p₁ r : ℕ) (T : List α) (fuel : ℕ) : List ℕ :=
  ((scanRun v k p₁ r T fuel ⟨u.length, 0⟩).map (fun p => p - u.length)).filter
    (fun i => decide (MatchLen u T i u.length))

theorem gsScan_sound_complete {u v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r)
    (hk : 0 < k) (hv : 0 < v.length) {fuel : ℕ}
    (hfuel : (k + 1) * T.length + v.length + 1 ≤ fuel) (i : ℕ) :
    i ∈ gsScan u v k p₁ r T fuel ↔ OccAt (u ++ v) T i := by
  have hinv : ScanInv v T ⟨u.length, 0⟩ :=
    ⟨by simpa using matchLen_zero v T u.length, by simp⟩
  unfold gsScan
  rw [List.mem_filter, List.mem_map]
  simp only [decide_eq_true_eq]
  rw [occAt_append_iff]
  constructor
  · rintro ⟨⟨p, hp, hpi⟩, hu⟩
    obtain ⟨h1, h2⟩ := scan_sound hK fuel _ hinv p hp
    simp only [ScanState.mk_pos] at h1
    have hpe : p = i + u.length := by omega
    exact ⟨hu, hpe ▸ h2⟩
  · rintro ⟨hu, hocc⟩
    refine ⟨⟨i + u.length, ?_, by omega⟩, hu⟩
    refine scan_complete hK hk hv fuel _ hinv _ hocc (by simp) ?_
    simp only [Phi, ScanState.mk_pos, ScanState.mk_q]
    omega

/-! ## L3：線形時間 -/

theorem phi_le_of_in_range {v T : List α} {k : ℕ} {st : ScanState}
    (hpos : st.pos + v.length ≤ T.length) (hq : st.q ≤ v.length) :
    Phi k st ≤ (k + 1) * T.length + v.length := by
  have h3 : (k + 1) * st.pos ≤ (k + 1) * T.length :=
    Nat.mul_le_mul (Nat.le_refl _) (by omega)
  have h4 : Phi k st = (k + 1) * st.pos + st.q := rfl
  omega

/-- **L3（線形仕事量）**：歩数はポテンシャルの残り以下。 -/
theorem scanSteps_le {v T : List α} {k p₁ r : ℕ} (hk : 0 < k) (hp : 0 < p₁) :
    ∀ (fuel : ℕ) (st : ScanState), st.q ≤ v.length →
      scanSteps v k p₁ r T fuel st ≤ (k + 1) * T.length + v.length + 1 - Phi k st := by
  intro fuel
  induction fuel with
  | zero => intro st _; simp [scanSteps]
  | succ fuel ih =>
    intro st hq
    simp only [scanSteps]
    split_ifs with hstop
    · exact Nat.zero_le _
    · have hbound : Phi k st ≤ (k + 1) * T.length + v.length :=
        phi_le_of_in_range (by omega) hq
      have hlt := phi_step_lt (v := v) (T := T) (p₁ := p₁) (r := r) hk hp st
      have hih := ih (scanStep v k p₁ r T st) (scanStep_q_le hq)
      omega

/-- 走査全体の歩数は `(k+1)|T| + |v| + 1` 以下（線形）。 -/
theorem scanSteps_le_bound {v T : List α} {k p₁ r : ℕ} (hk : 0 < k) (hp : 0 < p₁)
    (fuel : ℕ) :
    scanSteps v k p₁ r T fuel ⟨0, 0⟩ ≤ (k + 1) * T.length + v.length + 1 := by
  have h := scanSteps_le (v := v) (T := T) (p₁ := p₁) (r := r) hk hp fuel ⟨0, 0⟩ (by simp)
  have h0 : Phi k (⟨0, 0⟩ : ScanState) = 0 := by simp [Phi]
  omega

/-- 報告数は歩数以下。 -/
theorem scanRun_length_le {v T : List α} {k p₁ r : ℕ} :
    ∀ (fuel : ℕ) (st : ScanState),
      (scanRun v k p₁ r T fuel st).length ≤ scanSteps v k p₁ r T fuel st := by
  intro fuel
  induction fuel with
  | zero => intro st; simp [scanRun, scanSteps]
  | succ fuel ih =>
    intro st
    simp only [scanRun, scanSteps]
    split_ifs with h1 h2
    · simp
    · have h := ih (scanStep v k p₁ r T st)
      simp only [List.length_cons]
      omega
    · have h := ih (scanStep v k p₁ r T st)
      omega

/-! ## 小例による健全性チェック -/

section Examples

/-- 周期を持たない場合の分解（`period = None`, `r = 0`）。 -/
example : KSimple ([0, 1, 1] : List ℕ) 8 3 0 := by
  refine ⟨by norm_num, by simp [HasPeriod], ?_⟩
  intro q p' hq hp' hkp _
  simp only [List.length_cons, List.length_nil] at hq
  omega

example : scanRun ([0, 1, 1] : List ℕ) 8 3 0 [0, 1, 1, 0, 1, 1] 20 ⟨0, 0⟩ = [0, 3] := by
  decide

/-- 周期を持つ場合（`p₁ = 1`, `r = 8`）。周期ずらしの枝を通る。 -/
example : KSimple ([0, 0, 0, 0, 0, 0, 0, 0] : List ℕ) 8 1 8 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro i hi
    simp only [List.length_take, List.length_cons, List.length_nil] at hi
    interval_cases i <;> rfl
  · intro q p' hq hp' hkp _
    simp only [List.length_cons, List.length_nil] at hq
    omega

example :
    scanRun ([0, 0, 0, 0, 0, 0, 0, 0] : List ℕ) 8 1 8 [0, 0, 0, 0, 0, 0, 0, 0, 0] 20 ⟨0, 0⟩
      = [0, 1] := by
  decide

example : gsShift 8 1 8 8 = 1 := by decide
example : gsNextQ 8 1 8 8 = 7 := by decide
example : gsShift 8 3 0 3 = 1 := by decide
example : gsShift 8 2 40 40 = 2 := by decide
example : gsShift 8 2 40 41 = 6 := by decide

example : OccAt ([0, 1, 1] : List ℕ) [0, 1, 1, 0, 1, 1] 3 := by decide
example : ¬ OccAt ([0, 1, 1] : List ℕ) [0, 1, 1, 0, 1, 1] 1 := by decide

/-- `u = [1]`, `v = [0,0,0,0,0,0,0,0]` の完全パターン走査。 -/
example :
    gsScan ([1] : List ℕ) [0, 0, 0, 0, 0, 0, 0, 0] 8 1 8
      [1, 0, 0, 0, 0, 0, 0, 0, 0, 0] 30 = [0] := by
  decide

end Examples

end PalPeg
