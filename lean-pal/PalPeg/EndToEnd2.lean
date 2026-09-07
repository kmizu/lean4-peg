import PalPeg.EndToEnd
import PalPeg.GSDecompose2Work

/-!
# `decompose2` による中央・前処理実装の再インスタンス化（EndToEnd2）

`PalPeg.EndToEnd` は `decompose` を使い、**二つ**の仮定
（`hdec : GSDecomp …` と `hOK : DecOK`）を外から受け取っていた。
本ファイルは同じ組み立てを `decompose2`（`PalPeg.GSDecompose2`）で行う。
`decompose2_gsDecomp` は**無条件**なので正当性の仮定はすべて消え、
残るのは仕事量の仮説

`PassPeriodSum k C₁ : ∀ x b s, stripLoop2Periods x k b (|x|+1) s ≤ C₁ * b`

ただ一つになる。
-/

namespace PalPeg
namespace EndToEnd2

open MiddleBorder

variable {α : Type} [DecidableEq α]

/-! ## §0 唯一残る仮説 -/

/-- **唯一残る仮説**：1 パスで `firstOuter` が返す最小周期の総和が `bound` に線形。 -/
def PassPeriodSum (k C₁ : ℕ) : Prop :=
  ∀ (x : List (Fin 2)) (b s : ℕ), stripLoop2Periods x k b (x.length + 1) s ≤ C₁ * b

/-! ## §1 段の分解 -/

/-- 窓 `y` の段 `L` に与える分解：`decompose2 (y.take L) k`。
`p₁ = 0`（`k`-繰り返しが存在しない）の退化ケースだけ `KSimple` が要求する
`0 < p₁` に合わせて正規化する（`GSDecompL1.stageOK_exists` と同じ形）。 -/
def gsDec2 (y : List α) (k : ℕ) : ℕ → ℕ × ℕ × ℕ := fun L =>
  if (decompose2 (y.take L) k).2.1 = 0 then
    ((decompose2 (y.take L) k).1,
      ((y.take L).drop (decompose2 (y.take L) k).1).length + 1, 0)
  else decompose2 (y.take L) k

theorem gsDec2_fst (y : List α) (k L : ℕ) :
    (gsDec2 y k L).1 = (decompose2 (y.take L) k).1 := by
  simp only [gsDec2]; split_ifs <;> rfl

/-- **無条件の段の正当性**（`MiddleBorder.DecOK` に対応、ただし仮定ではなく定理）。 -/
theorem decOK2 (y : List α) (L : ℕ) (hL : 1 ≤ L) :
    StageOK y 8 L (gsDec2 y 8 L).1 (gsDec2 y 8 L).2.1 (gsDec2 y 8 L).2.2 := by
  set x := y.take L with hx
  have hxL : x.length ≤ L := by simp [hx, List.length_take]
  have H := decompose2_gsDecomp (k := 8) (by omega) x
  set s := (decompose2 x 8).1 with hs
  have hcut : s ≤ x.length := H.cut_le
  have hne : x.length = 0 → s = 0 := by intro h; omega
  have hpos : 0 < x.length → 7 * s < x.length := by
    intro h
    have hx0 : x ≠ [] := by
      intro hc; rw [hc] at h; simp at h
    have := H.cut_bound hx0
    simpa using this
  have hshort : (8 - 1) * s < L := by
    rcases Nat.eq_zero_or_pos x.length with h0 | h0
    · have := hne h0; omega
    · have := hpos h0; omega
  have hdlen : (x.drop s).length = x.length - s := List.length_drop
  simp only [gsDec2, ← hx, ← hs]
  split_ifs with hp
  · refine ⟨by omega, H.toGSCore.ksimple_none hp, ?_, hshort⟩
    show s ≤ 8 * ((x.drop s).length + 1)
    rcases Nat.eq_zero_or_pos x.length with h0 | h0
    · have := hne h0; omega
    · have := hpos h0; omega
  · exact ⟨by omega, H.ksimple hp, cut_charge_of_ratio (by omega) (H.cut_period_bound hp),
      hshort⟩

/-! ## §2 一つの凍結窓に対する仕事 -/

/-- 窓 `y` の回文接頭辞フラグ。 -/
def borderFlags2 (y : List α) : List Bool := palPrefixFlagsGS y (gsDec2 y 8) 8

/-- 各段のパターン `y.take L` に対する `decompose2` 前処理の費用の総和。 -/
def decompTotal2 (y : List α) (dec : ℕ → ℕ × ℕ × ℕ) (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, L =>
      if L = 0 then 0
      else decompose2Work (y.take L) k + decompTotal2 y dec k fuel (nextLen (dec L).1)

/-- 窓 `y` を処理する総仕事量。 -/
def borderWork2 (y : List α) : ℕ :=
  totalSteps y (gsDec2 y 8) 8 + decompTotal2 y (gsDec2 y 8) 8 (y.length + 1) y.length

/-- 段ごとの `decompose2Work` の線形係数（`k = 8`）：`(4k+2)*C₁ + 17k + 50`。 -/
def CW (C₁ : ℕ) : ℕ := 34 * C₁ + 186

/-- 総和の係数：`3 * (CW + 21)`。 -/
def Cwork (C₁ : ℕ) : ℕ := 102 * C₁ + 621

theorem decompTotal2_le {C₁ : ℕ} (hsum : PassPeriodSum 8 C₁) (y : List (Fin 2)) :
    ∀ (fuel L : ℕ), decompTotal2 y (gsDec2 y 8) 8 fuel L ≤ Cwork C₁ * L := by
  intro fuel
  induction fuel with
  | zero => intro L; simp [decompTotal2]
  | succ fuel ih =>
    intro L
    simp only [decompTotal2]
    split_ifs with h0
    · exact Nat.zero_le _
    · obtain ⟨M, rfl⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
      set B := CW C₁ + 21 with hB
      have hA : Cwork C₁ = 3 * B := by simp only [Cwork, hB, CW]; ring
      have hw : decompose2Work (y.take (M + 1)) 8 ≤ CW C₁ * (M + 1) + 21 := by
        have h := decompose2Work_le (y.take (M + 1)) 8 C₁ (by omega)
          (fun b s => hsum (y.take (M + 1)) b s)
        have hlen : (y.take (M + 1)).length ≤ M + 1 := by simp [List.length_take]
        have hmul : ((4 * 8 + 2) * C₁ + 17 * 8 + 50) * (y.take (M + 1)).length
            ≤ CW C₁ * (M + 1) := by
          have : ((4 * 8 + 2) * C₁ + 17 * 8 + 50) = CW C₁ := by simp [CW]
          rw [this]
          exact Nat.mul_le_mul_left _ hlen
        omega
      have hshort := (decOK2 y (M + 1) (by omega)).cut_short
      have hshrink : 3 * nextLen (gsDec2 y 8 (M + 1)).1 + 1 ≤ M + 1 :=
        nextLen_shrink (by omega)
      have hrec := ih (nextLen (gsDec2 y 8 (M + 1)).1)
      set N := nextLen (gsDec2 y 8 (M + 1)).1 with hN
      have hAN : Cwork C₁ * N = B * (3 * N) := by rw [hA]; ring
      have h1 : B * (3 * N) ≤ B * M := Nat.mul_le_mul_left _ (by omega)
      have h2 : CW C₁ * (M + 1) ≤ B * (M + 1) := Nat.mul_le_mul_right _ (by omega)
      have h3 : B * (M + 1) = B * M + B := by ring
      have h4 : Cwork C₁ * (M + 1) = 3 * (B * M) + 3 * B := by rw [hA]; ring
      have h5 : 21 ≤ B := by simp only [hB]; omega
      set bm := B * M with hbm
      omega

theorem borderWork2_le {C₁ : ℕ} (hsum : PassPeriodSum 8 C₁) (y : List (Fin 2)) :
    borderWork2 y ≤ (258 + Cwork C₁) * y.length := by
  have h1 : totalSteps y (gsDec2 y 8) 8 ≤ 258 * y.length :=
    palPrefixFlagsGS_work (fun L hL _ => decOK2 y L hL)
  have h2 := decompTotal2_le hsum y (y.length + 1) y.length
  have h3 : (258 + Cwork C₁) * y.length = 258 * y.length + Cwork C₁ * y.length := by ring
  simp only [borderWork2]
  omega

/-! ## §3 ラウンド実装 -/

/-- サービスレート。 -/
def rate2 (C₁ : ℕ) : ℕ := 50 * (258 + Cwork C₁)

/-- 1 ラウンドの費用上界。 -/
def Cm2 (C₁ : ℕ) : ℕ := rate2 C₁ + 1

/-- 状態遷移（`MiddleBorder.bstep` の `decompose2` 版）。 -/
def bstep2 (C₁ : ℕ) (t : List α) (n : ℕ) (st : BState α) : BState α :=
  if st.width < 8 then
    { st with out := naiveFlags ((t.drop (st.width / 2)).take (3 * st.width)) }
  else if n = st.next ∧ st.idx < numJobs then
    let j := st.idx + 1
    let win := (t.drop (st.width / 2)).take (st.width + j * gw st.width)
    { width := st.width, idx := j, next := n + gw st.width, cur := win,
      rem := borderWork2 win, out := borderFlags2 st.cur }
  else
    { st with rem := st.rem - rate2 C₁ }

/-- **`decompose2` 版の中央フラグ実装**。 -/
def borderMiddle2 (α : Type) [DecidableEq α] (C₁ : ℕ) : MiddleImpl α where
  State := BState α
  init S := ⟨S, 0, relTime S 1, [], 0, []⟩
  step := bstep2 C₁
  flag st n := st.out.getD (n - st.width) false
  cost _ _ st := if st.width < 8 then 3 * st.width * st.width + 1
    else min st.rem (rate2 C₁) + 1

theorem borderMiddle2_cost_le (C₁ : ℕ) (t : List α) (n : ℕ) (st : BState α) :
    (borderMiddle2 α C₁).cost t n st ≤ Cm2 C₁ := by
  show (if st.width < 8 then 3 * st.width * st.width + 1
    else min st.rem (rate2 C₁) + 1) ≤ Cm2 C₁
  split_ifs with h
  · have : 3 * st.width * st.width ≤ 3 * 7 * 7 := by
      have h1 : st.width ≤ 7 := by omega
      calc 3 * st.width * st.width ≤ 3 * 7 * st.width :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 h1)
        _ ≤ 3 * 7 * 7 := Nat.mul_le_mul_left _ h1
    have hr : 147 ≤ rate2 C₁ := by simp only [rate2, Cwork]; omega
    simp only [Cm2]; omega
  · simp only [Cm2]; omega

/-! ## §4 状態の展開 -/

/-- ラウンド `n` 終了時の状態。 -/
def bstate2 (C₁ : ℕ) (w : List α) (S n : ℕ) : BState α := (borderMiddle2 α C₁).runToH w S n

theorem bstate2_init (C₁ : ℕ) {w : List α} {S n : ℕ} (h : n ≤ S / 2) :
    bstate2 C₁ w S n = ⟨S, 0, relTime S 1, [], 0, []⟩ :=
  MiddleImpl.runToH_init (borderMiddle2 α C₁) w S h

theorem bstate2_succ (C₁ : ℕ) {w : List α} {S n : ℕ} (h : ¬ (n + 1 ≤ S / 2)) :
    bstate2 C₁ w S (n + 1) = bstep2 C₁ (w.take (n + 1)) (n + 1) (bstate2 C₁ w S n) := by
  show (borderMiddle2 α C₁).runToH w S (n + 1) = _
  rw [MiddleImpl.runToH, if_neg h]
  rfl

/-! ## §5 不変条件 -/

theorem inv2_before (C₁ : ℕ) (w : List α) (S : ℕ) (hS : 8 ≤ S) :
    ∀ n, n < relTime S 1 →
      (bstate2 C₁ w S n).width = S ∧ (bstate2 C₁ w S n).idx = 0 ∧
        (bstate2 C₁ w S n).next = relTime S 1 := by
  intro n
  induction n with
  | zero => intro _; rw [bstate2_init (α := α) C₁ (Nat.zero_le _)]; exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    intro hn
    by_cases hle : n + 1 ≤ S / 2
    · rw [bstate2_init (α := α) C₁ hle]; exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨hw, hi, hx⟩ := ih (by omega)
      rw [bstate2_succ (α := α) C₁ hle]
      simp only [bstep2, hw, if_neg (show ¬ S < 8 by omega), hx]
      rw [if_neg (by omega : ¬ (n + 1 = relTime S 1 ∧ (bstate2 C₁ w S n).idx < numJobs))]
      exact ⟨rfl, hi, rfl⟩

theorem inv2_block (C₁ : ℕ) (w : List α) (S : ℕ) (hS : 8 ≤ S) :
    ∀ p, 1 ≤ p → p ≤ numJobs → ∀ i, (p < numJobs → i < gw S) →
      (bstate2 C₁ w S (relTime S p + i)).width = S ∧
      (bstate2 C₁ w S (relTime S p + i)).idx = p ∧
      (bstate2 C₁ w S (relTime S p + i)).next = relTime S (p + 1) ∧
      (bstate2 C₁ w S (relTime S p + i)).cur = Wnd w S p ∧
      (2 ≤ p → (bstate2 C₁ w S (relTime S p + i)).out = borderFlags2 (Wnd w S (p - 1))) := by
  have hg : 2 ≤ gw S := by simp only [gw]; omega
  intro p
  induction p with
  | zero => intro h; omega
  | succ p ih =>
    intro _ hple i
    induction i with
    | zero =>
      intro _
      have hpos : S / 2 < relTime S (p + 1) := relTime_gt (by omega) _
      obtain ⟨m, hm⟩ : ∃ m, relTime S (p + 1) = m + 1 := ⟨relTime S (p + 1) - 1, by omega⟩
      have hprev : (bstate2 C₁ w S m).width = S ∧ (bstate2 C₁ w S m).idx = p ∧
          (bstate2 C₁ w S m).next = relTime S (p + 1) ∧
          (1 ≤ p → (bstate2 C₁ w S m).cur = Wnd w S p) := by
        rcases Nat.eq_zero_or_pos p with rfl | hp
        · simp only [Nat.zero_add] at hm ⊢
          obtain ⟨a, b, c⟩ := inv2_before C₁ w S hS m (by omega)
          exact ⟨a, b, c, by omega⟩
        · have hrs := relTime_succ S p
          have hstep : relTime S p + (gw S - 1) = m := by omega
          have hb := ih hp (by simp only [numJobs] at hple ⊢; omega) (gw S - 1)
            (fun _ => by omega)
          rw [hstep] at hb
          exact ⟨hb.1, hb.2.1, hb.2.2.1, fun _ => hb.2.2.2.1⟩
      rw [Nat.add_zero, hm, bstate2_succ (α := α) C₁ (by omega)]
      simp only [bstep2, hprev.1, if_neg (show ¬ S < 8 by omega), hprev.2.2.1, hprev.2.1]
      rw [if_pos (show m + 1 = relTime S (p + 1) ∧ p < numJobs by
        simp only [numJobs] at hple ⊢; omega)]
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩
      · show m + 1 + gw S = relTime S (p + 1 + 1)
        have := relTime_succ S (p + 1)
        omega
      · show ((w.take (m + 1)).drop (S / 2)).take (S + (p + 1) * gw S) = Wnd w S (p + 1)
        rw [show m + 1 = relTime S (p + 1) from hm.symm]
        exact window_eq w S (p + 1)
      · intro h2
        show borderFlags2 (bstate2 C₁ w S m).cur = borderFlags2 (Wnd w S (p + 1 - 1))
        simp only [Nat.add_sub_cancel]
        exact congrArg borderFlags2 (hprev.2.2.2 (by omega))
    | succ i ih2 =>
      intro hi
      have h2 := ih2 (fun hlt => by have := hi hlt; omega)
      rw [show relTime S (p + 1) + (i + 1) = relTime S (p + 1) + i + 1 by omega,
        bstate2_succ (α := α) C₁
          (by have := relTime_gt (show 0 < S by omega) (p + 1); omega)]
      have hne : ¬ (relTime S (p + 1) + i + 1 = (bstate2 C₁ w S (relTime S (p + 1) + i)).next ∧
          (bstate2 C₁ w S (relTime S (p + 1) + i)).idx < numJobs) := by
        rw [h2.2.2.1, h2.2.1]
        rintro ⟨ha, hb⟩
        have h3 := hi hb
        have h4 := relTime_succ S (p + 1)
        omega
      simp only [bstep2, h2.1, if_neg (show ¬ S < 8 by omega), if_neg hne]
      exact ⟨trivial, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2⟩

/-! ## §6 フラグの読み出し -/

theorem bstate2_width (C₁ : ℕ) (w : List α) (S : ℕ) : ∀ n, (bstate2 C₁ w S n).width = S := by
  intro n
  induction n with
  | zero => rw [bstate2_init (α := α) C₁ (Nat.zero_le _)]
  | succ n ih =>
    by_cases hle : n + 1 ≤ S / 2
    · rw [bstate2_init (α := α) C₁ hle]
    · rw [bstate2_succ (α := α) C₁ hle]
      simp only [bstep2]
      split_ifs <;> simp only [] <;> exact ih

theorem borderFlags2_getD {y : List α} {L : ℕ} (h : L ≤ y.length) :
    (borderFlags2 y).getD L false = decide (IsPal (y.take L)) := by
  rw [List.getD_eq_getElem?_getD, borderFlags2,
    palPrefixFlagsGS_spec (by omega) (fun L hL _ => decOK2 y L hL) L h]
  rfl

theorem out2_small (C₁ : ℕ) (w : List α) (S n : ℕ) (hS : S < 8) (hn : S / 2 < n) :
    (bstate2 C₁ w S n).out = naiveFlags (((w.take n).drop (S / 2)).take (3 * S)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [bstate2_succ (α := α) C₁ (by omega)]
  simp only [bstep2, bstate2_width C₁ w S m, if_pos hS]

/-! ## §7 主定理 -/

theorem borderMiddle2_flag_correct (C₁ : ℕ) (w : List α) (S n : ℕ)
    (hS : 2 ≤ S) (hev : 2 * (S / 2) = S) (h1 : 2 * S ≤ n) (h2 : n < 4 * S)
    (hw : n ≤ w.length) :
    (borderMiddle2 α C₁).flag ((borderMiddle2 α C₁).runToH w S n) n
      = decide (IsPal ((w.drop (S / 2)).take (n - S))) := by
  have hflag : (borderMiddle2 α C₁).flag ((borderMiddle2 α C₁).runToH w S n) n
      = (bstate2 C₁ w S n).out.getD (n - S) false := by
    show (bstate2 C₁ w S n).out.getD (n - (bstate2 C₁ w S n).width) false = _
    rw [bstate2_width]
  rw [hflag]
  rcases Nat.lt_or_ge S 8 with hsmall | hbig
  · have hlen : n - S ≤ (((w.take n).drop (S / 2)).take (3 * S)).length := by
      rw [List.drop_take, List.take_take]
      simp only [List.length_take, List.length_drop]
      omega
    have hkey : (((w.take n).drop (S / 2)).take (3 * S)).take (n - S)
        = (w.drop (S / 2)).take (n - S) := by
      rw [List.drop_take, List.take_take, List.take_take]
      congr 1
      omega
    rw [out2_small C₁ w S n hsmall (by omega), naiveFlags_getD hlen, hkey]
    rfl
  · obtain ⟨p, i, hp2, hple, hn, hi, hcov⟩ := find_batch hbig hev h1 h2
    have hblk := inv2_block C₁ w S hbig p (by omega) hple i hi
    rw [← hn] at hblk
    have hlen : n - S ≤ (Wnd w S (p - 1)).length := by
      simp only [Wnd, List.length_take, List.length_drop]
      omega
    have hkey : (Wnd w S (p - 1)).take (n - S) = (w.drop (S / 2)).take (n - S) := by
      simp only [Wnd, List.take_take]
      congr 1
      omega
    rw [hblk.2.2.2.2 hp2, borderFlags2_getD hlen, hkey]

/-- **主定理**：`borderMiddle2` は半分割スケジュールの中央フラグ実装の仕様を満たす。
費用側の定数 `Cm2 C₁` は周期和の仮説の定数 `C₁` に依存する。 -/
theorem borderMiddle2_spec {C₁ : ℕ} (_hsum : PassPeriodSum 8 C₁) :
    MiddleImplSpecH (borderMiddle2 (Fin 2) C₁) (Cm2 C₁) where
  correct w S n hS hev h1 h2 hw := by
    rw [borderMiddle2_flag_correct C₁ w S n hS hev h1 h2 hw]
    exact decide_eq_true_iff
  cost_le := borderMiddle2_cost_le C₁

/-- **レートの妥当性**：一つのバッチの総仕事量は解放から次の解放までに使える
`rate2 C₁ * (gw S - 1)` に収まる。ここで `decompose2Work_le` を使う。 -/
theorem borderMiddle2_work_fits {C₁ : ℕ} (hsum : PassPeriodSum 8 C₁) (w : List (Fin 2))
    (S p : ℕ) (hS : 8 ≤ S) (hev : 2 * (S / 2) = S) (hp : p ≤ numJobs) :
    borderWork2 (Wnd w S p) ≤ rate2 C₁ * (gw S - 1) := by
  have hlen : (Wnd w S p).length ≤ 5 * S := by
    have h1 : p * gw S ≤ 13 * gw S :=
      Nat.mul_le_mul_right _ (by simp only [numJobs] at hp; omega)
    have h2 : 13 * gw S ≤ 4 * S := by simp only [gw]; omega
    simp only [Wnd, List.length_take, List.length_drop]
    omega
  have hw := borderWork2_le hsum (Wnd w S p)
  have hmul : (258 + Cwork C₁) * (Wnd w S p).length ≤ (258 + Cwork C₁) * (5 * S) :=
    Nat.mul_le_mul_left _ hlen
  have hS10 : S ≤ 10 * (gw S - 1) := by simp only [gw]; omega
  have hfin : (258 + Cwork C₁) * (5 * S) ≤ (258 + Cwork C₁) * (5 * (10 * (gw S - 1))) :=
    Nat.mul_le_mul_left _ (by omega)
  have heq : (258 + Cwork C₁) * (5 * (10 * (gw S - 1))) = rate2 C₁ * (gw S - 1) := by
    simp only [rate2]; ring
  omega

/-! ## §8 前処理実装 -/

/-- 1 ラウンドあたりの仕事量（`decompose2Work_le` の係数から）。 -/
def prepCp2 (k C₁ : ℕ) : ℕ := 2 * ((4 * k + 2) * C₁ + 17 * k + 50) + 2 * k + 6

/-- `decompose2` 前処理のラウンド実装。 -/
def prepDecompose2 (k C₁ : ℕ) : PrepImpl α where
  State := PrepDecompState α
  init S := ⟨S, [], 0, false⟩
  step t _ st :=
    if st.started then
      { st with rem := st.rem - prepCp2 k C₁ }
    else
      let x := (t.take (st.S / 2)).reverse
      ⟨st.S, x, decompose2Work x k - prepCp2 k C₁, true⟩
  result st := if st.started ∧ st.rem = 0 then decompose2 st.x k else (st.x.length, 0, 0)
  cost _ _ _ := prepCp2 k C₁

theorem prepDecompose2_runToH (k C₁ : ℕ) (w : List α) (S : ℕ) (hS : 2 ≤ S) :
    ∀ j : ℕ, 1 ≤ j → S / 2 + j ≤ S →
      (prepDecompose2 (α := α) k C₁).runToH w S (S / 2 + j) =
        ⟨S, (w.take (S / 2)).reverse,
          decompose2Work ((w.take (S / 2)).reverse) k - prepCp2 k C₁ * j, true⟩ := by
  have hhalf : 1 ≤ S / 2 := by omega
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro _ hle
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have hzero : S / 2 + (0 + 1) = (S / 2) + 1 := by omega
      rw [hzero]
      simp only [PrepImpl.runToH]
      rw [if_neg (show ¬ (S / 2 + 1 ≤ S / 2) by omega), if_pos (show S / 2 + 1 ≤ S by omega),
        PrepImpl.runToH_init (P := prepDecompose2 (α := α) k C₁) w S (le_refl _)]
      have htk : ((w.take (S / 2 + 1)).take (S / 2)) = w.take (S / 2) := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
      simp [prepDecompose2, htk]
    · have := ih (by omega) (by omega)
      have harr : S / 2 + (j + 1) = (S / 2 + j) + 1 := by omega
      rw [harr]
      simp only [PrepImpl.runToH]
      rw [if_neg (show ¬ ((S / 2 + j) + 1 ≤ S / 2) by omega),
        if_pos (show (S / 2 + j) + 1 ≤ S by omega), this]
      have harith : decompose2Work ((w.take (S / 2)).reverse) k - prepCp2 k C₁ * j
            - prepCp2 k C₁
          = decompose2Work ((w.take (S / 2)).reverse) k - prepCp2 k C₁ * (j + 1) := by
        rw [Nat.mul_succ]; omega
      simp [prepDecompose2, harith]

/-- 予算が足りる（`decompose2Work_le` を使う唯一の箇所）。 -/
theorem decompose2Work_le_prepCp2 {k C₁ : ℕ} (hk : 4 ≤ k) (hsum : PassPeriodSum k C₁)
    (x : List (Fin 2)) (m : ℕ) (hlen : x.length = m) (hm : 1 ≤ m) :
    decompose2Work x k ≤ prepCp2 k C₁ * m := by
  have h := decompose2Work_le x k C₁ hk (fun b s => hsum x b s)
  rw [hlen] at h
  set C := (4 * k + 2) * C₁ + 17 * k + 50 with hC
  have hstep : prepCp2 k C₁ * m = C * m + (C + 2 * k + 6) * m := by
    simp only [prepCp2, hC]; ring
  have h2 : (2 * k + 5) ≤ (C + 2 * k + 6) * m :=
    le_trans (by omega) (Nat.le_mul_of_pos_right _ hm)
  omega

theorem prepDecompose2_runToH_done {k C₁ : ℕ} (hk : 4 ≤ k) (hsum : PassPeriodSum k C₁)
    (w : List (Fin 2)) (S : ℕ) (hS : 2 ≤ S) (hw : 2 * S ≤ w.length) :
    (prepDecompose2 (α := Fin 2) k C₁).runToH w S S =
      ⟨S, (w.take (S / 2)).reverse, 0, true⟩ := by
  have hhalf : 1 ≤ S / 2 := by omega
  have hj : S / 2 + (S - S / 2) = S := by omega
  have hrun := prepDecompose2_runToH (α := Fin 2) k C₁ w S hS (S - S / 2) (by omega) (by omega)
  rw [hj] at hrun
  rw [hrun]
  have hlen : ((w.take (S / 2)).reverse).length = S / 2 := by
    simp [List.length_take, Nat.min_eq_left (show S / 2 ≤ w.length by omega)]
  have hbudget := decompose2Work_le_prepCp2 hk hsum ((w.take (S / 2)).reverse) (S / 2)
    hlen hhalf
  have : decompose2Work ((w.take (S / 2)).reverse) k - prepCp2 k C₁ * (S - S / 2) = 0 := by
    have : prepCp2 k C₁ * (S / 2) ≤ prepCp2 k C₁ * (S - S / 2) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  rw [this]

/-- **主定理**：正当性は `decompose2_gsDecomp`（無条件）、費用は周期和の仮説から。 -/
theorem prepDecompose2_spec {k C₁ : ℕ} (hk : 4 ≤ k) (hsum : PassPeriodSum k C₁) :
    PrepImplSpecH (prepDecompose2 (α := Fin 2) k C₁) k (prepCp2 k C₁) where
  correct := by
    intro w S hS hw
    have hhalf : 1 ≤ S / 2 := by omega
    have hrun := prepDecompose2_runToH_done hk hsum w S hS hw
    have hres : (prepDecompose2 (α := Fin 2) k C₁).result
        ((prepDecompose2 (α := Fin 2) k C₁).runToH w S S)
        = decompose2 ((w.take (S / 2)).reverse) k := by
      rw [hrun]
      simp [prepDecompose2]
    have hlen : ((w.take (S / 2)).reverse).length = S / 2 := by
      simp [List.length_take, Nat.min_eq_left (show S / 2 ≤ w.length by omega)]
    have hne : (w.take (S / 2)).reverse ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen; omega
    have H := decompose2_gsDecomp hk ((w.take (S / 2)).reverse)
    rw [hres]
    refine ⟨H, ?_⟩
    have hcut := H.cut_bound hne
    rw [hlen] at hcut
    have : (decompose2 ((w.take (S / 2)).reverse) k).1
        ≤ (k - 1) * (decompose2 ((w.take (S / 2)).reverse) k).1 :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  cost_le := by intro t n st; exact le_refl _

/-! ## §9 端から端まで -/

/-- **端から端まで（正当性）**。仮定は周期和 `hsum` ただ一つ。 -/
theorem endToEnd2_correct {C₁ : ℕ} (hsum : PassPeriodSum 8 C₁) (w : List (Fin 2)) (n : ℕ)
    (hn : n ≤ w.length) :
    outputH (borderMiddle2 (Fin 2) C₁) (prepDecompose2 8 C₁) (w.take n) n
        (fullStateH (borderMiddle2 (Fin 2) C₁) (prepDecompose2 8 C₁) 8 w n) = true
      ↔ IsPal (w.take n) :=
  output_correctH (borderMiddle2 (Fin 2) C₁) (prepDecompose2 8 C₁) 8 w
    (borderMiddle2_spec hsum) (prepDecompose2_spec (by omega) hsum) (by omega) hn

/-- **端から端まで（`PAL` の判定）**。 -/
theorem endToEnd2_mem_PAL {C₁ : ℕ} (hsum : PassPeriodSum 8 C₁) (w : List (Fin 2)) :
    outputH (borderMiddle2 (Fin 2) C₁) (prepDecompose2 8 C₁) (w.take w.length) w.length
        (fullStateH (borderMiddle2 (Fin 2) C₁) (prepDecompose2 8 C₁) 8 w w.length) = true
      ↔ w ∈ PAL :=
  output_mem_PALH (borderMiddle2_spec hsum) (prepDecompose2_spec (by omega) hsum) (by omega)

/-- **端から端まで（1 ラウンドの費用）**。 -/
theorem endToEnd2_round_cost {C₁ : ℕ} (hsum : PassPeriodSum 8 C₁) (w : List (Fin 2)) (n : ℕ) :
    roundCostH (borderMiddle2 (Fin 2) C₁) (prepDecompose2 8 C₁) 8 w n
      ≤ 3 * (gsRateInterleaved 8 + Cm2 C₁ + prepCp2 8 C₁) :=
  round_cost_leH (borderMiddle2 (Fin 2) C₁) (prepDecompose2 8 C₁) 8 w
    (borderMiddle2_spec hsum) (prepDecompose2_spec (by omega) hsum) n

end EndToEnd2
end PalPeg

section Audit
open PalPeg.EndToEnd2
end Audit
