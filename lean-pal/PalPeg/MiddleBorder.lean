import PalPeg.BorderJob
import PalPeg.GSPreprocess
import PalPeg.OnlineMachine

/-!
# 中央フラグを境界ジョブ（GS）で供給するラウンド実装

`PalPeg.MiddleJob` は Manacher 版の中央ジョブを扱った。本ファイルはその
**GS（Galil–Seiferas）版**、すなわち数値配列を持たない `PalPeg.BorderJob` を
凍結窓の上で回す版を、`PalPeg.MiddleImpl` のラウンド実装として与える。
-/

namespace PalPeg
namespace MiddleBorder

variable {α : Type} [DecidableEq α]

/-! ## §1 一つの凍結窓に対する仕事 -/

/-- 窓 `y` の段 `L` に与える分解：`decompose (y.take L) k`。 -/
def gsDec (y : List α) (k : ℕ) : ℕ → ℕ × ℕ × ℕ := fun L => decompose (y.take L) k

/-- 窓 `y` の回文接頭辞フラグ（`ℓ = 0 .. |y|`）。 -/
def borderFlags (y : List α) : List Bool := palPrefixFlagsGS y (gsDec y 8) 8

/-- 素朴なフラグ（`S < 8` の退化した段でだけ使う。長さが定数なので費用も定数）。 -/
def naiveFlags (y : List α) : List Bool :=
  (List.range (y.length + 1)).map (fun L => decide (IsPal (y.take L)))

/-- 各段のパターン `y.take L` に対する GS 前処理の費用の総和。 -/
def decompTotal (y : List α) (dec : ℕ → ℕ × ℕ × ℕ) (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, L =>
      if L = 0 then 0
      else decomposeWork (y.take L) k + decompTotal y dec k fuel (nextLen (dec L).1)

/-- 窓 `y` を処理する総仕事量：境界ジョブの走査 ＋ 各段の前処理。 -/
def borderWork (y : List α) : ℕ :=
  totalSteps y (gsDec y 8) 8 + decompTotal y (gsDec y 8) 8 (y.length + 1) y.length

/-- 各段の分解が `StageOK`（L1 を含む）を満たすという仮定。
`GSDecompL1` が与えるべき形をそのまま外から受け取る。 -/
def DecOK (α : Type) [DecidableEq α] : Prop :=
  ∀ (y : List α) (L : ℕ), 1 ≤ L →
    StageOK y 8 L (gsDec y 8 L).1 (gsDec y 8 L).2.1 (gsDec y 8 L).2.2

theorem decompTotal_le (hOK : DecOK α) (y : List α) :
    ∀ (fuel L : ℕ), decompTotal y (gsDec y 8) 8 fuel L ≤ 300 * L := by
  intro fuel
  induction fuel with
  | zero => intro L; simp [decompTotal]
  | succ fuel ih =>
    intro L
    simp only [decompTotal]
    split_ifs with h0
    · exact Nat.zero_le _
    · have hw : decomposeWork (y.take L) 8 ≤ 166 * (y.take L).length + 21 := by
        have := decomposeWork_le (y.take L) 8 (by omega)
        simpa using this
      have hlen : (y.take L).length ≤ L := by simp [List.length_take]
      have hshort := (hOK y L (by omega)).cut_short
      have hshrink : 3 * nextLen (gsDec y 8 L).1 + 1 ≤ L := nextLen_shrink (by omega)
      have hrec := ih (nextLen (gsDec y 8 L).1)
      have h100 : 300 * nextLen (gsDec y 8 L).1 ≤ 100 * (L - 1) := by
        have : 100 * (3 * nextLen (gsDec y 8 L).1) ≤ 100 * (L - 1) :=
          Nat.mul_le_mul (Nat.le_refl _) (by omega)
        omega
      have h166 : 166 * (y.take L).length ≤ 166 * L := Nat.mul_le_mul (Nat.le_refl _) hlen
      omega

theorem borderWork_le (hOK : DecOK α) (y : List α) : borderWork y ≤ 558 * y.length := by
  have h1 : totalSteps y (gsDec y 8) 8 ≤ 258 * y.length :=
    palPrefixFlagsGS_work (fun L hL _ => hOK y L hL)
  have h2 := decompTotal_le hOK y (y.length + 1) y.length
  simp only [borderWork]
  omega

/-! ## §2 ラウンド実装 -/

/-- サービスレート（1 ラウンドあたりに進める仕事の単位数）。 -/
def rate : ℕ := 27900

/-- 1 ラウンドの費用上界。 -/
def Cm : ℕ := rate + 1

/-- サブジョブの本数（実バッチ `1..12` ＋ 最後の掃き出し `13`）。 -/
def numJobs : ℕ := 13

/-- 段幅 `S` におけるバッチ幅 `g = ⌊S/4⌋`。 -/
def gw (S : ℕ) : ℕ := S / 4

/-- バッチ `j` の解放ラウンド `r j = S/2 + S + j*g`。 -/
def relTime (S j : ℕ) : ℕ := S / 2 + S + j * gw S

/-- 実装の内部状態。 -/
structure BState (α : Type) where
  /-- 段幅 `S`。 -/
  width : ℕ
  /-- これまでに解放されたバッチ数。 -/
  idx : ℕ
  /-- 次の解放ラウンド。 -/
  next : ℕ
  /-- いま挽いている凍結窓。 -/
  cur : List α
  /-- 残りの仕事量。 -/
  rem : ℕ
  /-- 直前に完了したバッチのフラグ列。 -/
  out : List Bool

/-- 状態遷移。 -/
def bstep (t : List α) (n : ℕ) (st : BState α) : BState α :=
  if st.width < 8 then
    { st with out := naiveFlags ((t.drop (st.width / 2)).take (3 * st.width)) }
  else if n = st.next ∧ st.idx < numJobs then
    let j := st.idx + 1
    let win := (t.drop (st.width / 2)).take (st.width + j * gw st.width)
    { width := st.width, idx := j, next := n + gw st.width, cur := win,
      rem := borderWork win, out := borderFlags st.cur }
  else
    { st with rem := st.rem - rate }

/-- **境界ジョブ版の中央フラグ実装**。 -/
def borderMiddle (α : Type) [DecidableEq α] : MiddleImpl α where
  State := BState α
  init S := ⟨S, 0, relTime S 1, [], 0, []⟩
  step := bstep
  flag st n := st.out.getD (n - st.width) false
  cost _ _ st := if st.width < 8 then 3 * st.width * st.width + 1 else min st.rem rate + 1

@[simp] theorem borderMiddle_State : (borderMiddle α).State = BState α := rfl

theorem borderMiddle_cost_le (t : List α) (n : ℕ) (st : BState α) :
    (borderMiddle α).cost t n st ≤ Cm := by
  show (if st.width < 8 then 3 * st.width * st.width + 1 else min st.rem rate + 1) ≤ Cm
  split_ifs with h
  · have : 3 * st.width * st.width ≤ 3 * 7 * 7 := by
      have h1 : st.width ≤ 7 := by omega
      calc 3 * st.width * st.width ≤ 3 * 7 * st.width :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 h1)
        _ ≤ 3 * 7 * 7 := Nat.mul_le_mul_left _ h1
    simp only [Cm, rate]; omega
  · simp only [Cm]; omega

/-! ## §3 状態の展開 -/

/-- ラウンド `n` 終了時の状態。 -/
def bstate (w : List α) (S n : ℕ) : BState α := (borderMiddle α).runToH w S n

theorem bstate_init {w : List α} {S n : ℕ} (h : n ≤ S / 2) :
    bstate w S n = ⟨S, 0, relTime S 1, [], 0, []⟩ :=
  MiddleImpl.runToH_init (borderMiddle α) w S h

theorem bstate_succ {w : List α} {S n : ℕ} (h : ¬ (n + 1 ≤ S / 2)) :
    bstate w S (n + 1) = bstep (w.take (n + 1)) (n + 1) (bstate w S n) := by
  show (borderMiddle α).runToH w S (n + 1) = _
  rw [MiddleImpl.runToH, if_neg h]
  rfl

/-- バッチ `j` の凍結窓。 -/
def Wnd (w : List α) (S j : ℕ) : List α := (w.drop (S / 2)).take (S + j * gw S)

omit [DecidableEq α] in
theorem window_eq (w : List α) (S j : ℕ) :
    ((w.take (relTime S j)).drop (S / 2)).take (S + j * gw S) = Wnd w S j := by
  rw [List.drop_take]
  simp only [Wnd, relTime, List.take_take]
  congr 1
  omega

omit [DecidableEq α] in
theorem relTime_succ (S q : ℕ) : relTime S (q + 1) = relTime S q + gw S := by
  simp only [relTime, add_mul, one_mul]; omega

omit [DecidableEq α] in
theorem relTime_gt {S : ℕ} (hS : 0 < S) (p : ℕ) : S / 2 < relTime S p := by
  have h := Nat.zero_le (p * gw S)
  simp only [relTime]
  omega

/-! ## §4 不変条件 -/

/-- 最初の解放より前は初期状態のまま。 -/
theorem inv_before (w : List α) (S : ℕ) (hS : 8 ≤ S) :
    ∀ n, n < relTime S 1 →
      (bstate w S n).width = S ∧ (bstate w S n).idx = 0 ∧ (bstate w S n).next = relTime S 1 := by
  intro n
  induction n with
  | zero => intro _; rw [bstate_init (Nat.zero_le _)]; exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    intro hn
    by_cases hle : n + 1 ≤ S / 2
    · rw [bstate_init hle]; exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨hw, hi, hx⟩ := ih (by omega)
      rw [bstate_succ hle]
      simp only [bstep, hw, if_neg (show ¬ S < 8 by omega), hx]
      rw [if_neg (by omega : ¬ (n + 1 = relTime S 1 ∧ (bstate w S n).idx < numJobs))]
      exact ⟨rfl, hi, rfl⟩

/-- **ブロック不変条件**：バッチ `p` が解放されてから次の解放までの間、
状態は「窓 `Wnd w S p` を挽きつつ、直前のバッチ `p-1` のフラグを保持している」。 -/
theorem inv_block (w : List α) (S : ℕ) (hS : 8 ≤ S) :
    ∀ p, 1 ≤ p → p ≤ numJobs → ∀ i, (p < numJobs → i < gw S) →
      (bstate w S (relTime S p + i)).width = S ∧
      (bstate w S (relTime S p + i)).idx = p ∧
      (bstate w S (relTime S p + i)).next = relTime S (p + 1) ∧
      (bstate w S (relTime S p + i)).cur = Wnd w S p ∧
      (2 ≤ p → (bstate w S (relTime S p + i)).out = borderFlags (Wnd w S (p - 1))) := by
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
      have hprev : (bstate w S m).width = S ∧ (bstate w S m).idx = p ∧
          (bstate w S m).next = relTime S (p + 1) ∧
          (1 ≤ p → (bstate w S m).cur = Wnd w S p) := by
        rcases Nat.eq_zero_or_pos p with rfl | hp
        · simp only [Nat.zero_add] at hm ⊢
          obtain ⟨a, b, c⟩ := inv_before w S hS m (by omega)
          exact ⟨a, b, c, by omega⟩
        · have hrs := relTime_succ S p
          have hstep : relTime S p + (gw S - 1) = m := by omega
          have hb := ih hp (by simp only [numJobs] at hple ⊢; omega) (gw S - 1) (fun _ => by omega)
          rw [hstep] at hb
          exact ⟨hb.1, hb.2.1, hb.2.2.1, fun _ => hb.2.2.2.1⟩
      rw [Nat.add_zero, hm, bstate_succ (by omega)]
      simp only [bstep, hprev.1, if_neg (show ¬ S < 8 by omega), hprev.2.2.1, hprev.2.1]
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
        show borderFlags (bstate w S m).cur = borderFlags (Wnd w S (p + 1 - 1))
        simp only [Nat.add_sub_cancel]
        exact congrArg borderFlags (hprev.2.2.2 (by omega))
    | succ i ih2 =>
      intro hi
      have h2 := ih2 (fun hlt => by have := hi hlt; omega)
      rw [show relTime S (p + 1) + (i + 1) = relTime S (p + 1) + i + 1 by omega,
        bstate_succ (by have := relTime_gt (show 0 < S by omega) (p + 1); omega)]
      have hne : ¬ (relTime S (p + 1) + i + 1 = (bstate w S (relTime S (p + 1) + i)).next ∧
          (bstate w S (relTime S (p + 1) + i)).idx < numJobs) := by
        rw [h2.2.2.1, h2.2.1]
        rintro ⟨ha, hb⟩
        have h3 := hi hb
        have h4 := relTime_succ S (p + 1)
        omega
      simp only [bstep, h2.1, if_neg (show ¬ S < 8 by omega), if_neg hne]
      exact ⟨trivial, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2⟩

/-! ## §5 フラグの読み出し -/

theorem bstate_width (w : List α) (S : ℕ) : ∀ n, (bstate w S n).width = S := by
  intro n
  induction n with
  | zero => rw [bstate_init (Nat.zero_le _)]
  | succ n ih =>
    by_cases hle : n + 1 ≤ S / 2
    · rw [bstate_init hle]
    · rw [bstate_succ hle]
      simp only [bstep]
      split_ifs <;> simp only [] <;> exact ih

theorem naiveFlags_getD {y : List α} {L : ℕ} (h : L ≤ y.length) :
    (naiveFlags y).getD L false = decide (IsPal (y.take L)) := by
  rw [List.getD_eq_getElem?_getD]
  simp only [naiveFlags, List.getElem?_map,
    List.getElem?_range (show L < y.length + 1 by omega)]
  rfl

theorem borderFlags_getD (hOK : DecOK α) {y : List α} {L : ℕ} (h : L ≤ y.length) :
    (borderFlags y).getD L false = decide (IsPal (y.take L)) := by
  rw [List.getD_eq_getElem?_getD, borderFlags,
    palPrefixFlagsGS_spec (by omega) (fun L hL _ => hOK y L hL) L h]
  rfl

/-- 退化した段（`S < 8`）では毎ラウンド直接計算する。 -/
theorem out_small (w : List α) (S n : ℕ) (hS : S < 8) (hn : S / 2 < n) :
    (bstate w S n).out = naiveFlags (((w.take n).drop (S / 2)).take (3 * S)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [bstate_succ (by omega)]
  simp only [bstep, bstate_width w S m, if_pos hS]

/-- 消費ラウンド `n` を担当するバッチの添字を取り出す。 -/
theorem find_batch {S n : ℕ} (hS : 8 ≤ S) (hev : 2 * (S / 2) = S) (h1 : 2 * S ≤ n)
    (h2 : n < 4 * S) :
    ∃ p i, 2 ≤ p ∧ p ≤ numJobs ∧ n = relTime S p + i ∧ (p < numJobs → i < gw S) ∧
      n - S ≤ S + (p - 1) * gw S := by
  have hg : 2 ≤ gw S := by simp only [gw]; omega
  have h2g : 2 * gw S ≤ S / 2 := by simp only [gw]; omega
  have h12g : 3 * S ≤ 12 * gw S + 6 := by simp only [gw]; omega
  set g := gw S with hgdef
  set d := n - (S / 2 + S) with hddef
  have hdn : n = S / 2 + S + d := by omega
  obtain ⟨q, i, hqi, hilt⟩ : ∃ q i, d = q * g + i ∧ i < g := by
    refine ⟨d / g, d % g, ?_, Nat.mod_lt _ (by omega)⟩
    rw [Nat.mul_comm]; exact (Nat.div_add_mod d g).symm
  have hq2 : 2 ≤ q := by
    by_contra hc
    have : q * g ≤ 1 * g := Nat.mul_le_mul_right g (by omega)
    omega
  have hq1g : (q - 1) * g + g = q * g := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel, add_mul, one_mul]
  rcases Nat.lt_or_ge q numJobs with hlt | hge
  · refine ⟨q, i, hq2, by omega, ?_, fun _ => hilt, ?_⟩
    · simp only [relTime, ← hgdef]; omega
    · omega
  · have h13 : 13 * g ≤ q * g := Nat.mul_le_mul_right g (by simp only [numJobs] at hge; omega)
    refine ⟨numJobs, n - relTime S numJobs, by simp only [numJobs]; omega, le_rfl, ?_,
      fun hc => by simp only [numJobs] at hc; omega, ?_⟩
    · have : relTime S numJobs ≤ n := by simp only [relTime, numJobs, ← hgdef]; omega
      omega
    · simp only [numJobs]
      omega

/-! ## §6 主定理 -/

/-- **フラグの正当性**：ラウンド `n ∈ [2S, 4S)` に読まれるフラグは
中央部 `(w.drop (S/2)).take (n - S)` の回文性に一致する。 -/
theorem borderMiddle_flag_correct (hOK : DecOK α) (w : List α) (S n : ℕ)
    (hS : 2 ≤ S) (hev : 2 * (S / 2) = S) (h1 : 2 * S ≤ n) (h2 : n < 4 * S)
    (hw : n ≤ w.length) :
    (borderMiddle α).flag ((borderMiddle α).runToH w S n) n
      = decide (IsPal ((w.drop (S / 2)).take (n - S))) := by
  have hflag : (borderMiddle α).flag ((borderMiddle α).runToH w S n) n
      = (bstate w S n).out.getD (n - S) false := by
    show (bstate w S n).out.getD (n - (bstate w S n).width) false = _
    rw [bstate_width]
  rw [hflag]
  rcases Nat.lt_or_ge S 8 with hsmall | hbig
  · -- 退化した段：素朴な直接計算
    have hlen : n - S ≤ (((w.take n).drop (S / 2)).take (3 * S)).length := by
      rw [List.drop_take, List.take_take]
      simp only [List.length_take, List.length_drop]
      omega
    have hkey : (((w.take n).drop (S / 2)).take (3 * S)).take (n - S)
        = (w.drop (S / 2)).take (n - S) := by
      rw [List.drop_take, List.take_take, List.take_take]
      congr 1
      omega
    rw [out_small w S n hsmall (by omega), naiveFlags_getD hlen, hkey]
  · obtain ⟨p, i, hp2, hple, hn, hi, hcov⟩ := find_batch hbig hev h1 h2
    have hblk := inv_block w S hbig p (by omega) hple i hi
    rw [← hn] at hblk
    have hlen : n - S ≤ (Wnd w S (p - 1)).length := by
      simp only [Wnd, List.length_take, List.length_drop]
      omega
    have hkey : (Wnd w S (p - 1)).take (n - S) = (w.drop (S / 2)).take (n - S) := by
      simp only [Wnd, List.take_take]
      congr 1
      omega
    rw [hblk.2.2.2.2 hp2, borderFlags_getD hOK hlen, hkey]

/-- **主定理**：`borderMiddle` は半分割スケジュールの中央フラグ実装の仕様を満たす。 -/
theorem borderMiddle_spec (hOK : DecOK α) : MiddleImplSpecH (borderMiddle α) Cm where
  correct w S n hS hev h1 h2 hw := by
    rw [borderMiddle_flag_correct hOK w S n hS hev h1 h2 hw]
    exact decide_eq_true_iff
  cost_le := borderMiddle_cost_le

/-! ## §7 レートと締切（`Cm` が本当に足りていること） -/

/-- **締切**：バッチ `p` の凍結窓は解放 `relTime S p` から `gw S` ラウンド後、すなわち
`relTime S (p+1)` に `out` へ移る。この時刻は、そのバッチの最初のフラグが必要になる
時刻 `2*S + (p-1)*gw S`（＝長さ `L = S + (p-1)*gw S` の中央部の判定）以下である。 -/
theorem borderMiddle_deadline {S p : ℕ} (_hS : 8 ≤ S) (hev : 2 * (S / 2) = S) (hp : 1 ≤ p) :
    relTime S (p + 1) ≤ 2 * S + (p - 1) * gw S := by
  have hq1g : (p - 1) * gw S + gw S = p * gw S := by
    obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel, add_mul, one_mul]
  have h2g : 2 * gw S ≤ S / 2 := by simp only [gw]; omega
  have hrs := relTime_succ S p
  simp only [relTime] at hrs ⊢
  omega

/-- **レートの妥当性**：一つのバッチの総仕事量（境界ジョブの走査 ＋ 各段の GS 前処理）は
解放から次の解放までに使える `gw S - 1` ラウンド分の仕事 `rate * (gw S - 1)` に収まる。 -/
theorem borderMiddle_work_fits (hOK : DecOK α) (w : List α) (S p : ℕ) (hS : 8 ≤ S)
    (hev : 2 * (S / 2) = S) (hp : p ≤ numJobs) :
    borderWork (Wnd w S p) ≤ rate * (gw S - 1) := by
  have hlen : (Wnd w S p).length ≤ 5 * S := by
    have h1 : p * gw S ≤ 13 * gw S :=
      Nat.mul_le_mul_right _ (by simp only [numJobs] at hp; omega)
    have h2 : 13 * gw S ≤ 4 * S := by simp only [gw]; omega
    simp only [Wnd, List.length_take, List.length_drop]
    omega
  have hw := borderWork_le hOK (Wnd w S p)
  have hmul : 558 * (Wnd w S p).length ≤ 558 * (5 * S) := Nat.mul_le_mul_left _ hlen
  have hS10 : S ≤ 10 * (gw S - 1) := by simp only [gw]; omega
  have hfin : 2790 * S ≤ 2790 * (10 * (gw S - 1)) := Nat.mul_le_mul_left _ hS10
  simp only [rate]
  omega

end MiddleBorder
end PalPeg
