import PalPeg.TextFeedBacklog

/-! A fixed worker rate can pay for finite preprocessing before the first
possible scanner report. The rate depends on implementation constants,
never on the input word, pattern length, or future text length. -/
set_option autoImplicit false

namespace PalPeg.TextFeedStartupBudget

def slope (rate : ℕ) : ℕ := GSPreProg.preprocessSlope + 25 + 7 * rate
def offset (rate : ℕ) : ℕ := GSPreProg.preprocessOffset + 37 + 11 * rate

def startupRate (rate : ℕ) : ℕ :=
  max (TextFeedRefine.workRate rate) (4 * (slope rate + offset rate + 2))

theorem startupRate_work (rate : ℕ) : TextFeedRefine.workRate rate ≤ startupRate rate :=
  Nat.le_max_left _ _

theorem startupRate_pos (rate : ℕ) : 0 < startupRate rate := by
  have h := Nat.le_max_right (TextFeedRefine.workRate rate) (4 * (slope rate + offset rate + 2))
  change 4 * (slope rate + offset rate + 2) ≤ startupRate rate at h
  omega

/-- The +1 is the first ordinary worker call that normalizes the source
endpoint. Enqueue uses its own reserved call and does not reduce R. -/
theorem prep_calls_fit {rate L cost : ℕ} (hL : 4 ≤ L)
    (hc : cost ≤ slope rate * L + offset rate) :
    cost + 1 ≤ startupRate rate * (L / 2) := by
  have hR : 4 * (slope rate + offset rate + 2) ≤ startupRate rate := Nat.le_max_right _ _
  have hd : 1 ≤ L / 2 := by omega
  have hl : L ≤ 4 * (L / 2) := by omega
  have hA := Nat.mul_le_mul_left (slope rate) hl
  have hB := Nat.mul_le_mul_left (offset rate + 1) hd
  have hr := Nat.mul_le_mul_right (L / 2) hR
  nlinarith

/-- The least number of R-call windows needed for prep and handoff. -/
def frames (rate cost : ℕ) : ℕ := (cost + startupRate rate) / startupRate rate

theorem frames_of_split {rate cost q J : ℕ}
    (h : q * startupRate rate + J = cost) (hJ : J < startupRate rate) :
    frames rate cost = q + 1 := by
  apply Nat.div_eq_of_lt_le <;> nlinarith

theorem frames_half {rate L cost : ℕ} (hL : 4 ≤ L)
    (hc : cost ≤ slope rate * L + offset rate) : frames rate cost ≤ L / 2 := by
  have hh := prep_calls_fit hL hc
  have hlt : cost + startupRate rate < (L / 2 + 1) * startupRate rate := by nlinarith
  have hd := (Nat.div_lt_iff_lt_mul (startupRate_pos rate)).mpr hlt
  change frames rate cost < L / 2 + 1 at hd
  omega

/-- The GS split satisfies 7*cut<L, so half of the original pattern
length is comfortably within the scanner's initial credit reserve. -/
theorem half_credit {rate L cut n : ℕ} (hk : 2 ≤ rate)
    (hc : 7 * cut < L) (hn : n ≤ L / 2) :
    (rate + 1) * n ≤ rate * (L - cut) := by
  have hv : cut ≤ L := by omega
  have hnv : n ≤ L - cut := by omega
  have hthree : 3 * n ≤ 2 * (L - cut) := by omega
  have hd : n + ((L - cut) - n) = L - cut := by omega
  have hm := Nat.mul_le_mul_right ((L - cut) - n) hk
  nlinarith

theorem frames_credit {rate L cost cut : ℕ} (hk : 2 ≤ rate) (hL : 4 ≤ L)
    (hc : cost ≤ slope rate * L + offset rate) (hcut : 7 * cut < L) :
    (rate + 1) * frames rate cost ≤ rate * (L - cut) :=
  half_credit hk hcut (frames_half hL hc)

/-- info: 'PalPeg.TextFeedStartupBudget.frames_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frames_credit

end PalPeg.TextFeedStartupBudget
