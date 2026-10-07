import Complexity.Univ.Sim

/-!
# One tape for `k`: the codes of columns and of control states

The one-tape simulator of a `k`-tape machine `M` keeps on its single tape one *column* per cell: the `k` symbols of
`M`'s tapes at that index, a flag per tape saying whether that head is there, and a *left bit* marking cell `0`.

* A column is a list of `k` digits in base `base M = 2·na`; digit `i` is `2·symbol + flag` of tape `i`.
* The symbols `0`, `1`, `2` (blank and the input bits) stand for the column with that symbol on tape `0`, blanks
  elsewhere, no flags and no left bit (`cdig_raw`), so the input needs no conversion except at cell `0`.
* Every other column is written as `cenc ds l = 3 + l + 2·rcode ds` (`cdigits_cenc`, `clft_cenc`).

A control state of the simulator is a record `Ctl` (phase, tape index, `M`'s state, the symbols read so far), coded
by mixed radix as `enc` and read back by `dec` (`dec_enc`); all codes are at least `3`, so they never clash with the
accepting, rejecting and starting states `0`, `1`, `2`.
-/

namespace Complexity
namespace OneTape

variable {k : Nat} (M : TM k)

/-! ## Columns -/

/-- The base of the digits of a column: a digit is `2·symbol + flag`. -/
def base : Nat := 2 * M.na

theorem six_le_base : 6 ≤ base M := by have := M.three_le_na; unfold base; omega

/-- The digits of the column that the tape symbol `a` stands for. -/
def cdigits (a : Nat) : List Nat :=
  if a < 3 then List.ofFn (fun i : Fin k => if i.val = 0 then 2 * a else 0)
  else digits (base M) k ((a - 3) / 2)

/-- Digit `i` of the column of `a`. -/
def cdig (a i : Nat) : Nat := (cdigits M a).getD i 0

/-- The left bit of the column of `a`. -/
def clft (a : Nat) : Bool := decide (3 ≤ a ∧ (a - 3) % 2 = 1)

/-- The tape symbol of the column with digits `ds` and left bit `l`. -/
def cenc (ds : List Nat) (l : Bool) : Nat := 3 + (if l then 1 else 0) + 2 * rcode (base M) ds

/-- The number of tape symbols of the simulator. -/
def NA : Nat := 3 + 2 * base M ^ k

theorem cdigits_length (a : Nat) : (cdigits M a).length = k := by
  unfold cdigits; split
  · simp
  · exact length_digits _ _ _

theorem cdigits_lt (a : Nat) : ∀ d ∈ cdigits M a, d < base M := by
  have h6 := six_le_base M
  unfold cdigits; split
  · intro d hd
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hd
    split <;> omega
  · exact digits_lt (by omega) _ _

theorem cdig_lt (a i : Nat) : cdig M a i < base M := by
  have h6 := six_le_base M
  unfold cdig
  rw [List.getD_eq_getElem?_getD]
  cases h : (cdigits M a)[i]? with
  | none => simp; omega
  | some d => exact cdigits_lt M a d (List.mem_of_getElem? h)

/-- The digits of a raw symbol (blank or input bit). -/
theorem cdig_raw {a : Nat} (ha : a < 3) (i : Fin k) : cdig M a i.val = if i.val = 0 then 2 * a else 0 := by
  simp [cdig, cdigits, ha, List.getD_eq_getElem?_getD]

theorem clft_raw {a : Nat} (ha : a < 3) : clft a = false := by
  simp [clft]; omega

theorem cdigits_cenc {ds : List Nat} (hl : ds.length = k) (hd : ∀ d ∈ ds, d < base M) (l : Bool) :
    cdigits M (cenc M ds l) = ds := by
  unfold cdigits cenc
  rw [if_neg (by omega)]
  have : (3 + (if l then 1 else 0) + 2 * rcode (base M) ds - 3) / 2 = rcode (base M) ds := by
    cases l <;> simp <;> omega
  rw [this]
  have e := digits_rcode hd
  rw [hl] at e
  exact e

theorem clft_cenc (ds : List Nat) (l : Bool) : clft (cenc M ds l) = l := by
  unfold clft cenc
  cases l <;> simp <;> omega

theorem cenc_lt {ds : List Nat} (hl : ds.length = k) (hd : ∀ d ∈ ds, d < base M) (l : Bool) :
    cenc M ds l < NA M := by
  have h := rcode_lt hd
  rw [hl] at h
  unfold cenc NA
  cases l <;> simp <;> omega

theorem raw_lt_NA {a : Nat} (ha : a < 3) : a < NA M := by unfold NA; omega

/-! ## Changing one digit -/

/-- The column of `a` with digit `i` replaced by `v`. -/
def setDig (a i v : Nat) : Nat := cenc M ((cdigits M a).set i v) (clft a)

theorem setDig_digits_lt (a i : Nat) {v : Nat} (hv : v < base M) : ∀ d ∈ (cdigits M a).set i v, d < base M := by
  intro d hd
  rw [List.mem_iff_getElem?] at hd
  obtain ⟨j, hj⟩ := hd
  rw [List.getElem?_set] at hj
  split at hj
  · split at hj
    · simp at hj; omega
    · simp at hj
  · exact cdigits_lt M a d (List.mem_of_getElem? hj)

theorem setDig_lt (a i : Nat) {v : Nat} (hv : v < base M) : setDig M a i v < NA M :=
  cenc_lt M (by rw [List.length_set, cdigits_length]) (setDig_digits_lt M a i hv) _

theorem clft_setDig (a i v : Nat) : clft (setDig M a i v) = clft a := clft_cenc M _ _

theorem cdig_setDig (a : Nat) {i v : Nat} (hi : i < k) (hv : v < base M) (j : Nat) :
    cdig M (setDig M a i v) j = if j = i then v else cdig M a j := by
  unfold setDig cdig
  rw [cdigits_cenc M (by rw [List.length_set, cdigits_length]) (setDig_digits_lt M a i hv)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
  by_cases h : j = i
  · subst h; simp [cdigits_length, hi]
  · simp [Ne.symm h, h]

/-! ## The symbol written on cell `0` at the start -/

/-- The column of the raw symbol `a` with every flag and the left bit set. -/
def initSym (a : Nat) : Nat := cenc M ((cdigits M a).map (· + 1)) true

theorem initSym_digits_lt {a : Nat} (ha : a < 3) : ∀ d ∈ (cdigits M a).map (· + 1), d < base M := by
  have h6 := six_le_base M
  intro d hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
  unfold cdigits at he
  rw [if_pos ha] at he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
  split <;> omega

theorem initSym_lt {a : Nat} (ha : a < 3) : initSym M a < NA M :=
  cenc_lt M (by simp [cdigits_length]) (initSym_digits_lt M ha) _

theorem clft_initSym (a : Nat) : clft (initSym M a) = true := clft_cenc M _ _

theorem cdig_initSym {a : Nat} (ha : a < 3) (i : Fin k) :
    cdig M (initSym M a) i.val = (if i.val = 0 then 2 * a else 0) + 1 := by
  unfold initSym
  have e : cdig M (cenc M ((cdigits M a).map (· + 1)) true) i.val = cdig M a i.val + 1 := by
    unfold cdig
    rw [cdigits_cenc M (by simp [cdigits_length]) (initSym_digits_lt M ha)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (l := cdigits M a) (by rw [cdigits_length]; exact i.isLt)]
  rw [e, cdig_raw M ha]

/-! ## Control states -/

/-- A control state: the phase, the tape at hand, `M`'s state and the symbols read so far (or all of them). -/
structure Ctl where
  ph : Nat
  i : Nat
  q : Nat
  rs : List Nat

/-- How many symbols a control state carries: `i` while reading, `k` afterwards. -/
def clen (k ph i : Nat) : Nat := if ph ≤ 1 then i else k

/-- The code of a control state. -/
def enc (x : Ctl) : Nat := 3 + x.ph + 6 * (x.i + (k + 1) * (x.q + M.nq * rcode M.na x.rs))

/-- Reading a control state back from its code. -/
def dec (n : Nat) : Ctl :=
  { ph := (n - 3) % 6
    i := (n - 3) / 6 % (k + 1)
    q := (n - 3) / 6 / (k + 1) % M.nq
    rs := digits M.na (clen k ((n - 3) % 6) ((n - 3) / 6 % (k + 1))) ((n - 3) / 6 / (k + 1) / M.nq) }

/-- A control state that the simulator can be in. -/
structure WF (x : Ctl) : Prop where
  ph : x.ph < 6
  i : x.i ≤ k
  q : x.q < M.nq
  len : x.rs.length = clen k x.ph x.i
  rs : ∀ a ∈ x.rs, a < M.na

/-- The number of states of the simulator. -/
def NQ : Nat := 3 + 6 * ((k + 1) * (M.nq * M.na ^ k))

theorem mr_mod {a b : Nat} (c : Nat) (h : a < b) : (a + b * c) % b = a := by
  rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt h

theorem mr_div {a b : Nat} (c : Nat) (h : a < b) : (a + b * c) / b = c := by
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt h, Nat.zero_add]

theorem dec_enc {x : Ctl} (h : WF M x) : dec M (enc M x) = x := by
  obtain ⟨ph, i, q, rs⟩ := x
  have hph := h.ph; have hi := h.i; have hq := h.q; have hl := h.len; have hrs := h.rs
  simp only at hph hi hq hl hrs
  have e0 : 3 + ph + 6 * (i + (k + 1) * (q + M.nq * rcode M.na rs)) - 3 =
      ph + 6 * (i + (k + 1) * (q + M.nq * rcode M.na rs)) := by omega
  simp only [dec, enc, e0]
  rw [mr_mod _ hph, mr_div _ hph, mr_mod _ (by omega : i < k + 1), mr_div _ (by omega : i < k + 1),
    mr_mod _ hq, mr_div _ hq, ← hl, digits_rcode hrs]

theorem three_le_enc (x : Ctl) : 3 ≤ enc M x := by unfold enc; omega

theorem enc_lt {x : Ctl} (h : WF M x) : enc M x < NQ M := by
  obtain ⟨ph, i, q, rs⟩ := x
  have hph := h.ph; have hi := h.i; have hq := h.q; have hl := h.len; have hrs := h.rs
  simp only at hph hi hq hl hrs
  have hlk : rs.length ≤ k := by rw [hl]; unfold clen; split <;> omega
  have hna : 0 < M.na := by have := M.three_le_na; omega
  have hr : rcode M.na rs < M.na ^ k :=
    Nat.lt_of_lt_of_le (rcode_lt hrs) (Nat.pow_le_pow_right hna hlk)
  have h1 : q + M.nq * rcode M.na rs + 1 ≤ M.nq * M.na ^ k := by
    have : M.nq * (rcode M.na rs + 1) ≤ M.nq * M.na ^ k := Nat.mul_le_mul_left _ hr
    rw [Nat.mul_succ] at this; omega
  have h2 : i + (k + 1) * (q + M.nq * rcode M.na rs) + 1 ≤ (k + 1) * (M.nq * M.na ^ k) := by
    have : (k + 1) * (q + M.nq * rcode M.na rs + 1) ≤ (k + 1) * (M.nq * M.na ^ k) :=
      Nat.mul_le_mul_left _ h1
    rw [Nat.mul_succ] at this; omega
  unfold enc NQ
  simp only
  omega

theorem three_le_NQ : 3 ≤ NQ M := by unfold NQ; omega

theorem three_le_NA : 3 ≤ NA M := by unfold NA; omega

end OneTape
end Complexity
