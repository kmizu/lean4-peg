import Complexity.OneTape.Code

/-!
# The one-tape simulator

The control states of the simulator of `M`, by phase (`Ctl.ph`):

* `0` (read, scan): move right until the column flagged for tape `i`; record its symbol and go to phase `1`.
* `1` (read, back): move left until the left bit; then the next tape (`rNext`).
* `2` (compute): apply `M`'s transition to the recorded symbols; stop in `M`'s new state if it halts, otherwise go
  to the writing phases (`wNext`).
* `3` (write, scan): move right until the column flagged for tape `i`; write `M`'s new symbol there, clear the flag,
  move like `M`'s head `i` and go to phase `4`.
* `4` (write, flag): set the flag of tape `i` on the column reached, then phase `5`.
* `5` (write, back): move left until the left bit; then the next tape, or after the last tape the reading phase of
  `M`'s next step (`wNext`).

The starting state `2` writes the column of cell `0` with all flags and the left bit set (`initSym`). The
transition function is clamped to the ranges (`clamp`), so that it trivially respects them; on the runs that
matter the clamp never acts (`step_ctl`).
-/

namespace Complexity
namespace OneTape

variable {k : Nat} (M : TM k)

/-- `M`'s transition from state `q` on the symbols listed in `rs`. -/
def mdelta (q : Nat) (rs : List Nat) : Nat × (Fin k → Nat) × (Fin k → Move) :=
  M.delta q (fun j => rs.getD j.val 0)

/-- The reading phase for tape `i`, or the computing phase after the last tape. -/
def rNext (k i q : Nat) (rs : List Nat) : Ctl := if i < k then ⟨0, i, q, rs⟩ else ⟨2, i, q, rs⟩

/-- The writing phase for tape `i`, or the reading phase of the next step after the last tape. -/
def wNext (i q : Nat) (rs : List Nat) : Ctl :=
  if i < k then ⟨3, i, q, rs⟩ else rNext k 0 (mdelta M q rs).1 []

/-- What the simulator does in control state `x` reading `a`: new state, symbol to write, move. -/
def act (x : Ctl) (a : Nat) : Nat × Nat × Move :=
  if x.ph = 0 then
    if cdig M a x.i % 2 = 1 then (enc M ⟨1, x.i + 1, x.q, x.rs ++ [cdig M a x.i / 2]⟩, a, .S)
    else (enc M x, a, .R)
  else if x.ph = 1 then
    if clft a then (enc M (rNext k x.i x.q x.rs), a, .S) else (enc M x, a, .L)
  else if x.ph = 2 then
    if (mdelta M x.q x.rs).1 = 0 ∨ (mdelta M x.q x.rs).1 = 1 then ((mdelta M x.q x.rs).1, a, .S)
    else (enc M (wNext M 0 x.q x.rs), a, .S)
  else if x.ph = 3 then
    if cdig M a x.i % 2 = 1 then
      (enc M ⟨4, x.i, x.q, x.rs⟩, setDig M a x.i (2 * (List.ofFn (mdelta M x.q x.rs).2.1).getD x.i 0),
        (List.ofFn (mdelta M x.q x.rs).2.2).getD x.i .S)
    else (enc M x, a, .R)
  else if x.ph = 4 then
    (enc M ⟨5, x.i + 1, x.q, x.rs⟩, setDig M a x.i (cdig M a x.i + 1), .S)
  else
    if clft a then (enc M (wNext M x.i x.q x.rs), a, .S) else (enc M x, a, .L)

/-- The start: mark cell `0` as the column with all heads and the left bit, then read tape `0`. -/
def initAct (a : Nat) : Nat × Nat × Move := (enc M (rNext k 0 2 []), initSym M a, .S)

/-- The unclamped transition. -/
def out (q a : Nat) : Nat × Nat × Move := if q = 2 then initAct M a else act M (dec M q) a

/-- Clamp a transition to the ranges of states and symbols. -/
def clamp (o : Nat × Nat × Move) : Nat × (Fin 1 → Nat) × (Fin 1 → Move) :=
  if o.1 < NQ M ∧ o.2.1 < NA M then (o.1, fun _ => o.2.1, fun _ => o.2.2) else (0, fun _ => 0, fun _ => .S)

/-- **The one-tape simulator of `M`.** -/
def sim : TM 1 where
  nq := NQ M
  na := NA M
  delta := fun q r => clamp M (out M q (r 0))
  three_le_nq := three_le_NQ M
  three_le_na := three_le_NA M
  delta_state := by
    intro q r _ _
    simp only [clamp]
    split
    · rename_i h; exact h.1
    · have := three_le_NQ M; simp; omega
  delta_sym := by
    intro q r _ _ i
    simp only [clamp]
    split
    · rename_i h; exact h.2
    · have := three_le_NA M; simp; omega

/-! ## One step of the simulator -/

/-- A step of a one-tape machine, by its three components. -/
theorem step_one {S : TM 1} {sc : Cfg 1} {q' a' : Nat} {m : Move} (hn : ¬ sc.halted)
    (hd : S.delta sc.state sc.read = (q', fun _ => a', fun _ => m)) :
    (S.step sc).state = q' ∧ (S.step sc).pos 0 = m.apply (sc.pos 0) ∧
      (S.step sc).cells 0 = fun j => if j = sc.pos 0 then a' else sc.cells 0 j := by
  simp [TM.step, hn, hd]

theorem enc_not_halted {sc : Cfg 1} {x : Ctl} (hs : sc.state = enc M x) : ¬ sc.halted := by
  have := three_le_enc M x
  unfold Cfg.halted; omega

/-- **A step in a control state**, when the result is in range. -/
theorem step_ctl {sc : Cfg 1} {x : Ctl} (hx : WF M x) (hs : sc.state = enc M x)
    (hq : (act M x (sc.cells 0 (sc.pos 0))).1 < NQ M) (ha : (act M x (sc.cells 0 (sc.pos 0))).2.1 < NA M) :
    ((sim M).step sc).state = (act M x (sc.cells 0 (sc.pos 0))).1 ∧
      ((sim M).step sc).pos 0 = (act M x (sc.cells 0 (sc.pos 0))).2.2.apply (sc.pos 0) ∧
      ((sim M).step sc).cells 0 = fun j => if j = sc.pos 0 then (act M x (sc.cells 0 (sc.pos 0))).2.1
        else sc.cells 0 j := by
  apply step_one (enc_not_halted M hs)
  have h2 : enc M x ≠ 2 := by have := three_le_enc M x; omega
  show clamp M (out M sc.state (sc.cells 0 (sc.pos 0))) = _
  rw [hs, out, if_neg h2, dec_enc M hx, clamp, if_pos ⟨hq, ha⟩]

/-- The first step of the simulator. -/
theorem step_init {sc : Cfg 1} (hs : sc.state = 2) (ha : sc.cells 0 (sc.pos 0) < 3) :
    ((sim M).step sc).state = enc M (rNext k 0 2 []) ∧
      ((sim M).step sc).pos 0 = sc.pos 0 ∧
      ((sim M).step sc).cells 0 = fun j => if j = sc.pos 0 then initSym M (sc.cells 0 (sc.pos 0))
        else sc.cells 0 j := by
  have hn : ¬ sc.halted := by unfold Cfg.halted; omega
  have hw : WF M (rNext k 0 2 []) := by
    have := M.three_le_nq
    unfold rNext; split
    · exact ⟨by decide, by show 0 ≤ k; omega, by show 2 < M.nq; omega, by simp [clen], by simp⟩
    · exact ⟨by decide, by show 0 ≤ k; omega, by show 2 < M.nq; omega, by simp [clen]; omega, by simp⟩
  refine step_one (m := .S) hn ?_
  show clamp M (out M sc.state (sc.cells 0 (sc.pos 0))) = _
  rw [hs, out, if_pos rfl, initAct, clamp, if_pos ⟨enc_lt M hw, initSym_lt M ha⟩]

end OneTape
end Complexity
