import PalPeg.ProgramMachine
import PalPeg.GalilScaffoldCounter

/-!
# K-local refinement, piece 1: a segmented unary counter

`PalPeg.GalilScaffoldCounter.Counter` is the *logical* two-stack counter used by
the Galil scaffold.  This file realizes it on a single physical tape
(`PalPeg.Program.STape`) over the three-letter alphabet

```
Seg := Fin 3        blank = 0,  sep = 1,  mark = 2
```

with **all three operations costing exactly one `STape.applyAction`** (one write
plus one move), in particular `Counter.reset`, which is normally linear in the
stored value.  The trick is *segmentation*: `reset` does not erase the stored
marks, it drops a fresh separator at the head and abandons everything below it.

## Tape discipline

The head sits on the *frontier*: the cell immediately above the topmost mark.
The stored value is the length of the maximal run of `mark` starting at the top
of `left`, and the run is terminated by a `sep`; everything below that `sep` is
garbage (older, abandoned segments).  `right` and `focus` carry no counter
information.

```
left  = mark^v ++ sep :: garbage          (top of `left` = most recent cell)
focus = blank                             (the frontier)
```

Consequences of putting the head on the frontier rather than on the top mark:
`push` = "write `mark`, move right" lands on fresh tape, and `pop` = "write
`blank`, move left" lands on the mark it just logically removed.  The zero test
is therefore *not* a test of `focus`; it is a test of the top of `left`, which a
finite control performs by the single `peek` action below (`peek_focus_sep`).

The polarity of the counter is kept in the finite control as a `Bool` (`true` =
non-negative), so a canonical `Counter` is represented by the pair
(tape value, sign bit); `absCtr` is that abstraction map.
-/

set_option autoImplicit false

namespace PalPeg.LocalCounter

open PalPeg.Program
open PegSeparation.RealTimeTM
open PalPeg.GalilScaffoldCounter

/-! ## Alphabet -/

/-- The three-letter alphabet of a counter tape. -/
abbrev Seg := Fin 3

/-- The blank symbol. -/
def blank : Seg := 0
/-- The segment separator. -/
def sep : Seg := 1
/-- One unit of the unary value. -/
def mark : Seg := 2

theorem sep_ne_mark : sep ≠ mark := by decide
theorem blank_ne_mark : blank ≠ mark := by decide
theorem blank_ne_sep : blank ≠ sep := by decide

/-! ## The stored value -/

/-- Length of the maximal `mark`-run at the head of a list. -/
def markRun : List Seg → ℕ
  | [] => 0
  | s :: rest => if s = mark then markRun rest + 1 else 0

@[simp] theorem markRun_nil : markRun [] = 0 := rfl

@[simp] theorem markRun_mark (rest : List Seg) :
    markRun (mark :: rest) = markRun rest + 1 := by
  simp [markRun]

@[simp] theorem markRun_sep (rest : List Seg) : markRun (sep :: rest) = 0 := by
  simp [markRun, sep, mark]

@[simp] theorem markRun_blank (rest : List Seg) : markRun (blank :: rest) = 0 := by
  simp [markRun, blank, mark]

theorem markRun_eq_zero_or_cons (L : List Seg) :
    markRun L = 0 ∨ ∃ L', L = mark :: L' := by
  cases L with
  | nil => exact Or.inl rfl
  | cons s rest =>
      by_cases h : s = mark
      · exact Or.inr ⟨rest, by rw [h]⟩
      · exact Or.inl (by simp [markRun, h])

/-- The value stored on a counter tape: the mark-run at the top of `left`. -/
def val (t : STape Seg) : ℕ := markRun t.left

/-- The shape invariant: the mark-run is terminated by a separator, below which
anything may sit. -/
def SegCtr (t : STape Seg) (v : ℕ) : Prop :=
  ∃ garbage : List Seg, t.left = List.replicate v mark ++ sep :: garbage

theorem markRun_replicate_sep (v : ℕ) (g : List Seg) :
    markRun (List.replicate v mark ++ sep :: g) = v := by
  induction v with
  | zero => simp
  | succ v ih => simp [List.replicate_succ, ih]

/-- Under the shape invariant, `val` reads off the index. -/
theorem val_eq_of_segCtr {t : STape Seg} {v : ℕ} (h : SegCtr t v) : val t = v := by
  obtain ⟨g, hg⟩ := h
  simp [val, hg, markRun_replicate_sep]

/-! ## The three O(1) actions -/

/-- `push`: write a `mark` on the frontier and step to the new frontier. -/
def push (t : STape Seg) : STape Seg := STape.applyAction blank t (mark, Move.right)

/-- `pop`: blank the frontier and step back onto the top mark. -/
def pop (t : STape Seg) : STape Seg := STape.applyAction blank t (blank, Move.left)

/-- `resetSeg`: drop a fresh separator, abandoning the segment below. -/
def resetSeg (t : STape Seg) : STape Seg := STape.applyAction blank t (sep, Move.right)

/-- `peek`: the zero test.  It moves the head onto the top cell, so it is a
*test only* and must be undone by the control; it does not preserve `val`. -/
def peek (t : STape Seg) : STape Seg := STape.applyAction blank t (blank, Move.left)

theorem push_left (t : STape Seg) : (push t).left = mark :: t.left := by
  cases t with | mk L f R => cases R <;> rfl

theorem resetSeg_left (t : STape Seg) : (resetSeg t).left = sep :: t.left := by
  cases t with | mk L f R => cases R <;> rfl

theorem pop_left (t : STape Seg) : (pop t).left = t.left.tail := by
  cases t with | mk L f R => cases L <;> rfl

theorem peek_focus (t : STape Seg) (s : Seg) (L : List Seg) (h : t.left = s :: L) :
    (peek t).focus = s := by
  cases t with | mk L' f R => cases L' with
    | nil => exact absurd h (by simp)
    | cons a as => cases h; rfl

/-! ### The actions on `val` -/

@[simp] theorem val_push (t : STape Seg) : val (push t) = val t + 1 := by
  simp [val, push_left]

@[simp] theorem val_resetSeg (t : STape Seg) : val (resetSeg t) = 0 := by
  simp [val, resetSeg_left]

theorem val_pop {t : STape Seg} {v : ℕ} (h : val t = v + 1) : val (pop t) = v := by
  rcases markRun_eq_zero_or_cons t.left with h0 | ⟨L', hL⟩
  · exact absurd (h ▸ h0 : (v : ℕ) + 1 = 0) (by omega)
  · have : markRun L' + 1 = v + 1 := by
      simpa [val, hL] using h
    simp [val, pop_left, hL]
    omega

/-! ### The actions on the shape invariant -/

theorem segCtr_push {t : STape Seg} {v : ℕ} (h : SegCtr t v) : SegCtr (push t) (v + 1) := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, by simp [push_left, hg, List.replicate_succ]⟩

theorem segCtr_pop {t : STape Seg} {v : ℕ} (h : SegCtr t (v + 1)) : SegCtr (pop t) v := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, by simp [pop_left, hg, List.replicate_succ]⟩

theorem segCtr_reset (t : STape Seg) : SegCtr (resetSeg t) 0 :=
  ⟨t.left, by simp [resetSeg_left]⟩

/-! ## Abstraction to `Counter` -/

/-- The negative canonical counter of absolute value `n`. -/
def negOfNat (n : ℕ) : Counter := ⟨[], List.replicate n ()⟩

/-- Polarity flip on logical counters. -/
def negate (c : Counter) : Counter := ⟨c.neg, c.pos⟩

/-- The abstraction map: tape + control-held sign bit ↦ canonical `Counter`. -/
def absCtr (t : STape Seg) (b : Bool) : Counter :=
  if b then ofNat (val t) else negOfNat (val t)

theorem absCtr_canonical (t : STape Seg) (b : Bool) : Canonical (absCtr t b) := by
  cases b <;> simp [absCtr, Canonical, ofNat, negOfNat]

theorem value_eq (t : STape Seg) (b : Bool) :
    value (absCtr t b) = if b then (val t : ℤ) else -(val t : ℤ) := by
  cases b <;> simp [absCtr, value, ofNat, negOfNat]

theorem neg_flip (t : STape Seg) (b : Bool) : absCtr t (!b) = negate (absCtr t b) := by
  cases b <;> simp [absCtr, negate, ofNat, negOfNat]

theorem inc_negOfNat_succ (n : ℕ) : inc (negOfNat (n + 1)) = negOfNat n := by
  simp [inc, negOfNat, List.replicate_succ]

theorem dec_negOfNat (n : ℕ) : dec (negOfNat n) = negOfNat (n + 1) := by
  simp [dec, negOfNat, List.replicate_succ]

/-- `push` increments the absolute value: it is `inc` on the positive side and
`dec` on the negative side. -/
theorem absCtr_push (t : STape Seg) (b : Bool) :
    absCtr (push t) b = if b then inc (absCtr t b) else dec (absCtr t b) := by
  cases b <;> simp [absCtr, inc_ofNat, dec_negOfNat]

/-- `pop` decrements the absolute value. -/
theorem absCtr_pop {t : STape Seg} {v : ℕ} (h : val t = v + 1) (b : Bool) :
    absCtr (pop t) b = if b then dec (absCtr t b) else inc (absCtr t b) := by
  have hp : val (pop t) = v := val_pop h
  cases b <;>
    simp [absCtr, hp, h, dec_ofNat_succ, inc_negOfNat_succ]

/-- `resetSeg` realizes `Counter.reset` in one tape action, whatever the sign. -/
theorem absCtr_reset (t : STape Seg) (b : Bool) : absCtr (resetSeg t) b = reset := by
  cases b <;> simp [absCtr, reset, ofNat, negOfNat]

/-- The zero test reads off `val`. -/
theorem zero_iff (t : STape Seg) (b : Bool) :
    zero (absCtr t b) = decide (val t = 0) := by
  cases b <;> cases hv : val t <;>
    simp [absCtr, zero, ofNat, negOfNat, hv, List.replicate_succ]

/-- …and under the shape invariant a finite control can perform it with the
single `peek` action, by looking at the symbol it lands on. -/
theorem peek_focus_sep {t : STape Seg} {v : ℕ} (h : SegCtr t v) :
    ((peek t).focus = sep) ↔ v = 0 := by
  obtain ⟨g, hg⟩ := h
  cases v with
  | zero =>
      have : t.left = sep :: g := by simpa using hg
      simp [peek_focus t sep g this]
  | succ v =>
      have hL : t.left = mark :: (List.replicate v mark ++ sep :: g) := by
        simpa [List.replicate_succ] using hg
      simp [peek_focus t mark _ hL, Ne.symm sep_ne_mark]

theorem zero_iff_peek {t : STape Seg} {v : ℕ} (h : SegCtr t v) (b : Bool) :
    zero (absCtr t b) = decide ((peek t).focus = sep) := by
  rw [zero_iff, val_eq_of_segCtr h]
  simp [peek_focus_sep h]

#print axioms absCtr_push
#print axioms absCtr_pop
#print axioms absCtr_reset
#print axioms segCtr_push
#print axioms segCtr_pop
#print axioms segCtr_reset
#print axioms zero_iff
#print axioms zero_iff_peek
#print axioms peek_focus_sep
#print axioms value_eq
#print axioms neg_flip
#print axioms absCtr_canonical

end PalPeg.LocalCounter
