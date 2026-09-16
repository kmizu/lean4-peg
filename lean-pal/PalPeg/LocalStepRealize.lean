import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import PalPeg.ProgramMachine

/-!
# Realizing local steps on a strictly real-time structured machine

A *local step* reads and rewrites, on every tape, only the `2K+1` cells within
distance `K` of the head, and then moves each head by at most `K`; its effect is
a function of the finite control, of the input symbol (if any) and of those local
windows.  This file shows that such a step can be *realized* on
`PalPeg.Program.StructuredMachine`, which may only read the scanned symbol and
move one cell per micro-step: `c K = 7 * K + 2` micro-steps suffice for one local
step, so `n` local steps per input symbol are realized by a machine with
`B = n * c K` micro-steps per input symbol.

The file is self-contained and independent of the Galil scaffold.

## What is and is not claimed

`STape.applyAction` implements a tape that is infinite to the right only: a
`.left` move at the left edge writes but does not move.  A radius-`K` local step
therefore cannot be realized *semantically* near the left edge — and the initial
configuration has every head at the edge.  Accordingly:

* `LocalStep.apply` is defined by the physical sweep (`sweep`), so the
  simulation theorems `realize_srun` / `realize_SAccepts` hold
  **unconditionally**;
* the semantic reading of one local step is given separately by `readWin_eq`
  (unconditional), and by `pos_sweep` / `rd_sweep`, which hold whenever the head
  is at least `K` cells away from the left edge (`K ≤ pos T`) — then the step
  reads the `2 * K + 1` cells centred on the head, overwrites exactly them with
  the new window, and moves the head by `d`.

The displacement is an integer `d` with `|d| ≤ K` (field `disp_le`); it is
latched into the finite control as `d + K : Fin (2 * K + 1)` during the write
sweep.  `Terminal` must be a `Fintype` with decidable equality, since the input
symbol is buffered in the finite control.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PalPeg.Local

open PalPeg.Program
open PalPeg.Speedup
open PegSeparation.RealTimeTM

variable {Γ : Type}

/-! ## Absolute view of a structured tape

`STape.applyAction` implements a tape that is infinite to the *right* only: a
`.left` move at the left edge writes but does not move.  Positions are therefore
measured absolutely, from the left edge, and the *content* of a tape is a
function `ℕ → Γ` (blank beyond the stored lists). -/

/-- The stored content of a tape, as a list; cells beyond it are blank. -/
def toList (T : STape Γ) : List Γ := T.left.reverse ++ T.focus :: T.right

/-- Absolute head position, measured from the left edge. -/
def pos (T : STape Γ) : ℕ := T.left.length

/-- The symbol at absolute position `p`. -/
def rd (blank : Γ) (T : STape Γ) (p : ℕ) : Γ := (toList T).getD p blank

@[simp] theorem rd_pos (blank : Γ) (T : STape Γ) : rd blank T (pos T) = T.focus := by
  have h : T.left.reverse.length ≤ pos T := by simp [pos]
  simp [rd, toList, pos]

/-- Overwriting position `p` of a list at the join, the general step lemma. -/
theorem getD_swap (A : List Γ) (x y : Γ) (R : List Γ) (blank : Γ) (p : ℕ) :
    (A ++ x :: R).getD p blank = if p = A.length then x else (A ++ y :: R).getD p blank := by
  rcases Nat.lt_trichotomy p A.length with h | h | h
  · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
    simp [Nat.ne_of_lt h]
  · subst h
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
    simp
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_lt h),
      List.getD_append_right _ _ _ _ (Nat.le_of_lt h)]
    obtain ⟨k, hk⟩ : ∃ k, p - A.length = k + 1 := ⟨p - A.length - 1, by omega⟩
    rw [hk]
    simp [Nat.ne_of_gt h]

theorem getD_snoc_blank (A : List Γ) (blank : Γ) (p : ℕ) :
    (A ++ [blank]).getD p blank = A.getD p blank := by
  rcases Nat.lt_or_ge p A.length with h | h
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ h, List.getD_eq_default _ _ h]
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · simp [← h']
    · rw [List.getD_eq_default]
      simpa using by omega

/-- The head position after one micro-action: `.left` is clamped at the edge,
which is exactly truncated subtraction. -/
theorem pos_applyAction (blank w : Γ) (T : STape Γ) (m : Move) :
    pos (T.applyAction blank (w, m)) =
      match m with
      | .right => pos T + 1
      | .left => pos T - 1
      | .stay => pos T := by
  cases m <;> cases hl : T.left <;> cases hr : T.right <;>
    simp [pos, STape.applyAction, hl, hr]

theorem rd_eq (blank : Γ) (L : List Γ) (f : Γ) (R : List Γ) (p : ℕ) :
    rd blank ⟨L, f, R⟩ p = (L.reverse ++ f :: R).getD p blank := rfl

theorem pos_eq (L : List Γ) (f : Γ) (R : List Γ) : pos ⟨L, f, R⟩ = L.length := rfl

/-- The content after one micro-action: the scanned cell is overwritten with `w`
and nothing else changes — independently of the move. -/
theorem rd_applyAction (blank w : Γ) (T : STape Γ) (m : Move) (p : ℕ) :
    rd blank (T.applyAction blank (w, m)) p = if p = pos T then w else rd blank T p := by
  obtain ⟨L, f, R⟩ := T
  cases m with
  | stay =>
    rw [show (STape.mk L f R).applyAction blank (w, Move.stay) = ⟨L, w, R⟩ from rfl,
      rd_eq, rd_eq, pos_eq, show L.length = L.reverse.length from by simp]
    exact getD_swap L.reverse w f R blank p
  | left =>
    cases L with
    | nil =>
        rw [show (STape.mk [] f R).applyAction blank (w, Move.left) = ⟨[], w, R⟩ from rfl,
          rd_eq, rd_eq, pos_eq]
        simpa using getD_swap [] w f R blank p
    | cons n l =>
        rw [show (STape.mk (n :: l) f R).applyAction blank (w, Move.left)
              = ⟨l, n, w :: R⟩ from rfl, rd_eq, rd_eq, pos_eq,
          show (n :: l).length = (l.reverse ++ [n]).length from by simp,
          show l.reverse ++ n :: w :: R = (l.reverse ++ [n]) ++ w :: R from by simp,
          show (n :: l).reverse ++ f :: R = (l.reverse ++ [n]) ++ f :: R from by simp]
        exact getD_swap (l.reverse ++ [n]) w f R blank p
  | right =>
    cases R with
    | nil =>
        rw [show (STape.mk L f ([] : List Γ)).applyAction blank (w, Move.right)
              = ⟨w :: L, blank, []⟩ from rfl, rd_eq, rd_eq, pos_eq,
          show (w :: L).reverse ++ blank :: ([] : List Γ)
              = (L.reverse ++ [w]) ++ [blank] from by simp,
          getD_snoc_blank, show L.length = L.reverse.length from by simp,
          show L.reverse ++ [w] = L.reverse ++ w :: ([] : List Γ) from rfl]
        exact getD_swap L.reverse w f [] blank p
    | cons n r =>
        rw [show (STape.mk L f (n :: r)).applyAction blank (w, Move.right)
              = ⟨w :: L, n, r⟩ from rfl, rd_eq, rd_eq, pos_eq,
          show (w :: L).reverse ++ n :: r = L.reverse ++ w :: n :: r from by simp,
          show L.length = L.reverse.length from by simp]
        exact getD_swap L.reverse w f (n :: r) blank p


/-! ## Primitive head motions

Both motions write back the symbol they scanned, so they change the head
position only — never the content. -/

/-- Writing back the scanned symbol without moving changes nothing. -/
@[simp] theorem applyAction_stay_self (blank : Γ) (T : STape Γ) :
    T.applyAction blank (T.focus, .stay) = T := rfl

/-- Move the head one cell left (clamped at the left edge). -/
def mvL (blank : Γ) (T : STape Γ) : STape Γ := T.applyAction blank (T.focus, .left)

/-- Move the head one cell right. -/
def mvR (blank : Γ) (T : STape Γ) : STape Γ := T.applyAction blank (T.focus, .right)

theorem pos_applyAction_left (blank w : Γ) (T : STape Γ) :
    pos (T.applyAction blank (w, .left)) = pos T - 1 := pos_applyAction blank w T .left

theorem pos_applyAction_right (blank w : Γ) (T : STape Γ) :
    pos (T.applyAction blank (w, .right)) = pos T + 1 := pos_applyAction blank w T .right

theorem pos_applyAction_stay (blank w : Γ) (T : STape Γ) :
    pos (T.applyAction blank (w, .stay)) = pos T := pos_applyAction blank w T .stay

@[simp] theorem pos_mvL (blank : Γ) (T : STape Γ) : pos (mvL blank T) = pos T - 1 :=
  pos_applyAction blank T.focus T .left

@[simp] theorem pos_mvR (blank : Γ) (T : STape Γ) : pos (mvR blank T) = pos T + 1 :=
  pos_applyAction blank T.focus T .right

@[simp] theorem rd_mvL (blank : Γ) (T : STape Γ) (p : ℕ) :
    rd blank (mvL blank T) p = rd blank T p := by
  rw [mvL, rd_applyAction]
  split_ifs with h
  · rw [h, rd_pos]
  · rfl

@[simp] theorem rd_mvR (blank : Γ) (T : STape Γ) (p : ℕ) :
    rd blank (mvR blank T) p = rd blank T p := by
  rw [mvR, rd_applyAction]
  split_ifs with h
  · rw [h, rd_pos]
  · rfl

@[simp] theorem pos_mvLN (blank : Γ) (m : ℕ) (T : STape Γ) :
    pos ((mvL blank)^[m] T) = pos T - m := by
  induction m with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', pos_mvL, ih]; omega

@[simp] theorem pos_mvRN (blank : Γ) (m : ℕ) (T : STape Γ) :
    pos ((mvR blank)^[m] T) = pos T + m := by
  induction m with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', pos_mvR, ih]; omega

@[simp] theorem rd_mvLN (blank : Γ) (m : ℕ) (T : STape Γ) (p : ℕ) :
    rd blank ((mvL blank)^[m] T) p = rd blank T p := by
  induction m with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', rd_mvL, ih]

@[simp] theorem rd_mvRN (blank : Γ) (m : ℕ) (T : STape Γ) (p : ℕ) :
    rd blank ((mvR blank)^[m] T) p = rd blank T p := by
  induction m with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', rd_mvR, ih]

/-! ## Local steps -/

/-- The `2 * K + 1` cells around a head: index `i` is the cell at absolute
position `headPosition - K + i`. -/
abbrev Window (Γ : Type) (K : ℕ) : Type := Fin (2 * K + 1) → Γ

/-- Total clamped window index, so that no side conditions leak into
definitions. -/
def idx (K : ℕ) (m : ℕ) : Fin (2 * K + 1) := ⟨min m (2 * K), by omega⟩

theorem idx_val {K m : ℕ} (h : m ≤ 2 * K) : (idx K m : ℕ) = m := by
  simp only [idx]
  omega

@[simp] theorem idx_coe (K : ℕ) (i : Fin (2 * K + 1)) : idx K (i : ℕ) = i := by
  apply Fin.ext
  simp only [idx]
  omega

/-- A step that only reads and writes within distance `K` of each head and moves
each head by at most `K`; its effect is a function of the finite control, of the
input symbol (if any) and of the local windows.  `next` returns the new control
state and, per tape, the new window contents together with the head
displacement `d`, which `disp_le` bounds by `K`. -/
structure LocalStep (Terminal Q Γ : Type) (t K : ℕ) where
  next : Q → Option Terminal → (Fin t → Window Γ K) → Q × (Fin t → Window Γ K × ℤ)
  disp_le : ∀ (q : Q) (a : Option Terminal) (ws : Fin t → Window Γ K) (j : Fin t),
    |((next q a ws).2 j).2| ≤ (K : ℤ)

/-! ## The write sweep

`cPhase blank g c` performs `c` micro-steps: it writes `g (c-1), …, g 0` into the
cells at the head and to its left, moving left after each write except the last
one. -/

def cPhase (blank : Γ) (g : ℕ → Γ) : ℕ → STape Γ → STape Γ
  | 0, T => T
  | 1, T => T.applyAction blank (g 0, .stay)
  | (c + 2), T => cPhase blank g (c + 1) (T.applyAction blank (g (c + 1), .left))

theorem pos_cPhase (blank : Γ) (g : ℕ → Γ) (c : ℕ) (T : STape Γ) :
    pos (cPhase blank g (c + 1) T) = pos T - c := by
  induction c generalizing T with
  | zero => simpa [cPhase] using pos_applyAction_stay blank (g 0) T
  | succ n ih =>
      rw [show cPhase blank g (n + 1 + 1) T
            = cPhase blank g (n + 1) (T.applyAction blank (g (n + 1), .left)) from rfl,
        ih, pos_applyAction_left]
      omega

theorem rd_cPhase (blank : Γ) (g : ℕ → Γ) (c : ℕ) (T : STape Γ) (hc : c ≤ pos T) (p : ℕ) :
    rd blank (cPhase blank g (c + 1) T) p =
      if pos T - c ≤ p ∧ p ≤ pos T then g (p - (pos T - c)) else rd blank T p := by
  induction c generalizing T with
  | zero =>
      rw [show cPhase blank g 1 T = T.applyAction blank (g 0, .stay) from rfl, rd_applyAction]
      by_cases h : p = pos T
      · simp [h]
      · simp only [h, if_false]
        rw [if_neg]
        omega
  | succ n ih =>
      have hpos : pos (T.applyAction blank (g (n + 1), .left)) = pos T - 1 :=
        pos_applyAction_left blank (g (n + 1)) T
      have hstep := ih (T.applyAction blank (g (n + 1), .left)) (by omega)
      rw [show cPhase blank g (n + 1 + 1) T
            = cPhase blank g (n + 1) (T.applyAction blank (g (n + 1), .left)) from rfl,
        hstep, hpos, rd_applyAction]
      by_cases h1 : pos T - (n + 1) ≤ p ∧ p ≤ pos T
      · rw [if_pos h1]
        by_cases h2 : pos T - 1 - n ≤ p ∧ p ≤ pos T - 1
        · rw [if_pos h2]
          congr 1
          omega
        · rw [if_neg h2, if_pos (by omega : p = pos T)]
          congr 1
          omega
      · rw [if_neg h1, if_neg (by omega), if_neg (by omega)]

/-! ## One local step, physically

`sweep blank K T w d` is the tape transformation performed by one realized local
step: move `K` cells left, sweep `2 * K` cells right (this is the read pass),
write the new window while sweeping back left, and finally move right to the
target displacement.  `readWin` is what that read pass observes. -/

def readWin (blank : Γ) (K : ℕ) (T : STape Γ) : Window Γ K :=
  fun i => ((mvR blank)^[(i : ℕ)] ((mvL blank)^[K] T)).focus

def sweep (blank : Γ) (K : ℕ) (T : STape Γ) (w : Window Γ K) (d : ℤ) : STape Γ :=
  (mvR blank)^[(d + (K : ℤ)).toNat]
    (cPhase blank (fun i => w (idx K i)) (2 * K + 1)
      ((mvR blank)^[2 * K] ((mvL blank)^[K] T)))

/-- **What the read pass sees**: the `2 * K + 1` cells centred on the head. -/
theorem readWin_eq (blank : Γ) (K : ℕ) (T : STape Γ) (i : Fin (2 * K + 1)) :
    readWin blank K T i = rd blank T (pos T - K + (i : ℕ)) := by
  rw [readWin, ← rd_pos blank ((mvR blank)^[(i : ℕ)] ((mvL blank)^[K] T))]
  simp

/-- **Head position after one local step**, assuming the head is at least `K`
cells away from the left edge and `|d| ≤ K`. -/
theorem pos_sweep (blank : Γ) (K : ℕ) (T : STape Γ) (w : Window Γ K) (d : ℤ)
    (hK : K ≤ pos T) (hd : |d| ≤ (K : ℤ)) :
    ((pos (sweep blank K T w d) : ℤ)) = (pos T : ℤ) + d := by
  have hd1 : -(K : ℤ) ≤ d := neg_le_of_abs_le hd
  have hd2 : d ≤ (K : ℤ) := le_of_abs_le hd
  have htn : ((d + (K : ℤ)).toNat : ℤ) = d + (K : ℤ) := Int.toNat_of_nonneg (by omega)
  rw [sweep, pos_mvRN, pos_cPhase, pos_mvRN, pos_mvLN]
  omega

/-- **Content after one local step**: the window is overwritten by `w`, nothing
else changes. -/
theorem rd_sweep (blank : Γ) (K : ℕ) (T : STape Γ) (w : Window Γ K) (d : ℤ)
    (hK : K ≤ pos T) (p : ℕ) :
    rd blank (sweep blank K T w d) p =
      if pos T - K ≤ p ∧ p ≤ pos T + K then w (idx K (p - (pos T - K)))
      else rd blank T p := by
  have hp : pos ((mvR blank)^[2 * K] ((mvL blank)^[K] T)) = pos T + K := by
    rw [pos_mvRN, pos_mvLN]; omega
  rw [sweep, rd_mvRN, rd_cPhase _ _ _ _ (by omega), hp, rd_mvRN, rd_mvLN]
  by_cases h : pos T - K ≤ p ∧ p ≤ pos T + K
  · rw [if_pos h, if_pos (by omega)]
    congr 2
    omega
  · rw [if_neg h, if_neg (by omega)]

namespace LocalStep

variable {Terminal Q : Type} {t K : ℕ}

/-- One local step on structured tapes, realized physically by `sweep`. -/
def apply (L : LocalStep Terminal Q Γ t K) (blank : Γ)
    (x : Q × (Fin t → STape Γ)) (a : Option Terminal) : Q × (Fin t → STape Γ) :=
  let res := L.next x.1 a (fun j => readWin blank K (x.2 j))
  (res.1, fun j => sweep blank K (x.2 j) (res.2 j).1 (res.2 j).2)

@[simp] theorem apply_fst (L : LocalStep Terminal Q Γ t K) (blank : Γ)
    (x : Q × (Fin t → STape Γ)) (a : Option Terminal) :
    (L.apply blank x a).1 = (L.next x.1 a (fun j => readWin blank K (x.2 j))).1 := rfl

@[simp] theorem apply_snd (L : LocalStep Terminal Q Γ t K) (blank : Γ)
    (x : Q × (Fin t → STape Γ)) (a : Option Terminal) (j : Fin t) :
    (L.apply blank x a).2 j =
      sweep blank K (x.2 j) ((L.next x.1 a (fun j => readWin blank K (x.2 j))).2 j).1
        ((L.next x.1 a (fun j => readWin blank K (x.2 j))).2 j).2 := rfl

end LocalStep


/-! ## The realization

One local step is realized by `cnt K = 7 * K + 2` micro-steps, in four phases,
where `r` below is the index of the micro-step inside the block:

* `A`: `r < K` — move `K` cells left (writing back what is scanned);
* `B`: `K ≤ r ≤ 3 * K` — sweep `2 * K` cells right, recording the `2 * K + 1`
  scanned symbols into the finite control (this is the window read);
* `C`: `3 * K + 1 ≤ r ≤ 5 * K + 1` — write the new window while sweeping back
  left, ending on the cell `K` to the left of the original head; the control
  state is updated on the last of these micro-steps, which also latches the head
  displacements;
* `D`: `5 * K + 2 ≤ r ≤ 7 * K + 1` — move right to the target displacement,
  padding with `stay`s.

The input symbol is visible only on micro-step `r = 0`, so it is latched into the
control there. -/

/-- Micro-steps per local step. -/
def cnt (K : ℕ) : ℕ := 7 * K + 2

theorem cnt_pos (K : ℕ) : 0 < cnt K := by simp [cnt]

theorem cnt_split (K : ℕ) : cnt K = K + (2 * K + 1) + (2 * K + 1) + 2 * K := by
  simp [cnt]; omega

/-- The control of the realization: the local state, the latched input symbol,
the window buffer and the latched head displacements (as `d + K`). -/
abbrev Ctrl (Terminal Q Γ : Type) (t K : ℕ) : Type :=
  Q × Option Terminal × (Fin t → Window Γ K) × (Fin t → Fin (2 * K + 1))

namespace LocalStep

variable {Terminal Q : Type} {t K : ℕ}

/-- The latched input symbol after micro-step `r`. -/
def stepIn (r : ℕ) (inp : Option Terminal) (ctrl : Ctrl Terminal Q Γ t K) :
    Option Terminal := if r = 0 then inp else ctrl.2.1

/-- The local step's verdict, computed from the control alone. -/
def stepRes (L : LocalStep Terminal Q Γ t K) (r : ℕ) (inp : Option Terminal)
    (ctrl : Ctrl Terminal Q Γ t K) : Q × (Fin t → Window Γ K × ℤ) :=
  L.next ctrl.1 (stepIn r inp ctrl) ctrl.2.2.1

/-- The window buffer after micro-step `r`. -/
def stepBuf (r : ℕ) (ctrl : Ctrl Terminal Q Γ t K) (s : Fin t → Γ) :
    Fin t → Window Γ K :=
  if K ≤ r ∧ r ≤ 3 * K then
    fun j z => if (z : ℕ) = r - K then s j else ctrl.2.2.1 j z
  else ctrl.2.2.1

/-- The local state after micro-step `r`. -/
def stepQ (L : LocalStep Terminal Q Γ t K) (r : ℕ) (inp : Option Terminal)
    (ctrl : Ctrl Terminal Q Γ t K) : Q :=
  if r = 5 * K + 1 then (L.stepRes r inp ctrl).1 else ctrl.1

/-- The latched displacements after micro-step `r`. -/
def stepDv (L : LocalStep Terminal Q Γ t K) (r : ℕ) (inp : Option Terminal)
    (ctrl : Ctrl Terminal Q Γ t K) : Fin t → Fin (2 * K + 1) :=
  if r = 5 * K + 1 then fun j => idx K (((L.stepRes r inp ctrl).2 j).2 + (K : ℤ)).toNat
  else ctrl.2.2.2

/-- The tape actions of micro-step `r`. -/
def stepAct (L : LocalStep Terminal Q Γ t K) (r : ℕ) (inp : Option Terminal)
    (ctrl : Ctrl Terminal Q Γ t K) (s : Fin t → Γ) : Fin t → Γ × Move :=
  fun j =>
    if r < K then (s j, Move.left)
    else if r ≤ 3 * K then (s j, if r = 3 * K then Move.stay else Move.right)
    else if r ≤ 5 * K + 1 then
      (((L.stepRes r inp ctrl).2 j).1 (idx K (5 * K + 1 - r)),
        if r = 5 * K + 1 then Move.stay else Move.left)
    else (s j, if r - (5 * K + 2) < ((ctrl.2.2.2 j : ℕ)) then Move.right else Move.stay)

/-- The micro-transition of the realization, at in-block index `r`. -/
def mstep (L : LocalStep Terminal Q Γ t K) (r : ℕ) (inp : Option Terminal)
    (ctrl : Ctrl Terminal Q Γ t K) (s : Fin t → Γ) :
    Ctrl Terminal Q Γ t K × (Fin t → Γ × Move) :=
  ((L.stepQ r inp ctrl, stepIn r inp ctrl, stepBuf r ctrl s, L.stepDv r inp ctrl),
    L.stepAct r inp ctrl s)

/-- One micro-step of the realization on structured tapes. -/
def mbody (L : LocalStep Terminal Q Γ t K) (blank : Γ) (r : ℕ) (inp : Option Terminal)
    (x : Ctrl Terminal Q Γ t K × (Fin t → STape Γ)) :
    Ctrl Terminal Q Γ t K × (Fin t → STape Γ) :=
  let out := L.mstep r inp x.1 (fun j => (x.2 j).focus)
  (out.1, fun j => (x.2 j).applyAction blank (out.2 j))

/-- `runB r m` runs `m` micro-steps, at in-block indices `r, r+1, …, r+m-1`.
Only the step with `r = 0` inspects `inp`. -/
def runB (L : LocalStep Terminal Q Γ t K) (blank : Γ) (inp : Option Terminal) :
    ℕ → ℕ → (Ctrl Terminal Q Γ t K × (Fin t → STape Γ)) →
      Ctrl Terminal Q Γ t K × (Fin t → STape Γ)
  | _, 0, x => x
  | r, (m + 1), x => L.runB blank inp (r + 1) m (L.mbody blank r inp x)

@[simp] theorem runB_zero (L : LocalStep Terminal Q Γ t K) (blank : Γ)
    (inp : Option Terminal) (r : ℕ) (x : Ctrl Terminal Q Γ t K × (Fin t → STape Γ)) :
    L.runB blank inp r 0 x = x := rfl

theorem runB_succ (L : LocalStep Terminal Q Γ t K) (blank : Γ) (inp : Option Terminal)
    (r m : ℕ) (x : Ctrl Terminal Q Γ t K × (Fin t → STape Γ)) :
    L.runB blank inp r (m + 1) x = L.runB blank inp (r + 1) m (L.mbody blank r inp x) := rfl

theorem runB_add (L : LocalStep Terminal Q Γ t K) (blank : Γ) (inp : Option Terminal)
    (r m₁ m₂ : ℕ) (x : Ctrl Terminal Q Γ t K × (Fin t → STape Γ)) :
    L.runB blank inp r (m₁ + m₂) x
      = L.runB blank inp (r + m₁) m₂ (L.runB blank inp r m₁ x) := by
  induction m₁ generalizing r x with
  | zero => simp
  | succ n ih =>
      rw [show n + 1 + m₂ = (n + m₂) + 1 from by omega, runB_succ, ih,
        show r + (n + 1) = r + 1 + n from by omega, runB_succ]

/-! ### Phase A: `K` moves left -/

theorem phaseA (L : LocalStep Terminal Q Γ t K) (blank : Γ) (inp : Option Terminal) :
    ∀ (i r : ℕ) (x : Ctrl Terminal Q Γ t K × (Fin t → STape Γ)), r + i = K →
      L.runB blank inp r i x
        = ((x.1.1, (if r = 0 ∧ 0 < i then inp else x.1.2.1), x.1.2.2.1, x.1.2.2.2),
            fun j => (mvL blank)^[i] (x.2 j)) := by
  intro i
  induction i with
  | zero => intro r x _; simp
  | succ n ih =>
      intro r x hr
      have hrK : r < K := by omega
      have hstep : L.mbody blank r inp x
          = ((x.1.1, (if r = 0 then inp else x.1.2.1), x.1.2.2.1, x.1.2.2.2),
              fun j => mvL blank (x.2 j)) := by
        obtain ⟨⟨q, ab, buf, dv⟩, T⟩ := x
        simp only [mbody, mstep, stepQ, stepDv, stepBuf, stepAct, stepIn, mvL,
          if_neg (by omega : ¬ r = 5 * K + 1),
          if_neg (by omega : ¬ (K ≤ r ∧ r ≤ 3 * K)), if_pos hrK]
      rw [runB_succ, hstep, ih (r + 1) _ (by omega)]
      simp only [Function.iterate_succ_apply]
      by_cases h : r = 0
      · simp [h]
      · simp [h]

/-! ### Phase B: the read sweep -/

theorem phaseB (L : LocalStep Terminal Q Γ t K) (blank : Γ) (inp : Option Terminal) :
    ∀ (i r : ℕ) (x : Ctrl Terminal Q Γ t K × (Fin t → STape Γ)), K ≤ r → r + i = 3 * K + 1 →
      L.runB blank inp r i x
        = ((x.1.1, (if r = 0 ∧ 0 < i then inp else x.1.2.1),
            (fun (j : Fin t) (z : Fin (2 * K + 1)) => if r - K ≤ (z : ℕ)
              then ((mvR blank)^[(z : ℕ) - (r - K)] (x.2 j)).focus else x.1.2.2.1 j z),
            x.1.2.2.2),
            fun j => (mvR blank)^[i - 1] (x.2 j)) := by
  intro i
  induction i with
  | zero =>
      intro r x _ hr
      obtain ⟨⟨q, ab, buf, dv⟩, T⟩ := x
      have e : (fun (j : Fin t) (z : Fin (2 * K + 1)) =>
            if r - K ≤ (z : ℕ) then ((mvR blank)^[(z : ℕ) - (r - K)] (T j)).focus else buf j z)
          = buf := by
        funext j z
        have hz := z.isLt
        rw [if_neg (by omega)]
      rw [runB_zero, e]
      simp
  | succ n ih =>
      intro r x hKr hr
      obtain ⟨⟨q, ab, buf, dv⟩, T⟩ := x
      have hr3 : r ≤ 3 * K := by omega
      by_cases h3 : r = 3 * K
      · have hn : n = 0 := by omega
        subst hn
        have hstep : L.mbody blank r inp ((q, ab, buf, dv), T)
            = ((q, (if r = 0 then inp else ab),
                (fun (j : Fin t) (z : Fin (2 * K + 1)) =>
                  if (z : ℕ) = r - K then (T j).focus else buf j z), dv), T) := by
          simp only [mbody, mstep, stepQ, stepDv, stepBuf, stepAct, stepIn,
            if_neg (by omega : ¬ r = 5 * K + 1), if_pos (⟨hKr, hr3⟩ : K ≤ r ∧ r ≤ 3 * K),
            if_neg (by omega : ¬ r < K), if_pos hr3, if_pos h3, applyAction_stay_self]
        rw [runB_succ, hstep, runB_zero]
        have e1 : (fun (j : Fin t) (z : Fin (2 * K + 1)) =>
              if (z : ℕ) = r - K then (T j).focus else buf j z)
            = (fun (j : Fin t) (z : Fin (2 * K + 1)) =>
              if r - K ≤ (z : ℕ) then ((mvR blank)^[(z : ℕ) - (r - K)] (T j)).focus
              else buf j z) := by
          funext j z
          have hz := z.isLt
          by_cases hze : (z : ℕ) = r - K
          · rw [if_pos hze, if_pos (by omega : r - K ≤ (z : ℕ)), hze, Nat.sub_self]
            simp
          · rw [if_neg hze, if_neg (by omega : ¬ r - K ≤ (z : ℕ))]
        rw [e1]
        simp
      · have hn : 0 < n := by omega
        have hstep : L.mbody blank r inp ((q, ab, buf, dv), T)
            = ((q, (if r = 0 then inp else ab),
                (fun (j : Fin t) (z : Fin (2 * K + 1)) =>
                  if (z : ℕ) = r - K then (T j).focus else buf j z), dv),
                fun j => mvR blank (T j)) := by
          simp only [mbody, mstep, stepQ, stepDv, stepBuf, stepAct, stepIn, mvR,
            if_neg (by omega : ¬ r = 5 * K + 1), if_pos (⟨hKr, hr3⟩ : K ≤ r ∧ r ≤ 3 * K),
            if_neg (by omega : ¬ r < K), if_pos hr3, if_neg h3]
        rw [runB_succ, hstep, ih (r + 1) _ (by omega) (by omega)]
        have e1 : (fun (j : Fin t) (z : Fin (2 * K + 1)) =>
              if r + 1 - K ≤ (z : ℕ)
                then ((mvR blank)^[(z : ℕ) - (r + 1 - K)] (mvR blank (T j))).focus
                else if (z : ℕ) = r - K then (T j).focus else buf j z)
            = (fun (j : Fin t) (z : Fin (2 * K + 1)) =>
              if r - K ≤ (z : ℕ) then ((mvR blank)^[(z : ℕ) - (r - K)] (T j)).focus
              else buf j z) := by
          funext j z
          have hz := z.isLt
          by_cases hz1 : r + 1 - K ≤ (z : ℕ)
          · rw [if_pos hz1, if_pos (by omega : r - K ≤ (z : ℕ)),
              show (z : ℕ) - (r - K) = ((z : ℕ) - (r + 1 - K)) + 1 from by omega,
              Function.iterate_succ_apply]
          · rw [if_neg hz1]
            by_cases hz2 : (z : ℕ) = r - K
            · rw [if_pos hz2, if_pos (by omega : r - K ≤ (z : ℕ)), hz2, Nat.sub_self]
              simp
            · rw [if_neg hz2, if_neg (by omega : ¬ r - K ≤ (z : ℕ))]
        have e2 : (fun j : Fin t => (mvR blank)^[n - 1] (mvR blank (T j)))
            = (fun j : Fin t => (mvR blank)^[n + 1 - 1] (T j)) := by
          funext j
          rw [show n + 1 - 1 = (n - 1) + 1 from by omega, Function.iterate_succ_apply]
        rw [e1, e2]
        simp [hn]

/-! ### Phase C: the write sweep -/

theorem phaseC (L : LocalStep Terminal Q Γ t K) (blank : Γ) (inp : Option Terminal) :
    ∀ (i r : ℕ) (q : Q) (ab : Option Terminal) (buf : Fin t → Window Γ K)
      (dv : Fin t → Fin (2 * K + 1)) (T : Fin t → STape Γ),
      3 * K + 1 ≤ r → r + i = 5 * K + 2 → 0 < i →
      L.runB blank inp r i ((q, ab, buf, dv), T)
        = (((L.next q ab buf).1, ab, buf,
            fun j => idx K ((((L.next q ab buf).2 j).2 + (K : ℤ)).toNat)),
            fun j => cPhase blank (fun z => ((L.next q ab buf).2 j).1 (idx K z)) i (T j)) := by
  intro i
  induction i with
  | zero => intro _ _ _ _ _ _ _ _ h; exact absurd h (by omega)
  | succ c ih =>
      intro r q ab buf dv T hr1 hr2 _
      have hnb : ¬ (K ≤ r ∧ r ≤ 3 * K) := by omega
      have hnA : ¬ r < K := by omega
      have hnB : ¬ r ≤ 3 * K := by omega
      have hC : r ≤ 5 * K + 1 := by omega
      have hin : stepIn r inp ((q, ab, buf, dv) : Ctrl Terminal Q Γ t K) = ab := by
        rw [stepIn, if_neg (by omega : ¬ r = 0)]
      have hres : L.stepRes r inp ((q, ab, buf, dv) : Ctrl Terminal Q Γ t K)
          = L.next q ab buf := by rw [stepRes, hin]
      rcases Nat.eq_or_lt_of_le (show 1 ≤ c + 1 from by omega) with hc | hc
      · -- last micro-step of the phase: `r = 5 * K + 1`
        have hc0 : c = 0 := by omega
        have hr : r = 5 * K + 1 := by omega
        subst hc0
        have hstep : L.mbody blank r inp ((q, ab, buf, dv), T)
            = (((L.next q ab buf).1, ab, buf,
                fun j => idx K ((((L.next q ab buf).2 j).2 + (K : ℤ)).toNat)),
                fun j => (T j).applyAction blank
                  (((L.next q ab buf).2 j).1 (idx K 0), Move.stay)) := by
          simp only [mbody, mstep, stepQ, stepDv, stepBuf, stepAct, hres, hin,
            if_pos hr, if_neg hnb, if_neg hnA, if_neg hnB, if_pos hC,
            show 5 * K + 1 - r = 0 from by omega]
        rw [runB_succ, hstep, runB_zero]
        rfl
      · -- an inner micro-step
        have hc1 : 0 < c := by omega
        have hrne : ¬ r = 5 * K + 1 := by omega
        have hstep : L.mbody blank r inp ((q, ab, buf, dv), T)
            = ((q, ab, buf, dv),
                fun j => (T j).applyAction blank
                  (((L.next q ab buf).2 j).1 (idx K c), Move.left)) := by
          simp only [mbody, mstep, stepQ, stepDv, stepBuf, stepAct, hres, hin,
            if_neg hrne, if_neg hnb, if_neg hnA, if_neg hnB, if_pos hC,
            show 5 * K + 1 - r = c from by omega]
        rw [runB_succ, hstep, ih (r + 1) q ab buf dv _ (by omega) (by omega) (by omega)]
        refine congrArg _ ?_
        funext j
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        rfl

/-! ### Phase D: repositioning -/

theorem phaseD (L : LocalStep Terminal Q Γ t K) (blank : Γ) (inp : Option Terminal) :
    ∀ (i r : ℕ) (q : Q) (ab : Option Terminal) (buf : Fin t → Window Γ K)
      (dv : Fin t → Fin (2 * K + 1)) (T : Fin t → STape Γ),
      5 * K + 2 ≤ r → r + i = 7 * K + 2 →
      L.runB blank inp r i ((q, ab, buf, dv), T)
        = ((q, ab, buf, dv),
            fun j => (mvR blank)^[((dv j : ℕ)) - (r - (5 * K + 2))] (T j)) := by
  intro i
  induction i with
  | zero =>
      intro r q ab buf dv T hr1 hr2
      rw [runB_zero]
      have e : (fun j => (mvR blank)^[((dv j : ℕ)) - (r - (5 * K + 2))] (T j)) = T := by
        funext j
        have := (dv j).isLt
        rw [show ((dv j : ℕ)) - (r - (5 * K + 2)) = 0 from by omega]
        rfl
      rw [e]
  | succ c ih =>
      intro r q ab buf dv T hr1 hr2
      have hstep : L.mbody blank r inp ((q, ab, buf, dv), T)
          = ((q, ab, buf, dv),
              fun j => (T j).applyAction blank ((T j).focus,
                if r - (5 * K + 2) < ((dv j : ℕ)) then Move.right else Move.stay)) := by
        simp only [mbody, mstep, stepQ, stepDv, stepBuf, stepAct, stepIn,
          if_neg (by omega : ¬ r = 5 * K + 1), if_neg (by omega : ¬ (K ≤ r ∧ r ≤ 3 * K)),
          if_neg (by omega : ¬ r < K), if_neg (by omega : ¬ r ≤ 3 * K),
          if_neg (by omega : ¬ r ≤ 5 * K + 1), if_neg (by omega : ¬ r = 0)]
      rw [runB_succ, hstep, ih (r + 1) q ab buf dv _ (by omega) (by omega)]
      refine congrArg _ ?_
      funext j
      by_cases h : r - (5 * K + 2) < ((dv j : ℕ))
      · rw [if_pos h,
          show (T j).applyAction blank ((T j).focus, Move.right) = mvR blank (T j) from rfl,
          show ((dv j : ℕ)) - (r - (5 * K + 2))
              = (((dv j : ℕ)) - (r + 1 - (5 * K + 2))) + 1 from by omega,
          Function.iterate_succ_apply]
      · rw [if_neg h, applyAction_stay_self,
          show ((dv j : ℕ)) - (r - (5 * K + 2)) = 0 from by omega,
          show ((dv j : ℕ)) - (r + 1 - (5 * K + 2)) = 0 from by omega]


/-! ### One block of `cnt K` micro-steps is one local step -/

theorem runB_block (L : LocalStep Terminal Q Γ t K) (blank : Γ) (inp : Option Terminal)
    (q : Q) (ab : Option Terminal) (buf : Fin t → Window Γ K)
    (dv : Fin t → Fin (2 * K + 1)) (T : Fin t → STape Γ) :
    L.runB blank inp 0 (cnt K) ((q, ab, buf, dv), T)
      = (((L.next q inp (fun j => readWin blank K (T j))).1, inp,
          (fun j => readWin blank K (T j)),
          (fun j => idx K ((((L.next q inp (fun j => readWin blank K (T j))).2 j).2
            + (K : ℤ)).toNat))),
          fun j => sweep blank K (T j)
            (((L.next q inp (fun j => readWin blank K (T j))).2 j).1)
            (((L.next q inp (fun j => readWin blank K (T j))).2 j).2)) := by
  rw [cnt_split,
    runB_add L blank inp 0 (K + (2 * K + 1) + (2 * K + 1)) (2 * K),
    runB_add L blank inp 0 (K + (2 * K + 1)) (2 * K + 1),
    runB_add L blank inp 0 K (2 * K + 1),
    phaseA L blank inp K 0 _ (by omega)]
  rw [Nat.zero_add K, Nat.zero_add (K + (2 * K + 1)),
    Nat.zero_add (K + (2 * K + 1) + (2 * K + 1)), phaseB L blank inp (2 * K + 1) K _ (le_refl K) (by omega)]
  dsimp only
  have hab : (if K = 0 ∧ 0 < 2 * K + 1 then inp else (if 0 = 0 ∧ 0 < K then inp else ab))
      = inp := by
    by_cases hK : K = 0 <;> simp [hK]
  have hbuf : (fun (j : Fin t) (z : Fin (2 * K + 1)) =>
        if K - K ≤ (z : ℕ)
          then ((mvR blank)^[(z : ℕ) - (K - K)] ((mvL blank)^[K] (T j))).focus
          else buf j z)
      = fun j => readWin blank K (T j) := by
    funext j z
    rw [if_pos (by omega)]
    simp [readWin]
  rw [hab, hbuf, show K + (2 * K + 1) = 3 * K + 1 from by omega,
    phaseC L blank inp (2 * K + 1) (3 * K + 1) q inp _ _ _ (by omega) (by omega) (by omega),
    show 3 * K + 1 + (2 * K + 1) = 5 * K + 2 from by omega,
    phaseD L blank inp (2 * K) (5 * K + 2) _ _ _ _ _ (by omega) (by omega)]
  refine congrArg _ ?_
  funext j
  have hd := L.disp_le q inp (fun j => readWin blank K (T j)) j
  have hd1 : -(K : ℤ) ≤ ((L.next q inp (fun j => readWin blank K (T j))).2 j).2 :=
    neg_le_of_abs_le hd
  have hd2 : ((L.next q inp (fun j => readWin blank K (T j))).2 j).2 ≤ (K : ℤ) :=
    le_of_abs_le hd
  have hle : ((((L.next q inp (fun j => readWin blank K (T j))).2 j).2 + (K : ℤ)).toNat)
      ≤ 2 * K := by omega
  rw [sweep, show 5 * K + 2 - (5 * K + 2) = 0 from by omega, Nat.sub_zero,
    idx_val hle, show 2 * K + 1 - 1 = 2 * K from by omega]


/-! ### Independence of the input symbol away from the block boundary -/

theorem mbody_inp_irrel (L : LocalStep Terminal Q Γ t K) (blank : Γ)
    (inp inp' : Option Terminal) (r : ℕ) (hr : 0 < r)
    (x : Ctrl Terminal Q Γ t K × (Fin t → STape Γ)) :
    L.mbody blank r inp x = L.mbody blank r inp' x := by
  have h : stepIn r inp x.1 = stepIn r inp' x.1 := by
    rw [stepIn, stepIn, if_neg (by omega), if_neg (by omega)]
  simp only [mbody, mstep, stepQ, stepDv, stepBuf, stepAct, stepRes, h]

theorem runB_inp_irrel (L : LocalStep Terminal Q Γ t K) (blank : Γ)
    (inp inp' : Option Terminal) :
    ∀ (m r : ℕ), 0 < r → ∀ (x : Ctrl Terminal Q Γ t K × (Fin t → STape Γ)),
      L.runB blank inp r m x = L.runB blank inp' r m x := by
  intro m
  induction m with
  | zero => intro r _ x; rfl
  | succ c ih =>
      intro r hr x
      rw [runB_succ, runB_succ, mbody_inp_irrel L blank inp inp' r hr x,
        ih (r + 1) (by omega)]

/-! ### From `phaseRun` to `runB` -/

/-- The control type of the realization carries the phase counter, added by
`ofPhases`. -/
def body (L : LocalStep Terminal Q Γ t K) (n : ℕ) :
    PhaseBody Terminal (Ctrl Terminal Q Γ t K) Γ t (n * cnt K) :=
  fun ctrl a p s => L.mstep ((p : ℕ) % cnt K) a ctrl s

theorem phaseRun_append {B : ℕ} (blank : Γ)
    (bd : PhaseBody Terminal (Ctrl Terminal Q Γ t K) Γ t B)
    (l₁ l₂ : List (Option Terminal)) (p : Fin B)
    (x : Ctrl Terminal Q Γ t K × (Fin t → STape Γ)) :
    phaseRun blank bd (l₁ ++ l₂) p x
      = phaseRun blank bd l₂ (nextPhase^[l₁.length] p) (phaseRun blank bd l₁ p x) := by
  induction l₁ generalizing p x with
  | nil => simp
  | cons a l ih => simp [ih, Function.iterate_succ_apply]

theorem nextPhase_iter {B : ℕ} : ∀ (m j : ℕ) (hj : j < B) (_ : j + m < B),
    (nextPhase^[m] (⟨j, hj⟩ : Fin B)).val = j + m := by
  intro m
  induction m with
  | zero => intro j hj _; rfl
  | succ c ih =>
      intro j hj h
      have hv : (nextPhase^[c] (⟨j, hj⟩ : Fin B)).val = j + c := ih j hj (by omega)
      rw [Function.iterate_succ_apply', nextPhase,
        dif_pos (by omega : (nextPhase^[c] (⟨j, hj⟩ : Fin B)).val + 1 < B)]
      simp only [hv]
      omega

theorem nextPhase_iter' {B : ℕ} (m j : ℕ) (hj : j < B) (h : j + m < B) :
    nextPhase^[m] (⟨j, hj⟩ : Fin B) = ⟨j + m, h⟩ :=
  Fin.ext (nextPhase_iter m j hj h)

theorem phaseRun_eq_runB (L : LocalStep Terminal Q Γ t K) (blank : Γ) (n : ℕ) :
    ∀ (m j : ℕ) (hj : j < n * cnt K) (x : Ctrl Terminal Q Γ t K × (Fin t → STape Γ)),
      j % cnt K + m ≤ cnt K → j + m ≤ n * cnt K →
      phaseRun blank (L.body n) (List.replicate m none) ⟨j, hj⟩ x
        = L.runB blank none (j % cnt K) m x := by
  intro m
  induction m with
  | zero => intro j hj x _ _; rfl
  | succ c ih =>
      intro j hj x h1 h2
      have hbody : bodyStep blank (L.body n) (⟨j, hj⟩ : Fin (n * cnt K)) none x
          = L.mbody blank (j % cnt K) none x := rfl
      rw [List.replicate_succ, phaseRun_cons, hbody, runB_succ]
      rcases Nat.eq_zero_or_pos c with hc | hc
      · subst hc; simp
      · have hjB : j + 1 < n * cnt K := by omega
        have hcnt : 0 < cnt K := cnt_pos K
        have hlt : j % cnt K + 1 < cnt K := by omega
        have hmod : (j + 1) % cnt K = j % cnt K + 1 := by
          rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < cnt K),
            Nat.mod_eq_of_lt hlt]
        have hnext : nextPhase (⟨j, hj⟩ : Fin (n * cnt K)) = ⟨j + 1, hjB⟩ := by
          rw [nextPhase, dif_pos (by omega : ((⟨j, hj⟩ : Fin (n * cnt K)) : ℕ) + 1 < n * cnt K)]
        rw [hnext, ih (j + 1) hjB _ (by rw [hmod]; omega) (by omega), hmod]

/-! ### Decoding -/

/-- Forget the bookkeeping: the local state and the tapes. -/
def decode (y : Ctrl Terminal Q Γ t K × (Fin t → STape Γ)) : Q × (Fin t → STape Γ) :=
  (y.1.1, y.2)

theorem decode_runB_block (L : LocalStep Terminal Q Γ t K) (blank : Γ)
    (inp : Option Terminal) (y : Ctrl Terminal Q Γ t K × (Fin t → STape Γ)) :
    decode (L.runB blank inp 0 (cnt K) y) = L.apply blank (decode y) inp := by
  obtain ⟨⟨q, ab, buf, dv⟩, T⟩ := y
  rw [runB_block]
  rfl

theorem decode_blocks (L : LocalStep Terminal Q Γ t K) (blank : Γ) :
    ∀ (k : ℕ) (y : Ctrl Terminal Q Γ t K × (Fin t → STape Γ)),
      decode ((fun y => L.runB blank none 0 (cnt K) y)^[k] y)
        = (fun z => L.apply blank z none)^[k] (decode y) := by
  intro k
  induction k with
  | zero => intro y; rfl
  | succ c ih =>
      intro y
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih,
        decode_runB_block]

theorem phaseRun_blocks (L : LocalStep Terminal Q Γ t K) (blank : Γ) (n : ℕ) :
    ∀ (k j : ℕ) (hj : j < n * cnt K) (x : Ctrl Terminal Q Γ t K × (Fin t → STape Γ)),
      j % cnt K = 0 → j + k * cnt K ≤ n * cnt K →
      phaseRun blank (L.body n) (List.replicate (k * cnt K) none) ⟨j, hj⟩ x
        = (fun y => L.runB blank none 0 (cnt K) y)^[k] x := by
  intro k
  induction k with
  | zero => intro j hj x _ _; simp
  | succ c ih =>
      intro j hj x h0 h2
      have hcnt : 0 < cnt K := cnt_pos K
      have hsplit : (c + 1) * cnt K = cnt K + c * cnt K := by ring
      rw [hsplit, List.replicate_add, phaseRun_append, List.length_replicate,
        phaseRun_eq_runB L blank n (cnt K) j hj x (by omega) (by omega), h0]
      rcases Nat.eq_zero_or_pos c with hc | hc
      · subst hc
        simp
      · have hc2 : cnt K ≤ c * cnt K := Nat.le_mul_of_pos_left _ hc
        have hjB : j + cnt K < n * cnt K := by omega
        rw [nextPhase_iter' (cnt K) j hj hjB,
          ih (j + cnt K) hjB _ (by rw [Nat.add_mod_right]; exact h0) (by omega),
          Function.iterate_succ_apply]
      

/-! ### One round -/

theorem phaseRun_round (L : LocalStep Terminal Q Γ t K) (blank : Γ) (n : ℕ) (hn : 0 < n)
    (a : Terminal) (x : Ctrl Terminal Q Γ t K × (Fin t → STape Γ))
    (hB : 0 < n * cnt K) :
    phaseRun blank (L.body n) (MultiStepMachine.roundInputs (n * cnt K) a) ⟨0, hB⟩ x
      = (fun y => L.runB blank none 0 (cnt K) y)^[n - 1]
          (L.runB blank (some a) 0 (cnt K) x) := by
  have hcnt : 2 ≤ cnt K := by simp only [cnt]; omega
  have hnc : cnt K ≤ n * cnt K := Nat.le_mul_of_pos_left _ hn
  have h1B : 1 < n * cnt K := by omega
  have hbody : bodyStep blank (L.body n) (⟨0, hB⟩ : Fin (n * cnt K)) (some a) x
      = L.mbody blank (0 % cnt K) (some a) x := rfl
  rw [Nat.zero_mod] at hbody
  have hnext : nextPhase (⟨0, hB⟩ : Fin (n * cnt K)) = ⟨1, h1B⟩ := by
    have h := nextPhase_iter' (B := n * cnt K) 1 0 hB (by omega)
    simpa using h
  have hlen : n * cnt K - 1 = (cnt K - 1) + (n - 1) * cnt K := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : (m + 1) * cnt K = cnt K + m * cnt K := by ring
    simp only [Nat.add_sub_cancel]
    omega
  have hfirst : L.runB blank (some a) 0 (cnt K) x
      = L.runB blank (some a) 1 (cnt K - 1) (L.mbody blank 0 (some a) x) := by
    conv_lhs => rw [show cnt K = (cnt K - 1) + 1 from by omega]
    rw [runB_succ]
  rw [MultiStepMachine.roundInputs, phaseRun_cons, hbody, hnext, hlen,
    List.replicate_add, phaseRun_append, List.length_replicate,
    phaseRun_eq_runB L blank n (cnt K - 1) 1 h1B _
      (by rw [Nat.mod_eq_of_lt (by omega)]; omega) (by omega),
    Nat.mod_eq_of_lt (by omega : 1 < cnt K),
    runB_inp_irrel L blank none (some a) (cnt K - 1) 1 (by omega), hfirst]
  rcases Nat.eq_or_lt_of_le hn with h1 | h2
  · rw [show n - 1 = 0 from by omega]
    simp
  · have hcB : cnt K < n * cnt K := by
      have h2' : 2 * cnt K ≤ n * cnt K := Nat.mul_le_mul_right _ (by omega)
      omega
    have hph : nextPhase^[cnt K - 1] (⟨1, h1B⟩ : Fin (n * cnt K)) = ⟨cnt K, hcB⟩ := by
      rw [nextPhase_iter' (cnt K - 1) 1 h1B (by omega)]
      exact Fin.ext (show 1 + (cnt K - 1) = cnt K from by omega)
    rw [hph, phaseRun_blocks L blank n (n - 1) (cnt K) hcB _
        (Nat.mod_self (cnt K)) (by omega)]

/-- One round of the realization, abstractly: `n` blocks, the first of which sees
the input symbol. -/
def roundStep (L : LocalStep Terminal Q Γ t K) (blank : Γ) (n : ℕ)
    (y : Ctrl Terminal Q Γ t K × (Fin t → STape Γ)) (a : Terminal) :
    Ctrl Terminal Q Γ t K × (Fin t → STape Γ) :=
  (fun z => L.runB blank none 0 (cnt K) z)^[n - 1] (L.runB blank (some a) 0 (cnt K) y)

theorem decode_roundStep (L : LocalStep Terminal Q Γ t K) (blank : Γ) (n : ℕ)
    (y : Ctrl Terminal Q Γ t K × (Fin t → STape Γ)) (a : Terminal) :
    decode (L.roundStep blank n y a)
      = (fun z => L.apply blank z none)^[n - 1] (L.apply blank (decode y) (some a)) := by
  rw [roundStep, decode_blocks, decode_runB_block]

/-! ### The realized machine -/

/-- `n` local steps for one input symbol: the symbol is seen by the first one
only. -/
def applyN (L : LocalStep Terminal Q Γ t K) (blank : Γ) (n : ℕ)
    (z : Q × (Fin t → STape Γ)) (a : Terminal) : Q × (Fin t → STape Γ) :=
  (fun y => L.apply blank y none)^[n - 1] (L.apply blank z (some a))

/-- `n` local steps per input symbol, realized on a strictly real-time
structured machine with `n * cnt K` micro-steps per input symbol. -/
def realize [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    [Fintype Terminal] [DecidableEq Terminal]
    (L : LocalStep Terminal Q Γ t K) (blank : Γ) (init : Q) (accept : Q → Bool)
    (n : ℕ) (htape : 0 < t) (hn : 0 < n) :
    StructuredMachine Terminal (Ctrl Terminal Q Γ t K × Fin (n * cnt K)) Γ t (n * cnt K) :=
  ofPhases htape (Nat.mul_pos hn (cnt_pos K)) blank
    (init, none, (fun _ _ => blank), (fun _ => idx K 0)) (fun c => accept c.1) (L.body n)

theorem realize_sRound_shape [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    [Fintype Terminal] [DecidableEq Terminal]
    (L : LocalStep Terminal Q Γ t K) (blank : Γ) (init : Q) (accept : Q → Bool)
    (n : ℕ) (htape : 0 < t) (hn : 0 < n)
    (ctrl : Ctrl Terminal Q Γ t K) (T : Fin t → STape Γ) (a : Terminal) :
    (L.realize blank init accept n htape hn).sRound
        { state := (ctrl, ⟨0, Nat.mul_pos hn (cnt_pos K)⟩), tape := T } a
      = { state := ((L.roundStep blank n (ctrl, T) a).1, ⟨0, Nat.mul_pos hn (cnt_pos K)⟩),
          tape := (L.roundStep blank n (ctrl, T) a).2 } := by
  rw [realize, ofPhases_round, phaseRun_round L blank n hn a (ctrl, T), roundStep]

theorem realize_foldl [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    [Fintype Terminal] [DecidableEq Terminal]
    (L : LocalStep Terminal Q Γ t K) (blank : Γ) (init : Q) (accept : Q → Bool)
    (n : ℕ) (htape : 0 < t) (hn : 0 < n) :
    ∀ (w : List Terminal) (ctrl : Ctrl Terminal Q Γ t K) (T : Fin t → STape Γ),
      (((w.foldl (L.realize blank init accept n htape hn).sRound
            { state := (ctrl, ⟨0, Nat.mul_pos hn (cnt_pos K)⟩), tape := T }).state.1.1),
        ((w.foldl (L.realize blank init accept n htape hn).sRound
            { state := (ctrl, ⟨0, Nat.mul_pos hn (cnt_pos K)⟩), tape := T }).tape))
        = w.foldl (L.applyN blank n) (ctrl.1, T) := by
  intro w
  induction w with
  | nil => intro ctrl T; rfl
  | cons a rest ih =>
      intro ctrl T
      rw [List.foldl_cons, List.foldl_cons, realize_sRound_shape,
        ih (L.roundStep blank n (ctrl, T) a).1 (L.roundStep blank n (ctrl, T) a).2]
      exact congrArg (rest.foldl (L.applyN blank n)) (decode_roundStep L blank n (ctrl, T) a)

/-- **Simulation.**  The run of the realized machine decodes to `n` local steps
per input symbol, the input symbol being fed to the first of them. -/
theorem realize_srun [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    [Fintype Terminal] [DecidableEq Terminal]
    (L : LocalStep Terminal Q Γ t K) (blank : Γ) (init : Q) (accept : Q → Bool)
    (n : ℕ) (htape : 0 < t) (hn : 0 < n) (w : List Terminal) :
    ((((L.realize blank init accept n htape hn).srun w).state.1.1),
      (((L.realize blank init accept n htape hn).srun w).tape))
      = w.foldl (L.applyN blank n) (init, fun _ => STape.blankTape blank) :=
  realize_foldl L blank init accept n htape hn w
    (init, none, (fun _ _ => blank), (fun _ => idx K 0)) (fun _ => STape.blankTape blank)

/-- **Acceptance.**  The realized machine accepts exactly when the local state
reached by the local steps is accepting. -/
theorem realize_SAccepts [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    [Fintype Terminal] [DecidableEq Terminal]
    (L : LocalStep Terminal Q Γ t K) (blank : Γ) (init : Q) (accept : Q → Bool)
    (n : ℕ) (htape : 0 < t) (hn : 0 < n) (w : List Terminal) :
    (L.realize blank init accept n htape hn).SAccepts w
      ↔ accept (w.foldl (L.applyN blank n)
          (init, fun _ => STape.blankTape blank)).1 = true := by
  have h : (((L.realize blank init accept n htape hn).srun w).state.1.1)
      = (w.foldl (L.applyN blank n) (init, fun _ => STape.blankTape blank)).1 :=
    congrArg Prod.fst (realize_srun L blank init accept n htape hn w)
  show accept (((L.realize blank init accept n htape hn).srun w).state.1.1) = true ↔ _
  rw [h]


end LocalStep

end PalPeg.Local

/-! ## Axiom audit -/

#print axioms PalPeg.Local.readWin_eq
#print axioms PalPeg.Local.pos_sweep
#print axioms PalPeg.Local.rd_sweep
#print axioms PalPeg.Local.LocalStep.runB_block
#print axioms PalPeg.Local.LocalStep.realize_srun
#print axioms PalPeg.Local.LocalStep.realize_SAccepts
