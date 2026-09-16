import Mathlib
import PegSeparation.Common.Compiler.RealTimeTM.Model

/-!
# Linear speedup (tape compression) for the artifact's strictly real-time machines

This file is self-contained on top of the Kim--Park artifact's
`PegSeparation.Common.Compiler.RealTimeTM.Model`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.Speedup

open PegSeparation.RealTimeTM

/-! ## Part A: a functional view of the artifact's tape zippers -/

section FunctionalTape

variable {k : ℕ}

/-- The head position of a tape zipper. -/
def tpos (T : TapeConfiguration k) : ℕ := T.left.length

/-- The visited portion of a tape, left-to-right. -/
def tlist (T : TapeConfiguration k) : List (Fin k) :=
  T.left.reverse ++ T.focus :: T.right

/-- The tape as a total function `ℕ → Fin k`, blank outside the visited portion. -/
def tget (blank : Fin k) (T : TapeConfiguration k) (i : ℕ) : Fin k :=
  (tlist T).getD i blank

private theorem getD_append_cons (l : List (Fin k)) (a : Fin k) (r : List (Fin k))
    (d : Fin k) (i : ℕ) :
    (l ++ a :: r).getD i d =
      if i < l.length then l.getD i d
      else if i = l.length then a
      else r.getD (i - l.length - 1) d := by
  induction l generalizing i with
  | nil =>
      cases i with
      | zero => simp
      | succ j => simp
  | cons x l ih =>
      cases i with
      | zero => simp
      | succ j =>
          simp only [List.getD_cons_succ, List.length_cons, List.cons_append, ih j]
          split_ifs <;>
            first
              | rfl
              | omega
              | (congr 1; omega)

@[simp] theorem tget_tpos (blank : Fin k) (T : TapeConfiguration k) :
    tget blank T (tpos T) = T.focus := by
  simp only [tget, tlist, tpos, getD_append_cons, List.length_reverse]
  simp

private theorem getD_two (l : List (Fin k)) (a b : Fin k) (r s : List (Fin k))
    (d : Fin k) (i : ℕ) (h : ∀ j, r.getD j d = s.getD j d) :
    (l ++ a :: r).getD i d = if i = l.length then a else (l ++ b :: s).getD i d := by
  rw [getD_append_cons, getD_append_cons]
  split_ifs <;>
    first
      | rfl
      | omega
      | exact h _

private theorem getD_singleton (d x : Fin k) (j : ℕ) :
    [d].getD j d = ([] : List (Fin k)).getD j d := by
  cases j <;> simp

theorem tpos_applyAction (blank : Fin k) (T : TapeConfiguration k)
    (act : TapeAction k) :
    tpos (T.applyAction blank act) =
      match act.move with
      | Move.left => tpos T - 1
      | Move.stay => tpos T
      | Move.right => tpos T + 1 := by
  obtain ⟨left, focus, right⟩ := T
  obtain ⟨w, m⟩ := act
  cases m with
  | stay => rfl
  | right => cases right <;> rfl
  | left => cases left <;> simp [TapeConfiguration.applyAction, tpos]

theorem tget_applyAction (blank : Fin k) (T : TapeConfiguration k)
    (act : TapeAction k) (i : ℕ) :
    tget blank (T.applyAction blank act) i =
      if i = tpos T then act.write else tget blank T i := by
  obtain ⟨left, focus, right⟩ := T
  obtain ⟨w, m⟩ := act
  cases m with
  | stay =>
      simp only [TapeConfiguration.applyAction_stay, tget, tlist, tpos]
      rw [getD_two _ _ focus _ right _ _ (fun _ => rfl)]
      simp
  | right =>
      cases right with
      | nil =>
          simp only [TapeConfiguration.applyAction_right_nil, tget, tlist, tpos,
            List.reverse_cons, List.append_assoc, List.singleton_append]
          rw [getD_two _ _ focus _ ([] : List (Fin k)) _ _
            (fun j => getD_singleton blank blank j)]
          simp
      | cons r rs =>
          simp only [TapeConfiguration.applyAction_right_cons, tget, tlist, tpos,
            List.reverse_cons, List.append_assoc, List.singleton_append]
          rw [getD_two _ _ focus _ (r :: rs) _ _ (fun _ => rfl)]
          simp
  | left =>
      cases left with
      | nil =>
          simp only [TapeConfiguration.applyAction_left_nil, tget, tlist, tpos,
            List.reverse_nil, List.nil_append, List.length_nil]
          rw [show (w :: right) = ([] : List (Fin k)) ++ w :: right from rfl,
            getD_two _ _ focus _ right _ _ (fun _ => rfl)]
          simp
      | cons n rest =>
          simp only [TapeConfiguration.applyAction_left_cons, tget, tlist, tpos,
            List.reverse_cons, List.append_assoc, List.singleton_append,
            List.length_cons]
          rw [show rest.reverse ++ n :: w :: right
              = (rest.reverse ++ [n]) ++ w :: right by simp,
            show rest.reverse ++ n :: focus :: right
              = (rest.reverse ++ [n]) ++ focus :: right by simp,
            getD_two _ _ focus _ right _ _ (fun _ => rfl)]
          simp

end FunctionalTape

/-! ## Part B: multi-step (bounded-burst) real-time machines -/

/-- A strictly real-time machine which, on each input symbol, performs `B`
sequential micro-transitions.  Each micro-transition reads the symbol under every
head and performs one `TapeAction` per tape, exactly as `Machine.step` does; the
input symbol is available only during the first micro-step of the round. -/
structure MultiStepMachine (Terminal : Type) (tapeCount stateCount symbolCount B : ℕ) where
  tapeCount_pos : 0 < tapeCount
  blank : Fin symbolCount
  initialState : Fin stateCount
  accepting : Finset (Fin stateCount)
  micro : Fin stateCount → Option Terminal → (Fin tapeCount → Fin symbolCount) →
    Fin stateCount × (Fin tapeCount → TapeAction symbolCount)

namespace MultiStepMachine

variable {Terminal : Type} {t s k B : ℕ}

/-- All tapes blank, head at the left edge. -/
def initialConfiguration (M : MultiStepMachine Terminal t s k B) :
    Configuration t s k where
  state := M.initialState
  tape := fun _ => { left := [], focus := M.blank, right := [] }

/-- One micro-transition. -/
def microStep (M : MultiStepMachine Terminal t s k B)
    (c : Configuration t s k) (a : Option Terminal) : Configuration t s k :=
  let r := M.micro c.state a (fun j => (c.tape j).focus)
  { state := r.1
    tape := fun j => (c.tape j).applyAction M.blank (r.2 j) }

/-- The micro-inputs consumed during one round: the input symbol, then `B-1`
blind micro-steps. -/
def roundInputs (B : ℕ) (a : Terminal) : List (Option Terminal) :=
  some a :: List.replicate (B - 1) none

@[simp] theorem length_roundInputs (B : ℕ) (hB : 0 < B) (a : Terminal) :
    (roundInputs B a).length = B := by
  simp [roundInputs]
  omega

/-- One round: `B` micro-transitions triggered by one input symbol. -/
def round (M : MultiStepMachine Terminal t s k B)
    (c : Configuration t s k) (a : Terminal) : Configuration t s k :=
  (roundInputs B a).foldl M.microStep c

def run (M : MultiStepMachine Terminal t s k B) (input : List Terminal) :
    Configuration t s k :=
  input.foldl M.round M.initialConfiguration

def Accepts (M : MultiStepMachine Terminal t s k B) (input : List Terminal) : Prop :=
  (M.run input).state ∈ M.accepting

@[simp] theorem run_nil (M : MultiStepMachine Terminal t s k B) :
    M.run [] = M.initialConfiguration := rfl

@[simp] theorem run_append_singleton (M : MultiStepMachine Terminal t s k B)
    (input : List Terminal) (a : Terminal) :
    M.run (input ++ [a]) = M.round (M.run input) a := by
  simp [run, List.foldl_append]

/-- For `B = 1` a `MultiStepMachine` is literally a `Machine`. -/
def toMachine (M : MultiStepMachine Terminal t s k 1) : Machine Terminal t s k where
  tapeCount_pos := M.tapeCount_pos
  blank := M.blank
  initialState := M.initialState
  accepting := M.accepting
  transition := fun q a focus =>
    { nextState := (M.micro q (some a) focus).1
      tapeAction := (M.micro q (some a) focus).2 }

theorem toMachine_step (M : MultiStepMachine Terminal t s k 1)
    (c : Configuration t s k) (a : Terminal) :
    M.toMachine.step c a = M.round c a := rfl

theorem toMachine_run (M : MultiStepMachine Terminal t s k 1)
    (input : List Terminal) : M.toMachine.run input = M.run input := by
  have h : ∀ (w : List Terminal) (c : Configuration t s k),
      w.foldl M.toMachine.step c = w.foldl M.round c := by
    intro w
    induction w with
    | nil => intro c; rfl
    | cons a rest ih =>
        intro c
        simp only [List.foldl_cons, toMachine_step, ih]
  exact h input M.initialConfiguration

/-- Agreement of the two models at `B = 1`. -/
theorem multiStep_one_accepts_iff (M : MultiStepMachine Terminal t s k 1)
    (input : List Terminal) : M.toMachine.Accepts input ↔ M.Accepts input := by
  unfold Machine.Accepts Accepts
  rw [toMachine_run]
  rfl

end MultiStepMachine

/-! ## Part C1: blocks and windows

`Sym0 k = Option (Fin k)`: the alphabet of the *shifted* tape, `none` being a
wall symbol occupying the `B` virtual cells to the left of the real tape.  A
`Blk` is one block of `B` consecutive shifted cells, a `Win` is a window of
three consecutive blocks. -/

abbrev Sym0 (k : ℕ) := Option (Fin k)
abbrev Blk (k B : ℕ) := Fin B → Sym0 k
abbrev Win (k B : ℕ) := Blk k B × Blk k B × Blk k B

section BlockAlgebra

variable {k B : ℕ}

def blkGet (b : Blk k B) (i : ℕ) : Sym0 k := if h : i < B then b ⟨i, h⟩ else none

def blkSet (b : Blk k B) (i : ℕ) (x : Sym0 k) : Blk k B :=
  fun u => if (u : ℕ) = i then x else b u

def winGet (w : Win k B) (r : ℕ) : Sym0 k :=
  if r < B then blkGet w.1 r
  else if r < 2 * B then blkGet w.2.1 (r - B)
  else blkGet w.2.2 (r - 2 * B)

def winSet (w : Win k B) (r : ℕ) (x : Sym0 k) : Win k B :=
  if r < B then (blkSet w.1 r x, w.2.1, w.2.2)
  else if r < 2 * B then (w.1, blkSet w.2.1 (r - B) x, w.2.2)
  else (w.1, w.2.1, blkSet w.2.2 (r - 2 * B) x)

/-- The `q`-th block of a shifted tape. -/
def blkOf (F : ℕ → Sym0 k) (q : ℕ) : Blk k B := fun u => F (q * B + (u : ℕ))

theorem blkGet_blkOf (F : ℕ → Sym0 k) (q i : ℕ) (h : i < B) :
    blkGet (blkOf F q : Blk k B) i = F (q * B + i) := by
  simp [blkGet, blkOf, h]

theorem blkOf_ext {F G : ℕ → Sym0 k} {q : ℕ}
    (h : ∀ u, u < B → F (q * B + u) = G (q * B + u)) :
    (blkOf F q : Blk k B) = blkOf G q := by
  funext u
  exact h u u.isLt

theorem blk_eq_blkOf {b : Blk k B} {F : ℕ → Sym0 k} {q : ℕ}
    (h : ∀ i, i < B → blkGet b i = F (q * B + i)) : b = blkOf F q := by
  funext u
  have := h u u.isLt
  simpa [blkGet, u.isLt, blkOf] using this

theorem blkGet_blkSet (b : Blk k B) {i : ℕ} (j : ℕ) (x : Sym0 k) (hi : i < B) :
    blkGet (blkSet b i x) j = if j = i then x else blkGet b j := by
  by_cases hj : j < B
  · simp [blkGet, blkSet, hj]
  · have : j ≠ i := by omega
    simp [blkGet, hj, this]

theorem winGet_winSet (w : Win k B) (r i : ℕ) (x : Sym0 k)
    (hr : r < 3 * B) (hi : i < 3 * B) :
    winGet (winSet w r x) i = if i = r then x else winGet w i := by
  by_cases hr1 : r < B
  · simp only [winSet, if_pos hr1]
    by_cases hi1 : i < B
    · simp only [winGet, if_pos hi1]
      exact blkGet_blkSet _ _ _ hr1
    · by_cases hi2 : i < 2 * B
      · simp only [winGet, if_neg hi1, if_pos hi2, if_neg (show i ≠ r by omega)]
      · simp only [winGet, if_neg hi1, if_neg hi2, if_neg (show i ≠ r by omega)]
  · by_cases hr2 : r < 2 * B
    · simp only [winSet, if_neg hr1, if_pos hr2]
      by_cases hi1 : i < B
      · simp only [winGet, if_pos hi1, if_neg (show i ≠ r by omega)]
      · by_cases hi2 : i < 2 * B
        · simp only [winGet, if_neg hi1, if_pos hi2]
          rw [blkGet_blkSet _ _ _ (show r - B < B by omega)]
          by_cases h : i = r
          · simp [h]
          · simp [h, show i - B ≠ r - B by omega]
        · simp only [winGet, if_neg hi1, if_neg hi2, if_neg (show i ≠ r by omega)]
    · simp only [winSet, if_neg hr1, if_neg hr2]
      by_cases hi1 : i < B
      · simp only [winGet, if_pos hi1, if_neg (show i ≠ r by omega)]
      · by_cases hi2 : i < 2 * B
        · simp only [winGet, if_neg hi1, if_pos hi2, if_neg (show i ≠ r by omega)]
        · simp only [winGet, if_neg hi1, if_neg hi2]
          rw [blkGet_blkSet _ _ _ (show r - 2 * B < B by omega)]
          by_cases h : i = r
          · simp [h]
          · simp [h, show i - 2 * B ≠ r - 2 * B by omega]

/-- The window `w` faithfully represents blocks `P, P+1, P+2` of `F`. -/
def WinRel (P : ℕ) (w : Win k B) (F : ℕ → Sym0 k) : Prop :=
  ∀ i, i < 3 * B → winGet w i = F (P * B + i)

theorem winRel_of_blocks (P : ℕ) (F : ℕ → Sym0 k) (hB : 0 < B) :
    WinRel P ((blkOf F P, blkOf F (P + 1), blkOf F (P + 2)) : Win k B) F := by
  intro i hi
  unfold winGet
  by_cases h1 : i < B
  · rw [if_pos h1, blkGet_blkOf _ _ _ h1]
  · by_cases h2 : i < 2 * B
    · rw [if_neg h1, if_pos h2, blkGet_blkOf _ _ _ (by omega)]
      congr 1
      cases Nat.exists_eq_add_of_le (show B ≤ i by omega) with
      | intro d hd => subst hd; ring_nf; omega
    · rw [if_neg h1, if_neg h2, blkGet_blkOf _ _ _ (by omega)]
      congr 1
      cases Nat.exists_eq_add_of_le (show 2 * B ≤ i by omega) with
      | intro d hd => subst hd; ring_nf; omega

end BlockAlgebra

/-! ## Part C2: the shifted tape and the micro-step simulation -/

section Simulation

variable {Terminal : Type} {t s k B : ℕ}

/-- `T` shifted right by `B` cells; the first block consists of wall symbols
(`none`), which is how the artifact's "moving left at cell `0` stays" rule is
made *locally* observable. -/
def shift (blank : Fin k) (B : ℕ) (T : TapeConfiguration k) : ℕ → Sym0 k :=
  fun i => if i < B then none else some (tget blank T (i - B))

theorem shift_ge (blank : Fin k) (B : ℕ) (T : TapeConfiguration k) {x : ℕ}
    (h : B ≤ x) : shift blank B T x = some (tget blank T (x - B)) := by
  simp [shift, Nat.not_lt.mpr h]

theorem shift_lt (blank : Fin k) (B : ℕ) (T : TapeConfiguration k) {x : ℕ}
    (h : x < B) : shift blank B T x = none := by simp [shift, h]

theorem shift_applyAction (blank : Fin k) (B : ℕ) (T : TapeConfiguration k)
    (act : TapeAction k) (x : ℕ) :
    shift blank B (T.applyAction blank act) x =
      if x = tpos T + B then some act.write else shift blank B T x := by
  by_cases h : x < B
  · rw [shift_lt _ _ _ h, if_neg (by omega), shift_lt _ _ _ h]
  · rw [shift_ge _ _ _ (by omega), shift_ge _ _ _ (by omega), tget_applyAction]
    by_cases h2 : x = tpos T + B
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]

/-- The state of the round-simulation carried out inside one step of the
compressed machine. -/
structure SimState (t s k B : ℕ) where
  st : Fin s
  win : Fin t → Win k B
  pos : Fin t → ℕ

namespace MultiStepMachine

/-- One micro-step, performed inside the windows. -/
def simMicro (M : MultiStepMachine Terminal t s k B) (S : SimState t s k B)
    (a : Option Terminal) : SimState t s k B :=
  let res := M.micro S.st a (fun j => (winGet (S.win j) (S.pos j)).getD M.blank)
  { st := res.1
    win := fun j => winSet (S.win j) (S.pos j) (some (res.2 j).write)
    pos := fun j =>
      match (res.2 j).move with
      | Move.stay => S.pos j
      | Move.right => S.pos j + 1
      | Move.left =>
          if S.pos j = 0 then S.pos j
          else if winGet (S.win j) (S.pos j - 1) = none then S.pos j
          else S.pos j - 1 }

/-- The simulation invariant for a single micro-step: the simulated state agrees,
each window faithfully shows blocks `P j, P j + 1, P j + 2` of the (shifted)
tape, and the window offset locates the real head. -/
def MicroInv (M : MultiStepMachine Terminal t s k B) (P : Fin t → ℕ)
    (c : Configuration t s k) (S : SimState t s k B) : Prop :=
  S.st = c.state ∧
  ∀ j, WinRel (P j) (S.win j) (shift M.blank B (c.tape j)) ∧
       P j * B + S.pos j = tpos (c.tape j) + B

theorem simMicro_read (M : MultiStepMachine Terminal t s k B) {P : Fin t → ℕ}
    {c : Configuration t s k} {S : SimState t s k B}
    (hinv : MicroInv M P c S) (hhi : ∀ j, S.pos j < 3 * B) (j : Fin t) :
    (winGet (S.win j) (S.pos j)).getD M.blank = (c.tape j).focus := by
  obtain ⟨hst, hj⟩ := hinv
  obtain ⟨hw, hp⟩ := hj j
  rw [hw _ (hhi j), hp, shift_ge _ _ _ (by omega)]
  simp

theorem simMicro_correct (M : MultiStepMachine Terminal t s k B) (hB : 0 < B)
    (P : Fin t → ℕ) (c : Configuration t s k) (S : SimState t s k B)
    (a : Option Terminal) (hinv : MicroInv M P c S)
    (hlo : ∀ j, 1 ≤ S.pos j) (hhi : ∀ j, S.pos j < 3 * B) :
    MicroInv M P (M.microStep c a) (M.simMicro S a) ∧
    (∀ j, S.pos j ≤ (M.simMicro S a).pos j + 1 ∧
          (M.simMicro S a).pos j ≤ S.pos j + 1) ∧
    (∀ j x, (x < P j * B ∨ P j * B + 3 * B ≤ x) →
      shift M.blank B ((M.microStep c a).tape j) x =
        shift M.blank B (c.tape j) x) := by
  obtain ⟨hst, hj⟩ := hinv
  have hread : (fun j => (winGet (S.win j) (S.pos j)).getD M.blank) =
      (fun j => (c.tape j).focus) := by
    funext j
    exact simMicro_read M ⟨hst, hj⟩ hhi j
  have hsim : M.simMicro S a =
      { st := (M.micro c.state a (fun j => (c.tape j).focus)).1
        win := fun j => winSet (S.win j) (S.pos j)
          (some ((M.micro c.state a (fun j => (c.tape j).focus)).2 j).write)
        pos := fun j =>
          match ((M.micro c.state a (fun j => (c.tape j).focus)).2 j).move with
          | Move.stay => S.pos j
          | Move.right => S.pos j + 1
          | Move.left =>
              if S.pos j = 0 then S.pos j
              else if winGet (S.win j) (S.pos j - 1) = none then S.pos j
              else S.pos j - 1 } := by
    unfold simMicro
    rw [hst, hread]
  set res := M.micro c.state a (fun j => (c.tape j).focus) with hresdef
  have hstep : M.microStep c a =
      { state := res.1
        tape := fun j => (c.tape j).applyAction M.blank (res.2 j) } := by
    unfold microStep
    rw [hresdef]
  refine ⟨⟨by rw [hsim, hstep], ?_⟩, ?_, ?_⟩
  · intro j
    obtain ⟨hw, hp⟩ := hj j
    have hpos3 : S.pos j < 3 * B := hhi j
    have hpos1 : 1 ≤ S.pos j := hlo j
    have hposge : P j * B + S.pos j = tpos (c.tape j) + B := hp
    -- the new (shifted) tape
    have hnew : ∀ x, shift M.blank B ((M.microStep c a).tape j) x =
        if x = tpos (c.tape j) + B then some (res.2 j).write
        else shift M.blank B (c.tape j) x := by
      intro x
      rw [hstep]
      exact shift_applyAction _ _ _ _ x
    constructor
    · intro i hi
      rw [hsim]
      simp only
      rw [winGet_winSet _ _ _ _ hpos3 hi, hnew]
      by_cases h : i = S.pos j
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega), hw _ hi]
    · rw [hsim, hstep]
      simp only
      rcases hmove : (res.2 j).move with _ | _ | _
      · -- left
        rw [tpos_applyAction]
        simp only [hmove]
        have h0 : ¬ (S.pos j = 0) := by omega
        rw [if_neg h0]
        have hwall : winGet (S.win j) (S.pos j - 1) =
            shift M.blank B (c.tape j) (P j * B + (S.pos j - 1)) :=
          hw _ (by omega)
        have harith : P j * B + (S.pos j - 1) = tpos (c.tape j) + B - 1 := by omega
        by_cases hz : tpos (c.tape j) = 0
        · have : winGet (S.win j) (S.pos j - 1) = none := by
            rw [hwall, harith, hz, shift_lt _ _ _ (by omega)]
          rw [if_pos this, hz]
          omega
        · have : winGet (S.win j) (S.pos j - 1) ≠ none := by
            rw [hwall, harith, shift_ge _ _ _ (by omega)]
            simp
          rw [if_neg this]
          omega
      · -- stay
        rw [tpos_applyAction]
        simp only [hmove]
        omega
      · -- right
        rw [tpos_applyAction]
        simp only [hmove]
        omega
  · intro j
    rw [hsim]
    simp only
    rcases hmove : (res.2 j).move with _ | _ | _ <;> simp only [hmove] <;>
      [skip; omega; omega]
    split_ifs <;> omega
  · intro j x hx
    obtain ⟨hw, hp⟩ := hj j
    rw [hstep]
    simp only
    have hb := hhi j
    rw [shift_applyAction, if_neg (show ¬ (x = tpos (c.tape j) + B) by omega)]

end MultiStepMachine

end Simulation

/-! ## Part C3: a whole round -/

section Round

variable {Terminal : Type} {t s k B : ℕ}

namespace MultiStepMachine

/-- The simulation of a whole round, inside the windows. -/
def simRound (M : MultiStepMachine Terminal t s k B) (S : SimState t s k B)
    (a : Terminal) : SimState t s k B :=
  (roundInputs B a).foldl M.simMicro S

theorem simFold_correct (M : MultiStepMachine Terminal t s k B) (hB : 0 < B)
    (P : Fin t → ℕ) (L : List (Option Terminal)) :
    ∀ (n : ℕ) (c : Configuration t s k) (S : SimState t s k B),
      L.length + n ≤ B → MicroInv M P c S →
      (∀ j, B ≤ S.pos j + n) → (∀ j, S.pos j ≤ 2 * B - 1 + n) →
      MicroInv M P (L.foldl M.microStep c) (L.foldl M.simMicro S) ∧
      (∀ j, B ≤ (L.foldl M.simMicro S).pos j + (n + L.length)) ∧
      (∀ j, (L.foldl M.simMicro S).pos j ≤ 2 * B - 1 + (n + L.length)) ∧
      (∀ j x, (x < P j * B ∨ P j * B + 3 * B ≤ x) →
        shift M.blank B ((L.foldl M.microStep c).tape j) x =
          shift M.blank B (c.tape j) x) := by
  induction L with
  | nil =>
      intro n c S _ hinv h1 h2
      refine ⟨hinv, ?_, ?_, ?_⟩
      · intro j; have := h1 j; simp; omega
      · intro j; have := h2 j; simp; omega
      · intro j x _; rfl
  | cons a L ih =>
      intro n c S hlen hinv h1 h2
      have hn : n + 1 ≤ B := by simp at hlen; omega
      have hlo : ∀ j, 1 ≤ S.pos j := by
        intro j; have := h1 j; omega
      have hhi : ∀ j, S.pos j < 3 * B := by
        intro j; have := h2 j; omega
      obtain ⟨hinv', hbnd, hloc⟩ := simMicro_correct M hB P c S a hinv hlo hhi
      have hlen' : L.length + (n + 1) ≤ B := by simp at hlen; omega
      have h1' : ∀ j, B ≤ (M.simMicro S a).pos j + (n + 1) := by
        intro j; have := h1 j; have := (hbnd j).1; omega
      have h2' : ∀ j, (M.simMicro S a).pos j ≤ 2 * B - 1 + (n + 1) := by
        intro j; have := h2 j; have := (hbnd j).2; omega
      obtain ⟨ha, hb, hc, hd⟩ := ih (n + 1) (M.microStep c a) (M.simMicro S a)
        hlen' hinv' h1' h2'
      simp only [List.foldl_cons, List.length_cons]
      refine ⟨ha, ?_, ?_, ?_⟩
      · intro j; have := hb j; omega
      · intro j; have := hc j; omega
      · intro j x hx
        rw [hd j x hx, hloc j x hx]

theorem simRound_correct (M : MultiStepMachine Terminal t s k B) (hB : 0 < B)
    (P : Fin t → ℕ) (c : Configuration t s k) (S : SimState t s k B)
    (a : Terminal) (hinv : MicroInv M P c S)
    (h1 : ∀ j, B ≤ S.pos j) (h2 : ∀ j, S.pos j ≤ 2 * B - 1) :
    MicroInv M P (M.round c a) (M.simRound S a) ∧
    (∀ j, (M.simRound S a).pos j < 3 * B) ∧
    (∀ j x, (x < P j * B ∨ P j * B + 3 * B ≤ x) →
      shift M.blank B ((M.round c a).tape j) x = shift M.blank B (c.tape j) x) := by
  have hlen : (roundInputs B a).length + 0 ≤ B := by
    rw [length_roundInputs B hB a]; omega
  obtain ⟨ha, _, hc, hd⟩ :=
    simFold_correct M hB P (roundInputs B a) 0 c S hlen hinv
      (fun j => by have := h1 j; omega) (fun j => by have := h2 j; omega)
  refine ⟨ha, ?_, hd⟩
  intro j
  have := hc j
  rw [length_roundInputs B hB a] at this
  simp only [simRound]
  omega

end MultiStepMachine

end Round

/-! ## Part D1: the compressed machine -/

/-- Which third of the window has to be taken from the symbol under the head. -/
inductive Pending where
  | full
  | needLeft
  | needRight
  deriving DecidableEq, Fintype, Repr

section Compressed

variable {Terminal : Type} {t s k B : ℕ}

/-- Per-tape information carried in the state of the compressed machine. -/
abbrev Cell (k B : ℕ) := Pending × Win k B × Fin B

/-- The state of the compressed machine. -/
abbrev CState (t s k B : ℕ) := Fin s × (Fin t → Cell k B)

def resolve (C : Cell k B) (x : Blk k B) : Win k B :=
  match C.1 with
  | Pending.full => C.2.1
  | Pending.needRight => (C.2.1.1, C.2.1.2.1, x)
  | Pending.needLeft => (x, C.2.1.2.1, C.2.1.2.2)

def scount (t s k B : ℕ) : ℕ := Fintype.card (CState t s k B)
def kcount (k B : ℕ) : ℕ := Fintype.card (Blk k B)

noncomputable def eSt (t s k B : ℕ) : CState t s k B ≃ Fin (scount t s k B) :=
  Fintype.equivFin _

noncomputable def eBlk (k B : ℕ) : Blk k B ≃ Fin (kcount k B) :=
  Fintype.equivFin _

def junkBlk (k B : ℕ) : Blk k B := fun _ => none

def mkOff (hB : 0 < B) (x : ℕ) : Fin B := ⟨x % B, Nat.mod_lt _ hB⟩

theorem mkOff_val (hB : 0 < B) {x : ℕ} (h : x < B) : ((mkOff hB x : Fin B) : ℕ) = x := by
  simp [mkOff, Nat.mod_eq_of_lt h]

/-- After the round: from the final window and window-offset, read off the new
cell information, the block to be written back, and the direction. -/
def outCell (hB : 0 < B) (w : Win k B) (r : ℕ) : Cell k B × Blk k B × Move :=
  if r < B then
    ((Pending.needLeft, (junkBlk k B, w.1, w.2.1), mkOff hB r), w.2.2, Move.left)
  else if r < 2 * B then
    ((Pending.full, w, mkOff hB (r - B)), w.2.1, Move.stay)
  else
    ((Pending.needRight, (w.2.1, w.2.2, junkBlk k B), mkOff hB (r - 2 * B)),
      w.1, Move.right)

namespace MultiStepMachine

/-- The initial window: a wall block, then two blank blocks. -/
def initWin (M : MultiStepMachine Terminal t s k B) : Win k B :=
  (fun _ => none, fun _ => some M.blank, fun _ => some M.blank)

noncomputable def ctransition (M : MultiStepMachine Terminal t s k B) (hB : 0 < B)
    (q : Fin (scount t s k B)) (a : Terminal)
    (focus : Fin t → Fin (kcount k B)) :
    Instruction t (scount t s k B) (kcount k B) :=
  let Q := (eSt t s k B).symm q
  let S0 : SimState t s k B :=
    { st := Q.1
      win := fun j => resolve (Q.2 j) ((eBlk k B).symm (focus j))
      pos := fun j => B + ((Q.2 j).2.2 : ℕ) }
  let S1 := M.simRound S0 a
  let out : Fin t → Cell k B × Blk k B × Move := fun j => outCell hB (S1.win j) (S1.pos j)
  { nextState := eSt t s k B (S1.st, fun j => (out j).1)
    tapeAction := fun j => { write := eBlk k B (out j).2.1, move := (out j).2.2 } }

/-- The compressed machine: one step per input symbol, same number of tapes. -/
noncomputable def compressed (M : MultiStepMachine Terminal t s k B) (hB : 0 < B) :
    Machine Terminal t (scount t s k B) (kcount k B) where
  tapeCount_pos := M.tapeCount_pos
  blank := eBlk k B (fun _ => some M.blank)
  initialState :=
    eSt t s k B (M.initialState, fun _ => (Pending.full, M.initWin, ⟨0, hB⟩))
  accepting := Finset.univ.filter (fun x => ((eSt t s k B).symm x).1 ∈ M.accepting)
  transition := M.ctransition hB

/-- The simulation invariant, for one tape. -/
def TapeInv (M : MultiStepMachine Terminal t s k B) (hB : 0 < B)
    (T : TapeConfiguration k) (G : TapeConfiguration (kcount k B))
    (C : Cell k B) : Prop :=
  (∀ i, i < tpos G →
      (eBlk k B).symm (tget ((M.compressed hB).blank) G i)
        = blkOf (shift M.blank B T) i) ∧
  (∀ i, tpos G < i →
      (eBlk k B).symm (tget ((M.compressed hB).blank) G i)
        = blkOf (shift M.blank B T) (i + 2)) ∧
  WinRel (tpos G) (resolve C ((eBlk k B).symm G.focus)) (shift M.blank B T) ∧
  tpos T + B = tpos G * B + B + ((C.2.2 : ℕ))

/-- The simulation invariant. -/
def Enc (M : MultiStepMachine Terminal t s k B) (hB : 0 < B)
    (c : Configuration t s k)
    (c' : Configuration t (scount t s k B) (kcount k B)) : Prop :=
  ((eSt t s k B).symm c'.state).1 = c.state ∧
  ∀ j, M.TapeInv hB (c.tape j) (c'.tape j) (((eSt t s k B).symm c'.state).2 j)

end MultiStepMachine

end Compressed

/-! ## Part D2: preservation of the invariant -/

section Preservation

variable {Terminal : Type} {t s k B : ℕ}

theorem tget_init {k : ℕ} (d : Fin k) (i : ℕ) :
    tget d ⟨[], d, []⟩ i = d := by
  cases i with
  | zero => rfl
  | succ n => simp [tget, tlist]

namespace MultiStepMachine

theorem win_fst (M : MultiStepMachine Terminal t s k B) {P : ℕ} {w : Win k B}
    {F : ℕ → Sym0 k} (hB : 0 < B) (hw : WinRel P w F) : w.1 = blkOf F P := by
  refine blk_eq_blkOf (fun i hi => ?_)
  have := hw i (by omega)
  rwa [winGet, if_pos hi] at this

theorem win_snd (M : MultiStepMachine Terminal t s k B) {P : ℕ} {w : Win k B}
    {F : ℕ → Sym0 k} (hB : 0 < B) (hw : WinRel P w F) : w.2.1 = blkOf F (P + 1) := by
  refine blk_eq_blkOf (fun i hi => ?_)
  have h := hw (B + i) (by omega)
  rw [winGet, if_neg (by omega), if_pos (by omega)] at h
  simp only [Nat.add_sub_cancel_left] at h
  rw [h]
  congr 1
  ring

theorem win_thd (M : MultiStepMachine Terminal t s k B) {P : ℕ} {w : Win k B}
    {F : ℕ → Sym0 k} (hB : 0 < B) (hw : WinRel P w F) : w.2.2 = blkOf F (P + 2) := by
  refine blk_eq_blkOf (fun i hi => ?_)
  have h := hw (2 * B + i) (by omega)
  rw [winGet, if_neg (by omega), if_neg (by omega)] at h
  simp only [Nat.add_sub_cancel_left] at h
  rw [h]
  congr 1
  ring

theorem tapeInv_step (M : MultiStepMachine Terminal t s k B) (hB : 0 < B)
    (T T' : TapeConfiguration k) (G : TapeConfiguration (kcount k B))
    (C : Cell k B) (w : Win k B) (r : ℕ)
    (hold : M.TapeInv hB T G C)
    (hwin : WinRel (tpos G) w (shift M.blank B T'))
    (hpos : tpos G * B + r = tpos T' + B)
    (hr3 : r < 3 * B)
    (hloc : ∀ x, (x < tpos G * B ∨ tpos G * B + 3 * B ≤ x) →
      shift M.blank B T' x = shift M.blank B T x) :
    M.TapeInv hB T'
      (G.applyAction ((M.compressed hB).blank)
        { write := eBlk k B (outCell hB w r).2.1, move := (outCell hB w r).2.2 })
      (outCell hB w r).1 := by
  obtain ⟨hc1, hc2, _, _⟩ := hold
  have hblkL : ∀ q, q < tpos G → blkOf (shift M.blank B T') q
      = (blkOf (shift M.blank B T) q : Blk k B) := by
    intro q hq
    funext u
    exact hloc _ (Or.inl (by
      have : (q + 1) * B ≤ tpos G * B := Nat.mul_le_mul_right B (by omega)
      have hu : (u : ℕ) < B := u.isLt
      have : q * B + B = (q + 1) * B := by ring
      omega))
  have hblkR : ∀ q, tpos G + 3 ≤ q → blkOf (shift M.blank B T') q
      = (blkOf (shift M.blank B T) q : Blk k B) := by
    intro q hq
    funext u
    exact hloc _ (Or.inr (by
      have h1 : (tpos G + 3) * B ≤ q * B := Nat.mul_le_mul_right B hq
      have h2 : (tpos G + 3) * B = tpos G * B + 3 * B := by ring
      omega))
  have hw1 := M.win_fst hB hwin
  have hw2 := M.win_snd hB hwin
  have hw3 := M.win_thd hB hwin
  have hgetnew : ∀ i, tget ((M.compressed hB).blank)
      (G.applyAction ((M.compressed hB).blank)
        { write := eBlk k B (outCell hB w r).2.1, move := (outCell hB w r).2.2 }) i
      = if i = tpos G then eBlk k B (outCell hB w r).2.1
        else tget ((M.compressed hB).blank) G i := fun i =>
    tget_applyAction _ _ _ i
  by_cases hr1 : r < B
  · -- move left
    have hP : 0 < tpos G := by
      rcases Nat.eq_zero_or_pos (tpos G) with h | h
      · rw [h] at hpos; simp at hpos; omega
      · exact h
    obtain ⟨P0, hP0⟩ : ∃ P0, tpos G = P0 + 1 := ⟨tpos G - 1, by omega⟩
    have hPB : P0 * B + B = tpos G * B := by rw [hP0]; ring
    have hout : outCell hB w r =
        ((Pending.needLeft, (junkBlk k B, w.1, w.2.1), mkOff hB r), w.2.2, Move.left) := by
      simp [outCell, hr1]
    have htpos' : tpos (G.applyAction ((M.compressed hB).blank)
        { write := eBlk k B (outCell hB w r).2.1, move := (outCell hB w r).2.2 }) = P0 := by
      rw [tpos_applyAction, hout]
      simp [hP0]
    have hfocus : (G.applyAction ((M.compressed hB).blank)
        { write := eBlk k B (outCell hB w r).2.1,
          move := (outCell hB w r).2.2 }).focus
        = tget ((M.compressed hB).blank) G P0 := by
      rw [← tget_tpos ((M.compressed hB).blank), htpos', hgetnew P0,
        if_neg (by omega)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [htpos'] at hi
      rw [hgetnew i, if_neg (by omega), hc1 i (by omega), hblkL i (by omega)]
    · intro i hi
      rw [htpos'] at hi
      rcases Nat.lt_or_ge (tpos G) (i + 1) with h | h
      · -- i ≥ tpos G
        rcases Nat.eq_or_lt_of_le (show tpos G ≤ i by omega) with heq | hlt
        · rw [hgetnew i, if_pos heq.symm, hout]
          simp only [Equiv.symm_apply_apply]
          rw [hw3, ← heq]
        · rw [hgetnew i, if_neg (by omega), hc2 i hlt, hblkR (i + 2) (by omega)]
      · omega
    · rw [htpos', hfocus, hout]
      simp only
      have hread : (eBlk k B).symm (tget ((M.compressed hB).blank) G P0)
          = blkOf (shift M.blank B T') P0 := by
        rw [hc1 P0 (by omega), hblkL P0 (by omega)]
      rw [hread]
      have heq : resolve (Pending.needLeft, (junkBlk k B, w.1, w.2.1), mkOff hB r)
            (blkOf (shift M.blank B T') P0)
          = ((blkOf (shift M.blank B T') P0, blkOf (shift M.blank B T') (P0 + 1),
             blkOf (shift M.blank B T') (P0 + 2)) : Win k B) := by
        simp only [resolve]
        rw [hw1, hw2, hP0]
      rw [heq]
      exact winRel_of_blocks P0 _ hB
    · rw [htpos', hout]
      simp only
      rw [mkOff_val hB hr1]
      omega
  · by_cases hr2 : r < 2 * B
    · -- stay
      have hout : outCell hB w r =
          ((Pending.full, w, mkOff hB (r - B)), w.2.1, Move.stay) := by
        simp [outCell, hr1, hr2]
      have htpos' : tpos (G.applyAction ((M.compressed hB).blank)
          { write := eBlk k B (outCell hB w r).2.1,
            move := (outCell hB w r).2.2 }) = tpos G := by
        rw [tpos_applyAction, hout]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi
        rw [htpos'] at hi
        rw [hgetnew i, if_neg (by omega), hc1 i hi, hblkL i hi]
      · intro i hi
        rw [htpos'] at hi
        rw [hgetnew i, if_neg (by omega), hc2 i hi, hblkR (i + 2) (by omega)]
      · rw [htpos', hout]
        simp only [resolve]
        exact hwin
      · rw [htpos', hout]
        simp only
        rw [mkOff_val hB (by omega)]
        omega
    · -- move right
      have hout : outCell hB w r =
          ((Pending.needRight, (w.2.1, w.2.2, junkBlk k B), mkOff hB (r - 2 * B)),
            w.1, Move.right) := by
        simp [outCell, hr1, hr2]
      have htpos' : tpos (G.applyAction ((M.compressed hB).blank)
          { write := eBlk k B (outCell hB w r).2.1,
            move := (outCell hB w r).2.2 }) = tpos G + 1 := by
        rw [tpos_applyAction, hout]
      have hfocus : (G.applyAction ((M.compressed hB).blank)
          { write := eBlk k B (outCell hB w r).2.1,
            move := (outCell hB w r).2.2 }).focus
          = tget ((M.compressed hB).blank) G (tpos G + 1) := by
        rw [← tget_tpos ((M.compressed hB).blank), htpos', hgetnew (tpos G + 1),
          if_neg (by omega)]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi
        rw [htpos'] at hi
        rcases Nat.eq_or_lt_of_le (show i ≤ tpos G by omega) with heq | hlt
        · rw [hgetnew i, if_pos heq, hout]
          simp only [Equiv.symm_apply_apply]
          rw [hw1, heq]
        · rw [hgetnew i, if_neg (by omega), hc1 i hlt, hblkL i hlt]
      · intro i hi
        rw [htpos'] at hi
        rw [hgetnew i, if_neg (by omega), hc2 i (by omega),
          hblkR (i + 2) (by omega)]
      · rw [htpos', hfocus, hout]
        simp only
        have hread : (eBlk k B).symm (tget ((M.compressed hB).blank) G (tpos G + 1))
            = blkOf (shift M.blank B T') (tpos G + 1 + 2) := by
          rw [hc2 (tpos G + 1) (by omega), hblkR (tpos G + 1 + 2) (by omega)]
        rw [hread]
        have heq : resolve (Pending.needRight, (w.2.1, w.2.2, junkBlk k B),
              mkOff hB (r - 2 * B)) (blkOf (shift M.blank B T') (tpos G + 1 + 2))
            = ((blkOf (shift M.blank B T') (tpos G + 1),
               blkOf (shift M.blank B T') (tpos G + 1 + 1),
               blkOf (shift M.blank B T') (tpos G + 1 + 2)) : Win k B) := by
          simp only [resolve]
          rw [hw2, hw3]
        rw [heq]
        exact winRel_of_blocks (tpos G + 1) _ hB
      · rw [htpos', hout]
        simp only
        rw [mkOff_val hB (by omega)]
        have h1 : (tpos G + 1) * B = tpos G * B + B := by ring
        omega

end MultiStepMachine

end Preservation

/-! ## Part D3: the speedup theorem -/

section Main

variable {Terminal : Type} {t s k B : ℕ}

namespace MultiStepMachine

theorem Enc_init (M : MultiStepMachine Terminal t s k B) (hB : 0 < B) :
    M.Enc hB M.initialConfiguration ((M.compressed hB).initialConfiguration) := by
  constructor
  · show ((eSt t s k B).symm ((eSt t s k B) _)).1 = _
    rw [Equiv.symm_apply_apply]
    rfl
  · intro j
    show M.TapeInv hB ⟨[], M.blank, []⟩ ⟨[], (M.compressed hB).blank, []⟩
      (((eSt t s k B).symm ((eSt t s k B)
        (M.initialState, fun _ => (Pending.full, M.initWin, ⟨0, hB⟩)))).2 j)
    rw [Equiv.symm_apply_apply]
    have htp : tpos (⟨[], (M.compressed hB).blank, []⟩ : TapeConfiguration (kcount k B))
        = 0 := rfl
    have hF : ∀ x, B ≤ x →
        shift M.blank B (⟨[], M.blank, []⟩ : TapeConfiguration k) x = some M.blank := by
      intro x hx
      rw [shift_ge _ _ _ hx, tget_init]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi; rw [htp] at hi; omega
    · intro i hi
      rw [htp] at hi
      rw [tget_init]
      show (eBlk k B).symm ((eBlk k B) _) = _
      rw [Equiv.symm_apply_apply]
      funext u
      have hu : (u : ℕ) < B := u.isLt
      have hle : B ≤ (i + 2) * B := Nat.le_mul_of_pos_left B (by omega)
      rw [blkOf, hF _ (by omega)]
    · rw [htp]
      simp only [resolve, initWin]
      intro i hi
      simp only [Nat.zero_mul, Nat.zero_add]
      unfold winGet
      by_cases h1 : i < B
      · rw [if_pos h1, shift_lt _ _ _ h1]
        simp [blkGet, h1]
      · by_cases h2 : i < 2 * B
        · rw [if_neg h1, if_pos h2, hF _ (by omega)]
          simp [blkGet, show i - B < B by omega]
        · rw [if_neg h1, if_neg h2, hF _ (by omega)]
          simp [blkGet, show i - 2 * B < B by omega]
    · rw [htp]
      show tpos (⟨[], M.blank, []⟩ : TapeConfiguration k) + B = 0 * B + B + 0
      simp [tpos]

theorem Enc_step (M : MultiStepMachine Terminal t s k B) (hB : 0 < B)
    (c : Configuration t s k) (c' : Configuration t (scount t s k B) (kcount k B))
    (a : Terminal) (h : M.Enc hB c c') :
    M.Enc hB (M.round c a) ((M.compressed hB).step c' a) := by
  obtain ⟨hstate, htapes⟩ := h
  set Q := (eSt t s k B).symm c'.state with hQ
  set P : Fin t → ℕ := fun j => tpos (c'.tape j) with hPdef
  set S0 : SimState t s k B :=
    { st := Q.1
      win := fun j => resolve (Q.2 j) ((eBlk k B).symm ((c'.tape j).focus))
      pos := fun j => B + ((Q.2 j).2.2 : ℕ) } with hS0
  have hinv : M.MicroInv P c S0 := by
    refine ⟨hstate, fun j => ⟨?_, ?_⟩⟩
    · exact (htapes j).2.2.1
    · have h4 := (htapes j).2.2.2
      show P j * B + (B + ((Q.2 j).2.2 : ℕ)) = tpos (c.tape j) + B
      simp only [hPdef]
      omega
  have h1 : ∀ j, B ≤ S0.pos j := fun j => by
    show B ≤ B + ((Q.2 j).2.2 : ℕ); omega
  have h2 : ∀ j, S0.pos j ≤ 2 * B - 1 := fun j => by
    have := ((Q.2 j).2.2).isLt
    show B + ((Q.2 j).2.2 : ℕ) ≤ 2 * B - 1
    omega
  obtain ⟨⟨hst1, hj1⟩, hbound, hloc⟩ := M.simRound_correct hB P c S0 a hinv h1 h2
  set S1 := M.simRound S0 a with hS1
  have hstep : (M.compressed hB).step c' a =
      { state := eSt t s k B (S1.st,
          fun j => (outCell hB (S1.win j) (S1.pos j)).1)
        tape := fun j => (c'.tape j).applyAction ((M.compressed hB).blank)
          { write := eBlk k B (outCell hB (S1.win j) (S1.pos j)).2.1
            move := (outCell hB (S1.win j) (S1.pos j)).2.2 } } := rfl
  rw [hstep]
  constructor
  · show ((eSt t s k B).symm ((eSt t s k B) _)).1 = _
    rw [Equiv.symm_apply_apply]
    exact hst1
  · intro j
    show M.TapeInv hB _ _ (((eSt t s k B).symm ((eSt t s k B) _)).2 j)
    rw [Equiv.symm_apply_apply]
    exact M.tapeInv_step hB (c.tape j) ((M.round c a).tape j) (c'.tape j)
      (Q.2 j) (S1.win j) (S1.pos j) (htapes j) (hj1 j).1 (hj1 j).2
      (hbound j) (hloc j)

theorem Enc_run (M : MultiStepMachine Terminal t s k B) (hB : 0 < B)
    (w : List Terminal) : M.Enc hB (M.run w) ((M.compressed hB).run w) := by
  have key : ∀ (v : List Terminal) (c : Configuration t s k)
      (c' : Configuration t (scount t s k B) (kcount k B)),
      M.Enc hB c c' → M.Enc hB (v.foldl M.round c) (v.foldl (M.compressed hB).step c') := by
    intro v
    induction v with
    | nil => intro c c' h; exact h
    | cons a rest ih =>
        intro c c' h
        simp only [List.foldl_cons]
        exact ih _ _ (M.Enc_step hB c c' a h)
  exact key w _ _ (M.Enc_init hB)

theorem compressed_accepts_iff (M : MultiStepMachine Terminal t s k B) (hB : 0 < B)
    (w : List Terminal) : (M.compressed hB).Accepts w ↔ M.Accepts w := by
  obtain ⟨hstate, _⟩ := M.Enc_run hB w
  show ((M.compressed hB).run w).state ∈ (M.compressed hB).accepting ↔ _
  show ((M.compressed hB).run w).state ∈
    Finset.univ.filter (fun x => ((eSt t s k B).symm x).1 ∈ M.accepting) ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [hstate]
  rfl

end MultiStepMachine

/-- **Linear speedup / tape compression.**  A strictly real-time multitape
machine which performs `B` micro-transitions per input symbol is simulated,
symbol for symbol, by an ordinary strictly real-time machine of the artifact
with the *same number of tapes* (at the price of more states and more tape
symbols). -/
theorem multiStep_recognizedBy {Terminal : Type} [DecidableEq Terminal]
    {t s k B : ℕ} (hB : 0 < B) (M : MultiStepMachine Terminal t s k B) :
    ∃ (s' k' : ℕ) (M' : Machine Terminal t s' k'),
      ∀ w, M'.Accepts w ↔ M.Accepts w :=
  ⟨scount t s k B, kcount k B, M.compressed hB,
    fun w => M.compressed_accepts_iff hB w⟩

end Main

end PalPeg.Speedup
