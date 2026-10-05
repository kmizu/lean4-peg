/-!
# Multi-tape Turing machines and the classes PSPACE / polynomial-time reductions

The machine model for the TQBF development: a deterministic `k`-tape Turing machine with finitely many states
(`0` accepts, `1` rejects, `2` is the start state) and finitely many tape symbols (`0` is the blank; an input bit
`false`/`true` is written as `1`/`2`). Configurations store each tape as a function from cell index to symbol, so there
is no ambiguity about trailing blanks.

* `TM.Decides M L`: on every input `M` halts, and it halts in the accepting state iff the input is in `L`.
* `TM.SpaceBounded M s`: every configuration of the run on an input of length `n` fits in `s n` cells per tape.
* `PSPACE L`: some machine decides `L` within polynomial space.
* `PolyTimeComputable f`: some machine, on input `w`, halts within polynomially many steps in the accepting state with
  `f w` written at the start of tape `0`.
* `Reduces L L'` (polynomial-time many-one), `PSPACEHard`, `PSPACEComplete`.
-/

namespace Complexity

inductive Move where
  | L
  | S
  | R
  deriving DecidableEq

def Move.apply : Move → Nat → Nat
  | .L, p => p - 1
  | .S, p => p
  | .R, p => p + 1

/-- A deterministic `k`-tape Turing machine. -/
structure TM (k : Nat) where
  /-- States are `0 … nq - 1`; `0` accepts, `1` rejects, `2` starts. -/
  nq : Nat
  /-- Symbols are `0 … na - 1`; `0` is the blank, `1`/`2` are the input bits `false`/`true`. -/
  na : Nat
  /-- From a non-halting state and the symbols under the heads: new state, symbols to write, head moves. -/
  delta : Nat → (Fin k → Nat) → Nat × (Fin k → Nat) × (Fin k → Move)
  three_le_nq : 3 ≤ nq
  three_le_na : 3 ≤ na
  delta_state : ∀ q r, q < nq → (∀ i, r i < na) → (delta q r).1 < nq
  delta_sym : ∀ q r, q < nq → (∀ i, r i < na) → ∀ i, (delta q r).2.1 i < na

structure Cfg (k : Nat) where
  state : Nat
  pos : Fin k → Nat
  cells : Fin k → Nat → Nat

def Cfg.halted {k : Nat} (c : Cfg k) : Prop := c.state = 0 ∨ c.state = 1

instance {k : Nat} (c : Cfg k) : Decidable c.halted := by unfold Cfg.halted; infer_instance

def Cfg.read {k : Nat} (c : Cfg k) : Fin k → Nat := fun i => c.cells i (c.pos i)

/-- One step; a halted configuration does not change. -/
def TM.step {k : Nat} (M : TM k) (c : Cfg k) : Cfg k :=
  if c.halted then c
  else
    let d := M.delta c.state c.read
    { state := d.1
      pos := fun i => (d.2.2 i).apply (c.pos i)
      cells := fun i j => if j = c.pos i then d.2.1 i else c.cells i j }

def TM.run {k : Nat} (M : TM k) (c : Cfg k) : Nat → Cfg k
  | 0 => c
  | t + 1 => M.step (M.run c t)

def bitSym (b : Bool) : Nat := if b then 2 else 1

/-- The initial configuration: the input bits on tape `0` from cell `0`, everything else blank. -/
def initCfg (k : Nat) (w : List Bool) : Cfg k where
  state := 2
  pos := fun _ => 0
  cells := fun i j => if i.val = 0 then (match w[j]? with | some b => bitSym b | none => 0) else 0

/-- Every tape fits in `s` cells: the head is inside and everything from cell `s` on is blank. -/
def Fits {k : Nat} (s : Nat) (c : Cfg k) : Prop := ∀ i, c.pos i < s ∧ ∀ j, s ≤ j → c.cells i j = 0

def IsPoly (f : Nat → Nat) : Prop := ∃ c d, ∀ n, f n ≤ c * (n + 1) ^ d

abbrev Lang := List Bool → Prop

def TM.Decides {k : Nat} (M : TM k) (L : Lang) : Prop :=
  ∀ w, ∃ t, (M.run (initCfg k w) t).halted ∧ ((M.run (initCfg k w) t).state = 0 ↔ L w)

def TM.SpaceBounded {k : Nat} (M : TM k) (s : Nat → Nat) : Prop :=
  ∀ w t, Fits (s w.length) (M.run (initCfg k w) t)

def PSPACE (L : Lang) : Prop :=
  ∃ (k : Nat) (M : TM k) (s : Nat → Nat), IsPoly s ∧ M.Decides L ∧ M.SpaceBounded s

/-- Tape `0` starts with `out` followed by a blank. -/
def OutputIs {k : Nat} (h : 0 < k) (c : Cfg k) (out : List Bool) : Prop :=
  (∀ j (hj : j < out.length), c.cells ⟨0, h⟩ j = bitSym (out[j]'hj)) ∧ c.cells ⟨0, h⟩ out.length = 0

def PolyTimeComputable (f : List Bool → List Bool) : Prop :=
  ∃ (k : Nat) (h : 0 < k) (M : TM k) (T : Nat → Nat), IsPoly T ∧
    ∀ w, ∃ t, t ≤ T w.length ∧ (M.run (initCfg k w) t).state = 0 ∧ OutputIs h (M.run (initCfg k w) t) (f w)

/-- Polynomial-time many-one reducibility. -/
def Reduces (L L' : Lang) : Prop := ∃ f, PolyTimeComputable f ∧ ∀ w, L w ↔ L' (f w)

def PSPACEHard (L : Lang) : Prop := ∀ L', PSPACE L' → Reduces L' L

def PSPACEComplete (L : Lang) : Prop := PSPACE L ∧ PSPACEHard L

/-! ## Basic facts about runs -/

theorem TM.run_add {k : Nat} (M : TM k) (c : Cfg k) (t u : Nat) : M.run c (t + u) = M.run (M.run c t) u := by
  induction u with
  | zero => rfl
  | succ u ih => show M.step (M.run c (t + u)) = M.step (M.run (M.run c t) u); rw [ih]

theorem TM.step_halted {k : Nat} (M : TM k) {c : Cfg k} (h : c.halted) : M.step c = c := by
  simp [TM.step, h]

theorem TM.run_halted {k : Nat} (M : TM k) {c : Cfg k} (h : c.halted) : ∀ t, M.run c t = c
  | 0 => rfl
  | t + 1 => by simp only [TM.run, TM.run_halted M h t, TM.step_halted M h]

/-- Once halted, the run stays put. -/
theorem TM.run_stays {k : Nat} (M : TM k) (c : Cfg k) {t t' : Nat} (hle : t ≤ t') (h : (M.run c t).halted) :
    M.run c t' = M.run c t := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [TM.run_add, TM.run_halted M h]

end Complexity
