import Complexity.TM

/-!
# Turing machines as tables

A machine's transition function matters only on states below `nq` and symbols below `na`, so a machine is a finite
table (`tableOf`). The row of state `q` reading the symbols `rs` is number `q·na^k + rcode na rs`, where `rcode`
reads `rs` as digits in base `na`, least significant first (`digits_rcode`).

A finite configuration keeps, for every tape, its head and the cells written so far (`FCfg`); `fstep` is one step
of a table on it.
-/

namespace Complexity

/-! ## Digits in base `na` -/

/-- The number with the digits `rs` in base `na`, least significant first. -/
def rcode (na : Nat) : List Nat → Nat
  | [] => 0
  | a :: rs => a + na * rcode na rs

/-- The `k` lowest digits of `m` in base `na`, least significant first. -/
def digits (na : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, m => m % na :: digits na k (m / na)

theorem length_digits (na : Nat) : ∀ k m, (digits na k m).length = k
  | 0, _ => rfl
  | k + 1, m => by simp [digits, length_digits na k]

theorem rcode_lt {na : Nat} : ∀ {rs : List Nat}, (∀ a ∈ rs, a < na) → rcode na rs < na ^ rs.length
  | [], _ => by simp [rcode]
  | a :: rs, h => by
    have ha := h a (by simp)
    have ih := rcode_lt (rs := rs) (fun b hb => h b (by simp [hb]))
    simp only [rcode, List.length_cons, Nat.pow_succ]
    have : na * rcode na rs + na ≤ na * na ^ rs.length := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ih
    rw [Nat.mul_comm (na ^ rs.length)]; omega

/-- Digits read back: `digits` inverts `rcode` on digit lists. -/
theorem digits_rcode {na : Nat} : ∀ {rs : List Nat}, (∀ a ∈ rs, a < na) → digits na rs.length (rcode na rs) = rs
  | [], _ => rfl
  | a :: rs, h => by
    have ha := h a (by simp)
    have hpos : 0 < na := Nat.lt_of_le_of_lt (Nat.zero_le _) ha
    have ih := digits_rcode (rs := rs) (fun b hb => h b (by simp [hb]))
    simp only [List.length_cons, digits, rcode]
    have h₁ : (a + na * rcode na rs) % na = a := by
      rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt ha
    have h₂ : (a + na * rcode na rs) / na = rcode na rs := by
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt ha, Nat.zero_add]
    rw [h₁, h₂, ih]

theorem digits_lt {na : Nat} (hna : 0 < na) : ∀ k m, ∀ a ∈ digits na k m, a < na
  | 0, _ => by simp [digits]
  | k + 1, m => by
    intro a ha
    simp only [digits, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact Nat.mod_lt _ hna
    · exact digits_lt hna k _ a ha

/-! ## Tables -/

def Move.code : Move → Nat
  | .L => 0
  | .S => 1
  | .R => 2

def Move.ofCode : Nat → Move
  | 0 => .L
  | 1 => .S
  | _ => .R

theorem Move.ofCode_code (m : Move) : Move.ofCode m.code = m := by cases m <;> rfl

/-- A row of a table: new state, symbols to write, codes of the head moves. -/
abbrev Row := Nat × List Nat × List Nat

/-- A machine with `k` tapes as a table. -/
structure TTable where
  k : Nat
  nq : Nat
  na : Nat
  rows : List Row

/-- The number of the row of state `q` reading `rs`. -/
def TTable.idx (T : TTable) (q : Nat) (rs : List Nat) : Nat := q * T.na ^ T.k + rcode T.na rs

/-- The row of a machine for state `q` reading `rs`. -/
def rowOf {k : Nat} (M : TM k) (q : Nat) (rs : List Nat) : Row :=
  let d := M.delta q (fun i => rs.getD i.val 0)
  (d.1, List.ofFn d.2.1, List.ofFn (fun i => (d.2.2 i).code))

/-- The table of a machine. -/
def tableOf {k : Nat} (M : TM k) : TTable where
  k := k
  nq := M.nq
  na := M.na
  rows := (List.range (M.nq * M.na ^ k)).map fun m => rowOf M (m / M.na ^ k) (digits M.na k (m % M.na ^ k))

/-- The row of the table of `M` at the number of `(q, rs)` is the row of `M`. -/
theorem tableOf_row {k : Nat} (M : TM k) {q : Nat} {rs : List Nat} (hq : q < M.nq) (hl : rs.length = k)
    (hrs : ∀ a ∈ rs, a < M.na) : (tableOf M).rows[(tableOf M).idx q rs]? = some (rowOf M q rs) := by
  have hpos : 0 < M.na ^ k := Nat.pow_pos (by have := M.three_le_na; omega)
  have hr : rcode M.na rs < M.na ^ k := by have := rcode_lt hrs; rw [hl] at this; exact this
  have hlt : q * M.na ^ k + rcode M.na rs < M.nq * M.na ^ k := by
    have : (q + 1) * M.na ^ k ≤ M.nq * M.na ^ k := Nat.mul_le_mul_right _ hq
    rw [Nat.succ_mul] at this; omega
  simp only [tableOf, TTable.idx, List.getElem?_map, List.getElem?_range hlt, Option.map_some]
  congr 2
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    have := digits_rcode hrs
    rw [hl] at this; exact this

/-! ## Finite configurations -/

/-- A configuration with finitely many written cells: every tape is its head and its written cells. -/
structure FCfg where
  state : Nat
  pos : List Nat
  tapes : List (List Nat)

/-- The symbols under the heads. -/
def FCfg.reads (c : FCfg) : List Nat := (c.pos.zip c.tapes).map fun (p, t) => t.getD p 0

/-- Write `a` at cell `p` of a tape, extending it with blanks when needed. -/
def writeAt (t : List Nat) (p a : Nat) : List Nat :=
  if p < t.length then t.set p a else t ++ List.replicate (p - t.length) 0 ++ [a]

/-- One step of a table; halted configurations and missing rows do not change. -/
def fstep (T : TTable) (c : FCfg) : FCfg :=
  if c.state = 0 ∨ c.state = 1 then c
  else
    match T.rows[T.idx c.state c.reads]? with
    | none => c
    | some (q, ws, ms) =>
      { state := q
        pos := (c.pos.zip ms).map fun (p, m) => (Move.ofCode m).apply p
        tapes := ((c.tapes.zip c.pos).zip ws).map fun ((t, p), a) => writeAt t p a }

def frun (T : TTable) (c : FCfg) : Nat → FCfg
  | 0 => c
  | t + 1 => fstep T (frun T c t)

/-- The initial finite configuration on the bits `w`. -/
def finit (k : Nat) (w : List Bool) : FCfg where
  state := 2
  pos := List.replicate k 0
  tapes := List.ofFn fun i : Fin k => if i.val = 0 then w.map bitSym else []

end Complexity
