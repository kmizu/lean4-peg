import Shallot.Peg.Packrat.Main

/-!
# Numeric entries for the stack machine

A stored success contains its absolute end position rather than its consumed
length. This makes sequence use the first result directly as the position
of the second lookup. Zero means unknown, one means failure, and `j + 2`
means success ending at position `j`.
-/

namespace Shallot.Packrat.Machine

/-- Encode a table entry at position `i` as a single natural number. -/
def code (i : Nat) : Option Res → Nat
  | none => 0
  | some none => 1
  | some (some k) => i + k + 2

/-- Numeric success has a unique consumed length at its starting position. -/
theorem code_eq_success (i k : Nat) (r : Option Res) :
    code i r = i + k + 2 ↔ r = some (some k) := by
  cases r with
  | none => simp [code]
  | some r =>
    cases r with
    | none => simp [code]
    | some m => simp only [code, Option.some.injEq]; omega

/-- The eventual machine checks the full-input endpoint, matching `Cfg.IsPEL`. -/
theorem start_full_iff (g : Grammar) (x : List Char) :
    code 0 (iter g x (bound g x) (.nt g.start) 0) = x.length + 2 ↔
      ∃ t, Derives g (.nt g.start) x (.ok t []) := by
  change code 0 (parse g x) = x.length + 2 ↔ _
  have hc : code 0 (parse g x) = x.length + 2 ↔ parse g x = some (some x.length) := by
    simpa only [Nat.zero_add] using code_eq_success 0 x.length (parse g x)
  exact hc.trans (by simpa only [fullAccepts, decide_eq_true_eq] using fullAccepts_iff g x)

/-- Numeric table entries are addressed by expression and input position. -/
abbrev Table := PExp → Nat → Nat

/-- Encode every entry of a function table. -/
def encode (T : Tbl) : Table := fun e i => code i (T e i)

/-- One round on numeric entries. Leaf tests are shared with `F`. -/
def step (g : Grammar) (x : List Char) (T : Table) : Table := fun e i =>
  match e with
  | .nt j => match ruleAt g.rules j with
    | none => 1
    | some b => T b i
  | .seq a b => match T a i with
    | 0 => 0
    | 1 => 1
    | j + 2 => T b j
  | .alt a b => match T a i with
    | 1 => T b i
    | r => r
  | .star a => match T a i with
    | 0 => 0
    | 1 => i + 2
    | j + 2 => match T (.star a) j with
      | 0 | 1 => 0
      | r => r
  | .notP a => match T a i with
    | 0 => 0
    | 1 => i + 2
    | _ => 1
  | e => code i (F g x (fun _ _ => none) e i)

/-- Absolute-position coding commutes with a table round. -/
theorem step_encode (g : Grammar) (x : List Char) (T : Tbl) (e : PExp) (i : Nat) :
    step g x (encode T) e i = code i (F g x T e i) := by
  cases e with
  | eps | any | chr _ | range _ _ | lit _ => rfl
  | nt j =>
    simp only [step, F]
    cases ruleAt g.rules j <;> rfl
  | seq a b =>
    simp only [step, encode, F]
    cases ha : T a i with
    | none => rfl
    | some r =>
      cases r with
      | none => rfl
      | some k =>
        simp only [code, Nat.add_succ, Nat.add_zero]
        cases T b (i + k) with
        | none => rfl
        | some s => cases s <;> simp [Nat.add_assoc]
  | alt a b =>
    simp only [step, encode, F]
    cases T a i with
    | none => rfl
    | some r => cases r <;> simp only [code, Nat.add_succ, Nat.add_zero]
  | star a =>
    simp only [step, encode, F]
    cases T a i with
    | none => rfl
    | some r =>
      cases r with
      | none => simp [code]
      | some k =>
        simp only [code, Nat.add_succ, Nat.add_zero]
        cases T (.star a) (i + k) with
        | none => rfl
        | some s => cases s <;> simp [Nat.add_assoc]
  | notP a =>
    simp only [step, encode, F]
    cases T a i with
    | none => rfl
    | some r => cases r <;> simp only [code, Nat.add_succ, Nat.add_zero]

/-- A numeric entry in a verified round cannot point beyond the input. -/
theorem code_bound {g : Grammar} {x : List Char} {n : Nat} {e : PExp} {i : Nat}
    (hi : i ≤ x.length) : code i (iter g x n e i) ≤ x.length + 2 := by
  cases h : iter g x n e i with
  | none => simp [code]
  | some r =>
    cases r with
    | none => simp [code]
    | some k =>
      have hk := iter_consumption h
      simp only [List.length_drop] at hk
      simp only [code]
      omega

/-- A numeric success points at or after its starting position. -/
theorem code_forward (T : Tbl) (e : PExp) (i j : Nat)
    (h : code i (T e i) = j + 2) : i ≤ j := by
  cases hv : T e i with
  | none => simp [hv, code] at h
  | some r => cases r <;> simp_all [code] <;> omega

/-- Rows store entries in input-position order. -/
def row (T : Tbl) (e : PExp) (n : Nat) : List Nat :=
  (List.range (n + 1)).map fun i => code i (T e i)

@[simp] theorem row_length (T : Tbl) (e : PExp) (n : Nat) :
    (row T e n).length = n + 1 := by simp [row]

theorem row_get (T : Tbl) (e : PExp) (n i : Nat) (hi : i ≤ n) :
    (row T e n)[i]'(by simp; omega) = code i (T e i) := by simp [row]

end Shallot.Packrat.Machine
