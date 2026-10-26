import MacroPeg.CBV.SequentialFiniteRows

/-! An actual finite table for unrestricted Seq evaluation. The keys depend
only on grammar arities and input length. Row computation queries the previous
finite list, never a canonical source rule table or an arbitrary-environment oracle.
The layer bound counts rule-table dependencies, not Boolean circuit depth or
cell probes for evaluating a row. -/
namespace Shallot.MacroPeg.CBV.SequentialFiniteEvaluator

open SequentialTupleKeys (Key keys values cursor)
open SequentialFiniteRows (Cell Correct Complete table)

def compute (g : MGrammar) (x : List Char) (previous : List Cell) (key : Key) : Res :=
  if cursor key.path ≤ x.length then
    match ruleAtM g.rules key.rule with
    | none => none
    | some r => evV g x .callByValueSeq (table x previous) (values x key.path) r.body (cursor key.path)
  else none

def cells (g : MGrammar) (x : List Char) : Nat → List Cell
  | 0 => (keys g x.length).map (fun key => ⟨key, none⟩)
  | m + 1 =>
    let previous := cells g x m
    (keys g x.length).map (fun key => ⟨key, compute g x previous key⟩)

theorem cells_complete (g : MGrammar) (x : List Char) (m : Nat) : Complete g x (cells g x m) := by
  intro key hk
  cases m <;> exact ⟨_, List.mem_map.mpr ⟨key, hk, rfl⟩, rfl⟩

theorem cells_correct (g : MGrammar) (x : List Char) : ∀ m,
    Correct x (tblV g x .callByValueSeq m) (cells g x m) := by
  intro m
  induction m with
  | zero =>
    intro c hc
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hc
    simp [tblV, valAt_nil]
  | succ m ih =>
    intro c hc
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hc
    change compute g x (cells g x m) key =
      valAt (tblV g x .callByValueSeq (m + 1) key.rule (values x key.path)) (cursor key.path)
    by_cases hp : cursor key.path ≤ x.length
    · cases hr : ruleAtM g.rules key.rule with
      | none => simp [compute, hp, hr, tblV, valAt_nil]
      | some r =>
        rw [compute, if_pos hp, hr, valAt_tblV_succ hr _ hp]
        exact (SequentialFiniteRows.expression_agree
          (SequentialClock.table_descending g x m)
          (SequentialFiniteRows.table_agree ih (cells_complete g x m)) _ _ _ hp).symm
    · cases hr : ruleAtM g.rules key.rule <;>
        simp [compute, hp, hr, tblV, valAt_rangeMap, valAt_nil]

def run (g : MGrammar) (x : List Char) (m : Nat) (E : List (List Char)) (e : MExp) (p : Nat) : Res :=
  evV g x .callByValueSeq (table x (cells g x m)) E e p

/-- Every physical clock, every valid position, every raw expression and
arbitrary incoming retained words. Only actual call tuples use finite keys. -/
theorem run_correct (g : MGrammar) (x : List Char) (m : Nat)
    (E : List (List Char)) (e : MExp) (p : Nat) (hp : p ≤ x.length) :
    run g x m E e p = evV g x .callByValueSeq (tblV g x .callByValueSeq m) E e p :=
  (SequentialFiniteRows.expression_agree (SequentialClock.table_descending g x m)
    (SequentialFiniteRows.table_agree (cells_correct g x m) (cells_complete g x m)) E e p hp).symm

def clock (g : MGrammar) (n : Nat) : Nat := SequentialClock.positionClock g n

def decide (g : MGrammar) (x : List Char) (e : MExp) : Option (Option (List Char)) :=
  match run g x (clock g x.length) [] e x.length with
  | none => none
  | some none => some none
  | some (some q) => some (some (sfx x q))

theorem decide_eq_standard (g : MGrammar) (x : List Char) (e : MExp) :
    decide g x e = decideObsV .callByValueSeq g x e := by
  unfold decide
  rw [run_correct g x _ [] e _ (Nat.le_refl _)]
  exact SequentialClock.decide_eq_standard g x e

theorem observations_iff (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (rest : Option (List Char)) :
    decide g x e = some rest ↔ SObs g .callByValueSeq e x rest := by
  rw [decide_eq_standard]
  exact decideObsV_iff hg (by decide) he x rest

theorem undefined_iff (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) : decide g x e = none ↔ ∀ rest, ¬SObs g .callByValueSeq e x rest := by
  rw [decide_eq_standard]
  exact decideObsV_none_iff hg (by decide) he x

theorem cells_length (g : MGrammar) (x : List Char) (m : Nat) :
    (cells g x m).length = (keys g x.length).length := by
  cases m <;> simp [cells]

theorem cells_length_le (g : MGrammar) (x : List Char) (m : Nat) :
    (cells g x m).length ≤ g.rules.length *
      (x.length + 1) ^ (SequentialStackPayload.arityBudget g + 1) := by
  rw [cells_length]
  exact SequentialTupleKeys.keys_length_le g x.length

theorem clock_linear (g : MGrammar) (n : Nat) :
    clock g n = (g.rules.length + 1) * (n + 1) := rfl

def producedCells (g : MGrammar) (x : List Char) : Nat → Nat
  | 0 => (cells g x 0).length
  | m + 1 => producedCells g x m + (cells g x (m + 1)).length

theorem producedCells_eq (g : MGrammar) (x : List Char) (m : Nat) :
    producedCells g x m = (m + 1) * (keys g x.length).length := by
  induction m with
  | zero => simp [producedCells, cells_length]
  | succ m ih => simp [producedCells, ih, cells_length, Nat.add_mul]

end Shallot.MacroPeg.CBV.SequentialFiniteEvaluator
