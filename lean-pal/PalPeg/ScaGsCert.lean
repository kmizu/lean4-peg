import PalPeg.ScaGsCoroutine

/-!
# Compiled tables simulate their coroutines, by certificate

`compileController` explores the coroutine's configurations and minimizes them into table rows.
A certificate lists the reachable configurations with their pending event, their row, and the
index of each successor. The checker `certOk` looks at each entry once: the row has the same
event, and stepping the coroutine on each response lands on the named successor, whose row is the
table's target (a return goes to the sink `0`). A true check gives the simulation `Sim`.
-/
set_option autoImplicit false
namespace PalPeg.ScaGsCert
open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine

/-- One reachable configuration of the coroutine. -/
structure Entry where
  event : Event
  config : Config
  row : Nat
  succ : List (Option Nat)
  deriving Repr

/-- The successor on one response is the named entry (or a return into the sink). -/
def succOk (vs : List Entry) (target : Nat) : Option Outcome → Option Nat → Bool
  | some (.returned _), none => target == 0
  | some (.yielded e c), some j =>
    match vs[j]? with
    | some v => v.event == e && v.config == c && v.row == target
    | none => false
  | _, _ => false

def entryOk (program : Program) (tests : List String) (vs : List Entry) (v : Entry) : Bool :=
  match program.code[v.row]? with
  | none => false
  | some row =>
    row.event == v.event &&
      (responsesFor tests v.event).length == row.targets.length &&
      (responsesFor tests v.event).length == v.succ.length &&
      ((List.range (responsesFor tests v.event).length).all fun k =>
        succOk vs (row.targets.getD k 0) (next v.config ((responsesFor tests v.event).getD k none))
          (v.succ.getD k none))

def certOk (program : Program) (tests : List String) (initial : Config) (vs : List Entry) : Bool :=
  (match vs[0]? with
    | some v0 => next initial none == some (.yielded v0.event v0.config) && v0.row == program.start
    | none => false) &&
  vs.all (entryOk program tests vs)

/-- The coroutine at `c` with pending event `e` is simulated by row `r`. -/
def Sim (vs : List Entry) (c : Config) (e : Event) (r : Nat) : Prop :=
  ∃ v ∈ vs, v.config = c ∧ v.event = e ∧ v.row = r

section
variable {program : Program} {tests : List String} {initial : Config} {vs : List Entry}

theorem sim_start (h : certOk program tests initial vs = true) :
    ∃ e c, next initial none = some (.yielded e c) ∧ Sim vs c e program.start := by
  simp only [certOk, Bool.and_eq_true] at h
  obtain ⟨h0, -⟩ := h
  cases hv : vs[0]? with
  | none => rw [hv] at h0; cases h0
  | some v0 =>
    rw [hv] at h0
    simp only [Bool.and_eq_true, beq_iff_eq] at h0
    exact ⟨v0.event, v0.config, h0.1, v0, List.mem_of_getElem? hv, rfl, rfl, h0.2⟩

/-- **The simulation step**: the row carries the coroutine's event, and every response leads to
the row the table names. -/
theorem sim_step (h : certOk program tests initial vs = true) {c : Config} {e : Event} {r : Nat}
    (hs : Sim vs c e r) :
    ∃ row, program.code[r]? = some row ∧ row.event = e ∧
      (responsesFor tests e).length = row.targets.length ∧
      ∀ k, k < (responsesFor tests e).length →
        (∃ val, next c ((responsesFor tests e).getD k none) = some (.returned val) ∧
            row.targets.getD k 0 = 0) ∨
        (∃ e' c', next c ((responsesFor tests e).getD k none) = some (.yielded e' c') ∧
            Sim vs c' e' (row.targets.getD k 0)) := by
  obtain ⟨v, hv, rfl, rfl, rfl⟩ := hs
  simp only [certOk, Bool.and_eq_true, List.all_eq_true] at h
  have hok := h.2 v hv
  unfold entryOk at hok
  cases hrow : program.code[v.row]? with
  | none => rw [hrow] at hok; cases hok
  | some row =>
    rw [hrow] at hok
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
    obtain ⟨⟨⟨hev, hlen⟩, -⟩, hall⟩ := hok
    refine ⟨row, rfl, hev, hlen, fun k hk => ?_⟩
    have hk' := hall k hk
    generalize next v.config ((responsesFor tests v.event).getD k none) = o at hk' ⊢
    generalize v.succ.getD k none = s at hk'
    unfold succOk at hk'
    rcases o with _ | ⟨e', c'⟩ | val <;> rcases s with _ | j <;> simp at hk'
    · cases hj : vs[j]? with
      | none => rw [hj] at hk'; cases hk'
      | some w =>
        rw [hj] at hk'
        simp only [Bool.and_eq_true, beq_iff_eq] at hk'
        exact .inr ⟨e', c', rfl, w, List.mem_of_getElem? hj, hk'.1.2, hk'.1.1, hk'.2⟩
    · exact .inl ⟨val, rfl, hk'⟩

end
end PalPeg.ScaGsCert
