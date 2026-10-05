import Complexity.ListMachine

/-!
# Reasoning kit for list programs

`Runs Q p L L' T`: from `L` the program `p` continues in state `L'` within `T` steps (all visited states satisfy `Q`).
`Halts Q p L b L' T`: it stops with answer `b` in state `L'` within `T` steps. Composition rules, instruction rules and a
loop rule with an invariant and a decreasing measure.
-/

namespace Complexity

variable {k : Nat}

def Runs (Q : Lists k → Prop) (p : LProg k) (L L' : Lists k) (T : Nat) : Prop :=
  ∃ t, t ≤ T ∧ LExec Q p L t (.cont L')

def Halts (Q : Lists k → Prop) (p : LProg k) (L : Lists k) (b : Bool) (L' : Lists k) (T : Nat) : Prop :=
  ∃ t, t ≤ T ∧ LExec Q p L t (.stop b L')

section
variable {Q : Lists k → Prop}

theorem Runs.mono {p : LProg k} {L L' : Lists k} {T T' : Nat} (h : Runs Q p L L' T) (hT : T ≤ T') :
    Runs Q p L L' T' := let ⟨t, ht, hx⟩ := h; ⟨t, Nat.le_trans ht hT, hx⟩

theorem Halts.mono {p : LProg k} {L L' : Lists k} {b : Bool} {T T' : Nat} (h : Halts Q p L b L' T) (hT : T ≤ T') :
    Halts Q p L b L' T' := let ⟨t, ht, hx⟩ := h; ⟨t, Nat.le_trans ht hT, hx⟩

theorem Runs.seq {p q : LProg k} {L L₁ L₂ : Lists k} {T₁ T₂ : Nat} (h₁ : Runs Q p L L₁ T₁) (h₂ : Runs Q q L₁ L₂ T₂) :
    Runs Q (.seq p q) L L₂ (T₁ + T₂) :=
  let ⟨t₁, ht₁, hx₁⟩ := h₁; let ⟨t₂, ht₂, hx₂⟩ := h₂; ⟨t₁ + t₂, Nat.add_le_add ht₁ ht₂, .seqC hx₁ hx₂⟩

theorem Runs.seqH {p q : LProg k} {L L₁ L₂ : Lists k} {b : Bool} {T₁ T₂ : Nat} (h₁ : Runs Q p L L₁ T₁)
    (h₂ : Halts Q q L₁ b L₂ T₂) : Halts Q (.seq p q) L b L₂ (T₁ + T₂) :=
  let ⟨t₁, ht₁, hx₁⟩ := h₁; let ⟨t₂, ht₂, hx₂⟩ := h₂; ⟨t₁ + t₂, Nat.add_le_add ht₁ ht₂, .seqC hx₁ hx₂⟩

theorem Halts.seq {p q : LProg k} {L L₁ : Lists k} {b : Bool} {T : Nat} (h : Halts Q p L b L₁ T) :
    Halts Q (.seq p q) L b L₁ T :=
  let ⟨t, ht, hx⟩ := h; ⟨t, ht, .seqS hx⟩

theorem runs_push {i : Fin k} {e : Nat} {L : Lists k} (h₁ : Q L) (h₂ : Q (L.set i (L i ++ [e]))) :
    Runs Q (.push i e) L (L.set i (L i ++ [e])) 1 := ⟨1, Nat.le_refl _, .push h₁ h₂⟩

theorem runs_pop {i : Fin k} {L : Lists k} (h₁ : Q L) (h₂ : Q (L.set i (L i).dropLast)) :
    Runs Q (.pop i) L (L.set i (L i).dropLast) 1 := ⟨1, Nat.le_refl _, .pop h₁ h₂⟩

theorem runs_copy {i j : Fin k} {L : Lists k} (hij : i ≠ j) (h₁ : Q L)
    (h₂ : Q (L.set j (L j ++ (L i).getLast?.toList))) :
    Runs Q (.copy i j) L (L.set j (L j ++ (L i).getLast?.toList)) 1 := ⟨1, Nat.le_refl _, .copy hij h₁ h₂⟩

theorem halts_halt {b : Bool} {L : Lists k} (h : Q L) : Halts Q (.halt b) L b L 1 := ⟨1, Nat.le_refl _, .halt h⟩

theorem Runs.iteT {i : Fin k} {c : Nat → Bool} {p q : LProg k} {L L' : Lists k} {T : Nat} (hq : Q L)
    (hc : c (lastSym (L i)) = true) (h : Runs Q p L L' T) : Runs Q (.ite i c p q) L L' (T + 1) :=
  let ⟨t, ht, hx⟩ := h; ⟨t + 1, Nat.add_le_add_right ht 1, .iteT hq hc hx⟩

theorem Runs.iteF {i : Fin k} {c : Nat → Bool} {p q : LProg k} {L L' : Lists k} {T : Nat} (hq : Q L)
    (hc : c (lastSym (L i)) = false) (h : Runs Q q L L' T) : Runs Q (.ite i c p q) L L' (T + 1) :=
  let ⟨t, ht, hx⟩ := h; ⟨t + 1, Nat.add_le_add_right ht 1, .iteF hq hc hx⟩

theorem Halts.iteT {i : Fin k} {c : Nat → Bool} {p q : LProg k} {L L' : Lists k} {b : Bool} {T : Nat} (hq : Q L)
    (hc : c (lastSym (L i)) = true) (h : Halts Q p L b L' T) : Halts Q (.ite i c p q) L b L' (T + 1) :=
  let ⟨t, ht, hx⟩ := h; ⟨t + 1, Nat.add_le_add_right ht 1, .iteT hq hc hx⟩

theorem Halts.iteF {i : Fin k} {c : Nat → Bool} {p q : LProg k} {L L' : Lists k} {b : Bool} {T : Nat} (hq : Q L)
    (hc : c (lastSym (L i)) = false) (h : Halts Q q L b L' T) : Halts Q (.ite i c p q) L b L' (T + 1) :=
  let ⟨t, ht, hx⟩ := h; ⟨t + 1, Nat.add_le_add_right ht 1, .iteF hq hc hx⟩

/-- Loop rule: an invariant `I` (implying `Q`), a measure `μ` decreased by each pass of the body, each pass within `T`. -/
theorem runs_loop {i : Fin k} {c : Nat → Bool} {p : LProg k} {I : Lists k → Prop} {μ : Lists k → Nat} {T : Nat}
    (hQ : ∀ L, I L → Q L)
    (hbody : ∀ L, I L → c (lastSym (L i)) = true → ∃ L', Runs Q p L L' T ∧ I L' ∧ μ L' < μ L) :
    ∀ L, I L → ∃ L', Runs Q (.loop i c p) L L' ((μ L + 1) * (T + 1)) ∧ I L' ∧ c (lastSym (L' i)) = false := by
  intro L
  induction hm : μ L using Nat.strongRecOn generalizing L with
  | _ m ih =>
    intro hI
    cases hc : c (lastSym (L i)) with
    | false => exact ⟨L, ⟨1, by rw [Nat.add_mul]; have := Nat.zero_le (m * (T + 1)); omega,
        .loopF (hQ L hI) hc⟩, hI, hc⟩
    | true =>
      obtain ⟨L₁, ⟨t₁, ht₁, hx₁⟩, hI₁, hμ⟩ := hbody L hI hc
      obtain ⟨L', ⟨t₂, ht₂, hx₂⟩, hI', hc'⟩ := ih (μ L₁) (hm ▸ hμ) L₁ rfl hI₁
      refine ⟨L', ⟨t₁ + 1 + t₂, ?_, .loopC (hQ L hI) hc hx₁ hx₂⟩, hI', hc'⟩
      have : (μ L₁ + 1) * (T + 1) ≤ m * (T + 1) := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul]; omega

/-- Loop rule with a stopping body: if the invariant is kept until some pass halts. -/
theorem halts_loop {i : Fin k} {c : Nat → Bool} {p : LProg k} {I : Lists k → Prop} {μ : Lists k → Nat} {T : Nat}
    {R : Bool → Lists k → Prop}
    (hQ : ∀ L, I L → Q L)
    (hexit : ∀ L, I L → c (lastSym (L i)) = false → False)
    (hbody : ∀ L, I L → c (lastSym (L i)) = true →
      (∃ L', Runs Q p L L' T ∧ I L' ∧ μ L' < μ L) ∨ (∃ b L', Halts Q p L b L' T ∧ R b L')) :
    ∀ L, I L → ∃ b L', Halts Q (.loop i c p) L b L' ((μ L + 1) * (T + 1)) ∧ R b L' := by
  intro L
  induction hm : μ L using Nat.strongRecOn generalizing L with
  | _ m ih =>
    intro hI
    cases hc : c (lastSym (L i)) with
    | false => exact (hexit L hI hc).elim
    | true =>
      rcases hbody L hI hc with ⟨L₁, ⟨t₁, ht₁, hx₁⟩, hI₁, hμ⟩ | ⟨b, L', ⟨t₁, ht₁, hx₁⟩, hR⟩
      · obtain ⟨b, L', ⟨t₂, ht₂, hx₂⟩, hR⟩ := ih (μ L₁) (hm ▸ hμ) L₁ rfl hI₁
        refine ⟨b, L', ⟨t₁ + 1 + t₂, ?_, .loopC (hQ L hI) hc hx₁ hx₂⟩, hR⟩
        have : (μ L₁ + 1) * (T + 1) ≤ m * (T + 1) := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul]; omega
      · refine ⟨b, L', ⟨t₁ + 1, ?_, .loopS (hQ L hI) hc hx₁⟩, hR⟩
        rw [Nat.add_mul, Nat.one_mul]; have := Nat.zero_le (m * (T + 1)); omega

end

/-! ## Updating lists -/

@[simp] theorem Lists.set_same (L : Lists k) (i : Fin k) (l : List Nat) : (L.set i l) i = l := by
  simp [Lists.set]

theorem Lists.set_ne (L : Lists k) {i j : Fin k} (l : List Nat) (h : j ≠ i) : (L.set i l) j = L j := by
  simp [Lists.set, h]

theorem lastSym_append (l : List Nat) (e : Nat) : lastSym (l ++ [e]) = e + 4 := by
  simp [lastSym]

theorem lastSym_nil : lastSym [] = 3 := rfl

end Complexity
