import Shallot.Peg.Packrat.Domain

/-!
# A finite bound on iteration

Every nonstationary round fills a previously empty cell. There are only
`(dom g).length * (x.length + 1)` relevant cells (duplicates are harmless).
Thus the table has stabilized by `bound g x`.
-/

namespace Shallot.Packrat

/-- All relevant cells, with repetitions allowed. -/
def cells (g : Grammar) (x : List Char) : List (PExp × Nat) :=
  (dom g).flatMap fun e => (List.range (x.length + 1)).map fun i => (e, i)

theorem mem_cells {g : Grammar} {x : List Char} {e : PExp} {i : Nat} :
    (e, i) ∈ cells g x ↔ e ∈ dom g ∧ i ≤ x.length := by
  simp [cells, List.mem_flatMap, List.mem_map, List.mem_range, Nat.lt_succ_iff]

theorem length_cells (g : Grammar) (x : List Char) :
    (cells g x).length = (dom g).length * (x.length + 1) := by
  simp only [cells, List.length_flatMap, List.length_map, List.length_range]
  generalize dom g = es
  induction es with
  | nil => simp
  | cons e es ih => simp [ih, Nat.add_mul, Nat.add_comm]

/-- The number of filled entries, counted with the same multiplicities as `cells`. -/
def filled (g : Grammar) (x : List Char) (n : Nat) : Nat :=
  (cells g x).countP fun c => (iter g x n c.1 c.2).isSome

private theorem count_eq_pointwise {α : Type} (l : List α) (p q : α → Bool)
    (hm : ∀ a ∈ l, p a = true → q a = true)
    (heq : l.countP p = l.countP q) : ∀ a ∈ l, p a = q a := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hm' : ∀ b ∈ l, p b = true → q b = true :=
      fun b hb => hm b (List.mem_cons_of_mem a hb)
    have hle := List.countP_mono_left hm'
    have hhead : p a = q a := by
      cases hp : p a <;> cases hq : q a
      · rfl
      · simp only [List.countP_cons, hp, hq, Bool.false_eq_true, ↓reduceIte] at heq
        omega
      · have := hm a List.mem_cons_self hp
        simp [hq] at this
      · rfl
    have htail : l.countP p = l.countP q := by
      simp only [List.countP_cons, hhead] at heq
      omega
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hhead
    · exact ih hm' htail b hb

private theorem known_mono (g : Grammar) (x : List Char) (n : Nat) (c : PExp × Nat)
    (h : (iter g x n c.1 c.2).isSome = true) :
    (iter g x (n + 1) c.1 c.2).isSome = true := by
  cases hv : iter g x n c.1 c.2 with
  | none => simp [hv] at h
  | some r => simp [iter_mono hv (Nat.le_succ n)]

theorem filled_le (g : Grammar) (x : List Char) (n : Nat) :
    filled g x n ≤ (cells g x).length := List.countP_le_length

theorem filled_mono (g : Grammar) (x : List Char) (n : Nat) :
    filled g x n ≤ filled g x (n + 1) :=
  List.countP_mono_left fun c _ => known_mono g x n c

/-- If a round fills no new cells, its relevant entries are unchanged. -/
theorem agree_of_filled_eq {g : Grammar} {x : List Char} {n : Nat}
    (h : filled g x n = filled g x (n + 1)) : Agree g x n (n + 1) := by
  have hp := count_eq_pointwise (cells g x)
    (fun c => (iter g x n c.1 c.2).isSome)
    (fun c => (iter g x (n + 1) c.1 c.2).isSome)
    (fun c _ => known_mono g x n c) h
  intro e he i hi
  have hc := hp (e, i) (mem_cells.mpr ⟨he, hi⟩)
  cases hv : iter g x n e i with
  | some r => exact (iter_mono hv (Nat.le_succ n)).symm
  | none =>
    cases hv' : iter g x (n + 1) e i with
    | none => rfl
    | some r => simp [hv, hv'] at hc

/-- Some stationary round occurs by the number of cells. -/
theorem exists_stationary (g : Grammar) (x : List Char) :
    ∃ n, n ≤ (cells g x).length ∧ Agree g x n (n + 1) := by
  apply Classical.byContradiction
  intro h
  have hgrow : ∀ n, n ≤ (cells g x).length → filled g x n < filled g x (n + 1) := by
    intro n hn
    have hle := filled_mono g x n
    have hne : filled g x n ≠ filled g x (n + 1) := by
      intro heq
      exact h ⟨n, hn, agree_of_filled_eq heq⟩
    omega
  have hlower : ∀ n, n ≤ (cells g x).length + 1 → n ≤ filled g x n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hn
      have := ih (by omega)
      have := hgrow n (by omega)
      omega
  have := hlower ((cells g x).length + 1) (by omega)
  have := filled_le g x ((cells g x).length + 1)
  omega

/-- The explicit bound is a fixed point on all relevant cells. -/
theorem bound_stationary (g : Grammar) (x : List Char) :
    Agree g x (bound g x) (bound g x + 1) := by
  obtain ⟨n, hn, hs⟩ := exists_stationary g x
  have hnb : n ≤ bound g x := by rw [length_cells] at hn; unfold bound; omega
  have h₁ := agree_later hs (bound g x - n)
  have h₂ := agree_later hs (bound g x + 1 - n)
  have he₁ : n + (bound g x - n) = bound g x := by omega
  have he₂ : n + (bound g x + 1 - n) = bound g x + 1 := by omega
  rw [he₁] at h₁
  rw [he₂] at h₂
  intro e he i hi
  exact (h₁ e he i hi).symm.trans (h₂ e he i hi)

/-- All later rounds agree with the bounded computation. -/
theorem bound_fixed (g : Grammar) (x : List Char) (n : Nat) :
    Agree g x (bound g x) (bound g x + n) :=
  agree_later (bound_stationary g x) n

end Shallot.Packrat
