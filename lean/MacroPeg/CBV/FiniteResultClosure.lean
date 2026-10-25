import MacroPeg.CBV.SequentialClock

/-! A finite vector of flat partial parser results reaches its least fixed
point after at most one round per entry. Both failure and success are defined
values; undefinedness is the bottom value, not failure. -/
namespace Shallot.MacroPeg.CBV.FiniteResultClosure

abbrev Vector (n : Nat) := Fin n → Res
def Le {n : Nat} (U V : Vector n) : Prop := ∀ i, RLe (U i) (V i)
def Monotone {n : Nat} (F : Vector n → Vector n) : Prop := ∀ U V, Le U V → Le (F U) (F V)
def rounds {n : Nat} (F : Vector n → Vector n) : Nat → Vector n
  | 0 => fun _ => none
  | k+1 => F (rounds F k)
def count {n : Nat} (V : Vector n) := ((List.finRange n).map (fun i => defined (V i))).sum

theorem count_le {n : Nat} (V : Vector n) : count V≤n := by
  have h := sum_le_length_mul (fun i : Fin n => defined (V i)) 1 (List.finRange n)
    (fun i _ => defined_le_one _)
  simpa [count] using h

theorem count_mono {n : Nat} {U V : Vector n} (h : Le U V) : count U≤count V :=
  sum_le_sum_of_le _ _ _ (fun i _ => defined_le (h i))

theorem eq_of_count_eq {n : Nat} {U V : Vector n} (h : Le U V) (hc : count U=count V) : U=V := by
  have hh := eq_of_sum_eq (fun i : Fin n => defined (U i)) (fun i => defined (V i))
    (List.finRange n) (fun i _ => defined_le (h i)) hc
  funext i
  have hi := hh i (List.mem_finRange i)
  rcases h i with hn|he
  · rw [hn] at hi ⊢
    cases hv : V i with
    | none => rfl
    | some r => simp [hv,defined] at hi
  · exact he

theorem rounds_step {n : Nat} (F : Vector n → Vector n) (hF : Monotone F) :
    ∀ k, Le (rounds F k) (rounds F (k+1))
  | 0 => by intro i; exact Or.inl rfl
  | k+1 => hF _ _ (rounds_step F hF k)

theorem plateau_exists {n : Nat} (F : Vector n → Vector n) (hF : Monotone F) :
    ∃ k, k≤n ∧ rounds F k=rounds F (k+1) := by
  apply Classical.byContradiction
  intro hnone
  have hlt (k : Nat) (hk : k≤n) : count (rounds F k)<count (rounds F (k+1)) := by
    apply Nat.lt_of_le_of_ne (count_mono (rounds_step F hF k))
    intro he
    exact hnone ⟨k,hk,eq_of_count_eq (rounds_step F hF k) he⟩
  have grow : ∀ k, k≤n+1 → k≤count (rounds F k) := by
    intro k
    induction k with
    | zero => intro _; omega
    | succ k ih => intro hk; have := ih (by omega); have := hlt k (by omega); omega
  have hg := grow (n+1) (Nat.le_refl _)
  have hb := count_le (rounds F (n+1))
  omega

theorem plateau_persists {n : Nat} (F : Vector n → Vector n) (k : Nat)
    (hk : rounds F k=rounds F (k+1)) : ∀ d, rounds F (k+d)=rounds F k
  | 0 => rfl
  | d+1 => by
    rw [show k+(d+1)=(k+d)+1 by omega,rounds,plateau_persists F k hk d]
    exact hk.symm

theorem fixed {n : Nat} (F : Vector n → Vector n) (hF : Monotone F) :
    F (rounds F n)=rounds F n := by
  obtain ⟨k,hk,he⟩ := plateau_exists F hF
  have h0 := plateau_persists F k he (n-k)
  have h1 := plateau_persists F k he (n+1-k)
  have h0 : rounds F n=rounds F k := by simpa only [Nat.add_sub_cancel' hk] using h0
  have h1 : rounds F (n+1)=rounds F k := by simpa only [Nat.add_sub_cancel' (show k≤n+1 by omega)] using h1
  exact h1.trans h0.symm

theorem least {n : Nat} (F : Vector n → Vector n) (hF : Monotone F) (V : Vector n) (hv : F V=V) :
    Le (rounds F n) V := by
  have h : ∀ k, Le (rounds F k) V := by
    intro k
    induction k with
    | zero => intro i; exact Or.inl rfl
    | succ k ih => simpa only [rounds,hv] using hF _ _ ih
  exact h n

end Shallot.MacroPeg.CBV.FiniteResultClosure
