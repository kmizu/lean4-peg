import MacroPeg.Properties.DecideCBV

/-! Freeze physically stabilized helper rows while iterating user rows.
The frozen evaluator and actual grammar tables are cofinal in information
order; no frozen result is supplied as advice to a generated grammar. -/
namespace Shallot.MacroPeg.CBV.ClockFreezing

abbrev Table := Nat → List (List Char) → Val

def step (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) : Table :=
  fun i W => match ruleAtM g.rules i with
    | none => []
    | some r => (List.range (x.length+1)).map (fun p => evV g x s T W r.body p)

theorem step_physical (g : MGrammar) (x : List Char) (s : Strategy) (k : Nat) :
    step g x s (tblV g x s k) = tblV g x s (k+1) := by
  funext i W
  simp only [step,tblV]
  cases ruleAtM g.rules i <;> rfl

theorem step_mono (g : MGrammar) (x : List Char) (s : Strategy) {T U : Table}
    (h : TLeV T U) : TLeV (step g x s T) (step g x s U) := by
  intro i W p
  simp only [step]
  cases ruleAtM g.rules i with
  | none => exact RLe.refl _
  | some r =>
    rw [valAt_rangeMap,valAt_rangeMap]
    split
    · exact evV_mono h r.body p
    · exact RLe.refl _

def frozen (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool) (floor : Nat) : Nat → Table
  | 0 => fun i W => if pick i then tblV g x s floor i W else []
  | k+1 => fun i W => if pick i then tblV g x s floor i W else step g x s (frozen g x s pick floor k) i W

def StableRows (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool) (floor : Nat) : Prop :=
  ∀ k i, pick i = true → ∀ W, tblV g x s (floor+k) i W = tblV g x s floor i W

theorem frozen_rows (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool) (floor k i : Nat)
    (hi : pick i = true) (W : List (List Char)) :
    frozen g x s pick floor k i W = tblV g x s floor i W := by
  cases k <;> simp [frozen,hi]

/-- A non-helper rule spends exactly one user round. -/
theorem frozen_user_step (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor k i : Nat) (hi : pick i = false) (r : MRule) (hr : ruleAtM g.rules i = some r)
    (W : List (List Char)) (p : Nat) (hp : p ≤ x.length) :
    valAt (frozen g x s pick floor (k+1) i W) p =
      evV g x s (frozen g x s pick floor k) W r.body p := by
  simp only [frozen,hi,Bool.false_eq_true,if_false,step,hr,valAt_rangeMap,if_pos hp]

/-- Fixing rows at an actual finite stage never invents a result, even if
those rows have not yet stabilized. -/
theorem frozen_le_physical (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor k : Nat) : TLeV (frozen g x s pick floor k) (tblV g x s (floor+k)) := by
  induction k with
  | zero =>
    intro i W p
    simp only [frozen,Nat.add_zero]
    by_cases hi : pick i = true
    · simp only [hi,if_true]; exact RLe.refl _
    · simp only [hi,Bool.false_eq_true,if_false,valAt_nil]; exact Or.inl rfl
  | succ k ih =>
    intro i W p
    simp only [frozen]
    by_cases hi : pick i = true
    · simp only [hi,if_true]
      exact tblV_le g x s (by omega) i W p
    · simp only [hi,Bool.false_eq_true,if_false]
      have hh := step_mono g x s ih i W p
      simpa only [step_physical,Nat.add_assoc] using hh

theorem physical_le_frozen (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor : Nat) (hs : StableRows g x s pick floor) (k : Nat) :
    TLeV (tblV g x s k) (frozen g x s pick floor k) := by
  induction k with
  | zero => intro i W p; exact Or.inl rfl
  | succ k ih =>
    intro i W p
    by_cases hi : pick i = true
    · rw [frozen_rows g x s pick floor (k+1) i hi W]
      by_cases hk : k+1 ≤ floor
      · exact tblV_le g x s hk i W p
      · have he := hs (k+1-floor) i hi W
        have hn : floor+(k+1-floor) = k+1 := by omega
        rw [hn] at he
        exact Or.inr (congrArg (fun v => valAt v p) he)
    · have hh := step_mono g x s ih i W p
      simpa only [frozen,hi,Bool.false_eq_true,if_false,step_physical] using hh

theorem frozen_mono (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor : Nat) : ∀ k, TLeV (frozen g x s pick floor k) (frozen g x s pick floor (k+1))
  | 0 => by
    intro i W p
    by_cases hi : pick i = true
    · simp only [frozen,hi,if_true]; exact RLe.refl _
    · simp only [frozen,hi,Bool.false_eq_true,if_false,valAt_nil]; exact Or.inl rfl
  | k+1 => by
    intro i W p
    by_cases hi : pick i = true
    · simp only [frozen,hi,if_true]; exact RLe.refl _
    · have hh := step_mono g x s (frozen_mono g x s pick floor k) i W p
      simpa only [frozen,hi,Bool.false_eq_true,if_false] using hh

theorem frozen_ok (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor k : Nat) : OkTV x.length (frozen g x s pick floor k) := by
  intro i W p j hv
  exact tblV_ok g x s (floor+k) i W p j
    ((frozen_le_physical g x s pick floor k i W p).eq_of_some hv)

/-- The same finite successes and failures occur in both evaluations.
Undefinedness is not converted into a negative answer. -/
theorem defined_iff (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor : Nat) (hs : StableRows g x s pick floor) (E : List (List Char)) (e : MExp) (p : Nat)
    (v : Option Nat) :
    (∃ k, evV g x s (frozen g x s pick floor k) E e p = some v) ↔
      ∃ k, evV g x s (tblV g x s k) E e p = some v := by
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨floor+k,(evV_mono (frozen_le_physical g x s pick floor k) e p).eq_of_some hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,(evV_mono (physical_le_frozen g x s pick floor hs k) e p).eq_of_some hk⟩

theorem stable_defined_iff (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor : Nat) (hs : StableRows g x s pick floor) (e : MExp) (p : Nat) (hp : p ≤ x.length)
    (v : Option Nat) :
    (∃ k, evV g x s (frozen g x s pick floor k) [] e p = some v) ↔
      evV g x s (tblV g x s (iterBoundV g x)) [] e p = some v :=
  (defined_iff g x s pick floor hs [] e p v).trans (tblV_stable g x s hp)

theorem observations_iff {g : MGrammar} (hg : g.FirstOrder) (x : List Char) (s : Strategy)
    (hs : s ≠ .callByName) (pick : Nat → Bool) (floor : Nat) (hst : StableRows g x s pick floor)
    (e : MExp) (he : e.FirstOrder) (r : Option (List Char)) :
    SObs g s e x r ↔ ∃ k v, evV g x s (frozen g x s pick floor k) [] e x.length = some v ∧
      v.map (sfx x) = r := by
  rw [← decideObsV_iff hg hs he x r]
  constructor
  · intro h
    unfold decideObsV at h
    cases hv : evV g x s (tblV g x s (iterBoundV g x)) [] e x.length with
    | none => rw [hv] at h; cases h
    | some v =>
      obtain ⟨k,hk⟩ := (stable_defined_iff g x s pick floor hst e x.length (Nat.le_refl _) v).mpr hv
      refine ⟨k,v,hk,?_⟩
      rw [hv] at h
      cases v <;> simpa using h
  · rintro ⟨k,v,hk,hr⟩
    have hv := (stable_defined_iff g x s pick floor hst e x.length (Nat.le_refl _) v).mp ⟨k,hk⟩
    unfold decideObsV
    rw [hv]
    cases v <;> simpa using congrArg some hr

end Shallot.MacroPeg.CBV.ClockFreezing
