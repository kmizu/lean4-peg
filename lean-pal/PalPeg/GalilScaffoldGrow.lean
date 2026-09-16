import PalPeg.GalilScaffoldCounter

set_option autoImplicit false
namespace PalPeg.GalilScaffoldGrow
open GalilScaffoldCounter

def add (n : ℕ) (c : Counter) : Counter := Nat.rec c (fun _ c => inc c) n

theorem add_value (n : ℕ) (c : Counter) : value (add n c) = value c+n := by
  induction n with
  | zero => simp [add]
  | succ n ih =>
    change value (inc (add n c)) = value c+(n+1 : ℕ)
    rw [inc_value,ih]
    push_cast
    omega

theorem add_canonical (n : ℕ) (c : Counter) (hc : Canonical c) : Canonical (add n c) := by
  induction n with
  | zero => exact hc
  | succ n ih => exact inc_canonical _ ih

structure State where
  work : Counter
  span : Counter
  debt : Counter

def step (x : State) : State := ⟨dec x.work,add 8 x.span,add 2 x.debt⟩

/-- Grow dispatch through its final zero-work test. Preparation's reset/load
operations on that final tick are handled separately. -/
inductive Grow : State → ℕ → State → Prop
  | stop (x : State) (h : positive x.work = false) : Grow x 1 x
  | next (x y : State) (k : ℕ) (h : positive x.work = true)
      (hr : Grow (step x) k y) : Grow x (k+1) y

theorem grow_exact (g : ℕ) (span debt : Counter)
    (hs : Canonical span) (hd : Canonical debt) :
    ∃ y, Grow ⟨ofNat g,span,debt⟩ (g+1) y ∧ y.work = ofNat 0 ∧
      value y.span = value span+8*g ∧ value y.debt = value debt+2*g ∧
      Canonical y.span ∧ Canonical y.debt := by
  induction g generalizing span debt with
  | zero =>
    exact ⟨⟨ofNat 0,span,debt⟩,.stop _ (by simp [positive,ofNat]),rfl,
      by simp,by simp,hs,hd⟩
  | succ g ih =>
    obtain ⟨y,hr,hw,hsv,hdv,hsc,hdc⟩ := ih (add 8 span) (add 2 debt)
      (add_canonical _ _ hs) (add_canonical _ _ hd)
    refine ⟨y,Grow.next _ _ _ (by simp [positive,ofNat,List.replicate_succ]) ?_,
      hw,?_,?_,hsc,hdc⟩
    · simpa [step,dec_ofNat_succ] using hr
    · rw [add_value] at hsv
      push_cast
      omega
    · rw [add_value] at hdv
      push_cast
      omega

def afterMatch (b : Bool) (x : State) : State :=
  if b then {x with debt := dec x.debt} else x

/-- Grow's update precedes the outer advanceMatch update on each tick. -/
def paced : List Bool → State → State
  | [],x => x
  | b :: bs,x => paced bs (afterMatch b (if positive x.work then step x else x))

theorem afterMatch_value (b : Bool) (x : State) :
    value (afterMatch b x).debt = value x.debt - (if b then 1 else 0) := by
  cases b <;> simp [afterMatch,dec_value]

theorem paced_values (bs : List Bool) (g : ℕ) (span debt : Counter) (hb : bs.length ≤ g) :
    (paced bs ⟨ofNat g,span,debt⟩).work = ofNat (g-bs.length) ∧
    value (paced bs ⟨ofNat g,span,debt⟩).span = value span+8*bs.length ∧
    value (paced bs ⟨ofNat g,span,debt⟩).debt = value debt+2*bs.length-bs.count true := by
  induction bs generalizing g span debt with
  | nil => simp [paced]
  | cons b bs ih =>
    cases g with
    | zero => simp at hb
    | succ g =>
      have hr := ih g (add 8 span) (if b then dec (add 2 debt) else add 2 debt) (by simpa using hb)
      have hp : positive (ofNat (g+1)) = true := by simp [positive,ofNat,List.replicate_succ]
      rw [paced]
      cases b <;> simp only [hp,ite_true,step,afterMatch,Bool.false_eq_true,
        ite_false,dec_ofNat_succ] at hr ⊢
      all_goals
        obtain ⟨hw,hs,hd⟩ := hr
        refine ⟨?_,?_,?_⟩
        · simpa using hw
        · simp only [add_value] at hs
          simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
          omega
        · simp only [add_value,dec_value] at hd
          simp
          omega

/-- After grow work is exhausted, the projected counters retain only the
outer advance decrements. This covers the debt projection of preparation/run,
provided no later double or restart occurs. -/
theorem paced_zero (bs : List Bool) (span debt : Counter) :
    (paced bs ⟨ofNat 0,span,debt⟩).work = ofNat 0 ∧
    (paced bs ⟨ofNat 0,span,debt⟩).span = span ∧
    value (paced bs ⟨ofNat 0,span,debt⟩).debt = value debt-bs.count true := by
  induction bs generalizing debt with
  | nil => simp [paced]
  | cons b bs ih =>
    cases b <;> simp only [paced,positive,ofNat,List.replicate_zero,List.isEmpty_nil,
      Bool.not_true,Bool.false_eq_true,ite_false,afterMatch,ite_true]
    · exact ih debt
    · obtain ⟨hw,hs,hd⟩ := ih (dec debt)
      refine ⟨hw,hs,?_⟩
      rw [dec_value] at hd
      simp only [List.count_cons_self,Nat.cast_add,Nat.cast_one]
      change value (paced bs ⟨ofNat 0,span,dec debt⟩).debt = _
      omega

theorem paced_append (xs ys : List Bool) (x : State) :
    paced (xs ++ ys) x = paced ys (paced xs x) := by
  induction xs generalizing x with
  | nil => rfl
  | cons b bs ih => exact ih _

/-- Grow followed by any number of debt-only ticks: the full advance count
appears in the ledger, not just the prefix during positive work. -/
theorem paced_stage (growAdv laterAdv : List Bool) (span debt : Counter) :
    value (paced (growAdv ++ laterAdv) ⟨ofNat growAdv.length,span,debt⟩).debt =
      value debt+2*growAdv.length-(growAdv ++ laterAdv).count true := by
  have hp := paced_values growAdv growAdv.length span debt (le_refl _)
  rw [Nat.sub_self] at hp
  rw [paced_append]
  let x := paced growAdv ⟨ofNat growAdv.length,span,debt⟩
  have hx : x = ⟨ofNat 0,x.span,x.debt⟩ := by
    have hw : x.work = ofNat 0 := hp.1
    rw [← hw]
  change value (paced laterAdv x).debt = _
  rw [hx]
  have hz := (paced_zero laterAdv x.span x.debt).2.2
  rw [hz]
  change value (paced growAdv ⟨ofNat growAdv.length,span,debt⟩).debt - _ = _
  rw [hp.2.2,List.count_append]
  push_cast
  omega

#print axioms paced_stage
#print axioms paced_values
#print axioms grow_exact
end PalPeg.GalilScaffoldGrow
