import MacroPeg.CBV.GuardedReplayRotation

namespace Shallot.MacroPeg.CBV.GuardedReplayControl
open ClockFreezing (Table)

def Aligned (x w : List Char) (p q : Nat) : Prop :=
  p≤x.length ∧ q≤x.length ∧ sfx x p=w++sfx x q

def Results (R : Nat → Nat → Prop) : Option (Option Nat) → Option (Option Nat) → Prop
  | none,none | some none,some none => True
  | some (some p),some (some q) => R p q
  | _,_ => False

def bindValue (a : Option (Option Nat)) (f : Nat → Option (Option Nat)) :=
  match a with | some (some p) => f p | other => other

def altValue (a b : Option (Option Nat)) :=
  match a with | some none => b | other => other

def notValue (p : Nat) (a : Option (Option Nat)) :=
  match a with | some (some _) => some none | some none => some (some p) | none => none

theorem bind_results {R : Nat → Nat → Prop} {a b : Option (Option Nat)}
    (h : Results R a b) (F G : Nat → Option (Option Nat))
    (hF : ∀ p q, R p q → Results R (F p) (G q)) :
    Results R (bindValue a F) (bindValue b G) := by
  rcases a with _ | (_ | a) <;> rcases b with _ | (_ | b) <;> simp_all [Results,bindValue]

theorem alt_results {R : Nat → Nat → Prop} {a b c d : Option (Option Nat)}
    (h : Results R a b) (k : Results R c d) : Results R (altValue a c) (altValue b d) := by
  rcases a with _ | (_ | a) <;> rcases b with _ | (_ | b) <;> simp_all [Results,altValue]

theorem not_results {R : Nat → Nat → Prop} {a b : Option (Option Nat)}
    (h : Results R a b) (p q : Nat) (hpq : R p q) : Results R (notValue p a) (notValue q b) := by
  rcases a with _ | (_ | a) <;> rcases b with _ | (_ | b) <;> simp_all [Results,notValue]

theorem aligned_length {x w : List Char} {p q : Nat} (h : Aligned x w p q) : p=w.length+q := by
  have hl := congrArg List.length h.2.2
  rw [List.length_append,length_sfx x h.1,length_sfx x h.2.1] at hl
  exact hl

theorem aligned_replay (g : MGrammar) (x w : List Char) (s : Strategy) (T : Table)
    (p q : Nat) (h : Aligned x w p q) : evV g x s T [w] (.param 0) p=some (some q) := by
  simp only [evV,List.getElem?_cons_zero,(CBVtoCBN.stripPrefix_exact _ _ _).mpr h.2.2,length_sfx x h.2.1]

theorem aligned_of_replay (g : MGrammar) (x w : List Char) (s : Strategy) (T : Table)
    (p q : Nat) (hp : p≤x.length) (hv : evV g x s T [w] (.param 0) p=some (some q)) :
    Aligned x w p q := by
  obtain ⟨hq,he⟩ := SequenceArguments.success_prefix g x s T [w] (.param 0) True.intro p q hp hv
  have hw : w=pre x p q := by
    simpa [WordArguments.value] using WordArguments.value_of_success g x s T [w] (.param 0) True.intro p q hp hv
  exact ⟨hp,hq,hw ▸ he⟩

/-- Lifting a step relation to greedy partial repetition uses the actual
capture alignment to preserve strict decrease, including nullable divergence. -/
theorem star_results (x w : List Char) (F G : Nat → Option (Option Nat))
    (hStep : ∀ p q, Aligned x w p q → Results (Aligned x w) (F p) (G q)) :
    ∀ p q, Aligned x w p q → Results (Aligned x w) (evStar F p) (evStar G q) := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro q h
    have hr := hStep p q h
    cases hf : F p with
    | none =>
      cases hg : G q <;> simp [hf,hg,Results] at hr
      rw [evStar_none hf,evStar_none hg]; trivial
    | some a => cases a with
      | none =>
        cases hg : G q with
        | none => simp [hf,hg,Results] at hr
        | some b => cases b with
          | some z => simp [hf,hg,Results] at hr
          | none => rw [evStar_fail hf,evStar_fail hg]; exact h
      | some p' =>
        cases hg : G q with
        | none => simp [hf,hg,Results] at hr
        | some b => cases b with
          | none => simp [hf,hg,Results] at hr
          | some q' =>
            have hr : Aligned x w p' q' := by simpa [hf,hg,Results] using hr
            have hlen := aligned_length h
            have hlen' := aligned_length hr
            by_cases hd : p'<p
            · rw [evStar_ok hf hd,evStar_ok hg (by omega)]
              exact ih p' hd q' hr
            · rw [evStar_stuck hf hd,evStar_stuck hg (by omega)]
              trivial

end Shallot.MacroPeg.CBV.GuardedReplayControl
