import MacroPeg.CBV.ParSimulation.Control
import MacroPeg.CBVtoCBN.LeafTests

namespace Shallot.MacroPeg.CBV.ParSimulation

open RootObservation PrefixCounters
open CBVtoCBN (Atom)

theorem atom_observation (g : MGrammar) (s : Strategy) (a : Atom) (x : List Char) :
    SObs g s a.exp x (a.run x) := by
  cases a with
  | eps => exact ⟨_, .eps x, rfl⟩
  | any => cases x with
    | nil => exact ⟨_, .anyFail, rfl⟩
    | cons c cs => exact ⟨_, .anyOk c cs, rfl⟩
  | chr c => cases x with
    | nil => exact ⟨_, .chrEmpty c, rfl⟩
    | cons d ds =>
      cases he : Shallot.beqChar c d with
      | false => exact ⟨_, .chrFail c d ds he, by simp [Atom.run, he, MOutcome.restOf]⟩
      | true => exact ⟨_, .chrOk c d ds he, by simp [Atom.run, he, MOutcome.restOf]⟩
  | range lo hi => cases x with
    | nil => exact ⟨_, .rangeEmpty lo hi, rfl⟩
    | cons d ds =>
      cases he : Shallot.leChar lo d && Shallot.leChar d hi with
      | false => exact ⟨_, .rangeFail lo hi d ds he, by simp [Atom.run, he, MOutcome.restOf]⟩
      | true => exact ⟨_, .rangeOk lo hi d ds he, by simp [Atom.run, he, MOutcome.restOf]⟩
  | lit w => cases he : Shallot.stripPrefix? w x with
    | none => exact ⟨_, .litFail _ _ he, by simp [Atom.run, he, MOutcome.restOf]⟩
    | some rest => exact ⟨_, .litOk _ _ _ he, by simp [Atom.run, he, MOutcome.restOf]⟩

def terminalSuccess (equal : Nat) (position finish : MExp) (a : Atom) : MExp :=
  endpoint equal position finish a.exp

def terminalFailure (position : MExp) (a : Atom) : MExp :=
  atPosition position (.notP a.exp)

theorem terminalSuccess_firstOrder (equal : Nat) {p q : MExp}
    (hp : p.FirstOrder) (hq : q.FirstOrder) (a : Atom) :
    (terminalSuccess equal p q a).FirstOrder := ⟨⟨hp, a.firstOrder⟩, hq, trivial⟩

theorem terminalFailure_firstOrder {p : MExp} (hp : p.FirstOrder) (a : Atom) :
    (terminalFailure p a).FirstOrder := ⟨hp, a.firstOrder⟩

private theorem suffix_length_iff {g : MGrammar} {e : MExp} {x rest : List Char} {p : Nat}
    (h : SObs g .callByValuePar e (sfx x p) (some rest))
    (q : Nat) (hq : q ≤ x.length) : rest = sfx x q ↔ rest.length = q := by
  obtain ⟨o, hd, ho⟩ := h
  cases o with
  | fail => cases ho
  | ok t y =>
    have hy := Option.some.inj ho
    subst y
    obtain ⟨pref, hx⟩ := mderives_suffix hd t rest rfl
    have hwhole : x = (x.take (x.length - p) ++ pref) ++ rest := by
      calc
        x = x.take (x.length - p) ++ sfx x p := (List.take_append_drop _ _).symm
        _ = x.take (x.length - p) ++ (pref ++ rest) := congrArg (fun ys => x.take (x.length - p) ++ ys) hx
        _ = (x.take (x.length - p) ++ pref) ++ rest := (List.append_assoc _ _ _).symm
    constructor
    · intro he
      rw [he, length_sfx x hq]
    · intro he
      have hs := sfx_suffix hwhole
      rw [he] at hs
      exact hs.symm

/-- Every native source terminal has an exact success-at-endpoint test in
Par, for every source strategy, table approximation and captured environment. -/
theorem terminal_success_test {g : MGrammar} {equal : Nat}
    (he : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (source : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char))
    (a : Atom) (p q : Nat) (hp : p ≤ x.length) (hq : q ≤ x.length) :
    Predicate g .callByValuePar
      (terminalSuccess equal (.lit (x.take (x.length - p))) (.lit (x.take (x.length - q))) a) x
      (evV source x s T E a.exp p = some (some q)) := by
  rw [Atom.source source x s T E a p hp]
  have ht := atom_observation g .callByValuePar a (sfx x p)
  cases hRun : a.run (sfx x p) with
  | none =>
    rw [hRun] at ht
    have h := endpoint_failure he (p := x.length - p) (q := x.length - q) ht
    apply Predicate.of_obs
    simpa only [Option.map_none, Option.some.injEq, reduceCtorEq, ite_false, terminalSuccess] using h
  | some rest =>
    rw [hRun] at ht
    have h := endpoint_success he (p := x.length - p) (q := x.length - q) (by omega) ht
    have hEq := suffix_length_iff ht q hq
    apply Predicate.of_obs
    simpa only [terminalSuccess, Option.map_some, Option.some.injEq,
      show x.drop (x.length - q) = sfx x q from rfl, hEq] using h

theorem terminal_failure_test (g source : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char))
    (a : Atom) (p : Nat) (hp : p ≤ x.length) :
    Predicate g .callByValuePar (terminalFailure (.lit (x.take (x.length - p))) a) x
      (evV source x s T E a.exp p = some none) := by
  rw [Atom.source source x s T E a p hp]
  have ht := atom_observation g .callByValuePar a (sfx x p)
  have hl : SObs g .callByValuePar (.lit (x.take (x.length - p))) x (some (sfx x p)) :=
    ⟨_, literal_take g .callByValuePar x (x.length - p), rfl⟩
  cases hRun : a.run (sfx x p) with
  | none =>
    rw [hRun] at ht
    have h := peek_success (seq_ok hl (not_fail ht))
    apply Predicate.of_obs
    simpa only [terminalFailure, atPosition, Test, Option.map_none, ite_true] using h
  | some rest =>
    rw [hRun] at ht
    have h := peek_failure (seq_ok hl (not_ok ht))
    apply Predicate.of_obs
    simpa only [terminalFailure, atPosition, Test, Option.map_some,
      Option.some.injEq, reduceCtorEq, ite_false] using h

end Shallot.MacroPeg.CBV.ParSimulation
