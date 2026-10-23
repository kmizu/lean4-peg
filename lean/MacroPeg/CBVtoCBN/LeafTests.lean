import MacroPeg.CBVtoCBN.PartialTests

namespace Shallot.MacroPeg.CBVtoCBN

/-- First-order terminal expressions have total, grammar-independent matching behavior. -/
inductive Atom where
  | eps
  | any
  | chr (c : Char)
  | range (lo hi : Char)
  | lit (w : List Char)

def Atom.exp : Atom → MExp
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit w => .lit w

def Atom.run : Atom → List Char → Option (List Char)
  | .eps, x => some x
  | .any, [] => none
  | .any, _ :: xs => some xs
  | .chr _, [] => none
  | .chr c, d :: ds => if Shallot.beqChar c d then some ds else none
  | .range _ _, [] => none
  | .range lo hi, d :: ds => if Shallot.leChar lo d && Shallot.leChar d hi then some ds else none
  | .lit w, x => Shallot.stripPrefix? w x

theorem Atom.firstOrder (a : Atom) : a.exp.FirstOrder := by cases a <;> trivial

theorem Atom.obs (g : MGrammar) (a : Atom) (x : List Char) : MacroObs g a.exp x (a.run x) := by
  cases a with
  | eps => exact obs_eps x
  | any => cases x with
    | nil => exact obs_any_nil
    | cons c cs => exact obs_any_some c cs
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
    | none => simpa only [Atom.exp, Atom.run, he] using obs_lit_fail (g := g) he
    | some rest => exact ⟨_, .litOk w x rest he, by simp [Atom.run, he, MOutcome.restOf]⟩

theorem Atom.source (source : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (a : Atom) (p : Nat) (hp : p ≤ x.length) :
    evV source x s T E a.exp p = some ((a.run (sfx x p)).map List.length) := by
  cases a with
  | eps => simp only [Atom.exp, evV, Atom.run, Option.map_some, length_sfx x hp]
  | any =>
    simp only [Atom.exp, evV, Atom.run]
    cases sfx x p <;> rfl
  | chr c =>
    simp only [Atom.exp, evV, Atom.run]
    cases sfx x p with
    | nil => rfl
    | cons d ds => cases hb : Shallot.beqChar c d <;> simp [hb]
  | range lo hi =>
    simp only [Atom.exp, evV, Atom.run]
    cases sfx x p with
    | nil => rfl
    | cons d ds => cases hb : Shallot.leChar lo d && Shallot.leChar d hi <;> simp [hb]
  | lit w =>
    simp only [Atom.exp, evV, Atom.run]
    cases Shallot.stripPrefix? w (sfx x p) <;> rfl

/-- Test a terminal at a logical position and require its remaining input to have the selected length. -/
def terminalSuccessP (positionComplement remaining terminal : MExp) : MExp :=
  andP (.seq positionComplement (.seq terminal (exactLengthP remaining)))

def terminalFailureP (positionComplement terminal : MExp) : MExp :=
  andP (.seq positionComplement (.notP terminal))

theorem terminalSuccess_firstOrder {pre remaining terminal : MExp}
    (hp : pre.FirstOrder) (hr : remaining.FirstOrder) (ht : terminal.FirstOrder) :
    (terminalSuccessP pre remaining terminal).FirstOrder := ⟨hp, ht, hr, trivial⟩

theorem terminalFailure_firstOrder {pre terminal : MExp} (hp : pre.FirstOrder) (ht : terminal.FirstOrder) :
    (terminalFailureP pre terminal).FirstOrder := ⟨hp, ht⟩

/-- A finite terminal observation yields a total success-at-position predicate at the original input root. -/
theorem terminalSuccess_test {g : MGrammar} (x : List Char) (p q : Nat) (hp : p ≤ x.length)
    (terminal : MExp) (r : Option (List Char)) (ht : MacroObs g terminal (sfx x p) r) :
    RootTest g (terminalSuccessP (skipN (x.length - p)) (skipN q) terminal) x
      (r.map List.length = some q) := by
  classical
  have hpre : MacroObs g (skipN (x.length - p)) x (some (sfx x p)) := by
    simpa only [sfx, if_pos (show x.length - p ≤ x.length by omega)] using (skipN_rep g (x.length - p)) x
  apply RootTest.of_obs
  cases r with
  | none =>
    simp only [Option.map_none, reduceCtorEq, if_false]
    exact obs_and_none (obs_seq hpre (obs_seq_none ht))
  | some rest =>
    simp only [Option.map_some, Option.some.injEq]
    have he := exactLength_obs (skipN_rep g q) rest
    by_cases hq : rest.length = q
    · rw [if_pos hq]
      rw [if_pos hq.symm] at he
      exact obs_and_some (obs_seq hpre (obs_seq ht he))
    · rw [if_neg hq]
      rw [if_neg (Ne.symm hq)] at he
      exact obs_and_none (obs_seq hpre (obs_seq ht he))

theorem terminalFailure_test {g : MGrammar} (x : List Char) (p : Nat) (hp : p ≤ x.length)
    (terminal : MExp) (r : Option (List Char)) (ht : MacroObs g terminal (sfx x p) r) :
    RootTest g (terminalFailureP (skipN (x.length - p)) terminal) x (r = none) := by
  classical
  have hpre : MacroObs g (skipN (x.length - p)) x (some (sfx x p)) := by
    simpa only [sfx, if_pos (show x.length - p ≤ x.length by omega)] using (skipN_rep g (x.length - p)) x
  apply RootTest.of_obs
  cases r with
  | none => simpa only [if_true, terminalFailureP] using obs_and_some (obs_seq hpre (obs_not_none ht))
  | some rest => simpa only [reduceCtorEq, if_false, terminalFailureP] using obs_and_none (obs_seq hpre (obs_not_some ht))

/-- The terminal translation uses the same original character string for every source strategy and environment. -/
theorem atomSuccess_test (target source : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (a : Atom)
    (p q : Nat) (hp : p ≤ x.length) :
    RootTest target (terminalSuccessP (skipN (x.length - p)) (skipN q) a.exp) x
      (evV source x s T E a.exp p = some (some q)) := by
  rw [Atom.source source x s T E a p hp]
  simpa only [Option.some.injEq] using terminalSuccess_test x p q hp a.exp _ (a.obs target _)

theorem atomFailure_test (target source : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (a : Atom) (p : Nat) (hp : p ≤ x.length) :
    RootTest target (terminalFailureP (skipN (x.length - p)) a.exp) x
      (evV source x s T E a.exp p = some none) := by
  apply (terminalFailure_test x p hp a.exp _ (a.obs target _)).congr
  rw [Atom.source source x s T E a p hp]
  cases a.run (sfx x p) <;> simp

end Shallot.MacroPeg.CBVtoCBN
