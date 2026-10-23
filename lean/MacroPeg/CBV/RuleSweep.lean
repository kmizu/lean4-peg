import MacroPeg.CBV.EnvSweep
import MacroPeg.CBV.Decide

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.KExp

def ruleValues (g : MGrammar) (s : Strategy) (x : List Char) (row : List Nat) (i : Nat) : List Nat :=
  match ruleAtM g.rules i with
  | none => []
  | some rule => envValues g s x row [] rule.body rule.arity

def ruleProgram {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (i : Nat) : NProg K :=
  match ruleAtM g.rules i with
  | none => nskip (r.get 3)
  | some rule => envSweepP r g s rule.arity rule.body rule.arity

def ruleCost (g : MGrammar) (i n : Nat) : Nat :=
  match ruleAtM g.rules i with
  | none => 2
  | some rule => envSweepCost g rule.arity rule.body rule.arity n

def ruleSweepP {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) : List Nat → NProg K
  | [] => nskip (r.get 3)
  | i :: is => .seq (ruleProgram r g s i) (ruleSweepP r g s is)

def ruleSweepCost (g : MGrammar) : List Nat → Nat → Nat
  | [], _ => 2
  | i :: is, n => ruleCost g i n + ruleSweepCost g is n

theorem ruleProgram_runs {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (x : List Char)
    (T : Nat → List (List Char) → Val) (hT : OkTV x.length T) (i : Nat) (S : Lists K)
    (ready : EvalReady r S x (pack g x T) []) :
    NRuns (ruleProgram r g s i) S (S.set (r.get 25) (S (r.get 25) ++ ruleValues g s x (pack g x T) i))
      (ruleCost g i x.length) := by
  cases hr : ruleAtM g.rules i with
  | none =>
    simpa only [ruleProgram, ruleValues, ruleCost, hr, List.append_nil, Lists.set_get_self] using nruns_skip (r.get 3) S
  | some rule =>
    have hx := envSweep_runs r g s x T hT rule.arity rule.body rule.arity [] (by simp)
      (by simp) S ready
    simpa only [ruleProgram, ruleValues, ruleCost, hr] using hx

/-- Static rule enumeration appends their entire computed rows, preserving the empty caller environment. -/
theorem ruleSweep_runs {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (x : List Char)
    (T : Nat → List (List Char) → Val) (hT : OkTV x.length T) :
    ∀ (is : List Nat) (S : Lists K), EvalReady r S x (pack g x T) [] →
    NRuns (ruleSweepP r g s is) S
      (S.set (r.get 25) (S (r.get 25) ++ is.flatMap (ruleValues g s x (pack g x T))))
      (ruleSweepCost g is x.length)
  | [], S, ready => by
    simpa only [ruleSweepP, ruleSweepCost, List.flatMap_nil, List.append_nil, Lists.set_get_self] using nruns_skip (r.get 3) S
  | i :: is, S, ready => by
    have xi := ruleProgram_runs r g s x T hT i S ready
    let V := S.set (r.get 25) (S (r.get 25) ++ ruleValues g s x (pack g x T) i)
    have xt := ruleSweep_runs r g s x T hT is V (ready.reserved 25 (by decide) _)
    have hv25 : V (r.get 25) = S (r.get 25) ++ ruleValues g s x (pack g x T) i := by simp [V]
    rw [hv25] at xt
    simp only [V, Lists.set_set_u, List.flatMap_cons, List.append_assoc] at xt ⊢
    exact xi.seq xt

theorem numericRound_ruleValues (g : MGrammar) (s : Strategy) (x : List Char) (row : List Nat) :
    numericRound s g x row = (List.range g.rules.length).flatMap (ruleValues g s x row) := by
  unfold numericRound keys
  rw [List.map_flatMap]
  apply congrArg (fun f : Nat → List Nat => (List.range g.rules.length).flatMap f)
  funext i
  cases hr : ruleAtM g.rules i with
  | none => simp [hr, ruleValues]
  | some rule =>
    simp [hr, ruleValues, envValues, positionValues, List.map_flatMap, List.map_map, Function.comp_def]

def roundProgram {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) : NProg K :=
  ruleSweepP r g s (List.range g.rules.length)

def roundCost (g : MGrammar) (n : Nat) : Nat := ruleSweepCost g (List.range g.rules.length) n

/-- One complete saturation round is performed by a real stack program, with no free table construction. -/
theorem roundProgram_runs {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (x : List Char)
    (T : Nat → List (List Char) → Val) (hT : OkTV x.length T) (S : Lists K)
    (ready : EvalReady r S x (pack g x T) []) :
    NRuns (roundProgram r g s) S
      (S.set (r.get 25) (S (r.get 25) ++ numericRound s g x (pack g x T))) (roundCost g x.length) := by
  rw [numericRound_ruleValues]
  exact ruleSweep_runs r g s x T hT (List.range g.rules.length) S ready

theorem ruleCost_poly (g : MGrammar) (i : Nat) : IsPoly (ruleCost g i) := by
  change IsPoly (fun n => ruleCost g i n)
  cases hr : ruleAtM g.rules i with
  | none => simpa only [ruleCost, hr] using isPoly_const 2
  | some rule => simpa only [ruleCost, hr] using envSweepCost_poly g rule.arity rule.body rule.arity

theorem ruleSweepCost_poly (g : MGrammar) : ∀ is, IsPoly (ruleSweepCost g is)
  | [] => isPoly_const 2
  | i :: is => isPoly_add (ruleCost_poly g i) (ruleSweepCost_poly g is)

theorem roundCost_poly (g : MGrammar) : IsPoly (roundCost g) := ruleSweepCost_poly g _

end Shallot.MacroPeg.CBV
