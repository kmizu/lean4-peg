import MacroPeg.HigherOrder.Complete

/-!
# Higher-order Macro PEG recognition is decidable

For a typed grammar `G` and a closed parser `t`, `decideHO G t x` evaluates `t` in the finite model with the rule
values of the stopped iterate. It decides the observations of the call-by-name runs (`decideHO_iff`,
`decideHO_none_iff`).

How long it takes: the iteration stops after at most `maxEnv |x| R` rounds (`iter_stable`), where
`maxCount N (a ⇒ b) = |elems N a| · maxCount N b`, and the number of values grows as a tower
(`elems_length_le`: `|elems N p| ≤ (N+3)^(N+1)`, `|elems N (a ⇒ b)| ≤ |elems N b| ^ |elems N a|`). For a rule of
order `k` the arguments have order `< k`, so the rounds, and the table entries per round, are bounded by a `k`-fold
exponential in `|x|`: first-order rules give exponential time (as in `Decide.lean`), order 2 doubly exponential, and
so on. The running time is this bound times the size of the grammar; it is not formalized as a cost model.
-/

namespace Shallot.MacroPeg.HO

variable {R : List Ty}

/-- Decide a typed grammar: the result at the full input, in the stopped iterate. -/
def decideHO (G : TGrammar R) (t : Tm R [] .p) (x : List Char) : Res :=
  atq (den x t (iter x G (maxEnv x.length R)) ()) x.length

section Main

variable (G : TGrammar R) (t : Tm R [] .p) (x : List Char)

theorem decideHO_sound {r' : Option Nat} (h : decideHO G t x = some r') :
    HObs G.erase t.erase x (r'.map (sfx x)) :=
  sound_iter G t _ h

theorem decideHO_complete {r : Option (List Char)} (h : HObs G.erase t.erase x r) :
    decideHO G t x = some (r.map List.length) := by
  obtain ⟨n, hn⟩ := h
  exact complete_fix G t hn

/-- **Decidability**: `t` has a run on `x` with result `r` iff the decision procedure gives `r`'s length. -/
theorem decideHO_iff (r : Option (List Char)) :
    HObs G.erase t.erase x r ↔ ∃ r', decideHO G t x = some r' ∧ r'.map (sfx x) = r := by
  constructor
  · intro h
    refine ⟨_, decideHO_complete G t x h, ?_⟩
    obtain ⟨n, hn⟩ := h
    cases r with
    | none => rfl
    | some rest => exact congrArg some (sfx_of_suffix (hrun_suffix hn))
  · rintro ⟨r', h, rfl⟩
    exact decideHO_sound G t x h

theorem decideHO_none_iff : decideHO G t x = none ↔ ∀ r, ¬ HObs G.erase t.erase x r := by
  constructor
  · intro h r hr
    rw [decideHO_complete G t x hr] at h
    cases h
  · intro h
    cases hd : decideHO G t x with
    | none => rfl
    | some r' => exact absurd (decideHO_sound G t x hd) (h _)

end Main

/-- **Every well-typed grammar is decided**: for a well-typed grammar and a closed start parser, the decision
procedure of a typed version decides the observations. -/
theorem decide_wellTyped {g : HGrammar} (hg : g.WellTyped) {e : HExp} (he : HasTy g.types [] e .p) :
    ∃ (G : TGrammar g.types) (t : Tm g.types [] .p),
      ∀ x r, HObs g e x r ↔ ∃ r', decideHO G t x = some r' ∧ r'.map (sfx x) = r := by
  obtain ⟨G, hG⟩ := hg.toTGrammar
  obtain ⟨t, ht⟩ := he.toTm
  refine ⟨G, t, fun x r => ?_⟩
  have := decideHO_iff G t x r
  rwa [hG, ht] at this

/-! ## How many values -/

theorem length_allVecs {α : Type} (xs : List α) : ∀ m, (allVecs xs m).length = xs.length ^ m
  | 0 => rfl
  | m + 1 => by
    simp only [allVecs, List.length_flatMap, List.length_map, length_allVecs xs m]
    rw [List.map_const', sum_replicate_nat, Nat.pow_succ, Nat.mul_comm]

/-- The tower bounding the number of values: `(N+3)^(N+1)` parsers, `|b| ^ |a|` functions. -/
def sizeBound (N : Nat) : Ty → Nat
  | .p => (N + 3) ^ (N + 1)
  | .arr a b => sizeBound N b ^ sizeBound N a

theorem sizeBound_pos (N : Nat) : ∀ τ : Ty, 0 < sizeBound N τ
  | .p => Nat.pow_pos (by omega)
  | .arr a b => Nat.pow_pos (sizeBound_pos N b)

theorem elems_length_le (N : Nat) : ∀ τ : Ty, (elems N τ).length ≤ sizeBound N τ
  | .p => by
    show (allVecs (resElems N) (N + 1)).length ≤ _
    rw [length_allVecs]; simp [resElems, sizeBound]
  | .arr a b => by
    simp only [elems, sizeBound]
    refine Nat.le_trans (List.length_filter_le _ _) (Nat.le_trans (Nat.le_of_eq (length_allVecs (elems N b) _)) ?_)
    exact Nat.le_trans (Nat.pow_le_pow_left (elems_length_le N b) _)
      (Nat.pow_le_pow_right (sizeBound_pos N b) (elems_length_le N a))

/-- First-order rules: the rounds are at most exponential in `N`. -/
theorem maxCount_parsers (N : Nat) : ∀ n, maxCount N (Ty.parsers n) ≤ ((N + 3) ^ (N + 1)) ^ n * (N + 1)
  | 0 => by simp [maxCount, Ty.parsers]
  | n + 1 => by
    simp only [Ty.parsers, maxCount, Nat.pow_succ]
    have h₁ := elems_length_le N .p
    have h₂ := maxCount_parsers N n
    simp only [sizeBound] at h₁
    calc (elems N .p).length * maxCount N (Ty.parsers n)
        ≤ (N + 3) ^ (N + 1) * (((N + 3) ^ (N + 1)) ^ n * (N + 1)) := Nat.mul_le_mul h₁ h₂
      _ = ((N + 3) ^ (N + 1)) ^ n * (N + 3) ^ (N + 1) * (N + 1) := by
        rw [Nat.mul_comm ((N + 3) ^ (N + 1)), Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm (N + 1)]

end Shallot.MacroPeg.HO

namespace Shallot.MacroPeg.HO.DecideExamples

open Tm

/-- `A = λk. "a" (A k) / k`: a first-order rule. -/
def gA : TGrammar [.p ⇒ .p] :=
  ⟨(lam (alt (seq (chr 'a') (app (rule 0 rfl) (var 0 rfl))) (var 0 rfl)), ())⟩

def startA : Tm [.p ⇒ .p] [] .p := app (rule 0 rfl) (chr 'b')

-- The decision procedure agrees with the runs (on inputs of length 1 the model has 16 parser values).
#guard decideHO gA startA "b".toList = some (some 0)
#guard decideHO gA startA "a".toList = some none
#guard hrun gA.erase 20 startA.erase "b".toList = some (some [])
#guard hrun gA.erase 20 startA.erase "a".toList = some none

end Shallot.MacroPeg.HO.DecideExamples
