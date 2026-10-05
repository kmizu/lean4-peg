import MacroPeg.HigherOrder.Mach.Rows
import MacroPeg.HigherOrder.Mach.ParseSpec
import MacroPeg.HigherOrder.Flat.Packed

/-!
# The packed evaluator on numbered items

The evaluator `stepF` needs, for an item, numbers that depend on types: the number of environments of its context
(`envNum`), the length of written-out values (`valNum`), the variable numbers over the environments (`varVecNum`)
and the rows of a type (`rowsNum`). Here they are computed from the arrow and context tables, and `stepM` is `stepF`
on numbered items (`MItem`): `stepM_eq`.
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

variable (N : Nat) (tt ct : List (Nat × Nat))

/-- The length of the written-out values of type number `k`. -/
def valNum : Nat → Nat
  | 0 => N + 1
  | k + 1 =>
    match tt[k]? with
    | some (a, b) => if a ≤ k ∧ b ≤ k then (rowsNum N tt a).length * valNum b else 0
    | none => 0
termination_by k => k
decreasing_by omega

/-- The number of environments of context number `c`. -/
def envNum : Nat → Nat
  | 0 => 1
  | k + 1 =>
    match ct[k]? with
    | some (par, t) => if par ≤ k then envNum par * (rowsNum N tt t).length else 0
    | none => 0
termination_by k => k
decreasing_by omega

/-- The numbers of variable `i` over the environments of context number `c`. -/
def varVecNum : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, i =>
    match ct[k]? with
    | some (par, t) =>
      if par ≤ k then
        match i with
        | 0 => (List.replicate (envNum N tt ct par) (List.range (rowsNum N tt t).length)).flatten
        | i + 1 => (varVecNum par i).flatMap (fun v => List.replicate (rowsNum N tt t).length v)
      else []
    | none => []
termination_by k => k
decreasing_by omega

/-! ## They agree with the types -/

variable {N tt ct}

theorem rowsNum_length {k : Nat} {τ : HO.Ty} (h : tyOf tt k = some τ) : (rowsNum N tt k).length = (elems N τ).length := by
  rw [rowsNum_eq N k h, eRows, List.length_map]

theorem valNum_eq : ∀ (k : Nat) {τ : HO.Ty}, tyOf tt k = some τ → valNum N tt k = valSize N τ
  | 0, τ, h => by rw [tyOf] at h; cases h; rw [valNum, valSize]
  | k + 1, τ, h => by
    rw [tyOf] at h
    split at h
    · rename_i a b hk
      split at h
      · rename_i hab
        split at h
        · rename_i σ ρ hσ hρ
          cases h
          rw [valNum]; simp only [hk]
          rw [if_pos hab, rowsNum_length hσ, valNum_eq b hρ, valSize]
        · cases h
      · cases h
    · cases h

theorem envNum_eq : ∀ (c : Nat) {Γ : List HO.Ty}, ctxOf tt ct c = some Γ → envNum N tt ct c = envSize N Γ
  | 0, Γ, h => by rw [ctxOf] at h; cases h; rw [envNum, envSize]
  | k + 1, Γ, h => by
    rw [ctxOf] at h
    split at h
    · rename_i par t hk
      split at h
      · rename_i hp
        split at h
        · rename_i τ Γ' hτ hΓ
          cases h
          rw [envNum]; simp only [hk]
          rw [if_pos hp, envNum_eq par hΓ, rowsNum_length hτ, envSize]
        · cases h
      · cases h
    · cases h

theorem varVecNum_eq : ∀ (c : Nat) {Γ : List HO.Ty}, ctxOf tt ct c = some Γ → ∀ i,
    varVecNum N tt ct c i = varVec N Γ i
  | 0, Γ, h, i => by rw [ctxOf] at h; cases h; rw [varVecNum]; cases i <;> rfl
  | k + 1, Γ, h, i => by
    rw [ctxOf] at h
    split at h
    · rename_i par t hk
      split at h
      · rename_i hp
        split at h
        · rename_i τ Γ' hτ hΓ
          cases h
          rw [varVecNum]; simp only [hk]
          rw [if_pos hp]
          cases i with
          | zero => dsimp only; rw [envNum_eq par hΓ, rowsNum_length hτ, varVec]
          | succ i => dsimp only; rw [varVecNum_eq par hΓ i, rowsNum_length hτ, varVec]
        · cases h
      · cases h
    · cases h

/-! ## One numbered item -/

section Step

variable (x : List Char) (tt ct : List (Nat × Nat)) (lt : List (List Nat)) (Tf : List (List Nat))

/-- One numbered item, on a stack of packed vectors. -/
def stepM (it : MItem) (st : List (List Nat)) : List (List Nat) :=
  let n := envNum x.length tt ct it.ctx
  match it.tag, st with
  | 5, vb :: va :: st =>
    (List.zipWith (seqCodes x) (chunksN (x.length + 1) n va) (chunksN (x.length + 1) n vb)).flatten :: st
  | 6, vb :: va :: st =>
    (List.zipWith (altCodes x) (chunksN (x.length + 1) n va) (chunksN (x.length + 1) n vb)).flatten :: st
  | 7, va :: st => ((chunksN (x.length + 1) n va).map (starCodes x)).flatten :: st
  | 8, va :: st => ((chunksN (x.length + 1) n va).map (notCodes x)).flatten :: st
  | 9, st =>
    ((varVecNum x.length tt ct it.ctx it.a).map
      (fun k => (rowsNum x.length tt ((varTy ct it.ctx it.a).getD 0)).getD k [])).flatten :: st
  | 10, st => (List.replicate n (Tf.getD it.a [])).flatten :: st
  | 11, st => st
  | 12, vy :: vf :: st =>
    (List.zipWith (fun fv yv => block (valNum x.length tt it.b) (indexIn yv (rowsNum x.length tt it.a)) fv)
      (chunksN ((rowsNum x.length tt it.a).length * valNum x.length tt it.b) n vf)
      (chunksN (valNum x.length tt it.a) n vy)).flatten :: st
  | _, st =>
    match opOf tt lt it with
    | some (.leaf e) => (List.replicate n (leafCodes x e)).flatten :: st
    | _ => st

end Step

end Shallot.MacroPeg.Mach
