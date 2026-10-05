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

/-! ## `stepM` is `stepF` -/

section StepEq

variable {x : List Char} {tt ct : List (Nat × Nat)} {lt : List (List Nat)} {Tf : List (List Nat)}

theorem varRows_eq (hw : TTWF tt) {c : Nat} {Γ : List HO.Ty} (hΓ : ctxOf tt ct c = some Γ) (i : Nat) :
    rowsNum x.length tt ((varTy ct c i).getD 0) = eRows x.length (Γ.getD i .p) := by
  obtain ⟨hb, hle⟩ := varTy_ctx c hΓ i
  rcases hv : varTy ct c i with _ | t
  · rw [hv] at hb
    have : Γ[i]? = none := by simpa using hb.symm
    rw [Option.getD_none, List.getD_eq_getElem?_getD, this, Option.getD_none]
    exact rowsNum_eq x.length 0 (by rw [tyOf])
  · rw [hv] at hb
    obtain ⟨τ, hτ⟩ := tyOf_some hw t (hle t hv)
    rw [Option.bind_some, hτ] at hb
    rw [Option.getD_some, List.getD_eq_getElem?_getD, ← hb, Option.getD_some]
    exact rowsNum_eq x.length t hτ

/-- **The numbered evaluator agrees with the packed one.** -/
theorem stepM_eq (hw : TTWF tt) {it : MItem} {item : Item} (h : itemOf tt ct lt it = some item)
    (st : List (List Nat)) : stepM x tt ct lt Tf it st = stepF x Tf item st := by
  unfold itemOf at h
  split at h
  · rename_i op Γ hop hΓ
    cases h
    have hn : envNum x.length tt ct it.ctx = envSize x.length Γ := envNum_eq it.ctx hΓ
    have hop' := hop
    unfold opOf at hop
    unfold stepM
    simp only [hn]
    split at hop
    -- leaves
    all_goals first
      | (rename_i htag; cases hop; rw [htag]; simp only [hop', stepF]; done)
      | (rename_i htag; cases hop; rw [htag]; rcases st with _ | ⟨vb, _ | ⟨va, st⟩⟩ <;> simp [hop', stepF]; done)
      | (rename_i htag; cases hop; rw [htag]; simp only [stepF]; rw [varRows_eq hw hΓ, varVecNum_eq _ hΓ])
      | (rename_i htag; rw [htag]
         rcases hl : litOf lt it.a with _ | str
         · rw [hl] at hop; cases hop
         · rw [hl] at hop; cases hop; simp only [hop', stepF])
      | (rename_i htag; rw [htag]
         split at hop
         · rename_i a σ ha hσ
           cases hop
           rcases st with _ | ⟨vb, st⟩ <;> rfl
         · cases hop)
      | (rename_i htag; rw [htag]
         split at hop
         · rename_i a b ha hb
           cases hop
           rcases st with _ | ⟨vy, _ | ⟨vf, st⟩⟩
           · simp [hop', stepF]
           · simp [hop', stepF]
           · simp only [stepF]
             rw [rowsNum_eq x.length _ ha, valNum_eq _ hb, valNum_eq _ ha, eRows, List.length_map, valSize]
         · cases hop)
      | (cases hop)
      | skip
    all_goals done
  · cases h

end StepEq

end Shallot.MacroPeg.Mach
