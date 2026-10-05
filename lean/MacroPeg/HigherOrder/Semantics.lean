import MacroPeg.HigherOrder.Syntax
import MacroPeg.Syntax
import Shallot.Peg.Props

/-!
# Higher-order Macro PEG: call-by-name semantics

A closed expression of type `p` is run on an input. PEG operators run as in a PEG. Anything else is first brought to
a PEG operator by *head reduction* (`step`): a rule is replaced by its body, and `(λ. b) a` by `b` with `a` put in for
the bound variable — the argument is not evaluated (call by name). An expression whose head cannot reduce (only possible
for an ill-typed or open expression) fails.

* `hrun g n e x`: the run with fuel `n` (one unit per step). `none` = out of fuel, `some none` = failure,
  `some (some r)` = success leaving `r`.
* `HObs g e x r`: some fuel gives the result `r`; `hrun_mono` and `hobs_det` make this a function of `(e, x)`.

Substitution: arguments that `step` puts in are closed (subterms of a closed expression), so `inst` needs no index
shifting; on closed arguments it is the usual capture-avoiding substitution.
-/

namespace Shallot.MacroPeg.HO

open Shallot (stripPrefix? beqChar leChar)

/-- Put the closed expression `a` in for the variable bound `k` binders above (`var k` at depth 0). -/
def HExp.inst (a : HExp) : Nat → HExp → HExp
  | k, .var i => if i = k then a else .var i
  | k, .lam τ b => .lam τ (HExp.inst a (k + 1) b)
  | k, .app f b => .app (HExp.inst a k f) (HExp.inst a k b)
  | k, .seq e₁ e₂ => .seq (HExp.inst a k e₁) (HExp.inst a k e₂)
  | k, .alt e₁ e₂ => .alt (HExp.inst a k e₁) (HExp.inst a k e₂)
  | k, .star e => .star (HExp.inst a k e)
  | k, .notP e => .notP (HExp.inst a k e)
  | _, e => e

/-- One step of head reduction, if the head is a rule or a lambda applied to an argument. -/
def step (g : HGrammar) : HExp → Option HExp
  | .rule i => (g.rules[i]?).map HRule.body
  | .app (.lam _ b) a => some (HExp.inst a 0 b)
  | .app f a => (step g f).map (fun f' => .app f' a)
  | _ => none

/-- The call-by-name run with fuel. -/
def hrun (g : HGrammar) : Nat → HExp → List Char → Option (Option (List Char))
  | 0, _, _ => none
  | n + 1, e, x =>
    match e with
    | .eps => some (some x)
    | .any =>
      match x with
      | [] => some none
      | _ :: rest => some (some rest)
    | .chr c =>
      match x with
      | [] => some none
      | d :: rest => if beqChar c d then some (some rest) else some none
    | .range lo hi =>
      match x with
      | [] => some none
      | d :: rest => if leChar lo d && leChar d hi then some (some rest) else some none
    | .lit s =>
      match stripPrefix? s x with
      | some rest => some (some rest)
      | none => some none
    | .seq a b =>
      match hrun g n a x with
      | some (some rest) => hrun g n b rest
      | r => r
    | .alt a b =>
      match hrun g n a x with
      | some none => hrun g n b x
      | r => r
    | .star a =>
      match hrun g n a x with
      | some (some rest) => hrun g n (.star a) rest
      | some none => some (some x)
      | none => none
    | .notP a =>
      match hrun g n a x with
      | some (some _) => some none
      | some none => some (some x)
      | none => none
    | e =>
      match step g e with
      | some e' => hrun g n e' x
      | none => some none

/-- `e` has a run on `x` with the result `r`. -/
def HObs (g : HGrammar) (e : HExp) (x : List Char) (r : Option (List Char)) : Prop := ∃ n, hrun g n e x = some r

/-! ## More fuel never changes a result -/

theorem hrun_mono {g : HGrammar} : ∀ {n : Nat} {e : HExp} {x : List Char} {r : Option (List Char)},
    hrun g n e x = some r → hrun g (n + 1) e x = some r
  | 0, _, _, _, h => by simp [hrun] at h
  | n + 1, e, x, r, h => by
    cases e <;> (rw [hrun.eq_def] at h ⊢; dsimp only at h ⊢)
    case eps | any | chr | range | lit => exact h
    case seq a b =>
      cases ha : hrun g n a x with
      | none => rw [ha] at h; cases h
      | some ra =>
        rw [ha] at h; rw [hrun_mono ha]
        cases ra with
        | none => exact h
        | some rest => exact hrun_mono h
    case alt a b =>
      cases ha : hrun g n a x with
      | none => rw [ha] at h; cases h
      | some ra =>
        rw [ha] at h; rw [hrun_mono ha]
        cases ra with
        | none => exact hrun_mono h
        | some rest => exact h
    case star a =>
      cases ha : hrun g n a x with
      | none => rw [ha] at h; cases h
      | some ra =>
        rw [ha] at h; rw [hrun_mono ha]
        cases ra with
        | none => exact h
        | some rest => exact hrun_mono h
    case notP a =>
      cases ha : hrun g n a x with
      | none => rw [ha] at h; cases h
      | some ra => rw [ha] at h; rw [hrun_mono ha]; exact h
    case var | rule | lam | app =>
      split at h
      · exact hrun_mono h
      · exact h

theorem hrun_mono_le {g : HGrammar} {n m : Nat} {e : HExp} {x : List Char} {r : Option (List Char)}
    (h : hrun g n e x = some r) (hnm : n ≤ m) : hrun g m e x = some r := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact hrun_mono ih

/-- The result of a run does not depend on the fuel. -/
theorem hobs_det {g : HGrammar} {e : HExp} {x : List Char} {r r' : Option (List Char)}
    (h : HObs g e x r) (h' : HObs g e x r') : r = r' := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, hm⟩ := h'
  have a := hrun_mono_le hn (Nat.le_max_left n m)
  have b := hrun_mono_le hm (Nat.le_max_right n m)
  rw [a] at b
  exact Option.some.inj b

/-! ## A success leaves a suffix of the input -/

theorem hrun_suffix {g : HGrammar} : ∀ {n : Nat} {e : HExp} {y r : List Char},
    hrun g n e y = some (some r) → ∃ p, y = p ++ r
  | 0, _, _, _, h => by simp [hrun] at h
  | n + 1, e, y, r, h => by
    cases e <;> (rw [hrun.eq_def] at h; dsimp only at h)
    case eps => cases h; exact ⟨[], rfl⟩
    case any =>
      cases y with
      | nil => cases h
      | cons c rest => cases h; exact ⟨[c], rfl⟩
    case chr c =>
      cases y with
      | nil => cases h
      | cons d rest =>
        dsimp only at h
        split at h
        · obtain rfl := Option.some.inj (Option.some.inj h); exact ⟨[d], rfl⟩
        · simp at h
    case range lo hi =>
      cases y with
      | nil => cases h
      | cons d rest =>
        dsimp only at h
        split at h
        · obtain rfl := Option.some.inj (Option.some.inj h); exact ⟨[d], rfl⟩
        · simp at h
    case lit s =>
      split at h
      · rename_i rest hs; cases h; exact Shallot.stripPrefix?_suffix s y _ hs
      · cases h
    case seq a b =>
      cases ha : hrun g n a y with
      | none => rw [ha] at h; cases h
      | some ra =>
        rw [ha] at h
        cases ra with
        | none => cases h
        | some m =>
          obtain ⟨p₁, rfl⟩ := hrun_suffix ha
          obtain ⟨p₂, rfl⟩ := hrun_suffix h
          exact ⟨p₁ ++ p₂, by simp⟩
    case alt a b =>
      cases ha : hrun g n a y with
      | none => rw [ha] at h; cases h
      | some ra =>
        rw [ha] at h
        cases ra with
        | none => exact hrun_suffix h
        | some m => cases h; exact hrun_suffix ha
    case star a =>
      cases ha : hrun g n a y with
      | none => rw [ha] at h; cases h
      | some ra =>
        rw [ha] at h
        cases ra with
        | none => cases h; exact ⟨[], rfl⟩
        | some m =>
          obtain ⟨p₁, rfl⟩ := hrun_suffix ha
          obtain ⟨p₂, rfl⟩ := hrun_suffix h
          exact ⟨p₁ ++ p₂, by simp⟩
    case notP a =>
      cases ha : hrun g n a y with
      | none => rw [ha] at h; cases h
      | some ra =>
        rw [ha] at h
        cases ra with
        | none => cases h; exact ⟨[], rfl⟩
        | some m => cases h
    case var | rule | lam | app =>
      split at h
      · exact hrun_suffix h
      · cases h

end Shallot.MacroPeg.HO
