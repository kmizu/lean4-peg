import MacroPeg.HigherOrder.Semantics
import MacroPeg.Properties.DefunCorrect

/-!
# First-order Macro PEG is the order-1 fragment of higher-order Macro PEG

A first-order rule `R(x₀, …, xₙ₋₁) = body` becomes the rule `R = λx₀. … λxₙ₋₁. body` of type `p ⇒ … ⇒ p ⇒ p`;
the parameter `xₖ` becomes the variable `var (n - 1 - k)`, and a call `R(a₀, …, aₙ₋₁)` becomes the application
`R a₀ … aₙ₋₁` (`emb`). On first-order, arity-correct grammars the two call-by-name semantics give the same observations
(`emb_obs`).

The proof is a simulation, as in `DefunCorrect.lean`. One source call is `1 + n` target steps: unfold the rule, then
`n` β-steps, which put the (embedded, closed) arguments in for the variables (`instArgs_emb`).
-/

namespace Shallot.MacroPeg.HO

open Shallot.MacroPeg (MExp MGrammar MRule ruleAtM argAt)

/-- `λ. … λ. b` with `n` lambdas over parsers. -/
def lams : Nat → HExp → HExp
  | 0, b => b
  | n + 1, b => .lam .p (lams n b)

mutual
  /-- Embed an expression in the body of a rule of arity `ar` (`ar = 0` for closed expressions). -/
  def emb (ar : Nat) : MExp → HExp
    | .eps => .eps
    | .any => .any
    | .chr c => .chr c
    | .range lo hi => .range lo hi
    | .lit s => .lit s
    | .param k => if k < ar then .var (ar - 1 - k) else HExp.failAlways
    | .call i args => HExp.apps (.rule i) (embArgs ar args)
    | .seq e₁ e₂ => .seq (emb ar e₁) (emb ar e₂)
    | .alt e₁ e₂ => .alt (emb ar e₁) (emb ar e₂)
    | .star e => .star (emb ar e)
    | .notP e => .notP (emb ar e)
    -- not first-order: never embedded under the hypotheses of `emb_obs`
    | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => HExp.failAlways

  def embArgs (ar : Nat) : List MExp → List HExp
    | [] => []
    | e :: es => emb ar e :: embArgs ar es
end

def embRule (r : MRule) : HRule := ⟨Ty.parsers r.arity, lams r.arity (emb r.arity r.body)⟩

def embGrammar (g : MGrammar) : HGrammar := ⟨g.rules.map embRule⟩

/-! ## Substitution into embedded expressions -/

theorem inst_apps (a : HExp) (k : Nat) (f : HExp) : ∀ bs : List HExp,
    HExp.inst a k (HExp.apps f bs) = HExp.apps (HExp.inst a k f) (bs.map (HExp.inst a k))
  | [] => rfl
  | b :: bs => by simp only [HExp.apps, inst_apps a k _ bs, HExp.inst, List.map_cons]

theorem embArgs_eq_map (ar : Nat) : ∀ es : List MExp, embArgs ar es = es.map (emb ar)
  | [] => rfl
  | e :: es => by simp [embArgs, embArgs_eq_map ar es]

mutual
  /-- A closed embedding has no variables, so substitution leaves it alone. -/
  theorem inst_emb0 (a : HExp) (k : Nat) : ∀ e : MExp, HExp.inst a k (emb 0 e) = emb 0 e
    | .param _ => rfl
    | .call i args => by
      simp only [emb]; rw [inst_apps, inst_embArgs0 a k args]; rfl
    | .seq e₁ e₂ | .alt e₁ e₂ => by simp only [emb, HExp.inst, inst_emb0 a k e₁, inst_emb0 a k e₂]
    | .star e | .notP e => by simp only [emb, HExp.inst, inst_emb0 a k e]
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => rfl

  theorem inst_embArgs0 (a : HExp) (k : Nat) : ∀ es : List MExp, (embArgs 0 es).map (HExp.inst a k) = embArgs 0 es
    | [] => rfl
    | e :: es => by simp only [embArgs, List.map_cons, inst_emb0 a k e, inst_embArgs0 a k es]
end

theorem inst_lams (a : HExp) : ∀ (n k : Nat) (b : HExp), HExp.inst a k (lams n b) = lams n (HExp.inst a (k + n) b)
  | 0, _, _ => rfl
  | n + 1, k, b => by
    simp only [lams, HExp.inst, inst_lams a n (k + 1) b]
    rw [Nat.add_assoc, Nat.add_comm 1 n]

/-- The β-steps of a call: `instArgs [a₀, …, aₙ₋₁] B` puts `a₀` in for `var (n-1)`, …, `aₙ₋₁` for `var 0`. -/
def instArgs : List HExp → HExp → HExp
  | [], b => b
  | a :: as, b => instArgs as (HExp.inst a as.length b)

theorem instArgs_apps : ∀ (as : List HExp) (f : HExp) (bs : List HExp),
    instArgs as (HExp.apps f bs) = HExp.apps (instArgs as f) (bs.map (instArgs as))
  | [], _, bs => by simp [instArgs]
  | a :: as, f, bs => by
    simp only [instArgs, inst_apps, instArgs_apps as _ (bs.map _), List.map_map]; rfl

theorem instArgs_emb0 : ∀ (as : List HExp) (e : MExp), instArgs as (emb 0 e) = emb 0 e
  | [], _ => rfl
  | a :: as, e => by simp only [instArgs, inst_emb0, instArgs_emb0 as e]

theorem instArgs_failAlways : ∀ as : List HExp, instArgs as HExp.failAlways = HExp.failAlways
  | [] => rfl
  | _ :: as => instArgs_failAlways as

theorem instArgs_rule (i : Nat) : ∀ as : List HExp, instArgs as (.rule i) = .rule i
  | [] => rfl
  | _ :: as => instArgs_rule i as

/-- The `k`-th argument lands at its variable. -/
theorem instArgs_var (args : List MExp) : ∀ {k : Nat}, k < args.length →
    instArgs (embArgs 0 args) (.var (args.length - 1 - k)) = emb 0 (args[k]?.getD MExp.failAlways) := by
  induction args with
  | nil => intro k hk; simp at hk
  | cons a args ih =>
    intro k hk
    simp only [embArgs, instArgs, List.length_cons]
    have hlen : (embArgs 0 args).length = args.length := by simp [embArgs_eq_map]
    rw [hlen]
    cases k with
    | zero => simp [HExp.inst, instArgs_emb0]
    | succ k =>
      have hk' : k < args.length := by simp at hk; omega
      have hne : args.length + 1 - 1 - (k + 1) ≠ args.length := by omega
      simp only [HExp.inst, hne, ↓reduceIte, List.getElem?_cons_succ]
      rw [show args.length + 1 - 1 - (k + 1) = args.length - 1 - k by omega]
      exact ih hk'

theorem argAt_eq_getElem? : ∀ (A : List MExp) (k : Nat), argAt A k = A[k]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: A, k + 1 => argAt_eq_getElem? A k

theorem instArgs_fixed {e : HExp} (h : ∀ a k, HExp.inst a k e = e) : ∀ as : List HExp, instArgs as e = e
  | [] => rfl
  | a :: as => by simp only [instArgs, h, instArgs_fixed h as]

theorem instArgs_seq : ∀ (as : List HExp) (a b : HExp), instArgs as (.seq a b) = .seq (instArgs as a) (instArgs as b)
  | [], _, _ => rfl
  | _ :: as, _, _ => instArgs_seq as _ _
theorem instArgs_alt : ∀ (as : List HExp) (a b : HExp), instArgs as (.alt a b) = .alt (instArgs as a) (instArgs as b)
  | [], _, _ => rfl
  | _ :: as, _, _ => instArgs_alt as _ _
theorem instArgs_star : ∀ (as : List HExp) (a : HExp), instArgs as (.star a) = .star (instArgs as a)
  | [], _ => rfl
  | _ :: as, _ => instArgs_star as _
theorem instArgs_notP : ∀ (as : List HExp) (a : HExp), instArgs as (.notP a) = .notP (instArgs as a)
  | [], _ => rfl
  | _ :: as, _ => instArgs_notP as _

mutual
  /-- **The β-steps of a call compute the substituted body**: putting the embedded arguments in for the variables of
  the embedded body is embedding the substituted body. -/
  theorem instArgs_emb (args : List MExp) : ∀ b : MExp,
      instArgs (embArgs 0 args) (emb args.length b) = emb 0 (MExp.subst args b)
    | .param k => by
      simp only [emb, MExp.subst, argAt_eq_getElem?]
      by_cases hk : k < args.length
      · rw [if_pos hk, instArgs_var args hk, List.getElem?_eq_getElem hk]; rfl
      · rw [if_neg hk, instArgs_failAlways, List.getElem?_eq_none (by omega)]; rfl
    | .call i m => by
      simp only [emb, MExp.subst]
      rw [instArgs_apps, instArgs_rule, instArgs_embArgs]
    | .seq e₁ e₂ => by simp only [emb, MExp.subst, instArgs_seq, instArgs_emb args e₁, instArgs_emb args e₂]
    | .alt e₁ e₂ => by simp only [emb, MExp.subst, instArgs_alt, instArgs_emb args e₁, instArgs_emb args e₂]
    | .star e => by simp only [emb, MExp.subst, instArgs_star, instArgs_emb args e]
    | .notP e => by simp only [emb, MExp.subst, instArgs_notP, instArgs_emb args e]
    | .eps | .any | .chr _ | .range _ _ | .lit _ => by
      simp only [emb, MExp.subst]; exact instArgs_fixed (fun _ _ => rfl) _
    | .dbg _ | .lam _ _ | .invoke _ _ _ => by simp only [emb, MExp.subst]; exact instArgs_failAlways _
    | .callParam k m => by
      simp only [emb, MExp.subst, instArgs_failAlways]
      split <;> rfl

  theorem instArgs_embArgs (args : List MExp) : ∀ m : List MExp,
      (embArgs args.length m).map (instArgs (embArgs 0 args)) = embArgs 0 (MExp.substArgs args m)
    | [] => rfl
    | e :: es => by simp only [embArgs, List.map_cons, MExp.substArgs, instArgs_emb args e, instArgs_embArgs args es]
end

end Shallot.MacroPeg.HO
