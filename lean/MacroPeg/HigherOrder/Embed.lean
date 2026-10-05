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

/-! ## Runs of the higher-order calculus, step by step -/

section Steps

variable {g : HGrammar} {n : Nat} {x : List Char}

/-- Expressions whose run starts with a head-reduction step. -/
def HExp.isHead : HExp → Bool
  | .var _ | .rule _ | .lam _ _ | .app _ _ => true
  | _ => false

theorem hrun_head {e : HExp} (h : e.isHead = true) :
    hrun g (n + 1) e x = match step g e with
      | some e' => hrun g n e' x
      | none => some none := by
  cases e <;> simp [HExp.isHead] at h <;> rw [hrun.eq_def] <;> rfl

theorem hrun_seq (a b : HExp) : hrun g (n + 1) (.seq a b) x =
    match hrun g n a x with
    | some (some r) => hrun g n b r
    | r => r := by rw [hrun.eq_def]; rfl
theorem hrun_alt (a b : HExp) : hrun g (n + 1) (.alt a b) x =
    match hrun g n a x with
    | some none => hrun g n b x
    | r => r := by rw [hrun.eq_def]; rfl
theorem hrun_star (a : HExp) : hrun g (n + 1) (.star a) x =
    match hrun g n a x with
    | some (some r) => hrun g n (.star a) r
    | some none => some (some x)
    | none => none := by rw [hrun.eq_def]; rfl
theorem hrun_notP (a : HExp) : hrun g (n + 1) (.notP a) x =
    match hrun g n a x with
    | some (some _) => some none
    | some none => some (some x)
    | none => none := by rw [hrun.eq_def]; rfl

theorem hrun_failAlways_eq {r : Option (List Char)} (h : hrun g (n + 1) HExp.failAlways x = some r) : r = none := by
  unfold HExp.failAlways at h
  rw [hrun_notP] at h
  cases n with
  | zero => simp [hrun] at h
  | succ n => rw [hrun.eq_def] at h; cases h; rfl

theorem hrun_failAlways : hrun g (n + 2) HExp.failAlways x = some none := by
  unfold HExp.failAlways; rw [hrun_notP, hrun.eq_def]

theorem isHead_apps_cons (a : HExp) : ∀ (f : HExp) (as : List HExp), (HExp.apps f (a :: as)).isHead = true
  | _, [] => rfl
  | f, b :: as => isHead_apps_cons b (.app f a) as

theorem step_app {f f' : HExp} (a : HExp) (hf : step g f = some f') (hl : ∀ τ b, f ≠ .lam τ b) :
    step g (.app f a) = some (.app f' a) := by
  cases f with
  | lam τ b => exact absurd rfl (hl τ b)
  | rule _ | app _ _ => simp only [step] at hf ⊢; rw [hf]; rfl
  | _ => simp [step] at hf

theorem step_apps {f f' : HExp} (hf : step g f = some f') (hl : ∀ τ b, f ≠ .lam τ b) :
    ∀ as : List HExp, step g (HExp.apps f as) = some (HExp.apps f' as)
  | [] => hf
  | a :: as => step_apps (step_app a hf hl) (fun _ _ h => by cases h) as

/-- `n` β-steps on `(λ. … λ. B) a₁ … aₙ`. -/
theorem hrun_spine (B : HExp) : ∀ (as : List HExp) (m : Nat),
    hrun g (m + as.length) (HExp.apps (lams as.length B) as) x = hrun g m (instArgs as B) x
  | [], m => rfl
  | a :: as, m => by
    have hstep : step g (HExp.apps (lams (as.length + 1) B) (a :: as)) =
        some (HExp.apps (lams as.length (HExp.inst a as.length B)) as) := by
      have := step_apps (g := g) (f := .app (.lam .p (lams as.length B)) a) (rfl) (fun _ _ h => by cases h) as
      rw [inst_lams, Nat.zero_add] at this
      exact this
    rw [List.length_cons, ← Nat.add_assoc, hrun_head (isHead_apps_cons a _ as), hstep]
    exact hrun_spine (HExp.inst a as.length B) as m

end Steps

/-! ## A call is `1 + arity` steps -/

theorem embArgs_length (ar : Nat) (es : List MExp) : (embArgs ar es).length = es.length := by
  simp [embArgs_eq_map]

theorem embGrammar_rule {G : MGrammar} {i : Nat} {r : MRule} (hr : ruleAtM G.rules i = some r) :
    (embGrammar G).rules[i]? = some (embRule r) := by
  rw [Shallot.MacroPeg.ruleAtM_eq_getElem?] at hr
  simp [embGrammar, hr]

theorem hrun_call_emb {G : MGrammar} {i : Nat} {r : MRule} {args : List MExp} {x : List Char}
    (hr : ruleAtM G.rules i = some r) (ha : r.arity = args.length) (m : Nat) :
    hrun (embGrammar G) (m + args.length + 1) (emb 0 (.call i args)) x =
      hrun (embGrammar G) m (emb 0 (MExp.subst args r.body)) x := by
  have hhead : (HExp.apps (.rule i) (embArgs 0 args)).isHead = true := by
    cases h : embArgs 0 args with
    | nil => rfl
    | cons a as => exact isHead_apps_cons a _ as
  have hstep : step (embGrammar G) (HExp.apps (.rule i) (embArgs 0 args)) =
      some (HExp.apps (embRule r).body (embArgs 0 args)) :=
    step_apps (by simp [step, embGrammar_rule hr]) (fun _ _ h => by cases h) _
  simp only [emb]
  rw [hrun_head hhead, hstep]
  dsimp only
  have hlen := embArgs_length 0 args
  simp only [embRule, ha, ← hlen]
  rw [hrun_spine, hlen, instArgs_emb]

/-! ## The runs agree -/

section Simulation

open Shallot.MacroPeg (runObs runObs_eps runObs_param runObs_seq runObs_alt runObs_star runObs_notP runObs_call
  macroObs_iff_obs MacroObs firstOrder_subst firstOrderArgs_subst arityOk_subst arityOkArgs_subst)

variable {G : MGrammar}

local notation "src" => Shallot.MacroPeg.mpegRun G Shallot.MacroPeg.Strategy.callByName
local notation "tgt" => hrun (embGrammar G)

/-- PEG leaves run the same way in both calculi. -/
theorem runObs_leaf {n : Nat} {x : List Char} {e : MExp}
    (he : e = .any ∨ (∃ c, e = .chr c) ∨ (∃ lo hi, e = .range lo hi) ∨ (∃ s, e = .lit s)) :
    runObs (src (n + 1) e x) = tgt (n + 1) (emb 0 e) x := by
  rcases he with rfl | ⟨c, rfl⟩ | ⟨lo, hi, rfl⟩ | ⟨s, rfl⟩ <;>
    (rw [Shallot.MacroPeg.mpegRun.eq_def, hrun.eq_def]; simp only [emb])
  · cases x <;> rfl
  · cases x with
    | nil => rfl
    | cons d rest => dsimp only; split <;> rfl
  · cases x with
    | nil => rfl
    | cons d rest => dsimp only; split <;> rfl
  · cases stripPrefix? s x <;> rfl

theorem emb_forward (hg : G.FirstOrder) (hga : G.arityOk = true) :
    ∀ (n : Nat) (e : MExp) (x : List Char) (r : Option (List Char)), e.FirstOrder → MExp.arityOk G e = true →
      runObs (src n e x) = some r → ∃ m, tgt m (emb 0 e) x = some r
  | 0, _, _, _, _, _, h => by rw [Shallot.MacroPeg.mpegRun.eq_def] at h; cases h
  | n + 1, e, x, r, he, hea, h => by
    cases e with
    | eps => rw [runObs_eps] at h; exact ⟨n + 1, by rw [hrun.eq_def]; exact h⟩
    | any => exact ⟨n + 1, (runObs_leaf (.inl rfl)).symm.trans h⟩
    | chr c => exact ⟨n + 1, (runObs_leaf (.inr (.inl ⟨c, rfl⟩))).symm.trans h⟩
    | range lo hi => exact ⟨n + 1, (runObs_leaf (.inr (.inr (.inl ⟨lo, hi, rfl⟩)))).symm.trans h⟩
    | lit s => exact ⟨n + 1, (runObs_leaf (.inr (.inr (.inr ⟨s, rfl⟩)))).symm.trans h⟩
    | param k =>
      rw [runObs_param] at h
      exact ⟨2, by simp only [emb, Nat.not_lt_zero, ↓reduceIte]; rw [hrun_failAlways (n := 0)]; exact h⟩
    | seq a b =>
      simp only [Shallot.MacroPeg.MExp.arityOk, Bool.and_eq_true] at hea
      rw [runObs_seq] at h
      cases hra : runObs (src n a x) with
      | none => rw [hra] at h; cases h
      | some ra =>
        obtain ⟨m₁, h₁⟩ := emb_forward hg hga n a x ra he.1 hea.1 hra
        rw [hra] at h
        cases ra with
        | none =>
          refine ⟨m₁ + 1, ?_⟩
          simp only [emb]; rw [hrun_seq, h₁]; exact h
        | some r₁ =>
          obtain ⟨m₂, h₂⟩ := emb_forward hg hga n b r₁ r he.2 hea.2 h
          refine ⟨max m₁ m₂ + 1, ?_⟩
          simp only [emb]
          rw [hrun_seq, hrun_mono_le h₁ (Nat.le_max_left _ _)]
          exact hrun_mono_le h₂ (Nat.le_max_right _ _)
    | alt a b =>
      simp only [Shallot.MacroPeg.MExp.arityOk, Bool.and_eq_true] at hea
      rw [runObs_alt] at h
      cases hra : runObs (src n a x) with
      | none => rw [hra] at h; cases h
      | some ra =>
        obtain ⟨m₁, h₁⟩ := emb_forward hg hga n a x ra he.1 hea.1 hra
        rw [hra] at h
        cases ra with
        | none =>
          obtain ⟨m₂, h₂⟩ := emb_forward hg hga n b x r he.2 hea.2 h
          refine ⟨max m₁ m₂ + 1, ?_⟩
          simp only [emb]
          rw [hrun_alt, hrun_mono_le h₁ (Nat.le_max_left _ _)]
          exact hrun_mono_le h₂ (Nat.le_max_right _ _)
        | some r₁ =>
          refine ⟨m₁ + 1, ?_⟩
          simp only [emb]; rw [hrun_alt, h₁]; exact h
    | star a =>
      rw [runObs_star] at h
      cases hra : runObs (src n a x) with
      | none => rw [hra] at h; cases h
      | some ra =>
        obtain ⟨m₁, h₁⟩ := emb_forward hg hga n a x ra he hea hra
        rw [hra] at h
        cases ra with
        | none =>
          refine ⟨m₁ + 1, ?_⟩
          simp only [emb]; rw [hrun_star, h₁]; exact h
        | some r₁ =>
          obtain ⟨m₂, h₂⟩ := emb_forward hg hga n (.star a) r₁ r he hea h
          refine ⟨max m₁ m₂ + 1, ?_⟩
          simp only [emb] at h₂ ⊢
          rw [hrun_star, hrun_mono_le h₁ (Nat.le_max_left _ _)]
          exact hrun_mono_le h₂ (Nat.le_max_right _ _)
    | notP a =>
      rw [runObs_notP] at h
      cases hra : runObs (src n a x) with
      | none => rw [hra] at h; cases h
      | some ra =>
        obtain ⟨m₁, h₁⟩ := emb_forward hg hga n a x ra he hea hra
        rw [hra] at h
        refine ⟨m₁ + 1, ?_⟩
        simp only [emb]; rw [hrun_notP, h₁]
        cases ra <;> exact h
    | call i args =>
      simp only [Shallot.MacroPeg.MExp.arityOk, Bool.and_eq_true] at hea
      obtain ⟨hcall, hargs⟩ := hea
      cases hr : ruleAtM G.rules i with
      | none => rw [hr] at hcall; cases hcall
      | some rule =>
        rw [hr, beq_iff_eq] at hcall
        rw [runObs_call hr hcall] at h
        have hmem := Shallot.MacroPeg.ruleAtM_mem hr
        obtain ⟨m, hm⟩ := emb_forward hg hga n _ x r (firstOrder_subst he _ (hg rule hmem))
          (arityOk_subst hargs (Shallot.MacroPeg.arityOk_rule hga hr)) h
        exact ⟨m + args.length + 1, by rw [hrun_call_emb hr hcall]; exact hm⟩
    | dbg _ | lam _ _ | callParam _ _ | invoke _ _ _ => exact absurd he id

theorem emb_backward (hg : G.FirstOrder) (hga : G.arityOk = true) :
    ∀ (n : Nat) (e : MExp) (x : List Char) (r : Option (List Char)), e.FirstOrder → MExp.arityOk G e = true →
      tgt n (emb 0 e) x = some r → runObs (src n e x) = some r
  | 0, _, _, _, _, _, h => by simp [hrun] at h
  | n + 1, e, x, r, he, hea, h => by
    cases e with
    | eps => rw [runObs_eps]; rw [hrun.eq_def] at h; exact h
    | any => exact (runObs_leaf (.inl rfl)).trans h
    | chr c => exact (runObs_leaf (.inr (.inl ⟨c, rfl⟩))).trans h
    | range lo hi => exact (runObs_leaf (.inr (.inr (.inl ⟨lo, hi, rfl⟩)))).trans h
    | lit s => exact (runObs_leaf (.inr (.inr (.inr ⟨s, rfl⟩)))).trans h
    | param k =>
      simp only [emb, Nat.not_lt_zero, ↓reduceIte] at h
      rw [runObs_param, hrun_failAlways_eq h]
    | seq a b =>
      simp only [Shallot.MacroPeg.MExp.arityOk, Bool.and_eq_true] at hea
      simp only [emb] at h; rw [hrun_seq] at h; rw [runObs_seq]
      cases hra : tgt n (emb 0 a) x with
      | none => rw [hra] at h; cases h
      | some ra =>
        rw [emb_backward hg hga n a x ra he.1 hea.1 hra]
        rw [hra] at h
        cases ra with
        | none => exact h
        | some r₁ => exact emb_backward hg hga n b r₁ r he.2 hea.2 h
    | alt a b =>
      simp only [Shallot.MacroPeg.MExp.arityOk, Bool.and_eq_true] at hea
      simp only [emb] at h; rw [hrun_alt] at h; rw [runObs_alt]
      cases hra : tgt n (emb 0 a) x with
      | none => rw [hra] at h; cases h
      | some ra =>
        rw [emb_backward hg hga n a x ra he.1 hea.1 hra]
        rw [hra] at h
        cases ra with
        | none => exact emb_backward hg hga n b x r he.2 hea.2 h
        | some r₁ => exact h
    | star a =>
      simp only [emb] at h; rw [hrun_star] at h; rw [runObs_star]
      cases hra : tgt n (emb 0 a) x with
      | none => rw [hra] at h; cases h
      | some ra =>
        rw [emb_backward hg hga n a x ra he hea hra]
        rw [hra] at h
        cases ra with
        | none => exact h
        | some r₁ => exact emb_backward hg hga n (.star a) r₁ r he hea h
    | notP a =>
      simp only [emb] at h; rw [hrun_notP] at h; rw [runObs_notP]
      cases hra : tgt n (emb 0 a) x with
      | none => rw [hra] at h; cases h
      | some ra =>
        rw [emb_backward hg hga n a x ra he hea hra]
        rw [hra] at h
        cases ra <;> exact h
    | call i args =>
      simp only [Shallot.MacroPeg.MExp.arityOk, Bool.and_eq_true] at hea
      obtain ⟨hcall, hargs⟩ := hea
      cases hr : ruleAtM G.rules i with
      | none => rw [hr] at hcall; cases hcall
      | some rule =>
        rw [hr, beq_iff_eq] at hcall
        rw [runObs_call hr hcall]
        have hmem := Shallot.MacroPeg.ruleAtM_mem hr
        have h' := hrun_mono_le h (show n + 1 ≤ n + args.length + 1 by omega)
        rw [hrun_call_emb hr hcall] at h'
        exact emb_backward hg hga n _ x r (firstOrder_subst he _ (hg rule hmem))
          (arityOk_subst hargs (Shallot.MacroPeg.arityOk_rule hga hr)) h'
    | dbg _ | lam _ _ | callParam _ _ | invoke _ _ _ => exact absurd he id

/-- **First-order Macro PEG embeds into higher-order Macro PEG**: on a first-order, arity-correct grammar, an
expression and its embedding have the same observations. -/
theorem emb_obs (hg : G.FirstOrder) (hga : G.arityOk = true) {e : MExp} (he : e.FirstOrder)
    (hea : MExp.arityOk G e = true) (x : List Char) (r : Option (List Char)) :
    MacroObs G e x r ↔ HObs (embGrammar G) (emb 0 e) x r := by
  rw [macroObs_iff_obs]
  constructor
  · rintro ⟨n, h⟩; exact emb_forward hg hga n e x r he hea h
  · rintro ⟨n, h⟩; exact ⟨n, emb_backward hg hga n e x r he hea h⟩

end Simulation

/-! ## The embedded grammar has order at most one -/

theorem order_parsers : ∀ n : Nat, (Ty.parsers n).order ≤ 1
  | 0 => by simp [Ty.parsers, Ty.order]
  | n + 1 => by
    have := order_parsers n
    simp only [Ty.parsers, Ty.order]; omega

theorem foldr_max_le {l : List Nat} {b : Nat} (h : ∀ a ∈ l, a ≤ b) : l.foldr max 0 ≤ b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact Nat.max_le.2 ⟨h a (by simp), ih (fun c hc => h c (by simp [hc]))⟩

theorem embGrammar_order (G : MGrammar) : (embGrammar G).order ≤ 1 := by
  apply foldr_max_le
  intro a ha
  simp only [embGrammar, List.map_map, List.mem_map, Function.comp] at ha
  obtain ⟨r, _, rfl⟩ := ha
  exact order_parsers r.arity

end Shallot.MacroPeg.HO
