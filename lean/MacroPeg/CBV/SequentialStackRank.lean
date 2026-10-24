import MacroPeg.CBV.SequentialStack

namespace Shallot.MacroPeg.CBV.SequentialStackRank

open SequentialStack

noncomputable def taskRank (C : Nat) : Task → Nat
  | .expr m _ e _ => m * C + sizeOf e
  | .args m _ args _ => m * C + sizeOf args
  | .query m _ _ _ => m * C
  | .value _ => 0

noncomputable def frameNeed (C : Nat) : Frame → Nat
  | .seq m _ b | .alt m _ b _ => m * C + sizeOf b
  | .notP _ => 0
  | .star m _ a _ => m * C + sizeOf (MExp.star a)
  | .argHead m _ args _ => m * C + sizeOf args + 1
  | .argCons _ => 0
  | .call m _ => m * C

/-- Ranks are proof witnesses, not extra fields in the runtime frames. -/
inductive Ranked (C : Nat) : Nat → List Frame → Nat → Prop where
  | nil {r cap} (h : r ≤ cap) : Ranked C r [] cap
  | cons {r cap level f K} (small : r < level) (need : frameNeed C f ≤ level)
      (tail : Ranked C level K cap) : Ranked C r (f :: K) cap

theorem Ranked.lower {C r r' cap : Nat} {K : List Frame} (h : Ranked C r K cap) (hr : r' ≤ r) :
    Ranked C r' K cap := by
  cases h with
  | nil hb => exact .nil (by omega)
  | cons hs hn ht => exact .cons (by omega) hn ht

theorem Ranked.pop {C r cap : Nat} {f : Frame} {K : List Frame} (h : Ranked C r (f :: K) cap) :
    ∃ level, frameNeed C f ≤ level ∧ Ranked C level K cap := by
  cases h with
  | cons hs hn ht => exact ⟨_, hn, ht⟩

theorem Ranked.length_bound {C r cap : Nat} {K : List Frame} (h : Ranked C r K cap) :
    K.length + r ≤ cap := by
  induction h with
  | nil hh => simpa using hh
  | cons hs hn ht ih => simp only [List.length_cons]; omega

def ConfigRanked (C cap : Nat) (c : Config) : Prop := Ranked C (taskRank C c.task) c.stack cap

theorem return_ranked (g : MGrammar) (x : List Char) (C cap level : Nat)
    (v : SequentialStack.Value) (f : Frame) (K : List Frame) (next : Config)
    (hn : frameNeed C f ≤ level) (ht : Ranked C level K cap)
    (hs : step g x ⟨.value v, f :: K⟩ = some next) : ConfigRanked C cap next := by
  cases v with
  | expr result =>
    cases f with
    | seq m E b =>
      cases result with
      | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ht.lower (Nat.zero_le _)
      | some result =>
        cases result with
        | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ht.lower (Nat.zero_le _)
        | some q =>
          simp only [step, Option.some.injEq] at hs
          cases hs
          exact ht.lower hn
    | alt m E b p =>
      cases result with
      | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ht.lower (Nat.zero_le _)
      | some result =>
        cases result with
        | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ht.lower hn
        | some q => simp only [step, Option.some.injEq] at hs; cases hs; exact ht.lower (Nat.zero_le _)
    | notP p =>
      simp only [step, Option.some.injEq] at hs
      cases hs
      exact ht.lower (Nat.zero_le _)
    | star m E a p =>
      cases result with
      | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ht.lower (Nat.zero_le _)
      | some result =>
        cases result with
        | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ht.lower (Nat.zero_le _)
        | some q =>
          by_cases hq : q < p
          · simp only [step, if_pos hq, Option.some.injEq] at hs
            cases hs
            exact ht.lower hn
          · simp only [step, if_neg hq, Option.some.injEq] at hs
            cases hs
            exact ht.lower (Nat.zero_le _)
    | argHead m E args p =>
      cases result with
      | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ht.lower (Nat.zero_le _)
      | some result =>
        cases result with
        | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ht.lower (Nat.zero_le _)
        | some q =>
          simp only [step, Option.some.injEq] at hs
          cases hs
          refine Ranked.cons (level := level) ?_ (Nat.zero_le _) ht
          simp only [taskRank, frameNeed] at hn ⊢
          omega
    | argCons _ | call _ _ => simp [step] at hs
  | args result =>
    cases f with
    | seq _ _ _ | alt _ _ _ _ | notP _ | star _ _ _ _ | argHead _ _ _ _ => simp [step] at hs
    | argCons span =>
      simp only [step, Option.some.injEq] at hs
      cases hs
      exact ht.lower (Nat.zero_le _)
    | call m i =>
      cases result with
      | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ht.lower (Nat.zero_le _)
      | some result =>
        cases result with
        | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ht.lower (Nat.zero_le _)
        | some Wq =>
          obtain ⟨W, q⟩ := Wq
          simp only [step, Option.some.injEq] at hs
          cases hs
          exact ht.lower hn

theorem step_ranked (g : MGrammar) (x : List Char) (C cap : Nat)
    (hcode : ∀ rule ∈ g.rules, sizeOf rule.body ≤ C) (c next : Config)
    (hc : ConfigRanked C cap c) (hs : step g x c = some next) : ConfigRanked C cap next := by
  obtain ⟨task, K⟩ := c
  cases task with
  | expr m E e p =>
    cases e with
    | eps | any | chr _ | range _ _ | lit _ | param _ | dbg _ | lam _ _
    | callParam _ _ | invoke _ _ _ =>
      simp only [step, Option.some.injEq] at hs
      cases hs
      exact hc.lower (Nat.zero_le _)
    | seq a b =>
      simp only [step, Option.some.injEq] at hs
      cases hs
      refine Ranked.cons (level := m * C + sizeOf (MExp.seq a b)) ?_ ?_ hc
      · simp only [taskRank, MExp.seq.sizeOf_spec]; omega
      · simp only [frameNeed, MExp.seq.sizeOf_spec]; omega
    | alt a b =>
      simp only [step, Option.some.injEq] at hs
      cases hs
      refine Ranked.cons (level := m * C + sizeOf (MExp.alt a b)) ?_ ?_ hc
      · simp only [taskRank, MExp.alt.sizeOf_spec]; omega
      · simp only [frameNeed, MExp.alt.sizeOf_spec]; omega
    | notP a =>
      simp only [step, Option.some.injEq] at hs
      cases hs
      refine Ranked.cons (level := m * C + sizeOf (MExp.notP a)) ?_ (Nat.zero_le _) hc
      simp only [taskRank, MExp.notP.sizeOf_spec]; omega
    | star a =>
      simp only [step, Option.some.injEq] at hs
      cases hs
      refine Ranked.cons (level := m * C + sizeOf (MExp.star a)) ?_ (Nat.le_refl _) hc
      simp only [taskRank, MExp.star.sizeOf_spec]; omega
    | call i args =>
      cases hr : ruleAtM g.rules i with
      | none =>
        simp only [step, hr, Option.some.injEq] at hs
        cases hs
        exact hc.lower (Nat.zero_le _)
      | some rule =>
        by_cases ha : rule.arity = args.length
        · simp only [step, hr, if_pos ha, Option.some.injEq] at hs
          cases hs
          refine Ranked.cons (level := m * C + sizeOf (MExp.call i args)) ?_ ?_ hc
          · simp only [taskRank, MExp.call.sizeOf_spec]; omega
          · simp only [frameNeed, MExp.call.sizeOf_spec]; omega
        · simp only [step, hr, if_neg ha, Option.some.injEq] at hs
          cases hs
          exact hc.lower (Nat.zero_le _)
  | args m E args p =>
    cases args with
    | nil =>
      simp only [step, Option.some.injEq] at hs
      cases hs
      exact hc.lower (Nat.zero_le _)
    | cons a args =>
      simp only [step, Option.some.injEq] at hs
      cases hs
      refine Ranked.cons (level := m * C + sizeOf (a :: args)) ?_ ?_ hc
      · simp only [taskRank, List.cons.sizeOf_spec]; omega
      · simp only [frameNeed, List.cons.sizeOf_spec]; omega
  | query m i E p =>
    cases m with
    | zero =>
      simp only [step, Option.some.injEq] at hs
      cases hs
      exact hc.lower (Nat.zero_le _)
    | succ m =>
      by_cases hp : p ≤ x.length
      · cases hr : ruleAtM g.rules i with
        | none =>
          simp only [step, if_pos hp, hr, Option.some.injEq] at hs
          cases hs
          exact hc.lower (Nat.zero_le _)
        | some rule =>
          simp only [step, if_pos hp, hr, Option.some.injEq] at hs
          cases hs
          apply hc.lower
          have hb := hcode rule (ruleAtM_mem hr)
          simp only [taskRank, Nat.succ_mul]
          omega
      · simp only [step, if_neg hp, Option.some.injEq] at hs
        cases hs
        exact hc.lower (Nat.zero_le _)
  | value v =>
    cases K with
    | nil => cases v <;> simp [step] at hs
    | cons f K =>
      obtain ⟨level, hn, ht⟩ := hc.pop
      exact return_ranked g x C cap level v f K next hn ht hs

theorem runs_ranked (g : MGrammar) (x : List Char) (C cap : Nat)
    (hcode : ∀ rule ∈ g.rules, sizeOf rule.body ≤ C) {a b : Config}
    (h : Runs g x a b) (ha : ConfigRanked C cap a) : ConfigRanked C cap b := by
  revert ha
  induction h with
  | refl => exact fun ha => ha
  | cons hs ht ih => intro ha; exact ih (step_ranked g x C cap hcode _ _ ha hs)

noncomputable def codeBudget (g : MGrammar) : Nat :=
  1 + (g.rules.map (fun rule => sizeOf rule.body)).sum

theorem codeBudget_spec (g : MGrammar) : ∀ rule ∈ g.rules, sizeOf rule.body ≤ codeBudget g := by
  have aux : ∀ rules : List MRule, ∀ rule ∈ rules,
      sizeOf rule.body ≤ (rules.map (fun rule => sizeOf rule.body)).sum := by
    intro rules
    induction rules with
    | nil => intro rule hr; cases hr
    | cons head rules ih =>
      intro rule hr
      rcases List.mem_cons.mp hr with he | hr
      · subst rule; simp only [List.map_cons, List.sum_cons]; omega
      · have hh := ih rule hr
        simp only [List.map_cons, List.sum_cons]
        omega
  intro rule hr
  have hh := aux g.rules rule hr
  unfold codeBudget
  omega

noncomputable def initialCap (g : MGrammar) (x : List Char) (e : MExp) : Nat :=
  SequentialClock.positionClock g x.length * codeBudget g + sizeOf e

theorem initial_ranked (g : MGrammar) (x : List Char) (e : MExp) :
    ConfigRanked (codeBudget g) (initialCap g x e) (initial g x e) :=
  Ranked.nil (Nat.le_refl _)

/-- The bound holds at every reachable intermediate state of the actual
transition machine, not merely at its final state. -/
theorem reachable_stack_bound (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) : c.stack.length ≤ initialCap g x e := by
  have hc := runs_ranked g x (codeBudget g) (initialCap g x e) (codeBudget_spec g) h (initial_ranked g x e)
  have hh := hc.length_bound
  omega

/-- For a fixed source program, the number of simultaneously retained
continuation frames is linear in the original input length. This does not
yet bound the encoded size of the environments inside those frames. -/
theorem stack_linear_bound (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    c.stack.length ≤ ((g.rules.length + 1) * codeBudget g) * (x.length + 1) + sizeOf e := by
  have hh := reachable_stack_bound g x e c h
  simpa only [initialCap, SequentialClock.positionClock, Nat.mul_right_comm] using hh

end Shallot.MacroPeg.CBV.SequentialStackRank
