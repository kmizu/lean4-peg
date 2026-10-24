import MacroPeg.CBV.SequentialStackRank

namespace Shallot.MacroPeg.CBV.SequentialStackPayload

/-! Expected argument counts prevent continuation returns from accumulating
unbounded environments. All payload invariants below are for the actual
SequentialStack transition function; the runtime carries no extra types. -/

open SequentialStack

def EnvOK (n A : Nat) (E : CaptureEnv) : Prop :=
  SequentialSpanRecompute.ValidEnv n E ∧ E.length ≤ A

theorem empty_env (n A : Nat) : EnvOK n A [] := by
  refine ⟨?_, by simp⟩
  intro span hm; cases hm

inductive Kind where
  | expr
  | args (length : Nat)

inductive ValueTyped (n A : Nat) : Kind → SequentialStack.Value → Prop where
  | expr (r : Res) (h : OkR n r) : ValueTyped n A .expr (.expr r)
  | args (r : ArgsResult) (k : Nat) (hk : k ≤ A)
      (h : ∀ W q, r = some (some (W, q)) → EnvOK n A W ∧ q ≤ n ∧ W.length = k) :
      ValueTyped n A (.args k) (.args r)

inductive TaskTyped (n A M : Nat) : Task → Kind → Prop where
  | expr (m E e p) (hm : m ≤ M) (hE : EnvOK n A E) (hp : p ≤ n) :
      TaskTyped n A M (.expr m E e p) .expr
  | args (m E es p) (hm : m ≤ M) (hE : EnvOK n A E) (hp : p ≤ n) (hlen : es.length ≤ A) :
      TaskTyped n A M (.args m E es p) (.args es.length)
  | query (m i E p) (hm : m ≤ M) (hE : EnvOK n A E) (hp : p ≤ n) :
      TaskTyped n A M (.query m i E p) .expr
  | value {v k} (h : ValueTyped n A k v) : TaskTyped n A M (.value v) k

inductive FrameTyped (g : MGrammar) (n A M : Nat) : Frame → Kind → Kind → Prop where
  | seq (m E b) (hm : m ≤ M) (hE : EnvOK n A E) :
      FrameTyped g n A M (.seq m E b) .expr .expr
  | alt (m E b p) (hm : m ≤ M) (hE : EnvOK n A E) (hp : p ≤ n) :
      FrameTyped g n A M (.alt m E b p) .expr .expr
  | notP (p) (hp : p ≤ n) : FrameTyped g n A M (.notP p) .expr .expr
  | star (m E a p) (hm : m ≤ M) (hE : EnvOK n A E) (hp : p ≤ n) :
      FrameTyped g n A M (.star m E a p) .expr .expr
  | argHead (m E es p) (hm : m ≤ M) (hE : EnvOK n A E) (hp : p ≤ n) (hlen : es.length + 1 ≤ A) :
      FrameTyped g n A M (.argHead m E es p) .expr (.args (es.length + 1))
  | argCons (span : Nat × Nat) (k) (hspan : span.2 ≤ span.1 ∧ span.1 ≤ n) (hk : k + 1 ≤ A) :
      FrameTyped g n A M (.argCons span) (.args k) (.args (k + 1))
  | call (m i) (rule : MRule) (hm : m ≤ M) (hr : ruleAtM g.rules i = some rule) (ha : rule.arity ≤ A) :
      FrameTyped g n A M (.call m i) (.args rule.arity) .expr

inductive StackTyped (g : MGrammar) (n A M : Nat) : Kind → List Frame → Kind → Prop where
  | nil (k) : StackTyped g n A M k [] k
  | cons {k k' final f K} (head : FrameTyped g n A M f k k') (tail : StackTyped g n A M k' K final) :
      StackTyped g n A M k (f :: K) final

def Typed (g : MGrammar) (n A M : Nat) (final : Kind) (c : Config) : Prop :=
  ∃ k, TaskTyped n A M c.task k ∧ StackTyped g n A M k c.stack final

theorem atom_bound (x : List Char) (A : Nat) (E : CaptureEnv) (hE : EnvOK x.length A E)
    (e : MExp) (p : Nat) (hp : p ≤ x.length) : OkR x.length (atom x E e p) := by
  have hT : OkTV x.length (fun _ _ => []) := by
    intro i W q; simp only [valAt_nil]; exact okR_none _
  have hbase := evV_ok (g := ⟨[]⟩) (s := .callByValueSeq) (E := []) hT e p hp
  cases e with
  | eps | any | chr _ | range _ _ | lit _ | dbg _ | lam _ _ | invoke _ _ _ =>
    exact hbase
  | call _ _ | callParam _ _ | seq _ _ | alt _ _ | notP _ | star _ => exact okR_fail _
  | param k =>
    cases he : E[k]? with
    | none => simp only [atom, he]; exact okR_fail _
    | some span =>
      obtain ⟨a, b⟩ := span
      have ha := (hE.1 (a, b) (List.mem_of_getElem? he)).2
      simp only [atom, he, SequentialSpanRecompute.matchSpan_eq x a b p ha]
      cases hr : Shallot.stripPrefix? (pre x a b) (sfx x p) with
      | none => exact okR_fail _
      | some rest => exact okR_ok (Nat.le_trans (stripPrefix_length _ _ _ hr) (length_sfx_le x p))

theorem env_cons {n A : Nat} {span : Nat × Nat} {E : CaptureEnv}
    (hs : span.2 ≤ span.1 ∧ span.1 ≤ n) (hE : SequentialSpanRecompute.ValidEnv n E)
    (hlen : E.length + 1 ≤ A) : EnvOK n A (span :: E) := by
  refine ⟨?_, by simpa using hlen⟩
  intro v hv
  rcases List.mem_cons.mp hv with he | hv
  · subst v; exact hs
  · exact hE v hv

theorem args_bottom (n A k : Nat) (hk : k ≤ A) : ValueTyped n A (.args k) (.args none) :=
  .args none k hk (fun _ _ h => by cases h)

theorem args_failure (n A k : Nat) (hk : k ≤ A) : ValueTyped n A (.args k) (.args (some none)) :=
  .args (some none) k hk (fun _ _ h => by cases h)

theorem return_typed (g : MGrammar) (x : List Char) (A M : Nat)
    {v : SequentialStack.Value} {kind out final : Kind} {f : Frame} {K : List Frame} {next : Config}
    (hv : ValueTyped x.length A kind v) (hf : FrameTyped g x.length A M f kind out)
    (htail : StackTyped g x.length A M out K final)
    (hs : step g x ⟨.value v, f :: K⟩ = some next) : Typed g x.length A M final next := by
  cases hf with
  | seq m E b hm hE =>
    cases hv with
    | expr result hresult =>
      cases result with
      | none =>
        simp only [step, Option.some.injEq] at hs; cases hs
        exact ⟨.expr, .value (.expr _ hresult), htail⟩
      | some result =>
        cases result with
        | none =>
          simp only [step, Option.some.injEq] at hs; cases hs
          exact ⟨.expr, .value (.expr _ hresult), htail⟩
        | some q =>
          simp only [step, Option.some.injEq] at hs; cases hs
          exact ⟨.expr, .expr m E b q hm hE (hresult q rfl), htail⟩
  | alt m E b p hm hE hp =>
    cases hv with
    | expr result hresult =>
      cases result with
      | none =>
        simp only [step, Option.some.injEq] at hs; cases hs
        exact ⟨.expr, .value (.expr _ hresult), htail⟩
      | some result =>
        cases result with
        | none =>
          simp only [step, Option.some.injEq] at hs; cases hs
          exact ⟨.expr, .expr m E b p hm hE hp, htail⟩
        | some q =>
          simp only [step, Option.some.injEq] at hs; cases hs
          exact ⟨.expr, .value (.expr _ hresult), htail⟩
  | notP p hp =>
    cases hv with
    | expr result hresult =>
      cases result with
      | none =>
        simp only [step, Option.some.injEq] at hs; cases hs
        exact ⟨.expr, .value (.expr _ (okR_none _)), htail⟩
      | some result =>
        cases result with
        | none =>
          simp only [step, Option.some.injEq] at hs; cases hs
          exact ⟨.expr, .value (.expr _ (okR_ok hp)), htail⟩
        | some q =>
          simp only [step, Option.some.injEq] at hs; cases hs
          exact ⟨.expr, .value (.expr _ (okR_fail _)), htail⟩
  | star m E a p hm hE hp =>
    cases hv with
    | expr result hresult =>
      cases result with
      | none =>
        simp only [step, Option.some.injEq] at hs; cases hs
        exact ⟨.expr, .value (.expr _ (okR_none _)), htail⟩
      | some result =>
        cases result with
        | none =>
          simp only [step, Option.some.injEq] at hs; cases hs
          exact ⟨.expr, .value (.expr _ (okR_ok hp)), htail⟩
        | some q =>
          by_cases hq : q < p
          · simp only [step, if_pos hq, Option.some.injEq] at hs; cases hs
            exact ⟨.expr, .expr m E (.star a) q hm hE (hresult q rfl), htail⟩
          · simp only [step, if_neg hq, Option.some.injEq] at hs; cases hs
            exact ⟨.expr, .value (.expr _ (okR_none _)), htail⟩
  | argHead m E es p hm hE hp hlen =>
    cases hv with
    | expr result hresult =>
      cases result with
      | none =>
        simp only [step, Option.some.injEq] at hs; cases hs
        exact ⟨_, .value (args_bottom _ _ _ hlen), htail⟩
      | some result =>
        cases result with
        | none =>
          simp only [step, Option.some.injEq] at hs; cases hs
          exact ⟨_, .value (args_failure _ _ _ hlen), htail⟩
        | some q =>
          simp only [step, Option.some.injEq] at hs; cases hs
          refine ⟨.args es.length, .args m E es q hm hE (hresult q rfl) (by omega), ?_⟩
          exact .cons (.argCons (p, min q p) es.length ⟨Nat.min_le_right _ _, hp⟩ hlen) htail
  | argCons span k hspan hk =>
    cases hv with
    | args result _ hinput hresult =>
      cases result with
      | none =>
        simp only [step, Option.some.injEq] at hs; cases hs
        exact ⟨_, .value (args_bottom _ _ _ hk), htail⟩
      | some result =>
        cases result with
        | none =>
          simp only [step, Option.some.injEq] at hs; cases hs
          exact ⟨_, .value (args_failure _ _ _ hk), htail⟩
        | some Wq =>
          obtain ⟨W, q⟩ := Wq
          obtain ⟨hW, hq, hsize⟩ := hresult W q rfl
          simp only [step, Option.some.injEq] at hs; cases hs
          refine ⟨.args (k + 1), .value (.args _ _ hk ?_), htail⟩
          intro V r he
          cases he
          exact ⟨env_cons hspan hW.1 (by omega), hq, by simp [hsize]⟩
  | call m i rule hm hr ha =>
    cases hv with
    | args result _ hk hresult =>
      cases result with
      | none =>
        simp only [step, Option.some.injEq] at hs; cases hs
        exact ⟨.expr, .value (.expr _ (okR_none _)), htail⟩
      | some result =>
        cases result with
        | none =>
          simp only [step, Option.some.injEq] at hs; cases hs
          exact ⟨.expr, .value (.expr _ (okR_fail _)), htail⟩
        | some Wq =>
          obtain ⟨W, q⟩ := Wq
          obtain ⟨hW, hq, hlen⟩ := hresult W q rfl
          simp only [step, Option.some.injEq] at hs; cases hs
          exact ⟨.expr, .query m i W q hm hW hq, htail⟩

theorem step_typed (g : MGrammar) (x : List Char) (A M : Nat)
    (hcode : ∀ rule ∈ g.rules, rule.arity ≤ A) {final : Kind} (c next : Config)
    (hc : Typed g x.length A M final c) (hs : step g x c = some next) :
    Typed g x.length A M final next := by
  obtain ⟨task, K⟩ := c
  obtain ⟨kind, htask, hstack⟩ := hc
  cases htask with
  | expr m E e p hm hE hp =>
    cases e with
    | eps | any | chr _ | range _ _ | lit _ | param _ | dbg _ | lam _ _
    | callParam _ _ | invoke _ _ _ =>
      simp only [step, Option.some.injEq] at hs
      cases hs
      exact ⟨.expr, .value (.expr _ (atom_bound x A E hE _ p hp)), hstack⟩
    | seq a b =>
      simp only [step, Option.some.injEq] at hs; cases hs
      exact ⟨.expr, .expr m E a p hm hE hp, .cons (.seq m E b hm hE) hstack⟩
    | alt a b =>
      simp only [step, Option.some.injEq] at hs; cases hs
      exact ⟨.expr, .expr m E a p hm hE hp, .cons (.alt m E b p hm hE hp) hstack⟩
    | notP a =>
      simp only [step, Option.some.injEq] at hs; cases hs
      exact ⟨.expr, .expr m E a p hm hE hp, .cons (.notP p hp) hstack⟩
    | star a =>
      simp only [step, Option.some.injEq] at hs; cases hs
      exact ⟨.expr, .expr m E a p hm hE hp, .cons (.star m E a p hm hE hp) hstack⟩
    | call i args =>
      cases hr : ruleAtM g.rules i with
      | none =>
        simp only [step, hr, Option.some.injEq] at hs; cases hs
        exact ⟨.expr, .value (.expr _ (okR_fail _)), hstack⟩
      | some rule =>
        by_cases ha : rule.arity = args.length
        · simp only [step, hr, if_pos ha, Option.some.injEq] at hs; cases hs
          have hbound := hcode rule (ruleAtM_mem hr)
          refine ⟨.args args.length, .args m E args p hm hE hp (by omega), .cons ?_ hstack⟩
          have hf : FrameTyped g x.length A M (.call m i) (.args rule.arity) .expr :=
            .call m i rule hm hr hbound
          simpa only [ha] using hf
        · simp only [step, hr, if_neg ha, Option.some.injEq] at hs; cases hs
          exact ⟨.expr, .value (.expr _ (okR_fail _)), hstack⟩
  | args m E es p hm hE hp hlen =>
    cases es with
    | nil =>
      simp only [step, Option.some.injEq] at hs; cases hs
      refine ⟨.args 0, .value (.args _ 0 (Nat.zero_le _) ?_), hstack⟩
      intro W q he
      cases he
      exact ⟨empty_env _ _, hp, rfl⟩
    | cons a es =>
      simp only [step, Option.some.injEq] at hs; cases hs
      exact ⟨.expr, .expr m E a p hm hE hp, .cons (.argHead m E es p hm hE hp hlen) hstack⟩
  | query m i E p hm hE hp =>
    cases m with
    | zero =>
      simp only [step, Option.some.injEq] at hs; cases hs
      exact ⟨.expr, .value (.expr _ (okR_none _)), hstack⟩
    | succ m =>
      cases hr : ruleAtM g.rules i with
      | none =>
        simp only [step, if_pos hp, hr, Option.some.injEq] at hs; cases hs
        exact ⟨.expr, .value (.expr _ (okR_none _)), hstack⟩
      | some rule =>
        simp only [step, if_pos hp, hr, Option.some.injEq] at hs; cases hs
        exact ⟨.expr, .expr m E rule.body p (by omega) hE hp, hstack⟩
  | value hv =>
    cases hstack with
    | nil => cases hv <;> simp [step] at hs
    | cons hf htail => exact return_typed g x A M hv hf htail hs

theorem runs_typed (g : MGrammar) (x : List Char) (A M : Nat)
    (hcode : ∀ rule ∈ g.rules, rule.arity ≤ A) {a b : Config} {final : Kind}
    (h : Runs g x a b) (ha : Typed g x.length A M final a) : Typed g x.length A M final b := by
  revert ha
  induction h with
  | refl => exact fun ha => ha
  | cons hs ht ih => intro ha; exact ih (step_typed g x A M hcode _ _ ha hs)

def arityBudget (g : MGrammar) : Nat := (g.rules.map MRule.arity).sum

theorem arityBudget_spec (g : MGrammar) : ∀ rule ∈ g.rules, rule.arity ≤ arityBudget g := by
  have aux : ∀ rules : List MRule, ∀ rule ∈ rules, rule.arity ≤ (rules.map MRule.arity).sum := by
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
  exact aux g.rules

theorem initial_typed (g : MGrammar) (x : List Char) (e : MExp) :
    Typed g x.length (arityBudget g) (SequentialClock.positionClock g x.length) .expr (initial g x e) :=
  ⟨.expr, .expr _ [] e x.length (Nat.le_refl _) (empty_env _ _) (Nat.le_refl _), .nil .expr⟩

theorem reachable_typed (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    Typed g x.length (arityBudget g) (SequentialClock.positionClock g x.length) .expr c :=
  runs_typed g x _ _ (arityBudget_spec g) h (initial_typed g x e)

def taskCaptures : Task → CaptureEnv
  | .expr _ E _ _ | .args _ E _ _ | .query _ _ E _ => E
  | .value (.args (some (some (W, _)))) => W
  | .value _ => []

def taskClock : Task → Nat
  | .expr m _ _ _ | .args m _ _ _ | .query m _ _ _ => m
  | .value _ => 0

def taskPosition : Task → Nat
  | .expr _ _ _ p | .args _ _ _ p | .query _ _ _ p => p
  | .value (.expr (some (some p))) | .value (.args (some (some (_, p)))) => p
  | .value _ => 0

def frameCaptures : Frame → CaptureEnv
  | .seq _ E _ | .alt _ E _ _ | .star _ E _ _ | .argHead _ E _ _ => E
  | .argCons span => [span]
  | .notP _ | .call _ _ => []

def frameClock : Frame → Nat
  | .seq m _ _ | .alt m _ _ _ | .star m _ _ _ | .argHead m _ _ _ | .call m _ => m
  | .notP _ | .argCons _ => 0

def framePosition : Frame → Nat
  | .alt _ _ _ p | .notP p | .star _ _ _ p | .argHead _ _ _ p => p
  | .seq _ _ _ | .argCons _ | .call _ _ => 0

theorem TaskTyped.bounds {n A M : Nat} {task : Task} {kind : Kind} (h : TaskTyped n A M task kind) :
    EnvOK n A (taskCaptures task) ∧ taskClock task ≤ M ∧ taskPosition task ≤ n := by
  cases h with
  | expr m E e p hm hE hp => exact ⟨hE, hm, hp⟩
  | args m E es p hm hE hp hlen => exact ⟨hE, hm, hp⟩
  | query m i E p hm hE hp => exact ⟨hE, hm, hp⟩
  | value hv =>
    cases hv with
    | expr result hresult =>
      cases result with
      | none => exact ⟨empty_env _ _, Nat.zero_le _, Nat.zero_le _⟩
      | some result =>
        cases result with
        | none => exact ⟨empty_env _ _, Nat.zero_le _, Nat.zero_le _⟩
        | some q => exact ⟨empty_env _ _, Nat.zero_le _, hresult q rfl⟩
    | args result k hk hresult =>
      cases result with
      | none => exact ⟨empty_env _ _, Nat.zero_le _, Nat.zero_le _⟩
      | some result =>
        cases result with
        | none => exact ⟨empty_env _ _, Nat.zero_le _, Nat.zero_le _⟩
        | some Wq =>
          obtain ⟨W, q⟩ := Wq
          obtain ⟨hW, hq, hlen⟩ := hresult W q rfl
          exact ⟨hW, Nat.zero_le _, hq⟩

theorem FrameTyped.bounds {g : MGrammar} {n A M : Nat} {f : Frame} {kind out : Kind}
    (h : FrameTyped g n A M f kind out) :
    EnvOK n A (frameCaptures f) ∧ frameClock f ≤ M ∧ framePosition f ≤ n := by
  cases h with
  | seq m E b hm hE => exact ⟨hE, hm, Nat.zero_le _⟩
  | alt m E b p hm hE hp => exact ⟨hE, hm, hp⟩
  | notP p hp => exact ⟨empty_env _ _, Nat.zero_le _, hp⟩
  | star m E a p hm hE hp => exact ⟨hE, hm, hp⟩
  | argHead m E es p hm hE hp hlen => exact ⟨hE, hm, hp⟩
  | argCons span k hspan hk =>
    exact ⟨env_cons hspan (empty_env n A).1 (by simp; omega), Nat.zero_le _, Nat.zero_le _⟩
  | call m i rule hm hr ha => exact ⟨empty_env _ _, hm, Nat.zero_le _⟩

theorem StackTyped.bounds {g : MGrammar} {n A M : Nat} {kind final : Kind} {K : List Frame}
    (h : StackTyped g n A M kind K final) : ∀ f ∈ K,
      EnvOK n A (frameCaptures f) ∧ frameClock f ≤ M ∧ framePosition f ≤ n := by
  induction h with
  | nil => intro f hf; cases hf
  | cons hhead htail ih =>
    intro f hf
    rcases List.mem_cons.mp hf with he | hf
    · subst f; exact hhead.bounds
    · exact ih f hf

theorem Typed.bounds {g : MGrammar} {n A M : Nat} {final : Kind} {c : Config}
    (h : Typed g n A M final c) :
    (EnvOK n A (taskCaptures c.task) ∧ taskClock c.task ≤ M ∧ taskPosition c.task ≤ n) ∧
    (∀ f ∈ c.stack, EnvOK n A (frameCaptures f) ∧ frameClock f ≤ M ∧ framePosition f ≤ n) := by
  obtain ⟨kind, ht, hstack⟩ := h
  exact ⟨ht.bounds, hstack.bounds⟩

def captureCells (c : Config) : Nat :=
  (taskCaptures c.task).length + (c.stack.map (fun f => (frameCaptures f).length)).sum

theorem captureCells_bound {g : MGrammar} {n A M : Nat} {final : Kind} {c : Config}
    (h : Typed g n A M final c) : captureCells c ≤ (c.stack.length + 1) * A := by
  obtain ⟨htask, hstack⟩ := h.bounds
  have hh := sum_le_length_mul (fun f => (frameCaptures f).length) A c.stack
    (fun f hf => (hstack f hf).1.2)
  have ht := htask.1.2
  unfold captureCells
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- All captured span pairs retained across the task and every live frame
have a linear bound for a fixed source program. No frame is omitted. -/
theorem reachable_capture_bound (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    captureCells c ≤ (SequentialStackRank.initialCap g x e + 1) * arityBudget g := by
  have hc := captureCells_bound (reachable_typed g x e c h)
  have hstack := SequentialStackRank.reachable_stack_bound g x e c h
  exact Nat.le_trans hc (Nat.mul_le_mul_right (arityBudget g) (by omega))

theorem reachable_payload_bounds (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    (EnvOK x.length (arityBudget g) (taskCaptures c.task) ∧
      taskClock c.task ≤ SequentialClock.positionClock g x.length ∧ taskPosition c.task ≤ x.length) ∧
    (∀ f ∈ c.stack, EnvOK x.length (arityBudget g) (frameCaptures f) ∧
      frameClock f ≤ SequentialClock.positionClock g x.length ∧ framePosition f ≤ x.length) :=
  (reachable_typed g x e c h).bounds

end Shallot.MacroPeg.CBV.SequentialStackPayload
