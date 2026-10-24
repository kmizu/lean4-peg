import MacroPeg.CBV.SequentialStack

/-! A deterministic Seq evaluator with one current capture environment.
Structural continuation frames contain no environments. Entering a rule body
saves the caller environment once in a scope frame; returning restores it.
The semantics and original input agree with `SequentialStack`. -/
namespace Shallot.MacroPeg.CBV.SequentialSharedStack

open Shallot (beqChar leChar stripPrefix?)
abbrev CaptureEnv := SequentialSpanRecompute.Env
abbrev SpanEval := SequentialSpanRecompute.eval
abbrev SpanArgs := SequentialSpanRecompute.evalArgs
abbrev SpanQuery := SequentialSpanRecompute.query

abbrev ArgsResult := Option (Option (CaptureEnv × Nat))

inductive Value where
  | expr (result : Res)
  | args (result : ArgsResult)
  deriving DecidableEq, Repr

inductive Task where
  | expr (clock : Nat) (e : MExp) (pos : Nat)
  | args (clock : Nat) (es : List MExp) (pos : Nat)
  | query (clock rule : Nat) (env : CaptureEnv) (pos : Nat)
  | value (v : Value)

inductive Frame where
  | seq (clock : Nat) (right : MExp)
  | alt (clock : Nat) (right : MExp) (pos : Nat)
  | notP (pos : Nat)
  | star (clock : Nat) (body : MExp) (pos : Nat)
  | argHead (clock : Nat) (tail : List MExp) (pos : Nat)
  | argCons (span : Nat × Nat)
  | call (clock rule : Nat)
  | scope (saved : CaptureEnv)

structure Config where
  task : Task
  env : CaptureEnv
  stack : List Frame

abbrev atom := SequentialStack.atom

/-- One deterministic transition. Repetition replaces its frame on each
iteration instead of accumulating frames for the consumed input. -/
def step (g : MGrammar) (x : List Char) : Config → Option Config
  | ⟨.expr m (.seq a b) p, E, K⟩ => some ⟨.expr m a p, E, .seq m b :: K⟩
  | ⟨.expr m (.alt a b) p, E, K⟩ => some ⟨.expr m a p, E, .alt m b p :: K⟩
  | ⟨.expr m (.notP a) p, E, K⟩ => some ⟨.expr m a p, E, .notP p :: K⟩
  | ⟨.expr m (.star a) p, E, K⟩ => some ⟨.expr m a p, E, .star m a p :: K⟩
  | ⟨.expr m (.call i args) p, E, K⟩ =>
    match ruleAtM g.rules i with
    | some rule =>
      if rule.arity = args.length then some ⟨.args m args p, E, .call m i :: K⟩
      else some ⟨.value (.expr (some none)), E, K⟩
    | none => some ⟨.value (.expr (some none)), E, K⟩
  | ⟨.expr _ e p, E, K⟩ => some ⟨.value (.expr (atom x E e p)), E, K⟩
  | ⟨.args _ [] p, E, K⟩ => some ⟨.value (.args (some (some ([], p)))), E, K⟩
  | ⟨.args m (a :: args) p, E, K⟩ => some ⟨.expr m a p, E, .argHead m args p :: K⟩
  | ⟨.query 0 _ _ _, E, K⟩ => some ⟨.value (.expr none), E, K⟩
  | ⟨.query (m + 1) i W p, E, K⟩ =>
    if p ≤ x.length then
      match ruleAtM g.rules i with
      | some rule => some ⟨.expr m rule.body p, W, .scope E :: K⟩
      | none => some ⟨.value (.expr none), E, K⟩
    else some ⟨.value (.expr none), E, K⟩
  | ⟨.value (.expr result), E, .seq m b :: K⟩ =>
    match result with
    | some (some q) => some ⟨.expr m b q, E, K⟩
    | result => some ⟨.value (.expr result), E, K⟩
  | ⟨.value (.expr result), E, .alt m b p :: K⟩ =>
    match result with
    | some none => some ⟨.expr m b p, E, K⟩
    | result => some ⟨.value (.expr result), E, K⟩
  | ⟨.value (.expr result), E, .notP p :: K⟩ =>
    some ⟨.value (.expr (match result with
      | some (some _) => some none
      | some none => some (some p)
      | none => none)), E, K⟩
  | ⟨.value (.expr result), E, .star m a p :: K⟩ =>
    match result with
    | none => some ⟨.value (.expr none), E, K⟩
    | some none => some ⟨.value (.expr (some (some p))), E, K⟩
    | some (some q) =>
      if q < p then some ⟨.expr m (.star a) q, E, K⟩ else some ⟨.value (.expr none), E, K⟩
  | ⟨.value (.expr result), E, .argHead m args p :: K⟩ =>
    match result with
    | none => some ⟨.value (.args none), E, K⟩
    | some none => some ⟨.value (.args (some none)), E, K⟩
    | some (some q) => some ⟨.args m args q, E, .argCons (p, min q p) :: K⟩
  | ⟨.value (.args result), E, .argCons span :: K⟩ =>
    some ⟨.value (.args (match result with
      | some (some (W, q)) => some (some (span :: W, q))
      | result => result)), E, K⟩
  | ⟨.value (.args result), E, .call m i :: K⟩ =>
    match result with
    | none => some ⟨.value (.expr none), E, K⟩
    | some none => some ⟨.value (.expr (some none)), E, K⟩
    | some (some (W, q)) => some ⟨.query m i W q, E, K⟩
  | ⟨.value v, _, .scope E :: K⟩ => some ⟨.value v, E, K⟩
  | _ => none

inductive Runs (g : MGrammar) (x : List Char) : Config → Config → Prop where
  | refl (c) : Runs g x c c
  | cons {a b c} (h : step g x a = some b) (tail : Runs g x b c) : Runs g x a c

theorem Runs.single {g : MGrammar} {x : List Char} {a b : Config}
    (h : step g x a = some b) : Runs g x a b := .cons h (.refl _)

theorem Runs.trans {g : MGrammar} {x : List Char} {a b c : Config}
    (h : Runs g x a b) (h' : Runs g x b c) : Runs g x a c := by
  induction h with
  | refl => exact h'
  | cons hs ht ih => exact .cons hs (ih h')

theorem terminal_unique {g : MGrammar} {x : List Char} {start a b : Config}
    (h : Runs g x start a) (h' : Runs g x start b)
    (ha : step g x a = none) (hb : step g x b = none) : a = b := by
  induction h generalizing b with
  | refl =>
    cases h' with
    | refl => rfl
    | cons hs ht => rw [ha] at hs; cases hs
  | cons hs ht ih =>
    cases h' with
    | refl => rw [hb] at hs; cases hs
    | cons hs' ht' =>
      rw [hs] at hs'
      cases hs'
      exact ih ht' ha hb

def QueryRuns (g : MGrammar) (x : List Char) (m : Nat) : Prop :=
  ∀ i W p E K, Runs g x ⟨.query m i W p, E, K⟩ ⟨.value (.expr (SpanQuery g x m i W p)), E, K⟩

theorem star_runs (g : MGrammar) (x : List Char) (m : Nat) (E : CaptureEnv) (a : MExp)
    (child : ∀ p K, Runs g x ⟨.expr m a p, E, K⟩
      ⟨.value (.expr (SpanEval g x (SpanQuery g x m) E a p)), E, K⟩) :
    ∀ p K, Runs g x ⟨.expr m (.star a) p, E, K⟩
      ⟨.value (.expr (SpanEval g x (SpanQuery g x m) E (.star a) p)), E, K⟩ := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro K
    apply Runs.cons (b := ⟨.expr m a p, E, .star m a p :: K⟩) rfl
    have hc := child p (.star m a p :: K)
    change Runs g x _ ⟨.value (.expr (evStar (fun q => SpanEval g x (SpanQuery g x m) E a q) p)), E, K⟩
    cases hv : SpanEval g x (SpanQuery g x m) E a p with
    | none =>
      rw [hv] at hc
      rw [evStar_none hv]
      exact hc.trans (.single rfl)
    | some result =>
      cases result with
      | none =>
        rw [hv] at hc
        rw [evStar_fail hv]
        exact hc.trans (.single rfl)
      | some q =>
        rw [hv] at hc
        by_cases hq : q < p
        · rw [evStar_ok hv hq]
          exact hc.trans (.cons (by simp [step, hq]) (ih q hq K))
        · rw [evStar_stuck hv hq]
          exact hc.trans (.single (by simp [step, hq]))

mutual
  theorem expression_runs (g : MGrammar) (x : List Char) (m : Nat) (hq : QueryRuns g x m) :
      ∀ e E p K, Runs g x ⟨.expr m e p, E, K⟩
        ⟨.value (.expr (SpanEval g x (SpanQuery g x m) E e p)), E, K⟩
    | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _ | .range _ _, _, _, _
    | .lit _, _, _, _ | .param _, _, _, _ | .dbg _, _, _, _ | .lam _ _, _, _, _
    | .callParam _ _, _, _, _ | .invoke _ _ _, _, _, _ => .single rfl
    | .seq a b, E, p, K => by
      apply Runs.cons (b := ⟨.expr m a p, E, .seq m b :: K⟩) rfl
      have hc := expression_runs g x m hq a E p (.seq m b :: K)
      cases hv : SpanEval g x (SpanQuery g x m) E a p with
      | none =>
        rw [hv] at hc
        simpa only [SequentialSpanRecompute.eval, hv] using hc.trans (.single rfl)
      | some result =>
        cases result with
        | none =>
          rw [hv] at hc
          simpa only [SequentialSpanRecompute.eval, hv] using hc.trans (.single rfl)
        | some q =>
          rw [hv] at hc
          simpa only [SequentialSpanRecompute.eval, hv] using
            hc.trans (.cons rfl (expression_runs g x m hq b E q K))
    | .alt a b, E, p, K => by
      apply Runs.cons (b := ⟨.expr m a p, E, .alt m b p :: K⟩) rfl
      have hc := expression_runs g x m hq a E p (.alt m b p :: K)
      cases hv : SpanEval g x (SpanQuery g x m) E a p with
      | none =>
        rw [hv] at hc
        simpa only [SequentialSpanRecompute.eval, hv] using hc.trans (.single rfl)
      | some result =>
        cases result with
        | none =>
          rw [hv] at hc
          simpa only [SequentialSpanRecompute.eval, hv] using
            hc.trans (.cons rfl (expression_runs g x m hq b E p K))
        | some q =>
          rw [hv] at hc
          simpa only [SequentialSpanRecompute.eval, hv] using hc.trans (.single rfl)
    | .notP a, E, p, K => by
      apply Runs.cons (b := ⟨.expr m a p, E, .notP p :: K⟩) rfl
      exact (expression_runs g x m hq a E p (.notP p :: K)).trans (.single rfl)
    | .star a, E, p, K =>
      star_runs g x m E a (fun p K => expression_runs g x m hq a E p K) p K
    | .call i args, E, p, K => by
      cases hr : ruleAtM g.rules i with
      | none =>
        apply Runs.single
        simp [step, SequentialSpanRecompute.eval, hr]
      | some rule =>
        by_cases ha : rule.arity = args.length
        · apply Runs.cons (b := ⟨.args m args p, E, .call m i :: K⟩) (by simp [step, hr, ha])
          have hc := arguments_runs g x m hq args E p (.call m i :: K)
          cases hv : SpanArgs g x (SpanQuery g x m) E args p with
          | none =>
            rw [hv] at hc
            simpa only [SequentialSpanRecompute.eval, hr, if_pos ha, hv] using hc.trans (.single rfl)
          | some result =>
            cases result with
            | none =>
              rw [hv] at hc
              simpa only [SequentialSpanRecompute.eval, hr, if_pos ha, hv] using hc.trans (.single rfl)
            | some Wq =>
              obtain ⟨W, q⟩ := Wq
              rw [hv] at hc
              simpa only [SequentialSpanRecompute.eval, hr, if_pos ha, hv] using
                hc.trans (.cons rfl (hq i W q E K))
        · apply Runs.single
          simp [step, SequentialSpanRecompute.eval, hr, ha]

  theorem arguments_runs (g : MGrammar) (x : List Char) (m : Nat) (hq : QueryRuns g x m) :
      ∀ args E p K, Runs g x ⟨.args m args p, E, K⟩
        ⟨.value (.args (SpanArgs g x (SpanQuery g x m) E args p)), E, K⟩
    | [], _, _, _ => .single rfl
    | a :: args, E, p, K => by
      apply Runs.cons (b := ⟨.expr m a p, E, .argHead m args p :: K⟩) rfl
      have hc := expression_runs g x m hq a E p (.argHead m args p :: K)
      cases hv : SpanEval g x (SpanQuery g x m) E a p with
      | none =>
        rw [hv] at hc
        simpa only [SequentialSpanRecompute.evalArgs, hv] using hc.trans (.single rfl)
      | some result =>
        cases result with
        | none =>
          rw [hv] at hc
          simpa only [SequentialSpanRecompute.evalArgs, hv] using hc.trans (.single rfl)
        | some q =>
          rw [hv] at hc
          have ht := arguments_runs g x m hq args E q (.argCons (p, min q p) :: K)
          simp only [SequentialSpanRecompute.evalArgs, hv]
          exact hc.trans (.cons rfl (ht.trans (.single rfl)))
end


theorem query_runs (g : MGrammar) (x : List Char) : ∀ m, QueryRuns g x m
  | 0 => fun _ _ _ _ _ => .single rfl
  | m + 1 => by
    intro i W p E K
    by_cases hp : p ≤ x.length
    · cases hr : ruleAtM g.rules i with
      | none => apply Runs.single; simp [step, SequentialSpanRecompute.query, hp, hr]
      | some rule =>
        apply Runs.cons (b := ⟨.expr m rule.body p, W, .scope E :: K⟩)
          (by simp [step, hp, hr])
        simpa only [SequentialSpanRecompute.query, if_pos hp, hr] using
          (expression_runs g x m (query_runs g x m) rule.body W p (.scope E :: K)).trans
            (.single rfl)
    · apply Runs.single
      simp [step, SequentialSpanRecompute.query, hp]

def initial (g : MGrammar) (x : List Char) (e : MExp) : Config :=
  ⟨.expr (SequentialClock.positionClock g x.length) e x.length, [], []⟩

theorem initial_runs (g : MGrammar) (x : List Char) (e : MExp) :
    Runs g x (initial g x e)
      ⟨.value (.expr (SequentialSpanRecompute.run g x e)), [], []⟩ :=
  expression_runs g x _ (query_runs g x _) e [] x.length []

/-- The terminal result and the restored outer environment are both unique. -/
theorem result_iff (g : MGrammar) (x : List Char) (e : MExp) (r : Res)
    (E : CaptureEnv) :
    Runs g x (initial g x e) ⟨.value (.expr r), E, []⟩ ↔
      r = SequentialSpanRecompute.run g x e ∧ E = [] := by
  constructor
  · intro h
    have he := terminal_unique h (initial_runs g x e) rfl rfl
    cases he
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact initial_runs g x e

theorem accepts_iff {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (x : List Char) : Runs g x (initial g x e) ⟨.value (.expr (some (some 0))), [], []⟩ ↔
      SObs g .callByValueSeq e x (some []) := by
  simp only [result_iff, eq_self, and_true]
  exact eq_comm.trans (SequentialSpanRecompute.run_accepts_iff hg he x)

/-- Agreement with the original machine uses the original input verbatim. -/
theorem original_result_iff (g : MGrammar) (x : List Char) (e : MExp) (r : Res) :
    Runs g x (initial g x e) ⟨.value (.expr r), [], []⟩ ↔
      SequentialStack.Runs g x (SequentialStack.initial g x e)
        ⟨.value (.expr r), []⟩ := by
  simp only [result_iff, SequentialStack.result_iff, eq_self, and_true]

/-- Executable fuelled driver. Environments are returned as part of the state,
so the restoration guarantee is checked rather than discarded. -/
def drive (g : MGrammar) (x : List Char) : Nat → Config → Option Config
  | 0, _ => none
  | fuel + 1, c =>
    match step g x c with
    | some next => drive g x fuel next
    | none => some c

theorem drive_of_runs {g : MGrammar} {x : List Char} {a b : Config}
    (h : Runs g x a b) (hb : step g x b = none) :
    ∃ fuel, drive g x fuel a = some b := by
  induction h with
  | refl => exact ⟨1, by simp [drive, hb]⟩
  | cons hs ht ih =>
    obtain ⟨fuel, hfuel⟩ := ih hb
    exact ⟨fuel + 1, by simp only [drive, hs, hfuel]⟩

theorem runs_of_drive {g : MGrammar} {x : List Char} (fuel : Nat) (c b : Config)
    (h : drive g x fuel c = some b) : Runs g x c b ∧ step g x b = none := by
  induction fuel generalizing c with
  | zero => cases h
  | succ fuel ih =>
    cases hs : step g x c with
    | some next =>
      simp only [drive, hs] at h
      obtain ⟨hr, ht⟩ := ih next h
      exact ⟨.cons hs hr, ht⟩
    | none =>
      simp only [drive, hs, Option.some.injEq] at h
      subst b
      exact ⟨.refl _, hs⟩

theorem drive_result_iff (g : MGrammar) (x : List Char) (e : MExp) (r : Res)
    (E : CaptureEnv) :
    (∃ fuel, drive g x fuel (initial g x e) = some ⟨.value (.expr r), E, []⟩) ↔
      r = SequentialSpanRecompute.run g x e ∧ E = [] := by
  constructor
  · rintro ⟨fuel, h⟩
    exact (result_iff g x e r E).mp (runs_of_drive fuel _ _ h).1
  · intro h
    exact drive_of_runs ((result_iff g x e r E).mpr h) rfl

end Shallot.MacroPeg.CBV.SequentialSharedStack
