import MacroPeg.CBV.SequentialSpanRecompute

namespace Shallot.MacroPeg.CBV.SequentialStack

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
  | expr (clock : Nat) (env : CaptureEnv) (e : MExp) (pos : Nat)
  | args (clock : Nat) (env : CaptureEnv) (es : List MExp) (pos : Nat)
  | query (clock rule : Nat) (env : CaptureEnv) (pos : Nat)
  | value (v : Value)

inductive Frame where
  | seq (clock : Nat) (env : CaptureEnv) (right : MExp)
  | alt (clock : Nat) (env : CaptureEnv) (right : MExp) (pos : Nat)
  | notP (pos : Nat)
  | star (clock : Nat) (env : CaptureEnv) (body : MExp) (pos : Nat)
  | argHead (clock : Nat) (env : CaptureEnv) (tail : List MExp) (pos : Nat)
  | argCons (span : Nat × Nat)
  | call (clock rule : Nat)

structure Config where
  task : Task
  stack : List Frame

def atom (x : List Char) (E : CaptureEnv) : MExp → Nat → Res
  | .eps, p | .dbg _, p | .lam _ _, p => some (some p)
  | .any, p =>
    match sfx x p with
    | _ :: rest => some (some rest.length)
    | [] => some none
  | .chr c, p =>
    match sfx x p with
    | d :: rest => if beqChar c d then some (some rest.length) else some none
    | [] => some none
  | .range lo hi, p =>
    match sfx x p with
    | d :: rest => if leChar lo d && leChar d hi then some (some rest.length) else some none
    | [] => some none
  | .lit w, p =>
    match stripPrefix? w (sfx x p) with
    | some rest => some (some rest.length)
    | none => some none
  | .param k, p =>
    match E[k]? with
    | some (a, b) => SequentialSpanRecompute.matchSpan x a b p
    | none => some none
  | .invoke _ _ _, _ => none
  | _, _ => some none

/-- One deterministic transition. Repetition replaces its frame on each
iteration instead of accumulating frames for the consumed input. -/
def step (g : MGrammar) (x : List Char) : Config → Option Config
  | ⟨.expr m E (.seq a b) p, K⟩ => some ⟨.expr m E a p, .seq m E b :: K⟩
  | ⟨.expr m E (.alt a b) p, K⟩ => some ⟨.expr m E a p, .alt m E b p :: K⟩
  | ⟨.expr m E (.notP a) p, K⟩ => some ⟨.expr m E a p, .notP p :: K⟩
  | ⟨.expr m E (.star a) p, K⟩ => some ⟨.expr m E a p, .star m E a p :: K⟩
  | ⟨.expr m E (.call i args) p, K⟩ =>
    match ruleAtM g.rules i with
    | some rule =>
      if rule.arity = args.length then some ⟨.args m E args p, .call m i :: K⟩
      else some ⟨.value (.expr (some none)), K⟩
    | none => some ⟨.value (.expr (some none)), K⟩
  | ⟨.expr _ E e p, K⟩ => some ⟨.value (.expr (atom x E e p)), K⟩
  | ⟨.args _ _ [] p, K⟩ => some ⟨.value (.args (some (some ([], p)))), K⟩
  | ⟨.args m E (a :: args) p, K⟩ => some ⟨.expr m E a p, .argHead m E args p :: K⟩
  | ⟨.query 0 _ _ _, K⟩ => some ⟨.value (.expr none), K⟩
  | ⟨.query (m + 1) i E p, K⟩ =>
    if p ≤ x.length then
      match ruleAtM g.rules i with
      | some rule => some ⟨.expr m E rule.body p, K⟩
      | none => some ⟨.value (.expr none), K⟩
    else some ⟨.value (.expr none), K⟩
  | ⟨.value (.expr result), .seq m E b :: K⟩ =>
    match result with
    | some (some q) => some ⟨.expr m E b q, K⟩
    | result => some ⟨.value (.expr result), K⟩
  | ⟨.value (.expr result), .alt m E b p :: K⟩ =>
    match result with
    | some none => some ⟨.expr m E b p, K⟩
    | result => some ⟨.value (.expr result), K⟩
  | ⟨.value (.expr result), .notP p :: K⟩ =>
    some ⟨.value (.expr (match result with
      | some (some _) => some none
      | some none => some (some p)
      | none => none)), K⟩
  | ⟨.value (.expr result), .star m E a p :: K⟩ =>
    match result with
    | none => some ⟨.value (.expr none), K⟩
    | some none => some ⟨.value (.expr (some (some p))), K⟩
    | some (some q) =>
      if q < p then some ⟨.expr m E (.star a) q, K⟩ else some ⟨.value (.expr none), K⟩
  | ⟨.value (.expr result), .argHead m E args p :: K⟩ =>
    match result with
    | none => some ⟨.value (.args none), K⟩
    | some none => some ⟨.value (.args (some none)), K⟩
    | some (some q) => some ⟨.args m E args q, .argCons (p, min q p) :: K⟩
  | ⟨.value (.args result), .argCons span :: K⟩ =>
    some ⟨.value (.args (match result with
      | some (some (W, q)) => some (some (span :: W, q))
      | result => result)), K⟩
  | ⟨.value (.args result), .call m i :: K⟩ =>
    match result with
    | none => some ⟨.value (.expr none), K⟩
    | some none => some ⟨.value (.expr (some none)), K⟩
    | some (some (W, q)) => some ⟨.query m i W q, K⟩
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
  ∀ i E p K, Runs g x ⟨.query m i E p, K⟩ ⟨.value (.expr (SpanQuery g x m i E p)), K⟩

theorem star_runs (g : MGrammar) (x : List Char) (m : Nat) (E : CaptureEnv) (a : MExp)
    (child : ∀ p K, Runs g x ⟨.expr m E a p, K⟩
      ⟨.value (.expr (SpanEval g x (SpanQuery g x m) E a p)), K⟩) :
    ∀ p K, Runs g x ⟨.expr m E (.star a) p, K⟩
      ⟨.value (.expr (SpanEval g x (SpanQuery g x m) E (.star a) p)), K⟩ := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro K
    apply Runs.cons (b := ⟨.expr m E a p, .star m E a p :: K⟩) rfl
    have hc := child p (.star m E a p :: K)
    change Runs g x _ ⟨.value (.expr (evStar (fun q => SpanEval g x (SpanQuery g x m) E a q) p)), K⟩
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
      ∀ e E p K, Runs g x ⟨.expr m E e p, K⟩
        ⟨.value (.expr (SpanEval g x (SpanQuery g x m) E e p)), K⟩
    | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _ | .range _ _, _, _, _
    | .lit _, _, _, _ | .param _, _, _, _ | .dbg _, _, _, _ | .lam _ _, _, _, _
    | .callParam _ _, _, _, _ | .invoke _ _ _, _, _, _ => .single rfl
    | .seq a b, E, p, K => by
      apply Runs.cons (b := ⟨.expr m E a p, .seq m E b :: K⟩) rfl
      have hc := expression_runs g x m hq a E p (.seq m E b :: K)
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
      apply Runs.cons (b := ⟨.expr m E a p, .alt m E b p :: K⟩) rfl
      have hc := expression_runs g x m hq a E p (.alt m E b p :: K)
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
      apply Runs.cons (b := ⟨.expr m E a p, .notP p :: K⟩) rfl
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
        · apply Runs.cons (b := ⟨.args m E args p, .call m i :: K⟩) (by simp [step, hr, ha])
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
                hc.trans (.cons rfl (hq i W q K))
        · apply Runs.single
          simp [step, SequentialSpanRecompute.eval, hr, ha]

  theorem arguments_runs (g : MGrammar) (x : List Char) (m : Nat) (hq : QueryRuns g x m) :
      ∀ args E p K, Runs g x ⟨.args m E args p, K⟩
        ⟨.value (.args (SpanArgs g x (SpanQuery g x m) E args p)), K⟩
    | [], _, _, _ => .single rfl
    | a :: args, E, p, K => by
      apply Runs.cons (b := ⟨.expr m E a p, .argHead m E args p :: K⟩) rfl
      have hc := expression_runs g x m hq a E p (.argHead m E args p :: K)
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
  | 0 => fun _ _ _ _ => .single rfl
  | m + 1 => by
    intro i E p K
    by_cases hp : p ≤ x.length
    · cases hr : ruleAtM g.rules i with
      | none => apply Runs.single; simp [step, SequentialSpanRecompute.query, hp, hr]
      | some rule =>
        apply Runs.cons (b := ⟨.expr m E rule.body p, K⟩) (by simp [step, hp, hr])
        simpa only [SequentialSpanRecompute.query, if_pos hp, hr] using
          expression_runs g x m (query_runs g x m) rule.body E p K
    · apply Runs.single
      simp [step, SequentialSpanRecompute.query, hp]

def initial (g : MGrammar) (x : List Char) (e : MExp) : Config :=
  ⟨.expr (SequentialClock.positionClock g x.length) [] e x.length, []⟩

theorem initial_runs (g : MGrammar) (x : List Char) (e : MExp) :
    Runs g x (initial g x e) ⟨.value (.expr (SequentialSpanRecompute.run g x e)), []⟩ :=
  expression_runs g x _ (query_runs g x _) e [] x.length []

theorem result_iff (g : MGrammar) (x : List Char) (e : MExp) (r : Res) :
    Runs g x (initial g x e) ⟨.value (.expr r), []⟩ ↔ r = SequentialSpanRecompute.run g x e := by
  constructor
  · intro h
    have he := terminal_unique h (initial_runs g x e) rfl rfl
    cases he
    rfl
  · intro h; subst r; exact initial_runs g x e

theorem accepts_iff {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (x : List Char) : Runs g x (initial g x e) ⟨.value (.expr (some (some 0))), []⟩ ↔
      SObs g .callByValueSeq e x (some []) := by
  rw [result_iff]
  exact (eq_comm.trans (SequentialSpanRecompute.run_accepts_iff hg he x))

def drive (g : MGrammar) (x : List Char) : Nat → Config → Option Value
  | 0, _ => none
  | fuel + 1, c =>
    match step g x c with
    | some next => drive g x fuel next
    | none =>
      match c.task, c.stack with
      | .value v, [] => some v
      | _, _ => none

theorem drive_of_runs {g : MGrammar} {x : List Char} {a b : Config} (h : Runs g x a b)
    (v : Value) (hb : b = ⟨.value v, []⟩) : ∃ fuel, drive g x fuel a = some v := by
  revert hb
  induction h with
  | refl c => intro hb; cases hb; exact ⟨1, by cases v <;> rfl⟩
  | cons hs ht ih =>
    intro hb
    obtain ⟨fuel, hfuel⟩ := ih hb
    exact ⟨fuel + 1, by simp only [drive, hs, hfuel]⟩

theorem runs_of_drive {g : MGrammar} {x : List Char} (fuel : Nat) (c : Config) (v : Value)
    (h : drive g x fuel c = some v) : Runs g x c ⟨.value v, []⟩ := by
  induction fuel generalizing c with
  | zero => cases h
  | succ fuel ih =>
    cases hs : step g x c with
    | some next =>
      simp only [drive, hs] at h
      exact .cons hs (ih next h)
    | none =>
      simp only [drive, hs] at h
      obtain ⟨task, K⟩ := c
      cases task <;> cases K <;> simp at h
      subst v
      exact .refl _

theorem drive_result_iff (g : MGrammar) (x : List Char) (e : MExp) (r : Res) :
    (∃ fuel, drive g x fuel (initial g x e) = some (.expr r)) ↔
      r = SequentialSpanRecompute.run g x e := by
  constructor
  · rintro ⟨fuel, h⟩
    exact (result_iff g x e r).mp (runs_of_drive fuel _ _ h)
  · intro h
    exact drive_of_runs ((result_iff g x e r).mpr h) (.expr r) rfl

theorem drive_accepts_iff {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (x : List Char) :
    (∃ fuel, drive g x fuel (initial g x e) = some (.expr (some (some 0)))) ↔
      SObs g .callByValueSeq e x (some []) := by
  rw [drive_result_iff]
  exact eq_comm.trans (SequentialSpanRecompute.run_accepts_iff hg he x)

end Shallot.MacroPeg.CBV.SequentialStack
