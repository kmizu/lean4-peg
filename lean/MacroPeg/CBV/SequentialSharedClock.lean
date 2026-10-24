import MacroPeg.CBV.SequentialSharedSpace

/-! One shared clock for the Seq evaluator. Entering a rule body decrements
it, and returning through a scope frame increments it. Tasks and continuation
frames store no copies of the clock. `inflate` reconstructs the previous
machine and commutes with every transition. -/
namespace Shallot.MacroPeg.CBV.SequentialSharedClock

abbrev CaptureEnv := SequentialSpanRecompute.Env

abbrev Value := SequentialSharedStack.Value

inductive Task where
  | expr (e : MExp) (pos : Nat)
  | args (es : List MExp) (pos : Nat)
  | query (rule : Nat) (env : CaptureEnv) (pos : Nat)
  | value (v : Value)

inductive Frame where
  | seq (right : MExp)
  | alt (right : MExp) (pos : Nat)
  | notP (pos : Nat)
  | star (body : MExp) (pos : Nat)
  | argHead (tail : List MExp) (pos : Nat)
  | argCons (span : Nat × Nat)
  | call (rule : Nat)
  | scope (saved : CaptureEnv)

structure Config where
  clock : Nat
  task : Task
  env : CaptureEnv
  stack : List Frame

abbrev atom := SequentialStack.atom

/-- One deterministic transition. Repetition replaces its frame on each
iteration instead of accumulating frames for the consumed input. -/
def step (g : MGrammar) (x : List Char) : Config → Option Config
  | ⟨m, .expr (.seq a b) p, E, K⟩ => some ⟨m, .expr a p, E, .seq b :: K⟩
  | ⟨m, .expr (.alt a b) p, E, K⟩ => some ⟨m, .expr a p, E, .alt b p :: K⟩
  | ⟨m, .expr (.notP a) p, E, K⟩ => some ⟨m, .expr a p, E, .notP p :: K⟩
  | ⟨m, .expr (.star a) p, E, K⟩ => some ⟨m, .expr a p, E, .star a p :: K⟩
  | ⟨m, .expr (.call i args) p, E, K⟩ =>
    match ruleAtM g.rules i with
    | some rule =>
      if rule.arity = args.length then some ⟨m, .args args p, E, .call i :: K⟩
      else some ⟨m, .value (.expr (some none)), E, K⟩
    | none => some ⟨m, .value (.expr (some none)), E, K⟩
  | ⟨m, .expr e p, E, K⟩ => some ⟨m, .value (.expr (atom x E e p)), E, K⟩
  | ⟨m, .args [] p, E, K⟩ => some ⟨m, .value (.args (some (some ([], p)))), E, K⟩
  | ⟨m, .args (a :: args) p, E, K⟩ => some ⟨m, .expr a p, E, .argHead args p :: K⟩
  | ⟨0, .query _ _ _, E, K⟩ => some ⟨0, .value (.expr none), E, K⟩
  | ⟨m + 1, .query i W p, E, K⟩ =>
    if p ≤ x.length then
      match ruleAtM g.rules i with
      | some rule => some ⟨m, .expr rule.body p, W, .scope E :: K⟩
      | none => some ⟨m + 1, .value (.expr none), E, K⟩
    else some ⟨m + 1, .value (.expr none), E, K⟩
  | ⟨m, .value (.expr result), E, .seq b :: K⟩ =>
    match result with
    | some (some q) => some ⟨m, .expr b q, E, K⟩
    | result => some ⟨m, .value (.expr result), E, K⟩
  | ⟨m, .value (.expr result), E, .alt b p :: K⟩ =>
    match result with
    | some none => some ⟨m, .expr b p, E, K⟩
    | result => some ⟨m, .value (.expr result), E, K⟩
  | ⟨m, .value (.expr result), E, .notP p :: K⟩ =>
    some ⟨m, .value (.expr (match result with
      | some (some _) => some none
      | some none => some (some p)
      | none => none)), E, K⟩
  | ⟨m, .value (.expr result), E, .star a p :: K⟩ =>
    match result with
    | none => some ⟨m, .value (.expr none), E, K⟩
    | some none => some ⟨m, .value (.expr (some (some p))), E, K⟩
    | some (some q) =>
      if q < p then some ⟨m, .expr (.star a) q, E, K⟩ else some ⟨m, .value (.expr none), E, K⟩
  | ⟨m, .value (.expr result), E, .argHead args p :: K⟩ =>
    match result with
    | none => some ⟨m, .value (.args none), E, K⟩
    | some none => some ⟨m, .value (.args (some none)), E, K⟩
    | some (some q) => some ⟨m, .args args q, E, .argCons (p, min q p) :: K⟩
  | ⟨m, .value (.args result), E, .argCons span :: K⟩ =>
    some ⟨m, .value (.args (match result with
      | some (some (W, q)) => some (some (span :: W, q))
      | result => result)), E, K⟩
  | ⟨m, .value (.args result), E, .call i :: K⟩ =>
    match result with
    | none => some ⟨m, .value (.expr none), E, K⟩
    | some none => some ⟨m, .value (.expr (some none)), E, K⟩
    | some (some (W, q)) => some ⟨m, .query i W q, E, K⟩
  | ⟨m, .value v, _, .scope E :: K⟩ => some ⟨m + 1, .value v, E, K⟩
  | _ => none


def inflateTask (m : Nat) : Task → SequentialSharedStack.Task
  | .expr e p => .expr m e p
  | .args es p => .args m es p
  | .query i W p => .query m i W p
  | .value v => .value v

def inflateStack (m : Nat) : List Frame → List SequentialSharedStack.Frame
  | [] => []
  | .seq b :: K => .seq m b :: inflateStack m K
  | .alt b p :: K => .alt m b p :: inflateStack m K
  | .notP p :: K => .notP p :: inflateStack m K
  | .star a p :: K => .star m a p :: inflateStack m K
  | .argHead es p :: K => .argHead m es p :: inflateStack m K
  | .argCons span :: K => .argCons span :: inflateStack m K
  | .call i :: K => .call m i :: inflateStack m K
  | .scope E :: K => .scope E :: inflateStack (m + 1) K

def inflate (c : Config) : SequentialSharedStack.Config :=
  ⟨inflateTask c.clock c.task, c.env, inflateStack c.clock c.stack⟩

/-- Reconstruction commutes with every actual transition, including the
clock-zero branch, invalid queries, and scope returns. -/
theorem step_commutes (g : MGrammar) (x : List Char) (c : Config) :
    (step g x c).map inflate = SequentialSharedStack.step g x (inflate c) := by
  obtain ⟨m,t,E,K⟩ := c
  cases t with
  | expr e p =>
    cases e <;> try rfl
    rename_i i args
    cases hr : ruleAtM g.rules i with
    | none => simp [step, inflate, inflateTask, SequentialSharedStack.step, hr]
    | some rule =>
      by_cases ha : rule.arity = args.length <;>
        simp [step, inflate, inflateTask, inflateStack, SequentialSharedStack.step, hr, ha]
  | args es p => cases es <;> rfl
  | query i W p =>
    cases m with
    | zero => rfl
    | succ m =>
      by_cases hp : p ≤ x.length
      · cases hr : ruleAtM g.rules i <;>
          simp [step, inflate, inflateTask, inflateStack, SequentialSharedStack.step, hp, hr]
      · simp [step, inflate, inflateTask, SequentialSharedStack.step, hp]
  | value v =>
    cases K with
    | nil => cases v <;> rfl
    | cons f K =>
      cases f <;> cases v <;> try rfl
      all_goals rename_i r; cases r with
      | none => rfl
      | some result =>
        cases result with
        | none => rfl
        | some val =>
          first
          | rfl
          | simp only [step, inflate, inflateTask, inflateStack, SequentialSharedStack.step]
            split <;> rfl

inductive Runs (g : MGrammar) (x : List Char) : Config → Config → Prop where
  | refl (c) : Runs g x c c
  | cons {a b c} (h : step g x a = some b) (tail : Runs g x b c) : Runs g x a c

theorem runs_inflate {g : MGrammar} {x : List Char} {a b : Config}
    (h : Runs g x a b) : SequentialSharedStack.Runs g x (inflate a) (inflate b) := by
  induction h with
  | refl => exact .refl _
  | cons hs ht ih =>
    apply SequentialSharedStack.Runs.cons _ ih
    rw [← step_commutes, hs]
    rfl

theorem Runs.lift {g : MGrammar} {x : List Char} {a : Config}
    {b : SequentialSharedStack.Config}
    (h : SequentialSharedStack.Runs g x (inflate a) b) :
    ∃ c, Runs g x a c ∧ inflate c = b := by
  generalize ha : inflate a = start at h
  induction h generalizing a with
  | refl => exact ⟨a, .refl _, ha⟩
  | @cons start mid last hs ht ih =>
    rw [← ha, ← step_commutes] at hs
    cases hn : step g x a with
    | none => simp [hn] at hs
    | some next =>
      simp only [hn, Option.map_some, Option.some.injEq] at hs
      obtain ⟨c,hr,hc⟩ := ih hs
      exact ⟨c,.cons hn hr,hc⟩

def scopeCount : List Frame → Nat
  | [] => 0
  | .scope _ :: K => scopeCount K + 1
  | _ :: K => scopeCount K

def clockMass (c : Config) : Nat := c.clock + scopeCount c.stack

/-- The one clock and the number of active scopes have constant sum. -/
theorem step_clock_mass (g : MGrammar) (x : List Char) {c next : Config}
    (hs : step g x c = some next) : clockMass next = clockMass c := by
  obtain ⟨m,t,E,K⟩ := c
  cases t with
  | expr e p =>
    cases e <;> try (cases hs <;> rfl)
    rename_i i args
    cases hr : ruleAtM g.rules i with
    | none => simp only [step, hr] at hs; cases hs <;> rfl
    | some rule =>
      by_cases ha : rule.arity = args.length <;>
        simp only [step, hr, ha, if_pos] at hs <;> cases hs <;> rfl
  | args es p => cases es <;> cases hs <;> rfl
  | query i W p =>
    cases m with
    | zero => cases hs <;> rfl
    | succ m =>
      by_cases hp : p ≤ x.length
      · cases hr : ruleAtM g.rules i <;>
          simp only [step, hp, if_pos, hr] at hs <;> cases hs <;>
          simp [clockMass, scopeCount, Nat.add_assoc, Nat.add_comm]
      · simp only [step, hp] at hs; cases hs <;> rfl
  | value v =>
    cases K with
    | nil => cases v <;> cases hs
    | cons f K =>
      cases f <;> cases v <;> try (cases hs <;> rfl)
      all_goals first
      | cases hs <;> simp [clockMass, scopeCount, Nat.add_assoc, Nat.add_comm]
      | rename_i r; cases r with
        | none => cases hs <;> rfl
        | some result =>
          cases result with
          | none => cases hs <;> rfl
          | some val =>
            first
            | cases hs <;> rfl
            | simp only [step] at hs
              split at hs <;> cases hs <;> rfl

theorem runs_clock_mass {g : MGrammar} {x : List Char} {a b : Config}
    (h : Runs g x a b) : clockMass b = clockMass a := by
  induction h with
  | refl => rfl
  | cons hs ht ih => exact ih.trans (step_clock_mass g x hs)

def initial (g : MGrammar) (x : List Char) (e : MExp) : Config :=
  ⟨SequentialClock.positionClock g x.length, .expr e x.length, [], []⟩

theorem inflate_initial (g : MGrammar) (x : List Char) (e : MExp) :
    inflate (initial g x e) = SequentialSharedStack.initial g x e := rfl

theorem reachable_clock_mass (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    c.clock + scopeCount c.stack = SequentialClock.positionClock g x.length :=
  runs_clock_mass h

theorem inflateStack_eq_nil (m : Nat) (K : List Frame) :
    inflateStack m K = [] ↔ K = [] := by
  cases K with
  | nil => simp [inflateStack]
  | cons f K => cases f <;> simp [inflateStack]

theorem inflate_terminal {c : Config} {v : Value} {E : CaptureEnv}
    (h : inflate c = ⟨.value v,E,[]⟩) :
    ∃ m, c = ⟨m,.value v,E,[]⟩ := by
  obtain ⟨m,t,W,K⟩ := c
  have hk : inflateStack m K = [] := congrArg SequentialSharedStack.Config.stack h
  have hk' := (inflateStack_eq_nil m K).mp hk
  subst K
  cases t <;> simp only [inflate, inflateTask, inflateStack,
    SequentialSharedStack.Config.mk.injEq] at h
  all_goals obtain ⟨ht,hE,_⟩ := h; cases ht <;> subst W <;> exact ⟨m,rfl⟩

theorem initial_runs (g : MGrammar) (x : List Char) (e : MExp) :
    Runs g x (initial g x e)
      ⟨SequentialClock.positionClock g x.length,
        .value (.expr (SequentialSpanRecompute.run g x e)),[],[]⟩ := by
  have ho := SequentialSharedStack.initial_runs g x e
  rw [← inflate_initial] at ho
  obtain ⟨c,hr,hc⟩ := Runs.lift ho
  obtain ⟨m,rfl⟩ := inflate_terminal hc
  have hm := runs_clock_mass hr
  simp only [clockMass, scopeCount, Nat.add_zero, initial] at hm
  subst m
  exact hr

/-- Both the one clock and the number of suspended environments are linear
in input length, with a constant depending only on the fixed grammar. -/
theorem reachable_clock_bounds (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    c.clock ≤ (g.rules.length + 1) * (x.length + 1) ∧
      scopeCount c.stack ≤ (g.rules.length + 1) * (x.length + 1) := by
  have hm := reachable_clock_mass g x e c h
  unfold SequentialClock.positionClock at hm
  omega

theorem result_iff (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (r : Res)
    (E : CaptureEnv) :
    Runs g x (initial g x e) ⟨m,.value (.expr r),E,[]⟩ ↔
      r = SequentialSpanRecompute.run g x e ∧ E = [] ∧
        m = SequentialClock.positionClock g x.length := by
  constructor
  · intro h
    have ho := runs_inflate h
    have he := (SequentialSharedStack.result_iff g x e r E).mp ho
    have hm := reachable_clock_mass g x e _ h
    exact ⟨he.1,he.2,hm⟩
  · rintro ⟨rfl,rfl,rfl⟩
    exact initial_runs g x e

theorem accepts_iff {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (x : List Char) :
    Runs g x (initial g x e)
      ⟨SequentialClock.positionClock g x.length,.value (.expr (some (some 0))),[],[]⟩ ↔
      SObs g .callByValueSeq e x (some []) := by
  simp only [result_iff, eq_self, and_self, and_true]
  exact eq_comm.trans (SequentialSpanRecompute.run_accepts_iff hg he x)

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
    obtain ⟨fuel,hfuel⟩ := ih hb
    exact ⟨fuel + 1,by simp only [drive,hs,hfuel]⟩

theorem runs_of_drive {g : MGrammar} {x : List Char} (fuel : Nat) (c b : Config)
    (h : drive g x fuel c = some b) : Runs g x c b ∧ step g x b = none := by
  induction fuel generalizing c with
  | zero => cases h
  | succ fuel ih =>
    cases hs : step g x c with
    | some next =>
      simp only [drive,hs] at h
      obtain ⟨hr,ht⟩ := ih next h
      exact ⟨.cons hs hr,ht⟩
    | none =>
      simp only [drive,hs,Option.some.injEq] at h
      subst b
      exact ⟨.refl _,hs⟩

theorem drive_result_iff (g : MGrammar) (x : List Char) (e : MExp)
    (m : Nat) (r : Res) (E : CaptureEnv) :
    (∃ fuel, drive g x fuel (initial g x e) = some ⟨m,.value (.expr r),E,[]⟩) ↔
      r = SequentialSpanRecompute.run g x e ∧ E = [] ∧
        m = SequentialClock.positionClock g x.length := by
  constructor
  · rintro ⟨fuel,h⟩
    exact (result_iff g x e m r E).mp (runs_of_drive fuel _ _ h).1
  · intro h
    exact drive_of_runs ((result_iff g x e m r E).mpr h) rfl

def taskCaptures (task : Task) : CaptureEnv :=
  SequentialSharedSpace.taskCaptures (inflateTask 0 task)

def frameCaptures : Frame → CaptureEnv
  | .argCons span => [span]
  | .scope E => E
  | _ => []

def retainedCaptures (c : Config) : CaptureEnv :=
  taskCaptures c.task ++ c.env ++ c.stack.flatMap frameCaptures

theorem inflateStack_captures (m : Nat) (K : List Frame) :
    (inflateStack m K).flatMap SequentialSharedSpace.frameCaptures =
      K.flatMap frameCaptures := by
  induction K generalizing m with
  | nil => rfl
  | cons f K ih =>
    cases f <;> simp only [inflateStack, List.flatMap_cons,
      SequentialSharedSpace.frameCaptures, frameCaptures, ih]

theorem inflate_captures (c : Config) :
    SequentialSharedSpace.retainedCaptures (inflate c) = retainedCaptures c := by
  obtain ⟨m,t,E,K⟩ := c
  have ht : SequentialSharedSpace.taskCaptures (inflateTask m t) = taskCaptures t := by
    cases t <;> rfl
  simp only [SequentialSharedSpace.retainedCaptures, inflate, retainedCaptures,
    inflateStack_captures, ht]

theorem reachable_captured_characters (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    ((SequentialSpanRecompute.decodeEnv x (retainedCaptures c)).map List.length).sum ≤
      x.length := by
  have ho := SequentialSharedSpace.reachable_captured_characters g x e (inflate c)
    (runs_inflate h)
  simpa only [inflate_captures] using ho

end Shallot.MacroPeg.CBV.SequentialSharedClock
