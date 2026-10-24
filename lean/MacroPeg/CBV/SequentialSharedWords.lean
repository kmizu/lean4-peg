import MacroPeg.CBV.SequentialSharedPayload

/-! An executable Seq machine whose retained captures are actual words.
It has one current environment and one shared query clock; continuation
frames retain no capture origins. Decoding valid span configurations commutes
with its transitions on the same original input. -/
namespace Shallot.MacroPeg.CBV.SequentialSharedWords

open Shallot (beqChar leChar stripPrefix?)
abbrev CaptureEnv := List (List Char)
abbrev ArgsResult := Option (Option (CaptureEnv × Nat))

inductive Value where
  | expr (result : Res)
  | args (result : ArgsResult)
  deriving DecidableEq, Repr

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
  | argCons (word : List Char)
  | call (rule : Nat)
  | scope (saved : CaptureEnv)

structure Config where
  clock : Nat
  task : Task
  env : CaptureEnv
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
    | some w =>
      match stripPrefix? w (sfx x p) with
      | some rest => some (some rest.length)
      | none => some none
    | none => some none
  | .invoke _ _ _, _ => none
  | _, _ => some none

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
    | some (some q) => some ⟨m, .args args q, E, .argCons (pre x p q) :: K⟩
  | ⟨m, .value (.args result), E, .argCons word :: K⟩ =>
    some ⟨m, .value (.args (match result with
      | some (some (W, q)) => some (some (word :: W, q))
      | result => result)), E, K⟩
  | ⟨m, .value (.args result), E, .call i :: K⟩ =>
    match result with
    | none => some ⟨m, .value (.expr none), E, K⟩
    | some none => some ⟨m, .value (.expr (some none)), E, K⟩
    | some (some (W, q)) => some ⟨m, .query i W q, E, K⟩
  | ⟨m, .value v, _, .scope E :: K⟩ => some ⟨m + 1, .value v, E, K⟩
  | _ => none



def decodeValue (x : List Char) : SequentialSharedClock.Value → Value
  | .expr r => .expr r
  | .args r => .args (SequentialSpanRecompute.decodeArgs x r)

def decodeTask (x : List Char) : SequentialSharedClock.Task → Task
  | .expr e p => .expr e p
  | .args es p => .args es p
  | .query i W p => .query i (SequentialSpanRecompute.decodeEnv x W) p
  | .value v => .value (decodeValue x v)

def decodeFrame (x : List Char) : SequentialSharedClock.Frame → Frame
  | .seq b => .seq b
  | .alt b p => .alt b p
  | .notP p => .notP p
  | .star a p => .star a p
  | .argHead es p => .argHead es p
  | .argCons span => .argCons (pre x span.1 span.2)
  | .call i => .call i
  | .scope E => .scope (SequentialSpanRecompute.decodeEnv x E)

def decode (x : List Char) (c : SequentialSharedClock.Config) : Config :=
  ⟨c.clock,decodeTask x c.task,SequentialSpanRecompute.decodeEnv x c.env,
    c.stack.map (decodeFrame x)⟩

theorem atom_decode (x : List Char) (E : SequentialSharedClock.CaptureEnv)
    (hE : SequentialSpanRecompute.ValidEnv x.length E) (e : MExp) (p : Nat) :
    SequentialSharedClock.atom x E e p = atom x (SequentialSpanRecompute.decodeEnv x E) e p := by
  cases e <;> try rfl
  rename_i k
  cases hs : E[k]? with
  | none => simp [SequentialSharedClock.atom,SequentialStack.atom,atom,
      SequentialSpanRecompute.decodeEnv,hs]
  | some span =>
    obtain ⟨a,b⟩ := span
    have ha := (hE (a,b) (List.mem_of_getElem? hs)).2
    simp only [SequentialSharedClock.atom,SequentialStack.atom,atom,
      SequentialSpanRecompute.decodeEnv,List.getElem?_map,hs,Option.map_some]
    rw [SequentialSpanRecompute.matchSpan_eq x a b p ha]
    cases stripPrefix? (pre x a b) (sfx x p) <;> rfl

/-- All non-parameter transitions commute without validity hypotheses;
validity is used only to match a span parameter against its decoded word. -/
theorem step_commutes (g : MGrammar) (x : List Char) (c : SequentialSharedClock.Config)
    (hE : SequentialSpanRecompute.ValidEnv x.length c.env) :
    (SequentialSharedClock.step g x c).map (decode x) = step g x (decode x c) := by
  obtain ⟨m,t,E,K⟩ := c
  cases t with
  | expr e p =>
    cases e <;> try rfl
    case param k =>
      simp only [SequentialSharedClock.step,decode,decodeTask,step]
      rw [atom_decode x E hE]
      rfl
    case call i args =>
      cases hr : ruleAtM g.rules i with
      | none => simp [SequentialSharedClock.step,decode,decodeTask,step,decodeValue,hr]
      | some rule =>
        by_cases ha : rule.arity = args.length <;>
          simp [SequentialSharedClock.step,decode,decodeTask,decodeFrame,step,decodeValue,hr,ha]
  | args es p =>
    cases es <;> rfl
  | query i W p =>
    cases m with
    | zero => rfl
    | succ m =>
      by_cases hp : p ≤ x.length
      · cases hr : ruleAtM g.rules i <;>
          simp [SequentialSharedClock.step,decode,decodeTask,decodeFrame,step,decodeValue,hp,hr]
      · simp [SequentialSharedClock.step,decode,decodeTask,step,decodeValue,hp]
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
          | simp only [SequentialSharedClock.step,decode,decodeTask,decodeFrame,decodeValue,
              step,List.map_cons,SequentialSpanRecompute.decodeEnv,Option.map_some,
              SequentialSpanRecompute.decode_capture] <;>
              first | rfl | split <;> rfl

inductive Runs (g : MGrammar) (x : List Char) : Config → Config → Prop where
  | refl (c) : Runs g x c c
  | cons {a b c} (h : step g x a = some b) (tail : Runs g x b c) : Runs g x a c

def initial (g : MGrammar) (x : List Char) (e : MExp) : Config :=
  ⟨SequentialClock.positionClock g x.length,.expr e x.length,[],[]⟩

theorem decode_initial (g : MGrammar) (x : List Char) (e : MExp) :
    decode x (SequentialSharedClock.initial g x e) = initial g x e := rfl

/-- Every span execution from the real initial state decodes to a word
execution, with no assumption of a word-machine semantic oracle. -/
theorem runs_decode (g : MGrammar) (x : List Char) (e : MExp)
    (c : SequentialSharedClock.Config) (h : SequentialSharedClock.Runs g x
      (SequentialSharedClock.initial g x e) c) : Runs g x (initial g x e) (decode x c) := by
  have aux : ∀ a b, SequentialSharedClock.Runs g x a b →
      SequentialSharedClock.Runs g x (SequentialSharedClock.initial g x e) a →
      Runs g x (decode x a) (decode x b) := by
    intro a b hab
    induction hab with
    | refl => exact fun _ => .refl _
    | cons hs ht ih =>
      intro ha
      have hE := (SequentialSharedPayload.reachable_envs_ok g x e _ ha).1.1
      have hc := step_commutes g x _ hE
      rw [hs] at hc
      exact .cons hc.symm (ih (ha.trans (.cons hs (.refl _))))
  exact aux _ _ h (.refl _)

/-- A word step from a decoded reachable state has a matching actual span
step. This also rules out additional word-only executions from the initial state. -/
theorem lift_step (g : MGrammar) (x : List Char) (e : MExp)
    {c : SequentialSharedClock.Config} {next : Config}
    (h : SequentialSharedClock.Runs g x (SequentialSharedClock.initial g x e) c)
    (hs : step g x (decode x c) = some next) :
    ∃ d, SequentialSharedClock.step g x c = some d ∧ decode x d = next := by
  have hc := step_commutes g x c (SequentialSharedPayload.reachable_envs_ok g x e c h).1.1
  rw [hs] at hc
  cases hd : SequentialSharedClock.step g x c with
  | none => simp [hd] at hc
  | some d => exact ⟨d,rfl,by simpa only [hd,Option.map_some,Option.some.injEq] using hc⟩

theorem runs_lift (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    ∃ d, SequentialSharedClock.Runs g x (SequentialSharedClock.initial g x e) d ∧
      decode x d = c := by
  have aux : ∀ a b, Runs g x a b → ∀ d,
      SequentialSharedClock.Runs g x (SequentialSharedClock.initial g x e) d →
      decode x d = a → ∃ f, SequentialSharedClock.Runs g x
        (SequentialSharedClock.initial g x e) f ∧ decode x f = b := by
    intro a b hab
    induction hab with
    | refl => exact fun d hd ha => ⟨d,hd,ha⟩
    | cons hs ht ih =>
      intro d hd ha
      rw [← ha] at hs
      obtain ⟨f,hf,he⟩ := lift_step g x e hd hs
      exact ih f (hd.trans (.cons hf (.refl _))) he
  exact aux _ _ h _ (.refl _) rfl

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

theorem initial_runs (g : MGrammar) (x : List Char) (e : MExp) :
    Runs g x (initial g x e)
      ⟨SequentialClock.positionClock g x.length,
        .value (.expr (SequentialSpanRecompute.run g x e)),[],[]⟩ := by
  exact runs_decode g x e _ (SequentialSharedClock.initial_runs g x e)

theorem result_iff (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (r : Res)
    (E : CaptureEnv) :
    Runs g x (initial g x e) ⟨m,.value (.expr r),E,[]⟩ ↔
      r = SequentialSpanRecompute.run g x e ∧ E = [] ∧
        m = SequentialClock.positionClock g x.length := by
  constructor
  · intro h
    have he := terminal_unique h (initial_runs g x e) rfl rfl
    cases he
    exact ⟨rfl,rfl,rfl⟩
  · rintro ⟨rfl,rfl,rfl⟩
    exact initial_runs g x e

theorem original_result_iff (g : MGrammar) (x : List Char) (e : MExp) (r : Res) :
    Runs g x (initial g x e)
      ⟨SequentialClock.positionClock g x.length,.value (.expr r),[],[]⟩ ↔
      SequentialStack.Runs g x (SequentialStack.initial g x e) ⟨.value (.expr r),[]⟩ := by
  simp only [result_iff,SequentialStack.result_iff,eq_self,and_self,and_true]

theorem accepts_iff {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (x : List Char) :
    Runs g x (initial g x e)
      ⟨SequentialClock.positionClock g x.length,.value (.expr (some (some 0))),[],[]⟩ ↔
      SObs g .callByValueSeq e x (some []) := by
  rw [original_result_iff]
  exact SequentialStack.accepts_iff hg he x

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


end Shallot.MacroPeg.CBV.SequentialSharedWords
