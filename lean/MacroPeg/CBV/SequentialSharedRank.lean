import MacroPeg.CBV.SequentialSharedClock
import MacroPeg.CBV.SequentialStackRank

/-! Transfer the original linear stack bound to the evaluator with one
current environment and one clock. Erasing environment-restoration scopes
simulates every transition by one old transition or a stuttering step. -/
namespace Shallot.MacroPeg.CBV.SequentialSharedRank
open SequentialSharedClock

def eraseValue : SequentialSharedClock.Value → SequentialStack.Value
  | .expr r => .expr r
  | .args r => .args r

def eraseTask (m : Nat) (E : CaptureEnv) : Task → SequentialStack.Task
  | .expr e p => .expr m E e p
  | .args es p => .args m E es p
  | .query i W p => .query m i W p
  | .value v => .value (eraseValue v)

/-- Restore the old frames' lexical environments as well as their clocks.
Scope frames are administrative and disappear from the original machine. -/
def eraseStack (m : Nat) (E : CaptureEnv) : List Frame → List SequentialStack.Frame
  | [] => []
  | .seq b :: K => .seq m E b :: eraseStack m E K
  | .alt b p :: K => .alt m E b p :: eraseStack m E K
  | .notP p :: K => .notP p :: eraseStack m E K
  | .star a p :: K => .star m E a p :: eraseStack m E K
  | .argHead es p :: K => .argHead m E es p :: eraseStack m E K
  | .argCons span :: K => .argCons span :: eraseStack m E K
  | .call i :: K => .call m i :: eraseStack m E K
  | .scope W :: K => eraseStack (m + 1) W K

def erase (c : Config) : SequentialStack.Config :=
  ⟨eraseTask c.clock c.env c.task, eraseStack c.clock c.env c.stack⟩

/-- The simulation includes all intermediate states, rather than only
agreement of terminal results. Scope restoration is its only stuttering case. -/
theorem step_erases (g : MGrammar) (x : List Char) {c next : Config}
    (hs : step g x c = some next) : SequentialStack.Runs g x (erase c) (erase next) := by
  obtain ⟨m,t,E,K⟩ := c
  cases t with
  | expr e p =>
    cases e <;> try (cases hs <;> exact .single rfl)
    rename_i i args
    cases hr : ruleAtM g.rules i with
    | none =>
      simp only [step,hr] at hs
      cases hs
      apply SequentialStack.Runs.single
      simp [erase,eraseTask,SequentialStack.step,hr,eraseValue]
    | some rule =>
      by_cases ha : rule.arity = args.length <;>
        simp only [step,hr,ha,if_pos] at hs <;> cases hs <;>
        apply SequentialStack.Runs.single <;>
        simp [erase,eraseTask,eraseStack,SequentialStack.step,hr,ha,eraseValue]
  | args es p => cases es <;> cases hs <;> exact .single rfl
  | query i W p =>
    cases m with
    | zero => cases hs; exact .single rfl
    | succ m =>
      by_cases hp : p ≤ x.length
      · cases hr : ruleAtM g.rules i <;>
          simp only [step,hp,if_pos,hr] at hs <;> cases hs <;>
          apply SequentialStack.Runs.single <;>
          simp [erase,eraseTask,eraseStack,SequentialStack.step,hp,hr,eraseValue]
      · simp only [step,hp] at hs
        cases hs
        apply SequentialStack.Runs.single
        simp [erase,eraseTask,SequentialStack.step,hp,eraseValue]
  | value v =>
    cases K with
    | nil => cases v <;> cases hs
    | cons f K =>
      cases f <;> cases v <;>
        try (cases hs <;> first | exact .single rfl | exact .refl _)
      all_goals rename_i r; cases r with
      | none => cases hs <;> exact .single rfl
      | some result =>
        cases result with
        | none => cases hs <;> exact .single rfl
        | some val =>
          first
          | cases hs <;> exact .single rfl
          | simp only [step] at hs
            split at hs <;> cases hs <;>
              apply SequentialStack.Runs.single <;>
              simp_all [erase,eraseTask,eraseStack,eraseValue,SequentialStack.step]

theorem runs_erase {g : MGrammar} {x : List Char} {a b : Config}
    (h : Runs g x a b) : SequentialStack.Runs g x (erase a) (erase b) := by
  induction h with
  | refl => exact .refl _
  | cons hs ht ih => exact (step_erases g x hs).trans ih

theorem erase_initial (g : MGrammar) (x : List Char) (e : MExp) :
    erase (initial g x e) = SequentialStack.initial g x e := rfl

/-- Exact frame accounting: erasure drops one record for each active scope
and keeps every structural, call, and pending-argument continuation. -/
theorem eraseStack_length (m : Nat) (E : CaptureEnv) (K : List Frame) :
    (eraseStack m E K).length + scopeCount K = K.length := by
  induction K generalizing m E with
  | nil => rfl
  | cons f K ih =>
    cases f <;> simp only [eraseStack,scopeCount,List.length_cons]
    all_goals first
    | have hh := ih m E; omega
    | rename_i W; have hh := ih (m + 1) W; omega

/-- All records are counted, including scopes and continuations with zero
captured-character payload. -/
theorem reachable_stack_bound (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    c.stack.length ≤ SequentialStackRank.initialCap g x e +
      SequentialClock.positionClock g x.length := by
  have ho := runs_erase h
  have hb := SequentialStackRank.reachable_stack_bound g x e (erase c) ho
  have hc := reachable_clock_mass g x e c h
  have hl := eraseStack_length c.clock c.env c.stack
  change (eraseStack c.clock c.env c.stack).length ≤ _ at hb
  omega

theorem stack_linear_bound (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    c.stack.length ≤ ((g.rules.length + 1) * (SequentialStackRank.codeBudget g + 1)) *
      (x.length + 1) + sizeOf e := by
  have hb := reachable_stack_bound g x e c h
  simpa only [SequentialStackRank.initialCap, SequentialClock.positionClock,
    Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.mul_right_comm, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using hb

end Shallot.MacroPeg.CBV.SequentialSharedRank
