import MacroPeg.CBV.SequentialSharedRank
import MacroPeg.CBV.SequentialStackPayload

/-! Bounds on all retained capture records, including empty words. Scope
records keep environments that the original machine may already have dropped,
so their bounds are maintained explicitly rather than inferred from erasure. -/
namespace Shallot.MacroPeg.CBV.SequentialSharedPayload
open SequentialSharedClock SequentialSharedRank
open SequentialStackPayload (EnvOK arityBudget empty_env)

def scopeEnvs : List Frame → List CaptureEnv
  | [] => []
  | .scope E :: K => E :: scopeEnvs K
  | _ :: K => scopeEnvs K

def EnvsOK (n A : Nat) (c : Config) : Prop :=
  EnvOK n A c.env ∧ ∀ W ∈ scopeEnvs c.stack, EnvOK n A W

theorem push_scope {n A m p : Nat} {E W : CaptureEnv} {e : MExp} {K : List Frame}
    (h : EnvOK n A E ∧ ∀ V ∈ scopeEnvs K, EnvOK n A V) (hW : EnvOK n A W) :
    EnvsOK n A ⟨m,.expr e p,W,.scope E :: K⟩ := by
  refine ⟨hW,?_⟩
  intro V hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact h.1
  · exact h.2 V hv

theorem pop_scope {n A : Nat} {E W : CaptureEnv} {K : List Frame}
    (h : EnvOK n A W ∧ ∀ V ∈ E :: scopeEnvs K, EnvOK n A V) :
    EnvOK n A E ∧ ∀ V ∈ scopeEnvs K, EnvOK n A V := by
  exact ⟨h.2 E (List.mem_cons_self),fun V hv => h.2 V (List.mem_cons_of_mem E hv)⟩

theorem step_envs_ok (g : MGrammar) (x : List Char) (n A : Nat) {c next : Config}
    (h : EnvsOK n A c)
    (hq : ∀ i W p, c.task = .query i W p → EnvOK n A W)
    (hs : step g x c = some next) : EnvsOK n A next := by
  obtain ⟨m,t,E,K⟩ := c
  cases t with
  | expr e p =>
    cases e <;> try (cases hs <;> simpa only [EnvsOK,scopeEnvs] using h)
    rename_i i args
    cases hr : ruleAtM g.rules i with
    | none => simp only [step,hr] at hs; cases hs; exact h
    | some rule =>
      by_cases ha : rule.arity = args.length <;>
        simp only [step,hr,ha,if_pos] at hs <;> cases hs <;>
        simpa only [EnvsOK,scopeEnvs] using h
  | args es p =>
    cases es <;> cases hs <;> simpa only [EnvsOK,scopeEnvs] using h
  | query i W p =>
    cases m with
    | zero => cases hs; exact h
    | succ m =>
      by_cases hp : p ≤ x.length
      · cases hr : ruleAtM g.rules i with
        | none => simp only [step,hp,if_pos,hr] at hs; cases hs; exact h
        | some rule =>
          simp only [step,hp,if_pos,hr] at hs
          cases hs
          exact push_scope h (hq i W p rfl)
      · simp only [step,hp] at hs; cases hs; exact h
  | value v =>
    cases K with
    | nil => cases v <;> cases hs
    | cons f K =>
      cases f
      case scope saved =>
        cases v <;> cases hs <;> exact pop_scope h
      all_goals cases v <;> try (cases hs <;> simpa only [EnvsOK,scopeEnvs] using h)
      all_goals rename_i r; cases r with
      | none => cases hs <;> simpa only [EnvsOK,scopeEnvs] using h
      | some result =>
        cases result with
        | none => cases hs <;> simpa only [EnvsOK,scopeEnvs] using h
        | some val =>
          first
          | cases hs <;> simpa only [EnvsOK,scopeEnvs] using h
          | simp only [step] at hs
            split at hs <;> cases hs <;> simpa only [EnvsOK,scopeEnvs] using h

theorem query_env_ok (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    ∀ i W p, c.task = .query i W p → EnvOK x.length (arityBudget g) W := by
  intro i W p ht
  have ho := (SequentialStackPayload.reachable_payload_bounds g x e (erase c) (runs_erase h)).1.1
  change EnvOK _ _ (SequentialStackPayload.taskCaptures (eraseTask c.clock c.env c.task)) at ho
  rw [ht] at ho
  exact ho

theorem reachable_envs_ok (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) : EnvsOK x.length (arityBudget g) c := by
  have aux : ∀ a b, Runs g x a b → Runs g x (initial g x e) a →
      EnvsOK x.length (arityBudget g) a → EnvsOK x.length (arityBudget g) b := by
    intro a b hab
    induction hab with
    | refl => exact fun _ ha => ha
    | cons hs ht ih =>
      intro ha hE
      exact ih (ha.trans (.cons hs (.refl _)))
        (step_envs_ok g x _ _ hE (query_env_ok g x e _ ha) hs)
  apply aux _ _ h (.refl _)
  exact ⟨empty_env _ _,by intro W hw; cases hw⟩


theorem scope_mem {E : CaptureEnv} {K : List Frame}
    (h : Frame.scope E ∈ K) : E ∈ scopeEnvs K := by
  induction K with
  | nil => cases h
  | cons f K ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · exact List.mem_cons_self
    · have ht := ih hm
      cases f <;> simp only [scopeEnvs] <;>
        first | exact ht | exact List.mem_cons_of_mem _ ht

theorem argCons_mem_erase (m : Nat) (E : CaptureEnv) {span : Nat × Nat} {K : List Frame}
    (h : Frame.argCons span ∈ K) : SequentialStack.Frame.argCons span ∈ eraseStack m E K := by
  induction K generalizing m E with
  | nil => cases h
  | cons f K ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · exact List.mem_cons_self
    · cases f <;> simp only [eraseStack]
      all_goals first
      | exact List.mem_cons_of_mem _ (ih m E hm)
      | rename_i W; exact ih (m + 1) W hm

theorem reachable_task_captures (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    EnvOK x.length (arityBudget g) (taskCaptures c.task) := by
  have ho := (SequentialStackPayload.reachable_payload_bounds g x e (erase c) (runs_erase h)).1.1
  obtain ⟨m,t,E,K⟩ := c
  cases t with
  | expr _ _ | args _ _ => exact empty_env _ _
  | query _ _ _ => exact ho
  | value v =>
    cases v with
    | expr _ => exact ho
    | args r =>
      cases r with
      | none => exact ho
      | some result => cases result <;> exact ho

theorem reachable_frame_captures (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    ∀ f ∈ c.stack, EnvOK x.length (arityBudget g) (frameCaptures f) := by
  intro f hf
  cases f with
  | scope E => exact (reachable_envs_ok g x e c h).2 E (scope_mem hf)
  | argCons span =>
    have ho := (SequentialStackPayload.reachable_payload_bounds g x e (erase c) (runs_erase h)).2
    exact (ho (.argCons span) (argCons_mem_erase c.clock c.env hf)).1
  | seq _ | alt _ _ | notP _ | star _ _ | argHead _ _ | call _ => exact empty_env _ _

/-- Empty captures are included: this counts entries, not their word lengths. -/
theorem reachable_capture_records (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    (retainedCaptures c).length ≤ (c.stack.length + 2) * arityBudget g := by
  have ht := (reachable_task_captures g x e c h).2
  have he := (reachable_envs_ok g x e c h).1.2
  have hf := reachable_frame_captures g x e c h
  have hs : ∀ K : List Frame, (∀ f ∈ K, (frameCaptures f).length ≤ arityBudget g) →
      (K.flatMap frameCaptures).length ≤ K.length * arityBudget g := by
    intro K hK
    induction K with
    | nil => simp
    | cons f K ih =>
      have hh := hK f List.mem_cons_self
      have htail := ih (fun F hF => hK F (List.mem_cons_of_mem f hF))
      simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  have hK := hs c.stack (fun f hm => (hf f hm).2)
  simp only [retainedCaptures,List.length_append,Nat.succ_mul]
  omega

theorem capture_records_linear (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    (retainedCaptures c).length ≤
      ((((g.rules.length + 1) * (SequentialStackRank.codeBudget g + 1)) *
        (x.length + 1) + sizeOf e) + 2) * arityBudget g := by
  exact Nat.le_trans (reachable_capture_records g x e c h)
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (stack_linear_bound g x e c h) 2))

/-- Every retained interval lies in the original input, including environments
saved only for restoration and absent from the erased machine's stack. -/
theorem reachable_valid_captures (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    SequentialSpanRecompute.ValidEnv x.length (retainedCaptures c) := by
  intro span hs
  simp only [retainedCaptures,List.mem_append,List.mem_flatMap] at hs
  rcases hs with (ht | he) | ⟨f,hf,hspan⟩
  · exact (reachable_task_captures g x e c h).1 span ht
  · exact (reachable_envs_ok g x e c h).1.1 span he
  · exact (reachable_frame_captures g x e c h f hf).1 span hspan

end Shallot.MacroPeg.CBV.SequentialSharedPayload
