import MacroPeg.CBV.SequentialWordCycle

/-! All Seq transitions are local to the task and the top continuation frame.
The remaining continuation can stay encoded throughout a transition. -/

namespace Shallot.MacroPeg.CBV.SequentialFront

open SequentialStack SequentialStackCodec SequentialStackCodecBound
open CBVtoCBN

def front (c : Config) : Config := ⟨c.task, c.stack.take 1⟩
def tail (c : Config) : List Frame := c.stack.drop 1
def attach (K : List Frame) (c : Config) : Config := ⟨c.task, c.stack ++ K⟩

theorem step_cons (g : MGrammar) (x : List Char) (task : Task) (f : Frame) (K : List Frame) :
    step g x ⟨task, f :: K⟩ = (step g x ⟨task, [f]⟩).map (attach K) := by
  cases task with
  | expr m E e p =>
    cases e with
    | call i es =>
      simp only [step]
      split
      · split <;> rfl
      · rfl
    | eps | any | chr _ | range _ _ | lit _ | param _ | dbg _ | lam _ _
      | invoke _ _ _ | callParam _ _ | seq _ _ | alt _ _ | notP _ | star _ => rfl
  | args m E es p => cases es <;> rfl
  | query m i E p =>
    cases m with
    | zero => rfl
    | succ m =>
      simp only [step]
      split
      · split <;> rfl
      · rfl
  | value v =>
    cases v with
    | expr r =>
      cases r with
      | none => cases f <;> rfl
      | some r =>
        cases r with
        | none => cases f <;> rfl
        | some q =>
          cases f <;> simp only [step]
          all_goals first | rfl | split <;> rfl
    | args r =>
      cases r with
      | none => cases f <;> rfl
      | some r =>
        cases r with
        | none => cases f <;> rfl
        | some Wp => cases Wp; cases f <;> rfl

/-- Exact one-step factoring, including undefined/mismatched terminal states. -/
theorem step_front (g : MGrammar) (x : List Char) (c : Config) :
    step g x c = (step g x (front c)).map (attach (tail c)) := by
  obtain ⟨task, K⟩ := c
  cases K with
  | nil =>
    change step g x ⟨task, []⟩ = (step g x ⟨task, []⟩).map (attach [])
    cases hh : step g x ⟨task, []⟩ with
    | none => rfl
    | some c => cases c; simp [attach]
  | cons f K => exact step_cons g x task f K

theorem step_front_iff (g : MGrammar) (x : List Char) (c next : Config) :
    step g x c = some next ↔
      ∃ localNext, step g x (front c) = some localNext ∧ next = attach (tail c) localNext := by
  rw [step_front]
  cases hh : step g x (front c) <;> simp [eq_comm]

theorem step_stack_length (g : MGrammar) (x : List Char) (c next : Config)
    (hs : step g x c = some next) : next.stack.length ≤ c.stack.length + 1 := by
  obtain ⟨task, K⟩ := c
  cases task with
  | expr m E e p =>
    cases e <;> simp only [step] at hs
    all_goals repeat' first | split at hs | (cases hs <;> simp <;> omega)
  | args m E es p =>
    cases es <;> simp only [step] at hs <;> cases hs <;> simp
  | query m i E p =>
    cases m <;> simp only [step] at hs
    all_goals repeat' first | split at hs | (cases hs <;> simp <;> omega)
  | value v =>
    cases K with
    | nil => simp [step] at hs
    | cons f K =>
      cases v <;> cases f <;> simp only [step] at hs
      all_goals repeat' first | split at hs | (cases hs <;> simp <;> omega)

theorem local_stack_length (g : MGrammar) (x : List Char) (c localNext : Config)
    (hs : step g x (front c) = some localNext) : localNext.stack.length ≤ 2 := by
  have hh := step_stack_length g x (front c) localNext hs
  have hl : (front c).stack.length ≤ 1 := by simp [front]; omega
  omega

/-- The unchanged suffix has no length header of its own: only the front's
header counts it. Hence the suffix's actual bytes can be copied verbatim. -/
def suffixCode (ns : List CompileNode) (K : List Frame) : List Nat := K.flatMap (writeFrame ns)

def prefixCode (ns : List CompileNode) (K : List Frame) (c : Config) : List Nat :=
  writeTask ns c.task ++ (c.stack.length + K.length) :: suffixCode ns c.stack

theorem encode_attach (ns : List CompileNode) (K : List Frame) (c : Config) :
    encode ns (attach K c) = prefixCode ns K c ++ suffixCode ns K := by
  simp [encode, attach, prefixCode, suffixCode, writeList, List.flatMap_append, List.append_assoc]

theorem attach_front (c : Config) : attach (tail c) (front c) = c := by
  obtain ⟨task, K⟩ := c
  change Config.mk task (K.take 1 ++ K.drop 1) = Config.mk task K
  rw [List.take_append_drop]

theorem encode_front (ns : List CompileNode) (c : Config) :
    encode ns c = prefixCode ns (tail c) (front c) ++ suffixCode ns (tail c) := by
  rw [← encode_attach, attach_front]

/-- Every successful original-machine step rewrites only this finite front
and the total-stack-length header; the encoded continuation tail is identical. -/
theorem encoded_step (g : MGrammar) (x : List Char) (ns : List CompileNode) (c next : Config)
    (hs : step g x c = some next) :
    ∃ localNext,
      step g x (front c) = some localNext ∧
      encode ns next = prefixCode ns (tail c) localNext ++ suffixCode ns (tail c) := by
  obtain ⟨localNext, hh, rfl⟩ := (step_front_iff g x c next).mp hs
  exact ⟨localNext, hh, encode_attach ns (tail c) localNext⟩

theorem prefix_length (ns : List CompileNode) (K : List Frame) (c : Config) (B k : Nat)
    (ht : (writeTask ns c.task).length ≤ B)
    (hf : ∀ f ∈ c.stack, (writeFrame ns f).length ≤ B) (hk : c.stack.length ≤ k) :
    (prefixCode ns K c).length ≤ (k + 1) * B + 1 := by
  have hh := sum_le_length_mul (fun f => (writeFrame ns f).length) B c.stack hf
  have hm := Nat.mul_le_mul_right B hk
  simp only [prefixCode, suffixCode, List.length_append, List.length_cons,
    List.length_flatMap]
  rw [Nat.add_mul, Nat.one_mul]
  omega

open SequentialStackPayload

/-- The front to decode contains a source-dependent constant number of natural
fields, even if the continuation has linearly many frames. -/
theorem reachable_prefix_length (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    (prefixCode (compilerNodes g e) (tail c) (front c)).length ≤ 13 + 6 * arityBudget g := by
  obtain ⟨kind, ht, hK⟩ := reachable_typed g x e c h
  have hs := frames_length (compilerNodes g e) hK
  have hf : ∀ f ∈ (front c).stack,
      (writeFrame (compilerNodes g e) f).length ≤ 6 + 3 * arityBudget g := by
    intro f hm
    exact hs f (List.mem_of_mem_take hm)
  have hh := prefix_length (compilerNodes g e) (tail c) (front c) (6 + 3 * arityBudget g) 1
    (task_length _ ht) hf (by simp [front]; omega)
  omega

/-- The output front contains at most two frames and a bounded number of
fields. This covers every transition, including call arguments and returns. -/
theorem reachable_step_prefix (g : MGrammar) (x : List Char) (e : MExp) (c next : Config)
    (h : Runs g x (initial g x e) c) (hs : step g x c = some next) :
    ∃ localNext,
      step g x (front c) = some localNext ∧
      encode (compilerNodes g e) next =
        prefixCode (compilerNodes g e) (tail c) localNext ++ suffixCode (compilerNodes g e) (tail c) ∧
      localNext.stack.length ≤ 2 ∧
      (prefixCode (compilerNodes g e) (tail c) localNext).length ≤ 19 + 9 * arityBudget g := by
  obtain ⟨localNext, hh, he⟩ := (step_front_iff g x c next).mp hs
  have hn := h.trans (Runs.single hs)
  obtain ⟨kind, ht, hK⟩ := reachable_typed g x e next hn
  have hframes := frames_length (compilerNodes g e) hK
  have htask : (writeTask (compilerNodes g e) localNext.task).length ≤ 6 + 3 * arityBudget g := by
    simpa only [he, attach] using task_length (compilerNodes g e) ht
  have hfs : ∀ f ∈ localNext.stack,
      (writeFrame (compilerNodes g e) f).length ≤ 6 + 3 * arityBudget g := by
    intro f hf
    exact hframes f (by simp [he, attach, hf])
  have hl := local_stack_length g x c localNext hh
  have hp := prefix_length (compilerNodes g e) (tail c) localNext (6 + 3 * arityBudget g) 2 htask hfs hl
  refine ⟨localNext, hh, ?_, hl, by omega⟩
  rw [he, encode_attach]

end Shallot.MacroPeg.CBV.SequentialFront
