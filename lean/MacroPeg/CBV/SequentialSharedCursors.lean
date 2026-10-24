import MacroPeg.CBV.SequentialCursorChain

/-! The actual word machine's current and saved input cursors form one
increasing list from the top of the stack towards its bottom. Difference
encoding therefore uses linear bits, even when many cursors are equal. -/
namespace Shallot.MacroPeg.CBV.SequentialSharedCursors
open SequentialCursorChain (Chain)
open SequentialSharedWords (Config Runs initial)
open SequentialCaptureRegions (Kind)

private def sharedTaskCursor : SequentialSharedStack.Task → Option Nat
  | .expr _ _ p | .args _ _ p | .query _ _ _ p => some p
  | .value (.expr (some (some p))) => some p
  | .value (.args (some (some (_,p)))) => some p
  | _ => none

private def sharedFrameCursor : SequentialSharedStack.Frame → Option Nat
  | .alt _ _ p | .notP p | .star _ _ p | .argHead _ _ p => some p
  | _ => none

private def sharedPositions (c : SequentialSharedStack.Config) : List Nat :=
  (sharedTaskCursor c.task).toList ++ c.stack.filterMap sharedFrameCursor

def taskCursor : SequentialSharedWords.Task → Option Nat
  | .expr _ p | .args _ p | .query _ _ p => some p
  | .value (.expr (some (some p))) => some p
  | .value (.args (some (some (_,p)))) => some p
  | _ => none

def frameCursor : SequentialSharedWords.Frame → Option Nat
  | .alt _ p | .notP p | .star _ p | .argHead _ p => some p
  | _ => none

/-- Includes the current successful result cursor, if present, and every
saved input position; capture-origin endpoints no longer exist in this machine. -/
def positions (c : Config) : List Nat :=
  (taskCursor c.task).toList ++ c.stack.filterMap frameCursor

private theorem task_cursor_bound {t : SequentialSharedStack.Task} {kind : Kind}
    (h : SequentialSharedSpace.ScopedTask t kind) :
    ∀ p, sharedTaskCursor t = some p → p ≤ kind.bound := by
  cases h with
  | expr hp => intro p he; cases he; exact hp
  | args => intro p he; cases he; exact Nat.le_refl _
  | query hp => intro p he; cases he; simp only [Kind.bound]; omega
  | value hv =>
    cases hv with
    | @expr p r hr =>
      cases r with
      | none => intro q he; cases he
      | some result => cases result with
        | none => intro q he; cases he
        | some q => intro j he; cases he; exact hr q rfl
    | @args p r hr =>
      cases r with
      | none => intro q he; cases he
      | some result => cases result with
        | none => intro q he; cases he
        | some Wq =>
          obtain ⟨W,q⟩ := Wq
          intro j he
          cases he
          exact (hr W q rfl).descending

private theorem frame_bound {f : SequentialSharedStack.Frame}
    {E E' : SequentialSharedStack.CaptureEnv} {kind out : Kind}
    (h : SequentialSharedSpace.ScopedFrame f E kind E' out) : kind.bound ≤ out.bound := by
  cases h <;> simp only [Kind.bound] at * <;> omega

private theorem frame_cursor_eq {f : SequentialSharedStack.Frame}
    {E E' : SequentialSharedStack.CaptureEnv} {kind out : Kind}
    (h : SequentialSharedSpace.ScopedFrame f E kind E' out) (p : Nat)
    (hp : sharedFrameCursor f = some p) : p = kind.bound := by
  cases h <;> simp_all [sharedFrameCursor,Kind.bound]

private theorem stack_chain {E : SequentialSharedStack.CaptureEnv} {kind : Kind}
    {K : List SequentialSharedStack.Frame} {n : Nat}
    (h : SequentialSharedSpace.ScopedStack E kind K n) :
    Chain kind.bound (K.filterMap sharedFrameCursor) n := by
  induction h with
  | nil hp => exact .nil (by omega)
  | @cons E E' k out n f K hf ht ih =>
    have hb := frame_bound hf
    cases hc : sharedFrameCursor f with
    | none => simpa only [List.filterMap_cons,hc] using ih.lower hb
    | some p =>
      have hp := frame_cursor_eq hf p hc
      subst p
      simpa only [List.filterMap_cons,hc] using Chain.cons (Nat.le_refl _) (ih.lower hb)

private theorem scoped_positions {n : Nat} {c : SequentialSharedStack.Config}
    (h : SequentialSharedSpace.Scoped n c) : Chain 0 (sharedPositions c) n := by
  obtain ⟨kind,ht,hK⟩ := h
  have hc := stack_chain hK
  cases hp : sharedTaskCursor c.task with
  | none => simpa only [sharedPositions,hp,Option.toList_none,List.nil_append] using
      hc.lower (Nat.zero_le _)
  | some p =>
    have hb := task_cursor_bound ht p hp
    simpa only [sharedPositions,hp,Option.toList_some,List.singleton_append] using
      Chain.cons (Nat.zero_le p) (hc.lower hb)

private theorem task_transfer (x : List Char) (m : Nat) (t : SequentialSharedClock.Task) :
    sharedTaskCursor (SequentialSharedClock.inflateTask m t) =
      taskCursor (SequentialSharedWords.decodeTask x t) := by
  cases t with
  | expr _ _ | args _ _ | query _ _ _ => rfl
  | value v =>
    cases v with
    | expr r => cases r with
      | none => rfl
      | some result => cases result <;> rfl
    | args r => cases r with
      | none => rfl
      | some result => cases result <;> rfl

private theorem stack_transfer (x : List Char) (m : Nat) (K : List SequentialSharedClock.Frame) :
    (SequentialSharedClock.inflateStack m K).filterMap sharedFrameCursor =
      (K.map (SequentialSharedWords.decodeFrame x)).filterMap frameCursor := by
  induction K generalizing m with
  | nil => rfl
  | cons f K ih =>
    cases f <;> simp only [SequentialSharedClock.inflateStack,SequentialSharedWords.decodeFrame,
      List.map_cons,List.filterMap_cons,sharedFrameCursor,frameCursor,ih]

private theorem positions_transfer (x : List Char) (c : SequentialSharedClock.Config) :
    sharedPositions (SequentialSharedClock.inflate c) = positions (SequentialSharedWords.decode x c) := by
  simp only [sharedPositions,SequentialSharedClock.inflate,positions,SequentialSharedWords.decode]
  rw [task_transfer x c.clock c.task,stack_transfer x c.clock c.stack]

/-- Current-to-saved cursors are nondecreasing and bounded by original input
length at every actual reachable word-machine state, including failures. -/
theorem reachable_chain (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) : Chain 0 (positions c) x.length := by
  obtain ⟨d,hd,rfl⟩ := SequentialSharedWords.runs_lift g x e c h
  have hs := SequentialSharedSpace.reachable_scoped g x e (SequentialSharedClock.inflate d)
    (SequentialSharedClock.runs_inflate hd)
  rw [← positions_transfer x d]
  exact scoped_positions hs

theorem positions_length (c : Config) : (positions c).length ≤ c.stack.length + 1 := by
  have aux : ∀ K : List SequentialSharedWords.Frame, (K.filterMap frameCursor).length ≤ K.length := by
    intro K
    induction K with
    | nil => exact Nat.le_refl _
    | cons f K ih => cases hp : frameCursor f <;> simp only [List.filterMap_cons,hp,List.length_cons] <;> omega
  have hK := aux c.stack
  have ht : (taskCursor c.task).toList.length ≤ 1 := by cases taskCursor c.task <;> simp
  simp only [positions,List.length_append]
  omega

/-- The stream is executable and has a verified inverse; the lower bound
zero is fixed and is not extra input-sized metadata. -/
theorem cursor_stream_correct (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    SequentialCursorChain.decode (SequentialCursorChain.encode (positions c)) = some (positions c) :=
  (reachable_chain g x e c h).decode_encode

theorem reachable_cursor_bits (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    (SequentialCursorChain.encode (positions c)).length ≤ x.length + c.stack.length + 1 := by
  have hb := (reachable_chain g x e c h).encode_length
  have hl := positions_length c
  omega

theorem cursor_bits_linear (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    (SequentialCursorChain.encode (positions c)).length ≤ x.length +
      (((g.rules.length + 1) * (SequentialStackRank.codeBudget g + 1)) *
        (x.length + 1) + sizeOf e) + 1 := by
  have hb := reachable_cursor_bits g x e c h
  have hs := SequentialSharedWordSpace.stack_linear_bound g x e c h
  omega

end Shallot.MacroPeg.CBV.SequentialSharedCursors
