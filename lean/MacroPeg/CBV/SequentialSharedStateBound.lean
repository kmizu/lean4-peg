import MacroPeg.CBV.SequentialSharedStateCodec

/-! The whole-state representation has linear stored length. This bounds
encoded states, not the workspace of packedStep's materializing decoder. -/
namespace Shallot.MacroPeg.CBV.SequentialSharedStateBound
open SequentialSharedWords
open SequentialSharedStateCodec
open CBVtoCBN (CompileNode compilerNodes)

def TaskFits (g : MGrammar) (D : Nat) : Task → Prop
  | .args es _ => sizeOf es ≤ D
  | .query i _ _ => i < g.rules.length
  | _ => True

def FrameFits (g : MGrammar) (D : Nat) : Frame → Prop
  | .argHead es _ => sizeOf es ≤ D
  | .call i => i < g.rules.length
  | _ => True

theorem decode_task_fits (g : MGrammar) (D : Nat) (x : List Char) (m : Nat)
    (E : SequentialSharedClock.CaptureEnv) (t : SequentialSharedClock.Task)
    (h : SequentialStackCode.TaskCode g D (SequentialSharedRank.eraseTask m E t)) :
    TaskFits g D (decodeTask x t) := by
  cases t <;> first | exact h | trivial

theorem decode_stack_fits (g : MGrammar) (D : Nat) (x : List Char) (m : Nat)
    (E : SequentialSharedClock.CaptureEnv) (K : List SequentialSharedClock.Frame)
    (h : SequentialStackCode.FramesCode g D (SequentialSharedRank.eraseStack m E K)) :
    ∀ f ∈ K.map (decodeFrame x), FrameFits g D f := by
  induction K generalizing m E with
  | nil => intro f hf; cases hf
  | cons f K ih =>
    cases f
    case scope W =>
      intro F hF
      rcases List.mem_cons.mp hF with rfl | hF
      · trivial
      · exact ih (m + 1) W h _ hF
    all_goals
      have ht : SequentialStackCode.FramesCode g D
          (SequentialSharedRank.eraseStack m E K) := by
        intro F hF
        exact h F (List.mem_cons_of_mem _ hF)
      have hk := ih m E ht
      intro F hF
      rcases List.mem_cons.mp hF with rfl | hF
      · first | exact h _ List.mem_cons_self | trivial
      · exact hk _ hF

theorem reachable_fits (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    TaskFits g (SequentialStackCode.programBudget g e) c.task ∧
      ∀ f ∈ c.stack, FrameFits g (SequentialStackCode.programBudget g e) f := by
  obtain ⟨d,hd,rfl⟩ := runs_lift g x e c h
  have ho := SequentialStackCode.reachable_code g x e (SequentialSharedRank.erase d)
    (SequentialSharedRank.runs_erase hd)
  exact ⟨decode_task_fits _ _ x d.clock d.env d.task ho.1,
    decode_stack_fits _ _ x d.clock d.env d.stack ho.2⟩

def cost (code : List Nat) : Nat := code.sum + code.length

theorem cost_append (a b : List Nat) : cost (a ++ b) = cost a + cost b := by
  simp only [cost,List.sum_append,List.length_append]
  omega

theorem cost_cons (a : Nat) (tail : List Nat) : cost (a :: tail) = a + 1 + cost tail := by
  simp only [cost,List.sum_cons,List.length_cons]
  omega

theorem cost_nil : cost [] = 0 := rfl

theorem expr_cost (ns : List CompileNode) (e : MExp) :
    cost (SequentialStackCodec.writeExpr ns e) ≤ (SequentialStackPool.exprPool ns).length + 1 := by
  have hh : (SequentialStackPool.exprPool ns).idxOf e ≤ (SequentialStackPool.exprPool ns).length :=
    List.idxOf_le_length
  simp only [SequentialStackCodec.writeExpr,SequentialStackCodec.exprId,cost_cons,cost_nil]
  omega

theorem exprs_cost (ns : List CompileNode) (es : List MExp) :
    cost (SequentialStackCodec.writeExprs ns es) ≤
      es.length * ((SequentialStackPool.exprPool ns).length + 1) + es.length + 1 := by
  have aux : ∀ es : List MExp,
      cost (es.flatMap (SequentialStackCodec.writeExpr ns)) ≤
        es.length * ((SequentialStackPool.exprPool ns).length + 1) := by
    intro es
    induction es with
    | nil => simp [cost]
    | cons e es ih =>
      have he := expr_cost ns e
      simp only [List.flatMap_cons,cost_append,List.length_cons,Nat.succ_mul]
      omega
  have hh := aux es
  simp only [SequentialStackCodec.writeExprs,SequentialStackCodec.writeList,cost_cons]
  omega

theorem exprs_length_size (es : List MExp) : es.length ≤ sizeOf es := by
  induction es with
  | nil => simp
  | cons e es ih => simp only [List.length_cons,List.cons.sizeOf_spec]; omega

/-- A constant determined entirely by the grammar and syntax pool. -/
def controlBudget (ns : List CompileNode) (g : MGrammar) (D : Nat) : Nat :=
  D * ((SequentialStackPool.exprPool ns).length + 1) + D + g.rules.length +
    (SequentialStackPool.exprPool ns).length + 10

theorem task_cost (ns : List CompileNode) (g : MGrammar) (D : Nat) (t : Task)
    (h : TaskFits g D t) : cost (writeTask ns t).control ≤
      controlBudget ns g D + (SequentialSharedWordSpace.taskWords t).length := by
  cases t with
  | expr e p =>
    have he := expr_cost ns e
    simp only [writeTask,Input.append,putControl,putExpr,putCursor,cost_append,cost_cons,cost_nil,
      SequentialSharedWordSpace.taskWords,List.length_nil]
    unfold controlBudget
    omega
  | args es p =>
    have hl : es.length ≤ D := Nat.le_trans (exprs_length_size es) h
    have he := exprs_cost ns es
    have hm := Nat.mul_le_mul_right ((SequentialStackPool.exprPool ns).length + 1) hl
    simp only [writeTask,Input.append,putControl,putExprs,putCursor,cost_append,cost_cons,cost_nil,
      SequentialSharedWordSpace.taskWords,List.length_nil]
    unfold controlBudget
    omega
  | query i W p =>
    change i < g.rules.length at h
    simp only [writeTask,Input.append,putControl,putCursor,putWords,cost_append,cost_cons,cost_nil,
      SequentialSharedWordSpace.taskWords]
    unfold controlBudget
    omega
  | value v =>
    cases v with
    | expr r =>
      cases r with
      | none =>
        simp only [writeTask,Input.append,putControl,cost_append,cost_cons,cost_nil,
          SequentialSharedWordSpace.taskWords,List.length_nil]
        unfold controlBudget
        omega
      | some result =>
        cases result <;>
          simp only [writeTask,Input.append,putControl,putCursor,cost_append,cost_cons,cost_nil,
            SequentialSharedWordSpace.taskWords,List.length_nil] <;> unfold controlBudget <;> omega
    | args r =>
      cases r with
      | none =>
        simp only [writeTask,Input.append,putControl,cost_append,cost_cons,cost_nil,
          SequentialSharedWordSpace.taskWords,List.length_nil]
        unfold controlBudget
        omega
      | some result =>
        cases result with
        | none =>
          simp only [writeTask,Input.append,putControl,cost_append,cost_cons,cost_nil,
            SequentialSharedWordSpace.taskWords,List.length_nil]
          unfold controlBudget
          omega
        | some Wp =>
          obtain ⟨W,p⟩ := Wp
          simp only [writeTask,Input.append,putControl,putCursor,putWords,cost_append,cost_cons,cost_nil,
            SequentialSharedWordSpace.taskWords]
          unfold controlBudget
          omega

theorem frame_cost (ns : List CompileNode) (g : MGrammar) (D : Nat) (f : Frame)
    (h : FrameFits g D f) : cost (writeFrame ns f).control ≤
      controlBudget ns g D + (SequentialSharedWordSpace.frameWords f).length := by
  cases f with
  | seq b | alt b p | star b p =>
    have hb := expr_cost ns b
    simp only [writeFrame,Input.append,putControl,putExpr,putCursor,cost_append,cost_cons,cost_nil,
      SequentialSharedWordSpace.frameWords,List.length_nil]
    unfold controlBudget
    omega
  | notP p | argCons p =>
    simp only [writeFrame,Input.append,putControl,putCursor,putWords,cost_append,cost_cons,cost_nil,
      SequentialSharedWordSpace.frameWords,List.length_nil,List.length_cons]
    unfold controlBudget
    omega
  | argHead es p =>
    have hl : es.length ≤ D := Nat.le_trans (exprs_length_size es) h
    have he := exprs_cost ns es
    have hm := Nat.mul_le_mul_right ((SequentialStackPool.exprPool ns).length + 1) hl
    simp only [writeFrame,Input.append,putControl,putExprs,putCursor,cost_append,cost_cons,cost_nil,
      SequentialSharedWordSpace.frameWords,List.length_nil]
    unfold controlBudget
    omega
  | call i =>
    change i < g.rules.length at h
    simp only [writeFrame,Input.append,putControl,cost_append,cost_cons,cost_nil,
      SequentialSharedWordSpace.frameWords,List.length_nil]
    unfold controlBudget
    omega
  | scope E =>
    simp only [writeFrame,Input.append,putControl,putWords,cost_append,cost_cons,cost_nil,
      SequentialSharedWordSpace.frameWords]
    unfold controlBudget
    omega

theorem frames_cost (ns : List CompileNode) (g : MGrammar) (D : Nat) (K : List Frame)
    (h : ∀ f ∈ K, FrameFits g D f) : cost (writeFrames ns K).control ≤
      K.length * controlBudget ns g D + (K.flatMap SequentialSharedWordSpace.frameWords).length := by
  induction K with
  | nil => simp [writeFrames,Input.empty,cost]
  | cons f K ih =>
    have hh := frame_cost ns g D f (h f List.mem_cons_self)
    have ht := ih (fun F hF => h F (List.mem_cons_of_mem f hF))
    simp only [writeFrames,Input.append,cost_append,List.length_cons,Nat.succ_mul,
      List.flatMap_cons,List.length_append]
    omega

theorem control_cost (ns : List CompileNode) (g : MGrammar) (D : Nat) (c : Config)
    (ht : TaskFits g D c.task) (hK : ∀ f ∈ c.stack, FrameFits g D f) :
    cost (write ns c).control ≤ (c.stack.length + 1) * controlBudget ns g D +
      c.stack.length + 2 + (SequentialSharedWordSpace.retainedWords c).length := by
  have hh := task_cost ns g D c.task ht
  have hs := frames_cost ns g D c.stack hK
  simp only [write,Input.append,putControl,putWords,cost_append,cost_cons,cost_nil,
    SequentialSharedWordSpace.retainedWords,List.length_append,Nat.succ_mul]
  omega

theorem reachable_control_cost (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    cost (write (compilerNodes g e) c).control ≤
      (c.stack.length + 1) * controlBudget (compilerNodes g e) g (SequentialStackCode.programBudget g e) +
      c.stack.length + 2 + (c.stack.length + 2) * SequentialStackPayload.arityBudget g := by
  have hf := reachable_fits g x e c h
  have hc := control_cost (compilerNodes g e) g _ c hf.1 hf.2
  have hr := SequentialSharedWordSpace.reachable_word_records g x e c h
  omega

/-- Bounds the complete four-stream state, with no unencoded runtime fields. -/
theorem reachable_length (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    (encode (compilerNodes g e) c).length ≤
      (c.stack.length + 1) * controlBudget (compilerNodes g e) g (SequentialStackCode.programBudget g e) +
      SequentialClock.positionClock g x.length + 2 * x.length + 2 * c.stack.length + 4 +
      2 * ((c.stack.length + 2) * SequentialStackPayload.arityBudget g) := by
  have hc := reachable_control_cost g x e c h
  have hp := SequentialSharedCursors.reachable_cursor_bits g x e c h
  have hw := SequentialSharedWordSpace.reachable_capture_stream g x e c h
  have hm : c.clock ≤ SequentialClock.positionClock g x.length := by
    obtain ⟨d,hd,he⟩ := runs_lift g x e c h
    rw [← he]
    exact (SequentialSharedClock.reachable_clock_bounds g x e d hd).1
  rw [encode_length]
  unfold cost at hc
  omega

noncomputable def frameFactor (g : MGrammar) (e : MExp) : Nat :=
  (g.rules.length + 1) * (SequentialStackRank.codeBudget g + 1) + sizeOf e + 2

noncomputable def linearFactor (g : MGrammar) (e : MExp) : Nat :=
  frameFactor g e * (controlBudget (compilerNodes g e) g (SequentialStackCode.programBudget g e) +
    2 + 2 * SequentialStackPayload.arityBudget g) + (g.rules.length + 1) + 2

/-- The coefficient depends on the source grammar and start expression only;
the input and every intermediate word-machine state remain arbitrary. -/
theorem encoded_state_linear (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    (encode (compilerNodes g e) c).length ≤ linearFactor g e * (x.length + 1) := by
  let B := controlBudget (compilerNodes g e) g (SequentialStackCode.programBudget g e)
  let A := SequentialStackPayload.arityBudget g
  have hraw := reachable_length g x e c h
  have hsmall : (encode (compilerNodes g e) c).length ≤
      (c.stack.length + 2) * (B + 2 + 2 * A) +
        SequentialClock.positionClock g x.length + 2 * (x.length + 1) := by
    change _ ≤ (c.stack.length + 1) * B + _ + _ + _ + _ + 2 * ((c.stack.length + 2) * A) at hraw
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_comm,Nat.mul_left_comm] at hraw ⊢
    omega
  have hs := SequentialSharedWordSpace.stack_linear_bound g x e c h
  have hp : sizeOf e + 2 ≤ (sizeOf e + 2) * (x.length + 1) := by
    rw [Nat.mul_succ]
    omega
  have hK : c.stack.length + 2 ≤ frameFactor g e * (x.length + 1) := by
    unfold frameFactor
    simp only [Nat.add_mul] at hs hp ⊢
    omega
  have hmul := Nat.mul_le_mul_right (B + 2 + 2 * A) hK
  have hsum := Nat.add_le_add_right
    (Nat.add_le_add_right hmul (SequentialClock.positionClock g x.length)) (2 * (x.length + 1))
  apply Nat.le_trans hsmall
  simpa only [linearFactor,SequentialClock.positionClock,Nat.add_mul,Nat.mul_right_comm,
    B,A,Nat.add_assoc] using hsum

end Shallot.MacroPeg.CBV.SequentialSharedStateBound
