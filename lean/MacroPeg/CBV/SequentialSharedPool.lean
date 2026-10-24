import MacroPeg.CBV.SequentialSharedCursors
import MacroPeg.CBV.SequentialStackCodec

/-! Fixed-program syntax references for every state of the word machine.
Scope frames contain no syntax, and the other frames inherit the original
machine's expression-pool certificates through scope erasure. -/
namespace Shallot.MacroPeg.CBV.SequentialSharedPool
open SequentialSharedWords
open SequentialStackPool (ExprOK ArgsOK)
open CBVtoCBN (CompileNode compilerNodes)

def TaskOK (ns : List CompileNode) : Task → Prop
  | .expr e _ => ExprOK ns e
  | .args es _ => ArgsOK ns es
  | _ => True

def FrameOK (ns : List CompileNode) : Frame → Prop
  | .seq b | .alt b _ => ExprOK ns b
  | .star a _ => ExprOK ns (.star a)
  | .argHead es _ => ArgsOK ns es
  | _ => True

def ConfigOK (ns : List CompileNode) (c : Config) : Prop :=
  TaskOK ns c.task ∧ ∀ f ∈ c.stack, FrameOK ns f

theorem decode_task_ok (ns : List CompileNode) (x : List Char) (m : Nat)
    (E : SequentialSharedClock.CaptureEnv) (t : SequentialSharedClock.Task)
    (h : SequentialStackPool.TaskOK ns (SequentialSharedRank.eraseTask m E t)) :
    TaskOK ns (decodeTask x t) := by
  cases t <;> exact h

theorem decode_stack_ok (ns : List CompileNode) (x : List Char) (m : Nat)
    (E : SequentialSharedClock.CaptureEnv) (K : List SequentialSharedClock.Frame)
    (h : SequentialStackPool.FramesOK ns (SequentialSharedRank.eraseStack m E K)) :
    ∀ f ∈ K.map (decodeFrame x), FrameOK ns f := by
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
      have ht : SequentialStackPool.FramesOK ns
          (SequentialSharedRank.eraseStack m E K) := by
        intro F hF
        exact h F (List.mem_cons_of_mem _ hF)
      have hk := ih m E ht
      intro F hF
      rcases List.mem_cons.mp hF with rfl | hF
      · exact h _ List.mem_cons_self
      · exact hk _ hF

theorem reachable_ok (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) : ConfigOK (compilerNodes g e) c := by
  obtain ⟨d,hd,rfl⟩ := runs_lift g x e c h
  have ho := SequentialStackPool.reachable_ok g x e (SequentialSharedRank.erase d)
    (SequentialSharedRank.runs_erase hd)
  exact ⟨decode_task_ok _ x d.clock d.env d.task ho.1,
    decode_stack_ok _ x d.clock d.env d.stack ho.2⟩

end Shallot.MacroPeg.CBV.SequentialSharedPool
