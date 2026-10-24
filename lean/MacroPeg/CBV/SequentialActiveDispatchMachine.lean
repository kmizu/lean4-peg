import MacroPeg.CBV.SequentialQueryDispatchMachine

/-! A single fixed program dispatches all non-return tasks from the actual
control stream, then dispatches their expression, argument, or rule fields. -/
namespace Shallot.MacroPeg.CBV.SequentialActiveDispatchMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (encode writeFrames)
open SequentialCaptureCopyMachine (withInput)

def Active : SequentialSharedWords.Task → Prop
  | .value _ => False
  | _ => True

def branches (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (bound : Nat) (tag : Nat) : LProg 8 :=
  if tag=0 then SequentialExpressionDispatchMachine.program ns g
  else if tag=1 then SequentialArgumentsDispatchMachine.program ns g bound
  else if tag=2 then SequentialQueryDispatchMachine.program ns g
  else skipP 2

def program (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (bound : Nat) : LProg 8 :=
  SequentialTagDispatchMachine.program 2 1 2 4 (branches ns g bound)

theorem kind_runs (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (bound tag : Nat) (htag : tag ≤ 4)
    (env stack : Nat) (payload tail : List Nat) (L M : Lists 8) {B T : Nat}
    (hctrl : L 2=tail ++ blocks (tag :: payload) ++ blocks [env,stack]) (h1 : L 1=[]) (hL : LenOK B L)
    (hp : Complexity.Runs (LenOK B) (branches ns g bound tag) L M T) :
    ∃ U, Complexity.Runs (LenOK B) (program ns g bound) L M U := by
  let C := (tail ++ blocks payload) ++ [0]
  have hsrc : L 2=C ++ unary tag ++ blocks [env,stack] := by
    rw [hctrl,blocks_cons]
    simp only [C,List.append_assoc]
  exact SequentialTagDispatchMachine.dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    [env,stack] 4 tag htag C (branches ns g bound) L M hsrc (by rw [lastSym_append]; rfl) h1 hL hp

/-- Every reachable expression, argument-list, and query task takes its
complete original Seq step through this one source-fixed eight-tape program. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (c next : Config)
    (h : Runs g x (initial g x e) c) (hs : SequentialSharedWords.step g x c=some next)
    (ha : Active c.task) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) g (SequentialStackCode.programBudget g e))
      (withInput (encode (CBVtoCBN.compilerNodes g e) c) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let bound := SequentialStackCode.programBudget g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  cases c with
  | mk m task E K => cases task with
    | expr a p =>
      obtain ⟨T,ht⟩ := SequentialExpressionDispatchMachine.transition_runs g x e a m E p K next h hs
      have hbranch : Complexity.Runs (LenOK B) (branches ns g bound 0)
          (withInput (encode ns ⟨m,.expr a p,E,K⟩) x) (withInput (encode ns next) x) T := ht
      have hL : LenOK B (withInput (encode ns ⟨m,.expr a p,E,K⟩) x) := by
        obtain ⟨t,ht,hx⟩ := hbranch; exact hx.q_start
      exact kind_runs ns g bound 0 (by decide) E.length K.length [SequentialStackCodec.exprId ns a]
        (blocks (writeFrames ns K).control) _ _ (SequentialExpressionDispatchMachine.before_control ns a m E p K)
        rfl hL hbranch
    | args es p =>
      obtain ⟨T,ht⟩ := SequentialArgumentsDispatchMachine.transition_runs g x e es m E p K next h hs
      have hbranch : Complexity.Runs (LenOK B) (branches ns g bound 1)
          (withInput (encode ns ⟨m,.args es p,E,K⟩) x) (withInput (encode ns next) x) T := ht
      have hL : LenOK B (withInput (encode ns ⟨m,.args es p,E,K⟩) x) := by
        obtain ⟨t,ht,hx⟩ := hbranch; exact hx.q_start
      apply kind_runs ns g bound 1 (by decide) E.length K.length (SequentialStackCodec.writeExprs ns es)
        (blocks (writeFrames ns K).control) _ _ ?_ rfl hL hbranch
      have hh := SequentialArgumentsDispatchMachine.before_control ns es m E p K
      change withInput (encode ns (SequentialArgumentsDispatchMachine.before es m E p K)) [] 2 = _
      rw [hh]
      simp only [blocks_cons,show blocks []=[] from rfl,List.nil_append,List.append_assoc]
    | query i W p =>
      obtain ⟨T,ht⟩ := SequentialQueryDispatchMachine.transition_runs g x e m E W i p K next h hs
      have hbranch : Complexity.Runs (LenOK B) (branches ns g bound 2)
          (withInput (encode ns ⟨m,.query i W p,E,K⟩) x) (withInput (encode ns next) x) T := ht
      have hL : LenOK B (withInput (encode ns ⟨m,.query i W p,E,K⟩) x) := by
        obtain ⟨t,ht,hx⟩ := hbranch; exact hx.q_start
      apply kind_runs ns g bound 2 (by decide) E.length K.length [i,W.length]
        (blocks (writeFrames ns K).control) _ _ ?_ rfl hL hbranch
      change withInput (encode ns (SequentialQueryPackedMachine.before m E W i p K)) x 2 = _
      rw [SequentialQueryPackedMachine.before_control]
      simp only [show [E.length,K.length,2,i,W.length]=[E.length,K.length] ++ [2,i,W.length] from rfl,
        blocks_append,List.append_assoc]
    | value v => exact False.elim ha

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (c next : Config)
    (h : Runs g x (initial g x e) c) (hs : SequentialSharedWords.step g x c=some next)
    (ha : Active c.task) (tau : Tapes 8) (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e) c) x) tau) :
    ∃ t tau', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) g (SequentialStackCode.programBudget g e)).compile tau t (.cont tau') ∧
      Rep (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) tau' := by
  obtain ⟨T,hr⟩ := transition_runs g x e c next h hs ha
  exact tape_runs hr tau hrep

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (bound : Nat) :
    ∃ E, 0x110001 ≤ E ∧ (program ns g bound).compile.SymOK (E+4) := by
  obtain ⟨E,_hE,hc⟩ := LProg.exists_constOK (program ns g bound)
  exact ⟨max E 0x110001,Nat.le_max_right _ _,compile_symOK _ _
    (LProg.ConstOK.mono (Nat.le_max_left E 0x110001) hc)⟩

end Shallot.MacroPeg.CBV.SequentialActiveDispatchMachine
