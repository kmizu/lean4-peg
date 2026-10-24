import MacroPeg.CBV.SequentialArgumentsDispatchMachine

/-! Read the actual query-rule identifier before entering its fixed query
program. The bounded rule id comes from the reachable-state invariant. -/
namespace Shallot.MacroPeg.CBV.SequentialQueryDispatchMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (encode writeFrames)
open SequentialCaptureCopyMachine (withInput)

def program (ns : List CBVtoCBN.CompileNode) (g : MGrammar) : LProg 8 :=
  SequentialTagDispatchMachine.program 2 1 3 g.rules.length (SequentialQueryPackedMachine.program ns g)

theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E W : CaptureEnv)
    (i p : Nat) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (SequentialQueryPackedMachine.before m E W i p K))
    (hs : SequentialSharedWords.step g x (SequentialQueryPackedMachine.before m E W i p K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) g)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (SequentialQueryPackedMachine.before m E W i p K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let L := withInput (encode ns (SequentialQueryPackedMachine.before m E W i p K)) x
  let target := withInput (encode ns next) x
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  have he := Option.some.inj (hs.symm.trans (SequentialQueryPackedMachine.reachable_step g x e m E W i p K h))
  obtain ⟨T,ht⟩ := SequentialQueryPackedMachine.transition_runs g x e m E W i p K h
  rw [← he] at ht
  have hb : Complexity.Runs (LenOK B) (SequentialQueryPackedMachine.program ns g i) L target T := ht
  have hL : LenOK B L := by obtain ⟨t,ht,hx⟩ := hb; exact hx.q_start
  have hi : i < g.rules.length := (SequentialSharedStateBound.reachable_fits g x e _ h).1
  let C := (blocks (writeFrames ns K).control ++ blocks [W.length]) ++ [0]
  have hsrc : L 2=C ++ unary i ++ blocks [E.length,K.length,2] := by
    change withInput (encode ns (SequentialQueryPackedMachine.before m E W i p K)) x 2 = _
    rw [SequentialQueryPackedMachine.before_control]
    simp only [C,blocks_cons,show blocks []=[] from rfl,List.nil_append,List.append_assoc]
  exact SequentialTagDispatchMachine.dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    [E.length,K.length,2] g.rules.length i (Nat.le_of_lt hi) C (SequentialQueryPackedMachine.program ns g)
    L target hsrc (by rw [lastSym_append]; rfl) rfl hL hb

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (g : MGrammar) :
    ∃ E, 0x110001 ≤ E ∧ (program ns g).compile.SymOK (E+4) := by
  obtain ⟨E,_hE,hc⟩ := LProg.exists_constOK (program ns g)
  exact ⟨max E 0x110001,Nat.le_max_right _ _,compile_symOK _ _
    (LProg.ConstOK.mono (Nat.le_max_left E 0x110001) hc)⟩

end Shallot.MacroPeg.CBV.SequentialQueryDispatchMachine
