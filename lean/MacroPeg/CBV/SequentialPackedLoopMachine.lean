import MacroPeg.CBV.SequentialRunningMachine

/-! Iterate the complete fixed step program until an actual terminal value.
The one-bit running flag is removed before every step so all instruction
scratch invariants remain exact. -/
namespace Shallot.MacroPeg.CBV.SequentialPackedLoopMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine
open SequentialSharedWords (Config Runs initial)
open SequentialSharedStateCodec (encode)
open SequentialCaptureCopyMachine (withInput)
open SequentialRunningMachine (running flag)

def body (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (bound : Nat) : LProg 8 :=
  .seq (.pop 7) (.seq (SequentialStepDispatchMachine.program ns g bound) SequentialRunningMachine.program)

def loop (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (bound : Nat) : LProg 8 :=
  .loop 7 (symIs 1) (body ns g bound)

def program (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (bound : Nat) : LProg 8 :=
  .seq SequentialRunningMachine.program (.seq (loop ns g bound) (.pop 7))

noncomputable def capacity (g : MGrammar) (e : MExp) (n : Nat) : Nat :=
  (SequentialSharedStateBound.linearFactor g e+1)*(n+1)+3

def state (g : MGrammar) (x : List Char) (e : MExp) (c : Config) : Lists 8 :=
  withInput (encode (CBVtoCBN.compilerNodes g e) c) x

def marked (g : MGrammar) (x : List Char) (e : MExp) (c : Config) : Lists 8 :=
  (state g x e c).set 7 [flag c]

theorem reachable_fits (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) : LenOK (capacity g e x.length) (state g x e c) := by
  have hb := SequentialSharedStateBound.encoded_state_linear g x e c h
  apply SequentialCaptureCopyMachine.withInput_fits
  · dsimp [capacity]; rw [Nat.add_mul,Nat.one_mul]; omega
  · dsimp [capacity]; rw [Nat.add_mul,Nat.one_mul]; omega

theorem marked_fits (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) : LenOK (capacity g e x.length) (marked g x e c) := by
  exact SequentialRunningMachine.flag_fits c x _ (reachable_fits g x e c h) (by unfold capacity; omega)

theorem unmark_runs (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    Complexity.Runs (LenOK (capacity g e x.length)) (.pop 7) (marked g x e c) (state g x e c) 1 := by
  have he : (marked g x e c).set 7 ((marked g x e c 7).dropLast)=state g x e c := by
    have h7 : state g x e c 7=[] := rfl
    simp only [marked,Lists.set_same,List.dropLast_singleton,Lists.set_set_u]
    rw [← h7,Lists.set_get_self]
  have hr := runs_pop (i := (7 : Fin 8)) (marked_fits g x e c h) (by rw [he]; exact reachable_fits g x e c h)
  simpa only [he] using hr

private theorem next_reachable {g : MGrammar} {x : List Char} {a b c : Config}
    (h : Runs g x a b) (hs : SequentialSharedWords.step g x b=some c) : Runs g x a c := by
  induction h with
  | refl => exact .cons hs (.refl _)
  | cons hh ht ih => exact .cons hh (ih hs)

theorem loop_runs (g : MGrammar) (x : List Char) (e : MExp) {c final : Config}
    (trace : Runs g x c final) (hfinal : running final=false) (hreach : Runs g x (initial g x e) c) :
    ∃ T, Complexity.Runs (LenOK (capacity g e x.length))
      (loop (CBVtoCBN.compilerNodes g e) g (SequentialStackCode.programBudget g e))
      (marked g x e c) (marked g x e final) T := by
  revert hreach
  induction trace with
  | refl c =>
    intro hc
    exact ⟨1,1,by omega,.loopF (marked_fits g x e c hc) (by
      simp only [marked,Lists.set_same,flag,hfinal,Bool.false_eq_true,if_false]
      rfl)⟩
  | @cons c next final hs ht ih =>
    intro hc
    have hn := next_reachable hc hs
    obtain ⟨Ti,hi⟩ := ih hfinal hn
    have hstart := SequentialRunningMachine.step_running g x c next hs
    obtain ⟨Ts,hstep⟩ := SequentialStepDispatchMachine.transition_runs g x e c next hc hs
    obtain ⟨Tr,hrun⟩ := SequentialRunningMachine.running_runs (CBVtoCBN.compilerNodes g e) x next
      (reachable_fits g x e next hn) (by unfold capacity; omega)
    have hb : Complexity.Runs (LenOK (capacity g e x.length))
        (body (CBVtoCBN.compilerNodes g e) g (SequentialStackCode.programBudget g e))
        (marked g x e c) (marked g x e next) (1+Ts+Tr) := by
      simpa only [body,marked,state,Nat.add_assoc] using (unmark_runs g x e c hc).seq (hstep.seq hrun)
    obtain ⟨t1,ht1,hx1⟩ := hb
    obtain ⟨t2,ht2,hx2⟩ := hi
    exact ⟨t1+1+t2,t1+1+t2,by omega,.loopC (marked_fits g x e c hc) (by
      simp only [marked,Lists.set_same,flag,hstart,if_true]
      rfl) hx1 hx2⟩

/-- One input-independent program executes any actual finite source run to a
terminal value. All transient running flags and instruction scratch are cleared. -/
theorem run_trace (g : MGrammar) (x : List Char) (e : MExp) {c final : Config}
    (trace : Runs g x c final) (hfinal : running final=false) (hreach : Runs g x (initial g x e) c) :
    ∃ T, Complexity.Runs (LenOK (capacity g e x.length))
      (program (CBVtoCBN.compilerNodes g e) g (SequentialStackCode.programBudget g e))
      (state g x e c) (state g x e final) T := by
  obtain ⟨Tc,hc⟩ := SequentialRunningMachine.running_runs (CBVtoCBN.compilerNodes g e) x c
    (reachable_fits g x e c hreach) (by unfold capacity; omega)
  obtain ⟨Tl,hl⟩ := loop_runs g x e trace hfinal hreach
  have hf : Runs g x (initial g x e) final := by
    have aux : ∀ {a b}, Runs g x a b → Runs g x (initial g x e) a → Runs g x (initial g x e) b := by
      intro a b hab
      induction hab with
      | refl => exact id
      | cons hs ht ih => intro ha; exact ih (next_reachable ha hs)
    exact aux trace hreach
  exact ⟨_,hc.seq (hl.seq (unmark_runs g x e final hf))⟩

def final (g : MGrammar) (x : List Char) (e : MExp) : Config :=
  ⟨SequentialClock.positionClock g x.length,.value (.expr (SequentialSpanRecompute.run g x e)),[],[]⟩

/-- The real initialized word machine always supplies the finite execution;
no running-time fuel or precomputed result is an argument to the program. -/
theorem evaluate_runs (g : MGrammar) (x : List Char) (e : MExp) :
    ∃ T, Complexity.Runs (LenOK (capacity g e x.length))
      (program (CBVtoCBN.compilerNodes g e) g (SequentialStackCode.programBudget g e))
      (state g x e (initial g x e)) (state g x e (final g x e)) T := by
  exact run_trace g x e (SequentialSharedWords.initial_runs g x e)
    (by simp [final,running,SequentialStepDispatchMachine.taskTag]) (.refl _)

theorem evaluate_tape (g : MGrammar) (x : List Char) (e : MExp) (tau : Tapes 8)
    (hrep : Rep (state g x e (initial g x e)) tau) :
    ∃ t tau', Exec (TFits (capacity g e x.length))
      (program (CBVtoCBN.compilerNodes g e) g (SequentialStackCode.programBudget g e)).compile tau t (.cont tau') ∧
      Rep (state g x e (final g x e)) tau' := by
  obtain ⟨T,hr⟩ := evaluate_runs g x e
  exact tape_runs hr tau hrep

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (bound : Nat) :
    ∃ E, 0x110001 ≤ E ∧ (program ns g bound).compile.SymOK (E+4) := by
  obtain ⟨E,_hE,hc⟩ := LProg.exists_constOK (program ns g bound)
  exact ⟨max E 0x110001,Nat.le_max_right _ _,compile_symOK _ _
    (LProg.ConstOK.mono (Nat.le_max_left E 0x110001) hc)⟩

end Shallot.MacroPeg.CBV.SequentialPackedLoopMachine
