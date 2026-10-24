import MacroPeg.CBV.SequentialTerminalMachine

/-! Repeated execution from the initialized binary state and original-input
encoding. The terminal handler empties the state register and records the answer. -/
namespace Shallot.MacroPeg.CBV.SequentialEvaluationMachine
open Complexity Complexity.BinaryWord SequentialStack SequentialStackCodec SequentialStackCodecBound CBVtoCBN
open SequentialStackBinary SequentialTerminalMachine

def body (ns : List CompileNode) (g : MGrammar) : LProg 20 :=
  SequentialStepMachine.program ns g SequentialTerminalMachine.program

def loop (ns : List CompileNode) (g : MGrammar) : LProg 20 := .loop 0 nonEmpty (body ns g)

def finish : LProg 20 := .ite 17 nonEmpty (.halt true) (.halt false)

def program (ns : List CompileNode) (g : MGrammar) : LProg 20 := .seq (loop ns g) finish

theorem state_test (g : MGrammar) (x : List Char) (e : MExp) (c : Config) :
    nonEmpty (lastSym (SequentialStepMachine.state g x e c 0)) = true := by
  have hlen : 0 < (SequentialStepMachine.state g x e c 0).length := by
    change 0 < (storage (SequentialStackBinary.pack (width g x e) (encode (compilerNodes g e) c) ++ [])).length
    simp only [List.append_nil,storage,List.length_reverse,List.length_map,SequentialStackBinary.pack_length]
    apply Nat.mul_pos
    · simp only [encode,writeList,List.length_append,List.length_cons]; omega
    · unfold width; omega
  have hne : SequentialStepMachine.state g x e c 0 ≠ [] := by
    intro hh; rw [hh] at hlen; contradiction
  simpa only [nonEmpty,bne_iff_ne,ne_eq,lastSym_eq_three] using hne

noncomputable def coefficient (g : MGrammar) (e : MExp) : Nat :=
  Classical.choose (SequentialTerminalMachine.space_bound g e)

noncomputable def space (g : MGrammar) (x : List Char) (e : MExp) : Nat :=
  coefficient g e*(x.length+1)+11*((cellCoefficient g e*(x.length+1))*
    ((x.length+1).log2+(numberCoefficient g e).log2+2))

theorem reachable_space (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) :
    SequentialTerminalMachine.space g x e c ≤ space g x e :=
  Classical.choose_spec (SequentialTerminalMachine.space_bound g e) x c h

theorem loop_of_runs (g : MGrammar) (x : List Char) (e : MExp) {c d : Config}
    (trace : SequentialStack.Runs g x c d) (r : Res)
    (hd : d=⟨.value (.expr r),[]⟩)
    (hc : SequentialStack.Runs g x (initial g x e) c) :
    ∃ held T, Complexity.Runs (LenOK (space g x e)) (loop (compilerNodes g e) g)
      (SequentialStepMachine.state g x e c)
      (stopped (width g x e) (Complexity.encS (SequentialInputRead.codes x)) held (SequentialTerminalTest.accept r)) T := by
  revert hd hc
  induction trace with
  | refl c =>
    intro hd hc
    subst c
    obtain ⟨held,T,hr⟩ := SequentialTerminalMachine.terminal_runs g x e r hc
    have hh := hr.weaken (fun _ h i => Nat.le_trans (h i) (reachable_space g x e _ hc))
    obtain ⟨t,ht,he⟩ := hh
    have hstart := he.q_start
    have hend := he.q_end _ (Or.inl rfl)
    exact ⟨held,t+1+1,t+1+1,Nat.le_refl _,
      .loopC hstart (state_test g x e _) he (.loopF hend (stopped_test _ _ _ _))⟩
  | @cons a b d hs tail ih =>
    intro hd hc
    obtain ⟨held,T,hr⟩ := ih hd (hc.trans (.single hs))
    obtain ⟨Ts,hstep⟩ := SequentialStepMachine.transition_runs g x e a b hc hs SequentialTerminalMachine.program
    have hcap : SequentialStepMachine.space g x e a ≤ space g x e := by
      have hh := reachable_space g x e a hc
      unfold SequentialTerminalMachine.space at hh
      omega
    have hh := hstep.weaken (fun _ h i => Nat.le_trans (h i) hcap)
    obtain ⟨t₁,_,he₁⟩ := hh
    obtain ⟨t₂,_,he₂⟩ := hr
    exact ⟨held,t₁+1+t₂,t₁+1+t₂,Nat.le_refl _,
      .loopC he₁.q_start (state_test g x e a) he₁ he₂⟩

theorem finish_halts {B w held : Nat} {X : List Nat} (b : Bool)
    (h : LenOK B (stopped w X held b)) :
    Halts (LenOK B) finish (stopped w X held b) b (stopped w X held b) 2 := by
  cases b with
  | false => exact (halts_halt h).iteF h (accept_test _ _ _ false)
  | true => exact (halts_halt h).iteT h (accept_test _ _ _ true)

theorem initialized_halts (g : MGrammar) (x : List Char) (e : MExp) :
    ∃ held T, Halts (LenOK (space g x e)) (program (compilerNodes g e) g)
      (SequentialStepMachine.state g x e (initial g x e))
      (SequentialTerminalTest.accept (SequentialSpanRecompute.run g x e))
      (stopped (width g x e) (Complexity.encS (SequentialInputRead.codes x)) held
        (SequentialTerminalTest.accept (SequentialSpanRecompute.run g x e))) T := by
  obtain ⟨held,T,hr⟩ := loop_of_runs g x e (initial_runs g x e)
    (SequentialSpanRecompute.run g x e) rfl (.refl _)
  have hend : LenOK (space g x e) (stopped (width g x e) (Complexity.encS (SequentialInputRead.codes x)) held
      (SequentialTerminalTest.accept (SequentialSpanRecompute.run g x e))) := by
    obtain ⟨_,_,he⟩ := hr
    exact he.q_end _ (Or.inl rfl)
  exact ⟨held,_,hr.seqH (finish_halts _ hend)⟩

/-- The complete initialized evaluator runs on twenty actual tapes, with the
same space bound at every intermediate instruction and scan. -/
theorem initialized_tape (g : MGrammar) (x : List Char) (e : MExp)
    (τ : Tapes 20) (hτ : Rep (SequentialStepMachine.state g x e (initial g x e)) τ) :
    ∃ held t τ', Exec (TFits (space g x e)) (program (compilerNodes g e) g).compile τ t
      (.stop (SequentialTerminalTest.accept (SequentialSpanRecompute.run g x e)) τ') ∧
      Rep (stopped (width g x e) (Complexity.encS (SequentialInputRead.codes x)) held
        (SequentialTerminalTest.accept (SequentialSpanRecompute.run g x e))) τ' := by
  obtain ⟨held,T,t,ht,he⟩ := initialized_halts g x e
  obtain ⟨t',o,_,hex,hr⟩ := (compile_exec (fun _ h => h) he).1 τ hτ
  cases o with
  | cont τ' => exact False.elim hr
  | stop b τ' =>
    obtain ⟨hb,hrep⟩ := hr
    subst b
    exact ⟨held,t',τ',hex,hrep⟩

theorem answer_iff {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (x : List Char) : SequentialTerminalTest.accept (SequentialSpanRecompute.run g x e) = true ↔
      SObs g .callByValueSeq e x (some []) := by
  simp only [SequentialTerminalTest.accept,decide_eq_true_eq]
  exact SequentialSpanRecompute.run_accepts_iff hg he x

end Shallot.MacroPeg.CBV.SequentialEvaluationMachine
