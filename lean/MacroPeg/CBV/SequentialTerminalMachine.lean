import MacroPeg.CBV.SequentialTerminalTest
import MacroPeg.CBV.SequentialStepMachine

/-! Terminal expression results are read from their binary state. The binary
state register becomes empty and a separate acceptance marker remains. -/
namespace Shallot.MacroPeg.CBV.SequentialTerminalMachine
open Complexity Complexity.BinaryWord SequentialStack SequentialStackCodec SequentialStackCodecBound CBVtoCBN
open SequentialStackBinary SequentialInputHost
open SequentialFrontRead (frontSpace locals)

def reg (i : Fin 6) : Fin 20 :=
  if i=0 then 9 else if i=1 then 10 else if i=2 then 17 else if i=3 then 12 else if i=4 then 13 else 2

theorem reg_injective : Function.Injective reg := by unfold Function.Injective; decide

def stopped (w : Nat) (X : List Nat) (held : Nat) (accept : Bool) : Lists 20 :=
  (extend (SequentialFieldFetch.start w [] [] [] held []) X).set 17 (if accept then [2] else [])

def program : LProg 20 := .seq (SequentialFrontScan.parserProgram.rename old)
  (SequentialTerminalTest.program.compile.rename reg)

noncomputable def space (g : MGrammar) (x : List Char) (e : MExp) (c : Config) : Nat :=
  SequentialStepMachine.space g x e c+SequentialTerminalTest.space (numberBound g x e)

private theorem projection (X D : List Nat) (w held : Nat) :
    ∀ i, extend (SequentialFieldFetch.start w [] [] (locals D) held []) X (reg i) =
      encL (SequentialNumericFive.st D [] [] [] []) i := by
  intro i
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem frame_result (X D : List Nat) (w held : Nat) (b : Bool) :
    (encL (SequentialNumericFive.st [] [] (if b then [0] else []) [] [])).frame reg
      (extend (SequentialFieldFetch.start w [] [] (locals D) held []) X) = stopped w X held b := by
  cases b <;> funext j <;> by_cases hj : ∃ i, reg i=j
  all_goals first
    | (obtain ⟨i,rfl⟩ := hj
       rw [Lists.frame_get reg_injective]
       have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
       rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    | (rw [Lists.frame_outside _ _ j hj]
       have hj' : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 ∨ j=19 := by omega
       rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
       all_goals first
         | rfl
         | exact False.elim (hj ⟨0,rfl⟩)
         | exact False.elim (hj ⟨1,rfl⟩)
         | exact False.elim (hj ⟨2,rfl⟩)
         | exact False.elim (hj ⟨3,rfl⟩)
         | exact False.elim (hj ⟨4,rfl⟩)
         | exact False.elim (hj ⟨5,rfl⟩))

private theorem local_runs (r : Res) (X : List Nat) (w held : Nat) {B N : Nat}
    (hN : 3 ≤ N) (hq : ∀ q, r=some (some q) → q ≤ N) (hspace : SequentialTerminalTest.space N ≤ B)
    (hR : LenOK B (extend (SequentialFieldFetch.start w [] [] (locals (SequentialTerminalTest.word r)) held []) X)) :
    Complexity.Runs (LenOK B) (SequentialTerminalTest.program.compile.rename reg)
      (extend (SequentialFieldFetch.start w [] [] (locals (SequentialTerminalTest.word r)) held []) X)
      (stopped w X held (SequentialTerminalTest.accept r)) (100*ncost (SequentialTerminalTest.space N)) := by
  have hr := (SequentialTerminalTest.compiled_runs r hN hq).weaken (fun _ hh i => Nat.le_trans (hh i) hspace)
  let R := extend (SequentialFieldFetch.start w [] [] (locals (SequentialTerminalTest.word r)) held []) X
  obtain ⟨t,ht,he⟩ := hr
  have hh := he.rename_frame reg_injective R hR
  rw [Lists.frame_eq reg_injective R _ (projection X (SequentialTerminalTest.word r) w held)] at hh
  change LExec (LenOK B) (SequentialTerminalTest.program.compile.rename reg) R t
    (.cont ((encL (SequentialNumericFive.st [] [] (if SequentialTerminalTest.accept r then [0] else []) [] [])).frame reg R)) at hh
  rw [frame_result] at hh
  exact ⟨t,ht,hh⟩

theorem handler_runs (g : MGrammar) (x : List Char) (e : MExp) (r : Res)
    (h : SequentialStack.Runs g x (initial g x e) ⟨.value (.expr r),[]⟩) :
    ∃ held T, Complexity.Runs (LenOK (space g x e ⟨.value (.expr r),[]⟩)) program
      (SequentialStepMachine.state g x e ⟨.value (.expr r),[]⟩)
      (stopped (width g x e) (Complexity.encS (SequentialInputRead.codes x)) held (SequentialTerminalTest.accept r)) T := by
  let c : Config := ⟨.value (.expr r),[]⟩
  let N := numberBound g x e
  let B := space g x e c
  have hfront : frontSpace g x e c ≤ B := by unfold B space SequentialStepMachine.space; omega
  have hspace : SequentialTerminalTest.space N ≤ B := by unfold B space N; omega
  have hX : (Complexity.encS (SequentialInputRead.codes x)).length+2 ≤ B := by
    have hh := SequentialInputRead.encoded_length x
    unfold B space SequentialStepMachine.space SequentialInputRead.space
    omega
  have hN : 3 ≤ N := by unfold N numberBound; omega
  have hcode : encode (compilerNodes g e) c = SequentialTerminalTest.word r := by
    simp [c,encode,SequentialTerminalTest.word,SequentialAtomCodec.outputFields,writeTask,writeValue,writeList]
  have hq : ∀ q, r=some (some q) → q ≤ N := by
    intro q hq
    have hh := reachable_numbers g x e c h q
    apply hh
    simp [hcode,SequentialTerminalTest.word,SequentialAtomCodec.outputFields,writeRes,hq]
  obtain ⟨held,Tp,hp⟩ := SequentialFrontScanMachine.reachable_parser_runs g x e c h
  have hprefix : SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) (SequentialFront.front c) =
      SequentialTerminalTest.word r := by
    simp [c,SequentialFront.tail,SequentialFront.front,SequentialFront.prefixCode,SequentialFront.suffixCode,
      SequentialTerminalTest.word,SequentialAtomCodec.outputFields,writeTask,writeValue]
  have hsuffix : SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c) = [] := rfl
  rw [hprefix,hsuffix] at hp
  have hp20 := old_runs _ _ _ (Complexity.encS (SequentialInputRead.codes x))
    (hp.weaken (fun _ hh i => Nat.le_trans (hh i) hfront)) hX
  have hparsed : LenOK B (extend (SequentialFieldFetch.start (width g x e) [] []
      (locals (SequentialTerminalTest.word r)) held []) (Complexity.encS (SequentialInputRead.codes x))) := by
    obtain ⟨_,_,he⟩ := hp20
    exact he.q_end _ (Or.inl rfl)
  have hc := local_runs r (Complexity.encS (SequentialInputRead.codes x)) (width g x e) held hN hq hspace hparsed
  exact ⟨held,_,hp20.seq hc⟩

theorem terminal_runs (g : MGrammar) (x : List Char) (e : MExp) (r : Res)
    (h : SequentialStack.Runs g x (initial g x e) ⟨.value (.expr r),[]⟩) :
    ∃ held T, Complexity.Runs (LenOK (space g x e ⟨.value (.expr r),[]⟩))
      (SequentialStepMachine.program (compilerNodes g e) g program)
      (SequentialStepMachine.state g x e ⟨.value (.expr r),[]⟩)
      (stopped (width g x e) (Complexity.encS (SequentialInputRead.codes x)) held (SequentialTerminalTest.accept r)) T := by
  obtain ⟨held,T,hr⟩ := handler_runs g x e r h
  refine ⟨held,?_⟩
  exact SequentialStepScanMachine.selected_runs g x e _ h (SequentialStepMachine.continuations (compilerNodes g e) g program)
    (Complexity.encS (SequentialInputRead.codes x)) _ (by unfold space SequentialStepMachine.space; omega)
    (by
      have hh := SequentialInputRead.encoded_length x
      unfold space SequentialStepMachine.space SequentialInputRead.space
      omega) hr

theorem stopped_test (w : Nat) (X : List Nat) (held : Nat) (b : Bool) :
    nonEmpty (lastSym (stopped w X held b 0)) = false := rfl

theorem accept_test (w : Nat) (X : List Nat) (held : Nat) (b : Bool) :
    nonEmpty (lastSym (stopped w X held b 17)) = b := by cases b <;> rfl

theorem space_bound (g : MGrammar) (e : MExp) :
    ∃ C, ∀ x c, SequentialStack.Runs g x (initial g x e) c →
      space g x e c ≤ C*(x.length+1)+11*((cellCoefficient g e*(x.length+1))*
        ((x.length+1).log2+(numberCoefficient g e).log2+2)) := by
  obtain ⟨C,hC⟩ := SequentialStepMachine.space_bound g e
  refine ⟨C+(105*numberCoefficient g e+10107),?_⟩
  intro x c hc
  have hh := hC x c hc
  have hn := numberBound_linear g x e
  have hm := Nat.mul_le_mul_left 105 hn
  have hd : 10107 ≤ 10107*(x.length+1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold space
  rw [SequentialTerminalTest.space_linear,Nat.add_mul]
  have he : (105*numberCoefficient g e+10107)*(x.length+1) =
      105*(numberCoefficient g e*(x.length+1))+10107*(x.length+1) := by rw [Nat.add_mul,Nat.mul_assoc]
  have hterm : 105*numberBound g x e+10107 ≤ (105*numberCoefficient g e+10107)*(x.length+1) := by
    rw [he]
    exact Nat.add_le_add hm hd
  have ht := Nat.add_le_add hh hterm
  rw [Nat.add_right_comm] at ht
  simpa only [Nat.add_assoc] using ht

end Shallot.MacroPeg.CBV.SequentialTerminalMachine
