import MacroPeg.CBV.SequentialInputLength

/-! Sequential evaluation from only the encoded original input. Length, clock,
width, binary stack initialization, evaluation, and the final answer are computed. -/
namespace Shallot.MacroPeg.CBV.SequentialEncodedMachine
open Complexity Complexity.BinaryWord SequentialStackCodecBound SequentialStackBinary CBVtoCBN
open SequentialTerminalMachine

noncomputable def program (g : MGrammar) (e : MExp) : LProg 20 :=
  .seq SequentialInputLength.program (SequentialSeedMachine.program g e)

def input (x : List Char) : Lists 20 :=
  SequentialInputLength.state (Complexity.encS (SequentialInputRead.codes x)) [] 0

noncomputable def space (g : MGrammar) (x : List Char) (e : MExp) : Nat :=
  SequentialInputLength.space (Complexity.encS (SequentialInputRead.codes x))+SequentialSeedMachine.space g x e

theorem halts (g : MGrammar) (x : List Char) (e : MExp) :
    ∃ held T, Halts (LenOK (space g x e)) (program g e) (input x)
      (SequentialTerminalTest.accept (SequentialSpanRecompute.run g x e))
      (stopped (width g x e) (Complexity.encS (SequentialInputRead.codes x)) held
        (SequentialTerminalTest.accept (SequentialSpanRecompute.run g x e))) T := by
  obtain ⟨Tl,hl⟩ := SequentialInputLength.original_runs x
  obtain ⟨held,Ts,t,ht,he⟩ := SequentialSeedMachine.halts g x e
  have hl' := hl.weaken (Q' := LenOK (space g x e)) (fun _ hh i => by unfold space; have := hh i; omega)
  have he' := he.weaken (Q' := LenOK (space g x e)) (fun _ hh i => by unfold space; have := hh i; omega)
  exact ⟨held,_,hl'.seqH ⟨t,ht,he'⟩⟩

theorem tape (g : MGrammar) (x : List Char) (e : MExp) (τ : Tapes 20)
    (hτ : Rep (input x) τ) :
    ∃ held t τ', Exec (TFits (space g x e)) (program g e).compile τ t
      (.stop (SequentialTerminalTest.accept (SequentialSpanRecompute.run g x e)) τ') ∧
      Rep (stopped (width g x e) (Complexity.encS (SequentialInputRead.codes x)) held
        (SequentialTerminalTest.accept (SequentialSpanRecompute.run g x e))) τ' := by
  obtain ⟨held,T,t,ht,he⟩ := halts g x e
  obtain ⟨t',o,_,hex,hr⟩ := (compile_exec (fun _ h => h) he).1 τ hτ
  cases o with
  | cont τ' => exact False.elim hr
  | stop b τ' =>
    obtain ⟨hb,hrep⟩ := hr
    subst b
    exact ⟨held,t',τ',hex,hrep⟩

theorem recognizes {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (x : List Char) (τ : Tapes 20) (hτ : Rep (input x) τ) :
    ∃ b held t τ', Exec (TFits (space g x e)) (program g e).compile τ t (.stop b τ') ∧
      Rep (stopped (width g x e) (Complexity.encS (SequentialInputRead.codes x)) held b) τ' ∧
      (b=true ↔ SObs g .callByValueSeq e x (some [])) := by
  obtain ⟨held,t,τ',hex,hrep⟩ := tape g x e τ hτ
  exact ⟨_,held,t,τ',hex,hrep,SequentialEvaluationMachine.answer_iff hg he x⟩

theorem space_bound (g : MGrammar) (e : MExp) :
    ∃ C, ∀ x : List Char, space g x e ≤ C*(x.length+1)+11*((cellCoefficient g e*(x.length+1))*
      ((x.length+1).log2+(numberCoefficient g e).log2+2)) := by
  obtain ⟨Cs,hs⟩ := SequentialSeedMachine.space_bound g e
  refine ⟨(2^32+5)+Cs,?_⟩
  intro x
  have hl := SequentialInputLength.space_linear x
  have hh := hs x
  unfold space
  rw [Nat.add_mul]
  omega

end Shallot.MacroPeg.CBV.SequentialEncodedMachine
