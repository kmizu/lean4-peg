import MacroPeg.CBV.SequentialInitializationFields

/-! One fixed sequential evaluator from a unary input length and the encoded
original input, including all initialization numbers and the binary initial state. -/
namespace Shallot.MacroPeg.CBV.SequentialSeedMachine
open Complexity Complexity.BinaryWord SequentialStackCodecBound SequentialStackBinary CBVtoCBN
open SequentialTerminalMachine

noncomputable def program (g : MGrammar) (e : MExp) : LProg 20 :=
  .seq (SequentialInitializationNumbers.program g e)
    (.seq (SequentialInitializationFields.program g e)
      (SequentialEvaluationMachine.program (compilerNodes g e) g))

noncomputable def space (g : MGrammar) (x : List Char) (e : MExp) : Nat :=
  SequentialInitializationNumbers.space g e x.length (Complexity.encS (SequentialInputRead.codes x))+
    SequentialInitializationFields.space g x e+SequentialEvaluationMachine.space g x e

theorem halts (g : MGrammar) (x : List Char) (e : MExp) :
    ∃ held T, Halts (LenOK (space g x e)) (program g e)
      (SequentialInitializationNumbers.seed x.length (Complexity.encS (SequentialInputRead.codes x)))
      (SequentialTerminalTest.accept (SequentialSpanRecompute.run g x e))
      (stopped (width g x e) (Complexity.encS (SequentialInputRead.codes x)) held
        (SequentialTerminalTest.accept (SequentialSpanRecompute.run g x e))) T := by
  obtain ⟨Tn,hn⟩ := SequentialInitializationNumbers.runs g e x.length (Complexity.encS (SequentialInputRead.codes x))
  obtain ⟨Tf,hf⟩ := SequentialInitializationFields.runs g x e
  obtain ⟨held,Te,t,ht,he⟩ := SequentialEvaluationMachine.initialized_halts g x e
  have hn' := hn.weaken (Q' := LenOK (space g x e)) (fun _ hh i => by unfold space; have := hh i; omega)
  have hf' := hf.weaken (Q' := LenOK (space g x e)) (fun _ hh i => by unfold space; have := hh i; omega)
  have he' := he.weaken (Q' := LenOK (space g x e)) (fun _ hh i => by unfold space; have := hh i; omega)
  exact ⟨held,_,hn'.seqH (hf'.seqH ⟨t,ht,he'⟩)⟩

/-- The same twenty physical tapes run initialization, evaluation, and the
final acceptance branch. No initial width or clock is an extra input. -/
theorem tape (g : MGrammar) (x : List Char) (e : MExp) (τ : Tapes 20)
    (hτ : Rep (SequentialInitializationNumbers.seed x.length (Complexity.encS (SequentialInputRead.codes x))) τ) :
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

/-- For first-order source grammars, the actual halting answer agrees with
sequential full-consumption observation on the same original character list. -/
theorem recognizes {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (x : List Char) (τ : Tapes 20)
    (hτ : Rep (SequentialInitializationNumbers.seed x.length (Complexity.encS (SequentialInputRead.codes x))) τ) :
    ∃ b held t τ', Exec (TFits (space g x e)) (program g e).compile τ t (.stop b τ') ∧
      Rep (stopped (width g x e) (Complexity.encS (SequentialInputRead.codes x)) held b) τ' ∧
      (b=true ↔ SObs g .callByValueSeq e x (some [])) := by
  obtain ⟨held,t,τ',hex,hrep⟩ := tape g x e τ hτ
  exact ⟨_,held,t,τ',hex,hrep,SequentialEvaluationMachine.answer_iff hg he x⟩

/-- Initialization adds a linear term to the previously verified binary stack
space bound, uniformly over the whole halting computation. -/
theorem space_bound (g : MGrammar) (e : MExp) :
    ∃ C, ∀ x : List Char, space g x e ≤ C*(x.length+1)+11*((cellCoefficient g e*(x.length+1))*
      ((x.length+1).log2+(numberCoefficient g e).log2+2)) := by
  obtain ⟨Cn,hn⟩ := SequentialInitializationNumbers.space_linear g e
  obtain ⟨Cf,hf⟩ := SequentialInitializationFields.space_linear g e
  refine ⟨Cn+Cf+SequentialEvaluationMachine.coefficient g e,?_⟩
  intro x
  have h1 := hn x
  have h2 := hf x
  unfold space SequentialEvaluationMachine.space
  simp only [Nat.add_mul]
  omega

end Shallot.MacroPeg.CBV.SequentialSeedMachine
