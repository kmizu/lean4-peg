import MacroPeg.CBV.SequentialBinaryLoader
import Complexity.ListFiniteAlphabet
import Complexity.ListClasses

/-! A standard-input Turing machine for first-order sequential CBV on ordinary
a/b words, with the complete initialization and intermediate space bound. -/
namespace Shallot.MacroPeg.CBV.SequentialBinaryInputMachine
open Complexity Complexity.BinaryWord SequentialStackCodecBound SequentialStackBinary CBVtoCBN
open Shallot.PegSeparation (bitWord)

noncomputable def coefficient (g : MGrammar) (e : MExp) : Nat :=
  Classical.choose (SequentialEncodedMachine.space_bound g e)

noncomputable def space (g : MGrammar) (e : MExp) (n : Nat) : Nat :=
  (coefficient g e+104)*(n+1)+11*((cellCoefficient g e*(n+1))*
    ((n+1).log2+(numberCoefficient g e).log2+2))

noncomputable def lists (g : MGrammar) (e : MExp) : LProg 20 :=
  .seq SequentialBinaryLoader.program (SequentialEncodedMachine.program g e)

noncomputable def program (g : MGrammar) (e : MExp) : Prog 20 :=
  .seq (initP (by decide : 1 < 20)) (lists g e).compile

private theorem encoded_space (g : MGrammar) (e : MExp) (w : List Bool) :
    SequentialEncodedMachine.space g (bitWord w) e ≤ space g e w.length := by
  have hh := Classical.choose_spec (SequentialEncodedMachine.space_bound g e) (bitWord w)
  have hlen : (bitWord w).length = w.length := by simp [bitWord]
  rw [hlen] at hh
  unfold space coefficient
  rw [Nat.add_mul]
  omega

private theorem loader_space (g : MGrammar) (e : MExp) (n : Nat) :
    SequentialBinaryLoader.space n ≤ space g e n := by
  unfold SequentialBinaryLoader.space space
  rw [Nat.add_mul]
  omega

theorem lists_halts (g : MGrammar) (e : MExp) (w : List Bool) :
    ∃ held T, Halts (LenOK (space g e w.length)) (lists g e) (initLists 20 w)
      (SequentialTerminalTest.accept (SequentialSpanRecompute.run g (bitWord w) e))
      (SequentialTerminalMachine.stopped (width g (bitWord w) e)
        (Complexity.encS (SequentialInputRead.codes (bitWord w))) held
        (SequentialTerminalTest.accept (SequentialSpanRecompute.run g (bitWord w) e))) T := by
  obtain ⟨Tl,hl⟩ := SequentialBinaryLoader.runs w
  obtain ⟨held,Te,t,ht,he⟩ := SequentialEncodedMachine.halts g (bitWord w) e
  have hl' := hl.weaken (Q' := LenOK (space g e w.length))
    (fun _ hh i => Nat.le_trans (hh i) (loader_space g e w.length))
  have he' := he.weaken (Q' := LenOK (space g e w.length))
    (fun _ hh i => Nat.le_trans (hh i) (encoded_space g e w))
  exact ⟨held,_,hl'.seqH ⟨t,ht,he'⟩⟩

theorem tape (g : MGrammar) (e : MExp) (w : List Bool) :
    ∃ t τ', Exec (TFits (space g e w.length)) (program g e) (initTapes 20 w) t
      (.stop (SequentialTerminalTest.accept (SequentialSpanRecompute.run g (bitWord w) e)) τ') := by
  obtain ⟨ti,τi,_,hi,hrep⟩ := initP_spec (by decide : 1 < 20) w
  have hcap : w.length+2 ≤ space g e w.length := by
    have hh := loader_space g e w.length
    unfold SequentialBinaryLoader.space at hh
    omega
  have hi' := hi.mono (fun _ hh => hh.mono hcap)
  obtain ⟨held,T,t,ht,he⟩ := lists_halts g e w
  obtain ⟨t',o,_,hex,hr⟩ := (compile_exec (fun _ h => h) he).1 τi hrep
  cases o with
  | cont τ' => exact False.elim hr
  | stop b τ' =>
    obtain ⟨hb,_⟩ := hr
    subst b
    exact ⟨ti+t',τ',.seqC hi' hex⟩

theorem recognizes {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (w : List Bool) :
    ∃ t b τ', Exec (TFits (space g e w.length)) (program g e) (initTapes 20 w) t (.stop b τ') ∧
      (b=true ↔ SObs g .callByValueSeq e (bitWord w) (some [])) := by
  obtain ⟨t,τ',hex⟩ := tape g e w
  exact ⟨t,_,τ',hex,SequentialEvaluationMachine.answer_iff hg he (bitWord w)⟩

/-- The fixed list program uses a finite tape alphabet, including the standard
input normalizer. No grammar-dependent runtime advice is present. -/
theorem finite_alphabet (g : MGrammar) (e : MExp) :
    ∃ na, 3 ≤ na ∧ (program g e).SymOK na := by
  obtain ⟨E,hE,hc⟩ := (lists g e).exists_constOK
  exact ⟨E+4,by omega,initP_symOK (by decide : 1 < 20) (E+4) (by omega),compile_symOK E _ hc⟩

/-- The standard initial TM configuration recognizes the original a/b word
language within the stated grammar-dependent linear plus n log n bound. -/
theorem machine {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder) :
    ∃ M : TM 20, M.Decides (fun w => SObs g .callByValueSeq e (bitWord w) (some [])) ∧
      M.SpaceBounded (space g e) := by
  obtain ⟨na,hna,hs⟩ := finite_alphabet g e
  exact ⟨(program g e).machine na hna hs,
    (program g e).decides_of_exec na hna hs _ (space g e) (recognizes hg he)⟩

end Shallot.MacroPeg.CBV.SequentialBinaryInputMachine
