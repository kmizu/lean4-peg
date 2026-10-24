import MacroPeg.CBV.SequentialPackedBinaryLoader
import Complexity.ListClasses

/-! A complete standard-input eight-tape Turing machine for sequential CBV
on ordinary a/b words, with a linear bound on every intermediate tape state. -/
namespace Shallot.MacroPeg.CBV.SequentialPackedBinaryInputMachine
open Complexity
open Shallot.PegSeparation (bitWord)

noncomputable def space (g : MGrammar) (e : MExp) (n : Nat) : Nat := SequentialPackedLoopMachine.capacity g e n

noncomputable def lists (g : MGrammar) (e : MExp) : LProg 8 :=
  .seq SequentialPackedBinaryLoader.program (SequentialPackedHaltMachine.recognize g e)

noncomputable def program (g : MGrammar) (e : MExp) : Prog 8 :=
  .seq (initP (by decide : 1<8)) (lists g e).compile

theorem input_capacity (g : MGrammar) (e : MExp) (n : Nat) : n+2 ≤ space g e n := by
  unfold space SequentialPackedLoopMachine.capacity
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem lists_halts (g : MGrammar) (e : MExp) (w : List Bool) :
    ∃ M T, Halts (LenOK (space g e w.length)) (lists g e) (initLists 8 w)
      (SequentialPackedHaltMachine.accept (SequentialSpanRecompute.run g (bitWord w) e)) M T := by
  obtain ⟨Tl,hl⟩ := SequentialPackedBinaryLoader.runs w
  have hl' := hl.weaken (Q' := LenOK (space g e w.length)) (fun _ hh i => Nat.le_trans (hh i) (input_capacity g e w.length))
  obtain ⟨M,T,he⟩ := SequentialPackedHaltMachine.recognize_halts g (bitWord w) e
  have he' : Halts (LenOK (space g e w.length)) (SequentialPackedHaltMachine.recognize g e)
      (SequentialPackedInitMachine.input (SequentialCaptureCopyMachine.characters (bitWord w)))
      (SequentialPackedHaltMachine.accept (SequentialSpanRecompute.run g (bitWord w) e)) M T := by
    simpa only [space,bitWord,List.length_map] using he
  exact ⟨M,_,hl'.seqH he'⟩

theorem tape (g : MGrammar) (e : MExp) (w : List Bool) :
    ∃ t tau', Exec (TFits (space g e w.length)) (program g e) (initTapes 8 w) t
      (.stop (SequentialPackedHaltMachine.accept (SequentialSpanRecompute.run g (bitWord w) e)) tau') := by
  obtain ⟨ti,taui,_,hi,hrep⟩ := initP_spec (by decide : 1<8) w
  have hi' := hi.mono (fun _ hh => hh.mono (input_capacity g e w.length))
  obtain ⟨M,T,t,ht,he⟩ := lists_halts g e w
  obtain ⟨t',o,_,hex,hr⟩ := (compile_exec (fun _ h => h) he).1 taui hrep
  cases o with
  | cont tau' => exact False.elim hr
  | stop b tau' =>
    obtain ⟨hb,_⟩ := hr
    subst b
    exact ⟨ti+t',tau',.seqC hi' hex⟩

theorem recognizes {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder) (w : List Bool) :
    ∃ t b tau', Exec (TFits (space g e w.length)) (program g e) (initTapes 8 w) t (.stop b tau') ∧
      (b=true ↔ SObs g .callByValueSeq e (bitWord w) (some [])) := by
  obtain ⟨t,tau',hex⟩ := tape g e w
  exact ⟨t,_,tau',hex,SequentialPackedHaltMachine.answer_iff hg he (bitWord w)⟩

theorem finite_alphabet (g : MGrammar) (e : MExp) : ∃ na, 3 ≤ na ∧ (program g e).SymOK na := by
  obtain ⟨E,hE,hc⟩ := (lists g e).exists_constOK
  exact ⟨E+4,by omega,initP_symOK (by decide : 1<8) (E+4) (by omega),compile_symOK E _ hc⟩

/-- Standard binary input represents exactly the original a/b word. Loading,
initialization, evaluation, and the accepting/rejecting halt all fit linearly. -/
theorem machine {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder) :
    ∃ M : TM 8, M.Decides (fun w => SObs g .callByValueSeq e (bitWord w) (some [])) ∧ M.SpaceBounded (space g e) := by
  obtain ⟨na,hna,hs⟩ := finite_alphabet g e
  exact ⟨(program g e).machine na hna hs,
    (program g e).decides_of_exec na hna hs _ (space g e) (recognizes hg he)⟩

theorem space_linear_bound (g : MGrammar) (e : MExp) : ∃ C, ∀ n, space g e n ≤ C*(n+1) := by
  refine ⟨SequentialSharedStateBound.linearFactor g e+4,fun n => ?_⟩
  unfold space SequentialPackedLoopMachine.capacity
  simp only [Nat.add_mul,Nat.one_mul]
  omega

end Shallot.MacroPeg.CBV.SequentialPackedBinaryInputMachine
