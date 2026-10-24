import MacroPeg.CBV.CallLookahead
import MacroPeg.CBV.PrefixPairFusion

/-! Replay-test fusion with two common-origin captures represented by adjacent
Seq chunks. The template calls have two arguments, including inside recursion. -/
namespace Shallot.MacroPeg.CBV.PrefixPairTestFusion

def PairCalls : MExp → Prop
  | .call _ [a,b] => PairCalls a ∧ PairCalls b
  | .call _ _ => False
  | .seq a b | .alt a b => PairCalls a ∧ PairCalls b
  | .star a | .notP a => PairCalls a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => False

theorem render_commute (parallel : Bool) : ∀ e, PairCalls e →
    CallLookahead.render (PrefixPairFusion.render parallel e) =
      PrefixPairFusion.render parallel (CallLookahead.render e)
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => rfl
  | .param k, _ => by
    cases parallel <;> by_cases hk : k=1 <;>
      simp [PrefixPairFusion.render,CallLookahead.render,hk]
  | .call i [a,b], hf => by
    cases parallel <;>
      simp [PrefixPairFusion.render,CallLookahead.render,CallLookahead.renderArgs,MExp.andP,
        render_commute _ a hf.1,render_commute _ b hf.2]
  | .call _ [], hf | .call _ [_], hf | .call _ (_::_::_::_), hf => False.elim hf
  | .seq a b, hf | .alt a b, hf => by
    simp only [PrefixPairFusion.render,CallLookahead.render]
    rw [render_commute parallel a hf.1,render_commute parallel b hf.2]
  | .star a, hf | .notP a, hf => by
    simp only [PrefixPairFusion.render,CallLookahead.render]
    rw [render_commute parallel a hf]
  | .dbg _, hf | .lam _ _, hf | .callParam _ _, hf | .invoke _ _ _, hf => False.elim hf

def parGrammar (tails : List MExp) : MGrammar := CallLookahead.tested (PrefixPairFusion.parGrammar tails)
def seqGrammar (tails : List MExp) : MGrammar := PrefixPairFusion.seqGrammar (tails.map CallLookahead.render)
def source (e : MExp) : MExp := PrefixPairFusion.render true e
def translate (e : MExp) : MExp := PrefixPairFusion.render false (CallLookahead.render e)

theorem par_firstOrder (tails : List MExp) : (parGrammar tails).FirstOrder :=
  CallLookahead.tested_firstOrder (PrefixPairFusion.par_firstOrder tails)
theorem seq_firstOrder (tails : List MExp) : (seqGrammar tails).FirstOrder :=
  PrefixPairFusion.seq_firstOrder _
theorem translate_firstOrder (e : MExp) : (translate e).FirstOrder :=
  PrefixPairFusion.render_firstOrder _ _

theorem wrapped_pair {tails : List MExp} (hf : ∀ e ∈ tails, PairCalls e) :
    CallLookahead.wrapped (PrefixPairFusion.parGrammar tails) =
      PrefixPairFusion.parGrammar (tails.map CallLookahead.render) := by
  unfold CallLookahead.wrapped PrefixPairFusion.parGrammar
  simp only [List.map_map,Function.comp_def]
  apply congrArg MGrammar.mk
  apply List.map_congr_left
  intro e he
  simp only [CallLookahead.render]
  rw [render_commute true e (hf e he)]

/-- The Par source captures u and u++v at the same origin. The Seq target
captures u and v consecutively, reconstructs both source values inside the
test, and restores the caller's position after the test. -/
theorem observations_iff {tails : List MExp} (hf : ∀ e ∈ tails, PairCalls e)
    {e : MExp} (he : PairCalls e) (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar tails) .callByValuePar (source e) x r ↔
      SObs (seqGrammar tails) .callByValueSeq (translate e) x r := by
  have h1 := CallLookahead.observations_iff (PrefixPairFusion.par_firstOrder tails)
    (source e) (PrefixPairFusion.render_firstOrder true e) x r
  rw [wrapped_pair hf,show CallLookahead.render (source e) =
      PrefixPairFusion.render true (CallLookahead.render e) from render_commute true e he] at h1
  exact h1.trans (PrefixPairFusion.observations_iff _ _ x r)

theorem language_translation {tails : List MExp} (hf : ∀ e ∈ tails, PairCalls e)
    {e : MExp} (he : PairCalls e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (parGrammar tails) .callByValuePar (source e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar tails,translate e,seq_firstOrder tails,translate_firstOrder e,
    fun x => observations_iff hf he x (some [])⟩

end Shallot.MacroPeg.CBV.PrefixPairTestFusion
