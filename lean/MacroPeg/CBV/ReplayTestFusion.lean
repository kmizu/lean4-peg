import MacroPeg.CBV.CallLookahead

/-! A direct Par-to-Seq transformation for recursive replay tests.
Source rules are F(x) <- &(x B); target rules are F(x) <- translated B,
and every translated call is under lookahead. The capture remains available,
while the enclosing lookahead restores the caller's original input position. -/
namespace Shallot.MacroPeg.CBV.ReplayTestFusion

def parGrammar (tails : List MExp) : MGrammar := CallLookahead.tested (ReplayFusion.parGrammar tails)
def seqGrammar (tails : List MExp) : MGrammar := ReplayFusion.seqGrammar (tails.map CallLookahead.render)
def translate (e : MExp) : MExp := CallLookahead.render e

theorem par_firstOrder {tails : List MExp} (hf : ∀ body ∈ tails, body.FirstOrder) :
    (parGrammar tails).FirstOrder := CallLookahead.tested_firstOrder (ReplayFusion.par_firstOrder hf)

theorem seq_firstOrder (tails : List MExp) : (seqGrammar tails).FirstOrder := by
  apply ReplayFusion.seq_firstOrder
  intro body hb
  obtain ⟨src,hsrc,rfl⟩ := List.mem_map.mp hb
  exact CallLookahead.render_firstOrder src

theorem translate_firstOrder (e : MExp) : (translate e).FirstOrder := CallLookahead.render_firstOrder e

theorem wrapped_replay (tails : List MExp) :
    CallLookahead.wrapped (ReplayFusion.parGrammar tails) =
      ReplayFusion.parGrammar (tails.map CallLookahead.render) := by
  simp [CallLookahead.wrapped,ReplayFusion.parGrammar,List.map_map,Function.comp_def,CallLookahead.render]

/-- One fixed first-order Seq grammar preserves all finite observations of
recursive replay-test rules on the original strings, with no totality premise. -/
theorem observations_iff {tails : List MExp} (hf : ∀ body ∈ tails, body.FirstOrder)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar tails) .callByValuePar e x r ↔
      SObs (seqGrammar tails) .callByValueSeq (translate e) x r := by
  have h1 := CallLookahead.observations_iff (ReplayFusion.par_firstOrder hf) e he x r
  rw [wrapped_replay] at h1
  apply h1.trans
  apply ReplayFusion.observations_iff
  · intro body hb
    obtain ⟨src,hsrc,rfl⟩ := List.mem_map.mp hb
    exact CallLookahead.render_firstOrder src
  · exact translate_firstOrder e

theorem recognizes_iff {tails : List MExp} (hf : ∀ body ∈ tails, body.FirstOrder)
    (e : MExp) (he : e.FirstOrder) (x : List Char) :
    SObs (parGrammar tails) .callByValuePar e x (some []) ↔
      SObs (seqGrammar tails) .callByValueSeq (translate e) x (some []) :=
  observations_iff hf e he x (some [])

/-- The result is an actual language-class inclusion for this source fragment,
not merely a comparison of executions of one unchanged grammar. -/
theorem language_translation {tails : List MExp} (hf : ∀ body ∈ tails, body.FirstOrder)
    {e : MExp} (he : e.FirstOrder) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (parGrammar tails) .callByValuePar e x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar tails,translate e,seq_firstOrder tails,translate_firstOrder e,recognizes_iff hf e he⟩

end Shallot.MacroPeg.CBV.ReplayTestFusion
