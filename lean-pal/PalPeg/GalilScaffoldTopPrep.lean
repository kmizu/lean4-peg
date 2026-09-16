import PalPeg.GalilScaffoldTopChainUnique

/-!
# The preparation phase on the controller

After the found comparison the chain is the credited `chainStart`. A
general scan run over the preparation ticks whose events are
`bs ++ dm :: cs` (copy, end, back) drives the chain — by determinism — to
exactly the `watchStart` state of `found_to_watchStart`, while the heads
follow `ScanEvents`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter

theorem prep_to_watch {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as0 : List Bool} {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as0 t y) (hs : s.mode = .run) (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (ver : GalilScaffoldInputHead.PlaceHead) (r0 : ℕ) (sm dm : Bool) :
    ∃ (h : ℕ) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate w lower h ∧ GalilScaffoldPlace.read p = some c ∧ ys.length + 1 = h ∧
      ∀ (delay : ℕ) (g g' : GScan) (as : List Bool) (bs cs : List Bool),
        bs.length = h → cs.length = h+1 →
        (if sm then ChainMatched (chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) g.chain
          else g.chain = chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) →
        GRun delay g as g' →
        (∀ events, events.length = as.length → ChainTicks events g.chain g'.chain →
          (∀ (raw : List (Fin 2)) (c0 r : ℕ), ScanEvents raw c0 r g.left g.right events g'.left g'.right) →
          events = bs ++ dm :: cs) →
        g'.chain = .watch (watchStart ver c ys b (GalilScaffoldChainCredits.run
          (GalilScaffoldChainCredits.start (ofNat (r0+1)))
          (GalilScaffoldChainCredits.prepEvents sm dm bs cs))) := by
  obtain ⟨h, c, ys, b, hcand, hread, hlen, hrest⟩ := found_to_watchStart p hw hr hs ht hv ver r0 sm dm
  refine ⟨h, c, ys, b, hcand, hread, hlen, ?_⟩
  intro delay g g' as bs cs hbs hcs hstart hrun hev
  obtain ⟨events, hlen', hchain, hscan⟩ := grun_events hrun
  have hevents := hev events hlen' hchain hscan
  subst hevents
  obtain ⟨x1, hx1, hticks⟩ := hrest bs cs hbs hcs
  -- the credited start is unique, so `g.chain = x1`
  have hg : g.chain = x1 := by
    cases sm
    · simp only [Bool.false_eq_true, ite_false] at hstart hx1
      rw [hstart, hx1]
    · simp only [ite_true] at hstart hx1
      exact chainMatched_unique hstart hx1
  rw [hg] at hchain
  exact chainTicks_unique hchain hticks

#print axioms prep_to_watch

end PalPeg.GalilScaffoldChainInputSupply
