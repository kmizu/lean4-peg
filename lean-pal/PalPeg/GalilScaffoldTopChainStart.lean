import PalPeg.GalilScaffoldTopChain

/-!
# From the found search to the watching chain

`found_start_back` (lower layer) turns a found DP search on the reversed
window at the centre place `p` into the `Copy` walk over the unary answer,
the tail mark, and the `Back` walk to the front mark. On `ChainVM` this is
`chainStart` followed by `h` copy steps, the copy end, and `h+1` back steps,
ending in `watch` with control `ready c ys b` (the `ys ++ [b]` semiperiod),
`lag = radius`, `margin = radius - 4h` (no scan credits interleaved here).
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter

theorem found_to_watch {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (ver : GalilScaffoldInputHead.PlaceHead) (radius : Counter) :
    ∃ (h : ℕ) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3) (q : GalilScaffoldPlace.Place),
      GalilDpCorrect.Candidate w lower h ∧ GalilScaffoldPlace.read p = some c ∧
      ys ++ [b] = ((GalilScaffoldPlace.stream p).drop 1).take h ∧
      ChainSteps (h + (h + 1 + 1)) (chainStart (y.config.tapes 11) c p ver radius)
        (.watch ⟨⟨ver, GalilScaffoldChainConsume.ready c ys b⟩, radius,
          GalilScaffoldChainCredits.decFour^[h] radius⟩) := by
  obtain ⟨h, c, u, q, ys, b, hcand, hread, hcopy, hu, hpos, hfocus, hback, hys, _⟩ :=
    GalilScaffoldChainPeriod.found_start_back p hw hr hs ht hv
  refine ⟨h, c, ys, b, q, hcand, hread, hys, ?_⟩
  have h1 := copy_steps h radius radius ver hcopy
  have h2 : ChainStep (.copy u (ofNat h) q (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start c) (ys ++ [b]))
      radius (GalilScaffoldChainCredits.decFour^[h] radius) ver)
      (.back (GalilScaffoldChainPeriod.write (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start c) (ys ++ [b])) (.last b))
        (ofNat h) radius (GalilScaffoldChainCredits.decFour^[h] radius) ver) :=
    .copyEnd _ _ _ _ _ _ _ b hu hpos hfocus
  have h3 := back_steps (h+1) (ofNat h) radius (GalilScaffoldChainCredits.decFour^[h] radius) ver hback
  exact chainSteps_trans h1 (.succ h2 h3)

#print axioms found_to_watch

end PalPeg.GalilScaffoldChainInputSupply
