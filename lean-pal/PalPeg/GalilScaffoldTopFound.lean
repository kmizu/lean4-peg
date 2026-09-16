import PalPeg.GalilScaffoldTopRestart
import PalPeg.GalilScaffoldTopChainEntry

/-!
# The found search starts the chain

In the transition whose search quantum ends in `found`, the background
calls `chain.start()` (the chain leaves `idle` for `copy` with the DP answer
tape, the centre place and the current radius) before the scan comparison,
whose match then credits the fresh chain (`prepEvents`' first event). The
comparison with that start is `compareFound` (`galilFrameS`).
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter

/-- A matched comparison whose quantum ends `found` on an idle chain: the
chain is started and credited. -/
theorem found_start_match (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control) (s : GalilVM)
    (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (hav : (galilFrame P q first).available s) (hidle : s.chain = .idle)
    (vq : SearchVM) (hq : searchEffect P true s vq) (hfound : vq.search.mode = .found)
    (hmt : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
      GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right s.right))
    (ch : ChainVM) (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre s) (P.place s) s.center s.radius) ch)
    (o : Bool)
    (ho : refresh (galilFrame P q first)
      (afterCompare s ⟨GalilScaffoldInputHead.left s.left, GalilScaffoldChainVerifier.right s.right, ch⟩ vq)
      c.output o) :
    Tick (galilFrameS P q first) delay ⟨c, s⟩
      ⟨{c with clock := delay, output := o, replaying := false},
        (afterCompare s ⟨GalilScaffoldInputHead.left s.left, GalilScaffoldChainVerifier.right s.right, ch⟩ vq)⟩ := by
  let vs : ScanVM := ⟨GalilScaffoldInputHead.left s.left, GalilScaffoldChainVerifier.right s.right, ch⟩
  have hmt' : (galilFrame P q first).matched (scanLens.set s vs) := by
    show GalilScaffoldInputHead.read (scanLens.get (scanLens.set s vs)).left =
      GalilScaffoldInputHead.read (scanLens.get (scanLens.set s vs)).right
    rw [scanLens.get_set]; exact hmt
  have hcmp : (galilFrameS P q first).compare s (afterCompare s vs vq) := by
    refine ⟨vs, vq, true, rfl, rfl, ⟨fun _ => hmt', fun _ => rfl⟩, hq, ?_, rfl⟩
    right; right
    refine ⟨hidle, by rw [decide_eq_true hfound], ?_⟩
    simpa using hch
  have hmt'' : (galilFrameS P q first).matched (afterCompare s vs vq) := hmt'
  have hpl : (galilFrameS P q first).matchedPlace c.replaying (afterCompare s vs vq)
      (afterCompare s vs vq) := by
    show afterCompare s vs vq = (if c.replaying then _ else afterCompare s vs vq)
    rw [hr]; simp
  have ht := Tick.scan_match (F := galilFrameS P q first) (delay := delay) c s _ _ o hm (Or.inr hav) hc
    hcmp hmt'' hpl ho
  rw [hr] at ht
  simpa using ht

#print axioms found_start_match

end PalPeg.GalilScaffoldChainInputSupply
