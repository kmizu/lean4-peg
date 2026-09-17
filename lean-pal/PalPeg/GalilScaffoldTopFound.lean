import PalPeg.GalilScaffoldTopRestart
import PalPeg.GalilScaffoldTopChainEntry

/-!
# The found search starts the chain

In the transition whose search quantum ends in `found`, the background
calls `chain.start()` (the chain leaves `idle` for `copy` with the DP answer
tape, the centre place and the current radius) before the scan comparison,
whose match then credits the fresh chain (`prepEvents`' first event). The
comparison with that start is `compareFound` (`galilFrameS`).

`chain.start()` also clears `periodOnly` and resets `cycle` (`M-periodOnly`),
so the state after the tick is the *birth-adjusted* comparison state
`afterBirth true (afterCompare …)`; `afterBirth` only rewrites those two
fields, so the heads, the chain and the search are the ones of `afterCompare`.
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
      (afterBirth true
        (afterCompare s ⟨GalilScaffoldInputHead.left s.left, GalilScaffoldChainVerifier.right s.right, ch⟩ vq))
      c.output o) :
    Tick (galilFrameS P q first) delay ⟨c, s⟩
      ⟨{c with clock := delay, output := o, replaying := false},
        (afterBirth true
          (afterCompare s ⟨GalilScaffoldInputHead.left s.left, GalilScaffoldChainVerifier.right s.right, ch⟩ vq))⟩ := by
  let vs : ScanVM := ⟨GalilScaffoldInputHead.left s.left, GalilScaffoldChainVerifier.right s.right, ch⟩
  have hborn : chainBorn (decide (vq.search.mode = .found)) s.chain = true := by
    unfold chainBorn; rw [hidle, decide_eq_true hfound]; rfl
  have hmt' : (galilFrame P q first).matched (scanLens.set s vs) := by
    show GalilScaffoldInputHead.read (scanLens.get (scanLens.set s vs)).left =
      GalilScaffoldInputHead.read (scanLens.get (scanLens.set s vs)).right
    rw [scanLens.get_set]; exact hmt
  have hcmp : (galilFrameS P q first).compare s (afterBirth true (afterCompare s vs vq)) := by
    refine ⟨vs, vq, true, rfl, rfl, ⟨fun _ => hmt', fun _ => rfl⟩, hq, ?_, ?_⟩
    · right; right
      refine ⟨hidle, by rw [decide_eq_true hfound], ?_⟩
      simpa using hch
    · rw [hborn]
      rfl
  have hmt'' : (galilFrameS P q first).matched (afterBirth true (afterCompare s vs vq)) := hmt'
  have hpl : (galilFrameS P q first).matchedPlace c.replaying (afterBirth true (afterCompare s vs vq))
      (afterBirth true (afterCompare s vs vq)) := by
    show afterBirth true (afterCompare s vs vq)
      = (if c.replaying then _ else afterBirth true (afterCompare s vs vq))
    rw [hr]; simp
  have ht := Tick.scan_match (F := galilFrameS P q first) (delay := delay) c s _ _ o hm (Or.inr hav) hc
    hcmp hmt'' hpl ho
  rw [hr] at ht
  simpa using ht

#print axioms found_start_match

/-- `afterBirth` rewrites only `periodOnly` and `cycle`, and the output refresh
reads the heads, so it transports across a birth. -/
theorem refresh_afterBirth (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (b : Bool) (t : GalilVM)
    (old o : Bool) :
    refresh (galilFrame P q first) (afterBirth b t) old o ↔
      refresh (galilFrame P q first) t old o := by
  have hon : (galilFrame P q first).onLetter (afterBirth b t)
      = (galilFrame P q first).onLetter t := by
    show P.onLetter (afterBirth b t) = P.onLetter t
    rw [hP]
    unfold onLetterVM
    rw [afterBirth_right]
  have hlf : (galilFrame P q first).leftFirst (afterBirth b t)
      = (galilFrame P q first).leftFirst t := by
    show P.leftFirst (afterBirth b t) = P.leftFirst t
    rw [hP']
    unfold leftFirstVM
    rw [afterBirth_left]
  unfold refresh
  rw [hon, hlf]

#print axioms refresh_afterBirth

end PalPeg.GalilScaffoldChainInputSupply
