import PalPeg.GalilScaffoldTopMatchedSeq

/-!
# Scan segments of the controller

`ScanSeg`: a run of the controller in scan mode consisting of waits (R not
available), counts (clock above one) and matched comparisons at clock one
whose chain stays watching and whose continuation cell is not the last.
It lifts to `Steps` of `galilFrameS` (with the clock bookkeeping) and
projects to `MatchedSeq`, hence — in `periodOnly` at lag zero — to the
lower layer's `OnlyMatchedRun`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

inductive ScanSeg (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) :
    ℕ → Control → GalilVM → Control → GalilVM → Prop
  | stop (c : Control) (s : GalilVM) : ScanSeg P q first delay 0 c s c s
  | wait (c : Control) (s s' : GalilVM) {n : ℕ} {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = false) (hn : ¬ canRight s.right)
      (hb : (galilFrameS P q first).background s s')
      (rest : ScanSeg P q first delay n c s' c' t) : ScanSeg P q first delay n c s c' t
  | count (c : Control) (s s' : GalilVM) {n : ℕ} {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = false) (ha : canRight s.right) (hc : 1 < c.clock)
      (hb : (galilFrameS P q first).background s s')
      (rest : ScanSeg P q first delay n {c with clock := c.clock - 1} s' c' t) :
      ScanSeg P q first delay n c s c' t
  | match (c : Control) (s : GalilVM) (vs : ScanVM) (vq : SearchVM) (o : Bool) {n : ℕ} {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = false) (ha : canRight s.right) (hc : c.clock = 1)
      (hcont : singlePositive s.cycle = false)
      (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
      (hmt : (galilFrame P q first).matched (scanLens.set s vs))
      (hwatch : ∃ w', vs.chain = .watch w')
      (hq : searchEffect P true s vq)
      (ho : refresh (galilFrame P q first) (afterCompare s vs vq) c.output o)
      (rest : ScanSeg P q first delay n {c with clock := delay, output := o, replaying := false}
        (afterCompare s vs vq) c' t) :
      ScanSeg P q first delay (n+1) c s c' t

/-- A scan segment is a run of `galilFrameS`. -/
theorem scanSeg_steps (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t) :
    ∃ k, Steps (galilFrameS P q first) delay k ⟨c, s⟩ ⟨c', t⟩ := by
  induction h with
  | stop c s => exact ⟨0, .zero _⟩
  | wait c s s' hm hr hn hb _ ih =>
    obtain ⟨k, hs⟩ := ih
    exact ⟨k+1, .succ (.scan_wait c s s' hm ⟨hr, hn⟩ hb) hs⟩
  | count c s s' hm hr ha hc hb _ ih =>
    obtain ⟨k, hs⟩ := ih
    exact ⟨k+1, .succ (.scan_count c s s' hm (Or.inr ha) hc hb) hs⟩
  | «match» c s vs vq o hm hr ha hc hcont hcmp hmt hwatch hq ho _ ih =>
    obtain ⟨k, hs⟩ := ih
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨w', hw'⟩ := hwatch
    have hne : s.chain ≠ .idle :=
      chainTick_source_ne_idle (compare_parts P q first hcmp hmatch).2.2 (by rw [hw']; intro h0; cases h0)
    exact ⟨k+1, .succ (scan_match_S P q first delay c s vs vq o hm hr ha hc hne hcmp hmt hq ho) hs⟩

/-- A scan segment projects to a matched sequence with the same number of
comparisons. -/
theorem scanSeg_matchedSeq (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t) :
    MatchedSeq P q first n s t := by
  induction h with
  | stop c s => exact .stop _
  | wait c s s' _ _ _ hb _ ih => exact .count s s' hb ih
  | count c s s' _ _ _ _ hb _ ih => exact .count s s' hb ih
  | «match» c s vs vq o _ _ ha _ hcont hcmp hmt hwatch hq _ _ ih =>
    exact .compare s vs vq ha hcont hcmp hmt hwatch hq ih

/-- Hence, in `periodOnly` at lag zero, an only-compare run of the lower layer. -/
theorem scanSeg_only (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t)
    (w : GalilScaffoldChainWatch.State) (hp : s.periodOnly = true) (hs : s.chain = .watch w)
    (hz : zero w.lag = true) :
    ∃ w' : GalilScaffoldChainWatch.State, t.chain = .watch w' ∧ zero w'.lag = true ∧
      t.periodOnly = true ∧ OnlyMatchedRun (toOnly s w) n (toOnly t w') :=
  matchedSeq_only P q first w (scanSeg_matchedSeq P q first delay h) hp hs hz

#print axioms scanSeg_steps
#print axioms scanSeg_only

end PalPeg.GalilScaffoldChainInputSupply
