import PalPeg.GalilScaffoldTopFallbackS

/-!
# The fallback cycle on `galilFrameS`

A mismatching comparison with the chain idle (so the shift guard fails)
enters the fallback (`beginFallback`: the FPP is prepared, the chain and the
search are dropped), and `fallback_to_scan_S` brings the controller back to
scan mode with the heads on the chosen centre and the replay of its radius.
On `galilFrameS` the comparison also carries the search's step (with the
chain start recorded in `chainAt` when that step lands in `found`; the
fallback drops it again).
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

theorem afterMismatch_fpp (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : (afterMismatch s vs vq).fpp = s.fpp := rfl
theorem afterMismatch_remaining (s : GalilVM) (vs : ScanVM) (vq : SearchVM) :
    (afterMismatch s vs vq).remaining = s.remaining := rfl

/-- The mismatch target with the chain birth applied (`M-periodOnly`): the Scala
`ScaffoldChain.start()` clears `periodOnly` and resets `cycle`, so a mismatch that
starts a chain must carry that change. -/
def afterMismatchB (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : GalilVM :=
  afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain)
    (afterMismatch s vs vq)

/-- 不一致（と chain 誕生）の後の walker は search 量子のもの
（`searchLens` が `walker` を運ぶ）。 -/
theorem afterMismatchB_walker (s : GalilVM) (vs : ScanVM) (vq : SearchVM) :
    (afterMismatchB s vs vq).walker = vq.walker := by
  unfold afterMismatchB
  rw [afterBirth_walker]
  rfl

theorem afterMismatchB_left (s : GalilVM) (vs : ScanVM) (vq : SearchVM) :
    (afterMismatchB s vs vq).left = (afterMismatch s vs vq).left := afterBirth_left _ _
theorem afterMismatchB_right (s : GalilVM) (vs : ScanVM) (vq : SearchVM) :
    (afterMismatchB s vs vq).right = (afterMismatch s vs vq).right := afterBirth_right _ _
theorem afterMismatchB_length (s : GalilVM) (vs : ScanVM) (vq : SearchVM) :
    (afterMismatchB s vs vq).length = (afterMismatch s vs vq).length := afterBirth_length _ _
theorem afterMismatchB_remaining (s : GalilVM) (vs : ScanVM) (vq : SearchVM) :
    (afterMismatchB s vs vq).remaining = s.remaining :=
  (afterBirth_remaining _ _).trans (afterMismatch_remaining s vs vq)
theorem afterMismatchB_fpp (s : GalilVM) (vs : ScanVM) (vq : SearchVM) :
    (afterMismatchB s vs vq).fpp = (afterMismatch s vs vq).fpp := afterBirth_fpp _ _

/-- **The birth reset never turns the shift guard on.**  If the source chain is
active the reset is the identity (`afterBirth_of_ne_idle`); if it is idle then
`chainAt` leaves `vs.chain` either `.idle` or a freshly started `.copy`
(`chainStart` is a `.copy`), and `shiftGuardVM` demands a `.watch`. -/
theorem not_shiftGuard_afterMismatchB {s : GalilVM} {vs : ScanVM} {vq : SearchVM}
    (answer : GalilScaffoldTape.Tape) (cc : Fin 3) (walker : GalilScaffoldPlace.Place)
    (ver : PlaceHead) (radius : Counter)
    (hch : chainAt false (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found))
      answer cc walker ver radius s.chain vs.chain)
    (hg : ¬ shiftGuardVM (afterMismatch s vs vq)) :
    ¬ shiftGuardVM (afterMismatchB s vs vq) := by
  unfold afterMismatchB
  by_cases hne : s.chain = ChainVM.idle
  · rintro ⟨w, hw, -⟩
    rw [afterBirth_chain, afterMismatch_chain] at hw
    rcases hch with ⟨hne', -⟩ | ⟨-, -, hz⟩ | ⟨-, -, hz⟩
    · exact hne' hne
    · rw [hz] at hw; exact ChainVM.noConfusion hw
    · rw [if_neg (by decide), chainStart] at hz
      rw [hz] at hw; exact ChainVM.noConfusion hw
  · rw [afterBirth_of_ne_idle hne]
    exact hg

theorem scan_fallback_cycle_S (onLetter leftFirst : GalilVM → Prop) (rs : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (hq0 : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8) (delay : ℕ)
    (c : Control) (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (s : GalilVM) (hi : ShiftIdle s) (hav : canRight s.right)
    (vs : ScanVM) (vq : SearchVM) (hl : vs.left = left s.left) (hrr : vs.right = right s.right)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hq : searchEffect (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry)
      false s vq)
    (hch : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11) (centre s) (place s)
      s.center s.radius s.chain vs.chain)
    (hg : ¬ shiftGuardVM (afterMismatch s vs vq))
    (p : GalilScaffoldPlace.Place)
    (hcan : Canonical s.length) (ℓ : ℕ) (hv : value s.length = ℓ)
    (hne : (GalilScaffoldPlace.stream p) ≠ []) (hpw : (GalilScaffoldPlace.stream p).length ≤ position (right s.right))
    (heven : ((GalilScaffoldPlace.stream p).take (ℓ+1)).length % 2 = 0) :
    ∃ (n : ℕ) (o : Bool) (t : GalilVM),
      Steps (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first)
        delay (1 + (n+1)) ⟨c, s⟩
        ⟨{c with mode := .scan, clock := delay, output := o, replaying := decide (0 < chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1))), odd := oddAt false (((GalilScaffoldPlace.stream p).take (ℓ+1)).length - (2*chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1))+1)), pair := pairAt (2*chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1)))}, t⟩ ∧
      t.left = GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1))] (right s.right) ∧
      t.right = GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1))] (right s.right) ∧
      t.center = GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1))] (right s.right) ∧
      t.replay = ofNat (chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1))) ∧ t.radius = reset ∧
      t.length = ofNat 1 ∧ t.chain = .idle ∧
      t.fpp.program = GalilScaffoldControl.reset 320 t.fpp.program ∧ ShiftIdle t ∧
      (0 < chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1)) → o = c.output) ∧
      t.search = GalilScaffoldSearchFinish.begin reset reset ∧ t.lower = reset := by
  -- the mismatch tick
  have hmis' : ¬ (galilFrame (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first).matched
      (scanLens.set s vs) := by
    intro h0
    apply hmis
    have h1 : read (scanLens.get (scanLens.set s vs)).left = read (scanLens.get (scanLens.set s vs)).right := h0
    rw [scanLens.get_set] at h1
    have h2 : read vs.left = read vs.right := h1
    rw [hl, hrr] at h2
    exact h2
  have hcmpS : (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first).compare
      s (afterMismatchB s vs vq) :=
    ⟨vs, vq, false, hl, hrr, Iff.intro (fun h0 => by cases h0) (fun h0 => absurd h0 hmis'), hq, hch, rfl⟩
  have hmisS : ¬ (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first).matched
      (afterMismatchB s vs vq) := by
    intro h0
    apply hmis
    have h1 : read (afterMismatchB s vs vq).left = read (afterMismatchB s vs vq).right := h0
    rw [afterMismatchB_left, afterMismatchB_right, afterMismatch_left, afterMismatch_right, hl, hrr] at h1
    exact h1
  have hav' : (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first).available s := hav
  have ht1 : Tick (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first) delay ⟨c, s⟩
      ⟨{c with clock := delay, mode := .copy},
        {afterMismatchB s vs vq with fpp := FppControl.beginFallback (afterMismatchB s vs vq).fpp.program p (afterMismatchB s vs vq).length, chain := .idle, search := {(afterMismatchB s vs vq).search with mode := .idle}}⟩ :=
    .scan_fallback c s _ _ hm (Or.inr hav') hc hcmpS hmisS
      (Or.inr (not_shiftGuard_afterMismatchB _ _ _ _ _ hch hg)) hr ⟨p, rfl, by rw [afterMismatchB_right, afterMismatch_right, hrr]; exact hpw⟩
  have hm2 : ({c with clock := delay, mode := .copy} : Control).mode = .copy := rfl
  have hi2 : ShiftIdle {afterMismatchB s vs vq with fpp := FppControl.beginFallback (afterMismatchB s vs vq).fpp.program p (afterMismatchB s vs vq).length, chain := .idle, search := {(afterMismatchB s vs vq).search with mode := .idle}} := by
    rw [shiftIdle_iff] at hi ⊢
    show positive (afterMismatchB s vs vq).remaining = false
    rw [afterMismatchB_remaining]
    exact hi
  have hcan' : Canonical (afterMismatchB s vs vq).length := by rw [afterMismatchB_length, afterMismatch_length]; exact hcan
  have hv' : value (afterMismatchB s vs vq).length = ℓ := by rw [afterMismatchB_length, afterMismatch_length]; exact hv
  obtain ⟨n, o, t, hst, hl', hR, hC, hrep, hrad, hlen, hw, hprog, hi', ho, hsearch, hlower, _⟩ :=
    fallback_to_scan_S onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry q hq0 first
      h7 h8 delay _ hm2 _ hi2 (afterMismatchB s vs vq).fpp.program p (afterMismatchB s vs vq).length hcan' ℓ hv'
      rfl hne heven
  have hright : ({afterMismatchB s vs vq with fpp := FppControl.beginFallback (afterMismatchB s vs vq).fpp.program p (afterMismatchB s vs vq).length, chain := .idle, search := {(afterMismatchB s vs vq).search with mode := .idle}} : GalilVM).right = right s.right := by
    show (afterMismatchB s vs vq).right = _
    rw [afterMismatchB_right, afterMismatch_right, hrr]
  rw [hright] at hl' hR hC
  exact ⟨n, o, t, steps_trans (.succ ht1 (.zero _)) hst, hl', hR, hC, hrep, hrad, hlen, hw, hprog, hi', ho, hsearch, hlower⟩

#print axioms scan_fallback_cycle_S

end PalPeg.GalilScaffoldChainInputSupply
