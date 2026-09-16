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
    (hne : (GalilScaffoldPlace.stream p) ≠ [])
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
      s (afterMismatch s vs vq) :=
    ⟨vs, vq, false, hl, hrr, Iff.intro (fun h0 => by cases h0) (fun h0 => absurd h0 hmis'), hq, hch, rfl⟩
  have hmisS : ¬ (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first).matched
      (afterMismatch s vs vq) := by
    intro h0
    apply hmis
    have h1 : read (afterMismatch s vs vq).left = read (afterMismatch s vs vq).right := h0
    rw [afterMismatch_left, afterMismatch_right, hl, hrr] at h1
    exact h1
  have hav' : (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first).available s := hav
  have ht1 : Tick (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first) delay ⟨c, s⟩
      ⟨{c with clock := delay, mode := .copy},
        {afterMismatch s vs vq with fpp := FppControl.beginFallback (afterMismatch s vs vq).fpp.program p (afterMismatch s vs vq).length, chain := .idle, search := {(afterMismatch s vs vq).search with mode := .idle}}⟩ :=
    .scan_fallback c s _ _ hm (Or.inr hav') hc hcmpS hmisS (Or.inr hg) hr ⟨p, rfl⟩
  have hm2 : ({c with clock := delay, mode := .copy} : Control).mode = .copy := rfl
  have hi2 : ShiftIdle {afterMismatch s vs vq with fpp := FppControl.beginFallback (afterMismatch s vs vq).fpp.program p (afterMismatch s vs vq).length, chain := .idle, search := {(afterMismatch s vs vq).search with mode := .idle}} := by
    rw [shiftIdle_iff] at hi ⊢
    exact hi
  have hcan' : Canonical (afterMismatch s vs vq).length := by rw [afterMismatch_length]; exact hcan
  have hv' : value (afterMismatch s vs vq).length = ℓ := by rw [afterMismatch_length]; exact hv
  obtain ⟨n, o, t, hst, hl', hR, hC, hrep, hrad, hlen, hw, hprog, hi', ho, hsearch, hlower, _⟩ :=
    fallback_to_scan_S onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry q hq0 first
      h7 h8 delay _ hm2 _ hi2 (afterMismatch s vs vq).fpp.program p (afterMismatch s vs vq).length hcan' ℓ hv'
      rfl hne heven
  have hright : ({afterMismatch s vs vq with fpp := FppControl.beginFallback (afterMismatch s vs vq).fpp.program p (afterMismatch s vs vq).length, chain := .idle, search := {(afterMismatch s vs vq).search with mode := .idle}} : GalilVM).right = right s.right := by
    show (afterMismatch s vs vq).right = _
    rw [afterMismatch_right, hrr]
  rw [hright] at hl' hR hC
  exact ⟨n, o, t, steps_trans (.succ ht1 (.zero _)) hst, hl', hR, hC, hrep, hrad, hlen, hw, hprog, hi', ho, hsearch, hlower⟩

#print axioms scan_fallback_cycle_S

end PalPeg.GalilScaffoldChainInputSupply
