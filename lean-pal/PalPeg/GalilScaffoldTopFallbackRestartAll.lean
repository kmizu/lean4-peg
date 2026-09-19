import PalPeg.GalilScaffoldTopFallbackAll

/-!
# The fallback cycle lands in a restarted state, with every state sound

`fallback_restarted_All` is `fallback_restarted` with the run carrying any
predicate that holds off scan mode and at the two scan endpoints, and with
the re-entry refresh clause when the chosen radius is `0`.
`fallback_restarted_soundNR` instantiates it with `SoundScanNR`: in scan
mode and not replaying, the output is sound with respect to the right head.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- Output sound in scan mode when not replaying. -/
def SoundScanNR (raw : List (Fin 2)) (st : State GalilVM) : Prop :=
  st.ctl.mode = .scan → st.ctl.replaying = false → OutputRel raw st.ctl st.vm

theorem soundScanNR_of_soundScan (raw : List (Fin 2)) (st : State GalilVM) (h : SoundScan raw st) :
    SoundScanNR raw st := fun hm _ => h hm

theorem fallback_restarted_All (onLetter leftFirst : GalilVM → Prop) (rs : GalilVM → GalilVM → Prop)
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
    {raw : List (Fin 2)} (hrep : GalilScaffoldInputTrace.Represents (right s.right).head raw)
    (hfoc : (right s.right).head.focus ≠ none)
    (hcan : Canonical s.length) (ℓ : ℕ) (hv : value s.length = ℓ)
    (heven : ∀ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' →
      ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length % 2 = 0) :
    ∃ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' ∧
      raw = (a :: xs).reverse ++ rs' ++ q' ∧
      ∃ (n : ℕ) (o : Bool) (t : GalilVM),
        (∀ Q : State GalilVM → Prop, (∀ st : State GalilVM, st.ctl.mode ≠ .scan → Q st) → Q ⟨c, s⟩ →
          Q ⟨{c with mode := .scan, clock := delay, output := o, replaying := decide (0 < chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))), odd := oddAt false (((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length - (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))+1)), pair := pairAt (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))}, t⟩ →
          StepsAll (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first) delay Q (1 + (n+1)) ⟨c, s⟩
            ⟨{c with mode := .scan, clock := delay, output := o, replaying := decide (0 < chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))), odd := oddAt false (((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length - (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))+1)), pair := pairAt (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))}, t⟩) ∧
        Restarted raw t 0 reset ∧
        t.replay = ofNat (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        position t.center = position (right s.right) - chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)) ∧
        Manacher.PalAt (encoded raw) (position (right s.right) - chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))
          (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        (∀ r', 2*r'+1 ≤ ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length →
          Manacher.PalAt (encoded raw) (position (right s.right) - r') r' →
          r' ≤ chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)) = 0 →
          (onLetter t → (o = true ↔ leftFirst t)) ∧ (¬ onLetter t → o = c.output)) := by
  -- the fallback's choice on the encoded word
  let w0 : GalilScaffoldChainWatch.State :=
    ⟨⟨right s.right, GalilScaffoldChainConsume.ready 0 [] 0⟩, reset, reset⟩
  obtain ⟨a, xs, rs', q', hdec, hraw, hpal, hmax, h, hmoves, hhrep, hhfoc, hhpos, _⟩ :=
    fallback_replay (⟨s.center, s.left, right s.right, w0, s.cycle, s.radius⟩ : OnlyCompareState)
      hrep hfoc s.length hcan ℓ hv
  refine ⟨a, xs, rs', q', hdec, hraw, ?_⟩
  -- the fallback cycle on the controller
  obtain ⟨n, o, t, hst, hl', hR, hC, hrep', hrad, hlen, hw, hprog, hi', ho, ho0, hsearch, hlower⟩ :=
    scan_fallback_cycle_All onLetter leftFirst rs centre place entry q hq0 first h7 h8 delay c hm hr hc s hi hav
      vs vq hl hrr hmis hq hch hg ⟨a :: xs,(right s.right).gap⟩ hcan ℓ hv (stream_ne_nil _ _ _)
      (by
        have hpos : position (right s.right)
            = (GalilScaffoldPlace.stream ⟨a :: xs, (right s.right).gap⟩).length := by
          have h0 : (right s.right)
              = represent ⟨a :: xs, (right s.right).gap⟩ (rs'.map some) q' := hdec
          conv_lhs => rw [h0]
          exact position_represent a xs (right s.right).gap (rs'.map some) q'
        omega) (heven a xs rs' q' hdec)
  have hh : GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))]
      (right s.right) = h := (leftMoves_eq hmoves).symm
  rw [hh] at hl' hR hC
  refine ⟨n, o, t, hst, ?_, hrep', ?_, hpal, hmax, ho0⟩
  · refine ⟨hw, ?_, ?_, ?_, ?_, ?_, ?_, hlower, ofNat_canonical 0, by rw [reset_eq_ofNat, ofNat_value]; simp⟩
    · rw [hC]; exact hhrep
    · rw [hC]; exact hhfoc
    · rw [hC, hl', hR]; exact scan_initial raw h hhrep hhfoc
    · rw [hrad, reset_eq_ofNat]; exact ⟨ofNat_canonical 0, ofNat_value 0⟩
    · rw [hlen]; exact ofNat_canonical 1
    · rw [hsearch, hrad]
  · rw [hC]; exact hhpos


theorem fallback_restarted_soundNR (onLetter leftFirst : GalilVM → Prop) (rs : GalilVM → GalilVM → Prop)
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
    {raw : List (Fin 2)} (hrep : GalilScaffoldInputTrace.Represents (right s.right).head raw)
    (hfoc : (right s.right).head.focus ≠ none)
    (hcan : Canonical s.length) (ℓ : ℕ) (hv : value s.length = ℓ)
    (heven : ∀ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' →
      ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length % 2 = 0)
    (honL : onLetter = onLetterVM raw) (hlF : leftFirst = leftFirstVM) (hout : OutputRel raw c s) :
    ∃ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' ∧
      raw = (a :: xs).reverse ++ rs' ++ q' ∧
      ∃ (n : ℕ) (o : Bool) (t : GalilVM),
        StepsAll (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first) delay (SoundScanNR raw) (1 + (n+1)) ⟨c, s⟩
          ⟨{c with mode := .scan, clock := delay, output := o, replaying := decide (0 < chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))), odd := oddAt false (((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length - (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))+1)), pair := pairAt (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))}, t⟩ ∧
        Restarted raw t 0 reset ∧
        t.replay = ofNat (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        position t.center = position (right s.right) - chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)) := by
  obtain ⟨a, xs, rs', q', hdec, hraw, n, o, t, hstA, hRst, hrep', hpos, _, _, ho0⟩ :=
    fallback_restarted_All onLetter leftFirst rs centre place entry q hq0 first h7 h8 delay c hm hr hc s hi hav
      vs vq hl hrr hmis hq hch hg hrep hfoc hcan ℓ hv heven
  refine ⟨a, xs, rs', q', hdec, hraw, n, o, t, hstA (SoundScanNR raw) (fun st hns hsc => absurd hsc hns)
    (fun _ _ => hout) ?_, hRst, hrep', hpos⟩
  intro _ hrepl
  have hr0 : chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)) = 0 := by
    simp at hrepl; omega
  obtain ⟨_, _, _, hscan, _⟩ := hRst
  intro hout' k hk hk2 hrk
  refine output_sound raw t c.output o hscan k hk hk2 hrk ?_ hout'
  have := ho0 hr0
  rw [honL, hlF] at this
  exact this

#print axioms fallback_restarted_All
#print axioms fallback_restarted_soundNR

end PalPeg.GalilScaffoldChainInputSupply
