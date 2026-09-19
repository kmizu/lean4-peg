import PalPeg.GalilTickFair
import PalPeg.PackedRun
import PalPeg.ShapedRun
import PalPeg.GalilLeafFb
/-!
# Canonical fallback and the fresh restart used by the cycle oracle

The existing costed phase run is polymorphic in its off-scan invariant.
Instantiate it with “off scan or the final state” to recover both scheduling
contracts, then select the actual right-head copy origin. Replay is separate.
-/
set_option autoImplicit false
namespace PalPeg.CanonicalFallback
open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton
open PalPeg.GalilTickFair PalPeg.ShapedRun

/-- The existing fallback run is polymorphic in its off-scan invariant.
Its only scan state is the fresh exit, so both scheduling refinements follow. -/
theorem exit_refine {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} {n : ℕ} {x y last : State GalilVM}
    (h : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (fun z => z.ctl.mode ≠ .scan ∨ z = last) n x y)
    (hRest : Restarted raw last.vm 0 GalilScaffoldCounter.reset)
    (hMode : last.ctl.mode = .scan) (hClock : last.ctl.clock = 2048)
    (hSound : SoundScanNR raw last) :
    StepsAllR (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) (OracleTick entry raw) n x y ∧
    ShapedSteps centre place entry q first raw n x y := by
  have sound : ∀ z : State GalilVM, (z.ctl.mode ≠ .scan ∨ z = last) → SoundScanNR raw z := by
    intro z hz
    rcases hz with hm | rfl
    · exact fun hm' => (hm hm').elim
    · exact hSound
  induction h with
  | zero x hx => exact ⟨.zero x (sound x hx), .zero x⟩
  | @succ n x y z hx ht hrest ih =>
    have hy := stepsAll_head hrest
    have hnr : x.ctl.mode = .scan → ¬ restartVM entry x.vm y.vm := by
      intro hm hr
      have he : x = last := hx.resolve_left (by simpa using hm)
      obtain ⟨w, hw, _⟩ := hr
      rw [he, hRest.1] at hw
      cases hw
    have hpin : x.ctl.mode = .scan → y.ctl.mode = .copy →
        y.vm.fpp.walker = rightPlace y.vm := by
      intro hm hm'
      have he : x = last := hx.resolve_left (by simpa using hm)
      have hc : x.ctl.clock = 2048 := he ▸ hClock
      cases ht <;> simp_all
    have hng : x.ctl.mode = .scan → ¬ restartGuardVM x.vm := by
      rintro hm ⟨w, hw, -⟩
      have he : x = last := hx.resolve_left (by simpa using hm)
      rw [he, hRest.1] at hw
      cases hw
    have hcan : Canonical entry 2048 x y :=
      ⟨fun hm hg => absurd hg (hng hm), hpin, keepsSearchCursor_of_tick ht⟩
    have hrs : x.ctl.mode = .replayStart →
        Restarted raw y.vm 0 GalilScaffoldCounter.reset ∧ y.ctl.mode = .scan ∧ y.ctl.clock = 2048 := by
      intro hm
      obtain ⟨t, o, hi, ho, ho0, he⟩ := tick_replayStart_cases hm ht
      have hscan : y.ctl.mode = .scan := by rw [he]
      have hylast : y = last := hy.resolve_left (by simpa using hscan)
      rw [hylast]
      exact ⟨hRest, hMode, hClock⟩
    exact ⟨.succ (sound x hx) ht ⟨hcan, fun hm hr => (hnr hm hr).elim, hrs⟩ ih.1,
      .succ ht (fun hm hr => (hnr hm hr).elim) hrs ih.2⟩

open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilStructuredSkeleton

/-- Facts needed by the oracle's replay continuation, all about the same exit. -/
structure Landing (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (x y : State GalilVM)
    (ℓ radius ticks : ℕ) : Prop where
  run : StepsAllR (galilFrameS (PofC centre place entry raw) q first) 2048
    (SoundScanNR raw) (OracleTick entry raw) ticks x y
  shaped : ShapedSteps centre place entry q first raw ticks x y
  cost : ticks ≤ 1588*(ℓ+1)+836
  mode : y.ctl.mode = .scan
  clock : y.ctl.clock = 2048
  replaying : y.ctl.replaying = decide (0 < radius)
  restarted : Restarted raw y.vm 0 reset
  replay : y.vm.replay = ofNat radius
  right : y.vm.right = GalilScaffoldInputHead.left^[radius] x.vm.right
  center : y.vm.center = y.vm.right
  length : y.vm.length = ofNat 1
  idle : ShiftIdle y.vm
  refreshed : radius = 0 → Refreshed (PofC centre place entry raw) q first y

/-- Reuse the existing costed fallback.  Its semantic rewind head suffices to
supply the restart invariant; no primitive phase proof is duplicated. -/
theorem to_scan {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} (hq : 0 < q) (h7 : first ≠ 7) (h8 : first ≠ 8)
    (c : Control) (hm : c.mode = .copy) (s : GalilVM) (hi : ShiftIdle s)
    (old : GalilScaffoldControl.Machine 9) (p : GalilScaffoldPlace.Place)
    (len : Counter) (hc : GalilScaffoldCounter.Canonical len) (ℓ : ℕ) (hv : value len = ℓ)
    (hs : s.fpp = FppControl.beginFallback old p len)
    (hne : GalilScaffoldPlace.stream p ≠ [])
    (heven : ((GalilScaffoldPlace.stream p).take (ℓ+1)).length % 2 = 0)
    (hRep : GalilScaffoldInputTrace.Represents
      (GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1))] s.right).head raw)
    (hPresent : (GalilScaffoldInputHead.left^[chosenRadius
      ((GalilScaffoldPlace.stream p).take (ℓ+1))] s.right).head.focus ≠ none) :
    ∃ ticks y, Landing centre place entry q first raw ⟨c,s⟩ y ℓ
      (chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1))) ticks := by
  let win := (GalilScaffoldPlace.stream p).take (ℓ+1)
  let r := chosenRadius win
  obtain ⟨n,o,t,hRun,hCost,hL,hR,hC,hReplay,hRad,hLen,hChain,hProg,hIdle,hOut,hOut0,hSearch,hLower,_⟩ :=
    PalPeg.GalilLeafFb.fallback_to_scan_All_le (onLetterVM raw) leftFirstVM
      shiftGuardVM beginShiftVM' beginFallbackVM' (restartVM entry) centre place entry
      q hq first h7 h8 2048 c hm s hi old p len hc ℓ hv hs hne heven
  let y : State GalilVM := ⟨{c with mode := .scan, clock := 2048, output := o, replaying := decide (0 < r), odd := oddAt false (win.length-(2*r+1)), pair := pairAt (2*r)},t⟩
  have hRest : Restarted raw t 0 reset := by
    refine ⟨hChain, ?_, ?_, ?_, ?_, ?_, ?_, hLower, ofNat_canonical 0,
      by rw [reset_eq_ofNat, ofNat_value]; simp⟩
    · rw [hC]; exact hRep
    · rw [hC]; exact hPresent
    · rw [hC,hL,hR]; exact scan_initial raw _ hRep hPresent
    · rw [hRad, reset_eq_ofNat]; exact ⟨ofNat_canonical 0, ofNat_value 0⟩
    · rw [hLen]; exact ofNat_canonical 1
    · rw [hSearch,hRad]
  have hSound : SoundScanNR raw y := by
    intro _ hrepl
    have hr0 : r = 0 := by simpa [y] using hrepl
    intro hout' k hk hk2 hrk
    exact output_sound raw t c.output o hRest.2.2.2.1 k hk hk2 hrk (hOut0 hr0) hout'
  have hRun' := hRun (fun z => z.ctl.mode ≠ .scan ∨ z = y)
    (fun z hz => Or.inl hz) (Or.inr rfl)
  obtain ⟨hCan,hShape⟩ := exit_refine hRun' hRest rfl rfl hSound
  refine ⟨n+1,y,hCan,hShape,hCost,rfl,rfl,rfl,hRest,hReplay,hR,hC.trans hR.symm,hLen,hIdle,?_⟩
  intro hr0
  exact ⟨c.output,hOut0 hr0⟩

/-- The actual right-head copy origin constructs a canonical fallback entry
and a costed fresh restart, together with the palindrome needed for replay. -/
theorem begin_to_scan {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} (hq : 0 < q) (h7 : first ≠ 7) (h8 : first ≠ 8)
    (c : Control) (hm : c.mode = .copy) (s : GalilVM) (hi : ShiftIdle s)
    (hRep : GalilScaffoldInputTrace.Represents s.right.head raw)
    (hPresent : s.right.head.focus ≠ none)
    (hCan : GalilScaffoldCounter.Canonical s.length) (ℓ : ℕ) (hValue : value s.length = ℓ)
    (hEven : ((GalilScaffoldPlace.stream (rightPlace s)).take (ℓ+1)).length % 2 = 0) :
    let u := beginFallbackAt (rightPlace s) s
    let win := (GalilScaffoldPlace.stream (rightPlace s)).take (ℓ+1)
    let radius := chosenRadius win
    beginFallbackVM' s u ∧ u.fpp.walker = rightPlace u ∧
    ∃ ticks y, Landing centre place entry q first raw ⟨c,u⟩ y ℓ radius ticks ∧
      position y.vm.center = position s.right - radius ∧
      Manacher.PalAt (encoded raw) (position s.right-radius) radius ∧
      (∀ r', 2*r'+1 ≤ win.length →
        Manacher.PalAt (encoded raw) (position s.right-r') r' → r' ≤ radius) := by
  dsimp only
  let w0 : GalilScaffoldChainWatch.State :=
    ⟨⟨s.right, GalilScaffoldChainConsume.ready 0 [] 0⟩,reset,reset⟩
  obtain ⟨a,xs,rs,queue,hDec,hRaw,hPal,hMax,h,hMoves,hhRep,hhPresent,hhPos,_⟩ :=
    fallback_replay (⟨s.center,s.left,s.right,w0,s.cycle,s.radius⟩ : OnlyCompareState)
      hRep hPresent s.length hCan ℓ hValue
  have hp : rightPlace s = ⟨a :: xs,s.right.gap⟩ := rightPlace_of_represent _ _ _ hDec
  have hmove : GalilScaffoldInputHead.left^[chosenRadius
      ((GalilScaffoldPlace.stream (rightPlace s)).take (ℓ+1))] s.right = h := by
    rw [hp]
    exact (leftMoves_eq hMoves).symm
  obtain ⟨hEntry,hPin⟩ := fallbackAt_rightPlace_of_represented hRep
  refine ⟨hEntry,hPin,?_⟩
  obtain ⟨ticks,y,hLanding⟩ := to_scan (centre := centre) (place := place) (entry := entry)
    hq h7 h8 c hm (beginFallbackAt (rightPlace s) s)
    hi s.fpp.program (rightPlace s) s.length hCan ℓ hValue rfl
    (by rw [hp]; exact stream_ne_nil _ _ _) hEven
    (by change GalilScaffoldInputTrace.Represents
          (GalilScaffoldInputHead.left^[_] s.right).head raw
        rw [hmove]; exact hhRep)
    (by change (GalilScaffoldInputHead.left^[_] s.right).head.focus ≠ none
        rw [hmove]; exact hhPresent)
  refine ⟨ticks,y,hLanding,?_,?_,?_⟩
  · rw [hLanding.center,hLanding.right]
    change position (GalilScaffoldInputHead.left^[_] s.right) = _
    rw [hmove,hp]
    exact hhPos
  · simpa only [hp] using hPal
  · simpa only [hp] using hMax

#print axioms exit_refine
#print axioms to_scan
#print axioms begin_to_scan
end PalPeg.CanonicalFallback
