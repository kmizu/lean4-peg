import PalPeg.RestartStageRun

/-!
# No break inside the certified periodic window

A lag-zero break needs the verifier's next read to differ from the predicted period symbol.  The
prediction is the text two semiperiods back (`BlockOn`); the scan palindrome mirrors that place
to the left of the centre, a left period certificate moves it two semiperiods further left, and
the matched comparison brings it back to the verifier's next read.  So inside the certificate a
matched comparison cannot break the chain.
-/

set_option autoImplicit false

namespace PalPeg.RestartBoundary

open PalPeg GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply GalilBranchInvariants
open PalPeg.ShiftPalAlongTrace PalPeg.GalilReplaySpan PalPeg.GalilReplayGeneral2

/-- The chain-level core: three index equalities of the text exclude `BreakStep`. -/
theorem not_breakStep_of_text {raw : List (Fin 2)} {cen₀ P : ℕ} {cc b : Fin 3}
    {xs : List (Fin 3)} {w w' : GalilScaffoldChainWatch.State} {leftPlace : ℕ}
    (hwindow : WatchWindow raw cen₀ P cc b xs (.watch w))
    (hsize : cen₀ + 1 + 2 * (xs.length + 1) ≤ P + 1)
    (hmirror : (encoded raw)[P + 1 - 2 * (xs.length + 1)]?
      = (encoded raw)[leftPlace + 2 * (xs.length + 1)]?)
    (hcertificate : (encoded raw)[leftPlace]? = (encoded raw)[leftPlace + 2 * (xs.length + 1)]?)
    (hmatched : (encoded raw)[leftPlace]? = (encoded raw)[P + 1]?) :
    ¬ BreakStep w w' := by
  rintro ⟨hzero, hcanRight, a, hsymbol, hread, -⟩
  obtain ⟨⟨hneg, hposition⟩, hblock, hcore⟩ := hwindow
  have hlagEmpty : w.lag.pos = [] := by
    rcases hw : w.lag with ⟨pos, neg⟩
    rw [hw] at hzero
    simp only [zero, Bool.and_eq_true, List.isEmpty_iff] at hzero
    exact hzero.1
  have hverifier : position w.machine.verifier = P := by
    rw [hlagEmpty] at hposition
    simpa using hposition
  have hrep := hcore.2.1
  have hpresent := hcore.2.2.1
  have hleft0 : 0 < w.machine.verifier.head.left.length :=
    (represented_position _ raw hrep hpresent).1
  have hnextRead : read (right w.machine.verifier) = (encoded raw)[P + 1]? := by
    rw [represented_read _ raw (right_word _ raw hrep hcanRight)
      (right_present _ raw hrep hpresent hcanRight),
      right_position _ hcanRight hleft0, hverifier]
  have hprediction := symbol_of_coreP hcore
  rw [hverifier] at hprediction
  have hback := hblock (P + 1 - 2 * (xs.length + 1) - (cen₀ + 1)) (by omega)
  have hindex : cen₀ + 1 + (P + 1 - 2 * (xs.length + 1) - (cen₀ + 1))
      = P + 1 - 2 * (xs.length + 1) := by omega
  have hmod : (P + 1 - (cen₀ + 1)) % (2 * (xs.length + 1))
      = (P + 1 - 2 * (xs.length + 1) - (cen₀ + 1)) % (2 * (xs.length + 1)) := by
    have : P + 1 - (cen₀ + 1)
        = (P + 1 - 2 * (xs.length + 1) - (cen₀ + 1)) + 2 * (xs.length + 1) := by omega
    rw [this, Nat.add_mod_right]
  rw [hindex] at hback
  apply hread
  rw [hnextRead, ← hmatched, hcertificate, ← hmirror, hback, ← hmod, ← hprediction, hsymbol]

open GalilScaffoldTop GalilScaffoldController GalilRunSkeleton GalilInvPlus3
open PalPeg.WindowPack PalPeg.WindowRun PalPeg.WindowInv PalPeg.GalilChainCoupling
open PalPeg.RestartStageRun

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- The left period certificate of a watching chain at the scan centre: the text has period
`2h` on the four semiperiods to the left of the centre. -/
def LeftCertificate (raw : List (Fin 2)) (s : GalilVM) : Prop :=
  ∀ w, s.chain = .watch w →
    PeriodOn (encoded raw) (2 * periodLength w)
      (position s.center - 4 * periodLength w) (position s.center)

/-- **The boundary case is unreachable.**  At a matched comparison of a window-packed scan state
with its scan geometry and the left certificate, a lag-zero break does not happen at
`distance = 4h − 1`. -/
theorem distance_ne_boundary {raw : List (Fin 2)} {c : Control} {s s' : GalilVM}
    {w1 w' : GalilScaffoldChainWatch.State}
    (hwin : WindowRunPack raw c s) (hm : c.mode = Mode.scan)
    {R : ℕ} (hscan : ScanInvariant raw (position s.center) R s.left s.right)
    (hradius : RadiusRep s.radius R)
    (hcert : LeftCertificate raw s)
    (hcmp : (galilFrameS (PofC centre place entry raw) q first).compare s s')
    (hmt : (galilFrameS (PofC centre place entry raw) q first).matched s')
    (hstep : ChainStep s.chain (.watch w1)) (hbreak : BreakStep w1 w') :
    value w1.machine.control.distance ≠ 4 * (periodLength w1 : ℤ) - 1 := by
  intro hdistance
  generalize hy : ChainVM.watch w1 = y at hstep
  generalize hx : s.chain = x at hstep
  cases hstep with
  | idle => cases hy
  | brokenIdle => cases hy
  | copyBit => cases hy
  | copyEnd => cases hy
  | backStep => cases hy
  | watchBreak => cases hy
  | backDone v h lag margin ver hf =>
    cases hy
    have hzero : value (watchControl v).distance = 0 := rfl
    rw [show (⟨⟨ver, watchControl v⟩, lag, margin⟩ : GalilScaffoldChainWatch.State).machine.control.distance
      = (watchControl v).distance from rfl, hzero] at hdistance
    omega
  | watchStep w0 w1' hinternal =>
    cases hy
    have hchain : s.chain = .watch w0 := hx
    -- the window of the watch after its internal step
    obtain ⟨cen₀, cc, hcentre, hinv, hk, -, -⟩ := hwin.window
    rw [hchain] at hinv
    obtain ⟨b, xs, hW0⟩ := hinv
    have hW1 := watchWindow_step hW0 hinternal
    have hlength1 : periodLength w1 = xs.length + 1 := periodLength_of_coreP hW1.2.2
    have hlength0 : periodLength w0 = xs.length + 1 := periodLength_of_coreP hW0.2.2
    obtain ⟨k, hk⟩ := (hk w0 hchain).2 (by rw [hm]; decide)
    -- the radius is the distance
    have hunbroken1 : w1.machine.control.broken = false := hW1.2.2.2.2.2.1
    have hsum0 : SumRel (.watch w0) (value s.radius) := by
      have := hwin.coupled.sum; rwa [hchain] at this
    have hblock0 : BlockInv (.watch w0) := by
      have := hwin.coupled.block; rwa [hchain] at this
    have hsum1 : SumRel (.watch w1) (value s.radius) :=
      (step_inv (.watchStep w0 w1 hinternal) (F := True) trivial (O := fun _ => True) hblock0
        hsum0 (fun _ _ _ => Or.inr trivial)).1
    have hd := hsum1 hunbroken1
    rw [value_zero_of_zero hbreak.1, add_zero, hradius.2, hdistance, hlength1] at hd
    have hR : R + 1 = 4 * (xs.length + 1) := by
      push_cast at hd
      omega
    have hRC := scan_radius_lt hscan
    -- the three text equalities
    have hpal := hscan.palindrome
    have hmirror : (encoded raw)[position s.right + 1 - 2 * (xs.length + 1)]?
        = (encoded raw)[(position s.center - (R + 1)) + 2 * (xs.length + 1)]? := by
      have h1 := hpal.2.2 (2 * (xs.length + 1)) (by omega)
      rw [hscan.rightPos,
        show position s.center + R + 1 - 2 * (xs.length + 1)
          = position s.center + 2 * (xs.length + 1) from by omega,
        show position s.center - (R + 1) + 2 * (xs.length + 1)
          = position s.center - 2 * (xs.length + 1) from by omega]
      exact h1.symm
    have hcertificate : (encoded raw)[position s.center - (R + 1)]?
        = (encoded raw)[(position s.center - (R + 1)) + 2 * (xs.length + 1)]? := by
      have h1 := hcert w0 hchain
      rw [hlength0] at h1
      exact h1 (position s.center - (R + 1)) (by omega) (by omega)
    -- the matched comparison
    have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
    obtain ⟨vs, vq, a, hvl, hvr, -, -, -, heq⟩ := hcmp'
    obtain ⟨hl', hr', -⟩ := PalPeg.WindowTick.compare_target_heads heq
    have hreads : read (left s.left) = read (right s.right) := by
      have h0 : read s'.left = read s'.right := hmt
      rwa [hl', hr', hvl, hvr] at h0
    have hverCan := hbreak.2.1
    have hverifier : position w1.machine.verifier = position s.right := by
      obtain ⟨⟨-, hposition⟩, -, -⟩ := hW1
      have hlagEmpty : w1.lag.pos = [] := by
        have hz := hbreak.1
        rcases hw : w1.lag with ⟨pos, neg⟩
        rw [hw] at hz
        simp only [zero, Bool.and_eq_true, List.isEmpty_iff] at hz
        exact hz.1
      rw [hlagEmpty] at hposition
      simpa using hposition
    have hrightCan : canRight s.right := by
      have hrep := hW1.2.2.2.1
      have hpresent := hW1.2.2.2.2.1
      have hbound := position_bound _ raw (right_word _ raw hrep hverCan)
        (right_present _ raw hrep hpresent hverCan)
      rw [right_position _ hverCan (represented_position _ raw hrep hpresent).1, hverifier]
        at hbound
      exact canRight_of_bound _ raw hscan.rightRep hscan.rightPresent hbound
    have hrightRead : read (right s.right) = (encoded raw)[position s.right + 1]? := by
      rw [represented_read _ raw (right_word _ raw hscan.rightRep hrightCan)
        (right_present _ raw hscan.rightRep hscan.rightPresent hrightCan),
        right_position _ hrightCan
          (represented_position _ raw hscan.rightRep hscan.rightPresent).1]
    have hrightSome : ∃ z, (encoded raw)[position s.right + 1]? = some z := by
      have hbound := position_bound _ raw (right_word _ raw hscan.rightRep hrightCan)
        (right_present _ raw hscan.rightRep hscan.rightPresent hrightCan)
      rw [right_position _ hrightCan
        (represented_position _ raw hscan.rightRep hscan.rightPresent).1] at hbound
      exact ⟨_, List.getElem?_eq_getElem hbound⟩
    have hleftRead := left_signed_read s.left raw hscan.leftRep hscan.leftPresent
    rw [hscan.leftPos] at hleftRead
    have hmatched : (encoded raw)[position s.center - (R + 1)]?
        = (encoded raw)[position s.right + 1]? := by
      rw [← hrightRead, ← hreads, hleftRead]
      unfold signedRead
      have hcast : ((position s.center - R : ℕ) : ℤ) - 1 = ((position s.center - (R + 1) : ℕ) : ℤ) := by
        omega
      split_ifs with hle
      · exfalso
        obtain ⟨z, hz⟩ := hrightSome
        rw [hleftRead] at hreads
        unfold signedRead at hreads
        rw [if_pos hle, hrightRead, hz] at hreads
        cases hreads
      · rw [hcast, Int.toNat_natCast]
    exact not_breakStep_of_text (w' := w') hW1 (by rw [hscan.rightPos, hk]; nlinarith [hR])
      hmirror hcertificate hmatched hbreak

end PalPeg.RestartBoundary
