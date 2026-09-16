import PalPeg.GalilOracleDischarge
import PalPeg.GalilReplayFound
import PalPeg.GalilBootVM

/-!
# The cycle oracle in local form

`PalPeg.GalilOracleDischarge.cycleOracle_of_pieces` states every report exit as
`GlobalReport`, i.e. as a `ScaffoldRun` starting from `Control.initial 2048`.
At a mid-run state no such prefix is available, so those exits cannot be
discharged there (`PalPeg.GalilOracleGlueA.lastMatch_report` needed an extra
prefix hypothesis).

This module restates the oracle **locally**: a report exit is a sound run from
the *current* state to a refreshed report point (`LocalReport`).  The prefix is
composed exactly once, at the very top, in `H_run_of_oracleL`, where the `init`
tick supplies it.

The recursion state is widened once more, to `InvL := InvS ∧ OutputRel`:
`OutputRel` at the entering state is what `watchSegE_stepsAll` needs, and at
every non-replaying landing it comes for free from the landing run's
`SoundScanNR`.
-/

set_option autoImplicit false

namespace PalPeg.GalilOracleLocal

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge
open PalPeg.GalilBranchInvariants2 (SearchReady)

/-! ## The local recursion state and report -/

/-- The recursion state: the widened pack together with a sound output. -/
def InvL (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  InvS raw c s ∧ OutputRel raw c s

/-- A finished run, **local** form: a sound run from `⟨c, r⟩` to a refreshed
report point. -/
def LocalReport (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) : Prop :=
  ∃ y : State GalilVM,
    (∃ k, StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ y) ∧
    ReportPoint raw y ∧ Refreshed P q first y

/-- What one turn of the main loop may deliver, local form. -/
def CycleOutL (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) : Prop :=
  LocalReport P q first raw c r ∨
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      InvL raw cT sT ∧ position r.center < position sT.center

/-- **The local cycle oracle.** -/
def CycleOracleL (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvL raw c r → CycleOutL P q first raw c r

/-! ## Mode facts of the widened pack -/

theorem invS_mode {raw : List (Fin 2)} {c : Control} {s : GalilVM} (h : InvS raw c s) :
    c.mode = Mode.scan ∧ c.replaying = false := by
  rcases h with h | ⟨k, h⟩
  · exact ⟨h.mode.1, h.mode.2.1⟩
  · exact ⟨h.mode.1, h.mode.2.1⟩

/-- A non-replaying landing of a sound run carries `OutputRel` for free. -/
theorem invL_of_run {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {k : ℕ}
    {x : State GalilVM} {c : Control} {s : GalilVM}
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k x ⟨c, s⟩)
    (hI : InvS raw c s) : InvL raw c s :=
  ⟨hI, stepsAll_last hst (invS_mode hI).1 (invS_mode hI).2⟩

/-! ## The recursion -/

theorem runL_fuel (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleL P q first raw) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), 2 * raw.length - position r.center ≤ n →
      InvL raw c r → LocalReport P q first raw c r := by
  intro n
  induction n with
  | zero =>
    intro c r hn hI
    rcases hor c r hI with hdone | ⟨cT, sT, k, _, hIT, hlt⟩
    · exact hdone
    · exact absurd (invS_center_le hIT.1) (by have := invS_center_le hI.1; omega)
  | succ n ih =>
    intro c r hn hI
    rcases hor c r hI with hdone | ⟨cT, sT, k, hst, hIT, hlt⟩
    · exact hdone
    · obtain ⟨y, ⟨k', hst'⟩, hrp, hfr⟩ :=
        ih cT sT (by have := invS_center_le hIT.1; omega) hIT
      exact ⟨y, ⟨k + k', stepsAll_trans hst hst'⟩, hrp, hfr⟩

/-- **The recursion**, local form: from any `InvL` state the oracle drives the
run to a refreshed report point. -/
theorem run_from_invL (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleL P q first raw) (c : Control) (r : GalilVM) (hI : InvL raw c r) :
    LocalReport P q first raw c r :=
  runL_fuel P q first raw hor (2 * raw.length - position r.center) c r le_rfl hI

/-- **`H_run` from the local oracle**, booted at `initVM0`. -/
theorem H_run_of_oracleL (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (hor : ∀ w : List (Fin 2), CycleOracleL (PofC centre place entry w) q first w) :
    ∀ w : List (Fin 2), 0 < w.length →
      ∃ y : State GalilVM,
        ScaffoldRun (PofC centre place entry) (fun _ => q) (fun _ => first) 2048 w y ∧
        ReportPoint w y ∧ Refreshed (PofC centre place entry w) q first y := by
  intro w hw
  rcases w with _ | ⟨a, rest⟩
  · simp at hw
  · obtain ⟨c1, t, hst, hI⟩ :=
      inv_init (onLetterVM (a :: rest)) leftFirstVM centre place entry q first
        (PalPeg.GalilBootVM.initVM0 (a :: rest)) a rest
        (PalPeg.GalilBootVM.initVM0_right _) (PalPeg.GalilBootVM.initVM0_radius _)
        (PalPeg.GalilBootVM.initVM0_length _) (PalPeg.GalilBootVM.initVM0_replay _)
        (PalPeg.GalilBootVM.initVM0_shiftIdle _)
    have hL : InvL (a :: rest) c1 t := invL_of_run hst (invS_of_inv hI)
    obtain ⟨y, ⟨k, hst'⟩, hrp, hfr⟩ :=
      run_from_invL (PofC centre place entry (a :: rest)) q first (a :: rest)
        (hor (a :: rest)) c1 t hL
    exact ⟨y, ⟨1 + k, ⟨initial 2048, PalPeg.GalilBootVM.initVM0 (a :: rest)⟩, rfl,
      stepsAll_mono (fun _ _ => trivial) (stepsAll_trans hst hst')⟩, hrp, hfr⟩

/-! ## Local report lemmas -/

/-- `PalPeg.GalilReportReach.report_of_last_consume` without the run prefix.
The source state's soundness `hsrc` replaces the prefix's last state. -/
theorem report_of_last_consume_local
    (w : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM w)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c : Control} {s : GalilVM}
    (hsrc : SoundScanNR w ⟨c, s⟩)
    (hm : c.mode = Mode.scan) (hclk : c.clock = 1)
    (hpop : PopsIncoming s.right) {a : Fin 2} (hinc : s.right.head.incoming = [a])
    (hfr : Frontier s) (hM : MInv w c s)
    {r : ℕ} (hi : ScanInvariant w (position s.center) r s.left s.right)
    (hrep : GalilScaffoldInputTrace.Represents s.right.head w)
    (vs : ScanVM) (vq : SearchVM) (o : Bool)
    (hl : vs.left = GalilScaffoldInputHead.left s.left)
    (hrr : vs.right = right s.right)
    (hcmp : (galilFrameS P q first).compare s (afterCompare s vs vq))
    (hmt : (galilFrameS P q first).matched (afterCompare s vs vq))
    (ho : refresh (galilFrameS P q first) (afterCompare s vs vq) c.output o) :
    (∃ k : ℕ, StepsAll (galilFrameS P q first) delay (SoundScanNR w) k ⟨c, s⟩
        ⟨{c with clock := delay, output := o, replaying := false}, afterCompare s vs vq⟩) ∧
      ReportPoint w
        ⟨{c with clock := delay, output := o, replaying := false}, afterCompare s vs vq⟩ ∧
      Refreshed P q first
        ⟨{c with clock := delay, output := o, replaying := false}, afterCompare s vs vq⟩ := by
  obtain ⟨hav, hlast, hne⟩ := PalPeg.GalilReportReach.last_consume_geometry hrep hpop hinc
  have hnr : c.replaying = false := PalPeg.GalilReportReach.not_replaying_of_pops hfr hpop hM
  have hmt0 : (galilFrame P q first).matched (scanLens.set s vs) := hmt
  have hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
      GalilScaffoldInputHead.read (right s.right) := by
    have h0 := matched_parts P q first hmt0
    rw [hl, hrr] at h0; exact h0
  have hi' : ScanInvariant w (position s.center) (r + 1)
      (afterCompare s vs vq).left (afterCompare s vs vq).right :=
    matched_invariant' w vq hl hrr hmatch hav hi
  have hpl : (galilFrameS P q first).matchedPlace c.replaying (afterCompare s vs vq)
      (afterCompare s vs vq) := by
    show afterCompare s vs vq = (if c.replaying then _ else afterCompare s vs vq)
    rw [hnr]; simp
  have htick : Tick (galilFrameS P q first) delay ⟨c, s⟩
      ⟨{c with clock := delay, output := o, replaying := false}, afterCompare s vs vq⟩ := by
    have h := Tick.scan_match (F := galilFrameS P q first) (delay := delay) c s
      (afterCompare s vs vq) (afterCompare s vs vq) o hm (Or.inr hav) hclk hcmp hmt hpl ho
    rw [hnr] at h
    simpa using h
  have hsound : SoundScanNR w
      ⟨{c with clock := delay, output := o, replaying := false}, afterCompare s vs vq⟩ := by
    intro _ _
    exact outputRel_of_refreshS' w P hP hP' q first (afterCompare s vs vq) c.output o hi' ho _ rfl
  have hlast' : position (afterCompare s vs vq).right = 2 * w.length - 1 := by
    rw [afterCompare_right, hrr]; exact hlast
  refine ⟨⟨1, .succ hsrc htick (.zero _ hsound)⟩, ?_, ?_⟩
  · exact PalPeg.GalilReportReach.reportPoint_of_parts rfl hi'
      (minv_match o delay hnr hl hrr hav hmatch hi hM) hlast' hne
  · exact ⟨c.output, (refreshS_iff P q first _ _ _).1 ho⟩

/-- `PalPeg.GalilReplayFound.report_after_replay_of_halted` without the run
prefix. -/
theorem report_after_replay_of_halted_local (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (hd : 1 ≤ delay)
    (hsearch : ∀ s' : GalilVM, SearchReady (searchLens.get s') → ∀ a : Bool,
      ∃ v, searchEffect P a s' v)
    (hpres : ∀ (s' : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s') → searchEffect P a s' v → SearchReady v)
    (hbg : ∀ (s' : GalilVM) (v : SearchVM), searchEffect P false s' v → v.search.mode ≠ .found)
    (hhalt : ∀ (s' : GalilVM) (m : ℕ), 0 < m → s'.replay = ofNat m →
      PalPeg.GalilReplayFound.SearchHalted s')
    {c : Control} {t : GalilVM} {r : ℕ}
    (hm : c.mode = Mode.scan) (hclk : 1 ≤ c.clock)
    (hR : Restarted raw t 0 reset)
    (hM : MInv raw c t)
    (hsr : SearchReady (searchLens.get t))
    (hrepl : t.replay = ofNat r) (hrp : c.replaying = decide (0 < r)) (hr0 : 0 < r)
    (hhead : ∃ xs rs : List (Fin 2),
      t.right.head = layout xs (rs.map some) [] ∧ raw = xs.reverse ++ rs)
    (hlast : position t.right + r = 2 * raw.length - 1) :
    ∃ (es : List Bool) (c' : Control) (y : GalilVM),
      WatchSegE P q first delay es c t c' y ∧
      (∃ k : ℕ, StepsAll (galilFrameS P q first) delay (SoundScanNR raw) k ⟨c, t⟩ ⟨c', y⟩) ∧
      ReportPoint raw ⟨c', y⟩ ∧ Refreshed P q first ⟨c', y⟩ := by
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  have hrp' : c.replaying = true := by rw [hrp]; simp
  have hidle : t.chain = ChainVM.idle := hR.1
  have hi : ScanInvariant raw (position t.center) 0 t.left t.right := hR.2.2.2.1
  have hinc : t.right.head.incoming = [] := by
    obtain ⟨xs, rs, hh, -⟩ := hhead
    rw [hh, PalPeg.GalilEndOfInput.layout_incoming]
  have hne : 0 < raw.length := by omega
  obtain ⟨es, k, c', y, hseg, hall, -, hrpF, hposF, -, -, hMF, ⟨radF, hiF⟩, hfrF⟩ :=
    PalPeg.GalilReportReplay.replay_run raw P hP hP' hex q first delay hd hsearch hpres hbg
      (PalPeg.GalilReplayFound.not_found_during_replay P hhalt) j c t 0 hm hclk hrp'
      hrepl hidle hsr hM hi hinc hlast
  exact ⟨es, c', y, hseg, ⟨k, hall⟩, ⟨hrpF, ⟨radF, hiF⟩, hMF, hposF, hne⟩, hfrF⟩

/-! ## The routes, local form -/

/-- `FoundRoute` with the report exit in local form. -/
inductive FoundRouteL (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) : Prop
  /-- the report point falls inside the chain's life -/
  | report (h : LocalReport P q first raw c r)
  /-- the cycle with a first shift and the re-shift rounds -/
  | shift (cT : Control) (sT : GalilVM)
      (hst : ∃ k, StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
      (hres : FoundResidual raw cT sT) (hprog : position r.center < position sT.center)
  /-- the cycle that breaks before any shift -/
  | noShift (cT : Control) (sT : GalilVM)
      (hst : ∃ k, StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
      (hres : FoundResidual raw cT sT) (hprog : position r.center < position sT.center)

/-- `FallbackRoute` with the report exit in local form. -/
inductive FallbackRouteL (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) : Prop
  /-- the report point falls inside the fallback -/
  | report (h : LocalReport P q first raw c r)
  /-- the FPP chose radius `0` -/
  | landed (cT : Control) (sT : GalilVM)
      (hst : ∃ k, StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hI : Inv raw cT sT) (hprog : position r.center < position sT.center)
  /-- the FPP chose a positive radius -/
  | replaying (cT : Control) (sT : GalilVM) (R : ℕ)
      (hst : ∃ k, StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hL : ReplayLanding raw cT sT R) (hprog : position r.center < position sT.center)

/-- The positive-radius fallback landing, local form. -/
theorem cycleOutL_of_replayLanding (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet (PofC centre place entry raw))
    (hout : ∀ (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' k → SoundScanNR raw ⟨c', t'⟩)
    (c : Control) (r : GalilVM) (cT : Control) (sT : GalilVM) (R : ℕ)
    (hst : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hL : ReplayLanding raw cT sT R) (hprog : position r.center < position sT.center) :
    CycleOutL (PofC centre place entry raw) q first raw c r := by
  obtain ⟨es, c', t', _hseg, hrun, _hlen, _hcnt, _hrpos, hcen, hIS⟩ :=
    PalPeg.GalilReplaySegment.replay_after_fallback raw (PofC centre place entry raw) q first 2048
      hex (by norm_num) hsearch hpres hquiet R hL.pos cT sT hL.mode hL.clock hL.replaying
      hL.rest hL.replay hL.minv hL.frontier hL.shiftIdle
  obtain ⟨k, hst1⟩ := hst
  have hall := stepsAll_trans hst1 (hrun (hout c' t' R hIS))
  refine Or.inr ⟨c', t', k + es.length, hall, invL_of_run hall (Or.inr ⟨R, hIS⟩), ?_⟩
  rw [hcen]
  exact hprog

/-! ## The oracle, exit by exit, local form -/

/-- **The local cycle oracle, assembled.**  Same hypotheses as
`cycleOracleS_of_pieces`, with every premise at an `InvL` state and every
report exit in `LocalReport` form. -/
theorem cycleOracleL_of_pieces (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet (PofC centre place entry raw))
    (houtReplay : ∀ (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' k → SoundScanNR raw ⟨c', t'⟩)
    (hsegment : ∀ (c : Control) (r : GalilVM), InvL raw c r →
      ∃ (c' : Control) (t : GalilVM),
        SegReached centre place entry q first raw c r c' t ∧
        PalPeg.GalilSegmentConstruct.SegEnd (PofC centre place entry raw) c' t)
    (hended : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvL raw c r →
      SegReached centre place entry q first raw c r c' t → ¬ canRight t.right →
      LocalReport (PofC centre place entry raw) q first raw c r)
    (hlastMatch : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvL raw c r →
      SegReached centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      LocalReport (PofC centre place entry raw) q first raw c r)
    (hlastMismatch : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvL raw c r →
      SegReached centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      LocalReport (PofC centre place entry raw) q first raw c r)
    (hmismatch : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvL raw c r →
      SegReached centre place entry q first raw c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRouteL (PofC centre place entry raw) q first raw c r)
    (hfound : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvL raw c r →
      SegReached centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centre place entry raw) true t vq ∧ vq.search.mode = .found) →
      FoundRouteL (PofC centre place entry raw) q first raw c r)
    (hfoundBg : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvL raw c r →
      SegReached centre place entry q first raw c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centre place entry raw) false t vq ∧ vq.search.mode = .found) →
      FoundRouteL (PofC centre place entry raw) q first raw c r) :
    CycleOracleL (PofC centre place entry raw) q first raw := by
  intro c r hI
  obtain ⟨c', t, hs, hend⟩ := hsegment c r hI
  cases hend with
  | ended hn =>
      exact Or.inl (hended c r c' t hI hs hn)
  | mismatch hr hc hav hne =>
      cases hmismatch c r c' t hI hs hr hc hav hne with
      | report h => exact Or.inl h
      | landed cT sT hst hIT hprog =>
          obtain ⟨k, hst⟩ := hst
          exact Or.inr ⟨cT, sT, k, hst, invL_of_run hst (Or.inl hIT), hprog⟩
      | replaying cT sT R hst hL hprog =>
          exact cycleOutL_of_replayLanding centre place entry q first raw hex hsearch hpres
            hquiet houtReplay c r cT sT R hst hL hprog
  | found hc hav hmt hq =>
      cases hfound c r c' t hI hs hc hav hmt hq with
      | report h => exact Or.inl h
      | shift cT sT hst hM hR hres hprog =>
          obtain ⟨k, hst⟩ := hst
          exact Or.inr ⟨cT, sT, k, hst,
            invL_of_run hst (Or.inl (inv_of_residual hM hR hres)), hprog⟩
      | noShift cT sT hst hM hR hres hprog =>
          obtain ⟨k, hst⟩ := hst
          exact Or.inr ⟨cT, sT, k, hst,
            invL_of_run hst (Or.inl (inv_of_residual hM hR hres)), hprog⟩
  | foundBackground hc hq =>
      cases hfoundBg c r c' t hI hs hc hq with
      | report h => exact Or.inl h
      | shift cT sT hst hM hR hres hprog =>
          obtain ⟨k, hst⟩ := hst
          exact Or.inr ⟨cT, sT, k, hst,
            invL_of_run hst (Or.inl (inv_of_residual hM hR hres)), hprog⟩
      | noShift cT sT hst hM hR hres hprog =>
          obtain ⟨k, hst⟩ := hst
          exact Or.inr ⟨cT, sT, k, hst,
            invL_of_run hst (Or.inl (inv_of_residual hM hR hres)), hprog⟩
  | lastLetter hc hav hpop hinc =>
      by_cases hmt : read (left t.left) = read (right t.right)
      · exact Or.inl (hlastMatch c r c' t hI hs hc hav hpop hinc hmt)
      · exact Or.inl (hlastMismatch c r c' t hI hs hc hav hpop hinc hmt)

#print axioms invS_mode
#print axioms invL_of_run
#print axioms runL_fuel
#print axioms run_from_invL
#print axioms H_run_of_oracleL
#print axioms report_of_last_consume_local
#print axioms report_after_replay_of_halted_local
#print axioms cycleOutL_of_replayLanding
#print axioms cycleOracleL_of_pieces

end PalPeg.GalilOracleLocal
