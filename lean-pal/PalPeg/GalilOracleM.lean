import PalPeg.GalilCheckpoints
import PalPeg.GalilOracleLocal
import PalPeg.GalilReportPrefix
import PalPeg.GalilOracleGlueA
import PalPeg.GalilOracleGlueB
import PalPeg.GalilOracleGlueC

/-!
# The per-target cycle oracle, assembled from pieces

`PalPeg.GalilCheckpoints.CycleOracleM` asks, at an `InvL` state whose right head
has not passed the target cell `2m-1`, for either a refreshed prefix report point
`ReachAt … m` or one cycle to an `InvL` state with centre progress and the right
head still not past `2m-1`.

`cycleOracleM_of_pieces` is `PalPeg.GalilOracleLocal.cycleOracleL_of_pieces`
adapted to the target `m`:

* the segment hypothesis `hsegmentM` has an extra exit `atTarget` — the segment
  stops *before* the comparison that moves the right head from `2m-2` onto `2m-1`;
* at `atTarget` the body splits on the comparison:
  - match, search not `found` — **proved here**: `reportAt_of_match` is the
    report tick, and the state it lands in is an `InvScan` state (chain idle,
    clock `= 2048`, not replaying), so the resume clause of `ReachAt` holds with
    zero further ticks;
  - match, search `found` — routed through `hfound`;
  - mismatch — routed through `hmismatch`;
* every report exit concludes `ReachAt … m`, and every cycle route carries the
  bound on the landing's right head (for the positive-radius fallback the bound
  is on the head *after* the `R` replay rounds, i.e. `position sT.right + R`).
-/

set_option autoImplicit false

namespace PalPeg.GalilOracleM

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge
open PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints
open PalPeg.GalilSegmentConstruct PalPeg.GalilTickFun2 PalPeg.GalilBranchInvariants2
open PalPeg.GalilReportReplay

/-! ## Routes with the target bound -/

/-- `FoundRouteL` toward the target `m`: the report exit is `ReachAt … m`, and the
cycle landings keep the right head on or before `2m-1`. -/
inductive FoundRouteM (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) : Prop
  | report (h : ReachAt P q first raw m c r)
  | shift (cT : Control) (sT : GalilVM)
      (hst : ∃ k, StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
      (hres : FoundResidual raw cT sT) (hprog : position r.center < position sT.center)
      (hpos : position sT.right ≤ 2 * m - 1)
  | noShift (cT : Control) (sT : GalilVM)
      (hst : ∃ k, StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
      (hres : FoundResidual raw cT sT) (hprog : position r.center < position sT.center)
      (hpos : position sT.right ≤ 2 * m - 1)

/-- `FallbackRouteL` toward the target `m`. -/
inductive FallbackRouteM (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) : Prop
  | report (h : ReachAt P q first raw m c r)
  | landed (cT : Control) (sT : GalilVM)
      (hst : ∃ k, StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hI : Inv raw cT sT) (hprog : position r.center < position sT.center)
      (hpos : position sT.right ≤ 2 * m - 1)
  | replaying (cT : Control) (sT : GalilVM) (R : ℕ)
      (hst : ∃ k, StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hL : ReplayLanding raw cT sT R) (hprog : position r.center < position sT.center)
      (hpos : position sT.right + R ≤ 2 * m - 1)

/-- The exit `atTarget` of the target-bounded segment: the next tick is the
non-replaying comparison that would move the right head from `2m-2` onto `2m-1`. -/
def AtTarget (m : ℕ) (c' : Control) (t : GalilVM) : Prop :=
  c'.replaying = false ∧ c'.clock = 1 ∧ canRight t.right ∧ position t.right = 2 * m - 2 ∧
    t.replay = reset

/-! ## Local helpers -/

/-- The positive-radius fallback landing re-enters the recursion with the bound. -/
theorem cycleOutM_of_replayLanding (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ)
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
    (hL : ReplayLanding raw cT sT R) (hprog : position r.center < position sT.center)
    (hpos : position sT.right + R ≤ 2 * m - 1) :
    CycleOutM (PofC centre place entry raw) q first raw m c r := by
  obtain ⟨es, c', t', _hseg, hrun, _hlen, _hcnt, hrpos, hcen, hIS⟩ :=
    PalPeg.GalilReplaySegment.replay_after_fallback raw (PofC centre place entry raw) q first 2048
      hex (by norm_num) hsearch hpres hquiet R hL.pos cT sT hL.mode hL.clock hL.replaying
      hL.rest hL.replay hL.minv hL.frontier hL.shiftIdle
  obtain ⟨k, hst1⟩ := hst
  have hall := stepsAll_trans hst1 (hrun (hout c' t' R hIS))
  refine Or.inr ⟨c', t', k + es.length, hall, invL_of_run hall (Or.inr ⟨R, hIS⟩), ?_, ?_⟩
  · rw [hcen]; exact hprog
  · rw [hrpos]; exact hpos

theorem cycleOutM_of_fallback (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet (PofC centre place entry raw))
    (hout : ∀ (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' k → SoundScanNR raw ⟨c', t'⟩)
    (c : Control) (r : GalilVM)
    (h : FallbackRouteM (PofC centre place entry raw) q first raw m c r) :
    CycleOutM (PofC centre place entry raw) q first raw m c r := by
  cases h with
  | report h => exact Or.inl h
  | landed cT sT hst hIT hprog hpos =>
      obtain ⟨k, hst⟩ := hst
      exact Or.inr ⟨cT, sT, k, hst, invL_of_run hst (Or.inl hIT), hprog, hpos⟩
  | replaying cT sT R hst hL hprog hpos =>
      exact cycleOutM_of_replayLanding centre place entry q first raw m hex hsearch hpres
        hquiet hout c r cT sT R hst hL hprog hpos

theorem cycleOutM_of_found {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM} (h : FoundRouteM P q first raw m c r) :
    CycleOutM P q first raw m c r := by
  cases h with
  | report h => exact Or.inl h
  | shift cT sT hst hM hR hres hprog hpos =>
      obtain ⟨k, hst⟩ := hst
      exact Or.inr ⟨cT, sT, k, hst,
        invL_of_run hst (Or.inl (inv_of_residual hM hR hres)), hprog, hpos⟩
  | noShift cT sT hst hM hR hres hprog hpos =>
      obtain ⟨k, hst⟩ := hst
      exact Or.inr ⟨cT, sT, k, hst,
        invL_of_run hst (Or.inl (inv_of_residual hM hR hres)), hprog, hpos⟩

/-- **The matched, not-found comparison onto `2m-1` is a `ReachAt` point.**  The
tick is `reportAt_of_match`; the landing is an `InvScan` state, so the resume
clause holds with zero ticks. -/
theorem reachAt_of_target_match (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (hs : SegReached centre place entry q first raw c r c' t)
    (hT : AtTarget m c' t)
    (hmt : read (left t.left) = read (right t.right))
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true t vq)
    (hnf : vq.search.mode ≠ .found) :
    ReachAt (PofC centre place entry raw) q first raw m c r := by
  classical
  set P : Shared := PofC centre place entry raw with hP
  obtain ⟨hnr, hc1, hav, hpos, hrep⟩ := hT
  obtain ⟨k0, hrun0⟩ := hs.run
  obtain ⟨R, hi⟩ := hs.scan
  set vs : ScanVM := ⟨left t.left, right t.right, ChainVM.idle⟩ with hvs
  have hmt0 : (galilFrame P q first).matched (scanLens.set t vs) := hmt
  have hborn : chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) t.chain
      = false := by
    have hd : decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found) = false := by
      simp [hnf]
    unfold chainBorn
    rw [hd]
    exact Bool.and_false _
  have hcmp : (galilFrameS P q first).compare t (afterCompare t vs vq) :=
    ⟨vs, vq, true, rfl, rfl, ⟨fun _ => hmt0, fun _ => rfl⟩, hq,
      Or.inr (Or.inl ⟨hs.idle, by simp [hnf], rfl⟩), by rw [hborn]; rfl⟩
  have hmt1 : (galilFrameS P q first).matched (afterCompare t vs vq) := hmt
  set u : GalilVM := afterCompare t vs vq with hu
  set o : Bool := if P.onLetter u then decide (P.leftFirst u) else c'.output with ho'
  have ho : refresh (galilFrameS P q first) u c'.output o := by
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c'.output) = true ↔ P.leftFirst u
      rw [if_pos hl']; exact decide_eq_true_iff
    · have hl' : ¬ P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c'.output) = c'.output
      rw [if_neg hl']
  have hsrc : SoundScanNR raw ⟨c', t⟩ := stepsAll_last hrun0
  obtain ⟨⟨k1, hrun1⟩, hrp, hfr⟩ :=
    PalPeg.GalilReportPrefix.reportAt_of_match raw P rfl rfl q first 2048 hsrc hs.mode hc1 hnr
      hav hs.minv hi hpos hm1 hmle vs vq o false rfl rfl hcmp hmt1 ho
  have hall := stepsAll_trans hrun0 hrun1
  refine ⟨_, k0 + k1, hall, hrp, hfr, fun _ => ⟨_, u, 0, .zero _ (stepsAll_last hall), ?_, ?_⟩⟩
  · have hIS : PalPeg.GalilReplaySegment.InvScan 2048 raw
        {c' with clock := 2048, output := o, replaying := false} u (R + 1) := by
      refine PalPeg.GalilReplaySegment.inv_after_replay 2048 raw _ u (R + 1) hs.mode rfl rfl
        (by rw [hu, afterCompare_chain]) ?_ hrp.centre ?_ ?_ ?_
      · exact matched_invariant' raw vq (vs := vs) rfl rfl hmt hav hi
      · exact hpres t true vq hs.search hq
      · rw [hu, afterCompare_replay]; exact hrep
      · exact PalPeg.GalilReplaySegment.shiftIdle_congr
          (PalPeg.GalilReplaySegment.afterCompare_remaining t vs vq) hs.shiftIdle
    exact invL_of_run hall (Or.inr ⟨R + 1, hIS⟩)
  · have h1 : position u.right = 2 * m - 1 := hrp.atPlace
    omega

/-! ## The oracle -/

/-- **The per-target cycle oracle, assembled.** -/
theorem cycleOracleM_of_pieces (centre : GalilVM → Fin 3)
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
    (hsegmentM : ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ raw.length →
      InvL raw c r → position r.right ≤ 2 * m - 1 →
      ∃ (c' : Control) (t : GalilVM),
        SegReached centre place entry q first raw c r c' t ∧
        (AtTarget m c' t ∨ SegEnd (PofC centre place entry raw) c' t))
    (hended : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvL raw c r → position r.right ≤ 2 * m - 1 →
      SegReached centre place entry q first raw c r c' t → ¬ canRight t.right →
      ReachAt (PofC centre place entry raw) q first raw m c r)
    (hlastMatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvL raw c r → position r.right ≤ 2 * m - 1 →
      SegReached centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      ReachAt (PofC centre place entry raw) q first raw m c r)
    (hlastMismatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvL raw c r → position r.right ≤ 2 * m - 1 →
      SegReached centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      ReachAt (PofC centre place entry raw) q first raw m c r)
    (hmismatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvL raw c r → position r.right ≤ 2 * m - 1 →
      SegReached centre place entry q first raw c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRouteM (PofC centre place entry raw) q first raw m c r)
    (hfound : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvL raw c r → position r.right ≤ 2 * m - 1 →
      SegReached centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centre place entry raw) true t vq ∧ vq.search.mode = .found) →
      FoundRouteM (PofC centre place entry raw) q first raw m c r)
    (hfoundBg : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvL raw c r → position r.right ≤ 2 * m - 1 →
      SegReached centre place entry q first raw c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centre place entry raw) false t vq ∧ vq.search.mode = .found) →
      FoundRouteM (PofC centre place entry raw) q first raw m c r) :
    CycleOracleM (PofC centre place entry raw) q first raw := by
  intro m c r hm1 hmle hI hp
  obtain ⟨c', t, hs, hend⟩ := hsegmentM m c r hm1 hmle hI hp
  rcases hend with hT | hend
  · obtain ⟨hnr, hc1, hav, _, _⟩ := id hT
    by_cases hmt : read (left t.left) = read (right t.right)
    · obtain ⟨vq, hq⟩ := hsearch t hs.search true
      by_cases hf : vq.search.mode = .found
      · exact cycleOutM_of_found (hfound m c r c' t hm1 hmle hI hp hs hc1 hav hmt ⟨vq, hq, hf⟩)
      · exact Or.inl (reachAt_of_target_match centre place entry q first raw m hm1 hmle hpres
          c r c' t hs hT hmt vq hq hf)
    · exact cycleOutM_of_fallback centre place entry q first raw m hex hsearch hpres hquiet
        houtReplay c r (hmismatch m c r c' t hm1 hmle hI hp hs hnr hc1 hav hmt)
  · cases hend with
    | ended hn => exact Or.inl (hended m c r c' t hm1 hmle hI hp hs hn)
    | mismatch hr hc hav hne =>
        exact cycleOutM_of_fallback centre place entry q first raw m hex hsearch hpres hquiet
          houtReplay c r (hmismatch m c r c' t hm1 hmle hI hp hs hr hc hav hne)
    | found hc hav hmt hq =>
        exact cycleOutM_of_found (hfound m c r c' t hm1 hmle hI hp hs hc hav hmt hq)
    | foundBackground hc hq =>
        exact cycleOutM_of_found (hfoundBg m c r c' t hm1 hmle hI hp hs hc hq)
    | lastLetter hc hav hpop hinc =>
        by_cases hmt : read (left t.left) = read (right t.right)
        · exact Or.inl (hlastMatch m c r c' t hm1 hmle hI hp hs hc hav hpop hinc hmt)
        · exact Or.inl (hlastMismatch m c r c' t hm1 hmle hI hp hs hc hav hpop hinc hmt)

#print axioms cycleOutM_of_replayLanding
#print axioms cycleOutM_of_fallback
#print axioms cycleOutM_of_found
#print axioms reachAt_of_target_match
#print axioms cycleOracleM_of_pieces

end PalPeg.GalilOracleM
