import PalPeg.GalilTickFun3
import PalPeg.GalilBranchInvariants2
import PalPeg.GalilRunSkeleton
import PalPeg.WindowInv
import PalPeg.GalilWatchPhase
import PalPeg.CloseoutCheckW
import PalPeg.CloseoutMarksPack
import PalPeg.WindowPack
import PalPeg.GalilTraceCost
import PalPeg.GalilLexMeasure
import PalPeg.GalilScaffoldTopMerge
import PalPeg.GalilScaffoldTopSteps
import PalPeg.GalilShiftPack
import PalPeg.GalilChainCoupling
import PalPeg.GalilOracleLeaves2
import PalPeg.ShapedRun

set_option autoImplicit false

/-!
# `OracleRun`: tick existence in the `PofC` frame

`CycleOracleMC3` (the remaining oracle obligation) speaks about runs of
`galilFrameS (PofC centre place entry w) q first`, whose fallback entry is the relational
`beginFallbackVM'`.  `GalilTickFun.tick_exists` is stated for the functional frame
`sharedFun`, so it does not apply; the generic `scan_tick_gen` / `phase_tick_gen` do.
This file instantiates them at `PofC` with the entries' own existence lemmas
(`beginShift_exists`, `beginFallback_exists`), the search co-process's totality
(`searchEffect_exists`, from `SearchReady`) and the chain's totality (`chainAt_exists`,
from `ChainReady` — with `M-watchBreak` fixed, a positive-lag watch always ticks).
-/

namespace PalPeg.OracleRun

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton PalPeg.GalilTickFun
  PalPeg.GalilTickFun3 PalPeg.ShiftPalAlongTrace PalPeg.GalilReplayGeneral2
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilTraceCost PalPeg.GalilLexMeasure PalPeg.GalilInvPlus3 PalPeg.CloseoutPackW
  PalPeg.GalilStructuredSkeleton PalPeg.GalilCheckpoints PalPeg.GalilIntervalCost
  PalPeg.CloseoutPackRun2 PalPeg.GalilInvPlus2

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **A non-replaying scan state with a positive clock ticks in the `PofC` frame**, given a
ready search co-process and a ready chain. -/
theorem scan_tick_exists_PofC {w : List (Fin 2)} (c : Control) (s : GalilVM)
    (hm : c.mode = .scan) (hclk : 1 ≤ c.clock) (hr : c.replaying = false)
    (hsearch : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s))
    (hready : ChainReady s.chain) :
    ∃ st', Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩ st' :=
  scan_tick_gen (PofC centre place entry w) q first 2048 c s hm hclk hr
    (fun t hg => beginShift_exists t hg) (fun t => beginFallback_exists t)
    (fun a => PalPeg.GalilBranchInvariants2.searchEffect_exists _ a s hsearch)
    (fun a v => chainAt_exists a _ _ _ _ _ _ s.chain hready)

/-- **Every phase mode ticks in the `PofC` frame** (the generic `phase_tick_gen`). -/
theorem phase_tick_exists_PofC {w : List (Fin 2)} (x : State GalilVM)
    (hx : PhaseEnabled q first x) :
    ∃ y, Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y :=
  phase_tick_gen (PofC centre place entry w) q first 2048 x hx


/-- A place head sits at most two cells per letter to its left. -/
theorem position_le_two_left (p : PlaceHead) : position p ≤ 2 * p.head.left.length := by
  unfold position; split <;> omega

/-- **`ChainReady` at a watch that carries the birth-anchored window**, given that the right
head (which the verifier trails, `LagAt`) can still move.  The watch clause is the one
`M-watchBreak` left: the verifier can move and the period tape reads a symbol; the read
itself may or may not match. -/
theorem chainReady_watch_of_watchWindow {raw : List (Fin 2)} {cen₀ : ℕ} {cc b : Fin 3}
    {xs : List (Fin 3)} {w : GalilScaffoldChainWatch.State} {r : PlaceHead}
    (hW : WatchWindow raw cen₀ (position r) cc b xs (ChainVM.watch w))
    (hrep : GalilScaffoldInputTrace.Represents r.head raw) (hpres : r.head.focus ≠ none)
    (hcan : canRight r) : ChainReady (ChainVM.watch w) := by
  obtain ⟨hlag, -, hcore⟩ := hW
  obtain ⟨hon, hvrep, hvpres, -, -⟩ := id hcore
  have hlength : (encoded raw).length = 2 * raw.length + 1 := by simp [encoded, pairs_length]
  -- the right head is strictly inside the encoded word
  have hrb : position r + 1 < (encoded raw).length := by
    have h1 := right_position r hcan (represented_position _ raw hrep hpres).1
    have h2 := (represented_position _ raw (right_word r raw hrep hcan)
      (right_present r raw hrep hpres hcan)).2
    have h3 := position_le_two_left (right r)
    omega
  have hvpos := hlag.2
  have hcanV : canRight w.machine.verifier :=
    canRight_of_bound _ raw hvrep hvpres (by omega)
  refine ⟨fun hp => ⟨hcanV, ?_⟩, hon, fun m hm => ?_⟩
  · have hi : (position w.machine.verifier + 1 - (cen₀ + 1)) % (2 * (xs.length + 1)) <
        (GalilScaffoldChainSweep.bounce cc b xs).length := by
      rw [PalPeg.GalilWatchPhase.bounce_length]; exact Nat.mod_lt _ (by omega)
    exact ⟨_, (symbol_of_coreP hcore).trans (List.getElem?_eq_getElem hi)⟩
  · cases hm with
    | idle _ => exact hcanV
    | take hp _ =>
      have hne : w.lag.pos ≠ [] := by
        intro h0; simp [positive, h0] at hp
      have hlen : 0 < w.lag.pos.length := List.length_pos_of_ne_nil hne
      have h1 := right_position w.machine.verifier hcanV (represented_position _ raw hvrep hvpres).1
      show canRight (right w.machine.verifier)
      exact canRight_of_bound _ raw (right_word _ raw hvrep hcanV)
        (right_present _ raw hvrep hvpres hcanV) (by omega)

/-- **The background ticks of one scan cycle.**  From a non-replaying scan state whose clock is
`n + 1` and whose right head can move, `n` background ticks (`scan_count`) reach the same heads,
centre and counters with the clock at `1`.  Readiness of the search (needed only while the chain
is idle) and of the chain are taken as run-form inputs over the run out of `⟨c, s⟩`. -/
theorem scanBackground_run {w : List (Fin 2)} :
    ∀ (n : ℕ) (c : Control) (s : GalilVM), c.mode = .scan → c.replaying = false →
      c.clock = n + 1 → canRight s.right → OutputRel w c s →
      (∀ (k : ℕ) (y : State GalilVM),
        PalPeg.ShapedRun.ShapedSteps centre place entry q first w k ⟨c, s⟩ y →
        y.ctl.mode = .scan → y.vm.chain = .idle →
        PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get y.vm)) →
      (∀ (k : ℕ) (y : State GalilVM),
        PalPeg.ShapedRun.ShapedSteps centre place entry q first w k ⟨c, s⟩ y →
        ChainReady y.vm.chain) →
      ∃ t : GalilVM,
        StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) n ⟨c, s⟩
          ⟨{c with clock := 1}, t⟩ ∧
        t.left = s.left ∧ t.right = s.right ∧ t.center = s.center ∧ t.replay = s.replay ∧
        t.remaining = s.remaining ∧ t.radius = s.radius ∧ t.length = s.length ∧ t.fpp = s.fpp ∧
        PalPeg.ShapedRun.ShapedSteps centre place entry q first w n ⟨c, s⟩ ⟨{c with clock := 1}, t⟩ := by
  intro n
  induction n with
  | zero =>
    intro c s hm hr hclk hav hout _ _
    have hceq : ({c with clock := 1} : Control) = c := by cases c; simp_all
    refine ⟨s, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    · rw [hceq]
      exact .zero _ (fun _ _ => hout)
    · rw [hceq]
      exact .zero _
  | succ n ih =>
    intro c s hm hr hclk hav hout hready hchain
    have hQ : SoundScanNR w ⟨c, s⟩ := fun _ _ => hout
    have hsearch : ∃ v, searchEffect (PofC centre place entry w) false s v := by
      by_cases hidle : s.chain = .idle
      · exact PalPeg.GalilBranchInvariants2.searchEffect_exists _ false s
          (hready 0 ⟨c, s⟩ (.zero _) hm hidle)
      · exact ⟨searchLens.get s, Or.inr ⟨hidle, rfl⟩⟩
    have hchainAt : ∀ v : SearchVM, ∃ z, chainAt false (decide (v.search.mode = .found))
        (v.dp.config.tapes 11) ((PofC centre place entry w).centre s)
        ((PofC centre place entry w).place s) s.center s.radius s.chain z :=
      fun v => chainAt_exists false _ _ _ _ _ _ s.chain (hchain 0 ⟨c, s⟩ (.zero _))
    obtain ⟨s', hb⟩ := backgroundS_exists (PofC centre place entry w) q first s hsearch hchainAt
    have hav' : (galilFrameS (PofC centre place entry w) q first).available s := hav
    have htick : Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩
        ⟨{c with clock := c.clock - 1}, s'⟩ :=
      Tick.scan_count c s s' hm (Or.inr hav') (by omega) hb
    obtain ⟨hl', hr', -, hc', -, hrad', hlen', -, hrem', hrep', hfpp', -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    have hout' : OutputRel w {c with clock := c.clock - 1} s' :=
      outputRel_background w (PofC centre place entry w) q first hb rfl hout
    have hnr : ¬ restartVM entry s s' :=
      PalPeg.ShapedRun.not_restartVM_background centre place entry q first hb
    have hrs : (⟨c, s⟩ : State GalilVM).ctl.mode = .replayStart →
        Restarted w s' 0 reset ∧ ({c with clock := c.clock - 1} : Control).mode = .scan ∧
        ({c with clock := c.clock - 1} : Control).clock = 2048 := by
      intro h
      have h' : c.mode = .replayStart := h
      rw [hm] at h'
      cases h'
    obtain ⟨t, hrun, htl, htr, htc, htrep, htrem, htrad, htlen, htfpp, hrunS⟩ :=
      ih {c with clock := c.clock - 1} s' hm hr (by simp; omega) (hr' ▸ hav) hout'
        (fun k y hst hmy hidle => hready (k + 1) y (.succ htick (fun _ => hnr) hrs hst) hmy hidle)
        (fun k y hst => hchain (k + 1) y (.succ htick (fun _ => hnr) hrs hst))
    refine ⟨t, .succ hQ htick hrun, htl.trans hl', htr.trans hr', htc.trans hc', htrep.trans hrep',
      htrem.trans hrem', htrad.trans hrad', htlen.trans hlen', htfpp.trans hfpp',
      .succ htick (fun _ => hnr) hrs hrunS⟩

#print axioms scanBackground_run

/-- **The comparison of one scan cycle, classified.**  At clock `1` in a non-replaying scan
state whose right head can move, with a ready search co-process and chain, the tick is one of:
a match (`scan_match`: the heads move out, the clock refills, the flag is refreshed), a
mismatch confirmed by the chain (`scan_shift`), or a mismatch without the shift guard
(`scan_fallback`).  `compare_progress_gen` with the outcome and the entry data exposed. -/
theorem scanCompare_cases {w : List (Fin 2)} (c : Control) (s : GalilVM) (hm : c.mode = .scan)
    (hc : c.clock = 1) (hr : c.replaying = false) (hav : canRight s.right)
    (hsearch : ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry w) a s v)
    (hchain : ChainReady s.chain) :
    (read (left s.left) = read (right s.right) ∧
      ∃ (vq : SearchVM) (z : ChainVM) (o : Bool),
        searchEffect (PofC centre place entry w) true s vq ∧
        chainAt true (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
          ((PofC centre place entry w).centre s) ((PofC centre place entry w).place s)
          s.center s.radius s.chain z ∧
        refresh (galilFrameS (PofC centre place entry w) q first)
          (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
            (afterCompare s ⟨left s.left, right s.right, z⟩ vq)) c.output o ∧
        Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩
          ⟨{c with clock := 2048, output := o, replaying := false},
            afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
              (afterCompare s ⟨left s.left, right s.right, z⟩ vq)⟩) ∨
    (read (left s.left) ≠ read (right s.right) ∧
      ∃ (vq : SearchVM) (z : ChainVM) (t : GalilVM),
        searchEffect (PofC centre place entry w) false s vq ∧
        chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
          ((PofC centre place entry w).centre s) ((PofC centre place entry w).place s)
          s.center s.radius s.chain z ∧
        (((PofC centre place entry w).shiftGuard
            (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
              (afterMismatch s ⟨left s.left, right s.right, z⟩ vq)) ∧
          (PofC centre place entry w).beginShift
            (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
              (afterMismatch s ⟨left s.left, right s.right, z⟩ vq)) t ∧
          Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩
            ⟨{c with clock := 2048, mode := .shift}, t⟩) ∨
         (¬ (PofC centre place entry w).shiftGuard
            (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
              (afterMismatch s ⟨left s.left, right s.right, z⟩ vq)) ∧
          (PofC centre place entry w).beginFallback
            (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
              (afterMismatch s ⟨left s.left, right s.right, z⟩ vq)) t ∧
          Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩
            ⟨{c with clock := 2048, mode := .copy}, t⟩))) := by
  classical
  have hav' : (galilFrameS (PofC centre place entry w) q first).available s := hav
  have hchainAt : ∀ (a : Bool) (v : SearchVM), ∃ z, chainAt a (decide (v.search.mode = .found))
      (v.dp.config.tapes 11) ((PofC centre place entry w).centre s)
      ((PofC centre place entry w).place s) s.center s.radius s.chain z :=
    fun a v => chainAt_exists a _ _ _ _ _ _ s.chain hchain
  by_cases hmt : read (left s.left) = read (right s.right)
  · obtain ⟨vq, hq⟩ := hsearch true
    obtain ⟨z, hz⟩ := hchainAt true vq
    let vs : ScanVM := ⟨left s.left, right s.right, z⟩
    have hmt0 : (galilFrame (PofC centre place entry w) q first).matched (scanLens.set s vs) := hmt
    let born := chainBorn (decide (vq.search.mode = .found)) s.chain
    have hcmp : (galilFrameS (PofC centre place entry w) q first).compare s
        (afterBirth born (afterCompare s vs vq)) :=
      ⟨vs, vq, true, rfl, rfl, ⟨fun _ => hmt0, fun _ => rfl⟩, hq, hz, rfl⟩
    have hmt1 : (galilFrameS (PofC centre place entry w) q first).matched
        (afterBirth born (afterCompare s vs vq)) := by
      show read (afterBirth born (afterCompare s vs vq)).left
        = read (afterBirth born (afterCompare s vs vq)).right
      rw [afterBirth_left, afterBirth_right]
      exact hmt
    let s'' : GalilVM := replayDec c.replaying (afterBirth born (afterCompare s vs vq))
    let o : Bool := if (PofC centre place entry w).onLetter s''
      then decide ((PofC centre place entry w).leftFirst s'') else c.output
    have ho : refresh (galilFrameS (PofC centre place entry w) q first) s'' c.output o := by
      refine ⟨fun hl => ?_, fun hl => ?_⟩
      · have hl' : (PofC centre place entry w).onLetter s'' := hl
        show (if (PofC centre place entry w).onLetter s''
          then decide ((PofC centre place entry w).leftFirst s'') else c.output) = true ↔
          (PofC centre place entry w).leftFirst s''
        rw [if_pos hl']
        exact decide_eq_true_iff
      · have hl' : ¬ (PofC centre place entry w).onLetter s'' := hl
        show (if (PofC centre place entry w).onLetter s''
          then decide ((PofC centre place entry w).leftFirst s'') else c.output) = c.output
        rw [if_neg hl']
    have htick := Tick.scan_match (F := galilFrameS (PofC centre place entry w) q first)
      (delay := 2048) c s _ s'' o hm (Or.inr hav') hc hcmp hmt1
      (matchedPlace_replayDec (PofC centre place entry w) q first c.replaying _) ho
    have hs'' : s'' = afterBirth born (afterCompare s vs vq) := by
      show replayDec c.replaying _ = _
      rw [hr]; rfl
    rw [hs''] at ho htick
    rw [hr] at htick
    exact Or.inl ⟨hmt, vq, z, o, hq, hz, ho, htick⟩
  · obtain ⟨vq, hq⟩ := hsearch false
    obtain ⟨z, hz⟩ := hchainAt false vq
    let vs : ScanVM := ⟨left s.left, right s.right, z⟩
    have hmt0 : ¬ (galilFrame (PofC centre place entry w) q first).matched (scanLens.set s vs) := hmt
    let born := chainBorn (decide (vq.search.mode = .found)) s.chain
    have hcmp : (galilFrameS (PofC centre place entry w) q first).compare s
        (afterBirth born (afterMismatch s vs vq)) :=
      ⟨vs, vq, false, rfl, rfl, Iff.intro (fun h0 => by cases h0) (fun h0 => absurd h0 hmt0),
        hq, hz, rfl⟩
    have hmt1 : ¬ (galilFrameS (PofC centre place entry w) q first).matched
        (afterBirth born (afterMismatch s vs vq)) := by
      intro h0
      apply hmt
      have h1 : read (afterBirth born (afterMismatch s vs vq)).left
        = read (afterBirth born (afterMismatch s vs vq)).right := h0
      rw [afterBirth_left, afterBirth_right] at h1
      exact h1
    by_cases hg : (PofC centre place entry w).shiftGuard (afterBirth born (afterMismatch s vs vq))
    · obtain ⟨t, hb⟩ := beginShift_exists (afterBirth born (afterMismatch s vs vq)) hg
      exact Or.inr ⟨hmt, vq, z, t, hq, hz, Or.inl ⟨hg, hb,
        Tick.scan_shift (F := galilFrameS (PofC centre place entry w) q first) (delay := 2048)
          c s _ t hm (Or.inr hav') hc hcmp hmt1 hr hg hb⟩⟩
    · obtain ⟨t, hb⟩ := beginFallback_exists (afterBirth born (afterMismatch s vs vq))
      exact Or.inr ⟨hmt, vq, z, t, hq, hz, Or.inr ⟨hg, hb,
        Tick.scan_fallback (F := galilFrameS (PofC centre place entry w) q first) (delay := 2048)
          c s _ t hm (Or.inr hav') hc hcmp hmt1 (Or.inr hg) hr hb⟩⟩

#print axioms scanCompare_cases

/-! ## One scan cycle out of a state of the packed run -/

/-- A tick keeps the clock positive. -/
theorem tick_one_le_clock {F : Frame GalilVM} {x y : State GalilVM} (h : Tick F 2048 x y)
    (h1 : 1 ≤ x.ctl.clock) : 1 ≤ y.ctl.clock := by
  cases h <;> dsimp only at h1 ⊢ <;> omega

/-- Along a run the clock stays in `[1, 2048]`. -/
theorem steps_clock_bounds {F : Frame GalilVM} {k : ℕ} {x y : State GalilVM}
    (h : Steps F 2048 k x y) (h1 : 1 ≤ x.ctl.clock) (h2 : x.ctl.clock ≤ 2048) :
    1 ≤ y.ctl.clock ∧ y.ctl.clock ≤ 2048 := by
  induction h with
  | zero _ => exact ⟨h1, h2⟩
  | succ ht _ ih => exact ih (tick_one_le_clock ht h1) (tick_bounded _ _ ht h2)

/-- The clock of an `InvLPS` state is the full delay. -/
theorem invLPS_clock {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hI : InvLPS (PofC centre place entry w) q first w c s) : c.clock = 2048 := by
  rcases hI.1.1.1.1.1 with h | ⟨k, h⟩
  · exact h.mode.2.2
  · exact h.mode.2.2

/-- The cost record of one matched comparison cycle: `wait` background ticks and the
comparison, no shift, no fallback. -/
def matchPiece (placeN wait : ℕ) (hw : wait ≤ 2048) : Piece :=
  ⟨placeN, [], [], wait, true, hw, by simp, by simp⟩

theorem matchPiece_ticks (placeN wait : ℕ) (hw : wait ≤ 2048) :
    (matchPiece placeN wait hw).ticks = wait + 1 := by
  simp [matchPiece, Piece.ticks, Piece.ev, Piece.cmpN, PlaceEvent.slot, PlaceEvent.shiftTicks,
    PlaceEvent.fbTicks, PlaceEvent.replayTicks]

theorem matchPiece_adv (placeN wait : ℕ) (hw : wait ≤ 2048) :
    (matchPiece placeN wait hw).adv = 0 := by
  simp [matchPiece, Piece.adv, Piece.ev, PlaceEvent.adv, PlaceEvent.shiftAdv, PlaceEvent.fbAdv]

/-- **One scan cycle out of a state of the packed run: the matched comparison is progress or
the report.**  From a non-replaying, refreshed scan state on the packed run out of an `InvLPS`
origin, with its right head at or below the report place `2m − 1`:

* at the report place the state itself is the report (`ReachAtOn`, zero ticks);
* below it, `clock − 1` background ticks and the comparison run; if the comparison matches,
  the landing is again such a state one place further right (`mu` decreases), or the report
  when that place is `2m − 1`; if it mismatches, the comparison state is handed back.

The three run-form inputs are the leaves still to be discharged along runs out of `InvLPS`:
readiness of the search while the chain is idle, readiness of the chain, and the centre
invariant `MInv`. -/
theorem scanCycle_of_leaves {w : List (Fin 2)} (hP : Decodes (PofC centre place entry w))
    (h4 : first ≠ 4) {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ w.length) {c : Control} {s : GalilVM}
    (hI : PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centre place entry q first w c s)
    (hp : position s.right ≤ 2 * m - 1)
    (hready : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (y : State GalilVM),
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      PalPeg.ShapedRun.ShapedSteps centre place entry q first w k ⟨c₀, r₀⟩ y →
      y.ctl.mode = .scan → y.vm.chain = .idle →
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get y.vm))
    (hchain : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (y : State GalilVM),
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      PalPeg.ShapedRun.ShapedSteps centre place entry q first w k ⟨c₀, r₀⟩ y →
      ChainReady y.vm.chain) :
    PalPeg.CloseoutCheckW.CycleOutOn centre place entry q first
      (PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centre place entry q first) w m c s ∨
    (position s.right < 2 * m - 1 ∧ ∃ t : GalilVM,
      StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w)
        (c.clock - 1) ⟨c, s⟩ ⟨{c with clock := 1}, t⟩ ∧
      PalPeg.ShapedRun.ShapedSteps centre place entry q first w (c.clock - 1) ⟨c, s⟩ ⟨{c with clock := 1}, t⟩ ∧
      t.left = s.left ∧ t.right = s.right ∧ t.center = s.center ∧ t.replay = s.replay ∧
      read (left t.left) ≠ read (right t.right)) := by
  classical
  obtain ⟨⟨hm, hr⟩, hf, hminvS, c₀, r₀, j, hI₀, hrun, jS, hsh⟩ := hI
  have hpack : IPackMW centre place entry q first w ⟨c, s⟩ :=
    PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMW centre place entry q first hrun
  obtain ⟨g, hg0, hgj, htr, -⟩ := id hrun
  have hjx : Steps (galilFrameS (PofC centre place entry w) q first) 2048 j ⟨c₀, r₀⟩ ⟨c, s⟩ := by
    have := PalPeg.CloseoutPackRun2.steps_of_trace htr j le_rfl
    rwa [hg0, hgj] at this
  have hout : OutputRel w c s := by
    have := htr.good j le_rfl
    rw [hgj] at this
    exact this hm hr
  obtain ⟨hclk1, hclk2⟩ := steps_clock_bounds hjx (by rw [invLPS_clock centre place entry q first hI₀]; decide)
    (by rw [invLPS_clock centre place entry q first hI₀])
  have hclk1' : 1 ≤ c.clock := hclk1
  have hclk2' : c.clock ≤ 2048 := hclk2
  obtain ⟨hrep, hpres⟩ := PalPeg.WindowPack.rightHead_of_packs hpack.pack hpack.m2 hm
  have hlength : (encoded w).length = 2 * w.length + 1 := by simp [encoded, pairs_length]
  have hav : canRight s.right := canRight_of_bound _ w hrep hpres (by omega)
  obtain ⟨rad, hsi⟩ := hpack.pack.scanGeom hm hr
  -- the report place: the state is the report
  by_cases hat : position s.right = 2 * m - 1
  · left; left
    have hstI0 : PalPeg.CloseoutCheckW.StepsIMW centre place entry q first w 0 ⟨c, s⟩ ⟨c, s⟩ :=
      ⟨fun _ => ⟨c, s⟩, rfl, rfl, ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ _ _ => hout⟩,
        fun _ _ => hpack⟩
    have hrp : PalPeg.GalilReportPrefix.ReportPointAt w m ⟨c, s⟩ :=
      ⟨hr, ⟨rad, hsi⟩, hminvS, hat, hm1, hmle⟩
    refine ⟨⟨c, s⟩, 0, [], hstI0, costedRun_nil s, hrp, hf, fun _ => ⟨c, s, 0, [], hstI0,
      costedRun_nil s, ⟨⟨hm, hr⟩, hf, hminvS, c₀, r₀, j, hI₀, hrun, jS, hsh⟩, by omega⟩⟩
  have hlt : position s.right < 2 * m - 1 := lt_of_le_of_ne hp hat
  -- the background ticks
  obtain ⟨t, hbg, htl, htr', htc, htrep, htrem, htrad, htlen, htfpp, hbgS⟩ :=
    scanBackground_run centre place entry q first (c.clock - 1) c s hm hr (by omega) hav hout
      (fun k y hst hmy hidle => hready c₀ r₀ (jS + k) y hI₀
        (PalPeg.ShapedRun.shapedSteps_trans centre place entry q first hsh hst) hmy hidle)
      (fun k y hst => hchain c₀ r₀ (jS + k) y hI₀
        (PalPeg.ShapedRun.shapedSteps_trans centre place entry q first hsh hst))
  have hjtS : PalPeg.ShapedRun.ShapedSteps centre place entry q first w (jS + (c.clock - 1)) ⟨c₀, r₀⟩ ⟨{c with clock := 1}, t⟩ :=
    PalPeg.ShapedRun.shapedSteps_trans centre place entry q first hsh hbgS
  have hrsT : (⟨{c with clock := 1}, t⟩ : State GalilVM).ctl.mode = .replayStart → False := by
    intro h
    have h' : c.mode = .replayStart := h
    rw [hm] at h'
    cases h'
  have hav' : canRight t.right := by rw [htr']; exact hav
  have hsearch : ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry w) a t v := by
    intro a
    by_cases hidle : t.chain = .idle
    · exact PalPeg.GalilBranchInvariants2.searchEffect_exists _ a t
        (hready c₀ r₀ _ _ hI₀ hjtS hm hidle)
    · exact ⟨searchLens.get t, Or.inr ⟨hidle, rfl⟩⟩
  have hchainT : ChainReady t.chain := hchain c₀ r₀ _ _ hI₀ hjtS
  have hsiT : ScanInvariant w (position t.center) rad t.left t.right := by
    rw [htl, htr', htc]; exact hsi
  rcases scanCompare_cases centre place entry q first {c with clock := 1} t hm rfl hr hav' hsearch
      hchainT with ⟨hmt, vq, z, o, hq, hz, ho, htick⟩ | ⟨hmis, -⟩
  · -- a matched comparison: one place further right
    left
    set born := chainBorn (decide (vq.search.mode = .found)) t.chain with hborn
    set s' := afterBirth born (afterCompare t ⟨left t.left, right t.right, z⟩ vq) with hs'
    set c' : Control := {c with clock := 2048, output := o, replaying := false} with hc'
    have hs'r : s'.right = right t.right := by
      rw [hs', afterBirth_right, afterCompare_right]
    have hs'l : s'.left = left t.left := by
      rw [hs', afterBirth_left, afterCompare_left]
    have hs'c : s'.center = t.center := by
      rw [hs', afterBirth_center, afterCompare_center]
    have hpos' : position s'.right = position s.right + 1 := by
      rw [hs'r, ← htr']
      exact right_position _ hav' (represented_position _ w (htr' ▸ hrep) (htr' ▸ hpres)).1
    have hsi' : ScanInvariant w (position s'.center) (rad + 1) s'.left s'.right := by
      rw [hs'l, hs'r, hs'c]
      exact scanInvariant_matched hsiT hav' hmt
    have hout' : OutputRel w c' s' := by
      have h1 := outputRel_of_refresh w (PofC centre place entry w) rfl rfl q first
        {c with clock := 1} s' o hsi' ho
      exact outputRel_transfer w rfl rfl h1
    have hQ' : SoundScanNR w ⟨c', s'⟩ := fun _ _ => hout'
    have htick' : Tick (galilFrameS (PofC centre place entry w) q first) 2048
        ⟨{c with clock := 1}, t⟩ ⟨c', s'⟩ := htick
    have hall : StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w)
        (c.clock - 1 + 1) ⟨c, s⟩ ⟨c', s'⟩ :=
      stepsAll_trans hbg (.succ (fun _ _ => by
        have : OutputRel w {c with clock := 1} t := outputRel_transfer w htr' rfl hout
        exact this) htick' (.zero _ hQ'))
    have hstI : PalPeg.CloseoutCheckW.StepsIMW centre place entry q first w (c.clock - 1 + 1)
        ⟨c, s⟩ ⟨c', s'⟩ :=
      PalPeg.CloseoutMarksPack.packRunR_MW_marksFree centre place entry q first h4 hP c₀ r₀ hI₀
        m hm1 hmle j ⟨c, s⟩ hjx _ ⟨c', s'⟩ hpack hall rfl (by show position s'.right ≤ 2 * m - 1; omega)
    have hminv' : MInv w c' s' := by
      have h1 : MInv w {c with clock := 1} t := minv_same rfl htr' htc htrep hminvS
      have h2 := minv_match (raw := w) (c := {c with clock := 1}) (vs := ⟨left t.left, right t.right, z⟩)
        (vq := vq) o 2048 hr rfl rfl hav' hmt hsiT h1
      exact minv_afterBirth born h2
    have hf' : Refreshed (PofC centre place entry w) q first ⟨c', s'⟩ := ⟨c.output, ho⟩
    have hnr' : ¬ restartVM entry t s' :=
      PalPeg.ShapedRun.not_restartVM_of_chainAt_target entry hz
        (by rw [hs', afterBirth_chain, afterCompare_chain])
    have hI' : PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centre place entry q first w c' s' :=
      ⟨⟨hm, rfl⟩, hf', hminv', c₀, r₀, _, hI₀,
        PalPeg.CloseoutCheckW.stepsIMW_trans centre place entry q first hrun hstI, _,
        PalPeg.ShapedRun.shapedSteps_trans centre place entry q first hjtS
          (.succ htick' (fun _ => hnr') (fun h => absurd h hrsT) (.zero _))⟩
    have hcr : CostedRun s s' (c.clock - 1 + 1) [matchPiece (position s'.right) (c.clock - 1) (by omega)] := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [matchPiece_ticks]
      · simp [matchPiece_adv, hs'c, htc]
      · omega
      · intro p hp; simp at hp; subst hp; simp [matchPiece]; omega
      · simp
    by_cases hat' : position s'.right = 2 * m - 1
    · left
      have hpack' : IPackMW centre place entry q first w ⟨c', s'⟩ :=
        PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMW centre place entry q first hstI
      have hstI0 : PalPeg.CloseoutCheckW.StepsIMW centre place entry q first w 0 ⟨c', s'⟩ ⟨c', s'⟩ :=
        ⟨fun _ => ⟨c', s'⟩, rfl, rfl, ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => hQ'⟩,
          fun _ _ => hpack'⟩
      have hrp : PalPeg.GalilReportPrefix.ReportPointAt w m ⟨c', s'⟩ :=
        ⟨rfl, ⟨rad + 1, hsi'⟩, hminv', hat', hm1, hmle⟩
      exact ⟨⟨c', s'⟩, _, _, hstI, hcr, hrp, hf', fun _ => ⟨c', s', 0, [], hstI0,
        costedRun_nil s', hI', by omega⟩⟩
    · right
      refine ⟨c', s', _, _, hstI, hcr, hI', ?_, by omega⟩
      unfold mu
      rw [hs'c, htc, hpos']
      have : position s.right + 1 ≤ 2 * w.length := by omega
      omega
  · right
    exact ⟨hlt, t, hbg, hbgS, htl, htr', htc, htrep, hmis⟩

#print axioms scanCycle_of_leaves

/-! ## The whole oracle from five run-form leaves -/

/-- The cost record of a comparison that entered a shift: `wait` background ticks, the
comparison, and `n ≤ adv + 1` shift-phase ticks advancing the centre by `adv ≥ 1`. -/
def shiftPiece (placeN wait n adv : ℕ) (hw : wait ≤ 2048) (hadv : 1 ≤ adv) (hn : n ≤ adv + 1) :
    Piece :=
  ⟨placeN, [⟨n, adv, hadv, hn⟩], [], wait, true, hw, by simp, by simp⟩

theorem shiftPiece_ticks (placeN wait n adv : ℕ) (hw : wait ≤ 2048) (hadv : 1 ≤ adv)
    (hn : n ≤ adv + 1) : (shiftPiece placeN wait n adv hw hadv hn).ticks = n + wait + 1 := by
  simp [shiftPiece, Piece.ticks, Piece.ev, Piece.cmpN, PlaceEvent.slot, PlaceEvent.shiftTicks,
    PlaceEvent.fbTicks, PlaceEvent.replayTicks, ShiftEv.ticks]

theorem shiftPiece_adv (placeN wait n adv : ℕ) (hw : wait ≤ 2048) (hadv : 1 ≤ adv)
    (hn : n ≤ adv + 1) : (shiftPiece placeN wait n adv hw hadv hn).adv = adv := by
  simp [shiftPiece, Piece.adv, Piece.ev, PlaceEvent.adv, PlaceEvent.shiftAdv, PlaceEvent.fbAdv,
    ShiftEv.adv]

/-- The cost record of a comparison that entered a fallback: `wait` background ticks, the
comparison, the fallback (`fb` ticks) and its replay (`replay` ticks) at window radius `k` and
chosen radius `r ≤ k`. -/
def fallbackPiece (placeN wait k r fb replay : ℕ) (hw : wait ≤ 2048) (hr : r ≤ k)
    (hfb : fb ≤ 12704 * (k + 1 - r) + 4012) (hre : replay ≤ 8 * 2048 * (k + 1 - r)) : Piece :=
  ⟨placeN, [], [⟨k, r, fb, replay, hr, hfb, hre⟩], wait, true, hw, by simp, by simp⟩

theorem fallbackPiece_ticks (placeN wait k r fb replay : ℕ) (hw : wait ≤ 2048) (hr : r ≤ k)
    (hfb : fb ≤ 12704 * (k + 1 - r) + 4012) (hre : replay ≤ 8 * 2048 * (k + 1 - r)) :
    (fallbackPiece placeN wait k r fb replay hw hr hfb hre).ticks = fb + replay + wait + 1 := by
  simp [fallbackPiece, Piece.ticks, Piece.ev, Piece.cmpN, PlaceEvent.slot, PlaceEvent.shiftTicks,
    PlaceEvent.fbTicks, PlaceEvent.replayTicks]

theorem fallbackPiece_adv (placeN wait k r fb replay : ℕ) (hw : wait ≤ 2048) (hr : r ≤ k)
    (hfb : fb ≤ 12704 * (k + 1 - r) + 4012) (hre : replay ≤ 8 * 2048 * (k + 1 - r)) :
    (fallbackPiece placeN wait k r fb replay hw hr hfb hre).adv = k + 1 - r := by
  simp [fallbackPiece, Piece.adv, Piece.ev, PlaceEvent.adv, PlaceEvent.shiftAdv, PlaceEvent.fbAdv,
    FallbackEv.adv]

/-- **The run-shaped cycle oracle from five leaves along runs out of `InvLPS` origins**:
readiness of the search while the chain is idle, readiness of the chain, the centre invariant,
the shift phase (from its entry tick to a refreshed scan landing, at most `adv + 1` ticks for a
centre advance of `adv ≥ 1`, right head kept), and the fallback with its replay (to a refreshed
scan landing one place right of the mismatch, with the window/chosen radii and the tick
budgets of `FallbackEv`).  Everything else — background ticks, the comparison, packs, the cost
ledger, `mu` — is `scanCycle_of_leaves` and the two phase cases below. -/
theorem cycleOracleOn_of_leaves {w : List (Fin 2)} (hP : Decodes (PofC centre place entry w))
    (h4 : first ≠ 4)
    (hready : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (y : State GalilVM),
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      PalPeg.ShapedRun.ShapedSteps centre place entry q first w k ⟨c₀, r₀⟩ y →
      y.ctl.mode = .scan → y.vm.chain = .idle →
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get y.vm))
    (hchain : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (y : State GalilVM),
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      PalPeg.ShapedRun.ShapedSteps centre place entry q first w k ⟨c₀, r₀⟩ y →
      ChainReady y.vm.chain)
    (hshift : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (c : Control) (s : GalilVM) (vq : SearchVM)
      (z : ChainVM) (u : GalilVM) (m : ℕ), 1 ≤ m → m ≤ w.length →
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      PalPeg.CloseoutCheckW.StepsIMW centre place entry q first w k ⟨c₀, r₀⟩ ⟨c, s⟩ →
      c.mode = .scan → c.replaying = false → c.clock = 1 → position s.right + 1 ≤ 2 * m - 1 →
      MInv w c s →
      read (left s.left) ≠ read (right s.right) →
      searchEffect (PofC centre place entry w) false s vq →
      chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
        ((PofC centre place entry w).centre s) ((PofC centre place entry w).place s)
        s.center s.radius s.chain z →
      (PofC centre place entry w).shiftGuard
        (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
          (afterMismatch s ⟨left s.left, right s.right, z⟩ vq)) →
      (PofC centre place entry w).beginShift
        (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
          (afterMismatch s ⟨left s.left, right s.right, z⟩ vq)) u →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩
        ⟨{c with clock := 2048, mode := .shift}, u⟩ →
      ∃ (c' : Control) (s' : GalilVM) (n : ℕ),
        StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) n
          ⟨{c with clock := 2048, mode := .shift}, u⟩ ⟨c', s'⟩ ∧
        PalPeg.ShapedRun.ShapedSteps centre place entry q first w n ⟨{c with clock := 2048, mode := .shift}, u⟩ ⟨c', s'⟩ ∧
        c'.mode = .scan ∧ c'.replaying = false ∧
        Refreshed (PofC centre place entry w) q first ⟨c', s'⟩ ∧ MInv w c' s' ∧
        position s'.right = position s.right + 1 ∧ position s.center < position s'.center ∧
        n ≤ position s'.center - position s.center + 1)
    (hfallback : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (c : Control) (s : GalilVM) (vq : SearchVM)
      (z : ChainVM) (u : GalilVM) (m : ℕ), 1 ≤ m → m ≤ w.length →
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      PalPeg.CloseoutCheckW.StepsIMW centre place entry q first w k ⟨c₀, r₀⟩ ⟨c, s⟩ →
      c.mode = .scan → c.replaying = false → c.clock = 1 → position s.right + 1 ≤ 2 * m - 1 →
      MInv w c s →
      read (left s.left) ≠ read (right s.right) →
      searchEffect (PofC centre place entry w) false s vq →
      chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
        ((PofC centre place entry w).centre s) ((PofC centre place entry w).place s)
        s.center s.radius s.chain z →
      ¬ (PofC centre place entry w).shiftGuard
        (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
          (afterMismatch s ⟨left s.left, right s.right, z⟩ vq)) →
      (PofC centre place entry w).beginFallback
        (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
          (afterMismatch s ⟨left s.left, right s.right, z⟩ vq)) u →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩
        ⟨{c with clock := 2048, mode := .copy}, u⟩ →
      ∃ (c' : Control) (s' : GalilVM) (kk r fb replay : ℕ),
        StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w)
          (fb + replay) ⟨{c with clock := 2048, mode := .copy}, u⟩ ⟨c', s'⟩ ∧
        PalPeg.ShapedRun.ShapedSteps centre place entry q first w (fb + replay) ⟨{c with clock := 2048, mode := .copy}, u⟩ ⟨c', s'⟩ ∧
        c'.mode = .scan ∧ c'.replaying = false ∧
        Refreshed (PofC centre place entry w) q first ⟨c', s'⟩ ∧ MInv w c' s' ∧
        position s'.right = position s.right + 1 ∧ r ≤ kk ∧
        position s'.center = position s.center + (kk + 1 - r) ∧
        fb ≤ 12704 * (kk + 1 - r) + 4012 ∧ replay ≤ 8 * 2048 * (kk + 1 - r)) :
    PalPeg.CloseoutCheckW.CycleOracleOn centre place entry q first
      (PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centre place entry q first) w := by
  classical
  intro m c s hm1 hmle hI hp
  rcases scanCycle_of_leaves centre place entry q first hP h4 hm1 hmle hI hp hready hchain
    with hdone | ⟨hlt, t, hbg, hbgS, htl, htr', htc, htrep, hmis⟩
  · exact hdone
  -- the comparison state after the background ticks
  obtain ⟨⟨hm, hr⟩, hf, hminvS, c₀, r₀, j, hI₀, hrun, jS, hsh⟩ := hI
  have hpack : IPackMW centre place entry q first w ⟨c, s⟩ :=
    PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMW centre place entry q first hrun
  obtain ⟨g, hg0, hgj, htr, -⟩ := id hrun
  have hjx : Steps (galilFrameS (PofC centre place entry w) q first) 2048 j ⟨c₀, r₀⟩ ⟨c, s⟩ := by
    have := PalPeg.CloseoutPackRun2.steps_of_trace htr j le_rfl
    rwa [hg0, hgj] at this
  have hout : OutputRel w c s := by
    have := htr.good j le_rfl
    rw [hgj] at this
    exact this hm hr
  obtain ⟨hclk1, hclk2⟩ := steps_clock_bounds hjx
    (by rw [invLPS_clock centre place entry q first hI₀]; decide)
    (by rw [invLPS_clock centre place entry q first hI₀])
  have hclk1' : 1 ≤ c.clock := hclk1
  have hclk2' : c.clock ≤ 2048 := hclk2
  obtain ⟨hrep, hpres⟩ := PalPeg.WindowPack.rightHead_of_packs hpack.pack hpack.m2 hm
  have hlength : (encoded w).length = 2 * w.length + 1 := by simp [encoded, pairs_length]
  have hav : canRight s.right := canRight_of_bound _ w hrep hpres (by omega)
  have hjtS : PalPeg.ShapedRun.ShapedSteps centre place entry q first w (jS + (c.clock - 1)) ⟨c₀, r₀⟩ ⟨{c with clock := 1}, t⟩ :=
    PalPeg.ShapedRun.shapedSteps_trans centre place entry q first hsh hbgS
  have hrsT : (⟨{c with clock := 1}, t⟩ : State GalilVM).ctl.mode = .replayStart → False := by
    intro h
    have h' : c.mode = .replayStart := h
    rw [hm] at h'
    cases h'
  have hav' : canRight t.right := by rw [htr']; exact hav
  have hsearch : ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry w) a t v := by
    intro a
    by_cases hidle : t.chain = .idle
    · exact PalPeg.GalilBranchInvariants2.searchEffect_exists _ a t
        (hready c₀ r₀ _ _ hI₀ hjtS hm hidle)
    · exact ⟨searchLens.get t, Or.inr ⟨hidle, rfl⟩⟩
  have hchainT : ChainReady t.chain := hchain c₀ r₀ _ _ hI₀ hjtS
  have hminvT : MInv w {c with clock := 1} t := minv_same rfl htr' htc htrep hminvS
  have hQt : SoundScanNR w ⟨{c with clock := 1}, t⟩ :=
    fun _ _ => outputRel_transfer w htr' rfl hout
  rcases scanCompare_cases centre place entry q first {c with clock := 1} t hm rfl hr hav' hsearch
      hchainT with ⟨hmt, -⟩ | ⟨-, vq, z, u, hq, hz, hcase⟩
  · exact absurd hmt hmis
  -- the packed prefix up to the comparison state
  have hrunT : PalPeg.CloseoutCheckW.StepsIMW centre place entry q first w (j + (c.clock - 1))
      ⟨c₀, r₀⟩ ⟨{c with clock := 1}, t⟩ :=
    PalPeg.CloseoutCheckW.stepsIMW_trans centre place entry q first hrun
      (PalPeg.CloseoutMarksPack.packRunR_MW_marksFree centre place entry q first h4 hP c₀ r₀ hI₀
        m hm1 hmle j ⟨c, s⟩ hjx _ ⟨{c with clock := 1}, t⟩ hpack hbg hr
        (by show position t.right ≤ 2 * m - 1; rw [htr']; omega))
  have hpT : position t.right + 1 ≤ 2 * m - 1 := by rw [htr']; omega
  -- the landing of either phase is a state of the run one place further right
  have hland : ∀ (y : State GalilVM) (c' : Control) (s' : GalilVM) (n : ℕ),
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨{c with clock := 1}, t⟩ y →
      ¬ restartVM entry t y.vm →
      y.ctl.mode ≠ .scan →
      StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) n y ⟨c', s'⟩ →
      PalPeg.ShapedRun.ShapedSteps centre place entry q first w n y ⟨c', s'⟩ →
      c'.mode = .scan → c'.replaying = false →
      Refreshed (PofC centre place entry w) q first ⟨c', s'⟩ →
      MInv w c' s' →
      position s'.right = position s.right + 1 →
      StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w)
        (c.clock - 1 + 1 + n) ⟨c, s⟩ ⟨c', s'⟩ ∧
      PalPeg.CloseoutCheckW.StepsIMW centre place entry q first w (c.clock - 1 + 1 + n)
        ⟨c, s⟩ ⟨c', s'⟩ ∧
      PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centre place entry q first w c' s' := by
    intro y c' s' n hty hnr hym hphase hphaseS hm' hr' hf' hminvL hpos'
    have hQy : SoundScanNR w y := fun h => absurd h hym
    have hall : StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w)
        (c.clock - 1 + 1 + n) ⟨c, s⟩ ⟨c', s'⟩ :=
      stepsAll_trans (stepsAll_trans hbg (.succ hQt hty (.zero _ hQy))) hphase
    have hstI : PalPeg.CloseoutCheckW.StepsIMW centre place entry q first w (c.clock - 1 + 1 + n)
        ⟨c, s⟩ ⟨c', s'⟩ :=
      PalPeg.CloseoutMarksPack.packRunR_MW_marksFree centre place entry q first h4 hP c₀ r₀ hI₀
        m hm1 hmle j ⟨c, s⟩ hjx _ ⟨c', s'⟩ hpack hall hr'
        (by show position s'.right ≤ 2 * m - 1; omega)
    exact ⟨hall, hstI, ⟨⟨hm', hr'⟩, hf', hminvL, c₀, r₀, _, hI₀,
      PalPeg.CloseoutCheckW.stepsIMW_trans centre place entry q first hrun hstI, _,
      PalPeg.ShapedRun.shapedSteps_trans centre place entry q first hjtS
        (.succ hty (fun _ => hnr) (fun h => absurd h hrsT) hphaseS)⟩⟩
  -- the report or the progress out of a landing
  have hfinish : ∀ (c' : Control) (s' : GalilVM) (K : ℕ) (L : List Piece),
      PalPeg.CloseoutCheckW.StepsIMW centre place entry q first w K ⟨c, s⟩ ⟨c', s'⟩ →
      CostedRun s s' K L →
      PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centre place entry q first w c' s' →
      position s'.right = position s.right + 1 → position s.center < position s'.center →
      PalPeg.CloseoutCheckW.CycleOutOn centre place entry q first
        (PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centre place entry q first) w m c s := by
    intro c' s' K L hstI hcr hI' hpos' hcen'
    obtain ⟨⟨hm', hr'⟩, hf', hminv', c₀', r₀', j', hI₀', hrun', jS', hsh'⟩ := id hI'
    have hpack' : IPackMW centre place entry q first w ⟨c', s'⟩ :=
      PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMW centre place entry q first hstI
    have hQ' : SoundScanNR w ⟨c', s'⟩ := by
      obtain ⟨g', -, hgj', htr'', -⟩ := hrun'
      have := htr''.good j' le_rfl
      rw [hgj'] at this
      exact this
    obtain ⟨rad', hsi'⟩ := hpack'.pack.scanGeom hm' hr'
    by_cases hat' : position s'.right = 2 * m - 1
    · left
      have hstI0 : PalPeg.CloseoutCheckW.StepsIMW centre place entry q first w 0 ⟨c', s'⟩ ⟨c', s'⟩ :=
        ⟨fun _ => ⟨c', s'⟩, rfl, rfl, ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => hQ'⟩,
          fun _ _ => hpack'⟩
      have hrp : PalPeg.GalilReportPrefix.ReportPointAt w m ⟨c', s'⟩ :=
        ⟨hr', ⟨rad', hsi'⟩, hminv', hat', hm1, hmle⟩
      exact ⟨⟨c', s'⟩, K, L, hstI, hcr, hrp, hf', fun _ => ⟨c', s', 0, [], hstI0,
        costedRun_nil s', hI', by omega⟩⟩
    · right
      refine ⟨c', s', K, L, hstI, hcr, hI', ?_, by omega⟩
      unfold mu
      have h1 : position s'.center ≤ 2 * w.length := by
        have hrp' : position s'.right = position s'.center + rad' := hsi'.rightPos
        omega
      exact lex_lt (2 * w.length) _ _ _ _ (by omega) (by omega)
  rcases hcase with ⟨hg, hb, htick⟩ | ⟨hng, hb, htick⟩
  · -- the shift phase
    obtain ⟨c', s', n, hphase, hphaseS, hm', hr', hf', hminvL, hpos', hcen', hn⟩ :=
      hshift c₀ r₀ _ {c with clock := 1} t vq z u m hm1 hmle hI₀ hrunT hm hr rfl hpT hminvT hmis hq hz hg hb
        htick
    rw [htr'] at hpos'
    rw [htc] at hcen' hn
    have hnr : ¬ restartVM entry t u := by
      obtain ⟨wg, hwg, -⟩ := hg
      rw [afterBirth_chain, afterMismatch_chain] at hwg
      have hzw : z = .watch wg := hwg
      exact PalPeg.ShapedRun.not_restartVM_of_chainAt entry hz
        (fun w' hw' => by rw [hzw] at hw'; cases hw')
    obtain ⟨hall, hstI, hI'⟩ := hland _ c' s' n htick hnr (by simp) hphase hphaseS hm' hr' hf' hminvL hpos'
    refine hfinish c' s' _ [shiftPiece (position s'.right) (c.clock - 1) n
      (position s'.center - position s.center) (by omega) (by omega) hn] hstI ?_ hI' hpos' hcen'
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [shiftPiece_ticks]; omega
    · simp [shiftPiece_adv]; omega
    · omega
    · intro p hp; simp at hp; subst hp; simp [shiftPiece]; omega
    · simp
  · -- the fallback and its replay
    obtain ⟨c', s', kk, r, fb, replay, hphase, hphaseS, hm', hr', hf', hminvL, hpos', hrk, hcen', hfb, hre⟩ :=
      hfallback c₀ r₀ _ {c with clock := 1} t vq z u m hm1 hmle hI₀ hrunT hm hr rfl hpT hminvT hmis hq hz hng hb
        htick
    rw [htr'] at hpos'
    rw [htc] at hcen'
    have hnr : ¬ restartVM entry t u := by
      obtain ⟨p, hbp, -⟩ := hb
      refine PalPeg.ShapedRun.not_restartVM_of_radius entry ?_
      rw [hbp]
      show value (afterBirth _ (afterMismatch t _ vq)).radius ≠ value t.radius
      rw [afterBirth_radius, afterMismatch_radius, inc_value]
      omega
    obtain ⟨hall, hstI, hI'⟩ := hland _ c' s' _ htick hnr (by simp) hphase hphaseS hm' hr' hf' hminvL hpos'
    refine hfinish c' s' _ [fallbackPiece (position s'.right) (c.clock - 1) kk r fb replay
      (by omega) hrk hfb hre] hstI ?_ hI' hpos' (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [fallbackPiece_ticks]; omega
    · simp [fallbackPiece_adv]; omega
    · omega
    · intro p hp; simp at hp; subst hp; simp [fallbackPiece]; omega
    · simp

#print axioms cycleOracleOn_of_leaves

/-! ## The shift phase in the `PofC` frame -/

/-- **The unit moves of a shift phase.**  With a copy-idle VM whose chain is the watch `wch`, a
chain shift run of `n` units is `n` `shift_one` ticks of `galilFrameS` keeping the control
(`shift_run_lift` per unit, pulled through `shiftLens`, transferred by `shift_transfer` and
`tick_S_of_tick`). -/
theorem shiftUnits_S {w : List (Fin 2)} (c : Control) (hm : c.mode = .shift) :
    ∀ (n : ℕ) (s : GalilVM) (wch : GalilScaffoldChainWatch.State) (t : ShiftState)
      (v : GalilScaffoldChainWatch.State) (finish : Counter),
      s.chain = .watch wch → CopyIdle s →
      ChainShiftRun ⟨s.center, s.left, s.remaining, s.radius, s.length⟩ wch s.cycle n t v finish →
      StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) n ⟨c, s⟩
        ⟨c, shiftLens.set s ⟨t, .watch v, finish⟩⟩ ∧
      PalPeg.ShapedRun.ShapedSteps centre place entry q first w n ⟨c, s⟩ ⟨c, shiftLens.set s ⟨t, .watch v, finish⟩⟩ ∧
      CopyIdle (shiftLens.set s ⟨t, .watch v, finish⟩) := by
  have hQ : ∀ x : GalilVM, SoundScanNR w ⟨c, x⟩ := fun x h => by rw [hm] at h; cases h
  intro n
  induction n with
  | zero =>
    intro s wch t v finish hs hi hr
    cases hr
    have hset : shiftLens.set s ⟨⟨s.center, s.left, s.remaining, s.radius, s.length⟩,
        .watch wch, s.cycle⟩ = s := by
      rw [← hs]; exact shiftLens.set_get s
    rw [hset]
    exact ⟨.zero _ (hQ s), .zero _, hi⟩
  | succ n ih =>
    intro s wch t v finish hs hi hr
    cases hr with
    | next _ _ _ hen hc hl hl' rest =>
      have hget : shiftLens.get s =
          ⟨⟨s.center, s.left, s.remaining, s.radius, s.length⟩, .watch wch, s.cycle⟩ := by
        show (⟨⟨s.center, s.left, s.remaining, s.radius, s.length⟩, s.chain, s.cycle⟩ : ShiftVM) = _
        rw [hs]
      -- one unit in the shift frame parametrised at `s`
      have hr1 : ChainShiftRun ⟨s.center, s.left, s.remaining, s.radius, s.length⟩ wch s.cycle 1
          (shiftTick ⟨s.center, s.left, s.remaining, s.radius, s.length⟩) (chainShiftOne wch)
          (inc (inc s.cycle)) :=
        .next _ _ _ hen hc hl hl' (.stop _ _ _)
      have h1 := shift_run_lift (fun v => (PofC centre place entry w).onLetter (shiftLens.set s v))
        (fun v => (PofC centre place entry w).leftFirst (shiftLens.set s v)) 2048 c hm 1 hr1
      have htick0 : Tick (shiftFrame (fun v => (PofC centre place entry w).onLetter (shiftLens.set s v))
          (fun v => (PofC centre place entry w).leftFirst (shiftLens.set s v))) 2048
          ⟨c, shiftLens.get s⟩
          ⟨c, ⟨shiftTick ⟨s.center, s.left, s.remaining, s.radius, s.length⟩,
            .watch (chainShiftOne wch), inc (inc s.cycle)⟩⟩ := by
        rw [hget]
        cases h1 with
        | succ ht hr => cases hr; exact ht
      have htickP := tick_pull shiftLens _ 2048 c c s _ htick0
      have htickG := shift_transfer (PofC centre place entry w) q first 2048 hm hi htickP
      have htickS := tick_S_of_tick (PofC centre place entry w) q first 2048 htickG
        (by rw [hm]; decide)
      have hi' := copyIdle_shift 2048 _ htickP hi
      obtain ⟨hrun, hrunS, hi''⟩ := ih (shiftLens.set s ⟨shiftTick ⟨s.center, s.left, s.remaining, s.radius, s.length⟩,
          .watch (chainShiftOne wch), inc (inc s.cycle)⟩) (chainShiftOne wch) t v finish rfl hi' rest
      rw [shiftLens.set_set] at hrun hrunS hi''
      have hnotScan : (⟨c, s⟩ : State GalilVM).ctl.mode = .scan → False := by
        intro h
        have h' : c.mode = .scan := h
        rw [hm] at h'
        cases h'
      have hnotReplayStart : (⟨c, s⟩ : State GalilVM).ctl.mode = .replayStart → False := by
        intro h
        have h' : c.mode = .replayStart := h
        rw [hm] at h'
        cases h'
      exact ⟨.succ (hQ s) htickS hrun,
        .succ htickS (fun h => absurd h hnotScan) (fun h => absurd h hnotReplayStart) hrunS, hi''⟩

/-- **The exit of a shift phase.**  With `remaining` exhausted and the copy walker idle,
`shift_done` fires with a refreshed flag. -/
theorem shiftExit_S {w : List (Fin 2)} (c : Control) (hm : c.mode = .shift) (s : GalilVM)
    (hz : positive s.remaining = false) (hi : CopyIdle s) :
    ∃ o : Bool, refresh (galilFrameS (PofC centre place entry w) q first) s c.output o ∧
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩
        ⟨{c with mode := .scan, output := o}, s⟩ := by
  classical
  let o : Bool := if (PofC centre place entry w).onLetter s
    then decide ((PofC centre place entry w).leftFirst s) else c.output
  have ho : refresh (galilFrameS (PofC centre place entry w) q first) s c.output o := by
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : (PofC centre place entry w).onLetter s := hl
      show (if (PofC centre place entry w).onLetter s
        then decide ((PofC centre place entry w).leftFirst s) else c.output) = true ↔
        (PofC centre place entry w).leftFirst s
      rw [if_pos hl']
      exact decide_eq_true_iff
    · have hl' : ¬ (PofC centre place entry w).onLetter s := hl
      show (if (PofC centre place entry w).onLetter s
        then decide ((PofC centre place entry w).leftFirst s) else c.output) = c.output
      rw [if_neg hl']
  refine ⟨o, ho, Tick.shift_done c s o hm ?_ ho⟩
  intro h
  rcases h with h1 | h1
  · have h2 : positive s.remaining = true := h1
    rw [hz] at h2
    cases h2
  · exact hi h1

#print axioms shiftUnits_S
#print axioms shiftExit_S

/-- **The shift leaf.**  From a clock-one, non-replaying scan state of the packed run whose
comparison mismatches with the shift guard up, the shift phase entered by `scan_shift` runs
`periodLength` unit moves and exits with a refreshed flag: a sound run to a scan landing one
place further right, the centre advanced by the period (`≥ 1`), in `period + 1` ticks. -/
theorem shiftLeaf {w : List (Fin 2)} (hP : Decodes (PofC centre place entry w)) (h4 : first ≠ 4)
    {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ w.length)
    {c₀ : Control} {r₀ : GalilVM} {k : ℕ} {c : Control} {s : GalilVM} {vq : SearchVM}
    {z : ChainVM} {u : GalilVM}
    (hI₀ : InvLPS (PofC centre place entry w) q first w c₀ r₀)
    (hrun : PalPeg.CloseoutCheckW.StepsIMW centre place entry q first w k ⟨c₀, r₀⟩ ⟨c, s⟩)
    (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (hp : position s.right + 1 ≤ 2 * m - 1) (hminvS : MInv w c s)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hq : searchEffect (PofC centre place entry w) false s vq)
    (hz : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
      ((PofC centre place entry w).centre s) ((PofC centre place entry w).place s)
      s.center s.radius s.chain z)
    (hg : (PofC centre place entry w).shiftGuard
      (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
        (afterMismatch s ⟨left s.left, right s.right, z⟩ vq)))
    (hb : (PofC centre place entry w).beginShift
      (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
        (afterMismatch s ⟨left s.left, right s.right, z⟩ vq)) u)
    (hperiodMin : ∀ wg : GalilScaffoldChainWatch.State, z = .watch wg →
      ∀ p : ℕ, 0 < p → p < 2 * periodLength wg →
        ¬ PalPeg.HasPeriod (Span w (position s.center) (position s.right - position s.center)) p)
    (htick : Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩
      ⟨{c with clock := 2048, mode := .shift}, u⟩) :
    ∃ (c' : Control) (s' : GalilVM) (n : ℕ),
      StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) n
        ⟨{c with clock := 2048, mode := .shift}, u⟩ ⟨c', s'⟩ ∧
      PalPeg.ShapedRun.ShapedSteps centre place entry q first w n ⟨{c with clock := 2048, mode := .shift}, u⟩ ⟨c', s'⟩ ∧
      c'.mode = .scan ∧ c'.replaying = false ∧
      Refreshed (PofC centre place entry w) q first ⟨c', s'⟩ ∧ MInv w c' s' ∧
      position s'.right = position s.right + 1 ∧ position s.center < position s'.center ∧
      n ≤ position s'.center - position s.center + 1 := by
  classical
  set born := chainBorn (decide (vq.search.mode = .found)) s.chain with hborn
  set vs : ScanVM := ⟨left s.left, right s.right, z⟩ with hvs
  set s1 := afterBirth born (afterMismatch s vs vq) with hs1
  set cE : Control := {c with clock := 2048, mode := .shift} with hcE
  -- the packed prefix and its facts at `⟨c, s⟩`
  have hpack : IPackMW centre place entry q first w ⟨c, s⟩ :=
    PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMW centre place entry q first hrun
  obtain ⟨g, hg0, hgk, htr, -⟩ := id hrun
  have hjx : Steps (galilFrameS (PofC centre place entry w) q first) 2048 k ⟨c₀, r₀⟩ ⟨c, s⟩ := by
    have := PalPeg.CloseoutPackRun2.steps_of_trace htr k le_rfl
    rwa [hg0, hgk] at this
  have hout : OutputRel w c s := by
    have := htr.good k le_rfl
    rw [hgk] at this
    exact this hm hr
  have hQ : SoundScanNR w ⟨c, s⟩ := fun _ _ => hout
  have hQE : SoundScanNR w ⟨cE, u⟩ := fun h => by rw [hcE] at h; cases h
  obtain ⟨hrep, hpres⟩ := PalPeg.WindowPack.rightHead_of_packs hpack.pack hpack.m2 hm
  have hlength : (encoded w).length = 2 * w.length + 1 := by simp [encoded, pairs_length]
  have hav : canRight s.right := canRight_of_bound _ w hrep hpres (by omega)
  have hpos1 : position (right s.right) = position s.right + 1 :=
    right_position _ hav (represented_position _ w hrep hpres).1
  obtain ⟨rad, hsi⟩ := hpack.pack.scanGeom hm hr
  have hwin := hpack.win hP
  have hcr : CentreRep w s := hwin.centreRep (Or.inl hm)
  -- the shift entry data
  obtain ⟨wch, hs1c, hu⟩ := hb
  set h := periodLength wch with hh
  have hcmp : (galilFrameS (PofC centre place entry w) q first).compare s s1 :=
    ⟨vs, vq, false, rfl, rfl, Iff.intro (fun h0 => by cases h0) (fun h0 => absurd h0 hmis),
      hq, hz, rfl⟩
  have hmt : ¬ (galilFrameS (PofC centre place entry w) q first).matched s1 := by
    intro h0
    apply hmis
    have h1 : read s1.left = read s1.right := h0
    rw [hs1, afterBirth_left, afterBirth_right] at h1
    exact h1
  have hfour := PalPeg.WindowPack.four_of_guard centre place entry q first (x := ⟨c, s⟩)
    hwin.coupled ⟨hm, hr⟩ hcmp hmt hg hs1c
  obtain ⟨R, hRR, hRpos⟩ := hwin.radiusScan hm
  have hRrad : R = rad := by have := hsi.rightPos; omega
  have hle : h ≤ rad := by
    have h1 := hRR.2
    rw [hRrad] at h1
    omega
  -- the entry state is on the packed run: its pack gives the period length and the block
  have hstE : StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) 1
      ⟨c, s⟩ ⟨cE, u⟩ := .succ hQ htick (.zero _ hQE)
  have hurt : u.right = right s.right := by
    rw [hu]
    show s1.right = right s.right
    rw [hs1, afterBirth_right, afterMismatch_right]
  have hstIE : PalPeg.CloseoutCheckW.StepsIMW centre place entry q first w 1 ⟨c, s⟩ ⟨cE, u⟩ :=
    PalPeg.CloseoutMarksPack.packRunR_MW_marksFree centre place entry q first h4 hP c₀ r₀ hI₀
      m hm1 hmle k ⟨c, s⟩ hjx 1 ⟨cE, u⟩ hpack hstE hr (by show position u.right ≤ 2 * m - 1; rw [hurt]; omega)
  have hpackE : IPackMW centre place entry q first w ⟨cE, u⟩ :=
    PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMW centre place entry q first hstIE
  have hwinE := hpackE.win hP
  have huch : u.chain = .watch (GalilScaffoldChainWatch.immediate wch) := by rw [hu]
  have hpos : 0 < h := by
    obtain ⟨cen₀, cc, -, hWI, -, -, -⟩ := hwinE.window
    rw [huch] at hWI
    obtain ⟨b, xs, hWW⟩ := hWI
    obtain ⟨-, -, hcore⟩ := hWW
    have h1 := PalPeg.ShiftPalAlongTrace.periodLength_of_coreP hcore
    have hblock : GalilBranchInvariants.WatchBlock wch := by
      have := hwin.coupled.block
      rcases hz with ⟨-, ht⟩ | ⟨-, -, hzi⟩ | ⟨-, -, hzs⟩
      · have hb1 := PalPeg.GalilBranchInvariants.blockInv_tick ht this
        have hzc : z = .watch wch := by
          have := hs1c; rw [hs1, afterBirth_chain, afterMismatch_chain] at this; exact this
        rw [hzc] at hb1; exact hb1
      · exfalso
        have h1 : z = ChainVM.watch wch := by
          have := hs1c; rw [hs1, afterBirth_chain, afterMismatch_chain] at this; exact this
        rw [hzi] at h1; cases h1
      · exfalso
        have h1 : z = ChainVM.watch wch := by
          have := hs1c; rw [hs1, afterBirth_chain, afterMismatch_chain] at this; exact this
        rw [hzs] at h1; cases h1
    have h2 := PalPeg.GalilChainCoupling.periodLength_consume wch.machine wch.lag wch.margin
      wch.lag (inc wch.margin) hblock
    rw [hh]
    have h3 : periodLength (GalilScaffoldChainWatch.immediate wch) = periodLength wch := h2
    omega
  -- the shift run of the heads
  obtain ⟨ce, le, hsh⟩ := PalPeg.GalilShiftPack.shiftHeads_of_scan w s.center s.left s.right rad h
    hcr.1 hcr.2 hsi hpos hle
  obtain ⟨t', hsr, htc, -, htrem, -, -⟩ :=
    shift_heads_counters hsh (inc s.radius) (inc (inc s.length))
  have htuple : (⟨s1.center, s1.left, ofNat h, s1.radius, inc (inc s1.length)⟩ : ShiftState) =
      ⟨s.center, left s.left, ofNat h, inc s.radius, inc (inc s.length)⟩ := by
    simp only [hs1, afterBirth_center, afterBirth_left, afterBirth_radius, afterBirth_length,
      afterMismatch_center, afterMismatch_left, afterMismatch_radius, afterMismatch_length]
    try rfl
  obtain ⟨v, finish, hcsr⟩ := shift_run_chain hsr (GalilScaffoldChainWatch.immediate wch) reset
  rw [← htuple] at hcsr
  have hcsr' : ChainShiftRun ⟨u.center, u.left, u.remaining, u.radius, u.length⟩
      (GalilScaffoldChainWatch.immediate wch) u.cycle h t' v finish := by
    rw [hu]; exact hcsr
  -- the copy walker is idle in the shift phase
  have hiU : CopyIdle u := by
    have hlv0 := PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry q first hI₀.1
    have haux0 : AuxPack c₀ r₀ :=
      ⟨PalPeg.CloseoutPackRun.coupled_of_invLPC hI₀.1, PalPeg.CloseoutPackRun.front_of_invLPC hI₀.1,
        PalPeg.CloseoutPackRun.copyPack_of_invLPC hI₀.1⟩
    have hauxE := PalPeg.CloseoutPackRun2.auxPack_steps centre place entry q first (x := ⟨c₀, r₀⟩)
      hlv0 haux0 (steps_trans hjx (stepsAll_steps hstE))
    exact hauxE.copyP (by show Mode.shift ≠ Mode.copy; decide)
  obtain ⟨hunits, hunitsS, hiD⟩ := shiftUnits_S centre place entry q first cE rfl h u _ t' v finish huch hiU hcsr'
  set uD := shiftLens.set u ⟨t', .watch v, finish⟩ with huD
  have hzD : positive uD.remaining = false := by
    show positive t'.remaining = false
    rw [htrem]; rfl
  obtain ⟨o, ho, htickD⟩ := shiftExit_S centre place entry q first cE rfl uD hzD hiD
  -- the landing is sound: the pack at the exhausted shift state gives the scan invariant
  have hstD : StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w)
      (1 + h) ⟨c, s⟩ ⟨cE, uD⟩ := stepsAll_trans hstE hunits
  have huDr : uD.right = u.right := rfl
  have hstID : PalPeg.CloseoutCheckW.StepsIMW centre place entry q first w (1 + h) ⟨c, s⟩ ⟨cE, uD⟩ :=
    PalPeg.CloseoutMarksPack.packRunR_MW_marksFree centre place entry q first h4 hP c₀ r₀ hI₀
      m hm1 hmle k ⟨c, s⟩ hjx _ ⟨cE, uD⟩ hpack hstD hr
      (by show position uD.right ≤ 2 * m - 1; rw [huDr, hurt]; omega)
  have hpackD : IPackMW centre place entry q first w ⟨cE, uD⟩ :=
    PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMW centre place entry q first hstID
  obtain ⟨rD, hsiD⟩ := PalPeg.CloseoutPackRun23.shiftGeom_exit (hpackD.m2.shiftGeom rfl) hzD
  set cL : Control := {cE with mode := .scan, output := o} with hcL
  have houtL : OutputRel w cL uD := by
    have h1 := outputRel_of_refresh w (PofC centre place entry w) rfl rfl q first cE uD o hsiD ho
    exact outputRel_transfer w rfl rfl h1
  have hQD : SoundScanNR w ⟨cE, uD⟩ := fun h => by rw [hcE] at h; cases h
  have hall : StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w)
      (h + 1) ⟨cE, u⟩ ⟨cL, uD⟩ :=
    stepsAll_trans hunits (.succ hQD htickD (.zero _ (fun _ _ => houtL)))
  have hallS : PalPeg.ShapedRun.ShapedSteps centre place entry q first w (h + 1) ⟨cE, u⟩ ⟨cL, uD⟩ :=
    PalPeg.ShapedRun.shapedSteps_trans centre place entry q first hunitsS
      (.succ htickD (fun h => by rw [hcE] at h; cases h) (fun h => by rw [hcE] at h; cases h)
        (.zero _))
  have hcenD : position uD.center = position s.center + h := by
    show position t'.center = position s.center + h
    have := (shift_run_center hsr w hcr.1 hcr.2).2.2
    exact this
  -- the landing keeps the leftmost live centre: the old centre died at the mismatch, the new
  -- one is live by the exit geometry, and nothing between them is live by period minimality
  have hzw : z = .watch wch := by
    have h1 : s1.chain = z := by rw [hs1, afterBirth_chain, afterMismatch_chain]
    rw [← h1]; exact hs1c
  have hLs : Leftmost w (position s.right) (position s.center) := hminvS.2 hr
  have hdead : ¬ Live w (position s.right + 1) (position s.center) :=
    not_live_of_mismatch hsi hav hmis
  have hliveD : Live w (position s.right + 1) (position s.center + h) := by
    have h1 := live_of_scanInvariant hsiD
    rw [huDr, hurt, hpos1, hcenD] at h1
    exact h1
  have hLD : Leftmost w (position s.right + 1) (position s.center + h) :=
    leftmost_shift hLs hdead hliveD (hperiodMin wch hzw)
  have hminvD : MInv w cL uD := by
    refine ⟨fun h1 => ?_, fun _ => ?_⟩
    · have h2 : c.replaying = true := h1
      rw [hr] at h2; cases h2
    · rw [huDr, hurt, hpos1, hcenD]; exact hLD
  refine ⟨cL, uD, h + 1, hall, hallS, rfl, hr, ⟨cE.output, ho⟩, hminvD, ?_, ?_, ?_⟩
  · rw [huDr, hurt, hpos1]
  · omega
  · omega

#print axioms shiftLeaf

/-- **The run-shaped cycle oracle from four leaves**: the shift phase is `shiftLeaf`, whose only
residue is the period minimality of the shifting chain at the shift entry (`hshiftPeriodMinimal`);
`MInv` (the leftmost live centre) is carried by the run predicate. -/
theorem cycleOracleOn_of_fourLeaves {w : List (Fin 2)} (hP : Decodes (PofC centre place entry w))
    (h4 : first ≠ 4)
    (hready : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (y : State GalilVM),
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      PalPeg.ShapedRun.ShapedSteps centre place entry q first w k ⟨c₀, r₀⟩ y →
      y.ctl.mode = .scan → y.vm.chain = .idle →
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get y.vm))
    (hchain : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (y : State GalilVM),
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      PalPeg.ShapedRun.ShapedSteps centre place entry q first w k ⟨c₀, r₀⟩ y →
      ChainReady y.vm.chain)
    (hshiftPeriodMinimal : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (c : Control) (s : GalilVM)
      (vq : SearchVM) (z : ChainVM) (u : GalilVM) (m : ℕ), 1 ≤ m → m ≤ w.length →
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      PalPeg.CloseoutCheckW.StepsIMW centre place entry q first w k ⟨c₀, r₀⟩ ⟨c, s⟩ →
      c.mode = .scan → c.replaying = false → c.clock = 1 → position s.right + 1 ≤ 2 * m - 1 →
      MInv w c s →
      GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) ≠
        GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right s.right) →
      searchEffect (PofC centre place entry w) false s vq →
      chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
        ((PofC centre place entry w).centre s) ((PofC centre place entry w).place s)
        s.center s.radius s.chain z →
      (PofC centre place entry w).shiftGuard
        (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
          (afterMismatch s ⟨GalilScaffoldInputHead.left s.left,
            GalilScaffoldChainVerifier.right s.right, z⟩ vq)) →
      (PofC centre place entry w).beginShift
        (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
          (afterMismatch s ⟨GalilScaffoldInputHead.left s.left,
            GalilScaffoldChainVerifier.right s.right, z⟩ vq)) u →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩
        ⟨{c with clock := 2048, mode := .shift}, u⟩ →
      ∀ wg : GalilScaffoldChainWatch.State, z = .watch wg →
        ∀ p : ℕ, 0 < p → p < 2 * periodLength wg →
          ¬ PalPeg.HasPeriod (Span w (position s.center) (position s.right - position s.center)) p)
    (hfallback : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (c : Control) (s : GalilVM) (vq : SearchVM)
      (z : ChainVM) (u : GalilVM) (m : ℕ), 1 ≤ m → m ≤ w.length →
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      PalPeg.CloseoutCheckW.StepsIMW centre place entry q first w k ⟨c₀, r₀⟩ ⟨c, s⟩ →
      c.mode = .scan → c.replaying = false → c.clock = 1 → position s.right + 1 ≤ 2 * m - 1 →
      MInv w c s →
      read (left s.left) ≠ read (right s.right) →
      searchEffect (PofC centre place entry w) false s vq →
      chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
        ((PofC centre place entry w).centre s) ((PofC centre place entry w).place s)
        s.center s.radius s.chain z →
      ¬ (PofC centre place entry w).shiftGuard
        (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
          (afterMismatch s ⟨left s.left, right s.right, z⟩ vq)) →
      (PofC centre place entry w).beginFallback
        (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
          (afterMismatch s ⟨left s.left, right s.right, z⟩ vq)) u →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩
        ⟨{c with clock := 2048, mode := .copy}, u⟩ →
      ∃ (c' : Control) (s' : GalilVM) (kk r fb replay : ℕ),
        StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w)
          (fb + replay) ⟨{c with clock := 2048, mode := .copy}, u⟩ ⟨c', s'⟩ ∧
        PalPeg.ShapedRun.ShapedSteps centre place entry q first w (fb + replay) ⟨{c with clock := 2048, mode := .copy}, u⟩ ⟨c', s'⟩ ∧
        c'.mode = .scan ∧ c'.replaying = false ∧
        Refreshed (PofC centre place entry w) q first ⟨c', s'⟩ ∧ MInv w c' s' ∧
        position s'.right = position s.right + 1 ∧ r ≤ kk ∧
        position s'.center = position s.center + (kk + 1 - r) ∧
        fb ≤ 12704 * (kk + 1 - r) + 4012 ∧ replay ≤ 8 * 2048 * (kk + 1 - r)) :
    PalPeg.CloseoutCheckW.CycleOracleOn centre place entry q first
      (PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centre place entry q first) w :=
  cycleOracleOn_of_leaves centre place entry q first hP h4 hready hchain
    (fun c₀ r₀ k c s vq z u m hm1 hmle hI₀ hrun hm hr hc hp hminvS hmis hq hz hg hb htick =>
      shiftLeaf centre place entry q first hP h4 hm1 hmle hI₀ hrun hm hr hc hp hminvS hmis hq hz hg hb
        (hshiftPeriodMinimal c₀ r₀ k c s vq z u m hm1 hmle hI₀ hrun hm hr hc hp hminvS hmis hq hz hg hb
          htick)
        htick)
    hfallback

#print axioms cycleOracleOn_of_fourLeaves

#print axioms chainReady_watch_of_watchWindow

#print axioms scan_tick_exists_PofC
#print axioms phase_tick_exists_PofC

end

end PalPeg.OracleRun
