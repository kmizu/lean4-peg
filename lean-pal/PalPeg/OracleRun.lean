import PalPeg.GalilTickFun3
import PalPeg.GalilBranchInvariants2
import PalPeg.GalilRunSkeleton
import PalPeg.WindowInv
import PalPeg.GalilWatchPhase

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
        StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) k ⟨c, s⟩ y →
        y.vm.chain = .idle → PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get y.vm)) →
      (∀ (k : ℕ) (y : State GalilVM),
        StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) k ⟨c, s⟩ y →
        ChainReady y.vm.chain) →
      ∃ t : GalilVM,
        StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) n ⟨c, s⟩
          ⟨{c with clock := 1}, t⟩ ∧
        t.left = s.left ∧ t.right = s.right ∧ t.center = s.center ∧ t.replay = s.replay ∧
        t.remaining = s.remaining ∧ t.radius = s.radius ∧ t.length = s.length ∧ t.fpp = s.fpp := by
  intro n
  induction n with
  | zero =>
    intro c s hm hr hclk hav hout _ _
    have hceq : ({c with clock := 1} : Control) = c := by cases c; simp_all
    refine ⟨s, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [hceq]
    exact .zero _ (fun _ _ => hout)
  | succ n ih =>
    intro c s hm hr hclk hav hout hready hchain
    have hQ : SoundScanNR w ⟨c, s⟩ := fun _ _ => hout
    have hsearch : ∃ v, searchEffect (PofC centre place entry w) false s v := by
      by_cases hidle : s.chain = .idle
      · exact PalPeg.GalilBranchInvariants2.searchEffect_exists _ false s
          (hready 0 ⟨c, s⟩ (.zero _ hQ) hidle)
      · exact ⟨searchLens.get s, Or.inr ⟨hidle, rfl⟩⟩
    have hchainAt : ∀ v : SearchVM, ∃ z, chainAt false (decide (v.search.mode = .found))
        (v.dp.config.tapes 11) ((PofC centre place entry w).centre s)
        ((PofC centre place entry w).place s) s.center s.radius s.chain z :=
      fun v => chainAt_exists false _ _ _ _ _ _ s.chain (hchain 0 ⟨c, s⟩ (.zero _ hQ))
    obtain ⟨s', hb⟩ := backgroundS_exists (PofC centre place entry w) q first s hsearch hchainAt
    have hav' : (galilFrameS (PofC centre place entry w) q first).available s := hav
    have htick : Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩
        ⟨{c with clock := c.clock - 1}, s'⟩ :=
      Tick.scan_count c s s' hm (Or.inr hav') (by omega) hb
    obtain ⟨hl', hr', -, hc', -, hrad', hlen', -, hrem', hrep', hfpp', -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    have hout' : OutputRel w {c with clock := c.clock - 1} s' :=
      outputRel_background w (PofC centre place entry w) q first hb rfl hout
    obtain ⟨t, hrun, htl, htr, htc, htrep, htrem, htrad, htlen, htfpp⟩ :=
      ih {c with clock := c.clock - 1} s' hm hr (by simp; omega) (hr' ▸ hav) hout'
        (fun k y hst hidle => hready (k + 1) y (.succ hQ htick hst) hidle)
        (fun k y hst => hchain (k + 1) y (.succ hQ htick hst))
    refine ⟨t, .succ hQ htick hrun, htl.trans hl', htr.trans hr', htc.trans hc', htrep.trans hrep',
      htrem.trans hrem', htrad.trans hrad', htlen.trans hlen', htfpp.trans hfpp'⟩

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

#print axioms chainReady_watch_of_watchWindow

#print axioms scan_tick_exists_PofC
#print axioms phase_tick_exists_PofC

end

end PalPeg.OracleRun
