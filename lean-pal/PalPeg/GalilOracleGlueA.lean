import PalPeg.GalilOracleDischarge
import PalPeg.GalilRewindSafe
import PalPeg.GalilScaffoldTopOutputTrace
import PalPeg.GalilSegmentCount
import PalPeg.GalilScaffoldTopInitRestart
import PalPeg.GalilScaffoldTopSegmentFacts
import PalPeg.GalilReportReach

/-!
# Glue A: discharging the segment and last-letter-match exits of the cycle oracle

`PalPeg.GalilOracleDischarge.cycleOracle_of_pieces` reduces the cycle oracle to
a handful of named hypotheses.  This module discharges two of them from the
constructions that are already proved, and records exactly what is left over.

* `segment_of_invS` **is** `hsegment`: from any state of the widened recursion
  `InvS` the chain-idle segment of `PalPeg.GalilSegmentConstruct` is built and
  every field of `SegReached` is produced.  Three facts the construction does
  not produce travel as named hypotheses:

  - `hout` — the output is sound at the state the cycle starts from
    (`OutputRel`).  `Inv`/`InvScan` do not carry it, and it is what
    `watchSegE_stepsAll` needs to turn the segment into a `StepsAll` run.
  - `hlive` — the rewind-phase side condition `CentreLive` along runs out of
    the entering state, i.e. the gap-7 hypothesis of
    `frontier_replayRest_of_scan`; it is what carries `Frontier` to the exit.
  - `hends` — the segment ends within a known fuel.  `watchSegE_construct` is
    fuelled, so *some* bound has to say that the fuel is not simply spent; the
    mathematical content (the right head advances at every comparison, and the
    input is finite) is not formalised here.

* `lastMatch_report` **is** `hlastMatch`, **relative to a run prefix**.  This is
  the honest form: `GlobalReport` asks for a `ScaffoldRun`, i.e. a run from a
  state whose controller is `Control.initial 2048` (mode `init`), and the
  oracle is invoked at a state that has no such history attached.  Given the
  prefix, `PalPeg.GalilReportReach.scaffoldRun_report_of_last_consume` closes
  the exit completely: the matched comparison tick is built here from the
  search and chain effects, exactly as in `compare_progress_S`.

  Consequently `hlastMatch` of `cycleOracle_of_pieces` is **not** dischargeable
  as stated — the run prefix is missing from the oracle's signature.  The same
  applies to `hlastMismatch` and `hended`, which conclude in the same global
  form; they stay named hypotheses (see the end of this file).
-/

set_option autoImplicit false

namespace PalPeg.GalilOracleGlueA

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge
open PalPeg.GalilSegmentConstruct (SegEnd watchSegE_construct)

/-! ## `hsegment` -/

/-- **The chain-idle segment exists from every state of the widened
recursion.**  This is `hsegment` of `cycleOracle_of_pieces`, with the three
named leftovers described in the module header. -/
theorem segment_of_invS (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v →
      PalPeg.GalilBranchInvariants2.SearchReady v)
    (hout : ∀ (c : Control) (r : GalilVM), InvS raw c r → OutputRel raw c r)
    (hlive : ∀ (c : Control) (r : GalilVM), InvS raw c r → ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c, r⟩ z →
      CentreLive z.ctl z.vm)
    (hends : ∀ (c : Control) (r : GalilVM), InvS raw c r → ∃ n : ℕ,
      ∀ (es : List Bool) (c' : Control) (t : GalilVM),
        WatchSegE (PofC centre place entry raw) q first 2048 es c r c' t →
        es.length = n → SegEnd (PofC centre place entry raw) c' t) :
    ∀ (c : Control) (r : GalilVM), InvS raw c r →
      ∃ (c' : Control) (t : GalilVM),
        SegReached centre place entry q first raw c r c' t ∧
        SegEnd (PofC centre place entry raw) c' t := by
  intro c r hI
  -- the six inputs of `watchSegE_construct`, plus `Frontier`/`ReplayRest`/`ShiftIdle`
  obtain ⟨hm, hclk, hidle, hsr, hM, R, hi, hfr, hrr, hsi⟩ :
      c.mode = Mode.scan ∧ 1 ≤ c.clock ∧ r.chain = ChainVM.idle ∧
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get r) ∧ MInv raw c r ∧
      ∃ R : ℕ, ScanInvariant raw (position r.center) R r.left r.right ∧ Frontier r ∧
        ReplayRest c r ∧ ShiftIdle r := by
    rcases hI with h | ⟨k, h⟩
    · obtain ⟨Rad, last, hR⟩ := h.rest
      exact ⟨h.mode.1, by rw [h.mode.2.2]; omega, hR.1, h.search, h.minv, Rad,
        hR.2.2.2.1, h.frontier, h.rest_replay, h.shiftIdle⟩
    · exact ⟨h.mode.1, by rw [h.mode.2.2]; omega, h.chainIdle, h.search, h.minv, k,
        h.scan, h.frontier, h.rest_replay, h.shiftIdle⟩
  obtain ⟨n, hn⟩ := hends c r hI
  obtain ⟨es, c', t, r', hseg, hm', hclk', hidle', hsrt, hMt, hit, hlen⟩ :=
    watchSegE_construct raw (PofC centre place entry raw) hex q first 2048 (by norm_num)
      hsearch hpres n c r R hm hclk hidle hsr hM hi
  have hEnd : SegEnd (PofC centre place entry raw) c' t := by
    rcases hlen with h0 | h0
    · exact hn es c' t hseg h0
    · exact h0
  -- the segment as a sound run
  obtain ⟨k1, h1⟩ :=
    watchSegE_stepsAll raw (PofC centre place entry raw) rfl rfl q first 2048 hseg
      (position r.center) R hi (hout c r hI)
  have hrun : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) k ⟨c, r⟩ ⟨c', t⟩ :=
    ⟨k1, stepsAll_mono (fun _ h0 _ _ => h0) h1⟩
  -- the frontier travels to the exit
  have hsteps : Steps (galilFrameS (PofC centre place entry raw) q first) 2048 es.length
      ⟨c, r⟩ ⟨c', t⟩ := watchSegE_steps_length _ q first 2048 hseg
  have hfrt : Frontier t ∧ ReplayRest c' t :=
    frontier_replayRest_of_scan (onLetterVM raw) leftFirstVM centre place entry q first 2048
      hsteps hm (hlive c r hI) hfr hrr
  -- the shift stays idle
  have hsit : ShiftIdle t := by
    rw [shiftIdle_iff, watchSegE_remaining _ q first 2048 hseg]
    exact (shiftIdle_iff r).1 hsi
  exact ⟨c', t,
    { run := hrun
      center := watchSegE_center _ q first 2048 hseg
      mode := hm'
      clock := hclk'
      idle := hidle'
      minv := hMt
      search := hsrt
      input := hit.rightRep
      frontier := hfrt.1
      shiftIdle := hsit
      scan := ⟨r', hit⟩ }, hEnd⟩

/-! ## `hlastMatch`, relative to a run prefix -/

/-- **The last-letter comparison that matches is a refreshed report point.**
The matched comparison tick is built here (search effect, chain effect,
`refresh` witness), exactly as in `compare_progress_S`; the report itself is
`PalPeg.GalilReportReach.scaffoldRun_report_of_last_consume`.

`hprefix` is the run of the scaffold so far, which `GlobalReport`'s
`ScaffoldRun` needs and which the oracle's own signature does not carry. -/
theorem lastMatch_report (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hchain : ∀ (s : GalilVM) (a : Bool) (v : SearchVM), ∃ z,
      chainAt a (decide (v.search.mode = .found)) (v.dp.config.tapes 11)
        ((PofC centre place entry raw).centre s) ((PofC centre place entry raw).place s)
        s.center s.radius s.chain z)
    (c' : Control) (t : GalilVM) {n : ℕ} {x : State GalilVM}
    (hx : x.ctl = GalilScaffoldController.initial 2048)
    (hprefix : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) n x ⟨c', t⟩)
    (hm : c'.mode = Mode.scan) (hc1 : c'.clock = 1)
    (hpop : PopsIncoming t.right) (a : Fin 2) (hinc : t.right.head.incoming = [a])
    (hfr : Frontier t) (hM : MInv raw c' t)
    (R : ℕ) (hi : ScanInvariant raw (position t.center) R t.left t.right)
    (hsr : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get t))
    (hmt : read (left t.left) = read (right t.right)) :
    GlobalReport centre place entry q first raw := by
  classical
  set P : Shared := PofC centre place entry raw with hP
  obtain ⟨vq, hq⟩ := hsearch t hsr true
  obtain ⟨z, hz⟩ := hchain t true vq
  set vs : ScanVM := ⟨left t.left, right t.right, z⟩ with hvs
  have hmt0 : (galilFrame P q first).matched (scanLens.set t vs) := hmt
  have hcmp : (galilFrameS P q first).compare t (afterCompare t vs vq) :=
    ⟨vs, vq, true, rfl, rfl, ⟨fun _ => hmt0, fun _ => rfl⟩, hq, hz, rfl⟩
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
  exact PalPeg.GalilReportReach.scaffoldRun_report_of_last_consume raw
    (PofC centre place entry) (fun _ => q) (fun _ => first) 2048 rfl rfl hx hprefix hm hc1
    hpop hinc hfr hM hi hi.rightRep vs vq o rfl rfl hcmp hmt1 ho

#print axioms segment_of_invS
#print axioms lastMatch_report

end PalPeg.GalilOracleGlueA
