import PalPeg.CloseoutPackRun22
import PalPeg.CloseoutReadyStage

/-!
# `CloseoutPackRun27`: the budgeted `ready` field for the pack

`CloseoutPackRun22` left `Extra3.ready` open along the tick: bare `SearchReady`
does not survive `searchEffect` (`GalilLeafPres.hpres_false_at`).  The datum
that does survive is the clock-paced closure `CloseoutReadyStage.ReadyPacedS`,
whose two effect lemmas (`readyPacedS_effect_false` / `readyPacedS_effect_true`)
are exactly the `scan_count` / `scan_match` steps, with the slack tied to the
controller clock by `k = 2048 - clock` (the tight form of the invariant
`2048 ≤ clock + k` used by `watchSegE_constructS`).

`ReadyFieldP x` is chosen over `GalilLeafPres.SearchReadyB` (its tick lemma
`searchReadyB_effect` needs a *fixed* event list, which the pack cannot name)
and over `GalilSegmentConstructB.ReadyFuel` (its match budget `K` decreases at
`scan_match` and is bounded by `headRank`, which the pack does not carry).
`ReadyPacedS` needs neither: `n = 0` is the strongest instance and is
preserved, and the slack is replenished by the clock itself.

* `ready` — bare `SearchReady` in `scan` mode (the projection `Extra3.ready`
  consumes);
* `paced` — `ReadyPacedS … 0 (2048 - clock)` in `scan` mode while the chain is
  idle.  While the chain is active the search view is frozen
  (`searchEffect_active`) and the chain never returns to idle except through
  `restart` (`chainTick_ne_idle'`), so no paced datum is needed there.

`readyField_tick` closes `scan_wait` / `scan_count` / `scan_match` from the
datum at the source, `init` from the pack (`FrontPack.notInit`), and the
off-`scan` landings vacuously.  The ONE residue `hentry` is the datum at a
re-entry into `scan`: `restart`, `replayStart` (both re-`begin` the search, so
the `ReadyRemS` half is free by `readyRemS_begin`; what is really needed is
`RunEntriesS` on every `PacedL 2048 0` list — `readyPacedS_restarted`'s `hE`),
and `shift_done` (the search view is untouched during `shift`, so the residue
there is the datum at the `scan_shift` source carried through the shift).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun27

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun11 PalPeg.CloseoutPackRun18 PalPeg.CloseoutPackRun22
open PalPeg.CloseoutReadyStage
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-- **The budgeted ready datum.**  `ready` is the shape `Extra3.ready` consumes;
`paced` is the clock-slack closure that makes it transportable. -/
structure ReadyFieldP (x : State GalilVM) : Prop where
  ready : x.ctl.mode = Mode.scan →
    PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm)
  paced : x.ctl.mode = Mode.scan → x.vm.chain = ChainVM.idle →
    ReadyPacedS (searchLens.get x.vm) 0 (2048 - x.ctl.clock)

/-- The projection to the `Extra3.ready` shape. -/
theorem readyField_to_ready {x : State GalilVM} (h : ReadyFieldP x)
    (hm : x.ctl.mode = Mode.scan) :
    PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm) :=
  h.ready hm

/-- One search effect on the paced datum at `n = 0`: a background step may
grow the slack by one, a comparison needs the slack full and resets it. -/
theorem readyPacedS_effect0 (P : Shared) {a : Bool} {k k' : ℕ} {s : GalilVM}
    {v : SearchVM} (hk : a = false → k' ≤ k + 1)
    (hk1 : a = true → 2048 ≤ k + 1 ∧ k' = 0) (hidle : s.chain = ChainVM.idle)
    (h : ReadyPacedS (searchLens.get s) 0 k) (he : searchEffect P a s v) :
    ReadyPacedS v 0 k' := by
  have h1 : ReadyPacedS (searchLens.get s) (0 + 1) k :=
    readyPacedS_mono (by omega) le_rfl h
  cases a
  · exact readyPacedS_effect_false P (hk rfl) hidle h1 he
  · obtain ⟨h2048, hk0⟩ := hk1 rfl
    subst hk0
    exact readyPacedS_effect_true P h2048 hidle h1 he

section TickT
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- A `galilFrameS` background tick on the datum: the search steps only while
the chain is idle, and an active chain stays active. -/
theorem readyField_background {w : List (Fin 2)} {c : Control} {s t : GalilVM} {k' : ℕ}
    (hm0 : c.mode = Mode.scan) (hf : ReadyFieldP ⟨c, s⟩)
    (hb : (galilFrameS (PofC centre place entry w) q first).background s t)
    (hk : k' ≤ (2048 - c.clock) + 1) :
    PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get t) ∧
      (t.chain = ChainVM.idle → ReadyPacedS (searchLens.get t) 0 k') := by
  obtain ⟨-, -, hch, -, -, -, -, -, -, -, -, hse⟩ := backgroundS_fields _ q first hb
  by_cases hidle : s.chain = ChainVM.idle
  · have hp : ReadyPacedS (searchLens.get t) 0 k' :=
      readyPacedS_effect0 _ (fun _ => hk) (fun h0 => by cases h0) hidle (hf.paced hm0 hidle) hse
    exact ⟨readyPacedS_ready hp, fun _ => hp⟩
  · have hget : searchLens.get t = searchLens.get s := searchEffect_active _ hse hidle
    refine ⟨by rw [hget]; exact hf.ready hm0, fun ht => absurd ht ?_⟩
    rcases hch with ⟨_, htk⟩ | ⟨hi, _⟩ | ⟨hi, _⟩
    · exact chainTick_ne_idle' htk hidle
    · exact absurd hi hidle
    · exact absurd hi hidle

/-- **`ReadyFieldP` along one `galilFrameS` tick.**  `scan_wait` / `scan_count`
/ `scan_match` from the datum at the source (the search view steps by
`searchEffect`, the slack follows the clock); `init` impossible from the pack;
off-`scan` landings vacuous.  The ONE residue `hentry` is the datum at a
re-entry into `scan` from outside it (`shift_done`, `replayStart`) or through
`restart`. -/
theorem readyField_tick {w : List (Fin 2)} {x y : State GalilVM}
    (hx : BigPack2M'' centre place entry q first w x) (hf : ReadyFieldP x)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hentry : (x.ctl.mode ≠ Mode.scan ∨ restartVM entry x.vm y.vm) →
      y.ctl.mode = Mode.scan → ReadyFieldP y) :
    ReadyFieldP y := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  cases h
  case init =>
    rename_i hm0 h0
    exact absurd hm0 hx.aux.front.notInit
  case scan_wait =>
    rename_i hm0 h0 hb
    obtain ⟨hr, hp⟩ := readyField_background centre place entry q first hm0 hf hb
      (k' := 2048 - c.clock) (by omega)
    exact ⟨fun _ => hr, fun _ hi => hp hi⟩
  case scan_count =>
    rename_i hm0 h0 hc hb
    obtain ⟨hr, hp⟩ := readyField_background centre place entry q first hm0 hf hb
      (k' := 2048 - (c.clock - 1)) (by omega)
    exact ⟨fun _ => hr, fun _ hi => hp hi⟩
  case scan_match =>
    rename_i s' o hmt hm0 hc hcmp h0 hpl ho
    obtain ⟨vs, vq, a, -, -, -, hse, hch, hs'⟩ := hcmp
    have hpl' : t = (if c.replaying then {s' with replay := GalilScaffoldCounter.dec s'.replay}
        else s') := hpl
    have hget : searchLens.get t = vq := by
      subst hpl'; subst hs'
      cases c.replaying <;> cases a <;>
        simp [afterBirth_search, afterBirth_dp, afterBirth_lower, afterBirth_walker,
          afterBirth_chain, afterCompare, afterMismatch, searchLens, scanLens]
    have hchain : t.chain = vs.chain := by
      subst hpl'; subst hs'
      cases c.replaying <;> cases a <;>
        simp [afterBirth_search, afterBirth_dp, afterBirth_lower, afterBirth_walker,
          afterBirth_chain, afterCompare, afterMismatch, searchLens, scanLens]
    by_cases hidle : s.chain = ChainVM.idle
    · have hp0 : ReadyPacedS (searchLens.get s) 0 (2048 - c.clock) := hf.paced hm0 hidle
      rw [hc] at hp0
      have hp : ReadyPacedS vq 0 0 :=
        readyPacedS_effect0 _ (fun _ => by omega) (fun _ => ⟨by omega, rfl⟩) hidle hp0 hse
      rw [← hget] at hp
      exact ⟨fun _ => readyPacedS_ready hp, fun _ _ => hp⟩
    · have hget' : vq = searchLens.get s := searchEffect_active _ hse hidle
      refine ⟨fun _ => by rw [hget, hget']; exact hf.ready hm0, fun _ ht => absurd ht ?_⟩
      rw [hchain]
      rcases hch with ⟨_, htk⟩ | ⟨hi, _⟩ | ⟨hi, _⟩
      · exact chainTick_ne_idle' htk hidle
      · exact absurd hi hidle
      · exact absurd hi hidle
  case shift_done =>
    rename_i o hm0 hp ho
    exact hentry (Or.inl (by rw [hm0]; decide)) rfl
  case replayStart =>
    rename_i o hm0 h0 ho ho'
    exact hentry (Or.inl (by rw [hm0]; decide)) rfl
  case restart =>
    rename_i hm0 hb
    exact hentry (Or.inr hb) hm0
  all_goals
    (clear hx hentry hf
     refine ⟨fun hm => ?_, fun hm _ => ?_⟩ <;> exfalso <;> simp_all)

end TickT

#print axioms readyField_to_ready
#print axioms readyPacedS_effect0
#print axioms readyField_background
#print axioms readyField_tick

end PalPeg.CloseoutPackRun27
