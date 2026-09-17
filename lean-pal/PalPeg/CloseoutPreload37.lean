import PalPeg.CloseoutPreload36
import PalPeg.CloseoutPackRun27

/-!
# `CloseoutPreload37`: the fuel-indexed ready field, and its restart entry

`CloseoutPackRun27.ReadyFieldP` fixes the fuel of `ReadyPacedS` at `n = 0`,
so its `paced` clause asks `SearchReadyS` of *every* paced list, including the
short ones on which it is refutable (`CloseoutPreload3.not_runEntriesS_eight`).
`ReadyFieldP2 n` carries the fuel, so only lists of length `≥ n` are asked; the
restart entry then supplies exactly the fuel `dpEntryG k D` that
`CloseoutPreload6.runEntriesS_of_namedG` serves, and **no post-run contract is
needed**: `PostRunC` / `ScanRealized` are excluded on purpose, since
`CloseoutPreload30.scanRealized_absurd` makes any statement taking the pair
`(ScanSupplyInv, ScanRealized)` vacuous.

`ReadyFieldP2` also carries the datum through `shift` mode (the clause
`readyField_along_run` was missing): the search view is untouched by
`shift_one`, so the datum entered at `scan_shift` walks to `shift_done`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload37

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldCounter (Counter value)
open PalPeg.CloseoutReadyStage (PacedL RunEntriesS ReadyPacedS readyPacedS_restarted
  readyPacedS_ready readyPacedS_mono)
open PalPeg.CloseoutPreload5 (CentreLongRun NoReturn EntryDepthG dpEntryG)
open PalPeg.CloseoutPreload6 (prepLen runEntriesS_of_namedG)
open PalPeg.GalilRunSkeleton (PofC)
open PalPeg.CloseoutPackRun18 (BigPack2M'')
open PalPeg.CloseoutReadyStage (readyPacedS_effect_false readyPacedS_effect_true)
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 1. The fuel-indexed ready field -/

/-- **`CloseoutPackRun27.ReadyFieldP` with a fuel index.**  `paced` is asked
only of lists of length `≥ n`, and `shifting` carries the same datum through
`shift` mode, where the search view is frozen. -/
structure ReadyFieldP2 (n : ℕ) (x : State GalilVM) : Prop where
  ready : x.ctl.mode = Mode.scan →
    PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm)
  readyS : x.ctl.mode = Mode.shift →
    PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm)
  paced : x.ctl.mode = Mode.scan → x.vm.chain = ChainVM.idle →
    ReadyPacedS (searchLens.get x.vm) n (2048 - x.ctl.clock)
  shifting : x.ctl.mode = Mode.shift → ReadyPacedS (searchLens.get x.vm) n (2048 - x.ctl.clock)

/-- The projection to `CloseoutPackRun27.ReadyFieldP` at fuel `0`. -/
theorem readyField2_to_field {x : State GalilVM} (h : ReadyFieldP2 0 x) :
    PalPeg.CloseoutPackRun27.ReadyFieldP x :=
  ⟨h.ready, h.paced⟩

#print axioms readyField2_to_field

section TickT
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- A background tick on the fuel-indexed datum. -/
theorem readyField2_background {w : List (Fin 2)} {c : Control} {s t : GalilVM} {n n' k' : ℕ}
    (hm0 : c.mode = Mode.scan) (hf : ReadyFieldP2 n ⟨c, s⟩)
    (hb : (galilFrameS (PofC centre place entry w) q first).background s t)
    (hn : n ≤ n' + 1) (hk : k' ≤ (2048 - c.clock) + 1) :
    PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get t) ∧
      (t.chain = ChainVM.idle → ReadyPacedS (searchLens.get t) n' k') := by
  obtain ⟨-, -, hch, -, -, -, -, -, -, -, -, hse⟩ :=
    backgroundS_fields _ q first hb
  by_cases hidle : s.chain = ChainVM.idle
  · have h1 : ReadyPacedS (searchLens.get s) n (2048 - c.clock) := hf.paced hm0 hidle
    have hp : ReadyPacedS (searchLens.get t) n' k' :=
      readyPacedS_effect_false _ hk hidle (readyPacedS_mono hn le_rfl h1) hse
    exact ⟨readyPacedS_ready hp, fun _ => hp⟩
  · have hget : searchLens.get t = searchLens.get s :=
      searchEffect_active _ hse hidle
    refine ⟨by rw [hget]; exact hf.ready hm0, fun ht => absurd ht ?_⟩
    rcases hch with ⟨_, htk⟩ | ⟨hi, _⟩ | ⟨hi, _⟩
    · exact chainTick_ne_idle' htk hidle
    · exact absurd hi hidle
    · exact absurd hi hidle

/-- **`CloseoutPackRun27.readyField_tick` with the fuel and the shift carry.**
`scan_wait` / `scan_count` / `scan_match` spend one unit of fuel through
`searchEffect` (the fuel index is monotone: `hn : n ≤ n'`, since every consumed
event is one fewer event the datum has to cover); `shift_one` leaves the search view and the control untouched,
so the `shifting` clause walks; `shift_done` turns `shifting` into `paced` at
the same clock.  Residues: `hentry` (re-entry into `scan` through `restart` /
`replayStart`, discharged by §2) and `hshift` (the `scan_shift` tick, which
takes a comparison and a `beginShift` in one step). -/
theorem readyField2_tick {w : List (Fin 2)} {n n' : ℕ} {x y : State GalilVM}
    (hx : BigPack2M'' centre place entry q first w x) (hf : ReadyFieldP2 n x)
    (hn : n ≤ n')
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hentry : x.ctl.mode = Mode.scan → restartVM entry x.vm y.vm → ReadyFieldP2 n' y)
    (hentry' : x.ctl.mode = Mode.replayStart → ReadyFieldP2 n' y)
    (hshift : x.ctl.mode = Mode.scan → y.ctl.mode = Mode.shift → ReadyFieldP2 n' y) :
    ReadyFieldP2 n' y := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  cases h
  case init => rename_i hm0 h0; exact absurd hm0 hx.aux.front.notInit
  case scan_wait =>
    rename_i hm0 h0 hb
    obtain ⟨hr, hp⟩ := readyField2_background centre place entry q first hm0 hf hb (n' := n') (by omega)
      (k' := 2048 - c.clock) (by omega)
    exact ⟨fun _ => hr, fun hm => absurd (hm0.symm.trans hm) (by decide), fun _ hi => hp hi,
      fun hm => absurd (hm0.symm.trans hm) (by decide)⟩
  case scan_count =>
    rename_i hm0 h0 hc hb
    obtain ⟨hr, hp⟩ := readyField2_background centre place entry q first hm0 hf hb (n' := n') (by omega)
      (k' := 2048 - (c.clock - 1)) (by omega)
    exact ⟨fun _ => hr, fun hm => absurd (hm0.symm.trans hm) (by decide), fun _ hi => hp hi,
      fun hm => absurd (hm0.symm.trans hm) (by decide)⟩
  case scan_match =>
    rename_i s' o hmt hm0 hc hcmp h0 hpl ho
    obtain ⟨vs, vq, a, -, -, -, hse, hch, hs'⟩ := hcmp
    have hpl' : t = (if c.replaying then {s' with replay := GalilScaffoldCounter.dec s'.replay}
        else s') := hpl
    have hget : searchLens.get t = vq := by
      subst hpl'; subst hs'; cases c.replaying <;> cases a <;> rfl
    have hchain : t.chain = vs.chain := by
      subst hpl'; subst hs'; cases c.replaying <;> cases a <;> rfl
    by_cases hidle : s.chain = ChainVM.idle
    · have hp0 : ReadyPacedS (searchLens.get s) (n' + 1) (2048 - c.clock) :=
        readyPacedS_mono (n := n) (n' := n' + 1) (by omega) le_rfl (hf.paced hm0 hidle)
      have hp : ReadyPacedS vq n' 0 := by
        cases a
        · exact readyPacedS_effect_false _ (Nat.zero_le _) hidle hp0 hse
        · exact readyPacedS_effect_true _ (by omega) hidle hp0 hse
      rw [← hget] at hp
      exact ⟨fun _ => readyPacedS_ready hp, fun hm => absurd (hm0.symm.trans hm) (by decide),
        fun _ _ => hp, fun hm => absurd (hm0.symm.trans hm) (by decide)⟩
    · have hget' : vq = searchLens.get s :=
        searchEffect_active _ hse hidle
      refine ⟨fun _ => by rw [hget, hget']; exact hf.ready hm0,
        fun hm => absurd (hm0.symm.trans hm) (by decide), fun _ ht => absurd ht ?_,
        fun hm => absurd (hm0.symm.trans hm) (by decide)⟩
      rw [hchain]
      rcases hch with ⟨_, htk⟩ | ⟨hi, _⟩ | ⟨hi, _⟩
      · exact chainTick_ne_idle' htk hidle
      · exact absurd hi hidle
      · exact absurd hi hidle
  case scan_shift =>
    exact hshift (by assumption) rfl
  case shift_one =>
    rename_i hm0 hpos hso
    have hget : searchLens.get t = searchLens.get s := by
      obtain ⟨-, hset⟩ := hso
      rw [hset]; rfl
    refine ⟨fun hm => absurd (hm0.symm.trans hm) (by decide), fun _ => by
        rw [hget]; exact hf.readyS hm0,
      fun hm => absurd (hm0.symm.trans hm) (by decide), fun _ => ?_⟩
    rw [hget]
    exact readyPacedS_mono hn le_rfl (hf.shifting hm0)
  case shift_done =>
    rename_i o hm0 hpos ho
    exact ⟨fun _ => hf.readyS hm0, fun hm => by simp at hm,
      fun _ _ => readyPacedS_mono hn le_rfl (hf.shifting hm0), fun hm => by simp at hm⟩
  case replayStart =>
    rename_i o hm0 h0 ho ho'
    exact hentry' hm0
  case restart =>
    rename_i hm0 hb
    exact hentry hm0 hb
  all_goals
    (clear hx hentry hentry' hshift hf
     refine ⟨fun hm => ?_, fun hm => ?_, fun hm _ => ?_, fun hm => ?_⟩ <;> exfalso <;> simp_all)

#print axioms readyField2_background
#print axioms readyField2_tick

end TickT

/-! ## 2. The datum at a `restart` / `replayStart` landing -/

/-- **`ReadyFieldP2` at a restart landing, from the run-restricted stage data
alone.**  `Tick.restart` / `Tick.replayStart` set `clock := 2048`, so the slack
is `0`; `Restarted` makes the `ReadyRemS` half free (`readyPacedS_restarted`);
`RunEntriesS` on the paced lists of length `≥ dpEntryG k D` is
`runEntriesS_of_namedG`, whose hypotheses (`StageEntry`, `CentreLongRun`,
`NoReturn`, `EntryDepthG`, `D ≤ prepLen k`) are all statements about the stage
the machine actually entered.  **No `PostRunC`, no `ScanRealized`**, so this is
not vacuous through `CloseoutPreload30.scanRealized_absurd`.

The fuel `dpEntryG k D` is not an artefact: at fuel `0` the claim is false
(`CloseoutPreload3.not_runEntriesS_eight`). -/
theorem readyField2_entry_of_datum {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    {Rad D : ℕ} {last : Counter}
    (hclk : c.clock = 2048)
    (hR : Restarted raw r Rad last) (hSE : StageEntry Rad last)
    (hcl : CentreLongRun r (value last).toNat) (hnr : NoReturn r)
    (hdep : EntryDepthG r D) (hD : D ≤ prepLen (value last).toNat) :
    ReadyFieldP2 (dpEntryG (value last).toNat D) ⟨c, r⟩ := by
  have hp : ReadyPacedS (searchLens.get r) (dpEntryG (value last).toNat D) 0 :=
    readyPacedS_restarted hR _ 0
      (fun as hlen hpaced => runEntriesS_of_namedG hR hSE hcl hnr hdep hD as hlen hpaced)
  have hslack : (2048 : ℕ) - c.clock = 0 := by rw [hclk]
  refine ⟨fun _ => readyPacedS_ready hp, fun _ => readyPacedS_ready hp, fun _ _ => ?_,
    fun _ => ?_⟩ <;>
    · show ReadyPacedS (searchLens.get r) _ (2048 - c.clock)
      rw [hslack]; exact hp

#print axioms readyField2_entry_of_datum

end PalPeg.CloseoutPreload37
