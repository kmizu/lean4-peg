import PalPeg.CloseoutPackRun18

/-!
# `CloseoutPackRun22`: producers for `H_extraEntry3` / `H_extraTick3`, field by field

`CloseoutPackRun18.Extra3` has four fields — `ready`, `failed`, `cand`,
`scanAvail`.  This file attacks the two NAMED obligations
`H_extraEntry3` (the four fields at an `InvLPC` origin) and `H_extraTick3` (the
four fields along one `galilFrameS` tick) **one field at a time**, and records
for each field exactly what closes and what does not.

## Entry (`H_extraEntry3`, at `InvLPC w c r`)

* `ready` — **closed** (`extraEntry3_ready`): `InvS` is `Inv ∨ InvScan`, and both
  carry `search : SearchReady (searchLens.get r)` as a field.
* `cand` — **closed** (`extraEntry3_cand`): vacuous, the origin is in `scan`
  (`invS_mode`).
* `scanAvail` — **closed up to the end-of-input fact**
  (`extraEntry3_scanAvail`): the right head represents `w` and is present
  (`Inv.input`/`InvScan.input` + `ScanInvariant.rightPresent`), and by
  `GalilEndOfInput.not_canRight_iff` it can move iff it is not on the final gap
  cell `2·|w|`.  The one hypothesis left is `position r.right ≠ 2 * w.length`
  at the origin; nothing in `InvLPC` bounds the right head away from the end of
  the input.
* `failed` — **open**: `StageFailed` is a statement about the DP tape
  `r.dp.config` (halted at `pc = 347` with a `Result` on the calibrated
  window), and `InvLPC` says nothing about `dp`.  Named premise
  `hfail` in `extraEntry3_of_pack`.

## Tick (`H_extraTick3`)

`H_extraTick3` as stated in `CloseoutPackRun18` is a **bare** transport
(`Extra3 x → Tick x y → Extra3 y`, no pack at `x`).  Two of the fields are
provably not bare-transportable, so this file works with the pack-relative
form `H_extraTick3P` (`BigPack2M'' x → Tick x y → Extra3 y`), which is what
`bigPack2M''_tick` actually has in hand at the point it calls `het`
(the pack at `x` is available there; a repackaged `bigPack2M''_tick` over
`H_extraTick3P` is a copy of the `CloseoutPackRun18` proof with `hx` threaded
into `het`, and is not repeated here).

* `scanAvail` — **closed on every branch except three**
  (`extra3_scanAvail_tick`): `init` is impossible (`FrontPack.notInit`),
  `scan_wait` contradicts `Extra3.scanAvail` at `x` (its guard is
  `¬ available`, and `available` is `canRight` on `galilFrameS`), `scan_count`
  and `restart` keep the right head (`backgroundS_fields`, `restartVM`), all
  the non-`scan` stationary ticks are mode-mismatched.  The residue is
  `hres`, needed only on the branches with `x.ctl.mode ≠ scan ∨ x.ctl.clock = 1`:
  **`scan_match`** (the right head moves one cell — `canRight` at the *new*
  cell is the arrival of the next input letter, which no pack field supplies),
  `shift_done` and `replayStart` (re-entries into a non-replaying scan from
  `shift` / `replayStart`, where no `canRight` fact is carried).
* `ready` — **open**, blocked at `scan_count` / `scan_match`: the search view
  steps by `searchEffect`, and bare `SearchReady` preservation through
  `searchEffect` is the refuted leaf `hpres`
  (`GalilLeafPres.hpres_false_at`); the preserved form is the budgeted
  `SearchReadyS`/`ReadyPacedS` (`CloseoutReadyStage`), which `BigPack2M''`
  does not carry.
* `cand` — **open**, blocked at `scan_shift`: the landing is `shift` and the
  only data at hand is `shiftGuardVM s'` (a watching chain at phase `4` with
  lag `0`); there is no lemma producing `GalilDpSuffix.Candidate` on
  `stream (place s'')` from the guard (the only producers of `Candidate` are
  the DP `Result` lemmas of `GalilDpSuffix`, which read the DP tape).
* `failed` — **open**, blocked at `shift_done` / `replayStart` / `scan_*`:
  the same DP-tape datum as at entry.

## Honest status

Standard axioms only; unconditional `PAL ∈ PEG` remains **open**.  Closed
here: `ready`/`cand` at entry outright, `scanAvail` at entry modulo
`position r.right ≠ 2·|w|`, `scanAvail` along the tick on all but the
`scan_match` / `shift_done` / `replayStart` branches.  Open: `failed` (entry and
tick, DP tape), `ready` (tick, `hpres`), `cand` (tick, `scan_shift`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun22

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun11 PalPeg.CloseoutPackRun18
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

section EntryT
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-! ## 1. Entry, field by field -/

/-- **`Extra3.ready` at an `InvLPC` origin.**  Both disjuncts of `InvS` carry
`SearchReady` as a field. -/
theorem extraEntry3_ready {w : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIC : InvLPC w c r) :
    PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get r) := by
  rcases hIC.1.1.1.1 with h | ⟨k, h⟩
  · exact h.search
  · exact h.search

/-- **`Extra3.cand` at an `InvLPC` origin.**  Vacuous: the origin is in `scan`. -/
theorem extraEntry3_cand {w : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIC : InvLPC w c r) :
    c.mode = Mode.shift →
      ∃ lower h, PalPeg.GalilDpSuffix.Candidate
        (GalilScaffoldPlace.stream ((PofC centre place entry w).place r)) lower h := by
  intro hm
  rw [(invS_mode hIC.1.1.1.1).1] at hm
  exact Mode.noConfusion hm

/-- The right head of an `InvLPC` origin represents the input and is present. -/
theorem rightRep_of_invLPC {w : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIC : InvLPC w c r) :
    GalilScaffoldInputTrace.Represents r.right.head w ∧ r.right.head.focus ≠ none := by
  rcases hIC.1.1.1.1 with h | ⟨k, h⟩
  · obtain ⟨Rad, last, hR⟩ := h.rest
    exact ⟨h.input, hR.2.2.2.1.rightPresent⟩
  · exact ⟨h.input, h.scan.rightPresent⟩

/-- **`Extra3.scanAvail` at an `InvLPC` origin, modulo the end of the input.**
The right head can move iff it is not on the final gap cell
(`GalilEndOfInput.not_canRight_iff`).  The hypothesis `hend` is the one fact
`InvLPC` does not supply. -/
theorem extraEntry3_scanAvail {w : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIC : InvLPC w c r) (hend : position r.right ≠ 2 * w.length) :
    canRight r.right := by
  obtain ⟨hrep, hpres⟩ := rightRep_of_invLPC hIC
  by_contra hc
  exact hend ((PalPeg.GalilEndOfInput.not_canRight_iff _ _ hrep hpres).1 hc)

/-- **`H_extraEntry3` from the two open entry facts.**  `ready` and `cand` are
free; `failed` (the DP tape at the origin) and the end-of-input bound on the
right head are the residue. -/
theorem extraEntry3_of_pack {w : List (Fin 2)}
    (hfail : ∀ (c : Control) (r : GalilVM), InvLPC w c r →
      PalPeg.GalilLeafDp.StageFailed (PofC centre place entry w) w r (value r.radius).toNat)
    (hend : ∀ (c : Control) (r : GalilVM), InvLPC w c r → position r.right ≠ 2 * w.length) :
    H_extraEntry3 centre place entry w := by
  intro c r hIC
  exact ⟨extraEntry3_ready hIC, fun _ => hfail c r hIC, extraEntry3_cand centre place entry hIC,
    fun _ _ => extraEntry3_scanAvail hIC (hend c r hIC)⟩

end EntryT

#print axioms extraEntry3_ready
#print axioms extraEntry3_cand
#print axioms rightRep_of_invLPC
#print axioms extraEntry3_scanAvail
#print axioms extraEntry3_of_pack

/-! ## 2. Tick, field by field (pack-relative) -/

section TickT
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the pack-relative tick obligation.**  `H_extraTick3` with the
pack `BigPack2M''` at the source in hand — exactly what `bigPack2M''_tick` has
at its call site. -/
def H_extraTick3P (w : List (Fin 2)) : Prop :=
  ∀ x y : State GalilVM, BigPack2M'' centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    Extra3 centre place entry w y

/-- The bare obligation implies the pack-relative one. -/
theorem h_extraTick3P_of_h_extraTick3 {w : List (Fin 2)}
    (h : H_extraTick3 centre place entry q first w) :
    H_extraTick3P centre place entry q first w :=
  fun x y hx ht => h x y hx.extra ht

/-- **`Extra3.scanAvail` along one tick, all branches but three.**  The residue
`hres` is consulted only when `x.ctl.mode ≠ scan ∨ x.ctl.clock = 1`, i.e. on
`scan_match` (clock `1`), `shift_done` and `replayStart` (source not in
`scan`).  Every other branch is closed from the pack at `x`. -/
theorem extra3_scanAvail_tick {w : List (Fin 2)} {x y : State GalilVM}
    (hx : BigPack2M'' centre place entry q first w x)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hres : (x.ctl.mode ≠ Mode.scan ∨ x.ctl.clock = 1) →
      y.ctl.mode = Mode.scan → y.ctl.replaying = false → canRight y.vm.right) :
    y.ctl.mode = Mode.scan → y.ctl.replaying = false → canRight y.vm.right := by
  intro hm hr
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  cases h
  case init =>
    rename_i hm0 h0
    exact absurd hm0 hx.aux.front.notInit
  case scan_wait =>
    rename_i hm0 h0 hb
    exact absurd (hx.extra.scanAvail hm0 h0.1) h0.2
  case scan_count =>
    rename_i hm0 h0 hc hb
    obtain ⟨-, hr', -⟩ := backgroundS_fields _ q first hb
    show canRight t.right
    rw [hr']
    exact hx.extra.scanAvail hm0 hr
  case scan_match =>
    rename_i s' o hm0 h0 hc hcmp hmt hpl ho
    exact hres (Or.inr hc) hm hr
  case shift_done =>
    rename_i o hm0 hp ho
    exact hres (Or.inl (by rw [hm0]; decide)) hm hr
  case replayStart =>
    rename_i o hm0 h0 ho ho'
    exact hres (Or.inl (by rw [hm0]; decide)) hm hr
  case restart =>
    rename_i hm0 hb
    have hb' : restartVM entry s t := hb
    obtain ⟨wch, -, -, -, -, ht⟩ := hb'
    show canRight t.right
    rw [ht]
    exact hx.extra.scanAvail hm0 hr
  all_goals (exfalso; clear hx hres; simp_all)

/-- **`H_extraTick3P` from the three open field transports.**  `scanAvail` is
`extra3_scanAvail_tick` with its residue; `ready`, `failed`, `cand` are the
named premises (see the header for the blocking branch of each). -/
theorem extraTick3P_of_parts {w : List (Fin 2)}
    (hready : ∀ x y : State GalilVM, BigPack2M'' centre place entry q first w x →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get y.vm))
    (hfail : ∀ x y : State GalilVM, BigPack2M'' centre place entry q first w x →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
      y.ctl.mode = Mode.scan →
      PalPeg.GalilLeafDp.StageFailed (PofC centre place entry w) w y.vm
        (value y.vm.radius).toNat)
    (hcand : ∀ x y : State GalilVM, BigPack2M'' centre place entry q first w x →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
      y.ctl.mode = Mode.shift →
      ∃ lower h, PalPeg.GalilDpSuffix.Candidate
        (GalilScaffoldPlace.stream ((PofC centre place entry w).place y.vm)) lower h)
    (hres : ∀ x y : State GalilVM, BigPack2M'' centre place entry q first w x →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
      (x.ctl.mode ≠ Mode.scan ∨ x.ctl.clock = 1) →
      y.ctl.mode = Mode.scan → y.ctl.replaying = false → canRight y.vm.right) :
    H_extraTick3P centre place entry q first w :=
  fun x y hx h =>
    ⟨hready x y hx h, hfail x y hx h, hcand x y hx h,
      extra3_scanAvail_tick centre place entry q first hx h (hres x y hx h)⟩

end TickT

#print axioms h_extraTick3P_of_h_extraTick3
#print axioms extra3_scanAvail_tick
#print axioms extraTick3P_of_parts

end PalPeg.CloseoutPackRun22
