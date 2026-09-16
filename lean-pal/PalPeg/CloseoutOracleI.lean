import PalPeg.CloseoutLPack6
import PalPeg.GalilInvPlus3
import PalPeg.GalilOracleLeaves2

/-!
# `CloseoutOracleI`: the packed oracle and the packed boot prefix

`CloseoutLPack5` leaves two run-level residuals on the way to
`CloseoutLPack6.pal_in_peg_final6`:

* `CloseoutLPack5.H_oracleI` — `CycleOracleI`, i.e. every exit run of the cycle
  oracle carries `IPack` (`LPack` plus the four shift-entry side conditions) at
  **every** tick, not just at its landing;
* `CloseoutLPack6.BootIPack` — `IPack` at the boot state and at the single
  `init` landing of `GalilFinalAssembly4.invLPC_init`.

This module does three things.

## 1. Pack transport (§1)

`PackTick` is the tick-local pack obligation and `stepsI_of_stepsAll` turns any
`StepsAll` run out of a packed state into a `StepsI` run.  This is the only
generic way to go from the unpacked runs the oracle leaves produce to the packed
runs `StepsI` wants, and it isolates exactly *what* is missing: a single
tick-local propagation statement.  (`CloseoutLPack4` showed the pack is not
tick-local along *five* routes, so `PackTick` is not expected to be provable as
stated; it is used here only as an interface, and the route-level leaves of §3
are the residuals that matter.)

## 2. `LPack` from `InvLPC` (§2)

`lpack_of_invLPC` is the real gain of this module: the `scanInv` and `minv`
fields of `CloseoutLPack.LPack` are **derivable** at any `InvLPC` state — the
extraction is the one `GalilOracleLeaves2.segment_of_invLPC` performs internally
(`Inv.minv` / `Restarted` radius in the `Inv` branch, `InvScan.minv` /
`InvScan.scan` in the replay branch).  Only the left-head representation
(`lrep`, i.e. `CloseoutLPack3.lrep_left`'s conclusion at the state itself) stays
named.  Consequently `IPack` at *any* landing reduces to `lrep` + `ShiftLocal`
there: `ipack_of_invLPC`.

## 3. The packed oracle, by routes (§3)

`cycleOracleI_of_pieces` is `GalilInvPlus3.cycleOracleMC3_of_pieces`'s case
analysis re-run with the conclusions packed.  Because the segment piece is
`GalilOracleLeaves2.segment_of_invLPC` — which only ever produces `SegEnd`, never
`AtTarget` — the analysis has exactly the five `SegEnd` constructors, so the
`AtTarget` and `foundReplay` machinery of `cycleOracleMC3_of_pieces` does not
appear.  The five (six, counting the `lastLetter` split) route leaves are stated
directly at `CycleOutI` / `ReachAtI`, so each is "the existing unpacked leaf plus
the pack along its own run":

| leaf | unpacked counterpart | pack along the run |
|---|---|---|
| `hended`, `hlastMatch`, `hlastMismatch` | `CloseoutReadyStage` / `CloseoutReportCase` report leaves | `minv_watchSegE` + `matched_invariant'` + `lrep_left` along the scan interval |
| `hmismatch` | `GalilFoundStage.fallbackRouteMC2_of_mismatch'` | `fallback_replayStart_All` + `minv_after_fallback` |
| `hfound`, `hfoundBg` | `CloseoutFoundExits.FoundExit` leaves | `leftmost_shift` / `live_shift_of_palAt` + `places_of_guard` + `Coupled.sum`, landing by `ipack_of_invLPC` |

## 4. `BootIPack` (§4)

`bootIPack_of_parts` reduces `CloseoutLPack6.BootIPack` to three state-local
facts: `ShiftLocal` at the boot state, and `lrep` + `ShiftLocal` at the `init`
landing.  `LPack` at the boot state is `CloseoutLPack.lpack_boot` verbatim (the
boot state *is* `GalilFinalAssembly.boot (a :: rest)` by definition) and `LPack`
at the landing is §2.

`ShiftLocal` at the boot state is **not** vacuous for the reason one would hope:
the boot chain is idle (`GalilBootVM.initVM0`), but `compareFound`'s chain clause
is `chainAt a found …`, whose third disjunct starts the chain (`chainStart`,
i.e. `.watch _`) when the search quantum of that very comparison reports
`found`.  So the `init` mode of the controller does not exclude a
`beginShiftVM'` successor; what would exclude it is that the boot search cannot
report `found` in one quantum, which is a statement about
`GalilBootVM.initVM0`'s search state, not about the chain.  It is therefore left
NAMED (`H_bootShift`).

## Residual (NAMED), precisely

* `PackTick centre place entry q first w` (§1) — interface only.
* `H_lrepC centre place entry q first raw` (§2) —
  `∀ c r, InvLPC raw c r → c.mode ≠ Mode.init →
     Represents r.left.head raw ∧ r.left.head.focus ≠ none`.
* the six route leaves of `cycleOracleI_of_pieces` (§3), each at `CycleOutI` /
  `ReachAtI` with `InvLPS` entry; plus `hstage`
  (`∀ c r, InvLPC raw c r → InvLPS (PofC …) q first raw c r`) and `hends`, both
  as in `GalilInvPlus3.cycleOracleMC3_of_pieces` / `segment_of_invLPS`.
* `H_bootShift centre place entry q first` (§4) — `ShiftLocal` at the boot state.
* `H_landShift centre place entry q first` (§4) — `ShiftLocal` at the `init`
  landing.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutOracleI

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilInvPlus3
open PalPeg.GalilOracleMC PalPeg.GalilOracleMC2 PalPeg.GalilOracleM
open PalPeg.GalilSegmentConstruct PalPeg.GalilOracleLeaves2
open PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2 PalPeg.GalilFinalAssembly4
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6

/-! ## 1. Pack transport -/

section Transport
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the tick-local pack obligation.**  One tick of the scan frame out
of a packed state, landing in a `SoundScanNR` state, keeps the pack. -/
def PackTick (w : List (Fin 2)) : Prop :=
  ∀ x y : State GalilVM, IPack centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    SoundScanNR w y → IPack centre place entry q first w y

/-- **Any `StepsAll` run out of a packed state is a `StepsI` run.**  This is the
generic bridge from the unpacked runs the oracle leaves produce to the packed
runs `CloseoutLPack5.StepsI` asks for. -/
theorem stepsI_of_stepsAll {w : List (Fin 2)} (hpt : PackTick centre place entry q first w)
    {k : ℕ} {x y : State GalilVM} (hx : IPack centre place entry q first w x)
    (h : StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) k x y) :
    StepsI centre place entry q first w k x y := by
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  refine ⟨g, hg0, hgk, htr, ?_⟩
  intro i
  induction i with
  | zero => intro _; rw [hg0]; exact hx
  | succ n ih =>
    intro hi
    exact hpt (g n) (g (n+1)) (ih (by omega)) (htr.tick n (by omega)) (htr.good (n+1) hi)

end Transport

#print axioms stepsI_of_stepsAll

/-! ## 2. `LPack` at an `InvLPC` state -/

section Pack
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the left-head representation at an `InvLPC` state.**  The `lrep`
field of `CloseoutLPack.LPack`; `CloseoutLPack3.lrep_left` moves it along a
comparison, but at an entry state it has to come from the input layer. -/
def H_lrepC (raw : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvLPC raw c r → c.mode ≠ Mode.init →
    GalilScaffoldInputTrace.Represents r.left.head raw ∧ r.left.head.focus ≠ none

end Pack

/-- **The scan invariant and the centre invariant are free at an `InvLPC`
state.**  Exactly the extraction `GalilOracleLeaves2.segment_of_invLPC` performs
internally, isolated: in the `Inv` branch the restart supplies the radius and
`Inv.minv` the centre invariant, in the `InvScan` branch the fields `scan` and
`minv` do. -/
theorem parts_of_invLPC {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIC : InvLPC raw c r) :
    c.mode = Mode.scan ∧ MInv raw c r ∧
      ∃ R : ℕ, ScanInvariant raw (position r.center) R r.left r.right := by
  have hI : InvS raw c r := hIC.1.1.1.1
  rcases hI with h | ⟨k, h⟩
  · obtain ⟨Rad, last, hR⟩ := h.rest
    exact ⟨h.mode.1, h.minv, Rad, hR.2.2.2.1⟩
  · exact ⟨h.mode.1, h.minv, k, h.scan⟩

#print axioms parts_of_invLPC

section PackOf
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`CloseoutLPack.LPack` at any `InvLPC` state**, modulo the left-head
representation.  Two of the three fields are theorems. -/
theorem lpack_of_invLPC {raw : List (Fin 2)} (hlr : H_lrepC raw)
    {c : Control} {r : GalilVM} (hIC : InvLPC raw c r) : LPack raw c r := by
  obtain ⟨hm, hM, R, hi⟩ := parts_of_invLPC hIC
  exact ⟨fun hne => hlr c r hIC hne, fun _ _ => ⟨R, hi⟩, fun hne => hM⟩

/-- **`IPack` at any `InvLPC` state**, modulo the left-head representation and
the shift-entry conditions at that state.  This is the landing half of every
route: `GalilInvPlus3.invLPS_of_landed` and `Inv.minv` are absorbed into
`InvLPC`. -/
theorem ipack_of_invLPC {raw : List (Fin 2)} (hlr : H_lrepC raw)
    {x : State GalilVM} (hIC : InvLPC raw x.ctl x.vm)
    (hsh : ShiftLocal centre place entry q first raw x) :
    IPack centre place entry q first raw x :=
  ⟨lpackG_of_lpack (lpack_of_invLPC hlr hIC), hsh⟩

end PackOf

#print axioms lpack_of_invLPC
#print axioms ipack_of_invLPC

/-! ## 3. The packed cycle oracle, by routes -/

section Oracle
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`GalilInvPlus3.cycleOracleMC3_of_pieces` with packed conclusions.**  The
segment piece is `GalilOracleLeaves2.segment_of_invLPC`, so the case analysis is
over the five `SegEnd` constructors only; each route leaf concludes `CycleOutI`
or `ReachAtI` (i.e. carries `IPack` along its own run) and is NAMED. -/
theorem cycleOracleI_of_pieces (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v →
      PalPeg.GalilBranchInvariants2.SearchReady v)
    (hstage : ∀ (c : Control) (r : GalilVM), InvLPC raw c r →
      InvLPS (PofC centre place entry raw) q first raw c r)
    (hends : ∀ (c : Control) (r : GalilVM),
      InvLPS (PofC centre place entry raw) q first raw c r →
      ∃ n : ℕ, ∀ (es : List Bool) (c' : Control) (t : GalilVM),
        WatchSegE (PofC centre place entry raw) q first 2048 es c r c' t →
        es.length = n → SegEnd (PofC centre place entry raw) c' t)
    (hended : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPS (PofC centre place entry raw) q first raw c r →
      position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → ¬ canRight t.right →
      ReachAtI centre place entry q first raw m c r)
    (hlastMatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPS (PofC centre place entry raw) q first raw c r →
      position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      ReachAtI centre place entry q first raw m c r)
    (hlastMismatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPS (PofC centre place entry raw) q first raw c r →
      position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      ReachAtI centre place entry q first raw m c r)
    (hmismatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPS (PofC centre place entry raw) q first raw c r →
      position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      CycleOutI centre place entry q first raw m c r)
    (hfound : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPS (PofC centre place entry raw) q first raw c r →
      position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centre place entry raw) true t vq ∧ vq.search.mode = .found) →
      CycleOutI centre place entry q first raw m c r)
    (hfoundBg : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPS (PofC centre place entry raw) q first raw c r →
      position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centre place entry raw) false t vq ∧ vq.search.mode = .found) →
      CycleOutI centre place entry q first raw m c r) :
    CycleOracleI centre place entry q first raw := by
  intro m c r hm1 hmle hIC hp
  have hIS : InvLPS (PofC centre place entry raw) q first raw c r := hstage c r hIC
  obtain ⟨c', t, hsW, hEnd⟩ :=
    segment_of_invLPC centre place entry q first raw hex hsearch hpres c r hIC (hends c r hIS)
  cases hEnd with
  | ended hn => exact Or.inl (hended m c r c' t hm1 hmle hIS hp hsW hn)
  | mismatch hr hc hav hne => exact hmismatch m c r c' t hm1 hmle hIS hp hsW hr hc hav hne
  | found hc hav hmt hq => exact hfound m c r c' t hm1 hmle hIS hp hsW hc hav hmt hq
  | foundBackground hc hq => exact hfoundBg m c r c' t hm1 hmle hIS hp hsW hc hq
  | lastLetter hc hav hpop hinc =>
      by_cases hmt : read (left t.left) = read (right t.right)
      · exact Or.inl (hlastMatch m c r c' t hm1 hmle hIS hp hsW hc hav hpop hinc hmt)
      · exact Or.inl (hlastMismatch m c r c' t hm1 hmle hIS hp hsW hc hav hpop hinc hmt)

/-- **`CloseoutLPack5.H_oracleI` from the packed pieces**, uniformly in `w`. -/
theorem h_oracleI_of_pieces
    (hcyc : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleI centre place entry q first w) :
    H_oracleI centre place entry q first :=
  fun w hw => hcyc w hw

end Oracle

#print axioms cycleOracleI_of_pieces
#print axioms h_oracleI_of_pieces

/-! ## 4. `BootIPack` -/

section Boot
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) `ShiftLocal` at the boot state.**  See the module docstring: the
boot chain is idle, but `chainAt`'s third disjunct can still start it inside the
very comparison, so `init` mode does not make this vacuous. -/
def H_bootShift : Prop :=
  ∀ (a : Fin 2) (rest : List (Fin 2)),
    ShiftLocal centre place entry q first (a :: rest)
      ⟨GalilScaffoldController.initial 2048, GalilBootVM.initVM0 (a :: rest)⟩

/-- **(NAMED) `ShiftLocal` at the `init` landing.** -/
def H_landShift : Prop :=
  ∀ (a : Fin 2) (rest : List (Fin 2)) (c1 : Control) (t : GalilVM),
    StepsAll (galilFrameS (PofC centre place entry (a :: rest)) q first) 2048
      (SoundScanNR (a :: rest)) 1
      ⟨GalilScaffoldController.initial 2048, GalilBootVM.initVM0 (a :: rest)⟩ ⟨c1, t⟩ →
    InvLPC (a :: rest) c1 t →
    ShiftLocal centre place entry q first (a :: rest) ⟨c1, t⟩

/-- **`CloseoutLPack6.BootIPack` from the three state-local residuals.**  The
`LPack` half at the boot state is `CloseoutLPack.lpack_boot` (the boot state *is*
`GalilFinalAssembly.boot (a :: rest)`), and at the landing it is §2. -/
theorem bootIPack_of_parts
    (hlr : ∀ w : List (Fin 2), H_lrepC w)
    (hbs : H_bootShift centre place entry q first)
    (hls : H_landShift centre place entry q first) :
    BootIPack centre place entry q first := by
  intro a rest
  refine ⟨⟨lpackG_of_lpack (lpack_boot (a :: rest)), hbs a rest⟩, ?_⟩
  intro c1 t hst hI
  exact ipack_of_invLPC centre place entry q first (hlr (a :: rest)) hI (hls a rest c1 t hst hI)

end Boot

#print axioms bootIPack_of_parts

/-! ## 5. What `pal_in_peg_final6` is left with -/

/-- **`CloseoutLPack6.pal_in_peg_final6` over this module's residuals.**  The
boot prefix is reduced to the three state-local facts of §4 and the oracle to the
packed routes of §3; `H_realizeLI'` is untouched. -/
theorem pal_in_peg_final6' (entry q : ℕ) (first : Fin 9)
    (hlr : ∀ w : List (Fin 2), H_lrepC w)
    (hbs : H_bootShift centreC placeC entry q first)
    (hls : H_landShift centreC placeC entry q first)
    (hcyc : ∀ w : List (Fin 2), 0 < w.length → CycleOracleI centreC placeC entry q first w)
    (hC : H_realizeLI' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final6 entry q first
    (bootIPack_of_parts centreC placeC entry q first hlr hbs hls)
    (fun w hw => hcyc w hw) hC

#print axioms pal_in_peg_final6'

end PalPeg.CloseoutOracleI
