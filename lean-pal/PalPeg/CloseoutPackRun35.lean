import PalPeg.CloseoutPackRun33

/-!
# `CloseoutPackRun35`: `LPackM2` on the guarded pack along a trace, `pal_in_peg_final19`

§1 re-threads `CloseoutPackRun29` §3 over `PreTraceIMG`: `LPackM2` at every
trace state from the leaves (`LTickLeavesN`, `AuxPack`, `ShiftPal` — the last
gives `LTickLeaves2` through `lTickLeaves2_of_shiftPal`, using the `LPackM2`
already established at that state by the induction).

§2 records the outcome of the examination asked for: `BigResid6G` is consumed
in `pal_in_peg_final17` only through `packRunR_MG` (Run30 §5), on runs whose
origin is an *arbitrary* `InvLPC` state quantified by `CycleOracleMC3` /
`CycleOracleIMG`; the pre-loaded trace `st` is *built* from those oracle
outputs (`checkpoints_costIMG_upto1`).  So the pack states at which `LPackM2`
is needed are not, by construction, trace states, and `hall` cannot be replaced
by "leaves at trace states" without a circularity.  The one hypothesis that
remains is `H_packOnRunG`: every guarded-pack state lies on some `PreTraceIMG`
trace.  `pal_in_peg_final19` is `final18` with `hall` replaced by trace leaves
plus `H_packOnRunG`.

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun35

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack5
open PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11 PalPeg.CloseoutPackRun16
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun26
open PalPeg.CloseoutPackRun29 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun33
open PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2
open PalPeg.GalilFinalAssembly4 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus3 PalPeg.GalilLookRefined PalPeg.GalilFinalBaseNeed
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.CloseoutPackRun
open PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3 PalPeg.CloseoutPackRun5
open PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8 PalPeg.CloseoutPackRun9
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun18 PalPeg.GalilTrailRad
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus2
open GalilScaffoldInputHead GalilScaffoldCounter

section TraceG
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- The leaves asked at a trace state: `LTickLeavesN`, `AuxPack`, `ShiftPal`
(`LTickLeaves2` is derived). -/
def TraceLeaves (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  LTickLeavesN centre place entry q first w x.ctl x.vm ∧
  AuxPack x.ctl x.vm ∧
  ShiftPal centre place entry q first w x.vm

/-- **`LPackM2` at every state of a `PreTraceIMG` trace** from the leaves
(`ShiftPal`-based): the tick induction of `lpackM2_steps`, with
`LTickLeaves2` produced at each step by `lTickLeaves2_of_shiftPal`. -/
theorem lpackM2_at_traceG {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTraceIMG centre place entry q first w st Tc)
    (hLv : ∀ i, i ≤ Tc w.length → TraceLeaves centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → LPackM2 w (st i).ctl (st i).vm := by
  intro i
  induction i with
  | zero => intro _; rw [hP.base.pre.start]; exact lpackM2_boot w
  | succ n ih =>
    intro hi
    have hM2 := ih (by omega)
    obtain ⟨h1, h2, h3⟩ := hLv n (by omega)
    exact lpackM2_tick' centre place entry q first hM2 h1 h2
      (lTickLeaves2_of_shiftPal centre place entry q first hM2 h1 h3)
      (hP.base.pre.trace.tick n (by omega))

/-- **(NAMED) every guarded-pack state lies on some pre-loaded guarded trace.**
This is the `BigPack2MG` analogue of `CloseoutPackRun29.H_packOnRun`, with the
trace existentially chosen per state.  It is what links the predicate
`BigPack2MG` (consumed by `packRunR_MG` on runs from arbitrary `InvLPC`
origins) to the traces on which `lpackM2_at_traceG` speaks. -/
def H_packOnRunG (w : List (Fin 2)) : Prop :=
  ∀ x : State GalilVM, BigPack2MG centre place entry q first w x →
    ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMG centre place entry q first w st Tc ∧
      ∃ i, i ≤ Tc w.length ∧ x = st i

/-- **`LPackM2` at every guarded-pack state** from trace leaves and
`H_packOnRunG` (Run29 §3 `lpackM2_on_pack_of_run` over `BigPack2MG`). -/
theorem lpackM2_on_packG_of_run {w : List (Fin 2)}
    (hLv : ∀ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMG centre place entry q first w st Tc →
      ∀ i, i ≤ Tc w.length → TraceLeaves centre place entry q first w (st i))
    (hon : H_packOnRunG centre place entry q first w) :
    ∀ x : State GalilVM, BigPack2MG centre place entry q first w x → LPackM2 w x.ctl x.vm := by
  intro x hx
  obtain ⟨st, Tc, hP, i, hi, rfl⟩ := hon x hx
  exact lpackM2_at_traceG centre place entry q first hP (hLv st Tc hP) i hi

/-- `BigResid6G` from trace leaves, `H_packOnRunG` and `WatchShiftG`. -/
theorem bigResid6G_of_run {w : List (Fin 2)}
    (hLv : ∀ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMG centre place entry q first w st Tc →
      ∀ i, i ≤ Tc w.length → TraceLeaves centre place entry q first w (st i))
    (hon : H_packOnRunG centre place entry q first w)
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y) :
    BigResid6G centre place entry q first w :=
  bigResid6G_of_lpackM2 centre place entry q first
    (lpackM2_on_packG_of_run centre place entry q first hLv hon) hws

end TraceG

#print axioms lpackM2_at_traceG
#print axioms lpackM2_on_packG_of_run
#print axioms bigResid6G_of_run

/-- **`pal_in_peg_final18` with `hall` replaced by the trace leaves
(`LTickLeavesN`, `AuxPack`, `ShiftPal` at every state of every `PreTraceIMG`
trace) and the single named hypothesis `H_packOnRunG`.** -/
theorem pal_in_peg_final19 (entry q : ℕ) (first : Fin 9)
    (hLv : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMG centreC placeC entry q first w st Tc →
      ∀ i, i ≤ Tc w.length → TraceLeaves centreC placeC entry q first w (st i))
    (hon : ∀ w : List (Fin 2), H_packOnRunG centreC placeC entry q first w)
    (hws : ∀ w : List (Fin 2), ∀ y : State GalilVM, WatchShiftG centreC placeC entry q first w y)
    (hee : ∀ w : List (Fin 2), H_extraEntry3 centreC placeC entry w)
    (het : ∀ w : List (Fin 2), H_extraTick3 centreC placeC entry q first w)
    (hme : ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalG centreC placeC entry q first w)
    (hsc : ∀ w : List (Fin 2), H_stageScan centreC placeC entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hbs : H_bootShift centreC placeC entry q first)
    (hls : H_landShift centreC placeC entry q first)
    (hC : H_realizeLIMG' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final18 entry q first
    (fun w => lpackM2_on_packG_of_run centreC placeC entry q first (hLv w) (hon w))
    hws hee het hme hsl hsc hor hbs hls hC

#print axioms pal_in_peg_final19

end PalPeg.CloseoutPackRun35
