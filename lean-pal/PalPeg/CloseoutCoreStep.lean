import PalPeg.CloseoutCoreAudit
import PalPeg.GalilVMEncode

/-!
# Closeout, step 1: a concrete carrier for `CloseoutCoreAudit.CoreLocal`

`CloseoutCoreAudit` records that `CoreLocal` has no inhabitant for the concrete
core `Mirrored1 P`, and lists four gaps.  This file closes the *shape* of gaps
(1), (2) and (4) and names gap (3) exactly; it builds no `LocalStep` and proves
no new dynamics, so

**無条件 PAL ∈ PEG は未完.**

## What is actually established here

* **§1 (gap 1, alphabet and geometry).**  `Γ := GalilVMEncode.Sym` with
  `blank := GalilVMEncode.blank`; the tape count `tL P tChain` is the explicit
  field-by-field budget of `GalilVML P` plus the mirror view, and `tL_pos`
  discharges the `htape : 0 < t` side condition of
  `CloseoutCoreAudit.pal_in_peg_of_coreLocal`.
* **§2 (gap 4, finiteness of `Q`).**  `QL delay Lp Lf P QC` is a *finite*
  control: the clock-bounded controller, the six finite mode/flag fields, the
  two program counters as `Fin (L+1)` together with their `done` and buffer
  `active` bits, the counter bank's `roles`/`pol` tables, and a finite summary
  `QC` of the chain.  `Fintype` and `DecidableEq` are derived (`instFintypeQL`,
  `instDecEqQL`), which is what `pal_in_peg_of_coreLocal` demands of `Q`.
* **§3 (gap 4, the control projection).**  `qOfL` reads that control off the
  concrete state, totally: the ℕ-valued `clock`, `dpPc`, `fppPc` are clamped,
  and `clampCtl_val` / `pcOf_val` say the clamp is the identity on the states
  where the corresponding bound holds.  The residual is a *bound* hypothesis,
  not a definition.
* **§4 (gap 2, word-independence).**  `AgreeOn` is pointwise agreement on the
  states the `Realizes` obligation quantifies over, `realizes_congr` transports
  `Realizes` along it, and `realizes_seven_of_agree` turns
  `LocalWF.realizes_seven` — stated for the word-dependent `stepsWF Pw` — into
  the same seven obligations for an arbitrary word-free `SL : Steps P`.  Gap (2)
  is thereby reduced to seven `AgreeOn` facts, one per mode, each a statement
  about reachable states only.  The `.fpp` one is the "fpp quantum" obligation:
  a `SL.fpp` written as a fixed-window function must agree with `LocalWF.ffpp`,
  whose successor is picked by `Classical.choice`.
* **§5 (packaging).**  `CoreLocal` for `sysC` is exactly the two intertwining
  facts `RealizedTick` / `RealizedFeed` plus the three readout equations
  (`coreLocal_of`).

## What is *not* established (gap 3, and the rest of gap 1)

No `encC : Mirrored1 P → QL … × (Fin (tL …) → STape Sym)` is defined, and no
`LocalStep` is built: the window-locality of each mode step — that it rewrites
only the radius-`K` window of each head and displaces each head by at most `K` —
is not proved anywhere, and `GalilVMEncode` encodes the *abstract* `GalilVM`,
not `GalilVML P`.  Those remain open exactly as `CloseoutCoreAudit` states.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace PalPeg.CloseoutCoreStep

variable {lastTick : ℕ}

open PalPeg PalPeg.Program
open PalPeg.GalilScaffoldTop (State)
open PalPeg.GalilScaffoldController (Control Mode Bounded BoundedControl)
open PalPeg.GalilScaffoldChainInputSupply (GalilVM ChainVM Shared galilFrameS)
open PalPeg.LocalState (GalilVML Ctr)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalSysConcrete (Steps Realizes InvC Needy TickNeed Starved sysC tickC feedC)
open PalPeg.GalilLookRefined (needT')
open PalPeg.Local (LocalStep)
open PalPeg.LocalTrackingLatch (LocalSys LX)
open PalPeg.CloseoutCoreAudit (CoreLocal)

/-! ## 1. The alphabet and the tape budget -/

/-- The tape alphabet of the core, reused from `GalilVMEncode`. -/
abbrev Γc : Type := PalPeg.GalilVMEncode.Sym

/-- The blank symbol. -/
abbrev blankc : Γc := PalPeg.GalilVMEncode.blank

instance : Fintype Γc := inferInstanceAs (Fintype PalPeg.GalilVMEncode.Sym)
instance : DecidableEq Γc := inferInstanceAs (DecidableEq PalPeg.GalilVMEncode.Sym)

/-- Tapes per `LocalInputView.InputView`: `back` (carrying `focus` at the head),
`near`, and the two stacks of the real-time queue `far`.  (`gap` is a bit and
lives in the finite control of the view's owner, not on a tape.) -/
def tView : ℕ := 4

/-- The six cursors: `left`, `center`, `right`, `walkerView`, `fppWalker` of
`GalilVML`, and the parked mirror `Mirrored1.mirL`. -/
def nViews : ℕ := 6

/-- `LocalMirror.Mirrored k` is a source tape plus `k` mirrors, and the core has
`radiusMir : Mirrored 2`, `lowerMir : Mirrored 1`, `lengthMir : Mirrored 1`. -/
def tMir : ℕ := (1 + 2) + (1 + 1) + (1 + 1)

/-- `LocalBuffers.Buffered n` is two banks of `n` tapes; the `active` bit is
finite control, the `job : Option ℕ` field gets one unary tape each.  The core
has `dpBuf : Buffered 12` and `fppBuf : Buffered 9`. -/
def tBuf : ℕ := (2 * 12 + 1) + (2 * 9 + 1)

/-- The whole tape budget: the six cursors, the `P` counter tapes of the bank,
the mirror banks, the two double buffers, and `tChain` tapes for the chain view
(still abstract, hence a parameter). -/
def tL (P tChain : ℕ) : ℕ := nViews * tView + P + tMir + tBuf + tChain

theorem tL_pos (P tChain : ℕ) : 0 < tL P tChain := by
  unfold tL nViews tView tMir tBuf; omega

/-! ## 2. The finite control -/

/-- The search unit's finite mode. -/
abbrev SMode : Type := PalPeg.GalilScaffoldSearchFinish.Mode

/-- The fpp unit's finite mode. -/
abbrev FMode : Type := PalPeg.GalilScaffoldChainInputSupply.FppControl.Mode

instance : Fintype SMode :=
  ⟨⟨[PalPeg.GalilScaffoldSearchFinish.Mode.idle, .grow, .lower, .lowerHome, .copy, .home,
      .run, .found, .missed, .wait, .double], by decide⟩, by intro x; cases x <;> decide⟩

instance : Fintype FMode :=
  ⟨⟨[PalPeg.GalilScaffoldChainInputSupply.FppControl.Mode.copy, .home, .run], by decide⟩,
    by intro x; cases x <;> decide⟩

/-- **The finite control of the core.**  Everything in `GalilVML P` that is not
a tape, with the three ℕ-valued fields bounded: the controller clock by `delay`
(`BoundedControl`), the two program counters by the lengths `Lp`, `Lf` of the
two `ProgLang` codes.  `QC` is a finite summary of the still abstract
`chain : ChainVM`. -/
def QL (delay Lp Lf P : ℕ) (QC : Type) : Type :=
  BoundedControl delay ×
    SMode × Bool × Fin 4 ×
    FMode × Bool × Bool ×
    (Fin (Lp + 1) × Bool × Bool) ×
    (Fin (Lf + 1) × Bool × Bool) ×
    (Ctr → Fin P) × (Ctr → Bool) × QC

noncomputable instance instFintypeQL (delay Lp Lf P : ℕ) (QC : Type) [Fintype QC]
    [DecidableEq QC] : Fintype (QL delay Lp Lf P QC) :=
  inferInstanceAs (Fintype (BoundedControl delay ×
    SMode × Bool × Fin 4 ×
    FMode × Bool × Bool ×
    (Fin (Lp + 1) × Bool × Bool) ×
    (Fin (Lf + 1) × Bool × Bool) ×
    (Ctr → Fin P) × (Ctr → Bool) × QC))

/-- Each component of `QL` has decidable equality on its own (these six
`example`s), but instance search does not assemble the twelve-fold product, so
the instance below is produced classically; this adds only `Classical.choice`,
which the development already uses. -/
example (delay : ℕ) : DecidableEq (BoundedControl delay) := inferInstance
example : DecidableEq SMode := inferInstance
example : DecidableEq FMode := inferInstance
example (P : ℕ) : DecidableEq (Ctr → Fin P) := inferInstance
example : DecidableEq (Ctr → Bool) := inferInstance
example (Lp : ℕ) : DecidableEq (Fin (Lp + 1) × Bool × Bool) := inferInstance

noncomputable instance instDecEqQL (delay Lp Lf P : ℕ) (QC : Type) [DecidableEq QC] :
    DecidableEq (QL delay Lp Lf P QC) := Classical.decEq _

/-! ## 3. Reading the finite control off the concrete state -/

/-- Total clamp of the controller record into `BoundedControl delay`. -/
def clampCtl (delay : ℕ) (c : Control) : BoundedControl delay :=
  ⟨{ c with clock := min c.clock delay }, Nat.min_le_right _ _⟩

/-- On a clock-bounded record the clamp is the identity. -/
theorem clampCtl_val {delay : ℕ} {c : Control} (h : Bounded delay c) :
    (clampCtl delay c).val = c := by
  have hm : min c.clock delay = c.clock := Nat.min_eq_left h
  simp only [clampCtl, hm]

/-- Total clamp of a program counter. -/
def pcOf (L : ℕ) (p : ℕ) : Fin (L + 1) := ⟨min p L, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

theorem pcOf_val {L p : ℕ} (h : p ≤ L) : (pcOf L p).val = p := Nat.min_eq_left h

variable {P : ℕ}

variable {Good : Mirrored1 P → Prop}

/-- **The control projection.**  Total, and word-independent by construction. -/
def qOfL (delay Lp Lf : ℕ) {QC : Type} (encChain : ChainVM → QC) (m : Mirrored1 P) :
    QL delay Lp Lf P QC :=
  (clampCtl delay m.vm.ctl,
    m.vm.searchMode, m.vm.searchFinalStage, m.vm.searchQuarter,
    m.vm.fppMode, m.vm.fppFinalStage, m.vm.periodOnly,
    (pcOf Lp m.vm.dpPc, m.vm.dpDone, m.vm.dpBuf.active),
    (pcOf Lf m.vm.fppPc, m.vm.fppDone, m.vm.fppBuf.active),
    m.vm.roles, m.vm.pol, encChain m.vm.chain)

/-- The controller mode survives the projection, so `repL`/`outL`-style readouts
and the mode dispatch are functions of `qOfL`. -/
@[simp] theorem qOfL_mode (delay Lp Lf : ℕ) {QC : Type} (encChain : ChainVM → QC)
    (m : Mirrored1 P) : ((qOfL delay Lp Lf encChain m).1).val.mode = m.vm.ctl.mode := rfl

/-- The output bit — the only thing `sysC.outL` reads — is a function of the
projected control. -/
@[simp] theorem qOfL_output (delay Lp Lf : ℕ) {QC : Type} (encChain : ChainVM → QC)
    (m : Mirrored1 P) : ((qOfL delay Lp Lf encChain m).1).val.output = m.vm.ctl.output := rfl

/-! ## 4. Word-independence of the mode steps -/

variable {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}

/-- **Agreement on the reachable states of one mode.**  Exactly the states the
`Realizes` obligation of `LocalSysConcrete` quantifies over. -/
def AgreeOn (Good : Mirrored1 P → Prop) (raw : List (Fin 2)) (stOf : ℕ → State GalilVM)
    (f g : Mirrored1 P → Mirrored1 P) (md : Mode) : Prop :=
  ∀ (m : Mirrored1 P) (k j : ℕ), InvC Good raw stOf m → m.vm.ctl.mode = md → ¬ Starved m.vm →
    Needy raw stOf k j m.vm → TickNeed raw stOf k j → f m = g m

theorem agreeOn_refl (f : Mirrored1 P → Mirrored1 P) (md : Mode) :
    AgreeOn Good raw stOf f f md := fun _ _ _ _ _ _ _ _ => rfl

/-- **`Realizes` only sees the reachable states**, so it transports along
`AgreeOn`.  This is the lemma that makes word-independence a *pointwise* residual
rather than a structural one. -/
theorem realizes_congr {f g : Mirrored1 P → Mirrored1 P} {md : Mode}
    (h : AgreeOn Good raw stOf f g md) (hf : Realizes Good raw stOf lastTick f md) :
    Realizes Good raw stOf lastTick g md := by
  intro m k j hinv hmd hns hn hneed hbefore
  have := hf m k j hinv hmd hns hn hneed hbefore
  rwa [h m k j hinv hmd hns hn hneed] at this

/-- **Gap (2), reduced.**  Given the word-dependent seven of `LocalWF`, any
word-free `SL : Steps P` whose seven phase steps agree with them on reachable
states satisfies the same seven obligations.

The `.fpp` component of `hagree` is the "fpp quantum" obligation: `SL.fpp` is to
be a fixed-window function (one `GalilDpCode` instruction), and must agree with
`LocalWF.ffpp`, whose successor is produced by `Classical.choice`. -/
theorem realizes_seven_of_agree {Pw : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}
    (SL : Steps P)
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, k < lastTick → PalPeg.GalilScaffoldTop.Tick (galilFrameS Pw qq first) delay
      (stOf k) (stOf (k+1)))
    (H_afterLast : ∀ k, lastTick ≤ k → stOf k = stOf lastTick)
    (H_start : PalPeg.LocalWF.NoReplay (stOf 0)) (hq : qq ≤ 64)
    (H_wf : ∀ m : Mirrored1 P, InvC Good raw stOf m → PalPeg.LocalWF.LocalWF m.vm)
    (H_shiftIdleInCopy : ∀ k, (stOf k).ctl.mode = .copy →
      ¬ PalPeg.GalilTickFun3.ShiftRemaining (stOf k).vm)
    (H_shiftLedgerOnTrace : ∀ k, (stOf k).ctl.mode = .shift →
      PalPeg.GalilScaffoldChainInputSupply.CopyIdle (stOf k).vm ∧
        GalilScaffoldCounter.value (stOf k).vm.remaining
          ≤ GalilScaffoldCounter.value (stOf k).vm.radius ∧
        PalPeg.GalilScaffoldChainInputSupply.SpanRep (stOf k).vm)
    (h_shift : AgreeOn Good raw stOf (PalPeg.LocalRealizesPhase.shiftStepL (P := P) Pw) SL.shift .shift)
    (h_copy : AgreeOn Good raw stOf (PalPeg.LocalRealizesPhase.copyStepL (P := P)) SL.copy .copy)
    (h_home : AgreeOn Good raw stOf (PalPeg.LocalRealizesPhase.homeStepL (P := P)) SL.home .home)
    (h_fpp : AgreeOn Good raw stOf (PalPeg.LocalWF.ffpp (P := P) Pw qq first) SL.fpp .fpp)
    (h_markEnd : AgreeOn Good raw stOf (PalPeg.LocalRealizesPhase.markEndStepL (P := P))
      SL.markEnd .markEnd)
    (h_choose : AgreeOn Good raw stOf (PalPeg.LocalRealizesScan.chooseStepC (P := P) Pw qq first)
      SL.choose .choose)
    (h_rewind : AgreeOn Good raw stOf (PalPeg.LocalRealizesScan.rewindStepC (P := P) Pw qq first)
      SL.rewind .rewind) :
    Realizes Good raw stOf lastTick SL.shift .shift ∧ Realizes Good raw stOf lastTick SL.copy .copy ∧
    Realizes Good raw stOf lastTick SL.home .home ∧ Realizes Good raw stOf lastTick SL.fpp .fpp ∧
    Realizes Good raw stOf lastTick SL.markEnd .markEnd ∧ Realizes Good raw stOf lastTick SL.choose .choose ∧
    Realizes Good raw stOf lastTick SL.rewind .rewind := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ :=
    PalPeg.LocalWF.realizes_seven (P := P) (delay := delay) H_shared H_trace H_afterLast H_start hq H_wf
      H_shiftIdleInCopy H_shiftLedgerOnTrace
  exact ⟨realizes_congr h_shift r1, realizes_congr h_copy r2, realizes_congr h_home r3,
    realizes_congr h_fpp r4, realizes_congr h_markEnd r5, realizes_congr h_choose r6,
    realizes_congr h_rewind r7⟩

/-! ## 5. Packaging: what a `CoreLocal` for `sysC` amounts to -/

variable {Q : Type} {t K : ℕ}

/-- The tick half of the intertwining: `enc_tick` of `CoreLocal`. -/
def RealizedTick (encC : Mirrored1 P → Q × (Fin t → STape Γc)) (L0 : LocalStep (Fin 2) Q Γc t K)
    (f : Mirrored1 P → Mirrored1 P) : Prop :=
  ∀ m : Mirrored1 P, encC (f m) = L0.apply blankc (encC m) none

/-- The arrival half: `enc_feed` of `CoreLocal`. -/
def RealizedFeed (encC : Mirrored1 P → Q × (Fin t → STape Γc))
    (L0 : LocalStep (Fin 2) Q Γc t K) : Prop :=
  ∀ (a : Fin 2) (m : Mirrored1 P), encC (feedC a m) = L0.apply blankc (encC m) (some a)

/-- **`CoreLocal` for the concrete core, from its two intertwinings and three
readouts.**  Nothing here is new dynamics; it records the exact residual shape,
and `CloseoutCoreAudit.pal_in_peg_of_coreLocal` consumes the result. -/
def coreLocal_of (M : Steps P) (repC : Control → Bool) (x0 : LX (Mirrored1 P))
    (L0 : LocalStep (Fin 2) Q Γc t K) (q0 : Q) (repQ outQ : Q → Bool)
    (encC : Mirrored1 P → Q × (Fin t → STape Γc))
    (htick : RealizedTick encC L0 (tickC M))
    (hfeed : RealizedFeed encC L0)
    (hrep : ∀ m : Mirrored1 P, repC m.vm.ctl = repQ (encC m).1)
    (hout : ∀ m : Mirrored1 P, m.vm.ctl.output = outQ (encC m).1)
    (hinit : encC x0.core = (q0, fun _ => STape.blankTape blankc)) :
    CoreLocal (sysC M repC) x0 Q Γc t K where
  L0 := L0
  blank := blankc
  q0 := q0
  repQ := repQ
  outQ := outQ
  encC := encC
  enc_tick := htick
  enc_feed := fun a m => hfeed a m
  rep_eq := hrep
  out_eq := hout
  encC_init := hinit

end PalPeg.CloseoutCoreStep

#print axioms PalPeg.CloseoutCoreStep.tL_pos
#print axioms PalPeg.CloseoutCoreStep.clampCtl_val
#print axioms PalPeg.CloseoutCoreStep.realizes_congr
#print axioms PalPeg.CloseoutCoreStep.realizes_seven_of_agree
#print axioms PalPeg.CloseoutCoreStep.coreLocal_of
