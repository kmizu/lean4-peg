import PalPeg.LocalLatchRealize
import PalPeg.LocalSysConcrete
import PalPeg.LocalWF

/-!
# Audit: is the concrete core encoded into a single `LocalStep`?

`LocalLatchRealize.pal_in_peg_of_local_core` discharges oracle group 1 of
`LocalTrackingLatch.pal_in_peg_of_local_latch` from a **core localization**:
a `L0 : LocalStep (Fin 2) Q Γ t K`, an encoding `encC : X → Q × (Fin t → STape Γ)`
and the four contracts `enc_tick`, `enc_feed`, `rep_eq`, `out_eq` (plus
`encC_init`).

This file only *checks* what exists.  It adds no `sorry`, no axiom, and edits
nothing.  Findings, in the order of the §s below:

1. Every occurrence of `PalPeg.Local.LocalStep` in `lean-pal` is a **binder**
   (a hypothesis or a variable).  No closed term of that type is ever built —
   in particular none for the concrete core `Mirrored1 P`.  So `L0`, `Q`, `Γ`,
   `t`, `K`, `blank`, `q0`, `repQ`, `outQ`, `encC` are all still open.
2. `LocalWF.exists_fppRun` / `exists_fppTick` / `ffpp` give only the *existence*
   of a tape update satisfying the abstract relation `TickL3`, and `ffpp` picks
   one with `Classical.choice`.  Choice is not the problem: the problem is that
   the chosen successor is an arbitrary `GalilVML P`, with no statement that the
   tapes it writes differ from the old ones only inside a radius-`K` window of
   each head, which is exactly what `LocalStep.next` must produce.
3. Word-independence of `(Q, Γ, t, K, next)` is **not** established for the
   steps that exist: `ffpp`, `shiftStepL`, `chooseStepC`, `rewindStepC` and
   hence `LocalWF.stepsWF` all take the word-dependent `Pw : Shared` (which the
   caller instantiates with `Pof w`), and they branch on it — e.g.
   `shiftDoneCtl Pw x = { x.ctl with output := refreshOf Pw (abs' x) _ }` and
   `chooseStepC` tests `(galilFrameS Pw qq firstT).markSet (abs' m.vm)`.
   A `LocalStep` may not depend on `w`.
4. The `Q`-side is not obviously finite: `GalilScaffoldController.Control` has
   `clock : ℕ`; only `BoundedControl delay` is the finite version.  `GalilVML`
   additionally carries `dpPc dpDone fppPc fppDone : ℕ × Bool` and the still
   abstract `chain : ChainVM`, none of which is yet split into
   "finite control" + "`t` structured tapes".

§5 records the one thing that *can* be closed generically here: the missing
data is a single bundle, and `pal_in_peg_of_local_core` fires from it.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace PalPeg.CloseoutCoreAudit

open PalPeg PalPeg.Program PegSeparation
open PalPeg.GalilScaffoldTop (State Tick)
open PalPeg.GalilScaffoldChainInputSupply (GalilVM Shared onLetterVM leftFirstVM galilFrameS)
open PalPeg.GalilLatchTracking (LedgerObligation)
open PalPeg.Local (LocalStep)
open PalPeg.LocalTrackingLatch (LocalSys LX)

/-! ## 1. The consumer and its core-side obligations -/

#check @PalPeg.LocalLatchRealize.pal_in_peg_of_local_core
#check @PalPeg.LocalLatchRealize.encL_step
#check @PalPeg.LocalLatchRealize.latchL
#check @PalPeg.Local.LocalStep
#check @PalPeg.Local.LocalStep.apply
#check @PalPeg.Local.LocalStep.realize_SAccepts

/-! ## 2. The abstract-existence side (no window contract) -/

#check @PalPeg.LocalWF.exists_fppRun
#check @PalPeg.LocalWF.exists_fppTick
#check @PalPeg.LocalWF.ffpp
#check @PalPeg.LocalWF.ffpp_spec
#check @PalPeg.LocalWF.realizes_seven
#check @PalPeg.LocalWF.stepsWF

/-! ## 3. The concrete core dynamics that `encC` would have to intertwine -/

#check @PalPeg.LocalSysConcrete.sysC
#check @PalPeg.LocalSysConcrete.tickC
#check @PalPeg.LocalSysConcrete.feedC
#check @PalPeg.LocalSysConcrete.stepOf
#check @PalPeg.LocalSysConcrete.x0C

/-! ## 4. The missing contract, named

`CoreLocal S x0` is exactly the data `pal_in_peg_of_local_core` wants and that
no file supplies for `S = LocalSysConcrete.sysC M repC`. -/

structure CoreLocal {X : Type} (S : LocalSys X) (x0 : LX X)
    (Q Γ : Type) (t K : ℕ) where
  L0 : LocalStep (Fin 2) Q Γ t K
  blank : Γ
  q0 : Q
  repQ : Q → Bool
  outQ : Q → Bool
  encC : X → Q × (Fin t → STape Γ)
  enc_tick : ∀ x : X, encC (S.tickL x) = L0.apply blank (encC x) none
  enc_feed : ∀ (a : Fin 2) (x : X), encC (S.feedC a x) = L0.apply blank (encC x) (some a)
  rep_eq : ∀ x : X, S.repL x = repQ (encC x).1
  out_eq : ∀ x : X, S.outL x = outQ (encC x).1
  encC_init : encC x0.core = (q0, fun _ => STape.blankTape blank)

/-! ## 5. The one connection that is provable today

Given the bundle, oracle group 1 is gone: this is `pal_in_peg_of_local_core`
repackaged, and it is the precise statement of what is left to build. -/

theorem pal_in_peg_of_coreLocal {X Q Γ : Type} {t K : ℕ}
    [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    (S : LocalSys X) (absS : X → State GalilVM) (Inv : List (Fin 2) → ℕ → X → Prop) (x0 : LX X)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9)
    (delay : ℕ)
    (H_letter : ∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w)
    (H_first : ∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM)
    (C : CoreLocal S x0 Q Γ t K) (htape : 0 < t)
    (x0_started : x0.started = false)
    (outL_abs : ∀ x : X, S.outL x = (absS x).ctl.output)
    (rep_sound : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length →
      (w.length - 1) * PalPeg.LocalTrackingLatch.nLocalL < s →
      S.repL (PalPeg.LocalTrackingLatch.micro S w x0 s).core = true →
      PalPeg.GalilStructuredSkeleton.ReportPoint w
          (PalPeg.LocalTrackingLatch.stAbs S absS w x0 s) ∧
        PalPeg.GalilStructuredSkeleton.Refreshed (Pof w) (qof w) (firstOf w)
          (PalPeg.LocalTrackingLatch.stAbs S absS w x0 s))
    (rep_complete : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length →
      PalPeg.GalilStructuredSkeleton.ReportPoint w
          (PalPeg.LocalTrackingLatch.stAbs S absS w x0 s) →
      PalPeg.GalilStructuredSkeleton.Refreshed (Pof w) (qof w) (firstOf w)
          (PalPeg.LocalTrackingLatch.stAbs S absS w x0 s) →
      ∃ s', s' ≤ s ∧ (w.length - 1) * PalPeg.LocalTrackingLatch.nLocalL + 1 < s' ∧
        S.repL (PalPeg.LocalTrackingLatch.micro S w x0 s').core = true)
    (x0_inv : ∀ w, 0 < w.length → Inv w 0 x0.core)
    (x0_ctl : (absS x0.core).ctl = PalPeg.GalilScaffoldController.initial delay)
    (inv_tick : ∀ w s x, PalPeg.LocalTrackingLatch.inp w s = none → Inv w s x →
      Inv w (s+1) (S.tickL x))
    (inv_feed : ∀ w s a x, PalPeg.LocalTrackingLatch.inp w s = some a → Inv w s x →
      Inv w (s+1) (S.feedC a x))
    (stutter_of_starved : ∀ w s x, PalPeg.LocalTrackingLatch.inp w s = none → Inv w s x → S.Starved x →
      absS (S.tickL x) = absS x)
    (tick_of_not_starved : ∀ w s x, PalPeg.LocalTrackingLatch.inp w s = none → Inv w s x → ¬ S.Starved x →
      Tick
        (galilFrameS (Pof w) (qof w) (firstOf w))
        delay (absS x) (absS (S.tickL x)))
    (feed_abs : ∀ w s a x, PalPeg.LocalTrackingLatch.inp w s = some a → Inv w s x →
      absS (S.feedC a x) = PalPeg.GalilArriveChain.arriveState' a (absS x))
    (H_ledger : LedgerObligation Pof qof firstOf
      (fun w => PalPeg.LocalTrackingLatch.stAbs S absS w x0)
      (fun w => w.length * PalPeg.LocalTrackingLatch.nLocalL)) :
    PegSeparation.RecognizedByTotalPEG PalPeg.PAL :=
  PalPeg.LocalLatchRealize.pal_in_peg_of_local_core (fun _ => S) absS Inv x0 Pof qof firstOf delay
    H_letter H_first C.L0 C.blank C.q0 C.repQ C.outQ C.encC htape
    (fun _ => C.enc_tick) (fun _ => C.enc_feed) (fun _ => C.rep_eq) (fun _ => C.out_eq)
    C.encC_init x0_started
    (fun _ => outL_abs) rep_sound rep_complete x0_inv x0_ctl inv_tick inv_feed
    stutter_of_starved tick_of_not_starved feed_abs H_ledger

#print axioms pal_in_peg_of_coreLocal

end PalPeg.CloseoutCoreAudit
