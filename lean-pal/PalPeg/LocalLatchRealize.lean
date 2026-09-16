import PalPeg.LocalTrackingLatch

/-!
# Oracle 1 of `LocalTrackingLatch`, discharged generically

`LocalTrackingLatch.pal_in_peg_of_local_latch` takes, as its first oracle group,
a `LocalStep` `L`, an initial control state, two control predicates `ansQ` /
`startQ` and an encoding `enc : LX X → Q' × (Fin t → STape Γ')` such that

* `enc_step` — `L.apply blank` intertwines with `stepL S` (`latchStep` /
  `arriveL`), i.e. with the *latched* dynamics;
* `enc_init`, `enc_ans`, `enc_started`.

This file removes that group from the caller's obligations whenever the **core**
dynamics `S.tickL` / `S.feedC` is already `K`-local, i.e. simulated by some
`L0 : LocalStep (Fin 2) Q Γ t K` through a core encoding
`encC : X → Q × (Fin t → STape Γ)`.

## The construction

`latchL L0 repQ outQ : LocalStep (Fin 2) (Q × Bool × Bool) Γ t K` runs `L0` and,
*in the finite control only*, keeps the latch and the started bit:

* the tape part of `next` is literally `L0`'s (`latchL_tapes`), so `disp_le` is
  inherited verbatim and the step is `K`-local with the same `t` and `K`;
* the core component of the new control is literally `L0`'s (`latchL_core`);
* the latch bit is `b || (repQ q' && outQ q')` where `q'` is the **new** core
  control state, which `LocalStep.next` computes before it has to name the new
  latch — this is why the `ans` read *after* the tick costs nothing;
* on an arrival (`a = some _`) the latch is reset and `started` is set.

## The one hypothesis this route needs

`LocalStep.next` may look at the old control state and the old windows only;
`latchStep` needs `repL` / `outL` of the *new* core. The new core's window is
not available to `next` (the head has already moved), so the generic route
requires `repL` and `outL` to factor through the local control state:

  `rep_eq : ∀ x, S.repL x = repQ (encC x).1`
  `out_eq : ∀ x, S.outL x = outQ (encC x).1`

i.e. the report test and the output bit must be readable off the finite control
of the core simulation. This is a constraint on the core encoding `encC`, not on
`LocalStepRealize`; nothing about `LocalStepRealize` is assumed here.

Everything else (`enc_init`, `enc_ans`, `enc_started`) becomes definitional.

The per-symbol input is handled entirely by `LocalStep.applyN`, which feeds
`some a` to the first of the `n = nLocalL` local steps and `none` to the other
`n - 1`; that is exactly `blockL = arriveL` then `nLocalL - 1` `latchStep`s, so
no extra hypothesis is needed for the arrival slot.

**Unconditional PAL ∈ PEG is not finished**: the remaining oracles of
`pal_in_peg_of_local_latch` (`rep_sound`, `rep_complete`, the stutter oracles,
`feed_abs`, `H_ledger`) are untouched here.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PalPeg.LocalLatchRealize

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.Local (LocalStep)
open PalPeg.LocalTrackingLatch

variable {X Q Γ : Type} {t K : ℕ}

/-! ## 1. The extended finite control -/

/-- The control of the latched local step: the core control, the latch, the
started bit. Finite and decidable whenever `Q` is. -/
abbrev QL (Q : Type) : Type := Q × Bool × Bool

/-- The new latch bit: reset on an arrival, otherwise `b` or "the new core
control state passes the report test and outputs `true`". -/
def ansNext (repQ outQ : Q → Bool) : Option (Fin 2) → Bool → Q → Bool
  | none, b, q' => b || (repQ q' && outQ q')
  | some _, _, _ => false

/-- The new started bit: set on an arrival, otherwise unchanged. -/
def startNext : Option (Fin 2) → Bool → Bool
  | none, b => b
  | some _, _ => true

/-! ## 2. The latched local step -/

/-- **The extended step is `K`-local.** `latchL L0 repQ outQ` is a `LocalStep`
with the *same* tape count `t` and the *same* radius `K`; only the finite
control grows, by the two bits. -/
def latchL (L0 : LocalStep (Fin 2) Q Γ t K) (repQ outQ : Q → Bool) :
    LocalStep (Fin 2) (QL Q) Γ t K where
  next := fun p a ws =>
    (((L0.next p.1 a ws).1, ansNext repQ outQ a p.2.1 (L0.next p.1 a ws).1,
      startNext a p.2.2), (L0.next p.1 a ws).2)
  disp_le := fun p a ws j => L0.disp_le p.1 a ws j

/-- The tape effect of the latched step is literally that of the core step. -/
theorem latchL_tapes (L0 : LocalStep (Fin 2) Q Γ t K) (blank : Γ) (repQ outQ : Q → Bool)
    (y : QL Q × (Fin t → STape Γ)) (a : Option (Fin 2)) :
    ((latchL L0 repQ outQ).apply blank y a).2 = (L0.apply blank (y.1.1, y.2) a).2 := rfl

/-- The core component of the latched step is literally the core step. -/
theorem latchL_core (L0 : LocalStep (Fin 2) Q Γ t K) (blank : Γ) (repQ outQ : Q → Bool)
    (y : QL Q × (Fin t → STape Γ)) (a : Option (Fin 2)) :
    ((latchL L0 repQ outQ).apply blank y a).1.1 = (L0.apply blank (y.1.1, y.2) a).1 := rfl

/-! ## 3. The extended encoding -/

/-- The latched encoding: the core encoding, with the two bits read off `LX`. -/
def encL (encC : X → Q × (Fin t → STape Γ)) (x : LX X) : QL Q × (Fin t → STape Γ) :=
  (((encC x.core).1, x.ans, x.started), (encC x.core).2)

@[simp] theorem encL_ans (encC : X → Q × (Fin t → STape Γ)) (x : LX X) :
    (encL encC x).1.2.1 = x.ans := rfl

@[simp] theorem encL_started (encC : X → Q × (Fin t → STape Γ)) (x : LX X) :
    (encL encC x).1.2.2 = x.started := rfl

theorem encL_init (encC : X → Q × (Fin t → STape Γ)) (blank : Γ) (x0 : LX X) (q0 : Q)
    (hC : encC x0.core = (q0, fun _ => STape.blankTape blank)) :
    encL encC x0 = ((q0, x0.ans, x0.started), fun _ => STape.blankTape blank) := by
  unfold encL; rw [hC]

/-! ## 4. `enc_step`, proved -/

/-- **Oracle 1 (tape simulation including the latch), discharged.** If the core
dynamics is simulated by `L0` through `encC`, and the report test and output bit
factor through the core control, then `latchL L0 repQ outQ` simulates the latched
dynamics `stepL S`. -/
theorem encL_step (L0 : LocalStep (Fin 2) Q Γ t K) (blank : Γ) (repQ outQ : Q → Bool)
    (S : LocalSys X) (encC : X → Q × (Fin t → STape Γ))
    (enc_tick : ∀ x : X, encC (S.tickL x) = L0.apply blank (encC x) none)
    (enc_feed : ∀ (a : Fin 2) (x : X), encC (S.feedC a x) = L0.apply blank (encC x) (some a))
    (rep_eq : ∀ x : X, S.repL x = repQ (encC x).1)
    (out_eq : ∀ x : X, S.outL x = outQ (encC x).1)
    (x : LX X) (a : Option (Fin 2)) :
    (latchL L0 repQ outQ).apply blank (encL encC x) a = encL encC (stepL S a x) := by
  cases a with
  | none =>
      have h : encC (S.tickL x.core) = L0.apply blank (encC x.core) none := enc_tick x.core
      have hr : S.repL (S.tickL x.core) = repQ (L0.apply blank (encC x.core) none).1 := by
        rw [rep_eq (S.tickL x.core), h]
      have ho : S.outL (S.tickL x.core) = outQ (L0.apply blank (encC x.core) none).1 := by
        rw [out_eq (S.tickL x.core), h]
      simp only [stepL, latchStep, encL, hr, ho, h]
      rfl
  | some c =>
      have h : encC (S.feedC c x.core) = L0.apply blank (encC x.core) (some c) :=
        enc_feed c x.core
      simp only [stepL, arriveL, encL, h]
      rfl

/-! ## 5. Packaged: oracle 1 removed from `pal_in_peg_of_local_latch` -/

/-- **`PAL ∈ PEG` from a `K`-local core.** Same as
`LocalTrackingLatch.pal_in_peg_of_local_latch`, with the first oracle group
(`L`, `initQ`, `ansQ`, `startQ`, `enc`, `enc_step`, `enc_init`, `enc_ans`,
`enc_started`) replaced by: a core local step `L0`, a core encoding `encC`
simulating `S.tickL` / `S.feedC`, and control-level readings `repQ` / `outQ` of
the report test and the output bit. The latch and the started bit are built
here. -/
theorem pal_in_peg_of_local_core
    [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    (S : LocalSys X) (absS : X → State GalilVM) (Inv : List (Fin 2) → X → Prop) (x0 : LX X)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9)
    (delay : ℕ)
    (H_letter : ∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w)
    (H_first : ∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM)
    -- the `K`-local core
    (L0 : LocalStep (Fin 2) Q Γ t K) (blank : Γ) (q0 : Q) (repQ outQ : Q → Bool)
    (encC : X → Q × (Fin t → STape Γ)) (htape : 0 < t)
    (enc_tick : ∀ x : X, encC (S.tickL x) = L0.apply blank (encC x) none)
    (enc_feed : ∀ (a : Fin 2) (x : X), encC (S.feedC a x) = L0.apply blank (encC x) (some a))
    (rep_eq : ∀ x : X, S.repL x = repQ (encC x).1)
    (out_eq : ∀ x : X, S.outL x = outQ (encC x).1)
    (encC_init : encC x0.core = (q0, fun _ => STape.blankTape blank))
    (x0_started : x0.started = false)
    -- unchanged oracles
    (outL_abs : ∀ x : X, S.outL x = (absS x).ctl.output)
    (rep_sound : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length → (w.length - 1) * nLocalL < s →
      S.repL (micro S w x0 s).core = true →
      ReportPoint w (stAbs S absS w x0 s) ∧
        Refreshed (Pof w) (qof w) (firstOf w) (stAbs S absS w x0 s))
    (rep_complete : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length →
      ReportPoint w (stAbs S absS w x0 s) →
      Refreshed (Pof w) (qof w) (firstOf w) (stAbs S absS w x0 s) →
      ∃ s', s' ≤ s ∧ (w.length - 1) * nLocalL + 1 < s' ∧ S.repL (micro S w x0 s').core = true)
    (x0_inv : ∀ w, Inv w x0.core)
    (x0_ctl : (absS x0.core).ctl = GalilScaffoldController.initial delay)
    (inv_tick : ∀ w x, Inv w x → Inv w (S.tickL x))
    (inv_feed : ∀ w a x, Inv w x → Inv w (S.feedC a x))
    (stutter_of_starved : ∀ w x, Inv w x → S.Starved x → absS (S.tickL x) = absS x)
    (tick_of_not_starved : ∀ w x, Inv w x → ¬ S.Starved x →
      Tick (galilFrameS (Pof w) (qof w) (firstOf w)) delay (absS x) (absS (S.tickL x)))
    (feed_abs : ∀ w a x, Inv w x → absS (S.feedC a x) = arriveState' a (absS x))
    (H_ledger : LedgerObligation Pof qof firstOf (fun w => stAbs S absS w x0)
      (fun w => w.length * nLocalL)) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_of_local_latch S absS Inv x0 Pof qof firstOf delay H_letter H_first
    (latchL L0 repQ outQ) blank (q0, x0.ans, x0.started)
    (fun p => p.2.1) (fun p => p.2.2) (encL encC) htape
    (encL_step L0 blank repQ outQ S encC enc_tick enc_feed rep_eq out_eq)
    (encL_init encC blank x0 q0 encC_init)
    (fun _ => rfl) (fun _ => rfl) x0_started outL_abs rep_sound rep_complete
    x0_inv x0_ctl inv_tick inv_feed stutter_of_starved tick_of_not_starved feed_abs H_ledger

#print axioms latchL_tapes
#print axioms latchL_core
#print axioms encL_init
#print axioms encL_step
#print axioms pal_in_peg_of_local_core

end PalPeg.LocalLatchRealize
