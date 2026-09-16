import PalPeg.LocalStepRealize
import PalPeg.LocalState
import PalPeg.GalilStructuredSkeleton
import PalPeg.GalilScaffoldTopOutputTrace

/-!
# Top-down skeleton of the *tracking* theorem for the local layer

`PalPeg.GalilStructuredSkeleton.pal_in_peg_of_galil'` reduces `PAL ∈ PEG` to two
obligations, of which `H_realize` — "the machine's accept flag agrees with the
scaffold controller's `output` at a report point of a scaffold run" — is the one
the *machine side* has to deliver.  `PalPeg.GalilRealizeOfTracking` turns a
single **tracking** statement into `H_realize`.

This file is the top-down skeleton of that tracking statement *for the local
layer* (`PalPeg.LocalState.GalilVML`, realized by `PalPeg.Local.LocalStep`).
Everything the local layer has not yet been given is isolated into named
**oracle hypotheses** `O1`–`O6` of `tracking_of_oracles`; what the file actually
proves is the bookkeeping that glues them:

* stutter-dropping: `O1` turns `n` local ticks into a `StepsAll` chain of
  abstract `Tick`s of `galilFrameS` (a local tick that does not move `absState`
  simply contributes no abstract step);
* the fold: `O3` turns `PalPeg.Local.LocalStep.applyN` — the `n`-local-steps-per
  -input-symbol shape that `realize_srun` produces — into `n` iterations of
  `tickL` after one `feed`;
* acceptance: `realize_SAccepts` plus `O3`'s output read-off pins the realized
  machine's language to the controller's `output` at the final state.

## The clock model behind `n`

`n := 2 * 2048` local steps are executed per input symbol: the scaffold's match
delay is `delay = 2048` abstract ticks per *place* (half-step) of the right
head, and there are two places per letter (`gap = true`, then `gap = false`).
`O5` (`report_at_end`) is exactly the timing fact that after `n * |w|` local
steps the right head sits on the *last letter* of `w`; it is left as an oracle
because it is a statement about that clock model — one place per `2048` abstract
ticks, and no stuttering beyond the budget of `O2`.

## Gaps (what this skeleton does *not* discharge)

1. **`O4` is inconsistent with `O4b` under the present abstract model.**
   `GalilScaffoldTop.Tick` never *grows* any head's `incoming` FIFO — the
   `compare` phase only ever pops from it (`pops_incoming_right`).  So the left
   disjunct of `O4b` is unavailable for an arrival, which forces
   `absState (feed (some a) x) = absState x`; together with `O4` that means
   `arriveVM a s = s`, which is false as stated.  The resolution is a design
   decision that has to be taken in the local layer, not here: either the whole
   input is *pre-loaded* in the abstract `incoming` (`x0.pending = w`, and
   `feed` is abstraction-invisible, which is what `O4b`'s right disjunct says),
   or `Tick` is extended with an arrival rule.  `O4` is therefore stated but
   deliberately **unused**; only `O4b` drives the induction.
2. **`O2` (`tickL_progress`) is stated but unused here.**  It is the budget that
   `O5` has to be proved from; without it `O5` is the whole timing argument.
3. **`O5` (`report_at_end`) is the timing fact itself** — that after
   `nLocal * |w|` local steps the right head stands on the last letter of `w`,
   the controller is in scan mode and not replaying, and the output is
   refreshed.  It is the largest remaining obligation of the local layer.
4. `tickL`, `InvL`, `enc`, `L`, `x0` are *hypotheses*: no local step function
   for the Galil scaffold is constructed here.  `PalPeg.LocalState.StepLocal`
   and `PalPeg.Local.LocalStep` are the two ends that `O3` must bridge.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PalPeg.LocalTracking

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.LocalState (GalilVML absState)
open PalPeg.Local (LocalStep)

/-! ## 1. Arrival, abstractly and locally -/

/-- One arrival at the **abstract** level: `a` is appended to the `incoming`
FIFO of every input head.  (The walker places of `GalilVM` carry no FIFO.) -/
def arriveVM (a : Fin 2) (s : GalilVM) : GalilVM :=
  { s with
    left := ⟨{ s.left.head with incoming := s.left.head.incoming ++ [a] }, s.left.gap⟩,
    center := ⟨{ s.center.head with incoming := s.center.head.incoming ++ [a] }, s.center.gap⟩,
    right := ⟨{ s.right.head with incoming := s.right.head.incoming ++ [a] }, s.right.gap⟩ }

/-- One arrival at the abstract level, on a whole scaffold state. -/
def arriveState (a : Fin 2) (st : State GalilVM) : State GalilVM := ⟨st.ctl, arriveVM a st.vm⟩

/-- One arrival at the **local** level: `LocalInputView.arrive` on all five
cursors (cf. `PalPeg.LocalState.stepLocal_arrive`, which shows this is a
`StepLocal` step, i.e. realizable by a bounded-radius local step). -/
def feedL {Np : ℕ} (a : Fin 2) (x : GalilVML Np) : GalilVML Np :=
  { x with
    left := LocalInputView.arrive a x.left,
    center := LocalInputView.arrive a x.center,
    right := LocalInputView.arrive a x.right,
    walkerView := LocalInputView.arrive a x.walkerView,
    fppWalker := LocalInputView.arrive a x.fppWalker }

/-- `feed` is what one micro-step of the realized machine does with its input
slot: deliver the letter if there is one, do nothing otherwise. -/
def feed {Np : ℕ} : Option (Fin 2) → GalilVML Np → GalilVML Np
  | none, x => x
  | some a, x => feedL a x

@[simp] theorem feed_none {Np : ℕ} (x : GalilVML Np) : feed none x = x := rfl

@[simp] theorem feed_some {Np : ℕ} (a : Fin 2) (x : GalilVML Np) :
    feed (some a) x = feedL a x := rfl

/-- The scaffold's match delay, in abstract ticks per place. -/
def delayS : ℕ := 2048

/-- **Local steps per input symbol**: `2` places per letter, `delayS` abstract
ticks per place. -/
def nLocal : ℕ := 2 * delayS

theorem nLocal_pos : 0 < nLocal := by decide

/-- One input symbol's worth of local work: deliver the letter, then run
`n` local ticks. -/
def stepW {Np : ℕ} (tickL : GalilVML Np → GalilVML Np) (n : ℕ)
    (x : GalilVML Np) (a : Fin 2) : GalilVML Np := tickL^[n] (feed (some a) x)

/-- The local state after reading the whole word. -/
def runW {Np : ℕ} (tickL : GalilVML Np → GalilVML Np) (n : ℕ)
    (x0 : GalilVML Np) (w : List (Fin 2)) : GalilVML Np := w.foldl (stepW tickL n) x0

/-! ## 2. Stutter-dropping: local ticks give an abstract `StepsAll` run -/

/-- One local transition contributes at most one abstract tick (`O1`, `O4b`). -/
theorem steps_one {Np : ℕ} (Pw : Shared) (qq : ℕ) (first : Fin 9)
    (f : GalilVML Np → GalilVML Np) (Inv : GalilVML Np → Prop)
    (habs : ∀ x : GalilVML Np, Inv x →
      Tick (galilFrameS Pw qq first) delayS (absState x) (absState (f x)) ∨
        absState (f x) = absState x)
    (x : GalilVML Np) (hx : Inv x) {k : ℕ} {z : State GalilVM}
    (hrest : StepsAll (galilFrameS Pw qq first) delayS (fun _ => True) k
      (absState (f x)) z) :
    ∃ k', StepsAll (galilFrameS Pw qq first) delayS (fun _ => True) k' (absState x) z := by
  rcases habs x hx with h | h
  · exact ⟨k + 1, StepsAll.succ trivial h hrest⟩
  · refine ⟨k, ?_⟩
    rw [← h]
    exact hrest

/-- `m` local ticks give an abstract run (`O1`, by induction; stutters drop). -/
theorem steps_iterate {Np : ℕ} (Pw : Shared) (qq : ℕ) (first : Fin 9)
    (tickL : GalilVML Np → GalilVML Np) (Inv : GalilVML Np → Prop)
    (habs : ∀ x : GalilVML Np, Inv x →
      Tick (galilFrameS Pw qq first) delayS (absState x) (absState (tickL x)) ∨
        absState (tickL x) = absState x)
    (hinv : ∀ x : GalilVML Np, Inv x → Inv (tickL x)) :
    ∀ (m : ℕ) (x : GalilVML Np), Inv x →
      Inv (tickL^[m] x) ∧
      ∃ k, StepsAll (galilFrameS Pw qq first) delayS (fun _ => True) k
        (absState x) (absState (tickL^[m] x)) := by
  intro m
  induction m with
  | zero => intro x hx; exact ⟨hx, 0, StepsAll.zero _ trivial⟩
  | succ m ih =>
      intro x hx
      obtain ⟨hi, k, hk⟩ := ih (tickL x) (hinv x hx)
      rw [Function.iterate_succ_apply]
      exact ⟨hi, steps_one Pw qq first tickL Inv habs x hx hk⟩

/-- The whole word gives an abstract run (`O1` + the arrival oracle `O4b`). -/
theorem steps_run {Np : ℕ} (Pw : Shared) (qq : ℕ) (first : Fin 9)
    (tickL : GalilVML Np → GalilVML Np) (Inv : GalilVML Np → Prop) (n : ℕ)
    (habs : ∀ x : GalilVML Np, Inv x →
      Tick (galilFrameS Pw qq first) delayS (absState x) (absState (tickL x)) ∨
        absState (tickL x) = absState x)
    (hinv : ∀ x : GalilVML Np, Inv x → Inv (tickL x))
    (hfabs : ∀ (a : Fin 2) (x : GalilVML Np), Inv x →
      Tick (galilFrameS Pw qq first) delayS (absState x) (absState (feed (some a) x)) ∨
        absState (feed (some a) x) = absState x)
    (hfinv : ∀ (a : Fin 2) (x : GalilVML Np), Inv x → Inv (feed (some a) x)) :
    ∀ (w : List (Fin 2)) (x : GalilVML Np), Inv x →
      Inv (runW tickL n x w) ∧
      ∃ k, StepsAll (galilFrameS Pw qq first) delayS (fun _ => True) k
        (absState x) (absState (runW tickL n x w)) := by
  intro w
  induction w with
  | nil => intro x hx; exact ⟨hx, 0, StepsAll.zero _ trivial⟩
  | cons a rest ih =>
      intro x hx
      have hfx : Inv (feed (some a) x) := hfinv a x hx
      obtain ⟨hit, kt, ht⟩ := steps_iterate Pw qq first tickL Inv habs hinv n _ hfx
      obtain ⟨hr, kr, hrr⟩ := ih _ hit
      refine ⟨by simpa [runW, stepW] using hr, ?_⟩
      have hchain :
          StepsAll (galilFrameS Pw qq first) delayS (fun _ => True) (kt + kr)
            (absState (feed (some a) x)) (absState (runW tickL n (tickL^[n] (feed (some a) x)) rest)) :=
        stepsAll_trans ht hrr
      have := steps_one Pw qq first (feed (some a)) Inv
        (fun y hy => hfabs a y hy) x hx (k := kt + kr) hchain
      simpa [runW, stepW] using this

/-! ## 3. The fold: `applyN` of the realized machine is `feed` then `tickL^[n]` -/

section Enc

variable {Np t K : ℕ} {Q' Γ' : Type}

/-- Input-free local steps track `tickL` (`O3` at `none`). -/
theorem iter_none (L : LocalStep (Fin 2) Q' Γ' t K) (blank : Γ')
    (tickL : GalilVML Np → GalilVML Np) (enc : GalilVML Np → Q' × (Fin t → STape Γ'))
    (hsim : ∀ (x : GalilVML Np) (a : Option (Fin 2)),
      L.apply blank (enc x) a = enc (tickL (feed a x))) :
    ∀ (m : ℕ) (y : GalilVML Np),
      (fun z => L.apply blank z none)^[m] (enc y) = enc (tickL^[m] y) := by
  intro m
  induction m with
  | zero => intro y; rfl
  | succ m ih =>
      intro y
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      have h : L.apply blank (enc y) none = enc (tickL y) := by
        rw [hsim y none, feed_none]
      rw [h, ih (tickL y)]

/-- One input symbol of the realized machine is `feed` followed by `n` local
ticks (`O3`). -/
theorem applyN_enc (L : LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (n : ℕ) (hn : 0 < n)
    (tickL : GalilVML Np → GalilVML Np) (enc : GalilVML Np → Q' × (Fin t → STape Γ'))
    (hsim : ∀ (x : GalilVML Np) (a : Option (Fin 2)),
      L.apply blank (enc x) a = enc (tickL (feed a x)))
    (x : GalilVML Np) (a : Fin 2) :
    L.applyN blank n (enc x) a = enc (stepW tickL n x a) := by
  have hstep : L.apply blank (enc x) (some a) = enc (tickL (feed (some a) x)) := hsim x (some a)
  have : L.applyN blank n (enc x) a
      = (fun z => L.apply blank z none)^[n - 1] (enc (tickL (feed (some a) x))) := by
    rw [LocalStep.applyN, hstep]
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [this, iter_none L blank tickL enc hsim (n - 1) (tickL (feed (some a) x)),
    ← Function.iterate_succ_apply]
  show enc (tickL^[n - 1 + 1] (feed (some a) x)) = enc (stepW tickL n x a)
  rw [hn1]
  rfl

/-- The whole word (`O3`, by induction). -/
theorem foldl_enc (L : LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (n : ℕ) (hn : 0 < n)
    (tickL : GalilVML Np → GalilVML Np) (enc : GalilVML Np → Q' × (Fin t → STape Γ'))
    (hsim : ∀ (x : GalilVML Np) (a : Option (Fin 2)),
      L.apply blank (enc x) a = enc (tickL (feed a x))) :
    ∀ (w : List (Fin 2)) (x : GalilVML Np),
      w.foldl (L.applyN blank n) (enc x) = enc (runW tickL n x w) := by
  intro w
  induction w with
  | nil => intro x; rfl
  | cons a rest ih =>
      intro x
      rw [List.foldl_cons, applyN_enc L blank n hn tickL enc hsim x a, ih (stepW tickL n x a)]
      rfl

end Enc

/-! ## 4. The tracking theorem -/

/-- **The tracking theorem from the oracles.**

The conclusion is exactly the body of `PalPeg.GalilRealizeOfTracking.Tracking`
at the word `w` — the hypothesis that `H_realize_of_tracking` consumes.  It is
stated inline so that this file does not depend on that one.

The oracles are, in the order of the module docstring:

* `O1` = `tickL_abs` + `invL_tickL`: one local tick is one abstract tick, or a
  stutter, and the local invariant is preserved;
* `O2` = `tickL_progress`: the stutter bound (at most `delayS` local ticks
  without an abstract tick).  It is *not used here*; it is what `O5` must be
  proved from;
* `O3` = `enc_step` + `enc_init` + `enc_output`: the encoding of the local state
  into the finite control and the `t` structured tapes intertwines `LocalStep`
  with `feed`-then-`tickL`, starts on blank tapes, and exposes the controller's
  `output` bit;
* `O4` = `abs_feed`: the abstract effect of one arrival.  Also *not used here*
  (see the `Gaps` section below);
* `O4b` = `feed_abs` + `invL_feed`: what the induction actually needs from an
  arrival — that it is an abstract tick or invisible;
* `O5` = `report_at_end`: the timing fact;
* `O6` = `x0_ctl`: the initial state carries the Scala initial controller. -/
theorem tracking_of_oracles
    {Np t K : ℕ} {Q' Γ' : Type} [Fintype Q'] [DecidableEq Q'] [Fintype Γ'] [DecidableEq Γ']
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9)
    (tickL : GalilVML Np → GalilVML Np) (InvL : List (Fin 2) → GalilVML Np → Prop)
    (x0 : GalilVML Np)
    (L : LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q') (outQ : Q' → Bool)
    (enc : GalilVML Np → Q' × (Fin t → STape Γ')) (htape : 0 < t)
    -- (O1) one local tick is one abstract tick of `galilFrameS`, or a stutter
    (tickL_abs : ∀ (u : List (Fin 2)) (x : GalilVML Np), InvL u x →
      Tick (galilFrameS (Pof u) (qof u) (firstOf u)) delayS
        (absState x) (absState (tickL x)) ∨ absState (tickL x) = absState x)
    (invL_tickL : ∀ (u : List (Fin 2)) (x : GalilVML Np), InvL u x → InvL u (tickL x))
    -- (O2) progress: no more than `delayS` local ticks without an abstract tick
    (tickL_progress : ∀ (u : List (Fin 2)) (x : GalilVML Np), InvL u x →
      ∃ j, j ≤ delayS ∧
        Tick (galilFrameS (Pof u) (qof u) (firstOf u)) delayS
          (absState x) (absState (tickL^[j] x)))
    -- (O3) the encoding intertwines `LocalStep` with `feed`-then-`tickL`
    (enc_step : ∀ (x : GalilVML Np) (a : Option (Fin 2)),
      L.apply blank (enc x) a = enc (tickL (feed a x)))
    (enc_init : enc x0 = (initQ, fun _ => STape.blankTape blank))
    (enc_output : ∀ x : GalilVML Np, outQ (enc x).1 = x.ctl.output)
    -- (O4) arrival semantics at the abstract level
    (abs_feed : ∀ (u : List (Fin 2)) (a : Fin 2) (x : GalilVML Np), InvL u x →
      absState (feed (some a) x) = arriveState a (absState x))
    -- (O4b) what the induction needs of an arrival
    (feed_abs : ∀ (u : List (Fin 2)) (a : Fin 2) (x : GalilVML Np), InvL u x →
      Tick (galilFrameS (Pof u) (qof u) (firstOf u)) delayS
        (absState x) (absState (feed (some a) x)) ∨ absState (feed (some a) x) = absState x)
    (invL_feed : ∀ (u : List (Fin 2)) (a : Fin 2) (x : GalilVML Np), InvL u x →
      InvL u (feed (some a) x))
    (invL_x0 : ∀ u : List (Fin 2), InvL u x0)
    -- (O5) timing: after `nLocal * |u|` local steps the run is at a refreshed report point
    (report_at_end : ∀ u : List (Fin 2), 0 < u.length →
      ReportPoint u (absState (runW tickL nLocal x0 u)) ∧
        Refreshed (Pof u) (qof u) (firstOf u) (absState (runW tickL nLocal x0 u)))
    -- (O6) the initial local state carries the Scala initial controller
    (x0_ctl : (absState x0).ctl = GalilScaffoldController.initial delayS)
    (w : List (Fin 2)) (hw : 0 < w.length) :
    ∃ y0 : State GalilVM,
      ScaffoldRun Pof qof firstOf delayS w y0 ∧
      ReportPoint w y0 ∧
      Refreshed (Pof w) (qof w) (firstOf w) y0 ∧
      ((L.realize blank initQ outQ nLocal htape nLocal_pos).SAccepts w ↔ y0.ctl.output = true) := by
  refine ⟨absState (runW tickL nLocal x0 w), ?_, (report_at_end w hw).1, (report_at_end w hw).2, ?_⟩
  · obtain ⟨_, k, hk⟩ :=
      steps_run (Pof w) (qof w) (firstOf w) tickL (InvL w) nLocal
        (tickL_abs w) (invL_tickL w) (fun a x hx => feed_abs w a x hx)
        (fun a x hx => invL_feed w a x hx) w x0 (invL_x0 w)
    exact ⟨k, absState x0, x0_ctl, hk⟩
  · rw [LocalStep.realize_SAccepts L blank initQ outQ nLocal htape nLocal_pos w, ← enc_init,
      foldl_enc L blank nLocal nLocal_pos tickL enc enc_step w x0, enc_output]
    exact Iff.rfl

#print axioms steps_one
#print axioms steps_iterate
#print axioms steps_run
#print axioms iter_none
#print axioms applyN_enc
#print axioms foldl_enc
#print axioms tracking_of_oracles

end PalPeg.LocalTracking
