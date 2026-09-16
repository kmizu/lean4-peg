import PalPeg.LocalStepRealize
import PalPeg.LocalTracking
import PalPeg.GalilRealizeOfTracking
import PalPeg.GalilScaffoldController

/-!
# The empty word, and how the realized machine accepts it

`PalPeg.GalilRealizeOfTracking.pal_in_peg_of_tracking` needs, besides
`Tracking`, the separate obligation `M.SAccepts []` — because `[] ∈ PAL`.
With the machine of `PalPeg.LocalTracking.tracking_of_oracles`, namely
`M = L.realize blank initQ outQ nLocal …`, this obligation is **false**:

* `realize_SAccepts` at `w = []` reduces `M.SAccepts []` to
  `outQ (initQ, blanks).1 = true`, i.e. `outQ initQ = true`;
* `enc_init` gives `initQ = (enc x0).1`, `enc_output` gives
  `outQ (enc x0).1 = x0.ctl.output`, and `x0_ctl` (`O6`) pins `x0.ctl` to
  `GalilScaffoldController.initial delayS`, whose `output` field is `false`
  (`initial_output_false`).

So `M.SAccepts []` unfolds to `false = true`.

The repair does not touch any existing file: it changes only the *accept
predicate* handed to `realize`, from `outQ` to

  `accept' initQ outQ q := outQ q || decide (q = initQ)`,

which is legal because `realize` already demands `[DecidableEq Q']`.  Then

* `realize_accept'_nil` — the empty word is accepted outright, since the run on
  `[]` ends in `initQ`;
* `realize_accept'_pos` — on a word whose run does **not** end in `initQ` the
  extra disjunct is inert, so the machine's language agrees with `outQ` exactly
  as before, which is what `tracking_of_oracles` needs.

The side condition of `realize_accept'_pos` is discharged by the *mode*
argument (`hne_of_run`): `x0` carries mode `.init` (`O6`), `Tick.init` is the
only tick out of `.init` and it moves to `.scan` (`tick_from_init`), and no tick
ever enters `.init` (`mode_never_init_again`, from `tick_mode` and
`GalilScaffoldController.no_step_to_init`).  Hence a run containing **at least
one** abstract tick cannot end in mode `.init`, so its encoded state differs
from `initQ`.

## Gaps

1. `hne_of_run` needs a *positive-length* abstract run for every nonempty input
   (`hrun_pos` below).  `PalPeg.LocalTracking.steps_run` only produces
   `∃ k, StepsAll … k …` with `k` possibly `0` (every local tick may stutter),
   so the positivity is an extra hypothesis here.  It is exactly what `O2`
   (`tickL_progress`, unused in `LocalTracking`) is meant to deliver, and it is
   implied by `O5` in spirit but not in letter: `ReportPoint` has no `mode`
   field, so it cannot rule out `mode = .init` by itself.
2. `modeQ` — the projection of the finite control `Q'` onto the controller mode
   — is **not** available from `LocalTracking`'s interface (`enc` exposes only
   `enc_output`).  It is therefore taken as a parameter together with
   `enc_mode : ∀ x, modeQ (enc x).1 = x.ctl.mode`, the mode analogue of
   `enc_output`.
3. Nothing here reproves `Tracking`; `realize_accept'_pos` is stated about the
   fold `w.foldl (L.applyN blank n) (initQ, blanks)`, which is the exact right
   hand side of `realize_SAccepts`, so it composes with
   `tracking_of_oracles`'s final `rw` chain without further glue.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PalPeg.GalilEmptyWord

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation
open PalPeg.LocalState (GalilVML absState)
open PalPeg.Local (LocalStep)
open PalPeg.LocalTracking (feed runW nLocal nLocal_pos foldl_enc delayS)

/-! ## (a) The initial controller does not accept -/

/-- **(a)** `Control.initial(timing)` has `output = false`: the Scala scaffold
starts with the output flag cleared. -/
theorem initial_output_false (delay : ℕ) :
    (GalilScaffoldController.initial delay).output = false := rfl

/-- The initial controller is in mode `.init`. -/
theorem initial_mode (delay : ℕ) :
    (GalilScaffoldController.initial delay).mode = Mode.init := rfl

/-! ## The repaired accept predicate -/

/-- The accept predicate of the realized machine, repaired for the empty word:
the controller's `output` bit, *or* the initial control state (which is where
the run on `[]` stops).  Decidability of `=` on the finite control is already a
hypothesis of `PalPeg.Local.LocalStep.realize`. -/
def accept' {Q' : Type} [DecidableEq Q'] (initQ : Q') (outQ : Q' → Bool) : Q' → Bool :=
  fun q => outQ q || decide (q = initQ)

@[simp] theorem accept'_self {Q' : Type} [DecidableEq Q'] (initQ : Q') (outQ : Q' → Bool) :
    accept' initQ outQ initQ = true := by
  simp [accept']

theorem accept'_of_ne {Q' : Type} [DecidableEq Q'] (initQ : Q') (outQ : Q' → Bool)
    {q : Q'} (hq : q ≠ initQ) : accept' initQ outQ q = outQ q := by
  simp [accept', hq]

/-! ## (b) The empty word is accepted -/

/-- **(b)** With `accept'` the realized machine accepts the empty word.
(`StructuredMachine.SAccepts` is a `Prop`, so the statement is the proposition
itself rather than a `Bool` equation.) -/
theorem realize_accept'_nil {Q' Γ' : Type} {t K : ℕ}
    [Fintype Q'] [DecidableEq Q'] [Fintype Γ'] [DecidableEq Γ']
    (L : LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q') (outQ : Q' → Bool)
    (n : ℕ) (htape : 0 < t) (hn : 0 < n) :
    (L.realize blank initQ (accept' initQ outQ) n htape hn).SAccepts [] := by
  rw [LocalStep.realize_SAccepts L blank initQ (accept' initQ outQ) n htape hn []]
  simp

/-! ## (c) On nonempty words the repair is inert -/

/-- **(c)** If the run on `w` does not end in the initial control state, the
extra disjunct of `accept'` is inert and the machine's language is read off
`outQ`, exactly as with the unrepaired accept predicate. -/
theorem realize_accept'_pos {Q' Γ' : Type} {t K : ℕ}
    [Fintype Q'] [DecidableEq Q'] [Fintype Γ'] [DecidableEq Γ']
    (L : LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q') (outQ : Q' → Bool)
    (n : ℕ) (htape : 0 < t) (hn : 0 < n) (w : List (Fin 2)) (hw : 0 < w.length)
    (hne : (w.foldl (L.applyN blank n)
        (initQ, fun _ => STape.blankTape blank)).1 ≠ initQ) :
    ((L.realize blank initQ (accept' initQ outQ) n htape hn).SAccepts w ↔
      outQ (w.foldl (L.applyN blank n) (initQ, fun _ => STape.blankTape blank)).1 = true) := by
  rw [LocalStep.realize_SAccepts L blank initQ (accept' initQ outQ) n htape hn w,
    accept'_of_ne initQ outQ hne]

/-! ## (d) The mode argument: runs of positive length never end in `.init` -/

/-- The only tick out of mode `.init` is `Tick.init`, and it lands in `.scan`. -/
theorem tick_from_init {σ : Type} {F : Frame σ} {delay : ℕ} {x y : State σ}
    (h : Tick F delay x y) (hx : x.ctl.mode = Mode.init) : y.ctl.mode = Mode.scan := by
  cases h <;> simp_all

/-- No tick ever enters mode `.init` (`tick_mode` plus `no_step_to_init`). -/
theorem mode_never_init_again {σ : Type} {F : Frame σ} {delay : ℕ} {x y : State σ}
    (h : Tick F delay x y) (hy : y.ctl.mode = Mode.init) : x.ctl.mode = Mode.init := by
  rcases tick_mode F delay h with h' | h'
  · rw [← h']; exact hy
  · exact absurd (hy ▸ h') (no_step_to_init _)

/-- Mode `.init` is never re-entered along a whole run. -/
theorem steps_ne_init {σ : Type} {F : Frame σ} {delay : ℕ} {Q : State σ → Prop} {k : ℕ}
    {x z : State σ} (h : StepsAll F delay Q k x z) (hx : x.ctl.mode ≠ Mode.init) :
    z.ctl.mode ≠ Mode.init := by
  induction h with
  | zero _ _ => exact hx
  | succ _ hstep _ ih =>
      exact ih (fun hy => hx (mode_never_init_again hstep hy))

/-- **The mode fact.** A run of *positive* length out of mode `.init` cannot end
in mode `.init`. -/
theorem steps_pos_ne_init {σ : Type} {F : Frame σ} {delay : ℕ} {Q : State σ → Prop} {k : ℕ}
    {x z : State σ} (hk : 0 < k) (h : StepsAll F delay Q k x z)
    (hx : x.ctl.mode = Mode.init) : z.ctl.mode ≠ Mode.init := by
  cases h with
  | zero _ _ => omega
  | succ _ hstep hrest =>
      refine steps_ne_init hrest ?_
      rw [tick_from_init hstep hx]
      decide

/-- **(d)** The side condition of `realize_accept'_pos`, from the oracles.

`O6` (`x0_ctl`) puts the initial local state in mode `.init`; `hrun_pos` gives,
for a nonempty input, an abstract run of positive length (see Gap 1); the mode
fact then says the final abstract state is not in mode `.init`, and `enc_mode`
(see Gap 2) transports that back to the finite control, where `enc_init`
identifies `initQ` with `(enc x0).1`. -/
theorem hne_of_run
    {Np t K : ℕ} {Q' Γ' : Type} [Fintype Q'] [DecidableEq Q'] [Fintype Γ'] [DecidableEq Γ']
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9)
    (tickL : GalilVML Np → GalilVML Np) (x0 : GalilVML Np)
    (L : LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q') (outQ : Q' → Bool)
    (enc : GalilVML Np → Q' × (Fin t → STape Γ')) (modeQ : Q' → Mode)
    -- (O3) the encoding intertwines `LocalStep` with `feed`-then-`tickL`
    (enc_step : ∀ (x : GalilVML Np) (a : Option (Fin 2)),
      L.apply blank (enc x) a = enc (tickL (feed a x)))
    (enc_init : enc x0 = (initQ, fun _ => STape.blankTape blank))
    -- the mode analogue of `enc_output`
    (enc_mode : ∀ x : GalilVML Np, modeQ (enc x).1 = x.ctl.mode)
    -- (O6) the initial local state carries the Scala initial controller
    (x0_ctl : (absState x0).ctl = GalilScaffoldController.initial delayS)
    -- Gap 1: a positive-length abstract run for every nonempty input
    (hrun_pos : ∀ u : List (Fin 2), 0 < u.length →
      ∃ k, 0 < k ∧ StepsAll (galilFrameS (Pof u) (qof u) (firstOf u)) delayS
        (fun _ => True) k (absState x0) (absState (runW tickL nLocal x0 u)))
    (w : List (Fin 2)) (hw : 0 < w.length) :
    (w.foldl (L.applyN blank nLocal)
      (initQ, fun _ => STape.blankTape blank)).1 ≠ initQ := by
  have hx0 : x0.ctl = GalilScaffoldController.initial delayS := x0_ctl
  obtain ⟨k, hk, hrun⟩ := hrun_pos w hw
  have hend : (absState (runW tickL nLocal x0 w)).ctl.mode ≠ Mode.init :=
    steps_pos_ne_init hk hrun (by rw [PalPeg.LocalState.absState_ctl, hx0]; rfl)
  have hfold : w.foldl (L.applyN blank nLocal) (initQ, fun _ => STape.blankTape blank)
      = enc (runW tickL nLocal x0 w) := by
    rw [← enc_init, foldl_enc L blank nLocal nLocal_pos tickL enc enc_step w x0]
  intro hcon
  apply hend
  have hinit : initQ = (enc x0).1 := by rw [enc_init]
  rw [PalPeg.LocalState.absState_ctl, ← enc_mode (runW tickL nLocal x0 w), ← hfold, hcon,
    hinit, enc_mode x0, hx0]
  rfl

/-- **(c) + (d) packaged.** Under the oracles, the repaired machine's language
on nonempty words is still read off `outQ` at the encoded final state — the
statement `PalPeg.LocalTracking.tracking_of_oracles` consumes — while
`realize_accept'_nil` supplies the empty-word obligation. -/
theorem realize_accept'_pos_of_oracles
    {Np t K : ℕ} {Q' Γ' : Type} [Fintype Q'] [DecidableEq Q'] [Fintype Γ'] [DecidableEq Γ']
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9)
    (tickL : GalilVML Np → GalilVML Np) (x0 : GalilVML Np)
    (L : LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q') (outQ : Q' → Bool)
    (enc : GalilVML Np → Q' × (Fin t → STape Γ')) (modeQ : Q' → Mode) (htape : 0 < t)
    (enc_step : ∀ (x : GalilVML Np) (a : Option (Fin 2)),
      L.apply blank (enc x) a = enc (tickL (feed a x)))
    (enc_init : enc x0 = (initQ, fun _ => STape.blankTape blank))
    (enc_output : ∀ x : GalilVML Np, outQ (enc x).1 = x.ctl.output)
    (enc_mode : ∀ x : GalilVML Np, modeQ (enc x).1 = x.ctl.mode)
    (x0_ctl : (absState x0).ctl = GalilScaffoldController.initial delayS)
    (hrun_pos : ∀ u : List (Fin 2), 0 < u.length →
      ∃ k, 0 < k ∧ StepsAll (galilFrameS (Pof u) (qof u) (firstOf u)) delayS
        (fun _ => True) k (absState x0) (absState (runW tickL nLocal x0 u)))
    (w : List (Fin 2)) (hw : 0 < w.length) :
    ((L.realize blank initQ (accept' initQ outQ) nLocal htape nLocal_pos).SAccepts w ↔
      (absState (runW tickL nLocal x0 w)).ctl.output = true) := by
  have hne := hne_of_run Pof qof firstOf tickL x0 L blank initQ outQ enc modeQ
    enc_step enc_init enc_mode x0_ctl hrun_pos w hw
  rw [realize_accept'_pos L blank initQ outQ nLocal htape nLocal_pos w hw hne]
  have hfold : w.foldl (L.applyN blank nLocal) (initQ, fun _ => STape.blankTape blank)
      = enc (runW tickL nLocal x0 w) := by
    rw [← enc_init, foldl_enc L blank nLocal nLocal_pos tickL enc enc_step w x0]
  rw [hfold, enc_output, PalPeg.LocalState.absState_ctl]

end PalPeg.GalilEmptyWord

/-! ## Axiom audit -/

#print axioms PalPeg.GalilEmptyWord.initial_output_false
#print axioms PalPeg.GalilEmptyWord.realize_accept'_nil
#print axioms PalPeg.GalilEmptyWord.realize_accept'_pos
#print axioms PalPeg.GalilEmptyWord.tick_from_init
#print axioms PalPeg.GalilEmptyWord.mode_never_init_again
#print axioms PalPeg.GalilEmptyWord.steps_ne_init
#print axioms PalPeg.GalilEmptyWord.steps_pos_ne_init
#print axioms PalPeg.GalilEmptyWord.hne_of_run
#print axioms PalPeg.GalilEmptyWord.realize_accept'_pos_of_oracles
