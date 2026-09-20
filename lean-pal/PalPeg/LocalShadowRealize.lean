import PalPeg.LocalLatchRealize

/-!
# A physical machine that shadows an abstract local system

`LocalLatchRealize.pal_in_peg_of_local_core` asks for an encoding `encC` of the local state with
`encC (S.tickL x) = L0.apply blank (encC x) none` on *every* state.  A physical machine follows an
abstract local system only up to a representation relation (`sweep` leaves junk, the bottom of a
stack is not determined by the tape), so no function from abstract states to physical states
satisfies that equation.

Here the local state is the pair *abstract state, physical state*, run in lockstep.  The encoding
is the second projection, so the equations of the consumer hold by definition.  What remains of
the physical machine is its specification: the representation relation holds initially, is kept
by a tick and by a feed on invariant states, and the two control readings agree with the
abstract ones on represented states.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PalPeg.LocalShadowRealize

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.Local (LocalStep)
open PalPeg.LocalTrackingLatch PalPeg.LocalLatchRealize

variable {A Q Γ : Type} {t K : ℕ}

/-- The abstract system and the physical machine in lockstep.  The report test and the output
bit are read from the physical control. -/
def shadowSys (S : LocalSys A) (L0 : LocalStep (Fin 2) Q Γ t K) (blank : Γ)
    (repQ outQ : Q → Bool) : LocalSys (A × (Q × (Fin t → STape Γ))) where
  tickL := fun x => (S.tickL x.1, L0.apply blank x.2 none)
  feedC := fun a x => (S.feedC a x.1, L0.apply blank x.2 (some a))
  repL := fun x => repQ x.2.1
  outL := fun x => outQ x.2.1
  Starved := fun x => S.Starved x.1

/-- The abstraction of a pair: that of the abstract state, with the output bit read from the
physical control. -/
def shadowAbs (absS : A → State GalilVM) (outQ : Q → Bool)
    (x : A × (Q × (Fin t → STape Γ))) : State GalilVM :=
  ⟨{ (absS x.1).ctl with output := outQ x.2.1 }, (absS x.1).vm⟩

theorem shadowAbs_eq (absS : A → State GalilVM) (outQ : Q → Bool)
    (x : A × (Q × (Fin t → STape Γ))) (houtput : outQ x.2.1 = (absS x.1).ctl.output) :
    shadowAbs absS outQ x = absS x.1 := by
  unfold shadowAbs
  rw [houtput]

/-- The initial pair. -/
def shadowInit (x0 : LX A) (q0 : Q) (blank : Γ) : LX (A × (Q × (Fin t → STape Γ))) :=
  ⟨(x0.core, (q0, fun _ => STape.blankTape blank)), x0.ans, x0.started⟩

section Lockstep

variable (S : LocalSys A) (L0 : LocalStep (Fin 2) Q Γ t K) (blank : Γ) (repQ outQ : Q → Bool)
  (Inv : List (Fin 2) → ℕ → A → Prop) (Rep : A → Q × (Fin t → STape Γ) → Prop)

/-- **The lockstep run.**  The abstract half of the run of the pair is the abstract run, with
the same latch and the same started bit, and the physical half represents it. -/
theorem micro_shadow (x0 : LX A) (q0 : Q) (w : List (Fin 2))
    (hrepInit : Rep x0.core (q0, fun _ => STape.blankTape blank))
    (hinvInit : Inv w 0 x0.core)
    (hinvTick : ∀ s a, inp w s = none → Inv w s a → Inv w (s+1) (S.tickL a))
    (hinvFeed : ∀ s letter a, inp w s = some letter → Inv w s a →
      Inv w (s+1) (S.feedC letter a))
    (hsimTick : ∀ s a p, inp w s = none → Inv w s a → Rep a p →
      Rep (S.tickL a) (L0.apply blank p none))
    (hsimFeed : ∀ s letter a p, inp w s = some letter → Inv w s a → Rep a p →
      Rep (S.feedC letter a) (L0.apply blank p (some letter)))
    (hreadRep : ∀ a p, Rep a p → S.repL a = repQ p.1)
    (hreadOut : ∀ a p, Rep a p → S.outL a = outQ p.1) :
    ∀ s, (micro (shadowSys S L0 blank repQ outQ) w (shadowInit x0 q0 blank) s).core.1
          = (micro S w x0 s).core ∧
      (micro (shadowSys S L0 blank repQ outQ) w (shadowInit x0 q0 blank) s).ans
          = (micro S w x0 s).ans ∧
      (micro (shadowSys S L0 blank repQ outQ) w (shadowInit x0 q0 blank) s).started
          = (micro S w x0 s).started ∧
      Inv w s (micro S w x0 s).core ∧
      Rep (micro S w x0 s).core
        (micro (shadowSys S L0 blank repQ outQ) w (shadowInit x0 q0 blank) s).core.2
  | 0 => ⟨rfl, rfl, rfl, hinvInit, hrepInit⟩
  | s + 1 => by
    obtain ⟨hcore, hans, hstarted, hinv, hrep⟩ := micro_shadow x0 q0 w hrepInit hinvInit hinvTick
      hinvFeed hsimTick hsimFeed hreadRep hreadOut s
    show (stepL (shadowSys S L0 blank repQ outQ) (inp w s) _).core.1
        = (stepL S (inp w s) _).core ∧
      (stepL (shadowSys S L0 blank repQ outQ) (inp w s) _).ans = (stepL S (inp w s) _).ans ∧
      (stepL (shadowSys S L0 blank repQ outQ) (inp w s) _).started
        = (stepL S (inp w s) _).started ∧
      Inv w (s+1) (stepL S (inp w s) _).core ∧
      Rep (stepL S (inp w s) _).core
        (stepL (shadowSys S L0 blank repQ outQ) (inp w s) _).core.2
    cases hinput : inp w s with
    | none =>
      have hrepNext := hsimTick s _ _ hinput hinv hrep
      refine ⟨by show S.tickL _ = S.tickL _; rw [hcore], ?_, hstarted,
        hinvTick s _ hinput hinv, ?_⟩
      · show (_ || (repQ (L0.apply blank _ none).1 && outQ (L0.apply blank _ none).1))
          = (_ || (S.repL (S.tickL _) && S.outL (S.tickL _)))
        rw [hans, hreadRep _ _ hrepNext, hreadOut _ _ hrepNext]
      · exact hrepNext
    | some letter =>
      refine ⟨by show S.feedC letter _ = S.feedC letter _; rw [hcore], rfl, rfl,
        hinvFeed s _ _ hinput hinv, hsimFeed s _ _ _ hinput hinv hrep⟩

end Lockstep

/-- **`PAL ∈ PEG` from an abstract local system and a physical machine that shadows it.**  The
hypotheses on the abstract system are those of `pal_in_peg_of_local_core`; the physical machine
enters only through the representation relation `Rep`. -/
theorem pal_in_peg_of_shadowed_core
    [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    (S : LocalSys A) (absS : A → State GalilVM) (Inv : List (Fin 2) → ℕ → A → Prop) (x0 : LX A)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9)
    (delay : ℕ)
    (H_letter : ∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w)
    (H_first : ∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM)
    -- the physical machine and its specification
    (L0 : LocalStep (Fin 2) Q Γ t K) (blank : Γ) (q0 : Q) (repQ outQ : Q → Bool) (htape : 0 < t)
    (Rep : A → Q × (Fin t → STape Γ) → Prop)
    (hrepInit : Rep x0.core (q0, fun _ => STape.blankTape blank))
    (hsimTick : ∀ w s a p, inp w s = none → Inv w s a → Rep a p →
      Rep (S.tickL a) (L0.apply blank p none))
    (hsimFeed : ∀ w s letter a p, inp w s = some letter → Inv w s a → Rep a p →
      Rep (S.feedC letter a) (L0.apply blank p (some letter)))
    (hreadRep : ∀ a p, Rep a p → S.repL a = repQ p.1)
    (hreadOut : ∀ a p, Rep a p → S.outL a = outQ p.1)
    -- the abstract system
    (x0_started : x0.started = false)
    (outL_abs : ∀ a : A, S.outL a = (absS a).ctl.output)
    (rep_sound : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length → (w.length - 1) * nLocalL < s →
      S.repL (micro S w x0 s).core = true →
      ReportPoint w (stAbs S absS w x0 s) ∧
        Refreshed (Pof w) (qof w) (firstOf w) (stAbs S absS w x0 s))
    (rep_complete : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length →
      ReportPoint w (stAbs S absS w x0 s) →
      Refreshed (Pof w) (qof w) (firstOf w) (stAbs S absS w x0 s) →
      ∃ s', s' ≤ s ∧ (w.length - 1) * nLocalL + 1 < s' ∧ S.repL (micro S w x0 s').core = true)
    (x0_inv : ∀ w, Inv w 0 x0.core)
    (x0_ctl : (absS x0.core).ctl = GalilScaffoldController.initial delay)
    (inv_tick : ∀ w s a, inp w s = none → Inv w s a → Inv w (s+1) (S.tickL a))
    (inv_feed : ∀ w s letter a, inp w s = some letter → Inv w s a →
      Inv w (s+1) (S.feedC letter a))
    (stutter_of_starved : ∀ w s a, inp w s = none → Inv w s a → S.Starved a →
      absS (S.tickL a) = absS a)
    (tick_of_not_starved : ∀ w s a, inp w s = none → Inv w s a → ¬ S.Starved a →
      Tick (galilFrameS (Pof w) (qof w) (firstOf w)) delay (absS a) (absS (S.tickL a)))
    (feed_abs : ∀ w s letter a, inp w s = some letter → Inv w s a →
      absS (S.feedC letter a) = arriveState' letter (absS a))
    (H_ledger : LedgerObligation Pof qof firstOf (fun w => stAbs S absS w x0)
      (fun w => w.length * nLocalL)) :
    RecognizedByTotalPEG PAL := by
  have hrun := fun w => micro_shadow S L0 blank repQ outQ Inv Rep x0 q0 w hrepInit (x0_inv w)
    (inv_tick w) (inv_feed w) (hsimTick w) (hsimFeed w) hreadRep hreadOut
  have habsOf : ∀ (a : A) (p : Q × (Fin t → STape Γ)), Rep a p →
      shadowAbs absS outQ (a, p) = absS a := fun a p hrep =>
    shadowAbs_eq absS outQ (a, p) (by rw [← hreadOut a p hrep, outL_abs])
  have hstAbs : ∀ w s, stAbs (shadowSys S L0 blank repQ outQ) (shadowAbs absS outQ) w
      (shadowInit x0 q0 blank) s = stAbs S absS w x0 s := by
    intro w s
    obtain ⟨hcore, -, -, -, hrep⟩ := hrun w s
    show shadowAbs absS outQ (micro _ w _ s).core = absS (micro S w x0 s).core
    rw [← habsOf _ _ hrep, ← hcore]
  have hrepL : ∀ w s, (shadowSys S L0 blank repQ outQ).repL
      (micro (shadowSys S L0 blank repQ outQ) w (shadowInit x0 q0 blank) s).core
        = S.repL (micro S w x0 s).core := by
    intro w s
    obtain ⟨-, -, -, -, hrep⟩ := hrun w s
    exact (hreadRep _ _ hrep).symm
  refine pal_in_peg_of_local_core (shadowSys S L0 blank repQ outQ) (shadowAbs absS outQ)
    (fun w s x => Inv w s x.1 ∧ Rep x.1 x.2) (shadowInit x0 q0 blank) Pof qof firstOf delay
    H_letter H_first L0 blank q0 repQ outQ Prod.snd htape (fun _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) rfl x0_started (fun _ => rfl) ?_ ?_
    (fun w => ⟨x0_inv w, hrepInit⟩) ?_
    (fun w s x hinput hx => ⟨inv_tick w s _ hinput hx.1, hsimTick w s _ _ hinput hx.1 hx.2⟩)
    (fun w s letter x hinput hx =>
      ⟨inv_feed w s _ _ hinput hx.1, hsimFeed w s _ _ _ hinput hx.1 hx.2⟩) ?_ ?_ ?_ ?_
  · intro w s hw hlate hreport
    rw [hstAbs]
    exact rep_sound w s hw hlate (by rw [← hrepL]; exact hreport)
  · intro w s hw hpoint hrefreshed
    rw [hstAbs] at hpoint hrefreshed
    obtain ⟨s', hle, hlate, hreport⟩ := rep_complete w s hw hpoint hrefreshed
    exact ⟨s', hle, hlate, by rw [hrepL]; exact hreport⟩
  · show (shadowAbs absS outQ (x0.core, (q0, fun _ => STape.blankTape blank))).ctl = _
    rw [habsOf _ _ hrepInit]
    exact x0_ctl
  · intro w s x hinput hx hstarved
    show shadowAbs absS outQ (S.tickL x.1, L0.apply blank x.2 none) = shadowAbs absS outQ x
    rw [habsOf _ _ (hsimTick w s _ _ hinput hx.1 hx.2), habsOf x.1 x.2 hx.2]
    exact stutter_of_starved w s _ hinput hx.1 hstarved
  · intro w s x hinput hx hstarved
    show Tick _ delay (shadowAbs absS outQ x)
      (shadowAbs absS outQ (S.tickL x.1, L0.apply blank x.2 none))
    rw [habsOf _ _ (hsimTick w s _ _ hinput hx.1 hx.2), habsOf x.1 x.2 hx.2]
    exact tick_of_not_starved w s _ hinput hx.1 hstarved
  · intro w s letter x hinput hx
    show shadowAbs absS outQ (S.feedC letter x.1, L0.apply blank x.2 (some letter))
      = arriveState' letter (shadowAbs absS outQ x)
    rw [habsOf _ _ (hsimFeed w s _ _ _ hinput hx.1 hx.2), habsOf x.1 x.2 hx.2]
    exact feed_abs w s _ _ hinput hx.1
  · have hfun : (fun w => stAbs (shadowSys S L0 blank repQ outQ) (shadowAbs absS outQ) w
        (shadowInit x0 q0 blank)) = fun w => stAbs S absS w x0 :=
      funext fun w => funext fun s => hstAbs w s
    rw [hfun]
    exact H_ledger

#print axioms pal_in_peg_of_shadowed_core

end PalPeg.LocalShadowRealize
