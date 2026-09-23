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
    (repQ : Q → (Fin t → PalPeg.Local.Window Γ K) → Bool) (outQ : Q → Bool) : LocalSys (A × (Q × (Fin t → STape Γ))) where
  tickL := fun x => (S.tickL x.1, L0.apply blank x.2 none)
  feedC := fun a x => (S.feedC a x.1, L0.apply blank x.2 (some a))
  repL := fun x => repQ x.2.1 (fun j => PalPeg.Local.readWin blank K (x.2.2 j))
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

variable (S : LocalSys A) (L0 : LocalStep (Fin 2) Q Γ t K) (blank : Γ)
  (repQ : Q → (Fin t → PalPeg.Local.Window Γ K) → Bool) (outQ : Q → Bool)
  (Inv : List (Fin 2) → ℕ → A → Prop) (Rep : A → Q × (Fin t → STape Γ) → Prop)

/-- **The lockstep run.**  The abstract half of the run of the pair is the abstract run, and the
physical half represents it.  (The latch of the pair reads the physical control; how it relates to
the abstract report test is the business of `pal_in_peg_of_shadowed_core`.) -/
theorem micro_shadow (x0 : LX A) (q0 : Q) (w : List (Fin 2))
    (hrepInit : Rep x0.core (q0, fun _ => STape.blankTape blank))
    (hinvInit : Inv w 0 x0.core)
    (hinvTick : ∀ s a, inp w s = none → Inv w s a → Inv w (s+1) (S.tickL a))
    (hinvFeed : ∀ s letter a, inp w s = some letter → Inv w s a →
      Inv w (s+1) (S.feedC letter a))
    (hsimTick : ∀ s a p, inp w s = none → Inv w s a → Rep a p →
      Rep (S.tickL a) (L0.apply blank p none))
    (hsimFeed : ∀ s letter a p, inp w s = some letter → Inv w s a → Rep a p →
      Rep (S.feedC letter a) (L0.apply blank p (some letter))) :
    ∀ s, (micro (shadowSys S L0 blank repQ outQ) w (shadowInit x0 q0 blank) s).core.1
          = (micro S w x0 s).core ∧
      Inv w s (micro S w x0 s).core ∧
      Rep (micro S w x0 s).core
        (micro (shadowSys S L0 blank repQ outQ) w (shadowInit x0 q0 blank) s).core.2
  | 0 => ⟨rfl, hinvInit, hrepInit⟩
  | s + 1 => by
    obtain ⟨hcore, hinv, hrep⟩ := micro_shadow x0 q0 w hrepInit hinvInit hinvTick
      hinvFeed hsimTick hsimFeed s
    show (stepL (shadowSys S L0 blank repQ outQ) (inp w s) _).core.1
        = (stepL S (inp w s) _).core ∧
      Inv w (s+1) (stepL S (inp w s) _).core ∧
      Rep (stepL S (inp w s) _).core
        (stepL (shadowSys S L0 blank repQ outQ) (inp w s) _).core.2
    cases hinput : inp w s with
    | none =>
      exact ⟨by show S.tickL _ = S.tickL _; rw [hcore], hinvTick s _ hinput hinv,
        hsimTick s _ _ hinput hinv hrep⟩
    | some letter =>
      exact ⟨by show S.feedC letter _ = S.feedC letter _; rw [hcore],
        hinvFeed s _ _ hinput hinv, hsimFeed s _ _ _ hinput hinv hrep⟩

end Lockstep

/-- **`PAL ∈ PEG` from an abstract local system and a physical machine that shadows it.**  The
hypotheses on the abstract system are those of `pal_in_peg_of_local_core`; the physical machine
enters only through the representation relation `Rep`. -/
theorem pal_in_peg_of_shadowed_core
    [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    (S : List (Fin 2) → LocalSys A) (absS : A → State GalilVM) (Inv : List (Fin 2) → ℕ → A → Prop) (x0 : LX A)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9)
    (H_letter : ∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w)
    (H_first : ∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM)
    -- the physical machine and its specification
    (L0 : LocalStep (Fin 2) Q Γ t K) (blank : Γ) (q0 : Q)
    (repQ : Q → (Fin t → PalPeg.Local.Window Γ K) → Bool) (outQ : Q → Bool) (htape : 0 < t)
    (Rep : List (Fin 2) → A → Q × (Fin t → STape Γ) → Prop)
    (hrepInit : ∀ w, Rep w x0.core (q0, fun _ => STape.blankTape blank))
    (hsimTick : ∀ w s a p, inp w s = none → Inv w s a → Rep w a p →
      Rep w ((S w).tickL a) (L0.apply blank p none))
    (hsimFeed : ∀ w s letter a p, inp w s = some letter → Inv w s a → Rep w a p →
      Rep w ((S w).feedC letter a) (L0.apply blank p (some letter)))
    (hreadRep : ∀ (w : List (Fin 2)) s a p, Inv w s a → Rep w a p →
      (S w).repL a = repQ p.1 (fun j => PalPeg.Local.readWin blank K (p.2 j)))
    (hreadOut : ∀ (w : List (Fin 2)) s a p, Inv w s a → Rep w a p → ReportPoint w (absS a) →
      (S w).outL a = outQ p.1)
    -- the abstract system
    (x0_started : x0.started = false)
    (outL_abs : ∀ (w : List (Fin 2)) (a : A), (S w).outL a = (absS a).ctl.output)
    (rep_sound : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length → (w.length - 1) * nLocalL < s →
      (S w).repL (micro (S w) w x0 s).core = true →
      ReportPoint w (stAbs (S w) absS w x0 s) ∧
        Refreshed (Pof w) (qof w) (firstOf w) (stAbs (S w) absS w x0 s))
    (rep_complete : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length →
      ReportPoint w (stAbs (S w) absS w x0 s) →
      Refreshed (Pof w) (qof w) (firstOf w) (stAbs (S w) absS w x0 s) →
      ∃ s', s' ≤ s ∧ (w.length - 1) * nLocalL + 1 < s' ∧ (S w).repL (micro (S w) w x0 s').core = true)
    (x0_inv : ∀ w, 0 < w.length → Inv w 0 x0.core)
    (inv_tick : ∀ w s a, inp w s = none → Inv w s a → Inv w (s+1) ((S w).tickL a))
    (inv_feed : ∀ w s letter a, inp w s = some letter → Inv w s a →
      Inv w (s+1) ((S w).feedC letter a))
    (H_ledger : LedgerObligation Pof qof firstOf (fun w => stAbs (S w) absS w x0)
      (fun w => w.length * nLocalL - 1)) :
    RecognizedByTotalPEG PAL := by
  have hrun := fun w (hw : 0 < w.length) =>
    micro_shadow (S w) L0 blank repQ outQ Inv (Rep w) x0 q0 w (hrepInit w) (x0_inv w hw)
    (inv_tick w) (inv_feed w) (hsimTick w) (hsimFeed w)
  -- the report point does not read the output bit, which is the only thing `shadowAbs` changes
  have hreportIff : ∀ (w : List (Fin 2)) (x : A × (Q × (Fin t → STape Γ))),
      ReportPoint w (shadowAbs absS outQ x) ↔ ReportPoint w (absS x.1) := fun w x =>
    ⟨fun h => ⟨h.notReplaying, h.scanInv, h.centre, h.atLast, h.nonempty⟩,
      fun h => ⟨h.notReplaying, h.scanInv, h.centre, h.atLast, h.nonempty⟩⟩
  -- at a report point of the abstract run the two abstractions agree
  have hstAbsAt : ∀ w, 0 < w.length → ∀ s, ReportPoint w (stAbs (S w) absS w x0 s) →
      stAbs (shadowSys (S w) L0 blank repQ outQ) (shadowAbs absS outQ) w
        (shadowInit x0 q0 blank) s = stAbs (S w) absS w x0 s := by
    intro w hw s hpoint
    obtain ⟨hcore, hinv, hrep⟩ := hrun w hw s
    show shadowAbs absS outQ (micro _ w _ s).core = absS (micro (S w) w x0 s).core
    have habs : shadowAbs absS outQ ((micro (S w) w x0 s).core,
        (micro (shadowSys (S w) L0 blank repQ outQ) w (shadowInit x0 q0 blank) s).core.2)
          = absS (micro (S w) w x0 s).core :=
      shadowAbs_eq absS outQ _ (by rw [← hreadOut w s _ _ hinv hrep hpoint, outL_abs w])
    rw [← habs, ← hcore]
  have hrepL : ∀ w, 0 < w.length → ∀ s, (shadowSys (S w) L0 blank repQ outQ).repL
      (micro (shadowSys (S w) L0 blank repQ outQ) w (shadowInit x0 q0 blank) s).core
        = (S w).repL (micro (S w) w x0 s).core := by
    intro w hw s
    obtain ⟨-, hinv, hrep⟩ := hrun w hw s
    exact (hreadRep w s _ _ hinv hrep).symm
  refine pal_in_peg_of_local_core (fun w => shadowSys (S w) L0 blank repQ outQ)
    (shadowAbs absS outQ) (shadowInit x0 q0 blank) Pof qof firstOf
    H_letter H_first L0 blank q0 repQ outQ Prod.snd htape (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl x0_started (fun _ _ => rfl) ?_ ?_ ?_
  · intro w s hw hlate hreport
    have hghost := rep_sound w s hw hlate (by rw [← hrepL w hw]; exact hreport)
    rw [hstAbsAt w hw s hghost.1]
    exact hghost
  · intro w s hw hpoint hrefreshed
    have hpointGhost : ReportPoint w (stAbs (S w) absS w x0 s) := by
      have h := (hreportIff w _).mp hpoint
      rw [(hrun w hw s).1] at h
      exact h
    rw [hstAbsAt w hw s hpointGhost] at hpoint hrefreshed
    obtain ⟨s', hle, hlate, hreport⟩ := rep_complete w s hw hpoint hrefreshed
    exact ⟨s', hle, hlate, by rw [hrepL w hw]; exact hreport⟩
  · intro w hw hpal
    obtain ⟨t', hle, hpoint, hrefreshed⟩ := H_ledger w hw hpal
    refine ⟨t', hle, ?_⟩
    show ReportPoint w (stAbs (shadowSys (S w) L0 blank repQ outQ) (shadowAbs absS outQ) w
        (shadowInit x0 q0 blank) t') ∧
      Refreshed (Pof w) (qof w) (firstOf w) (stAbs (shadowSys (S w) L0 blank repQ outQ)
        (shadowAbs absS outQ) w (shadowInit x0 q0 blank) t')
    rw [hstAbsAt w hw t' hpoint]
    exact ⟨hpoint, hrefreshed⟩

#print axioms pal_in_peg_of_shadowed_core

end PalPeg.LocalShadowRealize
