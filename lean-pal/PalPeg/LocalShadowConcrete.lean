import PalPeg.LocalShadowRealize
import PalPeg.LocalSysConcrete

/-!
# The concrete abstract local system, shadowed by a physical machine

`LocalShadowRealize.pal_in_peg_of_shadowed_core` applied to `LocalSysConcrete.sysC`.  The
invariant is a fact about the run: the state is the state of the run after `s` micro-steps, and
its abstraction is the pre-loaded trace at index `kOf … s`, truncated to the `arrL w s` letters
that have arrived.  A letter is only ever fed at its own slot, so tracking across an arrival is
`LocalSysConcrete.tracked_feedC`, and the trace is only used below its last report point.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PalPeg.LocalShadowConcrete

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.Local (LocalStep)
open PalPeg.LocalTrackingLatch PalPeg.LocalShadowRealize
open PalPeg.LocalLedgerShift (kOf kOf_succ_tick kOf_succ_stutter H_ledger_of_local_oracles)
open PalPeg.LocalReplayParked (absState'' Mirrored1 MirInv1)
open PalPeg.LocalSysConcrete (Steps stepOf tickC tickC_starved tickC_step sysC absSC feedC Starved
  Needy InvC PhysWF Realizes x0C x0C_ctl x0C_started x0C_physWF x0C_mirInv1 tick_of_need used_le_of_need
  tracked_feedC feed_abs_core physWF_feedC mirInv1_feedC)
open PalPeg.GalilThrottledRun (truncS usedVM SufVM)
open PalPeg.GalilLookRefined (needT')

variable {P : ℕ}

/-- The state `m` stands on the pre-loaded trace at index `k ≤ lastReport`, with `j` letters
arrived, none of which beyond `j` has been used. -/
structure TrackedAt (Good : Mirrored1 P → Prop) (raw : List (Fin 2))
    (stOf : ℕ → State GalilVM) (lastReport j k : ℕ) (m : Mirrored1 P) : Prop where
  phys : PhysWF m.vm
  mir : MirInv1 m
  needy : Needy raw stOf k j m.vm
  beforeEnd : k ≤ lastReport
  used : usedVM raw (stOf k).vm ≤ j
  good : Good m

theorem TrackedAt.invC {Good : Mirrored1 P → Prop} {raw : List (Fin 2)}
    {stOf : ℕ → State GalilVM} {lastReport j k : ℕ} {m : Mirrored1 P}
    (h : TrackedAt Good raw stOf lastReport j k m) : InvC Good raw stOf m :=
  ⟨h.phys, h.mir, ⟨k, j, h.needy⟩, h.good⟩

theorem micro_core_none {X : Type} (S : LocalSys X) (w : List (Fin 2)) (x0 : LX X) {s : ℕ}
    (hinput : inp w s = none) :
    (micro S w x0 (s+1)).core = S.tickL (micro S w x0 s).core := by
  show (stepL S (inp w s) (micro S w x0 s)).core = _
  rw [hinput]
  rfl

theorem micro_core_some {X : Type} (S : LocalSys X) (w : List (Fin 2)) (x0 : LX X) {s : ℕ}
    {letter : Fin 2} (hinput : inp w s = some letter) :
    (micro S w x0 (s+1)).core = S.feedC letter (micro S w x0 s).core := by
  show (stepL S (inp w s) (micro S w x0 s)).core = _
  rw [hinput]
  rfl

/-- **`PAL ∈ PEG` from the concrete abstract local system and a physical machine that shadows
it.**  The hypotheses are: the pre-loaded trace (used below its last report point only), the
per-mode obligation below the last report point, the starvation test in both directions and at
the last report point, the report test on the run, and the specification of the physical
machine. -/
theorem pal_in_peg_of_shadowed_sysC
    {Q Γ : Type} {t K : ℕ} [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    (M : Steps P) (repC : Control → Bool) (blank : PalPeg.LocalState.GalilVML P) (delay : ℕ)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9)
    (H_letter : ∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w)
    (H_first : ∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM)
    -- the initial abstract state
    (hblankInv : PalPeg.LocalTick1.Inv blank)
    (hblankTwin : PalPeg.LocalReplaySwap.Twin blank.left blank.center)
    (hblankView : PalPeg.LocalInputView.WF blank.left)
    -- the pre-loaded trace
    (stOf : List (Fin 2) → ℕ → State GalilVM) (TcOf : List (Fin 2) → ℕ → ℕ)
    (hshared : ∀ (w : List (Fin 2)) j, PalPeg.GalilTruncTick.SharedTrunc w j (Pof w))
    (htrace : ∀ w : List (Fin 2), 0 < w.length → ∀ k, k < TcOf w w.length →
      Tick (galilFrameS (Pof w) (qof w) (firstOf w)) delay (stOf w k) (stOf w (k+1)))
    (hsuffix : ∀ w : List (Fin 2), 0 < w.length → ∀ k, k ≤ TcOf w w.length →
      SufVM w (stOf w k).vm)
    (hinitTrack : ∀ w : List (Fin 2), 0 < w.length →
      absState'' (x0C blank delay).core.vm = truncS w.length (stOf w 0))
    (hinitUsed : ∀ w : List (Fin 2), 0 < w.length → usedVM w (stOf w 0).vm = 0)
    (hpreload : ∀ w : List (Fin 2), 0 < w.length →
      GalilLookRefined.PreloadL' w (stOf w) (TcOf w))
    (hbase : ∀ w : List (Fin 2), 0 < w.length → TcOf w 1 ≤ 2050)
    (hcost : ∀ (w : List (Fin 2)), 0 < w.length → ∀ m, 1 ≤ m → m < w.length →
      TcOf w (m+1) - TcOf w m
        ≤ GalilLedgerQ64.alpha' 2048 * (Cw w (m+1) - Cw w m)
          + GalilLedgerQ64.beta' 2048)
    (hlastReport : ∀ w : List (Fin 2), 0 < w.length →
      GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w w.length
        (stOf w (TcOf w w.length)))
    -- the invariants the abstract local system carries along the run
    (Good : Mirrored1 P → Prop) (hgoodInit : Good (x0C blank delay).core)
    (hgoodTick : ∀ (w : List (Fin 2)) (m : Mirrored1 P), 0 < w.length →
      InvC Good w (stOf w) m → Good (tickC M m))
    (hgoodFeed : ∀ (w : List (Fin 2)) (letter : Fin 2) (m : Mirrored1 P), 0 < w.length →
      InvC Good w (stOf w) m → Good (feedC letter m))
    -- the abstract local system on tracked states
    (hrealizes : ∀ (w : List (Fin 2)), 0 < w.length → ∀ mode : Mode,
      Realizes Good w (stOf w) (TcOf w w.length) (stepOf M mode) mode)
    (hneedOfNotStarved : ∀ (w : List (Fin 2)) (m : Mirrored1 P) (k j : ℕ), 0 < w.length →
      InvC Good w (stOf w) m →
      ¬ Starved m.vm → Needy w (stOf w) k j m.vm → needT' w (stOf w) k ≤ j)
    (hnotStarvedOfNeed : ∀ (w : List (Fin 2)) (m : Mirrored1 P) (k j : ℕ), 0 < w.length →
      InvC Good w (stOf w) m →
      Needy w (stOf w) k j m.vm → k < TcOf w w.length → needT' w (stOf w) k ≤ j →
      ¬ Starved m.vm)
    (hstarvedAtLastReport : ∀ (w : List (Fin 2)) (m : Mirrored1 P) (j : ℕ), 0 < w.length →
      InvC Good w (stOf w) m →
      Needy w (stOf w) (TcOf w w.length) j m.vm → Starved m.vm)
    (rep_sound : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length → (w.length - 1) * nLocalL < s →
      repC (micro (sysC M repC) w (x0C blank delay) s).core.vm.ctl = true →
      ReportPoint w (stAbs (sysC M repC) absSC w (x0C blank delay) s) ∧
        Refreshed (Pof w) (qof w) (firstOf w) (stAbs (sysC M repC) absSC w (x0C blank delay) s))
    (rep_complete : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length →
      ReportPoint w (stAbs (sysC M repC) absSC w (x0C blank delay) s) →
      Refreshed (Pof w) (qof w) (firstOf w) (stAbs (sysC M repC) absSC w (x0C blank delay) s) →
      ∃ s', s' ≤ s ∧ (w.length - 1) * nLocalL + 1 < s' ∧
        repC (micro (sysC M repC) w (x0C blank delay) s').core.vm.ctl = true)
    -- the physical machine and its specification
    (L0 : LocalStep (Fin 2) Q Γ t K) (blankSymbol : Γ) (q0 : Q) (repQ outQ : Q → Bool)
    (htape : 0 < t) (Rep : Mirrored1 P → Q × (Fin t → STape Γ) → Prop)
    (hrepInit : Rep (x0C blank delay).core (q0, fun _ => STape.blankTape blankSymbol))
    (hsimTick : ∀ m p, PhysWF m.vm → MirInv1 m → Rep m p →
      Rep (tickC M m) (L0.apply blankSymbol p none))
    (hsimFeed : ∀ letter m p, PhysWF m.vm → MirInv1 m → Rep m p →
      Rep (feedC letter m) (L0.apply blankSymbol p (some letter)))
    (hreadRep : ∀ m p, Rep m p → repC m.vm.ctl = repQ p.1)
    (hreadOut : ∀ m p, Rep m p → m.vm.ctl.output = outQ p.1) :
    RecognizedByTotalPEG PAL := by
  classical
  let S := sysC M repC
  let x0 := x0C blank delay
  let Inv : List (Fin 2) → ℕ → Mirrored1 P → Prop := fun w s m =>
    0 < w.length ∧ m = (micro S w x0 s).core ∧
      TrackedAt Good w (stOf w) (TcOf w w.length) (arrL w s) (kOf S w x0 s) m
  have harrZero : ∀ w : List (Fin 2), arrL w 0 = 0 := fun w => by
    unfold arrL
    rw [nLocalL_eq]
    omega
  have hinvInit : ∀ w, 0 < w.length → Inv w 0 x0.core := fun w hw => by
    refine ⟨hw, rfl, x0C_physWF hblankInv delay, x0C_mirInv1 hblankTwin hblankView delay, ?_,
      Nat.zero_le _, ?_, hgoodInit⟩
    · rw [harrZero]
      exact ⟨Nat.zero_le _, hinitTrack w hw⟩
    · rw [harrZero]
      exact (hinitUsed w hw).le
  have hinvTick : ∀ w s m, inp w s = none → Inv w s m → Inv w (s+1) (S.tickL m) := by
    rintro w s m hinput ⟨hw, rfl, htracked⟩
    refine ⟨hw, (micro_core_none S w x0 hinput).symm, ?_⟩
    rw [arrL_none w s hinput]
    by_cases hstarved : Starved (micro S w x0 s).core.vm
    · rw [kOf_succ_stutter S w x0 s (fun h => h.2 hstarved)]
      show TrackedAt _ _ _ _ _ _ (tickC M _)
      rw [tickC_starved M hstarved]
      exact htracked
    · have hneed := hneedOfNotStarved w _ _ _ hw htracked.invC hstarved htracked.needy
      have hbefore : kOf S w x0 s < TcOf w w.length := by
        rcases Nat.lt_or_ge (kOf S w x0 s) (TcOf w w.length) with h | h
        · exact h
        · have hend : kOf S w x0 s = TcOf w w.length := le_antisymm htracked.beforeEnd h
          exact absurd (hstarvedAtLastReport w _ _ hw htracked.invC (hend ▸ htracked.needy)) hstarved
      obtain ⟨hneedy, hphys, hmir⟩ :=
        hrealizes w hw _ _ _ _ htracked.invC rfl hstarved htracked.needy hneed hbefore
      have hgoodNext := hgoodTick w _ hw htracked.invC
      rw [kOf_succ_tick S w x0 s ⟨hinput, hstarved⟩]
      show TrackedAt _ _ _ _ _ _ (tickC M _)
      rw [tickC_step M hstarved] at hgoodNext ⊢
      exact ⟨hphys, hmir, hneedy, hbefore, (used_le_of_need hneed).2.1, hgoodNext⟩
  have hinvFeed : ∀ w s letter m, inp w s = some letter → Inv w s m →
      Inv w (s+1) (S.feedC letter m) := by
    rintro w s letter m hinput ⟨hw, rfl, htracked⟩
    obtain ⟨harrived, hletter⟩ := arrL_some w s letter hinput
    have hindex : arrL w s < w.length := (List.getElem?_eq_some_iff.mp hletter).1
    have hletterEq : letter = w[arrL w s] := ((List.getElem?_eq_some_iff.mp hletter).2).symm
    refine ⟨hw, (micro_core_some S w x0 hinput).symm, ?_⟩
    rw [harrived, kOf_succ_stutter S w x0 s (fun h => by rw [hinput] at h; exact absurd h.1 (by simp))]
    refine ⟨physWF_feedC htracked.phys letter,
      mirInv1_feedC htracked.mir htracked.phys.pend htracked.phys.inv.views.2.1 letter, ?_,
      htracked.beforeEnd, by have := htracked.used; omega,
      hgoodFeed w letter _ hw htracked.invC⟩
    rw [hletterEq]
    exact tracked_feedC htracked.phys.inv.views htracked.phys.pend htracked.needy hindex
      (hsuffix w hw _ htracked.beforeEnd) htracked.used
  have hrun : ∀ w, 0 < w.length → ∀ s,
      TrackedAt Good w (stOf w) (TcOf w w.length) (arrL w s) (kOf S w x0 s) (micro S w x0 s).core :=
    fun w hw s => (inv_micro S w x0 (Inv w) (hinvInit w hw) (hinvTick w) (hinvFeed w) s).2.2
  refine pal_in_peg_of_shadowed_core S absSC Inv x0 Pof qof firstOf delay H_letter H_first
    L0 blankSymbol q0 repQ outQ htape Rep hrepInit
    (fun w s m p _ hinv hrep => hsimTick m p hinv.2.2.phys hinv.2.2.mir hrep)
    (fun w s letter m p _ hinv hrep => hsimFeed letter m p hinv.2.2.phys hinv.2.2.mir hrep)
    hreadRep hreadOut (x0C_started blank delay) (PalPeg.LocalSysConcrete.outL_abs M repC)
    rep_sound rep_complete hinvInit (x0C_ctl blank delay) hinvTick hinvFeed ?_ ?_ ?_ ?_
  · rintro w s m _ _ hstarved
    show absSC (tickC M m) = absSC m
    rw [tickC_starved M hstarved]
  · rintro w s m hinput ⟨hw, rfl, htracked⟩ hstarved
    have hnext := (hinvTick w s _ hinput ⟨hw, rfl, htracked⟩).2.2
    have hneed := hneedOfNotStarved w _ _ _ hw htracked.invC hstarved htracked.needy
    have hbefore : kOf S w x0 s < TcOf w w.length := by
      rcases Nat.lt_or_ge (kOf S w x0 s) (TcOf w w.length) with h | h
      · exact h
      · have hend : kOf S w x0 s = TcOf w w.length := le_antisymm htracked.beforeEnd h
        exact absurd (hstarvedAtLastReport w _ _ hw htracked.invC (hend ▸ htracked.needy)) hstarved
    rw [arrL_none w s hinput, kOf_succ_tick S w x0 s ⟨hinput, hstarved⟩] at hnext
    show Tick _ delay (absSC _) (absSC (tickC M _))
    rw [show absSC (micro S w x0 s).core = _ from htracked.needy.2,
      show absSC (tickC M (micro S w x0 s).core) = _ from hnext.needy.2]
    exact tick_of_need (hshared w _) (htrace w hw _ hbefore) hneed
  · rintro w s letter m _ ⟨_, rfl, htracked⟩
    exact feed_abs_core htracked.phys.inv.views htracked.phys.pend letter
  · exact H_ledger_of_local_oracles S absSC x0 Pof qof firstOf stOf TcOf hpreload
      (fun w hw s hstarved =>
        hneedOfNotStarved w _ _ _ hw (hrun w hw s).invC hstarved (hrun w hw s).needy)
      (fun w hw s hbefore hneed =>
        hnotStarvedOfNeed w _ _ _ hw (hrun w hw s).invC (hrun w hw s).needy hbefore hneed)
      hbase hcost (fun w hw s => (hrun w hw s).needy.2) hlastReport

#print axioms pal_in_peg_of_shadowed_sysC

end PalPeg.LocalShadowConcrete
