import PalPeg.LocalShadowRealize
import PalPeg.LocalSysConcrete
import PalPeg.LocalStarvedRight

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
open PalPeg.LocalSysConcrete (sysM Steps stepOf tickC tickC_starved tickC_step sysC absSC feedC Starved
  Needy TickNeed InvC PhysWF Realizes x0C x0C_ctl x0C_started x0C_physWF x0C_mirInv1 tick_of_need used_le_of_need
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

/-- **The states of the run**: tracked below the last report point, or in the phase after it.
The simulation by the physical machine is asked for on these states only. -/
def OnRun (Good : Mirrored1 P → Prop) (Post : List (Fin 2) → Mirrored1 P → Prop)
    (raw : List (Fin 2)) (stOf : ℕ → State GalilVM) (m : Mirrored1 P) : Prop :=
  InvC Good raw stOf m ∨ (Post raw m ∧ PhysWF m.vm ∧ MirInv1 m ∧ Good m)

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

/-- **The abstract successor of a local tick**: the same state when the test starves, and
otherwise a tick of the frame that satisfies the scheduling policy `Canon`.  With a policy that
makes the tick unique, two local states with the same abstraction have successors with the same
abstraction, whichever local step computed them. -/
def TickSucc (Pw : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (Canon : State GalilVM → State GalilVM → Prop) (starved : Prop) (x y : State GalilVM) : Prop :=
  (starved ∧ y = x) ∨ (¬ starved ∧ Tick (galilFrameS Pw q first) delay x y ∧ Canon x y)

/-- **`PAL ∈ PEG` from the concrete abstract local system and a physical machine that shadows
it.**  The hypotheses are: the pre-loaded trace (used below its last report point only), the
per-mode obligation below the last report point, the starvation test in both directions and at
the last report point, the report test on the run, and the specification of the physical
machine. -/
theorem pal_in_peg_of_shadowed_sysC
    {Q Γ : Type} {t K : ℕ} [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    (M : List (Fin 2) → Steps P) (repM : Mirrored1 P → Bool) (blank : PalPeg.LocalState.GalilVML P) (delay : ℕ)
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
    (Canon : List (Fin 2) → State GalilVM → State GalilVM → Prop)
    (hcanonTrace : ∀ w : List (Fin 2), 0 < w.length → ∀ k j, k < TcOf w w.length →
      TickNeed w (stOf w) k j →
      Canon w (truncS (w.length - j) (stOf w k)) (truncS (w.length - j) (stOf w (k+1))))
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
      InvC Good w (stOf w) m → Good (tickC (M w) m))
    (hgoodFeed : ∀ (w : List (Fin 2)) (letter : Fin 2) (m : Mirrored1 P), 0 < w.length →
      InvC Good w (stOf w) m → Good (feedC letter m))
    -- the abstract local system on tracked states
    (hrealizes : ∀ (w : List (Fin 2)), 0 < w.length → ∀ mode : Mode,
      Realizes Good w (stOf w) (TcOf w w.length) (stepOf (M w) mode) mode)
    -- what a non-starved tracked state still owes for its tick: the letters used by the target,
    -- and the lookahead of the chain verifier (the starvation test does not read the chain)
    (hnextUsedOfNotStarved : ∀ (w : List (Fin 2)) (m : Mirrored1 P) (k j : ℕ), 0 < w.length →
      InvC Good w (stOf w) m → ¬ Starved m.vm → Needy w (stOf w) k j m.vm →
      k < TcOf w w.length → usedVM w (stOf w k).vm ≤ j → usedVM w (stOf w (k+1)).vm ≤ j)
    (hchainLookOfNotStarved : ∀ (w : List (Fin 2)) (m : Mirrored1 P) (k j : ℕ), 0 < w.length →
      InvC Good w (stOf w) m → ¬ Starved m.vm → Needy w (stOf w) k j m.vm →
      k < TcOf w w.length → usedVM w (stOf w k).vm ≤ j → (stOf w k).ctl.mode = .scan →
      GalilLookRefined.lookChain' w.length (stOf w k).vm.chain ≤ j)
    (hnotStarvedOfNeed : ∀ (w : List (Fin 2)) (m : Mirrored1 P) (k j : ℕ), 0 < w.length →
      InvC Good w (stOf w) m →
      Needy w (stOf w) k j m.vm → k < TcOf w w.length → needT' w (stOf w) k ≤ j →
      ¬ Starved m.vm)
    -- after the last report point the trace says nothing: the local ticks are still ticks
    (Post : List (Fin 2) → Mirrored1 P → Prop)
    (hpostOfLastReport : ∀ (w : List (Fin 2)) (m : Mirrored1 P) (j : ℕ), 0 < w.length →
      InvC Good w (stOf w) m → Needy w (stOf w) (TcOf w w.length) j m.vm → Post w m)
    (hpostTick : ∀ (w : List (Fin 2)) (m : Mirrored1 P), 0 < w.length → Post w m →
      PhysWF m.vm → MirInv1 m → Good m → ¬ Starved m.vm →
      (Tick (galilFrameS (Pof w) (qof w) (firstOf w)) delay (absSC m) (absSC (tickC (M w) m)) ∧
          Canon w (absSC m) (absSC (tickC (M w) m))) ∧
        Post w (tickC (M w) m) ∧ PhysWF (tickC (M w) m).vm ∧ MirInv1 (tickC (M w) m) ∧ Good (tickC (M w) m))
    (rep_sound : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length → (w.length - 1) * nLocalL < s →
      repM (micro (sysM (M w) repM) w (x0C blank delay) s).core = true →
      ReportPoint w (stAbs (sysM (M w) repM) absSC w (x0C blank delay) s) ∧
        Refreshed (Pof w) (qof w) (firstOf w) (stAbs (sysM (M w) repM) absSC w (x0C blank delay) s))
    (rep_complete : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length →
      ReportPoint w (stAbs (sysM (M w) repM) absSC w (x0C blank delay) s) →
      Refreshed (Pof w) (qof w) (firstOf w) (stAbs (sysM (M w) repM) absSC w (x0C blank delay) s) →
      ∃ s', s' ≤ s ∧ (w.length - 1) * nLocalL + 1 < s' ∧
        repM (micro (sysM (M w) repM) w (x0C blank delay) s').core = true)
    -- the physical machine and its specification
    (L0 : LocalStep (Fin 2) Q Γ t K) (blankSymbol : Γ) (q0 : Q) (repQ outQ : Q → Bool)
    (htape : 0 < t) (Rep : Mirrored1 P → Q × (Fin t → STape Γ) → Prop)
    (hrepInit : Rep (x0C blank delay).core (q0, fun _ => STape.blankTape blankSymbol))
    (hsimTick : ∀ (w : List (Fin 2)) m p, 0 < w.length → OnRun Good Post w (stOf w) m →
      TickSucc (Pof w) (qof w) (firstOf w) delay (Canon w) (Starved m.vm) (absSC m)
        (absSC (tickC (M w) m)) →
      Rep m p → Rep (tickC (M w) m) (L0.apply blankSymbol p none))
    (hsimFeed : ∀ (w : List (Fin 2)) letter m p, 0 < w.length → OnRun Good Post w (stOf w) m →
      Rep m p → Rep (feedC letter m) (L0.apply blankSymbol p (some letter)))
    (hreadRep : ∀ m p, Rep m p → repM m = repQ p.1)
    (hreadOut : ∀ m p, Rep m p → m.vm.ctl.output = outQ p.1) :
    RecognizedByTotalPEG PAL := by
  classical
  let S : List (Fin 2) → LocalSys (Mirrored1 P) := fun w => sysM (M w) repM
  let x0 := x0C blank delay
  let Inv : List (Fin 2) → ℕ → Mirrored1 P → Prop := fun w s m =>
    0 < w.length ∧ m = (micro (S w) w x0 s).core ∧
      (TrackedAt Good w (stOf w) (TcOf w w.length) (arrL w s) (kOf (S w) w x0 s) m ∨
        (TcOf w w.length < kOf (S w) w x0 s ∧ arrL w s = w.length ∧
          Post w m ∧ PhysWF m.vm ∧ MirInv1 m ∧ Good m))
  have hneedOfNotStarved : ∀ (w : List (Fin 2)) (m : Mirrored1 P) (k j : ℕ), 0 < w.length →
      InvC Good w (stOf w) m → ¬ Starved m.vm → Needy w (stOf w) k j m.vm →
      k < TcOf w w.length → usedVM w (stOf w k).vm ≤ j → TickNeed w (stOf w) k j := by
    intro w m k j hw hinv hnotStarved hneedy hbefore hused
    refine ⟨hused, hnextUsedOfNotStarved w m k j hw hinv hnotStarved hneedy hbefore hused, ?_⟩
    unfold GalilLookRefined.look'
    split
    · rename_i hscan
      exact max_le
        (PalPeg.LocalStarvedRight.usedPH_right_le_of_notStarved hneedy hnotStarved
          (hsuffix w hw k hbefore.le) hused (Or.inr hscan))
        (hchainLookOfNotStarved w m k j hw hinv hnotStarved hneedy hbefore hused hscan)
    · exact Nat.zero_le _
  have honRun : ∀ {w s m}, Inv w s m → OnRun Good Post w (stOf w) m := by
    rintro w s m ⟨_, _, htracked | ⟨_, _, hpost, hphys, hmir, hgood⟩⟩
    · exact Or.inl htracked.invC
    · exact Or.inr ⟨hpost, hphys, hmir, hgood⟩
  have hpackOf : ∀ {w s m}, Inv w s m → PhysWF m.vm ∧ MirInv1 m := by
    rintro w s m ⟨_, _, htracked | ⟨_, _, _, hphys, hmir, _⟩⟩
    · exact ⟨htracked.phys, htracked.mir⟩
    · exact ⟨hphys, hmir⟩
  have harrZero : ∀ w : List (Fin 2), arrL w 0 = 0 := fun w => by
    unfold arrL
    rw [nLocalL_eq]
    omega
  have hinvInit : ∀ w, 0 < w.length → Inv w 0 x0.core := fun w hw => by
    refine ⟨hw, rfl, Or.inl ⟨x0C_physWF hblankInv delay,
      x0C_mirInv1 hblankTwin hblankView delay, ?_, Nat.zero_le _, ?_, hgoodInit⟩⟩
    · rw [harrZero]
      exact ⟨Nat.zero_le _, hinitTrack w hw⟩
    · rw [harrZero]
      exact (hinitUsed w hw).le
  -- at the last report point every letter has arrived
  have hallArrived : ∀ w (hw : 0 < w.length) s {m},
      TrackedAt Good w (stOf w) (TcOf w w.length) (arrL w s) (kOf (S w) w x0 s) m →
      kOf (S w) w x0 s = TcOf w w.length → arrL w s = w.length := by
    intro w hw s m htracked hend
    have hused := htracked.used
    rw [hend] at hused
    have hreport := PalPeg.GalilThrottledRun.used_of_report w hw (hlastReport w hw)
    have hle := PalPeg.LocalLedgerShift.arrL_le w s
    omega
  -- the tick out of the last report point, and every later tick
  have hfreeTick : ∀ w (hw : 0 < w.length) (m : Mirrored1 P), Post w m → PhysWF m.vm →
      MirInv1 m → Good m → ¬ Starved m.vm →
      (Tick (galilFrameS (Pof w) (qof w) (firstOf w)) delay (absSC m) (absSC (tickC (M w) m)) ∧
          Canon w (absSC m) (absSC (tickC (M w) m))) ∧
        Post w (tickC (M w) m) ∧ PhysWF (tickC (M w) m).vm ∧ MirInv1 (tickC (M w) m) ∧ Good (tickC (M w) m) :=
    fun w hw m => hpostTick w m hw
  have hsucc : ∀ w s m, Inv w s m → ¬ Starved m.vm →
      Tick (galilFrameS (Pof w) (qof w) (firstOf w)) delay (absSC m) (absSC (tickC (M w) m)) ∧
        Canon w (absSC m) (absSC (tickC (M w) m)) := by
    rintro w s m ⟨hw, rfl, hphase⟩ hstarved
    rcases hphase with htracked | ⟨_, _, hpost, hphys, hmir, hgood⟩
    · by_cases hend : kOf (S w) w x0 s = TcOf w w.length
      · exact (hfreeTick w hw _
          (hpostOfLastReport w _ _ hw htracked.invC (hend ▸ htracked.needy))
          htracked.phys htracked.mir htracked.good hstarved).1
      · have hbefore : kOf (S w) w x0 s < TcOf w w.length :=
          lt_of_le_of_ne htracked.beforeEnd hend
        have hneed := hneedOfNotStarved w _ _ _ hw htracked.invC hstarved htracked.needy
          hbefore htracked.used
        obtain ⟨hneedy, _, _⟩ :=
          hrealizes w hw _ _ _ _ htracked.invC rfl hstarved htracked.needy hneed hbefore
        rw [tickC_step (M w) hstarved,
          show absSC (micro (S w) w x0 s).core = _ from htracked.needy.2,
          show absSC (stepOf (M w) (micro (S w) w x0 s).core.vm.ctl.mode (micro (S w) w x0 s).core) = _
            from hneedy.2]
        exact ⟨tick_of_need (hshared w _) (htrace w hw _ hbefore) hneed,
          hcanonTrace w hw _ _ hbefore hneed⟩
    · exact (hfreeTick w hw _ hpost hphys hmir hgood hstarved).1
  have hinvTick : ∀ w s m, inp w s = none → Inv w s m → Inv w (s+1) ((S w).tickL m) := by
    rintro w s m hinput ⟨hw, rfl, hphase⟩
    refine ⟨hw, (micro_core_none (S w) w x0 hinput).symm, ?_⟩
    rw [arrL_none w s hinput]
    by_cases hstarved : Starved (micro (S w) w x0 s).core.vm
    · rw [kOf_succ_stutter (S w) w x0 s (fun h => h.2 hstarved)]
      show TrackedAt _ _ _ _ _ _ (tickC (M w) _) ∨ _ ∧ _ ∧ Post w (tickC (M w) _) ∧
        PhysWF (tickC (M w) _).vm ∧ MirInv1 (tickC (M w) _) ∧ Good (tickC (M w) _)
      rw [tickC_starved (M w) hstarved]
      exact hphase
    · rw [kOf_succ_tick (S w) w x0 s ⟨hinput, hstarved⟩]
      rcases hphase with htracked | ⟨hafter, harrived, hpost, hphys, hmir, hgood⟩
      · by_cases hend : kOf (S w) w x0 s = TcOf w w.length
        · obtain ⟨_, hpost', hphys', hmir', hgood'⟩ := hfreeTick w hw _
            (hpostOfLastReport w _ _ hw htracked.invC (hend ▸ htracked.needy))
            htracked.phys htracked.mir htracked.good hstarved
          exact Or.inr ⟨by omega, hallArrived w hw s htracked hend, hpost', hphys', hmir', hgood'⟩
        · have hbefore : kOf (S w) w x0 s < TcOf w w.length :=
            lt_of_le_of_ne htracked.beforeEnd hend
          have hneed := hneedOfNotStarved w _ _ _ hw htracked.invC hstarved htracked.needy
            hbefore htracked.used
          obtain ⟨hneedy, hphys', hmir'⟩ :=
            hrealizes w hw _ _ _ _ htracked.invC rfl hstarved htracked.needy hneed hbefore
          have hgoodNext := hgoodTick w _ hw htracked.invC
          refine Or.inl ?_
          show TrackedAt _ _ _ _ _ _ (tickC (M w) _)
          rw [tickC_step (M w) hstarved] at hgoodNext ⊢
          exact ⟨hphys', hmir', hneedy, hbefore, hneed.2.1, hgoodNext⟩
      · obtain ⟨_, hpost', hphys', hmir', hgood'⟩ :=
          hfreeTick w hw _ hpost hphys hmir hgood hstarved
        exact Or.inr ⟨by omega, harrived, hpost', hphys', hmir', hgood'⟩
  have hinvFeed : ∀ w s letter m, inp w s = some letter → Inv w s m →
      Inv w (s+1) ((S w).feedC letter m) := by
    rintro w s letter m hinput ⟨hw, rfl, hphase⟩
    obtain ⟨harrived, hletter⟩ := arrL_some w s letter hinput
    rcases hphase with htracked | ⟨_, hall, _⟩
    · have hindex : arrL w s < w.length := (List.getElem?_eq_some_iff.mp hletter).1
      have hletterEq : letter = w[arrL w s] := ((List.getElem?_eq_some_iff.mp hletter).2).symm
      refine ⟨hw, (micro_core_some (S w) w x0 hinput).symm, Or.inl ?_⟩
      rw [harrived,
        kOf_succ_stutter (S w) w x0 s (fun h => by rw [hinput] at h; exact absurd h.1 (by simp))]
      refine ⟨physWF_feedC htracked.phys letter,
        mirInv1_feedC htracked.mir htracked.phys.pend htracked.phys.inv.views.2.1 letter, ?_,
        htracked.beforeEnd, by have := htracked.used; omega,
        hgoodFeed w letter _ hw htracked.invC⟩
      rw [hletterEq]
      exact tracked_feedC htracked.phys.inv.views htracked.phys.pend htracked.needy hindex
        (hsuffix w hw _ htracked.beforeEnd) htracked.used
    · have hle := PalPeg.LocalLedgerShift.arrL_le w (s+1)
      omega
  have hrun : ∀ w, 0 < w.length → ∀ s, kOf (S w) w x0 s ≤ TcOf w w.length →
      TrackedAt Good w (stOf w) (TcOf w w.length) (arrL w s) (kOf (S w) w x0 s)
        (micro (S w) w x0 s).core := by
    intro w hw s hle
    rcases (inv_micro (S w) w x0 (Inv w) (hinvInit w hw) (hinvTick w) (hinvFeed w) s).2.2 with
      htracked | ⟨hafter, _⟩
    · exact htracked
    · omega
  refine pal_in_peg_of_shadowed_core S absSC Inv x0 Pof qof firstOf delay H_letter H_first
    L0 blankSymbol q0 repQ outQ htape Rep hrepInit
    (fun w s m p _ hinv hrep => hsimTick w m p hinv.1 (honRun hinv)
      (by
        by_cases hstarved : Starved m.vm
        · exact Or.inl ⟨hstarved, by rw [tickC_starved (M w) hstarved]⟩
        · exact Or.inr ⟨hstarved, hsucc w s m hinv hstarved⟩) hrep)
    (fun w s letter m p _ hinv hrep => hsimFeed w letter m p hinv.1 (honRun hinv) hrep)
    (fun _ => hreadRep) (fun _ => hreadOut) (x0C_started blank delay) (fun _ _ => rfl)
    rep_sound rep_complete hinvInit (x0C_ctl blank delay) hinvTick hinvFeed ?_ ?_ ?_ ?_
  · rintro w s m _ _ hstarved
    show absSC (tickC (M w) m) = absSC m
    rw [tickC_starved (M w) hstarved]
  · rintro w s m _ hinv hstarved
    exact (hsucc w s m hinv hstarved).1
  · rintro w s letter m _ hinv
    exact feed_abs_core (hpackOf hinv).1.inv.views (hpackOf hinv).1.pend letter
  · exact H_ledger_of_local_oracles S absSC x0 Pof qof firstOf stOf TcOf hpreload
      (fun w hw s hbefore hstarved =>
        (hneedOfNotStarved w _ _ _ hw (hrun w hw s hbefore.le).invC hstarved
          (hrun w hw s hbefore.le).needy hbefore (hrun w hw s hbefore.le).used).2.1)
      (fun w hw s hbefore hneed =>
        hnotStarvedOfNeed w _ _ _ hw (hrun w hw s hbefore.le).invC
          (hrun w hw s hbefore.le).needy hbefore hneed)
      hbase hcost (fun w hw s hle => (hrun w hw s hle).needy.2) hlastReport

#print axioms pal_in_peg_of_shadowed_sysC

end PalPeg.LocalShadowConcrete
