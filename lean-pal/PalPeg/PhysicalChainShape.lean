import PalPeg.PhysicalContract
import PalPeg.ChainStoredPeriod

/-!
# Period shape supplied by the final consumer's run

Truncating the not-yet-arrived input changes only the chain verifier. Its
period block therefore comes directly from the pre-trace. The post-report
phase carries a packed run from an idle-chain origin and supplies the same
fact. No new invariant is required of the physical machine.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalChainShape
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilBranchInvariants PalPeg.GalilChainCoupling
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.CloseoutCheckW (PreTraceIMW)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalShadowConcrete (OnRun)
open PalPeg.LocalBlankState (tapeCount)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter)

/-- The structural facts needed at back-to-watch, obtained without extra
physical state or a hypothesis about a target encoding. -/
def PeriodInv (chain : ChainVM) : Prop := BlockInv chain ∧ PalPeg.ChainStoredPeriod.Stored chain

theorem period_trunc (d : ℕ) (chain : ChainVM) (hb : PeriodInv chain) :
    PeriodInv (PalPeg.GalilThrottledRun.truncChain d chain) := by
  cases chain <;> exact hb

/-- Coupling supplies the block condition consumed by the stored-length step. -/
theorem coupled_stored_tick {w : List (Fin 2)} {x y : State GalilVM}
    (ht : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (hi : Coupled x.ctl x.vm ∧ PalPeg.ChainStoredPeriod.Stored x.vm.chain) :
    Coupled y.ctl y.vm ∧ PalPeg.ChainStoredPeriod.Stored y.vm.chain :=
  ⟨coupled_tick (onLetterVM w) leftFirstVM centreC placeC 0 1 0 2048 hi.1 ht,
    PalPeg.ChainStoredPeriod.vmTick (onLetterVM w) leftFirstVM centreC placeC 0 1 0 2048
      hi.2 hi.1.block ht⟩

/-- The source conditions of the final TickCases supply period shape and h,
also on the packed plateau after the last report. -/
theorem period_onRun (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (hpre : PreTraceIMW centreC placeC 0 1 0 w st Tc)
    (m : Mirrored1 (tapeCount 0))
    (hon : OnRun (localGood (spare := 0)) (postPhase 0 1 0) w
      (heldAfter (Tc w.length) st) m) (hnotFrozen : ¬ frozenAt w m) :
    PeriodInv (absSC m).vm.chain := by
  rcases hon with htracked | ⟨hpost, _, _, _⟩
  · obtain ⟨k, j, _, hsource⟩ := htracked.track
    have hstart : Coupled (st 0).ctl (st 0).vm ∧ PalPeg.ChainStoredPeriod.Stored (st 0).vm.chain := by
      rw [hpre.base.pre.start]
      exact ⟨coupled_of_idle rfl, trivial⟩
    have hb := hpre.base.pre.trace.carried
      (Pk := fun x => Coupled x.ctl x.vm ∧ PalPeg.ChainStoredPeriod.Stored x.vm.chain)
      hstart (fun _ _ ht hi => coupled_stored_tick ht hi)
      (min k (Tc w.length)) (Nat.min_le_right _ _)
    change PeriodInv (PalPeg.LocalReplayParked.absState'' m.vm).vm.chain
    rw [hsource]
    exact period_trunc (w.length - j) _ ⟨hb.1.block, hb.2⟩
  · rcases hpost with hplateau | hfrozen
    · obtain ⟨c, s, k, kS, horigin, hrun, _⟩ := hplateau.onRun
      obtain ⟨g, hzero, hlast, htrace, _, _⟩ := hrun
      have hidle : s.chain = .idle := by
        rcases horigin.1.1.1.1.1 with hI | ⟨n, hI⟩
        · obtain ⟨radius, last, hrest⟩ := hI.rest
          exact hrest.1
        · exact hI.chainIdle
      have hc : Coupled (g 0).ctl (g 0).vm ∧ PalPeg.ChainStoredPeriod.Stored (g 0).vm.chain := by
        rw [hzero]
        exact ⟨coupled_of_idle hidle, by rw [hidle]; trivial⟩
      have hend := htrace.carried
        (Pk := fun x => Coupled x.ctl x.vm ∧ PalPeg.ChainStoredPeriod.Stored x.vm.chain)
        hc (fun _ _ ht hi => coupled_stored_tick ht hi) k le_rfl
      rw [hlast] at hend
      exact ⟨hend.1.block, hend.2⟩
    · exact (hnotFrozen hfrozen).elim

/-- FIRST occurs only at the left end of a represented period block. -/
theorem first_shape {v : PalPeg.GalilScaffoldChainPeriod.Tape}
    (hb : OnBlock v) (hf : PalPeg.GalilScaffoldChainPeriod.isFirst v.focus = true) :
    ∃ (first last : Fin 3) (xs : List (Fin 3)), v = ⟨[], .first first, xs.map PalPeg.GalilScaffoldChainPeriod.Token.plain ++ [.last last]⟩ := by
  obtain ⟨first, hfirst⟩ : ∃ first, v.focus = .first first := by
    cases hfocus : v.focus <;> simp_all [PalPeg.GalilScaffoldChainPeriod.isFirst]
  have hleft := onBlock_first hb hfirst
  obtain ⟨a, b, xs, hblock⟩ := hb
  rw [hleft] at hblock
  simp only [List.reverse_nil, List.nil_append, blockTokens, List.cons.injEq] at hblock
  exact ⟨a, b, xs, by cases v; simp_all⟩

/-- info: 'PalPeg.PhysicalChainShape.period_onRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms period_onRun

end PalPeg.PhysicalChainShape
