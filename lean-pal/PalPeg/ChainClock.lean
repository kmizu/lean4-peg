import PalPeg.RestartStageRun

/-!
# The clock of a chain before it has caught up

A chain is born within two semiperiods of the centre and then copies its period, walks back and
catches up with the scan.  Each scan tick is one chain step, a match comes once in `2048` ticks,
so the radius cannot reach four semiperiods before the chain has caught up.  This file is the
chain-level half: the remaining work of a chain and its semiperiod, as functions of the chain
state, and how one chain step and one matched event change them.
-/

set_option autoImplicit false

namespace PalPeg.ChainClock

open PalPeg GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply GalilBranchInvariants
open GalilScaffoldTop PalPeg.GalilChainCoupling PalPeg.GalilShiftH

/-- The unary answer still to be copied: the run of `8`s from the focus leftwards. -/
def remainingBits (t : GalilScaffoldTape.Tape) : ℕ :=
  ((t.focus :: t.left).takeWhile (fun x => decide (x = 8))).length

theorem remainingBits_of_left {t : GalilScaffoldTape.Tape} (hleft : t.focus = 4) :
    remainingBits t = 0 := by
  unfold remainingBits
  rw [hleft]
  simp [List.takeWhile]

theorem remainingBits_moveLeft {t : GalilScaffoldTape.Tape} (hone : t.focus = 8)
    (hlegal : t.left ≠ []) :
    remainingBits (GalilScaffoldTape.moveLeft t) + 1 = remainingBits t := by
  obtain ⟨a, ls, hls⟩ := List.exists_cons_of_ne_nil hlegal
  unfold remainingBits GalilScaffoldTape.moveLeft
  rw [hls, hone]
  simp [List.takeWhile]

/-- The semiperiod of a chain: the cells of its period tape, plus what is still to be copied. -/
def chainPeriod : ChainVM → ℤ
  | .copy t _ _ v _ _ _ => (cells v : ℤ) + (remainingBits t : ℤ) - 1
  | x => (cellsOf x : ℤ) - 1

/-- The chain steps left before the chain has caught up with the scan. -/
def chainWork : ChainVM → ℤ
  | .copy t _ _ v lag _ _ =>
      (remainingBits t : ℤ) + 1 + ((cells v : ℤ) + (remainingBits t : ℤ) - 1) + 1 + value lag
  | .back v _ lag _ _ => (v.left.length : ℤ) + 1 + value lag
  | .watch w => value w.lag
  | _ => 0

/-- One chain step does one unit of the remaining work and keeps the semiperiod. -/
theorem chainWork_step {x y : ChainVM} (hstep : ChainStep x y) (hblock : BlockInv x)
    (hlag : ∀ w, x = .watch w → Canonical w.lag) (hwork : 0 < chainWork x) :
    chainWork y ≤ chainWork x - 1 ∧ (0 < chainWork y → chainPeriod y = chainPeriod x) := by
  cases hstep with
  | idle => simp [chainWork] at hwork
  | brokenIdle => simp [chainWork] at hwork
  | copyBit t h p v lag margin ver a one legal present =>
    have hbits := remainingBits_moveLeft one legal
    have hcells := cells_put v a hblock.1
    simp only [chainWork, chainPeriod]
    rw [hcells]
    push_cast
    constructor
    · omega
    · intro _; omega
  | copyEnd t h p v lag margin ver b hleft hp hv =>
    have hbits := remainingBits_of_left hleft
    have hright : v.right = [] := hblock.1
    have hcells : cells (GalilScaffoldChainPeriod.write v (.last b)) = cells v := cells_write _ _
    have hleftLength : (GalilScaffoldChainPeriod.write v (.last b)).left.length = v.left.length :=
      rfl
    simp only [chainWork, chainPeriod, cellsOf]
    rw [hbits, hcells, hleftLength]
    unfold cells
    rw [hright]
    simp only [List.length_nil]
    push_cast
    constructor
    · omega
    · intro _; omega
  | backStep v h lag margin ver hf =>
    have hne := onBlock_left_ne hblock hf
    obtain ⟨l0, ls, hls⟩ := List.exists_cons_of_ne_nil hne
    have hcells := cells_moveLeft v
    have hleftLength : (GalilScaffoldChainPeriod.moveLeft v).left.length + 1 = v.left.length := by
      rcases v with ⟨left, f, right⟩
      simp only at hls
      subst hls
      simp [GalilScaffoldChainPeriod.moveLeft]
    simp only [chainWork, chainPeriod, cellsOf]
    rw [hcells]
    constructor
    · omega
    · intro _; trivial
  | backDone v h lag margin ver hf =>
    have hleft : v.left = [] := by
      cases hv : v.focus with
      | first c => exact onBlock_first hblock hv
      | _ => rw [hv] at hf; simp [GalilScaffoldChainPeriod.isFirst] at hf
    have hright : v.right ≠ [] := onBlock_right_ne hblock (by
      cases hv : v.focus with
      | first c => rfl
      | _ => rw [hv] at hf; simp [GalilScaffoldChainPeriod.isFirst] at hf)
    have hcells : cells (watchControl v).period = cells v := cells_moveRight v hright
    simp only [chainWork, chainPeriod, cellsOf]
    rw [hleft, hcells]
    simp only [List.length_nil]
    push_cast
    constructor
    · omega
    · intro _; trivial
  | watchStep w w' hinternal =>
    have hbw : OnBlock w.machine.control.period := hblock
    cases hinternal with
    | idle hz =>
      exfalso
      have hcanonical := hlag w rfl
      have hvalue : ¬ 0 < value w.lag := fun hpos =>
        absurd ((positive_iff _ hcanonical).mpr hpos) (by rw [hz]; simp)
      exact hvalue hwork
    | take hp hg =>
      have hcells : cells (GalilScaffoldChainVerifier.consume w.machine).control.period
          = cells w.machine.control.period := cells_verifier_consume w.machine hbw
      simp only [chainWork, chainPeriod, cellsOf, GalilScaffoldChainWatch.caught, dec_value]
      rw [hcells]
      constructor
      · omega
      · intro _; trivial
  | watchBreak w hb =>
    simp only [chainWork]
    have : (0 : ℤ) < value w.lag := hwork
    constructor
    · omega
    · intro h; exact absurd h (lt_irrefl _)

/-- A matched event queues one more unit of work at most and keeps the semiperiod. -/
theorem chainWork_matched {y z : ChainVM} (hmatched : ChainMatched y z) :
    chainWork z ≤ chainWork y + 1 ∧ (0 < chainWork z → chainPeriod z = chainPeriod y) := by
  cases hmatched with
  | idle => simp [chainWork]
  | copy t h p v lag margin ver =>
    simp only [chainWork, chainPeriod, inc_value]
    exact ⟨by omega, fun _ => trivial⟩
  | back v h lag margin ver =>
    simp only [chainWork, chainPeriod, inc_value]
    exact ⟨by omega, fun _ => rfl⟩
  | watch w w' houter =>
    cases houter with
    | queued hz =>
      simp only [chainWork, chainPeriod, cellsOf, GalilScaffoldChainWatch.queued, inc_value]
      exact ⟨by omega, fun _ => trivial⟩
    | immediate hz hg =>
      have hzero : value w.lag = 0 := value_zero_of_zero hz
      simp only [chainWork, GalilScaffoldChainWatch.immediate]
      rw [hzero]
      exact ⟨by omega, fun h => absurd h (lt_irrefl _)⟩
  | breaks w w' hb =>
    simp only [chainWork]
    have hzero : value w.lag = 0 := value_zero_of_zero hb.1
    rw [hzero]
    exact ⟨by omega, fun h => absurd h (lt_irrefl _)⟩
  | brokenMatched w => simp [chainWork]

end PalPeg.ChainClock
