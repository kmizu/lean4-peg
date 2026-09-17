import PalPeg.CloseoutWatchRound50

/-!
# Closeout watch round 53 — `WatchTailC` discharged, `MatchQuantumC` slimmed

`CloseoutWatchRound50` left the match half of `ClockOneC` resting on two
hypotheses.  This round pays the first **in full** and removes it from the
second.

## §1 `WatchTailC` (Round 50 `:207`) is closed

The obstruction Round 50 records is real but *self-repairing*.  On a `.watch`
chain the match credit is not a field bump: `chainW_matched` takes
`Outer.queued` at a non-zero lag and `Outer.immediate` — an actual
`consume` — at lag zero, and the next `Internal` branches on `positive lag`,
which `inc` flips.  The fix is to close the relation under the flip: the pair
`(y, z)` travels along the run in **one of two** shapes,

* `WRel.queued`  — `z = queued y`    (same machine, lag +1, margin +1),
* `WRel.immediate` — `z = immediate y` (machine one `consume` ahead, same lag,
  margin +1),

and each background step maps one shape to the other (§1.3):

* `queued` at a lag-zero `y`: `y` idles, `z` (lag 1) *takes*, so `z` performs
  exactly the consume that `Outer.immediate` would have done — the pair leaves
  with shape `immediate`.  The `Good` this needs is `coreX_good` again, at
  `position ver + 1 ≤ R + 1`, which is where the *grown* window pays for
  itself.
* `queued` at a positive lag: both take, and `dec (inc lag) = inc (dec lag)`
  (`inc_dec_comm`) keeps the shape `queued`.
* `immediate`: the lag is untouched, so both sides branch alike and the shape
  is preserved; the take needs `Good` one cell further right, again inside the
  grown window.

So the run's **measure does not change**: the transported run has the *same*
length `n` (`wrel_run`, §1.4), and `WatchTailC` holds outright as soon as the
grown block `BlockOn … (C+1) (R+1)` and `R + 1 < |encoded raw|` are available
— both of which the caller (`clockOneC_of_match`) already has.

## §2 `MatchQuantumC` minus its `WatchTailC` conjunct

`MatchCoreC` (§2) is Round 50's `MatchQuantumC` with the `WatchTailC`
conjunct deleted; `matchQuantumC_of_core` puts it back from §1, using the
quantum's own block growth and right-head bound.  What is left open is
therefore purely the **machine-level** tick: `Tick.scan_match` at `clock = 1`
with the control transports.  That is the single named hypothesis
`MatchCoreC`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound53

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilReplaySpan (ChainW BlockOn coreX_good chainW_step)
open PalPeg.CloseoutWatchRound42 (LandingData)
open PalPeg.CloseoutWatchRound43 (ChainWRun)
open PalPeg.CloseoutWatchRound48 (ClockOneC run_succ run_zero)
open PalPeg.CloseoutWatchRound50 (WatchTailC WBump Bump MatchQuantumC inc_dec_comm encoded_len
  landing_right_lt)
open PalPeg.CloseoutWatchRound40 (LiveScanChain)

/-! ## 1. `WatchTailC` -/

/-! ### 1.1 The two shapes of the credit on a watching chain -/

/-- The match credit on a watching chain, closed under the `Internal` flip. -/
inductive WRel : ChainVM → ChainVM → Prop
  | queued (w : GalilScaffoldChainWatch.State) :
      WRel (.watch w) (.watch (GalilScaffoldChainWatch.queued w))
  | immediate (w : GalilScaffoldChainWatch.State) :
      WRel (.watch w) (.watch (GalilScaffoldChainWatch.immediate w))

/-- **Closed.**  A `WBump` is the `queued` shape. -/
theorem wrel_of_wbump {y z : ChainVM} (h : WBump y z) : WRel y z := by
  obtain ⟨w, rfl, rfl⟩ := h
  exact .queued w

/-! ### 1.2 The bundle at the grown window -/

/-- **Closed.**  `queued` transports `ChainW` from `(R, R)` to `(R+1, R+1)`;
only the grown block is needed. -/
theorem chainW_queued {raw : List (Fin 2)} {C R bud bud' : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    {w : GalilScaffoldChainWatch.State}
    (h : ChainW raw C R R bud false cc b xs (.watch w))
    (hblk : BlockOn raw cc b xs (C+1) (R+1)) :
    ChainW raw C (R+1) (R+1) bud' false cc b xs (.watch (GalilScaffoldChainWatch.queued w)) := by
  obtain ⟨hlag, hwin, hc, hcan, hmar, -⟩ := h
  obtain ⟨mach, lag, margin⟩ := w
  rcases lag with ⟨ps, ns⟩
  obtain ⟨hneg, hpos⟩ := hlag
  simp only at hneg hpos hc hcan hmar
  subst hneg
  refine ⟨⟨rfl, ?_⟩, hblk, hc, inc_canonical _ hcan, ?_, by simp⟩
  · show position mach.verifier + (inc (⟨ps, []⟩ : Counter)).pos.length = R + 1
    simp only [inc, List.length_cons]
    omega
  · show value (inc margin) + 4 * ((xs.length + 1 : ℕ) : ℤ) = ((R + 1 : ℕ) : ℤ) - C
    rw [inc_value]; push_cast at hmar ⊢; linarith

/-- **Closed.**  A positive lag inside the window gives `Good`. -/
theorem good_of_pos {raw : List (Fin 2)} {C E R bud : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    {w : GalilScaffoldChainWatch.State}
    (h : ChainW raw C E R bud false cc b xs (.watch w)) (hB : E < (encoded raw).length)
    (hR : R ≤ E) (hp : positive w.lag = true) : GalilScaffoldChainWatch.Good w := by
  obtain ⟨hlag, hwin, hc, -, -, -⟩ := h
  refine coreX_good (w := w) hc hwin hB ?_
  have h2 := hlag.2
  have h1 : 1 ≤ w.lag.pos.length := by
    cases hpl : w.lag.pos with
    | nil => simp [positive, hpl] at hp
    | cons u us => simp
  omega

/-! ### 1.3 One background step keeps the shape -/

/-- **Closed.**  The match credit on a watching chain commutes past one
background step, flipping between the two shapes of `WRel`.  The only input is
the bundle *at the grown window* for the credited side. -/
theorem wrel_step {raw : List (Fin 2)} {C R' bud : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    {y z y₁ : ChainVM} (hr : WRel y z) (hs : ChainStep y y₁)
    (hz : ChainW raw C R' R' bud false cc b xs z) (hB : R' < (encoded raw).length) :
    ∃ z₁, ChainStep z z₁ ∧ WRel y₁ z₁ := by
  cases hr with
  | queued w =>
    obtain ⟨mach, lag, margin⟩ := w
    rcases lag with ⟨ps, ns⟩
    cases hs with
    | watchStep _ w' hi =>
      cases hi with
      | idle hzp =>
        -- `positive ⟨ps, ns⟩ = false`, i.e. `ps = []`
        have hps : ps = [] := by
          cases ps with
          | nil => rfl
          | cons u us => simp [positive] at hzp
        subst hps
        cases ns with
        | nil =>
          -- the credited side has lag `1`: it *takes*, doing the immediate consume
          have hpq : positive (GalilScaffoldChainWatch.queued
              (⟨mach, ⟨[], []⟩, margin⟩ : GalilScaffoldChainWatch.State)).lag = true := rfl
          have hg := good_of_pos hz hB (le_refl _) hpq
          exact ⟨_, .watchStep _ _ (.take _ hpq hg), .immediate _⟩
        | cons n ns' =>
          have hpq : positive (GalilScaffoldChainWatch.queued
              (⟨mach, ⟨[], n :: ns'⟩, margin⟩ : GalilScaffoldChainWatch.State)).lag = false := rfl
          exact ⟨_, .watchStep _ _ (.idle _ hpq), .queued _⟩
      | take hp hg =>
        cases ps with
        | nil => simp [positive] at hp
        | cons u us =>
          cases ns with
          | nil =>
            have hpq : positive (GalilScaffoldChainWatch.queued
                (⟨mach, ⟨u :: us, []⟩, margin⟩ : GalilScaffoldChainWatch.State)).lag = true := rfl
            have hg' : GalilScaffoldChainWatch.Good (GalilScaffoldChainWatch.queued
                (⟨mach, ⟨u :: us, []⟩, margin⟩ : GalilScaffoldChainWatch.State)) := hg
            refine ⟨_, .watchStep _ _ (.take _ hpq hg'), ?_⟩
            cases u
            exact .queued _
          | cons n ns' =>
            have hpq : positive (GalilScaffoldChainWatch.queued
                (⟨mach, ⟨u :: us, n :: ns'⟩, margin⟩ : GalilScaffoldChainWatch.State)).lag
                = true := rfl
            have hg' : GalilScaffoldChainWatch.Good (GalilScaffoldChainWatch.queued
                (⟨mach, ⟨u :: us, n :: ns'⟩, margin⟩ : GalilScaffoldChainWatch.State)) := hg
            exact ⟨_, .watchStep _ _ (.take _ hpq hg'), .queued _⟩
  | immediate w =>
    cases hs with
    | watchStep _ w' hi =>
      cases hi with
      | idle hzp =>
        have hpq : positive (GalilScaffoldChainWatch.immediate w).lag = false := hzp
        exact ⟨_, .watchStep _ _ (.idle _ hpq), .immediate _⟩
      | take hp hg =>
        have hpq : positive (GalilScaffoldChainWatch.immediate w).lag = true := hp
        have hg' := good_of_pos hz hB (le_refl _) hpq
        exact ⟨_, .watchStep _ _ (.take _ hpq hg'), .immediate _⟩

/-! ### 1.4 The run, at the same length -/

/-- **Closed.**  A `ChainWRun` into `.watch` is transported along a `WRel` to a
run of the **same length** into some `.watch`, at radius `R+1` and the grown
window.  (The measure of Round 50's question is unchanged: neither shape of the
credit inserts or drops a background step.) -/
theorem wrel_run {raw : List (Fin 2)} {C R : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    (hblk : BlockOn raw cc b xs (C+1) (R+1)) (hB : R + 1 < (encoded raw).length) :
    ∀ (n : ℕ) (y w : ChainVM), ChainWRun raw C R R cc b xs n y w → (∃ v, w = ChainVM.watch v) →
      ∀ z, WRel y z → (∀ bud, ChainW raw C (R+1) (R+1) bud false cc b xs z) →
        ∃ v', ChainWRun raw C (R+1) (R+1) cc b xs n z (ChainVM.watch v') := by
  intro n
  induction n with
  | zero =>
    intro y w hrun hw z hr hzW
    cases hr with
    | queued w0 => exact ⟨GalilScaffoldChainWatch.queued w0, .zero _⟩
    | immediate w0 => exact ⟨GalilScaffoldChainWatch.immediate w0, .zero _⟩
  | succ n ih =>
    intro y w hrun hw z hr hzW
    obtain ⟨y₁, hstep, hwin, hrest⟩ := run_succ hrun
    obtain ⟨z₁, hstep', hr₁⟩ := wrel_step hr hstep (hzW 0) hB
    have hzW₁ : ∀ bud, ChainW raw C (R+1) (R+1) bud false cc b xs z₁ := by
      intro bud
      obtain ⟨z', hstep'', hz'⟩ := chainW_step (hzW (bud+1)) hB (le_refl _)
      have : z' = z₁ := PalPeg.GalilTickDet.chainStep_unique hstep'' hstep'
      rw [← this]; exact hz'
    obtain ⟨v', hrun'⟩ := ih y₁ w hrest hw z₁ hr₁ hzW₁
    exact ⟨v', .succ hstep' hzW₁ hrun'⟩

/-- **CLOSED — Round 50's `WatchTailC` (`CloseoutWatchRound50.lean:207`).**  Its
two inputs, the grown block and the length bound, are exactly what
`clockOneC_of_match` already has at the call site (`hblk'`, `hlen1`). -/
theorem watchTailC_of_coreX {raw : List (Fin 2)} {C R : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    (hblk : BlockOn raw cc b xs (C+1) (R+1)) (hB : R + 1 < (encoded raw).length) :
    WatchTailC raw C R cc b xs := by
  intro n y z w hwb hrun hw hwin
  obtain ⟨w0, rfl, rfl⟩ := hwb
  have hzW : ∀ bud, ChainW raw C (R+1) (R+1) bud false cc b xs
      (ChainVM.watch (GalilScaffoldChainWatch.queued w0)) :=
    fun bud => chainW_queued (hwin 0) hblk
  exact ⟨hzW, wrel_run hblk hB n _ w hrun hw _ (.queued w0) hzW⟩

/-! ## 2. `MatchQuantumC` without its `WatchTailC` conjunct -/

/-- **NAMED (open) — the machine-level match quantum at `clock = 1`, and
nothing else.**  Round 50's `MatchQuantumC` with the `WatchTailC` conjunct
deleted: the `Tick.scan_match` construction (comparison, `matched`,
`matchedPlace false`, `refresh`) together with the control transports (clock
reset, right head `+1`, centre and replay counter fixed, `matched_invariant'` /
`minv_match`, the `Leftmost`/`ScanInvariant`/`Frontier`/`ReplayRest`/`OutputRel`
fields at radius `R+1`) and the block growth `BlockOn … (C+1) (E+1)` from the
landing's own block data. -/
def MatchCoreC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (sT : GalilVM)
    (cc b : Fin 3) (xs : List (Fin 3)) (X : Control → GalilVM → Prop) : Prop :=
  ∀ (R : ℕ) (c' : Control) (t : GalilVM),
    LiveScanChain c' t → c'.clock = 1 → LandingData raw R sT cc b xs c' t →
    (∃ (c'' : Control) (t'' : GalilVM) (y : ChainVM),
        Tick (galilFrameS P q first) 2048 ⟨c', t⟩ ⟨c'', t''⟩ ∧
        c''.mode = Mode.scan ∧ c''.replaying = false ∧ 1 ≤ c''.clock ∧
        ChainStep t.chain y ∧ Bump y t''.chain ∧
        t''.center = t.center ∧ position t''.right = position sT.right + (R+1) ∧
        BlockOn raw cc b xs (position t.center + 1) (position sT.right + (R+1)) ∧
        t''.replay = reset ∧ MInv raw c'' t'' ∧
        Leftmost raw (position t''.right) (position t''.center) ∧
        ScanInvariant raw (position t''.center) (R+1) t''.left t''.right ∧
        Frontier t'' ∧ ReplayRest c'' t'' ∧ t''.remaining = sT.remaining ∧
        OutputRel raw c'' t'')
    ∨ X c' t

/-- **CLOSED — Round 50's `MatchQuantumC` from `MatchCoreC`.**  The deleted
conjunct is rebuilt by §1 out of the quantum's own data: the grown block is
`hblk` at `position t.right + 1` (a landing has `position t.right =
position sT.right + R`), and the length bound comes from the new right head's
`Represents` field, exactly as in `clockOneC_of_match`. -/
theorem matchQuantumC_of_tick (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (sT : GalilVM) (cc b : Fin 3) (xs : List (Fin 3)) (X : Control → GalilVM → Prop)
    (hc : MatchCoreC P q first raw sT cc b xs X) :
    MatchQuantumC P q first raw sT cc b xs X := by
  intro R c' t hlive hc1 hd
  rcases hc R c' t hlive hc1 hd with
    ⟨c1, t1, y, htick, hm1, hr1, hcl1, hstep, hbump, hcen, hpos, hblk, hrep1, hM1, hlm1,
      hsi1, hfr1, hrest1, hrem1, hout1⟩ | hx
  · have hE : position sT.right + R = position t.right := hd.2.2.1.symm
    have hblk' : BlockOn raw cc b xs (position t.center + 1) (position t.right + 1) := by
      rw [show position t.right + 1 = position sT.right + (R+1) from by omega]; exact hblk
    have hlen1 : position t.right + 1 < (encoded raw).length := by
      have h1 := PalPeg.CloseoutPackRun44.position_le_of_represents
        (w := raw) (p := t1.right) hsi1.rightRep
      rw [encoded_len] at *; omega
    exact Or.inl ⟨c1, t1, y, htick, hm1, hr1, hcl1, hstep, hbump, hcen, hpos, hblk,
      watchTailC_of_coreX hblk' hlen1, hrep1, hM1, hlm1, hsi1, hfr1, hrest1, hrem1, hout1⟩
  · exact Or.inr hx

/-- **`ClockOneC` from the machine-level quantum alone.** -/
theorem clockOneC_of_core (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (sT : GalilVM) (cc b : Fin 3) (xs : List (Fin 3)) (X : Control → GalilVM → Prop)
    (hc : MatchCoreC P q first raw sT cc b xs X) :
    ClockOneC P q first raw sT cc b xs X :=
  PalPeg.CloseoutWatchRound50.clockOneC_of_match P q first raw sT cc b xs X
    (matchQuantumC_of_tick P q first raw sT cc b xs X hc)

#print axioms watchTailC_of_coreX
#print axioms wrel_step
#print axioms wrel_run
#print axioms matchQuantumC_of_tick
#print axioms clockOneC_of_core

end PalPeg.CloseoutWatchRound53
