import PalPeg.CloseoutWatchRound48
import PalPeg.CloseoutPackRun44

/-!
# Closeout watch round 50 — discharging Round 48's two hypotheses

`CloseoutWatchRound48.chainWatchReachM_of_background` (`:230`) needs exactly two
inputs, `WindowEndC` (`:116`) and `ClockOneC` (`:159`).  This round pays the
first **in full** and reduces the match half of the second to two machine-level
quanta.

## §1 `WindowEndC` is free

The landing bundle already carries `ScanInvariant raw (position t.center) R
t.left t.right`, whose field `rightRep` is
`GalilScaffoldInputTrace.Represents t.right.head raw`.
`CloseoutPackRun44.position_le_of_represents` (`:47`) then bounds
`position t.right ≤ 2 * raw.length`, while `(encoded raw).length =
2 * raw.length + 1`.  With the bundle's own `position t.right =
position sT.right + R` this *is* `position sT.right + R < (encoded raw).length`
— strictly, with one cell to spare, and with **no `canRight` side condition**:
the bound `≤ 2·|raw|` against a length `2·|raw| + 1` already makes the
represented head a legal index.  `WindowEndC` closes with **no hypothesis at
all** (`windowEndC_free`, §1).

## §2 the match half of `ClockOneC`

`E` occurs in `GalilReplaySpan.ChainW` (`:304–320`) **only** through
`BlockOn raw cc b xs (C+1) E`, so the window end can be reset freely once the
new `BlockOn` is available (`chainW_setE`); and at `lim = false` the budget
field is vacuous (`chainW_setBud`).  `GalilReplaySpan.chainW_matched` (`:442`)
then supplies the credit: the bundle moves from radius `R` to `R+1` at the
grown window, and its `R + 1 ≤ E` is met **on the nose**, because a landing's
window end and right head coincide.

For the *run tail* the credit is, on a `.copy`/`.back` state, nothing but
`inc lag` / `inc margin` — the relation `Bump` of §2.3.  Its commutation past
one background step (`bump_step`) is proved here for `copyBit` (this is where
`inc (decFour m) = decFour (inc m)` is needed, §2.2), `copyEnd` and `backStep`;
`backDone` lands on `.watch` and leaves the `Bump` world, reported as `WBump`.

**Where it stops.**  On a `.watch` state the credit is *not* the field bump:
`chainW_matched`'s watch branch takes `Outer.queued` only when the lag is
non-zero and `Outer.immediate` (a `consume`!) otherwise
(`GalilReplaySpan.lean:468–496`), and even for `queued` the following
`Internal` branches on `positive s.lag`, which `inc` can flip.  The whole watch
suffix of the run is therefore the single named hypothesis `WatchTailC` (§2.4).
The mismatch half of `ClockOneC` stays the abstract `X`, routed by Round 48's
`ExitX`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound50

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilReplaySpan (ChainW BlockOn budOf chainW_matched chainW_mono)
open PalPeg.CloseoutWatchRound42 (LandingData)
open PalPeg.CloseoutWatchRound43 (ChainWRun)
open PalPeg.CloseoutWatchRound48 (WindowEndC ClockOneC run_succ run_zero)
open PalPeg.CloseoutWatchRound40 (LiveScanChain)

/-! ## 1. `WindowEndC` for free -/

/-- **Closed.**  The encoded word has odd length `2·|raw| + 1`. -/
theorem encoded_len (raw : List (Fin 2)) : (encoded raw).length = 2 * raw.length + 1 := by
  simp [encoded, pairs_length]

/-- **Closed.**  A landing's right head is strictly a place of the input. -/
theorem landing_right_lt {raw : List (Fin 2)} {R : ℕ} {sT : GalilVM} {cc b : Fin 3}
    {xs : List (Fin 3)} {c' : Control} {t : GalilVM}
    (hd : LandingData raw R sT cc b xs c' t) :
    position t.right < (encoded raw).length := by
  have hrep := hd.2.2.2.2.2.1.rightRep
  have hle := PalPeg.CloseoutPackRun44.position_le_of_represents (w := raw) (p := t.right) hrep
  rw [encoded_len]; omega

/-- **CLOSED — Round 48's `WindowEndC` (`CloseoutWatchRound48.lean:116`), with
no hypothesis whatsoever.** -/
theorem windowEndC_free (raw : List (Fin 2)) (sT : GalilVM) : WindowEndC raw sT := by
  intro R c' t cc b xs hd
  have h := landing_right_lt hd
  rw [hd.2.2.1] at h
  exact h

/-! ## 2. The match half of `ClockOneC` -/

/-! ### 2.1 `E` and `bud` are free parameters of `ChainW` at `lim = false` -/

/-- **Closed.**  `E` enters `ChainW` only through `BlockOn … (C+1) E`. -/
theorem chainW_setE {raw : List (Fin 2)} {C E E' R bud : ℕ} {lim : Bool} {cc b : Fin 3}
    {xs : List (Fin 3)} {x : ChainVM} (h : ChainW raw C E R bud lim cc b xs x)
    (hb : BlockOn raw cc b xs (C+1) E') : ChainW raw C E' R bud lim cc b xs x := by
  cases x with
  | idle => exact h.elim
  | broken w => exact h.elim
  | copy t hh p v lag margin ver =>
    obtain ⟨h1, h2, -, h4, n, u, d, q, h5, h6, h7, h8, h9, h10⟩ := h
    exact ⟨h1, h2, hb, h4, n, u, d, q, h5, h6, h7, h8, h9, h10⟩
  | back v hh lag margin ver =>
    obtain ⟨h1, h2, -, h4, h5, h6, h7⟩ := h
    exact ⟨h1, h2, hb, h4, h5, h6, h7⟩
  | watch w =>
    obtain ⟨h1, -, h3, h4, h5, h6⟩ := h
    exact ⟨h1, hb, h3, h4, h5, h6⟩

/-- **Closed.**  At `lim = false` the budget clause is vacuous. -/
theorem chainW_setBud {raw : List (Fin 2)} {C E R bud bud' : ℕ} {cc b : Fin 3}
    {xs : List (Fin 3)} {x : ChainVM} (h : ChainW raw C E R bud false cc b xs x) :
    ChainW raw C E R bud' false cc b xs x := by
  cases x with
  | idle => exact h.elim
  | broken w => exact h.elim
  | copy t hh p v lag margin ver =>
    obtain ⟨h1, h2, h3, h4, n, u, d, q, h5, h6, h7, h8, h9, -⟩ := h
    exact ⟨h1, h2, h3, h4, n, u, d, q, h5, h6, h7, h8, h9, by simp⟩
  | back v hh lag margin ver =>
    obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, by simp⟩
  | watch w =>
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
    exact ⟨h1, h2, h3, h4, h5, by simp⟩

/-! ### 2.2 The credit commutes with the copy step's debit -/

/-- **Closed.**  `inc` and `dec` commute on the two-stack counter. -/
theorem inc_dec_comm (c : Counter) : inc (dec c) = dec (inc c) := by
  rcases c with ⟨ps, ns⟩
  cases ps <;> cases ns <;> rfl

/-- **Closed.**  Hence `inc` commutes with the copy step's four-credit debit. -/
theorem inc_decFour_comm (c : Counter) :
    inc (GalilScaffoldChainCredits.decFour c) = GalilScaffoldChainCredits.decFour (inc c) := by
  simp only [GalilScaffoldChainCredits.decFour, inc_dec_comm]

/-! ### 2.3 `Bump`: the match credit on a `.copy`/`.back` chain -/

/-- The match credit on the states where it really is a field bump. -/
inductive Bump : ChainVM → ChainVM → Prop
  | copy (t h p v lag margin ver) :
      Bump (.copy t h p v lag margin ver) (.copy t h p v (inc lag) (inc margin) ver)
  | back (v h lag margin ver) :
      Bump (.back v h lag margin ver) (.back v h (inc lag) (inc margin) ver)

/-- The same bump on a watch state — the shape `backDone` produces, and exactly
`GalilScaffoldChainWatch.queued`. -/
def WBump (y z : ChainVM) : Prop :=
  ∃ w : GalilScaffoldChainWatch.State,
    y = ChainVM.watch w ∧ z = ChainVM.watch (GalilScaffoldChainWatch.queued w)

/-- **Closed.**  A `Bump` *is* the match credit `ChainMatched`. -/
theorem matched_of_bump {y z : ChainVM} (h : Bump y z) : ChainMatched y z := by
  cases h with
  | copy => exact .copy _ _ _ _ _ _ _
  | back => exact .back _ _ _ _ _

/-- **Closed.**  `Bump` transports `ChainW` from the landing's window
`(E = R)` to the grown window `(E = R+1)` at radius `R+1`.  The window growth
is the only input; the budget is free because `lim = false`. -/
theorem chainW_bump {raw : List (Fin 2)} {C R bud bud' : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    {u u' : ChainVM} (hb : Bump u u') (hu : ChainW raw C R R bud false cc b xs u)
    (hblk : BlockOn raw cc b xs (C+1) (R+1)) (hlt : R + 1 < (encoded raw).length) :
    ChainW raw C (R+1) (R+1) bud' false cc b xs u' := by
  obtain ⟨z0, hm0, hz0⟩ :=
    chainW_matched (E := R+1) (chainW_setE hu hblk) hlt (le_refl _)
  have hzz : z0 = u' := PalPeg.GalilTickDet.chainMatched_unique hm0 (matched_of_bump hb)
  subst hzz
  exact chainW_setBud hz0

/-! ### 2.4 The commutation past one background step -/

/-- **Closed.**  The match credit commutes past one background chain step, as
long as the step stays inside the `.copy`/`.back` world; `backDone` leaves it
and is reported as a `WBump`. -/
theorem bump_step {y z y₁ : ChainVM} (hb : Bump y z) (hs : ChainStep y y₁) :
    ∃ z₁, ChainStep z z₁ ∧ (Bump y₁ z₁ ∨ WBump y₁ z₁) := by
  cases hb with
  | copy t hh p v lag margin ver =>
    cases hs with
    | copyBit t hh p v lag margin ver a one legal present =>
      refine ⟨_, .copyBit _ _ _ _ _ _ _ _ one legal present, Or.inl ?_⟩
      rw [← inc_decFour_comm]
      exact .copy _ _ _ _ _ _ _
    | copyEnd t hh p v lag margin ver bb hleft hp hv =>
      exact ⟨_, .copyEnd _ _ _ _ _ _ _ _ hleft hp hv, Or.inl (.back _ _ _ _ _)⟩
  | back v hh lag margin ver =>
    cases hs with
    | backStep v hh lag margin ver hf =>
      exact ⟨_, .backStep _ _ _ _ _ hf, Or.inl (.back _ _ _ _ _)⟩
    | backDone v hh lag margin ver hf =>
      exact ⟨_, .backDone _ _ _ _ _ hf, Or.inr ⟨_, rfl, rfl⟩⟩

/-- **NAMED (open) — the watch suffix of the run.**  Once the chain is
watching, the match credit is no longer a field bump: `chainW_matched`'s watch
branch takes `Outer.queued` only when the lag is non-zero and `Outer.immediate`
(a `consume`) otherwise (`GalilReplaySpan.lean:468–496`), and even after
`queued` the next `Internal` branches on `positive s.lag`, which `inc` flips at
a `reset` lag.  So the whole watch-to-watch tail is stated abstractly here.
Supplier: `GalilReplaySpan.coreX_good` — the same fact `chainW_matched` uses to
build `Outer.immediate` — plus `chainW_step` at `.watch`. -/
def WatchTailC (raw : List (Fin 2)) (C R : ℕ) (cc b : Fin 3) (xs : List (Fin 3)) : Prop :=
  ∀ (n : ℕ) (y z w : ChainVM), WBump y z →
    ChainWRun raw C R R cc b xs n y w → (∃ v, w = ChainVM.watch v) →
    (∀ bud, ChainW raw C R R bud false cc b xs y) →
    (∀ bud, ChainW raw C (R+1) (R+1) bud false cc b xs z) ∧
      ∃ v', ChainWRun raw C (R+1) (R+1) cc b xs n z (ChainVM.watch v')

/-! ### 2.5 The run tail -/

/-- **Closed modulo `WatchTailC`.**  A `ChainWRun` into `.watch` is transported
along a `Bump` to a run of the *same length* into some `.watch`, at radius
`R+1` and the grown window. -/
theorem chainWRun_bump {raw : List (Fin 2)} {C R : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    (hwt : WatchTailC raw C R cc b xs)
    (hblk : BlockOn raw cc b xs (C+1) (R+1)) (hlt : R + 1 < (encoded raw).length) :
    ∀ (n : ℕ) (y w : ChainVM), ChainWRun raw C R R cc b xs n y w →
      (∃ v, w = ChainVM.watch v) →
      ∀ z, Bump y z → ∃ v', ChainWRun raw C (R+1) (R+1) cc b xs n z (ChainVM.watch v') := by
  intro n
  induction n with
  | zero =>
    intro y w hrun hw z hb
    obtain ⟨v, hv⟩ := hw
    have hy : y = w := run_zero hrun
    subst hy; subst hv
    cases hb
  | succ n ih =>
    intro y w hrun hw z hb
    obtain ⟨y₁, hstep, hwin, hrest⟩ := run_succ hrun
    obtain ⟨z₁, hstep', hcase⟩ := bump_step hb hstep
    rcases hcase with hb₁ | hw₁
    · obtain ⟨v', hrun'⟩ := ih y₁ w hrest hw z₁ hb₁
      exact ⟨v', .succ hstep' (fun bud => chainW_bump hb₁ (hwin bud) hblk hlt) hrun'⟩
    · obtain ⟨hz, v', hrun'⟩ := hwt n y₁ z₁ w hw₁ hrest hw hwin
      exact ⟨v', .succ hstep' hz hrun'⟩

/-! ## 3. `ClockOneC` from the match quantum -/

/-- **NAMED (open) — the machine-level match quantum at `clock = 1`.**  All the
*control* content of `ClockOneC`'s match branch: the comparison tick exists, it
resets the clock, advances the right head by one, leaves the centre, the replay
counter (`matchedPlace false s' s'' : s'' = s'`) and the block alone, carries
the non-chain landing fields to radius `R + 1` (`matched_invariant'`,
`minv_match`), and grows the block window by the newly matched cell —
`BlockOn raw cc b xs (position t.center + 1) (position sT.right + R + 1)`.
The chain half of the tick is `ChainTick true`: the background step of
`ChainStep`, then the credit, handed over here as a `Bump`. -/
def MatchQuantumC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (sT : GalilVM)
    (cc b : Fin 3) (xs : List (Fin 3)) (X : Control → GalilVM → Prop) : Prop :=
  ∀ (R : ℕ) (c' : Control) (t : GalilVM),
    LiveScanChain c' t → c'.clock = 1 → LandingData raw R sT cc b xs c' t →
    (∃ (c'' : Control) (t'' : GalilVM) (y : ChainVM),
        Tick (galilFrameS P q first) 2048 ⟨c', t⟩ ⟨c'', t''⟩ ∧
        c''.mode = Mode.scan ∧ c''.replaying = false ∧ 1 ≤ c''.clock ∧
        ChainStep t.chain y ∧ Bump y t''.chain ∧
        t''.center = t.center ∧ position t''.right = position sT.right + (R+1) ∧
        BlockOn raw cc b xs (position t.center + 1) (position sT.right + (R+1)) ∧
        WatchTailC raw (position t.center) (position t.right) cc b xs ∧
        t''.replay = reset ∧ MInv raw c'' t'' ∧
        Leftmost raw (position t''.right) (position t''.center) ∧
        ScanInvariant raw (position t''.center) (R+1) t''.left t''.right ∧
        Frontier t'' ∧ ReplayRest c'' t'' ∧ t''.remaining = sT.remaining ∧
        OutputRel raw c'' t'')
    ∨ X c' t

/-- **CLOSED modulo `MatchQuantumC` — Round 48's `ClockOneC`
(`CloseoutWatchRound48.lean:159`).**  The bundle at the new landing: the window
is reset by `chainW_setE`, the radius by `chainW_matched` (its `R + 1 ≤ E`
holds on the nose because a landing's window end and right head coincide), and
the remaining run is transported by `chainWRun_bump`. -/
theorem clockOneC_of_match (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (sT : GalilVM) (cc b : Fin 3) (xs : List (Fin 3)) (X : Control → GalilVM → Prop)
    (hmq : MatchQuantumC P q first raw sT cc b xs X) :
    ClockOneC P q first raw sT cc b xs X := by
  intro R n c' t w hlive hc1 hd hrun
  rcases hmq R c' t hlive hc1 hd with
    ⟨c1, t1, y, htick, hm1, hr1, hcl1, hstep, hbump, hcen, hpos, hblk, hwt, hrep1, hM1, hlm1,
      hsi1, hfr1, hrest1, hrem1, hout1⟩ | hx
  · obtain ⟨y', hstep', hwin, hrest⟩ := run_succ hrun
    have hy : y' = y := PalPeg.GalilTickDet.chainStep_unique hstep' hstep
    subst hy
    have hE : position sT.right + R = position t.right := hd.2.2.1.symm
    have hlen : position t.right < (encoded raw).length := landing_right_lt hd
    rw [hE] at hwin hrest
    have hblk' : BlockOn raw cc b xs (position t.center + 1) (position t.right + 1) := by
      rw [show position t.right + 1 = position sT.right + (R+1) from by omega]; exact hblk
    have hpos' : position t1.right = position t.right + 1 := by omega
    have hlen1 : position t.right + 1 < (encoded raw).length := by
      have h1 := PalPeg.CloseoutPackRun44.position_le_of_represents
        (w := raw) (p := t1.right) hsi1.rightRep
      rw [encoded_len] at *; omega
    -- the transported run
    obtain ⟨v', hrun'⟩ :=
      chainWRun_bump (C := position t.center) (R := position t.right) hwt
        hblk' hlen1 n y' (ChainVM.watch w) hrest ⟨w, rfl⟩ t1.chain hbump
    -- and the transported invariant at the new landing
    have hWnew : ∀ bud, ChainW raw (position t.center) (position t.right + 1)
        (position t.right + 1) bud false cc b xs t1.chain :=
      fun bud => chainW_bump hbump (hwin bud) hblk' hlen1
    refine Or.inl ⟨c1, t1, v', htick, hm1, hr1, hcl1, ⟨hrep1, ?_, hpos, hM1, hlm1, hsi1,
      hcen.trans hd.2.2.2.2.2.2.1, hfr1, hrest1, hrem1, hout1⟩, ?_⟩
    · rw [hcen, hpos', show position sT.right + (R+1) = position t.right + 1 from by omega]
      exact hWnew _
    · rw [hcen, hpos', show position sT.right + (R+1) = position t.right + 1 from by omega]
      exact hrun'
  · exact Or.inr hx

#print axioms windowEndC_free
#print axioms chainW_setE
#print axioms chainW_bump
#print axioms bump_step
#print axioms chainWRun_bump
#print axioms clockOneC_of_match

end PalPeg.CloseoutWatchRound50
