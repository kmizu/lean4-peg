import PalPeg.CloseoutWatchRound42

/-!
# Closeout watch round 43 — the copy/back → watch reach residue

`CloseoutWatchRound42.ChainWatchReachC` is the mechanical residue of the
replay-born round: from a `ChainW` landing whose chain is still in `.copy` or
`.back`, the background ticks of the landing's own `count` phase carry the
chain to `.watch` with the landing bundle (`LandingData`) unchanged.

This round *builds that run*.  Everything mechanical is discharged here:

* a background tick can always be taken with a **chosen** chain successor
  (`background_chainStep`): the search effect of a non-idle chain is the
  stutter `vq = searchLens.get s` (`searchEffect`'s second disjunct, as in
  `GalilBranchInvariants2.searchEffect_exists`), and `chainAt false` on a
  non-idle chain is exactly `ChainTick false`, i.e. one `ChainStep`;
* the controller offers such a tick at every clock above one, by
  `Tick.scan_count` when R is available and `Tick.scan_wait` when it is not
  (`landing_step`), so the clock drops by at most one per chain step;
* the whole bundle is transported across it (`landing_step`): the background
  keeps `left`, `right`, `center`, `radius`, `remaining`, `replay`
  (`backgroundS_fields`) and the tick keeps `mode`, `replaying`, `output`,
  so `MInv` (`minv_same`), `Leftmost`, `ScanInvariant`, `Frontier`,
  `ReplayRest` and `OutputRel` (`outputRel_background`) all survive verbatim,
  and `ChainW`'s budget clause is vacuous at `lim = false`
  (`chainW_bud_false`), so the shrinking `budOf` costs nothing.

## The ONE hypothesis

What is *not* mechanical is the length of the copy/back phase against the
clock.  At `lim = false` the `ChainW` of the landing carries **no** cost
bound at all (the `bud` clauses of `GalilReplaySpan.ChainW` are guarded by
`lim = true`), so the invariant alone does not bound the number of
`copyBit` / `copyEnd` / `backStep` steps before `backDone`.  The inequality
needed is

  `n + 1 ≤ c'.clock`, i.e. `n ≤ 2047`,

where `n` is the number of chain steps from the landing's `.copy` / `.back`
chain to `.watch` — the phase is `xs.length + 2` copy steps plus at most
`xs.length + 2` rewind steps, and the landing's clock is the full
`delay = 2048`, so it fits, but the bound must come from the window data
(`BlockOn … (C+1) E`, `n ≤ xs.length + 1`), not from the `lim = false`
invariant used here.  It is named `ChainWatchPhaseC`, packaged with the
`ChainW` of each state along the way (`ChainWRun`), which
`GalilReplaySpan.chainW_step` supplies step by step.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound43

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply

open PalPeg.CloseoutWatchRun (LiveScanWatch)
open PalPeg.CloseoutWatchRound40 (LiveScanChain)
open PalPeg.CloseoutWatchRound42 (LandingData ChainWatchReachC)
open PalPeg.GalilReplaySpan (ChainW budOf)

/-! ## 1. `ChainW` at `lim = false` does not depend on the budget -/

/-- **Closed.**  Every budget clause of `ChainW` is guarded by `lim = true`,
so at `lim = false` the budget is irrelevant.  (`chainW_mono` only moves the
budget up; the run below moves it *down*, since `budOf` shrinks with the
clock.) -/
theorem chainW_bud_false {raw : List (Fin 2)} {C E R bud bud' : ℕ} {cc b : Fin 3}
    {xs : List (Fin 3)} {x : ChainVM} (h : ChainW raw C E R bud false cc b xs x) :
    ChainW raw C E R bud' false cc b xs x := by
  cases x with
  | idle => exact h.elim
  | broken w => exact h.elim
  | copy t hh p v lag margin ver =>
    obtain ⟨h1, h2, h3, h4, n, u, d, q, h5, h6, h7, h8, h9, h10⟩ := h
    exact ⟨h1, h2, h3, h4, n, u, d, q, h5, h6, h7, h8, h9, fun hl => Bool.noConfusion hl⟩
  | back v hh lag margin ver =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, fun hl => Bool.noConfusion hl⟩
  | watch w =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, h2, h3, h4, h5, fun hl => Bool.noConfusion hl⟩

/-! ## 2. A background tick with a chosen chain successor -/

/-- **Closed.**  On a non-idle chain the background tick is free to take any
`ChainStep`. -/
theorem background_chainStep (P : Shared) (q : ℕ) (first : Fin 9) {s : GalilVM} {y : ChainVM}
    (hne : s.chain ≠ ChainVM.idle) (hstep : ChainStep s.chain y) :
    ∃ s', (galilFrameS P q first).background s s' ∧ s'.chain = y := by
  refine ⟨searchLens.set (scanLens.set s ⟨s.left, s.right, y⟩) (searchLens.get s), ?_, rfl⟩
  show backgroundS P q first s _
  refine ⟨rfl, rfl, Or.inr ⟨hne, rfl⟩, Or.inl ⟨hne, ⟨y, hstep, rfl⟩⟩, ?_⟩
  rw [afterBirth_of_ne_idle hne]
  rfl

/-! ## 3. A `ChainW`-run of the chain -/

/-- A run of background chain steps, each landing in `ChainW` (at every
budget, which is what `lim = false` gives).  This is what
`GalilReplaySpan.chainW_step` produces step by step. -/
inductive ChainWRun (raw : List (Fin 2)) (C E R : ℕ) (cc b : Fin 3) (xs : List (Fin 3)) :
    ℕ → ChainVM → ChainVM → Prop
  | zero (x : ChainVM) : ChainWRun raw C E R cc b xs 0 x x
  | succ {n : ℕ} {x y z : ChainVM} (h : ChainStep x y)
      (hw : ∀ bud, ChainW raw C E R bud false cc b xs y)
      (hr : ChainWRun raw C E R cc b xs n y z) : ChainWRun raw C E R cc b xs (n+1) x z

/-! ## 4. The ONE hypothesis: the copy/back phase fits inside the clock -/

/-- **NAMED (open) — the phase length against the clock.**  From a `ChainW`
landing at the full clock, the chain reaches `.watch` in `n` background chain
steps with `n + 1 ≤ c'.clock` (i.e. `n ≤ 2047`), each step keeping `ChainW`.
The steps themselves are `GalilReplaySpan.chainW_step`; the *inequality* is
what is open, because `LandingData` carries `ChainW` at `lim = false`, whose
budget clauses are vacuous. -/
def ChainWatchPhaseC (raw : List (Fin 2)) : Prop :=
  ∀ (R : ℕ) (sT : GalilVM) (c' : Control) (t : GalilVM) (cc b : Fin 3) (xs : List (Fin 3)),
    LiveScanChain c' t → c'.clock = 2048 → LandingData raw R sT cc b xs c' t →
    ∃ (n : ℕ) (w : GalilScaffoldChainWatch.State),
      n + 1 ≤ c'.clock ∧
      ChainWRun raw (position t.center) (position sT.right + R) (position t.right) cc b xs n
        t.chain (ChainVM.watch w)

/-! ## 5. One tick of the phase, with the bundle transported -/

/-- **Closed.**  One background tick along a chain step: `scan_count` when R
is available, `scan_wait` when it is not; the clock drops by at most one and
the entire landing bundle survives. -/
theorem landing_step (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (R : ℕ) (sT : GalilVM) (cc b : Fin 3) (xs : List (Fin 3))
    {c' : Control} {t : GalilVM} {y : ChainVM}
    (hm : c'.mode = Mode.scan) (hr : c'.replaying = false) (hc : 1 < c'.clock)
    (hne : t.chain ≠ ChainVM.idle) (hstep : ChainStep t.chain y)
    (hy : ∀ bud, ChainW raw (position t.center) (position sT.right + R) (position t.right)
      bud false cc b xs y)
    (hd : LandingData raw R sT cc b xs c' t) :
    ∃ (c'' : Control) (t'' : GalilVM),
      Tick (galilFrameS P q first) 2048 ⟨c', t⟩ ⟨c'', t''⟩ ∧
      c''.mode = Mode.scan ∧ c''.replaying = false ∧ c'.clock - 1 ≤ c''.clock ∧
      t''.chain = y ∧
      position t''.center = position t.center ∧ position t''.right = position t.right ∧
      LandingData raw R sT cc b xs c'' t'' := by
  classical
  obtain ⟨hrep, hW, hB, hM, hlm, hi, hcen, hfr, hrest, hrem, hout⟩ := hd
  obtain ⟨s', hb, hch⟩ := background_chainStep P q first hne hstep
  obtain ⟨hl', hr', -, hcen', -, hrad', -, -, hremm', hrepl', -, -⟩ :=
    backgroundS_fields P q first hb
  have bundle : ∀ c'' : Control, c''.mode = Mode.scan → c''.replaying = false →
      c''.output = c'.output → LandingData raw R sT cc b xs c'' s' := by
    intro c'' hm'' hr'' ho''
    refine ⟨by rw [hrepl']; exact hrep, ?_, by rw [hr']; exact hB, ?_, ?_, ?_,
      by rw [hcen']; exact hcen, ?_, ?_, by rw [hremm']; exact hrem, ?_⟩
    · rw [hch, hcen', hr']
      exact chainW_bud_false (hy 0)
    · exact minv_same (by rw [hr'', hr]) hr' hcen' hrepl' hM
    · rw [hr', hcen']; exact hlm
    · rw [hl', hr', hcen']; exact hi
    · intro m hm0; rw [hr']; rw [hrepl'] at hm0; exact hfr m hm0
    · intro h0; rw [hrepl']; exact hrest (Or.inl hr)
    · exact outputRel_background raw P q first hb ho'' hout
  by_cases hav : (galilFrameS P q first).available t
  · exact ⟨{c' with clock := c'.clock - 1}, s',
      Tick.scan_count c' t s' hm (Or.inr hav) hc hb, hm, hr, le_refl _, hch,
      by rw [hcen'], by rw [hr'], bundle _ hm hr rfl⟩
  · exact ⟨c', s', Tick.scan_wait c' t s' hm ⟨hr, hav⟩ hb, hm, hr, by omega, hch,
      by rw [hcen'], by rw [hr'], bundle _ hm hr rfl⟩

/-! ## 6. The run of the whole phase -/

/-- **Closed.**  A `ChainWRun` of length `n` that fits inside the clock
(`n + 1 ≤ c'.clock`) is realised as a `StepsAll` run of `n` background ticks
with the landing bundle transported and the clock still positive. -/
theorem phase_run (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (R : ℕ) (sT : GalilVM) (cc b : Fin 3) (xs : List (Fin 3)) (C E Rc : ℕ) :
    ∀ {n : ℕ} {x z : ChainVM}, ChainWRun raw C E Rc cc b xs n x z →
      ∀ {c' : Control} {t : GalilVM}, c'.mode = Mode.scan → c'.replaying = false →
        n + 1 ≤ c'.clock → t.chain = x → position t.center = C → position t.right = Rc →
        position sT.right + R = E → LandingData raw R sT cc b xs c' t →
        ∃ (c'' : Control) (t'' : GalilVM),
          StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) n ⟨c', t⟩ ⟨c'', t''⟩ ∧
          c''.mode = Mode.scan ∧ c''.replaying = false ∧ 1 ≤ c''.clock ∧ t''.chain = z ∧
          LandingData raw R sT cc b xs c'' t'' := by
  intro n x z hrun
  induction hrun with
  | zero x =>
    intro c' t hm hr hcl hx _ _ _ hd
    exact ⟨c', t, .zero _ (fun _ _ => hd.2.2.2.2.2.2.2.2.2.2), hm, hr, by omega, hx, hd⟩
  | @succ n x y z hstep hw hrr ih =>
    intro c' t hm hr hcl hx hC hR hE hd
    have hne : t.chain ≠ ChainVM.idle := by
      rw [hx]
      intro e
      rw [e] at hstep
      cases hstep
      exact (hw 0).elim
    have hy : ∀ bud, ChainW raw (position t.center) (position sT.right + R) (position t.right)
        bud false cc b xs y := by
      intro bud; rw [hC, hR, hE]; exact hw bud
    have hsound : SoundScanNR raw ⟨c', t⟩ := fun _ _ => hd.2.2.2.2.2.2.2.2.2.2
    obtain ⟨c1, t1, htick, hm1, hr1, hlo, hch1, hC1, hR1, hd1⟩ :=
      landing_step P q first raw R sT cc b xs hm hr (by omega) hne (hx ▸ hstep) hy hd
    obtain ⟨c2, t2, hsteps, hm2, hr2, hcl2, hz2, hd2⟩ :=
      ih hm1 hr1 (by omega) hch1 (by rw [hC1, hC]) (by rw [hR1, hR]) hE hd1
    exact ⟨c2, t2, .succ hsound htick hsteps, hm2, hr2, hcl2, hz2, hd2⟩

/-! ## 7. The target -/

/-- **`ChainWatchReachC` from the phase-length hypothesis.**  The run
construction is entirely mechanical (§2, §5, §6); the only thing assumed is
that the copy/back phase fits inside the landing's clock (§4). -/
theorem chainWatchReachC_of_background (P : Shared) (q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (hphase : ChainWatchPhaseC raw) :
    ChainWatchReachC P q first raw := by
  intro R sT c' t cc b xs hlive hc hd
  obtain ⟨n, w, hn, hrun⟩ := hphase R sT c' t cc b xs hlive hc hd
  obtain ⟨c'', t'', hsteps, hm'', hr'', hcl'', hch'', hd''⟩ :=
    phase_run P q first raw R sT cc b xs (position t.center) (position sT.right + R)
      (position t.right) hrun hlive.1 hlive.2.1 hn rfl rfl rfl rfl hd
  exact ⟨n, c'', t'', hsteps, ⟨hm'', hr'', hcl'', w, hch''⟩, hd''⟩

end PalPeg.CloseoutWatchRound43

#print axioms PalPeg.CloseoutWatchRound43.chainW_bud_false
#print axioms PalPeg.CloseoutWatchRound43.background_chainStep
#print axioms PalPeg.CloseoutWatchRound43.landing_step
#print axioms PalPeg.CloseoutWatchRound43.phase_run
#print axioms PalPeg.CloseoutWatchRound43.chainWatchReachC_of_background
