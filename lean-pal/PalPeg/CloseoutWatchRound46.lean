import PalPeg.CloseoutWatchRound43

/-!
# Closeout watch round 46 — the copy/back phase fits inside the clock

`CloseoutWatchRound43.ChainWatchPhaseC` is the residue of the replay-born
round: from a `.copy` / `.back` `ChainW` landing at clock `2048` the chain
reaches `.watch` in `n` background chain steps with `n + 1 ≤ c'.clock`.

Round 43 could not get the inequality from `ChainW`'s own cost clauses,
because they are guarded by `lim = true` and the landing carries
`lim = false`.  This round gets it from the **window data** instead: at
`lim = false` the structural part of `ChainW` still records

* `n ≤ xs.length + 1` (the copy counter against the window, `.copy`),
* `flat v = blockTokens cc b xs`, so `v.left.length ≤ xs.length + 1` (`.back`),
* `VerAt raw C ver` and `LagAt lag ver R`, so `lag.pos.length = R - C`,

and the `lim = true` cost of each phase is exactly `n + xs.length + 3 + lag`
(copy) resp. `v.left.length + 1 + lag` (back).  So the *false* invariant can be
upgraded to the *true* one at the explicit budget

  `2 * xs.length + 4 + (R - C)`                              (`chainW_true_of_window`)

and then `GalilReplaySpan.chainW_step` drives the budget down to `0`, where the
chain is necessarily `.watch` (`reach_watch`).  The phase therefore satisfies
`n ≤ 2 * xs.length + 4 + (R - C)`, and `n + 1 ≤ 2048` follows as soon as that
number is `≤ 2047`.

## The ONE hypothesis

`PhaseWindowC`: at such a landing the window fits the clock,

  `2 * xs.length + 4 + (position t.right - position t.center) ≤ 2047`

(together with the frame fact `position sT.right + R < (encoded raw).length`,
which `chainW_step` needs to read the input at the window end).  The first
conjunct is the real content: with `lag.pos.length = R_head - C` the radius
`d := R_head - C` of the landing and the semiperiod `xs.length + 1` are the
only free quantities, and `Canonical margin` alone does not sign the margin
identity `value margin + 4·(xs.length + 1) = R_head - C`, so neither
`xs.length` nor `d` is bounded here.  What the theory supplies is
`found_radius_le_two_period` (`R_f ≤ 2h`) with **no** bound on `h`; the
calibration `delay = 2048` needs `d ≤ 1363` once `4·(xs.length+1) ≤ d` holds,
i.e. a bound `h ≤ 681` on the period at a replay-born landing.  That bound is
not available, hence the hypothesis.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound46

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilReplayGeneral2 (VerAt LagAt flat)
open PalPeg.GalilBranchInvariants (blockTokens)
open PalPeg.CloseoutWatchRound40 (LiveScanChain)
open PalPeg.CloseoutWatchRound42 (LandingData)
open PalPeg.CloseoutWatchRound43 (ChainWRun ChainWatchPhaseC)
open PalPeg.GalilReplaySpan (ChainW)

variable {raw : List (Fin 2)} {C E R : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}

/-! ## 1. Relaxing `lim` -/

/-- **Closed.**  All cost clauses of `ChainW` are guarded by `lim = true`, so a
`ChainW` at any `lim` and budget gives one at `lim = false` and any budget. -/
theorem chainW_false {bud bud' : ℕ} {lim : Bool} {x : ChainVM}
    (h : ChainW raw C E R bud lim cc b xs x) : ChainW raw C E R bud' false cc b xs x := by
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

/-! ## 2. The window budget -/

/-- The block tape of a `.back` phase is the block, hence short. -/
theorem back_left_length {v : GalilScaffoldChainPeriod.Tape} (h : flat v = blockTokens cc b xs) :
    v.left.length ≤ xs.length + 1 := by
  rcases v with ⟨ls, f, rs⟩
  have h2 := congrArg List.length h
  simp [flat, blockTokens] at h2
  show ls.length ≤ xs.length + 1
  omega

/-- **Closed — the budget from the window.**  A `.copy` / `.back` `ChainW` at
`lim = false` is a `ChainW` at `lim = true` with the explicit window budget
`2 * xs.length + 4 + (R - C)`: the lag is exactly `R - C` (`VerAt` + `LagAt`),
the copy counter is `≤ xs.length + 1` and the rewind tape is `≤ xs.length + 1`
long. -/
theorem chainW_true_of_window {bud0 bud : ℕ} {x : ChainVM}
    (h : ChainW raw C E R bud0 false cc b xs x)
    (hb : 2 * xs.length + 4 + (R - C) ≤ bud) :
    (∃ w, x = ChainVM.watch w) ∨ ChainW raw C E R bud true cc b xs x := by
  cases x with
  | idle => exact h.elim
  | broken w => exact h.elim
  | watch w => exact Or.inl ⟨w, rfl⟩
  | copy t hh p v lag margin ver =>
    obtain ⟨h1, h2, h3, h4, n, u, d, q, h5, h6, h7, h8, h9, h10⟩ := h
    refine Or.inr ⟨h1, h2, h3, h4, n, u, d, q, h5, h6, h7, h8, h9, fun _ => ?_⟩
    have hlag : position ver + lag.pos.length = R := h2.2
    have hC : position ver = C := h1.2.2
    omega
  | back v hh lag margin ver =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    refine Or.inr ⟨h1, h2, h3, h4, h5, h6, fun _ => ?_⟩
    have hlag : position ver + lag.pos.length = R := h2.2
    have hC : position ver = C := h1.2.2
    have hv := back_left_length h4
    omega

/-! ## 3. Driving the budget to zero -/

/-- **Closed.**  At budget `0` a `ChainW` chain is already watching: every
other phase costs at least one background tick. -/
theorem watch_of_zero {x : ChainVM} (h : ChainW raw C E R 0 true cc b xs x) :
    ∃ w, x = ChainVM.watch w := by
  cases x with
  | idle => exact h.elim
  | broken w => exact h.elim
  | watch w => exact ⟨w, rfl⟩
  | copy t hh p v lag margin ver =>
    obtain ⟨-, -, -, -, n, u, d, q, -, -, -, -, -, h10⟩ := h
    have hcost := h10 rfl
    omega
  | back v hh lag margin ver =>
    obtain ⟨-, -, -, -, -, -, h7⟩ := h
    have hcost := h7 rfl
    omega

/-- **Closed — the phase run.**  A `ChainW` at `lim = true` and budget `bud`
reaches `.watch` in at most `bud` background chain steps, each step keeping
`ChainW` (at every `lim = false` budget, which is what `ChainWRun` records). -/
theorem reach_watch (hB : E < (encoded raw).length) (hR : R ≤ E) :
    ∀ (bud : ℕ) (x : ChainVM), ChainW raw C E R bud true cc b xs x →
      ∃ (n : ℕ) (w : GalilScaffoldChainWatch.State),
        n ≤ bud ∧ ChainWRun raw C E R cc b xs n x (ChainVM.watch w) := by
  intro bud
  induction bud with
  | zero =>
    intro x h
    obtain ⟨w, rfl⟩ := watch_of_zero h
    exact ⟨0, w, le_refl _, .zero _⟩
  | succ bud ih =>
    intro x h
    by_cases hw : ∃ w, x = ChainVM.watch w
    · obtain ⟨w, rfl⟩ := hw
      exact ⟨0, w, Nat.zero_le _, .zero _⟩
    · obtain ⟨y, hstep, hy⟩ := PalPeg.GalilReplaySpan.chainW_step h hB hR
      obtain ⟨n, w, hn, hrun⟩ := ih y hy
      exact ⟨n + 1, w, by omega, .succ hstep (fun _ => chainW_false hy) hrun⟩

/-! ## 4. The ONE hypothesis -/

/-- **NAMED (open) — the window of a replay-born landing fits the clock.**
The second conjunct is the phase-length bound of Round 43 read off the window
data (`n ≤ xs.length + 1`, `lag.pos.length = R_head - C`); the first is the
frame fact that the window end is a place of the input, which
`GalilReplaySpan.chainW_step` needs at `backDone`. -/
def PhaseWindowC (raw : List (Fin 2)) : Prop :=
  ∀ (R : ℕ) (sT : GalilVM) (c' : Control) (t : GalilVM) (cc b : Fin 3) (xs : List (Fin 3)),
    LiveScanChain c' t → c'.clock = 2048 → LandingData raw R sT cc b xs c' t →
    position sT.right + R < (encoded raw).length ∧
      2 * xs.length + 4 + (position t.right - position t.center) ≤ 2047

/-! ## 5. The target -/

/-- **`ChainWatchPhaseC` from the window bound.**  The upgrade of §2 turns the
`lim = false` landing into a `lim = true` one at the window budget, §3 drives
that budget to `.watch`, and the hypothesis says the budget is `≤ 2047`, i.e.
`n + 1 ≤ 2048 = c'.clock`. -/
theorem chainWatchPhaseC_of_window (raw : List (Fin 2)) (hwin : PhaseWindowC raw) :
    ChainWatchPhaseC raw := by
  intro R sT c' t cc b xs hlive hc hd
  obtain ⟨hlen, hfit⟩ := hwin R sT c' t cc b xs hlive hc hd
  obtain ⟨-, hW, hright, -⟩ := hd
  rcases chainW_true_of_window (bud := 2 * xs.length + 4 +
      (position t.right - position t.center)) hW (le_refl _) with ⟨w, hw⟩ | hT
  · exact ⟨0, w, by omega, by rw [hw]; exact .zero _⟩
  · obtain ⟨n, w, hn, hrun⟩ := reach_watch hlen (le_of_eq hright) _ _ hT
    exact ⟨n, w, by omega, hrun⟩

end PalPeg.CloseoutWatchRound46

#print axioms PalPeg.CloseoutWatchRound46.chainW_false
#print axioms PalPeg.CloseoutWatchRound46.back_left_length
#print axioms PalPeg.CloseoutWatchRound46.chainW_true_of_window
#print axioms PalPeg.CloseoutWatchRound46.watch_of_zero
#print axioms PalPeg.CloseoutWatchRound46.reach_watch
#print axioms PalPeg.CloseoutWatchRound46.chainWatchPhaseC_of_window
