import PalPeg.GalilScaffoldTopRoundS

/-!
# Chained controller rounds

`Rounds m c s c' s'`: `m` consecutive controller rounds (`round_next` data),
each starting in scan mode at the exact control the previous shift exit
produced. Under the `periodOnly`/lag-zero watch start the chain lifts to
`Steps` of `galilFrameS` and projects to `CompareRounds h … m …`, whose
`rounds_origin` then carries the read origin (`Entry`) across the rounds.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- A chain shift keeps the watch lag. -/
theorem chain_shift_lag {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : Counter} {n : ℕ} (hr : ChainShiftRun s w cycle n t v finish) :
    v.lag = w.lag := by
  induction hr with
  | stop s w cycle => rfl
  | next s w cycle he hc hl hl' rest ih => exact ih

/-- Rounds compose. -/
theorem compareRounds_append {h : ℕ} {a b : OnlyCompareState} {i : ℕ}
    (r1 : CompareRounds h a i b) : ∀ {c : OnlyCompareState} {j : ℕ}, CompareRounds h b j c →
      CompareRounds h a (i+j) c := by
  induction r1 with
  | stop s => intro c j r2; simpa using r2
  | next s run hend hc hprediction hlen hrun hchain rest ih =>
    intro c j r2
    rw [Nat.add_right_comm]
    exact .next s run hend hc hprediction hlen hrun hchain (ih r2)

inductive Rounds (P : Shared) (q : ℕ) (first : Fin 9) (delay h : ℕ) :
    ℕ → Control → GalilVM → Control → GalilVM → Prop
  | stop (c : Control) (s : GalilVM) : Rounds P q first delay h 0 c s c s
  | next {m : ℕ} (c : Control) (s : GalilVM) {n : ℕ} {c1 : Control} {s1 : GalilVM}
      (hseg : ScanSeg P q first delay n c s c1 s1)
      (hm1 : c1.mode = .scan) (hr1 : c1.replaying = false) (hc1 : c1.clock = 1)
      (w : GalilScaffoldChainWatch.State) (hs1 : s1.chain = .watch w)
      (hav : canRight s1.right) (vs : ScanVM) (vq : SearchVM)
      (hcmp : (galilFrame P q first).compare s1 (scanLens.set s1 vs))
      (hmis : ¬ (galilFrame P q first).matched (scanLens.set s1 vs))
      (hq : searchEffect P false s1 vq)
      (hend : singlePositive s1.cycle = true)
      (hpred : read (right s1.right) = GalilScaffoldChainConsume.symbol w.machine.control.period.focus)
      (hlen : Canonical s1.length)
      (hg : P.shiftGuard (afterMismatch s1 vs vq))
      (s2 : GalilVM) (hb : P.beginShift (afterMismatch s1 vs vq) s2)
      (hs2 : beginShiftVM h w (afterMismatch s1 vs vq) s2) (hi2 : CopyIdle s2)
      {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
      (hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
        (GalilScaffoldChainWatch.immediate w) reset h t' v cycle)
      (o : Bool)
      (ho : refresh (galilFrameS P q first) (shiftLens.set s2 ⟨t', .watch v, cycle⟩) c1.output o)
      {c' : Control} {s' : GalilVM}
      (rest : Rounds P q first delay h m {c1 with mode := .scan, clock := delay, output := o}
        (shiftLens.set s2 ⟨t', .watch v, cycle⟩) c' s') :
      Rounds P q first delay h (m+1) c s c' s'

/-- Chained rounds are controller steps and project to `CompareRounds`. -/
theorem rounds_lift (P : Shared) (q : ℕ) (first : Fin 9) (delay h : ℕ) {m : ℕ}
    {c c' : Control} {s s' : GalilVM} (hr : Rounds P q first delay h m c s c' s') :
    ∀ w0 : GalilScaffoldChainWatch.State, s.periodOnly = true → s.chain = .watch w0 →
      zero w0.lag = true →
      (∃ k : ℕ, Steps (galilFrameS P q first) delay k ⟨c, s⟩ ⟨c', s'⟩) ∧
      ∃ w' : GalilScaffoldChainWatch.State, s'.chain = .watch w' ∧ zero w'.lag = true ∧
        s'.periodOnly = true ∧ CompareRounds h (toOnly s w0) m (toOnly s' w') := by
  induction hr with
  | stop c s =>
    intro w0 hp hs hz
    exact ⟨⟨0, .zero _⟩, w0, hs, hz, hp, .stop _⟩
  | next c s hseg hm1 hr1 hc1 w hs1 hav vs vq hcmp hmis hq hend hpred hlen hg s2 hb hs2 hi2 hchain o ho rest ih =>
    intro w0 hp hs hz
    obtain ⟨hsteps1, hcr1⟩ := round_next P q first delay h hseg w0 hp hs hz hm1 hr1 hc1 w hs1 hav vs vq
      hcmp hmis hq hend hpred hlen hg s2 hb hs2 hi2 hchain o ho
    obtain ⟨k1, hst1⟩ := hsteps1
    -- the start of the next round
    obtain ⟨w1, hw1, hz1, _, _⟩ := scanSeg_only P q first delay hseg w0 hp hs hz
    have hww : w1 = w := by rw [hs1] at hw1; injection hw1 with e; exact e.symm
    subst hww
    obtain ⟨⟨k2, hst2⟩, w', hw', hz', hp', hcr2⟩ := ih _
      (by show s2.periodOnly = true; rw [hs2.2]) rfl
      (by rw [chain_shift_lag hchain]; exact hz1)
    refine ⟨⟨_, steps_trans hst1 hst2⟩, w', hw', hz', hp', ?_⟩
    have := compareRounds_append hcr1 hcr2
    rw [Nat.add_comm] at this
    exact this

#print axioms rounds_lift

end PalPeg.GalilScaffoldChainInputSupply
