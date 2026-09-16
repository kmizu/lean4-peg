import PalPeg.GalilOracleLeaves2

/-!
# Final assembly over the strengthened oracle: `hstr` removed

`GalilOracleLeaves2.h_oracle_of_leaves'` still carries one residual leaf,

```
hstr : ∀ w c r, InvL w c r → InvLPC w c r
```

which exists **only** because `GalilFinalAssembly.H_oracle` asks for
`GalilTraceCost.CycleOracleMC`, and that predicate quantifies over *every*
`InvL` state, boot-reachable or not (`GalilOracleMC2.cycleOracleMC_of_MC2C`).

The run the final theorem actually uses starts at the **boot** landing, and that
landing is an `InvLPC` state (`invLPC_init` below, from
`GalilInvPlus.init_restarted_span` plus `GalilOracleMC2.invLPC_of_boot`).  So the
whole checkpoint recursion can be run over `InvLPC` with the strengthened oracle
`GalilOracleMC2.CycleOracleMC2C`, which is exactly what
`GalilOracleMC2.checkpoints_cost2` does — except that
`GalilFinalAssembly3.pal_in_peg_final3` needs the `Tc 1 = 1` conjunct of
`GalilFinalBaseNeed.PreTraceB` (that is what discharges `H_base`).

This module therefore re-runs the chain

```
H_oracle2  →  checkpoints_cost2_upto1  →  preTraceB2_exists  →  pal_in_peg_final4
```

with `InvLPC`/`CycleOracleMC2C` in place of `InvL`/`CycleOracleMC` throughout:

* `invLPC_init` — the boot landing is `InvLPC` with right head at place `1`.
* `H_oracle2` — `CycleOracleMC2C (PofC centreC placeC entry w) q first w` for
  every nonempty `w` (the strengthened form of `GalilFinalAssembly.H_oracle`).
* `checkpoints_cost2_upto1` — `GalilFinalBaseNeed.checkpoints_cost_upto1` over
  the strengthened oracle (`GalilOracleMC2.checkpoints_cost2_upto` plus the two
  `Tc 1 = k0` conjuncts).
* `preTraceB2_exists` — `GalilFinalBaseNeed.preTraceB_exists` from `H_oracle2`.
* `pal_in_peg_final4` — `GalilFinalAssembly3.pal_in_peg_final3` verbatim, with
  `H_oracle` replaced by `H_oracle2`.
* `h_oracle2_of_leaves` — `GalilOracleLeaves2.h_oracle_of_leaves'` **minus**
  `hstr`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PalPeg.GalilFinalAssembly4

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilTickArrive PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.GalilThrottledRun PalPeg.GalilThrottledRunGen PalPeg.GalilLedgerQ64
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilTruncTick PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2
open PalPeg.GalilFinalBaseNeed PalPeg.GalilFinalAssembly3 PalPeg.GalilOracleLeaves2

/-! ## 1. The boot landing is an `InvLPC` state -/

/-- **`GalilInvPlus.invLP_init` strengthened to `InvLPC`.**  The `init` tick lands
in a radius-`0` restart, so it carries the centre head outright
(`centreRep_of_restarted`) and the span relation (`init_restarted_span`); the copy
pack is free from the boot (`invLPC_of_boot`).  The right head sits on place `1`. -/
theorem invLPC_init (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (a : Fin 2) (rest : List (Fin 2)) :
    ∃ (c1 : Control) (t : GalilVM),
      StepsAll (galilFrameS (PofC centre place entry (a :: rest)) q first) 2048
        (SoundScanNR (a :: rest)) 1
        ⟨initial 2048, GalilBootVM.initVM0 (a :: rest)⟩ ⟨c1, t⟩ ∧
      InvLPC (a :: rest) c1 t ∧ position t.right = 1 := by
  obtain ⟨t, ht, hR, hpos, hRt, hrem, hrp, hS⟩ :=
    init_restarted_span (onLetterVM (a :: rest)) leftFirstVM shiftGuardVM beginShiftVM'
      beginFallbackVM' (restartVM entry) centre place entry q first 2048 (initial 2048) rfl
      (GalilBootVM.initVM0 (a :: rest)) a rest (GalilBootVM.initVM0_right _)
      (GalilBootVM.initVM0_radius _) (GalilBootVM.initVM0_length _)
  have hst : StepsAll (galilFrameS (PofC centre place entry (a :: rest)) q first) 2048
      (SoundScanNR (a :: rest)) 1 ⟨initial 2048, GalilBootVM.initVM0 (a :: rest)⟩
      ⟨{(initial 2048) with mode := .scan, output := true}, t⟩ :=
    .succ (fun hsc => by cases hsc) ht
      (.zero _ (fun _ _ => outputRel_position_one a rest _ t (by rw [hRt, hpos])))
  have hMt : MInv (a :: rest) {(initial 2048) with mode := .scan, output := true} t := by
    refine minv_of_leftmost ?_ rfl
    rw [hRt, hpos]
    exact leftmost_one a rest
  have htrp : t.replay = reset := by
    rw [hrp]; exact GalilBootVM.initVM0_replay _
  have hI : Inv (a :: rest) {(initial 2048) with mode := .scan, output := true} t :=
    inv_of_parts hR hMt ⟨rfl, rfl, rfl⟩ (frontier_of_reset htrp) (replayRest_of_reset htrp)
      (by
        rw [shiftIdle_iff, hrem]
        exact (shiftIdle_iff (GalilBootVM.initVM0 (a :: rest))).1
          (GalilBootVM.initVM0_shiftIdle _))
  have hIP : InvLP (a :: rest) {(initial 2048) with mode := .scan, output := true} t :=
    ⟨invL_of_run hst (invS_of_inv hI), entryCounters_of_restarted hR hS⟩
  exact ⟨_, t, hst,
    invLPC_of_boot centre place entry q first 2048 (stepsAll_steps hst) hIP
      (centreRep_of_restarted hR),
    by rw [hRt, hpos]⟩

#print axioms invLPC_init

/-! ## 2. The checkpoint construction over `InvLPC`, with `Tc 1 = k0` -/

/-- **`GalilFinalBaseNeed.checkpoints_cost_upto1` over the strengthened oracle.**
Verbatim, with `InvL`/`CycleOracleMC`/`reachC_from_invL` replaced by
`InvLPC`/`CycleOracleMC2C`/`reachC2_from_invLPC`: the recursion never leaves
`InvLPC`, so there is no `hstr` anywhere. -/
theorem checkpoints_cost2_upto1 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC2C P q first raw)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 x0 ⟨c, r⟩)
    (hI : InvLPC raw c r) (hpos : position r.right = 1) :
    ∀ M, M ≤ raw.length →
    ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) (e : ℕ),
      st 0 = x0 ∧ Tc 0 = 0 ∧ Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st e ∧
      (∀ m, m < M → Tc m ≤ Tc (m+1)) ∧ Tc M ≤ e ∧
      (∀ m, 1 ≤ m → m ≤ M →
        PalPeg.GalilReportPrefix.ReportPointAt raw m (st (Tc m)) ∧
        Refreshed P q first (st (Tc m))) ∧
      (∀ m, 1 ≤ m → m < M →
        Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw raw (m+1) - Cw raw m) + beta' 2048) ∧
      (M < raw.length → ∃ (c' : Control) (r' : GalilVM),
        st e = ⟨c', r'⟩ ∧ InvLPC raw c' r' ∧ position r'.right ≤ 2 * (M+1) - 1 ∧
        (1 ≤ M → ∃ L : List Piece, CostedRun (st (Tc M)).vm r' (e - Tc M) L)) ∧
      (M = 0 → e = k0 ∧ st e = ⟨c, r⟩) ∧
      (1 ≤ M → Tc 1 = k0) := by
  intro M
  induction M with
  | zero =>
    intro _
    obtain ⟨g, hg0, hgn, htr⟩ := stepsAll_fn hpre
    refine ⟨g, fun _ => 0, k0, hg0, rfl, htr, fun m hm => absurd hm (Nat.not_lt_zero _),
      Nat.zero_le _, fun m h1 h2 => absurd h1 (by omega), fun m h1 h2 => absurd h2 (by omega),
      fun _ => ⟨c, r, hgn, hI, by omega, fun h => absurd h (by omega)⟩,
      fun _ => ⟨rfl, hgn⟩, fun h => absurd h (by omega)⟩
  | succ M ih =>
    intro hM
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, hres, hzero, hone⟩ :=
      ih (by omega)
    obtain ⟨c', r', hste, hI', hp', hpend⟩ := hres (by omega)
    obtain ⟨y, k, L2, hrun, hcr, hrp, hfr, hcont⟩ :=
      reachC2_from_invLPC P q first raw hor (m := M+1) (by omega) hM hI' hp'
    -- the first target is reached in zero ticks
    have hk0 : M = 0 → k = 0 ∧ e = k0 := by
      intro hM0
      subst hM0
      obtain ⟨he, hse⟩ := hzero rfl
      have hrr : r' = r := by
        have := hste.symm.trans hse
        exact (GalilScaffoldTop.State.mk.injEq _ _ _ _ ▸ this).2
      subst hrr
      have hyp := hrp.atPlace
      exact ⟨costedRun_zero hcr (by rw [hyp, hpos]), he⟩
    obtain ⟨g1, hg10, hg1k, htr1⟩ := stepsAll_fn hrun
    have hj1 : st e = g1 0 := by rw [hste, hg10]
    set st1 := concat st g1 e with hst1
    have htr1' : Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st1 (e + k) :=
      trace_concat htr htr1 hj1
    have hst1y : st1 (e + k) = y := by rw [hst1, concat_end st g1 hj1, hg1k]
    obtain ⟨st2, e2, htr2, hagree, hle2, hres2⟩ :
        ∃ (st2 : ℕ → State GalilVM) (e2 : ℕ),
          Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st2 e2 ∧
          (∀ i, i ≤ e + k → st2 i = st1 i) ∧ e + k ≤ e2 ∧
          (M + 1 < raw.length → ∃ (c'' : Control) (r'' : GalilVM),
            st2 e2 = ⟨c'', r''⟩ ∧ InvLPC raw c'' r'' ∧ position r''.right ≤ 2 * (M+1+1) - 1 ∧
            ∃ L : List Piece, CostedRun y.vm r'' (e2 - (e + k)) L) := by
      by_cases hlt : M + 1 < raw.length
      · obtain ⟨c'', r'', k', L', hrun2, hcr2, hI2, hp2⟩ := hcont hlt
        obtain ⟨g2, hg20, hg2k, htr2⟩ := stepsAll_fn hrun2
        have hj2 : st1 (e + k) = g2 0 := by rw [hst1y, hg20]
        refine ⟨concat st1 g2 (e + k), e + k + k', trace_concat htr1' htr2 hj2,
          fun i hi => concat_le st1 g2 hi, by omega, fun _ => ⟨c'', r'', ?_, hI2, hp2, L', ?_⟩⟩
        · rw [concat_end st1 g2 hj2, hg2k]
        · rw [show e + k + k' - (e + k) = k' by omega]; exact hcr2
      · exact ⟨st1, e + k, htr1', fun _ _ => rfl, le_rfl, fun h => absurd h hlt⟩
    have hTcle : ∀ m, m ≤ M → Tc m ≤ e := fun m hm =>
      le_trans (mono_of_step Tc M hmono m M hm le_rfl) hTcM
    have hst2old : ∀ m, m ≤ M → st2 (Tc m) = st (Tc m) := by
      intro m hm
      rw [hagree _ (by have := hTcle m hm; omega), hst1, concat_le st g1 (hTcle m hm)]
    have hst2y : st2 (e + k) = y := by rw [hagree _ le_rfl, hst1y]
    refine ⟨st2, fun m => if m ≤ M then Tc m else e + k, e2, ?_, ?_, htr2, ?_, ?_, ?_, ?_, ?_,
      fun h => absurd h (by omega), ?_⟩
    · rw [hagree 0 (by omega), hst1, concat_le st g1 (Nat.zero_le _), hst0]
    · simp [hTc0]
    · intro m hm
      by_cases hm' : m + 1 ≤ M
      · simp only [hm', show m ≤ M by omega, if_true]; exact hmono m (by omega)
      · have hmM : m = M := by omega
        subst hmM
        simp only [le_refl, if_true, hm', if_false]
        exact le_trans hTcM (Nat.le_add_right _ _)
    · simp only [show ¬ M + 1 ≤ M by omega, if_false]; exact hle2
    · intro m h1 h2
      by_cases hm' : m ≤ M
      · simp only [hm', if_true]
        rw [hst2old m hm']
        exact hchk m h1 hm'
      · have hmM : m = M + 1 := by omega
        subst hmM
        simp only [hm', if_false]
        rw [hst2y]
        exact ⟨hrp, hfr⟩
    · intro m h1 h2
      by_cases hm' : m + 1 ≤ M
      · simp only [hm', show m ≤ M by omega, if_true]
        exact hcost m h1 (by omega)
      · have hmM : m = M := by omega
        subst hmM
        simp only [le_refl, if_true, hm', if_false]
        obtain ⟨L1, hcr1⟩ := hpend h1
        have hall := costedRun_trans hcr1 hcr
        have hTm := hTcle m le_rfl
        obtain ⟨hrp0, hfr0⟩ := hchk m h1 le_rfl
        have hc' : CostedRun (st (Tc m)).vm y.vm (e + k - Tc m) (L1 ++ L2) := by
          rw [show e + k - Tc m = e - Tc m + k by omega]; exact hall
        exact interval_cost_of_costedRun h1 hrp0 hfr0 hrp hfr hc'
    · intro hlt
      obtain ⟨c'', r'', h1, h2, h3, L, h4⟩ := hres2 hlt
      refine ⟨c'', r'', h1, h2, h3, fun _ => ⟨L, ?_⟩⟩
      simp only [show ¬ M + 1 ≤ M by omega, if_false]
      rw [hst2y]
      exact h4
    · intro _
      by_cases hM0 : M = 0
      · subst hM0
        obtain ⟨hk, he⟩ := hk0 rfl
        simp only [show ¬ (1 ≤ 0) by omega, if_false]
        omega
      · simp only [show 1 ≤ M by omega, if_true]
        exact hone (by omega)

#print axioms checkpoints_cost2_upto1

/-! ## 3. The strengthened pre-loaded trace -/

/-- (A') The **strengthened** cycle oracle: `CycleOracleMC2C` for every nonempty
input.  This is `GalilFinalAssembly.H_oracle` with `GalilTraceCost.CycleOracleMC`
replaced by `GalilOracleMC2.CycleOracleMC2C`, i.e. the recursion is asked only
about `InvLPC` entry states — never about an arbitrary `InvL` state. -/
def H_oracle2 (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → CycleOracleMC2C (PofC centre place entry w) q first w

/-- **`GalilFinalBaseNeed.preTraceB_exists` from the strengthened oracle.**  Boot
through the `init` tick into an `InvLPC` state (`invLPC_init`), then
`checkpoints_cost2_upto1`.  No `hstr`. -/
theorem preTraceB2_exists (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (w : List (Fin 2)) (hw : 0 < w.length)
    (hor : CycleOracleMC2C (PofC centre place entry w) q first w) :
    ∃ st Tc, PreTraceB centre place entry q first w st Tc := by
  rcases w with _ | ⟨a, rest⟩
  · simp at hw
  · obtain ⟨c1, t, hst, hI, hpos⟩ := invLPC_init centre place entry q first a rest
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, -, -, hone⟩ :=
      checkpoints_cost2_upto1 (PofC centre place entry (a :: rest)) q first (a :: rest) hor hst
        hI hpos (a :: rest).length le_rfl
    refine ⟨st, Tc, ⟨⟨hst0, hTc0, trace_le htr hTcM, mono_of_step Tc _ hmono, ?_, hcost⟩,
      hone (by simp)⟩⟩
    intro m h1 h2
    exact ledgerAt_of_prefix (hchk m h1 h2).1 (hchk m h1 h2).2

/-! ## 4. The final theorem over `H_oracle2` -/

/-- **`PAL ∈ PEG`**, `GalilFinalAssembly3.pal_in_peg_final3` verbatim with the
oracle hypothesis strengthened to `H_oracle2`: `H_base` is still discharged via
`base_of_preTraceB`, (B) is still `H_needLB'` alone, (C) is still `H_realizeLB'`.
Only the route from the oracle to the pre-loaded trace changed — it now runs
entirely over `InvLPC`, so the leaf `hstr : InvL → InvLPC` disappears. -/
theorem pal_in_peg_final4 (entry q : ℕ) (first : Fin 9)
    (hA : H_oracle2 centreC placeC entry q first)
    (hB_need : H_needLB' centreC placeC entry q first)
    (hC : H_realizeLB' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL := by
  classical
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := hC
  have key : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceB centreC placeC entry q first w st Tc := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨st, Tc, h⟩ := preTraceB2_exists centreC placeC entry q first w hw (hA w hw)
      exact ⟨st, Tc, fun _ => h⟩
    · exact ⟨fun _ => boot w, fun _ => 0, fun h => absurd h hw⟩
  choose stP TcP hP using key
  let M := L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn
  have hpre : ∀ w : List (Fin 2), 0 < w.length → PreloadL w (stP w) (TcP w) := by
    intro w hw
    have h := hP w hw
    exact ⟨h.pre.tc0, fun m hm => h.pre.mono m (m+1) (by omega) hm,
      needL_boot w (stP w) h.pre.start,
      needLe_of_pointwise w (stP w) (TcP w) (hB_need w hw _ _ h)⟩
  refine pal_in_peg_of_latch' (Nat.mul_pos hn (PalPeg.Local.cnt_pos K)) M
    (PofC centreC placeC entry) (fun _ => q) (fun _ => first) 2048
    (fun w => PofC_onLetter centreC placeC entry w) (fun w => PofC_leftFirst centreC placeC entry w)
    (fun w => stLG τF w (stP w) (TcP w w.length))
    (fun w => arrLG τF w (stP w) (TcP w w.length))
    (fun w => (w.length + 1) * τF) ?_ ?_ ?_ ?_
  · intro w hw
    have h := hP w hw
    exact abstractRun_throttledL_2p18 w (stP w) (TcP w w.length) (PofC centreC placeC entry w) q
      first 2048
      (fun j => sharedC_trunc_vm w j centreC placeC entry (fun s => (centrePlaceC w j s).1)
        (fun s => (centrePlaceC w j s).2))
      (sharedC_suf w _ _ centreC placeC entry)
      (by rw [h.pre.start]; rfl) (needL_boot w (stP w) h.pre.start)
      (by rw [h.pre.start]; exact sufVM_boot w) h.pre.trace.tick
  · intro w hw
    exact hreal w hw _ _ (hP w hw)
  · exact ledger_throttledL_2p18 (PofC centreC placeC entry) (fun _ => q) (fun _ => first) stP TcP
      hpre (fun w hw => (hP w hw).pre.report w.length (by omega) le_rfl)
      (fun w hw => base_of_preTraceB (hP w hw))
      (fun w hw => (hP w hw).pre.cost)
  · exact GalilEmptyWord.realize_accept'_nil L blank initQ outQ n htape hn

/-! ## 5. `H_oracle2` from the leaves — `hstr` gone -/

/-- **`GalilOracleLeaves2.h_oracle_of_leaves'` minus `hstr`.**  Same twelve
residual leaves (`hpres`, `hquiet`, `houtReplay`, `hends`, `hended`,
`hlastMatch`, `hlastMismatch`, `hmismatch`, `hfound`, `hfoundBg`), the same
discharged ones (`hex`, `hsearch`, `hsegmentM` via `segment_of_invLPC`), but the
conclusion is `H_oracle2`, so the bridge `cycleOracleMC_of_MC2C` — and with it
its residue `hstr : ∀ w c r, InvL w c r → InvLPC w c r` — is never used. -/
theorem h_oracle2_of_leaves (entry q : ℕ) (first : Fin 9)
    (hpres : ∀ (w : List (Fin 2)) (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centreC placeC entry w) a s v → SearchReady v)
    (hquiet : ∀ w : List (Fin 2),
      PalPeg.GalilReplaySegment.SearchQuiet (PofC centreC placeC entry w))
    (houtReplay : ∀ (w : List (Fin 2)) (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 w c' t' k → SoundScanNR w ⟨c', t'⟩)
    (hends : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvLPC w c r →
      ∃ n : ℕ, ∀ (es : List Bool) (c' : Control) (t : GalilVM),
        WatchSegE (PofC centreC placeC entry w) q first 2048 es c r c' t →
        es.length = n → SegEnd (PofC centreC placeC entry w) c' t)
    (hended : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t → ¬ canRight t.right →
      ReachAtC2 (PofC centreC placeC entry w) q first w m c r)
    (hlastMatch : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      ReachAtC2 (PofC centreC placeC entry w) q first w m c r)
    (hlastMismatch : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      ReachAtC2 (PofC centreC placeC entry w) q first w m c r)
    (hmismatch : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRouteMC2 (PofC centreC placeC entry w) q first w m c r c' t)
    (hfound : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centreC placeC entry w) true t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centreC placeC entry w) q first w m c r c' t)
    (hfoundBg : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centreC placeC entry w) false t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centreC placeC entry w) q first w m c r c r) :
    H_oracle2 centreC placeC entry q first :=
  fun w _ =>
    cycleOracleMC2C_of_pieces centreC placeC entry q first w
      (fun s => hex_C centreC placeC entry w s)
      (fun s hs a => hsearch_C centreC placeC entry w s hs a)
      (hpres w) (hquiet w) (houtReplay w)
      (fun m c r _ _ hIC _ => by
        obtain ⟨c', t, hsW, hEnd⟩ :=
          segment_of_invLPC centreC placeC entry q first w
            (fun s => hex_C centreC placeC entry w s)
            (fun s hs a => hsearch_C centreC placeC entry w s hs a) (hpres w) c r hIC
            (hends w c r hIC)
        exact ⟨c', t, hsW, Or.inr hEnd⟩)
      (hended w) (hlastMatch w) (hlastMismatch w) (hmismatch w) (hfound w) (hfoundBg w)

#print axioms preTraceB2_exists
#print axioms pal_in_peg_final4
#print axioms h_oracle2_of_leaves

end PalPeg.GalilFinalAssembly4
