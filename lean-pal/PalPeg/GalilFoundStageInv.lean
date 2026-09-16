import PalPeg.GalilFoundStage

/-!
# The two named hypotheses of `GalilFoundStage`
-/

set_option autoImplicit false
namespace PalPeg.GalilFoundStageInv
open PalPeg PalPeg.GalilScaffoldChainInputSupply Manacher GalilScaffoldInputHead
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldChainVerifier
open PalPeg.GalilReplaySpan PalPeg.GalilBranchInvariants PalPeg.GalilBranchInvariants2
open PalPeg.GalilReplayBudgetProof PalPeg.GalilFoundStage

/-! ## 1. The found radius at a background tick -/

theorem found_radius_bg (P : Shared) (qq : ℕ) (first : Fin 9) (hP : Decodes P)
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw r Rad last)
    (hcen : r.center = represent ⟨a :: ls, gap⟩ (rs.map some) q)
    {c0 : Control} (hcl : c0.clock = 2048)
    (hstage : StageEntry Rad last)
    {es1 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg : WatchSegE P qq first 2048 es1 c0 r cF sF) (hsF : sF.chain = .idle)
    (vq : SearchVM) (hq : searchEffect P false sF vq)
    (hfound : vq.search.mode = .found) :
    ∃ k h span : ℕ,
      GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) k 0
        (GalilScaffoldProgram.denote vq.dp.config) ∧
      (GalilScaffoldProgram.denote vq.dp.config).pc = 346 ∧
      (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h ∧
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) k h ∧
      1 ≤ h ∧ value sF.radius ≤ 2 * (h : ℤ) := by
  obtain ⟨_, _, _, _, ⟨hrc, hrv⟩, _, hsearch, hlower, hlast, hlv⟩ := hR
  obtain ⟨_, hplr⟩ := hP.1 r a ls rs q gap hcen
  obtain ⟨k, hk⟩ : ∃ k : ℕ, value last = k := ⟨(value last).toNat, (Int.toNat_of_nonneg hlv).symm⟩
  have hstep : searchStep (P.place sF) false (searchLens.get sF) vq := by
    rcases hq with ⟨_, hstep⟩ | ⟨hne, _⟩
    · exact hstep
    · exact absurd hsF hne
  have hrunSeg0 := watchSegE_searchRun P qq first 2048 hP.2 hseg hsF
  have hrunSeg := hrunSeg0
  rw [hplr] at hrunSeg
  have hcen1 : sF.center = r.center := watchSegE_center P qq first 2048 hseg
  rw [hP.2 sF r hcen1, hplr] at hstep
  obtain ⟨av1, _, hes1, hcl1, _⟩ := watchSegE_clock P qq first 2048 hseg
  rw [hcl] at hes1 hcl1
  have hev : es1 ++ [false] = GalilScaffoldAdvanceClock.advances 2048 2048
      ((av1 ++ [false]).map (fun b => (b, true))) := by
    rw [List.map_append, GalilScaffoldAdvanceClock.advances_append, map_fst_map_pair, ← hcl1, ← hes1]
    rfl
  have hu : (searchLens.get sF).search.mode ≠ .found := by
    cases hes : es1 with
    | nil =>
      rw [hes] at hrunSeg
      have he : searchLens.get sF = searchLens.get r := searchRun_unique hrunSeg (.nil _)
      rw [he]
      show r.search.mode ≠ _
      rw [hsearch]
      simp [GalilScaffoldSearchFinish.begin]
    | cons x xs =>
      exact watchSegE_search_not_found P qq first 2048 hP.2 hseg hsF es1 [] _ (by simp)
        (by rw [hes]; simp) hrunSeg0
  obtain ⟨span, h, hres, hpc, hpos, hcand, hmin, hcase⟩ :=
    GalilLaterRadius.first_found ⟨a :: ls, gap⟩ last r.radius hlast k hk hrc Rad hrv (hstage k hk)
      (v0 := searchLens.get r) hsearch hlower ⟨hrunSeg, hstep, hu, hfound⟩ hev
  obtain ⟨hkh, h1⟩ := GalilFoundRadiusBound.candidate_lower_lt hcand
  obtain ⟨_, _, hrad, _, _⟩ := watchSegE_heads P qq first 2048 hseg
  rw [hrv] at hrad
  refine ⟨k, h, span, hres, hpc, hpos, hcand, h1, ?_⟩
  rcases hcase with ⟨-, hb, -⟩ | ⟨n', hs, -, hprev, hb⟩
  · have hm : max k 1 ≤ h := max_le (by omega) (by omega)
    have h2 : ((Rad + es1.count true : ℕ) : ℤ) ≤ ((2 * max k 1 : ℕ) : ℤ) := by exact_mod_cast hb
    have h3 : ((max k 1 : ℕ) : ℤ) ≤ (h : ℤ) := by exact_mod_cast hm
    rw [hrad]; push_cast at h2 h3 ⊢; omega
  · rw [hs] at hcand
    have hn : n' < 4 * h := GalilFoundRadiusBound.later_stage_n_lt _ n' k h hcand hprev
    have h2 : ((2 * (Rad + es1.count true) : ℕ) : ℤ) ≤ (n' : ℤ) := by exact_mod_cast hb
    have h3 : (n' : ℤ) < 4 * (h : ℤ) := by exact_mod_cast hn
    rw [hrad]; push_cast at h2 ⊢; omega

#print axioms found_radius_bg

/-! ## 2. The arrival bit only moves the debt -/

/-- Inversion of a one-event safe quantum. -/
theorem safeQuanta_single {s t : GalilScaffoldSearchFinish.State}
    {x z : GalilScaffoldControl.Machine 12} {a : Bool}
    (h : GalilScaffoldSearchRun.SafeQuanta s x [a] t z) :
    ∃ u y, GalilScaffoldSearchRun.SafeQuanta s x [false]
        (GalilScaffoldSearchRun.advance false u) y ∧
      t = GalilScaffoldSearchRun.advance a u ∧ z = y := by
  cases h with
  | cons s u t x y z a' as hm hq hr =>
    cases hr with
    | nil => exact ⟨u, _, .cons _ u _ _ _ _ false [] hm hq (.nil _ _), rfl, rfl⟩

/-- **The arrival bit is invisible to the DP and to the mode.**  Every branch
of `searchStep` feeds `a` to `advance`/`afterAdvance`, which only decrements the
debt counter; so a `true` arrival can be replayed as a `false` one with the same
DP machine and the same search mode. -/
theorem searchStep_false_of (center : GalilScaffoldPlace.Place) (a : Bool) {v w : SearchVM}
    (h : searchStep center a v w) :
    ∃ w', searchStep center false v w' ∧ w'.dp = w.dp ∧ w'.search.mode = w.search.mode := by
  cases hm : v.search.mode with
  | idle =>
    simp only [searchStep, hm] at h ⊢
    exact ⟨v, rfl, by rw [h], by rw [h]⟩
  | found =>
    simp only [searchStep, hm] at h ⊢
    exact ⟨v, rfl, by rw [h], by rw [h]⟩
  | missed =>
    simp only [searchStep, hm] at h ⊢
    exact ⟨v, rfl, by rw [h], by rw [h]⟩
  | grow =>
    simp only [searchStep, hm] at h ⊢
    by_cases hp : GalilScaffoldCounter.positive v.search.work = true
    · rw [if_pos hp] at h
      refine ⟨SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance false
        (GalilScaffoldStagePrepare.growStep v.toPrep)) v.search.quarter v.lower, ?_, ?_, ?_⟩
      · rw [if_pos hp]
      · rw [h]; cases a <;> rfl
      · rw [h]; cases a <;> rfl
    · rw [if_neg hp] at h
      refine ⟨SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance false
        (GalilScaffoldPrepareControl.prepare v.toPrep v.lower center)) v.search.quarter v.lower,
        ?_, ?_, ?_⟩
      · rw [if_neg hp]
      · rw [h]; cases a <;> rfl
      · rw [h]; cases a <;> rfl
  | double =>
    simp only [searchStep, hm] at h ⊢
    by_cases hp : GalilScaffoldCounter.positive v.search.work = true
    · rw [if_pos hp] at h
      refine ⟨{ v with search := GalilScaffoldSearchRun.advance false (GalilScaffoldDouble.step v.search) }, ?_, ?_, ?_⟩
      · rw [if_pos hp]
      · rw [h]
      · rw [h]; cases a <;> rfl
    · rw [if_neg hp] at h
      refine ⟨SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance false
        (GalilScaffoldPrepareControl.prepare v.toPrep v.lower center)) v.search.quarter v.lower,
        ?_, ?_, ?_⟩
      · rw [if_neg hp]
      · rw [h]; cases a <;> rfl
      · rw [h]; cases a <;> rfl
  | wait =>
    simp only [searchStep, hm] at h ⊢
    exact ⟨_, rfl, by rw [h], by rw [h]; cases a <;> rfl⟩
  | lower =>
    simp only [searchStep, hm] at h ⊢
    obtain ⟨y, hy, hw⟩ := h
    exact ⟨_, ⟨y, hy, rfl⟩, by rw [hw]; cases a <;> rfl, by rw [hw]; cases a <;> rfl⟩
  | lowerHome =>
    simp only [searchStep, hm] at h ⊢
    obtain ⟨y, hy, hw⟩ := h
    exact ⟨_, ⟨y, hy, rfl⟩, by rw [hw]; cases a <;> rfl, by rw [hw]; cases a <;> rfl⟩
  | copy =>
    simp only [searchStep, hm] at h ⊢
    obtain ⟨y, hy, hw⟩ := h
    exact ⟨_, ⟨y, hy, rfl⟩, by rw [hw]; cases a <;> rfl, by rw [hw]; cases a <;> rfl⟩
  | home =>
    simp only [searchStep, hm] at h ⊢
    obtain ⟨y, hy, hw⟩ := h
    exact ⟨_, ⟨y, hy, rfl⟩, by rw [hw]; cases a <;> rfl, by rw [hw]; cases a <;> rfl⟩
  | run =>
    simp only [searchStep, hm] at h ⊢
    obtain ⟨hq, hl, hwk⟩ := h
    obtain ⟨u, y, hq', ht, hz⟩ := safeQuanta_single hq
    refine ⟨⟨GalilScaffoldSearchRun.advance false u, y, v.lower, v.walker⟩, ⟨hq', rfl, rfl⟩, ?_, ?_⟩
    · rw [hz]
    · show (GalilScaffoldSearchRun.advance false u).mode = _
      rw [ht]; cases a <;> rfl

#print axioms searchStep_false_of

/-! ## 3. `OffCompareFoundStage` -/

theorem found_stage_data_bg (P : Shared) (qq : ℕ) (first : Fin 9) (hP : Decodes P)
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw r Rad last)
    (hcen : r.center = represent ⟨a :: ls, gap⟩ (rs.map some) q)
    {c0 : Control} (hcl : c0.clock = 2048) (hstage : StageEntry Rad last)
    {es1 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg : WatchSegE P qq first 2048 es1 c0 r cF sF) (hsF : sF.chain = .idle)
    (vq : SearchVM) (hq : searchEffect P false sF vq) (hfound : vq.search.mode = .found)
    {n : ℕ} (ha : AnswerAhead (vq.dp.config.tapes 11) n) :
    (∃ lower span : ℕ,
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) lower n) ∧
      1 ≤ n ∧ value sF.radius ≤ 2 * (n : ℤ) := by
  obtain ⟨k, h, span, hres, hpc, hpos, hcand, h1, hrad⟩ :=
    found_radius_bg P qq first hP a ls rs q gap hR hcen hcl hstage hseg hsF vq hq hfound
  have hnh : n = h := by
    rcases hres with ⟨k2, -, -, -, -, htape, hpos2⟩ | ⟨hpc', -⟩
    · have hk2 : k2 = h := by rw [← hpos, ← hpos2]
      subst hk2
      exact answerAhead_eq_head ha htape hpos2
    · rw [hpc] at hpc'; exact absurd hpc' (by decide)
  subst hnh
  exact ⟨⟨k, span, hcand⟩, h1, hrad⟩

/-- **`OffCompareFoundStage` for the concrete machine.**  A found tick that is
not a matched comparison is handled exactly like the comparison tick, with the
final clock event `false` instead of `true`; a `true` arrival off the comparison
is first replayed as a `false` one (`searchStep_false_of`), which changes
neither the DP output nor the mode. -/
theorem offCompareFoundStage_of_decodes {raw : List (Fin 2)} {P : Shared} {qq : ℕ} {first : Fin 9}
    (hP : Decodes P) : OffCompareFoundStage raw P qq first := by
  intro c s a vq k n _ hidle _ hq hf ha hn hrad hstage
  obtain ⟨r, Rad, last, es, c0, hRst, hSt, hcl, hseg⟩ := hstage
  have hstep : searchStep (P.place s) a (searchLens.get s) vq := by
    rcases hq with ⟨_, hstep⟩ | ⟨hne, _⟩
    · exact hstep
    · exact absurd hidle hne
  obtain ⟨vq', hstep', hdp', hmode'⟩ := searchStep_false_of (P.place s) a hstep
  have hq' : searchEffect P false s vq' := Or.inl ⟨hidle, hstep'⟩
  have hf' : vq'.search.mode = .found := by rw [hmode']; exact hf
  have ha' : AnswerAhead (vq'.dp.config.tapes 11) n := by rw [hdp']; exact ha
  have hcentre : s.center = r.center := watchSegE_center P qq first 2048 hseg
  obtain ⟨al, ls, rs, qq', hdec, -⟩ := represents_decompose r.center raw hRst.2.1 hRst.2.2.1
  obtain ⟨hcand, -, hrad2⟩ :=
    found_stage_data_bg P qq first hP al ls rs qq' r.center.gap hRst hdec hcl hSt hseg hidle
      vq' hq' hf' ha'
  obtain ⟨-, hplr⟩ := hP.1 r al ls rs qq' r.center.gap hdec
  have hplace : P.place s = P.place r := hP.2 s r hcentre
  refine ⟨by rw [hplace, hplr]; exact hcand, ?_⟩
  have hk : (k : ℤ) ≤ 2 * (n : ℤ) := by rw [← hrad.2]; exact hrad2
  exact_mod_cast hk

/-- **`ReplayBudgetR` from `Decodes P` alone.**  `replayBudgetR_of_decodes` with its
named hypothesis discharged. -/
theorem replayBudgetR_of_decodes' {raw : List (Fin 2)} {P : Shared} {qq : ℕ} {first : Fin 9}
    (hP : Decodes P) : ReplayBudgetR raw P qq first 2048 :=
  replayBudgetR_of_decodes hP (offCompareFoundStage_of_decodes hP)

#print axioms offCompareFoundStage_of_decodes
#print axioms replayBudgetR_of_decodes'

/-! ## 4. `ReplayStage` along a replay run

`ReplayStageInv` as stated quantifies over **every** `(c, s)` with `c.mode = .scan`,
`c.replaying = true`, `s.chain = .idle`, `SearchReady` and `MInv`, and in that form it is
**not** provable: `MInv` is only the leftmost-centre bookkeeping
(`GalilLiveCentreReplay.MInv`) and `SearchReady` only the local prep/DP reachability, so
nothing in the premises ties `s.search` to a `GalilScaffoldSearchFinish.begin`.  It is a
statement about the states the replay actually visits, so it has to be carried by the
construction, not proved after the fact.

What is provable here is its inductive content: the invariant holds at the replay entry and
is preserved by the two tick shapes the replay takes while the chain is idle — exactly the
steps `idle_countdown3` (`countR`) and `idle_compare3` (`matchIdleR`) perform, and exactly
the states at which `window_of_found` consumes the budget.  Threading it needs
`Entry` / `Result3` / `Busy` of `GalilReplaySpan` to carry the extra field.
-/

/-- **The replay entry.**  `replay_after_fallback_general'''` enters with
`Restarted raw t 0 reset` (so `StageEntry 0 reset` is free, `stageEntry_zero`) and
`c.clock = delay = 2048`: the empty segment. -/
theorem replayStage_entry {raw : List (Fin 2)} {P : Shared} {qq : ℕ} {first : Fin 9}
    {c : Control} {t : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw t Rad last) (hSt : StageEntry Rad last) (hc : c.clock = 2048) :
    ReplayStage raw P qq first c t :=
  ⟨t, Rad, last, [], c, hR, hSt, hc, .stop _ _⟩

/-- **Preservation along a segment.**  Any chain-idle stretch extends the stage segment. -/
theorem replayStage_trans {raw : List (Fin 2)} {P : Shared} {qq : ℕ} {first : Fin 9}
    {c c' : Control} {s s' : GalilVM} {es : List Bool}
    (hst : ReplayStage raw P qq first c s)
    (hseg : WatchSegE P qq first 2048 es c s c' s') :
    ReplayStage raw P qq first c' s' := by
  obtain ⟨r, Rad, last, es0, c0, hR, hSt, hcl, hseg0⟩ := hst
  exact ⟨r, Rad, last, es0 ++ es, c0, hR, hSt, hcl,
    watchSegE_trans P qq first 2048 hseg0 hseg⟩

/-- **The countdown tick of a replay** (`idle_countdown3`, `WatchSegE.countR`). -/
theorem replayStage_count {raw : List (Fin 2)} {P : Shared} {qq : ℕ} {first : Fin 9}
    {c : Control} {s s' : GalilVM} (hst : ReplayStage raw P qq first c s)
    (hm : c.mode = .scan) (hr : c.replaying = true) (hc : 1 < c.clock) (hidle : s.chain = .idle)
    (hb : (galilFrameS P qq first).background s s') :
    ReplayStage raw P qq first {c with clock := c.clock - 1} s' :=
  replayStage_trans hst (.countR c s s' hm hr hc hidle hb (.stop _ _))

/-- **The matched comparison of a replay that does not start the chain**
(`idle_compare3`, `WatchSegE.matchIdleR`). -/
theorem replayStage_matchIdle {raw : List (Fin 2)} {P : Shared} {qq : ℕ} {first : Fin 9}
    {c : Control} {s : GalilVM} {vs : ScanVM} {vq : SearchVM} {o : Bool}
    (hst : ReplayStage raw P qq first c s)
    (hm : c.mode = .scan) (hr : c.replaying = true) (hc : c.clock = 1) (ha : canRight s.right)
    (hidle : s.chain = .idle) (hl : vs.left = left s.left) (hrr : vs.right = right s.right)
    (hvs : vs.chain = .idle) (hmt : (galilFrame P qq first).matched (scanLens.set s vs))
    (hq : searchEffect P true s vq) (hnf : vq.search.mode ≠ .found)
    (ho : refresh (galilFrame P qq first) (replayDec true (afterCompare s vs vq)) c.output o) :
    ReplayStage raw P qq first {c with clock := 2048, output := o, replaying := !P.replayExhausted (replayDec true (afterCompare s vs vq))} (replayDec true (afterCompare s vs vq)) :=
  replayStage_trans hst
    (.matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho (.stop _ _))

#print axioms replayStage_entry
#print axioms replayStage_trans
#print axioms replayStage_count
#print axioms replayStage_matchIdle

end PalPeg.GalilFoundStageInv
