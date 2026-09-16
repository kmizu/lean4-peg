import PalPeg.CloseoutLaterQuantum

/-!
# `LaterQuantumC` discharged at the machine tick

`CloseoutLaterQuantum` proves `QuantumGoal` for every *later* stage entry
(`LaterEntry`).  The docstring there names the missing piece as
`LaterEntryAtSearchEffect` : a `LaterEntry` decomposition of the search run
inside `searchEffect P aF t vq` at any found tick.

**That statement is false as stated, and this file records why.**  The restart
state's search is `GalilScaffoldSearchFinish.begin lower radius`, whose mode is
`.grow`, not `.double`; so when the found tick belongs to the **first** stage
there is no `LaterEntry k n clock v0` with `v0 = searchLens.get r0` at all, and
a fortiori none quantified over all states `t` (the `GalilLeafQuiet`-style
stutter noted in `CloseoutLaterQuantum`).  What is true — and what the consumer
actually needs — is the disjunction-free export `LaterQuantumC`, because the
first stage supplies its own quantum:

* `first_quantum` — the analogue of `GalilLaterRadius.first_found` with the
  conclusion weakened to `CloseoutPrepInputs3.LaterQuantumC`.  Its `found`
  branch is `first_stage_aligned`'s `SafeQuanta` on the window `8*max k 1`;
  its exit branch hands the `.wait`/`.double` exit to
  `CloseoutLaterQuantum.exit_continue_quantum`, i.e. to the later-stage
  induction, which is where the `LaterEntry` really lives.
* `laterQuantum_at_tick` — `first_quantum` at a machine tick, entered through
  `CloseoutContracts.StageEntryC` + `SegReachedW` + `Decodes`, with the restart
  decomposition taken from `hE.stage` via `replayStage_trans` exactly as
  `CloseoutPrepInputs3.prepInputs3_of_found` does.
* `prepInputs3_of_found_C` — `prepInputs3_of_found_or_later` with its
  `LaterQuantumC` premise discharged.  **No `FirstStageC`, no `LaterQuantumC`.**

**What remains NAMED.**  Nothing in this file: `prepInputs3_of_found_C` has the
hypotheses of `prepInputs3_of_found_or_later` minus `hlater`.  The `LaterEntry`
export named in `CloseoutLaterQuantum` is *not* proved and is not needed.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutLaterEntry

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus
open PalPeg.GalilSearchReadyInv PalPeg.GalilSearchWait
open PalPeg.GalilFoundStage PalPeg.GalilFoundStageInv
open PalPeg.CloseoutContracts PalPeg.CloseoutFoundCompare
open PalPeg.GalilLaterRadius PalPeg.CloseoutLaterQuantum

/-! ## 1. The whole search from a restart, exporting the quantum -/

/-- **`first_found` with the `LaterQuantumC` conclusion.**  From the restart
entry (`v0.search = begin lower radius`) to a found tick: the quantum that the
found tick ends, whichever stage it belongs to. -/
theorem first_quantum (center : GalilScaffoldPlace.Place)
    (lower radius : Counter) (hlc : Canonical lower) (k : ℕ) (hk : value lower = k)
    (hrc : Canonical radius) (rad : ℕ) (hrad : value radius = rad) (hr : 3*rad ≤ 5*k)
    {v0 u vq : SearchVM} {es : List Bool} {e : Bool} {av : List Bool}
    (hsearch : v0.search = GalilScaffoldSearchFinish.begin lower radius) (hlower : v0.lower = lower)
    (hft : FoundTick center es v0 u e vq)
    (hev : es ++ [e] = GalilScaffoldAdvanceClock.advances 2048 2048 (av.map (fun b => (b, true)))) :
    CloseoutPrepInputs3.LaterQuantumC center vq.dp := by
  obtain ⟨hrun, hstep, hu, hfound⟩ := hft
  have hm1 : 1 ≤ max k 1 := le_max_right _ _
  have hkm : k ≤ max k 1 := le_max_left _ _
  obtain ⟨N, hN⟩ : ∃ N, max k 1
      + (2*k + 2*((GalilScaffoldPlace.stream center).take (8*max k 1+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (8*max k 1) = N := ⟨_, rfl⟩
  obtain ⟨esAll, hesAll⟩ : ∃ l, l = (es ++ [e]) ++ List.replicate N false := ⟨_, rfl⟩
  have hallEv : esAll = GalilScaffoldAdvanceClock.advances 2048 2048
      ((av ++ List.replicate N false).map (fun b => (b, true))) := by
    rw [hesAll, List.map_append, GalilScaffoldAdvanceClock.advances_append, ← hev, List.map_replicate,
      advances_replicate_false]
  have hrunE : SearchRun center (es ++ [e]) v0 vq := searchRun_append hrun (.cons hstep (.nil _))
  have hrunAll : SearchRun center esAll v0 vq := by
    rw [hesAll]; exact searchRun_append hrunE (searchRun_pad center N vq (Or.inl hfound))
  have hlenAll : N ≤ esAll.length := by rw [hesAll]; simp; omega
  have hrunAll' : SearchRun center (esAll.take N ++ esAll.drop N) v0 vq := by
    rw [List.take_append_drop]; exact hrunAll
  obtain ⟨vN, hrunN, _⟩ := searchRun_split _ _ hrunAll'
  have hesN : esAll.take N = GalilScaffoldAdvanceClock.advances 2048 2048
      (((av ++ List.replicate N false).take N).map (fun b => (b, true))) := by
    rw [List.map_take, GalilScaffoldAdvanceClock.advances_take, ← hallEv]
  have hlenN : (esAll.take N).length = max k 1
      + (2*k + 2*((GalilScaffoldPlace.stream center).take (8*max k 1+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (8*max k 1) := by
    rw [List.length_take, hN]; omega
  obtain ⟨as, bs, used, rest, v2, v3, hsplit, hasl, hr12, hr3, _, hm2, hq, hnr, ⟨dpv, hx3, hres⟩,
      hdebt, hc3, hn3, hspan2, hl3, htick⟩ :=
    first_stage_aligned center lower radius hlc k hk hrc rad hrad hr hrunN hsearch hlower hesN hlenN
  have hrunU : SearchRun center (as ++ bs ++ used) v0 v3 := searchRun_append hr12 hr3
  have hUpre : as ++ bs ++ used <+: esAll := by
    refine ⟨rest ++ esAll.drop N, ?_⟩
    conv_rhs => rw [← List.take_append_drop N esAll]
    rw [hsplit]; simp [List.append_assoc]
  have hEpre : es ++ [e] <+: esAll := by rw [hesAll]; exact List.prefix_append _ _
  by_cases hA : es.length + 1 ≤ (as ++ bs ++ used).length
  · -- the found tick lies inside the first stage: export its own quantum
    have hp1 : es ++ [e] <+: as ++ bs ++ used :=
      List.prefix_of_prefix_length_le hEpre hUpre
        (by rw [List.length_append, List.length_singleton]; exact hA)
    obtain ⟨D, hD⟩ := hp1
    rw [← hD] at hrunU
    obtain ⟨vm, hvm1, hvm2⟩ := searchRun_split _ (es ++ [e]) hrunU
    have hvm : vm = vq := searchRun_unique hvm1 hrunE
    have h3 : v3 = vq := by
      have := searchRun_terminal hvm2 (by rw [hvm]; exact Or.inr (Or.inl hfound))
      rw [this, hvm]
    have hf3 : v3.search.mode = .found := by rw [h3]; exact hfound
    obtain ⟨h, hres', hpc, hpos, hcand, hmin⟩ :=
      found_facts (S := 8 * max k 1) center hq hm2 hf3 hx3 hres
    refine ⟨k, 8 * max k 1, v2.search, vq.search, v2.dp, used, ?_, hm2, hfound, ?_⟩
    · rw [h3] at hq; exact hq
    · rw [← h3]; exact hres'
  · -- the first stage exits before the tick: continue into the later stages
    have hp2 : as ++ bs ++ used <+: es :=
      List.prefix_of_prefix_length_le hUpre ((List.prefix_append es [e]).trans hEpre) (by omega)
    obtain ⟨R, hR⟩ := hp2
    rw [← hR] at hrun
    obtain ⟨vm, hvm1, hvm2⟩ := searchRun_split _ _ hrun
    have hvm : vm = v3 := searchRun_unique hvm1 hrunU
    subst hvm
    have hev' : (as ++ bs ++ used) ++ (R ++ [e]) =
        GalilScaffoldAdvanceClock.advances 2048 2048 (av.map (fun b => (b, true))) := by
      rw [← List.append_assoc, hR]; exact hev
    obtain ⟨_, hevR⟩ := advances_split 2048 av _ _ hev'
    have hcl3 := GalilScaffoldMatchClock.run_invariant 2048 2048
      (av.take (as ++ bs ++ used).length) (by decide) ⟨by decide, le_rfl⟩
    have hwd : vm.search.mode = .wait ∨ vm.search.mode = .double := by
      rcases GalilScaffoldSearchRun.quanta_exit_mode hq hm2 hnr with h | h | h | h
      · exfalso
        have h1 := searchRun_terminal hvm2 (Or.inr (Or.inl h))
        exact hu (by rw [h1]; exact h)
      · exfalso
        have h1 := searchRun_terminal hvm2 (Or.inr (Or.inr h))
        have h2 := searchStep_terminal hstep (by rw [h1]; exact Or.inr (Or.inr h))
        rw [h2, h1, h] at hfound
        exact absurd hfound (by decide)
      · exact Or.inl h
      · exact Or.inr h
    have hspanW : vm.search.mode = .wait → vm.search.span = ofNat (8 * max k 1) := by
      intro hw
      have hfr := (GalilScaffoldSearchRun.safe_quanta_frame hq).2
      simp [GalilScaffoldSearchRun.stageSpan, hw, hm2] at hfr
      rw [hfr, hspan2]
    have hworkD : vm.search.mode = .double →
        vm.search.work = ofNat (8 * max k 1) ∧ vm.search.span = ofNat 0 ∧ vm.search.quarter = 0 := by
      intro hdb
      have h1 := GalilScaffoldSearchRun.double_work_of_quanta hq hm2 hdb
      have h2 := GalilScaffoldSearchRun.double_reset_of_quanta hq hm2 hdb
      exact ⟨h1.trans hspan2, h2.1, h2.2⟩
    exact exit_continue_quantum center k (8 * max k 1) R
      (fun es' _ => later_quantum_all center k es'.length es' le_rfl)
      hwd hspanW hworkD hc3 hn3 hl3 (by omega) (by omega) (by omega)
      ⟨hvm2, hstep, hu, hfound⟩ hevR ⟨hcl3.1, hcl3.2.1⟩

/-! ## 2. At the machine tick, through the closeout contracts -/

/-- **`LaterQuantumC` at the tick.**  The entry is the contract bundle
`StageEntryC` + `SegReachedW` (no `StartShape`, no `hpres`, no `hpos`), and the
restart decomposition is `hE.stage`'s own `ReplayStage`, transported across the
reached segment by `replayStage_trans`. -/
theorem laterQuantum_at_tick (centreC : GalilVM → Fin 3)
    (placeC : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (hP : Decodes (PofC centreC placeC entry w))
    {c c' : Control} {r t : GalilVM}
    (hE : StageEntryC (PofC centreC placeC entry w) q first w c r)
    (hsW : SegReachedW centreC placeC entry q first w c r c' t)
    (aF : Bool) (hcl : aF = true → c'.clock = 1) (hidle : t.chain = .idle)
    (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool)
    (hcen : t.center = represent ⟨a :: ls, gap⟩ (rs.map some) qq)
    (vq : SearchVM) (hq : searchEffect (PofC centreC placeC entry w) aF t vq)
    (hfound : vq.search.mode = .found) :
    CloseoutPrepInputs3.LaterQuantumC ⟨a :: ls, gap⟩ vq.dp := by
  obtain ⟨-, es, hseg⟩ := hsW
  obtain ⟨r0, Rad, last, es0, c0, hR0, hSt0, hcl0, hseg0⟩ :=
    replayStage_trans hE.stage hseg
  obtain ⟨hidle0, hrep0, hfoc0, hscan0, ⟨hrc, hrv⟩, -, hsearch, hlower, hlast, hlv⟩ := hR0
  have hcen0 : r0.center = represent ⟨a :: ls, gap⟩ (rs.map some) qq := by
    rw [← watchSegE_center (PofC centreC placeC entry w) q first 2048 hseg0]; exact hcen
  obtain ⟨hreadr, hplr⟩ := hP.1 r0 a ls rs qq gap hcen0
  obtain ⟨k, hk⟩ : ∃ k : ℕ, value last = (k : ℤ) :=
    ⟨(value last).toNat, (Int.toNat_of_nonneg hlv).symm⟩
  have hstep : searchStep ((PofC centreC placeC entry w).place t) aF (searchLens.get t) vq := by
    rcases hq with ⟨-, hstep⟩ | ⟨hne, -⟩
    · exact hstep
    · exact absurd hidle hne
  have hrunSeg0 := watchSegE_searchRun (PofC centreC placeC entry w) q first 2048 hP.2 hseg0 hidle
  have hrunSeg := hrunSeg0
  rw [hplr] at hrunSeg
  have hcen1 : t.center = r0.center :=
    watchSegE_center (PofC centreC placeC entry w) q first 2048 hseg0
  rw [hP.2 t r0 hcen1, hplr] at hstep
  obtain ⟨av1, hav1, hes1, hcl1, -⟩ :=
    watchSegE_clock (PofC centreC placeC entry w) q first 2048 hseg0
  rw [hcl0] at hes1 hcl1
  have hev : es0 ++ [aF] = GalilScaffoldAdvanceClock.advances 2048 2048
      ((av1 ++ [aF]).map (fun b => (b, true))) := by
    rw [List.map_append, GalilScaffoldAdvanceClock.advances_append, map_fst_map_pair, ← hcl1, ← hes1]
    congr 1
    cases aF
    · rfl
    · rw [hcl rfl]; rfl
  have hu : (searchLens.get t).search.mode ≠ .found := by
    cases hes : es0 with
    | nil =>
      rw [hes] at hrunSeg
      have he : searchLens.get t = searchLens.get r0 := searchRun_unique hrunSeg (.nil _)
      rw [he]
      show r0.search.mode ≠ _
      rw [hsearch]
      simp [GalilScaffoldSearchFinish.begin]
    | cons x xs =>
      exact watchSegE_search_not_found (PofC centreC placeC entry w) q first 2048 hP.2 hseg0 hidle
        es0 [] _ (by simp) (by rw [hes]; simp) hrunSeg0
  exact first_quantum ⟨a :: ls, gap⟩ last r0.radius hlast k hk hrc Rad hrv (hSt0 k hk)
    hsearch hlower ⟨hrunSeg, hstep, hu, hfound⟩ hev

/-! ## 3. `prepInputs3_of_found` with neither named hypothesis -/

/-- **`prepInputs3_of_found_or_later` with `hlater` discharged.**  Compared with
`CloseoutPrepInputs3.prepInputs3_of_found` this drops `FirstStageC`, and
compared with `prepInputs3_of_found_or_later` it drops `LaterQuantumC`: the
preparation inputs of the found comparison follow from the contracts, the
decoding and the tick alone. -/
theorem prepInputs3_of_found_C (centreC : GalilVM → Fin 3)
    (placeC : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (hP : Decodes (PofC centreC placeC entry w))
    {c c' cP : Control} {r t sP : GalilVM}
    (hE : StageEntryC (PofC centreC placeC entry w) q first w c r)
    (hsW : SegReachedW centreC placeC entry q first w c r c' t)
    (aF : Bool) (hcl : aF = true → c'.clock = 1) (hidle : t.chain = .idle)
    (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool)
    (hcen : t.center = represent ⟨a :: ls, gap⟩ (rs.map some) qq)
    (vq : SearchVM) (hq : searchEffect (PofC centreC placeC entry w) aF t vq)
    (hfound : vq.search.mode = .found)
    (hpost : CloseoutPrepInputs3.PostCompareG ⟨a :: ls, gap⟩ vq.dp cP sP) :
    ∃ lower span : ℕ,
      CloseoutPrepInputs3.PrepInputsG3 (PofC centreC placeC entry w) q first ⟨a :: ls, gap⟩
        lower span cP sP :=
  CloseoutPrepInputs3.prepInputs3_of_found_or_later centreC placeC entry q first w hP hE hsW aF
    hcl hidle a ls rs qq gap hcen vq hq hfound hpost
    (laterQuantum_at_tick centreC placeC entry q first w hP hE hsW aF hcl hidle a ls rs qq gap
      hcen vq hq hfound)

end PalPeg.CloseoutLaterEntry

#print axioms PalPeg.CloseoutLaterEntry.first_quantum
#print axioms PalPeg.CloseoutLaterEntry.laterQuantum_at_tick
#print axioms PalPeg.CloseoutLaterEntry.prepInputs3_of_found_C
