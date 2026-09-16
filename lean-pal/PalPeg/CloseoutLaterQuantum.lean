import PalPeg.GalilLaterRadius
import PalPeg.CloseoutPrepInputs3

/-!
# `LaterQuantumC` at the found tick

`CloseoutPrepInputs3.LaterQuantumC p y` is

```
∃ (lower span : ℕ) (sq tq : GalilScaffoldSearchFinish.State)
  (x : GalilScaffoldControl.Machine 12) (as : List Bool),
  GalilScaffoldSearchRun.SafeQuanta sq x as tq y ∧ sq.mode = .run ∧ tq.mode = .found ∧
  GalilDpCorrect.Result ((GalilScaffoldPlace.stream p).take (span+1)) lower 0
    (GalilScaffoldProgram.denote y.config)
```

i.e. exactly the `SafeQuanta` + DP `Result` pair that
`GalilSearchResult.search_later_stage` produces, with `y` the DP machine of the
found tick.  The docstring of `CloseoutPrepInputs3` records it as NAMED because
`search_later_stage` needs a `.double` **entry** (`n % 4 = 0`, `8 ≤ n`,
`4*k ≤ n`, plus the stage length budget) and neither
`GalilLaterRadius.found_radius_le_all_stages` nor `later_found` exports that
entry at the found tick — they export the DP facts only.

This file supplies the missing export.  `GalilLaterRadius.later_found_step`
*does* re-establish the entry at every later stage: its `found` branch hands out
`later_stage_aligned`'s `SafeQuanta` on the window `2n`, and its exit branch
hands the next entry on through `wait_split` / `waiting_debt` (a `wait` exit) or
directly (a `double` exit).  That induction is redone here with the conclusion
weakened to `LaterQuantumC`, which drops the debt ledger, the previous-window
failure `hprev` and the match bound entirely — so what is exported is the entry,
not the ledger.

* `exit_continue_quantum` — the `wait`/`double` exit step.
* `quantum_goal_step`, `later_quantum_all` — the induction on the event list.
* `later_stage_entry_at_tick` — `LaterQuantumC center vq.dp` at any found tick
  reached from a later-stage entry.

**What remains NAMED.**  `later_stage_entry_at_tick` still asks for its own
later-stage entry, so a consumer at a *machine* tick (e.g.
`CloseoutPrepInputs3.prepInputs3_of_found_or_later`, where the search state is
the `vq` of `searchEffect P aF t vq`) still needs

`LaterEntryAtSearchEffect` :
  `∀ (P : Shared) (t : GalilVM) (aF : Bool) (vq : SearchVM),
     searchEffect P aF t vq → vq.search.mode = .found →
     ∃ (k n clock : ℕ) (v0 u : SearchVM) (e : Bool) (es av : List Bool),
       GalilLaterRadius.LaterEntry k n clock v0 ∧
       GalilLaterRadius.FoundTick (P.place t) es v0 u e vq ∧
       es ++ [e] = GalilScaffoldAdvanceClock.advances 2048 clock (av.map (fun b => (b, true)))`

— the restart-to-later-stage decomposition of the search run inside
`searchEffect`.  `GalilLaterRadius.found_radius_le_all_stages` builds exactly
this decomposition internally (it is where `later_found` is applied) but does
not export it; factoring it out of that proof is the remaining work.  With it,
`LaterQuantumC` is discharged by `later_stage_entry_at_tick`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutLaterQuantum

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilSearchReadyInv PalPeg.GalilSearchWait
open GalilScaffoldCounter
open PalPeg.GalilLaterRadius

/-- The `LaterGoal` of `GalilLaterRadius` with the conclusion replaced by the
quantum export `LaterQuantumC` (and `hprev` dropped: `LaterQuantumC` says
nothing about the previous window). -/
def QuantumGoal (center : GalilScaffoldPlace.Place) (k : ℕ) (es : List Bool) : Prop :=
  ∀ (n clock : ℕ) (v0 u vq : SearchVM) (e : Bool) (av : List Bool),
    LaterEntry k n clock v0 → FoundTick center es v0 u e vq →
    es ++ [e] = GalilScaffoldAdvanceClock.advances 2048 clock (av.map (fun b => (b, true))) →
    CloseoutPrepInputs3.LaterQuantumC center vq.dp

/-- `GalilLaterRadius.exit_continue` for `QuantumGoal`: from a `wait`/`double`
exit of a stage whose window was `S`, the next stage reaches the found tick. -/
theorem exit_continue_quantum (center : GalilScaffoldPlace.Place) (k S : ℕ) (R : List Bool)
    (ih : ∀ es' : List Bool, es'.length ≤ R.length → QuantumGoal center k es')
    {v3 u vq : SearchVM} {e : Bool} {clock3 : ℕ} {av3 : List Bool}
    (hmode : v3.search.mode = .wait ∨ v3.search.mode = .double)
    (hspan : v3.search.mode = .wait → v3.search.span = ofNat S)
    (hwork : v3.search.mode = .double →
      v3.search.work = ofNat S ∧ v3.search.span = ofNat 0 ∧ v3.search.quarter = 0)
    (hc : Canonical v3.search.debt) (hnn : 0 ≤ value v3.search.debt) (hlow : v3.lower = ofNat k)
    (hS4 : S % 4 = 0) (hS8 : 8 ≤ S) (hSk : 4*k ≤ S)
    (hft : FoundTick center R v3 u e vq)
    (hev : R ++ [e] = GalilScaffoldAdvanceClock.advances 2048 clock3 (av3.map (fun b => (b, true))))
    (hclock3 : 1 ≤ clock3 ∧ clock3 ≤ 2048) :
    CloseoutPrepInputs3.LaterQuantumC center vq.dp := by
  obtain ⟨hrun, hstep, hu, hfound⟩ := hft
  rcases hmode with hw | hd
  · have hrunE : SearchRun center (R ++ [e]) v3 vq := searchRun_append hrun (.cons hstep (.nil _))
    obtain ⟨ws, b, L', hsplit, hval, hburn⟩ :=
      wait_split center (R ++ [e]) v3 vq hrunE hw hc (by rw [hfound]; decide)
    have hev' : ws ++ b :: L' =
        GalilScaffoldAdvanceClock.advances 2048 clock3 (av3.map (fun b => (b, true))) := by
      rw [← hsplit]; exact hev
    obtain ⟨_, hB⟩ := advances_split clock3 av3 ws (b :: L') hev'
    have hclW := GalilScaffoldMatchClock.run_invariant 2048 clock3 (av3.take ws.length) (by decide)
      hclock3
    obtain ⟨x, avW', hxav, hbx, hL'⟩ := advances_cons_head _ b L' _ hB
    obtain ⟨v4, hrun4, hm4, hq4, hw4, hs4, hc4, hd4, hcl4, hl4, hv4⟩ :=
      waiting_debt center ws x _ ⟨hclW.1, hclW.2.1⟩ v3 hw hc hval hburn S (hspan hw)
    rw [← hbx] at hrun4 hv4
    rcases List.eq_nil_or_concat L' with hnil | ⟨L'', e', hcat⟩
    · exfalso
      rw [hnil] at hsplit
      rw [hsplit] at hrunE
      have := searchRun_unique hrunE hrun4
      rw [this, hm4] at hfound
      exact absurd hfound (by decide)
    · rw [List.concat_eq_append] at hcat
      rw [hcat] at hsplit
      have hsplit' : R ++ [e] = (ws ++ b :: L'') ++ [e'] := by rw [hsplit]; simp
      obtain ⟨hR, he⟩ := List.append_inj' hsplit' rfl
      simp only [List.cons.injEq, and_true] at he
      subst he
      rw [hR, show ws ++ b :: L'' = (ws ++ [b]) ++ L'' by simp] at hrun
      obtain ⟨vm, hrm, hrest⟩ := searchRun_split _ (ws ++ [b]) hrun
      have hvm : vm = v4 := searchRun_unique hrm hrun4
      subst hvm
      have hlen : L''.length ≤ R.length := by rw [hR]; simp; omega
      exact ih L'' hlen S _ vm u vq e avW'
        ⟨hm4, hq4, hw4, hs4, hc4, hd4, by rw [hl4, hlow], hS4, hS8, hSk, hcl4.1, hcl4.2⟩
        ⟨hrest, hstep, hu, hfound⟩ (by rw [← hcat]; exact hL')
  · obtain ⟨hw3, hs3, hq3⟩ := hwork hd
    exact ih R le_rfl S clock3 v3 u vq e av3
      ⟨hd, hq3, hw3, hs3, hc, Or.inl hnn, hlow, hS4, hS8, hSk, hclock3.1, hclock3.2⟩
      ⟨hrun, hstep, hu, hfound⟩ hev

/-- One later stage, for `QuantumGoal`: either the found tick is inside this
stage — and then `later_stage_aligned`'s `SafeQuanta` on the window `2n` is the
export — or the stage exits in `wait`/`double` and `exit_continue_quantum`
carries the entry to the next stage. -/
theorem quantum_goal_step (center : GalilScaffoldPlace.Place) (k : ℕ) (es : List Bool)
    (ih : ∀ es' : List Bool, es'.length < es.length → QuantumGoal center k es') :
    QuantumGoal center k es := by
  intro n clock v0 u vq e av hent hft hev
  obtain ⟨hm0, hq0, hw0, hs0, hcanon, hd, hlow, hn4, hn8, hnk, hcl1, hcl2⟩ := hent
  obtain ⟨hrun, hstep, hu, hfound⟩ := hft
  obtain ⟨N, hN⟩ : ∃ N, n + (2*k + 2*((GalilScaffoldPlace.stream center).take (2*n+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (2*n) = N := ⟨_, rfl⟩
  have hNn : n ≤ N := by rw [← hN]; omega
  obtain ⟨esAll, hesAll⟩ : ∃ l, l = (es ++ [e]) ++ List.replicate N false := ⟨_, rfl⟩
  have hallEv : esAll = GalilScaffoldAdvanceClock.advances 2048 clock
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
  have hesN : esAll.take N = GalilScaffoldAdvanceClock.advances 2048 clock
      (((av ++ List.replicate N false).take N).map (fun b => (b, true))) := by
    rw [List.map_take, GalilScaffoldAdvanceClock.advances_take, ← hallEv]
  have hlenN : (esAll.take N).length = n
      + (2*k + 2*((GalilScaffoldPlace.stream center).take (2*n+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (2*n) := by
    rw [List.length_take, hN]; omega
  obtain ⟨as, bs, used, rest, v2, v3, hsplit, hasl, hr12, hr3, _, hm2, hq, hnr, ⟨dpv, hx3, hres⟩,
      hdebt, hc3, hn3, hspan2, hl3⟩ :=
    later_stage_aligned center k n clock hrunN hm0 hq0 hw0 hs0 hcanon hd hlow hn4 hn8 hnk hesN
      ⟨hcl1, hcl2⟩ hlenN
  have hrunU : SearchRun center (as ++ bs ++ used) v0 v3 := searchRun_append hr12 hr3
  have hUpre : as ++ bs ++ used <+: esAll := by
    refine ⟨rest ++ esAll.drop N, ?_⟩
    conv_rhs => rw [← List.take_append_drop N esAll]
    rw [hsplit]; simp [List.append_assoc]
  have hEpre : es ++ [e] <+: esAll := by rw [hesAll]; exact List.prefix_append _ _
  by_cases hA : es.length + 1 ≤ (as ++ bs ++ used).length
  · -- the found tick is inside this stage: export its quantum
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
    obtain ⟨h, hres', hpc, hpos, hcand, hmin⟩ := found_facts (S := 2*n) center hq hm2 hf3 hx3 hres
    refine ⟨k, 2*n, v2.search, vq.search, v2.dp, used, ?_, hm2, hfound, ?_⟩
    · rw [h3] at hq; exact hq
    · rw [← h3]; exact hres'
  · -- the stage exits before the tick
    have hp2 : as ++ bs ++ used <+: es :=
      List.prefix_of_prefix_length_le hUpre ((List.prefix_append es [e]).trans hEpre) (by omega)
    obtain ⟨R, hR⟩ := hp2
    rw [← hR] at hrun
    obtain ⟨vm, hvm1, hvm2⟩ := searchRun_split _ _ hrun
    have hvm : vm = v3 := searchRun_unique hvm1 hrunU
    subst hvm
    have hev' : (as ++ bs ++ used) ++ (R ++ [e]) =
        GalilScaffoldAdvanceClock.advances 2048 clock (av.map (fun b => (b, true))) := by
      rw [← List.append_assoc, hR]; exact hev
    obtain ⟨_, hevR⟩ := advances_split clock av _ _ hev'
    have hcl3 := GalilScaffoldMatchClock.run_invariant 2048 clock
      (av.take (as ++ bs ++ used).length) (by decide) ⟨hcl1, hcl2⟩
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
    have hspanW : vm.search.mode = .wait → vm.search.span = ofNat (2*n) := by
      intro hw
      have hfr := (GalilScaffoldSearchRun.safe_quanta_frame hq).2
      simp [GalilScaffoldSearchRun.stageSpan, hw, hm2] at hfr
      rw [hfr, hspan2]
    have hworkD : vm.search.mode = .double →
        vm.search.work = ofNat (2*n) ∧ vm.search.span = ofNat 0 ∧ vm.search.quarter = 0 := by
      intro hdb
      have h1 := GalilScaffoldSearchRun.double_work_of_quanta hq hm2 hdb
      have h2 := GalilScaffoldSearchRun.double_reset_of_quanta hq hm2 hdb
      exact ⟨h1.trans hspan2, h2.1, h2.2⟩
    exact exit_continue_quantum center k (2*n) R
      (fun es' hl => ih es' (by rw [← hR]; simp only [List.length_append]; omega))
      hwd hspanW hworkD hc3 hn3 (by rw [hl3, hlow]) (by omega) (by omega) (by omega)
      ⟨hvm2, hstep, hu, hfound⟩ hevR ⟨hcl3.1, hcl3.2.1⟩

theorem later_quantum_all (center : GalilScaffoldPlace.Place) (k : ℕ) :
    ∀ (N : ℕ) (es : List Bool), es.length ≤ N → QuantumGoal center k es := by
  intro N
  induction N with
  | zero => intro es hl; exact quantum_goal_step center k es (fun es' h => absurd h (by omega))
  | succ N ih => intro es hl; exact quantum_goal_step center k es (fun es' h => ih es' (by omega))

/-- **The tick-level export.**  From any later-stage entry, the found tick of
the run carries `CloseoutPrepInputs3.LaterQuantumC` on its own DP machine. -/
theorem later_stage_entry_at_tick (center : GalilScaffoldPlace.Place) (k n clock : ℕ)
    {v0 u vq : SearchVM} {e : Bool} {es av : List Bool}
    (hent : LaterEntry k n clock v0)
    (hft : FoundTick center es v0 u e vq)
    (hev : es ++ [e] = GalilScaffoldAdvanceClock.advances 2048 clock (av.map (fun b => (b, true)))) :
    CloseoutPrepInputs3.LaterQuantumC center vq.dp :=
  later_quantum_all center k es.length es le_rfl n clock v0 u vq e av hent hft hev

end PalPeg.CloseoutLaterQuantum

#print axioms PalPeg.CloseoutLaterQuantum.exit_continue_quantum
#print axioms PalPeg.CloseoutLaterQuantum.quantum_goal_step
#print axioms PalPeg.CloseoutLaterQuantum.later_stage_entry_at_tick
