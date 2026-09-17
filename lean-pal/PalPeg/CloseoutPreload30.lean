import PalPeg.CloseoutPreload29

/-!
# `postRunC_of_machine` — and why its hypothesis list is inconsistent

The readiness chain `PostRun` (`CloseoutPreload8`) → `PostRunP`
(`CloseoutPreload17`) → `PostRunC` (`CloseoutPreload24`) → `PostRunD`
(`CloseoutPreload29`) hangs on `postRunC_of_machine : PostRunC`, the induction
over all later `.run` entries.  Every consumer of `PostRunC` since
`CloseoutPreload24` takes the pair

* `hsup : ScanSupplyInv F 2048 I` — the supply invariant, and
* `hreal : ScanRealized F I` — "every `bs : List Bool` is the event list of a
  scan leg entered under `I` and in phase".

§1 shows the pair is **inconsistent**: `prefixPhase_of_scan_inv` turns any such
leg into `PrefixPhase bs`, i.e. `bs.length ≤ 2048 * bs.count true + 2047`, and
`bs = List.replicate 2048 false` violates it.  So `ScanRealized F I` is false on
every frame that has a supply invariant — in particular the named residue
`H_scanRealized` on `galilFrameS` is *refutable* once `bigPack2_scanSupply`'s
own residues hold — and every theorem taking both (`runEntriesS_of_stageInv2C`,
`runEntriesS_of_restartS2C`, `readyClosure_S2C`, `replay_final_of_decodes_S2C`,
`runEntriesS_of_stageInvPPC`, `runEntriesS_of_double_exitC`,
`double_leg_entries_windowC`, `round_trip_entries`, `runEntriesS_of_stageInvD`,
`runEntriesS_of_double_exitD`, `postRunD_of_machine`,
`postRunD_of_machine_galil`) is vacuous.  `postRunC_of_machine_vacuous` records
the consequence explicitly so it is not mistaken for progress.

§2 isolates what the consumers actually use `hreal` for: a `PrefixPhase` bound
on the stage's *own* preparation prefix.  `PostRunPh` is `PostRunP` at slack
`2047` stated through that bound; it sits strictly between `PostRunP` and
`PostRunC` and carries no realizability clause.  The honest replacement for
`ScanRealized` is therefore "`PrefixPhase bs` for every preparation prefix `bs`
a `StagePrep2` stage *reaches*", a fact about the clock firing every `2048`
ticks along a reachable scan leg — not a statement over all lists.

§3 closes the two `.run` exit kinds that need no budget at all: `.found` and
`.missed` are absorbing (`CloseoutPreload8` §1), so `RunEntriesS` holds for
every continuation.

§4 records, exit kind by exit kind, why the non-vacuous induction still does
not compose from the leg lemmas as stated.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload30

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.CloseoutReadyStage (DpSafeStage PacedL RunEntriesS RunEntryS)
open PalPeg.CloseoutPreload8 (step_found_fix step_missed_fix)
open PalPeg.CloseoutPreload17 (PostRunP)
open PalPeg.CloseoutPreload18 (PrefixPhase pacedL_suffix_2047)
open PalPeg.CloseoutPreload23 (ScanSupplyInv prefixPhase_of_scan_inv)
open PalPeg.CloseoutPreload24 (PostRunC ScanRealized)

/-! ## 1. `ScanSupplyInv ∧ ScanRealized` is inconsistent -/

section Absurd

variable {σ : Type} {F : Frame σ} {I : State σ → Prop}

/-- **NAMED — the realizability clause is refutable under the supply
invariant.**  `ScanRealized F I` hands a scan leg for the all-background list
of length `2048`; under `ScanSupplyInv` that leg is phase-bounded
(`prefixPhase_of_scan_inv`), which forces `2048 ≤ 2047`. -/
theorem scanRealized_absurd (hsup : ScanSupplyInv F 2048 I) (hreal : ScanRealized F I) :
    False := by
  obtain ⟨ts, p, q, hsc, hp, hcl⟩ := hreal (List.replicate 2048 false)
  have h := prefixPhase_of_scan_inv hsup hsc hp hcl.1 hcl.2
  unfold PrefixPhase at h
  rw [List.length_replicate, List.count_replicate] at h
  simp only [beq_iff_eq, Bool.false_eq_true, if_false, mul_zero, zero_add] at h
  omega

#print axioms scanRealized_absurd

/-- **`postRunC_of_machine` on the hypothesis list every consumer since
`CloseoutPreload24` uses — vacuous by §1.**  This is *not* a proof of the
post-run contract; it is the record that the pair `(hsup, hreal)` proves
anything, so no theorem downstream of it says anything about the machine. -/
theorem postRunC_of_machine_vacuous (hsup : ScanSupplyInv F 2048 I)
    (hreal : ScanRealized F I) : PostRunC :=
  (scanRealized_absurd hsup hreal).elim

#print axioms postRunC_of_machine_vacuous

end Absurd

/-! ## 2. The phase-bounded contract, without the realizability clause -/

/-- **NAMED — `PostRunP` at the clock's slack, stated through the prefix's
phase bound.**  This is exactly what `PostRunC`'s consumers extract from
`ScanRealized` (`prefixPhase_of_scan_inv` on the preparation prefix); nothing
else of the scan leg is used.  The obligation it leaves on the machine is
`PrefixPhase bs` for the *reachable* preparation prefixes only. -/
def PostRunPh : Prop :=
  ∀ (v : SearchVM) (as bs : List Bool), v.search.mode = Mode.run →
    DpSafeStage v as → PrefixPhase bs → PacedL 2048 0 (bs ++ as) → RunEntriesS as v

theorem postRunPh_of_postRunP (h : PostRunP) : PostRunPh :=
  fun v as _ hm hsafe hph hpaced => h v as 2047 hm hsafe (pacedL_suffix_2047 hpaced hph)

theorem postRunC_of_postRunPh (h : PostRunPh) : PostRunC :=
  fun {_ _ _} hsup {_ bs _ _} hsc hp hcl v as hm hsafe hpaced =>
    h v as bs hm hsafe (prefixPhase_of_scan_inv hsup hsc hp hcl.1 hcl.2) hpaced

#print axioms postRunPh_of_postRunP
#print axioms postRunC_of_postRunPh

/-! ## 3. The absorbing exits carry `RunEntriesS` for free -/

/-- A `.found` state never re-enters `.run` (`step_found_fix`), so the ledger
is trivially kept on every continuation. -/
theorem runEntriesS_of_found {v : SearchVM} (hm : v.search.mode = Mode.found) :
    ∀ as : List Bool, RunEntriesS as v
  | [] => trivial
  | a :: as => by
      intro c v' hs
      have he := step_found_fix hm hs
      subst he
      refine ⟨fun _ _ hr => ?_, runEntriesS_of_found hm as⟩
      rw [hm] at hr
      exact absurd hr (by decide)

/-- The same for `.missed` (`step_missed_fix`). -/
theorem runEntriesS_of_missed {v : SearchVM} (hm : v.search.mode = Mode.missed) :
    ∀ as : List Bool, RunEntriesS as v
  | [] => trivial
  | a :: as => by
      intro c v' hs
      have he := step_missed_fix hm hs
      subst he
      refine ⟨fun _ _ hr => ?_, runEntriesS_of_missed hm as⟩
      rw [hm] at hr
      exact absurd hr (by decide)

#print axioms runEntriesS_of_found
#print axioms runEntriesS_of_missed

/-!
## 4. What is left — the non-vacuous induction, exit kind by exit kind

`PostRunC` (equivalently `PostRunPh`) asks, from a `.run` state `v` with
`DpSafeStage v as` and the stream paced from the stage entry, for
`RunEntriesS as v`.  The induction is on the event list; while `v` stays in
`.run`, `RunEntryS` is vacuous and `dpSafeStage_step` (via `run_step_quanta`)
carries the witness, so only the exit tick matters.  By `run_exit_frame` the
exit is one of four modes:

* **`.found` / `.missed` — closed** (§3, `runEntriesS_of_found` /
  `runEntriesS_of_missed`).
* **`.wait` → `.double` → `prepare` → next `.run` entry — does not compose
  from `PostRunC`'s own premises.**  Three mismatches, none of them the budget:
  1. *Frame.*  `wait_exit_double` / `double_spends` / `prepAt_of_double_exit`
     need `v.search.span = ofNat mw`, `v.lower = ofNat k`, the calibration
     `8 * max k 1 ≤ mw`, `Canonical` debt and the DP preload at the `.run`
     entry.  `DpSafeStage v as` carries none of these (it is a statement about
     the DP tapes and the charged prefix only), so `PostRunC`'s conclusion is
     asked of a `.run` state whose window and lower bound are unknown.  The
     contract that the leg lemmas *can* prove is a `PostRunF` whose premise is
     the entry frame (`PrepAt k mw`-shaped data at the `.run` entry, as
     `CloseoutPreload12.entry_preload_at_prep` / `entry_debt_at_prep` deliver).
  2. *Phase at the next stage.*  `dpSafe_of_stagePrepD` / `bal_of_paced` want
     `PacedL 2048 0` measured from the `.double` exit, but the stream there is
     a suffix of `bs ++ as`; its slack is `≤ 2047` only under `PrefixPhase` of
     the whole prefix (preparation + `.run` leg + `.wait` leg + `.double` leg),
     which is a clock fact (`prefixPhase_of_scan_inv`) about a `ScanTrace`
     covering those legs — not derivable from `PacedL` (which bounds the count
     above, `PrefixPhase` bounds it below).  So either the stage invariant
     `StagePrep2` / `dpDemand` is restated at slack `2047`, or the induction
     carries the `ScanTrace` of the entire stream.
  3. *Realizability.*  The only machine input the consumers use is
     `PrefixPhase` of the preparation prefix, and `ScanRealized` supplies it for
     all lists — which §1 refutes.  The correct clause is `PrefixPhase bs` for
     every `bs` with `ReachP w bs x` from a `PrepAt` state that is itself a
     `.double` exit of the machine; it needs the coupling between `searchStep`'s
     boolean and the `Tick` branch (`CloseoutPreload21` §4) as before, but now
     quantified over reachable prefixes only.
* **scan exit (the controller leaves `.scan` mid-leg)** — `PostRunC` and
  `RunEntriesS` are statements about `searchStep` on the search VM alone and do
  not see the controller mode, so no case arises on the search VM; on the
  machine, `runP_exit_debt_at_exit_scan` is the budget at the *search* exit
  under a `ScanTrace` prefix and is unaffected by §1 (it does not take
  `ScanRealized`).

Net: the readiness chain from `PostRunC` downwards must be re-based on
`PostRunPh` (or a framed `PostRunF`) with a reachable-prefix phase clause in
place of `ScanRealized`; until then `postRunD_of_machine` and its consumers
prove nothing about `galilFrameS`.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload30
