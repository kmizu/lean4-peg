import PalPeg.GalilArriveChain
import PalPeg.GalilThrottledRunGen
import PalPeg.GalilTraceCost
import PalPeg.GalilCheckpoints
import PalPeg.GalilEmptyWord
import PalPeg.GalilBootVM
import PalPeg.GalilRunSkeleton

/-!
# Final top-down assembly: the exact remaining obligation list

`pal_in_peg_final` composes

* `GalilArriveChain.pal_in_peg_of_latch'`
* ← `GalilThrottledRunGen.abstractRun_throttled_2p18` / `ledger_throttled_2p18`
* ← `GalilTraceCost.checkpoints_cost` booted at `GalilBootVM.initVM0` through
  `GalilCheckpoints.inv_init_pos`
* and `GalilEmptyWord.realize_accept'_nil` for the empty word,

with the concrete shared record `PofC centre place entry`, fixed `q first`,
`delay = 2048`, arrival spacing `τ = GalilLedgerThrottled.ticksPerSymbol = 2^18`.

The pre-loaded trace is not a fixed term: `checkpoints_cost` only asserts its
existence.  Every hypothesis about the trace is therefore stated for **every**
trace satisfying `PreTrace` (the conclusion of `checkpoints_cost`, booted at
`initVM0`).

## Remaining obligations (the hypothesis list of `pal_in_peg_final`)

(A) oracle leaves
  * `H_oracle`     — `CycleOracleMC (PofC centre place entry w) q first w` for all nonempty `w`.

(B) throttling
  * `H_truncTick`  — `TruncTick w st (Tc |w|) (galilFrameS …) 2048` on every `PreTrace`.
  * `H_suf`        — `SufVM w (st k).vm` for `k ≤ Tc |w|` on every `PreTrace`.
  * `H_needLe`     — `Preload.needLe`: `need w st k ≤ m+1` for `k < Tc (m+1)`, `m < |w|`.
  * `H_base`       — `O_base`: `Tc 1 ≤ 2050` on every `PreTrace`.

(C) local realization
  * `H_realize`    — a `LocalStep` realized with `accept'` whose acceptance on nonempty
    `w` is `LatchTrue` of the `2^18`-throttled run of every `PreTrace`, by the deadline
    `(|w|+1)·2^18`.

(D) misc
  * none left: `needS … 0 = 0` at the boot state (`needS_boot`), `H_letter`/`H_first`
    (`rfl` for `PofC`), `H_empty` (`realize_accept'_nil`), `0 < B` (`n * cnt K`),
    `Preload.tc0`/`mono`, `O_cost` and the report point at `|w|` are all proved here.

## Adapters

* `preTrace_exists`   — `CycleOracleMC` ⇒ some `PreTrace` (boot through `inv_init_pos`,
  `invL_of_run`, then `checkpoints_cost`).
* `preload_of_preTrace` — `PreTrace` (`Trace`-shaped, monotone in `m ≤ m'`) plus
  `H_needLe` ⇒ `ThrottledRun.Preload` (step-monotone, `need0`).
* The report-point mismatch (`GalilReportPrefix.ReportPointAt` vs
  `GalilLedgerAssembly.ReportPointAt`) is already bridged inside `checkpoints_cost`
  (`ledgerAt_of_prefix`), so `PreTrace.report` is stated in the ledger form.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PalPeg.GalilFinalAssembly

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilTickArrive PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.GalilThrottledRun PalPeg.GalilThrottledRunGen PalPeg.GalilLedgerQ64
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleLocal

/-- Arrival spacing of the final run. -/
abbrev τF : ℕ := GalilLedgerThrottled.ticksPerSymbol

/-- The boot state: initial controller (delay 2048) on `initVM0 w`. -/
def boot (w : List (Fin 2)) : State GalilVM := ⟨GalilScaffoldController.initial 2048, GalilBootVM.initVM0 w⟩

/-- The pre-loaded checkpoint trace of `w`: the conclusion of `checkpoints_cost`
booted at `boot w`. -/
structure PreTrace (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) :
    Prop where
  start : st 0 = boot w
  tc0 : Tc 0 = 0
  trace : Trace (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) st
    (Tc w.length)
  mono : ∀ m m', m ≤ m' → m' ≤ w.length → Tc m ≤ Tc m'
  report : ∀ m, 1 ≤ m → m ≤ w.length →
    PalPeg.GalilLedgerAssembly.ReportPointAt (PofC centre place entry w) q first w m (st (Tc m))
  cost : ∀ m, 1 ≤ m → m < w.length →
    Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048

/-! ## The named hypotheses -/

section Hyps
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- (A) The costed per-target cycle oracle holds for every nonempty input. -/
def H_oracle : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → CycleOracleMC (PofC centre place entry w) q first w

/-- (B) Truncation commutation along every pre-loaded trace. -/
def H_truncTick : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    TruncTick w st (Tc w.length) (galilFrameS (PofC centre place entry w) q first) 2048

/-- (B) Every FIFO stays a suffix of the pre-loaded word along every pre-loaded trace. -/
def H_suf : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ k, k ≤ Tc w.length → SufVM w (st k).vm

/-- (B) `Preload.needLe`: ticks before checkpoint `m+1` need at most `m+1` letters. -/
def H_needLe : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ m, m < w.length → ∀ k, k < Tc (m+1) → need w st k ≤ m+1

/-- (B) `O_base`: the first checkpoint is reached within 2050 ticks. -/
def H_base : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    Tc 1 ≤ 2050

/-- (C) A local step machine, realized with `accept'`, whose acceptance on nonempty
inputs is the latch of the `2^18`-throttled run of every pre-loaded trace. -/
def H_realize : Prop :=
  ∃ (Q' Γ' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (_ : Fintype Γ') (_ : DecidableEq Γ')
    (t K : ℕ) (L : PalPeg.Local.LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q')
    (outQ : Q' → Bool) (n : ℕ) (htape : 0 < t) (hn : 0 < n),
    ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
      ((L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn).SAccepts w ↔
        LatchTrue (PofC centre place entry w) q first w (stTG τF w st (Tc w.length))
          ((w.length + 1) * τF))

end Hyps

/-! ## Adapters -/

/-- The boot state consumes no letter. -/
theorem needS_boot (w : List (Fin 2)) (st : ℕ → State GalilVM) (h : st 0 = boot w) :
    needS w st 0 = 0 := by
  simp [needS, h, boot, usedVM, usedPH, usedChain, verOf, GalilBootVM.initVM0,
    GalilScaffoldChainInputSupply.initialHead]

/-- **Adapter `Trace`/`checkpoints_cost` → `Preload`.** -/
theorem preload_of_preTrace {centre : GalilVM → Fin 3} {place : GalilVM → GalilScaffoldPlace.Place}
    {entry q : ℕ} {first : Fin 9} {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (h : PreTrace centre place entry q first w st Tc)
    (hneed : ∀ m, m < w.length → ∀ k, k < Tc (m+1) → need w st k ≤ m+1) :
    Preload w st Tc :=
  ⟨h.tc0, fun m hm => h.mono m (m+1) (by omega) hm, needS_boot w st h.start, hneed⟩

/-- **Adapter oracle → pre-loaded trace**: boot through the `init` tick, then
`checkpoints_cost`. -/
theorem preTrace_exists (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (w : List (Fin 2)) (hw : 0 < w.length)
    (hor : CycleOracleMC (PofC centre place entry w) q first w) :
    ∃ st Tc, PreTrace centre place entry q first w st Tc := by
  rcases w with _ | ⟨a, rest⟩
  · simp at hw
  · obtain ⟨c1, t, hst, hI, hpos⟩ :=
      inv_init_pos (onLetterVM (a :: rest)) leftFirstVM centre place entry q first
        (GalilBootVM.initVM0 (a :: rest)) a rest
        (GalilBootVM.initVM0_right _) (GalilBootVM.initVM0_radius _)
        (GalilBootVM.initVM0_length _) (GalilBootVM.initVM0_replay _)
        (GalilBootVM.initVM0_shiftIdle _)
    obtain ⟨st, Tc, h0, hT0, htr, hmono, hrep, hcost⟩ :=
      checkpoints_cost (PofC centre place entry (a :: rest)) q first (a :: rest) hor hst
        (invL_of_run hst (GalilOracleDischarge.invS_of_inv hI)) (by omega)
    exact ⟨st, Tc, ⟨h0, hT0, htr, hmono, hrep, hcost⟩⟩

/-! ## The final theorem -/

/-- **`PAL ∈ PEG` from the remaining obligations (A)–(C).** -/
theorem pal_in_peg_final (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9)
    (hA : H_oracle centre place entry q first)
    (hB_trunc : H_truncTick centre place entry q first)
    (hB_suf : H_suf centre place entry q first)
    (hB_need : H_needLe centre place entry q first)
    (hB_base : H_base centre place entry q first)
    (hC : H_realize centre place entry q first) :
    RecognizedByTotalPEG PAL := by
  classical
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := hC
  -- choose one pre-loaded trace per word (dummy on `[]`)
  have key : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTrace centre place entry q first w st Tc := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨st, Tc, h⟩ := preTrace_exists centre place entry q first w hw (hA w hw)
      exact ⟨st, Tc, fun _ => h⟩
    · exact ⟨fun _ => boot w, fun _ => 0, fun h => absurd h hw⟩
  choose stP TcP hP using key
  let M := L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn
  have hpre : ∀ w : List (Fin 2), 0 < w.length → Preload w (stP w) (TcP w) :=
    fun w hw => preload_of_preTrace (hP w hw) (hB_need w hw _ _ (hP w hw))
  refine pal_in_peg_of_latch' (Nat.mul_pos hn (PalPeg.Local.cnt_pos K)) M
    (PofC centre place entry) (fun _ => q) (fun _ => first) 2048
    (fun w => PofC_onLetter centre place entry w) (fun w => PofC_leftFirst centre place entry w)
    (fun w => stTG τF w (stP w) (TcP w w.length))
    (fun w => arrTG τF w (stP w) (TcP w w.length))
    (fun w => (w.length + 1) * τF) ?_ ?_ ?_ ?_
  · intro w hw
    have h := hP w hw
    exact abstractRun_throttled_2p18 w (stP w) (TcP w w.length) (PofC centre place entry w) q
      first 2048 (by rw [h.start]; rfl) (needS_boot w (stP w) h.start)
      (hB_suf w hw _ _ h) (hB_trunc w hw _ _ h)
  · intro w hw
    exact hreal w hw _ _ (hP w hw)
  · exact ledger_throttled_2p18 (PofC centre place entry) (fun _ => q) (fun _ => first) stP TcP
      hpre (fun w hw => (hP w hw).report w.length (by omega) le_rfl)
      (fun w hw => hB_base w hw _ _ (hP w hw))
      (fun w hw => (hP w hw).cost)
  · exact GalilEmptyWord.realize_accept'_nil L blank initQ outQ n htape hn

#print axioms needS_boot
#print axioms preload_of_preTrace
#print axioms preTrace_exists
#print axioms pal_in_peg_final

end PalPeg.GalilFinalAssembly
