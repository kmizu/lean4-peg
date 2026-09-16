import PalPeg.GalilFinalAssembly2
import PalPeg.GalilFinalBaseNeed

/-!
# Final assembly, with `H_base` discharged via `PreTraceB`

`GalilFinalAssembly2.pal_in_peg_final2` still requires `H_base`, quantified over
every `PreTrace`.  `GalilFinalBaseNeed.base_of_preTraceB` discharges the
`Tc 1 ≤ 2050` bound unconditionally, but only for the strengthened trace record
`PreTraceB` (`PreTrace` plus `Tc 1 = 1`, witnessed by `preTraceB_exists`).

Here we restate `GalilFinalAssembly2.H_needL` and `GalilFinalAssembly2.H_realizeL`
over `PreTraceB` instead of `PreTrace` (`H_needLB'`, `H_realizeLB'` — trivially
implied by the originals, since `PreTraceB` implies `PreTrace`), and reprove
`pal_in_peg_final2` with `H_base` dropped entirely: the witnessing trace built
from `preTraceB_exists` is already a `PreTraceB`, so `base_of_preTraceB` supplies
(B)'s base case directly.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PalPeg.GalilFinalAssembly3

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilTickArrive PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.GalilThrottledRun PalPeg.GalilThrottledRunGen PalPeg.GalilLedgerQ64
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilTruncTick PalPeg.GalilFinalAssembly
open PalPeg.GalilFinalAssembly2 PalPeg.GalilFinalBaseNeed

/-! ## The hypotheses, restated over `PreTraceB` -/

section Hyps
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `H_needL`, restated over `PreTraceB` instead of `PreTrace`. -/
def H_needLB' : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTraceB centre place entry q first w st Tc →
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → needL w st i ≤ m+1

/-- `H_realizeL`, restated over `PreTraceB` instead of `PreTrace`. -/
def H_realizeLB' : Prop :=
  ∃ (Q' Γ' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (_ : Fintype Γ') (_ : DecidableEq Γ')
    (t K : ℕ) (L : PalPeg.Local.LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q')
    (outQ : Q' → Bool) (n : ℕ) (htape : 0 < t) (hn : 0 < n),
    ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTraceB centre place entry q first w st Tc →
      ((L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn).SAccepts w ↔
        LatchTrue (PofC centre place entry w) q first w (stLG τF w st (Tc w.length))
          ((w.length + 1) * τF))

/-- The primed need-hypothesis is implied by the original (`PreTraceB → PreTrace`). -/
theorem needLB'_of_needL (h : H_needL centre place entry q first) :
    H_needLB' centre place entry q first :=
  fun w hw st Tc hB m hm i hi => h w hw st Tc hB.pre m hm i hi

/-- The primed realization hypothesis is implied by the original. -/
theorem realizeLB'_of_realizeL (h : H_realizeL centre place entry q first) :
    H_realizeLB' centre place entry q first := by
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hr⟩ := h
  exact ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn,
    fun w hw st Tc hB => hr w hw st Tc hB.pre⟩

end Hyps

/-! ## The final theorem, `H_base` discharged unconditionally -/

/-- **`PAL ∈ PEG`**, with (B) reduced to `H_needLB'` alone: `H_base` is discharged
via `base_of_preTraceB`, using that the witnessing trace is a `PreTraceB`. -/
theorem pal_in_peg_final3 (entry q : ℕ) (first : Fin 9)
    (hA : H_oracle centreC placeC entry q first)
    (hB_need : H_needLB' centreC placeC entry q first)
    (hC : H_realizeLB' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL := by
  classical
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := hC
  have key : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceB centreC placeC entry q first w st Tc := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨st, Tc, h⟩ := preTraceB_exists centreC placeC entry q first w hw (hA w hw)
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

#print axioms needLB'_of_needL
#print axioms realizeLB'_of_realizeL
#print axioms pal_in_peg_final3

end PalPeg.GalilFinalAssembly3
