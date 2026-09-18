import PalPeg.CloseoutPackRun46
import PalPeg.ProgLangPersist2

/-!
# `CloseoutRealize1`: the `LocalStep` in `H_realizeLIMG2'` is incidental

`CloseoutPackRun36.H_realizeLIMG2'` existentially quantifies a
`PalPeg.Local.LocalStep` and realizes it with `LocalStep.realize`.  The only
consumer of that witness, `CloseoutPackRun36.pal_in_peg_final5MG2`, feeds it to
`GalilArriveChain.pal_in_peg_of_latch'`, which is **generic in an arbitrary
`StructuredMachine`**: it uses the machine only through `H_realize`
(acceptance ↔ latch) and `H_empty` (`M.SAccepts []`).

This file makes that observation a theorem.

**実装されているのは §1 と §2 だけ**（2026-09-19 に実測して訂正した。以前の
docstring は §3〜§6 まで完了したかのように書いてあったが、このファイルの宣言は
`H_realizeSMG2'` と `h_realizeSMG2'_of_LIMG2'` の **2 つだけ**。散文を一次情報として
扱うとここで騙される）。

* §1 `H_realizeSMG2'` — the same hypothesis with `L.realize …` replaced by an
  arbitrary `StructuredMachine (Fin 2) Q' Γ' t B` plus `M.SAccepts []`.  **実装済み。**
* §2 `h_realizeSMG2'_of_LIMG2'` — the `LocalStep` route is a special case, so
  `H_realizeSMG2'` is *weaker*; the empty-word half is
  `GalilEmptyWord.realize_accept'_nil`.  **実装済み。**

以下は**構想のみ（未実装）**。書いた当時の計画であって、定理ではない:

* §3 `pal_in_peg_final5SM2` / §4 `pal_in_peg_final24SM` — `hC` を一般化した最上位。
* §5 `h_realizeSMG2'_of_prog` — `ProgLangPersist2.progMachinePMb` が有資格だという主張。
* §6 `pal_in_peg_of_progPal` — latch（したがって `CloseoutPackRun*` 全体）を迂回する
  直接 `Prog` 経路。**これは存在しない。** 迂回路があると思って探すと時間を失う。

**無条件 PAL ∈ PEG は未完.**  Nothing here builds a machine; it relocates the
remaining obligation from "a `LocalStep` with window-locality" to "any strictly
real-time structured machine", and exhibits the `Prog` packaging as an
admissible instance of it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutRealize1

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilLookRefined PalPeg.GalilFinalBaseNeed
open PalPeg.GalilFinalAssembly2 PalPeg.GalilFinalAssembly4
open PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun36 PalPeg.CloseoutPackRun46

/-! ## 1. The `StructuredMachine`-generic realization hypothesis -/

/-- `CloseoutPackRun36.H_realizeLIMG2'` with the `LocalStep` witness replaced by
an arbitrary strictly real-time `StructuredMachine`.  The empty-word clause is
the second obligation `pal_in_peg_of_latch'` makes of the machine; on the
`LocalStep` route it is supplied by `GalilEmptyWord.accept'`. -/
def H_realizeSMG2' (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) : Prop :=
  ∃ (Q' Γ' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (_ : Fintype Γ') (_ : DecidableEq Γ')
    (t B : ℕ) (M : StructuredMachine (Fin 2) Q' Γ' t B) (_ : 0 < B),
    M.SAccepts [] ∧
    ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTraceIMG2 centre place entry q first w st Tc →
      (M.SAccepts w ↔
        LatchTrue (PofC centre place entry w) q first w (stLG' τF w st (Tc w.length))
          ((w.length + 1) * τF))

/-! ## 2. The `LocalStep` route is a special case -/

/-- **`H_realizeLIMG2' → H_realizeSMG2'`.**  So the generic hypothesis is the
weaker one: anything that discharges the hand-built tape encoding also
discharges this. -/
theorem h_realizeSMG2'_of_LIMG2' {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    (h : H_realizeLIMG2' centre place entry q first) :
    H_realizeSMG2' centre place entry q first := by
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := h
  exact ⟨PalPeg.Local.Ctrl (Fin 2) Q' Γ' t K × Fin (n * PalPeg.Local.cnt K), Γ',
    inferInstance, inferInstance, iΓ, dΓ, t, n * PalPeg.Local.cnt K,
    L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn,
    Nat.mul_pos hn (PalPeg.Local.cnt_pos K),
    GalilEmptyWord.realize_accept'_nil L blank initQ outQ n htape hn, hreal⟩

end PalPeg.CloseoutRealize1

#print axioms PalPeg.CloseoutRealize1.h_realizeSMG2'_of_LIMG2'
