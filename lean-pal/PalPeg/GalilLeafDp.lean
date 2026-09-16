import PalPeg.GalilLeafMismatch
import PalPeg.GalilLeafPres

/-!
# The `hdp` residue of `GalilLeafMismatch.hmismatch_of_residues`, restated

`GalilLeafMismatch.hmismatch_of_residues` takes

```
hdp : ∀ w t Rad, ScanInvariant w (position t.center) Rad t.left t.right → DpPack w t Rad
```

**as stated it is false.**  `contract_of_dpPack` below shows that `DpPack` is
exactly the search contract of the span — the DP config `y` of `DpPack` is
existentially quantified, and `Result W lower 0 y` with `y.pc = 347` unfolds to
"no candidate above `lower` inside `W`", so `DpPack` carries no machine content
at all: it says the span at `t` has *no* period below `Rad/2`.  A bare
`ScanInvariant` state may have a perfectly periodic span (`a^n` at any centre),
so the ∀-form is refuted, not merely unproved.

The facts are real, but they belong to the **search co-run**, not to the heads:
the DP of the current stage runs on the window of the *centre*
(`GalilSearchResult`, `GalilLaterRadius`), `lower = value last` is the bound
installed at the restart, and the failure branch is `pc = 347`
(`GalilSearchResult.missed_pc_347`).  This file therefore splits `hdp` into

* `StageFailed P raw t Rad` — the **state-local** residue: the DP machine *of
  the state* `t.dp` has completed and failed on a window of the centre's own
  place stream that covers the scan radius, and every period `2δ` with
  `δ ≤ lower` was already excluded by the earlier stages.  Nothing here is
  existential over a fictitious config: `y` is pinned to `t.dp`.
* `dpPack_of_stageFailed` — the reduction.  The two conjuncts of `DpPack` that
  are pure bookkeeping (the centre-side decomposition of `raw` and
  `P.place t = ⟨a₀ :: ls₀, gap₀⟩`) are **derived**, from `Decodes` and the
  `CentreRep` half that `InvLPC` already carries, transported along the segment
  by `SegReached.center`.

So `hmismatch_of_residues'` needs **no extra premise on the entry `InvLPC`**:
`InvLPC = InvLP2 ∧ CentreRep` and `SegReached.center` give the decomposition.
What it does need is the *stage budget* at the mismatch state.  `SegReached`
only carries the bare `SearchReady`, and `GalilLeafPres` refutes that as an
invariant (`hpres_false_at`); the budgeted form `SearchReadyB v as`
(`ReadyRem` + `RunEntriesAll`) is the one that is preserved, and it is what
supplies the "the stage has enough events left to finish the DP" clause of
`DpSafeRem`.  Threading it through `watchSegE_construct`'s fuel induction is a
separate job, so it enters here as the named premise `StageBudgetAt`.
-/

set_option autoImplicit false

namespace PalPeg.GalilLeafDp

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilOracleMC2 PalPeg.GalilFinalAssembly2 PalPeg.GalilLeafMismatch
open PalPeg.GalilLeafPres
open Manacher

/-! ## 1. What `DpPack` actually says -/

/-- **`DpPack` is the search contract, nothing more.**  Its DP configuration is
existential, so the pair (`Result … lower 0 y`, `y.pc = 347`) only says that the
centre window has no candidate above `lower`; together with the exclusion below
`lower` that is exactly aperiodicity of the span.  Hence the ∀-form of `hdp`
over all `ScanInvariant` states is false: a span like `a^(2·Rad+1)` has period
`1`. -/
theorem contract_of_dpPack {raw : List (Fin 2)} {t : GalilVM} {Rad : ℕ}
    (hi : ScanInvariant raw (position t.center) Rad t.left t.right)
    (hkC : Rad < position t.center) (h : DpPack raw t Rad) :
    ∀ p, 0 < p → HasPeriod (Span raw (position t.center) Rad) p → Rad < 2*p := by
  obtain ⟨a₀, ls₀, rs₀, q₀, gap₀, lower, span, y, hraw₀, hC₀, hspan, hres, hidle, hlow⟩ := h
  have hc := search_contract_of_stage a₀ ls₀ rs₀ q₀ gap₀ hC₀ hkC hspan
    (by rw [← hraw₀]; exact hi.palindrome) hres hidle (by rw [← hraw₀]; exact hlow)
  rw [← hraw₀] at hc
  exact hc

/-- **…and hence the ∀-form of `hdp` is refuted, not merely unproved.**  At any
scan state whose span carries a period `p` with `2*p ≤ Rad` — e.g. `p = 1` on a
run of equal letters — `DpPack` is contradictory. -/
theorem not_dpPack_of_period {raw : List (Fin 2)} {t : GalilVM} {Rad p : ℕ}
    (hi : ScanInvariant raw (position t.center) Rad t.left t.right)
    (hkC : Rad < position t.center) (hp : 0 < p) (h2 : 2*p ≤ Rad)
    (hper : HasPeriod (Span raw (position t.center) Rad) p) : ¬ DpPack raw t Rad := by
  intro h
  have := contract_of_dpPack hi hkC h p hp hper
  omega

/-! ## 2. The state-local residue -/

/-- **The DP datum of the current stage, at the state that owns it.**  The DP
machine `t.dp` has completed and failed (`pc = 347`) on the calibrated window
`(stream (P.place t)).take (span+1)` of the *centre*, the window covers the scan
radius (`Rad ≤ span`), and the periods `2δ` with `δ ≤ lower` were excluded by
the earlier stages.  `lower` is the bound installed at the restart. -/
def StageFailed (P : Shared) (raw : List (Fin 2)) (t : GalilVM) (Rad : ℕ) : Prop :=
  ∃ lower span : ℕ,
    Rad ≤ span ∧
    GalilDpCorrect.Result ((GalilScaffoldPlace.stream (P.place t)).take (span+1)) lower 0
      (GalilScaffoldProgram.denote t.dp.config) ∧
    (GalilScaffoldProgram.denote t.dp.config).pc = 347 ∧
    (∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw (position t.center) Rad) (2*δ))

/-- **The reduction.**  `StageFailed` plus the centre head gives `DpPack`: the
decomposition of `raw` at the centre and the identification of the DP window
with `stream ⟨a₀ :: ls₀, gap₀⟩` are `represents_decompose` and `Decodes`. -/
theorem dpPack_of_stageFailed {P : Shared} {raw : List (Fin 2)} {t : GalilVM} {Rad : ℕ}
    (hP : Decodes P) (hc : CentreRep raw t) (h : StageFailed P raw t Rad) :
    DpPack raw t Rad := by
  obtain ⟨lower, span, hspan, hres, hpc, hlow⟩ := h
  obtain ⟨a₀, ls₀, rs₀, q₀, hdec, hraw⟩ := represents_decompose t.center raw hc.1 hc.2
  obtain ⟨-, hplace⟩ := hP.1 t a₀ ls₀ rs₀ q₀ t.center.gap hdec
  exact ⟨a₀, ls₀, rs₀, q₀, t.center.gap, lower, span, GalilScaffoldProgram.denote t.dp.config,
    hraw, congrArg position hdec, hspan, by rw [← hplace]; exact hres, hpc, hlow⟩

/-! ## 3. The residue at the mismatch state of a segment -/

/-- **`hdp'`.**  The restated residue: at the mismatch exit `t` of a segment out
of an `InvLPC` entry, with the *budgeted* search invariant `SearchReadyB`
available there, the stage's DP has completed and failed. -/
def MismatchDp (entry q : ℕ) (first : Fin 9) : Prop :=
  ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (as : List Bool) (Rad : ℕ),
    InvLPC w c r →
    SegReachedW centreC placeC entry q first w c r c' t →
    SearchReadyB (searchLens.get t) as →
    canRight t.right →
    read (left t.left) ≠ read (right t.right) →
    ScanInvariant w (position t.center) Rad t.left t.right →
    StageFailed (PofC centreC placeC entry w) w t Rad

/-- **The stage budget at the mismatch state.**  `SegReached` carries only the
bare `SearchReady`, which `GalilLeafPres.hpres_false_at` refutes as an
invariant; the preserved form is `SearchReadyB` (`ReadyRem` + `RunEntriesAll`),
and it is what pays for the DP's completion.  Carrying it along the segment
means re-proving `watchSegE_construct` with `SearchReadyB` in place of
`SearchReady`, so it is a named premise here. -/
def StageBudgetAt (entry q : ℕ) (first : Fin 9) : Prop :=
  ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
    InvLPC w c r → SegReachedW centreC placeC entry q first w c r c' t →
    ∃ as, SearchReadyB (searchLens.get t) as

/-- The budgeted invariant still implies the bare one, so `StageBudgetAt` is a
strengthening of what `SegReached.search` already gives. -/
theorem searchReady_of_budget {entry q : ℕ} {first : Fin 9} (h : StageBudgetAt entry q first)
    {w : List (Fin 2)} {c : Control} {r : GalilVM} {c' : Control} {t : GalilVM}
    (hIC : InvLPC w c r) (hs : SegReachedW centreC placeC entry q first w c r c' t) :
    PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get t) := by
  obtain ⟨as, hB⟩ := h w c r c' t hIC hs
  exact searchReadyB_ready hB

/-- **`hmismatch_of_residues'`.**  `GalilLeafMismatch.hmismatch_of_residues`
with the false `hdp` replaced by the state-local `hdp'` and the stage budget.
No extra premise on the entry `InvLPC` is needed: its `CentreRep` half,
transported by `SegReached.center`, supplies the centre-side decomposition. -/
theorem hmismatch_of_residues' (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8)
    (hsearch : ∀ (w : List (Fin 2)) (s : GalilVM),
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centreC placeC entry w) a s v)
    (hdp' : MismatchDp entry q first)
    (hbud : StageBudgetAt entry q first)
    (hfb : ∀ (w : List (Fin 2)) (c' : Control) (t : GalilVM) (n ℓ : ℕ) (cT : Control)
        (sT : GalilVM), value t.length = ℓ →
      StepsAll (galilFrameS (PofC centreC placeC entry w) q first) 2048 (SoundScanNR w)
        (1 + (n + 1)) ⟨c', t⟩ ⟨cT, sT⟩ → n + 1 ≤ 1588 * (ℓ + 1) + 836)
    (hpos : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t → canRight t.right →
      position (right t.right) ≤ 2 * m - 1) :
    ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRouteMC2 (PofC centreC placeC entry w) q first w m c r c' t := by
  intro w m c r c' t hm1 hmle hIC hrt hs hnr hc1 hav hmis
  obtain ⟨as, hB⟩ := hbud w c r c' t hIC hs
  have hcen : CentreRep w t := centreRep_congr hs.1.center hIC.2
  exact fallbackRouteMC2_of_mismatch entry q hq0 first h7 h8 hsearch w m c r c' t hIC hs hnr hc1
    hav hmis
    (fun Rad hi => dpPack_of_stageFailed (decodesC entry w) hcen
      (hdp' w c r c' t as Rad hIC hs hB hav hmis hi))
    (fun n ℓ cT sT => hfb w c' t n ℓ cT sT)
    (hpos w m c r c' t hm1 hmle hIC hrt hs hav)

#print axioms contract_of_dpPack
#print axioms not_dpPack_of_period
#print axioms StageFailed
#print axioms dpPack_of_stageFailed
#print axioms searchReady_of_budget
#print axioms hmismatch_of_residues'

end PalPeg.GalilLeafDp
