import PalPeg.CloseoutPreload39

/-!
# `CloseoutPreload40`: the readiness datum supplies `hpres` — pointwise

`CloseoutPackRun46` deleted the `ready` field from the pack's `Extra`, so on the
`pal_in_peg_final24` path the readiness layer has exactly one consumer left: the
`hpres` leaf of `GalilOracleMC3.h_oracle_of_leaves''` (`GalilOracleMC3:336`).

Two structural facts decide what this file can prove.

* `hpres` as it stands in `h_oracle_of_leaves''` is the **universally quantified**
  preservation law `∀ w s a v, SearchReady (get s) → searchEffect _ a s v →
  SearchReady v`, and that law is **refuted** by
  `GalilLeafPres.hpres_false_at`: at a chain-idle `.run` state with exhausted
  debt the next matching quantum breaks `SearchReady`.  No datum can supply it.
  What the datum *does* supply is the same law restricted to the states the run
  actually visits, with the clock side condition the scan loop enforces — that
  is `HpresAt` below.
* `CloseoutReadyStage.ReadyPacedS` closes over `SearchReadyS` (the **cut**
  budget `ReadyRemS` = `PrepInv ∧ DpSafeStage`), not over
  `GalilLeafPres.SearchReadyB` (= `ReadyRem ∧ RunEntriesAll`, the uncut budget).
  So `ReadyPacedS` yields `SearchReadyS`, hence `SearchReady`, directly; getting
  the *uncut* `SearchReadyB` out of it would need a separate `DpSafeStage →
  DpSafe` transfer, which is not what `hpres` asks for anyway (`hpres`'s
  conclusion is plain `SearchReady`).

Hence: `searchReadyB_of_readyField3` is proved here in the form the leaf needs
(`SearchReadyS`/`SearchReady` at the effect landing, §1), and
`h_oracle_hpres_of_readiness` (§2) discharges the *pointwise* leaf along a run
from the stage-entry data.  The one hypothesis left is `hOP`: the oracle must be
re-derived from the pointwise `HpresAt` instead of the refuted universal
`hpres`.  That is an edit to `GalilOracleMC3`, so here it is a parameter.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload40

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldCounter (Counter value)
open PalPeg.CloseoutReadyStage (ReadyPacedS SearchReadyS readyPacedS_ready readyPacedS_mono
  readyPacedS_effect_false readyPacedS_effect_true)
open PalPeg.GalilRunSkeleton (PofC)
open PalPeg.CloseoutPackRun18 (BigPack2M'')
open PalPeg.CloseoutPreload39 (ReadyFieldP3 readyField3_along_run)
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 1. The datum gives the cut readiness, and the pointwise `hpres` -/

/-- `ReadyPacedS` unfolded: the cut readiness for any event list the datum
covers. -/
theorem searchReadyS_of_readyPacedS {v : SearchVM} {n k : ℕ} (h : ReadyPacedS v n k)
    (as : List Bool) (hlen : n ≤ as.length)
    (hp : PalPeg.CloseoutReadyStage.PacedL 2048 k as) : SearchReadyS v as := h as hlen hp

#print axioms searchReadyS_of_readyPacedS

/-- **The preservation law the scan loop really has.**  At a chain-idle state,
a background quantum is always affordable and a comparison quantum is
affordable exactly when the clock has run down (`clock ≤ 1`, i.e. the
`scan_match` / `scan_shift` guard). -/
def HpresAt (P : Shared) (c : Control) (s : GalilVM) : Prop :=
  ∀ (a : Bool) (v : SearchVM), s.chain = ChainVM.idle → (a = true → c.clock ≤ 1) →
    searchEffect P a s v → PalPeg.GalilBranchInvariants2.SearchReady v

/-- **`searchReadyB_of_readyField3`.**  `ReadyFieldP3 (n+1)` at a `scan` state
supplies the pointwise preservation law: the `paced` clause is the datum, and
the clock side condition is exactly the slack `2048 - c.clock` the comparison
branch of `readyPacedS_effect_true` asks for. -/
theorem searchReadyB_of_readyField3 (P : Shared) {n : ℕ} {c : Control} {s : GalilVM}
    (hf : ReadyFieldP3 (n + 1) ⟨c, s⟩) (hm0 : c.mode = Mode.scan) :
    HpresAt P c s := by
  intro a v hidle hclk he
  have hd : ReadyPacedS (searchLens.get s) (n + 1) (2048 - c.clock) := hf.paced hm0 hidle
  cases a with
  | false =>
      exact readyPacedS_ready (readyPacedS_effect_false P (k' := 0) (Nat.zero_le _) hidle hd he)
  | true =>
      have hk : 2048 ≤ (2048 - c.clock) + 1 := by
        have := hclk rfl; omega
      exact readyPacedS_ready (readyPacedS_effect_true P hk hidle hd he)

#print axioms searchReadyB_of_readyField3

/-! ## 2. The leaf along a run -/

section RunT
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- The pointwise leaf holds at every state of a run carrying the datum. -/
theorem hpresAt_along_run {w : List (Fin 2)} {n m : ℕ} {x y : State GalilVM}
    (hr : GalilScaffoldChainInputSupply.StepsAll
      (galilFrameS (PofC centre place entry w) q first) 2048
      (BigPack2M'' centre place entry q first w) m x y)
    (hf : ReadyFieldP3 (n + 1) x)
    (hentry : ∀ z z' : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = Mode.scan → restartVM entry z.vm z'.vm → ReadyFieldP3 (n + 1) z')
    (hentry' : ∀ z z' : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = Mode.replayStart → ReadyFieldP3 (n + 1) z')
    (hm : y.ctl.mode = Mode.scan) :
    HpresAt (PofC centre place entry w) y.ctl y.vm := by
  have hy : ReadyFieldP3 (n + 1) y :=
    readyField3_along_run centre place entry q first hr hf hentry hentry'
  obtain ⟨c, s⟩ := y
  exact searchReadyB_of_readyField3 _ hy hm

#print axioms hpresAt_along_run

/-- **`h_oracle_hpres_of_readiness`.**  The `hpres` argument of
`GalilOracleMC3.h_oracle_of_leaves''` discharged from the stage-entry data —
*pointwise*.  `hOP` is the single named hypothesis: the oracle re-derived from
`HpresAt` at the scan states of the run, instead of from the refuted universal
`hpres` (`GalilLeafPres.hpres_false_at`). -/
theorem h_oracle_hpres_of_readiness {Oracle : Prop} {w : List (Fin 2)} {n : ℕ}
    {x : State GalilVM} (hf : ReadyFieldP3 (n + 1) x)
    (hentry : ∀ z z' : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = Mode.scan → restartVM entry z.vm z'.vm → ReadyFieldP3 (n + 1) z')
    (hentry' : ∀ z z' : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = Mode.replayStart → ReadyFieldP3 (n + 1) z')
    (hOP : (∀ (m : ℕ) (y : State GalilVM),
      GalilScaffoldChainInputSupply.StepsAll
        (galilFrameS (PofC centre place entry w) q first) 2048
        (BigPack2M'' centre place entry q first w) m x y →
      y.ctl.mode = Mode.scan → HpresAt (PofC centre place entry w) y.ctl y.vm) → Oracle) :
    Oracle :=
  hOP (fun _ _y hr hm =>
    hpresAt_along_run centre place entry q first hr hf hentry hentry' hm)

#print axioms h_oracle_hpres_of_readiness

end RunT

end PalPeg.CloseoutPreload40
