import PalPeg.CloseoutOracleBridge

/-!
# `ReplayStage` is provenance, and provenance concatenates

`CloseoutOracleBridge` reduced `hor` to `H_oracle2` plus *the landing's scan
branch carries its stage datum* (`InvSS`).  Reading what the datum actually is
(`GalilFoundStage:98`):

```
ReplayStage raw P qq first c s :=
  ∃ r Rad last es c0, Restarted raw r Rad last ∧ StageEntry Rad last ∧
    c0.clock = 2048 ∧ WatchSegE P qq first 2048 es c0 r c s
```

it is not a local property at all — it says **the state was reached from a
restart by a watch segment**.  Provenance like that is preserved by extending
the segment, so the transport lemma is concatenation of `WatchSegE`.

The tree has only the *split* direction (`GalilScaffoldTopWatchSegE.watchSegE_append`,
`WatchSegE (es1 ++ es2) → ∃ mid, …`); `CloseoutWatchRound18`'s header notes the
join is missing.  `watchSegE_trans` below is the join, by induction on the first
segment, and `replayStage_trans` is the transport it buys.

Consequence: an `InvLPS` origin (which carries `ReplayStage`) plus a watch
segment to the landing gives `ReplayStage` at the landing — so the `InvSS` lift
holds at every landing the oracle reaches *through a watch segment*, and the
remaining gap is only the landings whose run is not one (the fallback and found
exits, which carry `Inv` outright — see `GalilOracleMC2.FallbackRouteMC2.landed`
and `FoundRouteMC2.shift` / `.noShift`).

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutStageTrans

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFoundStage

/-- **`WatchSegE` concatenates.**  The join direction, which the tree only had
in its split form (`watchSegE_append`). -/
theorem watchSegE_trans (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) :
    ∀ {es1 : List Bool} {c c' : Control} {s s' : GalilVM},
      WatchSegE P q first delay es1 c s c' s' →
      ∀ {es2 : List Bool} {c'' : Control} {s'' : GalilVM},
        WatchSegE P q first delay es2 c' s' c'' s'' →
        WatchSegE P q first delay (es1 ++ es2) c s c'' s'' := by
  intro es1 c c' s s' h1
  induction h1 with
  | stop c s => intro es2 c'' s'' h2; simpa using h2
  | wait c s s0 hm hr hn hb rest ih =>
    intro es2 c'' s'' h2
    exact .wait c s s0 hm hr hn hb (ih h2)
  | count c s s0 hm hr ha hc hb rest ih =>
    intro es2 c'' s'' h2
    exact .count c s s0 hm hr ha hc hb (ih h2)
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho rest ih =>
    intro es2 c'' s'' h2
    exact .match c s vs vq o hm hr ha hc hne hcmp hmt hq ho (ih h2)
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho rest ih =>
    intro es2 c'' s'' h2
    exact .matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho (ih h2)
  | countR c s s0 hm hr hc hidle hb rest ih =>
    intro es2 c'' s'' h2
    exact .countR c s s0 hm hr hc hidle hb (ih h2)
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho rest ih =>
    intro es2 c'' s'' h2
    exact .matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho (ih h2)

/-- **`ReplayStage` travels a watch segment.**  Append the segment to the
provenance the origin already has. -/
theorem replayStage_trans {raw : List (Fin 2)} {P : Shared} {qq : ℕ} {first : Fin 9}
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : ReplayStage raw P qq first c s)
    (hw : WatchSegE P qq first 2048 es c s c' t) :
    ReplayStage raw P qq first c' t := by
  obtain ⟨r, Rad, last, es0, c0, hR, hSE, hcl, hw0⟩ := h
  exact ⟨r, Rad, last, es0 ++ es, c0, hR, hSE, hcl,
    watchSegE_trans P qq first 2048 hw0 hw⟩

/-- **`InvSS` at a landing reached by a watch segment**, from an `InvLPS`
origin.  The scan branch of `InvSS` is exactly `InvScan` plus the transported
provenance. -/
theorem invSS_of_watchSegE {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} {es : List Bool} {c c' : Control} {s t : GalilVM}
    (hO : PalPeg.GalilInvPlus3.InvLPS (PofC centre place entry raw) q first raw c s)
    (hw : WatchSegE (PofC centre place entry raw) q first 2048 es c s c' t)
    (hscan : Inv raw c' t ∨
      ∃ k : ℕ, PalPeg.GalilReplaySegment.InvScan 2048 raw c' t k) :
    PalPeg.CloseoutInvScanS.InvSS centre place entry q first raw c' t := by
  rcases hscan with hI | ⟨k, hS⟩
  · exact Or.inl hI
  · exact Or.inr ⟨k, hS, replayStage_trans hO.2 hw⟩

#print axioms watchSegE_trans
#print axioms replayStage_trans
#print axioms invSS_of_watchSegE

end PalPeg.CloseoutStageTrans
