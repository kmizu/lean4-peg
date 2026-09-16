import PalPeg.GalilOracleMC3
import PalPeg.GalilLeafPos
import PalPeg.GalilLeafReport
import PalPeg.GalilLeafEnds
import PalPeg.GalilLeafMismatch

/-!
# The place bound, and the leaves it unlocks

`GalilLeafPos.not_hpos_of_tight_entry` refutes the residue
`position (right t.right) ≤ 2m-1` from `SegReachedW` alone: along the segment the
right head moves by `es.count true`, and nothing in `SegReachedW` mentions `m`.
`GalilLeafPos.hpos_of_le` shows the residue *is* available once the segment exit
is known to stop short of the checkpoint cell, `position t.right ≤ 2m-2`.

That bound is not a new leaf: it comes from a case split the oracle can make for
itself, exactly the one `GalilLeafReport.hended_C`/`hlastMatch_C` already make.
At a cycle with entry `r` and segment exit `t`,

* `position r.right = 2m-1` — the entering state already *is* the report point:
  `GalilLeafReport.reachAtC2_of_entry` (residue `EntryRefreshed`);
* `position r.right < 2m-1 ≤ position t.right` — the segment crosses the
  checkpoint cell, so it passes through an `AtTarget` state whose next tick is
  the report comparison: `GalilLeafReport.reachAtC2_of_cross`;
* `position t.right ≤ 2m-2` — the remaining case, where every segment-ending
  leaf may now assume the bound.

`cycleOracleMC2C_of_pieces''` performs that split once, before the exit
analysis.  Consequences: `hended` disappears outright (a blocked right head sits
on `2|w|`, which the third case forbids), and `hmismatch`, `hfound`, `hfoundBg`,
`hlastMatch`, `hlastMismatch` all receive `position t.right ≤ 2m-2`.  That is
what lets `GalilLeafMismatch.fallbackRouteMC2_of_mismatch` be plugged with its
`hpos` argument built by `GalilLeafPos.hpos_of_le` — no segment-budget residue.

`hlastMatch_C'` is `GalilLeafReport.hlastMatch_C` with the refuted `hquiet`
replaced by a last-letter-scoped not-found premise (`hlastNotFound`), which is
all that proof uses it for.

**Not based on `GalilInvPlus3`.**  `cycleOracleMC3_of_pieces` would be the
natural base, but its leaves speak of `FallbackRouteMC3` / `ReachAtC3`, i.e. they
must return the `ReplayStage` datum at every landing, while
`GalilLeafMismatch.fallbackRouteMC2_of_mismatch`, `GalilLeafReport.hlastMatch_C`
and `hlastMismatch_C` all produce the `MC2` forms.  Until those are restated over
`InvLPS` the plugs do not typecheck at the `MC3` level, so this file stays at the
`InvLPC` level of `GalilOracleMC3`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.GalilOracleMC4

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilOracleM PalPeg.GalilOracleMC2 PalPeg.GalilFinalAssembly2
open PalPeg.GalilOracleLeaves2 PalPeg.GalilOracleMC3
open PalPeg.GalilLeafPos PalPeg.GalilLeafReport

/-! ## 1. `hlastMatch` without the refuted `hquiet` -/

/-- **`GalilLeafReport.hlastMatch_C` with `hquiet` scoped down.**  The only use
of quietness there is the `hnf` of the report comparison at the *last letter*;
`hlastNotFound` asks for exactly that, at a state whose right head is on the
final letter.  `GalilLeafQuiet.not_searchQuiet_PofC` refutes the unrestricted
form, not this one. -/
theorem hlastMatch_C' (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9)
    (hsearch : ∀ (w : List (Fin 2)) (s : GalilVM), SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry w) a s v)
    (hpres : ∀ (w : List (Fin 2)) (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry w) a s v → SearchReady v)
    (hlastNotFound : ∀ (w : List (Fin 2)) (t : GalilVM) (vq : SearchVM),
      SearchReady (searchLens.get t) → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      searchEffect (PofC centre place entry w) true t vq → vq.search.mode ≠ .found)
    (hentry : EntryRefreshed centre place entry q first)
    (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (hm1 : 1 ≤ m) (hmle : m ≤ w.length) (hIC : InvLPC w c r)
    (hp : position r.right ≤ 2 * m - 1)
    (hsW : SegReachedW centre place entry q first w c r c' t)
    (hc : c'.clock = 1) (hav : canRight t.right) (hpop : PopsIncoming t.right)
    (hinc : ∃ a : Fin 2, t.right.head.incoming = [a])
    (hmt : read (left t.left) = read (right t.right)) :
    ReachAtC2 (PofC centre place entry w) q first w m c r := by
  obtain ⟨a, hinc'⟩ := hinc
  obtain ⟨hposT, hwne⟩ := lastLetter_position centre place entry q first hsW hav hpop hinc'
  rcases Nat.lt_or_ge (position r.right) (2 * m - 1) with hlt | hge
  · rcases Nat.lt_or_ge (position t.right) (2 * m - 1) with h2 | h2
    · have hI : InvL w c r := invLPC_invL hIC
      obtain ⟨hmC, hclkC, hidleC, hsrC, hMC, R0, hi0, hfrC, hrrC, hsiC⟩ := invS_entry_data hI.1
      have hnrC : c.replaying = false := (invS_mode hI.1).2
      obtain ⟨es, hw⟩ := hsW.2
      have hnrT : c'.replaying = false :=
        watchSegE_notReplaying (PofC centre place entry w) q first 2048 hw hnrC
      have hstepsT : Steps (galilFrameS (PofC centre place entry w) q first) 2048 es.length
          ⟨c, r⟩ ⟨c', t⟩ := watchSegE_steps_length _ q first 2048 hw
      have hfrT : Frontier t ∧ ReplayRest c' t :=
        frontier_replayRest_of_scan (onLetterVM w) leftFirstVM centre place entry q first 2048
          hstepsT hmC (hlive_of_invLPC centre place entry q first hIC) hfrC hrrC
      obtain ⟨vq, hq⟩ := hsearch w t hsW.1.search true
      exact reachAtC2_of_target_match centre place entry q first w m hm1 hmle (hpres w)
        c r c' t hIC hsW ⟨hnrT, hc, hav, by omega, hfrT.2 (Or.inl hnrT)⟩ hmt vq hq
        (hlastNotFound w t vq hsW.1.search hpop ⟨a, hinc'⟩ hq)
    · exact reachAtC2_of_cross centre place entry q first w (hpres w) m hm1 hmle hIC hsW hlt h2
  · exact reachAtC2_of_entry centre place entry q first w m hm1 hmle hIC
      (hentry w m c r hm1 hmle hIC (by omega)) (by omega)

/-! ## 2. The oracle with the place bound handed to the exit leaves -/

/-- **`GalilOracleMC3.cycleOracleMC2C_of_pieces'` with the checkpoint split
performed once.**  `hended` is gone; the five segment-ending leaves receive
`position t.right ≤ 2 * m - 2`; the two report cases are `reachAtC2_of_entry`
(residue `EntryRefreshed`) and `reachAtC2_of_cross`. -/
theorem cycleOracleMC2C_of_pieces'' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (hshape : PalPeg.GalilWatchOkInst.StartShape (PofC centre place entry raw))
    (hbudget : PalPeg.GalilFoundStage.ReplayBudgetR raw (PofC centre place entry raw) q first 2048)
    (hstage : PalPeg.GalilFoundStage.ReplayStageInv raw (PofC centre place entry raw) q first)
    (hrs : PalPeg.GalilReplaySpan.RestartShape (PofC centre place entry raw))
    (hentry : EntryRefreshed centre place entry q first)
    (hsegmentM : ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ raw.length →
      InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      ∃ (c' : Control) (t : GalilVM),
        SegReachedW centre place entry q first raw c r c' t ∧
        (AtTarget m c' t ∨ SegEnd (PofC centre place entry raw) c' t))
    (hlastMatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → position t.right ≤ 2 * m - 2 →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      ReachAtC2 (PofC centre place entry raw) q first raw m c r)
    (hlastMismatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → position t.right ≤ 2 * m - 2 →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      ReachAtC2 (PofC centre place entry raw) q first raw m c r)
    (hmismatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → position t.right ≤ 2 * m - 2 →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRouteMC2 (PofC centre place entry raw) q first raw m c r c' t)
    (hfound : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → position t.right ≤ 2 * m - 2 →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centre place entry raw) true t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centre place entry raw) q first raw m c r c' t)
    (hfoundBg : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → position t.right ≤ 2 * m - 2 →
      1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centre place entry raw) false t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centre place entry raw) q first raw m c r c r)
    (hfoundReplay : ∀ (m : ℕ) (c : Control) (r : GalilVM) (cT : Control) (sT : GalilVM) (R k : ℕ),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r →
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
        ⟨c, r⟩ ⟨cT, sT⟩ →
      ReplayLanding raw cT sT R → SpanRep sT →
      position r.center < position sT.center → position sT.right ≤ 2 * m - 1 →
      (PalPeg.GalilReplaySpan.ChainEnd raw (PofC centre place entry raw) q first 2048
          (position sT.right + R) cT sT 0 R ∨
        PalPeg.GalilReplaySpan.BrokeAndRestarted raw (PofC centre place entry raw) q first 2048
          cT sT) →
      FoundInReplayRouteMC2 (PofC centre place entry raw) q first raw m c r) :
    CycleOracleMC2C (PofC centre place entry raw) q first raw := by
  intro m c r hm1 hmle hIC hp
  obtain ⟨c', t, hsW, hend⟩ := hsegmentM m c r hm1 hmle hIC hp
  obtain ⟨hs, es, hw⟩ := id hsW
  rcases Nat.lt_or_ge (position r.right) (2 * m - 1) with hlt | hge
  case inr =>
    exact Or.inl (reachAtC2_of_entry centre place entry q first raw m hm1 hmle hIC
      (hentry raw m c r hm1 hmle hIC (by omega)) (by omega))
  case inl =>
  rcases Nat.lt_or_ge (position t.right) (2 * m - 1) with h2 | h2
  case inr =>
    exact Or.inl (reachAtC2_of_cross centre place entry q first raw hpres m hm1 hmle hIC hsW hlt h2)
  case inl =>
  have hb : position t.right ≤ 2 * m - 2 := by omega
  rcases hend with hT | hend
  · obtain ⟨hnr, hc1, hav, -, -⟩ := id hT
    by_cases hmt : read (left t.left) = read (right t.right)
    · obtain ⟨vq, hq⟩ := hsearch t hs.search true
      by_cases hf : vq.search.mode = .found
      · exact cycleOutMC2C_of_found centre place entry q first raw m hIC hw hs.center hav
          (hfound m c r c' t hm1 hmle hIC hp hsW hb hc1 hav hmt ⟨vq, hq, hf⟩)
      · exact Or.inl (reachAtC2_of_target_match centre place entry q first raw m hm1 hmle hpres
          c r c' t hIC hsW hT hmt vq hq hf)
    · exact cycleOutMC2C_of_fallback' centre place entry q first raw m hm1 hmle hex hsearch hpres
        hshape hbudget hstage hrs (hfoundReplay m) hIC hw hs.center hc1 hav
        (hmismatch m c r c' t hm1 hmle hIC hp hsW hb hnr hc1 hav hmt)
  · cases hend with
    | ended hn =>
        obtain ⟨R, hiT⟩ := hs.scan
        have hendp : position t.right = 2 * raw.length :=
          (PalPeg.GalilEndOfInput.not_canRight_iff t.right raw hs.input hiT.rightPresent).1 hn
        omega
    | mismatch hr hc hav hne =>
        exact cycleOutMC2C_of_fallback' centre place entry q first raw m hm1 hmle hex hsearch hpres
          hshape hbudget hstage hrs (hfoundReplay m) hIC hw hs.center hc hav
          (hmismatch m c r c' t hm1 hmle hIC hp hsW hb hr hc hav hne)
    | found hc hav hmt hq =>
        exact cycleOutMC2C_of_found centre place entry q first raw m hIC hw hs.center hav
          (hfound m c r c' t hm1 hmle hIC hp hsW hb hc hav hmt hq)
    | foundBackground hc hq =>
        exact cycleOutMC2C_of_foundBg centre place entry q first raw m hIC
          (hfoundBg m c r c' t hm1 hmle hIC hp hsW hb hc hq)
    | lastLetter hc hav hpop hinc =>
        by_cases hmt : read (left t.left) = read (right t.right)
        · exact Or.inl (hlastMatch m c r c' t hm1 hmle hIC hp hsW hb hc hav hpop hinc hmt)
        · exact Or.inl (hlastMismatch m c r c' t hm1 hmle hIC hp hsW hb hc hav hpop hinc hmt)


/-! ## 3. `H_oracle` from the residual leaves -/

open PalPeg.GalilFinalAssembly in
/-- **`GalilOracleMC3.h_oracle_of_leaves''` with `hends`, `hended`, `hmismatch`,
`hlastMatch` and `hlastMismatch` discharged.**  `hends` is
`GalilLeafEnds.hends_C`, `hended` disappeared with the checkpoint split,
`hmismatch` is `GalilLeafMismatch.fallbackRouteMC2_of_mismatch` whose place
residue is now `GalilLeafPos.hpos_of_le`, and the two last-letter exits are
`hlastMatch_C'` and `GalilLeafReport.hlastMismatch_C`. -/
theorem h_oracle_of_leaves''' (entry q : ℕ) (first : Fin 9) (hq0 : 0 < q)
    (h7 : first ≠ 7) (h8 : first ≠ 8)
    (hpres : ∀ (w : List (Fin 2)) (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centreC placeC entry w) a s v → SearchReady v)
    (hshape : ∀ w : List (Fin 2),
      PalPeg.GalilWatchOkInst.StartShape (PofC centreC placeC entry w))
    (hbudget : ∀ w : List (Fin 2),
      PalPeg.GalilFoundStage.ReplayBudgetR w (PofC centreC placeC entry w) q first 2048)
    (hstage : ∀ w : List (Fin 2),
      PalPeg.GalilFoundStage.ReplayStageInv w (PofC centreC placeC entry w) q first)
    (hrs : ∀ w : List (Fin 2),
      PalPeg.GalilReplaySpan.RestartShape (PofC centreC placeC entry w))
    (hentry : EntryRefreshed centreC placeC entry q first)
    (hlast : LastMismatchReport centreC placeC entry q first)
    (hlastNotFound : ∀ (w : List (Fin 2)) (t : GalilVM) (vq : SearchVM),
      SearchReady (searchLens.get t) → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      searchEffect (PofC centreC placeC entry w) true t vq → vq.search.mode ≠ .found)
    (hdp : ∀ (w : List (Fin 2)) (t : GalilVM) (Rad : ℕ),
      ScanInvariant w (position t.center) Rad t.left t.right →
      PalPeg.GalilLeafMismatch.DpPack w t Rad)
    (hfb : ∀ (w : List (Fin 2)) (c' : Control) (t : GalilVM) (n ℓ : ℕ) (cT : Control)
        (sT : GalilVM), value t.length = ℓ →
      StepsAll (galilFrameS (PofC centreC placeC entry w) q first) 2048 (SoundScanNR w)
        (1 + (n + 1)) ⟨c', t⟩ ⟨cT, sT⟩ → n + 1 ≤ 1588 * (ℓ + 1) + 836)
    (hfound : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t → position t.right ≤ 2 * m - 2 →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centreC placeC entry w) true t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centreC placeC entry w) q first w m c r c' t)
    (hfoundBg : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t → position t.right ≤ 2 * m - 2 →
      1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centreC placeC entry w) false t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centreC placeC entry w) q first w m c r c r)
    (hfoundReplay : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (cT : Control)
      (sT : GalilVM) (R k : ℕ), 1 ≤ m → m ≤ w.length → InvLPC w c r →
      StepsAll (galilFrameS (PofC centreC placeC entry w) q first) 2048 (SoundScanNR w) k
        ⟨c, r⟩ ⟨cT, sT⟩ →
      ReplayLanding w cT sT R → SpanRep sT →
      position r.center < position sT.center → position sT.right ≤ 2 * m - 1 →
      (PalPeg.GalilReplaySpan.ChainEnd w (PofC centreC placeC entry w) q first 2048
          (position sT.right + R) cT sT 0 R ∨
        PalPeg.GalilReplaySpan.BrokeAndRestarted w (PofC centreC placeC entry w) q first 2048
          cT sT) →
      FoundInReplayRouteMC2 (PofC centreC placeC entry w) q first w m c r)
    (hstr : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvL w c r → InvLPC w c r) :
    H_oracle centreC placeC entry q first :=
  fun w _ => cycleOracleMC_of_MC2C
    (cycleOracleMC2C_of_pieces'' centreC placeC entry q first w
      (fun s => hex_C centreC placeC entry w s)
      (fun s hs a => hsearch_C centreC placeC entry w s hs a)
      (hpres w) (hshape w) (hbudget w) (hstage w) (hrs w) hentry
      (fun m c r _ _ hIC _ => by
        obtain ⟨c', t, hsW, hEnd⟩ :=
          segment_of_invLPC centreC placeC entry q first w
            (fun s => hex_C centreC placeC entry w s)
            (fun s hs a => hsearch_C centreC placeC entry w s hs a) (hpres w) c r hIC
            (PalPeg.GalilLeafEnds.hends_C entry q first w c r hIC)
        exact ⟨c', t, hsW, Or.inr hEnd⟩)
      (fun m c r c' t hm1 hmle hIC hp hsW _hb hc hav hpop hinc hmt =>
        hlastMatch_C' centreC placeC entry q first
          (fun w' s hs a => hsearch_C centreC placeC entry w' s hs a) hpres hlastNotFound hentry
          w m c r c' t hm1 hmle hIC hp hsW hc hav hpop hinc hmt)
      (fun m c r c' t hm1 hmle hIC hp hsW _hb hc hav hpop hinc hmt =>
        hlastMismatch_C centreC placeC entry q first hpres hentry hlast
          w m c r c' t hm1 hmle hIC hp hsW hc hav hpop hinc hmt)
      (fun m c r c' t hm1 hmle hIC hp hsW hb hnr hc1 hav hmis =>
        PalPeg.GalilLeafMismatch.fallbackRouteMC2_of_mismatch entry q hq0 first h7 h8
          (fun w' s hs a => hsearch_C centreC placeC entry w' s hs a)
          w m c r c' t hIC hsW hnr hc1 hav hmis (hdp w t) (hfb w c' t)
          (hpos_of_le centreC placeC entry q first w m hm1 hsW hav hb))
      (hfound w) (hfoundBg w) (hfoundReplay w)) (hstr w)

#print axioms hlastMatch_C'
#print axioms cycleOracleMC2C_of_pieces''
#print axioms h_oracle_of_leaves'''

end PalPeg.GalilOracleMC4
