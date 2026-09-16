import PalPeg.GalilReplayBudgetProof

/-!
# `FoundStage` is a fact about *reachable* found ticks

`GalilReplayBudgetProof.FoundStage raw P` quantifies over **all** states meeting
the premises of `ReplayBudget`, and in that form it is **false** for the concrete
`P = sharedC …`: the premises constrain disjoint parts of a `GalilVM`.  The
radius `k` is pinned by `ScanInvariant`/`RadiusRep` (heads and the radius
counter), the period `n` by `AnswerAhead` (the DP output tape `tapes 11`), and
`searchStep` in mode `.found` is the identity, so a state whose search already
sits in `.found` steps to itself for either arrival.  Nothing in the premises
ties the counter to the tape: take any state of the run and enlarge the radius
counter together with the two heads (`ScanInvariant` only wants a palindrome of
that radius, e.g. inside `a^N`), and `k ≤ 2n` fails while every premise still
holds.  The bound `k ≤ 2n` is a property of the *search history*: it comes from
the stage debt, which only a run from a restart establishes
(`GalilLaterRadius.found_radius_le_all_stages`).

So the budget is restricted to found ticks that occur inside the replay run:

* `ReplayStage` — the found tick is the end of a chain-idle segment
  (`WatchSegE`) out of a `Restarted`/`StageEntry` state with a full clock.  This
  is exactly the shape a `replay_start` leaves behind: the entry of
  `replay_after_fallback_general''` is `Restarted raw t 0 reset`, and
  `StageEntry 0 reset` is free (`stageEntry_zero`).
* `ReplayBudgetR` — `ReplayBudget` with that premise added.
* `replayBudgetR_of_decodes` — `ReplayBudgetR` from `Decodes P`, with the
  comparison-tick founds (`a = true`, `clock = 1`) fully discharged through
  `found_stage_data`; the off-comparison founds keep one named hypothesis
  `OffCompareFoundStage`, which is literally `found_stage_data` at a background
  tick (`GalilLaterRadius` states its stage bound only for the tick whose
  arrival bit is `true` and whose clock is `1`).
* `replayBudget_of_R` / `replay_after_fallback_general'''` — the construction of
  `GalilReplaySpan` is reused verbatim: `ReplayBudgetR` plus the named
  reachability invariant `ReplayStageInv` (every found tick of a replay carries
  `ReplayStage`) gives back `ReplayBudget`, so `replay_after_fallback_general''`
  applies unchanged and no branch has to be re-proved.
-/

set_option autoImplicit false
namespace PalPeg.GalilFoundStage
open PalPeg PalPeg.GalilScaffoldChainInputSupply Manacher GalilScaffoldInputHead
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter
open PalPeg.GalilReplaySpan PalPeg.GalilBranchInvariants PalPeg.GalilBranchInvariants2
open PalPeg.GalilReplayBudgetProof

/-! ## 1. The clauses at one found tick -/

/-- **The three clauses of `ReplayBudget` at a single found tick**, from the
three facts `FoundStage` asserts there. -/
theorem budget_clauses {raw : List (Fin 2)} {P : Shared} (hP : Decodes P)
    {c : Control} {s : GalilVM} {k m n j : ℕ} {xs : List (Fin 3)} {b : Fin 3}
    (hr : c.replaying = true) (hM : MInv raw c s)
    (hi : ScanInvariant raw (position s.center) k s.left s.right)
    (hrep : s.replay = ofNat m) (hn : 0 < n)
    (hsplit : (GalilScaffoldPlace.stream (P.place s)).tail.take n = xs ++ [b])
    (hcenrep : GalilScaffoldInputTrace.Represents s.center.head raw ∧ s.center.head.focus ≠ none)
    (hcand : ∃ lower span : ℕ,
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream (P.place s)).take (span+1)) lower n)
    (hk2 : k ≤ 2 * n)
    (hj1 : position s.center + 1 ≤ j) (hj2 : j ≤ position s.right + m)
    (hmis : Mispredicted raw (P.centre s) b xs (position s.center + 1) j) :
    position s.center + 4 * n < j ∧ position s.right + 2 ≤ j ∧
      2 * n + 3 + k ≤ (j - (position s.right + 2)) * (2048 - 1) := by
  obtain ⟨lower, span, hcand⟩ := hcand
  obtain ⟨al, ls, rs, qq, hdec, hraw⟩ := represents_decompose s.center raw hcenrep.1 hcenrep.2
  subst hraw
  obtain ⟨hread, hplace⟩ := hP.1 s al ls rs qq s.center.gap hdec
  obtain ⟨m', -, hrep', hleft⟩ := hM.1 hr
  have hmm : m' = m := ofNat_inj (by rw [← hrep', hrep])
  rw [hmm] at hleft
  have hRC : position s.right = position s.center + k := hi.rightPos
  have hpal : PalAt (encoded ((al :: ls).reverse ++ rs ++ qq)) (position s.center) (k + m) := by
    have := hleft.1.2.2
    rw [hRC] at this
    simpa [show position s.center + k + m - position s.center = k + m from by omega] using this
  have hCpos : position s.center
      = position (represent ⟨al :: ls, s.center.gap⟩ (rs.map some) qq) := by rw [← hdec]
  have hcen := centre_getElem al ls rs qq s.center.gap (P.centre s) hread
  rw [← hCpos] at hcen
  have hclause1 : position s.center + 4 * n < j := by
    have := mispredicted_beyond_candidate al ls rs qq s.center.gap span lower n (k + m)
      (P.centre s) b xs (by rw [← hplace]; exact hcand) (by rw [← hplace]; exact hsplit)
      (by rw [← hCpos]; exact hcen) (by rw [← hCpos]; exact hpal) j
      (by rw [← hCpos]; exact hj1) (by rw [← hCpos]; omega) (by rw [← hCpos]; exact hmis)
    rw [← hCpos] at this
    exact this
  obtain ⟨h2, h3⟩ := budget_arith hn hk2 hclause1
  exact ⟨hclause1, by omega, by rw [hRC]; simpa using h3⟩

/-! ## 2. The reachable budget -/

/-- **The found tick sits inside the replay run.**  It ends a chain-idle segment
out of a restarted state with a full clock — the shape of a `replay_start`
(`Restarted raw t 0 reset`, `stageEntry_zero`) and of every later search
restart. -/
def ReplayStage (raw : List (Fin 2)) (P : Shared) (qq : ℕ) (first : Fin 9)
    (c : Control) (s : GalilVM) : Prop :=
  ∃ (r : GalilVM) (Rad : ℕ) (last : Counter) (es : List Bool) (c0 : Control),
    Restarted raw r Rad last ∧ StageEntry Rad last ∧ c0.clock = 2048 ∧
      WatchSegE P qq first 2048 es c0 r c s

/-- **`ReplayBudget` restricted to the found ticks of the replay run.** -/
def ReplayBudgetR (raw : List (Fin 2)) (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ) : Prop :=
  ∀ (c : Control) (s : GalilVM) (a : Bool) (vq : SearchVM) (k m n : ℕ) (xs : List (Fin 3))
    (b : Fin 3),
    c.mode = .scan → c.replaying = true → s.chain = .idle → SearchReady (searchLens.get s) →
    searchEffect P a s vq → vq.search.mode = .found → MInv raw c s →
    ScanInvariant raw (position s.center) k s.left s.right → RadiusRep s.radius k →
    s.replay = ofNat m → 0 < m → Frontier s →
    AnswerAhead (vq.dp.config.tapes 11) n → 0 < n → PlaceAhead (P.place s) n →
    (GalilScaffoldPlace.stream (P.place s)).tail.take n = xs ++ [b] →
    ReplayStage raw P qq first c s →
    ∀ j, position s.center + 1 ≤ j → j ≤ position s.right + m →
      Mispredicted raw (P.centre s) b xs (position s.center + 1) j →
      position s.center + 4 * n < j ∧ position s.right + 2 ≤ j ∧
        2 * n + 3 + k ≤ (j - (position s.right + 2)) * (delay - 1)

/-- **Named hypothesis (reachability).**  Every found tick of a replay ends a
chain-idle segment out of a restarted state — the bookkeeping of the run, not of
the search. -/
def ReplayStageInv (raw : List (Fin 2)) (P : Shared) (qq : ℕ) (first : Fin 9) : Prop :=
  ∀ (c : Control) (s : GalilVM), c.mode = .scan → c.replaying = true → s.chain = .idle →
    SearchReady (searchLens.get s) → MInv raw c s → ReplayStage raw P qq first c s

/-- The restricted budget and the reachability invariant give the budget back. -/
theorem replayBudget_of_R {raw : List (Fin 2)} {P : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}
    (hR : ReplayBudgetR raw P qq first delay) (hinv : ReplayStageInv raw P qq first) :
    ReplayBudget raw P delay := by
  intro c s a vq k m n xs b hm hr hidle hsr hq hf hM hi hrad hrep hm0 hfr ha hn hpl hsplit
  exact hR c s a vq k m n xs b hm hr hidle hsr hq hf hM hi hrad hrep hm0 hfr ha hn hpl hsplit
    (hinv c s hm hr hidle hsr hM)

/-! ## 3. Discharging the restricted budget -/

/-- **Named hypothesis (the stage bound off the comparison tick).**
`found_stage_data` for a found detected at a background tick: `GalilLaterRadius`
proves its stage bound only for the tick whose arrival bit is `true` and whose
clock is `1`. -/
def OffCompareFoundStage (raw : List (Fin 2)) (P : Shared) (qq : ℕ) (first : Fin 9) : Prop :=
  ∀ (c : Control) (s : GalilVM) (a : Bool) (vq : SearchVM) (k n : ℕ),
    (a = false ∨ c.clock ≠ 1) → s.chain = .idle → SearchReady (searchLens.get s) →
    searchEffect P a s vq → vq.search.mode = .found →
    AnswerAhead (vq.dp.config.tapes 11) n → 0 < n → RadiusRep s.radius k →
    ReplayStage raw P qq first c s →
    (∃ lower span : ℕ,
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream (P.place s)).take (span+1)) lower n) ∧
      k ≤ 2 * n

/-- **`ReplayBudgetR` for the concrete machine.**  At a comparison-tick found
everything is proved: the centre representation comes from the restart
(`Restarted`) through `watchSegE_center`, the candidate and the radius bound
from `found_stage_data`.  Off the comparison tick the same data is the named
hypothesis `OffCompareFoundStage`. -/
theorem replayBudgetR_of_decodes {raw : List (Fin 2)} {P : Shared} {qq : ℕ} {first : Fin 9}
    (hP : Decodes P) (hoff : OffCompareFoundStage raw P qq first) :
    ReplayBudgetR raw P qq first 2048 := by
  intro c s a vq k m n xs b _ hr hidle hsr hq hf hM hi hrad hrep _ _ ha hn hpl hsplit hstage
    j hj1 hj2 hmis
  obtain ⟨r, Rad, last, es, c0, hRst, hSt, hcl, hseg⟩ := hstage
  -- the centre head is the restart's centre head
  have hcentre : s.center = r.center := watchSegE_center P qq first 2048 hseg
  have hcenrep : GalilScaffoldInputTrace.Represents s.center.head raw ∧ s.center.head.focus ≠ none := by
    rw [hcentre]; exact ⟨hRst.2.1, hRst.2.2.1⟩
  have hplace : P.place s = P.place r := hP.2 s r hcentre
  by_cases hcmp : a = true ∧ c.clock = 1
  · obtain ⟨rfl, hclk⟩ := hcmp
    obtain ⟨al, ls, rs, qq', hdec, -⟩ :=
      represents_decompose r.center raw hRst.2.1 hRst.2.2.1
    obtain ⟨hcand, -, hrad2⟩ :=
      found_stage_data P qq first hP al ls rs qq' r.center.gap hRst hdec hcl hSt hseg hidle hclk
        vq hq hf ha
    obtain ⟨-, hplr⟩ := hP.1 r al ls rs qq' r.center.gap hdec
    have hk2 : k ≤ 2 * n := by
      have : (k : ℤ) ≤ 2 * (n : ℤ) := by rw [← hrad.2]; exact hrad2
      exact_mod_cast this
    exact budget_clauses hP hr hM hi hrep hn hsplit hcenrep
      (by rw [hplace, hplr]; exact hcand) hk2 hj1 hj2 hmis
  · have hne : a = false ∨ c.clock ≠ 1 := by
      rcases Bool.eq_false_or_eq_true a with h | h
      · exact Or.inr (fun hc => hcmp ⟨h, hc⟩)
      · exact Or.inl h
    obtain ⟨hcand, hk2⟩ :=
      hoff c s a vq k n hne hidle hsr hq hf ha hn hrad
        ⟨r, Rad, last, es, c0, hRst, hSt, hcl, hseg⟩
    exact budget_clauses hP hr hM hi hrep hn hsplit hcenrep hcand hk2 hj1 hj2 hmis

/-! ## 4. The replay construction with the restricted budget -/

/-- **`replay_after_fallback_general'''`.**  `replay_after_fallback_general''`
with `ReplayBudget` replaced by `ReplayBudgetR` and the reachability invariant
`ReplayStageInv`; the construction itself is reused unchanged. -/
theorem replay_after_fallback_general''' (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (delay : ℕ) (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hshape : GalilWatchOkInst.StartShape P) (hbudget : ReplayBudgetR raw P q first delay)
    (hinv : ReplayStageInv raw P q first) (hrs : RestartShape P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = delay) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :
    (∃ (es : List Bool) (c' : Control) (t' : GalilVM),
      WatchSegE P q first delay es c t c' t' ∧
      (SoundScanNR raw ⟨c', t'⟩ →
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) es.length ⟨c, t⟩ ⟨c', t'⟩) ∧
      es.length = r * delay ∧ es.count true = r ∧
      position t'.right = position t.right + r ∧ t'.center = t.center ∧
      GalilReplaySegment.InvScan delay raw c' t' r) ∨
    ChainEnd raw P q first delay (position t.right + r) c t 0 r ∨
    (BrokeAndRestarted raw P q first delay c t ∧
      ∃ (n : ℕ) (c' : Control) (t' : GalilVM),
        (SoundScanNR raw ⟨c', t'⟩ →
          StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, t⟩ ⟨c', t'⟩) ∧
        position t'.right = position t.right + r ∧ t'.center = t.center ∧
        GalilReplaySegment.InvScan delay raw c' t' r) :=
  replay_after_fallback_general'' raw P hP hP' q first delay hex hd hsearch hpres hshape
    (replayBudget_of_R hbudget hinv) hrs r hr0 c t hm hc hrpl hR hrep hM hfr hsi

#print axioms budget_clauses
#print axioms replayBudget_of_R
#print axioms replayBudgetR_of_decodes
#print axioms replay_after_fallback_general'''

end PalPeg.GalilFoundStage
