import PalPeg.GalilOracleLeaves2
import PalPeg.GalilInvPlus2
import PalPeg.GalilReplaySegment
import PalPeg.GalilReplaySpan

/-!
# The `houtReplay` leaf of `GalilOracleLeaves2.h_oracle_of_leaves'`

The leaf, as `PalPeg.GalilOracleLeaves2.h_oracle_of_leaves'` states it, is

```
∀ (w : List (Fin 2)) (c' : Control) (t' : GalilVM) (k : ℕ),
  GalilReplaySegment.InvScan 2048 w c' t' k → SoundScanNR w ⟨c', t'⟩
```

and `SoundScanNR w ⟨c', t'⟩` unfolds (at an `InvScan` state, whose `mode`
field supplies both guards) to `OutputRel w c' t'`.

## 1. The leaf as stated is not provable

No field of `InvScan` mentions `c.output`: `mode` pins `c.mode`,
`c.replaying`, `c.clock`, `minv` (`MInv`) and `rest_replay` (`ReplayRest`)
see only `c.replaying` (and `c.mode`), and every other field is about the VM.
So `InvScan` is invariant under `c ↦ {c with output := b}`
(`invScan_output_irrelevant`), while `OutputRel` is not, and the leaf is
therefore *equivalent* to the global claim `invScan_forces_pal`: at **every**
`InvScan` state whose right head stands on a letter, the prefix read so far is
a palindrome.  That is false for the machine (the scan reaches non-palindromic
prefixes), so the leaf has to be restated, not proved.

## 2. The restatement, and why it is immediate

`GalilOracleLocal.InvL := InvS ∧ OutputRel` with
`InvS := Inv ∨ ∃ k, InvScan`, so the `InvScan` branch of `InvL` *is*
`InvScan ∧ OutputRel`.  Naming that conjunction

```
InvScanO delay raw c s k := InvScan delay raw c s k ∧ OutputRel raw c s
```

makes the leaf immediate (`houtReplay_of_invScanO`, `fun _ _ => h.2`), and
`invL_of_invScanO` / `invScanO_of_invL` show it is exactly the `InvScan`
branch of the recursion state the oracle already runs on.

## 3. The producers land in `InvScanO`

`watchSegE_outputM` weakens the entry hypothesis of
`GalilScaffoldChainInputSupply.watchSegE_output` from `OutputRel raw c s` to
`OutputRel raw c s ∨ 0 < es.count true`: the three matching constructors of
`WatchSegE` (`match`, `matchIdle`, `matchIdleR`) all carry a `refresh` of the
output, and `outputRel_of_refresh` makes the landing sound from that
comparison onwards — the entry relation is only needed for a segment with no
comparison at all.  (The existing proof already discards it in those three
cases.)

Every replay segment runs `r > 0` forced comparisons, so this discharges the
`WatchSegE`-producing landings **unconditionally**:

* `invScanO_of_replay_after_fallback` — `GalilReplaySegment.replay_after_fallback`;
* `invScanO_of_replay_general` — branch (i) (quiet) of
  `GalilReplaySpan.replay_after_fallback_general''`, equivalently of
  `GalilInvPlus2.invScanC_of_replay_general`.

The remaining producer, branch (iii) (`BrokeAndRestarted`) of
`replay_after_fallback_general''`, publishes only a `StepsAll` and no
`WatchSegE`, so `watchSegE_outputM` does not reach it.  It does not need a new
proof either: `GalilReplaySpan.chain_runW` already proves
`P.onLetter = onLetterVM raw → P.leftFirst = leftFirstVM → m' = 0 →
OutputRel raw c' t` in the second disjunct of `LiveEnd`, and that conjunct is
dropped by `Result3` / `replay_construct3` / `replay_after_fallback_general''`.
Re-exporting it through those three statements is the only edit to existing
files this leaf needs.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.GalilLeafOutReplay

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilInvPlus2
open PalPeg.GalilBranchInvariants2 (SearchReady)

/-! ## 1. The leaf as stated is not provable -/

/-- **`InvScan` does not see the output.**  Every field of `InvScan` is about
the VM or about `c.mode` / `c.replaying` / `c.clock`. -/
theorem invScan_output_irrelevant {delay : ℕ} {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    {k : ℕ} (b : Bool) (h : PalPeg.GalilReplaySegment.InvScan delay raw c s k) :
    PalPeg.GalilReplaySegment.InvScan delay raw {c with output := b} s k :=
  { chainIdle := h.chainIdle, scan := h.scan
    minv := by
      obtain ⟨h1, h2⟩ := h.minv
      exact ⟨h1, h2⟩
    mode := ⟨h.mode.1, h.mode.2.1, h.mode.2.2⟩
    search := h.search, block := h.block, frontier := h.frontier
    rest_replay := by
      intro hc
      exact h.rest_replay (by rcases hc with hc | hc; exacts [Or.inl hc, Or.inr hc])
    input := h.input, shiftIdle := h.shiftIdle }

/-- **What the leaf really asks for.**  Because the output is a free field of
an `InvScan` state, the leaf is equivalent to: at *every* `InvScan` state whose
right head stands on a letter, the prefix read so far is a palindrome. -/
theorem invScan_forces_pal
    (H : ∀ (w : List (Fin 2)) (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 w c' t' k → SoundScanNR w ⟨c', t'⟩) :
    ∀ (w : List (Fin 2)) (c' : Control) (t' : GalilVM) (k j : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 w c' t' k →
      0 < j → j ≤ w.length → position t'.right = 2 * j - 1 → IsPal (w.take j) := by
  intro w c' t' k j h hj hjw hpos
  have h' := invScan_output_irrelevant true h
  exact H w {c' with output := true} t' k h' h'.mode.1 h'.mode.2.1 rfl j hj hjw hpos

/-! ## 2. The restatement -/

/-- `InvScan` together with the sound output — the `InvScan` branch of
`GalilOracleLocal.InvL`. -/
def InvScanO (delay : ℕ) (raw : List (Fin 2)) (c : Control) (s : GalilVM) (k : ℕ) : Prop :=
  PalPeg.GalilReplaySegment.InvScan delay raw c s k ∧ OutputRel raw c s

/-- **The leaf, for `InvScanO`.**  Immediate. -/
theorem houtReplay_of_invScanO (w : List (Fin 2)) (c' : Control) (t' : GalilVM) (k : ℕ)
    (h : InvScanO 2048 w c' t' k) : SoundScanNR w ⟨c', t'⟩ :=
  fun _ _ => h.2

/-- `InvScanO` is an `InvL` state. -/
theorem invL_of_invScanO {raw : List (Fin 2)} {c : Control} {s : GalilVM} {k : ℕ}
    (h : InvScanO 2048 raw c s k) : InvL raw c s := ⟨Or.inr ⟨k, h.1⟩, h.2⟩

/-- Conversely, the `InvScan` branch of `InvL` *is* `InvScanO`. -/
theorem invScanO_of_invL {raw : List (Fin 2)} {c : Control} {s : GalilVM} {k : ℕ}
    (h : InvL raw c s) (hk : PalPeg.GalilReplaySegment.InvScan 2048 raw c s k) :
    InvScanO 2048 raw c s k := ⟨hk, h.2⟩

/-! ## 3. Output soundness from a segment that compares -/

/-- **`watchSegE_output` with the entry relation weakened.**  A segment with at
least one matched comparison refreshes the output at that comparison, so its
landing carries `OutputRel` whatever the entry output was. -/
theorem watchSegE_outputM (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) (cen : ℕ) :
    ∀ r : ℕ, ScanInvariant raw cen r s.left s.right →
      (OutputRel raw c s ∨ 0 < es.count true) → OutputRel raw c' t := by
  induction h with
  | stop c s =>
    intro r _ ho
    rcases ho with ho | ho
    · exact ho
    · simp at ho
  | wait c s s' _ _ _ hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr, _, _⟩ := background_frame P q first hb
    refine ih r (by rw [hl, hr]; exact hi) ?_
    rcases ho with ho | ho
    · refine Or.inl ?_
      intro hout k hk hk2 hrk
      rw [hr] at hrk
      exact ho hout k hk hk2 hrk
    · exact Or.inr (by simpa using ho)
  | count c s s' _ _ _ _ hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr, _, _⟩ := background_frame P q first hb
    refine ih r (by rw [hl, hr]; exact hi) ?_
    rcases ho with ho | ho
    · refine Or.inl ?_
      intro hout k hk hk2 hrk
      rw [hr] at hrk
      exact ho hout k hk hk2 hrk
    · exact Or.inr (by simpa using ho)
  | countR c s s' _ _ _ _ hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr, _, _⟩ := background_frame P q first hb
    refine ih r (by rw [hl, hr]; exact hi) ?_
    rcases ho with ho | ho
    · refine Or.inl ?_
      intro hout k hk hk2 hrk
      rw [hr] at hrk
      exact ho hout k hk hk2 hrk
    · exact Or.inr (by simpa using ho)
  | «match» c s vs vq o _ _ ha _ _ hcmp hmt _ ho' _ ih =>
    intro r hi _
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨hl, hr, _⟩ := compare_parts P q first hcmp hmatch
    have hi' : ScanInvariant raw cen (r+1) (afterCompare s vs vq).left (afterCompare s vs vq).right := by
      rw [afterCompare_left, afterCompare_right, hl, hr]
      exact scanInvariant_matched hi ha hmatch
    exact ih (r+1) hi' (Or.inl (outputRel_of_refresh raw P hP hP' q first _ _ o hi' ho'))
  | matchIdle c s vs vq o _ _ ha _ _ hl hr _ hmt _ _ ho' _ ih =>
    intro r hi _
    have hmatch : read (left s.left) = read (right s.right) := by
      have := matched_parts P q first hmt
      rw [hl, hr] at this; exact this
    have hi' : ScanInvariant raw cen (r+1) (afterCompare s vs vq).left (afterCompare s vs vq).right := by
      rw [afterCompare_left, afterCompare_right, hl, hr]
      exact scanInvariant_matched hi ha hmatch
    exact ih (r+1) hi' (Or.inl (outputRel_of_refresh raw P hP hP' q first _ _ o hi' ho'))
  | matchIdleR c s vs vq o _ _ _ ha _ hl hr _ hmt _ _ ho' _ ih =>
    intro r hi _
    have hmatch : read (left s.left) = read (right s.right) := by
      have := matched_parts P q first hmt
      rw [hl, hr] at this; exact this
    have hi' : ScanInvariant raw cen (r+1) (replayDec true (afterCompare s vs vq)).left
        (replayDec true (afterCompare s vs vq)).right := by
      rw [replayDec_left, replayDec_right, afterCompare_left, afterCompare_right, hl, hr]
      exact scanInvariant_matched hi ha hmatch
    exact ih (r+1) hi' (Or.inl (outputRel_of_refresh raw P hP hP' q first _ _ o hi' ho'))

/-! ## 4. The producers, re-exported at `InvScanO` -/

/-- **`GalilReplaySegment.replay_after_fallback` lands in `InvScanO`.**  The
`r > 0` forced comparisons of the replay refresh the output, so the landing's
`OutputRel` — and hence the `SoundScanNR` premise the lemma hands back — is
unconditional. -/
theorem invScanO_of_replay_after_fallback (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (q : ℕ) (first : Fin 9)
    (delay : ℕ) (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = delay) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :
    ∃ (es : List Bool) (c' : Control) (t' : GalilVM),
      WatchSegE P q first delay es c t c' t' ∧
      StepsAll (galilFrameS P q first) delay (SoundScanNR raw) es.length ⟨c, t⟩ ⟨c', t'⟩ ∧
      es.length = r * delay ∧ es.count true = r ∧
      position t'.right = position t.right + r ∧ t'.center = t.center ∧
      InvScanO delay raw c' t' r := by
  obtain ⟨es, c', t', hseg, hst, hlen, hcnt, hpos, hC, hIS⟩ :=
    PalPeg.GalilReplaySegment.replay_after_fallback raw P q first delay hex hd hsearch hpres
      hquiet r hr0 c t hm hc hrpl hR hrep hM hfr hsi
  have hout : OutputRel raw c' t' :=
    watchSegE_outputM raw P hP hP' q first delay hseg (position t.center) 0
      (by simpa using hR.2.2.2.1) (Or.inr (by rw [hcnt]; exact hr0))
  exact ⟨es, c', t', hseg, hst (fun _ _ => hout), hlen, hcnt, hpos, hC, ⟨hIS, hout⟩⟩

/-- **The quiet branch of `GalilReplaySpan.replay_after_fallback_general''`
lands in `InvScanO`** too, for the same reason.  Branches (ii) and (iii) are
unchanged. -/
theorem invScanO_of_replay_general (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (delay : ℕ) (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hshape : PalPeg.GalilWatchOkInst.StartShape P)
    (hbudget : PalPeg.GalilReplaySpan.ReplayBudget raw P delay)
    (hrs : PalPeg.GalilReplaySpan.RestartShape P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = delay) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :
    (∃ (es : List Bool) (c' : Control) (t' : GalilVM),
      WatchSegE P q first delay es c t c' t' ∧
      StepsAll (galilFrameS P q first) delay (SoundScanNR raw) es.length ⟨c, t⟩ ⟨c', t'⟩ ∧
      es.length = r * delay ∧ es.count true = r ∧
      position t'.right = position t.right + r ∧ t'.center = t.center ∧
      InvScanO delay raw c' t' r) ∨
    PalPeg.GalilReplaySpan.ChainEnd raw P q first delay (position t.right + r) c t 0 r ∨
    (PalPeg.GalilReplaySpan.BrokeAndRestarted raw P q first delay c t ∧
      ∃ (n : ℕ) (c' : Control) (t' : GalilVM),
        (SoundScanNR raw ⟨c', t'⟩ →
          StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, t⟩ ⟨c', t'⟩) ∧
        position t'.right = position t.right + r ∧ t'.center = t.center ∧
        PalPeg.GalilReplaySegment.InvScan delay raw c' t' r) := by
  rcases PalPeg.GalilReplaySpan.replay_after_fallback_general'' raw P hP hP' q first delay hex hd
      hsearch hpres hshape hbudget hrs r hr0 c t hm hc hrpl hR hrep hM hfr hsi with
    ⟨es, c', t', hseg, hst, hlen, hcnt, hpos, hC, hIS⟩ | hEnd | hBr
  · have hout : OutputRel raw c' t' :=
      watchSegE_outputM raw P hP hP' q first delay hseg (position t.center) 0
        (by simpa using hR.2.2.2.1) (Or.inr (by rw [hcnt]; exact hr0))
    exact Or.inl ⟨es, c', t', hseg, hst (fun _ _ => hout), hlen, hcnt, hpos, hC, ⟨hIS, hout⟩⟩
  · exact Or.inr (Or.inl hEnd)
  · exact Or.inr (Or.inr hBr)

#print axioms invScan_output_irrelevant
#print axioms invScan_forces_pal
#print axioms houtReplay_of_invScanO
#print axioms invL_of_invScanO
#print axioms invScanO_of_invL
#print axioms watchSegE_outputM
#print axioms invScanO_of_replay_after_fallback
#print axioms invScanO_of_replay_general

end PalPeg.GalilLeafOutReplay
