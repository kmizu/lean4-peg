import PalPeg.GalilReplaySpan
import PalPeg.GalilLaterRadius

/-!
# Discharging `ReplayBudget` for the concrete machine

`GalilReplaySpan.ReplayBudget raw P delay` constrains a place `j` of a replay
that the started chain mispredicts: `C + 4n < j`, `R + 2 ≤ j` and
`2n + 3 + k ≤ (j - (R+2))·(delay-1)`, where `C` is the centre, `R = C + k` the
right head, `k` the radius and `n` the found period.

The three clauses are **true**, and all three come from one fact about the
search: *at a found tick the scan radius is at most twice the found period*,
`k ≤ 2n`.  That is not the bound `GalilLaterRadius` advertises
(`radius ≤ 4090h - 2052`, far too weak here: clause 2 needs `k ≤ 4n - 1`), but
it *is* what its proof actually establishes, and `found_radius_le_two_period`
below extracts it:

* first stage — `radius ≤ 2·max k₀ 1` with `k₀ < h` (`k₀` the DP lower bound),
  so `radius ≤ 2h`;
* later stage — `2·radius ≤ n'` for a window `span = 2n'` whose half `n'+1`
  carries no candidate, so `n' < 4h` (`later_stage_n_lt`) and `radius ≤ 2h - 1`.

This matches the reference machine: at a `replay_start` the Python scaffold
(`docs/palindromes-in-peg/scaffold_galil.py`) resets the radius and restarts the
search with `lower = 0`, and `scaffold_search.py` keeps the stage debt
`span/4 - matches ≥ 0`, while a stage of window `S` reports the least
palindromic prefix, which the previous stage `S/2` missed — hence
`S/8 < h ≤ S/4` and `radius ≤ S/4 < 2h`.

With `k ≤ 2n` the rest is arithmetic (`budget_arith`): `j > C + 4n ≥ C + 2k + 1`
gives `j ≥ R + 2`, and `j - (R+2) ≥ 4n - k - 1 ≥ 2n - 1 ≥ 1`, so with
`delay = 2048` the right side is at least `(2n-1)·2047 ≥ 4n + 3 ≥ 2n + 3 + k`.
Clause 1 itself is `mispredicted_beyond_candidate`, fed with the landing
palindrome `PalAt (encoded raw) C (k+m)` that `MInv` carries through the replay.

The one thing *not* proved here is the link from a found tick of a replay to
its search history.  `FoundStage`, the named hypothesis of
`replayBudget_of_foundStage`, is exactly that link: at a found tick the centre
head is represented, the found answer `n` is a DP candidate of the search
window, and `k ≤ 2n`.  Its last two components are `found_stage_data` — proved
here, for a found tick at the end of a `WatchSegE` out of a `Restarted` state
with `StageEntry` (the shape a `replay_start` leaves behind: radius reset, search
restarted with `lower = 0`, `restart_stage_bound_fallback`), with the block
length `n` identified with the DP head position by `answerAhead_eq_head`; its
first component is carried by `Restarted` and kept by `watchSegE_center`.  What
remains is the bookkeeping that every found tick of a replay is the found tick of
such a segment.
-/

set_option autoImplicit false
namespace PalPeg.GalilReplayBudgetProof
open PalPeg PalPeg.GalilScaffoldChainInputSupply Manacher GalilScaffoldInputHead
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter
open PalPeg.GalilReplaySpan PalPeg.GalilBranchInvariants PalPeg.GalilBranchInvariants2

/-! ## 1. The arithmetic of the budget -/

/-- **The budget arithmetic.**  From the first clause (`C + 4n < j`) and the
found-radius bound (`k ≤ 2n`) the other two clauses follow, for `delay = 2048`.
-/
theorem budget_arith {C k n j : ℕ} (hn : 1 ≤ n) (hk : k ≤ 2 * n) (hj : C + 4 * n < j) :
    C + k + 2 ≤ j ∧ 2 * n + 3 + k ≤ (j - (C + k + 2)) * 2047 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨by omega, ?_⟩
  have h1 : 2 * m + 1 ≤ j - (C + k + 2) := by omega
  have h2 : (2 * m + 1) * 2047 ≤ (j - (C + k + 2)) * 2047 := Nat.mul_le_mul_right _ h1
  omega

/-! ## 2. The sharp found radius: `radius ≤ 2h` -/

/-- **`found_radius_le_all_stages`, sharpened.**  Its stage disjunction gives
`radius ≤ 2h` for the least candidate `h` of the search window — the bound the
replay budget needs, and much stronger than the `4090h - 2052` it advertises. -/
theorem found_radius_le_two_period (P : Shared) (qq : ℕ) (first : Fin 9) (hP : Decodes P)
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw r Rad last)
    (hcen : r.center = represent ⟨a :: ls, gap⟩ (rs.map some) q)
    {c0 : Control} (hcl : c0.clock = 2048)
    (hstage : StageEntry Rad last)
    {es1 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg : WatchSegE P qq first 2048 es1 c0 r cF sF) (hsF : sF.chain = .idle)
    (hcF : cF.clock = 1) (vq : SearchVM) (hq : searchEffect P true sF vq)
    (hfound : vq.search.mode = .found) :
    ∃ k h span : ℕ,
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) k h ∧
        (∀ g, g < h →
          ¬ GalilDpCorrect.Candidate
            ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) k g) ∧
        (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h ∧ 1 ≤ h ∧
        value sF.radius ≤ 2 * (h : ℤ) := by
  obtain ⟨k, h, span, -, -, -, hpos, hcand, hmin, hcase, h1, -⟩ :=
    GalilLaterRadius.found_radius_le_all_stages P qq first hP a ls rs q gap hR hcen hcl hstage hseg
      hsF hcF vq hq hfound
  refine ⟨k, h, span, hcand, hmin, hpos, h1, ?_⟩
  obtain ⟨hkh, -⟩ := GalilFoundRadiusBound.candidate_lower_lt hcand
  rcases hcase with ⟨-, -, hb⟩ | ⟨n', hs, -, hprev, hb, -⟩
  · have hm : max k 1 ≤ h := max_le (by omega) (by omega)
    have : ((max k 1 : ℕ) : ℤ) ≤ (h : ℤ) := by exact_mod_cast hm
    omega
  · rw [hs] at hcand
    have hn : n' < 4 * h :=
      GalilFoundRadiusBound.later_stage_n_lt _ n' k h hcand hprev
    have : (n' : ℤ) < 4 * (h : ℤ) := by exact_mod_cast hn
    omega

/-! ## 3. The first clause at a found tick -/

/-- The centre symbol of a represented centre, read off the encoded word. -/
theorem centre_getElem (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool) (centre : Fin 3)
    (hread : GalilScaffoldPlace.read ⟨a :: ls, gap⟩ = some centre) :
    (encoded ((a :: ls).reverse ++ rs ++ q))[
      position (represent ⟨a :: ls, gap⟩ (rs.map some) q)]? = some centre := by
  have hne : (GalilScaffoldPlace.stream ⟨a :: ls, gap⟩) ≠ [] := by
    cases gap <;> simp [GalilScaffoldPlace.stream]
  have hlen : 0 < (GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).length :=
    List.length_pos_of_ne_nil hne
  have hidx := stream_index a ls rs q gap 0 hlen
  rw [Nat.sub_zero] at hidx
  have hhead : (GalilScaffoldPlace.stream ⟨a :: ls, gap⟩)[0]?
      = (GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).head? := by
    cases (GalilScaffoldPlace.stream ⟨a :: ls, gap⟩) <;> rfl
  rw [position_represent, ← hidx, hhead, ← GalilScaffoldPlace.read_stream, hread]

/-! ## 4. `ReplayBudget` from the search history -/

/-- **Named hypothesis (the search history at a found tick).**  At a found tick
of a chain-idle scan with a block of length `n`:

* the centre head is represented on a real symbol (`Entry` carries this);
* the found answer `n` is a DP candidate of the search window
  (`found_radius_le_all_stages`, whose `h` is the block length);
* the scan radius is at most twice the found period
  (`found_radius_le_two_period`).
-/
def FoundStage (raw : List (Fin 2)) (P : Shared) : Prop :=
  ∀ (s : GalilVM) (a : Bool) (vq : SearchVM) (k n : ℕ),
    s.chain = .idle → SearchReady (searchLens.get s) → searchEffect P a s vq →
    vq.search.mode = .found → AnswerAhead (vq.dp.config.tapes 11) n → 0 < n →
    PlaceAhead (P.place s) n → ScanInvariant raw (position s.center) k s.left s.right →
    (GalilScaffoldInputTrace.Represents s.center.head raw ∧ s.center.head.focus ≠ none) ∧
    (∃ lower span : ℕ,
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream (P.place s)).take (span+1)) lower n) ∧
    k ≤ 2 * n

/-- **`ReplayBudget` for the concrete machine.**  All three clauses, from the
search history at the found tick and `Decodes P`. -/
theorem replayBudget_of_foundStage {raw : List (Fin 2)} {P : Shared} (hP : Decodes P)
    (hstage : FoundStage raw P) : ReplayBudget raw P 2048 := by
  intro c s a vq k m n xs b hm hr hidle hsr hq hf hM hi hrad hrep hm0 hfr ha hn hpl hsplit
    j hj1 hj2 hmis
  obtain ⟨⟨hcenrep, hfocus⟩, ⟨lower, span, hcand⟩, hk2⟩ :=
    hstage s a vq k n hidle hsr hq hf ha hn hpl hi
  obtain ⟨al, ls, rs, qq, hdec, hraw⟩ := represents_decompose s.center raw hcenrep hfocus
  subst hraw
  obtain ⟨hread, hplace⟩ := hP.1 s al ls rs qq s.center.gap hdec
  -- the landing palindrome of the replay, from `MInv`
  obtain ⟨m', hm'0, hrep', hleft⟩ := hM.1 hr
  have hmm : m' = m := ofNat_inj (by rw [← hrep', hrep])
  rw [hmm] at hleft
  have hRC : position s.right = position s.center + k := hi.rightPos
  have hpal : PalAt (encoded ((al :: ls).reverse ++ rs ++ qq)) (position s.center) (k + m) := by
    have := hleft.1.2.2
    rw [hRC] at this
    simpa [show position s.center + k + m - position s.center = k + m from by omega] using this
  -- the centre position and symbol
  have hCpos : position s.center
      = position (represent ⟨al :: ls, s.center.gap⟩ (rs.map some) qq) := by rw [← hdec]
  have hcen := centre_getElem al ls rs qq s.center.gap (P.centre s) hread
  rw [← hCpos] at hcen
  -- clause 1
  have hclause1 : position s.center + 4 * n < j := by
    have := mispredicted_beyond_candidate al ls rs qq s.center.gap span lower n (k + m)
      (P.centre s) b xs (by rw [← hplace]; exact hcand) (by rw [← hplace]; exact hsplit)
      (by rw [← hCpos]; exact hcen) (by rw [← hCpos]; exact hpal) j
      (by rw [← hCpos]; exact hj1) (by rw [← hCpos]; omega)
      (by rw [← hCpos]; exact hmis)
    rw [← hCpos] at this
    exact this
  -- clauses 2 and 3
  obtain ⟨h2, h3⟩ := budget_arith hn hk2 hclause1
  exact ⟨hclause1, by omega, by rw [hRC]; simpa using h3⟩

/-! ## 5. The block length is the DP head position -/

/-- **`AnswerAhead` reads the DP answer.**  On the output tape of a completed DP
(`tape 11 = output h`, `pos 11 = h`) the block length `n` that the chain copies
is exactly `h`: the answer tape carries its `4` at the origin, so the `n` eights
ahead of it are all of them. -/
theorem answerAhead_eq_head {t : GalilScaffoldTape.Tape} {n h : ℕ} (ha : AnswerAhead t n)
    (hden : GalilScaffoldTape.denote t = GalilDpCounters.output h)
    (hpos : GalilScaffoldTape.head t = h) : n = h := by
  obtain ⟨ls, he⟩ := ha
  have hlen : t.left.length = n + ls.length := by
    have := congrArg List.length he
    simp at this
    omega
  have hread : GalilScaffoldTape.denote t ls.length = 4 := by
    cases n with
    | zero =>
      have hf : t.focus = 4 := by simpa using (List.cons.inj he).1
      have hls : t.left = ls := by simpa using (List.cons.inj he).2
      have := GalilScaffoldTape.focus_eq t
      rw [hf] at this
      rw [← this]
      congr 1
      rw [GalilScaffoldTape.head, hls]
    | succ m =>
      have hl : t.left = List.replicate m 8 ++ 4 :: ls := by
        simpa [List.replicate_succ] using (List.cons.inj he).2
      have hrev : t.left.reverse ++ t.focus :: t.right
          = ls.reverse ++ 4 :: (List.replicate m 8 ++ t.focus :: t.right) := by
        rw [hl]
        simp [List.reverse_append, List.reverse_replicate]
      show GalilScaffoldTape.read (t.left.reverse ++ t.focus :: t.right) ls.length = 4
      rw [hrev, show ls.length = ls.reverse.length from by simp]
      exact GalilScaffoldTape.read_at_append _ _ _
  rw [hden] at hread
  have hz : ls.length = 0 := by
    by_contra hne
    unfold GalilDpCounters.output at hread
    rw [if_neg hne] at hread
    split at hread <;> exact absurd hread (by decide)
  rw [GalilScaffoldTape.head] at hpos
  omega

/-- **The found tick's candidate and radius, in terms of the block length.**
`found_radius_le_two_period` with the DP head position `h` replaced by the block
length `n` — the two components of `FoundStage` that come from the search. -/
theorem found_stage_data (P : Shared) (qq : ℕ) (first : Fin 9) (hP : Decodes P)
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw r Rad last)
    (hcen : r.center = represent ⟨a :: ls, gap⟩ (rs.map some) q)
    {c0 : Control} (hcl : c0.clock = 2048)
    (hstage : StageEntry Rad last)
    {es1 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg : WatchSegE P qq first 2048 es1 c0 r cF sF) (hsF : sF.chain = .idle)
    (hcF : cF.clock = 1) (vq : SearchVM) (hq : searchEffect P true sF vq)
    (hfound : vq.search.mode = .found) {n : ℕ} (ha : AnswerAhead (vq.dp.config.tapes 11) n) :
    (∃ lower span : ℕ,
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) lower n) ∧
      1 ≤ n ∧ value sF.radius ≤ 2 * (n : ℤ) := by
  obtain ⟨k, h, span, -, hres, hpc, hpos, -, -, -, -, -⟩ :=
    GalilLaterRadius.found_radius_le_all_stages P qq first hP a ls rs q gap hR hcen hcl hstage hseg
      hsF hcF vq hq hfound
  obtain ⟨k', h', span', hcand', -, hpos', h1, hrad⟩ :=
    found_radius_le_two_period P qq first hP a ls rs q gap hR hcen hcl hstage hseg hsF hcF vq hq
      hfound
  have hhh : h' = h := by rw [← hpos, ← hpos']
  subst hhh
  have hnh : n = h' := by
    rcases hres with ⟨k2, -, -, -, -, htape, hpos2⟩ | ⟨hpc', -⟩
    · have hk2 : k2 = h' := by rw [← hpos, ← hpos2]
      subst hk2
      exact answerAhead_eq_head ha htape hpos2
    · rw [hpc] at hpc'; exact absurd hpc' (by decide)
  subst hnh
  exact ⟨⟨k', span', hcand'⟩, h1, hrad⟩


#print axioms budget_arith
#print axioms found_radius_le_two_period
#print axioms centre_getElem
#print axioms replayBudget_of_foundStage
#print axioms answerAhead_eq_head
#print axioms found_stage_data

end PalPeg.GalilReplayBudgetProof
