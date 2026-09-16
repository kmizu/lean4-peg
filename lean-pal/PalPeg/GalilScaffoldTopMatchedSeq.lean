import PalPeg.GalilScaffoldTopOnly

/-!
# Matched comparison sequences as only-compare runs

`MatchedSeq n s t`: the controller's counting ticks (background only) and
`n` matched comparisons (`compareVM` data with the outer symbols agreeing,
the chain still watching), each comparison at a non-final continuation
cell. In `periodOnly` watch mode at lag zero the projection is constant
over counting ticks and steps by `onlyCompareNext` at comparisons, so the
sequence projects to `OnlyMatchedRun` — the building block of
`CompareRounds`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

inductive MatchedSeq (P : Shared) (q : ℕ) (first : Fin 9) : ℕ → GalilVM → GalilVM → Prop
  | stop (s : GalilVM) : MatchedSeq P q first 0 s s
  | count (s s' : GalilVM) {n : ℕ} {t : GalilVM}
      (hb : (galilFrameS P q first).background s s') (rest : MatchedSeq P q first n s' t) :
      MatchedSeq P q first n s t
  | compare (s : GalilVM) (vs : ScanVM) (vq : SearchVM) {n : ℕ} {t : GalilVM}
      (hav : canRight s.right) (hcont : singlePositive s.cycle = false)
      (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
      (hmt : (galilFrame P q first).matched (scanLens.set s vs))
      (hwatch : ∃ w', vs.chain = .watch w')
      (hq : searchEffect P true s vq)
      (rest : MatchedSeq P q first n (afterCompare s vs vq) t) :
      MatchedSeq P q first (n+1) s t

theorem compare_parts (P : Shared) (q : ℕ) (first : Fin 9) {s : GalilVM} {vs : ScanVM}
    (h : (galilFrame P q first).compare s (scanLens.set s vs))
    (hm : read (left s.left) = read (right s.right)) :
    vs.left = left s.left ∧ vs.right = right s.right ∧ ChainTick true s.chain vs.chain := by
  obtain ⟨⟨hl, hr, ht⟩, _⟩ := h
  rw [scanLens.get_set] at hl hr ht
  have ht' : ChainTick (decide (read (left s.left) = read (right s.right))) s.chain vs.chain := ht
  rw [decide_eq_true hm] at ht'
  exact ⟨hl, hr, ht'⟩

theorem matched_parts (P : Shared) (q : ℕ) (first : Fin 9) {s : GalilVM} {vs : ScanVM}
    (h : (galilFrame P q first).matched (scanLens.set s vs)) : read vs.left = read vs.right := by
  have h' : read (scanLens.get (scanLens.set s vs)).left = read (scanLens.get (scanLens.set s vs)).right := h
  rw [scanLens.get_set] at h'
  exact h'

/-- A background tick keeps the projection when the chain watches at lag zero. -/
theorem background_only (P : Shared) (q : ℕ) (first : Fin 9) {s s' : GalilVM}
    (hb : (galilFrameS P q first).background s s') (w : GalilScaffoldChainWatch.State)
    (hs : s.chain = .watch w) (hz : zero w.lag = true) :
    s'.chain = .watch w ∧ toOnly s' w = toOnly s w ∧ s'.periodOnly = s.periodOnly := by
  obtain ⟨hl, hr, _, hcen, hpo, hrad, _, hcy, _⟩ := backgroundS_fields P q first hb
  have ht := backgroundS_chainTick P q first hb (by rw [hs]; intro h0; cases h0)
  rw [hs] at ht
  have hc := chainTick_false_idle hz ht
  refine ⟨hc, ?_, hpo⟩
  simp only [toOnly, hl, hr, hcen, hcy, hrad]

/-- The matched sequence projects to an only-compare run. -/
theorem matchedSeq_only (P : Shared) (q : ℕ) (first : Fin 9) {n : ℕ} :
    ∀ {s t : GalilVM} (w : GalilScaffoldChainWatch.State), MatchedSeq P q first n s t →
      s.periodOnly = true → s.chain = .watch w → zero w.lag = true →
      ∃ w' : GalilScaffoldChainWatch.State, t.chain = .watch w' ∧ zero w'.lag = true ∧
        t.periodOnly = true ∧ OnlyMatchedRun (toOnly s w) n (toOnly t w') := by
  intro s t w h
  induction h generalizing w with
  | stop s =>
    intro hp hs hz
    exact ⟨w, hs, hz, hp, .stop _⟩
  | count s s' hb rest ih =>
    intro hp hs hz
    obtain ⟨hc, heq, hpo⟩ := background_only P q first hb w hs hz
    obtain ⟨w', ht, hz', hp', hrun⟩ := ih w (by rw [hpo]; exact hp) hc hz
    rw [heq] at hrun
    exact ⟨w', ht, hz', hp', hrun⟩
  | compare s vs vq hav hcont hcmp hmt hwatch hq rest ih =>
    intro hp hs hz
    have hmatch0 : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨hl, hr, ht⟩ := compare_parts P q first hcmp hmatch0
    obtain ⟨w1, hw1⟩ := hwatch
    have ht' := ht
    rw [hs, hw1] at ht'
    have hw1' := chainTick_true_immediate hz ht'
    subst hw1'
    have hz1 : zero (GalilScaffoldChainWatch.immediate w).lag = true := hz
    have hs1 : (afterCompare s vs vq).chain = .watch (GalilScaffoldChainWatch.immediate w) := by
      show (searchLens.set (scanLens.set s vs) vq).chain = _
      simp [searchLens, scanLens, hw1]
    have hp1 : (afterCompare s vs vq).periodOnly = true := hp
    obtain ⟨w', ht2, hz', hp', hrun⟩ := ih _ hp1 hs1 hz1
    refine ⟨w', ht2, hz', hp', ?_⟩
    have hmatch : read (left s.left) = read (right s.right) := by
      have := matched_parts P q first hmt
      rw [hl, hr] at this; exact this
    have hnext := afterCompare_only s w (GalilScaffoldChainWatch.immediate w) vs vq hp hs hz hl hr hw1 ht
    rw [hnext] at hrun
    exact .next _ hav hcont hmatch hrun

#print axioms matchedSeq_only

end PalPeg.GalilScaffoldChainInputSupply
