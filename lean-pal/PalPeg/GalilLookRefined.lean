import PalPeg.GalilTruncTick
import PalPeg.GalilNeedBound
import PalPeg.GalilFinalAssembly2
import PalPeg.GalilThrottledRunGen

/-!
# The refined chain lookahead

`GalilNeedBound.not_needLB_of_caughtUp`: `GalilTruncTick.lookChain` charges the chain
verifier two right moves in every mode, which overshoots at a caught-up checkpoint.
Here the lookahead is refined by the chain mode:

* `watch` with `positive lag` — two moves (`Internal.take` then `Outer.immediate`/break);
* `watch` with non-positive lag — one move (`Internal.idle` is forced, so only
  `Outer.immediate` or the break can move);
* `back` — one move (`backDone` then `Outer.immediate`/break);
* `copy` — no move (`copyBit`/`copyEnd` and `ChainMatched.copy`/`back` keep the verifier);
* `broken` — no move; `idle` — no verifier.

Everything downstream of `lookChain` (`tick_trunc`, `needL`, the τ-generic throttled run,
the ledger, and the final theorem) is redone with the refined lookahead.  §6 reduces
the pointwise bound `H_needL'` to a named trailing invariant `H_trail`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PalPeg.GalilLookRefined

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilTickArrive PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.GalilThrottledRun PalPeg.GalilThrottledRunGen PalPeg.GalilLedgerQ64
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilTruncTick PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2

/-! ## 1. The refined chain lookahead -/

/-- Letters the chain verifier may have consumed after one chain tick, by mode. -/
def lookChain' (n : ℕ) : ChainVM → ℕ
  | .idle => 0
  | .copy _ _ _ _ _ _ ver => usedPH n ver
  | .back _ _ _ _ ver => usedPH n (GalilScaffoldChainVerifier.right ver)
  | .watch w =>
    if GalilScaffoldCounter.positive w.lag = true then
      usedPH n (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right w.machine.verifier))
    else usedPH n (GalilScaffoldChainVerifier.right w.machine.verifier)
  | .broken w => usedPH n w.machine.verifier

/-- The refinement is below the old two-move lookahead. -/
theorem lookChain'_le (n : ℕ) (x : ChainVM) : lookChain' n x ≤ lookChain n x := by
  cases x with
  | idle => exact Nat.zero_le _
  | copy t h p v lag margin ver =>
    exact le_trans (usedPH_right_mono n _) (usedPH_right_mono n _)
  | back v h lag margin ver => exact usedPH_right_mono n _
  | watch w =>
    simp only [lookChain', lookChain, verOf]
    split_ifs
    · exact le_rfl
    · exact usedPH_right_mono n _
  | broken w => exact le_trans (usedPH_right_mono n _) (usedPH_right_mono n _)

/-- **`chainTick_used'`.** A chain tick consumes at most the refined lookahead. -/
theorem chainTick_used' (n : ℕ) {b : Bool} {x z : ChainVM} (ht : ChainTick b x z) :
    usedChain n z ≤ lookChain' n x := by
  obtain ⟨y, hs, hm⟩ := ht
  cases hs with
  | idle =>
    cases b
    · simp only [Bool.false_eq_true, if_false] at hm; subst hm; exact Nat.zero_le _
    · simp only [if_true] at hm; cases hm; exact Nat.zero_le _
  | brokenIdle w =>
    cases b
    · simp only [Bool.false_eq_true, if_false] at hm; subst hm; exact le_rfl
    · simp only [if_true] at hm; cases hm
  | copyBit t hh p v lag margin ver a one legal present =>
    cases b
    · simp only [Bool.false_eq_true, if_false] at hm; subst hm; exact le_rfl
    · simp only [if_true] at hm; cases hm; exact le_rfl
  | copyEnd t hh p v lag margin ver b' hl hp hv =>
    cases b
    · simp only [Bool.false_eq_true, if_false] at hm; subst hm; exact le_rfl
    · simp only [if_true] at hm; cases hm; exact le_rfl
  | backStep v hh lag margin ver hf =>
    cases b
    · simp only [Bool.false_eq_true, if_false] at hm; subst hm; exact usedPH_right_mono n _
    · simp only [if_true] at hm; cases hm; exact usedPH_right_mono n _
  | backDone v hh lag margin ver hf =>
    cases b
    · simp only [Bool.false_eq_true, if_false] at hm; subst hm; exact usedPH_right_mono n _
    · simp only [if_true] at hm
      cases hm with
      | watch w w' ho =>
        cases ho with
        | queued hz => exact usedPH_right_mono n _
        | immediate hz hg => exact le_rfl
      | breaks w w' hb =>
        obtain ⟨-, -, -, -, -, ht⟩ := hb
        subst ht
        exact le_rfl
  | watchStep w w' hi =>
    cases hi with
    | idle hz =>
      have hl : lookChain' n (.watch w) =
          usedPH n (GalilScaffoldChainVerifier.right w.machine.verifier) := by
        simp only [lookChain', hz, Bool.false_eq_true, if_false]
      rw [hl]
      cases b
      · simp only [Bool.false_eq_true, if_false] at hm; subst hm; exact usedPH_right_mono n _
      · simp only [if_true] at hm
        cases hm with
        | watch w1 w2 ho =>
          cases ho with
          | queued hz' => exact usedPH_right_mono n _
          | immediate hz' hg => exact le_rfl
        | breaks w1 w2 hb =>
          obtain ⟨-, -, -, -, -, ht⟩ := hb
          subst ht
          exact le_rfl
    | take hp hg =>
      have hl : lookChain' n (.watch w) =
          usedPH n (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right w.machine.verifier)) := by
        simp only [lookChain', hp, if_true]
      rw [hl]
      cases b
      · simp only [Bool.false_eq_true, if_false] at hm; subst hm; exact usedPH_right_mono n _
      · simp only [if_true] at hm
        cases hm with
        | watch w1 w2 ho =>
          cases ho with
          | queued hz' => exact usedPH_right_mono n _
          | immediate hz' hg' => exact le_rfl
        | breaks w1 w2 hb =>
          obtain ⟨-, -, -, -, -, ht⟩ := hb
          subst ht
          exact le_rfl


/-! ## 2. The refined truncated tick -/

section VM
variable (raw : List (Fin 2)) (j : ℕ)

/-- The lookahead of a scan-mode state: R one move right, the chain verifier by the refined lookahead. -/
def look' (x : State GalilVM) : ℕ :=
  if x.ctl.mode = .scan then
    max (usedPH raw.length (GalilScaffoldChainVerifier.right x.vm.right)) (lookChain' raw.length x.vm.chain)
  else 0

theorem look'_scan {x : State GalilVM} (hm : x.ctl.mode = .scan) :
    usedPH raw.length (GalilScaffoldChainVerifier.right x.vm.right) ≤ look' raw x ∧
      lookChain' raw.length x.vm.chain ≤ look' raw x := by
  unfold look'; rw [if_pos hm]; omega

theorem chainAt_used' {b found : Bool} {ans : GalilScaffoldTape.Tape} {c : Fin 3}
    {w : GalilScaffoldPlace.Place} {ver : PH} {r : GalilScaffoldCounter.Counter}
    {x z : ChainVM} (h : chainAt b found ans c w ver r x z) :
    usedChain raw.length z ≤ max (usedPH raw.length ver) (lookChain' raw.length x) := by
  rcases h with ⟨_, ht⟩ | ⟨_, _, hz⟩ | ⟨_, _, hz⟩
  · exact le_trans (chainTick_used' raw.length ht) (le_max_right _ _)
  · subst hz; exact Nat.zero_le _
  · cases b
    · simp only [Bool.false_eq_true, if_false] at hz; subst hz
      exact le_max_left _ _
    · simp only [if_true] at hz
      cases hz
      exact le_max_left _ _

theorem compareFound_trunc' {P : Shared} (hP : SharedTrunc raw j P) (q : ℕ) (first : Fin 9)
    {s t : GalilVM} (hu : usedVM raw s ≤ j)
    (hr : usedPH raw.length (GalilScaffoldChainVerifier.right s.right) ≤ j)
    (hc : lookChain' raw.length s.chain ≤ j) (h : compareFound P q first s t) :
    compareFound P q first (truncVM (raw.length - j) s) (truncVM (raw.length - j) t) := by
  obtain ⟨vs, vq, b, hl, hr', hb, hse, hch, ht⟩ := h
  have hz : usedChain raw.length vs.chain ≤ j :=
    le_trans (chainAt_used' raw hch) (max_le (le_trans (usedVM_center raw s) hu) hc)
  refine ⟨⟨truncPH (raw.length - j) vs.left, truncPH (raw.length - j) vs.right,
    truncChain (raw.length - j) vs.chain⟩, vq, b, ?_, ?_, hb, (searchEffect_trunc raw j hP b s vq).mpr hse, ?_, ?_⟩
  · show truncPH _ vs.left = GalilScaffoldInputHead.left (truncPH _ s.left)
    rw [truncPH_left, hl]
  · show truncPH _ vs.right = GalilScaffoldChainVerifier.right (truncPH _ s.right)
    rw [truncPH_right raw.length j _ hr, hr']
  · rw [hP.centre, hP.place]
    exact chainAt_trunc raw j hch hz
  · subst ht
    rw [truncVM_afterBirth, truncVM_chain, chainBorn_truncChain]
    cases b <;> rfl

theorem backgroundS_trunc' {P : Shared} (hP : SharedTrunc raw j P) (q : ℕ) (first : Fin 9)
    {s t : GalilVM} (hu : usedVM raw s ≤ j) (hc : lookChain' raw.length s.chain ≤ j)
    (h : backgroundS P q first s t) :
    backgroundS P q first (truncVM (raw.length - j) s) (truncVM (raw.length - j) t) := by
  obtain ⟨hl, hr, hse, hch, hset⟩ := h
  have hz : usedChain raw.length t.chain ≤ j :=
    le_trans (chainAt_used' raw hch) (max_le (le_trans (usedVM_center raw s) hu) hc)
  refine ⟨?_, ?_, (searchEffect_trunc raw j hP false s _).mpr hse, ?_, ?_⟩
  · show truncPH _ t.left = truncPH _ s.left
    rw [hl]
  · show truncPH _ t.right = truncPH _ s.right
    rw [hr]
  · rw [hP.centre, hP.place]
    exact chainAt_trunc raw j hch hz
  · rw [truncVM_chain, chainBorn_truncChain]
    calc truncVM (raw.length - j) t
        = truncVM (raw.length - j) (afterBirth (chainBorn (decide ((searchLens.get t).search.mode
              = GalilScaffoldSearchFinish.Mode.found)) s.chain)
            (searchLens.set (scanLens.set s (scanLens.get t)) (searchLens.get t))) :=
          congrArg _ hset
      _ = _ := by rw [truncVM_afterBirth]; rfl

/-- **`tick_trunc'`.** A pre-loaded tick whose endpoints consumed at most `j`
letters and whose source lookahead (`look'`: in scan mode, R one move right and
the chain verifier by `lookChain'`) is at most `j` is also a tick with only `j`
letters arrived. -/
theorem tick_trunc' {P : Shared} (hP : SharedTrunc raw j P) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {x y : State GalilVM} (h : Tick (galilFrameS P q first) delay x y)
    (hx : usedVM raw x.vm ≤ j) (hy : usedVM raw y.vm ≤ j) (hl : look' raw x ≤ j) :
    Tick (galilFrameS P q first) delay (truncS (raw.length - j) x) (truncS (raw.length - j) y) := by
  cases h with
  | init c s s' hm h0 =>
    exact .init c _ _ hm (hP.init s s' hy h0)
  | scan_wait c s s' hm h0 hb =>
    obtain ⟨-, hc⟩ := look'_scan raw (x := ⟨c, s⟩) hm
    refine .scan_wait c _ _ hm ⟨h0.1, fun hav => h0.2 (canRight_of_trunc _ _ hav)⟩
      (backgroundS_trunc' raw j hP q first (s := s) hx (le_trans hc hl) hb)
  | scan_count c s s' hm h0 hc hb =>
    obtain ⟨hr, hch⟩ := look'_scan raw (x := ⟨c, s⟩) hm
    refine .scan_count c _ _ hm ?_ hc (backgroundS_trunc' raw j hP q first (s := s) hx (le_trans hch hl) hb)
    exact h0.imp id (fun hav => canRight_truncPH raw.length j _ hav (le_trans hr hl))
  | scan_match c s s' s'' o hm h0 hc hcmp hmt hpl ho =>
    obtain ⟨hr, hch⟩ := look'_scan raw (x := ⟨c, s⟩) hm
    have ht := Tick.scan_match (F := galilFrameS P q first) (delay := delay) c (truncVM (raw.length - j) s)
      (truncVM (raw.length - j) s') (truncVM (raw.length - j) s'') o hm
      (h0.imp id (fun hav => canRight_truncPH raw.length j _ hav (le_trans hr hl))) hc
      (compareFound_trunc' raw j hP q first hx (le_trans hr hl) (le_trans hch hl) hcmp) hmt
      (matchedPlace_trunc P q first _ c.replaying hpl) (refresh_trunc raw j hP q first ho)
    have he : (galilFrameS P q first).replayExhausted (truncVM (raw.length - j) s'') =
        (galilFrameS P q first).replayExhausted s'' := hP.replayExhausted s''
    rw [he] at ht
    exact ht
  | scan_shift c s s' s'' hm h0 hc hcmp hmt hr hg hb =>
    obtain ⟨hrr, hch⟩ := look'_scan raw (x := ⟨c, s⟩) hm
    exact .scan_shift c _ (truncVM (raw.length - j) s') _ hm
      (h0.imp id (fun hav => canRight_truncPH raw.length j _ hav (le_trans hrr hl))) hc
      (compareFound_trunc' raw j hP q first hx (le_trans hrr hl) (le_trans hch hl) hcmp) hmt hr
      ((hP.shiftGuard s').mpr hg) (hP.beginShift s' s'' hy hb)
  | scan_fallback c s s' s'' hm h0 hc hcmp hmt hg hr hb =>
    obtain ⟨hrr, hch⟩ := look'_scan raw (x := ⟨c, s⟩) hm
    exact .scan_fallback c _ (truncVM (raw.length - j) s') _ hm
      (h0.imp id (fun hav => canRight_truncPH raw.length j _ hav (le_trans hrr hl))) hc
      (compareFound_trunc' raw j hP q first hx (le_trans hrr hl) (le_trans hch hl) hcmp) hmt
      (hg.imp id (fun hn hs => hn ((hP.shiftGuard s').mp hs))) hr (hP.beginFallback s' s'' hb)
  | shift_one c s s' hm hp h0 =>
    exact .shift_one c _ _ hm hp (shiftOne_trunc raw j _ _ hy h0)
  | shift_done c s o hm hp ho =>
    exact .shift_done c _ o hm hp (refresh_trunc raw j hP q first ho)
  | copy_one c s s' hm hp h0 =>
    exact .copy_one c _ _ hm hp (fpp_rel_trunc _ _ h0)
  | copy_done c s s' hm hp h0 =>
    exact .copy_done c _ _ hm hp (fpp_rel_trunc _ _ h0)
  | home_start c s s' hm hl' h0 =>
    exact .home_start c _ _ hm hl' (fpp_rel_trunc _ _ h0)
  | home_step c s s' hm hl' h0 =>
    exact .home_step c _ _ hm hl' (fpp_rel_trunc _ _ h0)
  | fpp_slice c s s' hm h0 =>
    exact .fpp_slice c _ _ hm (fpp_rel_trunc _ _ h0)
  | fpp_done c s s' hm h0 =>
    exact .fpp_done c _ _ hm (fpp_rel_trunc _ _ h0)
  | markEnd_found c s s' hm he h0 =>
    refine .markEnd_found c _ _ hm he (rewind_rel_trunc _ _ ?_ h0)
    rintro u v ⟨h1, h2⟩
    exact ⟨h1, by subst h2; rfl⟩
  | markEnd_step c s s' hm he h0 =>
    exact .markEnd_step c _ _ hm he (fpp_rel_trunc _ _ h0)
  | choose_select c s s' hm ho hs h0 =>
    refine .choose_select c _ _ hm ho hs (rewind_rel_trunc _ _ ?_ h0)
    rintro u v h2
    subst h2; rfl
  | choose_step c s s' hm hs h0 =>
    refine .choose_step c _ _ hm hs (rewind_rel_trunc _ _ ?_ h0)
    rintro u v ⟨h1, h2⟩
    exact ⟨h1, by subst h2; rfl⟩
  | rewind_done c s s' hm hf h0 =>
    refine .rewind_done c _ _ hm hf (rewind_rel_trunc _ _ ?_ h0)
    rintro u v h2
    subst h2; rfl
  | rewind_one c s s' hm hf hp h0 =>
    refine .rewind_one c _ _ hm hf hp (rewind_rel_trunc _ _ ?_ h0)
    rintro u v ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    subst h2
    simp only [truncRewind, truncPH_left]
  | rewind_pair c s s' hm hf hp h0 =>
    refine .rewind_pair c _ _ hm hf hp (rewind_rel_trunc _ _ ?_ h0)
    rintro u v ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    subst h2
    simp only [truncRewind, truncPH_left]
  | replayStart c s s' o hm h0 ho ho' =>
    have hx' : (galilFrameS P q first).replayPos (truncVM (raw.length - j) s') =
        (galilFrameS P q first).replayPos s' := hP.replayPos s'
    have ht := Tick.replayStart (F := galilFrameS P q first) (delay := delay) c (truncVM (raw.length - j) s)
      (truncVM (raw.length - j) s') o hm (hP.replayStart s s' h0) (fun e => ho (hx' ▸ e))
      (fun e => refresh_trunc raw j hP q first (ho' (hx' ▸ e)))
    rw [hx'] at ht
    exact ht
  | restart c s s' hm hb =>
    exact .restart c _ _ hm (hP.restart s s' hb)

end VM


/-! ## 3. The refined need and preload -/

section Need
variable (raw : List (Fin 2)) (st : ℕ → State GalilVM)

/-- The need of the pre-loaded state `i` with the refined lookahead. -/
def needL' (i : ℕ) : ℕ := max (needS raw st i) (look' raw (st i))

/-- The need of the tick `k → k+1` (prefix maximum). -/
def needT' (k : ℕ) : ℕ := pmax (needL' raw st) (k+1)

theorem needS_le_needL' (i : ℕ) : needS raw st i ≤ needL' raw st i := le_max_left _ _

theorem needL'_le_needT' {i k : ℕ} (h : i ≤ k+1) : needL' raw st i ≤ needT' raw st k :=
  le_pmax _ _ _ h

/-- The refined need is below the old one. -/
theorem needL'_le_needL (i : ℕ) : needL' raw st i ≤ needL raw st i := by
  unfold needL' needL look' look
  split_ifs
  · have := lookChain'_le raw.length (st i).vm.chain
    omega
  · exact le_rfl

/-- Hypotheses on the pre-loaded trace for the refined lookahead need. -/
structure PreloadL' (Tc : ℕ → ℕ) : Prop where
  tc0 : Tc 0 = 0
  mono : ∀ m, m < raw.length → Tc m ≤ Tc (m+1)
  need0 : needL' raw st 0 = 0
  needLe : ∀ m, m < raw.length → ∀ k, k < Tc (m+1) → needT' raw st k ≤ m+1

theorem needLe_of_pointwise' (Tc : ℕ → ℕ)
    (h : ∀ m, m < raw.length → ∀ i, i ≤ Tc (m+1) → needL' raw st i ≤ m+1) :
    ∀ m, m < raw.length → ∀ k, k < Tc (m+1) → needT' raw st k ≤ m+1 :=
  fun m hm k hk => pmax_le _ _ _ fun i hi => h m hm i (by omega)

end Need

/-! ## 4. The refined throttled run, generic in `τ` -/

section Run
variable (τ : ℕ) (raw : List (Fin 2)) (st : ℕ → State GalilVM) (e : ℕ)

abbrev cfgLG' (t : ℕ) : Cfg := cfgG τ raw.length e (needT' raw st) t

def stLG' (t : ℕ) : State GalilVM :=
  truncS (raw.length - (cfgLG' τ raw st e t).j) (st (cfgLG' τ raw st e t).k)

def arrLG' (t : ℕ) : ℕ := (cfgLG' τ raw st e t).j

/-- **`AbstractRun'` for the τ-spaced lookahead-throttled run** (no `TruncTick`,
no `SufVM` hypothesis). -/
theorem abstractRun_throttledLG' (hτ : 2 ≤ τ) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hP : ∀ j, SharedTrunc raw j P) (hS : SharedSuf raw P)
    (hctl : (st 0).ctl = GalilScaffoldController.initial delay)
    (h0 : needL' raw st 0 = 0) (hsuf0 : SufVM raw (st 0).vm)
    (htick : ∀ k, k < e → Tick (galilFrameS P q first) delay (st k) (st (k+1))) :
    AbstractRun' P q first delay raw (stLG' τ raw st e) (arrLG' τ raw st e) := by
  have hsuf := sufVM_trace raw st e hS q first delay htick hsuf0
  refine ⟨hctl, rfl, fun t => ?_⟩
  have hused := cfgG_used τ raw.length e (needT' raw st) (needL' raw st) h0
    (fun k i hi => needL'_le_needT' raw st hi) t
  obtain ⟨-, hke, -, -⟩ := cfgG_inv τ hτ raw.length e (needT' raw st) t
  rcases cfgG_succ_cases τ raw.length e (needT' raw st) t with
    ⟨h1, _, h3⟩ | ⟨_, h2, h3, h4⟩ | ⟨_, _, h3⟩
  · refine Or.inr ⟨by simp only [arrLG', cfgLG', h3], raw[(cfgLG' τ raw st e t).j], ?_, ?_⟩
    · exact List.getElem?_eq_getElem h1
    · simp only [stLG', cfgLG', h3]
      exact (arrive_trunc raw _ h1 _ (hsuf _ hke)
        (le_trans (needS_le_needL' raw st _) (hused _ le_rfl))).symm
  · refine Or.inl ⟨by simp only [arrLG', cfgLG', h4], Or.inl ?_⟩
    simp only [stLG', cfgLG', h4]
    have hA : needL' raw st (cfgLG' τ raw st e t).k ≤ (cfgLG' τ raw st e t).j := hused _ le_rfl
    have hB : needL' raw st ((cfgLG' τ raw st e t).k + 1) ≤ (cfgLG' τ raw st e t).j :=
      le_trans (needL'_le_needT' raw st le_rfl) h3
    exact tick_trunc' raw _ (hP _) q first delay (htick _ h2)
      (le_trans (needS_le_needL' raw st _) hA) (le_trans (needS_le_needL' raw st _) hB)
      (le_trans (le_max_right _ _) hA)
  · refine Or.inl ⟨by simp only [arrLG', cfgLG', h3], Or.inr ?_⟩
    simp only [stLG', cfgLG', h3]

open Classical in
noncomputable def TcLG' (Tc : ℕ → ℕ) (m : ℕ) : ℕ :=
  if h : ∃ t, Tc m ≤ (cfgLG' τ raw st e t).k then Nat.find h else 0

theorem TcLG'_spec (Tc : ℕ → ℕ) (m : ℕ) (h : ∃ t, Tc m ≤ (cfgLG' τ raw st e t).k) :
    Tc m ≤ (cfgLG' τ raw st e (TcLG' τ raw st e Tc m)).k ∧
      ∀ t, Tc m ≤ (cfgLG' τ raw st e t).k → TcLG' τ raw st e Tc m ≤ t := by
  unfold TcLG'
  rw [dif_pos h]
  exact ⟨Nat.find_spec h, fun t ht => Nat.find_min' h ht⟩

theorem TcLG'_exact (Tc : ℕ → ℕ) (m : ℕ) (h : ∃ t, Tc m ≤ (cfgLG' τ raw st e t).k) :
    (cfgLG' τ raw st e (TcLG' τ raw st e Tc m)).k = Tc m := by
  obtain ⟨h1, h2⟩ := TcLG'_spec τ raw st e Tc m h
  refine le_antisymm ?_ h1
  rcases hT : TcLG' τ raw st e Tc m with _ | t'
  · simp [cfgLG', cfgG]
  · have hlt : ¬ Tc m ≤ (cfgLG' τ raw st e t').k := fun hc => by
      have := h2 t' hc; omega
    have := (cfgG_mono τ raw.length e (needT' raw st) t').2.1
    simp only [cfgLG'] at hlt this ⊢
    omega

theorem TcLG'_exists (hτ : 2 ≤ τ) {Tc : ℕ → ℕ} (hp : PreloadL' raw st Tc) :
    ∀ m, m ≤ raw.length →
      ∃ t, Tc m ≤ (cfgG τ raw.length (Tc raw.length) (needT' raw st) t).k := by
  intro m
  induction m with
  | zero => intro _; exact ⟨0, by rw [hp.tc0]; exact Nat.zero_le _⟩
  | succ m ih =>
    intro hm
    obtain ⟨hK, -⟩ := TcLG'_spec τ raw st (Tc raw.length) Tc m (ih (by omega))
    exact ⟨_, ostepG τ hτ raw.length _ (needT' raw st) Tc m hm (hp.mono m hm)
      (GalilCheckpoints.mono_of_step Tc raw.length hp.mono (m+1) raw.length hm le_rfl)
      (hp.needLe m hm) _ hK⟩

theorem TcLG'_zero (hτ : 2 ≤ τ) {Tc : ℕ → ℕ} (hp : PreloadL' raw st Tc) :
    TcLG' τ raw st (Tc raw.length) Tc 0 = 0 := by
  have h := TcLG'_exists τ raw st hτ hp 0 (Nat.zero_le _)
  have := (TcLG'_spec τ raw st _ Tc 0 h).2 0 (by rw [hp.tc0]; exact Nat.zero_le _)
  omega

theorem O_step_throttledLG' (hτ : 2 ≤ τ) {Tc : ℕ → ℕ} (hp : PreloadL' raw st Tc) (m : ℕ)
    (hm : m < raw.length) :
    TcLG' τ raw st (Tc raw.length) Tc (m+1) ≤
      max (TcLG' τ raw st (Tc raw.length) Tc m) ((m+1) * τ) + dwT Tc (m+1) := by
  obtain ⟨hK, -⟩ := TcLG'_spec τ raw st (Tc raw.length) Tc m (TcLG'_exists τ raw st hτ hp m hm.le)
  have ho := ostepG τ hτ raw.length _ (needT' raw st) Tc m hm (hp.mono m hm)
    (GalilCheckpoints.mono_of_step Tc raw.length hp.mono (m+1) raw.length hm le_rfl)
    (hp.needLe m hm) _ hK
  have := (TcLG'_spec τ raw st (Tc raw.length) Tc (m+1)
    (TcLG'_exists τ raw st hτ hp (m+1) hm)).2 _ ho
  simpa [dwT] using this

theorem stLG'_at_end (hτ : 2 ≤ τ) {Tc : ℕ → ℕ} (hp : PreloadL' raw st Tc) (hn : 0 < raw.length)
    {P : Shared} {q : ℕ} {first : Fin 9}
    (hrep : GalilLedgerAssembly.ReportPointAt P q first raw raw.length (st (Tc raw.length))) :
    stLG' τ raw st (Tc raw.length) (TcLG' τ raw st (Tc raw.length) Tc raw.length) =
      st (Tc raw.length) := by
  have hex := TcLG'_exists τ raw st hτ hp raw.length le_rfl
  have hk := TcLG'_exact τ raw st (Tc raw.length) Tc raw.length hex
  have hused := cfgG_used τ raw.length (Tc raw.length) (needT' raw st) (needL' raw st) hp.need0
    (fun k i hi => needL'_le_needT' raw st hi) (TcLG' τ raw st (Tc raw.length) Tc raw.length)
    (Tc raw.length) (by simp only [cfgLG'] at hk; omega)
  have hu := used_of_report raw hn hrep
  have hS := needS_le_needL' raw st (Tc raw.length)
  obtain ⟨i1, -, -, -⟩ := cfgG_inv τ hτ raw.length (Tc raw.length) (needT' raw st)
    (TcLG' τ raw st (Tc raw.length) Tc raw.length)
  have hjn : (cfgLG' τ raw st (Tc raw.length)
      (TcLG' τ raw st (Tc raw.length) Tc raw.length)).j = raw.length := by
    simp only [cfgLG', needS] at hused i1 hS ⊢
    omega
  unfold stLG'
  rw [hjn, hk, Nat.sub_self, truncS_zero]

end Run

/-- Ledger obligation for the τ-spaced lookahead-throttled runs. -/
theorem ledger_throttledLG' (τ : ℕ) (hτ2 : 2 ≤ τ) (α β : ℕ) (hτ : 2 * (α + β) ≤ τ)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (stOf : List (Fin 2) → ℕ → State GalilVM)
    (TcOf : List (Fin 2) → ℕ → ℕ)
    (hpre : ∀ w : List (Fin 2), 0 < w.length → PreloadL' w (stOf w) (TcOf w))
    (hrep : ∀ w : List (Fin 2), 0 < w.length →
      GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w w.length
        (stOf w (TcOf w w.length)))
    (O_cost : ∀ w : List (Fin 2), 0 < w.length → ∀ m, m < w.length →
      dwT (TcOf w) (m+1) ≤ α * (Cw w (m+1) - Cw w m) + β) :
    LedgerObligation Pof qof firstOf
      (fun w => stLG' τ w (stOf w) (TcOf w w.length))
      (fun w => (w.length + 1) * τ) := by
  intro w hw hpal
  have hp := hpre w hw
  have hz := GalilLedgerThrottled.backlog_zero_trunc' α β τ hτ w hw hpal (dwT (TcOf w))
    (O_cost w hw)
  have ht := GalilLedgerThrottled.on_time_trunc' α β τ hτ w (dwT (TcOf w))
    (TcLG' τ w (stOf w) (TcOf w w.length) (TcOf w)) (TcLG'_zero τ w (stOf w) hτ2 hp)
    (O_step_throttledLG' τ w (stOf w) hτ2 hp) hz
  obtain ⟨hrp, hfr⟩ := GalilLedgerAssembly.reportPoint_of_at_length hw (hrep w hw)
  refine ⟨TcLG' τ w (stOf w) (TcOf w w.length) (TcOf w) w.length, ht, ?_, ?_⟩
  · show ReportPoint w (stLG' τ w (stOf w) (TcOf w w.length) _)
    rw [stLG'_at_end τ w (stOf w) hτ2 hp hw (hrep w hw)]; exact hrp
  · show Refreshed _ _ _ (stLG' τ w (stOf w) (TcOf w w.length) _)
    rw [stLG'_at_end τ w (stOf w) hτ2 hp hw (hrep w hw)]; exact hfr

/-- **`AbstractRun'` for the lookahead-throttled run with arrivals `2^18` apart.** -/
theorem abstractRun_throttledL'_2p18 (raw : List (Fin 2)) (st : ℕ → State GalilVM) (e : ℕ)
    (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hP : ∀ j, SharedTrunc raw j P) (hS : SharedSuf raw P)
    (hctl : (st 0).ctl = GalilScaffoldController.initial delay)
    (h0 : needL' raw st 0 = 0) (hsuf0 : SufVM raw (st 0).vm)
    (htick : ∀ k, k < e → Tick (galilFrameS P q first) delay (st k) (st (k+1))) :
    AbstractRun' P q first delay raw (stLG' GalilLedgerThrottled.ticksPerSymbol raw st e)
      (arrLG' GalilLedgerThrottled.ticksPerSymbol raw st e) :=
  abstractRun_throttledLG' _ raw st e two_le_ticksPerSymbol P q first delay hP hS hctl h0 hsuf0 htick

/-- **Ledger obligation, lookahead need, run spacing = deadline slope = `2^18`.** -/
theorem ledger_throttledL'_2p18 (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (stOf : List (Fin 2) → ℕ → State GalilVM)
    (TcOf : List (Fin 2) → ℕ → ℕ)
    (hpre : ∀ w : List (Fin 2), 0 < w.length → PreloadL' w (stOf w) (TcOf w))
    (hrep : ∀ w : List (Fin 2), 0 < w.length →
      GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w w.length
        (stOf w (TcOf w w.length)))
    (O_base : ∀ w : List (Fin 2), 0 < w.length → TcOf w 1 ≤ 2050)
    (O_cost : ∀ w : List (Fin 2), 0 < w.length → ∀ m, 1 ≤ m → m < w.length →
      TcOf w (m+1) - TcOf w m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048) :
    LedgerObligation Pof qof firstOf
      (fun w => stLG' GalilLedgerThrottled.ticksPerSymbol w (stOf w) (TcOf w w.length))
      (fun w => (w.length + 1) * GalilLedgerThrottled.ticksPerSymbol) := by
  have hτ : 2 * (2 * alpha' 2048 + (2 * beta' 2048 + 1)) ≤ GalilLedgerThrottled.ticksPerSymbol := by
    have := GalilLedgerThrottled.two_c2_le_τ'
    unfold GalilLedgerThrottled.c2 at this
    exact this.trans_eq' (by ring)
  exact ledger_throttledLG' _ two_le_ticksPerSymbol _ _ hτ Pof qof firstOf stOf TcOf hpre hrep
    (fun w hw m hm => GalilLedgerThrottled.dwT_cost w (TcOf w) (hpre w hw).tc0 (O_base w hw)
      (O_cost w hw) m hm)

/-! ### Boot and hypotheses -/

theorem needL'_boot (w : List (Fin 2)) (st : ℕ → State GalilVM) (h : st 0 = boot w) :
    needL' w st 0 = 0 := by
  have h1 := needS_boot w st h
  have h2 : look' w (st 0) = 0 := by
    unfold look'
    rw [if_neg]
    rw [h]; simp [boot, GalilScaffoldController.initial]
  simp [needL', h1, h2]


section Hyps
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- (B') Pointwise lookahead need bound with the refined lookahead (premise of `needLe_of_pointwise'`). -/
def H_needL' : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → needL' w st i ≤ m+1

/-- (C) Realization over the `2^18`-spaced run throttled by the refined need. -/
def H_realizeL' : Prop :=
  ∃ (Q' Γ' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (_ : Fintype Γ') (_ : DecidableEq Γ')
    (t K : ℕ) (L : PalPeg.Local.LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q')
    (outQ : Q' → Bool) (n : ℕ) (htape : 0 < t) (hn : 0 < n),
    ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
      ((L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn).SAccepts w ↔
        LatchTrue (PofC centre place entry w) q first w (stLG' τF w st (Tc w.length))
          ((w.length + 1) * τF))

end Hyps

/-! ## 5. The final theorem with the refined lookahead -/

theorem pal_in_peg_final2'_gen (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9)
    (hA : H_oracle centre place entry q first)
    (hCP : H_centrePlace centre place)
    (hB_need : H_needL' centre place entry q first)
    (hB_base : H_base centre place entry q first)
    (hC : H_realizeL' centre place entry q first) :
    RecognizedByTotalPEG PAL := by
  classical
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := hC
  have key : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTrace centre place entry q first w st Tc := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨st, Tc, h⟩ := preTrace_exists centre place entry q first w hw (hA w hw)
      exact ⟨st, Tc, fun _ => h⟩
    · exact ⟨fun _ => boot w, fun _ => 0, fun h => absurd h hw⟩
  choose stP TcP hP using key
  let M := L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn
  have hpre : ∀ w : List (Fin 2), 0 < w.length → PreloadL' w (stP w) (TcP w) := by
    intro w hw
    have h := hP w hw
    exact ⟨h.tc0, fun m hm => h.mono m (m+1) (by omega) hm, needL'_boot w (stP w) h.start,
      needLe_of_pointwise' w (stP w) (TcP w) (hB_need w hw _ _ h)⟩
  refine pal_in_peg_of_latch' (Nat.mul_pos hn (PalPeg.Local.cnt_pos K)) M
    (PofC centre place entry) (fun _ => q) (fun _ => first) 2048
    (fun w => PofC_onLetter centre place entry w) (fun w => PofC_leftFirst centre place entry w)
    (fun w => stLG' τF w (stP w) (TcP w w.length))
    (fun w => arrLG' τF w (stP w) (TcP w w.length))
    (fun w => (w.length + 1) * τF) ?_ ?_ ?_ ?_
  · intro w hw
    have h := hP w hw
    exact abstractRun_throttledL'_2p18 w (stP w) (TcP w w.length) (PofC centre place entry w) q
      first 2048
      (fun j => sharedC_trunc_vm w j centre place entry (fun s => (hCP w j s).1)
        (fun s => (hCP w j s).2))
      (sharedC_suf w _ _ centre place entry)
      (by rw [h.start]; rfl) (needL'_boot w (stP w) h.start)
      (by rw [h.start]; exact sufVM_boot w) h.trace.tick
  · intro w hw
    exact hreal w hw _ _ (hP w hw)
  · exact ledger_throttledL'_2p18 (PofC centre place entry) (fun _ => q) (fun _ => first) stP TcP
      hpre (fun w hw => (hP w hw).report w.length (by omega) le_rfl)
      (fun w hw => hB_base w hw _ _ (hP w hw))
      (fun w hw => (hP w hw).cost)
  · exact GalilEmptyWord.realize_accept'_nil L blank initQ outQ n htape hn


/-- **`PAL ∈ PEG` with concrete `centre`/`place`, refined lookahead**: (B) is down to
`H_needL'` and `H_base`. -/
theorem pal_in_peg_final2' (entry q : ℕ) (first : Fin 9)
    (hA : H_oracle centreC placeC entry q first)
    (hB_need : H_needL' centreC placeC entry q first)
    (hB_base : H_base centreC placeC entry q first)
    (hC : H_realizeL' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final2'_gen centreC placeC entry q first hA centrePlaceC hB_need hB_base hC

/-! ## 6. The pointwise bound from a trailing invariant -/

/-- A head whose read-off frontier (`position + [letter] + 2·|right stack|`) is within
`2(m+1)`. -/
def FrontLe (raw : List (Fin 2)) (m : ℕ) (p : PH) : Prop :=
  GalilScaffoldInputTrace.Represents p.head raw ∧ GalilFrontMono.Sane p ∧
    position p + (if p.gap then 0 else 1) + 2 * p.head.right.length ≤ 2 * (m+1)

theorem usedPH_le_of_frontLe (raw : List (Fin 2)) (m : ℕ) (p : PH) (h : FrontLe raw m p) :
    usedPH raw.length p ≤ m+1 := by
  obtain ⟨hr, hs, hle⟩ := h
  have := GalilNeedBound.two_usedPH_of_rep raw p hr hs
  omega

/-- Two right moves from a place strictly left of `2(m+1)-1` with an empty right stack
stay within `m+1` letters (the positive-lag watch lookahead). -/
theorem usedPH_right_right_le_of_position (raw : List (Fin 2)) (p : PH) (m : ℕ)
    (hr : GalilScaffoldInputTrace.Represents p.head raw) (hs : GalilFrontMono.Sane p)
    (hrl : p.head.right = []) (hpos : position p + 1 ≤ 2 * (m+1) - 1) :
    usedPH raw.length (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right p)) ≤ m+1 := by
  have h := GalilNeedBound.two_usedPH_of_rep raw p hr hs
  rw [hrl, List.length_nil] at h
  have h2 := usedPH_right_right_le raw.length p
  split_ifs at h <;> omega

/-- **The trailing invariant** at checkpoint bound `m`: L and C within the frontier;
R on a place `≤ 2(m+1)-1` with an empty right stack; the chain verifier (if any)
represented, sane, with an empty right stack, not right of R, and strictly left of R
when a watch has positive lag. -/
structure Trail (raw : List (Fin 2)) (m : ℕ) (x : State GalilVM) : Prop where
  left : FrontLe raw m x.vm.left
  center : FrontLe raw m x.vm.center
  rightRep : GalilScaffoldInputTrace.Represents x.vm.right.head raw
  rightSane : GalilFrontMono.Sane x.vm.right
  rightStack : x.vm.right.head.right = []
  rightPos : position x.vm.right ≤ 2 * (m+1) - 1
  ver : ∀ p, verOf x.vm.chain = some p →
    GalilScaffoldInputTrace.Represents p.head raw ∧ GalilFrontMono.Sane p ∧
      p.head.right = [] ∧ position p ≤ position x.vm.right
  lagPos : ∀ w, x.vm.chain = .watch w → GalilScaffoldCounter.positive w.lag = true →
    position w.machine.verifier + 1 ≤ position x.vm.right

/-- The positive-lag clause follows from the arithmetic trailing relation
`position verifier + lag = position R` on a canonical lag counter. -/
theorem lagPos_of_value (w : WS) (r : ℕ) (hc : GalilScaffoldCounter.Canonical w.lag)
    (h : (position w.machine.verifier : ℤ) + GalilScaffoldCounter.value w.lag = r)
    (hp : GalilScaffoldCounter.positive w.lag = true) : position w.machine.verifier + 1 ≤ r := by
  have := (GalilScaffoldCounter.positive_iff w.lag hc).mp hp
  omega

theorem usedChain_le_of_trail (raw : List (Fin 2)) (m : ℕ) (x : State GalilVM) (ht : Trail raw m x) :
    usedChain raw.length x.vm.chain ≤ m+1 := by
  unfold usedChain
  cases hv : verOf x.vm.chain with
  | none => exact Nat.zero_le _
  | some p =>
    obtain ⟨hr, hs, hrl, hpos⟩ := ht.ver p hv
    exact GalilNeedBound.usedPH_le_of_position raw p m hr hs hrl (le_trans hpos ht.rightPos)

theorem lookChain'_le_of_trail (raw : List (Fin 2)) (m : ℕ) (x : State GalilVM) (ht : Trail raw m x) :
    lookChain' raw.length x.vm.chain ≤ m+1 := by
  have hver := ht.ver
  have hlag := ht.lagPos
  have hR := ht.rightPos
  cases hx : x.vm.chain with
  | idle => exact Nat.zero_le _
  | copy t h p v lag margin ver =>
    rw [hx] at hver
    obtain ⟨hr, hs, hrl, hpos⟩ := hver ver rfl
    exact GalilNeedBound.usedPH_le_of_position raw ver m hr hs hrl (le_trans hpos hR)
  | back v h lag margin ver =>
    rw [hx] at hver
    obtain ⟨hr, hs, hrl, hpos⟩ := hver ver rfl
    exact GalilNeedBound.usedPH_right_le_of_position raw ver m hr hs hrl (le_trans hpos hR)
  | watch w =>
    rw [hx] at hver
    obtain ⟨hr, hs, hrl, hpos⟩ := hver w.machine.verifier rfl
    simp only [lookChain']
    split_ifs with hp
    · exact usedPH_right_right_le_of_position raw _ m hr hs hrl
        (le_trans (hlag w hx hp) hR)
    · exact GalilNeedBound.usedPH_right_le_of_position raw _ m hr hs hrl (le_trans hpos hR)
  | broken w =>
    rw [hx] at hver
    obtain ⟨hr, hs, hrl, hpos⟩ := hver w.machine.verifier rfl
    exact GalilNeedBound.usedPH_le_of_position raw _ m hr hs hrl (le_trans hpos hR)

/-- **The pointwise refined need bound under the trailing invariant.** -/
theorem needL'_le_of_trail (raw : List (Fin 2)) (st : ℕ → State GalilVM) (m i : ℕ)
    (ht : Trail raw m (st i)) : needL' raw st i ≤ m+1 := by
  have hL := usedPH_le_of_frontLe raw m _ ht.left
  have hC := usedPH_le_of_frontLe raw m _ ht.center
  have hR := GalilNeedBound.usedPH_le_of_position raw _ m ht.rightRep ht.rightSane ht.rightStack
    ht.rightPos
  have hR' := GalilNeedBound.usedPH_right_le_of_position raw _ m ht.rightRep ht.rightSane
    ht.rightStack ht.rightPos
  have hch := usedChain_le_of_trail raw m (st i) ht
  have hlc := lookChain'_le_of_trail raw m (st i) ht
  unfold needL' needS usedVM look'
  split_ifs <;> omega

/-- (B'') The trailing invariant along every pre-loaded trace, up to each checkpoint. -/
def H_trail (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → Trail w m (st i)

theorem needL'_of_trail (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (h : H_trail centre place entry q first) :
    H_needL' centre place entry q first :=
  fun w hw st Tc hP m hm i hi => needL'_le_of_trail w st m i (h w hw st Tc hP m hm i hi)

/-- **`PAL ∈ PEG`, refined lookahead, need bound reduced to the trailing invariant.** -/
theorem pal_in_peg_final2'_trail (entry q : ℕ) (first : Fin 9)
    (hA : H_oracle centreC placeC entry q first)
    (hB_trail : H_trail centreC placeC entry q first)
    (hB_base : H_base centreC placeC entry q first)
    (hC : H_realizeL' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final2' entry q first hA (needL'_of_trail _ _ entry q first hB_trail) hB_base hC

#print axioms lookChain'_le
#print axioms chainTick_used'
#print axioms tick_trunc'
#print axioms needL'_le_needL
#print axioms needLe_of_pointwise'
#print axioms abstractRun_throttledLG'
#print axioms ledger_throttledLG'
#print axioms abstractRun_throttledL'_2p18
#print axioms ledger_throttledL'_2p18
#print axioms needL'_boot
#print axioms pal_in_peg_final2'_gen
#print axioms pal_in_peg_final2'
#print axioms usedPH_right_right_le_of_position
#print axioms lagPos_of_value
#print axioms lookChain'_le_of_trail
#print axioms needL'_le_of_trail
#print axioms needL'_of_trail
#print axioms pal_in_peg_final2'_trail

end PalPeg.GalilLookRefined
