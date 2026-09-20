import PalPeg.GalilLookRefined
import PalPeg.GalilRunSkeleton

/-!
# The letters used by the target of a tick

A truncated tick is legitimate when the letters used by its source and by its target, and the
lookahead of its source, have arrived (`GalilLookRefined.tick_trunc'`).  The starvation test of
the local layer reads the source only, so the letters used by the target have to be bounded by
the source.  Here: a background tick keeps the three heads, and its chain either ticks (within
its refined lookahead, `chainTick_used'`), stays idle, or is born on the centre head.
-/

set_option autoImplicit false

namespace PalPeg.TickUsedLetters

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilThrottledRun (usedPH usedChain usedVM)
open PalPeg.GalilTruncTick (usedVM_left usedVM_center usedVM_right)
open PalPeg.GalilLookRefined (lookChain' chainTick_used')

/-- **The letters used after a background tick**: those used before, or the refined lookahead of
the chain. -/
theorem usedVM_background_le (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    {s s' : GalilVM} (hbackground : (galilFrameS P q first).background s s') :
    usedVM raw s' ≤ max (usedVM raw s) (lookChain' raw.length s.chain) := by
  obtain ⟨hleft, hright, hchain, hcenter, -⟩ := backgroundS_fields P q first hbackground
  have hchainBound : usedChain raw.length s'.chain
      ≤ max (usedVM raw s) (lookChain' raw.length s.chain) := by
    rcases hchain with ⟨_, htick⟩ | ⟨_, _, hidle⟩ | ⟨_, _, hborn⟩
    · exact le_trans (chainTick_used' raw.length htick) (le_max_right _ _)
    · rw [hidle]
      exact Nat.zero_le _
    · simp only [Bool.false_eq_true, if_false] at hborn
      rw [hborn]
      exact le_trans (usedVM_center raw s) (le_max_left _ _)
  have hl := usedVM_left raw s
  have hc := usedVM_center raw s
  have hr := usedVM_right raw s
  show max (max (usedPH raw.length s'.left) (usedPH raw.length s'.center))
      (max (usedPH raw.length s'.right) (usedChain raw.length s'.chain)) ≤ _
  rw [hleft, hcenter, hright]
  omega

#print axioms usedVM_background_le

/-- **The letters used after the `init` effect**: the three heads stand on the place right of the
right head and the chain is idle, so they are the letters used by that move. -/
theorem usedVM_init_le (raw : List (Fin 2)) {entry : ℕ} {s t : GalilVM}
    (hinit : initVM entry s t) :
    usedVM raw t ≤ usedPH raw.length (GalilScaffoldChainVerifier.right s.right) := by
  obtain ⟨hright, hleft, hcenter, -, -, -, -, -, -, hchain, -⟩ := hinit
  show max (max (usedPH raw.length t.left) (usedPH raw.length t.center))
      (max (usedPH raw.length t.right) (usedChain raw.length t.chain)) ≤ _
  rw [hleft, hcenter, hright, hchain]
  simp [usedChain, PalPeg.GalilThrottledRun.verOf]

/-- **The letters used after the `replayStart` effect**: the three heads stand on the centre head
and the chain is idle, so no new letter is used. -/
theorem usedVM_replayStart_le (raw : List (Fin 2)) {entry : ℕ} {s t : GalilVM}
    (hreplayStart : replayStartVM entry s t) : usedVM raw t ≤ usedVM raw s := by
  obtain ⟨-, hright, hleft, hcenter, -, -, -, -, -, hchain, -⟩ := hreplayStart
  have hcenterUsed := usedVM_center raw s
  show max (max (usedPH raw.length t.left) (usedPH raw.length t.center))
      (max (usedPH raw.length t.right) (usedChain raw.length t.chain)) ≤ _
  rw [hleft, hcenter, hright, hchain]
  simp only [usedChain, PalPeg.GalilThrottledRun.verOf]
  omega

#print axioms usedVM_replayStart_le

/-- **The letters used after a comparison**: the left head moves left (no letter), the right head
moves right, the centre stays, and the chain ticks within its refined lookahead, stays idle, or
is born on the centre head (a matched step does not move the verifier of a copying chain). -/
theorem usedVM_compare_le (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    {s t : GalilVM} (hcompare : compareFound P q first s t) :
    usedVM raw t ≤ max (max (usedVM raw s)
      (usedPH raw.length (GalilScaffoldChainVerifier.right s.right)))
      (lookChain' raw.length s.chain) := by
  obtain ⟨vs, vq, a, hleft, hright, -, -, hchain, ht⟩ := hcompare
  have hfields : t.left = vs.left ∧ t.center = s.center ∧ t.right = vs.right ∧
      t.chain = vs.chain := by
    subst ht
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [afterBirth_left]; cases a <;> rfl
    · rw [afterBirth_center]; cases a <;> rfl
    · rw [afterBirth_right]; cases a <;> rfl
    · rw [afterBirth_chain]; cases a <;> rfl
  obtain ⟨htl, htc, htr, htchain⟩ := hfields
  have hcenterUsed := usedVM_center raw s
  have hleftUsed := usedVM_left raw s
  have hchainBound : usedChain raw.length vs.chain
      ≤ max (usedVM raw s) (lookChain' raw.length s.chain) := by
    rcases hchain with ⟨_, htick⟩ | ⟨_, _, hidle⟩ | ⟨_, _, hborn⟩
    · exact le_trans (chainTick_used' raw.length htick) (le_max_right _ _)
    · rw [hidle]
      exact Nat.zero_le _
    · have hverifier : usedChain raw.length vs.chain = usedPH raw.length s.center := by
        cases a
        · simp only [Bool.false_eq_true, if_false] at hborn
          rw [hborn]
          rfl
        · simp only [if_true] at hborn
          generalize vs.chain = born at hborn ⊢
          unfold chainStart at hborn
          cases hborn
          rfl
      rw [hverifier]
      exact le_trans hcenterUsed (le_max_left _ _)
  show max (max (usedPH raw.length t.left) (usedPH raw.length t.center))
      (max (usedPH raw.length t.right) (usedChain raw.length t.chain)) ≤ _
  rw [htl, htc, htr, htchain, hleft, hright, PalPeg.GalilTruncTick.usedPH_left]
  omega

#print axioms usedVM_compare_le

/-- **The letters used after the fallback entry**: the heads stay and the chain becomes idle. -/
theorem usedVM_beginFallback_le (raw : List (Fin 2)) {s t : GalilVM}
    (hfallback : beginFallbackVM' s t) : usedVM raw t ≤ usedVM raw s := by
  obtain ⟨place, hplace, -⟩ := hfallback
  have hl := usedVM_left raw s
  have hc := usedVM_center raw s
  have hr := usedVM_right raw s
  rw [hplace]
  show max (max (usedPH raw.length s.left) (usedPH raw.length s.center))
      (max (usedPH raw.length s.right) (usedChain raw.length ChainVM.idle)) ≤ _
  simp only [usedChain, PalPeg.GalilThrottledRun.verOf]
  omega

/-- **The letters used after a restart**: the heads stay and the chain becomes idle. -/
theorem usedVM_restart_le (raw : List (Fin 2)) {entry : ℕ} {s t : GalilVM}
    (hrestart : restartVM entry s t) : usedVM raw t ≤ usedVM raw s := by
  obtain ⟨broken, -, -, -, -, ht⟩ := hrestart
  have hl := usedVM_left raw s
  have hc := usedVM_center raw s
  have hr := usedVM_right raw s
  rw [ht]
  show max (max (usedPH raw.length s.left) (usedPH raw.length s.center))
      (max (usedPH raw.length s.right) (usedChain raw.length ChainVM.idle)) ≤ _
  simp only [usedChain, PalPeg.GalilThrottledRun.verOf]
  omega

#print axioms usedVM_restart_le

/-- **The letters used by the target of a scan tick that does not enter `shift`.**  By cases on
the tick: a background tick, a comparison (with the matched place, which only touches `replay`),
a comparison followed by the fallback entry, or a restart.  The shift entry moves the chain
verifier once more and is not covered. -/
theorem usedVM_scanTick_le (raw : List (Fin 2)) {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q delay : ℕ} {first : Fin 9}
    {word : List (Fin 2)} {c : PalPeg.GalilScaffoldController.Control} {s : GalilVM}
    {y : State GalilVM} (hmode : c.mode = .scan)
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centre place entry word) q first)
      delay ⟨c, s⟩ y)
    (hnotShift : y.ctl.mode ≠ .shift) :
    usedVM raw y.vm ≤ max (max (usedVM raw s)
      (usedPH raw.length (GalilScaffoldChainVerifier.right s.right)))
      (lookChain' raw.length s.chain) := by
  have hplaceKeeps : ∀ compared placed : GalilVM,
      (galilFrameS (PalPeg.GalilRunSkeleton.PofC centre place entry word) q
        first).matchedPlace c.replaying compared placed →
      usedVM raw placed = usedVM raw compared := by
    intro compared placed hplace
    have hplaced : placed = (if c.replaying then
        { compared with replay := GalilScaffoldCounter.dec compared.replay } else compared) :=
      hplace
    rw [hplaced]
    split <;> rfl
  cases htick
  case scan_wait =>
    exact (usedVM_background_le raw _ q first (by assumption)).trans
      (max_le (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _))
  case scan_count =>
    exact (usedVM_background_le raw _ q first (by assumption)).trans
      (max_le (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _))
  case scan_match =>
    exact (le_of_eq (hplaceKeeps _ _ (by assumption))).trans
      (usedVM_compare_le raw _ q first (by assumption))
  case scan_shift => exact absurd rfl hnotShift
  case scan_fallback =>
    exact (usedVM_beginFallback_le raw (by assumption)).trans
      (usedVM_compare_le raw _ q first (by assumption))
  case restart =>
    exact (usedVM_restart_le raw (by assumption)).trans
      (le_trans (le_max_left _ _) (le_max_left _ _))
  all_goals (exfalso; simp_all)

#print axioms usedVM_scanTick_le

/-- **The letters used after the moving tick of a shift**: the centre head has moved one place,
the left head two, and the chain keeps its verifier. -/
theorem usedVM_shiftOne_le (raw : List (Fin 2)) {P : Shared} {q : ℕ} {first : Fin 9}
    {s s' : GalilVM} (hshiftOne : (galilFrameS P q first).shiftOne s s') :
    usedVM raw s' ≤ max (usedVM raw s)
      (max (usedPH raw.length (GalilScaffoldChainVerifier.right s.center))
        (usedPH raw.length (GalilScaffoldChainVerifier.right
          (GalilScaffoldChainVerifier.right s.left)))) := by
  obtain ⟨⟨-, -, -, watching, hwatching, htarget⟩, hset⟩ := hshiftOne
  have hs' := hset.trans (congrArg _ htarget)
  have hchain : usedChain raw.length s.chain ≤ usedVM raw s :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  rw [show s.chain = .watch watching from hwatching] at hchain
  rw [hs']
  exact max_le (max_le (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_trans (le_max_left _ _) (le_max_right _ _)))
    (max_le (le_trans (usedVM_right raw s) (le_max_left _ _)) (le_trans hchain (le_max_left _ _)))

/-- An effect through the fallback-program lens keeps the three heads and the chain. -/
theorem usedVM_fppRel (raw : List (Fin 2)) {R : FppControl.State → FppControl.State → Prop}
    {s t : GalilVM} (hrel : fppLens.rel R s t) : usedVM raw t = usedVM raw s := by
  rw [hrel.2]
  rfl

/-- An effect through the rewind lens keeps the chain, so the letters used by its target are
bounded as soon as those used by its three heads are. -/
theorem usedVM_rewindRel_le (raw : List (Fin 2)) {R : RewindVM → RewindVM → Prop} {s t : GalilVM}
    (hrel : rewindLens.rel R s t)
    (hleft : usedPH raw.length (rewindLens.get t).left ≤ usedVM raw s)
    (hcenter : usedPH raw.length (rewindLens.get t).center ≤ usedVM raw s)
    (hright : usedPH raw.length (rewindLens.get t).right ≤ usedVM raw s) :
    usedVM raw t ≤ usedVM raw s := by
  rw [hrel.2]
  exact max_le (max_le hleft hcenter)
    (max_le hright (le_trans (le_max_right _ _) (le_max_right _ _)))

/-- **The letters used by the target of a tick outside `init`, `scan` and `replayStart`.**  The
moving tick of a shift moves the centre head one place and the left head two
(`usedVM_shiftOne_le`); every other such tick uses no new letter: the fallback program does not
touch the heads, marking keeps them, `choose` puts the left and the centre head on the right
head, and rewinding moves the left and the centre head to the left.  The ticks left out are
`usedVM_init_le`, `usedVM_scanTick_le` and `usedVM_replayStart_le`. -/
theorem usedVM_phaseTick_le (raw : List (Fin 2)) {P : Shared} {q delay : ℕ} {first : Fin 9}
    {x y : State GalilVM} (htick : Tick (galilFrameS P q first) delay x y)
    (hnotInit : x.ctl.mode ≠ .init) (hnotScan : x.ctl.mode ≠ .scan)
    (hnotReplayStart : x.ctl.mode ≠ .replayStart) :
    usedVM raw y.vm ≤ max (usedVM raw x.vm)
      (max (usedPH raw.length (GalilScaffoldChainVerifier.right x.vm.center))
        (usedPH raw.length (GalilScaffoldChainVerifier.right
          (GalilScaffoldChainVerifier.right x.vm.left)))) := by
  cases htick with
  | init c s s' hm h0 => exact absurd hm hnotInit
  | scan_wait c s s' hm h0 hb => exact absurd hm hnotScan
  | scan_count c s s' hm h0 hc hb => exact absurd hm hnotScan
  | scan_match c s s' s'' o hm h0 hc hcmp hmt hpl ho => exact absurd hm hnotScan
  | scan_shift c s s' s'' hm h0 hc hcmp hmt hr hg hb => exact absurd hm hnotScan
  | scan_fallback c s s' s'' hm h0 hc hcmp hmt hg hr hb => exact absurd hm hnotScan
  | shift_one c s s' hm hp h0 => exact usedVM_shiftOne_le raw h0
  | shift_done c s o hm hp ho => exact le_max_left _ _
  | copy_one c s s' hm hp h0 => exact le_trans (le_of_eq (usedVM_fppRel raw h0)) (le_max_left _ _)
  | copy_done c s s' hm hp h0 => exact le_trans (le_of_eq (usedVM_fppRel raw h0)) (le_max_left _ _)
  | home_start c s s' hm hl h0 => exact le_trans (le_of_eq (usedVM_fppRel raw h0)) (le_max_left _ _)
  | home_step c s s' hm hl h0 => exact le_trans (le_of_eq (usedVM_fppRel raw h0)) (le_max_left _ _)
  | fpp_slice c s s' hm h0 => exact le_trans (le_of_eq (usedVM_fppRel raw h0)) (le_max_left _ _)
  | fpp_done c s s' hm h0 => exact le_trans (le_of_eq (usedVM_fppRel raw h0)) (le_max_left _ _)
  | markEnd_found c s s' hm he h0 =>
    obtain ⟨-, htarget⟩ := h0.1
    refine le_trans (usedVM_rewindRel_le raw h0 ?_ ?_ ?_) (le_max_left _ _) <;> rw [htarget]
    · exact usedVM_left raw s
    · exact usedVM_center raw s
    · exact usedVM_right raw s
  | markEnd_step c s s' hm he h0 => exact le_trans (le_of_eq (usedVM_fppRel raw h0)) (le_max_left _ _)
  | choose_select c s s' hm ho hs h0 =>
    have htarget := h0.1
    refine le_trans (usedVM_rewindRel_le raw h0 ?_ ?_ ?_) (le_max_left _ _) <;> rw [htarget]
    · exact usedVM_right raw s
    · exact usedVM_right raw s
    · exact usedVM_right raw s
  | choose_step c s s' hm hs h0 =>
    obtain ⟨-, htarget⟩ := h0.1
    refine le_trans (usedVM_rewindRel_le raw h0 ?_ ?_ ?_) (le_max_left _ _) <;> rw [htarget]
    · exact usedVM_left raw s
    · exact usedVM_center raw s
    · exact usedVM_right raw s
  | rewind_done c s s' hm hf h0 =>
    have htarget := h0.1
    refine le_trans (usedVM_rewindRel_le raw h0 ?_ ?_ ?_) (le_max_left _ _) <;> rw [htarget]
    · exact usedVM_left raw s
    · exact usedVM_center raw s
    · exact usedVM_right raw s
  | rewind_one c s s' hm hf hp h0 =>
    obtain ⟨-, htarget⟩ := h0.1
    refine le_trans (usedVM_rewindRel_le raw h0 ?_ ?_ ?_) (le_max_left _ _) <;> rw [htarget]
    · exact (le_of_eq (PalPeg.GalilTruncTick.usedPH_left _ _)).trans (usedVM_left raw s)
    · exact usedVM_center raw s
    · exact usedVM_right raw s
  | rewind_pair c s s' hm hf hp h0 =>
    obtain ⟨-, htarget⟩ := h0.1
    refine le_trans (usedVM_rewindRel_le raw h0 ?_ ?_ ?_) (le_max_left _ _) <;> rw [htarget]
    · exact (le_of_eq (PalPeg.GalilTruncTick.usedPH_left _ _)).trans (usedVM_left raw s)
    · exact (le_of_eq (PalPeg.GalilTruncTick.usedPH_left _ _)).trans (usedVM_center raw s)
    · exact usedVM_right raw s
  | replayStart c s s' o hm h0 ho ho' => exact absurd hm hnotReplayStart
  | restart c s s' hm hb => exact absurd hm hnotScan

#print axioms usedVM_phaseTick_le

end PalPeg.TickUsedLetters
