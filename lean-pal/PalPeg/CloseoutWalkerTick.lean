import PalPeg.CloseoutPackRun28
import PalPeg.CloseoutWinTick

/-!
# `WalkerInv` one tick, with `Fair` replaced by the walker pin

`CloseoutPackRun28.walkerInv_tick` uses its `Fair` hypothesis at **one** place —
the `init` branch, where it reads `Fair.keepsSearchCursor` to get
`t.walker = s.walker`.  That clause is

```
keepsSearchCursor : x.ctl.mode = Mode.init ∨ x.ctl.mode = Mode.replayStart →
  y.vm.periodOnly = x.vm.periodOnly ∧ y.vm.walker = x.vm.walker
```

so what the proof actually needs is the walker half at an `init` /
`replayStart` source.  Taking that directly removes the `Fair` hypothesis, in
the same way `CloseoutWinTick.windowInOrigin_tick_pin` removed it from the
`WindowInOrigin` tick (there it was `Fair.fallbackPlace`).

Together the two make the whole `WindowInOrigin` / `WalkerInOrigin` chain
`Fair`-free, which is what `CloseoutPackRun17.marks_steps`' `hwin` input needs.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWalkerTick

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldCounter
open PalPeg.CloseoutPackRun25 (WalkerInOrigin FairSteps)
open PalPeg.GalilTickFair (Fair)
open PalPeg.CloseoutPackRun28

section
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

theorem walkerInv_tick_pin
    (hplace : ∀ u, (GalilScaffoldPlace.stream (place u)).length ≤ position u.right)
    (hdelay : 2 ≤ delay) {c c' : Control} {s t : GalilVM}
    (hcan : c.replaying = true → GalilScaffoldChainVerifier.canRight s.right)
    (hkeep : c.mode = Mode.init ∨ c.mode = Mode.replayStart → t.walker = s.walker)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩)
    (hI : WalkerInv c s) : WalkerInv c' t := by
  cases h
  case init =>
    rename_i hm hi
    have hi' : initVM entry s t := hi
    have hw : t.walker = s.walker := hkeep (Or.inl hm)
    rcases hI with ⟨-, h0⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · refine Or.inr (Or.inl ⟨by simp, ?_⟩)
      unfold PalPeg.CloseoutPackRun28.Bounded
      rw [hw, h0]
      simp
    · exact absurd hm h1
    · rw [hm] at h1; cases h1
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, hr, hch, -, -, -, -, -, -, -, -, hse⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    refine walkerInv_scan onLetter leftFirst centre place entry hplace hm hm hse (by rw [hr])
      ?_ hI
    intro hidle hg
    left
    rcases hch with ⟨hne, -⟩ | ⟨-, -, hz⟩ | ⟨-, hfd, -⟩
    · exact absurd hidle hne
    · exact hz
    · have : (searchLens.get t).search.mode = .grow := hg
      rw [this] at hfd; cases hfd
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, hr, hch, -, -, -, -, -, -, -, -, hse⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    refine walkerInv_scan onLetter leftFirst centre place entry hplace hm hm hse (by rw [hr])
      ?_ hI
    intro hidle hg
    left
    rcases hch with ⟨hne, -⟩ | ⟨-, -, hz⟩ | ⟨-, hfd, -⟩
    · exact absurd hidle hne
    · exact hz
    · have : (searchLens.get t).search.mode = .grow := hg
      rw [this] at hfd; cases hfd
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨hs'r, a, hse⟩ := compareFound_fields onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have htw : searchLens.get t = searchLens.get s' := by rw [hpl']; split <;> rfl
    have htr : t.right = s'.right := by rw [hpl']; split <;> rfl
    have htc : t.chain = s'.chain := by rw [hpl']; split <;> rfl
    have hcr : GalilScaffoldChainVerifier.canRight s.right := by
      rcases hav with hrep | hav
      · exact hcan hrep
      · exact hav
    rw [← htw] at hse
    refine walkerInv_scan onLetter leftFirst centre place entry hplace hm hm hse ?_ ?_ hI
    · rw [htr, hs'r]; exact position_le_right s.right hcr
    · intro _ _; right; omega
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨hs'r, a, hse⟩ := compareFound_fields onLetter leftFirst centre place entry q first hcmp
    obtain ⟨w, -, ht⟩ : beginShiftVM' s' t := hb
    have htw : searchLens.get t = searchLens.get s' := by rw [ht]; rfl
    have htr : t.right = s'.right := by rw [ht]
    have hcr : GalilScaffoldChainVerifier.canRight s.right := by
      rcases hav with hrep | hav
      · rw [hr] at hrep; cases hrep
      · exact hav
    rw [← htw] at hse
    rcases hI with ⟨h1, -⟩ | ⟨-, hb'⟩ | ⟨-, hidle, hgrow, hwork⟩
    · rw [hm] at h1; cases h1
    · refine Or.inr (Or.inl ⟨by simp, ?_⟩)
      have hw := searchEffect_walker _ hse
      have hP : (sharedC onLetter leftFirst centre place entry).place s = place s := rfl
      rw [hP] at hw
      exact bounded_step place hplace hw (by rw [htr, hs'r]; exact position_le_right s.right hcr) hb'
    · rcases searchEffect_fresh _ hse hidle hgrow with ⟨hp, -, -, -⟩ | ⟨-, hw⟩
      · rcases hwork with ⟨-, hclk⟩ | hw2
        · omega
        · rw [hw2] at hp; cases hp
      · refine Or.inr (Or.inl ⟨by simp, ?_⟩)
        unfold PalPeg.CloseoutPackRun28.Bounded
        have hw' : t.walker = place s := hw
        rw [hw', htr, hs'r]
        have := hplace s
        have := position_le_right s.right hcr
        omega
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨hs'r, a, hse⟩ := compareFound_fields onLetter leftFirst centre place entry q first hcmp
    obtain ⟨pl, ht, -⟩ : beginFallbackVM' s' t := hb
    unfold GalilScaffoldChainInputSupply.beginFallbackVM at ht
    have htw : t.walker = s'.walker := by rw [ht]
    have htr : t.right = s'.right := by rw [ht]
    have hcr : GalilScaffoldChainVerifier.canRight s.right := by
      rcases hav with hrep | hav
      · rw [hr] at hrep; cases hrep
      · exact hav
    have hpos : position s.right ≤ position t.right := by
      rw [htr, hs'r]; exact position_le_right s.right hcr
    rcases hI with ⟨h1, -⟩ | ⟨-, hb'⟩ | ⟨-, hidle, hgrow, hwork⟩
    · rw [hm] at h1; cases h1
    · refine Or.inr (Or.inl ⟨by simp, ?_⟩)
      have hw := searchEffect_walker _ hse
      have hP : (sharedC onLetter leftFirst centre place entry).place s = place s := rfl
      rw [hP] at hw
      have hw' : t.walker = s.walker ∨ t.walker = GalilScaffoldPlace.left s.walker ∨
          t.walker = place s := by rw [htw]; exact hw
      exact bounded_step place hplace hw' hpos hb'
    · rcases searchEffect_fresh _ hse hidle hgrow with ⟨hp, -, -, -⟩ | ⟨-, hw⟩
      · rcases hwork with ⟨-, hclk⟩ | hw2
        · omega
        · rw [hw2] at hp; cases hp
      · refine Or.inr (Or.inl ⟨by simp, ?_⟩)
        unfold PalPeg.CloseoutPackRun28.Bounded
        have hw' : s'.walker = place s := hw
        rw [htw, hw']
        have := hplace s
        omega
  case shift_one =>
    rename_i hm hp hi
    exact walkerInv_pull shiftLens hi.2 rfl rfl (by rw [hm]; simp) (by rw [hm]; simp)
      (by rw [hm]; simp) hI
  case shift_done =>
    rename_i hm hp ho
    exact walkerInv_keep rfl rfl (by rw [hm]; simp) (by rw [hm]; simp) (by simp) hI
  case copy_one =>
    rename_i hm hp hi
    exact walkerInv_pull fppLens hi.2 rfl rfl (by rw [hm]; simp) (by rw [hm]; simp)
      (by rw [hm]; simp) hI
  case copy_done =>
    rename_i hm hp hi
    exact walkerInv_pull fppLens hi.2 rfl rfl (by rw [hm]; simp) (by rw [hm]; simp) (by simp) hI
  case home_start =>
    rename_i hm hl hi
    exact walkerInv_pull fppLens hi.2 rfl rfl (by rw [hm]; simp) (by rw [hm]; simp) (by simp) hI
  case home_step =>
    rename_i hm hl hi
    exact walkerInv_pull fppLens hi.2 rfl rfl (by rw [hm]; simp) (by rw [hm]; simp)
      (by rw [hm]; simp) hI
  case fpp_slice =>
    rename_i hm hi
    exact walkerInv_pull fppLens hi.2 rfl rfl (by rw [hm]; simp) (by rw [hm]; simp)
      (by rw [hm]; simp) hI
  case fpp_done =>
    rename_i hm hi
    exact walkerInv_pull fppLens hi.2 rfl rfl (by rw [hm]; simp) (by rw [hm]; simp) (by simp) hI
  case markEnd_found =>
    rename_i hm he hi
    exact walkerInv_pull rewindLens hi.2 rfl (by rw [hi.1.2]; rfl) (by rw [hm]; simp)
      (by rw [hm]; simp) (by simp) hI
  case markEnd_step =>
    rename_i hm he hi
    exact walkerInv_pull fppLens hi.2 rfl rfl (by rw [hm]; simp) (by rw [hm]; simp)
      (by rw [hm]; simp) hI
  case choose_select =>
    rename_i hm hodd hs hi
    exact walkerInv_pull rewindLens hi.2 rfl (by rw [hi.1]; rfl) (by rw [hm]; simp)
      (by rw [hm]; simp) (by simp) hI
  case choose_step =>
    rename_i hm hs hi
    exact walkerInv_pull rewindLens hi.2 rfl (by rw [hi.1.2]; rfl) (by rw [hm]; simp)
      (by rw [hm]; simp) (by rw [hm]; simp) hI
  case rewind_done =>
    rename_i hm hfi hi
    exact walkerInv_pull rewindLens hi.2 rfl (by rw [hi.1]; rfl) (by rw [hm]; simp)
      (by rw [hm]; simp) (by simp) hI
  case rewind_one =>
    rename_i hm hpr hfi hi
    exact walkerInv_pull rewindLens hi.2 rfl (by rw [hi.1.2]; rfl) (by rw [hm]; simp)
      (by rw [hm]; simp) (by rw [hm]; simp) hI
  case rewind_pair =>
    rename_i hm hpr hfi hi
    exact walkerInv_pull rewindLens hi.2 rfl (by rw [hi.1.2]; rfl) (by rw [hm]; simp)
      (by rw [hm]; simp) (by rw [hm]; simp) hI
  case replayStart =>
    rename_i o hm ho ho' hi
    have hi' : replayStartVM entry s t := hi
    refine Or.inr (Or.inr ⟨by simp, hi'.2.2.2.2.2.2.2.2.2.1, ?_, Or.inl ⟨?_, ?_⟩⟩)
    · rw [hi'.2.2.2.2.2.2.2.2.2.2.1]; exact begin_reset_mode
    · rw [hi'.2.2.2.2.2.2.2.2.2.2.1]; exact begin_reset_work
    · show 2 ≤ delay; exact hdelay
  case restart =>
    rename_i hm hb
    obtain ⟨w, hbr, -, -, -, ht⟩ : restartVM entry s t := hb
    rcases hI with ⟨h1, -⟩ | ⟨-, hb'⟩ | ⟨-, hidle, -, -⟩
    · rw [hm] at h1; cases h1
    · refine Or.inr (Or.inl ⟨by rw [hm]; simp, ?_⟩)
      unfold PalPeg.CloseoutPackRun28.Bounded at *
      rw [ht]; exact hb'
    · rw [hidle] at hbr; cases hbr


#print axioms walkerInv_tick_pin

end

end PalPeg.CloseoutWalkerTick
