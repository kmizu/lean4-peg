import PalPeg.LocalSysConcrete

/-!
# 局所化計画, piece 10: the phase-mode obligations of `LocalSysConcrete`

`PalPeg.LocalSysConcrete.localSys_oracles` leaves ten `Realizes` obligations
open, one per control mode.  This file discharges the five *phase* modes
`shift`, `copy`, `home`, `fpp`, `markEnd` — it supplies the `Steps` fields and
proves `Realizes raw stOf lastTick · md` for them.

## The shape of the argument

`Realizes` asks that the local step land on the trace's *next* abstract state.
The local layer only knows how to produce **some** scaffold tick
(`LocalTick3.tickL3_abs`), so the two are glued by **determinism of `Tick`
inside one mode**:

1. `LocalSysConcrete.tick_of_need` turns the trace tick `stOf k → stOf (k+1)`
   into a tick out of `absState'' m.vm` (`Needy`);
2. the local step is shown to be a `TickL3`, hence a tick out of the *same*
   state (`tickL3_abs`);
3. in each of the five modes the successor of a tick is unique
   (`tick_*_unique`, from the fact that every frame field the phase
   constructors consult is a functional relation — `lens_rel_unique` plus
   `control_run_unique` for the fpp quantum), so the two successors agree.

Step 2 is where the side conditions live.  Everything the *trace* tick already
knows (the mode guards `remainingPos`/`atLeft`/`atEnd`, the non-empty MARKS and
SOURCE windows, the copy letter, the watched chain) is **read off the trace
tick**, which `realizes_of_mode` hands to the step obligation.  What is left
over is genuinely physical — polarity bits and tape positivity that
`LocalSysConcrete.InvC` does not carry — and is kept as a *named* hypothesis,
one per mode.

## What is closed and what is not

| mode | step | residual hypotheses |
|---|---|---|
| `home` | `homeStepL` | `hnr` (`replaying = false`) |
| `markEnd` | `markEndStepL` | `hnr` |
| `copy` | `copyStepL` | `hnr`, `H_copy` (sign bit and positivity of `fppWork`, `ProperView` of the walker) |
| `shift` | `shiftStepL` | `hnr`, `H_shift` (`ShiftCounters`) |
| `fpp` | a parameter `ffpp` | `hnr`, `H_fpp` (the local fpp quantum realizes `TickL3`) |

`hnr` is the control-flow invariant "a phase mode never replays"; it is a
property of the *trace*, not of the local state, so it cannot be proved here.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

namespace PalPeg.LocalRealizesPhase

variable {lastTick : ℕ}

open PalPeg.GalilScaffoldTop
open PalPeg.GalilScaffoldController (Control Mode)
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.LocalState
open PalPeg.LocalInputView (InputView)
open PalPeg.LocalArrival (abs' absState' Ahead absHead')
open PalPeg.LocalReplayParked (abs'' absState'' abs''_eq_abs' Mirrored1 MirInv1)
open PalPeg.LocalSysConcrete (PhysWF InvC Needy Tracked Starved Realizes
  tick_of_need physWF_of_tickL3)
open PalPeg.LocalTick3 (TickL3 shiftVm copyVm copyDoneVm homeStartVm homeStepVm marksVm
  ShiftCounters tickL3_abs)
open PalPeg.GalilTickFun3 (marksOf sourceOf ShiftRemaining CopyRemaining)
open PalPeg.GalilThrottledRun (truncS)
open PalPeg.GalilLookRefined (needT')

variable {P : ℕ}

/-! ## 1. Every frame field a phase tick consults is functional -/

theorem lens_rel_unique {σ σ' : Type} {L : Lens σ σ'} {R : σ' → σ' → Prop}
    (hR : ∀ {a b c : σ'}, R a b → R a c → b = c) {s t₁ t₂ : σ}
    (h₁ : L.rel R s t₁) (h₂ : L.rel R s t₂) : t₁ = t₂ :=
  h₁.2.trans (by rw [hR h₁.1 h₂.1]; exact h₂.2.symm)

section Fields

variable (Pw : Shared) (qq : ℕ) (first : Fin 9)

theorem shiftOne_unique {s t₁ t₂ : GalilVM}
    (h₁ : (galilFrameS Pw qq first).shiftOne s t₁)
    (h₂ : (galilFrameS Pw qq first).shiftOne s t₂) : t₁ = t₂ := by
  refine lens_rel_unique (L := shiftLens)
    (R := (shiftFrame (fun _ => True) (fun _ => True)).shiftOne) ?_ h₁ h₂
  intro a b c hb hc
  obtain ⟨-, -, -, w₁, hw₁, he₁⟩ := hb
  obtain ⟨-, -, -, w₂, hw₂, he₂⟩ := hc
  have hww : ChainVM.watch w₁ = ChainVM.watch w₂ := hw₁.symm.trans hw₂
  injection hww with hw
  rw [he₁, he₂, hw]

theorem copyOne_unique {s t₁ t₂ : GalilVM}
    (h₁ : (galilFrameS Pw qq first).copyOne s t₁)
    (h₂ : (galilFrameS Pw qq first).copyOne s t₂) : t₁ = t₂ := by
  refine lens_rel_unique (L := fppLens)
    (R := (fallbackFrame (fun _ => True) (fun _ => True)).copyOne) ?_ h₁ h₂
  intro a b c hb hc
  obtain ⟨u, hu, he₁⟩ := hb
  obtain ⟨v, hv, he₂⟩ := hc
  have huv' : some u = some v := hu.symm.trans hv
  injection huv' with huv
  rw [he₁, he₂, huv]

theorem copyEnd_unique {s t₁ t₂ : GalilVM}
    (h₁ : (galilFrameS Pw qq first).copyEnd s t₁)
    (h₂ : (galilFrameS Pw qq first).copyEnd s t₂) : t₁ = t₂ := by
  refine lens_rel_unique (L := fppLens)
    (R := (fallbackFrame (fun _ => True) (fun _ => True)).copyEnd) ?_ h₁ h₂
  intro a b c hb hc
  exact hb.trans hc.symm

theorem fppStart_unique {s t₁ t₂ : GalilVM}
    (h₁ : (galilFrameS Pw qq first).fppStart s t₁)
    (h₂ : (galilFrameS Pw qq first).fppStart s t₂) : t₁ = t₂ := by
  refine lens_rel_unique (L := fppLens)
    (R := (fallbackFrame (fun _ => True) (fun _ => True)).fppStart) ?_ h₁ h₂
  intro a b c hb hc
  exact hb.trans hc.symm

theorem homeStep_unique {s t₁ t₂ : GalilVM}
    (h₁ : (galilFrameS Pw qq first).homeStep s t₁)
    (h₂ : (galilFrameS Pw qq first).homeStep s t₂) : t₁ = t₂ := by
  refine lens_rel_unique (L := fppLens)
    (R := (fallbackFrame (fun _ => True) (fun _ => True)).homeStep) ?_ h₁ h₂
  intro a b c hb hc
  exact hb.2.trans hc.2.symm

theorem markForward_unique {s t₁ t₂ : GalilVM}
    (h₁ : (galilFrameS Pw qq first).markForward s t₁)
    (h₂ : (galilFrameS Pw qq first).markForward s t₂) : t₁ = t₂ := by
  refine lens_rel_unique (L := fppLens)
    (R := (marksFrame first (fun _ => True) (fun _ => True)).markForward) ?_ h₁ h₂
  intro a b c hb hc
  exact hb.trans hc.symm

theorem markBack_unique {s t₁ t₂ : GalilVM}
    (h₁ : (galilFrameS Pw qq first).markBack s t₁)
    (h₂ : (galilFrameS Pw qq first).markBack s t₂) : t₁ = t₂ := by
  refine lens_rel_unique (L := rewindLens)
    (R := (rewindFrame first (fun _ => True) (fun _ => True)).markBack) ?_ h₁ h₂
  intro a b c hb hc
  exact hb.2.trans hc.2.symm

/-- The fpp quantum is a *deterministic* run of the marked FPP code
(`control_run_unique`), so the slice is functional. -/
theorem fppSlice_unique {s t₁ t₂ : GalilVM}
    (h₁ : (galilFrameS Pw qq first).fppSlice s t₁)
    (h₂ : (galilFrameS Pw qq first).fppSlice s t₂) : t₁ = t₂ := by
  refine lens_rel_unique (L := fppLens)
    (R := (fppFrame qq first (fun _ => True) (fun _ => True)).fppSlice) ?_ h₁ h₂
  intro a b c hb hc
  obtain ⟨-, hrb, -, heb⟩ := hb
  obtain ⟨-, hrc, -, hec⟩ := hc
  have hp : b.program = c.program := control_run_unique marked_wellFormed hrb hrc
  rw [heb, hec, hp]

theorem fppDone_unique {s t₁ t₂ : GalilVM}
    (h₁ : (galilFrameS Pw qq first).fppDone s t₁)
    (h₂ : (galilFrameS Pw qq first).fppDone s t₂) : t₁ = t₂ := by
  refine lens_rel_unique (L := fppLens)
    (R := (fppFrame qq first (fun _ => True) (fun _ => True)).fppDone) ?_ h₁ h₂
  intro a b c hb hc
  obtain ⟨-, p, hp, -, heb⟩ := hb
  obtain ⟨-, p', hp', -, hec⟩ := hc
  have hpp : p = p' := control_run_unique marked_wellFormed hp hp'
  rw [heb, hec, hpp]

/-- The two fpp constructors are mutually exclusive: the same quantum cannot
both halt and not halt. -/
theorem fppSlice_fppDone_absurd {s t₁ t₂ : GalilVM}
    (h₁ : (galilFrameS Pw qq first).fppSlice s t₁)
    (h₂ : (galilFrameS Pw qq first).fppDone s t₂) : False := by
  obtain ⟨-, hr1, hd1, -⟩ := h₁.1
  obtain ⟨-, p, hp, hdp, -⟩ := h₂.1
  have he : (fppLens.get t₁).program = p := control_run_unique marked_wellFormed hr1 hp
  rw [he, hdp] at hd1
  exact absurd hd1 (by decide)

/-- The output refresh is a function of the state. -/
theorem refresh_unique {σ : Type} {F : Frame σ} {s : σ} {old o₁ o₂ : Bool}
    (h₁ : refresh F s old o₁) (h₂ : refresh F s old o₂) : o₁ = o₂ := by
  by_cases h : F.onLetter s
  · have e₁ := h₁.1 h
    have e₂ := h₂.1 h
    cases o₁ <;> cases o₂
    · rfl
    · exact e₁.2 (e₂.1 rfl)
    · exact (e₂.2 (e₁.1 rfl)).symm
    · rfl
  · rw [h₁.2 h, h₂.2 h]

end Fields

/-! ## 2. In one phase mode the successor of a tick is unique -/

section Modes

variable {Pw : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}

theorem tick_shift_cases {c : Control} {s : GalilVM} {y : State GalilVM}
    (hm : c.mode = .shift) (h : Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ y) :
    (∃ s', (galilFrameS Pw qq first).remainingPos s ∧
        (galilFrameS Pw qq first).shiftOne s s' ∧ y = ⟨c, s'⟩) ∨
    (∃ o : Bool, ¬ (galilFrameS Pw qq first).remainingPos s ∧
        refresh (galilFrameS Pw qq first) s c.output o ∧
        y = ⟨{c with mode := .scan, output := o}, s⟩) := by
  cases h <;>
    first
      | (exact Or.inl ⟨_, ‹_›, ‹_›, rfl⟩)
      | (exact Or.inr ⟨_, ‹_›, ‹_›, rfl⟩)
      | (exfalso; simp_all)

theorem tick_copy_cases {c : Control} {s : GalilVM} {y : State GalilVM}
    (hm : c.mode = .copy) (h : Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ y) :
    (∃ s', (galilFrameS Pw qq first).remainingPos s ∧
        (galilFrameS Pw qq first).copyOne s s' ∧ y = ⟨c, s'⟩) ∨
    (∃ s', ¬ (galilFrameS Pw qq first).remainingPos s ∧
        (galilFrameS Pw qq first).copyEnd s s' ∧ y = ⟨{c with mode := .home}, s'⟩) := by
  cases h <;>
    first
      | (exact Or.inl ⟨_, ‹_›, ‹_›, rfl⟩)
      | (exact Or.inr ⟨_, ‹_›, ‹_›, rfl⟩)
      | (exfalso; simp_all)

theorem tick_home_cases {c : Control} {s : GalilVM} {y : State GalilVM}
    (hm : c.mode = .home) (h : Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ y) :
    (∃ s', (galilFrameS Pw qq first).atLeft s ∧
        (galilFrameS Pw qq first).fppStart s s' ∧ y = ⟨{c with mode := .fpp}, s'⟩) ∨
    (∃ s', ¬ (galilFrameS Pw qq first).atLeft s ∧
        (galilFrameS Pw qq first).homeStep s s' ∧ y = ⟨c, s'⟩) := by
  cases h <;>
    first
      | (exact Or.inl ⟨_, ‹_›, ‹_›, rfl⟩)
      | (exact Or.inr ⟨_, ‹_›, ‹_›, rfl⟩)
      | (exfalso; simp_all)

theorem tick_fpp_cases {c : Control} {s : GalilVM} {y : State GalilVM}
    (hm : c.mode = .fpp) (h : Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ y) :
    (∃ s', (galilFrameS Pw qq first).fppSlice s s' ∧ y = ⟨c, s'⟩) ∨
    (∃ s', (galilFrameS Pw qq first).fppDone s s' ∧ y = ⟨{c with mode := .markEnd}, s'⟩) := by
  cases h <;>
    first
      | (exact Or.inl ⟨_, ‹_›, rfl⟩)
      | (exact Or.inr ⟨_, ‹_›, rfl⟩)
      | (exfalso; simp_all)

theorem tick_markEnd_cases {c : Control} {s : GalilVM} {y : State GalilVM}
    (hm : c.mode = .markEnd) (h : Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ y) :
    (∃ s', (galilFrameS Pw qq first).atEnd s ∧
        (galilFrameS Pw qq first).markBack s s' ∧
        y = ⟨{c with mode := .choose, odd := false}, s'⟩) ∨
    (∃ s', ¬ (galilFrameS Pw qq first).atEnd s ∧
        (galilFrameS Pw qq first).markForward s s' ∧ y = ⟨c, s'⟩) := by
  cases h <;>
    first
      | (exact Or.inl ⟨_, ‹_›, ‹_›, rfl⟩)
      | (exact Or.inr ⟨_, ‹_›, ‹_›, rfl⟩)
      | (exfalso; simp_all)

theorem tick_shift_unique {c : Control} {s : GalilVM} {y z : State GalilVM}
    (hm : c.mode = .shift)
    (h₁ : Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ y)
    (h₂ : Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ z) : y = z := by
  rcases tick_shift_cases hm h₁ with ⟨s₁, hp₁, ho₁, hy⟩ | ⟨o₁, hp₁, ho₁, hy⟩ <;>
    rcases tick_shift_cases hm h₂ with ⟨s₂, hp₂, ho₂, hz⟩ | ⟨o₂, hp₂, ho₂, hz⟩
  · rw [hy, hz, shiftOne_unique Pw qq first ho₁ ho₂]
  · exact absurd hp₁ hp₂
  · exact absurd hp₂ hp₁
  · rw [hy, hz, refresh_unique ho₁ ho₂]

theorem tick_copy_unique {c : Control} {s : GalilVM} {y z : State GalilVM}
    (hm : c.mode = .copy)
    (h₁ : Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ y)
    (h₂ : Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ z) : y = z := by
  rcases tick_copy_cases hm h₁ with ⟨s₁, hp₁, ho₁, hy⟩ | ⟨s₁, hp₁, ho₁, hy⟩ <;>
    rcases tick_copy_cases hm h₂ with ⟨s₂, hp₂, ho₂, hz⟩ | ⟨s₂, hp₂, ho₂, hz⟩
  · rw [hy, hz, copyOne_unique Pw qq first ho₁ ho₂]
  · exact absurd hp₁ hp₂
  · exact absurd hp₂ hp₁
  · rw [hy, hz, copyEnd_unique Pw qq first ho₁ ho₂]

theorem tick_home_unique {c : Control} {s : GalilVM} {y z : State GalilVM}
    (hm : c.mode = .home)
    (h₁ : Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ y)
    (h₂ : Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ z) : y = z := by
  rcases tick_home_cases hm h₁ with ⟨s₁, hp₁, ho₁, hy⟩ | ⟨s₁, hp₁, ho₁, hy⟩ <;>
    rcases tick_home_cases hm h₂ with ⟨s₂, hp₂, ho₂, hz⟩ | ⟨s₂, hp₂, ho₂, hz⟩
  · rw [hy, hz, fppStart_unique Pw qq first ho₁ ho₂]
  · exact absurd hp₁ hp₂
  · exact absurd hp₂ hp₁
  · rw [hy, hz, homeStep_unique Pw qq first ho₁ ho₂]

theorem tick_fpp_unique {c : Control} {s : GalilVM} {y z : State GalilVM}
    (hm : c.mode = .fpp)
    (h₁ : Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ y)
    (h₂ : Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ z) : y = z := by
  rcases tick_fpp_cases hm h₁ with ⟨s₁, ho₁, hy⟩ | ⟨s₁, ho₁, hy⟩ <;>
    rcases tick_fpp_cases hm h₂ with ⟨s₂, ho₂, hz⟩ | ⟨s₂, ho₂, hz⟩
  · rw [hy, hz, fppSlice_unique Pw qq first ho₁ ho₂]
  · exact absurd (fppSlice_fppDone_absurd Pw qq first ho₁ ho₂) (by simp)
  · exact absurd (fppSlice_fppDone_absurd Pw qq first ho₂ ho₁) (by simp)
  · rw [hy, hz, fppDone_unique Pw qq first ho₁ ho₂]

theorem tick_markEnd_unique {c : Control} {s : GalilVM} {y z : State GalilVM}
    (hm : c.mode = .markEnd)
    (h₁ : Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ y)
    (h₂ : Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ z) : y = z := by
  rcases tick_markEnd_cases hm h₁ with ⟨s₁, hp₁, ho₁, hy⟩ | ⟨s₁, hp₁, ho₁, hy⟩ <;>
    rcases tick_markEnd_cases hm h₂ with ⟨s₂, hp₂, ho₂, hz⟩ | ⟨s₂, hp₂, ho₂, hz⟩
  · rw [hy, hz, markBack_unique Pw qq first ho₁ ho₂]
  · exact absurd hp₁ hp₂
  · exact absurd hp₂ hp₁
  · rw [hy, hz, markForward_unique Pw qq first ho₁ ho₂]

end Modes

/-! ## 3. From a local `TickL3` to a `Realizes` obligation -/

section Build

variable {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
variable {Pw : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}

/-- A step that does not move the centre cursor keeps the left mirror's twin
invariant. -/
theorem mirInv1_keep {m : Mirrored1 P} (h : MirInv1 m) {y : GalilVML P}
    (hy : y.center = m.vm.center) : MirInv1 (⟨y, m.mirL⟩ : Mirrored1 P) := by
  refine ⟨?_, h.2⟩
  show PalPeg.LocalReplaySwap.Twin m.mirL y.center
  rw [hy]; exact h.1

/-- **The bridge.**  A local step that is a `TickL3` out of an `InvC` state,
in a mode whose scaffold ticks have unique successors, realizes the trace. -/
theorem realizes_of_mode (f : Mirrored1 P → Mirrored1 P) (md : Mode)
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, k < lastTick → Tick (galilFrameS Pw qq first) delay (stOf k) (stOf (k+1)))
    (huniq : ∀ (c : Control) (s : GalilVM) (y z : State GalilVM), c.mode = md →
      Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ y →
      Tick (galilFrameS Pw qq first) delay ⟨c, s⟩ z → y = z)
    (hstep : ∀ (m : Mirrored1 P) (k j : ℕ), InvC raw stOf m → m.vm.ctl.mode = md →
      ¬ Starved m.vm → Needy raw stOf k j m.vm →
      Tick (galilFrameS Pw qq first) delay (absState'' m.vm)
        (truncS (raw.length - j) (stOf (k+1))) →
      TickL3 Pw qq first m.vm (f m).vm)
    (hmir : ∀ m : Mirrored1 P, InvC raw stOf m → m.vm.ctl.mode = md → ¬ Starved m.vm →
      MirInv1 (f m)) :
    Realizes raw stOf lastTick f md := by
  intro m k j hinv hmd hns hn hneed hbefore
  have htr : Tick (galilFrameS Pw qq first) delay
      (truncS (raw.length - j) (stOf k)) (truncS (raw.length - j) (stOf (k+1))) :=
    tick_of_need (H_shared j) (H_trace k hbefore) hneed
  rw [← hn.2] at htr
  have ht3 := hstep m k j hinv hmd hns hn htr
  have habs : Tick (galilFrameS Pw qq first) delay (absState'' m.vm) (absState'' (f m).vm) :=
    tickL3_abs delay hinv.phys.inv ht3
  refine ⟨⟨hn.1, ?_⟩, physWF_of_tickL3 hinv.phys ht3, hmir m hinv hmd hns⟩
  exact huniq m.vm.ctl (abs'' m.vm) _ _ hmd habs htr

end Build

/-! ## 4. `home` -/

/-- The frame guard `atLeft`, read off the local state. -/
def AtLeftL (x : GalilVML P) : Prop := (sourceOf (abs' x)).focus = 4

theorem atLeftL_iff (Pw : Shared) (qq : ℕ) (first : Fin 9) (x : GalilVML P) :
    (galilFrameS Pw qq first).atLeft (abs' x) ↔ AtLeftL x := Iff.rfl

open Classical in
/-- **The local `home` step.**  `fpp.start()` once SOURCE reads `LEFT`,
otherwise one cell left on SOURCE. -/
noncomputable def homeStepL (m : Mirrored1 P) : Mirrored1 P :=
  if AtLeftL m.vm then ⟨homeStartVm { m.vm.ctl with mode := .fpp } m.vm, m.mirL⟩
  else ⟨homeStepVm m.vm, m.mirL⟩

theorem mirInv1_homeStepL {m : Mirrored1 P} (h : MirInv1 m) : MirInv1 (homeStepL m) := by
  unfold homeStepL
  split
  · exact mirInv1_keep h rfl
  · exact mirInv1_keep h rfl

theorem tickL3_homeStepL {Pw : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}
    {m : Mirrored1 P} {T : State GalilVM}
    (hnr : m.vm.ctl.replaying = false) (hmd : m.vm.ctl.mode = .home)
    (htr : Tick (galilFrameS Pw qq first) delay (absState'' m.vm) T) :
    TickL3 Pw qq first m.vm (homeStepL m).vm := by
  have hA : abs'' m.vm = abs' m.vm := abs''_eq_abs' hnr
  have htr' : Tick (galilFrameS Pw qq first) delay ⟨m.vm.ctl, abs' m.vm⟩ T := by
    rw [← hA]; exact htr
  rcases tick_home_cases hmd htr' with ⟨s', hl, -, -⟩ | ⟨s', hl, hhs, -⟩
  · have hl' : AtLeftL m.vm := hl
    have he : homeStepL m = ⟨homeStartVm { m.vm.ctl with mode := .fpp } m.vm, m.mirL⟩ := by
      unfold homeStepL; rw [if_pos hl']
    rw [he]
    exact TickL3.home_start m.vm hmd hnr hl
  · have hl' : ¬ AtLeftL m.vm := hl
    have hne : ((abs' m.vm).fpp.program.config.tapes 7).left ≠ [] := hhs.1.1
    have he : homeStepL m = ⟨homeStepVm m.vm, m.mirL⟩ := by
      unfold homeStepL; rw [if_neg hl']
    rw [he]
    exact TickL3.home_step m.vm hmd hnr hl hne

/-- **`home` is closed**, modulo the control-flow fact that a phase mode never
replays. -/
theorem realizes_home {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {Pw : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, k < lastTick → Tick (galilFrameS Pw qq first) delay (stOf k) (stOf (k+1)))
    (H_nr : ∀ m : Mirrored1 P, InvC raw stOf m → m.vm.ctl.mode = .home →
      m.vm.ctl.replaying = false) :
    Realizes raw stOf lastTick (homeStepL (P := P)) .home :=
  realizes_of_mode (delay := delay) (qq := qq) (first := first) _ _ H_shared H_trace
    (fun _ _ _ _ hm h₁ h₂ => tick_home_unique hm h₁ h₂)
    (fun m k j hinv hmd _ _ htr => tickL3_homeStepL (H_nr m hinv hmd) hmd htr)
    (fun m hinv _ _ => mirInv1_homeStepL hinv.mir)

/-! ## 5. `markEnd` -/

/-- The frame guard `atEnd`, read off the local state. -/
def AtEndL (x : GalilVML P) : Prop := (marksOf (abs' x)).focus = 5

theorem atEndL_iff (Pw : Shared) (qq : ℕ) (first : Fin 9) (x : GalilVML P) :
    (galilFrameS Pw qq first).atEnd (abs' x) ↔ AtEndL x := Iff.rfl

open Classical in
/-- **The local `markEnd` step.**  MARKS one cell back (and into `choose`) when
it reads `END`, otherwise one cell forward. -/
noncomputable def markEndStepL (m : Mirrored1 P) : Mirrored1 P :=
  if AtEndL m.vm then
    ⟨marksVm GalilScaffoldTape.moveLeft
      { m.vm.ctl with mode := .choose, odd := false } m.vm, m.mirL⟩
  else ⟨marksVm GalilScaffoldTape.moveRight m.vm.ctl m.vm, m.mirL⟩

theorem mirInv1_markEndStepL {m : Mirrored1 P} (h : MirInv1 m) : MirInv1 (markEndStepL m) := by
  unfold markEndStepL
  split
  · exact mirInv1_keep h rfl
  · exact mirInv1_keep h rfl

theorem tickL3_markEndStepL {Pw : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}
    {m : Mirrored1 P} {T : State GalilVM}
    (hnr : m.vm.ctl.replaying = false) (hmd : m.vm.ctl.mode = .markEnd)
    (htr : Tick (galilFrameS Pw qq first) delay (absState'' m.vm) T) :
    TickL3 Pw qq first m.vm (markEndStepL m).vm := by
  have hA : abs'' m.vm = abs' m.vm := abs''_eq_abs' hnr
  have htr' : Tick (galilFrameS Pw qq first) delay ⟨m.vm.ctl, abs' m.vm⟩ T := by
    rw [← hA]; exact htr
  rcases tick_markEnd_cases hmd htr' with ⟨s', he, hmb, -⟩ | ⟨s', he, -, -⟩
  · have he' : AtEndL m.vm := he
    have hne : (marksOf (abs' m.vm)).left ≠ [] := hmb.1.1
    have hstep : markEndStepL m = ⟨marksVm GalilScaffoldTape.moveLeft
        { m.vm.ctl with mode := .choose, odd := false } m.vm, m.mirL⟩ := by
      unfold markEndStepL; rw [if_pos he']
    rw [hstep]
    exact TickL3.markEnd_found m.vm hmd hnr he hne
  · have he' : ¬ AtEndL m.vm := he
    have hstep : markEndStepL m
        = ⟨marksVm GalilScaffoldTape.moveRight m.vm.ctl m.vm, m.mirL⟩ := by
      unfold markEndStepL; rw [if_neg he']
    rw [hstep]
    exact TickL3.markEnd_step m.vm hmd hnr he

/-- **`markEnd` is closed**, modulo the same control-flow fact. -/
theorem realizes_markEnd {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {Pw : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, k < lastTick → Tick (galilFrameS Pw qq first) delay (stOf k) (stOf (k+1)))
    (H_nr : ∀ m : Mirrored1 P, InvC raw stOf m → m.vm.ctl.mode = .markEnd →
      m.vm.ctl.replaying = false) :
    Realizes raw stOf lastTick (markEndStepL (P := P)) .markEnd :=
  realizes_of_mode (delay := delay) (qq := qq) (first := first) _ _ H_shared H_trace
    (fun _ _ _ _ hm h₁ h₂ => tick_markEnd_unique hm h₁ h₂)
    (fun m k j hinv hmd _ _ htr => tickL3_markEndStepL (H_nr m hinv hmd) hmd htr)
    (fun m hinv _ _ => mirInv1_markEndStepL hinv.mir)

/-! ## 6. `copy` -/

/-- The frame guard `remainingPos`, read off the local state. -/
def RemPosL (x : GalilVML P) : Prop := ShiftRemaining (abs' x) ∨ CopyRemaining (abs' x)

theorem remPosL_iff (Pw : Shared) (qq : ℕ) (first : Fin 9) (x : GalilVML P) :
    (galilFrameS Pw qq first).remainingPos (abs' x) ↔ RemPosL x := Iff.rfl

/-- The copy unit, dispatching on the letter the walker reads. -/
noncomputable def copyPick (o : Option (Fin 3)) (m : Mirrored1 P) : Mirrored1 P :=
  match o with
  | some a => ⟨copyVm a m.vm, m.mirL⟩
  | none => m

@[simp] theorem copyPick_some (a : Fin 3) (m : Mirrored1 P) :
    copyPick (some a) m = ⟨copyVm a m.vm, m.mirL⟩ := rfl

open Classical in
/-- **The local `copy` step.**  One window cell onto SOURCE while the copy has
work left, otherwise `source.write(END)` and into `home`. -/
noncomputable def copyStepL (m : Mirrored1 P) : Mirrored1 P :=
  if RemPosL m.vm then copyPick (GalilScaffoldPlace.read (abs' m.vm).fpp.walker) m
  else ⟨copyDoneVm { m.vm.ctl with mode := .home } m.vm, m.mirL⟩

theorem mirInv1_copyStepL {m : Mirrored1 P} (h : MirInv1 m) : MirInv1 (copyStepL m) := by
  unfold copyStepL
  split
  · unfold copyPick
    split
    · exact mirInv1_keep h rfl
    · exact h
  · exact mirInv1_keep h rfl

/-- The physical side conditions of a local copy unit that `InvC` does not
carry: the sign bit and the positivity of the `fppWork` tape, and that the
walker cursor is anchored. -/
structure CopySide (x : GalilVML P) : Prop where
  pol : x.pol .fppWork = true
  pos : 0 < LocalCounter.val (x.phys (x.roles .fppWork))
  proper : PalPeg.LocalChain.ProperView x.fppWalker

theorem tickL3_copyStepL {Pw : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}
    {m : Mirrored1 P} {T : State GalilVM}
    (hnr : m.vm.ctl.replaying = false) (hmd : m.vm.ctl.mode = .copy)
    (hside : RemPosL m.vm → CopySide m.vm)
    (htr : Tick (galilFrameS Pw qq first) delay (absState'' m.vm) T) :
    TickL3 Pw qq first m.vm (copyStepL m).vm := by
  have hA : abs'' m.vm = abs' m.vm := abs''_eq_abs' hnr
  have htr' : Tick (galilFrameS Pw qq first) delay ⟨m.vm.ctl, abs' m.vm⟩ T := by
    rw [← hA]; exact htr
  rcases tick_copy_cases hmd htr' with ⟨s', hp, hco, -⟩ | ⟨s', hp, -, -⟩
  · obtain ⟨a, ha, -⟩ := hco.1
    have hp' : RemPosL m.vm := hp
    have hside' := hside hp'
    have hr : GalilScaffoldPlace.read (abs' m.vm).fpp.walker = some a := ha
    have he : copyStepL m = ⟨copyVm a m.vm, m.mirL⟩ := by
      unfold copyStepL; rw [if_pos hp', hr, copyPick_some]
    rw [he]
    exact TickL3.copy_one m.vm a hmd hnr ha hside'.proper hside'.pol hside'.pos
  · have hp' : ¬ RemPosL m.vm := hp
    have he : copyStepL m = ⟨copyDoneVm { m.vm.ctl with mode := .home } m.vm, m.mirL⟩ := by
      unfold copyStepL; rw [if_neg hp']
    rw [he]
    exact TickL3.copy_done m.vm hmd hnr hp

/-- **`copy` is closed**, modulo the control-flow fact and the physical side
conditions `CopySide` of a copy unit. -/
theorem realizes_copy {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {Pw : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, k < lastTick → Tick (galilFrameS Pw qq first) delay (stOf k) (stOf (k+1)))
    (H_nr : ∀ m : Mirrored1 P, InvC raw stOf m → m.vm.ctl.mode = .copy →
      m.vm.ctl.replaying = false)
    (H_copy : ∀ m : Mirrored1 P, InvC raw stOf m → m.vm.ctl.mode = .copy →
      ¬ Starved m.vm → RemPosL m.vm → CopySide m.vm) :
    Realizes raw stOf lastTick (copyStepL (P := P)) .copy :=
  realizes_of_mode (delay := delay) (qq := qq) (first := first) _ _ H_shared H_trace
    (fun _ _ _ _ hm h₁ h₂ => tick_copy_unique hm h₁ h₂)
    (fun m k j hinv hmd hns _ htr =>
      tickL3_copyStepL (H_nr m hinv hmd) hmd (H_copy m hinv hmd hns) htr)
    (fun m hinv _ _ => mirInv1_copyStepL hinv.mir)

/-! ## 7. `shift` -/

open Classical in
/-- The Scala `if (!right.gap) output = left.isFirst`, as a function. -/
noncomputable def refreshOf (Pw : Shared) (s : GalilVM) (old : Bool) : Bool :=
  if Pw.onLetter s then decide (Pw.leftFirst s) else old

open Classical in
theorem refresh_refreshOf (Pw : Shared) (qq : ℕ) (first : Fin 9) (s : GalilVM) (old : Bool) :
    refresh (galilFrameS Pw qq first) s old (refreshOf Pw s old) := by
  constructor
  · intro h
    have h' : Pw.onLetter s := h
    show (refreshOf Pw s old = true) ↔ Pw.leftFirst s
    rw [refreshOf, if_pos h']
    exact decide_eq_true_iff
  · intro h
    have h' : ¬ Pw.onLetter s := h
    show refreshOf Pw s old = old
    rw [refreshOf, if_neg h']

/-- The shift unit, dispatching on the (watched) chain. -/
noncomputable def shiftPick (ch : ChainVM) (x : GalilVML P) (mir : InputView) : Mirrored1 P :=
  match ch with
  | .watch w => ⟨shiftVm w x, PalPeg.LocalInputView.moveRight mir⟩
  | _ => ⟨x, mir⟩

@[simp] theorem shiftPick_watch (w : GalilScaffoldChainWatch.State) (x : GalilVML P)
    (mir : InputView) :
    shiftPick (ChainVM.watch w) x mir = ⟨shiftVm w x, PalPeg.LocalInputView.moveRight mir⟩ := rfl

/-- The controller record a finished shift hands back to `scan`. -/
noncomputable def shiftDoneCtl (Pw : Shared) (x : GalilVML P) : Control :=
  { x.ctl with mode := .scan, output := refreshOf Pw (abs' x) x.ctl.output }

open Classical in
/-- **The local `shift` step.**  One shift unit while `remaining` is positive,
otherwise back to `scan` with the output refreshed. -/
noncomputable def shiftStepL (Pw : Shared) (m : Mirrored1 P) : Mirrored1 P :=
  if RemPosL m.vm then shiftPick m.vm.chain m.vm m.mirL
  else ⟨{ m.vm with ctl := shiftDoneCtl Pw m.vm }, m.mirL⟩

theorem mirInv1_shiftStepL (Pw : Shared) {m : Mirrored1 P} (h : MirInv1 m)
    (hc : PalPeg.LocalInputView.WF m.vm.center) : MirInv1 (shiftStepL Pw m) := by
  unfold shiftStepL
  split
  · unfold shiftPick
    split <;>
      first
        | exact PalPeg.LocalReplayParked.mirInv1_mirrorTick1 h hc .right rfl
        | exact mirInv1_keep h rfl
  · exact mirInv1_keep h rfl

theorem tickL3_shiftStepL {Pw : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}
    {m : Mirrored1 P} {T : State GalilVM}
    (hnr : m.vm.ctl.replaying = false) (hmd : m.vm.ctl.mode = .shift)
    (hpend : m.vm.pending = [])
    (hside : RemPosL m.vm → ShiftCounters m.vm)
    (htr : Tick (galilFrameS Pw qq first) delay (absState'' m.vm) T) :
    TickL3 Pw qq first m.vm (shiftStepL Pw m).vm := by
  have hA : abs'' m.vm = abs' m.vm := abs''_eq_abs' hnr
  have htr' : Tick (galilFrameS Pw qq first) delay ⟨m.vm.ctl, abs' m.vm⟩ T := by
    rw [← hA]; exact htr
  rcases tick_shift_cases hmd htr' with ⟨s', hp, hso, -⟩ | ⟨o, hp, ho, -⟩
  · obtain ⟨hcC, hcL, hcL', w, hw, -⟩ := hso.1
    have hp' : RemPosL m.vm := hp
    have hw' : m.vm.chain = ChainVM.watch w := hw
    have he : shiftStepL Pw m
        = ⟨shiftVm w m.vm, PalPeg.LocalInputView.moveRight m.mirL⟩ := by
      unfold shiftStepL; rw [if_pos hp', hw', shiftPick_watch]
    rw [he]
    exact TickL3.shift_one m.vm w hmd hnr hw' (hside hp')
      (fun _ _ => Or.inr hpend) (fun _ _ => Or.inr hpend) (fun _ _ => Or.inr hpend)
      hcC hcL hcL'
  · have hp' : ¬ RemPosL m.vm := hp
    have he : shiftStepL Pw m = ⟨{ m.vm with ctl := shiftDoneCtl Pw m.vm }, m.mirL⟩ := by
      unfold shiftStepL; rw [if_neg hp']
    rw [he]
    exact TickL3.shift_done m.vm _ hmd hnr hp (refresh_refreshOf Pw qq first _ _)

/-- **`shift` is closed**, modulo the control-flow fact and the counter side
conditions `ShiftCounters` of a shift unit. -/
theorem realizes_shift {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {Pw : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, k < lastTick → Tick (galilFrameS Pw qq first) delay (stOf k) (stOf (k+1)))
    (H_nr : ∀ m : Mirrored1 P, InvC raw stOf m → m.vm.ctl.mode = .shift →
      m.vm.ctl.replaying = false)
    (H_shift : ∀ m : Mirrored1 P, InvC raw stOf m → m.vm.ctl.mode = .shift →
      ¬ Starved m.vm → RemPosL m.vm → ShiftCounters m.vm) :
    Realizes raw stOf lastTick (shiftStepL (P := P) Pw) .shift :=
  realizes_of_mode (delay := delay) (qq := qq) (first := first) _ _ H_shared H_trace
    (fun _ _ _ _ hm h₁ h₂ => tick_shift_unique hm h₁ h₂)
    (fun m k j hinv hmd hns _ htr =>
      tickL3_shiftStepL (H_nr m hinv hmd) hmd hinv.phys.pend (H_shift m hinv hmd hns) htr)
    (fun m hinv _ _ => mirInv1_shiftStepL Pw hinv.mir hinv.phys.inv.views.2.1)

/-! ## 8. `fpp`

The abstract tracking half is closed here too (`tick_fpp_unique`); what is left
is the purely *local* obligation that the fpp step of the finite control
executes one quantum of the marked FPP code on the double buffer, i.e. that it
is a `TickL3.fpp_slice`/`fpp_done`.  That needs the pointwise step family `g`
of `LocalTick3.fppRunBuf` and the program counter, which this file does not
construct; it is kept as the named hypothesis `H_fpp`. -/

theorem realizes_fpp {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {Pw : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}
    (ffpp : Mirrored1 P → Mirrored1 P)
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, k < lastTick → Tick (galilFrameS Pw qq first) delay (stOf k) (stOf (k+1)))
    (H_fpp : ∀ (m : Mirrored1 P) (k j : ℕ), InvC raw stOf m → m.vm.ctl.mode = .fpp →
      ¬ Starved m.vm → Needy raw stOf k j m.vm →
      Tick (galilFrameS Pw qq first) delay (absState'' m.vm)
        (truncS (raw.length - j) (stOf (k+1))) →
      TickL3 Pw qq first m.vm (ffpp m).vm)
    (H_fpp_mir : ∀ m : Mirrored1 P, InvC raw stOf m → m.vm.ctl.mode = .fpp →
      ¬ Starved m.vm → MirInv1 (ffpp m)) :
    Realizes raw stOf lastTick ffpp .fpp :=
  realizes_of_mode (delay := delay) (qq := qq) (first := first) _ _ H_shared H_trace
    (fun _ _ _ _ hm h₁ h₂ => tick_fpp_unique hm h₁ h₂) H_fpp H_fpp_mir

/-! ## 9. The `Steps` record -/

/-- The five phase steps of this file, with the other five modes supplied. -/
noncomputable def phaseSteps (Pw : Shared) (ffpp init scan choose rewind replayStart :
    Mirrored1 P → Mirrored1 P) : PalPeg.LocalSysConcrete.Steps P where
  init := init
  scan := scan
  shift := shiftStepL Pw
  copy := copyStepL
  home := homeStepL
  fpp := ffpp
  markEnd := markEndStepL
  choose := choose
  rewind := rewind
  replayStart := replayStart

@[simp] theorem phaseSteps_shift (Pw : Shared) (ffpp init scan choose rewind replayStart :
    Mirrored1 P → Mirrored1 P) :
    (phaseSteps Pw ffpp init scan choose rewind replayStart).shift = shiftStepL Pw := rfl

@[simp] theorem phaseSteps_copy (Pw : Shared) (ffpp init scan choose rewind replayStart :
    Mirrored1 P → Mirrored1 P) :
    (phaseSteps Pw ffpp init scan choose rewind replayStart).copy = copyStepL := rfl

@[simp] theorem phaseSteps_home (Pw : Shared) (ffpp init scan choose rewind replayStart :
    Mirrored1 P → Mirrored1 P) :
    (phaseSteps Pw ffpp init scan choose rewind replayStart).home = homeStepL := rfl

@[simp] theorem phaseSteps_fpp (Pw : Shared) (ffpp init scan choose rewind replayStart :
    Mirrored1 P → Mirrored1 P) :
    (phaseSteps Pw ffpp init scan choose rewind replayStart).fpp = ffpp := rfl

@[simp] theorem phaseSteps_markEnd (Pw : Shared) (ffpp init scan choose rewind replayStart :
    Mirrored1 P → Mirrored1 P) :
    (phaseSteps Pw ffpp init scan choose rewind replayStart).markEnd = markEndStepL := rfl

/-! ## 10. The five obligations together

`PhaseNoReplay` is the only hypothesis shared by all five: a phase mode never
replays.  It is a property of the trace's control flow (`replaying` is set only
by `scan_match`/`replayStart`, and `scan` leaves for `shift`/`copy` only when
`replaying = false`), so it cannot be proved from `InvC` alone. -/

/-- "A phase mode never replays." -/
def PhaseNoReplay (raw : List (Fin 2)) (stOf : ℕ → State GalilVM) : Prop :=
  ∀ m : Mirrored1 P, InvC raw stOf m →
    (m.vm.ctl.mode = .shift ∨ m.vm.ctl.mode = .copy ∨ m.vm.ctl.mode = .home ∨
      m.vm.ctl.mode = .fpp ∨ m.vm.ctl.mode = .markEnd) → m.vm.ctl.replaying = false

/-- **The five phase obligations of `LocalSysConcrete.localSys_oracles`**,
discharged from: the trace hypotheses of `localSys_oracles` itself, the shared
control-flow fact `PhaseNoReplay`, the physical side conditions of a copy unit
(`CopySide`) and of a shift unit (`ShiftCounters`), and the local fpp quantum
(`H_fpp`, `H_fpp_mir`). -/
theorem realizes_phases {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {Pw : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}
    (ffpp : Mirrored1 P → Mirrored1 P)
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, k < lastTick → Tick (galilFrameS Pw qq first) delay (stOf k) (stOf (k+1)))
    (H_nr : PhaseNoReplay (P := P) raw stOf)
    (H_copy : ∀ m : Mirrored1 P, InvC raw stOf m → m.vm.ctl.mode = .copy →
      ¬ Starved m.vm → RemPosL m.vm → CopySide m.vm)
    (H_shift : ∀ m : Mirrored1 P, InvC raw stOf m → m.vm.ctl.mode = .shift →
      ¬ Starved m.vm → RemPosL m.vm → ShiftCounters m.vm)
    (H_fpp : ∀ (m : Mirrored1 P) (k j : ℕ), InvC raw stOf m → m.vm.ctl.mode = .fpp →
      ¬ Starved m.vm → Needy raw stOf k j m.vm →
      Tick (galilFrameS Pw qq first) delay (absState'' m.vm)
        (truncS (raw.length - j) (stOf (k+1))) →
      TickL3 Pw qq first m.vm (ffpp m).vm)
    (H_fpp_mir : ∀ m : Mirrored1 P, InvC raw stOf m → m.vm.ctl.mode = .fpp →
      ¬ Starved m.vm → MirInv1 (ffpp m)) :
    Realizes raw stOf lastTick (shiftStepL (P := P) Pw) .shift ∧
    Realizes raw stOf lastTick (copyStepL (P := P)) .copy ∧
    Realizes raw stOf lastTick (homeStepL (P := P)) .home ∧
    Realizes raw stOf lastTick ffpp .fpp ∧
    Realizes raw stOf lastTick (markEndStepL (P := P)) .markEnd :=
  ⟨realizes_shift (delay := delay) H_shared H_trace
      (fun m hinv hmd => H_nr m hinv (Or.inl hmd)) H_shift,
   realizes_copy (delay := delay) H_shared H_trace
      (fun m hinv hmd => H_nr m hinv (Or.inr (Or.inl hmd))) H_copy,
   realizes_home (delay := delay) H_shared H_trace
      (fun m hinv hmd => H_nr m hinv (Or.inr (Or.inr (Or.inl hmd)))),
   realizes_fpp (delay := delay) ffpp H_shared H_trace H_fpp H_fpp_mir,
   realizes_markEnd (delay := delay) H_shared H_trace
      (fun m hinv hmd => H_nr m hinv (Or.inr (Or.inr (Or.inr (Or.inr hmd)))))⟩

#print axioms lens_rel_unique
#print axioms fppSlice_unique
#print axioms fppSlice_fppDone_absurd
#print axioms refresh_unique
#print axioms tick_shift_unique
#print axioms tick_copy_unique
#print axioms tick_home_unique
#print axioms tick_fpp_unique
#print axioms tick_markEnd_unique
#print axioms realizes_of_mode
#print axioms realizes_home
#print axioms realizes_markEnd
#print axioms realizes_copy
#print axioms realizes_shift
#print axioms realizes_fpp
#print axioms realizes_phases

end PalPeg.LocalRealizesPhase
