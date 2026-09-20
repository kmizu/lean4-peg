import PalPeg.LocalSysConcrete

/-!
# Discharging the mode obligations of `LocalSysConcrete.Realizes`

`LocalSysConcrete.localSys_oracles` needs one `Realizes Good raw stOf lastTick M.<mode> <mode>`
per control mode.  This file supplies the general bridge and then the modes
`rewind`, `choose`, `init`, `replayStart`, `scan`.

## The bridge

`realizes_of_tick_det` splits a mode obligation into

* **a local tick** (`Hloc`): on an invariant, non-starved state *at which the
  trace already has an abstract tick*, the mode's local step abstracts to some
  `Tick (galilFrameS Pw qq firstT) delay` out of `absState''` and keeps the
  physical pack and the left mirror; and
* **determinism of the abstract tick in that mode** (`Hdet`).

The trace's own tick survives truncation by `LocalSysConcrete.tick_of_need`, so
`Hdet` forces the local step onto `truncS (raw.length − j) (stOf (k+1))`, which
is exactly `Needy raw stOf (k+1) j`.  Passing the trace tick *into* `Hloc` is
what lets the local step read its abstract enabling conditions off the run
instead of assuming them.

## What is closed

* **`rewind`, `choose`** — `realizes_rewind`, `realizes_choose`.  Determinism is
  proved outright (`tick_det_rewind`, `tick_det_choose`): the branch is pinned by
  `atFirst`/`pair` resp. `odd`/`markSet`, and every `rewind`-frame block is an
  equation, so `lens_rel_unique` applies.  The local steps are `LocalTick3`'s
  `rewindDoneVm`/`rewindOneVm`/`rewindPairVm` and `chooseVm`/`marksVm`, selected
  classically; `marksLeft_of_rewind_tick` / `marksLeft_of_choose_tick` read
  `MARKS.left ≠ []` off the trace tick, `physWF_of_tickL3` gives the physical
  pack and `mirInv1_mirrorTick1` the mirror (`.left` only for `rewind_pair`,
  the one action that moves the centre).
  **Residual:** the local side conditions `RewindWF` / `ChooseWF`, supplied as
  `H_rewindWF` / `H_chooseWF`.
* **`init`, `replayStart`** — determinism is reduced, with nothing further
  assumed, to *functionality of the corresponding `Shared` field*
  (`tick_det_init`, `tick_det_replayStart`); the output bit is pinned
  unconditionally by `refresh_unique`.
  **Residual:** `H_initFun`/`H_rsFun` and the local realizations
  `H_initLoc`/`H_replayStartLoc`.  (`LocalReplayParked.commitReplayParked` is the
  intended witness for the latter, but `LocalTick2.commitReplay` has no
  `LocalTick1.Inv`-preservation lemma yet, so its physical half is not
  available.)
* **`scan`** — the one mode whose abstract successor is *not* pinned by its
  source: `Tick.restart` competes with all five scan constructors and the
  `background`/`compare` blocks carry the relational `SafeQuanta`/`chainAt`.
  Both halves stay open (`H_scanDet`, `H_scanLoc`).  Closed here: `tickL1_center`
  (no scan tick moves the centre) and hence `physWF_mir_of_tickL1`, the physical
  half of a non-replaying scan tick with its mirror.

**無条件 PAL ∈ PEG は未完.**
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace PalPeg.LocalRealizesScan

variable {lastTick : ℕ}

open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.LocalState
open PalPeg.LocalInputView (InputView)
open PalPeg.LocalArrival (absHead' abs')
open PalPeg.GalilTickFun3 (marksOf)
open PalPeg.LocalTick3 (TickL3 rewindDoneVm rewindOneVm rewindPairVm chooseVm marksVm absState''_eq)
open PalPeg.LocalReplayParked (abs'' absState'' ParkedOK Mirrored1 MirInv1 mirrorTick1)
open PalPeg.LocalTick1 (Inv)
open PalPeg.GalilThrottledRun (truncS)
open PalPeg.GalilLookRefined (needT')
open PalPeg.LocalSysConcrete

variable {P : ℕ}

variable {Good : Mirrored1 P → Prop}

/-! ## 1. The bridge: a local tick plus determinism of the abstract tick -/

/-- Identify successors using a deterministic refinement of the abstract tick. -/
theorem realizes_of_refined_tick_det {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {Pw : Shared} {qq : ℕ} {firstT : Fin 9} {delay : ℕ}
    {f : Mirrored1 P → Mirrored1 P} {md : Mode}
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, k < lastTick → Tick (galilFrameS Pw qq firstT) delay (stOf k) (stOf (k+1)))
    (Refinement : State GalilVM → State GalilVM → Prop)
    (hTraceRefinement : ∀ k j, k < lastTick → TickNeed raw stOf k j →
      Refinement (truncS (raw.length - j) (stOf k))
        (truncS (raw.length - j) (stOf (k+1))))
    (Hloc : ∀ (m : Mirrored1 P) (t : State GalilVM), InvC Good raw stOf m → m.vm.ctl.mode = md →
      ¬ Starved m.vm → Tick (galilFrameS Pw qq firstT) delay (absState'' m.vm) t →
      Tick (galilFrameS Pw qq firstT) delay (absState'' m.vm) (absState'' (f m).vm) ∧
        Refinement (absState'' m.vm) (absState'' (f m).vm) ∧ PhysWF (f m).vm ∧ MirInv1 (f m))
    (Hdet : ∀ {s t₁ t₂ : State GalilVM}, s.ctl.mode = md →
      Tick (galilFrameS Pw qq firstT) delay s t₁ → Refinement s t₁ →
      Tick (galilFrameS Pw qq firstT) delay s t₂ → Refinement s t₂ → t₁ = t₂) :
    Realizes Good raw stOf lastTick f md := by
  intro m k j hinv hmd hns hn hneed hbefore
  have h2 := tick_of_need (Pw := Pw) (qq := qq) (first := firstT) (delay := delay)
    (H_shared j) (H_trace k hbefore) hneed
  rw [← hn.2] at h2
  obtain ⟨ht, hRefinement, hph, hmir⟩ := Hloc m _ hinv hmd hns h2
  refine ⟨⟨hn.1, ?_⟩, hph, hmir⟩
  rw [hn.2] at ht h2 hRefinement
  have hm0 : (truncS (raw.length - j) (stOf k)).ctl.mode = md := by
    rw [← hn.2]; exact hmd
  exact Hdet hm0 ht hRefinement h2 (hTraceRefinement k j hbefore hneed)

theorem realizes_of_tick_det {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {Pw : Shared} {qq : ℕ} {firstT : Fin 9} {delay : ℕ}
    {f : Mirrored1 P → Mirrored1 P} {md : Mode}
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, k < lastTick → Tick (galilFrameS Pw qq firstT) delay (stOf k) (stOf (k+1)))
    (Hloc : ∀ (m : Mirrored1 P) (t : State GalilVM), InvC Good raw stOf m → m.vm.ctl.mode = md →
      ¬ Starved m.vm → Tick (galilFrameS Pw qq firstT) delay (absState'' m.vm) t →
      Tick (galilFrameS Pw qq firstT) delay (absState'' m.vm) (absState'' (f m).vm) ∧
        PhysWF (f m).vm ∧ MirInv1 (f m))
    (Hdet : ∀ {s t₁ t₂ : State GalilVM}, s.ctl.mode = md →
      Tick (galilFrameS Pw qq firstT) delay s t₁ →
      Tick (galilFrameS Pw qq firstT) delay s t₂ → t₁ = t₂) :
    Realizes Good raw stOf lastTick f md := by
  apply realizes_of_refined_tick_det H_shared H_trace (fun _ _ => True)
    (fun _ _ _ _ => True.intro)
  · intro m t hInvariant hMode hNotStarved hTick
    obtain ⟨hLocalTick, hPhysical, hMirror⟩ := Hloc m t hInvariant hMode hNotStarved hTick
    exact ⟨hLocalTick, True.intro, hPhysical, hMirror⟩
  · intro s t₁ t₂ hMode hTick₁ _ hTick₂ _
    exact Hdet hMode hTick₁ hTick₂

#print axioms realizes_of_tick_det


/-! ## 2. Determinism of the abstract tick in the `rewind` and `choose` modes -/

theorem lens_rel_unique {σ σ' : Type} (L : Lens σ σ') {R : σ' → σ' → Prop} {g : σ' → σ'}
    (hR : ∀ a b, R a b → b = g a) {s t₁ t₂ : σ}
    (h1 : L.rel R s t₁) (h2 : L.rel R s t₂) : t₁ = t₂ := by
  obtain ⟨hr1, he1⟩ := h1
  obtain ⟨hr2, he2⟩ := h2
  rw [he1, he2, hR _ _ hr1, hR _ _ hr2]

section Det
variable (Pw : Shared) (qq : ℕ) (firstT : Fin 9) (delay : ℕ)

/-- The image of the `rewind`-frame blocks, as functions on `RewindVM`. -/
def gReset (a : RewindVM) : RewindVM :=
  { a with fpp := { a.fpp with program := GalilScaffoldControl.reset 320 a.fpp.program } }

def gBack (a : RewindVM) : RewindVM := { a with fpp := markStep a.fpp GalilScaffoldTape.moveLeft }

def gOne (a : RewindVM) : RewindVM :=
  { a with
      fpp := markStep a.fpp GalilScaffoldTape.moveLeft
      left := GalilScaffoldInputHead.left a.left
      length := GalilScaffoldCounter.inc a.length }

def gPair (a : RewindVM) : RewindVM :=
  { a with
      fpp := markStep a.fpp GalilScaffoldTape.moveLeft
      left := GalilScaffoldInputHead.left a.left
      length := GalilScaffoldCounter.inc a.length
      center := GalilScaffoldInputHead.left a.center
      radius := GalilScaffoldCounter.inc a.radius }

def gChoose (a : RewindVM) : RewindVM :=
  { a with
      left := a.right
      center := a.right
      length := GalilScaffoldCounter.ofNat 1
      radius := GalilScaffoldCounter.reset }

theorem fppReset_unique {s t₁ t₂ : GalilVM}
    (h1 : (galilFrameS Pw qq firstT).fppReset s t₁)
    (h2 : (galilFrameS Pw qq firstT).fppReset s t₂) : t₁ = t₂ :=
  lens_rel_unique rewindLens (g := gReset) (fun a b h => h) h1 h2

theorem rewindOne_unique {s t₁ t₂ : GalilVM}
    (h1 : (galilFrameS Pw qq firstT).rewindOne s t₁)
    (h2 : (galilFrameS Pw qq firstT).rewindOne s t₂) : t₁ = t₂ :=
  lens_rel_unique rewindLens (g := gOne) (fun a b h => h.2) h1 h2

theorem rewindPair_unique {s t₁ t₂ : GalilVM}
    (h1 : (galilFrameS Pw qq firstT).rewindPair s t₁)
    (h2 : (galilFrameS Pw qq firstT).rewindPair s t₂) : t₁ = t₂ :=
  lens_rel_unique rewindLens (g := gPair) (fun a b h => h.2) h1 h2

theorem markBack_unique {s t₁ t₂ : GalilVM}
    (h1 : (galilFrameS Pw qq firstT).markBack s t₁)
    (h2 : (galilFrameS Pw qq firstT).markBack s t₂) : t₁ = t₂ :=
  lens_rel_unique rewindLens (g := gBack) (fun a b h => h.2) h1 h2

theorem choose_unique {s t₁ t₂ : GalilVM}
    (h1 : (galilFrameS Pw qq firstT).choose s t₁)
    (h2 : (galilFrameS Pw qq firstT).choose s t₂) : t₁ = t₂ :=
  lens_rel_unique rewindLens (g := gChoose) (fun a b h => h) h1 h2

/-- **The abstract tick is deterministic in `rewind` mode.** -/
theorem tick_det_rewind {s t₁ t₂ : State GalilVM} (hm : s.ctl.mode = .rewind)
    (h1 : Tick (galilFrameS Pw qq firstT) delay s t₁)
    (h2 : Tick (galilFrameS Pw qq firstT) delay s t₂) : t₁ = t₂ := by
  cases h1 <;> cases h2 <;> simp_all
  · exact fppReset_unique Pw qq firstT ‹_› ‹_›
  · exact rewindOne_unique Pw qq firstT ‹_› ‹_›
  · exact rewindPair_unique Pw qq firstT ‹_› ‹_›

/-- **The abstract tick is deterministic in `choose` mode.** -/
theorem tick_det_choose {s t₁ t₂ : State GalilVM} (hm : s.ctl.mode = .choose)
    (h1 : Tick (galilFrameS Pw qq firstT) delay s t₁)
    (h2 : Tick (galilFrameS Pw qq firstT) delay s t₂) : t₁ = t₂ := by
  cases h1 <;> cases h2 <;> simp_all
  · exact choose_unique Pw qq firstT ‹_› ‹_›
  · exact markBack_unique Pw qq firstT ‹_› ‹_›

#print axioms tick_det_rewind
#print axioms tick_det_choose

end Det


/-! ## 3. The `rewind` mode -/

/-- The local side conditions a `rewind` tick needs and `InvC` does not carry:
the phase is not replaying, the two counters it pushes are on the positive side
of the polarity bundle, and the idle half of the FPP double buffer is clear. -/
structure RewindWF (x : GalilVML P) : Prop where
  notReplaying : x.ctl.replaying = false
  polLength : x.pol .length = true
  polRadius : x.pol .radius = true
  clean : ∀ i, PalPeg.LocalBuffers.Cleared (PalPeg.LocalBuffers.idle x.fppBuf i)

open Classical in
/-- **The local `rewind` step.**  `LocalTick3`'s three rewind actions, selected
by the MARKS head and the `pair` flag; the left mirror follows the centre. -/
noncomputable def rewindStepC (Pw : Shared) (qq : ℕ) (firstT : Fin 9)
    (m : Mirrored1 P) : Mirrored1 P :=
  if (galilFrameS Pw qq firstT).atFirst (abs' m.vm) then
    mirrorTick1 .stay (rewindDoneVm { m.vm.ctl with mode := .replayStart } m.vm) m
  else if m.vm.ctl.pair = true then
    mirrorTick1 .left (rewindPairVm { m.vm.ctl with pair := false } m.vm) m
  else
    mirrorTick1 .stay (rewindOneVm { m.vm.ctl with pair := true } m.vm) m

/-- A `rewind` tick that is not at `FIRST` proves MARKS can still step left. -/
theorem marksLeft_of_rewind_tick {Pw : Shared} {qq : ℕ} {firstT : Fin 9} {delay : ℕ}
    {c : Control} {s : GalilVM} {t : State GalilVM} (hm : c.mode = .rewind)
    (hf : ¬ (galilFrameS Pw qq firstT).atFirst s)
    (h : Tick (galilFrameS Pw qq firstT) delay ⟨c, s⟩ t) : (marksOf s).left ≠ [] := by
  cases h <;> simp_all
  · exact ‹(galilFrameS Pw qq firstT).rewindOne s _›.1.1
  · exact ‹(galilFrameS Pw qq firstT).rewindPair s _›.1.1

/-- **The local `rewind` step is a scaffold tick.** -/
theorem tickL3_rewindStepC {Pw : Shared} {qq : ℕ} {firstT : Fin 9} {delay : ℕ}
    {m : Mirrored1 P} {t : State GalilVM} (hwf : RewindWF m.vm) (hmd : m.vm.ctl.mode = .rewind)
    (ht : Tick (galilFrameS Pw qq firstT) delay (absState'' m.vm) t) :
    TickL3 Pw qq firstT m.vm (rewindStepC Pw qq firstT m).vm := by
  classical
  have habs : absState'' m.vm = ⟨m.vm.ctl, abs' m.vm⟩ := absState''_eq hwf.notReplaying
  rw [habs] at ht
  unfold rewindStepC
  by_cases hf : (galilFrameS Pw qq firstT).atFirst (abs' m.vm)
  · rw [if_pos hf]
    exact .rewind_done m.vm hmd hwf.notReplaying hf hwf.clean
  · have hne := marksLeft_of_rewind_tick hmd hf ht
    rw [if_neg hf]
    by_cases hp : m.vm.ctl.pair = true
    · rw [if_pos hp]
      exact .rewind_pair m.vm hmd hwf.notReplaying hf hp hne hwf.polLength hwf.polRadius
    · rw [if_neg hp]
      exact .rewind_one m.vm hmd hwf.notReplaying hf (by simpa using hp) hne hwf.polLength

/-- The left mirror survives a `rewind` step. -/
theorem mirInv1_rewindStepC {Pw : Shared} {qq : ℕ} {firstT : Fin 9} {m : Mirrored1 P}
    (h : MirInv1 m) (hc : PalPeg.LocalInputView.WF m.vm.center) :
    MirInv1 (rewindStepC Pw qq firstT m) := by
  classical
  unfold rewindStepC
  by_cases hf : (galilFrameS Pw qq firstT).atFirst (abs' m.vm)
  · rw [if_pos hf]; exact PalPeg.LocalReplayParked.mirInv1_mirrorTick1 h hc .stay rfl
  · rw [if_neg hf]
    by_cases hp : m.vm.ctl.pair = true
    · rw [if_pos hp]; exact PalPeg.LocalReplayParked.mirInv1_mirrorTick1 h hc .left rfl
    · rw [if_neg hp]; exact PalPeg.LocalReplayParked.mirInv1_mirrorTick1 h hc .stay rfl

#print axioms tickL3_rewindStepC
#print axioms mirInv1_rewindStepC


/-- **The `rewind` obligation**, modulo the local side conditions `RewindWF`. -/
theorem realizes_rewind {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {Pw : Shared} {qq : ℕ} {firstT : Fin 9} {delay : ℕ}
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, k < lastTick → Tick (galilFrameS Pw qq firstT) delay (stOf k) (stOf (k+1)))
    (H_rewindWF : ∀ m : Mirrored1 P, InvC Good raw stOf m → m.vm.ctl.mode = .rewind → RewindWF m.vm) :
    Realizes (P := P) Good raw stOf lastTick (rewindStepC (P := P) Pw qq firstT) .rewind := by
  refine realizes_of_tick_det H_shared H_trace ?_ (tick_det_rewind Pw qq firstT delay)
  intro m t hinv hmd hns ht
  have htl := tickL3_rewindStepC (H_rewindWF m hinv hmd) hmd ht
  exact ⟨PalPeg.LocalTick3.tickL3_abs delay hinv.phys.inv htl,
    physWF_of_tickL3 hinv.phys htl, mirInv1_rewindStepC hinv.mir hinv.phys.inv.views.2.1⟩

/-! ## 4. The `choose` mode -/

/-- The local side conditions a `choose` tick needs.  `headsLeft`/`headsCenter`
are the parking invariant the selection relies on: `chooseVm` does not move the
heads, so L and C must already sit on R when the selection fires. -/
structure ChooseWF (x : GalilVML P) : Prop where
  notReplaying : x.ctl.replaying = false
  polLength : x.pol .length = true
  headsLeft : absHead' x.left x.pending = absHead' x.right x.pending
  headsCenter : absHead' x.center x.pending = absHead' x.right x.pending

open Classical in
/-- **The local `choose` step.** -/
noncomputable def chooseStepC (Pw : Shared) (qq : ℕ) (firstT : Fin 9)
    (m : Mirrored1 P) : Mirrored1 P :=
  if m.vm.ctl.odd = true ∧ (galilFrameS Pw qq firstT).markSet (abs' m.vm) then
    mirrorTick1 .stay (chooseVm { m.vm.ctl with mode := .rewind, pair := false } m.vm) m
  else
    mirrorTick1 .stay
      (marksVm GalilScaffoldTape.moveLeft { m.vm.ctl with odd := !m.vm.ctl.odd } m.vm) m

/-- A `choose` tick that does not select proves MARKS can still step left. -/
theorem marksLeft_of_choose_tick {Pw : Shared} {qq : ℕ} {firstT : Fin 9} {delay : ℕ}
    {c : Control} {s : GalilVM} {t : State GalilVM} (hm : c.mode = .choose)
    (hs : c.odd = false ∨ ¬ (galilFrameS Pw qq firstT).markSet s)
    (h : Tick (galilFrameS Pw qq firstT) delay ⟨c, s⟩ t) : (marksOf s).left ≠ [] := by
  cases h <;> simp_all
  exact ‹(galilFrameS Pw qq firstT).markBack s _›.1.1

/-- **The local `choose` step is a scaffold tick.** -/
theorem tickL3_chooseStepC {Pw : Shared} {qq : ℕ} {firstT : Fin 9} {delay : ℕ}
    {m : Mirrored1 P} {t : State GalilVM} (hwf : ChooseWF m.vm) (hmd : m.vm.ctl.mode = .choose)
    (ht : Tick (galilFrameS Pw qq firstT) delay (absState'' m.vm) t) :
    TickL3 Pw qq firstT m.vm (chooseStepC Pw qq firstT m).vm := by
  classical
  have habs : absState'' m.vm = ⟨m.vm.ctl, abs' m.vm⟩ := absState''_eq hwf.notReplaying
  rw [habs] at ht
  unfold chooseStepC
  by_cases hsel : m.vm.ctl.odd = true ∧ (galilFrameS Pw qq firstT).markSet (abs' m.vm)
  · rw [if_pos hsel]
    exact .choose_select m.vm hmd hwf.notReplaying hsel.1 hsel.2 hwf.polLength
      hwf.headsLeft hwf.headsCenter
  · have hs : m.vm.ctl.odd = false ∨ ¬ (galilFrameS Pw qq firstT).markSet (abs' m.vm) := by
      by_cases ho : m.vm.ctl.odd = true
      · exact Or.inr (fun hk => hsel ⟨ho, hk⟩)
      · exact Or.inl (by simpa using ho)
    rw [if_neg hsel]
    exact .choose_step m.vm hmd hwf.notReplaying hs (marksLeft_of_choose_tick hmd hs ht)

theorem mirInv1_chooseStepC {Pw : Shared} {qq : ℕ} {firstT : Fin 9} {m : Mirrored1 P}
    (h : MirInv1 m) (hc : PalPeg.LocalInputView.WF m.vm.center) :
    MirInv1 (chooseStepC Pw qq firstT m) := by
  classical
  unfold chooseStepC
  by_cases hsel : m.vm.ctl.odd = true ∧ (galilFrameS Pw qq firstT).markSet (abs' m.vm)
  · rw [if_pos hsel]; exact PalPeg.LocalReplayParked.mirInv1_mirrorTick1 h hc .stay rfl
  · rw [if_neg hsel]; exact PalPeg.LocalReplayParked.mirInv1_mirrorTick1 h hc .stay rfl

/-- **The `choose` obligation**, modulo the local side conditions `ChooseWF`. -/
theorem realizes_choose {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {Pw : Shared} {qq : ℕ} {firstT : Fin 9} {delay : ℕ}
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, k < lastTick → Tick (galilFrameS Pw qq firstT) delay (stOf k) (stOf (k+1)))
    (H_chooseWF : ∀ m : Mirrored1 P, InvC Good raw stOf m → m.vm.ctl.mode = .choose → ChooseWF m.vm) :
    Realizes (P := P) Good raw stOf lastTick (chooseStepC (P := P) Pw qq firstT) .choose := by
  refine realizes_of_tick_det H_shared H_trace ?_ (tick_det_choose Pw qq firstT delay)
  intro m t hinv hmd hns ht
  have htl := tickL3_chooseStepC (H_chooseWF m hinv hmd) hmd ht
  exact ⟨PalPeg.LocalTick3.tickL3_abs delay hinv.phys.inv htl,
    physWF_of_tickL3 hinv.phys htl, mirInv1_chooseStepC hinv.mir hinv.phys.inv.views.2.1⟩

#print axioms realizes_rewind
#print axioms realizes_choose


/-! ## 5. The `init` and `replayStart` modes

Both modes have a single `Tick` constructor, and their VM effect is an abstract
field of `Shared`.  Determinism therefore reduces, with no further assumption,
to **functionality of that field**; the output bit is pinned unconditionally
(`refresh_unique`).  What is left open is only the *local realization*. -/

/-- The output refresh determines the new output bit. -/
theorem refresh_unique {Pw : Shared} {qq : ℕ} {firstT : Fin 9} {s : GalilVM} {old o₁ o₂ : Bool}
    (h1 : refresh (galilFrameS Pw qq firstT) s old o₁)
    (h2 : refresh (galilFrameS Pw qq firstT) s old o₂) : o₁ = o₂ := by
  by_cases hl : (galilFrameS Pw qq firstT).onLetter s
  · have a1 := h1.1 hl
    have a2 := h2.1 hl
    cases o₁ <;> cases o₂ <;> simp_all
  · rw [h1.2 hl, h2.2 hl]

/-- **Determinism in `init` mode**, from functionality of `Pw.init`. -/
theorem tick_det_init {Pw : Shared} {qq : ℕ} {firstT : Fin 9} {delay : ℕ}
    (H_initFun : ∀ s t₁ t₂ : GalilVM, Pw.init s t₁ → Pw.init s t₂ → t₁ = t₂)
    {s t₁ t₂ : State GalilVM} (hm : s.ctl.mode = .init)
    (h1 : Tick (galilFrameS Pw qq firstT) delay s t₁)
    (h2 : Tick (galilFrameS Pw qq firstT) delay s t₂) : t₁ = t₂ := by
  cases h1 <;> cases h2 <;> simp_all
  exact H_initFun _ _ _ ‹_› ‹_›

/-- **Determinism in `replayStart` mode**, from functionality of `Pw.replayStart`. -/
theorem tick_det_replayStart {Pw : Shared} {qq : ℕ} {firstT : Fin 9} {delay : ℕ}
    (H_rsFun : ∀ s t₁ t₂ : GalilVM, Pw.replayStart s t₁ → Pw.replayStart s t₂ → t₁ = t₂)
    {s t₁ t₂ : State GalilVM} (hm : s.ctl.mode = .replayStart)
    (h1 : Tick (galilFrameS Pw qq firstT) delay s t₁)
    (h2 : Tick (galilFrameS Pw qq firstT) delay s t₂) : t₁ = t₂ := by
  cases h1 <;> cases h2 <;> simp_all
  rename_i cc sv s1 o1 hr1 hoa1 hob1 s2 o2 hm2 hoa2 hob2 hr2
  have hs : s1 = s2 := H_rsFun sv s1 s2 hr1 hr2
  subst hs
  refine ⟨⟨?_, rfl⟩, rfl⟩
  by_cases hp : (galilFrameS Pw qq firstT).replayPos s1 = true
  · rw [hoa1 hp, hoa2 hp]
  · have hp' : (galilFrameS Pw qq firstT).replayPos s1 = false := Bool.eq_false_iff.mpr hp
    exact refresh_unique (hob1 hp') (hob2 hp')

/-- **The `init` obligation**, reduced to the local realization `H_initLoc` and
functionality of `Pw.init`. -/
theorem realizes_init {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {Pw : Shared} {qq : ℕ} {firstT : Fin 9} {delay : ℕ} {f : Mirrored1 P → Mirrored1 P}
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, k < lastTick → Tick (galilFrameS Pw qq firstT) delay (stOf k) (stOf (k+1)))
    (H_initFun : ∀ s t₁ t₂ : GalilVM, Pw.init s t₁ → Pw.init s t₂ → t₁ = t₂)
    (H_initLoc : ∀ (m : Mirrored1 P) (t : State GalilVM), InvC Good raw stOf m →
      m.vm.ctl.mode = .init → ¬ Starved m.vm →
      Tick (galilFrameS Pw qq firstT) delay (absState'' m.vm) t →
      Tick (galilFrameS Pw qq firstT) delay (absState'' m.vm) (absState'' (f m).vm) ∧
        PhysWF (f m).vm ∧ MirInv1 (f m)) :
    Realizes (P := P) Good raw stOf lastTick f .init :=
  realizes_of_tick_det H_shared H_trace H_initLoc (tick_det_init H_initFun)

/-- **The `replayStart` obligation**, reduced to the local realization
`H_replayStartLoc` and functionality of `Pw.replayStart`. -/
theorem realizes_replayStart {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {Pw : Shared} {qq : ℕ} {firstT : Fin 9} {delay : ℕ} {f : Mirrored1 P → Mirrored1 P}
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, k < lastTick → Tick (galilFrameS Pw qq firstT) delay (stOf k) (stOf (k+1)))
    (H_rsFun : ∀ s t₁ t₂ : GalilVM, Pw.replayStart s t₁ → Pw.replayStart s t₂ → t₁ = t₂)
    (H_replayStartLoc : ∀ (m : Mirrored1 P) (t : State GalilVM), InvC Good raw stOf m →
      m.vm.ctl.mode = .replayStart → ¬ Starved m.vm →
      Tick (galilFrameS Pw qq firstT) delay (absState'' m.vm) t →
      Tick (galilFrameS Pw qq firstT) delay (absState'' m.vm) (absState'' (f m).vm) ∧
        PhysWF (f m).vm ∧ MirInv1 (f m)) :
    Realizes (P := P) Good raw stOf lastTick f .replayStart :=
  realizes_of_tick_det H_shared H_trace H_replayStartLoc (tick_det_replayStart H_rsFun)

/-! ## 6. The `scan` mode

A scan tick is the one mode whose abstract successor is *not* pinned by the
source state: `Tick.restart` competes with all five scan constructors, and the
`background`/`compare` blocks carry the relational `SafeQuanta`/`chainAt`.  Both
halves stay open.  What is closed here is the physical half of a non-replaying
scan tick, mirror included. -/

/-- No local scan tick moves the centre cursor. -/
theorem tickL1_center {S : Shared} {q : ℕ} {firstT : Fin 9} {d : ℕ} {x y : GalilVML P}
    (h : PalPeg.LocalTick1.TickL1 S q firstT d x y) : y.center = x.center := by
  cases h with
  | wait z ch hm hr hav hs hch =>
      exact (PalPeg.LocalTick1.bgState_center _ _ _ _).trans hs.frame.center
  | count z ch hm hav hc hs hch =>
      exact (PalPeg.LocalTick1.bgState_center _ _ _ _).trans hs.frame.center
  | «match» z ch o hm hav hc hpol hrep hper hahead hcan hs hmt hch ho =>
      exact (PalPeg.LocalTick1.birthL_center _ _).trans hs.frame.center

/-- **The physical half of a non-replaying scan tick**, mirror included. -/
theorem physWF_mir_of_tickL1 {S : Shared} {q : ℕ} {firstT : Fin 9} {d : ℕ}
    {m : Mirrored1 P} {y : GalilVML P} (hp : PhysWF m.vm) (hmir : MirInv1 m)
    (hr : m.vm.ctl.replaying = false) (ht : PalPeg.LocalTick1.TickL1 S q firstT d m.vm y) :
    PhysWF (mirrorTick1 .stay y m).vm ∧ MirInv1 (mirrorTick1 .stay y m) :=
  ⟨physWF_of_tickL1 hp hr ht,
    PalPeg.LocalReplayParked.mirInv1_mirrorTick1 hmir hp.inv.views.2.1 .stay (tickL1_center ht)⟩

/-- **The `scan` obligation**, reduced to its two open halves. -/
theorem realizes_scan {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {Pw : Shared} {qq : ℕ} {firstT : Fin 9} {delay : ℕ} {f : Mirrored1 P → Mirrored1 P}
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, k < lastTick → Tick (galilFrameS Pw qq firstT) delay (stOf k) (stOf (k+1)))
    (H_scanDet : ∀ {s t₁ t₂ : State GalilVM}, s.ctl.mode = .scan →
      Tick (galilFrameS Pw qq firstT) delay s t₁ →
      Tick (galilFrameS Pw qq firstT) delay s t₂ → t₁ = t₂)
    (H_scanLoc : ∀ (m : Mirrored1 P) (t : State GalilVM), InvC Good raw stOf m →
      m.vm.ctl.mode = .scan → ¬ Starved m.vm →
      Tick (galilFrameS Pw qq firstT) delay (absState'' m.vm) t →
      Tick (galilFrameS Pw qq firstT) delay (absState'' m.vm) (absState'' (f m).vm) ∧
        PhysWF (f m).vm ∧ MirInv1 (f m)) :
    Realizes (P := P) Good raw stOf lastTick f .scan :=
  realizes_of_tick_det H_shared H_trace H_scanLoc H_scanDet

#print axioms refresh_unique
#print axioms tick_det_init
#print axioms tick_det_replayStart
#print axioms realizes_init
#print axioms realizes_replayStart
#print axioms tickL1_center
#print axioms physWF_mir_of_tickL1
#print axioms realizes_scan

end PalPeg.LocalRealizesScan
