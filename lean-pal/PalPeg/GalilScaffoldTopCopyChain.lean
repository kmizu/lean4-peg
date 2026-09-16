import PalPeg.GalilScaffoldTopRewindChain

/-!
# The fallback chain: Copy → Home → Fpp, and the whole fallback

`fallback_prepared` runs the decoded `beginFallback` state through
`FppControl.Run` (copy the window, walk SOURCE home, start the program) in
`2|w|+3` enabled ticks. Lifted to the controller (`fpp_control_run_lift`),
pulled to the unified VM and transferred to `galilFrame`, it joins
`fpp_then_markEnd` and `choose_then_rewind` into one run from `copy` mode
to `replayStart` mode.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

/-- Copy/home/start on the merged frame: from `copy` mode with the decoded
`beginFallback` state, `2|w|+3` ticks reach `fpp` mode with the prepared
program running. -/
theorem copy_home_start (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (hm : c.mode = .copy) (s : GalilVM) (hi : ShiftIdle s)
    (old : GalilScaffoldControl.Machine 9) (p : GalilScaffoldPlace.Place)
    (length : GalilScaffoldCounter.Counter) (hc : GalilScaffoldCounter.Canonical length)
    (ℓ : ℕ) (hv : GalilScaffoldCounter.value length = ℓ)
    (hs : s.fpp = FppControl.beginFallback old p length) :
    let w := (GalilScaffoldPlace.stream p).take (ℓ+1)
    ∃ t : FppControl.State,
      Steps (galilFrame P q first) delay (2*w.length+3) ⟨c, s⟩ ⟨{c with mode := .fpp}, {s with fpp := t}⟩ ∧
      t.mode = .run ∧ t.program = ⟨fppInitial w, false⟩ ∧
      (t.finalStage = true ↔ (GalilScaffoldPlace.stream p).length ≤ ℓ+1) ∧
      ShiftIdle {s with fpp := t} := by
  intro w
  obtain ⟨t, hrun, hmode, hprog, hfin⟩ := FppControl.fallback_prepared old p length hc ℓ hv
  have hm' : c.mode = (FppControl.beginFallback old p length).mode.toController := by
    rw [hm]; rfl
  have hst := fpp_control_run_lift (fun _ => True) (fun _ => True) delay (2*w.length+3) c hm' hrun
  rw [hmode] at hst
  have hst' := steps_pull fppLens _ delay (2*w.length+3) c _ s t (by rw [show fppLens.get s = s.fpp from rfl, hs]; exact hst)
  obtain ⟨hg, hi'⟩ := steps_transfer_fallback P q first delay (2*w.length+3) (Or.inl hm) hi hst'
  exact ⟨t, hg, hmode, hprog, hfin, hi'⟩

/-- The whole fallback on the merged frame: from `copy` mode with the decoded
`beginFallback` state to `replayStart` mode, with L and C rewound to the
longest odd palindromic prefix of the reversed window (`r = chosenRadius w`),
`length = 2r+1`, `radius = r`, the FPP program reset. -/
theorem fallback_chain (P : Shared) (q : ℕ) (hq : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8)
    (delay : ℕ) (c : Control) (hm : c.mode = .copy) (s : GalilVM) (hi : ShiftIdle s)
    (old : GalilScaffoldControl.Machine 9) (p : GalilScaffoldPlace.Place)
    (length : GalilScaffoldCounter.Counter) (hc : GalilScaffoldCounter.Canonical length)
    (ℓ : ℕ) (hv : GalilScaffoldCounter.value length = ℓ)
    (hs : s.fpp = FppControl.beginFallback old p length)
    (hne : (GalilScaffoldPlace.stream p) ≠ [])
    (heven : ((GalilScaffoldPlace.stream p).take (ℓ+1)).length % 2 = 0) :
    let w := (GalilScaffoldPlace.stream p).take (ℓ+1)
    let r := chosenRadius w
    ∃ (n : ℕ) (y : RewindVM),
      Steps (galilFrame P q first) delay n ⟨c, s⟩
        ⟨{c with mode := .replayStart, odd := oddAt false (w.length - (2*r+1)), pair := pairAt (2*r)},
          rewindLens.set s y⟩ ∧
      y.left = GalilScaffoldInputHead.left^[2*r] s.right ∧
      y.center = GalilScaffoldInputHead.left^[r] s.right ∧ y.right = s.right ∧
      y.length = GalilScaffoldCounter.ofNat (2*r+1) ∧ y.radius = GalilScaffoldCounter.ofNat r ∧
      y.fpp.program = GalilScaffoldControl.reset 320 y.fpp.program ∧ ShiftIdle (rewindLens.set s y) := by
  intro w r
  have hw : 1 ≤ w.length := by
    show 1 ≤ ((GalilScaffoldPlace.stream p).take (ℓ+1)).length
    rw [List.length_take]
    have : 0 < (GalilScaffoldPlace.stream p).length := List.length_pos_iff.mpr hne
    omega
  obtain ⟨t, hg1, hmode, hprog, _, hi1⟩ := copy_home_start P q first delay c hm s hi old p length hc ℓ hv hs
  have hm1 : ({c with mode := .fpp} : Control).mode = .fpp := rfl
  obtain ⟨n2, y2, hg2, hden2, hhead2, _, _, _, _, hi2⟩ :=
    fpp_then_markEnd P q hq first delay {c with mode := .fpp} hm1 {s with fpp := t} hi1 hmode w hw hprog
  have hm2 : ({({c with mode := .fpp} : Control) with mode := .choose, odd := false} : Control).mode = .choose := rfl
  have ho2 : ({({c with mode := .fpp} : Control) with mode := .choose, odd := false} : Control).odd = false := rfl
  obtain ⟨y3, hg3, hl, hc3, hr3, hlen, hrad, hprog3, hi3⟩ :=
    choose_then_rewind P q first h7 h8 delay _ hm2 ho2 {({s with fpp := t} : GalilVM) with fpp := y2} hi2
      w hw heven r rfl hden2 hhead2
  exact ⟨_, y3, steps_trans hg1 (steps_trans hg2 hg3), hl, hc3, hr3, hlen, hrad, hprog3, hi3⟩

#print axioms fallback_chain

#print axioms copy_home_start

end PalPeg.GalilScaffoldChainInputSupply
