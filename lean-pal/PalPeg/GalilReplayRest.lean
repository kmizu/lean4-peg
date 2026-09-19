import PalPeg.GalilFrontier

/-!
# `ReplayRest` is an invariant

`PalPeg.GalilFrontier` states the coupling between the controller's
`replaying` flag and the VM's `replay` counter as an *assumption*:

```
ReplayRest c s := (c.replaying = false ∨ c.mode = Mode.init) → s.replay = reset
```

This module discharges it: `ReplayRest` holds at the initial controller (for a
VM whose replay counter starts empty) and is preserved by every constructor of
`Tick (galilFrameS (sharedC …) q first) delay`.

The two interesting branches are the ones that *write* the flag.

* `Tick.scan_match` sets `replaying := c.replaying && !replayExhausted t`.
  Since `sharedC`'s `replayExhausted` is `zero ·.replay`, the flag goes down
  exactly when the counter reads zero — and `zero c = true` forces
  `c = reset` outright (`eq_reset_of_zero`), *without* any canonicity side
  condition, because `zero` tests both stacks.
* `Tick.replayStart` sets `replaying := replayPos t = positive t.replay` with
  `t.replay = s.radius`.  Here `positive c = false` only says `c.pos = []`, so
  a counter carrying negative cells (`⟨[], [()]⟩`) would break the step.  This
  is the one branch that needs an extra fact about the state, and it is taken
  as the hypothesis `hrad` of `replayRest_tick`: at a `replayStart` the radius
  is a natural-number counter (`∃ r, s.radius = ofNat r`).  Note `Canonical`
  is *not* enough here (it is implied by `pos = []`), which is why the
  invariant is not stated as `ReplayRest ∧ Canonical replay`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

/-- `zero` tests *both* stacks, so a counter reading zero is literally `reset`.
No canonicity hypothesis is needed. -/
theorem eq_reset_of_zero {c : GalilScaffoldCounter.Counter}
    (h : GalilScaffoldCounter.zero c = true) : c = GalilScaffoldCounter.reset := by
  rcases c with ⟨ps, ns⟩
  simp only [GalilScaffoldCounter.zero, Bool.and_eq_true, List.isEmpty_iff] at h
  rw [h.1, h.2]
  rfl

/-- `reset` is canonical, so the invariant's conclusion carries canonicity for
free (kept for downstream users that want `Canonical s.replay`). -/
theorem canonical_of_replayRest {c : Control} {s : GalilVM} (h : ReplayRest c s)
    (hd : c.replaying = false ∨ c.mode = Mode.init) :
    GalilScaffoldCounter.Canonical s.replay := by
  rw [h hd]; exact Or.inl rfl

/-- The replay counter under a lens-pulled VM effect. -/
theorem replay_pull {σ' : Type} (L : Lens GalilVM σ') {s t : GalilVM}
    (h2 : t = L.set s (L.get t)) (hp : (L.set s (L.get t)).replay = s.replay) :
    t.replay = s.replay := (congrArg GalilVM.replay h2).trans hp

/-- Transport of the invariant along a tick that keeps the `replaying` flag,
never enters `init`, and keeps the replay counter. -/
theorem replayRest_of_eq {c c' : Control} {s t : GalilVM}
    (hrep : c'.replaying = c.replaying) (hmode : c'.mode = Mode.init → False)
    (ht : t.replay = s.replay) (h : ReplayRest c s) : ReplayRest c' t := by
  intro hd
  rw [ht]
  refine h ?_
  rcases hd with hd | hd
  · exact Or.inl (by rw [← hrep]; exact hd)
  · exact absurd hd hmode

/-- Trivially: a state with an empty replay counter satisfies the invariant
against any controller. -/
theorem replayRest_of_reset {c : Control} {s : GalilVM}
    (h : s.replay = GalilScaffoldCounter.reset) : ReplayRest c s := fun _ => h

/-- **Establishment.**  At the Scala initial controller `Control.initial delay`
(mode `init`, all flags off) the invariant says exactly that the machine boots
with an empty replay counter. -/
theorem replayRest_init (delay : ℕ) (s0 : GalilVM)
    (h0 : s0.replay = GalilScaffoldCounter.reset) : ReplayRest (initial delay) s0 :=
  replayRest_of_reset h0

/-- …and conversely, so the hypothesis on the boot state cannot be dropped:
`Control.initial` has `mode = init`, which triggers the invariant's premise. -/
theorem replayRest_init_iff (delay : ℕ) (s0 : GalilVM) :
    ReplayRest (initial delay) s0 ↔ s0.replay = GalilScaffoldCounter.reset :=
  ⟨fun h => h (Or.inr rfl), replayRest_of_reset⟩

/-- **Preservation.**  `ReplayRest` is an invariant of the online scaffold's
controller tick.

The single side condition `hrad` covers the `replayStart` branch, where the
flag is recomputed from `positive s.radius` rather than from `zero`. -/
theorem replayRest_tick (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM}
    (hrest : ReplayRest c s)
    (hrad : c.mode = Mode.replayStart → ∃ r, s.radius = GalilScaffoldCounter.ofNat r)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : ReplayRest c' t := by
  cases h
  case init =>
    rename_i hm hi
    have hi' : initVM entry s t := hi
    exact replayRest_of_reset (s := t) (hi'.2.2.2.2.2.2.1.trans (hrest (Or.inr hm)))
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, -, -, -, -, -, -, -, -, hpr, -, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion (hm.symm.trans hh)) hpr hrest
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, -, -, -, -, -, -, -, -, hpr, -, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion (hm.symm.trans hh)) hpr hrest
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨vs, vq, a, -, -, -, -, -, hteq⟩ :
      compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
    have hs'p : s'.replay = s.replay := by
      rw [hteq, GalilScaffoldChainInputSupply.afterBirth_replay]; cases a <;> rfl
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    intro hd
    have hmode : ¬ c.mode = Mode.init := fun hh => Mode.noConfusion (hm.symm.trans hh)
    have hflag : (c.replaying &&
        !(galilFrameS (sharedC onLetter leftFirst centre place entry) q first).replayExhausted t)
          = false := by
      rcases hd with hd | hd
      · exact hd
      · exact absurd hd hmode
    cases hcr : c.replaying with
    | false =>
      rw [hcr, if_neg (by simp)] at hpl'
      exact (congrArg GalilVM.replay hpl').trans (hs'p.trans (hrest (Or.inl hcr)))
    | true =>
      rw [hcr, Bool.true_and] at hflag
      have hex : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).replayExhausted t
          = true := by
        cases hx : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).replayExhausted t
        · rw [hx] at hflag; exact absurd hflag (by simp)
        · rfl
      have hz : GalilScaffoldCounter.zero t.replay = true := hex
      exact eq_reset_of_zero hz
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨vs, vq, a, -, -, -, -, -, hteq⟩ :
      compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
    have hs'p : s'.replay = s.replay := by
      rw [hteq, GalilScaffoldChainInputSupply.afterBirth_replay]; cases a <;> rfl
    obtain ⟨w, -, ht⟩ : beginShiftVM' s' t := hb
    exact replayRest_of_reset (s := t)
      (by rw [ht]; show s'.replay = _; rw [hs'p]; exact hrest (Or.inl hr))
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨vs, vq, a, -, -, -, -, -, hteq⟩ :
      compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
    have hs'p : s'.replay = s.replay := by
      rw [hteq, GalilScaffoldChainInputSupply.afterBirth_replay]; cases a <;> rfl
    obtain ⟨pl, ht, -⟩ : beginFallbackVM' s' t := hb
    exact replayRest_of_reset (s := t)
      (by rw [ht]; show s'.replay = _; rw [hs'p]; exact hrest (Or.inl hr))
  case shift_one =>
    rename_i hm hp hi
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion (hm.symm.trans hh))
      (replay_pull shiftLens hi.2 rfl) hrest
  case shift_done =>
    rename_i hm hp ho
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion hh) rfl hrest
  case copy_one =>
    rename_i hm hp hi
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion (hm.symm.trans hh))
      (replay_pull fppLens hi.2 rfl) hrest
  case copy_done =>
    rename_i hm hp hi
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion hh)
      (replay_pull fppLens hi.2 rfl) hrest
  case home_start =>
    rename_i hm hl hi
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion hh)
      (replay_pull fppLens hi.2 rfl) hrest
  case home_step =>
    rename_i hm hl hi
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion (hm.symm.trans hh))
      (replay_pull fppLens hi.2 rfl) hrest
  case fpp_slice =>
    rename_i hm hi
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion (hm.symm.trans hh))
      (replay_pull fppLens hi.2 rfl) hrest
  case fpp_done =>
    rename_i hm hi
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion hh)
      (replay_pull fppLens hi.2 rfl) hrest
  case markEnd_found =>
    rename_i hm he hi
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion hh)
      (replay_pull rewindLens hi.2 rfl) hrest
  case markEnd_step =>
    rename_i hm he hi
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion (hm.symm.trans hh))
      (replay_pull fppLens hi.2 rfl) hrest
  case choose_select =>
    rename_i hm hodd hs hi
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion hh)
      (replay_pull rewindLens hi.2 rfl) hrest
  case choose_step =>
    rename_i hm hs hi
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion (hm.symm.trans hh))
      (replay_pull rewindLens hi.2 rfl) hrest
  case rewind_done =>
    rename_i hm hfi hi
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion hh)
      (replay_pull rewindLens hi.2 rfl) hrest
  case rewind_one =>
    rename_i hm hpr hfi hi
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion (hm.symm.trans hh))
      (replay_pull rewindLens hi.2 rfl) hrest
  case rewind_pair =>
    rename_i hm hpr hfi hi
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion (hm.symm.trans hh))
      (replay_pull rewindLens hi.2 rfl) hrest
  case replayStart =>
    rename_i o hm ho ho' hi
    have hi' : replayStartVM entry s t := hi
    obtain ⟨r, hr⟩ := hrad hm
    have htr : t.replay = GalilScaffoldCounter.ofNat r := hi'.1.trans hr
    intro hd
    have hpos : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).replayPos t
        = false := by
      rcases hd with hd | hd
      · exact hd
      · exact absurd hd (fun hh => Mode.noConfusion hh)
    have hp : GalilScaffoldCounter.positive t.replay = false := hpos
    rw [htr, positive_ofNat] at hp
    have hr0 : r = 0 := by
      by_contra hne
      rw [decide_eq_false_iff_not] at hp
      exact hp (Nat.pos_of_ne_zero hne)
    rw [htr, hr0]
    rfl
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    exact replayRest_of_eq (c := c) rfl (fun hh => Mode.noConfusion (hm.symm.trans hh))
      (by rw [ht]) hrest

#print axioms eq_reset_of_zero
#print axioms canonical_of_replayRest
#print axioms replayRest_init
#print axioms replayRest_init_iff
#print axioms replayRest_tick

end PalPeg.GalilScaffoldChainInputSupply
