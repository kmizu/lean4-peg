import PalPeg.CloseoutRadPack3

/-!
# `H_verSane`, reduced to the shift entry

`CloseoutRadPack3.h_trailF_of_named` closes `H_trailF` from three named
hypotheses: `H_shiftEntry`, `H_leftLive` and `H_verSane`.  This file removes the
third one in favour of a hypothesis of the same shape as the first — a statement
about the *shift entry only*.

The observation is that `GalilFrontMono.Sane p := p.gap = true ∨ 0 < p.head.left.length`
is preserved by `GalilScaffoldChainVerifier.right` whenever `canRight p` holds
(`GalilFrontMono.right_sane`), and that **every right move of the chain verifier
is guarded by `canRight`**:

* `GalilScaffoldChainWatch.Internal.take` and `.Outer.immediate` carry
  `GalilScaffoldChainWatch.Good`, whose first component is literally
  `canRight s.machine.verifier`;
* `GalilScaffoldTopChainVM.BreakStep` carries `canRight` as its second component;
* every other `ChainStep` / `ChainMatched` constructor leaves the verifier where
  it was.

So the chain half of `Sane` travels along every chain tick unconditionally
(`chainTick_sane`), the fresh `chainStart` copies `s.center` (so `Sane C`, which
`CloseoutRadPack3.sanePack_trace'` already supplies from `H_leftLive`, is what it
needs), and along a whole tick of `galilFrameS` there is exactly **one** place
where a verifier move is not guarded: the shift entry `beginShiftVM`, which
applies `GalilScaffoldChainWatch.immediate` to the watching chain *without* a
`Good` premise (the shift guard `shiftGuardVM` constrains `s.right` and the
period tape, not the chain verifier's own FIFO).

That single residual is named here as `H_shiftVerSane`, at the exact shape
`saneTick` consumes and at the same trace points as `H_shiftEntry`.  Everything
else is proved.

## The named residual

* `H_shiftVerSane centre place entry q first` — **NAMED**:
  `∀ w, 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
   ∀ i ≤ Tc w.length, ∀ s'' t'' : GalilVM,
     (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
     beginShiftVM' s'' t'' → SaneVer t''.chain`.
  Its intended proof is `canRight` of the watching verifier at a shift entry,
  which on the real machine follows from the chain coupling (`position ver + lag
  = position R` with `R` still able to move) — the same coupling `H_shiftEntry`
  needs, and not available as a trace-level fact today.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutRadPack4

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.GalilTrailChain PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2
open PalPeg.CloseoutRadPack3
open PalPeg.GalilRunSkeleton
open GalilScaffoldInputHead

/-! ## 1. Saneness of the chain verifier, as a predicate on the chain -/

/-- The `sane` field of `GalilTrailChain.ChainBudget`, on its own. -/
def SaneVer (x : ChainVM) : Prop :=
  ∀ p, verOf x = some p → GalilFrontMono.Sane p

theorem saneVer_idle : SaneVer .idle := fun p hp => absurd hp (by simp [verOf])

theorem saneVer_congr {x z : ChainVM} (h : z = x) (hx : SaneVer x) : SaneVer z := h ▸ hx

/-- A guarded right move keeps `Sane`. -/
theorem sane_right {p : PH} (hs : GalilFrontMono.Sane p)
    (hc : GalilScaffoldChainVerifier.canRight p) :
    GalilFrontMono.Sane (GalilScaffoldChainVerifier.right p) :=
  (GalilFrontMono.right_sane hc hs).2

/-! ## 2. One chain tick -/

theorem chainStep_sane {x y : ChainVM} (h : ChainStep x y) (hx : SaneVer x) : SaneVer y := by
  cases h with
  | watchStep w w' ht =>
    cases ht with
    | idle hz => exact hx
    | take hp hg =>
      intro r hr
      obtain rfl : (GalilScaffoldChainVerifier.right w.machine.verifier) = r :=
        Option.some.inj hr
      exact sane_right (hx _ rfl) hg.1
  | watchBreak w w' hb =>
    have hcan := hb.2.1
    obtain ⟨-, -, -, -, -, ht⟩ := hb
    subst ht
    intro r hr
    obtain rfl : (GalilScaffoldChainVerifier.right w.machine.verifier) = r :=
      Option.some.inj hr
    exact sane_right (hx _ rfl) hcan
  | _ => exact fun r hr => hx r hr

theorem chainMatched_sane {y z : ChainVM} (h : ChainMatched y z) (hy : SaneVer y) : SaneVer z := by
  cases h with
  | watch w w' ho =>
    cases ho with
    | queued hz => exact fun r hr => hy r hr
    | immediate hz hg =>
      intro r hr
      obtain rfl : (GalilScaffoldChainVerifier.right w.machine.verifier) = r :=
        Option.some.inj hr
      exact sane_right (hy _ rfl) hg.1
  | breaks w w' hb =>
    obtain ⟨-, hc, a, -, -, ht⟩ := hb
    subst ht
    intro r hr
    obtain rfl : (GalilScaffoldChainVerifier.right w.machine.verifier) = r := Option.some.inj hr
    exact sane_right (hy _ rfl) hc
  | _ => exact fun r hr => hy r hr

theorem chainTick_sane {b : Bool} {x z : ChainVM} (ht : ChainTick b x z) (hx : SaneVer x) :
    SaneVer z := by
  obtain ⟨y, hs, hm⟩ := ht
  cases b with
  | false =>
    simp only [Bool.false_eq_true, if_false] at hm
    subst hm
    exact chainStep_sane hs hx
  | true =>
    simp only [if_true] at hm
    exact chainMatched_sane hm (chainStep_sane hs hx)

/-- `chainStart` copies the given place into the verifier. -/
theorem saneVer_chainStart (answer : GalilScaffoldTape.Tape) (c : Fin 3)
    (walker : GalilScaffoldPlace.Place) (ver : PH) (radius : GalilScaffoldCounter.Counter)
    (h : GalilFrontMono.Sane ver) : SaneVer (chainStart answer c walker ver radius) := by
  intro p hp
  obtain rfl : ver = p := Option.some.inj hp
  exact h

theorem chainAt_sane {b found : Bool} {ans : GalilScaffoldTape.Tape} {c : Fin 3}
    {wk : GalilScaffoldPlace.Place} {ver : PH} {r : GalilScaffoldCounter.Counter}
    {x z : ChainVM} (h : chainAt b found ans c wk ver r x z) (hx : SaneVer x)
    (hv : GalilFrontMono.Sane ver) : SaneVer z := by
  rcases h with ⟨-, ht⟩ | ⟨-, -, rfl⟩ | ⟨-, -, hz⟩
  · exact chainTick_sane ht hx
  · exact saneVer_idle
  · cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false] at hz
      subst hz
      exact saneVer_chainStart ans c wk ver r hv
    | true =>
      simp only [if_true] at hz
      exact chainMatched_sane hz (saneVer_chainStart ans c wk ver r hv)

/-! ## 3. One tick of `galilFrameS` -/

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- **`saneTick`.**  The chain verifier stays sane along every tick, given
saneness of `C` (what a fresh `chainStart` copies) and the shift-entry residual.
The case split is that of `GalilTrailChain.trailChain_scanTick`. -/
theorem saneTick {c c' : Control} {s t : GalilVM}
    (hx : SaneVer s.chain) (hC : GalilFrontMono.Sane s.center)
    (hen : ∀ s'' t'' : GalilVM,
      (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s'' →
      beginShiftVM' s'' t'' → SaneVer t''.chain)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : SaneVer t.chain := by
  cases h
  case init =>
    rename_i hm hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s t := hi
    exact saneVer_congr hch saneVer_idle
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, -, hch, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact chainAt_sane hch hx hC
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, -, hch, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact chainAt_sane hch hx hC
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    exact saneVer_idle
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨a, found, ans, cc, wk, hch, -⟩ :=
      compare_chainAt onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have htc : t.chain = s'.chain := by rw [hpl']; cases c.replaying <;> rfl
    exact saneVer_congr htc (chainAt_sane hch hx hC)
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    exact hen s' t hcmp hb
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨pl, ht⟩ : beginFallbackVM' s' t := hb
    subst ht
    exact saneVer_idle
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨-, -, -, w, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    have hws : s.chain = .watch w := hw
    exact fun r hr => hx r (by rw [hws]; exact hr)
  case shift_done =>
    rename_i o hm hp ho
    exact hx
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : replayStartVM entry s t := hi
    exact saneVer_congr hch saneVer_idle
  all_goals
    (rename_i hi
     have hch : t.chain = s.chain := (congrArg GalilVM.chain hi.2).trans rfl
     exact saneVer_congr hch hx)

end Tick

#print axioms chainStep_sane
#print axioms chainMatched_sane
#print axioms chainTick_sane
#print axioms chainAt_sane
#print axioms saneTick

/-! ## 4. The named residual, and `H_verSane` -/

section Trace
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the shift-entry saneness of the chain verifier.**  The one place
in a tick where the verifier moves right without a `canRight` guard in the
premises: `beginShiftVM` applies `GalilScaffoldChainWatch.immediate` to the
watching chain, and `shiftGuardVM` constrains `s.right` and the period tape, not
the verifier's own FIFO. -/
def H_shiftVerSane : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' → SaneVer t''.chain

/-- **`H_verSane` from `H_leftLive` and the shift-entry residual.**  `Sane C`
comes from `CloseoutRadPack3.sanePack_trace'`; the boot chain is idle. -/
theorem h_verSane_of_shift (hll : H_leftLive centre place entry q first)
    (hsv : H_shiftVerSane centre place entry q first) :
    H_verSane centre place entry q first := by
  intro w hw st Tc hP i
  have hsane := sanePack_trace' centre place entry q first hll hw hP
  induction i with
  | zero =>
    intro _
    rw [hP.start]
    exact saneVer_idle
  | succ i ih =>
    intro hi
    have hlt : i < Tc w.length := by omega
    have hle : i ≤ Tc w.length := by omega
    exact saneTick (onLetterVM w) leftFirstVM centre place entry q first 2048
      (ih hle) (hsane i hle).saneC
      (fun s'' t'' hcmp hb => hsv w hw st Tc hP i hle s'' t'' hcmp hb)
      (hP.trace.tick i hlt)

/-- **`H_trailF` from `H_shiftEntry`, `H_leftLive` and `H_shiftVerSane`.** -/
theorem h_trailF_of_named' (hen : H_shiftEntry centre place entry q first)
    (hll : H_leftLive centre place entry q first)
    (hsv : H_shiftVerSane centre place entry q first)
    (hnb : PalPeg.CloseoutRadPack2.H_noBgBreak centre place entry q first) :
    H_trailF centre place entry q first :=
  h_trailF_of_named centre place entry q first hen hll
    (h_verSane_of_shift centre place entry q first hll hsv) hnb

end Trace

#print axioms h_verSane_of_shift
#print axioms h_trailF_of_named'

/-- **The concrete instance** at `centreC` / `placeC`. -/
theorem h_trailF_C' (entry q : ℕ) (first : Fin 9)
    (hen : H_shiftEntry PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hll : H_leftLive PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hsv : H_shiftVerSane PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hnb : PalPeg.CloseoutRadPack2.H_noBgBreak PalPeg.GalilFinalAssembly2.centreC
      PalPeg.GalilFinalAssembly2.placeC entry q first) :
    H_trailF PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC entry q first :=
  h_trailF_of_named' _ _ entry q first hen hll hsv hnb

#print axioms h_trailF_C'

end PalPeg.CloseoutRadPack4
