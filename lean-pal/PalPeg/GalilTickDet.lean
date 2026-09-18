import PalPeg.LocalSysConcrete
import PalPeg.GalilSharedFunctional
import PalPeg.GalilFrontier
import PalPeg.GalilRunSkeleton

/-!
# Is the abstract `Tick` functional for the concrete `sharedC` / `PofC`?

**Answer: no.**  Three of the five sources of nondeterminism are genuinely
open at the *concrete* shared record, and two of them are settled here by
exhibiting the two distinct successors.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace PalPeg.GalilTickDet

open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (positive zero negative)

/-! ## (c) The chain layer is functional, unconditionally -/

theorem internal_unique {s t₁ t₂ : GalilScaffoldChainWatch.State}
    (h1 : GalilScaffoldChainWatch.Internal s t₁)
    (h2 : GalilScaffoldChainWatch.Internal s t₂) : t₁ = t₂ := by
  cases h1 <;> cases h2 <;> simp_all

theorem outer_unique {s t₁ t₂ : GalilScaffoldChainWatch.State} {b : Bool}
    (h1 : GalilScaffoldChainWatch.Outer s b t₁)
    (h2 : GalilScaffoldChainWatch.Outer s b t₂) : t₁ = t₂ := by
  cases h1 <;> cases h2 <;> simp_all

theorem chainStep_unique {x z₁ z₂ : ChainVM} (h1 : ChainStep x z₁) (h2 : ChainStep x z₂) :
    z₁ = z₂ := by
  cases h1 with
  | idle => cases h2 with | idle => rfl
  | brokenIdle w => cases h2 with | brokenIdle w => rfl
  | copyBit t h p v lag margin ver a one legal present =>
      cases h2 with
      | copyBit _ _ _ _ _ _ _ a' one' legal' present' =>
          have hab : some a' = some a := present'.symm.trans present
          rw [Option.some.injEq] at hab
          subst hab
          rfl
      | copyEnd _ _ _ _ _ _ _ b hleft hp hv =>
          rw [one] at hleft; exact absurd hleft (by decide)
  | copyEnd t h p v lag margin ver b hleft hp hv =>
      cases h2 with
      | copyBit _ _ _ _ _ _ _ a' one' legal' present' =>
          rw [one'] at hleft; exact absurd hleft (by decide)
      | copyEnd _ _ _ _ _ _ _ b' hleft' hp' hv' =>
          have hab : GalilScaffoldChainPeriod.Token.plain b' = .plain b := hv'.symm.trans hv
          injection hab with hab
          subst hab
          rfl
  | backStep v h lag margin ver hf =>
      cases h2 with
      | backStep _ _ _ _ _ hf' => rfl
      | backDone _ _ _ _ _ hf' => rw [hf] at hf'; exact absurd hf' (by decide)
  | backDone v h lag margin ver hf =>
      cases h2 with
      | backStep _ _ _ _ _ hf' => rw [hf] at hf'; exact absurd hf' (by decide)
      | backDone _ _ _ _ _ hf' => rfl
  | watchStep w w' ht =>
      cases h2 with
      | watchStep _ w'' ht' => rw [internal_unique ht ht']

/-- `Good` and `BreakStep` read the same period symbol with opposite verdicts. -/
theorem not_good_of_break {w w' : GalilScaffoldChainWatch.State}
    (hb : BreakStep w w') : ¬ GalilScaffoldChainWatch.Good w := by
  rintro ⟨-, a, hsym, hread⟩
  obtain ⟨-, -, b, hsym', hread', -⟩ := hb
  have hab : some b = some a := hsym'.symm.trans hsym
  rw [Option.some.injEq] at hab
  subst hab
  exact hread' hread

theorem outer_true_break_absurd {w w₁ w₂ : GalilScaffoldChainWatch.State}
    (ho : GalilScaffoldChainWatch.Outer w true w₁) (hb : BreakStep w w₂) : False := by
  cases ho with
  | queued hz => rw [hb.1] at hz; exact absurd hz (by decide)
  | immediate hz hg => exact not_good_of_break hb hg

theorem chainMatched_unique {x z₁ z₂ : ChainVM} (h1 : ChainMatched x z₁)
    (h2 : ChainMatched x z₂) : z₁ = z₂ := by
  cases h1 with
  | idle => cases h2 with | idle => rfl
  | copy t h p v lag margin ver => cases h2 with | copy _ _ _ _ _ _ _ => rfl
  | back v h lag margin ver => cases h2 with | back _ _ _ _ _ => rfl
  | watch w w' ho =>
      cases h2 with
      | watch _ w'' ho' => rw [outer_unique ho ho']
      | breaks _ w'' hb => exact (outer_true_break_absurd ho hb).elim
  | breaks w w' hb =>
      cases h2 with
      | watch _ w'' ho => exact (outer_true_break_absurd ho hb).elim
      | breaks _ w'' hb' =>
          obtain ⟨-, -, a, -, -, he⟩ := hb
          obtain ⟨-, -, a', -, -, he'⟩ := hb'
          rw [he, he']

theorem chainTick_unique {a : Bool} {x z₁ z₂ : ChainVM} (h1 : ChainTick a x z₁)
    (h2 : ChainTick a x z₂) : z₁ = z₂ := by
  obtain ⟨y₁, hs₁, hm₁⟩ := h1
  obtain ⟨y₂, hs₂, hm₂⟩ := h2
  have hy : y₁ = y₂ := chainStep_unique hs₁ hs₂
  subst hy
  cases a
  · simp only [Bool.false_eq_true, if_false] at hm₁ hm₂
    rw [hm₁, hm₂]
  · simp only [if_true] at hm₁ hm₂
    exact chainMatched_unique hm₁ hm₂

/-- **(c) `chainAt` is a function of its source.** -/
theorem chainAt_unique {a found : Bool} {ans : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : GalilScaffoldInputHead.PlaceHead}
    {radius : GalilScaffoldCounter.Counter} {x z₁ z₂ : ChainVM}
    (h1 : chainAt a found ans cc walker ver radius x z₁)
    (h2 : chainAt a found ans cc walker ver radius x z₂) : z₁ = z₂ := by
  rcases h1 with ⟨hne, ht⟩ | ⟨hi, hf, hz⟩ | ⟨hi, hf, hz⟩ <;>
    rcases h2 with ⟨hne', ht'⟩ | ⟨hi', hf', hz'⟩ | ⟨hi', hf', hz'⟩
  · exact chainTick_unique ht ht'
  · exact absurd hi' hne
  · exact absurd hi' hne
  · exact absurd hi hne'
  · rw [hz, hz']
  · rw [hf] at hf'; exact absurd hf' (by decide)
  · exact absurd hi hne'
  · rw [hf] at hf'; exact absurd hf' (by decide)
  · cases a
    · simp only [Bool.false_eq_true, if_false] at hz hz'
      rw [hz, hz']
    · simp only [if_true] at hz hz'
      exact chainMatched_unique hz hz'

#print axioms internal_unique
#print axioms chainStep_unique
#print axioms chainMatched_unique
#print axioms chainAt_unique

/-! ## (e) `Pw.init` and `Pw.replayStart` are **not** functional at `sharedC`

`initVM`/`replayStartVM` constrain 13 of the 15 `GalilVM` fields; `periodOnly`
and `walker` are left free, so both relations have two successors from every
source. -/

theorem initVM_not_unique (entry : ℕ) {s t : GalilVM} (h : initVM entry s t) :
    initVM entry s { t with periodOnly := !t.periodOnly } ∧
      t ≠ { t with periodOnly := !t.periodOnly } := by
  refine ⟨h, ?_⟩
  intro he
  have hb : t.periodOnly = !t.periodOnly := congrArg GalilVM.periodOnly he
  cases hp : t.periodOnly <;> rw [hp] at hb <;> exact absurd hb (by decide)

theorem replayStartVM_not_unique (entry : ℕ) {s t : GalilVM} (h : replayStartVM entry s t) :
    replayStartVM entry s { t with periodOnly := !t.periodOnly } ∧
      t ≠ { t with periodOnly := !t.periodOnly } := by
  refine ⟨h, ?_⟩
  intro he
  have hb : t.periodOnly = !t.periodOnly := congrArg GalilVM.periodOnly he
  cases hp : t.periodOnly <;> rw [hp] at hb <;> exact absurd hb (by decide)

/-- **`init` mode is nondeterministic at the concrete shared record.** -/
theorem tick_init_not_det (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)
    (c : Control) (hm : c.mode = .init) {s t : GalilVM} (h : initVM entry s t) :
    Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay ⟨c, s⟩
        ⟨{ c with mode := .scan, output := true }, t⟩ ∧
      Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay ⟨c, s⟩
        ⟨{ c with mode := .scan, output := true }, { t with periodOnly := !t.periodOnly }⟩ ∧
      (⟨{ c with mode := .scan, output := true }, t⟩ : State GalilVM) ≠
        ⟨{ c with mode := .scan, output := true }, { t with periodOnly := !t.periodOnly }⟩ := by
  obtain ⟨h2, hne⟩ := initVM_not_unique entry h
  refine ⟨.init c s t hm h, .init c s _ hm h2, ?_⟩
  intro he
  exact hne (congrArg State.vm he)

/-- Every abstract `replayStart` effect really is taken by a tick. -/
theorem replayStart_tick_of (Pw : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (hm : c.mode = .replayStart) {s t : GalilVM} (h : Pw.replayStart s t) :
    ∃ o : Bool, Tick (galilFrameS Pw q first) delay ⟨c, s⟩
      ⟨{ c with mode := .scan, clock := delay, output := o, replaying := Pw.replayPos t }, t⟩ := by
  classical
  by_cases hp : Pw.replayPos t = true
  · exact ⟨c.output, .replayStart c s t c.output hm h (fun _ => rfl)
      (fun h0 => absurd (hp.symm.trans h0) (by simp))⟩
  · have hp' : Pw.replayPos t = false := Bool.eq_false_iff.mpr hp
    refine ⟨if Pw.onLetter t then decide (Pw.leftFirst t) else c.output,
      .replayStart c s t _ hm h (fun h0 => absurd (hp'.symm.trans h0) (by simp)) (fun _ => ?_)⟩
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : Pw.onLetter t := hl
      show (if Pw.onLetter t then decide (Pw.leftFirst t) else c.output) = true ↔ Pw.leftFirst t
      rw [if_pos hl']
      exact decide_eq_true_iff
    · have hl' : ¬ Pw.onLetter t := hl
      show (if Pw.onLetter t then decide (Pw.leftFirst t) else c.output) = c.output
      rw [if_neg hl']

/-- **`replayStart` mode is nondeterministic at the concrete shared record.** -/
theorem tick_replayStart_not_det (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)
    (c : Control) (hm : c.mode = .replayStart) {s t : GalilVM} (h : replayStartVM entry s t) :
    ∃ y₁ y₂ : State GalilVM,
      Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
          ⟨c, s⟩ y₁ ∧
        Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
          ⟨c, s⟩ y₂ ∧ y₁ ≠ y₂ := by
  obtain ⟨h2, hne⟩ := replayStartVM_not_unique entry h
  obtain ⟨o₁, ht₁⟩ := replayStart_tick_of (sharedC onLetter leftFirst centre place entry) q first
    delay c hm h
  obtain ⟨o₂, ht₂⟩ := replayStart_tick_of (sharedC onLetter leftFirst centre place entry) q first
    delay c hm h2
  exact ⟨_, _, ht₁, ht₂, fun he => hne (congrArg State.vm he)⟩

/-! ## (a) `Tick.restart` overlaps the scan constructors

A chain in `broken` can take `ChainStep.brokenIdle`, so `backgroundS` has the
stutter `s → s`; the restart guard is satisfiable at exactly such a state, and
the restart goes to `chain = .idle`.  Hence two distinct successors. -/

theorem backgroundS_stutter (Pw : Shared) (qq : ℕ) (firstT : Fin 9) {s : GalilVM}
    (hne : s.chain ≠ .idle) (hst : ChainStep s.chain s.chain) :
    (galilFrameS Pw qq firstT).background s s := by
  refine ⟨rfl, rfl, Or.inr ⟨hne, rfl⟩, Or.inl ⟨hne, ⟨s.chain, hst, ?_⟩⟩, ?_⟩
  · simp
  · rw [afterBirth_of_ne_idle hne]
    rfl

/-- **(a) The scan mode is nondeterministic whenever a restart is enabled.** -/
theorem scan_restart_not_det (Pw : Shared) (qq : ℕ) (firstT : Fin 9) (delay : ℕ)
    {c : Control} {s t : GalilVM} {w : GalilScaffoldChainWatch.State}
    (hm : c.mode = .scan) (hr : c.replaying = false)
    (hav : ¬ (galilFrameS Pw qq firstT).available s)
    (hbk : s.chain = ChainVM.broken w)
    (hrs : (galilFrameS Pw qq firstT).restart s t) (hti : t.chain = ChainVM.idle) :
    Tick (galilFrameS Pw qq firstT) delay ⟨c, s⟩ ⟨c, s⟩ ∧
      Tick (galilFrameS Pw qq firstT) delay ⟨c, s⟩ ⟨{ c with clock := delay }, t⟩ ∧
      (⟨c, s⟩ : State GalilVM) ≠ ⟨{ c with clock := delay }, t⟩ := by
  have hne : s.chain ≠ ChainVM.idle := by rw [hbk]; exact fun h => ChainVM.noConfusion h
  have hst : ChainStep s.chain s.chain := by rw [hbk]; exact .brokenIdle w
  refine ⟨.scan_wait c s s hm ⟨hr, hav⟩ (backgroundS_stutter Pw qq firstT hne hst),
    .restart c s t hm hrs, ?_⟩
  intro he
  have hst' : s = t := congrArg State.vm he
  rw [hst', hti] at hbk
  exact ChainVM.noConfusion hbk

/-- The same at `sharedC`, where the restart guard delivers `hrs`/`hti`. -/
theorem scan_restart_not_det_sharedC (onLetter leftFirst : GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (delay : ℕ)
    {c : Control} {s : GalilVM} {w : GalilScaffoldChainWatch.State}
    (hm : c.mode = .scan) (hr : c.replaying = false)
    (hav : ¬ (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).available s)
    (hbk : s.chain = ChainVM.broken w) (hmg : negative w.margin = false)
    (hlast : positive w.machine.control.last = true) (hlag : zero w.lag = true) :
    ∃ t : GalilVM,
      Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
          ⟨c, s⟩ ⟨c, s⟩ ∧
        Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
          ⟨c, s⟩ ⟨{ c with clock := delay }, t⟩ ∧
        (⟨c, s⟩ : State GalilVM) ≠ ⟨{ c with clock := delay }, t⟩ :=
  ⟨_, scan_restart_not_det _ q first delay hm hr hav hbk ⟨w, hbk, hmg, hlast, hlag, rfl⟩ rfl⟩

/-! ## (b) The DP program and the search quantum

`GalilScaffoldProgram.Execute` is functional **iff** every `read` dispatch table
in the code is single-valued — the `read` constructor picks any `pc` paired with
the focus symbol.  That is a decidable property of `GalilDpCode.code`, kept as
the named hypothesis `ReadFun`; everything above it is then deterministic. -/

/-- The code's `read` dispatch tables are single-valued. -/
def ReadFun {n : ℕ} (code : List (GalilFppWide.Instruction n)) : Prop :=
  ∀ t : Fin n, ∀ cs : List (Fin 9 × ℕ), GalilFppWide.Instruction.read t cs ∈ code →
    ∀ (f : Fin 9) (p₁ p₂ : ℕ), (f, p₁) ∈ cs → (f, p₂) ∈ cs → p₁ = p₂

theorem mem_of_getElem? {n : ℕ} {code : List (GalilFppWide.Instruction n)} {k : ℕ}
    {i : GalilFppWide.Instruction n} (h : code[k]? = some i) : i ∈ code := by
  rw [List.getElem?_eq_some_iff] at h
  obtain ⟨hk, he⟩ := h
  exact he ▸ List.getElem_mem hk

theorem execute_unique {n : ℕ} {code : List (GalilFppWide.Instruction n)} (hrf : ReadFun code)
    {x y₁ y₂ : GalilScaffoldProgram.Config n} {i : GalilFppWide.Instruction n}
    (hi : code[x.pc]? = some i)
    (h1 : GalilScaffoldProgram.Execute i x y₁) (h2 : GalilScaffoldProgram.Execute i x y₂) :
    y₁ = y₂ := by
  cases h1 with
  | right _ t pc => cases h2 with | right _ _ _ => rfl
  | left _ t pc hl => cases h2 with | left _ _ _ _ => rfl
  | write _ t s pc => cases h2 with | write _ _ _ _ => rfl
  | read _ t cs pc hmem =>
      cases h2 with
      | read _ _ _ pc' hmem' =>
          have := hrf t cs (mem_of_getElem? hi) (x.tapes t).focus pc pc' hmem hmem'
          subst this
          rfl

theorem progTick_unique {n : ℕ} {code : List (GalilFppWide.Instruction n)} (hrf : ReadFun code)
    {b : Bool} {x y₁ y₂ : GalilScaffoldControl.Machine n}
    (h1 : GalilScaffoldControl.Tick code b x y₁)
    (h2 : GalilScaffoldControl.Tick code b x y₂) : y₁ = y₂ := by
  cases h1 with
  | idle _ _ hd =>
      cases h2 with
      | idle => rfl
      | halt cfg hi => rcases hd with hb | hb <;> exact absurd hb (by simp)
      | execute cfg y i hi he => rcases hd with hb | hb <;> exact absurd hb (by simp)
  | halt cfg hi =>
      cases h2 with
      | idle _ _ hd => rcases hd with hb | hb <;> exact absurd hb (by simp)
      | halt _ _ => rfl
      | execute _ y i hi' he =>
          have : i = GalilFppWide.Instruction.halt := by
            have h := hi'.symm.trans hi
            rw [Option.some.injEq] at h
            exact h
          subst this
          cases he
  | execute cfg y i hi he =>
      cases h2 with
      | idle _ _ hd => rcases hd with hb | hb <;> exact absurd hb (by simp)
      | halt _ hi' =>
          have : i = GalilFppWide.Instruction.halt := by
            have h := hi.symm.trans hi'
            rw [Option.some.injEq] at h
            exact h
          subst this
          cases he
      | execute _ y' i' hi' he' =>
          have hii : i' = i := by
            have h := hi'.symm.trans hi
            rw [Option.some.injEq] at h
            exact h
          subst hii
          have : y = y' := execute_unique hrf hi he he'
          rw [this]

theorem safeCalls_unique (hrf : ReadFun GalilDpCode.code)
    {s : GalilScaffoldSearchFinish.State} {x : GalilScaffoldControl.Machine 12} {bs : List Bool}
    {t₁ t₂ : GalilScaffoldSearchFinish.State} {y₁ y₂ : GalilScaffoldControl.Machine 12}
    (h1 : GalilScaffoldSearchRun.SafeCalls s x bs t₁ y₁)
    (h2 : GalilScaffoldSearchRun.SafeCalls s x bs t₂ y₂) : t₁ = t₂ ∧ y₁ = y₂ := by
  induction h1 generalizing t₂ y₂ with
  | nil s x => cases h2 with | nil => exact ⟨rfl, rfl⟩
  | cons s x y z b bs t ht hsafe hr ih =>
      cases h2 with
      | cons _ _ y' _ _ _ t' ht' hsafe' hr' =>
          have hy : y = y' := progTick_unique hrf ht ht'
          subst hy
          exact ih hr'

theorem safeQuanta_unique (hrf : ReadFun GalilDpCode.code)
    {s : GalilScaffoldSearchFinish.State} {x : GalilScaffoldControl.Machine 12} {bs : List Bool}
    {t₁ t₂ : GalilScaffoldSearchFinish.State} {y₁ y₂ : GalilScaffoldControl.Machine 12}
    (h1 : GalilScaffoldSearchRun.SafeQuanta s x bs t₁ y₁)
    (h2 : GalilScaffoldSearchRun.SafeQuanta s x bs t₂ y₂) : t₁ = t₂ ∧ y₁ = y₂ := by
  induction h1 generalizing t₂ y₂ with
  | nil s x => cases h2 with | nil => exact ⟨rfl, rfl⟩
  | cons s u t x y z a bs hm hq hr ih =>
      cases h2 with
      | cons _ u' _ _ y' _ _ _ hm' hq' hr' =>
          obtain ⟨hu, hy⟩ := safeCalls_unique hrf hq hq'
          subst hu
          subst hy
          exact ih hr'

#print axioms execute_unique
#print axioms progTick_unique
#print axioms safeCalls_unique
#print axioms safeQuanta_unique

/-! ### The fallback entry of `sharedC` is not a function either

`sharedC` takes `beginFallback := beginFallbackVM'`, whose right place is
existentially quantified and *not* read off the state
(`GalilSharedFunctional.beginFallbackVM'_not_unique`).  So `scan_fallback` also
has two successors whenever its premises hold. -/

section Fallback

variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

theorem scan_fallback_not_det {c : Control} {s s' : GalilVM} (hm : c.mode = .scan)
    (hav : c.replaying = true ∨
      (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).available s)
    (hc : c.clock = 1)
    (hcmp : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s')
    (hmt : ¬ (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).matched s')
    (hg : c.replaying = true ∨
      ¬ (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).shiftGuard s')
    (hr : c.replaying = false) :
    ∃ y₁ y₂ : State GalilVM,
      Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
          ⟨c, s⟩ y₁ ∧
        Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
          ⟨c, s⟩ y₂ ∧ y₁ ≠ y₂ := by
  obtain ⟨t₁, t₂, hb₁, hb₂, hne⟩ := beginFallbackVM'_not_unique s'
  exact ⟨_, _, .scan_fallback c s s' t₁ hm hav hc hcmp hmt hg hr hb₁,
    .scan_fallback c s s' t₂ hm hav hc hcmp hmt hg hr hb₂,
    fun he => hne (congrArg State.vm he)⟩

end Fallback

/-! ## Answer

`Tick (galilFrameS (sharedC …) q first) delay` is **not** functional in `y`.

* **(a) `restart` vs the five scan constructors — NOT disjoint.**
  `ChainStep.brokenIdle` lets `backgroundS` take the stutter `s → s` from a
  broken chain, which is exactly the state the restart guard needs.
  `scan_restart_not_det` / `scan_restart_not_det_sharedC` give the two
  successors `⟨c, s⟩` (scan_wait) and `⟨{c with clock := delay}, t⟩` (restart),
  distinguished by `chain`.  Scala restarts *in the prelude*, before the mode
  step; `Tick` does not encode that priority.  **`tick_det_scan` is therefore
  false as stated.**
* **(b) `SafeQuanta` / the search quantum — functional modulo one decidable
  property of the code.** `safeQuanta_unique`, `safeCalls_unique`,
  `progTick_unique`, `execute_unique`, all from `ReadFun GalilDpCode.code`
  (single-valued `read` dispatch tables).  Residual: `ReadFun GalilDpCode.code`.
  Still open above that: `GalilScaffoldPrepareControl.Tick` for the non-`run`
  branches of `searchStep`.
* **(c) `chainAt`/`ChainTick` — FUNCTIONAL, unconditionally.**  `chainAt_unique`
  (via `chainStep_unique`, `chainMatched_unique`, `internal_unique`,
  `outer_unique`, `not_good_of_break`).
* **(d) `refresh` — functional** (`LocalRealizesScan.refresh_unique`).
* **(e) The `Shared` fields.** `restartVM` and `beginShiftVM'` are functional
  (`GalilSharedFunctional`); `beginFallbackVM'` is *not*
  (`beginFallbackVM'_not_unique`, lifted here to `scan_fallback_not_det`); and
  `initVM`/`replayStartVM` are *not* — they constrain 13 of the 15 `GalilVM`
  fields, leaving `periodOnly` and `walker` free (`initVM_not_unique`,
  `replayStartVM_not_unique`, `tick_init_not_det`, `tick_replayStart_not_det`).

So the abstract model is under-specified in `init`, `replayStart`, `scan`
(restart priority) and `scan_fallback` (the place).  The trace must be
**defined from the local run** rather than assumed deterministic. -/

#print axioms initVM_not_unique
#print axioms replayStartVM_not_unique
#print axioms tick_init_not_det
#print axioms replayStart_tick_of
#print axioms tick_replayStart_not_det
#print axioms backgroundS_stutter
#print axioms scan_restart_not_det
#print axioms scan_restart_not_det_sharedC
#print axioms scan_fallback_not_det

end PalPeg.GalilTickDet
