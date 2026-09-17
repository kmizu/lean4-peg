import PalPeg.GalilBranchInvariants
import PalPeg.GalilSharedFunctional
import PalPeg.GalilScaffoldTopOutputTrace

/-!
# A step function for the scaffold tick

`Tick` is a relation; this module turns it into a (noncomputable) function on
the states where the existing existence lemmas give a successor.

`Enabled` collects those preconditions for the shared
`sharedFun = galilShared onLetter leftFirst shiftGuardVM beginShiftVM'
(fun s t => beginFallbackVM (place s) s t) (restartVM entry) centre place entry`:

* `init` and `replayStart`: unconditional (`initVM_exists`,
  `replayStartVM_exists` build the successor state outright);
* `scan`: either the concrete restart guard `restartGuardVM` (the only way out
  of a `broken` chain — see below), or `ScanEnabled`: a positive clock, not
  replaying, a search effect for both events, and `ChainReady` on the chain.

**Excluded branches** (no existence lemma, so `Enabled` is false there):

* modes `shift`, `copy`, `home`, `fpp`, `markEnd`, `choose`, `rewind` — the
  VM effects `shiftOne`/`copyOne`/`copyEnd`/`fppStart`/`homeStep`/`fppSlice`/
  `fppDone`/`markBack`/`markForward`/`choose`/`fppReset`/`rewindOne`/
  `rewindPair` have no totality lemma at this layer;
* scan with `clock = 0`: `scan_count` needs `1 < clock` and `scan_match` etc.
  need `clock = 1`, so a zero clock has no constructor;
* scan while `replaying = true`: `scan_shift`/`scan_fallback` both carry
  `hr : c.replaying = false`, so a mismatching comparison while replaying has
  no constructor (the restriction is inherited from `compare_progress_S`);
* a `broken` chain (`ChainReady .broken = False`): `ChainMatched` has no
  constructor from `broken`, so a matched comparison has no chain effect —
  such a state ticks only through `Tick.restart`, which is why `Enabled`
  offers `restartGuardVM` as the alternative in scan mode;
* the search modes are not restricted here: `ScanEnabled` assumes the search
  effect existentially (`∀ a, ∃ v, searchEffect P a s v`) rather than deriving
  it, so `lowerHome`/`home`/`grow`/… are covered only by that hypothesis.
-/

set_option autoImplicit false
namespace PalPeg.GalilTickFun

open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilBranchInvariants
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter

/-- The chain-side enabling condition. -/
def ChainReady : ChainVM → Prop
  | .idle => True
  | .copy t h p v _ _ _ => ∃ n : ℕ, CopyInv t h p v n
  | .back v _ lag margin ver =>
      GalilScaffoldChainPeriod.isFirst v.focus = true →
        (zero lag = true → WatchReady ⟨⟨ver, watchControl v⟩, lag, margin⟩)
  | .watch w =>
      (positive w.lag = true → GalilScaffoldChainWatch.Good w) ∧ WatchBlock w ∧
        (∀ m, GalilScaffoldChainWatch.Internal w m →
          GalilScaffoldChainVerifier.canRight m.machine.verifier)
  | .broken _ => False

theorem chainAt_exists (a found : Bool) (answer : GalilScaffoldTape.Tape) (c : Fin 3)
    (walker : GalilScaffoldPlace.Place) (ver : GalilScaffoldInputHead.PlaceHead)
    (radius : Counter) (x : ChainVM) (hx : ChainReady x) :
    ∃ z, chainAt a found answer c walker ver radius x z := by
  classical
  cases x with
  | idle =>
    cases found with
    | false => exact ⟨.idle, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
    | true =>
      cases a with
      | false =>
        exact ⟨chainStart answer c walker ver radius, Or.inr (Or.inr ⟨rfl, rfl, by simp⟩)⟩
      | true =>
        refine ⟨ChainVM.copy answer reset walker (GalilScaffoldChainPeriod.start c)
            (inc radius) (inc radius) ver, Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)⟩
        simpa [chainStart] using ChainMatched.copy answer reset walker (GalilScaffoldChainPeriod.start c)
          radius radius ver
  | copy t h p v lag margin ver =>
    obtain ⟨n, hi⟩ := hx
    obtain ⟨y, hstep⟩ := copy_step_exists hi lag margin ver
    cases a with
    | false => exact ⟨y, Or.inl ⟨by simp, y, hstep, by simp⟩⟩
    | true =>
      cases hstep with
      | copyBit _ _ _ _ _ _ _ a' h1 h2 h3 =>
        exact ⟨_, Or.inl ⟨by simp, _, ChainStep.copyBit _ _ _ _ _ _ _ a' h1 h2 h3,
          by simpa using ChainMatched.copy _ _ _ _ _ _ _⟩⟩
      | copyEnd _ _ _ _ _ _ _ b h1 h2 h3 =>
        exact ⟨_, Or.inl ⟨by simp, _, ChainStep.copyEnd _ _ _ _ _ _ _ b h1 h2 h3,
          by simpa using ChainMatched.back _ _ _ _ _⟩⟩
  | back v h lag margin ver =>
    obtain ⟨y, hstep⟩ := back_step_exists v h lag margin ver
    cases a with
    | false => exact ⟨y, Or.inl ⟨by simp, y, hstep, by simp⟩⟩
    | true =>
      cases hstep with
      | backStep _ _ _ _ _ hf =>
        exact ⟨_, Or.inl ⟨by simp, _, ChainStep.backStep _ _ _ _ _ hf,
          by simpa using ChainMatched.back _ _ _ _ _⟩⟩
      | backDone _ _ _ _ _ hf =>
        obtain ⟨z, hz⟩ := chainMatched_watch_total
          ⟨⟨ver, watchControl v⟩, lag, margin⟩ (hx hf)
        exact ⟨z, Or.inl ⟨by simp, _, ChainStep.backDone _ _ _ _ _ hf, by simpa using hz⟩⟩
  | watch w =>
    obtain ⟨h1, h2, h3⟩ := hx
    obtain ⟨z, hz⟩ := chainTick_watch_total w a h1 h2 h3
    exact ⟨z, Or.inl ⟨by simp, hz⟩⟩
  | broken w => exact absurd hx (by simp [ChainReady])

#print axioms chainAt_exists

/-! ## Scan-mode progress for an arbitrary shared -/

/-- `compare_progress_S` with the shared's entries abstracted: the shift entry
total under the shared's own guard, the fallback entry total outright. -/
theorem compare_progress_gen (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (s : GalilVM) (hm : c.mode = .scan) (hc : c.clock = 1) (hr : c.replaying = false)
    (hav : GalilScaffoldChainVerifier.canRight s.right)
    (hshift : ∀ t : GalilVM, P.shiftGuard t → ∃ u, P.beginShift t u)
    (hfall : ∀ t : GalilVM, ∃ u, P.beginFallback t u)
    (hsearch : ∀ a : Bool, ∃ v, searchEffect P a s v)
    (hchain : ∀ (a : Bool) (v : SearchVM), ∃ z, chainAt a (decide (v.search.mode = .found))
      (v.dp.config.tapes 11) (P.centre s) (P.place s) s.center s.radius s.chain z) :
    ∃ st', Tick (galilFrameS P q first) delay ⟨c, s⟩ st' := by
  classical
  have hav' : (galilFrameS P q first).available s := hav
  by_cases hmt : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
      GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right s.right)
  · obtain ⟨vq, hq⟩ := hsearch true
    obtain ⟨z, hz⟩ := hchain true vq
    let vs : ScanVM := ⟨GalilScaffoldInputHead.left s.left,
      GalilScaffoldChainVerifier.right s.right, z⟩
    have hmt0 : (galilFrame P q first).matched (scanLens.set s vs) := hmt
    have hcmp : (galilFrameS P q first).compare s
        (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)) :=
      ⟨vs, vq, true, rfl, rfl, ⟨fun _ => hmt0, fun _ => rfl⟩, hq, hz, rfl⟩
    have hmt1 : (galilFrameS P q first).matched
        (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)) := by
      show GalilScaffoldInputHead.read (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).left
        = GalilScaffoldInputHead.read (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).right
      rw [afterBirth_left, afterBirth_right]
      exact hmt
    let s'' : GalilVM := replayDec c.replaying (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq))
    let o : Bool := if P.onLetter s'' then decide (P.leftFirst s'') else c.output
    have ho : refresh (galilFrameS P q first) s'' c.output o := by
      refine ⟨fun hl => ?_, fun hl => ?_⟩
      · have hl' : P.onLetter s'' := hl
        show (if P.onLetter s'' then decide (P.leftFirst s'') else c.output) = true ↔ P.leftFirst s''
        rw [if_pos hl']
        exact decide_eq_true_iff
      · have hl' : ¬ P.onLetter s'' := hl
        show (if P.onLetter s'' then decide (P.leftFirst s'') else c.output) = c.output
        rw [if_neg hl']
    exact ⟨_, Tick.scan_match (F := galilFrameS P q first) (delay := delay) c s _ s'' o hm
      (Or.inr hav') hc hcmp hmt1 (matchedPlace_replayDec P q first c.replaying _) ho⟩
  · obtain ⟨vq, hq⟩ := hsearch false
    obtain ⟨z, hz⟩ := hchain false vq
    let vs : ScanVM := ⟨GalilScaffoldInputHead.left s.left,
      GalilScaffoldChainVerifier.right s.right, z⟩
    have hmt0 : ¬ (galilFrame P q first).matched (scanLens.set s vs) := hmt
    have hcmp : (galilFrameS P q first).compare s
        (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)) :=
      ⟨vs, vq, false, rfl, rfl, Iff.intro (fun h0 => by cases h0) (fun h0 => absurd h0 hmt0),
        hq, hz, rfl⟩
    have hmt1 : ¬ (galilFrameS P q first).matched
        (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)) := by
      intro h0
      apply hmt
      have h1 : GalilScaffoldInputHead.read (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)).left
        = GalilScaffoldInputHead.read (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)).right := h0
      rw [afterBirth_left, afterBirth_right] at h1
      exact h1
    by_cases hg : P.shiftGuard (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq))
    · obtain ⟨t, hb⟩ := hshift (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)) hg
      exact ⟨_, Tick.scan_shift (F := galilFrameS P q first) (delay := delay) c s _ t hm
        (Or.inr hav') hc hcmp hmt1 hr hg hb⟩
    · obtain ⟨t, hb⟩ := hfall (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq))
      exact ⟨_, Tick.scan_fallback (F := galilFrameS P q first) (delay := delay) c s _ t hm
        (Or.inr hav') hc hcmp hmt1 (Or.inr hg) hr hb⟩

/-- `scan_tick_exists` with the shared's entries abstracted. -/
theorem scan_tick_gen (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (s : GalilVM) (hm : c.mode = .scan) (hclk : 1 ≤ c.clock) (hr : c.replaying = false)
    (hshift : ∀ t : GalilVM, P.shiftGuard t → ∃ u, P.beginShift t u)
    (hfall : ∀ t : GalilVM, ∃ u, P.beginFallback t u)
    (hsearch : ∀ a : Bool, ∃ v, searchEffect P a s v)
    (hchain : ∀ (a : Bool) (v : SearchVM), ∃ z, chainAt a (decide (v.search.mode = .found))
      (v.dp.config.tapes 11) (P.centre s) (P.place s) s.center s.radius s.chain z) :
    ∃ st', Tick (galilFrameS P q first) delay ⟨c, s⟩ st' := by
  classical
  by_cases hav : GalilScaffoldChainVerifier.canRight s.right
  · rcases Nat.lt_or_ge 1 c.clock with hlt | hle
    · obtain ⟨s', hb⟩ := backgroundS_exists P q first s (hsearch false) (hchain false)
      have hav' : (galilFrameS P q first).available s := hav
      exact ⟨_, Tick.scan_count (F := galilFrameS P q first) (delay := delay) c s s' hm
        (Or.inr hav') hlt hb⟩
    · exact compare_progress_gen P q first delay c s hm (le_antisymm hle hclk) hr hav hshift hfall
        hsearch hchain
  · obtain ⟨s', hb⟩ := backgroundS_exists P q first s (hsearch false) (hchain false)
    have hav' : ¬ (galilFrameS P q first).available s := hav
    exact ⟨_, Tick.scan_wait (F := galilFrameS P q first) (delay := delay) c s s' hm
      ⟨hr, hav'⟩ hb⟩

#print axioms compare_progress_gen
#print axioms scan_tick_gen

/-! ## The remaining modes that have an existence proof -/

theorem init_tick_gen (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control) (s : GalilVM)
    (hm : c.mode = .init) (h : ∃ t, P.init s t) :
    ∃ st', Tick (galilFrameS P q first) delay ⟨c, s⟩ st' := by
  obtain ⟨t, ht⟩ := h
  exact ⟨_, Tick.init (F := galilFrameS P q first) (delay := delay) c s t hm ht⟩

theorem restart_tick_gen (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control) (s : GalilVM)
    (hm : c.mode = .scan) (h : ∃ t, P.restart s t) :
    ∃ st', Tick (galilFrameS P q first) delay ⟨c, s⟩ st' := by
  obtain ⟨t, ht⟩ := h
  exact ⟨_, Tick.restart (F := galilFrameS P q first) (delay := delay) c s t hm ht⟩

theorem replayStart_tick_gen (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (s : GalilVM) (hm : c.mode = .replayStart) (h : ∃ t, P.replayStart s t) :
    ∃ st', Tick (galilFrameS P q first) delay ⟨c, s⟩ st' := by
  classical
  obtain ⟨t, ht⟩ := h
  by_cases hp : P.replayPos t = true
  · refine ⟨_, Tick.replayStart (F := galilFrameS P q first) (delay := delay) c s t c.output hm ht
      (fun _ => rfl) (fun h0 => ?_)⟩
    exact absurd (hp.symm.trans h0) (by simp)
  · have hp' : P.replayPos t = false := Bool.eq_false_iff.mpr hp
    refine ⟨_, Tick.replayStart (F := galilFrameS P q first) (delay := delay) c s t
      (if P.onLetter t then decide (P.leftFirst t) else c.output) hm ht (fun h0 => ?_) (fun _ => ?_)⟩
    · exact absurd (hp'.symm.trans h0) (by simp)
    · refine ⟨fun hl => ?_, fun hl => ?_⟩
      · have hl' : P.onLetter t := hl
        show (if P.onLetter t then decide (P.leftFirst t) else c.output) = true ↔ P.leftFirst t
        rw [if_pos hl']
        exact decide_eq_true_iff
      · have hl' : ¬ P.onLetter t := hl
        show (if P.onLetter t then decide (P.leftFirst t) else c.output) = c.output
        rw [if_neg hl']

theorem initVM_exists (entry : ℕ) (s : GalilVM) : ∃ t, initVM entry s t :=
  ⟨{s with
      left := GalilScaffoldChainVerifier.right s.right,
      center := GalilScaffoldChainVerifier.right s.right,
      right := GalilScaffoldChainVerifier.right s.right,
      length := inc s.length, chain := ChainVM.idle,
      search := GalilScaffoldSearchFinish.begin reset s.radius,
      lower := reset, dp := GalilScaffoldControl.reset entry s.dp},
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem replayStartVM_exists (entry : ℕ) (s : GalilVM) : ∃ t, replayStartVM entry s t :=
  ⟨{s with
      left := s.center, center := s.center, right := s.center,
      replay := s.radius, radius := reset, length := ofNat 1, chain := ChainVM.idle,
      search := GalilScaffoldSearchFinish.begin reset reset,
      lower := reset, dp := GalilScaffoldControl.reset entry s.dp},
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

#print axioms init_tick_gen
#print axioms restart_tick_gen
#print axioms replayStart_tick_gen
#print axioms initVM_exists
#print axioms replayStartVM_exists

/-! ## The fixed shared and the step function -/

section Fixed

variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- The shared of `cycle_fallback_stepsAll` with the fallback entry
determinized by the shared's own `place`. -/
def sharedFun : Shared :=
  galilShared onLetter leftFirst shiftGuardVM beginShiftVM'
    (fun s t => beginFallbackVM (place s) s t) (restartVM entry) centre place entry

/-- The scan-mode enabling condition: a positive clock, not replaying, a
search effect for both events, and a chain able to tick. -/
def ScanEnabled (c : Control) (s : GalilVM) : Prop :=
  1 ≤ c.clock ∧ c.replaying = false ∧
    (∀ a : Bool, ∃ v, searchEffect (sharedFun onLetter leftFirst centre place entry) a s v) ∧
    ChainReady s.chain

/-- The enabling condition of one tick. -/
def Enabled (x : State GalilVM) : Prop :=
  x.ctl.mode = .init ∨ x.ctl.mode = .replayStart ∨
    (x.ctl.mode = .scan ∧
      (restartGuardVM x.vm ∨ ScanEnabled onLetter leftFirst centre place entry x.ctl x.vm))

theorem tick_exists (x : State GalilVM) (hx : Enabled onLetter leftFirst centre place entry x) :
    ∃ y, Tick (galilFrameS (sharedFun onLetter leftFirst centre place entry) q first) delay x y := by
  classical
  obtain ⟨c, s⟩ := x
  have hshift : ∀ t : GalilVM,
      (sharedFun onLetter leftFirst centre place entry).shiftGuard t →
      ∃ u, (sharedFun onLetter leftFirst centre place entry).beginShift t u :=
    fun t h => beginShiftVM'_exists t h
  have hfall : ∀ t : GalilVM,
      ∃ u, (sharedFun onLetter leftFirst centre place entry).beginFallback t u :=
    fun t => ⟨beginFallbackAt (place t) t, rfl⟩
  rcases hx with hm | hm | ⟨hm, hrest⟩
  · exact init_tick_gen _ q first delay c s hm (initVM_exists entry s)
  · exact replayStart_tick_gen _ q first delay c s hm (replayStartVM_exists entry s)
  · rcases hrest with hrg | ⟨hclk, hrep, hsearch, hchain⟩
    · exact restart_tick_gen _ q first delay c s hm (restartVM_exists entry s hrg)
    · exact scan_tick_gen _ q first delay c s hm hclk hrep hshift hfall hsearch
        (fun a v => chainAt_exists a (decide (v.search.mode = .found)) (v.dp.config.tapes 11)
          _ _ _ _ s.chain hchain)

/-- The chosen successor, the state itself when no tick is enabled. -/
noncomputable def tickFun (x : State GalilVM) : State GalilVM :=
  haveI : Decidable (Enabled onLetter leftFirst centre place entry x) := Classical.propDecidable _
  if h : Enabled onLetter leftFirst centre place entry x then
    Classical.choose (tick_exists onLetter leftFirst centre place entry q first delay x h)
  else x

theorem tickFun_spec (x : State GalilVM) (hx : Enabled onLetter leftFirst centre place entry x) :
    Tick (galilFrameS (sharedFun onLetter leftFirst centre place entry) q first) delay x
      (tickFun onLetter leftFirst centre place entry q first delay x) := by
  have he : tickFun onLetter leftFirst centre place entry q first delay x
      = Classical.choose (tick_exists onLetter leftFirst centre place entry q first delay x hx) := by
    unfold tickFun
    exact dif_pos hx
  rw [he]
  exact Classical.choose_spec (tick_exists onLetter leftFirst centre place entry q first delay x hx)

/-- The step function iterated. -/
noncomputable def runFun (n : ℕ) (x : State GalilVM) : State GalilVM :=
  (tickFun onLetter leftFirst centre place entry q first delay)^[n] x

theorem runFun_zero (x : State GalilVM) :
    runFun onLetter leftFirst centre place entry q first delay 0 x = x := rfl

theorem runFun_succ (n : ℕ) (x : State GalilVM) :
    runFun onLetter leftFirst centre place entry q first delay (n+1) x =
      runFun onLetter leftFirst centre place entry q first delay n
        (tickFun onLetter leftFirst centre place entry q first delay x) := by
  simp [runFun, Function.iterate_succ_apply]

theorem runFun_steps (n : ℕ) (x : State GalilVM)
    (h : ∀ i, i < n → Enabled onLetter leftFirst centre place entry
      (runFun onLetter leftFirst centre place entry q first delay i x)) :
    StepsAll (galilFrameS (sharedFun onLetter leftFirst centre place entry) q first) delay
      (fun _ => True) n x (runFun onLetter leftFirst centre place entry q first delay n x) := by
  induction n generalizing x with
  | zero => exact StepsAll.zero x trivial
  | succ n ih =>
    have h0 : Enabled onLetter leftFirst centre place entry x := h 0 (Nat.succ_pos n)
    rw [runFun_succ]
    refine StepsAll.succ trivial (tickFun_spec onLetter leftFirst centre place entry q first delay x h0)
      (ih _ (fun i hi => ?_))
    have hi' := h (i+1) (by omega)
    rwa [runFun_succ] at hi'

#print axioms tick_exists
#print axioms tickFun_spec
#print axioms runFun_zero
#print axioms runFun_succ
#print axioms runFun_steps

end Fixed

end PalPeg.GalilTickFun
