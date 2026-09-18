import PalPeg.GalilTickArrive
import PalPeg.GalilLatchTracking
import PalPeg.GalilReplaySegment

/-!
# Arrivals reach the chain's stored verifier

`GalilTickArrive.arriveVM` appends the new letter to the FIFOs of L/C/R only.
The chain stores its own verifier head (a copy of C made at `chainStart`)
inside `ChainVM.copy/back` and inside the watch machine (`w.machine.verifier`),
and that head never received the letter. This forced `NoStart` in
`tick_arrive_comm_or`.

Fix: `arriveChain` appends to the stored verifier in every constructor,
`arriveVM' a s := {arriveVM a s with chain := arriveChain a s.chain}`.

* §1 `arriveChain` and commutation of `ChainStep`/`ChainMatched`/`ChainTick`
  (unconditional: every verifier move in these relations is guarded by
  `GalilScaffoldChainVerifier.canRight`, via `Good` or `BreakStep`), `chainStart_arrive` (definitional).
* §2 `SharedArrive'` and `sharedC_arrive'`. The concrete `beginShiftVM'` does
  the immediate consume `GalilScaffoldChainWatch.immediate` *without* a
  `GalilScaffoldChainVerifier.canRight` guard, so its commutation needs `ShiftReady`.
* §3 `tick_arrive_comm_or'` / `tick_arrive_comm'` without `NoStart`;
  the replay side condition is discharged from `Frontier` plus a positive
  replay counter.
* §4 `RunStep'`/`AbstractRun'` with `arriveState'` and `pal_in_peg_of_latch'`.
-/

set_option autoImplicit false

namespace PalPeg.GalilArriveChain

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilTickArrive PalPeg.GalilLatchTracking

/-! ## 1. Arrival on the chain -/

def arriveW (a : Fin 2) (w : GalilScaffoldChainWatch.State) : GalilScaffoldChainWatch.State :=
  ⟨⟨arrivePH a w.machine.verifier, w.machine.control⟩, w.lag, w.margin⟩

def arriveChain (a : Fin 2) : ChainVM → ChainVM
  | .idle => .idle
  | .copy t h p v lag margin ver => .copy t h p v lag margin (arrivePH a ver)
  | .back v h lag margin ver => .back v h lag margin (arrivePH a ver)
  | .watch w => .watch (arriveW a w)
  | .broken w => .broken (arriveW a w)

def arriveVM' (a : Fin 2) (s : GalilVM) : GalilVM :=
  {LocalTracking.arriveVM a s with chain := arriveChain a s.chain}

def arriveState' (a : Fin 2) (st : State GalilVM) : State GalilVM := ⟨st.ctl, arriveVM' a st.vm⟩

theorem arriveVM'_chain (a : Fin 2) (s : GalilVM) :
    (arriveVM' a s).chain = arriveChain a s.chain := rfl

/-- The birth reset commutes with an arrival. -/
theorem arriveVM'_afterBirth (a : Fin 2) (b : Bool) (s : GalilVM) :
    arriveVM' a (afterBirth b s) = afterBirth b (arriveVM' a s) := by
  cases b <;> rfl

/-- An arrival does not change whether the chain is idle, so it does not change
whether a chain is born. -/
theorem chainBorn_arriveChain (b : Bool) (a : Fin 2) (x : ChainVM) :
    chainBorn b (arriveChain a x) = chainBorn b x := by
  cases x <;> simp [chainBorn, arriveChain, ChainVM.isIdle]

theorem arriveChain_idle_iff (a : Fin 2) (x : ChainVM) : arriveChain a x = .idle ↔ x = .idle := by
  cases x <;> simp [arriveChain]

theorem chainStart_arrive (a : Fin 2) (ans : GalilScaffoldTape.Tape) (c : Fin 3)
    (walker : GalilScaffoldPlace.Place) (ver : GalilScaffoldInputHead.PlaceHead) (r : GalilScaffoldCounter.Counter) :
    arriveChain a (chainStart ans c walker ver r) = chainStart ans c walker (arrivePH a ver) r := rfl

theorem consume_arrive (a : Fin 2) (m : GalilScaffoldChainVerifier.State) (hc : GalilScaffoldChainVerifier.canRight m.verifier) :
    GalilScaffoldChainVerifier.consume ⟨arrivePH a m.verifier, m.control⟩ =
      ⟨arrivePH a (GalilScaffoldChainVerifier.consume m).verifier,
        (GalilScaffoldChainVerifier.consume m).control⟩ := by
  simp only [GalilScaffoldChainVerifier.consume, right_arrive a _ hc]
  rfl

theorem good_arrive (a : Fin 2) {w : GalilScaffoldChainWatch.State}
    (h : GalilScaffoldChainWatch.Good w) : GalilScaffoldChainWatch.Good (arriveW a w) := by
  obtain ⟨hc, b, hs, hr⟩ := h
  refine ⟨canRight_arrive a _, b, hs, ?_⟩
  show GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right (arrivePH a w.machine.verifier)) = some b
  rw [right_arrive a _ hc, read_arrive]; exact hr

theorem caught_arrive (a : Fin 2) (w : GalilScaffoldChainWatch.State) (hc : GalilScaffoldChainVerifier.canRight w.machine.verifier) :
    GalilScaffoldChainWatch.caught (arriveW a w) = arriveW a (GalilScaffoldChainWatch.caught w) := by
  simp only [GalilScaffoldChainWatch.caught, arriveW]
  rw [consume_arrive a w.machine hc]

theorem immediate_arrive (a : Fin 2) (w : GalilScaffoldChainWatch.State) (hc : GalilScaffoldChainVerifier.canRight w.machine.verifier) :
    GalilScaffoldChainWatch.immediate (arriveW a w) = arriveW a (GalilScaffoldChainWatch.immediate w) := by
  simp only [GalilScaffoldChainWatch.immediate, arriveW]
  rw [consume_arrive a w.machine hc]

theorem internal_arrive (a : Fin 2) {w w' : GalilScaffoldChainWatch.State}
    (h : GalilScaffoldChainWatch.Internal w w') :
    GalilScaffoldChainWatch.Internal (arriveW a w) (arriveW a w') := by
  cases h with
  | idle hz => exact .idle _ hz
  | take hp hg =>
    rw [← caught_arrive a w hg.1]
    exact .take _ hp (good_arrive a hg)

theorem outer_arrive (a : Fin 2) {w w' : GalilScaffoldChainWatch.State} {b : Bool}
    (h : GalilScaffoldChainWatch.Outer w b w') :
    GalilScaffoldChainWatch.Outer (arriveW a w) b (arriveW a w') := by
  cases h with
  | idle => exact .idle _
  | queued hz => exact .queued _ hz
  | immediate hz hg =>
    rw [← immediate_arrive a w hg.1]
    exact .immediate _ hz (good_arrive a hg)

theorem breakStep_arrive (a : Fin 2) {w w' : GalilScaffoldChainWatch.State} (h : BreakStep w w') :
    BreakStep (arriveW a w) (arriveW a w') := by
  obtain ⟨hz, hc, b, hs, hr, ht⟩ := h
  refine ⟨hz, canRight_arrive a _, b, hs, ?_, ?_⟩
  · show GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right (arrivePH a w.machine.verifier)) ≠ some b
    rw [right_arrive a _ hc, read_arrive]; exact hr
  · subst ht
    show arriveW a ⟨_, _, _⟩ = ⟨GalilScaffoldChainVerifier.consume ⟨arrivePH a w.machine.verifier, w.machine.control⟩, _, _⟩
    rw [consume_arrive a w.machine hc]
    rfl

/-- **`BreakStepPos` も arrival を通る。** `breakStep_arrive` と同じ証明。 -/
theorem breakStepPos_arrive (a : Fin 2) {w w' : GalilScaffoldChainWatch.State}
    (h : BreakStepPos w w') : BreakStepPos (arriveW a w) (arriveW a w') := by
  obtain ⟨hz, hc, b, hs, hr, ht⟩ := h
  refine ⟨hz, canRight_arrive a _, b, hs, ?_, ?_⟩
  · show GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right (arrivePH a w.machine.verifier)) ≠ some b
    rw [right_arrive a _ hc, read_arrive]; exact hr
  · subst ht
    show arriveW a ⟨_, _, _⟩ = ⟨GalilScaffoldChainVerifier.consume ⟨arrivePH a w.machine.verifier, w.machine.control⟩, _, _⟩
    rw [consume_arrive a w.machine hc]
    rfl

theorem chainStep_arrive (a : Fin 2) {x y : ChainVM} (h : ChainStep x y) :
    ChainStep (arriveChain a x) (arriveChain a y) := by
  cases h with
  | idle => exact .idle
  | brokenIdle w => exact .brokenIdle _
  | copyBit t h p v lag margin ver b one legal present =>
    exact .copyBit t h p v lag margin _ b one legal present
  | copyEnd t h p v lag margin ver b hl hp hv => exact .copyEnd t h p v lag margin _ b hl hp hv
  | backStep v h lag margin ver hf => exact .backStep v h lag margin _ hf
  | backDone v h lag margin ver hf => exact .backDone v h lag margin _ hf
  | watchStep w w' ht => exact .watchStep _ _ (internal_arrive a ht)
  | watchBreak w w' hb => exact .watchBreak _ _ (breakStepPos_arrive a hb)

theorem chainMatched_arrive (a : Fin 2) {x y : ChainVM} (h : ChainMatched x y) :
    ChainMatched (arriveChain a x) (arriveChain a y) := by
  cases h with
  | idle => exact .idle
  | copy t h p v lag margin ver => exact .copy t h p v lag margin _
  | back v h lag margin ver => exact .back v h lag margin _
  | watch w w' ho => exact .watch _ _ (outer_arrive a ho)
  | breaks w w' hb => exact .breaks _ _ (breakStep_arrive a hb)
  | brokenMatched w => exact .brokenMatched _

theorem chainTick_arrive (a : Fin 2) {b : Bool} {x z : ChainVM} (h : ChainTick b x z) :
    ChainTick b (arriveChain a x) (arriveChain a z) := by
  obtain ⟨y, hs, hm⟩ := h
  refine ⟨arriveChain a y, chainStep_arrive a hs, ?_⟩
  cases b
  · simp only [Bool.false_eq_true, if_false] at hm ⊢; rw [hm]
  · simp only [if_true] at hm ⊢; exact chainMatched_arrive a hm

theorem chainAt_arrive (a : Fin 2) {b found : Bool} {ans : GalilScaffoldTape.Tape} {c : Fin 3}
    {w : GalilScaffoldPlace.Place} {ver : GalilScaffoldInputHead.PlaceHead} {r : GalilScaffoldCounter.Counter}
    {x z : ChainVM} (h : chainAt b found ans c w ver r x z) :
    chainAt b found ans c w (arrivePH a ver) r (arriveChain a x) (arriveChain a z) := by
  rcases h with ⟨hx, ht⟩ | ⟨hx, hf, hz⟩ | ⟨hx, hf, hz⟩
  · exact Or.inl ⟨fun e => hx ((arriveChain_idle_iff a x).mp e), chainTick_arrive a ht⟩
  · subst hx; subst hz; exact Or.inr (Or.inl ⟨rfl, hf, rfl⟩)
  · subst hx
    refine Or.inr (Or.inr ⟨rfl, hf, ?_⟩)
    cases b
    · simp only [Bool.false_eq_true, if_false] at hz ⊢; rw [hz]; rfl
    · simp only [if_true] at hz ⊢
      rw [← chainStart_arrive]; exact chainMatched_arrive a hz


/-! ## 2. The shared record under `arriveVM'` -/

/-- The watching chain's verifier can advance (needed by the unguarded
immediate consume of `beginShiftVM`). -/
def ShiftReady (s : GalilVM) : Prop :=
  ∀ w, s.chain = .watch w → GalilScaffoldChainVerifier.canRight w.machine.verifier

structure SharedArrive' (P : Shared) (a : Fin 2) : Prop where
  onLetter : ∀ s, P.onLetter (arriveVM' a s) ↔ P.onLetter s
  leftFirst : ∀ s, P.leftFirst (arriveVM' a s) ↔ P.leftFirst s
  init : ∀ s t, GalilScaffoldChainVerifier.canRight s.right → P.init s t → P.init (arriveVM' a s) (arriveVM' a t)
  replayStart : ∀ s t, P.replayStart s t → P.replayStart (arriveVM' a s) (arriveVM' a t)
  replayPos : ∀ s, P.replayPos (arriveVM' a s) = P.replayPos s
  replayExhausted : ∀ s, P.replayExhausted (arriveVM' a s) = P.replayExhausted s
  shiftGuard : ∀ s, P.shiftGuard (arriveVM' a s) ↔ P.shiftGuard s
  beginShift : ∀ s t, ShiftReady s → P.beginShift s t → P.beginShift (arriveVM' a s) (arriveVM' a t)
  beginFallback : ∀ s t, P.beginFallback s t → P.beginFallback (arriveVM' a s) (arriveVM' a t)
  restart : ∀ s t, P.restart s t → P.restart (arriveVM' a s) (arriveVM' a t)
  centre : ∀ s, P.centre (arriveVM' a s) = P.centre s
  place : ∀ s, P.place (arriveVM' a s) = P.place s

theorem sharedC_arrive' (raw : List (Fin 2)) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) (a : Fin 2)
    (hc : ∀ s, centre (arriveVM' a s) = centre s) (hp : ∀ s, place (arriveVM' a s) = place s) :
    SharedArrive' (sharedC (onLetterVM raw) leftFirstVM centre place entry) a where
  onLetter := fun _ => Iff.rfl
  leftFirst := fun _ => Iff.rfl
  init := by
    intro s t hcr h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
    have hr : GalilScaffoldChainVerifier.right (arriveVM' a s).right
        = arrivePH a (GalilScaffoldChainVerifier.right s.right) := right_arrive a s.right hcr
    refine ⟨?_, ?_, ?_, h4, h5, h6, h7, h8, h9, ?_, h11, h12, h13⟩
    · rw [hr, ← h1]; rfl
    · rw [hr, ← h2]; rfl
    · rw [hr, ← h3]; rfl
    · show arriveChain a t.chain = .idle
      rw [h10]; rfl
  replayStart := by
    intro s t h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
    refine ⟨h1, ?_, ?_, ?_, h5, h6, h7, h8, h9, ?_, h11, h12, h13⟩
    · show arrivePH a _ = arrivePH a _; rw [h2]
    · show arrivePH a _ = arrivePH a _; rw [h3]
    · show arrivePH a _ = arrivePH a _; rw [h4]
    · show arriveChain a t.chain = .idle
      rw [h10]; rfl
  replayPos := fun _ => rfl
  replayExhausted := fun _ => rfl
  shiftGuard := by
    intro s
    show shiftGuardVM (arriveVM' a s) ↔ shiftGuardVM s
    constructor
    · rintro ⟨w, hw, h1, h2, h3, h4, h5⟩
      have hw' : arriveChain a s.chain = .watch w := hw
      cases hcs : s.chain with
      | watch v =>
        rw [hcs] at hw'
        cases hw'
        exact ⟨v, hcs, h1, h2, h3, h4, h5⟩
      | idle => rw [hcs] at hw'; cases hw'
      | copy => rw [hcs] at hw'; cases hw'
      | back => rw [hcs] at hw'; cases hw'
      | broken => rw [hcs] at hw'; cases hw'
    · rintro ⟨w, hw, h1, h2, h3, h4, h5⟩
      exact ⟨arriveW a w, by show arriveChain a s.chain = _; rw [hw]; rfl, h1, h2, h3, h4, h5⟩
  beginShift := by
    rintro s t hready ⟨w, hw, ht⟩
    refine ⟨arriveW a w, by show arriveChain a s.chain = _; rw [hw]; rfl, ?_⟩
    subst ht
    rw [immediate_arrive a w (hready w hw)]
    rfl
  beginFallback := by
    rintro s t ⟨p, ht⟩
    exact ⟨p, by rw [ht]; rfl⟩
  restart := by
    rintro s t ⟨w, hw, h1, h2, h3, ht⟩
    exact ⟨arriveW a w, by show arriveChain a s.chain = _; rw [hw]; rfl, h1, h2, h3, by subst ht; rfl⟩
  centre := hc
  place := hp


/-! ## 3. Scan relations and the commutation -/

theorem searchEffect_arrive' {P : Shared} {a : Fin 2} (hP : SharedArrive' P a) (b : Bool)
    (s : GalilVM) (vq : SearchVM) : searchEffect P b (arriveVM' a s) vq ↔ searchEffect P b s vq := by
  show ((arriveChain a s.chain = .idle ∧ searchStep (P.place (arriveVM' a s)) b (searchLens.get s) vq) ∨
      (arriveChain a s.chain ≠ .idle ∧ vq = searchLens.get s)) ↔ _
  rw [hP.place s]
  unfold searchEffect
  simp only [ne_eq, arriveChain_idle_iff]

theorem compareFound_arrive' {P : Shared} {a : Fin 2} (hP : SharedArrive' P a) (q : ℕ) (first : Fin 9)
    {s t : GalilVM} (hcr : GalilScaffoldChainVerifier.canRight s.right)
    (h : compareFound P q first s t) : compareFound P q first (arriveVM' a s) (arriveVM' a t) := by
  obtain ⟨vs, vq, b, hl, hr, hb, hse, hch, ht⟩ := h
  refine ⟨⟨arrivePH a vs.left, arrivePH a vs.right, arriveChain a vs.chain⟩, vq, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show arrivePH a vs.left = GalilScaffoldInputHead.left (arrivePH a s.left)
    rw [left_arrive, hl]
  · show arrivePH a vs.right = GalilScaffoldChainVerifier.right (arrivePH a s.right)
    rw [right_arrive a _ hcr, hr]
  · exact hb
  · exact (searchEffect_arrive' hP b s vq).mpr hse
  · rw [hP.centre, hP.place]
    exact chainAt_arrive a hch
  · subst ht
    rw [arriveVM'_afterBirth, arriveVM'_chain, chainBorn_arriveChain]
    cases b <;> rfl

theorem backgroundS_arrive' {P : Shared} {a : Fin 2} (hP : SharedArrive' P a) (q : ℕ) (first : Fin 9)
    {s t : GalilVM} (h : backgroundS P q first s t) :
    backgroundS P q first (arriveVM' a s) (arriveVM' a t) := by
  obtain ⟨hl, hr, hse, hch, hset⟩ := h
  refine ⟨?_, ?_, (searchEffect_arrive' hP false s _).mpr hse, ?_, ?_⟩
  · show arrivePH a t.left = arrivePH a s.left
    rw [hl]
  · show arrivePH a t.right = arrivePH a s.right
    rw [hr]
  · rw [hP.centre, hP.place]
    exact chainAt_arrive a hch
  · rw [arriveVM'_chain, chainBorn_arriveChain]
    calc arriveVM' a t
        = arriveVM' a (afterBirth (chainBorn (decide ((searchLens.get t).search.mode
              = GalilScaffoldSearchFinish.Mode.found)) s.chain)
            (searchLens.set (scanLens.set s (scanLens.get t)) (searchLens.get t))) :=
          congrArg _ hset
      _ = _ := by rw [arriveVM'_afterBirth]; rfl

theorem rel_arrive' {σ' : Type} (L : Lens GalilVM σ') (arrV : σ' → σ') (R : σ' → σ' → Prop) (a : Fin 2)
    (hget : ∀ s, L.get (arriveVM' a s) = arrV (L.get s))
    (hset : ∀ s v, L.set (arriveVM' a s) (arrV v) = arriveVM' a (L.set s v))
    (hR : ∀ u v, R u v → R (arrV u) (arrV v)) {s t : GalilVM} (h : L.rel R s t) :
    L.rel R (arriveVM' a s) (arriveVM' a t) := by
  refine ⟨?_, ?_⟩
  · rw [hget, hget]; exact hR _ _ h.1
  · rw [hget, hset]; exact congrArg _ h.2

theorem fpp_rel_arrive' (R : FppControl.State → FppControl.State → Prop) (a : Fin 2) {s t : GalilVM}
    (h : fppLens.rel R s t) : fppLens.rel R (arriveVM' a s) (arriveVM' a t) :=
  rel_arrive' fppLens id R a (fun _ => rfl) (fun _ _ => rfl) (fun _ _ h => h) h

def arriveShift' (a : Fin 2) (v : ShiftVM) : ShiftVM :=
  ⟨⟨arrivePH a v.shift.center, arrivePH a v.shift.left, v.shift.remaining, v.shift.radius, v.shift.length⟩,
    arriveChain a v.chain, v.cycle⟩

theorem shiftOne_arrive' (a : Fin 2) (on lf : ShiftVM → Prop) {s t : GalilVM}
    (h : shiftLens.rel (shiftFrame on lf).shiftOne s t) :
    shiftLens.rel (shiftFrame on lf).shiftOne (arriveVM' a s) (arriveVM' a t) := by
  refine rel_arrive' shiftLens (arriveShift' a) _ a (fun _ => rfl) (fun _ _ => rfl) ?_ h
  rintro ⟨⟨c, l, rem, rad, len⟩, ch, cy⟩ v ⟨hc, hl, hl', w, hw, hv⟩
  refine ⟨canRight_arrive a c, canRight_arrive a l, ?_, arriveW a w, ?_, ?_⟩
  · show GalilScaffoldChainVerifier.canRight (GalilScaffoldChainVerifier.right (arrivePH a l))
    rw [right_arrive a l hl]; exact canRight_arrive a _
  · show arriveChain a ch = _
    rw [show ch = .watch w from hw]; rfl
  · subst hv
    show arriveShift' a ⟨shiftTick ⟨c, l, rem, rad, len⟩, _, _⟩ = ⟨shiftTick ⟨arrivePH a c, arrivePH a l, rem, rad, len⟩, _, _⟩
    simp only [arriveShift', shiftTick]
    rw [right_arrive a c hc, right_arrive a l hl, right_arrive a _ hl']
    rfl

theorem rewind_rel_arrive' (a : Fin 2) (R : RewindVM → RewindVM → Prop)
    (hR : ∀ u v, R u v → R (arriveRewind a u) (arriveRewind a v)) {s t : GalilVM}
    (h : rewindLens.rel R s t) : rewindLens.rel R (arriveVM' a s) (arriveVM' a t) :=
  rel_arrive' rewindLens (arriveRewind a) R a (fun _ => rfl) (fun _ _ => rfl) hR h

theorem refresh_arrive' {P : Shared} {a : Fin 2} (hP : SharedArrive' P a) (q : ℕ) (first : Fin 9)
    {s : GalilVM} {old o : Bool} (h : refresh (galilFrameS P q first) s old o) :
    refresh (galilFrameS P q first) (arriveVM' a s) old o := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · have := h1 ((hP.onLetter s).mp hl)
    exact this.trans (hP.leftFirst s).symm
  · exact h2 (fun hl' => hl ((hP.onLetter s).mpr hl'))

theorem matchedPlace_arrive' (P : Shared) (q : ℕ) (first : Fin 9) (a : Fin 2) (b : Bool)
    {s t : GalilVM} (h : (galilFrameS P q first).matchedPlace b s t) :
    (galilFrameS P q first).matchedPlace b (arriveVM' a s) (arriveVM' a t) := by
  have h' : t = (if b then {s with replay := GalilScaffoldCounter.dec s.replay} else s) := h
  show arriveVM' a t = (if b then {arriveVM' a s with replay := GalilScaffoldCounter.dec s.replay} else arriveVM' a s)
  subst h'
  cases b <;> rfl

/-- **Tick/arrival commutation with the chain's verifier fed.** No `NoStart`.
Side conditions: `hinit` (`initVM` moves R unguarded), `hrep` (a replaying
comparison moves R unguarded), `hsh` (`beginShiftVM`'s immediate consume
moves the watch verifier unguarded). -/
theorem tick_arrive_comm_or' {P : Shared} {a : Fin 2} (hP : SharedArrive' P a) (q : ℕ) (first : Fin 9)
    (delay : ℕ) {x y : State GalilVM} (h : Tick (galilFrameS P q first) delay x y)
    (hinit : x.ctl.mode = .init → GalilScaffoldChainVerifier.canRight x.vm.right)
    (hrep : x.ctl.mode = .scan → x.ctl.replaying = true → GalilScaffoldChainVerifier.canRight x.vm.right)
    (hsh : x.ctl.mode = .scan → ∀ s', compareFound P q first x.vm s' → ShiftReady s') :
    Tick (galilFrameS P q first) delay (arriveState' a x) (arriveState' a y) ∨
      (x.ctl.mode = .scan ∧ x.ctl.replaying = false ∧ ¬ GalilScaffoldChainVerifier.canRight x.vm.right ∧ y.ctl = x.ctl ∧
        backgroundS P q first (arriveVM' a x.vm) (arriveVM' a y.vm)) := by
  cases h with
  | init c s s' hm h0 =>
    exact Or.inl (.init c _ _ hm (hP.init s s' (hinit hm) h0))
  | scan_wait c s s' hm h0 hb =>
    exact Or.inr ⟨hm, h0.1, h0.2, rfl, backgroundS_arrive' hP q first hb⟩
  | scan_count c s s' hm h0 hc hb =>
    exact Or.inl (.scan_count c _ _ hm (Or.inr (canRight_arrive a s.right)) hc
      (backgroundS_arrive' hP q first hb))
  | scan_match c s s' s'' o hm h0 hc hcmp hmt hpl ho =>
    have ht := Tick.scan_match (F := galilFrameS P q first) (delay := delay) c (arriveVM' a s)
      (arriveVM' a s') (arriveVM' a s'') o hm (Or.inr (canRight_arrive a s.right)) hc
      (compareFound_arrive' hP q first (h0.elim (fun hr => hrep hm hr) id) hcmp) hmt
      (matchedPlace_arrive' P q first a c.replaying hpl) (refresh_arrive' hP q first ho)
    have hx : (galilFrameS P q first).replayExhausted (arriveVM' a s'') =
        (galilFrameS P q first).replayExhausted s'' := hP.replayExhausted s''
    rw [hx] at ht
    exact Or.inl ht
  | scan_shift c s s' s'' hm h0 hc hcmp hmt hr hg hb =>
    exact Or.inl (.scan_shift c _ (arriveVM' a s') _ hm (Or.inr (canRight_arrive a s.right)) hc
      (compareFound_arrive' hP q first (h0.elim (fun hr => hrep hm hr) id) hcmp) hmt hr
      ((hP.shiftGuard s').mpr hg) (hP.beginShift s' s'' (hsh hm s' hcmp) hb))
  | scan_fallback c s s' s'' hm h0 hc hcmp hmt hg hr hb =>
    exact Or.inl (.scan_fallback c _ (arriveVM' a s') _ hm (Or.inr (canRight_arrive a s.right)) hc
      (compareFound_arrive' hP q first (h0.elim (fun hr => hrep hm hr) id) hcmp) hmt
      (hg.imp id (fun hn hs => hn ((hP.shiftGuard s').mp hs))) hr (hP.beginFallback s' s'' hb))
  | shift_one c s s' hm hp h0 =>
    exact Or.inl (.shift_one c _ _ hm hp (shiftOne_arrive' a _ _ h0))
  | shift_done c s o hm hp ho =>
    exact Or.inl (.shift_done c _ o hm hp (refresh_arrive' hP q first ho))
  | copy_one c s s' hm hp h0 =>
    exact Or.inl (.copy_one c _ _ hm hp (fpp_rel_arrive' _ a h0))
  | copy_done c s s' hm hp h0 =>
    exact Or.inl (.copy_done c _ _ hm hp (fpp_rel_arrive' _ a h0))
  | home_start c s s' hm hl h0 =>
    exact Or.inl (.home_start c _ _ hm hl (fpp_rel_arrive' _ a h0))
  | home_step c s s' hm hl h0 =>
    exact Or.inl (.home_step c _ _ hm hl (fpp_rel_arrive' _ a h0))
  | fpp_slice c s s' hm h0 =>
    exact Or.inl (.fpp_slice c _ _ hm (fpp_rel_arrive' _ a h0))
  | fpp_done c s s' hm h0 =>
    exact Or.inl (.fpp_done c _ _ hm (fpp_rel_arrive' _ a h0))
  | markEnd_found c s s' hm he h0 =>
    refine Or.inl (.markEnd_found c _ _ hm he (rewind_rel_arrive' a _ ?_ h0))
    rintro u v ⟨h1, h2⟩
    exact ⟨h1, by subst h2; rfl⟩
  | markEnd_step c s s' hm he h0 =>
    exact Or.inl (.markEnd_step c _ _ hm he (fpp_rel_arrive' _ a h0))
  | choose_select c s s' hm ho hs h0 =>
    refine Or.inl (.choose_select c _ _ hm ho hs (rewind_rel_arrive' a _ ?_ h0))
    rintro u v h2
    subst h2; rfl
  | choose_step c s s' hm hs h0 =>
    refine Or.inl (.choose_step c _ _ hm hs (rewind_rel_arrive' a _ ?_ h0))
    rintro u v ⟨h1, h2⟩
    exact ⟨h1, by subst h2; rfl⟩
  | rewind_done c s s' hm hf h0 =>
    refine Or.inl (.rewind_done c _ _ hm hf (rewind_rel_arrive' a _ ?_ h0))
    rintro u v h2
    subst h2; rfl
  | rewind_one c s s' hm hf hp h0 =>
    refine Or.inl (.rewind_one c _ _ hm hf hp (rewind_rel_arrive' a _ ?_ h0))
    rintro u v ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    subst h2
    simp only [arriveRewind, left_arrive]
  | rewind_pair c s s' hm hf hp h0 =>
    refine Or.inl (.rewind_pair c _ _ hm hf hp (rewind_rel_arrive' a _ ?_ h0))
    rintro u v ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    subst h2
    simp only [arriveRewind, left_arrive]
  | replayStart c s s' o hm h0 ho ho' =>
    have hx : (galilFrameS P q first).replayPos (arriveVM' a s') =
        (galilFrameS P q first).replayPos s' := hP.replayPos s'
    have ht := Tick.replayStart (F := galilFrameS P q first) (delay := delay) c (arriveVM' a s)
      (arriveVM' a s') o hm (hP.replayStart s s' h0) (fun e => ho (hx ▸ e))
      (fun e => refresh_arrive' hP q first (ho' (hx ▸ e)))
    rw [hx] at ht
    exact Or.inl ht
  | restart c s s' hm hb =>
    exact Or.inl (.restart c _ _ hm (hP.restart s s' hb))

/-- A replaying scan state with a positive replay budget inside the frontier
can move R. -/
theorem canRight_of_replay {s : GalilVM} (hf : Frontier s) {m : ℕ} (hm : 0 < m)
    (hr : s.replay = GalilScaffoldCounter.ofNat m) : GalilScaffoldChainVerifier.canRight s.right :=
  GalilReplaySegment.canRight_of_frontier hm (hf m hr)

/-- The main commutation: no `NoStart`, `hrep` discharged from `Frontier` and
a positive replay counter while replaying, `scan_wait` excluded by `hw`. -/
theorem tick_arrive_comm' {P : Shared} {a : Fin 2} (hP : SharedArrive' P a) (q : ℕ) (first : Fin 9)
    (delay : ℕ) {x y : State GalilVM} (h : Tick (galilFrameS P q first) delay x y)
    (hw : ¬ (x.ctl.mode = .scan ∧ x.ctl.replaying = false ∧ ¬ GalilScaffoldChainVerifier.canRight x.vm.right ∧ y.ctl = x.ctl))
    (hinit : x.ctl.mode = .init → GalilScaffoldChainVerifier.canRight x.vm.right)
    (hfront : Frontier x.vm)
    (hlive : x.ctl.mode = .scan → x.ctl.replaying = true →
      ∃ m, 0 < m ∧ x.vm.replay = GalilScaffoldCounter.ofNat m)
    (hsh : x.ctl.mode = .scan → ∀ s', compareFound P q first x.vm s' → ShiftReady s') :
    Tick (galilFrameS P q first) delay (arriveState' a x) (arriveState' a y) := by
  have hrep : x.ctl.mode = .scan → x.ctl.replaying = true → GalilScaffoldChainVerifier.canRight x.vm.right := by
    intro hm hr
    obtain ⟨m, hm0, hmr⟩ := hlive hm hr
    exact canRight_of_replay hfront hm0 hmr
  rcases tick_arrive_comm_or' hP q first delay h hinit hrep hsh with h' | ⟨h1, h2, h3, h4, _⟩
  · exact h'
  · exact absurd ⟨h1, h2, h3, h4⟩ hw


/-! ## 4. Runs with the fixed arrival -/

def RunStep' (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (raw : List (Fin 2))
    (st : ℕ → State GalilVM) (arr : ℕ → ℕ) (k : ℕ) : Prop :=
  (arr (k+1) = arr k ∧
    (Tick (galilFrameS P q first) delay (st k) (st (k+1)) ∨ st (k+1) = st k)) ∨
  (arr (k+1) = arr k + 1 ∧
    ∃ a : Fin 2, raw[arr k]? = some a ∧ st (k+1) = arriveState' a (st k))

def AbstractRun' (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (raw : List (Fin 2))
    (st : ℕ → State GalilVM) (arr : ℕ → ℕ) : Prop :=
  (st 0).ctl = GalilScaffoldController.initial delay ∧ arr 0 = 0 ∧
    ∀ k, RunStep' P q first delay raw st arr k

theorem pal_in_peg_of_latch' {Q Γ : Type} [Fintype Q] [DecidableEq Q]
    [Fintype Γ] [DecidableEq Γ] {t B : ℕ} (hB : 0 < B)
    (M : StructuredMachine (Fin 2) Q Γ t B)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (delay : ℕ)
    (H_letter : ∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w)
    (H_first : ∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM)
    (stOf : List (Fin 2) → ℕ → State GalilVM) (arrOf : List (Fin 2) → ℕ → ℕ)
    (T : List (Fin 2) → ℕ)
    (_H_run : ∀ w : List (Fin 2), 0 < w.length →
      AbstractRun' (Pof w) (qof w) (firstOf w) delay w (stOf w) (arrOf w))
    (H_realize : ∀ w : List (Fin 2), 0 < w.length →
      (M.SAccepts w ↔ LatchTrue (Pof w) (qof w) (firstOf w) w (stOf w) (T w)))
    (H_ledger : LedgerObligation Pof qof firstOf stOf T)
    (H_empty : M.SAccepts []) :
    RecognizedByTotalPEG PAL := by
  refine pal_in_peg_of_structured hB M ?_
  intro w
  rcases w with _ | ⟨a, w⟩
  · simp only [H_empty, true_iff]
    rw [mem_PAL_iff_isPal]
    simp [PalPeg.IsPal]
  · have hlen : 0 < (a :: w).length := by simp
    exact (H_realize _ hlen).trans
      (latch_iff_pal (a :: w) _ (H_letter _) (H_first _) _ _ _ _ (H_ledger _ hlen))

#print axioms arriveChain_idle_iff
#print axioms chainStart_arrive
#print axioms consume_arrive
#print axioms chainStep_arrive
#print axioms chainMatched_arrive
#print axioms chainTick_arrive
#print axioms chainAt_arrive
#print axioms sharedC_arrive'
#print axioms compareFound_arrive'
#print axioms backgroundS_arrive'
#print axioms shiftOne_arrive'
#print axioms tick_arrive_comm_or'
#print axioms tick_arrive_comm'
#print axioms pal_in_peg_of_latch'

end PalPeg.GalilArriveChain
