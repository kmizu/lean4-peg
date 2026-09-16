import PalPeg.GalilLatchTracking
import PalPeg.LocalTracking
import PalPeg.GalilFrontier

/-!
# Ticks commute with arrivals

`tick_arrive_comm_or`: a `Tick (galilFrameS P q first) delay x y` taken
without the letter `a` is a tick `arriveState a x → arriveState a y`, except
`scan_wait` (then only the VM `backgroundS` step survives). Parameters of `P`
are bundled in `SharedArrive` (discharged for `sharedC` by `sharedC_arrive`,
given `centre`/`place` invariance).

Gap found: `ChainVM.copy/back` and the watch machine store their own
verifier `PlaceHead` (a copy of C made at `chainStart`), and `arriveVM` does
not append to it. Hence the chain start is excluded by `NoStart`, and after a
chain start the verifier's FIFO is frozen under `AbstractRun` arrivals.
-/

set_option autoImplicit false

namespace PalPeg.GalilTickArrive

open GalilScaffoldTop GalilScaffoldController GalilScaffoldChainInputSupply LocalTracking
open GalilScaffoldInputHead (PlaceHead)
open GalilScaffoldChainVerifier (canRight)

/-! ## 1. Arrival on one head -/

def arrivePH (a : Fin 2) (p : PlaceHead) : PlaceHead :=
  ⟨{ p.head with incoming := p.head.incoming ++ [a] }, p.gap⟩

theorem arriveVM_eq (a : Fin 2) (s : GalilVM) :
    arriveVM a s = { s with left := arrivePH a s.left, center := arrivePH a s.center, right := arrivePH a s.right } := rfl

theorem canRight_arrive (a : Fin 2) (p : PlaceHead) : canRight (arrivePH a p) := by
  right; right; simp [arrivePH]

theorem canRight_arriveVM (a : Fin 2) (s : GalilVM) : canRight (arriveVM a s).right :=
  canRight_arrive a s.right

theorem read_arrive (a : Fin 2) (p : PlaceHead) :
    GalilScaffoldInputHead.read (arrivePH a p) = GalilScaffoldInputHead.read p := rfl

theorem left_arrive (a : Fin 2) (p : PlaceHead) :
    GalilScaffoldInputHead.left (arrivePH a p) = arrivePH a (GalilScaffoldInputHead.left p) := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g <;> cases ls <;> rfl

theorem right_arrive (a : Fin 2) (p : PlaceHead) (hp : canRight p) :
    GalilScaffoldChainVerifier.right (arrivePH a p) = arrivePH a (GalilScaffoldChainVerifier.right p) := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g
  · rfl
  · cases rs with
    | cons r rs => rfl
    | nil =>
      cases q with
      | nil => simp [canRight] at hp
      | cons b q => rfl

theorem position_arrive (a : Fin 2) (p : PlaceHead) :
    position (arrivePH a p) = position p := rfl


/-! ## 2. Parameters of the shared record -/

/-- The shared record commutes with one arrival. `init` only under
`canRight s.right` (the concrete `initVM` moves R without a guard). -/
structure SharedArrive (P : Shared) (a : Fin 2) : Prop where
  onLetter : ∀ s, P.onLetter (arriveVM a s) ↔ P.onLetter s
  leftFirst : ∀ s, P.leftFirst (arriveVM a s) ↔ P.leftFirst s
  init : ∀ s t, canRight s.right → P.init s t → P.init (arriveVM a s) (arriveVM a t)
  replayStart : ∀ s t, P.replayStart s t → P.replayStart (arriveVM a s) (arriveVM a t)
  replayPos : ∀ s, P.replayPos (arriveVM a s) = P.replayPos s
  replayExhausted : ∀ s, P.replayExhausted (arriveVM a s) = P.replayExhausted s
  shiftGuard : ∀ s, P.shiftGuard (arriveVM a s) ↔ P.shiftGuard s
  beginShift : ∀ s t, P.beginShift s t → P.beginShift (arriveVM a s) (arriveVM a t)
  beginFallback : ∀ s t, P.beginFallback s t → P.beginFallback (arriveVM a s) (arriveVM a t)
  restart : ∀ s t, P.restart s t → P.restart (arriveVM a s) (arriveVM a t)
  centre : ∀ s, P.centre (arriveVM a s) = P.centre s
  place : ∀ s, P.place (arriveVM a s) = P.place s

/-- The concrete shared record `sharedC` (with `onLetterVM raw`, `leftFirstVM`)
commutes with arrivals as soon as its `centre`/`place` decoders do. -/
theorem sharedC_arrive (raw : List (Fin 2)) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) (a : Fin 2)
    (hc : ∀ s, centre (arriveVM a s) = centre s) (hp : ∀ s, place (arriveVM a s) = place s) :
    SharedArrive (sharedC (onLetterVM raw) leftFirstVM centre place entry) a where
  onLetter := fun _ => Iff.rfl
  leftFirst := fun _ => Iff.rfl
  init := by
    intro s t hcr h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
    have hr : GalilScaffoldChainVerifier.right (arriveVM a s).right
        = arrivePH a (GalilScaffoldChainVerifier.right s.right) := right_arrive a s.right hcr
    refine ⟨?_, ?_, ?_, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
    · rw [hr, ← h1]; rfl
    · rw [hr, ← h2]; rfl
    · rw [hr, ← h3]; rfl
  replayStart := by
    intro s t h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
    refine ⟨h1, ?_, ?_, ?_, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ <;>
      (show arrivePH a _ = arrivePH a _; congr 1)
  replayPos := fun _ => rfl
  replayExhausted := fun _ => rfl
  shiftGuard := fun _ => Iff.rfl
  beginShift := by
    rintro s t ⟨w, hw, ht⟩
    exact ⟨w, hw, by subst ht; rfl⟩
  beginFallback := by
    rintro s t ⟨p, ht⟩
    exact ⟨p, by rw [ht]; rfl⟩
  restart := by
    rintro s t ⟨w, hw, h1, h2, h3, ht⟩
    exact ⟨w, hw, h1, h2, h3, by subst ht; rfl⟩
  centre := hc
  place := hp


/-! ## 3. Scan relations: search, chain, comparison, background -/

theorem searchLens_arrive (a : Fin 2) (s : GalilVM) : searchLens.get (arriveVM a s) = searchLens.get s := rfl

theorem searchEffect_arrive {P : Shared} {a : Fin 2} (hP : SharedArrive P a) (b : Bool)
    (s : GalilVM) (vq : SearchVM) : searchEffect P b (arriveVM a s) vq ↔ searchEffect P b s vq := by
  unfold searchEffect
  rw [hP.place s]
  exact Iff.rfl

/-- `chainAt` only mentions the stored verifier `ver` in its chain-start
disjunct (idle chain, search `found`). -/
theorem chainAt_ver {b found : Bool} {ans : GalilScaffoldTape.Tape} {c : Fin 3}
    {w : GalilScaffoldPlace.Place} {ver ver' : PlaceHead} {r : GalilScaffoldCounter.Counter}
    {x z : ChainVM} (h : chainAt b found ans c w ver r x z) (hn : x = .idle → found = false) :
    chainAt b found ans c w ver' r x z := by
  rcases h with h | h | ⟨hx, hf, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd hf (by rw [hn hx]; decide)

/-- **No chain start** from a scan state: with an idle chain, no search
effect from `s` lands in `found`. This is the side condition under which the
chain start (which *stores a copy of C* inside `ChainVM.copy`, a head that
`arriveVM` does not reach) is excluded. -/
def NoStart (P : Shared) (s : GalilVM) : Prop :=
  s.chain = .idle → ∀ (b : Bool) (vq : SearchVM), searchEffect P b s vq → vq.search.mode ≠ .found

theorem compareFound_arrive {P : Shared} {a : Fin 2} (hP : SharedArrive P a) (q : ℕ) (first : Fin 9)
    {s t : GalilVM} (hcr : canRight s.right) (hns : NoStart P s)
    (h : compareFound P q first s t) : compareFound P q first (arriveVM a s) (arriveVM a t) := by
  obtain ⟨vs, vq, b, hl, hr, hb, hse, hch, ht⟩ := h
  refine ⟨⟨arrivePH a vs.left, arrivePH a vs.right, vs.chain⟩, vq, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show arrivePH a vs.left = GalilScaffoldInputHead.left (arrivePH a s.left)
    rw [left_arrive, hl]
  · show arrivePH a vs.right = GalilScaffoldChainVerifier.right (arrivePH a s.right)
    rw [right_arrive a _ hcr, hr]
  · exact hb
  · exact (searchEffect_arrive hP b s vq).mpr hse
  · rw [hP.centre, hP.place]
    refine chainAt_ver hch ?_
    intro hx
    have := hns hx b vq hse
    simpa using this
  · subst ht
    cases b <;> rfl

theorem backgroundS_arrive {P : Shared} {a : Fin 2} (hP : SharedArrive P a) (q : ℕ) (first : Fin 9)
    {s t : GalilVM} (hns : NoStart P s)
    (h : backgroundS P q first s t) : backgroundS P q first (arriveVM a s) (arriveVM a t) := by
  obtain ⟨hl, hr, hse, hch, hset⟩ := h
  refine ⟨?_, ?_, (searchEffect_arrive hP false s _).mpr hse, ?_, ?_⟩
  · show arrivePH a t.left = arrivePH a s.left
    rw [hl]
  · show arrivePH a t.right = arrivePH a s.right
    rw [hr]
  · rw [hP.centre, hP.place]
    refine chainAt_ver hch ?_
    intro hx
    have := hns hx false _ hse
    show decide ((searchLens.get t).search.mode = .found) = false
    simpa using this
  · calc arriveVM a t
        = arriveVM a (searchLens.set (scanLens.set s (scanLens.get t)) (searchLens.get t)) :=
          congrArg _ hset
      _ = _ := rfl


/-! ## 4. Lens-pulled relations of the other modes -/

theorem rel_arrive {σ' : Type} (L : Lens GalilVM σ') (arrV : σ' → σ') (R : σ' → σ' → Prop) (a : Fin 2)
    (hget : ∀ s, L.get (arriveVM a s) = arrV (L.get s))
    (hset : ∀ s v, L.set (arriveVM a s) (arrV v) = arriveVM a (L.set s v))
    (hR : ∀ u v, R u v → R (arrV u) (arrV v)) {s t : GalilVM} (h : L.rel R s t) :
    L.rel R (arriveVM a s) (arriveVM a t) := by
  refine ⟨?_, ?_⟩
  · rw [hget, hget]; exact hR _ _ h.1
  · rw [hget, hset]; exact congrArg _ h.2

/-- Relations on the FPP component do not see the heads. -/
theorem fpp_rel_arrive (R : FppControl.State → FppControl.State → Prop) (a : Fin 2) {s t : GalilVM}
    (h : fppLens.rel R s t) : fppLens.rel R (arriveVM a s) (arriveVM a t) :=
  rel_arrive fppLens id R a (fun _ => rfl) (fun _ _ => rfl) (fun _ _ h => h) h

def arriveShift (a : Fin 2) (v : ShiftVM) : ShiftVM :=
  ⟨⟨arrivePH a v.shift.center, arrivePH a v.shift.left, v.shift.remaining, v.shift.radius, v.shift.length⟩,
    v.chain, v.cycle⟩

def arriveRewind (a : Fin 2) (v : RewindVM) : RewindVM :=
  ⟨v.fpp, arrivePH a v.left, arrivePH a v.center, arrivePH a v.right, v.length, v.radius⟩

theorem shiftOne_arrive (a : Fin 2) (on lf : ShiftVM → Prop) {s t : GalilVM}
    (h : shiftLens.rel (shiftFrame on lf).shiftOne s t) :
    shiftLens.rel (shiftFrame on lf).shiftOne (arriveVM a s) (arriveVM a t) := by
  refine rel_arrive shiftLens (arriveShift a) _ a (fun _ => rfl) (fun _ _ => rfl) ?_ h
  rintro ⟨⟨c, l, rem, rad, len⟩, ch, cy⟩ v ⟨hc, hl, hl', w, hw, hv⟩
  refine ⟨canRight_arrive a c, canRight_arrive a l, ?_, w, hw, ?_⟩
  · show canRight (GalilScaffoldChainVerifier.right (arrivePH a l))
    rw [right_arrive a l hl]; exact canRight_arrive a _
  · subst hv
    show arriveShift a ⟨shiftTick ⟨c, l, rem, rad, len⟩, _, _⟩ = ⟨shiftTick ⟨arrivePH a c, arrivePH a l, rem, rad, len⟩, _, _⟩
    simp only [arriveShift, shiftTick]
    rw [right_arrive a c hc, right_arrive a l hl, right_arrive a _ hl']

theorem rewind_rel_arrive (a : Fin 2) (R : RewindVM → RewindVM → Prop)
    (hR : ∀ u v, R u v → R (arriveRewind a u) (arriveRewind a v)) {s t : GalilVM}
    (h : rewindLens.rel R s t) : rewindLens.rel R (arriveVM a s) (arriveVM a t) :=
  rel_arrive rewindLens (arriveRewind a) R a (fun _ => rfl) (fun _ _ => rfl) hR h

theorem marks_arrive (a : Fin 2) (u : RewindVM) : (arriveRewind a u).marks = u.marks := rfl


/-! ## 5. The commutation -/

theorem refresh_arrive {P : Shared} {a : Fin 2} (hP : SharedArrive P a) (q : ℕ) (first : Fin 9)
    {s : GalilVM} {old o : Bool} (h : refresh (galilFrameS P q first) s old o) :
    refresh (galilFrameS P q first) (arriveVM a s) old o := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · have := h1 ((hP.onLetter s).mp hl)
    exact this.trans (hP.leftFirst s).symm
  · exact h2 (fun hl' => hl ((hP.onLetter s).mpr hl'))

theorem matchedPlace_arrive (P : Shared) (q : ℕ) (first : Fin 9) (a : Fin 2) (b : Bool)
    {s t : GalilVM} (h : (galilFrameS P q first).matchedPlace b s t) :
    (galilFrameS P q first).matchedPlace b (arriveVM a s) (arriveVM a t) := by
  have h' : t = (if b then {s with replay := GalilScaffoldCounter.dec s.replay} else s) := h
  show arriveVM a t = (if b then {arriveVM a s with replay := GalilScaffoldCounter.dec s.replay} else arriveVM a s)
  subst h'
  cases b <;> rfl

/-- **Frame-wide tick/arrival commutation.** Every tick of `galilFrameS P`
taken without the new letter `a` is still a tick after `a` arrives, except
`scan_wait`, which then shows up as the right disjunct: the VM part is still a
`backgroundS` step after the arrival, but the controller cannot stay put
(after the arrival `canRight` holds, so the scan counts instead).

Side conditions (each genuinely needed, see the report):
* `hinit`: `init` moves R *without* a `canRight` guard;
* `hrep`: a replaying comparison moves R without the `available` guard;
* `hns` (`NoStart`): the chain start stores a copy of the C head inside
  `ChainVM.copy`; `arriveVM` does not append to heads stored in the chain. -/
theorem tick_arrive_comm_or {P : Shared} {a : Fin 2} (hP : SharedArrive P a) (q : ℕ) (first : Fin 9)
    (delay : ℕ) {x y : State GalilVM} (h : Tick (galilFrameS P q first) delay x y)
    (hinit : x.ctl.mode = .init → canRight x.vm.right)
    (hrep : x.ctl.mode = .scan → x.ctl.replaying = true → canRight x.vm.right)
    (hns : x.ctl.mode = .scan → NoStart P x.vm) :
    Tick (galilFrameS P q first) delay (arriveState a x) (arriveState a y) ∨
      (x.ctl.mode = .scan ∧ x.ctl.replaying = false ∧ ¬ canRight x.vm.right ∧ y.ctl = x.ctl ∧
        backgroundS P q first (arriveVM a x.vm) (arriveVM a y.vm)) := by
  cases h with
  | init c s s' hm h0 =>
    exact Or.inl (.init c _ _ hm (hP.init s s' (hinit hm) h0))
  | scan_wait c s s' hm h0 hb =>
    exact Or.inr ⟨hm, h0.1, h0.2, rfl, backgroundS_arrive hP q first (hns hm) hb⟩
  | scan_count c s s' hm h0 hc hb =>
    exact Or.inl (.scan_count c _ _ hm (Or.inr (canRight_arrive a s.right)) hc
      (backgroundS_arrive hP q first (hns hm) hb))
  | scan_match c s s' s'' o hm h0 hc hcmp hmt hpl ho =>
    have ht := Tick.scan_match (F := galilFrameS P q first) (delay := delay) c (arriveVM a s)
      (arriveVM a s') (arriveVM a s'') o hm (Or.inr (canRight_arrive a s.right)) hc
      (compareFound_arrive hP q first (h0.elim (fun hr => hrep hm hr) id) (hns hm) hcmp) hmt
      (matchedPlace_arrive P q first a c.replaying hpl) (refresh_arrive hP q first ho)
    have hx : (galilFrameS P q first).replayExhausted (arriveVM a s'') =
        (galilFrameS P q first).replayExhausted s'' := hP.replayExhausted s''
    rw [hx] at ht
    exact Or.inl ht
  | scan_shift c s s' s'' hm h0 hc hcmp hmt hr hg hb =>
    exact Or.inl (.scan_shift c _ (arriveVM a s') _ hm (Or.inr (canRight_arrive a s.right)) hc
      (compareFound_arrive hP q first (h0.elim (fun hr => hrep hm hr) id) (hns hm) hcmp) hmt hr
      ((hP.shiftGuard s').mpr hg) (hP.beginShift s' s'' hb))
  | scan_fallback c s s' s'' hm h0 hc hcmp hmt hg hr hb =>
    exact Or.inl (.scan_fallback c _ (arriveVM a s') _ hm (Or.inr (canRight_arrive a s.right)) hc
      (compareFound_arrive hP q first (h0.elim (fun hr => hrep hm hr) id) (hns hm) hcmp) hmt
      (hg.imp id (fun hn hs => hn ((hP.shiftGuard s').mp hs))) hr (hP.beginFallback s' s'' hb))
  | shift_one c s s' hm hp h0 =>
    exact Or.inl (.shift_one c _ _ hm hp (shiftOne_arrive a _ _ h0))
  | shift_done c s o hm hp ho =>
    exact Or.inl (.shift_done c _ o hm hp (refresh_arrive hP q first ho))
  | copy_one c s s' hm hp h0 =>
    exact Or.inl (.copy_one c _ _ hm hp (fpp_rel_arrive _ a h0))
  | copy_done c s s' hm hp h0 =>
    exact Or.inl (.copy_done c _ _ hm hp (fpp_rel_arrive _ a h0))
  | home_start c s s' hm hl h0 =>
    exact Or.inl (.home_start c _ _ hm hl (fpp_rel_arrive _ a h0))
  | home_step c s s' hm hl h0 =>
    exact Or.inl (.home_step c _ _ hm hl (fpp_rel_arrive _ a h0))
  | fpp_slice c s s' hm h0 =>
    exact Or.inl (.fpp_slice c _ _ hm (fpp_rel_arrive _ a h0))
  | fpp_done c s s' hm h0 =>
    exact Or.inl (.fpp_done c _ _ hm (fpp_rel_arrive _ a h0))
  | markEnd_found c s s' hm he h0 =>
    refine Or.inl (.markEnd_found c _ _ hm he (rewind_rel_arrive a _ ?_ h0))
    rintro u v ⟨h1, h2⟩
    exact ⟨h1, by subst h2; rfl⟩
  | markEnd_step c s s' hm he h0 =>
    exact Or.inl (.markEnd_step c _ _ hm he (fpp_rel_arrive _ a h0))
  | choose_select c s s' hm ho hs h0 =>
    refine Or.inl (.choose_select c _ _ hm ho hs (rewind_rel_arrive a _ ?_ h0))
    rintro u v h2
    subst h2; rfl
  | choose_step c s s' hm hs h0 =>
    refine Or.inl (.choose_step c _ _ hm hs (rewind_rel_arrive a _ ?_ h0))
    rintro u v ⟨h1, h2⟩
    exact ⟨h1, by subst h2; rfl⟩
  | rewind_done c s s' hm hf h0 =>
    refine Or.inl (.rewind_done c _ _ hm hf (rewind_rel_arrive a _ ?_ h0))
    rintro u v h2
    subst h2; rfl
  | rewind_one c s s' hm hf hp h0 =>
    refine Or.inl (.rewind_one c _ _ hm hf hp (rewind_rel_arrive a _ ?_ h0))
    rintro u v ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    subst h2
    simp only [arriveRewind, left_arrive]
  | rewind_pair c s s' hm hf hp h0 =>
    refine Or.inl (.rewind_pair c _ _ hm hf hp (rewind_rel_arrive a _ ?_ h0))
    rintro u v ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    subst h2
    simp only [arriveRewind, left_arrive]
  | replayStart c s s' o hm h0 ho ho' =>
    have hx : (galilFrameS P q first).replayPos (arriveVM a s') =
        (galilFrameS P q first).replayPos s' := hP.replayPos s'
    have ht := Tick.replayStart (F := galilFrameS P q first) (delay := delay) c (arriveVM a s)
      (arriveVM a s') o hm (hP.replayStart s s' h0) (fun e => ho (hx ▸ e))
      (fun e => refresh_arrive hP q first (ho' (hx ▸ e)))
    rw [hx] at ht
    exact Or.inl ht
  | restart c s s' hm hb =>
    exact Or.inl (.restart c _ _ hm (hP.restart s s' hb))

/-- The form asked for: every tick other than `scan_wait` commutes. Since
`canRight (arriveVM a s).right` always holds (`canRight_arriveVM`), the
alternative "`¬ canRight` after the arrival" is vacuous, so the exclusion of
`scan_wait` is stated as `hw`: the source is not a waiting scan state. -/
theorem tick_arrive_comm {P : Shared} {a : Fin 2} (hP : SharedArrive P a) (q : ℕ) (first : Fin 9)
    (delay : ℕ) {x y : State GalilVM} (h : Tick (galilFrameS P q first) delay x y)
    (hw : ¬ (x.ctl.mode = .scan ∧ x.ctl.replaying = false ∧ ¬ canRight x.vm.right ∧ y.ctl = x.ctl))
    (hinit : x.ctl.mode = .init → canRight x.vm.right)
    (hrep : x.ctl.mode = .scan → x.ctl.replaying = true → canRight x.vm.right)
    (hns : x.ctl.mode = .scan → NoStart P x.vm) :
    Tick (galilFrameS P q first) delay (arriveState a x) (arriveState a y) := by
  rcases tick_arrive_comm_or hP q first delay h hinit hrep hns with h' | ⟨h1, h2, h3, h4, _⟩
  · exact h'
  · exact absurd ⟨h1, h2, h3, h4⟩ hw

#print axioms arriveVM_eq
#print axioms canRight_arrive
#print axioms canRight_arriveVM
#print axioms read_arrive
#print axioms left_arrive
#print axioms right_arrive
#print axioms position_arrive
#print axioms sharedC_arrive
#print axioms searchEffect_arrive
#print axioms chainAt_ver
#print axioms compareFound_arrive
#print axioms backgroundS_arrive
#print axioms rel_arrive
#print axioms fpp_rel_arrive
#print axioms shiftOne_arrive
#print axioms rewind_rel_arrive
#print axioms refresh_arrive
#print axioms matchedPlace_arrive
#print axioms tick_arrive_comm_or
#print axioms tick_arrive_comm

end PalPeg.GalilTickArrive
