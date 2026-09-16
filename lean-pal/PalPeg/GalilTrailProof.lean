import PalPeg.GalilLookRefined
import PalPeg.GalilBootVM

/-!
# The trailing invariant in frontier form

`GalilLookRefined.Trail` asks two things that the machine does **not** satisfy:

* `rightStack`: the right head has an empty right stack;
* `ver`: the chain verifier has an empty right stack (and stands left of `R`).

Both fail after a fallback.  `GalilScaffoldTopFallbackAll.fallback_replayStart_All`
puts `L`, `R` and `C` at `GalilScaffoldInputHead.left^[r] s.right`, and
`GalilScaffoldTopRewind`'s `rewindPair` moves `C` (and `L`) left one place per tick;
`GalilScaffoldInputHead.left` on a letter place is `moveLeft`, which *pushes the focus
onto the right stack* (§1, `left_left_stack`).  `chainStart` copies `C` into the chain
verifier, so the verifier inherits the stack.  §1 exhibits a concrete state of exactly
that shape (`cx`) with `¬ Trail cxWord 0 cx`.

The fix is the one already used for `L` and `C`: state the clause as a *frontier*
(consumption) bound.  `Trails raw m d p` says the head has consumed at most `m+1`
letters, and — only when its right stack is empty — stands `d` places left of the
checkpoint place `2(m+1)-1`.  This is exactly what the lookahead needs, because a
right move over a non-empty right stack consumes nothing
(`usedPH_right_of_stack`, `usedPH_right_right_of_stack`).

`TrailF` is `Trail` with `R` and the verifier weakened this way; it is implied by
`Trail` (§3), it still yields the pointwise bound `needL' ≤ m+1` (§2), and it holds at
the boot state (§4).  §5 has the two head-arithmetic step lemmas the trace induction
needs: a rewind preserves `Trails` (this is what fails for `Trail`), and so does a
budgeted right move.

**Not proved here:** `H_trailF` itself.  The remaining gap is the trace induction
(`R`'s place bound before checkpoint `m+1`, and the verifier/`R` coupling under
`ChainTick`), which needs the per-tick analysis of `galilFrameS`, not head arithmetic.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PalPeg.GalilTrailProof

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTruncTick
open PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2 PalPeg.GalilLookRefined

abbrev PH := GalilScaffoldInputHead.PlaceHead

/-! ## 1. The empty-right-stack clauses are false -/

/-- **Rewinding fills the right stack.**  Two `left` moves from a head that is not at
the clipped origin leave a non-empty right stack, whatever the starting parity: one of
the two moves is a `moveLeft`, which pushes the focus onto the right stack. -/
theorem left_left_stack (p : PH) (h : 0 < p.head.left.length) :
    (GalilScaffoldInputHead.left (GalilScaffoldInputHead.left p)).head.right ≠ [] := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases ls with
  | nil => simp at h
  | cons a ls =>
    cases g <;>
      simp [GalilScaffoldInputHead.left, GalilScaffoldInputHead.moveLeft]

/-- The two-letter word of the counterexample. -/
def cxWord : List (Fin 2) := [0, 1]

/-- `R` after one letter, rewound two places: the shape `fallback_replayStart_All`
gives to `L`, `R` and `C` (with `chosenRadius = 2`). -/
def cxHead : PH := ⟨⟨none, [], [some 0], [1]⟩, true⟩

theorem cxHead_eq : cxHead = GalilScaffoldInputHead.left (GalilScaffoldInputHead.left
    (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right
      ⟨⟨none, [], [], cxWord⟩, true⟩))) := rfl

/-- The counterexample state: every head rewound, and a chain started on the rewound
centre (`chainStart` copies `C` into the verifier). -/
def cx : State GalilVM :=
  ⟨GalilScaffoldController.initial 2048,
    {GalilBootVM.initVM0 cxWord with
      left := cxHead, center := cxHead, right := cxHead,
      chain := chainStart GalilScaffoldTape.reset 0 GalilBootVM.emptyPlace cxHead
        GalilScaffoldCounter.reset}⟩

/-- **`Trail` fails on it at `rightStack`**: `R`'s right stack is `[some 0]`. -/
theorem not_trail_cx : ¬ Trail cxWord 0 cx := fun h => absurd h.rightStack (by decide)

/-- **`Trail` fails on it at `ver`** as well: the chain verifier is the rewound centre,
so its right stack is `[some 0]` too. -/
theorem not_trail_cx_ver : ¬ Trail cxWord 0 cx :=
  fun h => absurd (h.ver cxHead rfl).2.2.1 (by decide)

/-! ## 2. The frontier form -/

/-- **The weakened head clause.**  The head is represented and sane, it has consumed at
most `m+1` letters, and — only when its right stack is empty — it stands at least `d`
places left of the checkpoint place `2(m+1)-1`.  `d = 0` is what a zero/one-move
lookahead needs, `d = 1` what the two-move (positive lag) lookahead needs. -/
structure Trails (raw : List (Fin 2)) (m d : ℕ) (p : PH) : Prop where
  rep : GalilScaffoldInputTrace.Represents p.head raw
  sane : GalilFrontMono.Sane p
  used : usedPH raw.length p ≤ m + 1
  pos : p.head.right = [] → position p + d ≤ 2 * (m + 1) - 1

theorem trails_mono {raw : List (Fin 2)} {m d d' : ℕ} {p : PH} (h : Trails raw m d p)
    (hd : d' ≤ d) : Trails raw m d' p :=
  ⟨h.rep, h.sane, h.used, fun hs => le_trans (by omega) (h.pos hs)⟩

/-- A right move over a non-empty right stack consumes nothing. -/
theorem usedPH_right_of_stack (n : ℕ) (p : PH) (h : p.head.right ≠ []) :
    usedPH n (GalilScaffoldChainVerifier.right p) = usedPH n p := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases rs with
  | nil => simp at h
  | cons a rs => cases g <;> rfl

/-- Two right moves over a non-empty right stack consume nothing either: the stack
absorbs the one move that could have popped the FIFO. -/
theorem usedPH_right_right_of_stack (n : ℕ) (p : PH) (h : p.head.right ≠ []) :
    usedPH n (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right p)) =
      usedPH n p := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases rs with
  | nil => simp at h
  | cons a rs => cases g <;> rfl

theorem usedPH_right_le_of_trails {raw : List (Fin 2)} {m : ℕ} {p : PH}
    (h : Trails raw m 0 p) :
    usedPH raw.length (GalilScaffoldChainVerifier.right p) ≤ m + 1 := by
  by_cases hs : p.head.right = []
  · exact GalilNeedBound.usedPH_right_le_of_position raw p m h.rep h.sane hs
      (by have := h.pos hs; omega)
  · rw [usedPH_right_of_stack _ _ hs]; exact h.used

theorem usedPH_right_right_le_of_trails {raw : List (Fin 2)} {m : ℕ} {p : PH}
    (h : Trails raw m 1 p) :
    usedPH raw.length
      (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right p)) ≤ m + 1 := by
  by_cases hs : p.head.right = []
  · exact usedPH_right_right_le_of_position raw p m h.rep h.sane hs (h.pos hs)
  · rw [usedPH_right_right_of_stack _ _ hs]; exact h.used

/-- **The trailing invariant, frontier form.**  `L` and `C` as before; `R` and the chain
verifier only up to consumption, with a place bound when their right stack is empty; the
positive-lag watch verifier with one extra place of slack. -/
structure TrailF (raw : List (Fin 2)) (m : ℕ) (x : State GalilVM) : Prop where
  left : FrontLe raw m x.vm.left
  center : FrontLe raw m x.vm.center
  right : Trails raw m 0 x.vm.right
  ver : ∀ p, verOf x.vm.chain = some p → Trails raw m 0 p
  lagPos : ∀ w, x.vm.chain = .watch w → GalilScaffoldCounter.positive w.lag = true →
    Trails raw m 1 w.machine.verifier

theorem usedChain_le_of_trailF (raw : List (Fin 2)) (m : ℕ) (x : State GalilVM)
    (ht : TrailF raw m x) : usedChain raw.length x.vm.chain ≤ m + 1 := by
  unfold usedChain
  cases hv : verOf x.vm.chain with
  | none => exact Nat.zero_le _
  | some p => exact (ht.ver p hv).used

theorem lookChain'_le_of_trailF (raw : List (Fin 2)) (m : ℕ) (x : State GalilVM)
    (ht : TrailF raw m x) : lookChain' raw.length x.vm.chain ≤ m + 1 := by
  have hver := ht.ver
  have hlag := ht.lagPos
  cases hx : x.vm.chain with
  | idle => exact Nat.zero_le _
  | copy t h p v lag margin ver =>
    rw [hx] at hver
    exact (hver ver rfl).used
  | back v h lag margin ver =>
    rw [hx] at hver
    exact usedPH_right_le_of_trails (hver ver rfl)
  | watch w =>
    rw [hx] at hver
    simp only [lookChain']
    split_ifs with hp
    · exact usedPH_right_right_le_of_trails (hlag w hx hp)
    · exact usedPH_right_le_of_trails (hver w.machine.verifier rfl)
  | broken w =>
    rw [hx] at hver
    exact (hver w.machine.verifier rfl).used

/-- **The pointwise refined need bound under the weakened trailing invariant.** -/
theorem needL'_le_of_trailF (raw : List (Fin 2)) (st : ℕ → State GalilVM) (m i : ℕ)
    (ht : TrailF raw m (st i)) : needL' raw st i ≤ m + 1 := by
  have hL := usedPH_le_of_frontLe raw m _ ht.left
  have hC := usedPH_le_of_frontLe raw m _ ht.center
  have hR := ht.right.used
  have hR' := usedPH_right_le_of_trails ht.right
  have hch := usedChain_le_of_trailF raw m (st i) ht
  have hlc := lookChain'_le_of_trailF raw m (st i) ht
  unfold needL' needS usedVM look'
  split_ifs <;> omega

/-- (B'') The weakened trailing invariant along every pre-loaded trace. -/
def H_trailF (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → TrailF w m (st i)

theorem needL'_of_trailF (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (h : H_trailF centre place entry q first) : H_needL' centre place entry q first :=
  fun w hw st Tc hP m hm i hi => needL'_le_of_trailF w st m i (h w hw st Tc hP m hm i hi)

/-- **`PAL ∈ PEG`, refined lookahead, need bound reduced to the weakened trailing
invariant.** -/
theorem pal_in_peg_final2'_trailF (entry q : ℕ) (first : Fin 9)
    (hA : H_oracle centreC placeC entry q first)
    (hB_trail : H_trailF centreC placeC entry q first)
    (hB_base : H_base centreC placeC entry q first)
    (hC : H_realizeL' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final2' entry q first hA (needL'_of_trailF _ _ entry q first hB_trail) hB_base hC

/-- The counterexample head satisfies the weakened clause: it has consumed one letter
(`m+1 = 1`), and its place bound is vacuous because the right stack is non-empty. -/
theorem trails_cxHead (d : ℕ) : Trails cxWord 0 d cxHead :=
  ⟨⟨[], [0], [1], rfl, rfl⟩, Or.inl rfl, by decide, fun hs => absurd hs (by decide)⟩

theorem frontLe_cxHead : FrontLe cxWord 0 cxHead :=
  ⟨⟨[], [0], [1], rfl, rfl⟩, Or.inl rfl, by decide⟩

/-- **The state `Trail` rejects is accepted by `TrailF`.**  So the weakening is exactly
what the rewound heads need. -/
theorem trailF_cx : TrailF cxWord 0 cx := by
  refine ⟨frontLe_cxHead, frontLe_cxHead, trails_cxHead 0, fun p hv => ?_, fun w hx _ => ?_⟩
  · have hp : cxHead = p := Option.some.inj hv
    exact hp ▸ trails_cxHead 0
  · exact ChainVM.noConfusion hx

/-! ## 3. The weakened invariant really is weaker -/

theorem trails_of_trail_ver {raw : List (Fin 2)} {m : ℕ} {x : State GalilVM} {p : PH}
    (ht : Trail raw m x) (hv : verOf x.vm.chain = some p) : Trails raw m 0 p := by
  obtain ⟨hr, hs, hrl, hpos⟩ := ht.ver p hv
  exact ⟨hr, hs, GalilNeedBound.usedPH_le_of_position raw p m hr hs hrl
    (le_trans hpos ht.rightPos), fun _ => by have := ht.rightPos; omega⟩

theorem trailF_of_trail {raw : List (Fin 2)} {m : ℕ} {x : State GalilVM} (ht : Trail raw m x) :
    TrailF raw m x := by
  refine ⟨ht.left, ht.center, ⟨ht.rightRep, ht.rightSane, ?_, fun _ => by
      have := ht.rightPos; omega⟩, fun p hv => trails_of_trail_ver ht hv, fun w hx hp => ?_⟩
  · exact GalilNeedBound.usedPH_le_of_position raw _ m ht.rightRep ht.rightSane ht.rightStack
      ht.rightPos
  · obtain ⟨hr, hs, hrl, hpos⟩ := ht.ver w.machine.verifier (by rw [hx]; rfl)
    exact ⟨hr, hs, GalilNeedBound.usedPH_le_of_position raw _ m hr hs hrl
      (le_trans hpos ht.rightPos), fun _ => by
        have := ht.lagPos w hx hp; have := ht.rightPos; omega⟩

theorem h_trailF_of_h_trail (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (h : H_trail centre place entry q first) : H_trailF centre place entry q first :=
  fun w hw st Tc hP m hm i hi => trailF_of_trail (h w hw st Tc hP m hm i hi)

/-! ## 4. The base case: the boot state -/

theorem frontLe_initialHead (w : List (Fin 2)) (m : ℕ) :
    FrontLe w m ⟨⟨none, [], [], w⟩, true⟩ :=
  ⟨⟨[], [], w, rfl, rfl⟩, Or.inl rfl, by simp [position]⟩

theorem trails_initialHead (w : List (Fin 2)) (m d : ℕ) (hd : d ≤ 1) :
    Trails w m d ⟨⟨none, [], [], w⟩, true⟩ :=
  ⟨⟨[], [], w, rfl, rfl⟩, Or.inl rfl, by simp [usedPH], by
    simp only [position, if_true, List.length_nil, Nat.mul_zero]; omega⟩

/-- **The boot state satisfies the weakened invariant** for every checkpoint bound. -/
theorem trailF_boot (w : List (Fin 2)) (m : ℕ) : TrailF w m (boot w) := by
  refine ⟨frontLe_initialHead w m, frontLe_initialHead w m, trails_initialHead w m 0 (by omega),
    fun p hv => ?_, fun v hx _ => ?_⟩
  · exact absurd hv (by simp [boot, GalilBootVM.initVM0, verOf])
  · exact absurd hx (by simp [boot, GalilBootVM.initVM0])

/-! ## 5. Head arithmetic for the trace induction -/

theorem focus_ne_of_sane {raw : List (Fin 2)} {p : PH}
    (hr : GalilScaffoldInputTrace.Represents p.head raw) (hs : GalilFrontMono.Sane p)
    (hg : p.gap = false) : p.head.focus ≠ none := by
  obtain ⟨xs, rs, q, hh, -⟩ := hr
  simp only [GalilFrontMono.Sane, hg, Bool.false_eq_true, false_or, hh] at hs ⊢
  cases xs with
  | nil => simp [GalilScaffoldInputHead.layout] at hs
  | cons a xs => simp [GalilScaffoldInputHead.layout]

theorem usedPH_left (n : ℕ) (p : PH) :
    usedPH n (GalilScaffoldInputHead.left p) = usedPH n p := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g with
  | false => cases ls <;> rfl
  | true => rfl

/-- **A rewind step preserves the weakened clause.**  (It does not preserve `Trail`:
by `left_left_stack` the right stack fills up.)  The side condition is exactly that the
rewound head is still not at the clipped origin. -/
theorem trails_left {raw : List (Fin 2)} {m d : ℕ} {p : PH} (h : Trails raw m d p)
    (hs : GalilFrontMono.Sane (GalilScaffoldInputHead.left p)) :
    Trails raw m d (GalilScaffoldInputHead.left p) := by
  refine ⟨?_, hs, by rw [usedPH_left]; exact h.used, ?_⟩
  · cases hg : p.gap with
    | false =>
      have hf := focus_ne_of_sane h.rep h.sane hg
      have := (GalilScaffoldInputTrace.left_represents h.rep hf).2
      simpa [GalilScaffoldInputHead.left, hg] using this
    | true => simpa [GalilScaffoldInputHead.left, hg] using h.rep
  · intro hz
    have hsane := h.sane
    have hpos := h.pos
    obtain ⟨⟨f, ls, rs, q⟩, g⟩ := p
    cases g with
    | false =>
      exfalso
      simp only [GalilFrontMono.Sane, Bool.false_eq_true, false_or] at hsane
      cases ls with
      | nil => simp at hsane
      | cons a ls =>
        simp [GalilScaffoldInputHead.left, GalilScaffoldInputHead.moveLeft] at hz
    | true =>
      have h0 : rs = [] := by simpa [GalilScaffoldInputHead.left] using hz
      subst h0
      have hp := hpos rfl
      simp only [position, GalilScaffoldInputHead.left, if_true, Bool.not_true,
        Bool.false_eq_true, if_false] at hp ⊢
      omega

theorem represents_right {raw : List (Fin 2)} {p : PH}
    (hr : GalilScaffoldInputTrace.Represents p.head raw) :
    GalilScaffoldInputTrace.Represents (GalilScaffoldChainVerifier.right p).head raw := by
  rcases p with ⟨hd, g⟩
  cases g with
  | false => exact hr
  | true =>
    by_cases hc : GalilScaffoldInputTrace.canRight hd
    · exact GalilScaffoldInputTrace.right_represents hr hc
    · have hd' : GalilScaffoldInputTrace.moveRight hd = hd := by
        rcases hd with ⟨f, ls, rs, q⟩
        simp only [GalilScaffoldInputTrace.canRight, not_or, not_not] at hc
        obtain ⟨h1, h2⟩ := hc
        cases rs with
        | cons a rs => exact (List.cons_ne_nil a rs h1).elim
        | nil =>
          cases q with
          | cons a q => exact (List.cons_ne_nil a q h2).elim
          | nil => rfl
      simpa [GalilScaffoldChainVerifier.right, GalilScaffoldChainVerifier.headRight, hd'] using hr

theorem sane_right {p : PH} (hc : GalilScaffoldChainVerifier.canRight p) :
    GalilFrontMono.Sane (GalilScaffoldChainVerifier.right p) := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g with
  | false => exact Or.inl rfl
  | true =>
    refine Or.inr ?_
    cases rs with
    | cons a rs => simp [GalilScaffoldChainVerifier.right, GalilScaffoldChainVerifier.headRight,
        GalilScaffoldInputTrace.moveRight]
    | nil =>
      cases q with
      | nil => simp [GalilScaffoldChainVerifier.canRight] at hc
      | cons a q => simp [GalilScaffoldChainVerifier.right, GalilScaffoldChainVerifier.headRight,
          GalilScaffoldInputTrace.moveRight]

theorem stack_ne_of_right_stack_ne {p : PH}
    (h : (GalilScaffoldChainVerifier.right p).head.right ≠ []) : p.head.right ≠ [] := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases rs with
  | cons a rs => simp
  | nil =>
    exfalso
    cases g with
    | false => exact h rfl
    | true => cases q <;> exact h rfl

/-- **A budgeted right move preserves the weakened clause.**  The budget hypothesis is
the checkpoint condition on the *new* place, and it is only needed when the move empties
the right stack — over a non-empty stack nothing is consumed. -/
theorem trails_right {raw : List (Fin 2)} {m d : ℕ} {p : PH} (h : Trails raw m d p)
    (hc : GalilScaffoldChainVerifier.canRight p)
    (hb : (GalilScaffoldChainVerifier.right p).head.right = [] →
      position (GalilScaffoldChainVerifier.right p) + d ≤ 2 * (m + 1) - 1) :
    Trails raw m d (GalilScaffoldChainVerifier.right p) := by
  refine ⟨represents_right h.rep, sane_right hc, ?_, hb⟩
  by_cases hz : (GalilScaffoldChainVerifier.right p).head.right = []
  · exact GalilNeedBound.usedPH_le_of_position raw _ m (represents_right h.rep) (sane_right hc) hz
      (by have := hb hz; omega)
  · rw [usedPH_right_of_stack _ _ (stack_ne_of_right_stack_ne hz)]; exact h.used

#print axioms left_left_stack
#print axioms not_trail_cx
#print axioms not_trail_cx_ver
#print axioms trailF_cx
#print axioms usedPH_right_of_stack
#print axioms usedPH_right_right_of_stack
#print axioms usedPH_right_le_of_trails
#print axioms usedPH_right_right_le_of_trails
#print axioms usedChain_le_of_trailF
#print axioms lookChain'_le_of_trailF
#print axioms needL'_le_of_trailF
#print axioms needL'_of_trailF
#print axioms pal_in_peg_final2'_trailF
#print axioms trailF_of_trail
#print axioms h_trailF_of_h_trail
#print axioms trailF_boot
#print axioms trails_left
#print axioms trails_right

end PalPeg.GalilTrailProof
