import PalPeg.GalilScaffoldTopGuards
import PalPeg.GalilScaffoldTopRestart
import PalPeg.GalilScaffoldTopSearch
import PalPeg.GalilScaffoldTopReplay

/-!
# The replay frontier: a replay tick never pops a new letter

During a replay the right head re-reads places it has already visited.  This
module makes that precise with one arithmetic invariant on the right head.

`arrived p` is the number of letters the head can still reach *without*
touching the incoming FIFO: the letters already behind it (`head.left`) plus
the ones saved on its right stack (`head.right`).  Positions run at twice that
rate (`encoded` interleaves gaps), so `2 * arrived p` is the last place that is
reachable from the material already stored.

`Frontier s` says the replay counter never points past that bound:
`position s.right + replay ≤ 2 * arrived s.right`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead

/-- The places reachable from stored material: the consumed prefix plus the
saved right stack. -/
def arrived (p : PlaceHead) : ℕ := p.head.left.length + p.head.right.length

/-- The right head plus the remaining replay never passes the last arrived
place. -/
def Frontier (s : GalilVM) : Prop :=
  ∀ m, s.replay = GalilScaffoldCounter.ofNat m → position s.right + m ≤ 2 * arrived s.right

/-- A head always stands at or before its own frontier. -/
theorem position_le_arrived (p : PlaceHead) : position p ≤ 2 * arrived p := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g <;> (simp [position, arrived]; try omega)

theorem ofNat_inj {m n : ℕ} (h : GalilScaffoldCounter.ofNat m = GalilScaffoldCounter.ofNat n) :
    m = n := by
  have := congrArg (fun c => c.pos.length) h
  simpa [GalilScaffoldCounter.ofNat] using this

theorem ofNat_eq_reset {m : ℕ} (h : GalilScaffoldCounter.ofNat m = GalilScaffoldCounter.reset) :
    m = 0 := by
  have := congrArg (fun c => c.pos.length) h
  simpa [GalilScaffoldCounter.ofNat, GalilScaffoldCounter.reset] using this

/-- With the replay counter at rest the invariant is free. -/
theorem frontier_of_reset {s : GalilVM} (h : s.replay = GalilScaffoldCounter.reset) :
    Frontier s := by
  intro m hm
  rw [hm] at h
  rw [ofNat_eq_reset h]
  simpa using position_le_arrived s.right

/-- The invariant only looks at the right head and the replay counter. -/
theorem frontier_congr {s t : GalilVM} (hr : t.right = s.right) (hp : t.replay = s.replay)
    (h : Frontier s) : Frontier t := by
  intro m hm
  rw [hr]
  exact h m (by rw [← hp]; exact hm)

theorem dec_eq_ofNat {c : GalilScaffoldCounter.Counter} {m : ℕ}
    (h : GalilScaffoldCounter.dec c = GalilScaffoldCounter.ofNat m) :
    c = GalilScaffoldCounter.ofNat (m+1) := by
  rcases c with ⟨ps, ns⟩
  cases ps with
  | nil => simp [GalilScaffoldCounter.dec, GalilScaffoldCounter.ofNat] at h
  | cons a ps =>
    simp only [GalilScaffoldCounter.dec, GalilScaffoldCounter.ofNat] at h ⊢
    obtain ⟨h1, h2⟩ := GalilScaffoldCounter.Counter.mk.injEq .. ▸ h
    subst h1; subst h2
    cases a
    simp [List.replicate_succ]

/-- One right step of the head consumes exactly one unit of replay budget. -/
theorem right_frontier_step (p : PlaceHead) (m : ℕ)
    (h : position p + (m+1) ≤ 2 * arrived p) :
    position (GalilScaffoldChainVerifier.right p) + m ≤
      2 * arrived (GalilScaffoldChainVerifier.right p) := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g with
  | false =>
    simp only [position, arrived, GalilScaffoldChainVerifier.right, Bool.false_eq_true,
      if_false, Bool.not_false, if_true] at h ⊢
    omega
  | true =>
    cases rs with
    | cons a rs =>
      simp [position, arrived, GalilScaffoldChainVerifier.right,
        GalilScaffoldChainVerifier.headRight, GalilScaffoldInputTrace.moveRight] at h ⊢
      omega
    | nil =>
      cases q <;> simp [position, arrived] at h

/-- Stepping left never changes what has arrived: the letter leaving
`head.left` is pushed onto `head.right`. -/
theorem arrived_left (p : PlaceHead) :
    arrived (GalilScaffoldInputHead.left p) = arrived p := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g with
  | true => rfl
  | false =>
    cases ls with
    | nil => rfl
    | cons a ls =>
      show ls.length + (f :: rs).length = (a :: ls).length + rs.length
      simp
      omega

theorem left_length_pos_of_position {p : PlaceHead} (h : 0 < position p) :
    0 < p.head.left.length := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g <;>
    · simp only [position, Bool.false_eq_true, if_false, if_true] at h
      show 0 < ls.length
      omega

/-- A left step away from the origin lowers the position by exactly one. -/
theorem left_position_pos {p : PlaceHead} (h : 0 < position p) :
    position (GalilScaffoldInputHead.left p) + 1 = position p :=
  left_position p (left_length_pos_of_position h)

/-- `r` left steps from `p` land `r` places earlier and keep the frontier. -/
theorem left_iterate (r : ℕ) (p : PlaceHead) (h : r ≤ position p) :
    position (GalilScaffoldInputHead.left^[r] p) + r = position p ∧
      arrived (GalilScaffoldInputHead.left^[r] p) = arrived p := by
  induction r generalizing p with
  | zero => simp
  | succ r ih =>
    have hpos : 0 < position p := by omega
    have hstep := left_position_pos hpos
    have hle : r ≤ position (GalilScaffoldInputHead.left p) := by omega
    obtain ⟨h1, h2⟩ := ih (GalilScaffoldInputHead.left p) hle
    rw [Function.iterate_succ_apply]
    exact ⟨by omega, by rw [h2, arrived_left]⟩

/-- Establishment: `stepReplayStart` puts the right head on the centre with
`replay = radius`, and the centre was reached by `radius` rewind steps from
the right head, so the whole replay stays inside arrived material. -/
theorem frontier_replayStart {entry r : ℕ} {s t : GalilVM}
    (h : replayStartVM entry s t)
    (hcen : s.center = GalilScaffoldInputHead.left^[r] s.right)
    (hrad : s.radius = GalilScaffoldCounter.ofNat r)
    (hle : r ≤ position s.right) : Frontier t := by
  intro m hm
  have hrep : t.replay = s.radius := h.1
  have hright : t.right = s.center := h.2.1
  rw [hrep, hrad] at hm
  have hmr : m = r := (ofNat_inj hm).symm
  subst hmr
  obtain ⟨h1, h2⟩ := left_iterate m s.right hle
  rw [hright, hcen, h2, h1]
  exact position_le_arrived s.right

/-- The same establishment from the scan invariant: the right head sits at
`centre + radius`, so `radius` rewind steps are legal. -/
theorem frontier_replayStart_scan {entry r : ℕ} {raw : List (Fin 2)} {cen : ℕ} {s t : GalilVM}
    (h : replayStartVM entry s t)
    (hinv : ScanInvariant raw cen r s.left s.right)
    (hcen : s.center = GalilScaffoldInputHead.left^[r] s.right)
    (hrad : s.radius = GalilScaffoldCounter.ofNat r) : Frontier t :=
  frontier_replayStart h hcen hrad (by rw [hinv.rightPos]; omega)

/-- Transport along a lens-pulled VM effect. -/
theorem frontier_pull {σ' : Type} (L : Lens GalilVM σ') {s t : GalilVM}
    (h2 : t = L.set s (L.get t))
    (hr : (L.set s (L.get t)).right = s.right)
    (hp : (L.set s (L.get t)).replay = s.replay)
    (hf : Frontier s) : Frontier t :=
  frontier_congr ((congrArg GalilVM.right h2).trans hr)
    ((congrArg GalilVM.replay h2).trans hp) hf

/-- The concrete shared entries of the online scaffold. -/
def sharedC (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) : Shared :=
  galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' (restartVM entry)
    centre place entry

/-- **The one isolated assumption.**  The controller's `replaying` flag and the
replay counter agree at rest: whenever the flag is down (and at the `init`
entry) the counter is empty.  Scala keeps them in step — `replaying` is set
from `replay.sign` at `stepReplayStart` and cleared exactly when the counter
hits zero — but that coupling is not part of `Tick`, so it is assumed here.
It is only ever used to discharge the branches that move the right head
*without* paying replay (`stepInit`, and the shift/fallback exits of
`stepScan`, all of which are guarded by `!replaying`). -/
def ReplayRest (c : Control) (s : GalilVM) : Prop :=
  (c.replaying = false ∨ c.mode = Mode.init) → s.replay = GalilScaffoldCounter.reset

/-- How one controller tick moves the right head and the replay counter. -/
inductive RightReplayMove (c : Control) (s t : GalilVM) : Prop
  | rested (hreplay : t.replay = GalilScaffoldCounter.reset)
  | kept (hright : t.right = s.right) (hreplay : t.replay = s.replay)
  | replayed (hreplaying : c.replaying = true)
      (hright : t.right = GalilScaffoldChainVerifier.right s.right)
      (hreplay : t.replay = GalilScaffoldCounter.dec s.replay)
  | started (hmode : c.mode = Mode.replayStart) (hright : t.right = s.center)
      (hreplay : t.replay = s.radius)

theorem RightReplayMove.pull {σ' : Type} (L : Lens GalilVM σ') {c : Control} {s t : GalilVM}
    (h2 : t = L.set s (L.get t))
    (hr : (L.set s (L.get t)).right = s.right)
    (hp : (L.set s (L.get t)).replay = s.replay) : RightReplayMove c s t :=
  .kept ((congrArg GalilVM.right h2).trans hr) ((congrArg GalilVM.replay h2).trans hp)

theorem rightReplayMove_of_tick (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM}
    (hrest : ReplayRest c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : RightReplayMove c s t := by
  cases h
  case init =>
    rename_i hm hi
    have hi' : initVM entry s t := hi
    exact .rested (hi'.2.2.2.2.2.2.1.trans (hrest (Or.inr hm)))
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, hr, -, -, -, -, -, -, -, hpr, -, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact .kept hr hpr
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, hr, -, -, -, -, -, -, -, hpr, -, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact .kept hr hpr
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨vs, vq, a, -, hvr, -, -, -, hteq⟩ :
      compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
    have hs'r : s'.right = GalilScaffoldChainVerifier.right s.right := by
      rw [hteq, GalilScaffoldChainInputSupply.afterBirth_right]; cases a <;> exact hvr
    have hs'p : s'.replay = s.replay := by
      rw [hteq, GalilScaffoldChainInputSupply.afterBirth_replay]; cases a <;> rfl
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    cases hcr : c.replaying with
    | false =>
      rw [hcr, if_neg (by simp)] at hpl'
      exact .rested (by rw [hpl', hs'p]; exact hrest (Or.inl hcr))
    | true =>
      rw [hcr, if_pos rfl] at hpl'
      exact .replayed hcr (by rw [hpl', ← hs'r]) (by rw [hpl', ← hs'p])
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨vs, vq, a, -, -, -, -, -, hteq⟩ :
      compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
    have hs'p : s'.replay = s.replay := by
      rw [hteq, GalilScaffoldChainInputSupply.afterBirth_replay]; cases a <;> rfl
    obtain ⟨w, -, ht⟩ : beginShiftVM' s' t := hb
    exact .rested (by rw [ht]; show s'.replay = _; rw [hs'p]; exact hrest (Or.inl hr))
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨vs, vq, a, -, -, -, -, -, hteq⟩ :
      compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
    have hs'p : s'.replay = s.replay := by
      rw [hteq, GalilScaffoldChainInputSupply.afterBirth_replay]; cases a <;> rfl
    obtain ⟨pl, ht, -⟩ : beginFallbackVM' s' t := hb
    exact .rested (by rw [ht]; show s'.replay = _; rw [hs'p]; exact hrest (Or.inl hr))
  case shift_one =>
    rename_i hm hp hi
    exact .pull shiftLens hi.2 rfl rfl
  case shift_done => exact .kept rfl rfl
  case copy_one =>
    rename_i hm hp hi
    exact .pull fppLens hi.2 rfl rfl
  case copy_done =>
    rename_i hm hp hi
    exact .pull fppLens hi.2 rfl rfl
  case home_start =>
    rename_i hm hl hi
    exact .pull fppLens hi.2 rfl rfl
  case home_step =>
    rename_i hm hl hi
    exact .pull fppLens hi.2 rfl rfl
  case fpp_slice =>
    rename_i hm hi
    exact .pull fppLens hi.2 rfl rfl
  case fpp_done =>
    rename_i hm hi
    exact .pull fppLens hi.2 rfl rfl
  case markEnd_found =>
    rename_i hm he hi
    exact .pull rewindLens hi.2 (by rw [hi.1.2]; rfl) rfl
  case markEnd_step =>
    rename_i hm he hi
    exact .pull fppLens hi.2 rfl rfl
  case choose_select =>
    rename_i hm hodd hs hi
    exact .pull rewindLens hi.2 (by rw [hi.1]; rfl) rfl
  case choose_step =>
    rename_i hm hs hi
    exact .pull rewindLens hi.2 (by rw [hi.1.2]; rfl) rfl
  case rewind_done =>
    rename_i hm hfi hi
    exact .pull rewindLens hi.2 (by rw [hi.1]; rfl) rfl
  case rewind_one =>
    rename_i hm hpr hfi hi
    exact .pull rewindLens hi.2 (by rw [hi.1.2]; rfl) rfl
  case rewind_pair =>
    rename_i hm hpr hfi hi
    exact .pull rewindLens hi.2 (by rw [hi.1.2]; rfl) rfl
  case replayStart =>
    rename_i o hm ho ho' hi
    have hi' : replayStartVM entry s t := hi
    exact .started hm hi'.2.1 hi'.1
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    exact .kept (by rw [ht]) (by rw [ht])

/-- The frontier invariant is preserved by every controller tick.  The only
tick that moves the right head while replaying is the matched comparison, and
it decrements `replay` in the same breath (`matchedPlace`). -/
theorem frontier_tick (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM}
    (hrest : ReplayRest c s) (hf : Frontier s)
    (hrep : c.mode = Mode.replayStart → ∀ r, s.radius = GalilScaffoldCounter.ofNat r →
      position s.center + r ≤ 2 * arrived s.center)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : Frontier t := by
  cases rightReplayMove_of_tick onLetter leftFirst centre place entry q first delay hrest h with
  | rested hreplay => exact frontier_of_reset hreplay
  | kept hright hreplay => exact frontier_congr hright hreplay hf
  | replayed hreplaying hright hreplay =>
    intro m hm2
    rw [hreplay] at hm2
    have hsr := hf (m+1) (dec_eq_ofNat hm2)
    rw [hright]
    exact right_frontier_step s.right m hsr
  | started hmode hright hreplay =>
    intro m hm2
    rw [hright]
    exact hrep hmode m (hreplay ▸ hm2)

/-- The right head's next move needs a fresh letter: it stands on a gap (so
the move is a letter move) with an empty saved right stack, hence `moveRight`
must pop from `incoming`. -/
def PopsIncoming (p : PlaceHead) : Prop := p.gap = true ∧ p.head.right = []

/-- Such a move really does take the head of the incoming FIFO. -/
theorem pops_incoming_right {p : PlaceHead} (hp : PopsIncoming p) {a : Fin 2}
    {qs : List (Fin 2)} (hq : p.head.incoming = a :: qs) :
    GalilScaffoldChainVerifier.right p =
      ⟨⟨some a, p.head.focus :: p.head.left, [], qs⟩, false⟩ := by
  rcases p with ⟨⟨f, ls, rs, is⟩, g⟩
  obtain ⟨hg, hr⟩ := hp
  subst hg; subst hr
  simp only at hq
  subst hq
  rfl

/-- **The frontier consequence.**  A tick whose right move pops a new letter
from `incoming` is never a replay tick: the replay counter is already empty. -/
theorem consume_not_replaying {s : GalilVM} {m : ℕ} (hf : Frontier s)
    (hpop : PopsIncoming s.right) (hm : s.replay = GalilScaffoldCounter.ofNat m) : m = 0 := by
  have h := hf m hm
  obtain ⟨hg, hr⟩ := hpop
  rw [show position s.right = 2 * s.right.head.left.length by simp [position, hg],
    show arrived s.right = s.right.head.left.length by simp [arrived, hr]] at h
  omega

/-- The same statement as a refutation: no replay is in progress when the
machine reaches for a letter that has not been read yet. -/
theorem consume_not_replaying_false {s : GalilVM} {m : ℕ} (hf : Frontier s)
    (hpop : PopsIncoming s.right) (hm : s.replay = GalilScaffoldCounter.ofNat m)
    (hpos : 0 < m) : False := by
  have := consume_not_replaying hf hpop hm
  omega

/-- Packaged for the machine: at a pop the replay counter is at rest, so the
`replaying` short-circuit of `stepScan` cannot be taken on that tick. -/
theorem replay_reset_of_pops {s : GalilVM} {m : ℕ} (hf : Frontier s)
    (hpop : PopsIncoming s.right) (hm : s.replay = GalilScaffoldCounter.ofNat m) :
    s.replay = GalilScaffoldCounter.reset := by
  rw [hm, consume_not_replaying hf hpop hm]
  rfl

#print axioms position_le_arrived
#print axioms right_frontier_step
#print axioms left_iterate
#print axioms frontier_replayStart
#print axioms frontier_replayStart_scan
#print axioms frontier_tick
#print axioms pops_incoming_right
#print axioms consume_not_replaying
#print axioms consume_not_replaying_false
#print axioms replay_reset_of_pops

end PalPeg.GalilScaffoldChainInputSupply
