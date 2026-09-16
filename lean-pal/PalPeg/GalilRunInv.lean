import PalPeg.GalilMainLoopMInv
import PalPeg.GalilRestartStage
import PalPeg.GalilSearchReadyInv
import PalPeg.GalilReplayRest
import PalPeg.GalilBranchInvariants
import PalPeg.GalilRadiusConsumed
import PalPeg.GalilScaffoldTopInitRestart
import PalPeg.GalilScaffoldTopFallbackRestartAll

/-!
# The invariant pack at the restarted states of `H_run`

`ASSEMBLY_PLAN.md`, 「H_run 構成計画」, obligation **L9**: the well-founded
recursion `run_from_restarted` re-enters itself at every `Restarted` state, so
everything the three branches (input exhausted / found / fallback) consume has
to be re-established there.  `Inv` below is that pack, and the three theorems
of this file are its establishment (`inv_init`) and its two preservation
steps (`inv_after_fallback`, `inv_after_found`).
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## The pack -/

/-- The invariant carried across one turn of the `H_run` recursion. -/
structure Inv (raw : List (Fin 2)) (c : Control) (r : GalilVM) : Prop where
  /-- the state is a restart state -/
  rest : ∃ (Rad : ℕ) (last : Counter), Restarted raw r Rad last
  /-- the centre invariant (completeness) -/
  minv : MInv raw c r
  /-- the controller is parked in a fresh scan with the full match delay -/
  mode : c.mode = .scan ∧ c.replaying = false ∧ c.clock = 2048
  /-- the stage budget of `restarted_next_found` / `search_result_at_tick` -/
  stage : ∀ (Rad : ℕ) (last : Counter), Restarted raw r Rad last → StageEntry Rad last
  /-- branch coverage (iii)+(iv) for the search co-run -/
  search : GalilBranchInvariants2.SearchReady (searchLens.get r)
  /-- branch coverage (i)+(ii) for the chain -/
  block : GalilBranchInvariants.BlockInv r.chain
  /-- the replay counter never points past the arrived material -/
  frontier : Frontier r
  /-- the `replaying` flag and the replay counter agree at rest -/
  rest_replay : ReplayRest c r
  /-- the right head still represents the input word -/
  input : GalilScaffoldInputTrace.Represents r.right.head raw
  /-- no chain shift is in flight -/
  shiftIdle : ShiftIdle r

/-! ## Fields that a restart supplies on its own -/

/-- `Restarted` pins both of its numeric parameters. -/
theorem restarted_unique {raw : List (Fin 2)} {r : GalilVM} {Rad Rad' : ℕ} {last last' : Counter}
    (h : Restarted raw r Rad last) (h' : Restarted raw r Rad' last') : Rad = Rad' ∧ last = last' := by
  obtain ⟨-, -, -, -, hRR, -, -, hl, -, -⟩ := h
  obtain ⟨-, -, -, -, hRR', -, -, hl', -, -⟩ := h'
  refine ⟨?_, by rw [← hl, hl']⟩
  have h1 := hRR.2
  have h2 := hRR'.2
  omega

/-- A restart with radius `0` satisfies the stage budget, whatever parameters
another `Restarted` derivation might name. -/
theorem stage_of_restarted_zero {raw : List (Fin 2)} {r : GalilVM} {last0 : Counter}
    (h : Restarted raw r 0 last0) :
    ∀ (Rad : ℕ) (last : Counter), Restarted raw r Rad last → StageEntry Rad last := by
  intro Rad last h'
  obtain ⟨hr, -⟩ := restarted_unique h h'
  subst hr
  exact stageEntry_zero last

/-- The chain is idle at a restart, and `BlockInv` is vacuous there. -/
theorem blockInv_of_restarted {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ} {last : Counter}
    (h : Restarted raw r Rad last) : GalilBranchInvariants.BlockInv r.chain := by
  rw [h.1]; trivial

/-- The search sits in `GalilScaffoldSearchFinish.begin`, hence is ready. -/
theorem searchReady_of_restarted {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ} {last : Counter}
    (h : Restarted raw r Rad last) : GalilBranchInvariants2.SearchReady (searchLens.get r) :=
  GalilSearchReadyInv.searchReady_of_readyRem (GalilSearchReadyInv.searchReady_restarted h [])

/-- The scan invariant of a restart carries the right head's representation. -/
theorem input_of_restarted {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ} {last : Counter}
    (h : Restarted raw r Rad last) : GalilScaffoldInputTrace.Represents r.right.head raw :=
  h.2.2.2.1.rightRep

/-- Assembling the pack from the parts a cycle has to deliver. -/
theorem inv_of_parts {raw : List (Fin 2)} {c : Control} {r : GalilVM} {last0 : Counter}
    (hR : Restarted raw r 0 last0) (hM : MInv raw c r)
    (hmode : c.mode = .scan ∧ c.replaying = false ∧ c.clock = 2048)
    (hfr : Frontier r) (hrr : ReplayRest c r) (hsi : ShiftIdle r) : Inv raw c r :=
  { rest := ⟨0, last0, hR⟩, minv := hM, mode := hmode
    stage := stage_of_restarted_zero hR
    search := searchReady_of_restarted hR
    block := blockInv_of_restarted hR
    frontier := hfr, rest_replay := hrr
    input := input_of_restarted hR
    shiftIdle := hsi }

/-! ## Propagating `Frontier` and `ReplayRest` along a run -/

/-- The per-state side conditions of `frontier_tick` and `replayRest_tick`:
at a `replayStart` the radius is a natural-number counter, and the rewind it
authorises stays inside the arrived material. -/
def RewindSafe (c : Control) (s : GalilVM) : Prop :=
  (c.mode = Mode.replayStart → ∃ r, s.radius = GalilScaffoldCounter.ofNat r) ∧
  (c.mode = Mode.replayStart → ∀ r, s.radius = GalilScaffoldCounter.ofNat r →
    position s.center + r ≤ 2 * arrived s.center)

/-- `Frontier` and `ReplayRest` travel along any run of the concrete scaffold
whose states are all `RewindSafe`. -/
theorem frontier_replayRest_steps (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)
    {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hsafe : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      RewindSafe z.ctl z.vm)
    (hf : Frontier x.vm) (hr : ReplayRest x.ctl x.vm) :
    Frontier y.vm ∧ ReplayRest y.ctl y.vm := by
  induction h with
  | zero x => exact ⟨hf, hr⟩
  | @succ n x w y ht _ ih =>
    refine ih (fun m z hz => hsafe (m+1) z (.succ ht hz)) ?_ ?_
    · exact frontier_tick onLetter leftFirst centre place entry q first delay hr hf
        ((hsafe 0 x (.zero x)).2) ht
    · exact replayRest_tick onLetter leftFirst centre place entry q first delay hr
        ((hsafe 0 x (.zero x)).1) ht

/-! ## (1) Establishment: the `init` tick -/

/-- **`inv_init`.**  From `Control.initial 2048` and a boot VM whose right head
is on the first place, whose radius, length and replay counters are empty and
whose shift is idle, the `init` tick lands in a state carrying the whole pack. -/
theorem inv_init (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (s0 : GalilVM) (a : Fin 2) (rest : List (Fin 2))
    (h0 : s0.right = initialHead (a :: rest))
    (hrad : s0.radius = reset) (hlen : s0.length = reset)
    (hrepl : s0.replay = reset) (hsi : ShiftIdle s0) :
    ∃ (c1 : Control) (t : GalilVM),
      StepsAll (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) 2048
        (SoundScanNR (a :: rest)) 1 ⟨initial 2048, s0⟩ ⟨c1, t⟩ ∧
      Inv (a :: rest) c1 t := by
  obtain ⟨t, hst, hR, hpos, -, hRt, hrem, hrp⟩ :=
    init_stepsAll onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' (restartVM entry)
      centre place entry q first 2048 (initial 2048) rfl s0 a rest h0 hrad hlen
  have hMt : MInv (a :: rest) {(initial 2048) with mode := .scan, output := true} t := by
    refine minv_of_leftmost ?_ rfl
    rw [hRt, hpos]
    exact leftmost_one a rest
  have htrp : t.replay = reset := by rw [hrp, hrepl]
  refine ⟨_, t, hst, inv_of_parts hR hMt ⟨rfl, rfl, rfl⟩ (frontier_of_reset htrp)
    (replayRest_of_reset htrp) ?_⟩
  rw [shiftIdle_iff, hrem]
  exact (shiftIdle_iff s0).1 hsi

/-! ## (2) Preservation across a fallback cycle -/

/-- **`inv_after_fallback`.**  The landing state of `fallback_restarted_soundNR`
carries the pack, given (a) the leftmost-live-centre fact produced by
`leftmost_after_fallback`, (b) that the FPP chose radius `0` — otherwise the
landing controller has `replaying = true` and the `mode` field of `Inv` is
simply false — and (c) that no chain shift is in flight at the landing. -/
theorem inv_after_fallback (onLetter leftFirst : GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (hq0 : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8)
    (c : Control) (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (s : GalilVM) (hi : ShiftIdle s) (hav : canRight s.right)
    (vs : ScanVM) (vq : SearchVM) (hl : vs.left = left s.left) (hrr : vs.right = right s.right)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hq : searchEffect (sharedC onLetter leftFirst centre place entry) false s vq)
    (hch : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11) (centre s)
      (place s) s.center s.radius s.chain vs.chain)
    (hg : ¬ shiftGuardVM (afterMismatch s vs vq))
    {raw : List (Fin 2)} (hrep : GalilScaffoldInputTrace.Represents (right s.right).head raw)
    (hfoc : (right s.right).head.focus ≠ none)
    (hcan : Canonical s.length) (ℓ : ℕ) (hv : value s.length = ℓ)
    (heven : ∀ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' →
      ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length % 2 = 0)
    (honL : onLetter = onLetterVM raw) (hlF : leftFirst = leftFirstVM)
    (hout : OutputRel raw c s)
    (hcr : ∀ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' →
      chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)) = 0)
    (hL : Leftmost raw (position (right s.right)) (position (right s.right)))
    (hsiT : ∀ t : GalilVM, Restarted raw t 0 reset → ShiftIdle t) :
    ∃ (n : ℕ) (cT : Control) (t : GalilVM),
      StepsAll (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) 2048
        (SoundScanNR raw) (1 + (n+1)) ⟨c, s⟩ ⟨cT, t⟩ ∧
      Inv raw cT t := by
  obtain ⟨a, xs, rs', q', hdec, hraw, n, o, t, hstA, hRst, hrep', hpos⟩ :=
    fallback_restarted_soundNR onLetter leftFirst (restartVM entry) centre place entry q hq0 first
      h7 h8 2048 c hm hr hc s hi hav vs vq hl hrr hmis hq hch hg hrep hfoc hcan ℓ hv heven honL hlF
      hout
  have hz := hcr a xs rs' q' hdec
  rw [hz] at hrep' hpos
  have htrp : t.replay = reset := by rw [hrep']; exact reset_eq_ofNat.symm
  have hrt : position t.right = position t.center := by
    have := hRst.2.2.2.1.rightPos; omega
  refine ⟨n, _, t, hstA, inv_of_parts hRst ?_ ⟨rfl, by simp [hz], rfl⟩
    (frontier_of_reset htrp) (replayRest_of_reset htrp) (hsiT t hRst)⟩
  refine minv_of_leftmost ?_ (by simp [hz])
  rw [hrt, hpos]
  simpa using hL

/-! ## (3) Preservation across a found cycle -/

/-- The five facts about a found cycle's landing state that `foundCycle_step`
does not export (its landing state is existentially quantified). -/
def FoundResidual (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  (c.mode = .scan ∧ c.replaying = false ∧ c.clock = 2048) ∧
  (∀ (Rad : ℕ) (last : Counter), Restarted raw s Rad last → StageEntry Rad last) ∧
  Frontier s ∧ ReplayRest c s ∧ ShiftIdle s

/-- **`inv_after_found`.**  One main-loop cycle through a found comparison
carries the pack, given the residual facts at the landing state. -/
theorem inv_after_found (P : Shared) (qq : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c0 : Control) (r : GalilVM) (hC : FoundCycle P qq first 2048 raw c0 r)
    (Rad : ℕ) (last : Counter) (hR : Restarted raw r Rad last) (hI : Inv raw c0 r)
    (hres : ∀ (cT : Control) (sT : GalilVM), MInv raw cT sT →
      (∃ (Rad' : ℕ) (last' : Counter), Restarted raw sT Rad' last') → FoundResidual raw cT sT) :
    ∃ (cT : Control) (sT : GalilVM),
      (∃ k, StepsAll (galilFrameS P qq first) 2048 (SoundScanNR raw) k ⟨c0, r⟩ ⟨cT, sT⟩) ∧
      Inv raw cT sT := by
  obtain ⟨cT, sT, hsteps, hM, hRT⟩ := foundCycle_step P qq first 2048 raw c0 r hC Rad last hR hI.minv
  obtain ⟨hmode, hstage, hfr, hrr, hsi⟩ := hres cT sT hM hRT
  obtain ⟨Rad', last', hRT'⟩ := hRT
  exact ⟨cT, sT, hsteps,
    { rest := ⟨Rad', last', hRT'⟩, minv := hM, mode := hmode, stage := hstage
      search := searchReady_of_restarted hRT'
      block := blockInv_of_restarted hRT'
      frontier := hfr, rest_replay := hrr
      input := input_of_restarted hRT'
      shiftIdle := hsi }⟩

#print axioms restarted_unique
#print axioms stage_of_restarted_zero
#print axioms inv_of_parts
#print axioms frontier_replayRest_steps
#print axioms inv_init
#print axioms inv_after_fallback
#print axioms inv_after_found

end PalPeg.GalilScaffoldChainInputSupply
