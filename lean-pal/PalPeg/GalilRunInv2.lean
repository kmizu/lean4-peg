import PalPeg.GalilRunInv
import PalPeg.GalilFallbackLanding

/-!
# `inv_after_fallback`, rewired through the landing lemma

`ASSEMBLY_PLAN.md`, 「H_run 構成計画」, obligation **L9**.  `inv_after_fallback`
(`PalPeg/GalilRunInv.lean`) takes three facts about the *landing* state of a
fallback cycle as hypotheses, because `fallback_restarted_soundNR` drops them:

1. `hcr` — that the fallback picked radius `0`.  This is not a fact at all: the
   fallback picks the largest palindromic suffix radius, and when it is positive
   the landing controller has `replaying = true`, so the `mode` field of `Inv`
   is simply false there.
2. `hL` — the leftmost-live-centre fact at the landing centre.
3. `hsiT` — shift idleness at the landing state.

`fallback_landing` and `leftmost_after_fallback_landing`
(`PalPeg/GalilFallbackLanding.lean`) close (2) and (3): they state `PalAt`, the
maximality, `ShiftIdle t`, `t.chain = .idle` and `t.replay` about *one* witness.
`inv_after_fallback'` below uses them and removes the radius-zero assumption by
splitting the conclusion: on radius `0` the landing carries the full `Inv`, and
on a positive radius it carries `LandingReplay`, the same pack with the replay
flag up (`replaying = true`, `t.replay = ofNat R`, the right head back on the
centre).

**Remaining gap** (`hfrT`): `Frontier` at a positive-radius landing.  The
landing head is `left^[R] (right s.right)`, so `left_iterate` gives
`position + R ≤ 2 * arrived` immediately — but `fallback_landing` does not
export that head equation (only `position t.center`), and `Frontier` is not
derivable from `Restarted` alone: a `Represents` head whose saved right stack is
empty satisfies `position = 2 * arrived`, which would force `R = 0`.  So the
fact is taken as a hypothesis, guarded by `0 < chosenRadius`; the radius-zero
branch does not use it.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## The pack at a replaying landing -/

/-- `Inv`, with the replay flag up: every field of `Inv` except that
`c.replaying = true`, plus the three facts the replay needs — the counter holds
a positive radius, it is canonical, and the right head has been put back on the
centre. -/
structure LandingReplay (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  /-- the state is a restart state -/
  rest : ∃ (Rad : ℕ) (last : Counter), Restarted raw s Rad last
  /-- the centre invariant (completeness), now in its replaying clause -/
  minv : MInv raw c s
  /-- the controller is parked in a fresh scan with the full match delay, replaying -/
  mode : c.mode = .scan ∧ c.replaying = true ∧ c.clock = 2048
  /-- the replay counter holds the chosen radius, which is positive -/
  replay : ∃ R, 0 < R ∧ s.replay = GalilScaffoldCounter.ofNat R
  /-- the replay counter is canonical -/
  canon : Canonical s.replay
  /-- the right head has been rewound onto the centre -/
  rightPos : position s.right = position s.center
  /-- the stage budget of `restarted_next_found` / `search_result_at_tick` -/
  stage : ∀ (Rad : ℕ) (last : Counter), Restarted raw s Rad last → StageEntry Rad last
  /-- branch coverage (iii)+(iv) for the search co-run -/
  search : GalilBranchInvariants2.SearchReady (searchLens.get s)
  /-- branch coverage (i)+(ii) for the chain -/
  block : GalilBranchInvariants.BlockInv s.chain
  /-- the replay counter never points past the arrived material -/
  frontier : Frontier s
  /-- the `replaying` flag and the replay counter agree at rest (vacuous here) -/
  rest_replay : ReplayRest c s
  /-- the right head still represents the input word -/
  input : GalilScaffoldInputTrace.Represents s.right.head raw
  /-- no chain shift is in flight -/
  shiftIdle : ShiftIdle s

/-- With the flag up and the mode `scan`, `ReplayRest` is vacuous. -/
theorem replayRest_of_replaying {c : Control} {s : GalilVM}
    (hr : c.replaying = true) (hm : c.mode = Mode.scan) : ReplayRest c s := by
  intro h
  cases h with
  | inl h => rw [hr] at h; cases h
  | inr h => rw [hm] at h; cases h

/-! ## (2') Preservation across a fallback cycle, both radii -/

/-- **`inv_after_fallback'`.**  One fallback cycle from a mismatching scan
state.  The hypotheses are the facts `Inv raw c s` propagates to the mismatch
(`MInv`, the scan invariant with `RadiusRep`/`SpanRep`, `Canonical s.length`,
`ShiftIdle`, `OutputRel`) together with the mismatch data.  The landing carries
`Inv` when the fallback chose radius `0`, and `LandingReplay` otherwise. -/
theorem inv_after_fallback' (onLetter leftFirst : GalilVM → Prop) (rs : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (hq0 : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8)
    (c : Control) (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (s : GalilVM) (hsi : ShiftIdle s) (hav : canRight s.right)
    (vs : ScanVM) (vq : SearchVM) (hl : vs.left = left s.left) (hrr : vs.right = right s.right)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hq : searchEffect (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry)
      false s vq)
    (hch : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11) (centre s)
      (place s) s.center s.radius s.chain vs.chain)
    (hg : ¬ shiftGuardVM (afterMismatch s vs vq))
    {raw : List (Fin 2)} (Rad : ℕ) (hM : MInv raw c s)
    (hscan : ScanInvariant raw (position s.center) Rad s.left s.right)
    (hRR : RadiusRep s.radius Rad) (hS : SpanRep s)
    (hcan : Canonical s.length) (ℓ : ℕ) (hv : value s.length = ℓ)
    (heven : ∀ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' →
      ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length % 2 = 0)
    (honL : onLetter = onLetterVM raw) (hlF : leftFirst = leftFirstVM)
    (hout : OutputRel raw c s)
    (hfrT : ∀ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' →
      0 < chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)) →
      ∀ t : GalilVM, Restarted raw t 0 reset →
        t.replay = ofNat (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) →
        Frontier t) :
    ∃ (n R : ℕ) (cT : Control) (t : GalilVM),
      StepsAll (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first) 2048
        (SoundScanNR raw) (1 + (n+1)) ⟨c, s⟩ ⟨cT, t⟩ ∧
      cT.replaying = decide (0 < R) ∧
      (R = 0 → Inv raw cT t) ∧
      (0 < R → LandingReplay raw cT t) := by
  have hrep : GalilScaffoldInputTrace.Represents (right s.right).head raw :=
    right_word s.right raw hscan.rightRep hav
  have hfoc : (right s.right).head.focus ≠ none :=
    right_present s.right raw hscan.rightRep hscan.rightPresent hav
  obtain ⟨a, xs, rs', q', hdec, hraw, n, o, t, hstA, hRst, hposT, hpal, hmax, hrepT, hsiT, hchT⟩ :=
    fallback_landing onLetter leftFirst rs centre place entry q hq0 first h7 h8 2048 c hm hr hc
      s hsi hav vs vq hl hrr hmis hq hch hg hrep hfoc hcan ℓ hv heven honL hlF hout
  -- the leftmost live centre at the landing
  have hL : Leftmost raw (position (right s.right)) (position t.center) :=
    leftmost_after_fallback_landing raw hM hr hscan hRR hS hav hmis a xs rs' q' hdec ℓ hv
      hpal hmax hposT
  -- the mismatch place is one past the right head
  have hrpos : position (right s.right) = position s.right + 1 :=
    right_position s.right hav (represented_position _ raw hscan.rightRep hscan.rightPresent).1
  -- the centre invariant, in both clauses at once
  have hMT : MInv raw
      { c with
        mode := .scan, clock := 2048, output := o,
        replaying := decide (0 < chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))),
        odd := oddAt false (((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length - (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))+1)),
        pair := pairAt (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) } t :=
    minv_after_fallback hRst hrepT (by rw [hposT, hrpos]) (by rw [← hrpos]; exact hL) rfl
  -- the right head is back on the centre
  have hrt : position t.right = position t.center := by
    have := hRst.2.2.2.1.rightPos; omega
  refine ⟨n, chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)),
    _, t, hstA, rfl, ?_, ?_⟩
  · -- radius zero: the full `Inv`
    intro hz
    have htrp : t.replay = reset := by rw [hrepT, hz]; rfl
    exact inv_of_parts hRst hMT ⟨rfl, by simp [hz], rfl⟩ (frontier_of_reset htrp)
      (replayRest_of_reset htrp) hsiT
  · -- positive radius: the replaying pack
    intro hz
    exact
      { rest := ⟨0, reset, hRst⟩
        minv := hMT
        mode := ⟨rfl, by simp [hz], rfl⟩
        replay := ⟨_, hz, hrepT⟩
        canon := by rw [hrepT]; exact ofNat_canonical _
        rightPos := hrt
        stage := stage_of_restarted_zero hRst
        search := searchReady_of_restarted hRst
        block := blockInv_of_restarted hRst
        frontier := hfrT a xs rs' q' hdec hz t hRst hrepT
        rest_replay := replayRest_of_replaying (by simp [hz]) rfl
        input := input_of_restarted hRst
        shiftIdle := hsiT }

#print axioms replayRest_of_replaying
#print axioms inv_after_fallback'

end PalPeg.GalilScaffoldChainInputSupply
