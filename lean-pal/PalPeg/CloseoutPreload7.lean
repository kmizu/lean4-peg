import PalPeg.CloseoutPreload6

/-!
# What the three named restart contracts really reduce to

`CloseoutPreload6` closes the ledger from three named contracts about the
restart window: `CentreLongRun`, `NoReturn` and `EntryDepthG u D` with
`D ≤ prepLen k`.  This file discharges what is discharge*able* and records, as
proved arithmetic, why the third one is **off by `max k 1 + 1`**.

* §1 `CentreLong k c` is a statement about the *input*, not about the control:
  `stream_length_ge` computes the place stream's length from the letter count,
  so `centreLong_of_letters` reduces the contract to "at least `4 * max k 1 + 1`
  letters lie at and to the left of the dispatching centre".  There is no proof
  of `CentreLongRun` without such an input-length fact: on a short input the
  proposition is simply false (`not_centreLong_of_short`).

* §2 `NoReturn` is reduced to its one real content: a `ReachL` path that never
  passes through `.run` is a `ReachP` path (`noReturn_of_avoidRun`).  What is
  *not* available is that the window contains no `.run` exit at all; see the
  note at the end of the file.

* §3 The depth.  `entry_shape` gives `bs.length = max k 1 + 1 + n` with `n` the
  length of the preparation trace, and `CloseoutPreload.prep_run_preload` fixes
  the preparation phase at exactly `prepLen k`
  ticks, i.e. `2 * k + 2 * (8 * max k 1 + 1) + 6`, which is `prepLen k` on the
  nose.  So the entry depth of a real entry is
  `max k 1 + 1 + (prepLen k - 1) + 1 = max k 1 + prepLen k + 1`, and
  `depth_exceeds_prepLen` proves this is **strictly greater** than `prepLen k`:
  the grow phase and the `prepare` dispatch are not counted by `prepLen`.
-/

set_option autoImplicit false

namespace PalPeg.CloseoutPreload7

open PalPeg
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldPrepareControl (State)
open PalPeg.GalilScaffoldCounter (Counter value ofNat)
open PalPeg.CloseoutReadyStage
open PalPeg.CloseoutRunEntriesS
open PalPeg.CloseoutPreload5 (CentreLong CentreLongRun ReachP ReachL NoReturn
  EntryDepthG entry_shape reachP_ne_run)
open PalPeg.CloseoutPreload6 (prepLen)

/-! ## 1. `CentreLong` is an input-length fact -/

theorem gaps_length : ∀ xs : List (Fin 2),
    (GalilScaffoldPlace.gaps xs).length = 2 * xs.length := by
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [GalilScaffoldPlace.gaps, List.length_cons, ih]
    omega

/-- The place stream has `2 * letters - 1` cells, plus one when the head sits in
a gap.  Only the lower bound is needed. -/
theorem stream_length_ge (p : GalilScaffoldPlace.Place) :
    2 * p.letters.length ≤ (GalilScaffoldPlace.stream p).length + 1 := by
  rcases p with ⟨xs, g⟩
  cases xs with
  | nil => simp [GalilScaffoldPlace.stream]
  | cons a xs =>
    cases g <;> simp [GalilScaffoldPlace.stream, gaps_length]
    all_goals omega

theorem stream_length_le (p : GalilScaffoldPlace.Place) :
    (GalilScaffoldPlace.stream p).length ≤ 2 * p.letters.length := by
  rcases p with ⟨xs, g⟩
  cases xs with
  | nil => simp [GalilScaffoldPlace.stream]
  | cons a xs =>
    cases g <;> simp [GalilScaffoldPlace.stream, gaps_length]
    all_goals omega

/-- **`CentreLong` from a letter count.**  `4 * max k 1 + 1` letters at and to
the left of the centre suffice. -/
theorem centreLong_of_letters (k : ℕ) (c : GalilScaffoldPlace.Place)
    (h : 4 * max k 1 + 1 ≤ c.letters.length) : CentreLong k c := by
  have := stream_length_ge c
  unfold CentreLong
  omega

/-- **And it is genuinely false on a short input**: fewer than `4 * max k 1`
letters cannot carry the stage window.  So no unconditional proof of
`CentreLongRun` exists; it needs an input-length (`hfloor`-style) fact. -/
theorem not_centreLong_of_short (k : ℕ) (c : GalilScaffoldPlace.Place)
    (h : c.letters.length ≤ 4 * max k 1) : ¬ CentreLong k c := by
  have := stream_length_le c
  unfold CentreLong
  omega

#print axioms centreLong_of_letters
#print axioms not_centreLong_of_short

/-! ## 2. `NoReturn` is exactly "the path avoided `.run`" -/

/-- A `ReachL` path all of whose endpoints avoid `.run` is a `ReachP` path.
This is the whole content of `NoReturn`: what it asks for is that the restart
window contains no `.run` interval, which determinism alone does not give (the
`.run` phase exits to `begin` by `found`/`missed`). -/
theorem reachP_of_avoidRun {v w : SearchVM} {bs : List Bool}
    (h : ReachL v bs w)
    (havoid : ∀ (cs : List Bool) (x : SearchVM), ReachL v cs x →
      x.search.mode ≠ GalilScaffoldSearchFinish.Mode.run) :
    ReachP v bs w := by
  induction h with
  | nil => exact .nil _ (havoid [] v (.nil _))
  | snoc x x' cs a c hr hs ih =>
    exact .snoc _ _ _ _ _ c ih hs (havoid (cs ++ [a]) x' (.snoc _ _ _ _ _ c hr hs))

theorem noReturn_of_avoidRun (u : GalilVM)
    (havoid : ∀ (cs : List Bool) (x : SearchVM), ReachL (searchLens.get u) cs x →
      x.search.mode ≠ GalilScaffoldSearchFinish.Mode.run) :
    NoReturn u := by
  intro bs v h _
  exact reachP_of_avoidRun h havoid

#print axioms noReturn_of_avoidRun

/-! ## 3. The entry depth, and why `D ≤ prepLen k` is off by `max k 1 + 1` -/

/-- The depth identity of `entry_shape`, isolated. -/
theorem entry_depth_eq {raw : List (Fin 2)} {u : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw u Rad last) (hcl : CentreLongRun u (value last).toNat)
    {bs : List Bool} {v v' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool}
    (hp : ReachP (searchLens.get u) bs v) (hs : searchStep c a v v')
    (hr : v'.search.mode = GalilScaffoldSearchFinish.Mode.run) :
    ∃ n : ℕ, bs.length + 1 = max (value last).toNat 1 + 2 + n := by
  obtain ⟨-, -, -, n, -, -, -, -, -, -, -, -, -, -, hn⟩ := entry_shape hR hcl hp hs hr
  exact ⟨n, by omega⟩

#print axioms entry_depth_eq

/-- **`EntryDepthG` from `NoReturn` and a bound on the preparation trace.**  This
is the only route: the depth is the grow phase plus the dispatch plus the
preparation ticks. -/
theorem entryDepthG_of_prepBound {raw : List (Fin 2)} {u : GalilVM} {Rad : ℕ}
    {last : Counter} {N : ℕ}
    (_hR : Restarted raw u Rad last) (_hcl : CentreLongRun u (value last).toNat)
    (hnr : NoReturn u)
    (hN : ∀ (bs : List Bool) (v v' : SearchVM) (c : GalilScaffoldPlace.Place)
      (a : Bool), ReachP (searchLens.get u) bs v → searchStep c a v v' →
      v'.search.mode = GalilScaffoldSearchFinish.Mode.run →
      bs.length ≤ max (value last).toNat 1 + 1 + N) :
    EntryDepthG u (max (value last).toNat 1 + 2 + N) := by
  intro bs v v' c a hl hs hne hr
  have hp := hnr bs v hl hne
  have := hN bs v v' c a hp hs hr
  omega

#print axioms entryDepthG_of_prepBound

/-- **The negative result.**  `CloseoutPreload.prep_run_preload` fixes the
preparation phase of a stage with `lower = k` and window `stageWindow1 k` at
exactly `2 * k + 2 * stageWindow1 k + 6 = prepLen k` ticks, one of which is the
entry tick itself, so the preparation trace has `N = prepLen k - 1` ticks and the
true entry depth is `max k 1 + 2 + N = max k 1 + prepLen k + 1`.  That is
strictly larger than `prepLen k`: `CloseoutPreload6`'s side condition
`D ≤ prepLen k` forgets the `max k 1` grow ticks and the `prepare` dispatch. -/
theorem depth_exceeds_prepLen (k : ℕ) :
    prepLen k < max k 1 + 2 + (prepLen k - 1) := by
  unfold prepLen
  rcases Nat.le_total k 1 with h | h <;> simp [Nat.max_def] <;> omega

/-- The sharp bound the same data does support. -/
theorem depth_le_prepLen_shifted (k : ℕ) :
    max k 1 + 2 + (prepLen k - 1) = prepLen k + max k 1 + 1 := by
  unfold prepLen
  rcases Nat.le_total k 1 with h | h <;> simp [Nat.max_def] <;> omega

#print axioms depth_exceeds_prepLen
#print axioms depth_le_prepLen_shifted

/-!
## Note — what is missing

1. `CentreLongRun`: needs the machine fact *"at a `prepare` dispatch of a stage
   with counter `k`, at least `4 * max k 1 + 1` input letters lie at and to the
   left of the centre head"* (the `hfloor`/`hcopy` family).  §1 shows the
   contract is equivalent to it and false without it.

2. `NoReturn`: needs the machine fact *"no `.run` interval closes inside the
   restart window"*, i.e. neither `found` nor `missed` fires between the restart
   and the stage cut.  Determinism gives only that `.run` is entered by
   `startRun` and left by `found`/`missed`; it does not forbid the latter.

3. `EntryDepthG u D` with `D ≤ prepLen k` is **false** as stated
   (`depth_exceeds_prepLen`).  `CloseoutPreload6.ledger_closes_*` should be
   restated with `D ≤ prepLen k + max k 1 + 1`; `prepLen_le` then becomes
   `prepLen k + max k 1 + 1 ≤ 19 * max k 1 + 9`, which the same arithmetic
   absorbs.
-/

end PalPeg.CloseoutPreload7
