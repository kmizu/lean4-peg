import PalPeg.GalilReplayGeneral
import PalPeg.GalilChainTickable
import PalPeg.GalilGoodLag
import PalPeg.GalilRoundPeriod
import PalPeg.GalilBranchInvariants
import PalPeg.GalilShiftH

/-!
# Instantiating `WatchOk`, `hgood` and `StartOk` — and why the first two cannot be

`GalilReplayGeneral.replay_after_fallback_general` takes three named chain
hypotheses: `hOk : WatchOk Ok`, `hgood : ∀ w, Ok w → Good w` and
`hstart : StartOk P Ok`.

## 1. `WatchOk Ok ∧ hgood` is unsatisfiable (`watchOk_good_false`)

For **every** `Ok`, the pair is contradictory:

* direct cause — `hgood` makes every `Ok` state `Good`, and `Good` includes
  `canRight` of the verifier; `WatchOk.internal`/`WatchOk.outer` close `Ok`
  under `Internal.take` / `Outer.immediate` (both *move the verifier right*)
  and under `Outer.queued` (which moves a negative lag towards zero).  So from
  any `Ok` state there is an `Ok` state further right, forever; the measure
  `mu` (twice the cells still to the right, plus the gap bit) strictly
  decreases, so no `Ok` state exists (`watchOk_good_no_state`);
* but `WatchOk.born` forces `Ok` to hold of *every* newborn watch state (any
  verifier with `canRight`, any `OnBlock` period) — so `Ok` is inhabited.

Second layer (why the interface has this shape): `Ok` is a predicate on the
chain-local `WState` only.  The fact that actually keeps the verifier in range
during a replay — verifier ≤ right head, and `Frontier` for the right head — is
a relation to the *scan* heads, which `WState` does not contain; and `born` is
quantified over all verifiers/blocks instead of those the found start
produces.  No state predicate can carry a bound that the (unboundedly many)
credit steps of `Outer` preserve.  Hence `replay_after_fallback_general` is
vacuous as stated; the repair has to feed the bound per tick (the replay's
`chain_compare` already has `Frontier s` in hand).

## 2. What *is* provable: the span-relative core (`SpanCore`)

`SpanCore raw center b xs anchor m` on a verifier machine `m`: complete period
block, represented verifier, unbroken control with the same prediction as
`ready center xs b` after `pre` reads, and `position verifier + 1 =
anchor + pre.length`.  With `SpanWindow` (the `2h`-periodicity of
`encoded raw` on `[anchor, B]`, and the first `2h` cells equal to `bounce`):

* `spanCore_good` — `Good` as long as `position verifier + 1 ≤ B < |encoded raw|`
  (this is `good_of_periodOn` without an `Entry`, for *every* later read);
* `spanCore_consume`, `spanCore_internal`, `spanCore_outer` — closure under the
  whole watch phase, with no bound needed (the bound is not part of the core);
* `spanCore_born` — the watch state `backDone` creates from the rewound block
  `[FIRST c, ys…, LAST b]` is `SpanCore` with `pre = []`;
* `span_watch_tick` — the per-tick replacement of `no_break_during_replay` on a
  watching chain: with room `position verifier + 2 ≤ B`, the tick exists, never
  breaks, and stays in `SpanCore`, moving the verifier at most 2 places.

## 3. `StartOk`

`ChainOk` of `chainStart` does not mention `Ok`; it is `CopyInv` plus
`canRight` of the start verifier (`chainOk_chainStart`).  The premises of
`StartOk` say nothing about `s.center`, so `canRight s.center` is not derivable
from them; the DP answer shape (`AnswerAhead`) is available only through
`found_copy_walk_least` in run mode.  Both are isolated as the one named
hypothesis `StartShape` (`startOk_of_shape`).
-/

set_option autoImplicit false

namespace PalPeg.GalilWatchOkInst

open PalPeg PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilBranchInvariants
  PalPeg.GalilChainTickable PalPeg.GalilReplayGeneral
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

/-! ## 1. The inconsistency -/

/-- Cells still to the right of a verifier, doubled, plus the gap bit. -/
def mu (p : PlaceHead) : ℕ :=
  2 * (p.head.right.length + p.head.incoming.length) + (if p.gap then 1 else 2)

theorem mu_right (p : PlaceHead) (hc : GalilScaffoldChainVerifier.canRight p) :
    mu (GalilScaffoldChainVerifier.right p) < mu p := by
  rcases p with ⟨⟨f, ls, rs, qs⟩, g⟩
  cases g with
  | false => simp [mu, GalilScaffoldChainVerifier.right]
  | true =>
    cases rs with
    | cons a rs =>
      simp [mu, GalilScaffoldChainVerifier.right, headRight,
        GalilScaffoldInputTrace.moveRight]
      omega
    | nil =>
      cases qs with
      | nil => simp [GalilScaffoldChainVerifier.canRight] at hc
      | cons a qs =>
        simp [mu, GalilScaffoldChainVerifier.right, headRight,
          GalilScaffoldInputTrace.moveRight]
        omega

/-- **No `Ok` state exists** once `Ok` is closed under the watch phase and every
`Ok` state is `Good`. -/
theorem watchOk_good_no_state {Ok : WState → Prop} (hOk : WatchOk Ok)
    (hgood : ∀ w, Ok w → GalilScaffoldChainWatch.Good w) : ∀ w, ¬ Ok w := by
  suffices H : ∀ n k (w : WState), mu w.machine.verifier = n → w.lag.neg.length = k → ¬ Ok w by
    intro w; exact H _ _ w rfl rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro k
    induction k with
    | zero =>
      intro w hn hk hw
      have hg := hgood w hw
      cases hp : positive w.lag with
      | true =>
        have hm := hOk.internal w _ hw (.take w hp hg)
        exact ihn _ (by rw [← hn]; exact mu_right _ hg.1) _ _ rfl rfl hm
      | false =>
        have hz : zero w.lag = true := by
          have hpos : w.lag.pos = [] := by
            simpa [positive] using hp
          have hneg : w.lag.neg = [] := List.eq_nil_of_length_eq_zero hk
          simp [zero, hpos, hneg]
        have hm := hOk.outer w true _ hw (.immediate w hz hg)
        exact ihn _ (by rw [← hn]; exact mu_right _ hg.1) _ _ rfl rfl hm
    | succ k ihk =>
      intro w hn hk hw
      have hg := hgood w hw
      cases hp : positive w.lag with
      | true =>
        have hm := hOk.internal w _ hw (.take w hp hg)
        exact ihn _ (by rw [← hn]; exact mu_right _ hg.1) _ _ rfl rfl hm
      | false =>
        obtain ⟨u, ns, hns⟩ : ∃ u ns, w.lag.neg = u :: ns := by
          cases h : w.lag.neg with
          | nil => rw [h] at hk; simp at hk
          | cons u ns => exact ⟨u, ns, rfl⟩
        have hz : zero w.lag = false := by simp [zero, hns]
        have hm := hOk.outer w true _ hw (.queued w hz)
        refine ihk (GalilScaffoldChainWatch.queued w) hn ?_ hm
        simp only [GalilScaffoldChainWatch.queued, inc, hns]
        rw [hns] at hk; simpa using hk

/-- A concrete newborn watch state. -/
def bornVer : PlaceHead := ⟨⟨some 0, [], [], []⟩, false⟩
def bornBlock : GalilScaffoldChainPeriod.Tape :=
  ⟨[], .first 0, [GalilScaffoldChainPeriod.Token.last 0]⟩

theorem bornVer_can : GalilScaffoldChainVerifier.canRight bornVer := Or.inl rfl
theorem bornBlock_onBlock : OnBlock bornBlock := ⟨0, 0, [], rfl⟩

/-- **`WatchOk Ok` and `hgood` are jointly unsatisfiable, for every `Ok`.** -/
theorem watchOk_good_false {Ok : WState → Prop} (hOk : WatchOk Ok)
    (hgood : ∀ w, Ok w → GalilScaffoldChainWatch.Good w) : False :=
  watchOk_good_no_state hOk hgood _
    (hOk.born bornVer bornBlock reset reset bornVer_can bornBlock_onBlock)

theorem no_watchOk_instance :
    ¬ ∃ Ok : WState → Prop, WatchOk Ok ∧ ∀ w, Ok w → GalilScaffoldChainWatch.Good w :=
  fun ⟨_, hOk, hgood⟩ => watchOk_good_false hOk hgood

/-! ## 2. The span-relative core -/

open GalilScaffoldChainPrediction in
/-- The closure-stable part of the replay's watch invariant, on the machine. -/
def SpanCore (raw : List (Fin 2)) (center b : Fin 3) (xs : List (Fin 3)) (anchor : ℕ)
    (m : GalilScaffoldChainVerifier.State) : Prop :=
  OnBlock m.control.period ∧ GalilScaffoldInputTrace.Represents m.verifier.head raw ∧
    m.verifier.head.focus ≠ none ∧ m.control.broken = false ∧
    ∃ pre : List (Fin 3),
      SamePrediction m.control
        (GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready center xs b) pre) ∧
      (GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready center xs b) pre).broken =
        false ∧
      position m.verifier + 1 = anchor + pre.length

/-- The span: `encoded raw` is `2h`-periodic on `[anchor, B]` and starts with one
`bounce` word at `anchor` (`h = xs.length + 1`). -/
def SpanWindow (raw : List (Fin 2)) (center b : Fin 3) (xs : List (Fin 3)) (anchor B : ℕ) :
    Prop :=
  PeriodOn (encoded raw) (2 * (xs.length + 1)) anchor B ∧
    ∀ i, i < 2 * (xs.length + 1) →
      (encoded raw)[anchor + i]? = (GalilScaffoldChainSweep.bounce center b xs)[i]?

/-- Iterated periodicity from the anchor. -/
theorem periodOn_mod {x : List (Fin 3)} {p a B : ℕ} (hp : 0 < p) (h : PeriodOn x p a B) :
    ∀ j, a + j ≤ B → x[a + j]? = x[a + j % p]? := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hlt : j < p
    · rw [Nat.mod_eq_of_lt hlt]
    · have hpj : p ≤ j := Nat.le_of_not_lt hlt
      have hj' : j - p < j := Nat.sub_lt (Nat.lt_of_lt_of_le hp hpj) hp
      have e1 := ih (j - p) hj' (Nat.le_trans (Nat.add_le_add_left (Nat.sub_le j p) a) hj)
      have hsum : a + (j - p) + p = a + j := by omega
      have e2 := h (a + (j - p)) (Nat.le_add_right a _) (by rw [hsum]; exact hj)
      rw [hsum] at e2
      have e3 : j % p = (j - p) % p := Nat.mod_eq_sub_mod hpj
      rw [← e2, e1, e3]

/-- **`Good` from the span**, at any later read, with no `Entry`. -/
theorem spanCore_good {raw : List (Fin 2)} {center b : Fin 3} {xs : List (Fin 3)}
    {anchor B : ℕ} {w : WState}
    (hc : SpanCore raw center b xs anchor w.machine) (hwin : SpanWindow raw center b xs anchor B)
    (hB : B < (encoded raw).length) (hpos : position w.machine.verifier + 1 ≤ B) :
    GalilScaffoldChainWatch.Good w := by
  obtain ⟨-, hrep, hpres, hbr, pre, hsame, hbr0, hidx⟩ := hc
  have hcan : GalilScaffoldChainVerifier.canRight w.machine.verifier :=
    canRight_of_bound _ raw hrep hpres (by omega)
  have hpred := GalilScaffoldChainPrediction.continued_prediction center b xs pre []
    w.machine.control hsame (by rw [hbr, hbr0]) (by simpa [GalilScaffoldChainSweep.run] using hbr)
  simp only [List.length_nil, Nat.add_zero, GalilScaffoldChainSweep.run] at hpred
  have hleft := (represented_position _ raw hrep hpres).1
  have hnext : position (GalilScaffoldChainVerifier.right w.machine.verifier) =
      anchor + pre.length := by rw [right_position _ hcan hleft]; omega
  have hread : read (GalilScaffoldChainVerifier.right w.machine.verifier) =
      (encoded raw)[anchor + pre.length]? := by
    rw [represented_read _ raw (right_word _ raw hrep hcan) (right_present _ raw hrep hpres hcan),
      hnext]
  have hper := periodOn_mod (by omega) hwin.1 pre.length (by omega)
  have hwinv := hwin.2 (pre.length % (2 * (xs.length + 1))) (Nat.mod_lt _ (by omega))
  have hne : read (GalilScaffoldChainVerifier.right w.machine.verifier) ≠ none := by
    have hf := right_present _ raw hrep hpres hcan
    rcases hz : (GalilScaffoldChainVerifier.right w.machine.verifier).head.focus with _ | z
    · exact absurd hz hf
    · simp [GalilScaffoldInputHead.read, hz]
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
  refine ⟨hcan, a, ?_, ha⟩
  rw [hpred, ← hwinv, ← hper, ← hread, ha]

/-- One agreeing consume keeps the core (the read index advances by one). -/
theorem spanCore_consume {raw : List (Fin 2)} {center b : Fin 3} {xs : List (Fin 3)}
    {anchor : ℕ} {w : WState}
    (hc : SpanCore raw center b xs anchor w.machine) (hg : GalilScaffoldChainWatch.Good w) :
    SpanCore raw center b xs anchor (GalilScaffoldChainVerifier.consume w.machine) := by
  obtain ⟨hblk, hrep, hpres, hbr, pre, hsame, hbr0, hidx⟩ := hc
  obtain ⟨hcan, a, hsym, hread⟩ := hg
  have hleft := (represented_position _ raw hrep hpres).1
  have hctl : (GalilScaffoldChainVerifier.consume w.machine).control =
      GalilScaffoldChainConsume.consume w.machine.control (some a) := by
    show GalilScaffoldChainConsume.consume w.machine.control
      (read (GalilScaffoldChainVerifier.right w.machine.verifier)) = _
    rw [hread]
  refine ⟨onBlock_verifier_consume _ hblk, right_word _ raw hrep hcan,
    right_present _ raw hrep hpres hcan, ?_, pre ++ [a], ?_, ?_, ?_⟩
  · rw [hctl]; exact consume_keeps_unbroken _ a hsym hbr
  · rw [hctl, GalilScaffoldChainSweep.run_append]
    exact GalilScaffoldChainPrediction.consume_same_prediction hsame (some a)
  · rw [GalilScaffoldChainSweep.run_append]
    show (GalilScaffoldChainConsume.consume _ (some a)).broken = false
    rw [← GalilScaffoldChainPrediction.consume_same_broken hsame (by rw [hbr, hbr0]) (some a)]
    exact consume_keeps_unbroken _ a hsym hbr
  · show position (GalilScaffoldChainVerifier.right w.machine.verifier) + 1 = _
    rw [right_position _ hcan hleft, List.length_append, List.length_singleton]
    omega

theorem consume_position {raw : List (Fin 2)} {center b : Fin 3} {xs : List (Fin 3)}
    {anchor : ℕ} {w : WState}
    (hc : SpanCore raw center b xs anchor w.machine) (hg : GalilScaffoldChainWatch.Good w) :
    position (GalilScaffoldChainVerifier.consume w.machine).verifier =
      position w.machine.verifier + 1 :=
  right_position _ hg.1 (represented_position _ raw hc.2.1 hc.2.2.1).1

/-- Closure under the background phase. -/
theorem spanCore_internal {raw : List (Fin 2)} {center b : Fin 3} {xs : List (Fin 3)}
    {anchor : ℕ} {w m : WState} (h : GalilScaffoldChainWatch.Internal w m)
    (hc : SpanCore raw center b xs anchor w.machine) :
    SpanCore raw center b xs anchor m.machine := by
  cases h with
  | idle => exact hc
  | take _ hg => exact spanCore_consume hc hg

/-- Closure under the credit phase. -/
theorem spanCore_outer {raw : List (Fin 2)} {center b : Fin 3} {xs : List (Fin 3)}
    {anchor : ℕ} {w m : WState} {β : Bool} (h : GalilScaffoldChainWatch.Outer w β m)
    (hc : SpanCore raw center b xs anchor w.machine) :
    SpanCore raw center b xs anchor m.machine := by
  cases h with
  | idle => exact hc
  | queued => exact hc
  | immediate _ hg => exact spanCore_consume hc hg

/-- The watch state `backDone` creates from the rewound block is in the core,
with `pre = []`, when the verifier sits one place before the anchor. -/
theorem spanCore_born {raw : List (Fin 2)} (center b : Fin 3) (xs : List (Fin 3)) {anchor : ℕ}
    (ver : PlaceHead) (hrep : GalilScaffoldInputTrace.Represents ver.head raw)
    (hpres : ver.head.focus ≠ none) (hpos : position ver + 1 = anchor) :
    SpanCore raw center b xs anchor
      ⟨ver, watchControl
        ⟨[], .first center, xs.map GalilScaffoldChainPeriod.Token.plain ++
          [GalilScaffoldChainPeriod.Token.last b]⟩⟩ := by
  refine ⟨?_, hrep, hpres, rfl, [], ⟨rfl, rfl⟩, rfl, by simpa using hpos⟩
  exact onBlock_moveRight ⟨center, b, xs, rfl⟩ rfl

/-- **The per-tick watch step under the span.**  With room for two reads
(`position verifier + 2 ≤ B`), a watching chain in the core ticks — on either
comparison bit — into a watching chain in the core: the zero-lag credit is
the `immediate` consume, never `breaks`, and the verifier moves at most two
places.  This is what a repaired `no_break_during_replay` needs on `.watch`,
with the room supplied per tick by the replay's `Frontier` bound. -/
theorem span_watch_tick {raw : List (Fin 2)} {center b : Fin 3} {xs : List (Fin 3)}
    {anchor B : ℕ} {w : WState}
    (hc : SpanCore raw center b xs anchor w.machine) (hwin : SpanWindow raw center b xs anchor B)
    (hB : B < (encoded raw).length) (hroom : position w.machine.verifier + 2 ≤ B) (a : Bool) :
    ∃ w' : WState, ChainTick a (.watch w) (.watch w') ∧
      SpanCore raw center b xs anchor w'.machine ∧
      position w'.machine.verifier ≤ position w.machine.verifier + 2 := by
  have hgw := spanCore_good hc hwin hB (by omega)
  obtain ⟨m, hi, hpm⟩ : ∃ m : WState, GalilScaffoldChainWatch.Internal w m ∧
      position m.machine.verifier ≤ position w.machine.verifier + 1 := by
    by_cases hp : positive w.lag = true
    · refine ⟨_, .take w hp hgw, ?_⟩
      show position (GalilScaffoldChainVerifier.consume w.machine).verifier ≤ _
      rw [consume_position hc hgw]
    · exact ⟨w, .idle w (Bool.eq_false_iff.mpr hp), by omega⟩
  have hcm := spanCore_internal hi hc
  cases a with
  | false => exact ⟨m, ⟨_, .watchStep _ _ hi, rfl⟩, hcm, by omega⟩
  | true =>
    by_cases hz : zero m.lag = true
    · have hgm := spanCore_good hcm hwin hB (by omega)
      refine ⟨_, ⟨_, .watchStep _ _ hi, .watch _ _ (.immediate m hz hgm)⟩,
        spanCore_outer (.immediate m hz hgm) hcm, ?_⟩
      show position (GalilScaffoldChainVerifier.consume m.machine).verifier ≤ _
      rw [consume_position hcm hgm]; omega
    · have hz' : zero m.lag = false := Bool.eq_false_iff.mpr hz
      exact ⟨_, ⟨_, .watchStep _ _ hi, .watch _ _ (.queued m hz')⟩,
        spanCore_outer (.queued m hz') hcm, by show position m.machine.verifier ≤ _; omega⟩

/-! ## 3. `StartOk` -/

/-- `ChainOk` of the started chain, from the answer/walker shape and the
verifier guard (independent of `Ok`). -/
theorem chainOk_chainStart {Ok : WState → Prop} {answer : GalilScaffoldTape.Tape} {n : ℕ}
    (ha : AnswerAhead answer n) (hn : 0 < n) (c : Fin 3) {walker : GalilScaffoldPlace.Place}
    (hw : PlaceAhead walker n) {ver : PlaceHead} (hcan : GalilScaffoldChainVerifier.canRight ver)
    (radius : Counter) :
    ChainOk Ok (chainStart answer c walker ver radius) := by
  unfold chainStart
  exact ⟨⟨n, ha, hw, onPrefix_start c, rfl, fun h0 => absurd h0 (by omega)⟩, hcan⟩

/-- The same from the exact DP answer (`GalilShiftH.AnswerExact`). -/
theorem chainOk_chainStart_exact {Ok : WState → Prop} {answer : GalilScaffoldTape.Tape} {n : ℕ}
    (ha : GalilShiftH.AnswerExact answer n) (hn : 0 < n) (c : Fin 3)
    {walker : GalilScaffoldPlace.Place} (hw : PlaceAhead walker n) {ver : PlaceHead}
    (hcan : GalilScaffoldChainVerifier.canRight ver) (radius : Counter) :
    ChainOk Ok (chainStart answer c walker ver radius) :=
  chainOk_chainStart (GalilShiftH.answerExact_ahead ha) hn c hw hcan radius

open GalilScaffoldTop GalilBranchInvariants2 in
/-- **Named hypothesis.**  At a found search effect on an idle chain, the DP
answer tape carries `n ≥ 1` unary ones over `LEFT`, the walker has `n+1` cells,
and the start verifier `s.center` can move right.  (The last clause is not
implied by `StartOk`'s premises, which do not constrain `s.center`; in the
replay it comes from centre < right ≤ frontier.  The first two are the
`found_copy_walk_least` shape in run mode.) -/
def StartShape (P : Shared) : Prop :=
  ∀ (s : GalilVM) (a : Bool) (vq : SearchVM), s.chain = .idle →
    SearchReady (searchLens.get s) → searchEffect P a s vq → vq.search.mode = .found →
    ∃ n, 0 < n ∧ AnswerAhead (vq.dp.config.tapes 11) n ∧ PlaceAhead (P.place s) n ∧
      GalilScaffoldChainVerifier.canRight s.center

open GalilScaffoldTop in
/-- `StartOk` for every `Ok`, from `StartShape`. -/
theorem startOk_of_shape {P : Shared} (h : StartShape P) (Ok : WState → Prop) : StartOk P Ok := by
  intro s a vq hidle hsr hq hf
  obtain ⟨n, hn, ha, hw, hcan⟩ := h s a vq hidle hsr hq hf
  exact chainOk_chainStart ha hn _ hw hcan _

#print axioms mu_right
#print axioms watchOk_good_no_state
#print axioms watchOk_good_false
#print axioms no_watchOk_instance
#print axioms periodOn_mod
#print axioms spanCore_good
#print axioms spanCore_consume
#print axioms consume_position
#print axioms spanCore_internal
#print axioms spanCore_outer
#print axioms spanCore_born
#print axioms span_watch_tick
#print axioms chainOk_chainStart
#print axioms chainOk_chainStart_exact
#print axioms startOk_of_shape

end PalPeg.GalilWatchOkInst
