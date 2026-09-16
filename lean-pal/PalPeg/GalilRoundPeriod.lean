import PalPeg.GalilSegmentConstruct3
import PalPeg.GalilGoodLag
import PalPeg.GalilOriginPeriod

/-!
# The periodicity content of one re-shift round (`hmid` / `hbreak`)

`GalilRoundConstruct.round_scan_construct` leaves two named hypotheses:

* `hmid` — before the terminal every comparison matches **and** the watch is
  `Good`;
* `hbreak` — at a *matched* terminal the chain breaks.

This module supplies the mathematics behind both, with the loop invariant of
the round written out explicitly (`RoundScan`) instead of hidden.

## The index picture

Write `C`, `R` for the centre and radius of the round's *origin* (the previous
palindrome, `PalAt (encoded raw) C R` with `2h ≤ R`), and `C' = C + h` for the
shifted centre.  After `used` comparisons of the round the scan invariant is
`CaughtScan raw C' (R+1-h+used)`, so

* the left head reads at   `ℓ used = C' - (R+1-h+used) - 1 = C + 2h - R - 2 - used`;
* the right head reads at  `j used = C' + (R+1-h+used) + 1 = C + R + 2 + used`;
* the chain predicts       `π used = j used - 2h = C + R + 2 + used - 2h`.

The decisive identity is `ℓ used + π used = 2*C`: the compared left symbol and
the chain's prediction are **mirror images about the origin's centre `C`**.
Hence, as long as both sit inside the origin's palindrome, i.e.

  `C - R ≤ ℓ used`  ⟺  `used + 1 < 2*h`  ⟺  `singlePositive cycle = false`,

`mirror_getElem?` gives `read (left u.left) = prediction` *unconditionally*, and
therefore

* **non-terminal**: a matched comparison is a `Good` chain step
  (`roundScan_good_of_match`) — and, by the same identity, the scan match at `j`
  is *equivalent* to the period `2h` extending to `j` (`match_iff_period`);
* **terminal** (`used = 2h - 1`): `ℓ = C - R - 1` and `π = C + R + 1`, which is
  exactly the pair the origin *mismatched* on (`ReadOrigin.mismatch`), so the
  prediction is necessarily wrong and a matched comparison breaks the chain
  (`roundScan_break_of_match`).

So `hbreak` is fully derived, while `hmid` reduces to its first conjunct only:
that the round contains no mismatch.  That residue is genuinely input
dependent and is isolated as the hypothesis `hnomismatch` below; see the
"Gaps" section at the end of this file.
-/

set_option autoImplicit false
namespace PalPeg.GalilRoundPeriod

open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter
  GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilScaffoldChainInputSupply

universe u
variable {α : Type u}

/-! ## 1. The combinatorial core -/

/-- **Mirror identity.**  Two indices whose sum is `2*C` carry the same symbol,
provided the first one lies inside the palindrome `PalAt x C R`.  This is
`mirror_getElem?` in the form the round's bookkeeping produces it. -/
theorem mirror_match_of_period {x : List α} {C R l p : ℕ} (hpal : PalAt x C R)
    (hsum : l + p = 2 * C) (h1 : C - R ≤ l) (h2 : l ≤ C + R) : x[l]? = x[p]? := by
  have h := Manacher.mirror_getElem? hpal h1 h2
  rw [show 2 * C - l = p from by omega] at h
  exact h

set_option linter.unusedVariables false in
/-- **The scan match is the period extension.**  For a new place `j` just past
the origin's palindrome, comparing `x[j]` against its mirror about the shifted
centre `C + h` is the *same* comparison as testing the period `2h` at `j`:
the two right-hand sides are mirror images about `C`.

This is why the round needs no separate periodicity oracle: what the scan
verifies and what the chain predicts coincide, place by place. -/
theorem mirror_index_eq {x : List α} {C R h j : ℕ} (hpal : PalAt x C R)
    (hh : 0 < h) (hk : 2 * h ≤ R) (hR : R < C) (hj1 : C + R < j) (hj2 : j ≤ C + R + h) :
    x[j - 2 * h]? = x[2 * (C + h) - j]? :=
  mirror_match_of_period hpal (by omega) (by omega) (by omega)

/-- The equivalence form: the scan match at `j` holds iff the period `2h`
extends to `j`. -/
theorem match_iff_period {x : List α} {C R h j : ℕ} (hpal : PalAt x C R)
    (hh : 0 < h) (hk : 2 * h ≤ R) (hR : R < C) (hj1 : C + R < j) (hj2 : j ≤ C + R + h) :
    (x[j]? = x[2 * (C + h) - j]? ↔ x[j - 2 * h]? = x[j]?) := by
  have e := mirror_index_eq hpal hh hk hR hj1 hj2
  constructor
  · intro hm; rw [e]; exact hm.symm
  · intro hm; rw [← e]; exact hm.symm

set_option linter.unusedVariables false in
/-- A matched place extends a period interval by one. -/
theorem periodOn_snoc {x : List α} {p a b : ℕ} (hper : PeriodOn x p a b)
    (hp : p ≤ b + 1) (ha : a ≤ b + 1 - p)
    (heq : x[b + 1 - p]? = x[b + 1]?) : PeriodOn x p a (b + 1) := by
  intro i hi hib
  rcases Nat.lt_or_ge (i + p) (b + 1) with hlt | hge
  · exact hper i hi (by omega)
  · have : i = b + 1 - p := by omega
    subst this
    rw [show b + 1 - p + p = b + 1 from by omega]
    exact heq

/-! ## 2. Head bookkeeping -/

/-- The left neighbour of a represented head is still present, as soon as the
head is at least two places in. -/
theorem left_present (q : PlaceHead) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents q.head raw) (hp : q.head.focus ≠ none)
    (hpos : 2 ≤ position q) : (GalilScaffoldInputHead.left q).head.focus ≠ none := by
  rcases q with ⟨hd, gap⟩
  obtain ⟨xs, rs, qs, rfl, rfl⟩ := hh
  cases gap with
  | true => simpa [GalilScaffoldInputHead.left] using hp
  | false =>
    cases xs with
    | nil => simp [layout] at hp
    | cons a xs =>
      cases xs with
      | nil => simp [position, layout] at hpos
      | cons b xs =>
        simp [GalilScaffoldInputHead.left, GalilScaffoldInputHead.moveLeft, layout]

/-- The symbol the left head is about to compare, as an index into the encoded
word. -/
theorem left_read_index (q : PlaceHead) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents q.head raw) (hp : q.head.focus ≠ none)
    (hpos : 2 ≤ position q) :
    GalilScaffoldInputHead.read (GalilScaffoldInputHead.left q)
      = (encoded raw)[position q - 1]? := by
  have hl := (represented_position q.head raw hh hp).1
  have hstep := left_position q hl
  rw [represented_read _ raw (left_word q raw hh hp) (left_present q raw hh hp hpos)]
  rw [show position q - 1 = position (GalilScaffoldInputHead.left q) from by omega]

/-- The symbol the right head is about to compare, as an index into the encoded
word. -/
theorem right_read_index (q : PlaceHead) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents q.head raw) (hp : q.head.focus ≠ none)
    (hc : canRight q) :
    GalilScaffoldInputHead.read (right q) = (encoded raw)[position q + 1]? := by
  have hl := (represented_position q.head raw hh hp).1
  rw [represented_read _ raw (right_word q raw hh hc) (right_present q raw hh hp hc),
    right_position q hc hl]

/-- **The origin's mismatch, as an inequality of encoded symbols.**  A read
origin is built at a place where the scan *failed*: `x[C-R-1] ≠ x[C+R+1]`. -/
theorem origin_mismatch_index {raw : List (Fin 2)} (o : ReadOrigin raw)
    (hroom : o.radius + 2 ≤ o.center) :
    (encoded raw)[o.center - o.radius - 1]? ≠ (encoded raw)[o.center + o.radius + 1]? := by
  have hs := o.scan
  have hlpos : position o.left = o.center - o.radius := hs.leftPos
  have hrpos : position o.rightHead = o.center + o.radius := hs.rightPos
  have hl := left_read_index o.left raw hs.leftRep hs.leftPresent (by omega)
  have hr := right_read_index o.rightHead raw hs.rightRep hs.rightPresent o.available
  rw [hlpos] at hl
  rw [hrpos] at hr
  rw [← hl, ← hr]
  exact o.mismatch

/-! ## 3. The loop invariant of a round -/

/-- **The scan-half invariant of one re-shift round**, written out.

`C`, `R` are the origin's centre and radius, `h` the semiperiod, `used` the
number of comparisons already performed in this round.  The chain is a
zero-lag watch aligned with the scan (`CaughtScan`), the cycle counter is the
countdown `2h - used`, and — this is the only field that talks about the chain's
internals — `pred` records that the chain predicts the encoded symbol one
period behind its verifier. -/
structure RoundScan (raw : List (Fin 2)) (C R h used : ℕ)
    (v : GalilVM) (w : GalilScaffoldChainWatch.State) : Prop where
  chain : v.chain = ChainVM.watch w
  caught : CaughtScan raw (C + h) (R + 1 - h + used) v.left v.right w
  canon : Canonical v.cycle
  count : value v.cycle = (2 * h : ℤ) - used
  fresh : used < 2 * h
  size : 2 * h ≤ R
  posH : 0 < h
  pal : PalAt (encoded raw) C R
  room : R + 2 ≤ C
  origin : (encoded raw)[C - R - 1]? ≠ (encoded raw)[C + R + 1]?
  pred : GalilScaffoldChainConsume.symbol w.machine.control.period.focus
    = (encoded raw)[C + R + 2 + used - 2 * h]?

namespace RoundScan

variable {raw : List (Fin 2)} {C R h used : ℕ} {v : GalilVM}
  {w : GalilScaffoldChainWatch.State}

/-- The scan's right head sits at `C + R + 1 + used`. -/
theorem rightPos (hI : RoundScan raw C R h used v w) :
    position v.right = C + R + 1 + used := by
  have h1 := hI.caught.scan.rightPos
  have := hI.size; have := hI.posH; have := hI.room
  omega

/-- The scan's left head sits at `C + 2h - R - 1 - used`. -/
theorem leftPos (hI : RoundScan raw C R h used v w) :
    position v.left = C + 2 * h - R - 1 - used := by
  have h1 := hI.caught.scan.leftPos
  have := hI.size; have := hI.posH; have := hI.room; have := hI.fresh
  omega

/-- The compared left symbol, as an index. -/
theorem left_read (hI : RoundScan raw C R h used v w) :
    GalilScaffoldInputHead.read (GalilScaffoldInputHead.left v.left)
      = (encoded raw)[C + 2 * h - R - 2 - used]? := by
  have hs := hI.caught.scan
  have hpos := hI.leftPos
  have := hI.size; have := hI.posH; have := hI.room; have := hI.fresh
  have hl := left_read_index v.left raw hs.leftRep hs.leftPresent (by omega)
  rw [hl, hpos]
  congr 1
  omega

/-- The terminal of the round is exactly `used = 2h - 1`. -/
theorem terminal_iff (hI : RoundScan raw C R h used v w) :
    singlePositive v.cycle = true ↔ used + 1 = 2 * h := by
  rw [singlePositive_iff v.cycle hI.canon, hI.count]
  have := hI.fresh
  constructor <;> intro hh <;> omega

/-- **Before the terminal the chain's prediction is already known to be right.**
The compared left symbol and the prediction are mirror images about the
origin's centre `C`, and at a non-terminal place both lie inside the origin's
palindrome. -/
theorem prediction_left (hI : RoundScan raw C R h used v w)
    (hend : singlePositive v.cycle = false) :
    GalilScaffoldInputHead.read (GalilScaffoldInputHead.left v.left)
      = GalilScaffoldChainConsume.symbol w.machine.control.period.focus := by
  have hne : used + 1 ≠ 2 * h := by
    intro he
    rw [hI.terminal_iff.mpr he] at hend
    cases hend
  have := hI.size; have := hI.posH; have := hI.room; have := hI.fresh
  rw [hI.left_read, hI.pred]
  exact mirror_match_of_period hI.pal (by omega) (by omega) (by omega)

/-- **At the terminal the chain's prediction is already known to be wrong.**
There `used = 2h - 1`, so the compared left symbol is `x[C-R-1]` and the
prediction is `x[C+R+1]` — the very pair the origin mismatched on. -/
theorem prediction_terminal (hI : RoundScan raw C R h used v w)
    (hend : singlePositive v.cycle = true) :
    GalilScaffoldInputHead.read (GalilScaffoldInputHead.left v.left)
      ≠ GalilScaffoldChainConsume.symbol w.machine.control.period.focus := by
  have he := hI.terminal_iff.mp hend
  have := hI.size; have := hI.posH; have := hI.room
  rw [hI.left_read, hI.pred,
    show C + 2 * h - R - 2 - used = C - R - 1 from by omega,
    show C + R + 2 + used - 2 * h = C + R + 1 from by omega]
  exact hI.origin

/-- **`hmid`'s second conjunct, derived.**  A matched non-terminal comparison
is a `Good` chain step, and the invariant advances by one place. -/
theorem good_of_match (hI : RoundScan raw C R h used v w)
    (hav : canRight v.right) (hend : singlePositive v.cycle = false)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left v.left)
      = GalilScaffoldInputHead.read (right v.right)) :
    GalilScaffoldChainWatch.Good w ∧
      CaughtScan raw (C + h) (R + 1 - h + used + 1) (GalilScaffoldInputHead.left v.left)
        (right v.right) (GalilScaffoldChainWatch.immediate w) :=
  caught_scan_matched hI.caught hav (hI.prediction_left hend) hmatch

/-- **`hbreak`, derived.**  A matched terminal comparison breaks the chain: the
prediction is the origin's mismatching symbol, so it cannot equal the symbol
the verifier actually reads. -/
theorem break_of_match (hI : RoundScan raw C R h used v w)
    (hav : canRight v.right) (hend : singlePositive v.cycle = true)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left v.left)
      = GalilScaffoldInputHead.read (right v.right)) :
    ∃ w', BreakStep w w' := by
  have hc := hI.caught
  have hs := hc.scan
  -- the verifier can move right, because the scan's right head can
  have hrrep := right_word v.right raw hs.rightRep hav
  have hrpres := right_present v.right raw hs.rightRep hs.rightPresent hav
  have hrpos := right_position v.right hav
    (represented_position v.right.head raw hs.rightRep hs.rightPresent).1
  have hbound := position_bound (right v.right) raw hrrep hrpres
  have hvc : canRight w.machine.verifier :=
    canRight_of_bound w.machine.verifier raw hc.verifierRep hc.verifierPresent
      (by rw [hc.aligned]; omega)
  have hvrep := right_word _ raw hc.verifierRep hvc
  have hvpres := right_present _ raw hc.verifierRep hc.verifierPresent hvc
  have hvpos := right_position w.machine.verifier hvc
    (represented_position w.machine.verifier.head raw hc.verifierRep hc.verifierPresent).1
  -- the verifier reads the same symbol as the scan's right head
  have hread : GalilScaffoldInputHead.read (right w.machine.verifier)
      = GalilScaffoldInputHead.read (right v.right) := by
    rw [represented_read _ raw hvrep hvpres, represented_read _ raw hrrep hrpres,
      hvpos, hrpos, hc.aligned]
  -- the prediction is present: it is the encoded symbol at `C + R + 1`
  have he := hI.terminal_iff.mp hend
  have hsz := hI.size; have hph := hI.posH; have hrm := hI.room
  have hidx : C + R + 2 + used - 2 * h = C + R + 1 := by omega
  have hlt : C + R + 1 < (encoded raw).length := by
    have := hs.palindrome.2.1
    have := hs.rightPos
    omega
  obtain ⟨a, ha⟩ : ∃ a, (encoded raw)[C + R + 1]? = some a :=
    ⟨(encoded raw)[C + R + 1], List.getElem?_eq_getElem hlt⟩
  have hpred : GalilScaffoldChainConsume.symbol w.machine.control.period.focus = some a := by
    rw [hI.pred, hidx]; exact ha
  refine ⟨⟨consume w.machine, w.lag, inc w.margin⟩,
    hc.lagZero, hvc, a, hpred, ?_, rfl⟩
  rw [hread, ← hmatch]
  intro hbad
  exact (hI.prediction_terminal hend) (hbad.trans hpred.symm)

end RoundScan

/-! ## 5. Anchoring the invariant: entry and step -/

/-- **`RoundScan` at the start of a round.**  Everything comes from the read
origin: the scan half from `Entry`, the periodicity of the prediction from
`origin_prediction_index` at the empty continuation, and the mismatch from
`ReadOrigin.mismatch`.

`hroom` (`o.radius + 2 ≤ o.center`, i.e. the origin's mismatching place is not
the very first cell of the encoded word) is the one arithmetic side condition
that `ReadOrigin` does not record. -/
theorem roundScan_entry {raw : List (Fin 2)} (o : ReadOrigin raw) (h : ℕ)
    (hint : o.interior.length + 1 = h)
    {vm : GalilVM} {w : GalilScaffoldChainWatch.State}
    (hchain : vm.chain = ChainVM.watch w)
    (he : Entry raw o (toOnly vm w))
    (hroom : o.radius + 2 ≤ o.center) :
    RoundScan raw o.center o.radius h 0 vm w := by
  have hh : 0 < h := by omega
  have hsize : 2 * h ≤ o.radius := by have := o.size; omega
  have hmach : w.machine = o.shifted.machine := he.machine
  have hcaught : CaughtScan raw (o.center + h) (o.radius + 1 - h + 0) vm.left vm.right w := by
    have hcs := he.scan.caught
    rw [hint] at hcs
    exact hcs
  have hb0 : (GalilScaffoldChainSweep.run o.shifted.machine.control []).broken = false := by
    show o.shifted.machine.control.broken = false
    rw [← hmach]; exact he.scan.caught.unbroken
  have hpred := origin_prediction_index o h hint [] (by simp only [List.length_nil]; omega) hb0
  simp only [List.length_nil, Nat.add_zero] at hpred
  rw [← hmach] at hpred
  refine ⟨hchain, hcaught, he.scan.canonical, ?_, by omega, hsize, hh,
    o.scan.palindrome, hroom, origin_mismatch_index o hroom, ?_⟩
  · have hc : value vm.cycle
        = ((2 * (o.interior.length + 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) := he.scan.count
    rw [hc, ← hint]; push_cast; ring
  · show GalilScaffoldChainConsume.symbol
      (GalilScaffoldChainSweep.run w.machine.control []).period.focus = _
    rw [hpred]

/-- **`RoundScan` survives a matched non-terminal comparison.**  The scan half
is `caught_scan_matched`, the counter is `dec`, and the only genuinely new
field is `hadvance`: the chain's period tape, after the immediate consume,
predicts the next encoded symbol.  That is the transport supplied by
`origin_prediction_index` at a one-longer continuation; relating the round's
intermediate control to `run o.shifted.machine.control extra` needs the `Reads`
trace of the round, and is left as this named hypothesis. -/
theorem roundScan_step {raw : List (Fin 2)} {C R h used : ℕ} {vm vm' : GalilVM}
    {w : GalilScaffoldChainWatch.State}
    (hI : RoundScan raw C R h used vm w)
    (hav : canRight vm.right) (hend : singlePositive vm.cycle = false)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left vm.left)
      = GalilScaffoldInputHead.read (right vm.right))
    (hchain : vm'.chain = ChainVM.watch (GalilScaffoldChainWatch.immediate w))
    (hleft : vm'.left = GalilScaffoldInputHead.left vm.left)
    (hright : vm'.right = right vm.right)
    (hcycle : vm'.cycle = dec vm.cycle)
    (hadvance : GalilScaffoldChainConsume.symbol
        (GalilScaffoldChainWatch.immediate w).machine.control.period.focus
      = (encoded raw)[C + R + 2 + (used + 1) - 2 * h]?) :
    RoundScan raw C R h (used + 1) vm' (GalilScaffoldChainWatch.immediate w) := by
  have hne : used + 1 ≠ 2 * h := by
    intro heq
    rw [hI.terminal_iff.mpr heq] at hend
    cases hend
  have hcaught := (hI.good_of_match hav hend hmatch).2
  refine ⟨hchain, ?_, ?_, ?_, by have := hI.fresh; omega, hI.size, hI.posH,
    hI.pal, hI.room, hI.origin, hadvance⟩
  · rw [hleft, hright]
    have e : R + 1 - h + (used + 1) = R + 1 - h + used + 1 := by omega
    rw [e]; exact hcaught
  · rw [hcycle]; exact dec_canonical _ hI.canon
  · rw [hcycle, dec_value, hI.count]; push_cast; ring

/-! ## 6. The two hypotheses of `round_scan_construct` -/

/-- **`hmid`, in the shape `round_scan_construct` needs it**, with the round's
loop invariant `S` explicit.

Two hypotheses remain, and they are of different kinds.

* `hcover` — every state the scan loop reaches before its terminal satisfies
  the invariant.  `scan_half` quantifies `hmid` over *all* `u`, so the round's
  invariant has to be re-threaded through the loop before this can be
  discharged; see the "Gaps" note below.
* `hnomismatch` — the round contains no mismatch.  This is genuinely input
  dependent: `x[C+R+2+used]` is a symbol nobody has read yet, and by
  `match_iff_period` the comparison succeeds exactly when the period `2h`
  extends to it.  It cannot be derived. -/
theorem hmid_of_periodOn (raw : List (Fin 2)) (C R h : ℕ)
    (S : GalilVM → GalilScaffoldChainWatch.State → Prop)
    (hS : ∀ vm w, S vm w → ∃ used, RoundScan raw C R h used vm w)
    (hcover : ∀ vm w, vm.chain = ChainVM.watch w → canRight vm.right →
      singlePositive vm.cycle = false → S vm w)
    (hnomismatch : ∀ vm w, S vm w → canRight vm.right → singlePositive vm.cycle = false →
      GalilScaffoldInputHead.read (GalilScaffoldInputHead.left vm.left)
        = GalilScaffoldInputHead.read (right vm.right)) :
    ∀ (vm : GalilVM) (w : GalilScaffoldChainWatch.State),
      vm.chain = ChainVM.watch w → canRight vm.right → singlePositive vm.cycle = false →
      GalilScaffoldInputHead.read (GalilScaffoldInputHead.left vm.left)
          = GalilScaffoldInputHead.read (right vm.right) ∧
        GalilScaffoldChainWatch.Good w := by
  intro vm w hchain hav hend
  have hSvw := hcover vm w hchain hav hend
  obtain ⟨used, hI⟩ := hS vm w hSvw
  have hmatch := hnomismatch vm w hSvw hav hend
  exact ⟨hmatch, (hI.good_of_match hav hend hmatch).1⟩

/-- **`hbreak`, in the shape `round_scan_construct` needs it.**  Only the
coverage hypothesis remains: at a matched terminal the break is *derived*, with
no extra assumption about the input. -/
theorem hbreak_of_terminal (raw : List (Fin 2)) (C R h : ℕ)
    (S : GalilVM → GalilScaffoldChainWatch.State → Prop)
    (hS : ∀ vm w, S vm w → ∃ used, RoundScan raw C R h used vm w)
    (hcover : ∀ vm w, vm.chain = ChainVM.watch w → canRight vm.right →
      singlePositive vm.cycle = true → S vm w) :
    ∀ (vm : GalilVM) (w : GalilScaffoldChainWatch.State),
      vm.chain = ChainVM.watch w → canRight vm.right → singlePositive vm.cycle = true →
      GalilScaffoldInputHead.read (GalilScaffoldInputHead.left vm.left)
        = GalilScaffoldInputHead.read (right vm.right) → ∃ w', BreakStep w w' := by
  intro vm w hchain hav hend hmatch
  obtain ⟨used, hI⟩ := hS vm w (hcover vm w hchain hav hend)
  exact hI.break_of_match hav hend hmatch

#print axioms mirror_match_of_period
#print axioms mirror_index_eq
#print axioms match_iff_period
#print axioms periodOn_snoc
#print axioms left_present
#print axioms left_read_index
#print axioms right_read_index
#print axioms origin_mismatch_index
#print axioms RoundScan.rightPos
#print axioms RoundScan.leftPos
#print axioms RoundScan.left_read
#print axioms RoundScan.terminal_iff
#print axioms RoundScan.prediction_left
#print axioms RoundScan.prediction_terminal
#print axioms RoundScan.good_of_match
#print axioms RoundScan.break_of_match
#print axioms roundScan_entry
#print axioms roundScan_step
#print axioms hmid_of_periodOn
#print axioms hbreak_of_terminal

end PalPeg.GalilRoundPeriod
