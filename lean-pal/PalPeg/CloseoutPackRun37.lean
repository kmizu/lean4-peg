import PalPeg.CloseoutPackRun31

/-!
# `CloseoutPackRun37`: the shift phase of a chain round (`H_shiftDone`)

`CloseoutPackRun31.chainRound_tick` leaves `H_shiftDone`: the round datum
`RoundScan` of the *next* round at the `shift_done` exit.  That exit is a
one-state tick (`Tick.shift_done` keeps the VM), so nothing at the exit
remembers the terminal comparison; the datum has to be carried through the
shift phase.  This module does that.

* §1 `ShiftInv`: the shift-phase datum — the terminal round's origin `(C, R)`
  and half period `h`, the progress `k` of the shift (`remaining = h − k`,
  `cycle = 2k`, the left head `2k` places right of `C − R − 1`), the
  palindromes `PalAt (C+h) (R+h)` (the round's caught scan at its terminal)
  and `PalAt (C+2h) (R+1)` (`terminal_palindrome`), the terminal mismatch
  (the next round's origin) and the chain's prediction after the terminal
  consume (`x[C+R+2]`).
* §2 `roundScan_of_shiftInv`: at exhaustion (`k = h`) the datum *is* the
  next round's `RoundScan` at `(C+h, R+h)`, `used = 0`.  This discharges
  `H_shiftDone` from the one-state invariant `ShiftRound`
  (`h_shiftDone_of_shiftRound`).
* §3 `shiftInv_entry` / `shiftInv_step`: the datum is born at the
  `scan_shift` tick from the terminal `RoundScan` (the guard supplies the
  prediction, the mismatch supplies the origin) and survives `shift_one`.
  `shiftRound_tick` assembles them into a `galilFrameS` tick theorem, modulo
  `H_advanceT` (the prediction after the *terminal* consume — `H_advance`'s
  shape at `used = 2h − 1`, where `origin_prediction_index` no longer applies
  because the continuation wraps: it is the `mod 2h` form of
  `chain_shift_continued_prediction`) and `H_freshShift` (the first shift of
  a fresh chain, `periodOnly = false`, whose content is
  `GalilScaffoldTopFreshEntry`).
* §4 `ReadsInv` and `h_advance_of_readsInv`: the `Reads`-trace datum that
  `roundScan_step` asks for is not in `AuxPack`/`FrontPack`/`CopyPack`; the
  minimal addition is "the chain's control is `run o.shifted.machine.control
  extra` for the round's origin `o` and `used = extra.length`".  From it
  `H_advance` follows by `origin_prediction_index` (`readsInv_immediate`
  is its scan-match step; the background steps at lag zero are `Internal.idle`).

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun37

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono
open PalPeg.CloseoutLPack3 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun29
open PalPeg.GalilRoundPeriod PalPeg.GalilChainCoupling PalPeg.CloseoutPackRun31

/-! ## 1. The shift-phase datum -/

/-- **The shift-phase datum** of a re-shift round with origin `(C, R)` and
half period `h`, after `k` of the `h` shift units. -/
structure ShiftInv (raw : List (Fin 2)) (C R h k : ℕ) (v : GalilVM)
    (w : GalilScaffoldChainWatch.State) : Prop where
  chain : v.chain = ChainVM.watch w
  kle : k ≤ h
  posH : 0 < h
  size : 2 * h ≤ R
  room : R + 2 ≤ C
  remaining : v.remaining = ofNat (h - k)
  canon : Canonical v.cycle
  count : value v.cycle = ((2 * k : ℕ) : ℤ)
  leftRep : GalilScaffoldInputTrace.Represents v.left.head raw
  leftPresent : v.left.head.focus ≠ none
  leftPos : position v.left = C - R - 1 + 2 * k
  rightRep : GalilScaffoldInputTrace.Represents v.right.head raw
  rightPresent : v.right.head.focus ≠ none
  rightPos : position v.right = C + R + 2 * h + 1
  verifierRep : GalilScaffoldInputTrace.Represents w.machine.verifier.head raw
  verifierPresent : w.machine.verifier.head.focus ≠ none
  aligned : position w.machine.verifier = position v.right
  lagZero : zero w.lag = true
  unbroken : w.machine.control.broken = false
  pal : Manacher.PalAt (encoded raw) (C + h) (R + h)
  palNext : Manacher.PalAt (encoded raw) (C + 2 * h) (R + 1)
  origin : (encoded raw)[C - R - 1]? ≠ (encoded raw)[C + R + 2 * h + 1]?
  pred : GalilScaffoldChainConsume.symbol w.machine.control.period.focus
    = (encoded raw)[C + R + 2]?

/-- The one-state shift-round invariant: in shift mode every watching chain
carries a `ShiftInv` with `h` its period length. -/
def ShiftRound (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.shift →
  ∀ wch : GalilScaffoldChainWatch.State, s.chain = .watch wch →
    ∃ C R k : ℕ, ShiftInv w C R (periodLength wch) k s wch

/-! ## 2. Exhaustion: the next round's `RoundScan` -/

/-- **`RoundScan` of the next round at the end of the shift.** -/
theorem roundScan_of_shiftInv {raw : List (Fin 2)} {C R h k : ℕ} {v : GalilVM}
    {w : GalilScaffoldChainWatch.State} (hI : ShiftInv raw C R h k v w)
    (hz : positive v.remaining = false) :
    RoundScan raw (C + h) (R + h) h 0 v w := by
  have hk : k = h := by
    have hr := hI.remaining
    rw [hr, positive_ofNat] at hz
    have := hI.kle
    simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero_eq] at hz
    omega
  subst hk
  have hs := hI.size
  have hp := hI.posH
  have hr := hI.room
  refine ⟨hI.chain, ⟨⟨hI.leftRep, hI.rightRep, hI.leftPresent, hI.rightPresent, ?_, ?_, ?_⟩,
      hI.verifierRep, hI.verifierPresent, hI.aligned, hI.lagZero, hI.unbroken⟩,
    hI.canon, ?_, by omega, by omega, hp, hI.pal, by omega, ?_, ?_⟩
  · rw [hI.leftPos]; omega
  · rw [hI.rightPos]; omega
  · have e1 : C + k + k = C + 2 * k := by omega
    have e2 : R + k + 1 - k + 0 = R + 1 := by omega
    rw [e1, e2]; exact hI.palNext
  · rw [hI.count]; push_cast; ring
  · have e1 : C + k - (R + k) - 1 = C - R - 1 := by omega
    have e2 : C + k + (R + k) + 1 = C + R + 2 * k + 1 := by omega
    rw [e1, e2]; exact hI.origin
  · have e : C + k + (R + k) + 2 + 0 - 2 * k = C + R + 2 := by omega
    rw [e]; exact hI.pred

section Entry
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`H_shiftDone` from `ShiftRound`.** -/
theorem h_shiftDone_of_shiftRound {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hSR : ShiftRound w c s) : H_shiftDone centre place entry q first w c s := by
  intro hm _ _ hnp wch hchain
  obtain ⟨C, R, k, hI⟩ := hSR hm wch hchain
  have hz : positive s.remaining = false := by
    cases hp : positive s.remaining with
    | false => rfl
    | true => exact absurd (Or.inl hp) hnp
  exact ⟨C + periodLength wch, R + periodLength wch, 0, roundScan_of_shiftInv hI hz⟩

end Entry

/-! ## 3. Entry and step of the shift phase -/

/-- **(NAMED) the prediction after the terminal consume.**  `H_advance`'s
shape at `used = 2h − 1`: after consuming `x[C+R+1]` the chain predicts
`x[C+R+2]`, one period behind its verifier.  (`origin_prediction_index`
stops at `extra.length < 2h`; this is the wrapped, `mod 2h` form.)

The target's own guard data is part of the statement: without it the claim is
**false**, because a failing consume sets `broken := true` and leaves the period
tape where it was, so the prediction would still be `x[C+R+1]`.  Both extra
premises — `canRight s.right` and the guard's prediction — are in scope at the
only consumer (`shiftRound_tick`'s `scan_shift` branch, where `shiftGuardVM`
holds), so nothing new is owed.  `CloseoutAdvanceT.h_advanceT_of_readsRound`
discharges it from the carried `ReadsRound`. -/
def H_advanceT (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.scan → c.replaying = false → s.periodOnly = true →
  ∀ (C R used : ℕ) (w0 : GalilScaffoldChainWatch.State),
    RoundScan w C R (periodLength w0) used s w0 →
    singlePositive s.cycle = true →
    GalilScaffoldChainVerifier.canRight s.right →
    GalilScaffoldChainConsume.symbol w0.machine.control.period.focus
      = GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right s.right) →
    GalilScaffoldChainConsume.symbol
        (GalilScaffoldChainWatch.immediate w0).machine.control.period.focus =
      (encoded w)[C + R + 2]?

/-- **(NAMED) the first shift of a fresh chain** (`periodOnly = false` at the
source): its `ShiftInv` at the target, `GalilScaffoldTopFreshEntry`'s content. -/
def H_freshShift (w : List (Fin 2)) (s t : GalilVM) : Prop :=
  s.periodOnly = false →
  ∀ wch : GalilScaffoldChainWatch.State, t.chain = .watch wch →
    ∃ C R k : ℕ, ShiftInv w C R (periodLength wch) k t wch

/-- A watch born by `chainAt false` (`ChainStep.backDone`) has phase `0`. -/
theorem chainAt_false_born {found : Bool} {ans : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter} {x z : ChainVM}
    (h : chainAt false found ans cc walker ver radius x z)
    {wch : GalilScaffoldChainWatch.State} (hz : z = .watch wch)
    (hnot : ∀ w0, x ≠ .watch w0) : wch.machine.control.phase = 0 := by
  rcases h with ⟨-, y, hstep, hzy⟩ | ⟨-, -, rfl⟩ | ⟨-, -, hzc⟩
  · rw [if_neg (by simp)] at hzy
    subst hzy
    subst hz
    cases hstep with
    | watchStep w w' ht => exact absurd rfl (hnot w)
    | backDone v h lag margin ver hf => rfl
  · cases hz
  · rw [if_neg (by simp)] at hzc
    subst hzc
    unfold chainStart at hz
    cases hz

/-- **Birth of the datum at the shift entry.**  From the terminal `RoundScan`,
the guard's prediction, the mismatch and the `beginShiftVM` shape of the
target. -/
theorem shiftInv_entry {raw : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {w0 : GalilScaffoldChainWatch.State}
    (hI : RoundScan raw C R h used s w0)
    (hend : singlePositive s.cycle = true) (hcan : canRight s.right)
    (hmis : read (GalilScaffoldInputHead.left s.left) ≠ read (right s.right))
    (hpred : GalilScaffoldChainConsume.symbol w0.machine.control.period.focus =
      read (right s.right))
    (hadv : GalilScaffoldChainConsume.symbol
        (GalilScaffoldChainWatch.immediate w0).machine.control.period.focus =
      (encoded raw)[C + R + 2]?)
    {t : GalilVM}
    (hleft : t.left = GalilScaffoldInputHead.left s.left) (hright : t.right = right s.right)
    (hchain : t.chain = .watch (GalilScaffoldChainWatch.immediate w0))
    (hrem : t.remaining = ofNat h) (hcyc : t.cycle = reset) :
    ShiftInv raw C R h 0 t (GalilScaffoldChainWatch.immediate w0) := by
  have hterm := hI.terminal_iff.mp hend
  have hsize := hI.size
  have hposH := hI.posH
  have hroom := hI.room
  have hs := hI.caught.scan
  have hlpos := hI.leftPos
  have hrpos := hI.rightPos
  -- the left head
  have hl0 : 0 < s.left.head.left.length := (represented_position _ raw hs.leftRep hs.leftPresent).1
  have hlstep := left_position s.left hl0
  -- the right head
  have hr0 : 0 < s.right.head.left.length :=
    (represented_position _ raw hs.rightRep hs.rightPresent).1
  have hrrep := right_word s.right raw hs.rightRep hcan
  have hrpres := right_present s.right raw hs.rightRep hs.rightPresent hcan
  have hrstep := right_position s.right hcan hr0
  have hbound := position_bound (right s.right) raw hrrep hrpres
  -- the verifier
  have hc := hI.caught
  have hvc : canRight w0.machine.verifier :=
    canRight_of_bound _ raw hc.verifierRep hc.verifierPresent (by rw [hc.aligned]; omega)
  have hv0 : 0 < w0.machine.verifier.head.left.length :=
    (represented_position _ raw hc.verifierRep hc.verifierPresent).1
  have hvrep := right_word _ raw hc.verifierRep hvc
  have hvpres := right_present _ raw hc.verifierRep hc.verifierPresent hvc
  have hvstep := right_position w0.machine.verifier hvc hv0
  have hvread : read (right w0.machine.verifier) = read (right s.right) := by
    rw [represented_read _ raw hvrep hvpres, represented_read _ raw hrrep hrpres,
      hvstep, hrstep, hc.aligned]
  -- the read symbols as indices
  have hrr := right_read_index s.right raw hs.rightRep hs.rightPresent hcan
  have hlr := left_read_index s.left raw hs.leftRep hs.leftPresent (by omega)
  -- the right symbol is present
  have hlt : position s.right + 1 < (encoded raw).length := by rw [← hrstep]; exact hbound
  obtain ⟨a, ha⟩ : ∃ a, read (right s.right) = some a := by
    rw [hrr]
    exact ⟨(encoded raw)[position s.right + 1], List.getElem?_eq_getElem hlt⟩
  refine
    { chain := hchain
      kle := Nat.zero_le _
      posH := hposH
      size := hsize
      room := hroom
      remaining := by rw [hrem, Nat.sub_zero]
      canon := by rw [hcyc]; exact Or.inl rfl
      count := by rw [hcyc]; simp [value, reset]
      leftRep := by rw [hleft]; exact left_word s.left raw hs.leftRep hs.leftPresent
      leftPresent := by rw [hleft]; exact left_present s.left raw hs.leftRep hs.leftPresent (by omega)
      leftPos := by rw [hleft]; omega
      rightRep := by rw [hright]; exact hrrep
      rightPresent := by rw [hright]; exact hrpres
      rightPos := by rw [hright, hrstep]; omega
      verifierRep := hvrep
      verifierPresent := hvpres
      aligned := by
        show position (right w0.machine.verifier) = position t.right
        rw [hright, hvstep, hrstep, hc.aligned]
      lagZero := hc.lagZero
      unbroken := ?_
      pal := ?_
      palNext := terminal_palindrome hI hend hcan hpred
      origin := ?_
      pred := hadv }
  · show (GalilScaffoldChainVerifier.consume w0.machine).control.broken = false
    rw [(consume_agrees w0.machine a (hpred.trans ha) (hvread.trans ha)).2]
    exact hc.unbroken
  · have hp := hs.palindrome
    rw [show R + 1 - h + used = R + h by omega] at hp
    exact hp
  · rw [hlr, hrr, hlpos, hrpos] at hmis
    have e1 : C + 2 * h - R - 1 - used - 1 = C - R - 1 := by omega
    have e2 : C + R + 1 + used + 1 = C + R + 2 * h + 1 := by omega
    rw [e1, e2] at hmis
    exact hmis

/-- **One shift unit** keeps the datum, `k ↦ k + 1`. -/
theorem shiftInv_step {raw : List (Fin 2)} {C R h k : ℕ} {s t : GalilVM}
    {w : GalilScaffoldChainWatch.State}
    (hI : ShiftInv raw C R h k s w) (hpos : positive s.remaining = true)
    (hcl : canRight s.left) (hcl' : canRight (right s.left))
    (hleft : t.left = right (right s.left)) (hright : t.right = s.right)
    (hchain : t.chain = .watch (chainShiftOne w))
    (hrem : t.remaining = dec s.remaining) (hcyc : t.cycle = inc (inc s.cycle)) :
    ShiftInv raw C R h (k + 1) t (chainShiftOne w) := by
  have hlt : 0 < h - k := by
    have hr := hI.remaining
    rw [hr, positive_ofNat] at hpos
    simpa using hpos
  have hl0 : 0 < s.left.head.left.length := (represented_position _ raw hI.leftRep hI.leftPresent).1
  have rep1 := right_word s.left raw hI.leftRep hcl
  have pres1 := right_present s.left raw hI.leftRep hI.leftPresent hcl
  have pos1 := right_position s.left hcl hl0
  have hl1 : 0 < (right s.left).head.left.length := (represented_position _ raw rep1 pres1).1
  have rep2 := right_word _ raw rep1 hcl'
  have pres2 := right_present _ raw rep1 pres1 hcl'
  have pos2 := right_position _ hcl' hl1
  exact
    { chain := hchain
      kle := by have := hI.kle; omega
      posH := hI.posH
      size := hI.size
      room := hI.room
      remaining := by
        rw [hrem, hI.remaining, show h - k = (h - (k + 1)) + 1 by omega, dec_ofNat_succ]
      canon := by rw [hcyc]; exact inc_canonical _ (inc_canonical _ hI.canon)
      count := by rw [hcyc, inc_value, inc_value, hI.count]; push_cast; ring
      leftRep := by rw [hleft]; exact rep2
      leftPresent := by rw [hleft]; exact pres2
      leftPos := by rw [hleft, pos2, pos1, hI.leftPos]; omega
      rightRep := by rw [hright]; exact hI.rightRep
      rightPresent := by rw [hright]; exact hI.rightPresent
      rightPos := by rw [hright]; exact hI.rightPos
      verifierRep := hI.verifierRep
      verifierPresent := hI.verifierPresent
      aligned := by rw [hright]; exact hI.aligned
      lagZero := hI.lagZero
      unbroken := hI.unbroken
      pal := hI.pal
      palNext := hI.palNext
      origin := hI.origin
      pred := hI.pred }

section Tick
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`ShiftRound` along one tick of `galilFrameS`.**  Entry at `scan_shift`
from `ChainRound` (the chain was watching in a round; a chain born *in* the
comparison has phase `0` and fails the guard), step at `shift_one`, every
other target mode vacuous.  Named: `H_advanceT`, `H_freshShift`. -/
theorem shiftRound_tick {w : List (Fin 2)} {delay : ℕ} {x y : State GalilVM}
    (hCR : ChainRound w x.ctl x.vm)
    (hSR : ShiftRound w x.ctl x.vm)
    (hT : H_advanceT w x.ctl x.vm)
    (hF : H_freshShift w x.vm y.vm)
    (hblk : GalilBranchInvariants.BlockInv x.vm.chain)
    (hci : CopyIdle x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay x y) :
    ShiftRound w y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  cases h with
  | init c s t hm hi => intro hm' _ _; exact absurd hm' (by simp)
  | scan_wait c s t hm hav hb => intro hm' _ _; exact absurd hm' (by simp [hm])
  | scan_count c s t hm hav hc hb => intro hm' _ _; exact absurd hm' (by simp [hm])
  | restart c s t hm hb => intro hm' _ _; exact absurd hm' (by simp [hm])
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho => intro hm' _ _; exact absurd hm' (by simp [hm])
  | scan_fallback c s s' t hm h hc hcmp hmt hg hr hb => intro hm' _ _; exact absurd hm' (by simp)
  | shift_done c s o hm hp ho => intro hm' _ _; exact absurd hm' (by simp)
  | copy_one c s t hm hp hs => intro hm' _ _; exact absurd hm' (by simp [hm])
  | copy_done c s t hm hp hs => intro hm' _ _; exact absurd hm' (by simp)
  | home_start c s t hm hl hs => intro hm' _ _; exact absurd hm' (by simp)
  | home_step c s t hm hl hs => intro hm' _ _; exact absurd hm' (by simp [hm])
  | fpp_slice c s t hm hs => intro hm' _ _; exact absurd hm' (by simp [hm])
  | fpp_done c s t hm hs => intro hm' _ _; exact absurd hm' (by simp)
  | markEnd_found c s t hm he hs => intro hm' _ _; exact absurd hm' (by simp)
  | markEnd_step c s t hm he hs => intro hm' _ _; exact absurd hm' (by simp [hm])
  | choose_select c s t hm ho hs h => intro hm' _ _; exact absurd hm' (by simp)
  | choose_step c s t hm hs h => intro hm' _ _; exact absurd hm' (by simp [hm])
  | rewind_done c s t hm hf h => intro hm' _ _; exact absurd hm' (by simp)
  | rewind_one c s t hm hf hp h => intro hm' _ _; exact absurd hm' (by simp [hm])
  | rewind_pair c s t hm hf hp h => intro hm' _ _; exact absurd hm' (by simp [hm])
  | replayStart c s t o hm hrs ho ho' => intro hm' _ _; exact absurd hm' (by simp)
  | scan_shift c s s' t hm h hc hcmp hmt hr hg hb =>
    intro _ wch hchain
    have hav : canRight s.right := by
      rcases h with h | h
      · rw [hr] at h; cases h
      · exact h
    have hcf : compareFound (PofC centre place entry w) q first s s' := hcmp
    obtain ⟨vs, vq, a, hvl, hvr, hiff, -, hch, hteq⟩ := hcf
    cases a with
    | true =>
      rw [if_pos rfl] at hteq
      subst hteq
      refine absurd ?_ hmt
      show GalilScaffoldInputHead.read (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).left
        = GalilScaffoldInputHead.read (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).right
      rw [afterBirth_left, afterBirth_right]
      exact hiff.1 rfl
    | false =>
      rw [if_neg (by simp)] at hteq
      have hg0 : shiftGuardVM (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)) := by
        rw [← hteq]; exact hg
      obtain ⟨w1', hw1', -, -, -, -, -⟩ := hg0
      have hne : s.chain ≠ ChainVM.idle := by
        intro hidle
        rw [hidle] at hch
        rw [afterBirth_chain] at hw1'
        exact chainAt_idle_not_watch hch w1' hw1'
      rw [afterBirth_of_ne_idle hne] at hteq
      subst hteq
      have hg' : shiftGuardVM (afterMismatch s vs vq) := hg
      obtain ⟨w1, hw1, -, hph, -, hif, hsym⟩ := hg'
      have hb' : beginShiftVM' (afterMismatch s vs vq) t := hb
      obtain ⟨w2, hw2, ht⟩ := hb'
      have hw1' : vs.chain = .watch w1 := hw1
      have hw21 : w2 = w1 := by
        have h2 : vs.chain = .watch w2 := hw2
        rw [hw1'] at h2
        cases h2
        rfl
      subst hw21
      have hwch : wch = GalilScaffoldChainWatch.immediate w2 := by
        rw [ht] at hchain
        cases hchain
        rfl
      subst hwch
      rcases chainAt_false_watch hch hw1' with ⟨w0, hw0, hint⟩ | hnot
      · cases hpo : s.periodOnly with
        | false => exact hF hpo _ hchain
        | true =>
          obtain ⟨C, R, used, hI⟩ := hCR hm hr hpo w0 hw0
          have hwe := internal_of_zero hI.caught.lagZero hint
          subst hwe
          have hend : singlePositive s.cycle = true := by
            have hif' : (if s.periodOnly then singlePositive s.cycle = true
                else negative w2.margin = false) := hif
            rw [hpo, if_pos rfl] at hif'
            exact hif'
          have hpred : GalilScaffoldChainConsume.symbol w2.machine.control.period.focus =
              read (right s.right) := by
            rw [← hvr]; exact hsym
          have hmis : read (GalilScaffoldInputHead.left s.left) ≠ read (right s.right) := by
            intro he
            have hm2 : (galilFrame (PofC centre place entry w) q first).matched
                (scanLens.set s vs) := by
              show read vs.left = read vs.right
              rw [hvl, hvr]; exact he
            exact absurd (hiff.2 hm2) (by decide)
          have hadv := hT hm hr hpo C R used w2 hI hend hav hpred
          have hblk' : GalilBranchInvariants.OnBlock w2.machine.control.period := by
            have hb0 : GalilBranchInvariants.BlockInv s.chain := hblk
            rw [hw0] at hb0
            exact hb0
          have hper : periodLength (GalilScaffoldChainWatch.immediate w2) = periodLength w2 :=
            periodLength_consume w2.machine w2.lag w2.margin w2.lag (inc w2.margin) hblk'
          refine ⟨C, R, 0, ?_⟩
          rw [hper]
          exact shiftInv_entry hI hend hav hmis hpred hadv
            (by rw [ht]; exact hvl) (by rw [ht]; exact hvr) (by rw [ht]) (by rw [ht]) (by rw [ht])
      · -- a chain born in this comparison has phase `0`, against the guard's `4`
        have h0 := chainAt_false_born hch hw1' hnot
        rw [hph] at h0
        exact absurd h0 (by decide)
  | shift_one c s t hm hp hs =>
    intro _ wch hchain
    have hs' : shiftLens.rel (shiftFrame (fun _ => True) (fun _ => True)).shiftOne s t := hs
    obtain ⟨⟨hcc, hl, hl', w, hw, heq⟩, hset⟩ := hs'
    have hw' : s.chain = .watch w := hw
    obtain ⟨C, R, k, hI⟩ := hSR hm w hw'
    have hleft : t.left = right (right s.left) := congrArg (fun v : ShiftVM => v.shift.left) heq
    have htchain : t.chain = .watch (chainShiftOne w) := congrArg (fun v : ShiftVM => v.chain) heq
    have hrem : t.remaining = dec s.remaining :=
      congrArg (fun v : ShiftVM => v.shift.remaining) heq
    have hcyc : t.cycle = inc (inc s.cycle) := congrArg (fun v : ShiftVM => v.cycle) heq
    have hright : t.right = s.right := by
      have := congrArg GalilVM.right hset
      exact this
    have hpos : positive s.remaining = true := by
      rcases hp with hp | hp
      · exact hp
      · exact absurd hp hci
    have hwch : wch = chainShiftOne w := by
      rw [htchain] at hchain
      cases hchain
      rfl
    subst hwch
    exact ⟨C, R, k + 1, shiftInv_step hI hpos hl hl' hleft hright htchain hrem hcyc⟩

end Tick

/-! ## 4. The `Reads` datum behind `H_advance` -/

/-- **The minimal `Reads`-trace datum**: the chain's control is the round
origin's shifted control swept over the `used` symbols read so far. -/
def ReadsInv (raw : List (Fin 2)) (C R h used : ℕ) (w0 : GalilScaffoldChainWatch.State) : Prop :=
  ∃ (o : ReadOrigin raw) (extra : List (Fin 3)),
    o.center = C ∧ o.radius = R ∧ o.interior.length + 1 = h ∧ extra.length = used ∧
    w0.machine.control = GalilScaffoldChainSweep.run o.shifted.machine.control extra

/-- **`H_advance` from `ReadsInv`**: `origin_prediction_index` at the
one-longer continuation. -/
theorem h_advance_of_readsInv {raw : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {w0 : GalilScaffoldChainWatch.State}
    (hI : RoundScan raw C R h used s w0) (hR : ReadsInv raw C R h used w0)
    (hg : GalilScaffoldChainWatch.Good w0) (hend : singlePositive s.cycle = false) :
    GalilScaffoldChainConsume.symbol
        (GalilScaffoldChainWatch.immediate w0).machine.control.period.focus =
      (encoded raw)[C + R + 2 + (used + 1) - 2 * h]? := by
  obtain ⟨o, extra, hC, hRR, hh, hlen, hctl⟩ := hR
  obtain ⟨-, a, ha, hra⟩ := hg
  have hne : used + 1 ≠ 2 * h := by
    intro heq
    rw [hI.terminal_iff.mpr heq] at hend
    cases hend
  have hlt : (extra ++ [a]).length < 2 * h := by
    simp only [List.length_append, List.length_singleton, hlen]
    have := hI.fresh
    omega
  have hrun : (GalilScaffoldChainWatch.immediate w0).machine.control =
      GalilScaffoldChainSweep.run o.shifted.machine.control (extra ++ [a]) := by
    show GalilScaffoldChainConsume.consume w0.machine.control (read (right w0.machine.verifier)) = _
    rw [GalilScaffoldChainSweep.run_append, ← hctl, hra]
    rfl
  have hunb : (GalilScaffoldChainSweep.run o.shifted.machine.control (extra ++ [a])).broken = false := by
    rw [← hrun]
    show (GalilScaffoldChainConsume.consume w0.machine.control (read (right w0.machine.verifier))).broken = false
    rw [hra]
    exact consume_keeps_unbroken _ a ha hI.caught.unbroken
  rw [hrun, origin_prediction_index o h hh (extra ++ [a]) hlt hunb]
  simp only [List.length_append, List.length_singleton, hlen, hC, hRR]
  congr 1
  have := hI.size
  omega

/-- `ReadsInv` steps with the immediate consume of a `Good` chain. -/
theorem readsInv_immediate {raw : List (Fin 2)} {C R h used : ℕ}
    {w0 : GalilScaffoldChainWatch.State}
    (hR : ReadsInv raw C R h used w0) (hg : GalilScaffoldChainWatch.Good w0) :
    ReadsInv raw C R h (used + 1) (GalilScaffoldChainWatch.immediate w0) := by
  obtain ⟨o, extra, hC, hRR, hh, hlen, hctl⟩ := hR
  obtain ⟨-, a, -, hra⟩ := hg
  refine ⟨o, extra ++ [a], hC, hRR, hh, by simp [hlen], ?_⟩
  show GalilScaffoldChainConsume.consume w0.machine.control (read (right w0.machine.verifier)) = _
  rw [GalilScaffoldChainSweep.run_append, ← hctl, hra]
  rfl

#print axioms roundScan_of_shiftInv
#print axioms h_shiftDone_of_shiftRound
#print axioms shiftInv_entry
#print axioms shiftInv_step
#print axioms shiftRound_tick
#print axioms h_advance_of_readsInv
#print axioms readsInv_immediate

end PalPeg.CloseoutPackRun37
