import PalPeg.GalilReplayGeneral2
import PalPeg.GalilCandidatePeriod
import PalPeg.GalilPeriodUnion
import PalPeg.GalilLaterRadius

/-!
# `ReplaySpan` is false; the replay with chain breaks and restarts

`GalilReplayGeneral2.ReplaySpan` claims that a period block found during a replay
spans the whole replay (`SpanWindow … (C+1) (R+m)`).  **It is false.**  The DP
candidate `h` only gives period `2h` on `[C-4h, C]` (`candidate_periodOn`), which
the landing palindrome mirrors to `[C, C+4h]` (`periodOn_mirror_right`), not
further.  `cx_fallback`/`cx_candidate`/`cx_span`: on `aaaaabaaaab` the fallback
from centre `11` lands on centre `16` with replay end `21`; `h = 1` is a candidate
and `2` is not a period of `[17, 21]`.  (The Python reference machine
`scaffold_galil.py` breaks the chain inside replays and restarts the search with
`replaying = true`, e.g. on `aabbbbabbbbab`.)

The fix:
* `BlockOn … E` — the block window truncated at the first mispredicted place
  (`maximal_window`); `blockOn_of_candidate`/`mispredicted_beyond_candidate` —
  it always reaches `min (C+4h) (C+R)`.
* `ChainW` — the replay chain invariant with the truncated window, the margin
  identity and a cost budget; `chainW_break` — at the window end the credit is
  `ChainMatched.breaks` and the broken state passes `restartVM`'s checks.
* `ReplayChainSeg2` — `ReplayChainSeg` plus `breakC` and `restartC`.
* `ReplayBudget` (replaces `ReplaySpan`) and `RestartShape`
  (`restartShape_sharedC`).
* `replay_after_fallback_general''` — branches (i) quiet, (ii) `ChainEnd`,
  (iii) broke, restarted, and continued as an idle replay.
-/

set_option autoImplicit false
namespace PalPeg.GalilReplaySpan
open PalPeg PalPeg.GalilScaffoldChainInputSupply Manacher GalilScaffoldInputHead

/-- The left-to-right mirror. -/
theorem periodOn_mirror_right {α : Type} {x : List α} {C k p : ℕ} (hpal : PalAt x C k)
    (h : PeriodOn x p (C - k) C) : PeriodOn x p C (C + k) := by
  intro i hi hip
  have hk := hpal.1
  have hm1 : x[i]? = x[2 * C - i]? := Manacher.mirror_getElem? hpal (by omega) (by omega)
  have hm2 : x[i + p]? = x[2 * C - (i + p)]? :=
    Manacher.mirror_getElem? hpal (by omega) (by omega)
  have hstep : x[2 * C - (i + p)]? = x[2 * C - (i + p) + p]? := h _ (by omega) (by omega)
  rw [show 2 * C - (i + p) + p = 2 * C - i from by omega] at hstep
  rw [hm1, hm2]
  exact hstep.symm

def raw0 : List (Fin 2) := [0,0,0,0,0,1,0,0,0,0,1]

theorem leftmost_of_dec {raw : List (Fin 2)} {n C : ℕ} (hl : Live raw n C)
    (hno : ∀ c : Fin C, ¬ Live raw n c) : Leftmost raw n C := by
  refine ⟨hl, fun c hc => ?_⟩
  by_contra hlt
  exact hno ⟨c, by omega⟩ hc

/-- The old centre `11` (the letter `1` of `aaaaa b aaaa`) is the leftmost
live centre at place `20` and dies at place `21`; the fallback lands on
centre `16` (`b aaaa | aaaa b`), leftmost live at `21`. -/
theorem cx_fallback :
    Leftmost raw0 20 11 ∧ ¬ Live raw0 21 11 ∧ Leftmost raw0 21 16 := by
  refine ⟨leftmost_of_dec ?_ ?_, ?_, leftmost_of_dec ?_ ?_⟩ <;> unfold Live raw0 <;> decide

/-- The left stream of the landing centre `16`. -/
def place0 : GalilScaffoldPlace.Place := ⟨[0,0,1,0,0,0,0,0], true⟩

theorem cx_word : ([0,0,1,0,0,0,0,0] : List (Fin 2)).reverse ++ [0,0,1] ++ [] = raw0 := by decide

theorem cx_position :
    position (represent place0 (([0,0,1] : List (Fin 2)).map some) []) = 16 := by
  unfold place0; rw [position_represent]; decide

/-- `h = 1` is a DP candidate (the least one: `lower = 0`) on the window left of
the landing centre, for every window length `span + 1 ≥ 5` inside the stream. -/
theorem cx_candidate : GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream place0).take 16) 0 1 := by
  unfold GalilDpCorrect.Candidate place0; decide

/-- **`ReplaySpan`'s conclusion fails on this input.**  The candidate period `2`
holds on `[12, 16]` (left of the centre) and, mirrored, on `[16, 20]`, but not
on the replay span `[17, 21]`: place `21` is the letter `1` where the period
predicts `0`.  So no block `xs ++ [b]` of length `h = 1` spans the replay. -/
theorem cx_span :
    PeriodOn (encoded raw0) 2 12 16 ∧ PeriodOn (encoded raw0) 2 16 20 ∧
      ¬ PeriodOn (encoded raw0) 2 17 21 ∧
      ∀ c b : Fin 3, ¬ GalilWatchOkInst.SpanWindow raw0 c b [] 17 21 := by
  have hp : ¬ PeriodOn (encoded raw0) 2 17 21 := by
    intro h
    have := h 19 (by omega) (by omega)
    revert this; unfold raw0; decide
  refine ⟨?_, ?_, hp, fun c b hw => hp (by simpa using hw.1)⟩
  · intro i hi hip
    have : i ∈ [12,13,14] := by simp; omega
    simp at this; rcases this with rfl | rfl | rfl <;> (unfold raw0; decide)
  · intro i hi hip
    have : i ∈ [16,17,18] := by simp; omega
    simp at this; rcases this with rfl | rfl | rfl <;> (unfold raw0; decide)

#print axioms periodOn_mirror_right
#print axioms cx_fallback
#print axioms cx_position
#print axioms cx_candidate
#print axioms cx_span

/-! ## 2. The block window truncated at the replay's first mispredicted place -/

section Window

open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

abbrev WState := GalilScaffoldChainWatch.State

/-- The input from `anchor` up to `E` (inclusive) reads the block `bounce`
cyclically.  Unlike `SpanWindow` nothing is claimed past `E`. -/
def BlockOn (raw : List (Fin 2)) (center b : Fin 3) (xs : List (Fin 3)) (anchor E : ℕ) : Prop :=
  ∀ j, anchor + j ≤ E →
    (encoded raw)[anchor + j]? = (GalilScaffoldChainSweep.bounce center b xs)[j % (2 * (xs.length + 1))]?

/-- The place `E+1` is mispredicted by the block. -/
def Mispredicted (raw : List (Fin 2)) (center b : Fin 3) (xs : List (Fin 3)) (anchor j : ℕ) : Prop :=
  (encoded raw)[j]? ≠ (GalilScaffoldChainSweep.bounce center b xs)[(j - anchor) % (2 * (xs.length + 1))]?

/-- **The maximal window.**  Below any bound `B ≥ anchor - 1` there is a largest
`E` with the block agreeing on `[anchor, E]`; if `E < B` the next place is
mispredicted. -/
theorem maximal_window (raw : List (Fin 2)) (center b : Fin 3) (xs : List (Fin 3)) (anchor : ℕ)
    (ha : 1 ≤ anchor) :
    ∀ d B, anchor + d = B + 1 →
      ∃ E, anchor ≤ E + 1 ∧ E ≤ B ∧ BlockOn raw center b xs anchor E ∧
        (E < B → Mispredicted raw center b xs anchor (E + 1)) := by
  intro d
  induction d with
  | zero =>
    intro B hB
    refine ⟨B, by omega, le_rfl, fun j hj => by omega, fun h => by omega⟩
  | succ d ih =>
    intro B hB
    obtain ⟨E, h1, h2, h3, h4⟩ := ih (B - 1) (by omega)
    by_cases hlt : E < B - 1
    · exact ⟨E, h1, by omega, h3, fun _ => h4 hlt⟩
    · have hE : E = B - 1 := by omega
      by_cases hm : Mispredicted raw center b xs anchor B
      · exact ⟨E, h1, by omega, h3, fun _ => by rw [hE, show B - 1 + 1 = B from by omega]; exact hm⟩
      · refine ⟨B, by omega, le_rfl, fun j hj => ?_, fun h => absurd h (lt_irrefl B)⟩
        by_cases hjB : anchor + j ≤ E
        · exact h3 j hjB
        · have hj' : anchor + j = B := by omega
          unfold Mispredicted at hm
          rw [hj', show j = B - anchor from by omega]
          exact not_not.mp hm

/-- The watch machine along a replay: the control is literally the sweep from
`ready` over the consumed places (no chain shift happens in a replay). -/
def CoreX (raw : List (Fin 2)) (center b : Fin 3) (xs : List (Fin 3)) (anchor : ℕ)
    (m : GalilScaffoldChainVerifier.State) : Prop :=
  GalilBranchInvariants.OnBlock m.control.period ∧
    GalilScaffoldInputTrace.Represents m.verifier.head raw ∧ m.verifier.head.focus ≠ none ∧
    ∃ pre : List (Fin 3),
      m.control = GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready center xs b) pre ∧
      (GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready center xs b) pre).broken = false ∧
      position m.verifier + 1 = anchor + pre.length

/-- The prediction and the read at the next place. -/
theorem coreX_next {raw : List (Fin 2)} {center b : Fin 3} {xs : List (Fin 3)} {anchor : ℕ}
    {m : GalilScaffoldChainVerifier.State} (hc : CoreX raw center b xs anchor m)
    (hB : position m.verifier + 1 < (encoded raw).length) :
    canRight m.verifier ∧
    GalilScaffoldChainConsume.symbol m.control.period.focus =
      (GalilScaffoldChainSweep.bounce center b xs)[(position m.verifier + 1 - anchor) %
        (2 * (xs.length + 1))]? ∧
    read (right m.verifier) = (encoded raw)[position m.verifier + 1]? ∧
    read (right m.verifier) ≠ none := by
  obtain ⟨-, hrep, hpres, pre, hctl, hbr0, hidx⟩ := hc
  have hcan : canRight m.verifier := canRight_of_bound _ raw hrep hpres hB
  have hpred := GalilScaffoldChainPrediction.continued_prediction center b xs pre []
    m.control (by rw [hctl]; exact ⟨rfl, rfl⟩) (by rw [hctl]) (by simpa [GalilScaffoldChainSweep.run, hctl] using hbr0)
  simp only [List.length_nil, Nat.add_zero, GalilScaffoldChainSweep.run] at hpred
  have hleft := (represented_position _ raw hrep hpres).1
  have hnext : position (right m.verifier) = position m.verifier + 1 := right_position _ hcan hleft
  have hread : read (right m.verifier) = (encoded raw)[position m.verifier + 1]? := by
    rw [represented_read _ raw (right_word _ raw hrep hcan) (right_present _ raw hrep hpres hcan),
      hnext]
  have hne : read (right m.verifier) ≠ none := by
    have hf := right_present _ raw hrep hpres hcan
    rcases hz : (right m.verifier).head.focus with _ | z
    · exact absurd hz hf
    · simp [GalilScaffoldInputHead.read, hz]
  refine ⟨hcan, ?_, hread, hne⟩
  rw [hpred, show position m.verifier + 1 - anchor = pre.length from by omega]

/-- `Good` inside the window. -/
theorem coreX_good {raw : List (Fin 2)} {center b : Fin 3} {xs : List (Fin 3)} {anchor E : ℕ}
    {w : WState} (hc : CoreX raw center b xs anchor w.machine)
    (hwin : BlockOn raw center b xs anchor E) (hE : E < (encoded raw).length)
    (hpos : position w.machine.verifier + 1 ≤ E) :
    GalilScaffoldChainWatch.Good w := by
  have hidx := hc.2.2.2
  obtain ⟨pre, -, -, hp⟩ := hidx
  obtain ⟨hcan, hsym, hread, hne⟩ := coreX_next hc (by omega)
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
  refine ⟨hcan, a, ?_, ha⟩
  have hw := hwin (position w.machine.verifier + 1 - anchor) (by omega)
  rw [show anchor + (position w.machine.verifier + 1 - anchor) = position w.machine.verifier + 1
    from by omega] at hw
  rw [hsym, ← hw, ← hread, ha]

/-- **The break at the first mispredicted place.** -/
theorem coreX_break {raw : List (Fin 2)} {center b : Fin 3} {xs : List (Fin 3)} {anchor : ℕ}
    {w : WState} (hc : CoreX raw center b xs anchor w.machine)
    (hB : position w.machine.verifier + 1 < (encoded raw).length)
    (hmis : Mispredicted raw center b xs anchor (position w.machine.verifier + 1))
    (hz : zero w.lag = true) :
    BreakStep w ⟨consume w.machine, w.lag, inc w.margin⟩ := by
  obtain ⟨hcan, hsym, hread, hne⟩ := coreX_next hc hB
  refine ⟨hz, hcan, ?_⟩
  unfold Mispredicted at hmis
  rcases hq : (GalilScaffoldChainSweep.bounce center b xs)[(position w.machine.verifier + 1 - anchor) %
      (2 * (xs.length + 1))]? with _ | a
  · exfalso
    have hlt : (position w.machine.verifier + 1 - anchor) % (2 * (xs.length + 1)) <
        (GalilScaffoldChainSweep.bounce center b xs).length := by
      have hbl : (GalilScaffoldChainSweep.bounce center b xs).length = 2 * (xs.length + 1) := by
        simp [GalilScaffoldChainSweep.bounce]; omega
      rw [hbl]; exact Nat.mod_lt _ (by omega)
    rw [List.getElem?_eq_getElem hlt] at hq
    exact Option.some_ne_none _ hq
  · refine ⟨a, by rw [hsym, hq], ?_, rfl⟩
    rw [hread]; rw [hq] at hmis; exact hmis

/-- An agreeing consume keeps `CoreX`. -/
theorem coreX_consume {raw : List (Fin 2)} {center b : Fin 3} {xs : List (Fin 3)} {anchor : ℕ}
    {w : WState} (hc : CoreX raw center b xs anchor w.machine) (hg : GalilScaffoldChainWatch.Good w) :
    CoreX raw center b xs anchor (consume w.machine) := by
  obtain ⟨hblk, hrep, hpres, pre, hctl, hbr0, hidx⟩ := hc
  obtain ⟨hcan, a, hsym, hread⟩ := hg
  have hleft := (represented_position _ raw hrep hpres).1
  have hctl' : (consume w.machine).control =
      GalilScaffoldChainConsume.consume w.machine.control (some a) := by
    show GalilScaffoldChainConsume.consume w.machine.control (read (right w.machine.verifier)) = _
    rw [hread]
  refine ⟨GalilBranchInvariants.onBlock_verifier_consume _ hblk, right_word _ raw hrep hcan,
    right_present _ raw hrep hpres hcan, pre ++ [a], ?_, ?_, ?_⟩
  · rw [hctl', hctl, GalilScaffoldChainSweep.run_append]; rfl
  · rw [GalilScaffoldChainSweep.run_append]
    show (GalilScaffoldChainConsume.consume _ (some a)).broken = false
    rw [← hctl]
    exact consume_keeps_unbroken _ a hsym (by rw [hctl]; exact hbr0)
  · show position (right w.machine.verifier) + 1 = _
    rw [right_position _ hcan hleft, List.length_append, List.length_singleton]
    omega

/-- The watch state `backDone` creates is in `CoreX`. -/
theorem coreX_born {raw : List (Fin 2)} (center b : Fin 3) (xs : List (Fin 3)) {anchor : ℕ}
    (ver : PlaceHead) (hrep : GalilScaffoldInputTrace.Represents ver.head raw)
    (hpres : ver.head.focus ≠ none) (hpos : position ver + 1 = anchor) :
    CoreX raw center b xs anchor
      ⟨ver, watchControl
        ⟨[], .first center, xs.map GalilScaffoldChainPeriod.Token.plain ++
          [GalilScaffoldChainPeriod.Token.last b]⟩⟩ := by
  refine ⟨?_, hrep, hpres, [], rfl, rfl, by simpa using hpos⟩
  exact GalilBranchInvariants.onBlock_moveRight ⟨center, b, xs, rfl⟩ rfl

/-- After one full bounce the sweep's `last` is positive and canonical. -/
theorem coreX_last {raw : List (Fin 2)} {center b : Fin 3} {xs : List (Fin 3)} {anchor : ℕ}
    {m : GalilScaffoldChainVerifier.State} (hc : CoreX raw center b xs anchor m)
    (hlen : anchor + 2 * (xs.length + 1) ≤ position m.verifier + 1) :
    positive m.control.last = true ∧ Canonical m.control.last ∧ 0 ≤ value m.control.last := by
  obtain ⟨-, -, -, pre, hctl, hbr, hidx⟩ := hc
  have hb0 := (GalilScaffoldChainSweep.first_round_trip center b xs).2.2.2.2.2.2
  have hbl : (GalilScaffoldChainSweep.bounce center b xs).length = 2 * (xs.length + 1) := by
    simp [GalilScaffoldChainSweep.bounce]; omega
  have htake := GalilScaffoldChainPrediction.successful_prefix
    (GalilScaffoldChainSweep.bounce center b xs) pre (GalilScaffoldChainConsume.ready center xs b)
    hb0 hbr (by rw [hbl]; omega)
  have hsplit : pre = GalilScaffoldChainSweep.bounce center b xs ++
      pre.drop (GalilScaffoldChainSweep.bounce center b xs).length := by
    conv_lhs => rw [← List.take_append_drop (GalilScaffoldChainSweep.bounce center b xs).length pre]
    rw [htake]
  have hpos := GalilScaffoldChainRestart.last_positive_after_bounce center b xs
    (pre.drop (GalilScaffoldChainSweep.bounce center b xs).length)
  rw [← hsplit, ← hctl] at hpos
  have hcan := (GalilScaffoldChainRestart.run_canonical (GalilScaffoldChainConsume.ready center xs b)
    pre (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)).1
  rw [← hctl] at hcan
  have hv := (positive_iff _ hcan).mp hpos
  exact ⟨hpos, hcan, by omega⟩

end Window

/-! ## 3. The chain invariant with a truncated window, a budget and the margin -/

section ChainW

open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilReplayGeneral2 PalPeg.GalilBranchInvariants PalPeg.GalilTickFun

/-- **The chain invariant of a replay with a possible break.**  `C` the centre,
`E` the window end, `R` the right head, `(cc, b, xs)` the block.  Besides the
data of `GalilReplayGeneral2.ChainPart` (with `BlockOn … E` for `SpanWindow … B`)
it records the margin identity `margin + 4·(copied letters) = R - C` and, when
`lim`, the *cost* — the background ticks the chain still needs to be watching
with lag `0` — bounded by `bud`. -/
def ChainW (raw : List (Fin 2)) (C E R bud : ℕ) (lim : Bool) (cc b : Fin 3) (xs : List (Fin 3)) :
    ChainVM → Prop
  | .idle => False
  | .copy t h p v lag margin ver => VerAt raw C ver ∧ LagAt lag ver R ∧
      BlockOn raw cc b xs (C+1) E ∧ Canonical margin ∧
      ∃ n u d q, GalilScaffoldChainPeriod.Copy t h p v n u d q
          (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cc) (xs ++ [b])) ∧
        u.focus = 4 ∧ positive d = true ∧ n ≤ xs.length + 1 ∧
        value margin + 4 * ((xs.length + 1 - n : ℕ) : ℤ) = (R : ℤ) - C ∧
        (lim = true → n + xs.length + 3 + lag.pos.length ≤ bud)
  | .back v _ lag margin ver => VerAt raw C ver ∧ LagAt lag ver R ∧
      BlockOn raw cc b xs (C+1) E ∧ flat v = blockTokens cc b xs ∧ Canonical margin ∧
      value margin + 4 * ((xs.length + 1 : ℕ) : ℤ) = (R : ℤ) - C ∧
      (lim = true → v.left.length + 1 + lag.pos.length ≤ bud)
  | .watch w => LagAt w.lag w.machine.verifier R ∧ BlockOn raw cc b xs (C+1) E ∧
      CoreX raw cc b xs (C+1) w.machine ∧ Canonical w.margin ∧
      value w.margin + 4 * ((xs.length + 1 : ℕ) : ℤ) = (R : ℤ) - C ∧
      (lim = true → w.lag.pos.length ≤ bud)
  | .broken _ => False

variable {raw : List (Fin 2)} {C E : ℕ} {lim : Bool} {cc b : Fin 3} {xs : List (Fin 3)}

theorem chainW_ne_idle {R bud : ℕ} {x : ChainVM} (h : ChainW raw C E R bud lim cc b xs x) :
    x ≠ .idle := by
  intro e; rw [e] at h; exact h

theorem chainW_mono {R bud bud' : ℕ} {x : ChainVM} (h : ChainW raw C E R bud lim cc b xs x)
    (hle : bud ≤ bud') : ChainW raw C E R bud' lim cc b xs x := by
  cases x with
  | idle => exact h.elim
  | broken w => exact h.elim
  | copy t hh p v lag margin ver =>
    obtain ⟨h1, h2, h3, h4, n, u, d, q, h5, h6, h7, h8, h9, h10⟩ := h
    exact ⟨h1, h2, h3, h4, n, u, d, q, h5, h6, h7, h8, h9, fun hl => le_trans (h10 hl) hle⟩
  | back v hh lag margin ver =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, fun hl => le_trans (h7 hl) hle⟩
  | watch w =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, h2, h3, h4, h5, fun hl => le_trans (h6 hl) hle⟩

theorem fill_start_left (ys : List (Fin 3)) :
    (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cc) ys).left.length = ys.length := by
  obtain ⟨h1, h2⟩ := fill_right_flat ys (GalilScaffoldChainPeriod.start cc) rfl
  generalize GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cc) ys = z at h1 h2
  rcases z with ⟨ls, f, rs⟩
  simp only at h1
  subst h1
  have := congrArg List.length h2
  simp [flat, GalilScaffoldChainPeriod.start] at this
  simpa using this

/-- One background chain step in the invariant: the cost drops by one (or
stays at `0`). -/
theorem chainW_step {R bud : ℕ} {x : ChainVM} (hx : ChainW raw C E R (bud+1) lim cc b xs x)
    (hB : E < (encoded raw).length) (hR : R ≤ E) :
    ∃ y, ChainStep x y ∧ ChainW raw C E R bud lim cc b xs y := by
  cases x with
  | idle => exact hx.elim
  | broken w => exact hx.elim
  | copy t hh p v lag margin ver =>
    obtain ⟨hver, hlag, hwin, hcan, n, u, d, q, hcopy, hu, hd, hn, hmar, hbud⟩ := hx
    rcases copy_cases hcopy with ⟨rfl, rfl, rfl, rfl⟩ | ⟨n', a, rfl, one, legal, present, rest⟩
    · have hf := fill_last_focus (GalilScaffoldChainPeriod.start cc) xs b
      refine ⟨_, .copyEnd _ _ _ _ _ _ _ b hu hd hf, hver, hlag, hwin, flat_block cc b xs, hcan,
        by simpa using hmar, fun hl => ?_⟩
      have h1 := hbud hl
      have h2 : (GalilScaffoldChainPeriod.write
          (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cc) (xs ++ [b]))
          (.last b)).left.length = xs.length + 1 := by
        show (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cc) (xs ++ [b])).left.length = _
        rw [fill_start_left]; simp
      rw [h2]; omega
    · refine ⟨_, .copyBit _ _ _ _ _ _ _ a one legal present, hver, hlag, hwin, ?_, n', u, d, q, rest,
        hu, hd, by omega, ?_, fun hl => by have := hbud hl; omega⟩
      · exact dec_canonical _ (dec_canonical _ (dec_canonical _ (dec_canonical _ hcan)))
      · simp only [GalilScaffoldChainCredits.decFour, dec_value]
        have e : ((xs.length + 1 - n' : ℕ) : ℤ) = ((xs.length + 1 - (n' + 1) : ℕ) : ℤ) + 1 := by
          omega
        rw [e]; linarith
  | back v hh lag margin ver =>
    obtain ⟨hver, hlag, hwin, hflat, hcan, hmar, hbud⟩ := hx
    cases hf : GalilScaffoldChainPeriod.isFirst v.focus with
    | false =>
      refine ⟨_, .backStep _ _ _ _ _ hf, hver, hlag, hwin, by rw [flat_moveLeft]; exact hflat, hcan,
        hmar, fun hl => ?_⟩
      have h1 := hbud hl
      rcases v with ⟨ls, f, rs⟩
      cases ls with
      | nil =>
        exfalso
        simp only [flat, blockTokens, List.reverse_nil, List.nil_append, List.cons.injEq] at hflat
        rw [hflat.1] at hf; simp [GalilScaffoldChainPeriod.isFirst] at hf
      | cons a ls =>
        simp only [GalilScaffoldChainPeriod.moveLeft, List.length_cons] at h1 ⊢; omega
    | true =>
      have hv := rewound_of_flat hflat hf
      refine ⟨_, .backDone _ _ _ _ _ hf, hlag, hwin, ?_, hcan, hmar, fun hl => by
        have := hbud hl; show lag.pos.length ≤ bud; omega⟩
      show CoreX raw cc b xs (C+1) ⟨ver, watchControl v⟩
      rw [hv]
      exact coreX_born cc b xs ver hver.1 hver.2.1 (by rw [hver.2.2])
  | watch w =>
    obtain ⟨hlag, hwin, hc, hcan, hmar, hbud⟩ := hx
    obtain ⟨hneg, hpos⟩ := hlag
    rcases w with ⟨mach, ⟨ps, ns⟩, margin⟩
    simp only at hneg hpos hc hbud hcan hmar
    subst hneg
    cases ps with
    | nil =>
      exact ⟨_, .watchStep _ _ (.idle _ rfl), ⟨rfl, hpos⟩, hwin, hc, hcan, hmar,
        fun hl => by simp⟩
    | cons u ps =>
      have hp : positive (⟨u :: ps, []⟩ : Counter) = true := rfl
      have hg := coreX_good (w := ⟨mach, ⟨u :: ps, []⟩, margin⟩) hc hwin hB
        (by show position mach.verifier + 1 ≤ E; simp at hpos; omega)
      refine ⟨_, .watchStep _ _ (.take _ hp hg), ⟨rfl, ?_⟩, hwin, coreX_consume hc hg, hcan, hmar,
        fun hl => by have := hbud hl; simp [GalilScaffoldChainWatch.caught, dec] at this ⊢; omega⟩
      show position (consume mach).verifier + (dec ⟨u :: ps, []⟩).pos.length = R
      have hpc : position (consume mach).verifier = position mach.verifier + 1 :=
        right_position _ hg.1 (represented_position _ raw hc.2.1 hc.2.2.1).1
      rw [hpc]
      simp [dec] at hpos ⊢; omega

end ChainW

section ChainW2

open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilReplayGeneral2 PalPeg.GalilBranchInvariants PalPeg.GalilTickFun

variable {raw : List (Fin 2)} {C E : ℕ} {lim : Bool} {cc b : Fin 3} {xs : List (Fin 3)}

theorem canonical_inc_value {c : Counter} (hc : Canonical c) :
    Canonical (inc c) ∧ value (inc c) = value c + 1 :=
  ⟨inc_canonical c hc, inc_value c⟩

/-- The match credit inside the window (`R + 1 ≤ E`): the cost grows by at most one. -/
theorem chainW_matched {R bud : ℕ} {y : ChainVM} (hy : ChainW raw C E R bud lim cc b xs y)
    (hB : E < (encoded raw).length) (hR : R + 1 ≤ E) :
    ∃ z, ChainMatched y z ∧ ChainW raw C E (R+1) (bud+1) lim cc b xs z := by
  cases y with
  | idle => exact hy.elim
  | broken w => exact hy.elim
  | copy t h p v lag margin ver =>
    obtain ⟨hver, hlag, hwin, hcan, n, u, d, q, hcopy, hu, hd, hn, hmar, hbud⟩ := hy
    refine ⟨_, .copy _ _ _ _ _ _ _, hver, lagAt_inc hlag, hwin, inc_canonical _ hcan,
      n, u, d, q, hcopy, hu, hd, hn, ?_, fun hl => ?_⟩
    · rw [inc_value]; push_cast; linarith
    · have := hbud hl
      obtain ⟨hneg, -⟩ := hlag
      rcases lag with ⟨ps, ns⟩
      simp only at hneg; subst hneg
      simp [inc] at this ⊢; omega
  | back v h lag margin ver =>
    obtain ⟨hver, hlag, hwin, hflat, hcan, hmar, hbud⟩ := hy
    refine ⟨_, .back _ _ _ _ _, hver, lagAt_inc hlag, hwin, hflat, inc_canonical _ hcan, ?_,
      fun hl => ?_⟩
    · rw [inc_value]; push_cast at hmar ⊢; linarith
    · have := hbud hl
      obtain ⟨hneg, -⟩ := hlag
      rcases lag with ⟨ps, ns⟩
      simp only at hneg; subst hneg
      simp [inc] at this ⊢; omega
  | watch w =>
    obtain ⟨hlag, hwin, hc, hcan, hmar, hbud⟩ := hy
    obtain ⟨hneg, hpos⟩ := hlag
    rcases w with ⟨mach, ⟨ps, ns⟩, margin⟩
    simp only at hneg hpos hc hbud hcan hmar
    subst hneg
    cases ps with
    | nil =>
      have hz : zero (⟨[], []⟩ : Counter) = true := rfl
      have hg := coreX_good (w := ⟨mach, ⟨[], []⟩, margin⟩) hc hwin hB
        (by show position mach.verifier + 1 ≤ E; simp at hpos; omega)
      refine ⟨_, .watch _ _ (.immediate _ hz hg), ⟨rfl, ?_⟩, hwin, coreX_consume hc hg,
        inc_canonical _ hcan, ?_, fun _ => by simp [GalilScaffoldChainWatch.immediate]⟩
      · show position (consume mach).verifier + ([] : List Unit).length = R + 1
        have hpc : position (consume mach).verifier = position mach.verifier + 1 :=
          right_position _ hg.1 (represented_position _ raw hc.2.1 hc.2.2.1).1
        rw [hpc]; simp at hpos ⊢; omega
      · show value (inc margin) + _ = _
        rw [inc_value]; push_cast at hmar ⊢; linarith
    | cons u ps =>
      have hz : zero (⟨u :: ps, []⟩ : Counter) = false := rfl
      refine ⟨_, .watch _ _ (.queued _ hz), ⟨rfl, ?_⟩, hwin, hc, inc_canonical _ hcan, ?_,
        fun hl => ?_⟩
      · show position mach.verifier + (inc ⟨u :: ps, []⟩).pos.length = R + 1
        simp [inc] at hpos ⊢; omega
      · show value (inc margin) + _ = _
        rw [inc_value]; push_cast at hmar ⊢; linarith
      · have := hbud hl
        show (inc ⟨u :: ps, []⟩).pos.length ≤ bud + 1
        simp [inc] at this ⊢; omega

/-- The facts `restartVM` checks, on a broken watch state. -/
structure Restartable (w : WState) : Prop where
  lag : zero w.lag = true
  margin : negative w.margin = false
  last : positive w.machine.control.last = true
  lastCanonical : Canonical w.machine.control.last
  lastNonneg : 0 ≤ value w.machine.control.last

/-- **The break at the window's end.**  With no cost left the chain is watching
with lag `0`; the next place `R + 1` is mispredicted, so the match credit is
`ChainMatched.breaks`.  Past four semiperiods (`C + 4h ≤ R + 1`) the broken
state satisfies `restartVM`'s checks. -/
theorem chainW_break {R : ℕ} {y : ChainVM} (hy : ChainW raw C E R 0 true cc b xs y)
    (hB : R + 1 < (encoded raw).length)
    (hmis : Mispredicted raw cc b xs (C+1) (R+1)) (h4 : C + 4 * (xs.length + 1) ≤ R + 1) :
    ∃ w', ChainMatched y (.broken w') ∧ Restartable w' := by
  cases y with
  | idle => exact hy.elim
  | broken w => exact hy.elim
  | copy t h p v lag margin ver =>
    obtain ⟨-, -, -, -, n, u, d, q, -, -, -, -, -, hbud⟩ := hy
    have := hbud rfl; omega
  | back v h lag margin ver =>
    obtain ⟨-, -, -, -, -, -, hbud⟩ := hy
    have := hbud rfl; omega
  | watch w =>
    obtain ⟨hlag, hwin, hc, hcan, hmar, hbud⟩ := hy
    obtain ⟨hneg, hpos⟩ := hlag
    have hl0 : w.lag.pos.length = 0 := by have := hbud rfl; omega
    have hz : zero w.lag = true := by
      rcases w with ⟨mach, ⟨ps, ns⟩, margin⟩
      simp only at hneg hl0 ⊢
      subst hneg
      rw [List.length_eq_zero_iff] at hl0; subst hl0; rfl
    have hvpos : position w.machine.verifier = R := by omega
    have hbr := coreX_break hc (by omega) (by rw [hvpos]; exact hmis) hz
    have hctl : (consume w.machine).control.last = w.machine.control.last := by
      obtain ⟨-, -, a, hsym, hread, -⟩ := hbr
      show (GalilScaffoldChainConsume.consume w.machine.control (read (right w.machine.verifier))).last = _
      rw [GalilScaffoldChainConsume.mismatch _ a _ hsym hread]
    obtain ⟨hL1, hL2, hL3⟩ := coreX_last hc (by rw [hvpos]; omega)
    refine ⟨_, .breaks _ _ hbr, ⟨hz, ?_, ?_, ?_, ?_⟩⟩
    · show negative (inc w.margin) = false
      have hc' := inc_canonical _ hcan
      cases hn : negative (inc w.margin) with
      | false => rfl
      | true =>
        have := (negative_iff _ hc').mp hn
        rw [inc_value] at this; push_cast at hmar; omega
    · show positive (consume w.machine).control.last = true
      rw [hctl]; exact hL1
    · show Canonical (consume w.machine).control.last
      rw [hctl]; exact hL2
    · show 0 ≤ value (consume w.machine).control.last
      rw [hctl]; exact hL3

end ChainW2

section ChainW3

open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilReplayGeneral2 PalPeg.GalilBranchInvariants PalPeg.GalilTickFun

variable {raw : List (Fin 2)} {C E : ℕ} {lim : Bool} {cc b : Fin 3} {xs : List (Fin 3)}

/-- **The started chain is in the invariant**, with cost `2n + 2 + k`
(`n` copies, the copy end, `n` back moves, the back end, the lag `k`). -/
theorem chainW_start {R bud k n : ℕ} {answer : GalilScaffoldTape.Tape}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter}
    (hver : VerAt raw C ver) (hrad : RadiusRep radius k) (hR : C + k = R)
    (ha : AnswerAhead answer n) (hp : PlaceAhead walker n)
    (hsplit : (GalilScaffoldPlace.stream walker).tail.take n = xs ++ [b])
    (hwin : BlockOn raw cc b xs (C+1) E) (hbud : lim = true → 2 * n + 2 + k ≤ bud) :
    ChainW raw C E R bud lim cc b xs (chainStart answer cc walker ver radius) := by
  have hlag := lagAt_radius hrad ver
  obtain ⟨u, q, hcopy, hu⟩ := copy_of_ahead n answer 0 walker (GalilScaffoldChainPeriod.start cc) ha hp
  rw [hsplit] at hcopy
  have hlen : n = xs.length + 1 := by
    have := congrArg List.length hsplit
    rw [List.length_take, List.length_tail] at this
    unfold PlaceAhead at hp
    simp at this; omega
  refine ⟨hver, by rw [hver.2.2, hR] at hlag; exact hlag, hwin, hrad.1, n, u, ofNat (0+n), q, hcopy, hu,
    ?_, by omega, ?_, fun hl => ?_⟩
  · obtain ⟨n', rfl⟩ : ∃ n', n = n'+1 := ⟨n-1, by omega⟩
    rfl
  · rw [hrad.2, show xs.length + 1 - n = 0 from by omega]; push_cast; omega
  · have h1 := hbud hl
    have h2 : radius.pos.length = k := by have := hlag.2; omega
    rw [h2]; omega

end ChainW3

/-! ## 4. `ReplayChainSeg2`: the replay segment with a break and a restart -/

section Seg2

open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier
open PalPeg.GalilTickFun PalPeg.GalilTickFun2 PalPeg.GalilReportReplay PalPeg.GalilReplayChainSeg
  PalPeg.GalilStructuredSkeleton

/-- `ReplayChainSeg` extended by
* `breakC` — the forced comparison whose match credit is `ChainMatched.breaks`
  (the chain lands in `.broken`); it is `matchC` with the broken result named;
* `restartC` — `Tick.restart` (the broken-chain restart of the search), which
  keeps the heads, the replay counter and the `replaying` flag and resets the
  clock.  It consumes no comparison event. -/
inductive ReplayChainSeg2 (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) :
    List Bool → Control → GalilVM → Control → GalilVM → Prop
  | stop (c : Control) (s : GalilVM) : ReplayChainSeg2 P q first delay [] c s c s
  | countC (c : Control) (s s' : GalilVM) {es : List Bool} {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = true) (hc : 1 < c.clock)
      (hne : s.chain ≠ .idle)
      (hb : (galilFrameS P q first).background s s')
      (rest : ReplayChainSeg2 P q first delay es {c with clock := c.clock - 1} s' c' t) :
      ReplayChainSeg2 P q first delay (false :: es) c s c' t
  | matchC (c : Control) (s : GalilVM) (vs : ScanVM) (vq : SearchVM) (o : Bool)
      {es : List Bool} {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = true) (hc : c.clock = 1)
      (ha : canRight s.right) (hne : s.chain ≠ .idle)
      (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
      (hmt : (galilFrame P q first).matched (scanLens.set s vs))
      (hq : searchEffect P true s vq)
      (ho : refresh (galilFrame P q first) (replayDec true (afterCompare s vs vq)) c.output o)
      (rest : ReplayChainSeg2 P q first delay es
        {c with clock := delay, output := o, replaying := !P.replayExhausted (replayDec true (afterCompare s vs vq))} (replayDec true (afterCompare s vs vq)) c' t) :
      ReplayChainSeg2 P q first delay (true :: es) c s c' t
  | breakC (c : Control) (s : GalilVM) (vs : ScanVM) (vq : SearchVM) (o : Bool) (w' : WState)
      {es : List Bool} {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = true) (hc : c.clock = 1)
      (ha : canRight s.right) (hne : s.chain ≠ .idle)
      (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
      (hmt : (galilFrame P q first).matched (scanLens.set s vs))
      (hbr : vs.chain = .broken w')
      (hq : searchEffect P true s vq)
      (ho : refresh (galilFrame P q first) (replayDec true (afterCompare s vs vq)) c.output o)
      (rest : ReplayChainSeg2 P q first delay es
        {c with clock := delay, output := o, replaying := !P.replayExhausted (replayDec true (afterCompare s vs vq))} (replayDec true (afterCompare s vs vq)) c' t) :
      ReplayChainSeg2 P q first delay (true :: es) c s c' t
  | restartC (c : Control) (s s' : GalilVM) {es : List Bool} {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hb : P.restart s s')
      (hl : s'.left = s.left) (hr : s'.right = s.right) (hC : s'.center = s.center)
      (hrep : s'.replay = s.replay)
      (rest : ReplayChainSeg2 P q first delay es {c with clock := delay} s' c' t) :
      ReplayChainSeg2 P q first delay es c s c' t

variable {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}

theorem replayChainSeg2_of_seg {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : ReplayChainSeg P q first delay es c s c' t) : ReplayChainSeg2 P q first delay es c s c' t := by
  induction h with
  | stop c s => exact .stop c s
  | countC c s s' hm hr hc hne hb _ ih => exact .countC c s s' hm hr hc hne hb ih
  | matchC c s vs vq o hm hr hc ha hne hcmp hmt hq ho _ ih =>
    exact .matchC c s vs vq o hm hr hc ha hne hcmp hmt hq ho ih

theorem replayChainSeg2_trans {es1 : List Bool} {c c' : Control} {s t : GalilVM}
    (h1 : ReplayChainSeg2 P q first delay es1 c s c' t) :
    ∀ {es2 : List Bool} {c'' : Control} {u : GalilVM},
      ReplayChainSeg2 P q first delay es2 c' t c'' u →
      ReplayChainSeg2 P q first delay (es1 ++ es2) c s c'' u := by
  induction h1 with
  | stop c s => intro es2 c'' u h2; simpa using h2
  | countC c s s' hm hr hc hne hb _ ih => intro es2 c'' u h2; exact .countC c s s' hm hr hc hne hb (ih h2)
  | matchC c s vs vq o hm hr hc ha hne hcmp hmt hq ho _ ih =>
    intro es2 c'' u h2; exact .matchC c s vs vq o hm hr hc ha hne hcmp hmt hq ho (ih h2)
  | breakC c s vs vq o w' hm hr hc ha hne hcmp hmt hbr hq ho _ ih =>
    intro es2 c'' u h2; exact .breakC c s vs vq o w' hm hr hc ha hne hcmp hmt hbr hq ho (ih h2)
  | restartC c s s' hm hb hl hr hC hrep _ ih =>
    intro es2 c'' u h2; exact .restartC c s s' hm hb hl hr hC hrep (ih h2)

/-- The restart tick of `galilFrameS`. -/
theorem restart_tickS (c : Control) (s s' : GalilVM) (hm : c.mode = .scan) (hb : P.restart s s') :
    Tick (galilFrameS P q first) delay ⟨c, s⟩ ⟨{c with clock := delay}, s'⟩ :=
  .restart c s s' hm hb

/-- **The segment is a `SoundScanNR` run** (the restart keeps the output and the
right head, hence `OutputRel`). -/
theorem replayChainSeg2_stepsAll (raw : List (Fin 2))
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : ReplayChainSeg2 P q first delay es c s c' t) (cen : ℕ) :
    ∀ r : ℕ, ScanInvariant raw cen r s.left s.right → SoundScanNR raw ⟨c, s⟩ →
      ∃ k, StepsAll (galilFrameS P q first) delay (SoundScanNR raw) k ⟨c, s⟩ ⟨c', t⟩ := by
  induction h with
  | stop c s => intro r _ hQ; exact ⟨0, .zero _ hQ⟩
  | countC c s s' hm hr hc hne hb _ ih =>
    intro r hi hQ
    obtain ⟨hl, hr', _, _⟩ := background_frame P q first hb
    obtain ⟨k, hs⟩ := ih r (by rw [hl, hr']; exact hi) (GalilReplaySegment.soundScanNR_replaying raw hr)
    exact ⟨k+1, .succ hQ (.scan_count c s s' hm (Or.inl hr) hc hb) hs⟩
  | matchC c s vs vq o hm hr hc ha hne hcmp hmt hq ho _ ih =>
    intro r hi hQ
    have hmatch := matchC_read P q first hcmp hmt
    obtain ⟨hl, hrr, _⟩ := compare_parts P q first hcmp hmatch
    have hi' : ScanInvariant raw cen (r+1) (replayDec true (afterCompare s vs vq)).left
        (replayDec true (afterCompare s vs vq)).right := by
      rw [replayDec_left, replayDec_right]
      exact matched_invariant' raw vq hl hrr hmatch ha hi
    obtain ⟨k, hs⟩ := ih (r+1) hi'
      (fun _ _ => outputRel_of_refresh' raw P hP hP' q first _ c.output o hi' ho _ rfl)
    have ht := scan_match_S' P q first delay c s vs vq o hm (Or.inl hr) hc hne hcmp hmt hq
      (by rw [hr]; exact ho)
    rw [hr] at ht
    exact ⟨k+1, .succ hQ (by simpa using ht) hs⟩
  | breakC c s vs vq o w' hm hr hc ha hne hcmp hmt hbr hq ho _ ih =>
    intro r hi hQ
    have hmatch := matchC_read P q first hcmp hmt
    obtain ⟨hl, hrr, _⟩ := compare_parts P q first hcmp hmatch
    have hi' : ScanInvariant raw cen (r+1) (replayDec true (afterCompare s vs vq)).left
        (replayDec true (afterCompare s vs vq)).right := by
      rw [replayDec_left, replayDec_right]
      exact matched_invariant' raw vq hl hrr hmatch ha hi
    obtain ⟨k, hs⟩ := ih (r+1) hi'
      (fun _ _ => outputRel_of_refresh' raw P hP hP' q first _ c.output o hi' ho _ rfl)
    have ht := scan_match_S' P q first delay c s vs vq o hm (Or.inl hr) hc hne hcmp hmt hq
      (by rw [hr]; exact ho)
    rw [hr] at ht
    exact ⟨k+1, .succ hQ (by simpa using ht) hs⟩
  | restartC c s s' hm hb hl hr hC hrep _ ih =>
    intro r hi hQ
    have hQ' : SoundScanNR raw ⟨{c with clock := delay}, s'⟩ := by
      intro hm' hr'
      have h0 := hQ hm' hr'
      intro hout k hk hk2 hpos
      exact h0 hout k hk hk2 (by rw [← hr]; exact hpos)
    obtain ⟨k, hs⟩ := ih r (by rw [hl, hr]; exact hi) hQ'
    exact ⟨k+1, .succ hQ (restart_tickS c s s' hm hb) hs⟩

/-- The centre invariant along the segment. -/
theorem replayChainSeg2_minv (raw : List (Fin 2))
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : ReplayChainSeg2 P q first delay es c s c' t) :
    ∀ r : ℕ, ScanInvariant raw (position s.center) r s.left s.right → MInv raw c s →
      MInv raw c' t := by
  induction h with
  | stop c s => intro r _ hM; exact hM
  | countC c s s' hm hr hc hne hb _ ih =>
    intro r hi hM
    obtain ⟨hl, hr', _, hC, _, _, _, _, _, hrep, _, _⟩ := backgroundS_fields P q first hb
    exact ih r (by rw [hl, hr', hC]; exact hi) (minv_same rfl hr' hC hrep hM)
  | matchC c s vs vq o hm hr hc ha hne hcmp hmt hq ho _ ih =>
    intro r hi hM
    have hmatch := matchC_read P q first hcmp hmt
    obtain ⟨hl, hrr, _⟩ := compare_parts P q first hcmp hmatch
    have hM' := minv_matchR P hex (vs := vs) (vq := vq) o delay hr hrr ha hi hM
    have hi' : ScanInvariant raw (position (replayDec true (afterCompare s vs vq)).center) (r+1)
        (replayDec true (afterCompare s vs vq)).left (replayDec true (afterCompare s vs vq)).right := by
      rw [replayDec_left, replayDec_right, replayDec_center, afterCompare_center]
      exact matched_invariant' raw vq hl hrr hmatch ha hi
    exact ih (r+1) hi' hM'
  | breakC c s vs vq o w' hm hr hc ha hne hcmp hmt hbr hq ho _ ih =>
    intro r hi hM
    have hmatch := matchC_read P q first hcmp hmt
    obtain ⟨hl, hrr, _⟩ := compare_parts P q first hcmp hmatch
    have hM' := minv_matchR P hex (vs := vs) (vq := vq) o delay hr hrr ha hi hM
    have hi' : ScanInvariant raw (position (replayDec true (afterCompare s vs vq)).center) (r+1)
        (replayDec true (afterCompare s vs vq)).left (replayDec true (afterCompare s vs vq)).right := by
      rw [replayDec_left, replayDec_right, replayDec_center, afterCompare_center]
      exact matched_invariant' raw vq hl hrr hmatch ha hi
    exact ih (r+1) hi' hM'
  | restartC c s s' hm hb hl hr hC hrep _ ih =>
    intro r hi hM
    exact ih r (by rw [hl, hr, hC]; exact hi) (minv_same rfl hr hC hrep hM)

/-! ### The restart, as a named shape of `P.restart` -/

/-- **Named hypothesis (restart shape).**  On a broken chain passing
`restartVM`'s checks the restart exists, idles the chain, keeps the heads, the
replay counter, the radius and `remaining`, and begins the search at `last`. -/
def RestartShape (P : Shared) : Prop :=
  ∀ (s : GalilVM) (w : WState), s.chain = .broken w → Restartable w →
    ∃ s', P.restart s s' ∧ s'.chain = .idle ∧ s'.left = s.left ∧ s'.right = s.right ∧
      s'.center = s.center ∧ s'.replay = s.replay ∧ s'.radius = s.radius ∧
      s'.remaining = s.remaining ∧
      s'.search = GalilScaffoldSearchFinish.begin w.machine.control.last s.radius

/-- The state `restartVM` produces. -/
def restartState (entry : ℕ) (s : GalilVM) (w : WState) : GalilVM :=
  { s with chain := ChainVM.idle, lower := w.machine.control.last, search := GalilScaffoldSearchFinish.begin w.machine.control.last s.radius, dp := GalilScaffoldControl.reset entry s.dp }

/-- `RestartShape` holds for the concrete restart `restartVM`. -/
theorem restartShape_of_restartVM (entry : ℕ) (h : P.restart = restartVM entry) : RestartShape P := by
  intro s w hs hw
  refine ⟨restartState entry s w, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [h]
  exact ⟨w, hs, hw.margin, hw.last, hw.lag, rfl⟩

/-- The concrete `Shared` of the run skeleton (`PofC … w = sharedC (onLetterVM w) leftFirstVM …`). -/
theorem restartShape_sharedC (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) :
    RestartShape (sharedC onLetter leftFirst centre place entry) :=
  restartShape_of_restartVM entry rfl

theorem searchReady_of_begin {s : GalilVM} {last : Counter}
    (h : s.search = GalilScaffoldSearchFinish.begin last s.radius) :
    GalilBranchInvariants2.SearchReady (searchLens.get s) :=
  GalilSearchReadyInv.searchReady_of_readyRem
    (GalilSearchReadyInv.searchReady_begin (searchLens.get s) last s.radius h [])

end Seg2

/-! ## 5. The live chain along the replay: countdown, comparison, break -/

section LiveRun

open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier
open PalPeg.GalilTickFun PalPeg.GalilTickFun2 PalPeg.GalilReportReplay PalPeg.GalilReplayChainSeg
  PalPeg.GalilStructuredSkeleton PalPeg.GalilReplayGeneral2

/-- The comparison budget identity: `1 + (e+1)(D-1) = D + e(D-1)` for `D ≥ 1`. -/
theorem bud_arith (D e : ℕ) (hD : 1 ≤ D) : (e + 1) * (D - 1) + 1 = D + e * (D - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  simp only [Nat.add_sub_cancel]; ring

variable (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (B E : ℕ)
  (lim : Bool) (cc b : Fin 3) (xs : List (Fin 3))

/-- The budget attached to a state: the clock plus `D - 1` per comparison left
before the window end. -/
def budOf (c : Control) (s : GalilVM) : ℕ := c.clock + (E - position s.right) * (delay - 1)

/-- The countdown to the next comparison with the chain in `ChainW`. -/
theorem chain_countdownW (hB : E < (encoded raw).length) :
    ∀ (j : ℕ) (c : Control) (s : GalilVM), c.mode = .scan → c.replaying = true →
      c.clock = j + 1 →
      ChainW raw (position s.center) E (position s.right) (budOf delay E c s) lim cc b xs s.chain →
      position s.right ≤ E →
      ∃ (es : List Bool) (s' : GalilVM),
        ReplayChainSeg P q first delay es c s {c with clock := 1} s' ∧ es.count true = 0 ∧
        ChainW raw (position s'.center) E (position s'.right) (budOf delay E {c with clock := 1} s')
          lim cc b xs s'.chain ∧
        s'.left = s.left ∧ s'.right = s.right ∧ s'.center = s.center ∧ s'.replay = s.replay ∧
        s'.remaining = s.remaining ∧ s'.radius = s.radius := by
  intro j
  induction j with
  | zero =>
    intro c s hm hrp hclk hpart _
    have hc1 : c.clock = 1 := by omega
    have hc : ({c with clock := 1} : Control) = c := by rw [← hc1]
    refine ⟨[], s, ?_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [hc]; exact .stop _ _
    · rw [hc]; exact hpart
  | succ j ih =>
    intro c s hm hrp hclk hpart hRE
    have hne : s.chain ≠ .idle := chainW_ne_idle hpart
    have hbud : budOf delay E c s = (j + 1 + (E - position s.right) * (delay - 1)) + 1 := by
      unfold budOf; omega
    rw [hbud] at hpart
    obtain ⟨z, hstep, hz⟩ := chainW_step hpart hB hRE
    obtain ⟨s1, hb, hch1, hl1, hr1, hC1, hrep1⟩ := active_background_exists P q first s hne hstep
    have hf := backgroundS_fields P q first hb
    have hrem1 : s1.remaining = s.remaining := hf.2.2.2.2.2.2.2.2.1
    have hrad1 : s1.radius = s.radius := hf.2.2.2.2.2.1
    have hp1 : ChainW raw (position s1.center) E (position s1.right)
        (budOf delay E {c with clock := c.clock - 1} s1) lim cc b xs s1.chain := by
      rw [hch1, hr1, hC1]
      unfold budOf
      rw [hr1]
      convert hz using 2; simp; omega
    obtain ⟨es, s2, hseg, hcnt, hp2, hl2, hr2, hC2, hrep2, hrem2, hrad2⟩ :=
      ih {c with clock := c.clock - 1} s1 hm hrp (by simp; omega) hp1 (by rw [hr1]; exact hRE)
    refine ⟨false :: es, s2, ?_, by simpa using hcnt, ?_,
      by rw [hl2, hl1], by rw [hr2, hr1], by rw [hC2, hC1], by rw [hrep2, hrep1],
      by rw [hrem2, hrem1], by rw [hrad2, hrad1]⟩
    · exact .countC c s s1 hm hrp (by omega) hne hb hseg
    · simpa using hp2

end LiveRun

section LiveCompare

open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier
open PalPeg.GalilTickFun PalPeg.GalilTickFun2 PalPeg.GalilReportReplay PalPeg.GalilReplayChainSeg
  PalPeg.GalilStructuredSkeleton PalPeg.GalilReplayGeneral2

variable (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (B : ℕ)

/-- The scan part of a forced replay comparison on an active chain whose
credit is `z` (a match or a break). -/
def cmpVS (s : GalilVM) (z : ChainVM) : ScanVM := ⟨left s.left, right s.right, z⟩

def cmpU (s : GalilVM) (z : ChainVM) : GalilVM :=
  replayDec true (afterCompare s (cmpVS s z) (searchLens.get s))

open Classical in
noncomputable def cmpO (c : Control) (s : GalilVM) (z : ChainVM) : Bool :=
  if P.onLetter (cmpU s z) then decide (P.leftFirst (cmpU s z)) else c.output

noncomputable def cmpC (c : Control) (s : GalilVM) (z : ChainVM) : Control :=
  { c with clock := delay, output := cmpO P c s z, replaying := !P.replayExhausted (cmpU s z) }

/-- **A forced comparison on an active chain.** -/
theorem forced_compare (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (c : Control) (s : GalilVM) (k m : ℕ) (z : ChainVM)
    (hr : c.replaying = true) (hne : s.chain ≠ .idle)
    (hbd : Bnd B s) (hM : MInv raw c s) (hi : ScanInvariant raw (position s.center) k s.left s.right)
    (hrp : s.replay = ofNat (m+1)) (hfr : Frontier s) (hrad : RadiusRep s.radius k)
    (htz : read (left s.left) = read (right s.right) → ChainTick true s.chain z) :
    canRight s.right ∧
    (galilFrame P q first).compare s (scanLens.set s (cmpVS s z)) ∧
    (galilFrame P q first).matched (scanLens.set s (cmpVS s z)) ∧
    searchEffect P true s (searchLens.get s) ∧
    refresh (galilFrame P q first) (cmpU s z) c.output (cmpO P c s z) ∧
    (cmpC P delay c s z).replaying = decide (0 < m) ∧
    (cmpU s z).chain = z ∧ MInv raw (cmpC P delay c s z) (cmpU s z) ∧
    ScanInvariant raw (position (cmpU s z).center) (k+1) (cmpU s z).left (cmpU s z).right ∧
    (cmpU s z).replay = ofNat m ∧ position (cmpU s z).right = position s.right + 1 ∧
    (cmpU s z).center = s.center ∧ Frontier (cmpU s z) ∧ (cmpU s z).remaining = s.remaining ∧
    RadiusRep (cmpU s z).radius (k+1) ∧ Bnd B (cmpU s z) ∧
    (P.onLetter = onLetterVM raw → P.leftFirst = leftFirstVM →
      OutputRel raw (cmpC P delay c s z) (cmpU s z)) := by
  classical
  have hbound : position s.right + (m+1) ≤ 2 * arrived s.right := hfr (m+1) hrp
  have hav : canRight s.right := GalilReplaySegment.canRight_of_frontier (Nat.succ_pos m) hbound
  have hmatch : read (left s.left) = read (right s.right) := replay_match_of_minv hM hr hav hi
  have htz' := htz hmatch
  have hcmp : (galilFrame P q first).compare s (scanLens.set s (cmpVS s z)) := by
    refine ⟨?_, ?_⟩
    · rw [scanLens.get_set]
      refine ⟨rfl, rfl, ?_⟩
      show ChainTick (decide (read (left s.left) = read (right s.right))) s.chain z
      rw [decide_eq_true hmatch]; exact htz'
    · rw [scanLens.get_set]
  have hmt : (galilFrame P q first).matched (scanLens.set s (cmpVS s z)) := hmatch
  have hq : searchEffect P true s (searchLens.get s) := Or.inr ⟨hne, rfl⟩
  have ho : refresh (galilFrame P q first) (cmpU s z) c.output (cmpO P c s z) := by
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : P.onLetter (cmpU s z) := hl
      show (if P.onLetter (cmpU s z) then decide (P.leftFirst (cmpU s z)) else c.output) = true ↔
        P.leftFirst (cmpU s z)
      rw [if_pos hl']; exact decide_eq_true_iff
    · have hl' : ¬ P.onLetter (cmpU s z) := hl
      show (if P.onLetter (cmpU s z) then decide (P.leftFirst (cmpU s z)) else c.output) = c.output
      rw [if_neg hl']
  have hurep : (cmpU s z).replay = ofNat m := by
    unfold cmpU
    rw [replayDec_true_replay, afterCompare_replay, hrp, dec_ofNat_succ]
  have hflag : (!P.replayExhausted (cmpU s z)) = decide (0 < m) := by
    rw [hex, hurep]
    cases m with
    | zero => rw [(zero_ofNat_iff 0).2 rfl]; simp
    | succ k => rw [zero_ofNat_succ k]; simp
  have hpos : position (right s.right) = position s.right + 1 :=
    right_position s.right hav (represented_position _ raw hi.rightRep hi.rightPresent).1
  have hur : (cmpU s z).right = right s.right := by unfold cmpU; rw [replayDec_right, afterCompare_right]; rfl
  have hCu : (cmpU s z).center = s.center := by unfold cmpU; rw [replayDec_center, afterCompare_center]
  have hchu : (cmpU s z).chain = z := by unfold cmpU; rw [replayDec_chain, afterCompare_chain]; rfl
  have hiu : ScanInvariant raw (position (cmpU s z).center) (k+1) (cmpU s z).left (cmpU s z).right := by
    have h0 := matched_invariant' raw (searchLens.get s) (vs := cmpVS s z) rfl rfl hmatch hav hi
    unfold cmpU
    rw [replayDec_left, replayDec_right, replayDec_center, afterCompare_center]
    exact h0
  have hMu : MInv raw (cmpC P delay c s z) (cmpU s z) :=
    minv_matchR P hex (cmpO P c s z) delay hr rfl hav hi hM
  refine ⟨hav, hcmp, hmt, hq, ho, hflag, hchu, hMu, hiu, hurep, by rw [hur]; exact hpos, hCu, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro m' hm'
    have hmm : m' = m := (ofNat_inj (hurep.symm.trans hm')).symm
    subst hmm
    rw [hur]
    exact right_frontier_step s.right m' hbound
  · unfold cmpU; rfl
  · unfold cmpU
    rw [replayDec_radius, afterCompare_radius]; exact radius_rep_inc hrad
  · intro m' hm'
    have hmm : m' = m := (ofNat_inj (hurep.symm.trans hm')).symm
    subst hmm
    have := hbd (m'+1) hrp
    rw [hur, hpos]; omega
  · intro hP hP'
    exact outputRel_of_refresh' raw P hP hP' q first _ c.output _ hiu ho _ rfl

end LiveCompare

section LiveSteps

open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier
open PalPeg.GalilTickFun PalPeg.GalilTickFun2 PalPeg.GalilReportReplay PalPeg.GalilReplayChainSeg
  PalPeg.GalilStructuredSkeleton PalPeg.GalilReplayGeneral2

variable (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (B E : ℕ)
  (lim : Bool) (cc b : Fin 3) (xs : List (Fin 3))

/-- A matched comparison strictly inside the window. -/
theorem chain_compareW (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hE : E < (encoded raw).length)
    (c : Control) (s : GalilVM) (k m : ℕ)
    (hm : c.mode = .scan) (hr : c.replaying = true) (hc : c.clock = 1)
    (hpart : ChainW raw (position s.center) E (position s.right) (budOf delay E c s) lim cc b xs s.chain)
    (hRE : position s.right + 1 ≤ E)
    (hbd : Bnd B s) (hM : MInv raw c s) (hi : ScanInvariant raw (position s.center) k s.left s.right)
    (hrp : s.replay = ofNat (m+1)) (hfr : Frontier s) (hrad : RadiusRep s.radius k) :
    ∃ (c1 : Control) (u : GalilVM),
      ReplayChainSeg P q first delay [true] c s c1 u ∧
      c1.mode = .scan ∧ c1.clock = delay ∧ c1.replaying = decide (0 < m) ∧
      ChainW raw (position u.center) E (position u.right) (budOf delay E c1 u) lim cc b xs u.chain ∧
      MInv raw c1 u ∧ ScanInvariant raw (position u.center) (k+1) u.left u.right ∧
      u.replay = ofNat m ∧ position u.right = position s.right + 1 ∧
      u.center = s.center ∧ Frontier u ∧ u.remaining = s.remaining ∧
      RadiusRep u.radius (k+1) ∧ Bnd B u := by
  have hne : s.chain ≠ .idle := chainW_ne_idle hpart
  have hbud : budOf delay E c s = (E - position s.right) * (delay - 1) + 1 := by
    unfold budOf; rw [hc]; omega
  rw [hbud] at hpart
  obtain ⟨y, hstep, hy⟩ := chainW_step hpart hE (by omega)
  obtain ⟨z, hmat, hz⟩ := chainW_matched hy hE hRE
  obtain ⟨hav, hcmp, hmt, hq, ho, hflag, hchu, hMu, hiu, hurep, hposu, hCu, hfru, hremu, hradu, hbdu, -⟩ :=
    forced_compare raw P q first delay B hex c s k m z hr hne hbd hM hi hrp hfr hrad
      (fun _ => ⟨y, hstep, hmat⟩)
  refine ⟨cmpC P delay c s z, cmpU s z,
    .matchC c s (cmpVS s z) (searchLens.get s) (cmpO P c s z) hm hr hc hav hne hcmp hmt hq ho (.stop _ _),
    hm, rfl, hflag, ?_, hMu, hiu, hurep, hposu, hCu, hfru, hremu, hradu, hbdu⟩
  rw [hchu, hCu, hposu]
  have e : budOf delay E (cmpC P delay c s z) (cmpU s z) = (E - position s.right) * (delay - 1) + 1 := by
    unfold budOf; rw [hposu]
    show delay + (E - (position s.right + 1)) * (delay - 1) = _
    have := bud_arith delay (E - (position s.right + 1)) hd
    rw [show E - (position s.right + 1) + 1 = E - position s.right from by omega] at this
    omega
  rw [e]; exact hz

/-- **The break at the window's end, then the restart.** -/
theorem chain_breakW (hex : ∀ s, P.replayExhausted s = zero s.replay) (hrs : RestartShape P)
    (hBl : B < (encoded raw).length)
    (c : Control) (s : GalilVM) (k m : ℕ)
    (hm : c.mode = .scan) (hr : c.replaying = true) (hc : c.clock = 1)
    (hpart : ChainW raw (position s.center) E (position s.right) (budOf delay E c s) true cc b xs s.chain)
    (hRE : position s.right = E) (hEB : E < B)
    (hmis : Mispredicted raw cc b xs (position s.center + 1) (E + 1))
    (h4 : position s.center + 4 * (xs.length + 1) ≤ E + 1)
    (hbd : Bnd B s) (hM : MInv raw c s) (hi : ScanInvariant raw (position s.center) k s.left s.right)
    (hrp : s.replay = ofNat (m+1)) (hfr : Frontier s) (hrad : RadiusRep s.radius k) :
    ∃ (c1 : Control) (u : GalilVM),
      ReplayChainSeg2 P q first delay [true] c s c1 u ∧
      c1.mode = .scan ∧ c1.clock = delay ∧ c1.replaying = decide (0 < m) ∧
      u.chain = .idle ∧ GalilBranchInvariants2.SearchReady (searchLens.get u) ∧
      MInv raw c1 u ∧ ScanInvariant raw (position u.center) (k+1) u.left u.right ∧
      u.replay = ofNat m ∧ position u.right = position s.right + 1 ∧
      u.center = s.center ∧ Frontier u ∧ u.remaining = s.remaining ∧
      RadiusRep u.radius (k+1) ∧ Bnd B u ∧
      (P.onLetter = onLetterVM raw → P.leftFirst = leftFirstVM → OutputRel raw c1 u) := by
  have hne : s.chain ≠ .idle := chainW_ne_idle hpart
  have hbud : budOf delay E c s = 0 + 1 := by
    unfold budOf; rw [hc, hRE]; simp
  rw [hbud] at hpart
  obtain ⟨y, hstep, hy⟩ := chainW_step hpart (by omega) (by omega)
  rw [hRE] at hy
  obtain ⟨w', hmat, hw'⟩ := chainW_break hy (by omega) hmis h4
  obtain ⟨hav, hcmp, hmt, hq, ho, hflag, hchu, hMu, hiu, hurep, hposu, hCu, hfru, hremu, hradu, hbdu,
      hout⟩ :=
    forced_compare raw P q first delay B hex c s k m (.broken w') hr hne hbd hM hi hrp hfr hrad
      (fun _ => ⟨y, hstep, hmat⟩)
  obtain ⟨s', hb', hidle', hl', hr', hC', hrep', hrad', hrem', hsearch'⟩ :=
    hrs (cmpU s (.broken w')) w' hchu hw'
  refine ⟨{cmpC P delay c s (.broken w') with clock := delay}, s',
    .breakC c s (cmpVS s (.broken w')) (searchLens.get s) (cmpO P c s (.broken w')) w' hm hr hc hav hne
      hcmp hmt rfl hq ho (.restartC (cmpC P delay c s (.broken w')) (cmpU s (.broken w')) s' hm hb'
        hl' hr' hC' hrep' (.stop _ _)),
    hm, rfl, hflag, hidle', ?_, ?_, ?_, by rw [hrep', hurep], by rw [hr', hposu], by rw [hC', hCu],
    frontier_congr hr' hrep' hfru, by rw [hrem', hremu], by rw [hrad']; exact hradu,
    bnd_congr hr' hrep' hbdu, ?_⟩
  · apply searchReady_of_begin (last := w'.machine.control.last)
    rw [hsearch', hrad']
  · exact minv_same rfl hr' hC' hrep' hMu
  · rw [hl', hr', hC']; exact hiu
  · intro hP hP'
    have h0 := hout hP hP'
    intro ho' k' hk hk2 hpos
    exact h0 ho' k' hk hk2 (by rw [← hr']; exact hpos)

end LiveSteps

section LiveRunAll

open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier
open PalPeg.GalilTickFun PalPeg.GalilTickFun2 PalPeg.GalilReportReplay PalPeg.GalilReplayChainSeg
  PalPeg.GalilStructuredSkeleton PalPeg.GalilReplayGeneral2

variable (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (B E : ℕ)
  (lim : Bool) (cc b : Fin 3) (xs : List (Fin 3))

/-- The two ways a live replay chain ends: it survives to the landing (window
`B`), or it breaks at `E + 1` and the search restarts with `m'` comparisons of
the replay left. -/
def LiveEnd (c : Control) (s : GalilVM) (k m : ℕ) : Prop :=
  (∃ (es : List Bool) (c' : Control) (t : GalilVM),
      ReplayChainSeg P q first delay es c s c' t ∧ es.count true = m ∧
      c'.mode = .scan ∧ c'.clock = delay ∧ c'.replaying = false ∧ t.replay = reset ∧
      ChainW raw (position t.center) B (position t.right) (budOf delay B c' t) false cc b xs t.chain ∧
      position t.right = B ∧ MInv raw c' t ∧
      ScanInvariant raw (position t.center) (k + m) t.left t.right ∧
      position t.right = position s.right + m ∧ t.center = s.center ∧ Frontier t ∧
      t.remaining = s.remaining) ∨
  (∃ (es : List Bool) (c' : Control) (t : GalilVM) (m' : ℕ),
      ReplayChainSeg2 P q first delay es c s c' t ∧ m' < m ∧
      c'.mode = .scan ∧ c'.clock = delay ∧ c'.replaying = decide (0 < m') ∧ t.replay = ofNat m' ∧
      t.chain = .idle ∧ GalilBranchInvariants2.SearchReady (searchLens.get t) ∧ MInv raw c' t ∧
      ScanInvariant raw (position t.center) (k + (m - m')) t.left t.right ∧
      RadiusRep t.radius (k + (m - m')) ∧ position t.right = position s.right + (m - m') ∧
      t.center = s.center ∧ Frontier t ∧ t.remaining = s.remaining ∧ Bnd B t ∧
      (P.onLetter = onLetterVM raw → P.leftFirst = leftFirstVM → m' = 0 → OutputRel raw c' t))

/-- **The live chain along the rest of the replay.** -/
theorem chain_runW (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hrs : RestartShape P) (hBl : B < (encoded raw).length) (hEB : E ≤ B)
    (hlimF : lim = false → E = B) (hlimT : lim = true → E < B) :
    ∀ (m : ℕ) (c : Control) (s : GalilVM) (k : ℕ),
      c.mode = .scan → 1 ≤ c.clock → c.replaying = decide (0 < m) → (m = 0 → c.clock = delay) →
      s.replay = ofNat m → Bnd B s →
      ChainW raw (position s.center) E (position s.right) (budOf delay E c s) lim cc b xs s.chain →
      position s.right ≤ E →
      (lim = true → Mispredicted raw cc b xs (position s.center + 1) (E + 1) ∧
        position s.center + 4 * (xs.length + 1) ≤ E + 1) →
      MInv raw c s → ScanInvariant raw (position s.center) k s.left s.right → Frontier s →
      RadiusRep s.radius k →
      LiveEnd raw P q first delay B cc b xs c s k m := by
  intro m
  induction m with
  | zero =>
    intro c s k hm hclk hrp hc0 hrep hbd hpart hRE hbrk hM hi hfr hrad
    have hRB : position s.right = B := by simpa using hbd 0 hrep
    cases lim with
    | true => exact absurd (hlimT rfl) (by omega)
    | false =>
      have hEq := hlimF rfl
      subst hEq
      exact Or.inl ⟨[], c, s, .stop _ _, rfl, hm, hc0 rfl, by simpa using hrp, hrep, hpart, hRB, hM,
        by simpa using hi, by simp, rfl, hfr, rfl⟩
  | succ n ih =>
    intro c s k hm hclk hrp hc0 hrep hbd hpart hRE hbrk hM hi hfr hrad
    have hrt : c.replaying = true := by rw [hrp]; simp
    obtain ⟨j, hj⟩ : ∃ j, c.clock = j + 1 := ⟨c.clock - 1, by omega⟩
    have hElen : E < (encoded raw).length := by omega
    obtain ⟨es1, s1, hseg1, hcnt1, hp1, hl1, hr1, hC1, hrep1, hrem1, hrad1⟩ :=
      chain_countdownW raw P q first delay E lim cc b xs hElen j c s hm hrt hj hpart hRE
    have hM1 : MInv raw {c with clock := 1} s1 := minv_same rfl hr1 hC1 hrep1 hM
    have hi1 : ScanInvariant raw (position s1.center) k s1.left s1.right := by
      rw [hl1, hr1, hC1]; exact hi
    have hfr1 : Frontier s1 := frontier_congr hr1 hrep1 hfr
    have hbd1 : Bnd B s1 := bnd_congr hr1 hrep1 hbd
    have hrad1' : RadiusRep s1.radius k := by rw [hrad1]; exact hrad
    have hrep1' : s1.replay = ofNat (n+1) := by rw [hrep1, hrep]
    by_cases hlt : position s1.right + 1 ≤ E
    · obtain ⟨c2, u, hseg2, hm2, hc2, hr2, hp2, hM2, hi2, hrep2, hpos2, hC2, hfr2, hrem2, hrad2, hbd2⟩ :=
        chain_compareW raw P q first delay B E lim cc b xs hex hd hElen {c with clock := 1} s1 k n hm hrt rfl
          hp1 hlt hbd1 hM1 hi1 hrep1' hfr1 hrad1'
      have hbrk2 : lim = true → Mispredicted raw cc b xs (position u.center + 1) (E + 1) ∧
          position u.center + 4 * (xs.length + 1) ≤ E + 1 := by
        rw [hC2, hC1]; exact hbrk
      rcases ih c2 u (k+1) hm2 (by rw [hc2]; exact hd) hr2 (fun _ => hc2) hrep2 hbd2 hp2 (by omega) hbrk2
          hM2 hi2 hfr2 hrad2 with hA | hB'
      · obtain ⟨es3, c3, t3, hseg3, hcnt3, hm3, hc3, hr3, hrep3, hp3, hB3, hM3, hi3, hpos3, hC3, hfr3,
          hrem3⟩ := hA
        refine Or.inl ⟨es1 ++ ([true] ++ es3), c3, t3,
          replayChainSeg_trans P q first delay hseg1 (replayChainSeg_trans P q first delay hseg2 hseg3),
          ?_, hm3, hc3, hr3, hrep3, hp3, hB3, hM3, ?_, ?_, ?_, hfr3, ?_⟩
        · simp only [List.count_append, hcnt1, hcnt3, List.count_singleton_self]; omega
        · rw [show k + (n+1) = k+1+n from by omega]; exact hi3
        · rw [hpos3, hpos2, hr1]; omega
        · rw [hC3, hC2, hC1]
        · rw [hrem3, hrem2, hrem1]
      · obtain ⟨es3, c3, t3, m', hseg3, hlt3, hm3, hc3, hr3, hrep3, hidle3, hsr3, hM3, hi3, hrad3, hpos3,
          hC3, hfr3, hrem3, hbd3, hout3⟩ := hB'
        refine Or.inr ⟨es1 ++ ([true] ++ es3), c3, t3, m',
          replayChainSeg2_trans (replayChainSeg2_of_seg hseg1)
            (replayChainSeg2_trans (replayChainSeg2_of_seg hseg2) hseg3),
          by omega, hm3, hc3, hr3, hrep3, hidle3, hsr3, hM3, ?_, ?_, ?_, ?_, hfr3, ?_, hbd3, hout3⟩
        · rw [show k + (n + 1 - m') = k + 1 + (n - m') from by omega]; exact hi3
        · rw [show k + (n + 1 - m') = k + 1 + (n - m') from by omega]; exact hrad3
        · rw [hpos3, hpos2, hr1]; omega
        · rw [hC3, hC2, hC1]
        · rw [hrem3, hrem2, hrem1]
    · have hRE1 : position s1.right = E := by rw [hr1] at hlt ⊢; omega
      cases lim with
      | false =>
        exfalso
        have hEq := hlimF rfl
        have := hbd1 (n+1) hrep1'
        omega
      | true =>
        obtain ⟨hmis, h4⟩ := hbrk rfl
        obtain ⟨c2, u, hseg2, hm2, hc2, hr2, hidle2, hsr2, hM2, hi2, hrep2, hpos2, hC2, hfr2, hrem2, hrad2,
            hbd2, hout2⟩ :=
          chain_breakW raw P q first delay B E cc b xs hex hrs hBl {c with clock := 1} s1 k n hm hrt rfl
            hp1 hRE1 (hlimT rfl) (by rw [hC1]; exact hmis) (by rw [hC1]; exact h4) hbd1 hM1 hi1 hrep1'
            hfr1 hrad1'
        refine Or.inr ⟨es1 ++ [true], c2, u, n,
          replayChainSeg2_trans (replayChainSeg2_of_seg hseg1) hseg2, by omega, hm2, hc2, hr2, hrep2,
          hidle2, hsr2, hM2, ?_, ?_, ?_, ?_, hfr2, ?_, hbd2, fun hP hP' _ => hout2 hP hP'⟩
        · rw [show k + (n + 1 - n) = k + 1 from by omega]; exact hi2
        · rw [show k + (n + 1 - n) = k + 1 from by omega]; exact hrad2
        · rw [hpos2, hr1]; omega
        · rw [hC2, hC1]
        · rw [hrem2, hrem1]

end LiveRunAll

/-! ## 6. The replacement of `ReplaySpan`, and the window at a found search -/

section Found

open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier
open PalPeg.GalilTickFun PalPeg.GalilTickFun2 PalPeg.GalilReportReplay PalPeg.GalilReplayChainSeg
  PalPeg.GalilStructuredSkeleton PalPeg.GalilReplayGeneral2 PalPeg.GalilBranchInvariants2
  PalPeg.GalilBranchInvariants

/-- **Named hypothesis (break budget), replacing `ReplaySpan`.**  Same premises
as `ReplaySpan`.  Instead of claiming that the block spans the whole replay,
it constrains only a *mispredicted* place `j` of the replay (`C < j ≤ R + m`):
such a place lies beyond four semiperiods (`C + 4n < j`, the mirror of
`candidate_periodOn`), beyond the next comparison (`R + 2 ≤ j`), and far enough
for the chain to finish copying, rewinding and catching up its lag
(`2n + 3 + k ≤ (j - (R+2))·(delay - 1)`).  When no place is mispredicted the
hypothesis is vacuous and the chain survives the replay. -/
def ReplayBudget (raw : List (Fin 2)) (P : Shared) (delay : ℕ) : Prop :=
  ∀ (c : Control) (s : GalilVM) (a : Bool) (vq : SearchVM) (k m n : ℕ) (xs : List (Fin 3))
    (b : Fin 3),
    c.mode = .scan → c.replaying = true → s.chain = .idle → SearchReady (searchLens.get s) →
    searchEffect P a s vq → vq.search.mode = .found → MInv raw c s →
    ScanInvariant raw (position s.center) k s.left s.right → RadiusRep s.radius k →
    s.replay = ofNat m → 0 < m → Frontier s →
    AnswerAhead (vq.dp.config.tapes 11) n → 0 < n → PlaceAhead (P.place s) n →
    (GalilScaffoldPlace.stream (P.place s)).tail.take n = xs ++ [b] →
    ∀ j, position s.center + 1 ≤ j → j ≤ position s.right + m →
      Mispredicted raw (P.centre s) b xs (position s.center + 1) j →
      position s.center + 4 * n < j ∧ position s.right + 2 ≤ j ∧
        2 * n + 3 + k ≤ (j - (position s.right + 2)) * (delay - 1)

theorem split_length {walker : GalilScaffoldPlace.Place} {n : ℕ} {xs : List (Fin 3)} {b : Fin 3}
    (hp : PlaceAhead walker n) (h : (GalilScaffoldPlace.stream walker).tail.take n = xs ++ [b]) :
    n = xs.length + 1 := by
  have := congrArg List.length h
  rw [List.length_take, List.length_tail] at this
  unfold PlaceAhead at hp
  simp at this; omega

/-- The window at a found search inside a replay. -/
theorem window_of_found {raw : List (Fin 2)} {P : Shared} {delay : ℕ}
    (hbudget : ReplayBudget raw P delay)
    (c : Control) (s : GalilVM) (a : Bool) (vq : SearchVM) (k m n : ℕ) (xs : List (Fin 3)) (b : Fin 3)
    (hm : c.mode = .scan) (hr : c.replaying = true) (hidle : s.chain = .idle)
    (hsr : SearchReady (searchLens.get s)) (hq : searchEffect P a s vq)
    (hf : vq.search.mode = .found) (hM : MInv raw c s)
    (hi : ScanInvariant raw (position s.center) k s.left s.right) (hrad : RadiusRep s.radius k)
    (hrep : s.replay = ofNat m) (hm0 : 0 < m) (hfr : Frontier s)
    (ha : AnswerAhead (vq.dp.config.tapes 11) n) (hn : 0 < n) (hpl : PlaceAhead (P.place s) n)
    (hsplit : (GalilScaffoldPlace.stream (P.place s)).tail.take n = xs ++ [b]) :
    ∃ (E : ℕ) (lim : Bool),
      E ≤ position s.right + m ∧ (lim = false → E = position s.right + m) ∧
      (lim = true → E < position s.right + m) ∧ position s.right + 1 ≤ E ∧
      BlockOn raw (P.centre s) b xs (position s.center + 1) E ∧
      (lim = true → Mispredicted raw (P.centre s) b xs (position s.center + 1) (E + 1) ∧
        position s.center + 4 * (xs.length + 1) ≤ E + 1 ∧
        2 * n + 2 + k ≤ (E - position s.right) * (delay - 1)) := by
  have hRC : position s.right = position s.center + k := hi.rightPos
  obtain ⟨E, h1, h2, h3, h4⟩ := maximal_window raw (P.centre s) b xs (position s.center + 1) (by omega)
    (position s.right + m - position s.center) (position s.right + m) (by omega)
  have hlen := split_length hpl hsplit
  by_cases hEB : E < position s.right + m
  · obtain ⟨hj1, hj2, hj3⟩ := hbudget c s a vq k m n xs b hm hr hidle hsr hq hf hM hi hrad hrep hm0 hfr
      ha hn hpl hsplit (E + 1) (by omega) (by omega) (h4 hEB)
    refine ⟨E, true, h2, fun h => absurd h (by decide), fun _ => hEB, by omega, h3,
      fun _ => ⟨h4 hEB, by omega, ?_⟩⟩
    have hmono : (E + 1 - (position s.right + 2)) * (delay - 1) ≤ (E - position s.right) * (delay - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · refine ⟨E, false, h2, fun _ => by omega, fun h => absurd h (by decide), by omega, h3,
      fun h => absurd h (by decide)⟩

end Found

/-! ## 7. Landing shapes and their prefixes -/

section Ends

open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier
open PalPeg.GalilTickFun PalPeg.GalilTickFun2 PalPeg.GalilReportReplay PalPeg.GalilReplayChainSeg
  PalPeg.GalilStructuredSkeleton PalPeg.GalilReplayGeneral2 PalPeg.GalilBranchInvariants2
  PalPeg.GalilReplayGeneral

variable (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (B : ℕ)

/-- The idle landing of a replay (as in branch (i) of `replay_after_fallback_general'`). -/
def IdleEnd (s : GalilVM) (k r : ℕ) (c' : Control) (t : GalilVM) : Prop :=
  c'.mode = .scan ∧ c'.clock = delay ∧ c'.replaying = false ∧ t.replay = reset ∧
  t.chain = .idle ∧ SearchReady (searchLens.get t) ∧ MInv raw c' t ∧
  ScanInvariant raw (position t.center) (k + r) t.left t.right ∧
  position t.right = position s.right + r ∧ t.center = s.center ∧ Frontier t ∧ ReplayRest c' t ∧
  t.remaining = s.remaining

/-- (i) The replay ran with the chain idle throughout. -/
def QuietEnd (c : Control) (s : GalilVM) (k r : ℕ) : Prop :=
  ∃ (es : List Bool) (c' : Control) (t : GalilVM),
    WatchSegE P q first delay es c s c' t ∧
    (SoundScanNR raw ⟨c', t⟩ →
      StepsAll (galilFrameS P q first) delay (SoundScanNR raw) es.length ⟨c, s⟩ ⟨c', t⟩) ∧
    es.length = r * delay ∧ es.count true = r ∧ IdleEnd raw delay s k r c' t

/-- (ii) The last chain started in the replay survives to the landing, whose
right head is the span end `B`, in `ChainW` with window `B`. -/
def ChainEnd (c : Control) (s : GalilVM) (k r : ℕ) : Prop :=
  ∃ (n1 : ℕ) (c1 : Control) (s1 : GalilVM) (c2 : Control) (s2 : GalilVM) (es2 : List Bool)
    (c' : Control) (t : GalilVM) (n : ℕ) (cc b : Fin 3) (xs : List (Fin 3)),
    StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n1 ⟨c, s⟩ ⟨c1, s1⟩ ∧
    s1.chain = .idle ∧ c1.replaying = true ∧
    FoundTick P q first delay c1 s1 c2 s2 ∧
    ReplayChainSeg P q first delay es2 c2 s2 c' t ∧
    StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, s⟩ ⟨c', t⟩ ∧
    ChainTicks es2 s2.chain t.chain ∧
    c'.mode = .scan ∧ c'.clock = delay ∧ c'.replaying = false ∧ t.replay = reset ∧
    t.chain ≠ .idle ∧
    ChainW raw (position t.center) B (position t.right) (budOf delay B c' t) false cc b xs t.chain ∧
    position t.right = B ∧ MInv raw c' t ∧
    ScanInvariant raw (position t.center) (k + r) t.left t.right ∧
    position t.right = position s.right + r ∧ t.center = s.center ∧ Frontier t ∧
    ReplayRest c' t ∧ t.remaining = s.remaining

/-- A chain broke inside the run and the search restarted. -/
def BrokeAndRestarted (c : Control) (s : GalilVM) : Prop :=
  ∃ (n1 : ℕ) (c1 : Control) (s1 : GalilVM) (es : List Bool) (c2 : Control) (s2 : GalilVM),
    StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n1 ⟨c, s⟩ ⟨c1, s1⟩ ∧
    ReplayChainSeg2 P q first delay es c1 s1 c2 s2 ∧ s1.chain ≠ .idle ∧ s2.chain = .idle

/-- (iii) A chain broke during the replay, the search restarted, and the replay
continued as an idle replay to an idle landing. -/
def RestartEnd (c : Control) (s : GalilVM) (k r : ℕ) : Prop :=
  BrokeAndRestarted raw P q first delay c s ∧
  ∃ (n : ℕ) (c' : Control) (t : GalilVM),
    (SoundScanNR raw ⟨c', t⟩ →
      StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, s⟩ ⟨c', t⟩) ∧
    IdleEnd raw delay s k r c' t

def Busy (c : Control) (s : GalilVM) (k r : ℕ) : Prop :=
  ChainEnd raw P q first delay B c s k r ∨ RestartEnd raw P q first delay c s k r

def Result3 (c : Control) (s : GalilVM) (k r : ℕ) : Prop :=
  QuietEnd raw P q first delay c s k r ∨ Busy raw P q first delay B c s k r

/-- The entry of an idle replay stretch. -/
def Entry (c : Control) (s : GalilVM) (k r : ℕ) : Prop :=
  c.mode = .scan ∧ c.clock = delay ∧ c.replaying = decide (0 < r) ∧ s.replay = ofNat r ∧
  s.chain = .idle ∧ SearchReady (searchLens.get s) ∧ MInv raw c s ∧
  ScanInvariant raw (position s.center) k s.left s.right ∧ Frontier s ∧ RadiusRep s.radius k ∧
  Bnd B s ∧ GalilScaffoldInputTrace.Represents s.center.head raw ∧ s.center.head.focus ≠ none

variable {raw P q first delay B}

theorem idleEnd_shift {s s1 : GalilVM} {k r k1 r1 : ℕ} {c' : Control} {t : GalilVM}
    (hk : k1 + r1 = k + r) (hp : position s1.right + r1 = position s.right + r)
    (hC : s1.center = s.center) (hrem : s1.remaining = s.remaining)
    (h : IdleEnd raw delay s1 k1 r1 c' t) : IdleEnd raw delay s k r c' t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, by rw [← hk]; exact h8, by omega, by rw [h10, hC], h11, h12,
    by rw [h13, hrem]⟩

/-- Prefixing a `SoundScanNR` run to a busy landing. -/
theorem busy_prepend {c c1 : Control} {s s1 : GalilVM} {k r k1 r1 n0 : ℕ}
    (hst : StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n0 ⟨c, s⟩ ⟨c1, s1⟩)
    (hk : k1 + r1 = k + r) (hp : position s1.right + r1 = position s.right + r)
    (hC : s1.center = s.center) (hrem : s1.remaining = s.remaining)
    (h : Busy raw P q first delay B c1 s1 k1 r1) : Busy raw P q first delay B c s k r := by
  rcases h with hA | hB'
  · obtain ⟨n1, c2, s2, c3, s3, es, c', t, n, cc, b, xs, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ := hA
    exact Or.inl ⟨n0 + n1, c2, s2, c3, s3, es, c', t, n0 + n, cc, b, xs, stepsAll_trans hst h1, h2, h3,
      h4, h5, stepsAll_trans hst h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, by rw [← hk]; exact h16,
      by omega, by rw [h18, hC], h19, h20, by rw [h21, hrem]⟩
  · obtain ⟨⟨n1, ca, sa, es, cb, sb, w1, w2, w3, w4⟩, n, c', t, hrun, hend⟩ := hB'
    exact Or.inr ⟨⟨n0 + n1, ca, sa, es, cb, sb, stepsAll_trans hst w1, w2, w3, w4⟩, n0 + n, c', t,
      fun h => stepsAll_trans hst (hrun h), idleEnd_shift hk hp hC hrem hend⟩

/-- Prefixing a run that contains a break and a restart: a quiet end becomes a
restart end. -/
theorem result_prepend_restart {c c1 : Control} {s s1 : GalilVM} {k r k1 r1 n0 : ℕ}
    (hst : StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n0 ⟨c, s⟩ ⟨c1, s1⟩)
    (hw : BrokeAndRestarted raw P q first delay c s)
    (hk : k1 + r1 = k + r) (hp : position s1.right + r1 = position s.right + r)
    (hC : s1.center = s.center) (hrem : s1.remaining = s.remaining)
    (h : Result3 raw P q first delay B c1 s1 k1 r1) : Busy raw P q first delay B c s k r := by
  rcases h with hQ | hBusy
  · obtain ⟨es, c', t, -, hrun, -, -, hend⟩ := hQ
    exact Or.inr ⟨hw, n0 + es.length, c', t, fun h => stepsAll_trans hst (hrun h),
      idleEnd_shift hk hp hC hrem hend⟩
  · exact busy_prepend hst hk hp hC hrem hBusy

/-- Prefixing a quiet (chain-idle) segment. -/
theorem result_prepend_quiet {c c1 : Control} {s s1 : GalilVM} {k r k1 r1 : ℕ} {es0 : List Bool}
    (hseg : WatchSegE P q first delay es0 c s c1 s1)
    (hst : StepsAll (galilFrameS P q first) delay (SoundScanNR raw) es0.length ⟨c, s⟩ ⟨c1, s1⟩)
    (hk : k1 + r1 = k + r) (hp : position s1.right + r1 = position s.right + r)
    (hC : s1.center = s.center) (hrem : s1.remaining = s.remaining)
    (hlen : es0.length + r1 * delay = r * delay) (hcnt : es0.count true + r1 = r)
    (h : Result3 raw P q first delay B c1 s1 k1 r1) : Result3 raw P q first delay B c s k r := by
  rcases h with hQ | hBusy
  · obtain ⟨es, c', t, hseg', hrun, hlen', hcnt', hend⟩ := hQ
    refine Or.inl ⟨es0 ++ es, c', t, watchSegE_trans P q first delay hseg hseg', fun h => ?_, ?_, ?_,
      idleEnd_shift hk hp hC hrem hend⟩
    · have := stepsAll_trans hst (hrun h)
      rw [List.length_append]; exact this
    · rw [List.length_append, hlen']; omega
    · rw [List.count_append, hcnt']; omega
  · exact Or.inr (busy_prepend hst hk hp hC hrem hBusy)

end Ends

/-! ## 8. The idle replay with starts, breaks and restarts -/

section Construct

open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier
open PalPeg.GalilTickFun PalPeg.GalilTickFun2 PalPeg.GalilReportReplay PalPeg.GalilReplayChainSeg
  PalPeg.GalilStructuredSkeleton PalPeg.GalilReplayGeneral2 PalPeg.GalilBranchInvariants2
  PalPeg.GalilReplayGeneral PalPeg.GalilSegmentConstruct PalPeg.GalilBranchInvariants

variable {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ} {B : ℕ}

/-- **From a found tick to a busy landing.**  A surviving chain gives `ChainEnd`;
a break gives a restarted idle replay with fewer comparisons, handed to `ih`. -/
theorem found_result (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    {c c2 : Control} {s s2 : GalilVM} {k r r0 k2 m2 : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    (ih : ∀ m' < r0, ∀ (c : Control) (s : GalilVM) (k : ℕ), Entry raw delay B c s k m' →
      Result3 raw P q first delay B c s k m')
    (hidle : s.chain = .idle) (hrt : c.replaying = true)
    (hft : FoundTick P q first delay c s c2 s2)
    (hst1 : StepsAll (galilFrameS P q first) delay (SoundScanNR raw) 1 ⟨c, s⟩ ⟨c2, s2⟩)
    (hQ2 : SoundScanNR raw ⟨c2, s2⟩) (hne2 : s2.chain ≠ .idle)
    (hi2 : ScanInvariant raw (position s2.center) k2 s2.left s2.right)
    (hlive : LiveEnd raw P q first delay B cc b xs c2 s2 k2 m2)
    (hk : k2 + m2 = k + r) (hp : position s2.right + m2 = position s.right + r)
    (hC : s2.center = s.center) (hrem : s2.remaining = s.remaining) (hmr : m2 ≤ r) (hrr0 : r ≤ r0)
    (hcen : GalilScaffoldInputTrace.Represents s.center.head raw ∧ s.center.head.focus ≠ none) :
    Busy raw P q first delay B c s k r := by
  rcases hlive with hA | hB'
  · obtain ⟨es, c', t, hseg, -, hm', hc', hr', hrep', hpart', hBt, hM', hi', hpos', hC', hfr', hrem'⟩ :=
      hA
    obtain ⟨n, hst⟩ := replayChainSeg_stepsAll raw P hP hP' q first delay hseg (position s2.center) k2
      hi2 hQ2
    exact Or.inl ⟨0, c, s, c2, s2, es, c', t, 1 + n, cc, b, xs,
      .zero _ (GalilReplaySegment.soundScanNR_replaying raw hrt), hidle, hrt, hft, hseg,
      stepsAll_trans hst1 hst, replayChainSeg_chain P q first delay hseg hne2, hm', hc', hr', hrep',
      replayChainSeg_ne_idle P q first delay hseg hne2, hpart', hBt, hM',
      by rw [← hk]; exact hi', by omega, by rw [hC', hC], hfr', replayRest_of_reset hrep',
      by rw [hrem', hrem]⟩
  · obtain ⟨es, c', t, m', hseg, hlt, hm', hc', hr', hrep', hidle', hsr', hM', hi', hrad', hpos', hC',
      hfr', hrem', hbd', -⟩ := hB'
    obtain ⟨n, hst⟩ := replayChainSeg2_stepsAll raw hP hP' hseg (position s2.center) k2 hi2 hQ2
    have hres := ih m' (by omega) c' t (k2 + (m2 - m'))
      ⟨hm', hc', hr', hrep', hidle', hsr', hM', hi', hfr', hrad', hbd',
        by rw [hC', hC]; exact hcen.1, by rw [hC', hC]; exact hcen.2⟩
    exact result_prepend_restart (stepsAll_trans hst1 hst)
      ⟨1, c2, s2, es, c', t, hst1, hseg, hne2, hidle'⟩ (by omega) (by omega) (by rw [hC', hC])
      (by rw [hrem', hrem]) hres

end Construct

section Countdown

open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier
open PalPeg.GalilTickFun PalPeg.GalilTickFun2 PalPeg.GalilReportReplay PalPeg.GalilReplayChainSeg
  PalPeg.GalilStructuredSkeleton PalPeg.GalilReplayGeneral2 PalPeg.GalilBranchInvariants2
  PalPeg.GalilReplayGeneral PalPeg.GalilSegmentConstruct PalPeg.GalilBranchInvariants

variable {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ} {B : ℕ}

/-- The countdown of an idle replay stretch: either it reaches the comparison
with the chain idle, or the search reports `found` and the run is busy. -/
theorem idle_countdown3 (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hshape : GalilWatchOkInst.StartShape P) (hbudget : ReplayBudget raw P delay) (hrs : RestartShape P)
    (hBl : B < (encoded raw).length) {r : ℕ}
    (ih : ∀ m' < r, ∀ (c : Control) (s : GalilVM) (k : ℕ), Entry raw delay B c s k m' →
      Result3 raw P q first delay B c s k m') :
    ∀ (j : ℕ) (c : Control) (s : GalilVM) (k m : ℕ), m + 1 ≤ r → c.mode = .scan →
      c.replaying = true →
      c.clock = j + 1 → s.chain = ChainVM.idle → SearchReady (searchLens.get s) →
      s.replay = ofNat (m+1) → MInv raw c s →
      ScanInvariant raw (position s.center) k s.left s.right → Frontier s →
      RadiusRep s.radius k → Bnd B s →
      (GalilScaffoldInputTrace.Represents s.center.head raw ∧ s.center.head.focus ≠ none) →
      (∃ (c1 : Control) (t : GalilVM),
        WatchSegE P q first delay (List.replicate j false) c s c1 t ∧
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) j ⟨c, s⟩ ⟨c1, t⟩ ∧
        c1.mode = c.mode ∧ c1.replaying = c.replaying ∧ c1.clock = 1 ∧
        t.chain = ChainVM.idle ∧ SearchReady (searchLens.get t) ∧
        t.left = s.left ∧ t.right = s.right ∧ t.center = s.center ∧
        t.replay = s.replay ∧ t.remaining = s.remaining ∧ t.radius = s.radius) ∨
      Busy raw P q first delay B c s k (m+1) := by
  intro j
  induction j with
  | zero =>
    intro c s k m _ hm hr hc hidle hsr _ _ _ _ _ _ _
    exact Or.inl ⟨c, s, .stop _ _, .zero _ (GalilReplaySegment.soundScanNR_replaying raw hr),
      rfl, rfl, hc, hidle, hsr, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ j ihj =>
    intro c s k m hmr hm hr hc hidle hsr hrep hM hi hfr hrad hbd hcen
    obtain ⟨v, hv⟩ := hsearch s hsr false
    have hclt : 1 < c.clock := by omega
    by_cases hf : v.search.mode = .found
    · obtain ⟨s', hb, hch', hl', hr', hC', hrep', hget'⟩ :=
        background_found_step P q first s hidle hv hf
      have hfld := backgroundS_fields P q first hb
      have hrem' : s'.remaining = s.remaining := hfld.2.2.2.2.2.2.2.2.1
      have hrad' : s'.radius = s.radius := hfld.2.2.2.2.2.1
      obtain ⟨n, hn, ha, hpl, -⟩ := hshape s false v hidle hsr hv hf
      obtain ⟨xs, b, hsplit⟩ := stream_split hpl hn
      obtain ⟨E, lim, hE1, hlimF, hlimT, hRE, hwin, hbrk⟩ :=
        window_of_found hbudget c s false v k (m+1) n xs b hm hr hidle hsr hv hf hM hi hrad hrep
          (Nat.succ_pos m) hfr ha hn hpl hsplit
      have hBeq : position s.right + (m+1) = B := hbd (m+1) hrep
      have hpart0 : ChainW raw (position s'.center) E (position s'.right)
          (budOf delay E {c with clock := c.clock - 1} s') lim (P.centre s) b xs s'.chain := by
        rw [hch', hC', hr']
        refine chainW_start ⟨hcen.1, hcen.2, rfl⟩ hrad hi.rightPos.symm ha hpl hsplit hwin
          (fun hl => ?_)
        have h1 := (hbrk hl).2.2
        unfold budOf; rw [hr']; simp only; omega
      have hlive := chain_runW raw P q first delay B E lim (P.centre s) b xs hex hd hrs hBl (by omega)
        (fun h => by rw [← hBeq]; exact hlimF h) (fun h => by rw [← hBeq]; exact hlimT h)
        (m+1) {c with clock := c.clock - 1} s' k hm (by simp; omega) (by simpa using hr)
        (fun h => absurd h (Nat.succ_ne_zero m)) (by rw [hrep', hrep]) (bnd_congr hr' hrep' hbd) hpart0
        (by rw [hr']; omega) (by rw [hC']; exact fun h => ⟨(hbrk h).1, (hbrk h).2.1⟩)
        (minv_same rfl hr' hC' hrep' hM) (by rw [hl', hr', hC']; exact hi) (frontier_congr hr' hrep' hfr)
        (by rw [hrad']; exact hrad)
      have hQ : SoundScanNR raw ⟨{c with clock := c.clock - 1}, s'⟩ :=
        GalilReplaySegment.soundScanNR_replaying raw hr
      exact Or.inr <| found_result hP hP' ih hidle hr
        (.bg c s s' hm hr hclt hidle hb (by rw [hget']; exact hf))
        (.succ (GalilReplaySegment.soundScanNR_replaying raw hr)
          (.scan_count c s s' hm (Or.inl hr) hclt hb) (.zero _ hQ))
        hQ (by rw [hch']; exact chainStart_ne_idle _ _ _ _ _) (by rw [hl', hr', hC']; exact hi) hlive
        rfl (by rw [hr']) hC' hrem' le_rfl hmr hcen
    · obtain ⟨s', hb, hch', hl', hr', hC', hrep', hget'⟩ :=
        idle_background_exists P q first s hidle hv hf
      have hsr' : SearchReady (searchLens.get s') := by rw [hget']; exact hpres s false v hsr hv
      have hrem' : s'.remaining = s.remaining :=
        (backgroundS_fields P q first hb).2.2.2.2.2.2.2.2.1
      have hrad' : s'.radius = s.radius := (backgroundS_fields P q first hb).2.2.2.2.2.1
      have hQ' : SoundScanNR raw ⟨{c with clock := c.clock - 1}, s'⟩ :=
        GalilReplaySegment.soundScanNR_replaying raw hr
      have hst1 : StepsAll (galilFrameS P q first) delay (SoundScanNR raw) 1 ⟨c, s⟩
          ⟨{c with clock := c.clock - 1}, s'⟩ :=
        .succ (GalilReplaySegment.soundScanNR_replaying raw hr)
          (.scan_count c s s' hm (Or.inl hr) hclt hb) (.zero _ hQ')
      rcases ihj {c with clock := c.clock - 1} s' k m hmr hm hr (by simp; omega) hch' hsr'
          (by rw [hrep', hrep]) (minv_same rfl hr' hC' hrep' hM) (by rw [hl', hr', hC']; exact hi)
          (frontier_congr hr' hrep' hfr) (by rw [hrad']; exact hrad) (bnd_congr hr' hrep' hbd)
          (by rw [hC']; exact hcen) with hA | hB'
      · obtain ⟨c1, t, hseg, hst, hm1, hr1, hc1, hidle1, hsr1, hl1, hrr1, hC1, hrp1, hrem1,
          hrd1⟩ := hA
        exact Or.inl ⟨c1, t, .countR c s s' hm hr hclt hidle hb hseg,
          .succ (GalilReplaySegment.soundScanNR_replaying raw hr)
            (.scan_count c s s' hm (Or.inl hr) hclt hb) hst,
          hm1, hr1, hc1, hidle1, hsr1, by rw [hl1, hl'], by rw [hrr1, hr'], by rw [hC1, hC'],
          by rw [hrp1, hrep'], by rw [hrem1, hrem'], by rw [hrd1, hrad']⟩
      · exact Or.inr (busy_prepend hst1 rfl (by rw [hr']) hC' hrem' hB')

end Countdown

section Compare

open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier
open PalPeg.GalilTickFun PalPeg.GalilTickFun2 PalPeg.GalilReportReplay PalPeg.GalilReplayChainSeg
  PalPeg.GalilStructuredSkeleton PalPeg.GalilReplayGeneral2 PalPeg.GalilBranchInvariants2
  PalPeg.GalilReplayGeneral PalPeg.GalilSegmentConstruct PalPeg.GalilBranchInvariants

variable {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ} {B : ℕ}

/-- The comparison of an idle replay stretch: quiet (the chain stays idle), or
the search reports `found` and the chain starts with this comparison's credit. -/
theorem idle_compare3 (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hshape : GalilWatchOkInst.StartShape P) (hbudget : ReplayBudget raw P delay) (hrs : RestartShape P)
    (hBl : B < (encoded raw).length) {r : ℕ}
    (ih : ∀ m' < r, ∀ (c : Control) (s : GalilVM) (k : ℕ), Entry raw delay B c s k m' →
      Result3 raw P q first delay B c s k m')
    (c : Control) (s : GalilVM) (k m : ℕ) (hmr : m + 1 ≤ r)
    (hm : c.mode = .scan) (hr : c.replaying = true) (hc : c.clock = 1)
    (hidle : s.chain = ChainVM.idle) (hsr : SearchReady (searchLens.get s))
    (hM : MInv raw c s) (hi : ScanInvariant raw (position s.center) k s.left s.right)
    (hrp : s.replay = ofNat (m+1)) (hfr : Frontier s) (hrad : RadiusRep s.radius k)
    (hbd : Bnd B s)
    (hcen : GalilScaffoldInputTrace.Represents s.center.head raw ∧ s.center.head.focus ≠ none) :
    (∃ (c1 : Control) (u : GalilVM),
      WatchSegE P q first delay [true] c s c1 u ∧
      StepsAll (galilFrameS P q first) delay (SoundScanNR raw) 1 ⟨c, s⟩ ⟨c1, u⟩ ∧
      c1.mode = .scan ∧ c1.clock = delay ∧ c1.replaying = decide (0 < m) ∧
      u.chain = ChainVM.idle ∧ SearchReady (searchLens.get u) ∧ MInv raw c1 u ∧
      ScanInvariant raw (position u.center) (k+1) u.left u.right ∧
      u.replay = ofNat m ∧ position u.right = position s.right + 1 ∧
      u.center = s.center ∧ Frontier u ∧ u.remaining = s.remaining ∧
      RadiusRep u.radius (k+1) ∧ Bnd B u) ∨
    Busy raw P q first delay B c s k (m+1) := by
  classical
  have hbound : position s.right + (m+1) ≤ 2 * arrived s.right := hfr (m+1) hrp
  have hav : canRight s.right := GalilReplaySegment.canRight_of_frontier (Nat.succ_pos m) hbound
  have hmatch : read (left s.left) = read (right s.right) := replay_match_of_minv hM hr hav hi
  have hpos : position (right s.right) = position s.right + 1 :=
    right_position s.right hav (represented_position _ raw hi.rightRep hi.rightPresent).1
  have hBeq : position s.right + (m+1) = B := hbd (m+1) hrp
  obtain ⟨vq, hq⟩ := hsearch s hsr true
  by_cases hf : vq.search.mode = .found
  · -- the comparison starts the chain
    obtain ⟨n, hn, ha, hpl, -⟩ := hshape s true vq hidle hsr hq hf
    obtain ⟨xs, b, hsplit⟩ := stream_split hpl hn
    obtain ⟨E, lim, hE1, hlimF, hlimT, hRE, hwin, hbrk⟩ :=
      window_of_found hbudget c s true vq k (m+1) n xs b hm hr hidle hsr hq hf hM hi hrad hrp
        (Nat.succ_pos m) hfr ha hn hpl hsplit
    have hpart0 : ChainW raw (position s.center) E (position s.right)
        ((E - position s.right) * (delay - 1)) lim (P.centre s) b xs
        (chainStart (vq.dp.config.tapes 11) (P.centre s) (P.place s) s.center s.radius) :=
      chainW_start ⟨hcen.1, hcen.2, rfl⟩ hrad hi.rightPos.symm ha hpl hsplit hwin
        (fun hl => (hbrk hl).2.2)
    obtain ⟨z, hch, hz⟩ := chainW_matched hpart0 (by omega) hRE
    have hnez : z ≠ ChainVM.idle := chainW_ne_idle hz
    set vs : ScanVM := ⟨left s.left, right s.right, z⟩ with hvsdef
    have hmt : (galilFrame P q first).matched (scanLens.set s vs) := hmatch
    set u : GalilVM := replayDec true (afterCompare s vs vq) with hudef
    set o : Bool := if P.onLetter u then decide (P.leftFirst u) else c.output with hodef
    have ho : refresh (galilFrame P q first) u c.output o := by
      refine ⟨fun hl => ?_, fun hl => ?_⟩
      · have hl' : P.onLetter u := hl
        show (if P.onLetter u then decide (P.leftFirst u) else c.output) = true ↔ P.leftFirst u
        rw [if_pos hl']; exact decide_eq_true_iff
      · have hl' : ¬ P.onLetter u := hl
        show (if P.onLetter u then decide (P.leftFirst u) else c.output) = c.output
        rw [if_neg hl']
    have hurep : u.replay = ofNat m := by
      rw [hudef, replayDec_true_replay, afterCompare_replay, hrp, dec_ofNat_succ]
    have hflag : (!P.replayExhausted u) = decide (0 < m) := by
      rw [hex, hurep]
      cases m with
      | zero => rw [(zero_ofNat_iff 0).2 rfl]; simp
      | succ k => rw [zero_ofNat_succ k]; simp
    have hiu : ScanInvariant raw (position u.center) (k+1) u.left u.right := by
      have h0 := matched_invariant' raw vq (vs := vs) rfl rfl hmatch hav hi
      rw [hudef, replayDec_left, replayDec_right, replayDec_center, afterCompare_center]
      exact h0
    have hMu : MInv raw {c with clock := delay, output := o, replaying := !P.replayExhausted u} u :=
      minv_matchR P hex o delay hr rfl hav hi hM
    have hneu : u.chain ≠ .idle := by rw [hudef, replayDec_chain, afterCompare_chain]; exact hnez
    have hur : u.right = right s.right := by rw [hudef, replayDec_right, afterCompare_right]
    have hCu : u.center = s.center := by rw [hudef, replayDec_center, afterCompare_center]
    have hposu : position u.right = position s.right + 1 := by rw [hur]; exact hpos
    have hpu : ChainW raw (position u.center) E (position u.right)
        (budOf delay E {c with clock := delay, output := o, replaying := !P.replayExhausted u} u)
        lim (P.centre s) b xs u.chain := by
      have e : budOf delay E {c with clock := delay, output := o, replaying := !P.replayExhausted u} u =
          (E - position s.right) * (delay - 1) + 1 := by
        unfold budOf; rw [hposu]
        show delay + (E - (position s.right + 1)) * (delay - 1) = _
        have := bud_arith delay (E - (position s.right + 1)) hd
        rw [show E - (position s.right + 1) + 1 = E - position s.right from by omega] at this
        omega
      rw [e, hposu, hCu, hudef, replayDec_chain, afterCompare_chain]
      exact hz
    have hbdu : Bnd B u := by
      intro m' hm'
      have hmm : m' = m := (ofNat_inj (hurep.symm.trans hm')).symm
      subst hmm
      rw [hur, hpos]; omega
    have hfru : Frontier u := by
      intro m' hm'
      have hmm : m' = m := (ofNat_inj (hurep.symm.trans hm')).symm
      subst hmm
      rw [hur]
      exact right_frontier_step s.right m' hbound
    have hradu : RadiusRep u.radius (k+1) := by
      rw [hudef, replayDec_radius, afterCompare_radius]; exact radius_rep_inc hrad
    have hQu : SoundScanNR raw
        ⟨{c with clock := delay, output := o, replaying := !P.replayExhausted u}, u⟩ :=
      fun _ _ => outputRel_of_refresh' raw P hP hP' q first u c.output o hiu ho _ rfl
    have hlive := chain_runW raw P q first delay B E lim (P.centre s) b xs hex hd hrs hBl (by omega)
      (fun h => by rw [← hBeq]; exact hlimF h) (fun h => by rw [← hBeq]; exact hlimT h)
      m {c with clock := delay, output := o, replaying := !P.replayExhausted u} u (k+1) hm hd hflag
      (fun _ => rfl) hurep hbdu hpu (by rw [hposu]; exact hRE)
      (by rw [hCu]; exact fun h => ⟨(hbrk h).1, (hbrk h).2.1⟩) hMu hiu hfru hradu
    have ht := scan_match_found_S' P q first delay c s vs vq o hm (Or.inl hr) hc hidle rfl rfl hmt
      hq hf hch (by rw [hr]; exact ho)
    rw [hr] at ht
    exact Or.inr <| found_result hP hP' ih hidle hr
      (.cmp c s vs vq o hm hr hc hav hidle rfl rfl hmt hq hf hch ho)
      (.succ (GalilReplaySegment.soundScanNR_replaying raw hr) (by simpa using ht) (.zero _ hQu))
      hQu hneu hiu hlive (by omega) (by rw [hposu]; omega) hCu rfl (by omega) hmr hcen
  · -- a quiet comparison
    set vs : ScanVM := ⟨left s.left, right s.right, ChainVM.idle⟩ with hvsdef
    have hmt : (galilFrame P q first).matched (scanLens.set s vs) := hmatch
    set u : GalilVM := replayDec true (afterCompare s vs vq) with hudef
    set o : Bool := if P.onLetter u then decide (P.leftFirst u) else c.output with hodef
    have ho : refresh (galilFrame P q first) u c.output o := by
      refine ⟨fun hl => ?_, fun hl => ?_⟩
      · have hl' : P.onLetter u := hl
        show (if P.onLetter u then decide (P.leftFirst u) else c.output) = true ↔ P.leftFirst u
        rw [if_pos hl']; exact decide_eq_true_iff
      · have hl' : ¬ P.onLetter u := hl
        show (if P.onLetter u then decide (P.leftFirst u) else c.output) = c.output
        rw [if_neg hl']
    have hurep : u.replay = ofNat m := by
      rw [hudef, replayDec_true_replay, afterCompare_replay, hrp, dec_ofNat_succ]
    have hflag : (!P.replayExhausted u) = decide (0 < m) := by
      rw [hex, hurep]
      cases m with
      | zero => rw [(zero_ofNat_iff 0).2 rfl]; simp
      | succ k => rw [zero_ofNat_succ k]; simp
    have hiu : ScanInvariant raw (position u.center) (k+1) u.left u.right := by
      have h0 := matched_invariant' raw vq (vs := vs) rfl rfl hmatch hav hi
      rw [hudef, replayDec_left, replayDec_right, replayDec_center, afterCompare_center]
      exact h0
    have hur : u.right = right s.right := by rw [hudef, replayDec_right, afterCompare_right]
    refine Or.inl ⟨{c with clock := delay, output := o, replaying := !P.replayExhausted u}, u,
      .matchIdleR c s vs vq o hm hr hc hav hidle rfl rfl rfl hmt hq hf ho (.stop _ _), ?_,
      hm, rfl, hflag, ?_, ?_, ?_, hiu, hurep, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have ht := scan_match_idle_S' P q first delay c s vs vq o hm (Or.inl hr) hc hidle rfl rfl rfl
        hmt hq hf (by rw [hr]; exact ho)
      rw [hr] at ht
      exact .succ (GalilReplaySegment.soundScanNR_replaying raw hr) (by simpa using ht)
        (.zero _ (fun _ _ => outputRel_of_refresh' raw P hP hP' q first u c.output o hiu ho _ rfl))
    · rw [hudef, replayDec_chain, afterCompare_chain]
    · have hgetU : searchLens.get u = vq := by rw [hudef, replayDec_search]; rfl
      rw [hgetU]; exact hpres s true vq hsr hq
    · exact minv_matchR P hex o delay hr rfl hav hi hM
    · rw [hur]; exact hpos
    · rw [hudef, replayDec_center, afterCompare_center]
    · intro m' hm'
      have hmm : m' = m := (ofNat_inj (hurep.symm.trans hm')).symm
      subst hmm
      rw [hur]
      exact right_frontier_step s.right m' hbound
    · rw [hudef]; rfl
    · rw [hudef, replayDec_radius, afterCompare_radius]; exact radius_rep_inc hrad
    · intro m' hm'
      have hmm : m' = m := (ofNat_inj (hurep.symm.trans hm')).symm
      subst hmm
      rw [hur, hpos]; omega

end Compare

section Main

open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier
open PalPeg.GalilTickFun PalPeg.GalilTickFun2 PalPeg.GalilReportReplay PalPeg.GalilReplayChainSeg
  PalPeg.GalilStructuredSkeleton PalPeg.GalilReplayGeneral2 PalPeg.GalilBranchInvariants2
  PalPeg.GalilReplayGeneral PalPeg.GalilSegmentConstruct PalPeg.GalilBranchInvariants

variable {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ} {B : ℕ}

/-- **The idle replay with chain starts, breaks and restarts**, by strong
induction on the comparisons left (a break always spends one). -/
theorem replay_construct3 (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hshape : GalilWatchOkInst.StartShape P) (hbudget : ReplayBudget raw P delay)
    (hrs : RestartShape P) (hBl : B < (encoded raw).length) :
    ∀ (r : ℕ) (c : Control) (s : GalilVM) (k : ℕ), Entry raw delay B c s k r →
      Result3 raw P q first delay B c s k r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro c s k hE
    obtain ⟨hm, hc, hrp, hrep, hidle, hsr, hM, hi, hfr, hrad, hbd, hcen1, hcen2⟩ := hE
    cases r with
    | zero =>
      have hrf : c.replaying = false := by rw [hrp]; simp
      exact Or.inl ⟨[], c, s, .stop _ _, fun hlast => .zero _ hlast, by simp, by simp,
        ⟨hm, hc, hrf, hrep, hidle, hsr, hM, by simpa using hi, by simp, rfl, hfr,
          replayRest_of_reset hrep, rfl⟩⟩
    | succ n =>
      have hrt : c.replaying = true := by rw [hrp]; simp
      rcases idle_countdown3 (q := q) (first := first) hP hP' hex hd hsearch hpres hshape hbudget hrs
          hBl ih (delay - 1) c s k n le_rfl hm hrt (by omega) hidle hsr hrep hM hi hfr hrad hbd
          ⟨hcen1, hcen2⟩ with hA | hB1
      · obtain ⟨c1, t1, hseg1, hst1, hm1, hr1, hc1, hidle1, hsr1, hl1, hrr1, hC1, hrp1, hrem1,
          hrd1⟩ := hA
        have hm1' : c1.mode = Mode.scan := by rw [hm1, hm]
        have hr1' : c1.replaying = true := by rw [hr1, hrt]
        have hM1 : MInv raw c1 t1 := minv_same (by rw [hr1]) hrr1 hC1 hrp1 hM
        have hi1 : ScanInvariant raw (position t1.center) k t1.left t1.right := by
          rw [hl1, hrr1, hC1]; exact hi
        have hfr1 : Frontier t1 := frontier_congr hrr1 hrp1 hfr
        rcases idle_compare3 (q := q) (first := first) hP hP' hex hd hsearch hpres hshape hbudget hrs
            hBl ih c1 t1 k n le_rfl hm1' hr1' hc1 hidle1 hsr1 hM1 hi1 (by rw [hrp1, hrep]) hfr1
            (by rw [hrd1]; exact hrad) (bnd_congr hrr1 hrp1 hbd)
            (by rw [hC1]; exact ⟨hcen1, hcen2⟩) with hA2 | hB2
        · obtain ⟨c2, u, hseg2, hst2, hm2, hc2, hr2, hidle2, hsr2, hM2, hi2, hrep2, hpos2, hC2, hfr2,
            hrem2, hrad2, hbd2⟩ := hA2
          have hres := ih n (by omega) c2 u (k+1)
            ⟨hm2, hc2, hr2, hrep2, hidle2, hsr2, hM2, hi2, hfr2, hrad2, hbd2,
              by rw [hC2, hC1]; exact hcen1, by rw [hC2, hC1]; exact hcen2⟩
          have hlen : (List.replicate (delay - 1) false ++ [true]).length = delay := by
            simp; omega
          refine result_prepend_quiet (watchSegE_trans P q first delay hseg1 hseg2) ?_ (by omega)
            (by rw [hpos2, hrr1]; omega) (by rw [hC2, hC1]) (by rw [hrem2, hrem1]) ?_ ?_ hres
          · have := stepsAll_trans hst1 hst2
            rw [List.length_append, List.length_replicate]; simpa using this
          · rw [List.length_append, List.length_replicate]; simp; cases delay with
            | zero => omega
            | succ d => simp; ring
          · simp [List.count_replicate]; omega
        · exact Or.inr (busy_prepend hst1 rfl (by rw [hrr1]) hC1 hrem1 hB2)
      · exact Or.inr hB1

/-- **`replay_after_fallback_general''`.**  `replay_after_fallback_general'`
with the false `ReplaySpan` replaced by the break budget `ReplayBudget` and the
restart shape `RestartShape` (true for `restartVM`, `restartShape_sharedC`).
Branches: (i) the replay is quiet — exactly as before; (ii) the last chain
started in the replay survives to the landing (`ChainEnd`, window `B`); (iii) a
chain broke during the replay, the search restarted, and the replay continued
as an idle replay to an idle landing (`RestartEnd`). -/
theorem replay_after_fallback_general'' (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (delay : ℕ) (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hshape : GalilWatchOkInst.StartShape P) (hbudget : ReplayBudget raw P delay)
    (hrs : RestartShape P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = delay) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :
    (∃ (es : List Bool) (c' : Control) (t' : GalilVM),
      WatchSegE P q first delay es c t c' t' ∧
      (SoundScanNR raw ⟨c', t'⟩ →
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) es.length ⟨c, t⟩ ⟨c', t'⟩) ∧
      es.length = r * delay ∧ es.count true = r ∧
      position t'.right = position t.right + r ∧ t'.center = t.center ∧
      GalilReplaySegment.InvScan delay raw c' t' r) ∨
    ChainEnd raw P q first delay (position t.right + r) c t 0 r ∨
    (BrokeAndRestarted raw P q first delay c t ∧
      ∃ (n : ℕ) (c' : Control) (t' : GalilVM),
        (SoundScanNR raw ⟨c', t'⟩ →
          StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, t⟩ ⟨c', t'⟩) ∧
        position t'.right = position t.right + r ∧ t'.center = t.center ∧
        GalilReplaySegment.InvScan delay raw c' t' r) := by
  have hB : position t.right + r < (encoded raw).length := by
    have h1 := hfr r hrep
    have h2 := arrived_le_of_represents hR.2.2.2.1.rightRep
    simp only [encoded, List.length_append, List.length_singleton, pairs_length]
    omega
  have hbd : Bnd (position t.right + r) t := by
    intro m hm'
    rw [ofNat_inj (hrep.symm.trans hm')]
  rcases replay_construct3 (q := q) (first := first) hP hP' hex hd hsearch hpres hshape hbudget hrs hB r c t 0
      ⟨hm, hc, by rw [hrpl]; simp [hr0], hrep, hR.1, searchReady_of_restarted hR, hM,
        hR.2.2.2.1, hfr, hR.2.2.2.2.1, hbd, hR.2.1, hR.2.2.1⟩ with hQ | hBusy
  · obtain ⟨es, c', t', hseg, hst, hlen, hcnt, hm', hc', hr', hrep', hidle', hsr', hM', hi', hpos', hC',
      hfr', hrr', hrem'⟩ := hQ
    exact Or.inl ⟨es, c', t', hseg, hst, hlen, hcnt, hpos', hC',
      GalilReplaySegment.inv_after_replay delay raw c' t' r hm' hc' hr' hidle' (by simpa using hi')
        hM' hsr' hrep' (GalilReplaySegment.shiftIdle_congr hrem' hsi)⟩
  · rcases hBusy with hCh | hRs
    · exact Or.inr (Or.inl hCh)
    · obtain ⟨hw, n, c', t', hrun, hm', hc', hr', hrep', hidle', hsr', hM', hi', hpos', hC', hfr', hrr',
        hrem'⟩ := hRs
      exact Or.inr (Or.inr ⟨hw, n, c', t', hrun, hpos', hC',
        GalilReplaySegment.inv_after_replay delay raw c' t' r hm' hc' hr' hidle' (by simpa using hi')
          hM' hsr' hrep' (GalilReplaySegment.shiftIdle_congr hrem' hsi)⟩)

end Main

/-! ## 9. The first clause of `ReplayBudget` from the DP candidate -/

section CandidateWindow

open GalilScaffoldInputHead

/-- **The block agrees for four semiperiods.**  With the landing palindrome
`PalAt C R`, the DP candidate's palindrome `PalAt (C-h) h` and period `2h` on
`[C-4h, C]`, and the block read off the stream left of `C`, the input to the
right of the centre reads `bounce` up to `C + min (4h) R`. -/
theorem blockOn_of_candidate {raw : List (Fin 2)} {C R h : ℕ} {centre b : Fin 3} {xs : List (Fin 3)}
    (hh : xs.length + 1 = h) (hpal : PalAt (encoded raw) C R)
    (hpal1 : PalAt (encoded raw) (C - h) h) (hper : PeriodOn (encoded raw) (2 * h) (C - 4 * h) C)
    (hleft : ∀ i, i < h → (xs ++ [b])[i]? = (encoded raw)[C - 1 - i]?)
    (hcen : (encoded raw)[C]? = some centre) (h4 : 4 * h ≤ C) :
    BlockOn raw centre b xs (C + 1) (C + min (4 * h) R) := by
  intro j hj
  have hR := hpal.1
  have hjR : j + 1 ≤ R := by have := min_le_right (4 * h) R; omega
  have hj4 : j + 1 ≤ 4 * h := by have := min_le_left (4 * h) R; omega
  -- the palindrome at the centre
  have s1 : (encoded raw)[C + 1 + j]? = (encoded raw)[C - 1 - j]? := by
    have := Manacher.mirror_getElem? hpal (p := C + 1 + j) (by omega) (by omega)
    rw [this, show 2 * C - (C + 1 + j) = C - 1 - j from by omega]
  -- the period on the left
  have s2 : (encoded raw)[C - 1 - j]? = (encoded raw)[C - 1 - j % (2 * h)]? := by
    by_cases hlt : j < 2 * h
    · rw [Nat.mod_eq_of_lt hlt]
    · have hm : j % (2 * h) = j - 2 * h := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hm]
      have := hper (C - 1 - j) (by omega) (by omega)
      rw [this, show C - 1 - j + 2 * h = C - 1 - (j - 2 * h) from by omega]
  have hi2 : j % (2 * h) < 2 * h := Nat.mod_lt _ (by omega)
  set i := j % (2 * h) with hidef
  -- the block
  have s3 : (encoded raw)[C - 1 - i]? = (GalilScaffoldChainSweep.bounce centre b xs)[i]? := by
    unfold GalilScaffoldChainSweep.bounce
    have hlen1 : (xs ++ [b]).length = h := by simp; omega
    by_cases hih : i < h
    · rw [List.getElem?_append_left (by omega), hleft i hih]
    · rw [List.getElem?_append_right (by omega), hlen1]
      have hmir : (encoded raw)[C - 1 - i]? = (encoded raw)[C + 1 + i - 2 * h]? := by
        have := hpal1.2.2 (i + 1 - h) (by omega)
        rw [show C - h - (i + 1 - h) = C - 1 - i from by omega,
          show C - h + (i + 1 - h) = C + 1 + i - 2 * h from by omega] at this
        exact this
      rw [hmir]
      by_cases hlast : i - h < xs.length
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_reverse hlast]
        have := hleft (xs.length - 1 - (i - h)) (by omega)
        rw [List.getElem?_append_left (by omega)] at this
        rw [this, show C - 1 - (xs.length - 1 - (i - h)) = C + 1 + i - 2 * h from by omega]
      · rw [List.getElem?_append_right (by simp; omega)]
        have hi' : i - h - xs.reverse.length = 0 := by simp; omega
        rw [hi', show C + 1 + i - 2 * h = C from by omega, hcen]
        rfl
  rw [hh, s1, s2, s3]

/-- Consequently a mispredicted place of the landing palindrome lies beyond
four semiperiods — the first clause of `ReplayBudget`. -/
theorem mispredicted_beyond {raw : List (Fin 2)} {C R h : ℕ} {centre b : Fin 3} {xs : List (Fin 3)}
    (hh : xs.length + 1 = h) (hpal : PalAt (encoded raw) C R)
    (hpal1 : PalAt (encoded raw) (C - h) h) (hper : PeriodOn (encoded raw) (2 * h) (C - 4 * h) C)
    (hleft : ∀ i, i < h → (xs ++ [b])[i]? = (encoded raw)[C - 1 - i]?)
    (hcen : (encoded raw)[C]? = some centre) (h4 : 4 * h ≤ C)
    (j : ℕ) (hj1 : C + 1 ≤ j) (hjR : j ≤ C + R) (hmis : Mispredicted raw centre b xs (C + 1) j) :
    C + 4 * h < j := by
  by_contra hle
  have hw := blockOn_of_candidate hh hpal hpal1 hper hleft hcen h4 (j - (C + 1))
    (by have := le_min (show j ≤ C + 4 * h by omega) hjR; omega)
  apply hmis
  rw [show C + 1 + (j - (C + 1)) = j from by omega] at hw
  exact hw

/-- **The place-level form.**  For a represented centre with a DP candidate `h`
on its left window and the block cut from its stream, every mispredicted place
of a palindrome of radius `R` about the centre lies beyond `C + 4h`. -/
theorem mispredicted_beyond_candidate (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    (span lower h R : ℕ) (centre b : Fin 3) (xs : List (Fin 3))
    (hc : GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span + 1)) lower h)
    (hsplit : (GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).tail.take h = xs ++ [b])
    (hcen : (encoded ((a :: ls).reverse ++ rs ++ q))[
      position (represent ⟨a :: ls, gap⟩ (rs.map some) q)]? = some centre)
    (hpal : PalAt (encoded ((a :: ls).reverse ++ rs ++ q))
      (position (represent ⟨a :: ls, gap⟩ (rs.map some) q)) R) :
    ∀ j, position (represent ⟨a :: ls, gap⟩ (rs.map some) q) + 1 ≤ j →
      j ≤ position (represent ⟨a :: ls, gap⟩ (rs.map some) q) + R →
      Mispredicted ((a :: ls).reverse ++ rs ++ q) centre b xs
        (position (represent ⟨a :: ls, gap⟩ (rs.map some) q) + 1) j →
      position (represent ⟨a :: ls, gap⟩ (rs.map some) q) + 4 * h < j := by
  have hC := position_represent a ls gap (rs.map some) q
  have hpals := candidate_palAt a ls rs q gap span lower h hc
  have hperC := candidate_periodOn a ls rs q gap span lower h hc
  obtain ⟨_, hn, _, _⟩ := hc
  have hn' : 4 * h + 1 ≤ min (span + 1) (GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).length := by
    simpa only [List.length_take] using hn
  have hTlen : 4 * h + 1 ≤ (GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).length := by omega
  have hlen : xs.length + 1 = h := by
    have := congrArg List.length hsplit
    rw [List.length_take, List.length_tail] at this
    simp at this; omega
  intro j hj1 hjR hmis
  refine mispredicted_beyond hlen hpal hpals.1 hperC ?_ hcen (by omega) j hj1 hjR hmis
  intro i hi
  rw [← hsplit, List.getElem?_take_of_lt hi, List.getElem?_tail,
    stream_index a ls rs q gap (i + 1) (by omega), hC]
  congr 1
  omega

#print axioms blockOn_of_candidate
#print axioms mispredicted_beyond
#print axioms mispredicted_beyond_candidate

end CandidateWindow

#print axioms maximal_window
#print axioms coreX_good
#print axioms coreX_break
#print axioms coreX_last
#print axioms chainW_step
#print axioms chainW_matched
#print axioms chainW_break
#print axioms chainW_start
#print axioms replayChainSeg2_stepsAll
#print axioms replayChainSeg2_minv
#print axioms restartShape_sharedC
#print axioms chain_countdownW
#print axioms forced_compare
#print axioms chain_compareW
#print axioms chain_breakW
#print axioms chain_runW
#print axioms window_of_found
#print axioms found_result
#print axioms idle_countdown3
#print axioms idle_compare3
#print axioms replay_construct3
#print axioms replay_after_fallback_general''

end PalPeg.GalilReplaySpan
