import PalPeg.GalilBranchInvariants
import PalPeg.GalilScaffoldTopGuards

/-!
# The shift's semiperiod `h` against the DP's OUTPUT cursor

`beginShiftVM'` pins the shift's semiperiod to `periodLength w`, the number of
cells of the watching chain's period tape; the DP delivers its candidate as the
OUTPUT cursor `pos 11` (`search_result_at_tick`).  This module closes the gap
between the two by supplying the missing **period-tape length invariant**:

* `cells v = v.left.length + v.right.length + 1` is the cell count of a period
  tape, and `periodLength w + 1 = cells w.machine.control.period` by definition
  (`periodLength` does not count the FRONT cell);
* `cells_consume`: under `OnBlock`, *every* `consume` — matching, turning or
  breaking — keeps the cell count fixed (`moveRight` is only ever taken off a
  non-`LAST` cell, so it never appends a blank);
* `settled_step` / `settled_steps`: from the `Back` phase on, every
  `ChainStep`/`ChainMatched`/`ChainSteps` preserves the count;
* `copy_cells`: the `Copy` phase adds exactly one cell per unary answer bit, so
  a chain started on an answer tape carrying `n` ones over the `LEFT` mark
  reaches the watch with `n+1` cells.

The arithmetic now lines up with the shape the consumers assume.  `chainStart`
lays down `FRONT c`, then one plain cell per answer bit, and finally overwrites
the last plain cell with `LAST b`: `n` bits give `n+1` cells, i.e. the centre
token *plus* the `n` semiperiod letters.  Since `periodLength` counts only the
`n` semiperiod letters (the FRONT cell is excluded, as in the Scala source) and
`pos 11 = n` (`AnswerExact`), the conclusion is

  `h = periodLength w = (denote cfg).pos 11`,

which is exactly the `hout : (denote vq.dp.config).pos 11 = h` of
`cycle_found_minv` (`PalPeg/GalilLiveCentreCycle2.lean`).  The companion
`periodLength_watchStart` (`PalPeg/GalilSearchResult.lean`) records the same
count at the *start* of the watch against `found_rounds_restart`'s
`ys.length + 1 = h_dp`.
-/

set_option autoImplicit false
namespace PalPeg.GalilShiftH

open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainInputSupply
open GalilBranchInvariants
open GalilScaffoldChainPeriod (Token)

/-! ## The cell count of a period tape -/

/-- The number of cells of a period tape.  `periodLength` is this count. -/
def cells (v : GalilScaffoldChainPeriod.Tape) : ℕ := v.left.length + v.right.length + 1

theorem periodLength_succ_eq_cells (w : GalilScaffoldChainWatch.State) :
    periodLength w + 1 = cells w.machine.control.period := rfl

theorem cells_write (v : GalilScaffoldChainPeriod.Tape) (a : Token) :
    cells (GalilScaffoldChainPeriod.write v a) = cells v := rfl

theorem cells_moveLeft (v : GalilScaffoldChainPeriod.Tape) :
    cells (GalilScaffoldChainPeriod.moveLeft v) = cells v := by
  rcases v with ⟨ls, f, rs⟩
  cases ls with
  | nil => rfl
  | cons a ls => simp only [GalilScaffoldChainPeriod.moveLeft, cells, List.length_cons]; omega

theorem cells_moveRight (v : GalilScaffoldChainPeriod.Tape) (h : v.right ≠ []) :
    cells (GalilScaffoldChainPeriod.moveRight v) = cells v := by
  rcases v with ⟨ls, f, rs⟩
  cases rs with
  | nil => exact absurd rfl h
  | cons a rs => simp only [GalilScaffoldChainPeriod.moveRight, cells, List.length_cons]; omega

theorem cells_put (v : GalilScaffoldChainPeriod.Tape) (a : Fin 3) (h : v.right = []) :
    cells (GalilScaffoldChainPeriod.put v a) = cells v + 1 := by
  rcases v with ⟨ls, f, rs⟩
  simp only at h
  subst h
  simp only [GalilScaffoldChainPeriod.put, GalilScaffoldChainPeriod.write,
    GalilScaffoldChainPeriod.moveRight, cells, List.length_cons, List.length_nil]

theorem cells_start (c : Fin 3) : cells (GalilScaffoldChainPeriod.start c) = 1 := rfl

/-! ## The missing invariant: `consume` preserves the cell count -/

/-- **The period-tape length invariant.**  On a well-formed block the head
never runs off the right end, so no `consume` ever appends a blank cell: the
cell count — and hence `periodLength` — is preserved by every consume. -/
theorem consume_of_none (s : GalilScaffoldChainConsume.State) (seen : Option (Fin 3))
    (hsym : GalilScaffoldChainConsume.symbol s.period.focus = none) :
    GalilScaffoldChainConsume.consume s seen = {s with broken := true} := by
  simp [GalilScaffoldChainConsume.consume, hsym]

theorem cells_consume (s : GalilScaffoldChainConsume.State) (seen : Option (Fin 3))
    (h : OnBlock s.period) :
    cells (GalilScaffoldChainConsume.consume s seen).period = cells s.period := by
  cases hf : s.period.focus with
  | blank =>
    rw [consume_of_none s seen (by rw [hf]; rfl)]
  | left =>
    rw [consume_of_none s seen (by rw [hf]; rfl)]
  | plain a =>
    by_cases hs : seen = some a
    · subst hs
      rw [GalilScaffoldChainConsume.plain s a hf]
      cases s.forward
      · simpa using cells_moveLeft s.period
      · simp only [if_true]
        exact cells_moveRight _ (onBlock_right_ne h (by rw [hf]; rfl))
    · rw [GalilScaffoldChainConsume.mismatch s a seen (by rw [hf]; rfl) hs]
  | first c =>
    by_cases hs : seen = some c
    · subst hs
      rw [GalilScaffoldChainConsume.first s c hf]
      exact cells_moveRight _ (onBlock_right_ne h (by rw [hf]; rfl))
    · rw [GalilScaffoldChainConsume.mismatch s c seen (by rw [hf]; rfl) hs]
  | last b =>
    by_cases hs : seen = some b
    · subst hs
      rw [GalilScaffoldChainConsume.last s b hf]
      exact cells_moveLeft _
    · rw [GalilScaffoldChainConsume.mismatch s b seen (by rw [hf]; rfl) hs]

theorem cells_verifier_consume (m : GalilScaffoldChainVerifier.State)
    (h : OnBlock m.control.period) :
    cells (GalilScaffoldChainVerifier.consume m).control.period = cells m.control.period :=
  cells_consume _ _ h

theorem cells_internal {s t : GalilScaffoldChainWatch.State}
    (h : GalilScaffoldChainWatch.Internal s t) (hb : WatchBlock s) :
    cells t.machine.control.period = cells s.machine.control.period := by
  cases h with
  | idle => rfl
  | take => exact cells_verifier_consume _ hb

theorem cells_outer {s t : GalilScaffoldChainWatch.State} {b : Bool}
    (h : GalilScaffoldChainWatch.Outer s b t) (hb : WatchBlock s) :
    cells t.machine.control.period = cells s.machine.control.period := by
  cases h with
  | idle => rfl
  | queued => rfl
  | immediate => exact cells_verifier_consume _ hb

theorem cells_break {s t : GalilScaffoldChainWatch.State} (h : BreakStep s t)
    (hb : WatchBlock s) :
    cells t.machine.control.period = cells s.machine.control.period := by
  obtain ⟨_, _, _, _, _, ht⟩ := h
  rw [ht]
  exact cells_verifier_consume _ hb

/-! ## From the `Back` phase on, the count is frozen -/

/-- The chain states past the copy walk. -/
def Settled : ChainVM → Prop
  | .idle => False
  | .copy _ _ _ _ _ _ _ => False
  | _ => True

/-- The period-tape cell count carried by a chain state. -/
def cellsOf : ChainVM → ℕ
  | .idle => 0
  | .copy _ _ _ v _ _ _ => cells v
  | .back v _ _ _ _ => cells v
  | .watch w => cells w.machine.control.period
  | .broken w => cells w.machine.control.period

theorem settled_step {x y : ChainVM} (h : ChainStep x y) (hs : Settled x) (hb : BlockInv x) :
    Settled y ∧ cellsOf y = cellsOf x := by
  cases h with
  | idle => exact hs.elim
  | brokenIdle => exact ⟨trivial, rfl⟩
  | copyBit => exact hs.elim
  | copyEnd => exact hs.elim
  | backStep v h lag margin ver hf => exact ⟨trivial, cells_moveLeft v⟩
  | backDone v h lag margin ver hf =>
      exact ⟨trivial, cells_moveRight v (onBlock_right_ne hb (isFirst_isLast hf))⟩
  | watchStep w w' hi => exact ⟨trivial, cells_internal hi hb⟩

theorem settled_matched {x y : ChainVM} (h : ChainMatched x y) (hs : Settled x)
    (hb : BlockInv x) : Settled y ∧ cellsOf y = cellsOf x := by
  cases h with
  | idle => exact hs.elim
  | copy => exact hs.elim
  | back => exact ⟨trivial, rfl⟩
  | watch w w' ho => exact ⟨trivial, cells_outer ho hb⟩
  | breaks w w' hbr => exact ⟨trivial, cells_break hbr hb⟩

theorem settled_tick {a : Bool} {x z : ChainVM} (h : ChainTick a x z) (hs : Settled x)
    (hb : BlockInv x) : Settled z ∧ cellsOf z = cellsOf x := by
  obtain ⟨y, hstep, hm⟩ := h
  obtain ⟨hsy, hcy⟩ := settled_step hstep hs hb
  cases a with
  | false => rw [hm]; exact ⟨hsy, hcy⟩
  | true =>
    obtain ⟨hsz, hcz⟩ := settled_matched hm hsy (blockInv_step hstep hb)
    exact ⟨hsz, hcz.trans hcy⟩

theorem settled_steps {n : ℕ} {x z : ChainVM} (h : ChainSteps n x z) (hs : Settled x)
    (hb : BlockInv x) : Settled z ∧ cellsOf z = cellsOf x := by
  induction h with
  | zero => exact ⟨hs, rfl⟩
  | succ hstep _ ih =>
    obtain ⟨hsy, hcy⟩ := settled_step hstep hs hb
    obtain ⟨hsz, hcz⟩ := ih hsy (blockInv_step hstep hb)
    exact ⟨hsz, hcz.trans hcy⟩

/-! ## The copy walk adds one cell per answer bit -/

/-- **The copy accounting.**  A chain in `Copy` with `n` unary answer bits
ahead reaches any settled state with exactly `n` further period cells: `n`
`copyBit` ticks each append one cell, and the terminal `copyEnd` only
overwrites the last one with the `LAST` mark. -/
theorem copy_cells : ∀ (N : ℕ) {t : GalilScaffoldTape.Tape} {hc : Counter}
    {p : GalilScaffoldPlace.Place} {v : GalilScaffoldChainPeriod.Tape} {n : ℕ}
    {lag margin : Counter} {ver : PlaceHead} {z : ChainVM},
    CopyInv t hc p v n → ChainSteps N (.copy t hc p v lag margin ver) z → Settled z →
    cellsOf z = cells v + n := by
  intro N
  induction N with
  | zero =>
    intro t hc p v n lag margin ver z hi hs hz
    cases hs
    exact hz.elim
  | succ N ih =>
    intro t hc p v n lag margin ver z hi hs hz
    cases hs with
    | succ hstep hrest =>
      cases hstep with
      | copyBit t hc p v lag margin ver a one legal present =>
        cases n with
        | zero =>
          rw [answerAhead_zero hi.1] at one
          exact absurd one (by decide)
        | succ m =>
          have hres := ih (copyInv_step hi a) hrest hz
          rw [cells_put v a hi.2.2.1.1] at hres
          omega
      | copyEnd t hc p v lag margin ver b hleft hpos hv =>
        cases n with
        | zero =>
          have hblk : OnBlock (GalilScaffoldChainPeriod.write v (Token.last b)) :=
            onBlock_write_last hi.2.2.1 b hv
          have hc2 := (settled_steps hrest trivial hblk).2
          rw [hc2]
          exact cells_write v _
        | succ m =>
          rw [answerAhead_succ_focus hi.1] at hleft
          exact absurd hleft (by decide)

/-! ## The chain started at the found search -/

/-- The unary DP answer exactly as `Chain.start` finds it: `n` ones above the
`LEFT` mark, nothing below it, the head on the topmost one. -/
def AnswerExact (t : GalilScaffoldTape.Tape) (n : ℕ) : Prop :=
  t.focus :: t.left = List.replicate n 8 ++ [4]

theorem answerExact_ahead {t : GalilScaffoldTape.Tape} {n : ℕ} (h : AnswerExact t n) :
    AnswerAhead t n := ⟨[], h⟩

/-- The OUTPUT cursor reads off the exact answer: `pos 11 = n`. -/
theorem answerExact_head {t : GalilScaffoldTape.Tape} {n : ℕ} (h : AnswerExact t n) :
    GalilScaffoldTape.head t = n := by
  have hl := congrArg List.length h
  simp only [List.length_cons, List.length_append, List.length_replicate] at hl
  simpa [GalilScaffoldTape.head] using hl

/-- **The period tape of the chain started at a found search.**  From the
`chain.matched()` of the found tick, any settled state the chain reaches — in
particular the watch state at the terminal comparison — carries `n+1` period
cells, where `n` is the unary answer the DP wrote. -/
theorem chainStart_cells {answer : GalilScaffoldTape.Tape} {n : ℕ}
    (hans : AnswerExact answer n) (hn : 0 < n)
    (c : Fin 3) (walker : GalilScaffoldPlace.Place) (ver : PlaceHead) (radius : Counter)
    (hwalk : PlaceAhead walker n)
    {ch z : ChainVM} (hch : ChainMatched (chainStart answer c walker ver radius) ch)
    {N : ℕ} (hrun : ChainSteps N ch z) (hz : Settled z) :
    cellsOf z = n + 1 := by
  have hi : CopyInv answer reset walker (GalilScaffoldChainPeriod.start c) n :=
    ⟨answerExact_ahead hans, hwalk, onPrefix_start c, rfl, fun h0 => absurd h0 (by omega)⟩
  cases hch with
  | copy t h p v lag margin ver =>
    have hres := copy_cells N hi hrun hz
    rw [cells_start c] at hres
    omega

/-! ## Identifying the shift's `h` -/

/-- The shift entry `beginShiftVM'` pins `h` to the watching chain's
`periodLength`. -/
theorem beginShiftVM_periodLength {h : ℕ} {w : GalilScaffoldChainWatch.State} {s t : GalilVM}
    (hb : beginShiftVM h w s t) (hb' : beginShiftVM' s t) : h = periodLength w := by
  obtain ⟨w', hb2⟩ := hb'
  have hw : w = w' := ChainVM.watch.inj (hb.1.symm.trans hb2.1)
  subst hw
  have hr : GalilScaffoldCounter.ofNat h = GalilScaffoldCounter.ofNat (periodLength w) :=
    congrArg GalilVM.remaining (hb.2.symm.trans hb2.2)
  have hv := congrArg GalilScaffoldCounter.value hr
  rw [ofNat_value, ofNat_value] at hv
  exact_mod_cast hv

/-- **The shift's semiperiod against the DP's OUTPUT cursor.**  The chain
started by the found tick's `chainStart` on the DP answer tape `tapes 11`
carries `pos 11 + 1` period *cells* — i.e. `periodLength = pos 11` semiperiod
letters — all the way to the terminal comparison, and the shift entry reads its
`h` off exactly that count.  Hence

  `h = (denote cfg).pos 11`.

This is exactly the shape `pos 11 = h` assumed by `cycle_found_minv`'s `hout`
(see the module header). -/
theorem shift_h_eq_pos11 {cfg : GalilScaffoldProgram.Config 12} {n : ℕ}
    (hans : AnswerExact (cfg.tapes 11) n) (hn : 0 < n)
    (c : Fin 3) (walker : GalilScaffoldPlace.Place) (ver : PlaceHead) (radius : Counter)
    (hwalk : PlaceAhead walker n)
    {ch : ChainVM} (hch : ChainMatched (chainStart (cfg.tapes 11) c walker ver radius) ch)
    {N : ℕ} {w : GalilScaffoldChainWatch.State} (hrun : ChainSteps N ch (.watch w))
    {h : ℕ} {s t : GalilVM}
    (hb : beginShiftVM h w s t) (hb' : beginShiftVM' s t) :
    h = (GalilScaffoldProgram.denote cfg).pos 11 := by
  have hcells : cellsOf (ChainVM.watch w) = n + 1 :=
    chainStart_cells hans hn c walker ver radius hwalk hch hrun trivial
  have hpl : periodLength w + 1 = n + 1 := hcells
  have hpos : (GalilScaffoldProgram.denote cfg).pos 11 = n := answerExact_head hans
  rw [beginShiftVM_periodLength hb hb', hpos]
  omega

/-- The same statement in the `ReadOrigin` shape `cycle_found_minv` uses:
`org.interior.length + 1 = h` makes the interior length plus one equal to the
OUTPUT cursor. -/
theorem interior_eq_pos11 {cfg : GalilScaffoldProgram.Config 12} {n : ℕ}
    (hans : AnswerExact (cfg.tapes 11) n) (hn : 0 < n)
    (c : Fin 3) (walker : GalilScaffoldPlace.Place) (ver : PlaceHead) (radius : Counter)
    (hwalk : PlaceAhead walker n)
    {ch : ChainVM} (hch : ChainMatched (chainStart (cfg.tapes 11) c walker ver radius) ch)
    {N : ℕ} {w : GalilScaffoldChainWatch.State} (hrun : ChainSteps N ch (.watch w))
    {h : ℕ} {s t : GalilVM}
    (hb : beginShiftVM h w s t) (hb' : beginShiftVM' s t)
    {interior : List (Fin 2)} (hint : interior.length + 1 = h) :
    interior.length + 1 = (GalilScaffoldProgram.denote cfg).pos 11 := by
  rw [hint]
  exact shift_h_eq_pos11 hans hn c walker ver radius hwalk hch hrun hb hb'

#print axioms cells_consume
#print axioms settled_steps
#print axioms copy_cells
#print axioms chainStart_cells
#print axioms beginShiftVM_periodLength
#print axioms shift_h_eq_pos11
#print axioms interior_eq_pos11

end PalPeg.GalilShiftH
