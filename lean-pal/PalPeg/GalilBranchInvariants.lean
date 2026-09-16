import PalPeg.GalilScaffoldTopChainVM
import PalPeg.GalilScaffoldTopWatch

/-!
# Reachability invariants that make the chain's branch conditions total

`ASSEMBLY_PLAN.md`, 「分岐網羅の義務」, obligations (i) and (ii): every
`ChainStep`/`ChainMatched` constructor must be enabled from every reachable
chain state.  The two structural invariants proved here are

* `OnPrefix` / `OnBlock` on the period tape (`GalilScaffoldChainPeriod.Tape`):
  during `Copy` the tape is `FRONT` plus the letters written so far with the
  head on the last written cell (`OnPrefix`); from the endpoint marking on it
  is the whole block `FRONT c, plain ys, LAST b` with the head somewhere on it
  (`OnBlock`).  `OnBlock` is preserved by *every* `consume`, unconditionally,
  and it discharges the `∃ a, symbol … = some a` half of
  `GalilScaffoldChainWatch.Good` and of `BreakStep`.
* `AnswerAhead` / `PlaceAhead` on the unary DP answer tape and on the walker:
  `n` ones then the `LEFT` mark, and at least `n+1` letters left to read.
  Together with `OnPrefix` these make every `Copy` tick enabled and run the
  copy phase to `Back` in exactly `n+1` ticks.

The combined state predicate `BlockInv : ChainVM → Prop` is a valid `Q` for
the transfer-style lemmas: it is preserved by `ChainStep`, `ChainMatched`,
`ChainTick` and `ChainSteps`.
-/

set_option autoImplicit false
namespace PalPeg.GalilBranchInvariants

open GalilScaffoldCounter GalilScaffoldChainInputSupply
open GalilScaffoldChainPeriod (Token)

/-! ## The period block -/

/-- The decoded period block written by `Chain.start`/`stepCopy`: the front
mark, the semiperiod letters, and the tail mark. -/
def blockTokens (c b : Fin 3) (ys : List (Fin 3)) : List Token :=
  Token.first c :: (ys.map Token.plain ++ [Token.last b])

/-- Invariant of the period tape from the endpoint marking on: the tape is
exactly one block and the head is on one of its cells. -/
def OnBlock (v : GalilScaffoldChainPeriod.Tape) : Prop :=
  ∃ (c b : Fin 3) (ys : List (Fin 3)),
    v.left.reverse ++ v.focus :: v.right = blockTokens c b ys

/-- Invariant of the period tape during `Copy`: front mark plus the letters
written so far, head on the last written cell, nothing to the right. -/
def OnPrefix (v : GalilScaffoldChainPeriod.Tape) : Prop :=
  v.right = [] ∧
    ∃ (c : Fin 3) (ys : List (Fin 3)),
      v.focus :: v.left = (ys.map Token.plain).reverse ++ [Token.first c]

theorem onPrefix_start (c : Fin 3) : OnPrefix (GalilScaffoldChainPeriod.start c) :=
  ⟨rfl, c, [], rfl⟩

theorem onPrefix_put {v : GalilScaffoldChainPeriod.Tape} (h : OnPrefix v) (a : Fin 3) :
    OnPrefix (GalilScaffoldChainPeriod.put v a) := by
  obtain ⟨hr, c, ys, he⟩ := h
  rcases v with ⟨ls, f, rs⟩
  simp only at hr he
  subst hr
  refine ⟨rfl, c, ys ++ [a], ?_⟩
  simp only [GalilScaffoldChainPeriod.put, GalilScaffoldChainPeriod.moveRight,
    GalilScaffoldChainPeriod.write, List.map_append, List.reverse_append]
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]
  rw [← he]

/-- Marking the endpoint turns the copy prefix into a complete block. -/
theorem onBlock_write_last {v : GalilScaffoldChainPeriod.Tape} (h : OnPrefix v) (b : Fin 3)
    (hf : v.focus = Token.plain b) :
    OnBlock (GalilScaffoldChainPeriod.write v (Token.last b)) := by
  obtain ⟨hr, c, ys, he⟩ := h
  rcases List.eq_nil_or_concat' ys with rfl | ⟨zs, y, rfl⟩
  · rw [hf] at he
    simp at he
  · refine ⟨c, b, zs, ?_⟩
    rw [hf] at he
    simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at he
    have hl : v.left = (zs.map Token.plain).reverse ++ [Token.first c] :=
      (List.cons.inj he).2
    simp only [GalilScaffoldChainPeriod.write, hr, hl, blockTokens]
    simp

/-! ## Consequences of `OnBlock` -/

theorem onBlock_symbol {v : GalilScaffoldChainPeriod.Tape} (h : OnBlock v) :
    ∃ a : Fin 3, GalilScaffoldChainConsume.symbol v.focus = some a := by
  obtain ⟨c, b, ys, he⟩ := h
  have hm : v.focus ∈ blockTokens c b ys := by
    rw [← he]; simp
  simp only [blockTokens, List.mem_cons, List.mem_append, List.mem_map,
    List.not_mem_nil, or_false] at hm
  rcases hm with h1 | h1 | h1
  · exact ⟨c, by rw [h1]; rfl⟩
  · obtain ⟨a, _, ha⟩ := h1
    exact ⟨a, by rw [← ha]; rfl⟩
  · exact ⟨b, by rw [h1]; rfl⟩

/-- The head is on the tail mark exactly when there is nothing to its right. -/
theorem onBlock_right_ne {v : GalilScaffoldChainPeriod.Tape} (h : OnBlock v)
    (hl : GalilScaffoldChainConsume.isLast v.focus = false) : v.right ≠ [] := by
  obtain ⟨c, b, ys, he⟩ := h
  intro hr
  rw [hr] at he
  have h2 := congrArg List.reverse he
  simp only [blockTokens, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.reverse_reverse] at h2
  rw [(List.cons.inj h2).1] at hl
  exact absurd hl (by simp [GalilScaffoldChainConsume.isLast])

theorem onBlock_moveLeft {v : GalilScaffoldChainPeriod.Tape} (h : OnBlock v) :
    OnBlock (GalilScaffoldChainPeriod.moveLeft v) := by
  obtain ⟨c, b, ys, he⟩ := h
  refine ⟨c, b, ys, ?_⟩
  rcases v with ⟨ls, f, rs⟩
  cases ls with
  | nil => simpa [GalilScaffoldChainPeriod.moveLeft] using he
  | cons a ls =>
    simp only [GalilScaffoldChainPeriod.moveLeft]
    simpa using he

theorem onBlock_moveRight {v : GalilScaffoldChainPeriod.Tape} (h : OnBlock v)
    (hl : GalilScaffoldChainConsume.isLast v.focus = false) :
    OnBlock (GalilScaffoldChainPeriod.moveRight v) := by
  have hne := onBlock_right_ne h hl
  obtain ⟨c, b, ys, he⟩ := h
  refine ⟨c, b, ys, ?_⟩
  rcases v with ⟨ls, f, rs⟩
  cases rs with
  | nil => exact absurd rfl hne
  | cons a rs =>
    simp only [GalilScaffoldChainPeriod.moveRight]
    simpa using he

/-- **Unconditional preservation**: every `consume`, matching or breaking,
keeps the head on the block. -/
theorem onBlock_consume (s : GalilScaffoldChainConsume.State) (seen : Option (Fin 3))
    (h : OnBlock s.period) : OnBlock (GalilScaffoldChainConsume.consume s seen).period := by
  cases hf : s.period.focus with
  | blank =>
    simp only [GalilScaffoldChainConsume.consume, hf, GalilScaffoldChainConsume.symbol]
    exact h
  | left =>
    simp only [GalilScaffoldChainConsume.consume, hf, GalilScaffoldChainConsume.symbol]
    exact h
  | plain a =>
    by_cases hs : seen = some a
    · subst hs
      rw [GalilScaffoldChainConsume.plain s a hf]
      cases s.forward
      · simpa using onBlock_moveLeft h
      · simp only [if_true]
        exact onBlock_moveRight h (by rw [hf]; rfl)
    · rw [GalilScaffoldChainConsume.mismatch s a seen (by rw [hf]; rfl) hs]
      exact h
  | first c =>
    by_cases hs : seen = some c
    · subst hs
      rw [GalilScaffoldChainConsume.first s c hf]
      exact onBlock_moveRight h (by rw [hf]; rfl)
    · rw [GalilScaffoldChainConsume.mismatch s c seen (by rw [hf]; rfl) hs]
      exact h
  | last b =>
    by_cases hs : seen = some b
    · subst hs
      rw [GalilScaffoldChainConsume.last s b hf]
      exact onBlock_moveLeft h
    · rw [GalilScaffoldChainConsume.mismatch s b seen (by rw [hf]; rfl) hs]
      exact h

theorem onBlock_verifier_consume (m : GalilScaffoldChainVerifier.State)
    (h : OnBlock m.control.period) :
    OnBlock (GalilScaffoldChainVerifier.consume m).control.period :=
  onBlock_consume _ _ h

/-! ## The watch phase: obligation (ii) -/

/-- The block invariant on a watching chain state. -/
def WatchBlock (s : GalilScaffoldChainWatch.State) : Prop := OnBlock s.machine.control.period

theorem watchBlock_internal {s t : GalilScaffoldChainWatch.State}
    (h : GalilScaffoldChainWatch.Internal s t) (hb : WatchBlock s) : WatchBlock t := by
  cases h with
  | idle => exact hb
  | take => exact onBlock_verifier_consume _ hb

theorem watchBlock_outer {s t : GalilScaffoldChainWatch.State} {b : Bool}
    (h : GalilScaffoldChainWatch.Outer s b t) (hb : WatchBlock s) : WatchBlock t := by
  cases h with
  | idle => exact hb
  | queued => exact hb
  | immediate => exact onBlock_verifier_consume _ hb

theorem watchBlock_tick {s t : GalilScaffoldChainWatch.State} {b : Bool}
    (h : GalilScaffoldChainWatch.Tick s b t) (hb : WatchBlock s) : WatchBlock t := by
  cases h with
  | step hi ho => exact watchBlock_outer ho (watchBlock_internal hi hb)

theorem watchBlock_run {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (h : GalilScaffoldChainWatch.Run s bs t) (hb : WatchBlock s) : WatchBlock t := by
  induction h with
  | stop => exact hb
  | next ht _ ih => exact ih (watchBlock_tick ht hb)

theorem watchBlock_break {s t : GalilScaffoldChainWatch.State} (h : BreakStep s t)
    (hb : WatchBlock s) : WatchBlock t := by
  obtain ⟨_, _, _, _, _, ht⟩ := h
  rw [ht]
  exact onBlock_verifier_consume _ hb

/-- The structural half of `Good`: the verifier can move and the period
predicts a letter.  The remaining half — the input actually agreeing with the
prediction — is exactly the branch condition. -/
def WatchReady (s : GalilScaffoldChainWatch.State) : Prop :=
  GalilScaffoldChainVerifier.canRight s.machine.verifier ∧ WatchBlock s

theorem watchReady_of_good {s : GalilScaffoldChainWatch.State}
    (hg : GalilScaffoldChainWatch.Good s) (hb : WatchBlock s) : WatchReady s := ⟨hg.1, hb⟩

/-- **The branch dichotomy**: a ready watch either consumes successfully
(`Good`) or breaks (`BreakStep`'s mismatch condition).  There is no third case. -/
theorem watch_good_or_break (s : GalilScaffoldChainWatch.State) (hr : WatchReady s) :
    GalilScaffoldChainWatch.Good s ∨
      ∃ a : Fin 3,
        GalilScaffoldChainConsume.symbol s.machine.control.period.focus = some a ∧
        GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right s.machine.verifier)
          ≠ some a := by
  obtain ⟨hc, hb⟩ := hr
  obtain ⟨a, ha⟩ := onBlock_symbol hb
  by_cases hrd : GalilScaffoldInputHead.read
      (GalilScaffoldChainVerifier.right s.machine.verifier) = some a
  · exact Or.inl ⟨hc, a, ha, hrd⟩
  · exact Or.inr ⟨a, ha, hrd⟩

/-- **Totality of the matched-comparison branch.**  At a matched scan
comparison a watching chain always has a successor: it queues (nonzero lag),
consumes immediately, or breaks. -/
theorem chainMatched_watch_total (s : GalilScaffoldChainWatch.State)
    (h : zero s.lag = true → WatchReady s) :
    ∃ z, ChainMatched (.watch s) z := by
  by_cases hz : zero s.lag = true
  · rcases watch_good_or_break s (h hz) with hg | ⟨a, ha, hne⟩
    · exact ⟨_, .watch _ _ (.immediate s hz hg)⟩
    · exact ⟨_, .breaks _ _ ⟨hz, (h hz).1, a, ha, hne, rfl⟩⟩
  · exact ⟨_, .watch _ _ (.queued s (Bool.eq_false_iff.mpr hz))⟩

/-- Totality of the background step on a watching chain.  `Internal` has no
mismatch constructor, so a positive lag still needs the full `Good`. -/
theorem chainStep_watch_total (s : GalilScaffoldChainWatch.State)
    (h : positive s.lag = true → GalilScaffoldChainWatch.Good s) :
    ∃ y, ChainStep (.watch s) y := by
  by_cases hp : positive s.lag = true
  · exact ⟨_, .watchStep _ _ (.take s hp (h hp))⟩
  · exact ⟨_, .watchStep _ _ (.idle s (Bool.eq_false_iff.mpr hp))⟩

theorem chainTick_watch_total (s : GalilScaffoldChainWatch.State) (a : Bool)
    (h : positive s.lag = true → GalilScaffoldChainWatch.Good s)
    (hb : WatchBlock s)
    (hc : ∀ m, GalilScaffoldChainWatch.Internal s m →
      GalilScaffoldChainVerifier.canRight m.machine.verifier) :
    ∃ z, ChainTick a (.watch s) z := by
  obtain ⟨y, hy⟩ := chainStep_watch_total s h
  cases a with
  | false => exact ⟨y, y, hy, rfl⟩
  | true =>
    cases hy with
    | watchStep _ w' hi =>
      obtain ⟨z, hz⟩ := chainMatched_watch_total w'
        (fun _ => ⟨hc _ hi, watchBlock_internal hi hb⟩)
      exact ⟨z, _, .watchStep _ _ hi, hz⟩

/-! ## The copy and back phases: obligation (i) -/

/-- The unary DP answer ahead of the copy walk: `n` ones then the `LEFT` mark. -/
def AnswerAhead (t : GalilScaffoldTape.Tape) (n : ℕ) : Prop :=
  ∃ ls : List (Fin 9), t.focus :: t.left = List.replicate n 8 ++ 4 :: ls

/-- The walker still has `n+1` cells to read. -/
def PlaceAhead (p : GalilScaffoldPlace.Place) (n : ℕ) : Prop :=
  n + 1 ≤ (GalilScaffoldPlace.stream p).length

theorem answerAhead_zero {t : GalilScaffoldTape.Tape} (h : AnswerAhead t 0) : t.focus = 4 := by
  obtain ⟨ls, he⟩ := h
  simpa using (List.cons.inj he).1

theorem answerAhead_succ_focus {t : GalilScaffoldTape.Tape} {n : ℕ}
    (h : AnswerAhead t (n+1)) : t.focus = 8 := by
  obtain ⟨ls, he⟩ := h
  simpa [List.replicate_succ] using (List.cons.inj he).1

theorem answerAhead_succ_left {t : GalilScaffoldTape.Tape} {n : ℕ}
    (h : AnswerAhead t (n+1)) : t.left ≠ [] := by
  obtain ⟨ls, he⟩ := h
  rw [List.replicate_succ] at he
  have hl := (List.cons.inj he).2
  rw [hl]
  simp

theorem answerAhead_step {t : GalilScaffoldTape.Tape} {n : ℕ}
    (h : AnswerAhead t (n+1)) : AnswerAhead (GalilScaffoldTape.moveLeft t) n := by
  obtain ⟨ls, he⟩ := h
  rw [List.replicate_succ] at he
  have hl := (List.cons.inj he).2
  rcases t with ⟨left, f, rs⟩
  simp only at hl
  cases left with
  | nil => simp at hl
  | cons a left =>
    refine ⟨ls, ?_⟩
    simp only [GalilScaffoldTape.moveLeft]
    exact hl

theorem placeAhead_read {p : GalilScaffoldPlace.Place} {n : ℕ} (h : PlaceAhead p (n+1)) :
    GalilScaffoldPlace.read (GalilScaffoldPlace.left p) ≠ none := by
  rw [Ne, GalilScaffoldPlace.read_none, GalilScaffoldPlace.left_stream]
  intro he
  have hl := congrArg List.length he
  rw [List.length_tail] at hl
  unfold PlaceAhead at h
  simp only [List.length_nil] at hl
  omega

theorem placeAhead_step {p : GalilScaffoldPlace.Place} {n : ℕ} (h : PlaceAhead p (n+1)) :
    PlaceAhead (GalilScaffoldPlace.left p) n := by
  unfold PlaceAhead at h ⊢
  rw [GalilScaffoldPlace.left_stream, List.length_tail]
  omega

/-- The copy-phase invariant: `n` ticks of answer left, enough walker letters,
a well-formed period prefix, and (at the end) the counter and the plain
endpoint that `copyEnd` inspects. -/
def CopyInv (t : GalilScaffoldTape.Tape) (h : Counter) (p : GalilScaffoldPlace.Place)
    (v : GalilScaffoldChainPeriod.Tape) (n : ℕ) : Prop :=
  AnswerAhead t n ∧ PlaceAhead p n ∧ OnPrefix v ∧ h.neg = [] ∧
    (n = 0 → positive h = true ∧ ∃ b : Fin 3, v.focus = Token.plain b)

theorem inc_neg_nil {h : Counter} (hn : h.neg = []) : (inc h).neg = [] := by
  unfold inc
  rw [hn]

theorem inc_positive {h : Counter} (hn : h.neg = []) : positive (inc h) = true := by
  unfold inc positive
  rw [hn]
  rfl

/-- **Totality of the copy tick.** -/
theorem copy_step_exists {t : GalilScaffoldTape.Tape} {h : Counter}
    {p : GalilScaffoldPlace.Place} {v : GalilScaffoldChainPeriod.Tape} {n : ℕ}
    (hi : CopyInv t h p v n) (lag margin : Counter)
    (ver : GalilScaffoldInputHead.PlaceHead) :
    ∃ y, ChainStep (.copy t h p v lag margin ver) y := by
  obtain ⟨ha, hp, hv, hneg, hz⟩ := hi
  cases n with
  | zero =>
    obtain ⟨hpos, b, hb⟩ := hz rfl
    exact ⟨_, .copyEnd _ _ _ _ _ _ _ b (answerAhead_zero ha) hpos hb⟩
  | succ n =>
    have hr := placeAhead_read hp
    cases hread : GalilScaffoldPlace.read (GalilScaffoldPlace.left p) with
    | none => exact absurd hread hr
    | some a =>
      exact ⟨_, .copyBit _ _ _ _ _ _ _ a (answerAhead_succ_focus ha)
        (answerAhead_succ_left ha) hread⟩

/-- The copy invariant is preserved by the tick it enables. -/
theorem copyInv_step {t : GalilScaffoldTape.Tape} {h : Counter}
    {p : GalilScaffoldPlace.Place} {v : GalilScaffoldChainPeriod.Tape} {n : ℕ}
    (hi : CopyInv t h p v (n+1)) (a : Fin 3) :
    CopyInv (GalilScaffoldTape.moveLeft t) (inc h) (GalilScaffoldPlace.left p)
      (GalilScaffoldChainPeriod.put v a) n := by
  obtain ⟨ha, hp, hv, hneg, _⟩ := hi
  refine ⟨answerAhead_step ha, placeAhead_step hp, onPrefix_put hv a, inc_neg_nil hneg,
    fun _ => ⟨inc_positive hneg, a, ?_⟩⟩
  rcases v with ⟨ls, f, rs⟩
  rfl

/-- **The copy phase runs to `Back` in `n+1` ticks**, delivering the complete
period block that the watch phase needs. -/
theorem copy_run_to_back {t : GalilScaffoldTape.Tape} {h : Counter}
    {p : GalilScaffoldPlace.Place} {v : GalilScaffoldChainPeriod.Tape} {n : ℕ}
    (hi : CopyInv t h p v n) (lag margin : Counter)
    (ver : GalilScaffoldInputHead.PlaceHead) :
    ∃ (v' : GalilScaffoldChainPeriod.Tape) (h' m' : Counter),
      ChainSteps (n+1) (.copy t h p v lag margin ver) (.back v' h' lag m' ver) ∧
      OnBlock v' := by
  induction n generalizing t h p v margin with
  | zero =>
    obtain ⟨ha, hp, hv, hneg, hz⟩ := hi
    obtain ⟨hpos, b, hb⟩ := hz rfl
    exact ⟨_, h, margin,
      .succ (.copyEnd _ _ _ _ _ _ _ b (answerAhead_zero ha) hpos hb) (.zero _),
      onBlock_write_last hv b hb⟩
  | succ n ih =>
    have hi' := hi
    obtain ⟨ha, hp, hv, hneg, _⟩ := hi'
    have hr := placeAhead_read hp
    cases hread : GalilScaffoldPlace.read (GalilScaffoldPlace.left p) with
    | none => exact absurd hread hr
    | some a =>
      obtain ⟨v', h', m', hs, hb⟩ :=
        ih (copyInv_step hi a) (GalilScaffoldChainCredits.decFour margin)
      exact ⟨v', h', m', .succ (.copyBit _ _ _ _ _ _ _ a (answerAhead_succ_focus ha)
        (answerAhead_succ_left ha) hread) hs, hb⟩

/-- **Totality of the back tick**, unconditionally: the `FIRST` test is a
decidable boolean, so one of the two `Back` constructors always applies. -/
theorem back_step_exists (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter)
    (ver : GalilScaffoldInputHead.PlaceHead) :
    ∃ y, ChainStep (.back v h lag margin ver) y := by
  cases hf : GalilScaffoldChainPeriod.isFirst v.focus with
  | false => exact ⟨_, .backStep _ _ _ _ _ hf⟩
  | true => exact ⟨_, .backDone _ _ _ _ _ hf⟩

theorem isFirst_isLast {x : Token} (h : GalilScaffoldChainPeriod.isFirst x = true) :
    GalilScaffoldChainConsume.isLast x = false := by
  cases x <;> simp_all [GalilScaffoldChainPeriod.isFirst, GalilScaffoldChainConsume.isLast]

/-! ## The combined `ChainVM` invariant -/

/-- The chain-wide block invariant, a valid state predicate `Q` for the
`stepsAll_transfer_generic'`-style transfer lemmas. -/
def BlockInv : ChainVM → Prop
  | .idle => True
  | .copy _ _ _ v _ _ _ => OnPrefix v
  | .back v _ _ _ _ => OnBlock v
  | .watch w => WatchBlock w
  | .broken w => WatchBlock w

theorem blockInv_step {x y : ChainVM} (h : ChainStep x y) (hb : BlockInv x) : BlockInv y := by
  cases h with
  | idle => exact hb
  | brokenIdle => exact hb
  | copyBit _ _ _ _ _ _ _ a _ _ _ => exact onPrefix_put hb a
  | copyEnd _ _ _ _ _ _ _ b _ _ hv => exact onBlock_write_last hb b hv
  | backStep => exact onBlock_moveLeft hb
  | backDone _ _ _ _ _ hf => exact onBlock_moveRight hb (isFirst_isLast hf)
  | watchStep _ _ hi => exact watchBlock_internal hi hb

theorem blockInv_matched {x y : ChainVM} (h : ChainMatched x y) (hb : BlockInv x) :
    BlockInv y := by
  cases h with
  | idle => exact hb
  | copy => exact hb
  | back => exact hb
  | watch _ _ ho => exact watchBlock_outer ho hb
  | breaks _ _ hbr => exact watchBlock_break hbr hb

theorem blockInv_tick {a : Bool} {x z : ChainVM} (h : ChainTick a x z) (hb : BlockInv x) :
    BlockInv z := by
  obtain ⟨y, hs, hm⟩ := h
  cases a with
  | false =>
    rw [hm]
    exact blockInv_step hs hb
  | true => exact blockInv_matched hm (blockInv_step hs hb)

theorem blockInv_steps {n : ℕ} {x z : ChainVM} (h : ChainSteps n x z) (hb : BlockInv x) :
    BlockInv z := by
  induction h with
  | zero => exact hb
  | succ hs _ ih => exact ih (blockInv_step hs hb)

/-- `Chain.start` establishes the invariant. -/
theorem blockInv_chainStart (answer : GalilScaffoldTape.Tape) (c : Fin 3)
    (walker : GalilScaffoldPlace.Place) (ver : GalilScaffoldInputHead.PlaceHead)
    (radius : Counter) : BlockInv (chainStart answer c walker ver radius) :=
  onPrefix_start c

/-- The concrete watch entry point `ready` satisfies the block invariant. -/
theorem onBlock_ready (c b : Fin 3) (ys : List (Fin 3)) :
    OnBlock (GalilScaffoldChainConsume.ready c ys b).period := by
  have hbase : OnBlock ⟨[], Token.first c, ys.map Token.plain ++ [Token.last b]⟩ :=
    ⟨c, b, ys, rfl⟩
  exact onBlock_moveRight hbase rfl

#print axioms onPrefix_put
#print axioms onBlock_write_last
#print axioms onBlock_symbol
#print axioms onBlock_right_ne
#print axioms onBlock_moveLeft
#print axioms onBlock_moveRight
#print axioms onBlock_consume
#print axioms watchBlock_tick
#print axioms watchBlock_run
#print axioms watchBlock_break
#print axioms watch_good_or_break
#print axioms chainMatched_watch_total
#print axioms chainStep_watch_total
#print axioms chainTick_watch_total
#print axioms copy_step_exists
#print axioms copyInv_step
#print axioms copy_run_to_back
#print axioms back_step_exists
#print axioms blockInv_step
#print axioms blockInv_matched
#print axioms blockInv_tick
#print axioms blockInv_steps
#print axioms blockInv_chainStart
#print axioms onBlock_ready

end PalPeg.GalilBranchInvariants
