import PalPeg.GalilTrailProof
import PalPeg.GalilChainCoupling

/-!
# The verifier half of the trailing invariant

`GalilTrailProof.TrailF` has two chain clauses: `ver` (`Trails raw m 0` for the
chain verifier, whatever the mode) and `lagPos` (`Trails raw m 1`, one place of
extra slack, for a watch with positive lag — the mode whose lookahead is two
right moves, `GalilLookRefined.lookChain'`).  This file carries those two
clauses — packaged as `VerF` — through the chain start and through every chain
tick, and then lifts them to a tick of `galilFrameS`.

The **arithmetic** side conditions at the *target* are collected in
`ChainBudget`: the moved verifier is sane, and (only when its right stack is
empty) it is still left of the checkpoint place `2(m+1)-1`, one place further
left on a positive-lag watch.  That is exactly what the lag ledger
`position ver + value lag = position R` (`GalilChainCoupling.SumRel`,
`GalilLookRefined.lagPos_of_value`) plus `R`'s own `Trails` clause delivers, and
it is left to the caller: `trails_one_of_lag` below is the derivation, and the
L/C/R clauses stay hypotheses throughout.

What is proved here is the *combinatorics*: along `ChainStep`, `ChainMatched`,
`ChainTick`, `chainAt` and finally `Tick (galilFrameS …)` the verifier is the old
verifier after at most two `GalilScaffoldChainVerifier.right` moves (`VerMove`),
and consumption is preserved because a right move over a non-empty right stack
consumes nothing (`GalilTrailProof.usedPH_right_of_stack`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false

namespace PalPeg.GalilTrailChain

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof

/-! ## 1. Verifier moves -/

/-- One background/credit phase moves the chain verifier at most one place right. -/
def VerStep (p q : PH) : Prop := q = p ∨ q = GalilScaffoldChainVerifier.right p

/-- A whole chain tick (background step, then the match credit) moves the chain
verifier at most two places right. -/
def VerMove (p q : PH) : Prop := ∃ r, VerStep p r ∧ VerStep r q

theorem verMove_zero (p : PH) : VerMove p p := ⟨p, Or.inl rfl, Or.inl rfl⟩

theorem verMove_of_step {p q : PH} (h : VerStep p q) : VerMove p q := ⟨p, Or.inl rfl, h⟩

theorem verMove_snoc {p q : PH} (h : VerStep p q) :
    VerMove p (GalilScaffoldChainVerifier.right q) := ⟨q, h, Or.inr rfl⟩

/-! ## 2. Head arithmetic for a moved verifier -/

/-- One right move keeps the frontier clause, given the place bound at the target. -/
theorem trails_move1 {raw : List (Fin 2)} {m e : ℕ} {p : PH} (h : Trails raw m 0 p)
    (hs : GalilFrontMono.Sane (GalilScaffoldChainVerifier.right p))
    (hb : (GalilScaffoldChainVerifier.right p).head.right = [] →
      position (GalilScaffoldChainVerifier.right p) + e ≤ 2 * (m + 1) - 1) :
    Trails raw m e (GalilScaffoldChainVerifier.right p) := by
  refine ⟨represents_right h.rep, hs, ?_, hb⟩
  by_cases hz : (GalilScaffoldChainVerifier.right p).head.right = []
  · exact GalilNeedBound.usedPH_le_of_position raw _ m (represents_right h.rep) hs hz
      (by have := hb hz; omega)
  · rw [usedPH_right_of_stack _ _ (stack_ne_of_right_stack_ne hz)]; exact h.used

/-- Two right moves keep the frontier clause: over a non-empty right stack the
pair consumes nothing (`usedPH_right_right_of_stack`), otherwise the place bound
at the target does the work. -/
theorem trails_move2 {raw : List (Fin 2)} {m e : ℕ} {p : PH} (h : Trails raw m 0 p)
    (hs : GalilFrontMono.Sane
      (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right p)))
    (hb : (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right p)).head.right = [] →
      position (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right p)) + e
        ≤ 2 * (m + 1) - 1) :
    Trails raw m e (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right p)) := by
  refine ⟨represents_right (represents_right h.rep), hs, ?_, hb⟩
  by_cases hz : (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right p)).head.right = []
  · exact GalilNeedBound.usedPH_le_of_position raw _ m
      (represents_right (represents_right h.rep)) hs hz (by have := hb hz; omega)
  · rw [usedPH_right_right_of_stack _ _
      (stack_ne_of_right_stack_ne (stack_ne_of_right_stack_ne hz))]
    exact h.used

theorem trails_of_verMove {raw : List (Fin 2)} {m e : ℕ} {p q : PH} (hmv : VerMove p q)
    (h : Trails raw m 0 p) (hs : GalilFrontMono.Sane q)
    (hb : q.head.right = [] → position q + e ≤ 2 * (m + 1) - 1) : Trails raw m e q := by
  obtain ⟨r, h1, h2⟩ := hmv
  rcases h1 with rfl | rfl
  · rcases h2 with rfl | rfl
    · exact ⟨h.rep, hs, h.used, hb⟩
    · exact trails_move1 h hs hb
  · rcases h2 with rfl | rfl
    · exact trails_move1 h hs hb
    · exact trails_move2 h hs hb

/-- **The lag ledger delivers the positive-lag clause.**  `position ver + lag =
position R` on a canonical lag counter (`GalilChainCoupling.SumRel` for the watch,
via `GalilLookRefined.lagPos_of_value`) together with `R`'s own `Trails` clause
gives the verifier one place of slack — the `lagPos` field of `ChainBudget`. -/
theorem trails_one_of_lag {raw : List (Fin 2)} {m : ℕ} {r : PH}
    {w : GalilScaffoldChainWatch.State}
    (hR : Trails raw m 0 r) (hst : r.head.right = [])
    (hc : GalilScaffoldCounter.Canonical w.lag)
    (hsum : (position w.machine.verifier : ℤ) + GalilScaffoldCounter.value w.lag = position r)
    (hp : GalilScaffoldCounter.positive w.lag = true) :
    position w.machine.verifier + 1 ≤ 2 * (m + 1) - 1 := by
  have h1 := GalilLookRefined.lagPos_of_value w (position r) hc hsum hp
  have h2 := hR.pos hst
  omega

/-! ## 3. The two chain clauses, and their transport along a chain tick -/

/-- The two chain clauses of `GalilTrailProof.TrailF`, as a predicate on the
chain component alone. -/
structure VerF (raw : List (Fin 2)) (m : ℕ) (x : ChainVM) : Prop where
  ver : ∀ p, verOf x = some p → Trails raw m 0 p
  lagPos : ∀ w : GalilScaffoldChainWatch.State, x = .watch w →
    GalilScaffoldCounter.positive w.lag = true → Trails raw m 1 w.machine.verifier

/-- **The named side condition.**  The place budget the chain moves need at the
*target* of the tick.  `sane` and `pos` are the `Trails` fields that head
arithmetic cannot produce on its own (a right move can leave the checkpoint
window); `lagPos` is the extra place a positive-lag watch needs.  Both come from
the lag ledger and `R`'s clause (`trails_one_of_lag`), not from the chain. -/
structure ChainBudget (m : ℕ) (z : ChainVM) : Prop where
  sane : ∀ p, verOf z = some p → GalilFrontMono.Sane p
  pos : ∀ p, verOf z = some p → p.head.right = [] → position p ≤ 2 * (m + 1) - 1
  lagPos : ∀ w : GalilScaffoldChainWatch.State, z = .watch w →
    GalilScaffoldCounter.positive w.lag = true → w.machine.verifier.head.right = [] →
      position w.machine.verifier + 1 ≤ 2 * (m + 1) - 1

theorem verF_idle (raw : List (Fin 2)) (m : ℕ) : VerF raw m .idle :=
  ⟨fun p hp => absurd hp (by simp [verOf]), fun w hw _ => ChainVM.noConfusion hw⟩

theorem verF_congr {raw : List (Fin 2)} {m : ℕ} {x z : ChainVM} (h : z = x)
    (hx : VerF raw m x) : VerF raw m z := h ▸ hx

/-- The verifier after one background chain step. -/
theorem chainStep_ver {x y : ChainVM} (h : ChainStep x y) :
    verOf y = none ∨ ∃ p q, verOf x = some p ∧ verOf y = some q ∧ VerStep p q := by
  cases h with
  | idle => exact Or.inl rfl
  | brokenIdle w => exact Or.inr ⟨_, _, rfl, rfl, Or.inl rfl⟩
  | copyBit t hh p v lag margin ver a one legal present =>
    exact Or.inr ⟨_, _, rfl, rfl, Or.inl rfl⟩
  | copyEnd t hh p v lag margin ver b hl hp hv => exact Or.inr ⟨_, _, rfl, rfl, Or.inl rfl⟩
  | backStep v hh lag margin ver hf => exact Or.inr ⟨_, _, rfl, rfl, Or.inl rfl⟩
  | backDone v hh lag margin ver hf => exact Or.inr ⟨_, _, rfl, rfl, Or.inl rfl⟩
  | watchStep w w' hi =>
    cases hi with
    | idle hz => exact Or.inr ⟨_, _, rfl, rfl, Or.inl rfl⟩
    | take hp hg => exact Or.inr ⟨_, _, rfl, rfl, Or.inr rfl⟩
  | watchBreak w w' hb =>
    obtain ⟨-, -, -, -, -, ht⟩ := hb
    subst ht
    exact Or.inr ⟨_, _, rfl, rfl, Or.inr rfl⟩

/-- The verifier after the match credit. -/
theorem chainMatched_ver {y z : ChainVM} (h : ChainMatched y z) :
    verOf z = none ∨ ∃ p q, verOf y = some p ∧ verOf z = some q ∧ VerStep p q := by
  cases h with
  | idle => exact Or.inl rfl
  | copy t hh p v lag margin ver => exact Or.inr ⟨_, _, rfl, rfl, Or.inl rfl⟩
  | back v hh lag margin ver => exact Or.inr ⟨_, _, rfl, rfl, Or.inl rfl⟩
  | brokenMatched w => exact Or.inr ⟨_, _, rfl, rfl, Or.inl rfl⟩
  | watch w w' ho =>
    cases ho with
    | queued hz => exact Or.inr ⟨_, _, rfl, rfl, Or.inl rfl⟩
    | immediate hz hg => exact Or.inr ⟨_, _, rfl, rfl, Or.inr rfl⟩
  | breaks w w' hb =>
    obtain ⟨-, -, -, -, -, ht⟩ := hb
    subst ht
    exact Or.inr ⟨_, _, rfl, rfl, Or.inr rfl⟩

/-- A disabled chain tick is a bare background step: one move at most. -/
theorem chainTick_false_ver {x z : ChainVM} (ht : ChainTick false x z) :
    verOf z = none ∨ ∃ p q, verOf x = some p ∧ verOf z = some q ∧ VerStep p q := by
  obtain ⟨y, hs, hm⟩ := ht
  simp only [Bool.false_eq_true, if_false] at hm
  subst hm
  exact chainStep_ver hs

/-- **Two moves at most per chain tick.** -/
theorem chainTick_ver {b : Bool} {x z : ChainVM} (ht : ChainTick b x z) :
    verOf z = none ∨ ∃ p q, verOf x = some p ∧ verOf z = some q ∧ VerMove p q := by
  obtain ⟨y, hs, hm⟩ := ht
  cases b with
  | false =>
    simp only [Bool.false_eq_true, if_false] at hm
    subst hm
    rcases chainStep_ver hs with h | ⟨p, q, hp, hq, hv⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, q, hp, hq, verMove_of_step hv⟩
  | true =>
    simp only [if_true] at hm
    rcases chainStep_ver hs with h1 | ⟨p, q, hp, hq, hv1⟩
    · rcases chainMatched_ver hm with h2 | ⟨p', q', hp', -, -⟩
      · exact Or.inl h2
      · rw [h1] at hp'; exact absurd hp' (by simp)
    · rcases chainMatched_ver hm with h2 | ⟨p', q', hp', hq', hv2⟩
      · exact Or.inl h2
      · obtain rfl : p' = q := Option.some.inj (hp'.symm.trans hq)
        exact Or.inr ⟨p, q', hp, hq', ⟨p', hv1, hv2⟩⟩

/-- The transport principle: a `VerMove` of the verifier plus the target budget
carries both clauses. -/
theorem verF_of_verMove {raw : List (Fin 2)} {m : ℕ} {x z : ChainVM}
    (hmv : verOf z = none ∨ ∃ p q, verOf x = some p ∧ verOf z = some q ∧ VerMove p q)
    (hx : VerF raw m x) (hB : ChainBudget m z) : VerF raw m z := by
  rcases hmv with hn | ⟨p, q, hp, hq, hv⟩
  · refine ⟨fun r hr => absurd (hn ▸ hr) (by simp), fun w hw _ => ?_⟩
    rw [hw] at hn
    exact absurd hn (by simp [verOf])
  · refine ⟨fun r hr => ?_, fun w hw hpl => ?_⟩
    · obtain rfl : q = r := Option.some.inj (hq.symm.trans hr)
      exact trails_of_verMove hv (hx.ver p hp) (hB.sane q hq)
        (fun hs => by have := hB.pos q hq hs; omega)
    · have hq' : verOf z = some w.machine.verifier := by rw [hw]; rfl
      obtain rfl : q = w.machine.verifier := Option.some.inj (hq.symm.trans hq')
      exact trails_of_verMove hv (hx.ver p hp) (hB.sane _ hq')
        (fun hs => hB.lagPos w hw hpl hs)

/-- **`trailChain_start`.**  `chain.start()` copies the centre head into the
verifier, so the verifier clause is the centre's `Trails` clause, and the
`lagPos` clause is vacuous (the fresh chain is in `copy`, never `watch`). -/
theorem trailChain_start {raw : List (Fin 2)} {m : ℕ} (answer : GalilScaffoldTape.Tape)
    (c : Fin 3) (walker : GalilScaffoldPlace.Place) (ver : PH)
    (radius : GalilScaffoldCounter.Counter) (h : Trails raw m 0 ver) :
    VerF raw m (chainStart answer c walker ver radius) := by
  refine ⟨fun p hp => ?_, fun w hw _ => ChainVM.noConfusion hw⟩
  obtain rfl : ver = p := Option.some.inj hp
  exact h

/-- `C`'s frontier clause gives the copied verifier's clause, given the one place
bound `FrontLe` does not carry (a gap head may sit exactly on `2(m+1)`); that
bound is `position C ≤ position R` composed with `R`'s `Trails` clause. -/
theorem trails_of_frontLe {raw : List (Fin 2)} {m : ℕ} {p : PH}
    (h : GalilLookRefined.FrontLe raw m p)
    (hb : p.head.right = [] → position p ≤ 2 * (m + 1) - 1) : Trails raw m 0 p :=
  ⟨h.1, h.2.1, GalilLookRefined.usedPH_le_of_frontLe raw m p h, fun hs => by
    have := hb hs; omega⟩

/-- **`trailChain_tick`.**  Both clauses survive every chain tick. -/
theorem trailChain_tick {raw : List (Fin 2)} {m : ℕ} {b : Bool} {x z : ChainVM}
    (ht : ChainTick b x z) (hx : VerF raw m x) (hB : ChainBudget m z) : VerF raw m z :=
  verF_of_verMove (chainTick_ver ht) hx hB

/-- **`trailChain_chainAt`.**  The chain effect of a comparison or of a scan
background: an ordinary tick, an idle chain, or a fresh `chainStart` (with the
match credit when the comparison matched). -/
theorem trailChain_chainAt {raw : List (Fin 2)} {m : ℕ} {b found : Bool}
    {ans : GalilScaffoldTape.Tape} {c : Fin 3} {wk : GalilScaffoldPlace.Place} {ver : PH}
    {r : GalilScaffoldCounter.Counter} {x z : ChainVM}
    (h : chainAt b found ans c wk ver r x z) (hx : VerF raw m x)
    (hv : Trails raw m 0 ver) (hB : ChainBudget m z) : VerF raw m z := by
  rcases h with ⟨-, ht⟩ | ⟨-, -, rfl⟩ | ⟨-, -, hz⟩
  · exact trailChain_tick ht hx hB
  · exact verF_idle raw m
  · cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false] at hz
      subst hz
      exact trailChain_start ans c wk ver r hv
    | true =>
      simp only [if_true] at hz
      refine verF_of_verMove ?_ (trailChain_start ans c wk ver r hv) hB
      rcases chainMatched_ver hz with h1 | ⟨p, q, hp, hq, hs⟩
      · exact Or.inl h1
      · exact Or.inr ⟨p, q, hp, hq, verMove_of_step hs⟩

/-! ## 4. Lifting to a tick of `galilFrameS` -/

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- The chain effect of a comparison is a `chainAt` on `s.center`/`s.radius`; a
mismatched comparison is the disabled event. -/
theorem compare_chainAt {s s' : GalilVM}
    (hcmp : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s') :
    ∃ (a found : Bool) (ans : GalilScaffoldTape.Tape) (cc : Fin 3)
      (wk : GalilScaffoldPlace.Place),
      chainAt a found ans cc wk s.center s.radius s.chain s'.chain ∧
      (¬ (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).matched s' →
        a = false) := by
  obtain ⟨vs, vq, a, -, -, hiff, -, hch, hteq⟩ :
    compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
  cases a with
  | true =>
    rw [if_pos rfl] at hteq
    subst hteq
    rw [afterBirth_chain]
    exact ⟨true, _, _, _, _, hch, fun hn => absurd (by
      have h0 : GalilScaffoldInputHead.read (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).left
        = GalilScaffoldInputHead.read (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).right := by
        rw [afterBirth_left, afterBirth_right]; exact hiff.1 rfl
      exact h0) hn⟩
  | false =>
    rw [if_neg (by simp)] at hteq
    subst hteq
    rw [afterBirth_chain]
    exact ⟨false, _, _, _, _, hch, fun _ => rfl⟩

/-- **`trailChain_scanTick`.**  Both chain clauses survive every tick of
`galilFrameS`, given the target budget and the centre's clause.  The case split
is that of `GalilChainCoupling.coupled_tick`: the scan background and the
comparison act on the chain through `chainAt`, the shift entry adds the
immediate consume, a shift unit and `shift_done` keep the verifier, and every
other mode leaves the chain untouched, idle, or restarted. -/
theorem trailChain_scanTick {raw : List (Fin 2)} {m : ℕ} {c c' : Control} {s t : GalilVM}
    (hx : VerF raw m s.chain) (hC : Trails raw m 0 s.center)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : ChainBudget m t.chain → VerF raw m t.chain := by
  cases h
  case init =>
    rename_i hm hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s t := hi
    exact fun _ => verF_congr hch (verF_idle raw m)
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, -, hch, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact fun hB => trailChain_chainAt hch hx hC hB
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, -, hch, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact fun hB => trailChain_chainAt hch hx hC hB
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    exact fun _ => verF_idle raw m
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨a, found, ans, cc, wk, hch, -⟩ :=
      compare_chainAt onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have htc : t.chain = s'.chain := by rw [hpl']; cases c.replaying <;> rfl
    exact fun hB => verF_congr htc (trailChain_chainAt hch hx hC (htc ▸ hB))
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨a, found, ans, cc, wk, hch, ha⟩ :=
      compare_chainAt onLetter leftFirst centre place entry q first hcmp
    obtain rfl : a = false := ha hmt
    obtain ⟨w, hs0, ht⟩ : beginShiftVM' s' t := hb
    subst ht
    have hq0 : verOf s'.chain = some w.machine.verifier := by rw [hs0]; rfl
    have hstep : ∃ p, verOf s.chain = some p ∧ VerStep p w.machine.verifier := by
      rcases hch with ⟨-, htick⟩ | ⟨-, -, hz⟩ | ⟨-, -, hz⟩
      · rcases chainTick_false_ver htick with hn | ⟨p, qq, hp, hqq, hv⟩
        · rw [hn] at hq0; exact absurd hq0 (by simp)
        · obtain rfl : qq = w.machine.verifier := Option.some.inj (hqq.symm.trans hq0)
          exact ⟨p, hp, hv⟩
      · exfalso; rw [hs0] at hz; exact ChainVM.noConfusion hz
      · exfalso
        simp only [Bool.false_eq_true, if_false] at hz
        rw [hs0] at hz
        exact ChainVM.noConfusion hz
    obtain ⟨p, hp, hv⟩ := hstep
    refine fun hB => verF_of_verMove (Or.inr ⟨p,
      GalilScaffoldChainVerifier.right w.machine.verifier, hp, rfl, verMove_snoc hv⟩) hx hB
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨pl, ht⟩ : beginFallbackVM' s' t := hb
    subst ht
    exact fun _ => verF_idle raw m
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨-, -, -, w, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    have hws : s.chain = .watch w := hw
    exact fun hB => verF_of_verMove (Or.inr ⟨w.machine.verifier, w.machine.verifier,
      by rw [hws]; rfl, rfl, verMove_zero _⟩) hx hB
  case shift_done =>
    rename_i o hm hp ho
    exact fun _ => hx
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : replayStartVM entry s t := hi
    exact fun _ => verF_congr hch (verF_idle raw m)
  all_goals
    (rename_i hi
     have hch : t.chain = s.chain := (congrArg GalilVM.chain hi.2).trans rfl
     exact fun _ => verF_congr hch hx)

end Tick

/-! ## 5. The interface with the L/C/R half -/

/-- `VerF` really is the chain half of `TrailF`. -/
theorem verF_of_trailF {raw : List (Fin 2)} {m : ℕ} {x : State GalilVM}
    (h : TrailF raw m x) : VerF raw m x.vm.chain := ⟨h.ver, h.lagPos⟩

/-- …and together with the L/C/R clauses (proved elsewhere) it *is* `TrailF`. -/
theorem trailF_of_verF {raw : List (Fin 2)} {m : ℕ} {x : State GalilVM}
    (hL : GalilLookRefined.FrontLe raw m x.vm.left)
    (hC : GalilLookRefined.FrontLe raw m x.vm.center)
    (hR : Trails raw m 0 x.vm.right) (h : VerF raw m x.vm.chain) : TrailF raw m x :=
  ⟨hL, hC, hR, h.ver, h.lagPos⟩

#print axioms trails_move1
#print axioms trails_move2
#print axioms trails_of_verMove
#print axioms trails_one_of_lag
#print axioms chainStep_ver
#print axioms chainMatched_ver
#print axioms chainTick_false_ver
#print axioms chainTick_ver
#print axioms verF_of_verMove
#print axioms trailChain_start
#print axioms trails_of_frontLe
#print axioms trailChain_tick
#print axioms trailChain_chainAt
#print axioms compare_chainAt
#print axioms trailChain_scanTick
#print axioms verF_of_trailF
#print axioms trailF_of_verF

end PalPeg.GalilTrailChain
