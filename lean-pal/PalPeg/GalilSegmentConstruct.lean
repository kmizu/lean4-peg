import PalPeg.GalilTickFun2
import PalPeg.GalilBranchInvariants2
import PalPeg.GalilScaffoldTopProgressS
import PalPeg.GalilFrontier

/-!
# Constructing the chain-idle segment (L7a)

The cycle lemmas (`cycle_found_stepsAll`, `cycle_fallback_stepsAll`) take the
chain-idle segment `WatchSegE P q first delay es0 c0 r cF sF` as a *hypothesis*
and start working at its terminal comparison.  This module *builds* that
segment: from a scan state with the chain idle and a fuel `n`, either `n`
events are produced and the run is still in scan mode with an idle chain, or
the run stops at a state where the idle phase genuinely ends.

The three ways the idle phase ends are collected in `SegEnd`:

* `ended`   — the right head has no further symbol (end of input);
* `mismatch` — a comparison at clock one, not replaying, whose outer symbols
  differ: the entry of `cycle_fallback_stepsAll`;
* `found`   — a matching comparison at clock one whose search co-run reports
  `found`: the entry of `cycle_found_stepsAll`;
* `lastLetter` — the comparison at clock one that would pop the *last* letter
  of the incoming FIFO, stopped *before* the comparison is taken, so that the
  caller can apply `report_of_last_consume` (on a match) or its mismatch
  companions.  With this exit `ended` arises only when the incoming FIFO is
  already empty.

The construction is by ordinary recursion on the fuel: every `WatchSegE`
constructor emits exactly one event, so the fuel alone is the measure (no
`(fuel, clock)` lexicographic order is needed).

The hypotheses of the co-processes are named and not discharged here:

* `hsearch` — every state whose search projection is `SearchReady` has a search
  effect for every event (`searchEffect_exists` of `GalilBranchInvariants2`);
* `hpres`  — the effect's witness is again `SearchReady` (the preservation
  half, left as a hypothesis);
A background event (`false`) *can* land the search in `found` — the DP
quantum ignores the event (`PalPeg.GalilBackgroundNotFound`) — and
`backgroundS` then installs `chainStart …` through `chainAt`'s idle+found
branch.  So the idle phase has a fourth exit, `SegEnd.foundBackground`: the
next background tick would start the chain.  `background_found_step` builds
that very tick for the caller.
-/

set_option autoImplicit false
namespace PalPeg.GalilSegmentConstruct

open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilTickFun2 PalPeg.GalilBranchInvariants2
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- The three exits of the chain-idle phase. -/
inductive SegEnd (P : Shared) (c : Control) (t : GalilVM) : Prop
  | ended (h : ¬ canRight t.right)
  | mismatch (hr : c.replaying = false) (hc : c.clock = 1) (hav : canRight t.right)
      (hne : read (left t.left) ≠ read (right t.right))
  | found (hc : c.clock = 1) (hav : canRight t.right)
      (hmt : read (left t.left) = read (right t.right))
      (hq : ∃ vq, searchEffect P true t vq ∧ vq.search.mode = .found)
  | foundBackground (hc : 1 ≤ c.clock)
      (hq : ∃ vq, searchEffect P false t vq ∧ vq.search.mode = .found)
  | lastLetter (hc : c.clock = 1) (hav : canRight t.right) (hpop : PopsIncoming t.right)
      (hinc : ∃ a, t.right.head.incoming = [a])

/-- A background step that keeps the chain idle: the chain effect of the event
`false` on an idle chain is again idle as soon as the search does not report
`found`. -/
theorem idle_background_exists (P : Shared) (q : ℕ) (first : Fin 9) (s : GalilVM)
    (hidle : s.chain = ChainVM.idle) {v : SearchVM} (hv : searchEffect P false s v)
    (hnf : v.search.mode ≠ .found) :
    ∃ s', (galilFrameS P q first).background s s' ∧ s'.chain = ChainVM.idle ∧
      s'.left = s.left ∧ s'.right = s.right ∧ s'.center = s.center ∧ s'.replay = s.replay ∧
      searchLens.get s' = v := by
  refine ⟨searchLens.set (scanLens.set s ⟨s.left, s.right, ChainVM.idle⟩) v, ?_, rfl, rfl, rfl, rfl,
    rfl, rfl⟩
  exact ⟨rfl, rfl, hv, Or.inr (Or.inl ⟨hidle, decide_eq_false hnf, rfl⟩), rfl⟩

/-- The background tick of the `foundBackground` exit: when the search effect
of the event `false` reports `found` on an idle chain, `backgroundS`'s own
`chainAt` clause (`chainAt false true … .idle z ↔ z = chainStart …`, i.e.
`chainAt_background_found`) installs `chainStart` — the chain is started by
the background tick itself. -/
theorem background_found_step (P : Shared) (q : ℕ) (first : Fin 9) (s : GalilVM)
    (hidle : s.chain = ChainVM.idle) {v : SearchVM} (hv : searchEffect P false s v)
    (hf : v.search.mode = .found) :
    ∃ s', (galilFrameS P q first).background s s' ∧
      s'.chain = chainStart (v.dp.config.tapes 11) (P.centre s) (P.place s) s.center s.radius ∧
      s'.left = s.left ∧ s'.right = s.right ∧ s'.center = s.center ∧ s'.replay = s.replay ∧
      searchLens.get s' = v := by
  refine ⟨searchLens.set (scanLens.set s ⟨s.left, s.right,
    chainStart (v.dp.config.tapes 11) (P.centre s) (P.place s) s.center s.radius⟩) v,
    ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨rfl, rfl, hv, Or.inr (Or.inr ⟨hidle, decide_eq_true hf, rfl⟩), rfl⟩

/-- **L7a: the chain-idle segment exists.**  From a scan state with a positive
clock and an idle chain, carrying `SearchReady`, `MInv` and `ScanInvariant`,
a fuel `n` yields a `WatchSegE` run that either spends the whole fuel and is
still in scan mode with an idle chain, or stops at a state satisfying
`SegEnd` — the exits taken by `cycle_found_stepsAll` and
`cycle_fallback_stepsAll`.  All the invariants are carried to the end. -/
theorem watchSegE_construct (raw : List (Fin 2)) (P : Shared)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (hd : 1 ≤ delay)
    (hsearch : ∀ s' : GalilVM, SearchReady (searchLens.get s') → ∀ a : Bool,
      ∃ v, searchEffect P a s' v)
    (hpres : ∀ (s' : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s') → searchEffect P a s' v → SearchReady v) :
    ∀ (n : ℕ) (c : Control) (s : GalilVM) (r : ℕ), c.mode = .scan → 1 ≤ c.clock →
      s.chain = ChainVM.idle → SearchReady (searchLens.get s) → MInv raw c s →
      ScanInvariant raw (position s.center) r s.left s.right →
      ∃ (es : List Bool) (c' : Control) (t : GalilVM) (r' : ℕ),
        WatchSegE P q first delay es c s c' t ∧
        c'.mode = .scan ∧ 1 ≤ c'.clock ∧ t.chain = ChainVM.idle ∧
        SearchReady (searchLens.get t) ∧ MInv raw c' t ∧
        ScanInvariant raw (position t.center) r' t.left t.right ∧
        (es.length = n ∨ SegEnd P c' t) := by
  classical
  intro n
  induction n with
  | zero =>
    intro c s r hm hclk hidle hsr hM hi
    exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hsr, hM, hi, Or.inl rfl⟩
  | succ n ih =>
    intro c s r hm hclk hidle hsr hM hi
    by_cases hav : canRight s.right
    · by_cases hrp : c.replaying = true
      · -- replaying
        rcases Nat.lt_or_ge 1 c.clock with hlt | hle
        · -- `countR`
          obtain ⟨v, hv⟩ := hsearch s hsr false
          by_cases hfb : v.search.mode = .found
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hsr, hM, hi,
              Or.inr (.foundBackground hclk ⟨v, hv, hfb⟩)⟩
          obtain ⟨s', hb, hch', hl', hr', hC', hrep', hget'⟩ :=
            idle_background_exists P q first s hidle hv hfb
          have hsr' : SearchReady (searchLens.get s') := by
            rw [hget']; exact hpres s false v hsr hv
          have hM' : MInv raw {c with clock := c.clock - 1} s' := minv_same rfl hr' hC' hrep' hM
          have hi' : ScanInvariant raw (position s'.center) r s'.left s'.right := by
            rw [hl', hr', hC']; exact hi
          obtain ⟨es, c', t, r', hseg, hm', hclk', hidle', hsrt, hMt, hit, hlen⟩ :=
            ih {c with clock := c.clock - 1} s' r hm (by simp; omega) hch' hsr' hM' hi'
          refine ⟨false :: es, c', t, r', .countR c s s' hm hrp hlt hidle hb hseg, hm', hclk',
            hidle', hsrt, hMt, hit, ?_⟩
          rcases hlen with h0 | h0
          · exact Or.inl (by simp [h0])
          · exact Or.inr h0
        · -- clock one: a replay comparison, which matches by `replay_match_of_minv`
          have hc1 : c.clock = 1 := le_antisymm hle hclk
          by_cases hlast : PopsIncoming s.right ∧ ∃ a, s.right.head.incoming = [a]
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hsr, hM, hi,
              Or.inr (.lastLetter hc1 hav hlast.1 hlast.2)⟩
          have hmatch : read (left s.left) = read (right s.right) :=
            replay_match_of_minv hM hrp hav hi
          obtain ⟨vq, hq⟩ := hsearch s hsr true
          by_cases hf : vq.search.mode = .found
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hsr, hM, hi,
              Or.inr (.found hc1 hav hmatch ⟨vq, hq, hf⟩)⟩
          · set vs : ScanVM := ⟨left s.left, right s.right, ChainVM.idle⟩ with hvsdef
            have hmt : (galilFrame P q first).matched (scanLens.set s vs) := hmatch
            set u : GalilVM := replayDec true (afterCompare s vs vq) with hudef
            let o : Bool := if P.onLetter u then decide (P.leftFirst u) else c.output
            have ho : refresh (galilFrame P q first) u c.output o := by
              refine ⟨fun hl => ?_, fun hl => ?_⟩
              · have hl' : P.onLetter u := hl
                show (if P.onLetter u then decide (P.leftFirst u) else c.output) = true ↔
                  P.leftFirst u
                rw [if_pos hl']; exact decide_eq_true_iff
              · have hl' : ¬ P.onLetter u := hl
                show (if P.onLetter u then decide (P.leftFirst u) else c.output) = c.output
                rw [if_neg hl']
            have hidleU : u.chain = ChainVM.idle := by
              rw [hudef, replayDec_chain, afterCompare_chain]
            have hgetU : searchLens.get u = vq := by rw [hudef, replayDec_search]; rfl
            have hsrU : SearchReady (searchLens.get u) := by
              rw [hgetU]; exact hpres s true vq hsr hq
            have hMU : MInv raw {c with clock := delay, output := o, replaying := !(P.replayExhausted u)} u :=
              minv_matchR P hex o delay hrp rfl hav hi hM
            have hiU : ScanInvariant raw (position u.center) (r+1) u.left u.right := by
              have h0 := matched_invariant' raw vq (vs := vs) rfl rfl hmatch hav hi
              rw [hudef, replayDec_left, replayDec_right, replayDec_center, afterCompare_center]
              exact h0
            obtain ⟨es, c', t, r', hseg, hm', hclk', hidle', hsrt, hMt, hit, hlen⟩ :=
              ih {c with clock := delay, output := o, replaying := !(P.replayExhausted u)} u (r+1)
                hm hd hidleU hsrU hMU hiU
            refine ⟨true :: es, c', t, r',
              .matchIdleR c s vs vq o hm hrp hc1 hav hidle rfl rfl rfl hmt hq hf ho hseg,
              hm', hclk', hidle', hsrt, hMt, hit, ?_⟩
            rcases hlen with h0 | h0
            · exact Or.inl (by simp [h0])
            · exact Or.inr h0
      · -- not replaying
        have hrp' : c.replaying = false := by
          cases hb : c.replaying with
          | false => rfl
          | true => exact absurd hb hrp
        rcases Nat.lt_or_ge 1 c.clock with hlt | hle
        · -- `count`
          obtain ⟨v, hv⟩ := hsearch s hsr false
          by_cases hfb : v.search.mode = .found
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hsr, hM, hi,
              Or.inr (.foundBackground hclk ⟨v, hv, hfb⟩)⟩
          obtain ⟨s', hb, hch', hl', hr', hC', hrep', hget'⟩ :=
            idle_background_exists P q first s hidle hv hfb
          have hsr' : SearchReady (searchLens.get s') := by
            rw [hget']; exact hpres s false v hsr hv
          have hM' : MInv raw {c with clock := c.clock - 1} s' := minv_same rfl hr' hC' hrep' hM
          have hi' : ScanInvariant raw (position s'.center) r s'.left s'.right := by
            rw [hl', hr', hC']; exact hi
          obtain ⟨es, c', t, r', hseg, hm', hclk', hidle', hsrt, hMt, hit, hlen⟩ :=
            ih {c with clock := c.clock - 1} s' r hm (by simp; omega) hch' hsr' hM' hi'
          refine ⟨false :: es, c', t, r', .count c s s' hm hrp' hav hlt hb hseg, hm', hclk',
            hidle', hsrt, hMt, hit, ?_⟩
          rcases hlen with h0 | h0
          · exact Or.inl (by simp [h0])
          · exact Or.inr h0
        · -- clock one: the terminal comparison
          have hc1 : c.clock = 1 := le_antisymm hle hclk
          by_cases hlast : PopsIncoming s.right ∧ ∃ a, s.right.head.incoming = [a]
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hsr, hM, hi,
              Or.inr (.lastLetter hc1 hav hlast.1 hlast.2)⟩
          by_cases hmatch : read (left s.left) = read (right s.right)
          · obtain ⟨vq, hq⟩ := hsearch s hsr true
            by_cases hf : vq.search.mode = .found
            · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hsr, hM, hi,
                Or.inr (.found hc1 hav hmatch ⟨vq, hq, hf⟩)⟩
            · set vs : ScanVM := ⟨left s.left, right s.right, ChainVM.idle⟩ with hvsdef
              have hmt : (galilFrame P q first).matched (scanLens.set s vs) := hmatch
              set u : GalilVM := afterCompare s vs vq with hudef
              let o : Bool := if P.onLetter u then decide (P.leftFirst u) else c.output
              have ho : refresh (galilFrame P q first) u c.output o := by
                refine ⟨fun hl => ?_, fun hl => ?_⟩
                · have hl' : P.onLetter u := hl
                  show (if P.onLetter u then decide (P.leftFirst u) else c.output) = true ↔
                    P.leftFirst u
                  rw [if_pos hl']; exact decide_eq_true_iff
                · have hl' : ¬ P.onLetter u := hl
                  show (if P.onLetter u then decide (P.leftFirst u) else c.output) = c.output
                  rw [if_neg hl']
              have hidleU : u.chain = ChainVM.idle := by rw [hudef, afterCompare_chain]
              have hgetU : searchLens.get u = vq := rfl
              have hsrU : SearchReady (searchLens.get u) := by
                rw [hgetU]; exact hpres s true vq hsr hq
              have hMU : MInv raw {c with clock := delay, output := o, replaying := false} u :=
                minv_match o delay hrp' rfl rfl hav hmatch hi hM
              have hiU : ScanInvariant raw (position u.center) (r+1) u.left u.right := by
                have h0 := matched_invariant' raw vq (vs := vs) rfl rfl hmatch hav hi
                rw [hudef, afterCompare_center]
                exact h0
              obtain ⟨es, c', t, r', hseg, hm', hclk', hidle', hsrt, hMt, hit, hlen⟩ :=
                ih {c with clock := delay, output := o, replaying := false} u (r+1)
                  hm hd hidleU hsrU hMU hiU
              refine ⟨true :: es, c', t, r',
                .matchIdle c s vs vq o hm hrp' hav hc1 hidle rfl rfl rfl hmt hq hf ho hseg,
                hm', hclk', hidle', hsrt, hMt, hit, ?_⟩
              rcases hlen with h0 | h0
              · exact Or.inl (by simp [h0])
              · exact Or.inr h0
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hsr, hM, hi,
              Or.inr (.mismatch hrp' hc1 hav hmatch)⟩
    · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hsr, hM, hi, Or.inr (.ended hav)⟩

#print axioms idle_background_exists
#print axioms background_found_step
#print axioms watchSegE_construct

end PalPeg.GalilSegmentConstruct
