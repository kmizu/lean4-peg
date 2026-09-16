import PalPeg.GalilLeafPres
import PalPeg.GalilLeafEnds
import PalPeg.GalilOracleMC3

/-!
# The chain-idle segment without the false leaf `hpres`

`GalilLeafPres` refutes

```
hpres : ∀ s a v, SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v
```

so `GalilSegmentConstruct.watchSegE_construct`, and with it
`GalilInvPlus.segment_of_invLP` and `GalilOracleLeaves2.segment_of_invLPC`, are
vacuous in that premise.  This file re-runs the fuel induction on the
event-indexed invariant `GalilLeafPres.SearchReadyB v as = ReadyRem v as ∧
RunEntriesAll as v`, which *is* preserved (`searchReadyB_step`,
`searchReadyB_effect`) and is free at a stage restart (`searchReadyB_restarted`).

## The budget has to be closed over the run, not fixed in advance

`SearchReadyB v as` speaks about one concrete list `as` of events still ahead:
`RunEntriesAll (a :: as) v` constrains `searchStep … a …` and says nothing about
the other event, and `DpSafeRem v as` reads `as`'s length and its count of
`true`s.  The segment's event list is chosen by the *control* (clock, head,
replay flag) while the construction runs, so a single existential `as` handed in
at the entry cannot be known to be the one the machine spends.  What the
induction can thread is the closure over every budget large enough to cover the
remaining fuel and the remaining matches:

```
ReadyFuel v n K := ∀ as, n ≤ as.length → as.count true ≤ K → SearchReadyB v as
```

`n` is the fuel still to burn (one event each) and `K` the matches still
possible.  Both are honest, machine-side quantities: `n` is the `hends` fuel
`headRank s.right * delay + c.clock` of `GalilLeafEnds`, and `K` is
`headRank s.right`, because every `true` event is a comparison that steps the
right head (`GalilLeafEnds.rank_right`) while every `false` event is a
background tick, a frame on the head.  `ReadyFuel` is *weaker* the larger `n`
is and the smaller `K` is, so this is the cheapest closure the induction admits;
in particular it is not the ∀-over-all-lists closure, which is false at any
`.run` state (an all-`true` budget would demand unbounded debt).

`ReadyFuel v n K → SearchReady v` (take `List.replicate n false`), so the
landing of the segment still carries what `SegReachedW` wants.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.GalilSegmentConstructB

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilTickFun2 PalPeg.GalilBranchInvariants2
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier
open PalPeg.GalilSegmentConstruct PalPeg.GalilLeafPres PalPeg.GalilLeafEnds
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleLeaves2
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilOracleMC PalPeg.GalilGlueBLeaves
open PalPeg.GalilOracleM PalPeg.GalilOracleMC2 PalPeg.GalilFinalAssembly2
open PalPeg.GalilLeafOutReplay PalPeg.GalilOracleMC3

/-! ## 1. The budget closure -/

/-- `SearchReadyB` closed over every budget that covers `n` more events of which
at most `K` are matches. -/
def ReadyFuel (v : SearchVM) (n K : ℕ) : Prop :=
  ∀ as : List Bool, n ≤ as.length → as.count true ≤ K → SearchReadyB v as

/-- The closure still gives the bare readiness the rest of the development asks
for: spend the budget on background events only. -/
theorem readyFuel_ready {v : SearchVM} {n K : ℕ} (h : ReadyFuel v n K) : SearchReady v :=
  searchReadyB_ready (h (List.replicate n false) (by simp)
    (by simp [List.count_replicate]))

/-- Shrinking the fuel weakens nothing. -/
theorem readyFuel_mono {v : SearchVM} {n n' K K' : ℕ} (hn : n ≤ n') (hK : K' ≤ K)
    (h : ReadyFuel v n K) : ReadyFuel v n' K' :=
  fun as hlen hcnt => h as (le_trans hn hlen) (le_trans hcnt hK)

/-- **Preservation, background event.**  A `false` tick spends one unit of fuel
and no match. -/
theorem readyFuel_effect_false (P : Shared) {n K : ℕ} {s : GalilVM} {v : SearchVM}
    (hidle : s.chain = ChainVM.idle) (h : ReadyFuel (searchLens.get s) (n + 1) K)
    (he : searchEffect P false s v) : ReadyFuel v n K := by
  intro as hlen hcnt
  refine searchReadyB_effect P hidle (h (false :: as) ?_ ?_) he
  · simpa using hlen
  · simpa using hcnt

/-- **Preservation, comparison event.**  A `true` tick spends one unit of fuel
and one match. -/
theorem readyFuel_effect_true (P : Shared) {n K : ℕ} {s : GalilVM} {v : SearchVM}
    (hidle : s.chain = ChainVM.idle) (h : ReadyFuel (searchLens.get s) (n + 1) (K + 1))
    (he : searchEffect P true s v) : ReadyFuel v n K := by
  intro as hlen hcnt
  refine searchReadyB_effect P hidle (h (true :: as) ?_ ?_) he
  · simpa using hlen
  · simp only [List.count_cons]
    simp only [beq_self_eq_true, if_true]
    omega

/-- **Boot.**  At a stage restart the `ReadyRem` half is free for every budget,
so the closure reduces to the `.run`-entry datum `RunEntriesAll`. -/
theorem readyFuel_restarted {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ}
    {last : GalilScaffoldCounter.Counter} (hR : Restarted raw r Rad last) (n K : ℕ)
    (hE : ∀ as : List Bool, n ≤ as.length → as.count true ≤ K →
      RunEntriesAll as (searchLens.get r)) :
    ReadyFuel (searchLens.get r) n K :=
  fun as hlen hcnt => searchReadyB_restarted hR as (hE as hlen hcnt)

/-! ## 2. The segment construction (L7a), without `hpres` -/

/-- **`GalilSegmentConstruct.watchSegE_construct` on the event-indexed
invariant.**  Same fuel induction, same seven exits; `SearchReady` + the false
`hpres` are replaced by `ReadyFuel`, threaded along the events the run actually
emits: a background tick spends one unit of fuel, a comparison spends one unit
of fuel *and* one match, and the match budget is the right head's own rank, which
a comparison decrements (`rank_right`) and a background tick leaves alone. -/
theorem watchSegE_constructB (raw : List (Fin 2)) (P : Shared)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (hd : 1 ≤ delay)
    (hsearch : ∀ s' : GalilVM, SearchReady (searchLens.get s') → ∀ a : Bool,
      ∃ v, searchEffect P a s' v) :
    ∀ (n : ℕ) (c : Control) (s : GalilVM) (r : ℕ), c.mode = .scan → 1 ≤ c.clock →
      s.chain = ChainVM.idle → ReadyFuel (searchLens.get s) n (headRank s.right) →
      MInv raw c s → ScanInvariant raw (position s.center) r s.left s.right →
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
    exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, readyFuel_ready hsr, hM, hi, Or.inl rfl⟩
  | succ n ih =>
    intro c s r hm hclk hidle hsr hM hi
    have hrdy : SearchReady (searchLens.get s) := readyFuel_ready hsr
    by_cases hav : canRight s.right
    · have hrank : headRank (right s.right) + 1 = headRank s.right := rank_right s.right hav
      by_cases hrp : c.replaying = true
      · -- replaying
        rcases Nat.lt_or_ge 1 c.clock with hlt | hle
        · -- `countR`
          obtain ⟨v, hv⟩ := hsearch s hrdy false
          by_cases hfb : v.search.mode = .found
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hrdy, hM, hi,
              Or.inr (.foundBackground hclk ⟨v, hv, hfb⟩)⟩
          obtain ⟨s', hb, hch', hl', hr', hC', hrep', hget'⟩ :=
            idle_background_exists P q first s hidle hv hfb
          have hsr' : ReadyFuel (searchLens.get s') n (headRank s'.right) := by
            rw [hget', hr']; exact readyFuel_effect_false P hidle hsr hv
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
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hrdy, hM, hi,
              Or.inr (.lastLetter hc1 hav hlast.1 hlast.2)⟩
          have hmatch : read (left s.left) = read (right s.right) :=
            replay_match_of_minv hM hrp hav hi
          obtain ⟨vq, hq⟩ := hsearch s hrdy true
          by_cases hf : vq.search.mode = .found
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hrdy, hM, hi,
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
            have hurr : u.right = right s.right := by
              rw [hudef, replayDec_right, afterCompare_right]
            have hsrU : ReadyFuel (searchLens.get u) n (headRank u.right) := by
              rw [hgetU, hurr]
              refine readyFuel_effect_true P hidle ?_ hq
              rw [← hrank] at hsr
              exact hsr
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
          obtain ⟨v, hv⟩ := hsearch s hrdy false
          by_cases hfb : v.search.mode = .found
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hrdy, hM, hi,
              Or.inr (.foundBackground hclk ⟨v, hv, hfb⟩)⟩
          obtain ⟨s', hb, hch', hl', hr', hC', hrep', hget'⟩ :=
            idle_background_exists P q first s hidle hv hfb
          have hsr' : ReadyFuel (searchLens.get s') n (headRank s'.right) := by
            rw [hget', hr']; exact readyFuel_effect_false P hidle hsr hv
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
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hrdy, hM, hi,
              Or.inr (.lastLetter hc1 hav hlast.1 hlast.2)⟩
          by_cases hmatch : read (left s.left) = read (right s.right)
          · obtain ⟨vq, hq⟩ := hsearch s hrdy true
            by_cases hf : vq.search.mode = .found
            · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hrdy, hM, hi,
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
              have hurr : u.right = right s.right := by rw [hudef, afterCompare_right]
              have hsrU : ReadyFuel (searchLens.get u) n (headRank u.right) := by
                rw [hgetU, hurr]
                refine readyFuel_effect_true P hidle ?_ hq
                rw [← hrank] at hsr
                exact hsr
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
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hrdy, hM, hi,
              Or.inr (.mismatch hrp' hc1 hav hmatch)⟩
    · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hrdy, hM, hi, Or.inr (.ended hav)⟩

/-! ## 3. The segment out of an `InvLPC` entry, without `hpres` -/

/-- **`GalilOracleLeaves2.segment_of_invLPC` on `ReadyFuel`.**  Same body, with
`hpres` gone and the fuel bound `hends` inlined: `GalilLeafEnds.exhausted_of_long`
says that a run of `headRank r.right * 2048 + c.clock` events has run the right
head dry, which is `SegEnd.ended`.  That very number is the fuel index of the
entry premise, and its match budget is `headRank r.right`. -/
theorem segment_of_invLPCB (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (c : Control) (r : GalilVM) (hIC : InvLPC raw c r)
    (hready : ReadyFuel (searchLens.get r) (headRank r.right * 2048 + c.clock)
      (headRank r.right)) :
    ∃ (c' : Control) (t : GalilVM),
      SegReachedW centre place entry q first raw c r c' t ∧
      SegEnd (PofC centre place entry raw) c' t := by
  have hIP : InvLP raw c r := hIC.1.1
  have hI : InvS raw c r := hIP.1.1
  obtain ⟨hm, hclk, hidle, hM, R, hi, hfr, hrr, hsi⟩ :
      c.mode = Mode.scan ∧ 1 ≤ c.clock ∧ r.chain = ChainVM.idle ∧ MInv raw c r ∧
      ∃ R : ℕ, ScanInvariant raw (position r.center) R r.left r.right ∧ Frontier r ∧
        ReplayRest c r ∧ ShiftIdle r := by
    rcases hI with h | ⟨k, h⟩
    · obtain ⟨Rad, last, hR⟩ := h.rest
      exact ⟨h.mode.1, by rw [h.mode.2.2]; omega, hR.1, h.minv, Rad,
        hR.2.2.2.1, h.frontier, h.rest_replay, h.shiftIdle⟩
    · exact ⟨h.mode.1, by rw [h.mode.2.2]; omega, h.chainIdle, h.minv, k,
        h.scan, h.frontier, h.rest_replay, h.shiftIdle⟩
  obtain ⟨es, c', t, r', hseg, hm', hclk', hidle', hsrt, hMt, hit, hlen⟩ :=
    watchSegE_constructB raw (PofC centre place entry raw) hex q first 2048 (by norm_num)
      hsearch (headRank r.right * 2048 + c.clock) c r R hm hclk hidle hready hM hi
  have hEnd : SegEnd (PofC centre place entry raw) c' t := by
    rcases hlen with h0 | h0
    · exact .ended (exhausted_of_long (PofC centre place entry raw) q first 2048 (by norm_num)
        hseg hclk (le_of_eq h0.symm))
    · exact h0
  obtain ⟨k1, h1⟩ :=
    watchSegE_stepsAll raw (PofC centre place entry raw) rfl rfl q first 2048 hseg
      (position r.center) R hi hIP.1.2
  have hrun : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) k ⟨c, r⟩ ⟨c', t⟩ :=
    ⟨k1, stepsAll_mono (fun _ h0 _ _ => h0) h1⟩
  have hsteps : Steps (galilFrameS (PofC centre place entry raw) q first) 2048 es.length
      ⟨c, r⟩ ⟨c', t⟩ := watchSegE_steps_length _ q first 2048 hseg
  have hfrt : Frontier t ∧ ReplayRest c' t :=
    frontier_replayRest_of_scan (onLetterVM raw) leftFirstVM centre place
      entry q first 2048 hsteps hm (hlive_of_invLPC centre place entry q first hIC) hfr hrr
  have hsit : ShiftIdle t := by
    rw [shiftIdle_iff, watchSegE_remaining _ q first 2048 hseg]
    exact (shiftIdle_iff r).1 hsi
  exact ⟨c', t,
    ⟨{ run := hrun
       center := watchSegE_center _ q first 2048 hseg
       mode := hm'
       clock := hclk'
       idle := hidle'
       minv := hMt
       search := hsrt
       input := hit.rightRep
       frontier := hfrt.1
       shiftIdle := hsit
       scan := ⟨r', hit⟩ }, es, hseg⟩, hEnd⟩

/-! ## 4. `H_oracle` with the segment leaf closed -/

/-- **`GalilOracleMC3.h_oracle_of_leaves''` with the segment site off `hpres`.**

`hends` is discharged outright (it is `GalilLeafEnds.hends_C`, here inlined into
`segment_of_invLPCB`), and the segment leaf `hsegmentM` of
`GalilOracleMC3.cycleOracleMC2C_of_pieces'` is supplied from `hreadyB` — the one
named residual:

```
hreadyB : ∀ w c r, InvLPC w c r →
    ReadyFuel (searchLens.get r) (headRank r.right * 2048 + c.clock) (headRank r.right)
```

i.e. **at every `InvLPC` landing, for every event budget `as` with
`headRank r.right * 2048 + c.clock ≤ as.length` and
`as.count true ≤ headRank r.right`, both `GalilSearchReadyInv.ReadyRem
(searchLens.get r) as` and `GalilLeafPres.RunEntriesAll as (searchLens.get r)`
hold.**  Its `ReadyRem` half is free at a stage restart
(`GalilLeafPres.searchReadyB_restarted`, via `readyFuel_restarted`), so what the
landings really have to supply is `RunEntriesAll` — the `.run`-entry datum, the
single named gap of `GalilSearchReadyInv` (`search_first_stage` /
`search_later_stage` establish it for a calibrated stage).  `RunEntriesAll` at a
landing is *not* derivable here, so it stays as this residual.

`hpres` does **not** disappear from the assembly: `cycleOracleMC2C_of_pieces'`
consumes it at two further sites, whose signatures are fixed in already-landed
files and cannot be weakened from a new module —

* `GalilOracleMC2.reachAtC2_of_target_match`, where it is used exactly once, as
  `hpres t true vq hs.search hq`: readiness of the search at the landing of the
  target comparison;
* `GalilOracleMC3.invScanO_of_replay_generalR`, which passes it through to
  `GalilFoundStage.replay_after_fallback_general` (triple-primed) for the whole
  fallback replay.

Closing those two means re-proving those two theorems on `ReadyFuel`; until then
this theorem is still vacuous in `hpres`, and only its segment half is repaired. -/
theorem h_oracle_of_leaves''' (entry q : ℕ) (first : Fin 9)
    (hreadyB : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvLPC w c r →
      ReadyFuel (searchLens.get r) (headRank r.right * 2048 + c.clock) (headRank r.right))
    (hpres : ∀ (w : List (Fin 2)) (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centreC placeC entry w) a s v → SearchReady v)
    (hshape : ∀ w : List (Fin 2),
      PalPeg.GalilWatchOkInst.StartShape (PofC centreC placeC entry w))
    (hbudget : ∀ w : List (Fin 2),
      PalPeg.GalilFoundStage.ReplayBudgetR w (PofC centreC placeC entry w) q first 2048)
    (hstage : ∀ w : List (Fin 2),
      PalPeg.GalilFoundStage.ReplayStageInv w (PofC centreC placeC entry w) q first)
    (hrs : ∀ w : List (Fin 2),
      PalPeg.GalilReplaySpan.RestartShape (PofC centreC placeC entry w))
    (hended : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t → ¬ canRight t.right →
      ReachAtC2 (PofC centreC placeC entry w) q first w m c r)
    (hlastMatch : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      ReachAtC2 (PofC centreC placeC entry w) q first w m c r)
    (hlastMismatch : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      ReachAtC2 (PofC centreC placeC entry w) q first w m c r)
    (hmismatch : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRouteMC2 (PofC centreC placeC entry w) q first w m c r c' t)
    (hfound : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centreC placeC entry w) true t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centreC placeC entry w) q first w m c r c' t)
    (hfoundBg : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centreC placeC entry w) false t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centreC placeC entry w) q first w m c r c r)
    (hfoundReplay : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (cT : Control)
      (sT : GalilVM) (R k : ℕ), 1 ≤ m → m ≤ w.length → InvLPC w c r →
      StepsAll (galilFrameS (PofC centreC placeC entry w) q first) 2048 (SoundScanNR w) k
        ⟨c, r⟩ ⟨cT, sT⟩ →
      ReplayLanding w cT sT R → SpanRep sT →
      position r.center < position sT.center → position sT.right ≤ 2 * m - 1 →
      (PalPeg.GalilReplaySpan.ChainEnd w (PofC centreC placeC entry w) q first 2048
          (position sT.right + R) cT sT 0 R ∨
        PalPeg.GalilReplaySpan.BrokeAndRestarted w (PofC centreC placeC entry w) q first 2048
          cT sT) →
      FoundInReplayRouteMC2 (PofC centreC placeC entry w) q first w m c r)
    (hstr : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvL w c r → InvLPC w c r) :
    PalPeg.GalilFinalAssembly.H_oracle centreC placeC entry q first :=
  fun w _ => cycleOracleMC_of_MC2C
    (cycleOracleMC2C_of_pieces' centreC placeC entry q first w
      (fun s => hex_C centreC placeC entry w s)
      (fun s hs a => hsearch_C centreC placeC entry w s hs a)
      (hpres w) (hshape w) (hbudget w) (hstage w) (hrs w)
      (fun m c r _ _ hIC _ => by
        obtain ⟨c', t, hsW, hEnd⟩ :=
          segment_of_invLPCB centreC placeC entry q first w
            (fun s => hex_C centreC placeC entry w s)
            (fun s hs a => hsearch_C centreC placeC entry w s hs a) c r hIC
            (hreadyB w c r hIC)
        exact ⟨c', t, hsW, Or.inr hEnd⟩)
      (hended w) (hlastMatch w) (hlastMismatch w) (hmismatch w) (hfound w) (hfoundBg w)
      (hfoundReplay w)) (hstr w)

#print axioms watchSegE_constructB
#print axioms segment_of_invLPCB
#print axioms h_oracle_of_leaves'''

end PalPeg.GalilSegmentConstructB
