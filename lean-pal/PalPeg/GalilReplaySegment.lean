import PalPeg.GalilRunInv
import PalPeg.GalilSegmentConstruct

/-!
# The replay segment after a fallback (gap 1 of `PalPeg.GalilRunInv`)

`inv_after_fallback` of `PalPeg.GalilRunInv` only covers the fallback whose
FPP chose radius `0`: the landing controller then has `replaying = false` and
the `mode` field of `Inv` holds outright.  When the chosen radius is `r > 0`
the landing controller has `replaying = true`, the replay counter reads `r`
and the right head sits on the new centre (`Restarted raw t 0 reset`), so the
machine still owes `r` replay rounds before it is parked in a fresh scan.

This module runs those rounds.  One round is `delay - 1` background ticks
(`WatchSegE.countR`) followed by one matched comparison
(`WatchSegE.matchIdleR`); the comparison cannot fail, because
`replay_match_of_minv` of `PalPeg.GalilTickFun2` derives the match from
`MInv`.  After `r` rounds the replay counter is empty, the controller has
`replaying = false` and `clock = delay`, and the right head has walked back to
the place the fallback left, `r` places to the right of the centre, with the
scan invariant at radius `r`.

Two hypotheses are *not* discharged here and are named as such:

* `hquiet` — the search co-run does not report `found` while the replay is in
  flight.  Both replay constructors require it (`countR` through
  `idle_background_exists`, `matchIdleR` through its own `hnf`), and it is the
  ledger's statement that the FPP cannot finish a stage inside the `≤ 4δ`
  ticks of a replay.  It is assumed for every `SearchReady` state.
* the output relation at the landing state.  Every state of the run *inside*
  the replay has `replaying = true`, where `SoundScanNR` is vacuous, so the
  run carries `SoundScanNR` as soon as its final state does; the final state's
  obligation is handed back to the caller as the premise of the `StepsAll`
  conclusion.
-/

set_option autoImplicit false

namespace PalPeg.GalilReplaySegment

open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilTickFun2 PalPeg.GalilBranchInvariants2
  PalPeg.GalilSegmentConstruct
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## Small facts -/

/-- `SoundScanNR` is vacuous while replaying. -/
theorem soundScanNR_replaying (raw : List (Fin 2)) {st : State GalilVM}
    (h : st.ctl.replaying = true) : SoundScanNR raw st := by
  intro _ hf; rw [h] at hf; cases hf

/-- A head with replay budget left can still step right: the frontier bound
puts material on its right stack. -/
theorem canRight_of_frontier {p : PlaceHead} {m : ℕ} (hm : 0 < m)
    (h : position p + m ≤ 2 * arrived p) : canRight p := by
  rcases p with ⟨⟨f, ls, rs, qs⟩, g⟩
  cases g with
  | false => exact Or.inl rfl
  | true =>
    refine Or.inr (Or.inl ?_)
    intro h0
    simp only [position, arrived, if_true] at h
    change rs = [] at h0
    rw [h0] at h
    simp at h
    omega

theorem afterCompare_remaining (s : GalilVM) (vs : ScanVM) (vq : SearchVM) :
    (afterCompare s vs vq).remaining = s.remaining := rfl

theorem replayDec_remaining (b : Bool) (s : GalilVM) : (replayDec b s).remaining = s.remaining := by
  cases b <;> rfl


/-! ## One replay round -/

section Round

variable (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)

/-- The co-run hypotheses of `watchSegE_construct`, plus the one that is new
here: while the search is ready it never reports `found`. -/
def SearchQuiet : Prop :=
  ∀ (s : GalilVM) (a : Bool) (v : SearchVM), SearchReady (searchLens.get s) →
    searchEffect P a s v → v.search.mode ≠ .found

/-- **The counting part of a replay round.**  From a replaying scan state with
`clock = j+1` and an idle chain, `j` background ticks (`WatchSegE.countR`)
reach `clock = 1` without touching the heads, the centre or the replay
counter. -/
theorem countR_run
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hquiet : SearchQuiet P) :
    ∀ (j : ℕ) (c : Control) (s : GalilVM), c.mode = .scan → c.replaying = true →
      c.clock = j + 1 → s.chain = ChainVM.idle → SearchReady (searchLens.get s) →
      ∃ (c1 : Control) (t : GalilVM),
        WatchSegE P q first delay (List.replicate j false) c s c1 t ∧
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) j ⟨c, s⟩ ⟨c1, t⟩ ∧
        c1.mode = c.mode ∧ c1.replaying = c.replaying ∧ c1.clock = 1 ∧
        t.chain = ChainVM.idle ∧ SearchReady (searchLens.get t) ∧
        t.left = s.left ∧ t.right = s.right ∧ t.center = s.center ∧
        t.replay = s.replay ∧ t.remaining = s.remaining := by
  intro j
  induction j with
  | zero =>
    intro c s hm hr hc hidle hsr
    exact ⟨c, s, .stop _ _, .zero _ (soundScanNR_replaying raw hr), rfl, rfl, hc, hidle, hsr,
      rfl, rfl, rfl, rfl, rfl⟩
  | succ j ih =>
    intro c s hm hr hc hidle hsr
    obtain ⟨v, hv⟩ := hsearch s hsr false
    obtain ⟨s', hb, hch', hl', hr', hC', hrep', hget'⟩ :=
      idle_background_exists P q first s hidle hv (hquiet s false v hsr hv)
    have hsr' : SearchReady (searchLens.get s') := by rw [hget']; exact hpres s false v hsr hv
    have hclt : 1 < c.clock := by omega
    have hrem' : s'.remaining = s.remaining := (backgroundS_fields P q first hb).2.2.2.2.2.2.2.2.1
    obtain ⟨c1, t, hseg, hst, hm1, hr1, hc1, hidle1, hsr1, hl1, hrr1, hC1, hrp1, hrem1⟩ :=
      ih {c with clock := c.clock - 1} s' hm hr (by simp; omega) hch' hsr'
    refine ⟨c1, t, .countR c s s' hm hr hclt hidle hb hseg,
      .succ (soundScanNR_replaying raw hr) (.scan_count c s s' hm (Or.inl hr) hclt hb) hst,
      hm1, hr1, hc1, hidle1, hsr1, by rw [hl1, hl'], by rw [hrr1, hr'], by rw [hC1, hC'],
      by rw [hrp1, hrep'], by rw [hrem1, hrem']⟩

/-- **The comparison of a replay round.**  At `clock = 1`, still replaying and
with `r = m+1` places left, the comparison is forced to match
(`replay_match_of_minv`), the replay counter drops to `m`, the right head
advances one place and the controller comes back with a full clock and
`replaying = decide (0 < m)`. -/
theorem match_round (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hquiet : SearchQuiet P)
    (c : Control) (s : GalilVM) (k m : ℕ)
    (hm : c.mode = .scan) (hr : c.replaying = true) (hc : c.clock = 1)
    (hidle : s.chain = ChainVM.idle) (hsr : SearchReady (searchLens.get s))
    (hM : MInv raw c s) (hi : ScanInvariant raw (position s.center) k s.left s.right)
    (hrp : s.replay = ofNat (m+1)) (hfr : Frontier s) :
    ∃ (c1 : Control) (u : GalilVM),
      WatchSegE P q first delay [true] c s c1 u ∧
      (SoundScanNR raw ⟨c1, u⟩ →
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) 1 ⟨c, s⟩ ⟨c1, u⟩) ∧
      c1.mode = .scan ∧ c1.clock = delay ∧ c1.replaying = decide (0 < m) ∧
      u.chain = ChainVM.idle ∧ SearchReady (searchLens.get u) ∧ MInv raw c1 u ∧
      ScanInvariant raw (position u.center) (k+1) u.left u.right ∧
      u.replay = ofNat m ∧ position u.right = position s.right + 1 ∧
      u.center = s.center ∧ Frontier u ∧ u.remaining = s.remaining := by
  classical
  have hbound : position s.right + (m+1) ≤ 2 * arrived s.right := hfr (m+1) hrp
  have hav : canRight s.right := canRight_of_frontier (Nat.succ_pos m) hbound
  have hmatch : read (left s.left) = read (right s.right) := replay_match_of_minv hM hr hav hi
  obtain ⟨vq, hq⟩ := hsearch s hsr true
  have hnf : vq.search.mode ≠ .found := hquiet s true vq hsr hq
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
  refine ⟨{c with clock := delay, output := o, replaying := !P.replayExhausted u}, u,
    .matchIdleR c s vs vq o hm hr hc hav hidle rfl rfl rfl hmt hq hnf ho (.stop _ _), ?_,
    hm, rfl, hflag, ?_, ?_, ?_, ?_, hurep, ?_, ?_, ?_, ?_⟩
  · intro hlast
    have ht := scan_match_idle_S' P q first delay c s vs vq o hm (Or.inl hr) hc hidle rfl rfl rfl
      hmt hq hnf (by rw [hr]; exact ho)
    rw [hr] at ht
    exact .succ (soundScanNR_replaying raw hr) (by simpa using ht) (.zero _ hlast)
  · rw [hudef, replayDec_chain, afterCompare_chain]
  · have hgetU : searchLens.get u = vq := by rw [hudef, replayDec_search]; rfl
    rw [hgetU]; exact hpres s true vq hsr hq
  · exact minv_matchR P hex o delay hr rfl hav hi hM
  · have h0 := matched_invariant' raw vq (vs := vs) rfl rfl hmatch hav hi
    rw [hudef, replayDec_left, replayDec_right, replayDec_center, afterCompare_center]
    exact h0
  · have hpos : position (right s.right) = position s.right + 1 :=
      right_position s.right hav (represented_position _ raw hi.rightRep hi.rightPresent).1
    rw [hudef, replayDec_right, afterCompare_right]
    exact hpos
  · rw [hudef, replayDec_center, afterCompare_center]
  · intro m' hm'
    have hmm : m' = m := (ofNat_inj (hurep.symm.trans hm')).symm
    subst hmm
    have hur : u.right = right s.right := by rw [hudef, replayDec_right, afterCompare_right]
    rw [hur]
    exact right_frontier_step s.right m' hbound
  · rw [hudef, replayDec_remaining, afterCompare_remaining]

/-! ## The whole replay -/

/-- **`replay_segment_construct`.**  From a scan state that is `r` places into
a replay — controller parked with a full clock and `replaying = decide (0 < r)`,
replay counter `ofNat r`, chain idle — the machine runs `r` rounds of
`delay - 1` background ticks plus one forced comparison and comes out of the
replay: `replaying = false`, `clock = delay`, an empty replay counter, the
right head `r` places further right and the scan invariant at radius `k + r`.

The run is `r * delay` ticks long and carries `SoundScanNR raw` as soon as its
final state does (every earlier state is replaying, where the predicate is
vacuous). -/
theorem replay_segment_construct (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hquiet : SearchQuiet P) :
    ∀ (r : ℕ) (c : Control) (s : GalilVM) (k : ℕ),
      c.mode = .scan → c.clock = delay → c.replaying = decide (0 < r) →
      s.replay = ofNat r → s.chain = ChainVM.idle → SearchReady (searchLens.get s) →
      MInv raw c s → ScanInvariant raw (position s.center) k s.left s.right → Frontier s →
      ∃ (es : List Bool) (c' : Control) (t : GalilVM),
        WatchSegE P q first delay es c s c' t ∧
        (SoundScanNR raw ⟨c', t⟩ →
          StepsAll (galilFrameS P q first) delay (SoundScanNR raw) es.length ⟨c, s⟩ ⟨c', t⟩) ∧
        es.length = r * delay ∧ es.count true = r ∧
        c'.mode = .scan ∧ c'.clock = delay ∧ c'.replaying = false ∧
        t.replay = reset ∧ t.chain = ChainVM.idle ∧ SearchReady (searchLens.get t) ∧
        MInv raw c' t ∧ ScanInvariant raw (position t.center) (k + r) t.left t.right ∧
        position t.right = position s.right + r ∧ t.center = s.center ∧
        Frontier t ∧ ReplayRest c' t ∧ t.remaining = s.remaining := by
  intro r
  induction r with
  | zero =>
    intro c s k hm hc hrp hrep hidle hsr hM hi hfr
    have hrf : c.replaying = false := by rw [hrp]; simp
    have hreset : s.replay = reset := by rw [hrep, ← reset_eq_ofNat]
    exact ⟨[], c, s, .stop _ _, fun hlast => .zero _ hlast, by simp, by simp, hm, hc, hrf,
      hreset, hidle, hsr, hM, by simpa using hi, by simp, rfl, hfr,
      replayRest_of_reset hreset, rfl⟩
  | succ n ih =>
    intro c s k hm hc hrp hrep hidle hsr hM hi hfr
    have hrt : c.replaying = true := by rw [hrp]; simp
    obtain ⟨c1, t1, hseg1, hst1, hm1, hr1, hc1, hidle1, hsr1, hl1, hrr1, hC1, hrp1, hrem1⟩ :=
      countR_run raw P q first delay hsearch hpres hquiet (delay - 1) c s hm hrt
        (by omega) hidle hsr
    have hm1' : c1.mode = Mode.scan := by rw [hm1, hm]
    have hr1' : c1.replaying = true := by rw [hr1, hrt]
    have hM1 : MInv raw c1 t1 := minv_same (by rw [hr1]) hrr1 hC1 hrp1 hM
    have hi1 : ScanInvariant raw (position t1.center) k t1.left t1.right := by
      rw [hl1, hrr1, hC1]; exact hi
    have hfr1 : Frontier t1 := frontier_congr hrr1 hrp1 hfr
    obtain ⟨c2, u, hseg2, hst2, hm2, hc2, hr2, hidle2, hsr2, hM2, hi2, hrep2, hpos2, hC2,
        hfr2, hrem2⟩ :=
      match_round raw P q first delay hex hsearch hpres hquiet c1 t1 k n hm1' hr1' hc1 hidle1
        hsr1 hM1 hi1 (by rw [hrp1, hrep]) hfr1
    obtain ⟨es3, c3, t3, hseg3, hst3, hlen3, hcnt3, hm3, hc3, hr3, hrep3, hidle3, hsr3, hM3,
        hi3, hpos3, hC3, hfr3, hrr3, hrem3⟩ :=
      ih c2 u (k+1) hm2 hc2 hr2 hrep2 hidle2 hsr2 hM2 hi2 hfr2
    refine ⟨List.replicate (delay - 1) false ++ true :: es3, c3, t3,
      watchSegE_trans P q first delay hseg1 (watchSegE_trans P q first delay hseg2 hseg3),
      ?_, ?_, ?_, hm3, hc3, hr3, hrep3, hidle3, hsr3, hM3, ?_, ?_, ?_, hfr3, hrr3, ?_⟩
    · intro hlast
      have hs3 := hst3 hlast
      have hs2 := hst2 (stepsAll_head hs3)
      have hcomp := stepsAll_trans hst1 (stepsAll_trans hs2 hs3)
      have hlen : (List.replicate (delay - 1) false ++ true :: es3).length =
          delay - 1 + (1 + es3.length) := by simp; omega
      rw [hlen]
      exact hcomp
    · simp only [List.length_append, List.length_replicate, List.length_cons, hlen3]
      cases delay with
      | zero => omega
      | succ d => simp; ring
    · simp [hcnt3, List.count_replicate]
    · have e : k + (n + 1) = k + 1 + n := by omega
      rw [e, hC3, hC2, hC1]
      rw [hC3, hC2, hC1] at hi3
      exact hi3
    · rw [hpos3, hpos2, hrr1]; omega
    · rw [hC3, hC2, hC1]
    · rw [hrem3, hrem2, hrem1]

end Round

/-! ## The landing state

`Inv` of `PalPeg.GalilRunInv` cannot hold verbatim at the end of a replay.
Its first field asks for `∃ Rad last, Restarted raw t Rad last`, and three
clauses of `Restarted` are false there:

* `ScanInvariant raw (position t.center) Rad t.left t.right` with the `Rad`
  that `Restarted` pins — the fallback landed with `Rad = 0` (the right head
  *on* the centre), while after the replay the right head is `r` places to the
  right and the invariant holds at radius `r`;
* `RadiusRep t.radius Rad` — every matched comparison of the replay increments
  the radius counter, so it now reads `r`, not `0`;
* `t.search = GalilScaffoldSearchFinish.begin last t.radius` — the search
  co-run has taken `r * delay` quanta and its radius argument has moved.

Restating `Restarted` with `Rad = r` would repair the first two, but not the
third: the search is genuinely no longer parked at `begin`, only `SearchReady`.
So the landing is packaged as `InvScan`: `Inv` with `rest` replaced by the
chain-idle fact and the scan invariant at the explicit radius, and with the
`stage` field dropped (it is a statement *about* `Restarted` and so has no
content once `Restarted` is gone). -/

/-- `Inv` minus `rest` and `stage`, plus the chain-idle fact and the scan
invariant at radius `k`. -/
structure InvScan (delay : ℕ) (raw : List (Fin 2)) (c : Control) (s : GalilVM) (k : ℕ) : Prop where
  /-- no chain is running -/
  chainIdle : s.chain = ChainVM.idle
  /-- the scan invariant, at the radius the replay rebuilt -/
  scan : ScanInvariant raw (position s.center) k s.left s.right
  /-- the centre invariant (completeness) -/
  minv : MInv raw c s
  /-- the controller is parked in a fresh scan with the full match delay -/
  mode : c.mode = Mode.scan ∧ c.replaying = false ∧ c.clock = delay
  /-- branch coverage (iii)+(iv) for the search co-run -/
  search : SearchReady (searchLens.get s)
  /-- branch coverage (i)+(ii) for the chain -/
  block : GalilBranchInvariants.BlockInv s.chain
  /-- the replay counter never points past the arrived material -/
  frontier : Frontier s
  /-- the `replaying` flag and the replay counter agree at rest -/
  rest_replay : ReplayRest c s
  /-- the right head still represents the input word -/
  input : GalilScaffoldInputTrace.Represents s.right.head raw
  /-- no chain shift is in flight -/
  shiftIdle : ShiftIdle s

theorem shiftIdle_congr {s t : GalilVM} (h : t.remaining = s.remaining) (hs : ShiftIdle s) :
    ShiftIdle t := by
  rw [shiftIdle_iff, h]; exact (shiftIdle_iff s).1 hs

/-- **`inv_after_replay`.**  The state the replay lands in carries every field
of `Inv` except `rest` and `stage`, in the form `InvScan`. -/
theorem inv_after_replay (delay : ℕ) (raw : List (Fin 2)) (c : Control) (t : GalilVM) (k : ℕ)
    (hm : c.mode = Mode.scan) (hc : c.clock = delay) (hr : c.replaying = false)
    (hidle : t.chain = ChainVM.idle)
    (hi : ScanInvariant raw (position t.center) k t.left t.right)
    (hM : MInv raw c t) (hsr : SearchReady (searchLens.get t))
    (hrep : t.replay = reset) (hsi : ShiftIdle t) : InvScan delay raw c t k :=
  { chainIdle := hidle, scan := hi, minv := hM, mode := ⟨hm, hr, hc⟩, search := hsr
    block := by rw [hidle]; trivial
    frontier := frontier_of_reset hrep
    rest_replay := replayRest_of_reset hrep
    input := hi.rightRep
    shiftIdle := hsi }

/-- **The gap-1 cycle.**  The landing state of `fallback_restarted_soundNR`
with a *positive* chosen radius `r` runs its `r` replay rounds and comes out
carrying `InvScan` at radius `r`, `r * delay` ticks later, with the right head
back where the fallback found it. -/
theorem replay_after_fallback (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (delay : ℕ) (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hquiet : SearchQuiet P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = delay) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :
    ∃ (es : List Bool) (c' : Control) (t' : GalilVM),
      WatchSegE P q first delay es c t c' t' ∧
      (SoundScanNR raw ⟨c', t'⟩ →
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) es.length ⟨c, t⟩ ⟨c', t'⟩) ∧
      es.length = r * delay ∧ es.count true = r ∧
      position t'.right = position t.right + r ∧ t'.center = t.center ∧
      InvScan delay raw c' t' r := by
  obtain ⟨es, c', t', hseg, hst, hlen, hcnt, hm', hc', hr', hrep', hidle', hsr', hM', hi',
      hpos', hC', hfr', hrr', hrem'⟩ :=
    replay_segment_construct raw P q first delay hex hd hsearch hpres hquiet r c t 0
      hm hc (by rw [hrpl]; simp [hr0]) hrep hR.1 (searchReady_of_restarted hR) hM
      hR.2.2.2.1 hfr
  exact ⟨es, c', t', hseg, hst, hlen, hcnt, hpos', hC',
    inv_after_replay delay raw c' t' r hm' hc' hr' hidle' (by simpa using hi') hM' hsr' hrep'
      (shiftIdle_congr hrem' hsi)⟩

#print axioms canRight_of_frontier
#print axioms countR_run
#print axioms match_round
#print axioms replay_segment_construct
#print axioms inv_after_replay
#print axioms replay_after_fallback

end PalPeg.GalilReplaySegment
