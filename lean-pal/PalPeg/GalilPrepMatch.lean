import PalPeg.GalilPrepClock
import PalPeg.GalilMidRoundFallback
import PalPeg.GalilMismatchCaught

/-!
# Comparisons during the preparation: `hmatch` is not a theorem, the exit is a fallback

`GalilPrepClock.prep_segment_construct_general` / `_matched` carry `hmatch`:
every comparison the clock forces inside the `2h+2`-tick preparation matches.

## Why `hmatch` is false in general

At the found comparison the scan is at the centre `C` (the search walker's
place, `found_radius_le_all_stages`: `r.center = represent ⟨a :: ls, gap⟩ …`)
with radius `k0`.  What the data guarantee about `C` itself is only
`ScanInvariant … C k0` (so `PalAt … C k0`, one more after the matched found
comparison).  The DP candidate (`candidate_palAt`) speaks about the *left*
window `[C-4h, C]` — palindromes about `C-h` and `C-2h` — and nothing about the
symbols right of `C+k0+1`, which are fresh input.  A comparison during the
preparation reads exactly those symbols (radius `k0+2, k0+3, …`), so it can
mismatch.  (`GalilMismatchCaught.no_mismatch_before_caught` is about the
*shifted* centre `C-2h` after a shift, not about `C`.)

It is *vacuously* true when no comparison is forced: from the clock `delay`
set by the found comparison, a comparison inside the `2h+2` ticks needs
`delay - 1` counting ticks, so `2*h+2 < delay` makes `hmatch` vacuous
(`hmatch_of_clock`) — exactly the bound of `GalilPrepConstruct`.

## What happens on a mismatch during preparation

The chain is `.copy` / `.back` with positive lag.  Its disabled tick is a
`ChainStep` to `.copy`, `.back`, or (at `backDone`) a `.watch` with the *same*
positive lag.  `shiftGuardVM` needs a zero-lag `.watch`, so it fails
(`prep_guard_false`): the model takes `Tick.scan_fallback`.

* `drive_or_mismatch` — `GalilPrepClock.drive` without `hmatch`: either the full
  segment, or a strictly shorter prefix ending at a clock-one mismatching
  comparison with the family still `R (m+1)`.
* `prep_segment_construct_or_fallback` (and `_matched`) — the preparation
  segment, or a mismatch stop whose chain is `PrepChain` (copy/back, lag ≥ 1),
  whose disabled chain tick exists, and at which the shift guard is false for
  every disabled chain tick.
* `fallback_from_prep` — `fallback_landing` from that stop (the analogue of
  `GalilMidRoundFallback.fallback_from_watch`), with the guard failure proved.

## Gaps

`fallback_from_prep` keeps `fallback_landing`'s input-tape hypotheses
(`hi : ShiftIdle`, `hrep`, `hfoc`, `hcan`, `heven`, `hout`) as named
hypotheses, exactly like `fallback_from_watch`.
-/

set_option autoImplicit false
namespace PalPeg.GalilPrepMatch

open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilBranchInvariants PalPeg.GalilPrepClock
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## 1. `hmatch` is vacuous below the delay -/

/-- Along a segment the clock drops by at most one per event. -/
theorem watchSegE_clock_le (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (hseg : WatchSegE P qq first delay es c s c' t) : c.clock ≤ c'.clock + es.length := by
  induction hseg with
  | stop => simp
  | wait _ _ _ _ _ _ _ _ ih => simp only [List.length_cons]; omega
  | count _ _ _ _ _ _ hc _ _ ih => simp only [List.length_cons] at ih ⊢; omega
  | «match» _ _ _ _ _ _ _ _ hc _ _ _ _ _ _ ih => simp only [List.length_cons]; omega
  | matchIdle _ _ _ _ _ _ _ _ hc _ _ _ _ _ _ _ _ _ ih => simp only [List.length_cons]; omega
  | countR _ _ _ _ _ hc _ _ _ ih => simp only [List.length_cons] at ih ⊢; omega
  | matchIdleR _ _ _ _ _ _ _ hc _ _ _ _ _ _ _ _ _ _ ih => simp only [List.length_cons]; omega

/-- **`hmatch` holds vacuously when the preparation fits in one delay.** -/
theorem hmatch_of_clock (P : Shared) (qq : ℕ) (first : Fin 9) (delay h : ℕ)
    (cF' : Control) (sF : GalilVM) (hclk : cF'.clock = delay) (hh : 2*h+2 < delay) :
    ∀ (es0 : List Bool) (c' : Control) (v : GalilVM),
      WatchSegE P qq first delay es0 cF' sF c' v → es0.length < 2*h+2 → c'.clock = 1 →
      canRight v.right → read (left v.left) = read (right v.right) := by
  intro es0 c' v hs hl hc _
  have := watchSegE_clock_le P qq first delay hs
  omega

/-! ## 2. The driver with a mismatch exit -/

/-- **`drive` without `hmatch`.**  Either the full `n`-tick segment, or a
strictly shorter prefix ending at a clock-one comparison whose outer symbols
disagree, with the family still at `R (m+1)`. -/
theorem drive_or_mismatch (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ) (hdelay : 1 ≤ delay)
    (R : ℕ → ChainVM → Prop) (f : ChainVM → ℤ)
    (hstep : ∀ (n : ℕ) (x : ChainVM), R (n+1) x → x ≠ ChainVM.idle ∧
      ∀ a : Bool, ∃ y, ChainTick a x y ∧ R n y ∧ f y = f x + (if a then 1 else 0)) :
    ∀ (n : ℕ) (c : Control) (s : GalilVM), c.mode = .scan → c.replaying = false →
      1 ≤ c.clock → c.clock ≤ delay → R n s.chain →
      (∃ (es : List Bool) (c' : Control) (t : GalilVM),
        WatchSegE P qq first delay es c s c' t ∧ es.length = n ∧ R 0 t.chain ∧
        f t.chain = f s.chain + (es.count true : ℤ) ∧
        c'.mode = .scan ∧ c'.replaying = false ∧ 1 ≤ c'.clock ∧ c'.clock ≤ delay) ∨
      (∃ (es : List Bool) (c' : Control) (t : GalilVM) (m : ℕ),
        WatchSegE P qq first delay es c s c' t ∧ es.length + (m+1) = n ∧ R (m+1) t.chain ∧
        f t.chain = f s.chain + (es.count true : ℤ) ∧
        c'.mode = .scan ∧ c'.replaying = false ∧ c'.clock = 1 ∧ canRight t.right ∧
        read (left t.left) ≠ read (right t.right)) := by
  intro n
  induction n with
  | zero =>
    intro c s hm hr h1 h2 hR
    exact Or.inl ⟨[], c, s, .stop _ _, rfl, hR, by simp, hm, hr, h1, h2⟩
  | succ n ih =>
    intro c s hm hr h1 h2 hR
    obtain ⟨hne, htick⟩ := hstep n s.chain hR
    by_cases hav : canRight s.right
    · by_cases hc1 : c.clock = 1
      · by_cases hm0 : read (left s.left) = read (right s.right)
        · obtain ⟨y, hty, hRy, hfy⟩ := htick true
          let vs : ScanVM := ⟨left s.left, right s.right, y⟩
          let vq : SearchVM := searchLens.get s
          have hcmp : (galilFrame P qq first).compare s (scanLens.set s vs) := by
            refine Lens.rel_set scanLens _ s _ ⟨rfl, rfl, ?_⟩
            show ChainTick (decide (read (left s.left) = read (right s.right))) s.chain y
            rw [decide_eq_true hm0]; exact hty
          have hmt : (galilFrame P qq first).matched (scanLens.set s vs) := by
            show read (scanLens.get (scanLens.set s vs)).left
              = read (scanLens.get (scanLens.set s vs)).right
            rw [scanLens.get_set]; exact hm0
          have hq : searchEffect P true s vq := Or.inr ⟨hne, rfl⟩
          obtain ⟨o, ho⟩ := GalilRoundConstruct.frame_refresh_exists P qq first
            (afterCompare s vs vq) c.output
          have hch : (afterCompare s vs vq).chain = y := afterCompare_chain s vs vq
          rcases ih {c with clock := delay, output := o, replaying := false} (afterCompare s vs vq)
              hm rfl hdelay le_rfl (by rw [hch]; exact hRy) with
            ⟨es, c', t, hseg, hlen, hR0, hf, hm', hr', h1', h2'⟩ |
            ⟨es, c', t, m, hseg, hlen, hRm, hf, hm', hr', hc', ha', hmis'⟩
          · refine Or.inl ⟨true :: es, c', t,
              .match c s vs vq o hm hr hav hc1 hne hcmp hmt hq ho hseg,
              by simp [hlen], hR0, ?_, hm', hr', h1', h2'⟩
            rw [hf, hch, hfy]; simp; ring
          · refine Or.inr ⟨true :: es, c', t, m,
              .match c s vs vq o hm hr hav hc1 hne hcmp hmt hq ho hseg,
              by simp; omega, hRm, ?_, hm', hr', hc', ha', hmis'⟩
            rw [hf, hch, hfy]; simp; ring
        · exact Or.inr ⟨[], c, s, n, .stop _ _, by simp, hR, by simp, hm, hr, hc1, hav, hm0⟩
      · obtain ⟨y, hty, hRy, hfy⟩ := htick false
        obtain ⟨m, hsm, hym⟩ := hty
        simp only [Bool.false_eq_true, if_false] at hym
        subst hym
        obtain ⟨s', hb, hch', -⟩ := GalilPrepConstruct.active_background_exists P qq first s hne hsm
        have hlt : 1 < c.clock := by omega
        rcases ih {c with clock := c.clock - 1} s' hm hr (by simp only []; omega)
            (by simp only []; omega) (by rw [hch']; exact hRy) with
          ⟨es, c', t, hseg, hlen, hR0, hf, hm', hr', h1', h2'⟩ |
          ⟨es, c', t, k, hseg, hlen, hRm, hf, hm', hr', hc', ha', hmis'⟩
        · refine Or.inl ⟨false :: es, c', t, .count c s s' hm hr hav hlt hb hseg, by simp [hlen],
            hR0, ?_, hm', hr', h1', h2'⟩
          rw [hf, hch', hfy]; simp
        · refine Or.inr ⟨false :: es, c', t, k, .count c s s' hm hr hav hlt hb hseg,
            by simp; omega, hRm, ?_, hm', hr', hc', ha', hmis'⟩
          rw [hf, hch', hfy]; simp
    · obtain ⟨y, hty, hRy, hfy⟩ := htick false
      obtain ⟨m, hsm, hym⟩ := hty
      simp only [Bool.false_eq_true, if_false] at hym
      subst hym
      obtain ⟨s', hb, hch', -⟩ := GalilPrepConstruct.active_background_exists P qq first s hne hsm
      rcases ih c s' hm hr h1 h2 (by rw [hch']; exact hRy) with
        ⟨es, c', t, hseg, hlen, hR0, hf, hm', hr', h1', h2'⟩ |
        ⟨es, c', t, k, hseg, hlen, hRm, hf, hm', hr', hc', ha', hmis'⟩
      · refine Or.inl ⟨false :: es, c', t, .wait c s s' hm hr hav hb hseg, by simp [hlen], hR0, ?_,
          hm', hr', h1', h2'⟩
        rw [hf, hch', hfy]; simp
      · refine Or.inr ⟨false :: es, c', t, k, .wait c s s' hm hr hav hb hseg, by simp; omega,
          hRm, ?_, hm', hr', hc', ha', hmis'⟩
        rw [hf, hch', hfy]; simp

/-! ## 3. A preparing chain fails the shift guard -/

/-- The chain is still copying or walking back, with positive lag. -/
def PrepChain (x : ChainVM) : Prop :=
  (∃ (t : GalilScaffoldTape.Tape) (c : Counter) (p : GalilScaffoldPlace.Place)
      (v : GalilScaffoldChainPeriod.Tape) (lag margin : Counter) (ver : PlaceHead),
      x = .copy t c p v lag margin ver ∧ 1 ≤ value lag) ∨
  (∃ (v : GalilScaffoldChainPeriod.Tape) (c lag margin : Counter) (ver : PlaceHead),
      x = .back v c lag margin ver ∧ 1 ≤ value lag)

theorem prepChain_of_prepAt (u : GalilScaffoldTape.Tape) (hc : Counter)
    (q' : GalilScaffoldPlace.Place) (Z W : GalilScaffoldChainPeriod.Tape) (ver : PlaceHead)
    (h m : ℕ) (x : ChainVM) (hx : PrepAt u hc q' Z W ver h (m+1) x) : PrepChain x := by
  rcases hx with ⟨_, t, c, pp, v, lag, margin, _, rfl, _, hl⟩ | ⟨v, lag, margin, rfl, _, hl⟩ |
    ⟨hn, _⟩
  · exact Or.inl ⟨t, c, pp, v, lag, margin, ver, rfl, hl⟩
  · exact Or.inr ⟨v, hc, lag, margin, ver, rfl, hl⟩
  · omega

theorem prepChain_ne_idle {x : ChainVM} (hx : PrepChain x) : x ≠ ChainVM.idle := by
  rcases hx with ⟨_, _, _, _, _, _, _, rfl, _⟩ | ⟨_, _, _, _, _, rfl, _⟩ <;>
    exact fun h0 => ChainVM.noConfusion h0

/-- **`prep_guard_false`.**  After the disabled tick of a preparing chain the
chain is `.copy`, `.back`, or a `.watch` with the same positive lag: never a
zero-lag watch, so `shiftGuardVM` fails on any state carrying it. -/
theorem prep_guard_false {x z : ChainVM} (hx : PrepChain x) (ht : ChainTick false x z)
    (u : GalilVM) (hu : u.chain = z) : ¬ shiftGuardVM u := by
  rintro ⟨w, hw, hz, -⟩
  obtain ⟨y, hs, hy⟩ := ht
  simp only [Bool.false_eq_true, if_false] at hy
  subst hy
  rw [hu] at hw
  rcases hx with ⟨t, c, p, v, lag, margin, ver, rfl, hl⟩ | ⟨v, c, lag, margin, ver, rfl, hl⟩
  · cases hs <;> exact ChainVM.noConfusion hw
  · cases hs with
    | backStep => exact ChainVM.noConfusion hw
    | backDone _ _ _ _ _ hf =>
      injection hw with hw
      subst hw
      rw [zero_false_of_value hl] at hz
      exact Bool.false_ne_true hz

theorem prep_guard_false_afterMismatch {s : GalilVM} (hx : PrepChain s.chain) (vs : ScanVM)
    (vq : SearchVM) (ht : ChainTick false s.chain vs.chain) :
    ¬ shiftGuardVM (afterMismatch s vs vq) :=
  prep_guard_false hx ht _ rfl

/-- The disabled tick of a preparing chain exists. -/
theorem prepChain_tick_exists (u : GalilScaffoldTape.Tape) (hc : Counter)
    (q' : GalilScaffoldPlace.Place) (Z W : GalilScaffoldChainPeriod.Tape) (ver : PlaceHead)
    (h : ℕ) (b : Fin 3) (hu : u.focus = 4) (hpos : positive hc = true)
    (hfocus : Z.focus = .plain b)
    (hback : GalilScaffoldChainPeriod.Back (GalilScaffoldChainPeriod.write Z (.last b)) (h+1) W)
    (m : ℕ) (x : ChainVM) (hx : PrepAt u hc q' Z W ver h (m+1) x) :
    ∃ z, ChainTick false x z :=
  let ⟨z, hz, _⟩ := (prepAt_step u hc q' Z W ver h b hu hpos hfocus hback m x hx).2 false
  ⟨z, hz⟩

/-! ## 4. The preparation segment, or a fallback-bound mismatch -/

/-- **`prep_segment_construct_or_fallback`.**  `prep_segment_construct_general`
without `hmatch`: either the whole `2h+2`-tick preparation (same conclusion),
or a strictly shorter prefix ending at a clock-one mismatching comparison
while the chain is still preparing (`PrepChain`, positive lag); there the
disabled chain tick exists and the shift guard fails after any disabled chain
tick, so the comparison is `Tick.scan_fallback`. -/
theorem prep_segment_construct_or_fallback (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    (hdelay : 1 ≤ delay)
    (answer : GalilScaffoldTape.Tape) (cen : Fin 3) (p q' : GalilScaffoldPlace.Place)
    (ver : PlaceHead) (u : GalilScaffoldTape.Tape)
    (h : ℕ) (ys : List (Fin 3)) (b : Fin 3)
    (hcopy : GalilScaffoldChainPeriod.Copy answer reset p (GalilScaffoldChainPeriod.start cen) h u
      (ofNat h) q' (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])))
    (hu : u.focus = 4) (hpos : positive (ofNat h) = true)
    (hfocus : (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen)
      (ys ++ [b])).focus = .plain b)
    (hback : GalilScaffoldChainPeriod.Back (GalilScaffoldChainPeriod.write
      (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])) (.last b))
      (h+1) (GalilScaffoldChainPeriod.moveRight ⟨[], .first cen,
        ys.map GalilScaffoldChainPeriod.Token.plain ++ [.last b]⟩))
    (lag0 margin0 : Counter) (hlag : 1 ≤ value lag0)
    (cF' : Control) (sF : GalilVM)
    (hm : cF'.mode = .scan) (hr : cF'.replaying = false)
    (hclk1 : 1 ≤ cF'.clock) (hclk2 : cF'.clock ≤ delay)
    (hchain : sF.chain = ChainVM.copy answer reset p (GalilScaffoldChainPeriod.start cen)
      lag0 margin0 ver) :
    (∃ (es bs cs : List Bool) (dm : Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE P qq first delay es cF' sF c2 s2 ∧
      es = bs ++ dm :: cs ∧ es.length = 2*h+2 ∧ bs.length = h ∧ cs.length = h+1 ∧
      (∃ lag margin : Counter,
        s2.chain = ChainVM.watch ⟨⟨ver, GalilScaffoldChainConsume.ready cen ys b⟩, lag, margin⟩ ∧
        value lag = value lag0 + (es.count true : ℤ)) ∧
      c2.mode = .scan ∧ c2.replaying = false ∧ 1 ≤ c2.clock ∧ c2.clock ≤ delay) ∨
    (∃ (es : List Bool) (c1 : Control) (s1 : GalilVM),
      WatchSegE P qq first delay es cF' sF c1 s1 ∧ es.length < 2*h+2 ∧
      c1.mode = .scan ∧ c1.replaying = false ∧ c1.clock = 1 ∧ canRight s1.right ∧
      read (left s1.left) ≠ read (right s1.right) ∧
      PrepChain s1.chain ∧ lagv s1.chain = value lag0 + (es.count true : ℤ) ∧
      (∃ z, ChainTick false s1.chain z) ∧
      (∀ (vs : ScanVM) (vq : SearchVM), ChainTick false s1.chain vs.chain →
        ¬ shiftGuardVM (afterMismatch s1 vs vq))) := by
  have hR : PrepAt u (ofNat h) q' (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen)
      (ys ++ [b])) (GalilScaffoldChainPeriod.moveRight ⟨[], .first cen,
        ys.map GalilScaffoldChainPeriod.Token.plain ++ [.last b]⟩) ver h (2*h+2) sF.chain :=
    Or.inl ⟨h, answer, reset, p, _, lag0, margin0, by omega, hchain, hcopy, hlag⟩
  have hf0 : lagv sF.chain = value lag0 := by rw [hchain]; rfl
  rcases drive_or_mismatch P qq first delay hdelay _ lagv
      (prepAt_step u (ofNat h) q' _ _ ver h b hu hpos hfocus hback)
      (2*h+2) cF' sF hm hr hclk1 hclk2 hR with
    ⟨es, c2, s2, hseg, hlen, hR0, hf, hm2, hr2, h12, h22⟩ |
    ⟨es, c1, s1, m, hseg, hlen, hRm, hf, hm1, hr1, hc1, ha1, hmis⟩
  · left
    obtain ⟨bs, cs, dm, hes, hbs, hcs⟩ := GalilPreludeEnds.split_prelude es h hlen
    have hwatch : ∃ lag margin : Counter,
        s2.chain = ChainVM.watch ⟨⟨ver, GalilScaffoldChainConsume.ready cen ys b⟩, lag, margin⟩ ∧
        value lag = value lag0 + (es.count true : ℤ) := by
      rcases hR0 with ⟨k, _, _, _, _, _, _, hn, _⟩ | ⟨_, _, _, _, hb, _⟩ | ⟨_, lag, margin, hw⟩
      · omega
      · have := back_pos hb; omega
      · refine ⟨lag, margin, hw, ?_⟩
        have hf' := hf
        rw [hw, hf0] at hf'
        simpa [lagv] using hf'
    exact ⟨es, bs, cs, dm, c2, s2, hseg, hes, hlen, hbs, hcs, hwatch, hm2, hr2, h12, h22⟩
  · right
    have hpc := prepChain_of_prepAt _ _ _ _ _ ver h m _ hRm
    refine ⟨es, c1, s1, hseg, by omega, hm1, hr1, hc1, ha1, hmis, hpc, by rw [hf, hf0],
      prepChain_tick_exists _ _ _ _ _ ver h b hu hpos hfocus hback m _ hRm, ?_⟩
    intro vs vq ht
    exact prep_guard_false_afterMismatch hpc vs vq ht

/-- **From the credited `chain.start()`** (the found-comparison entry). -/
theorem prep_segment_construct_or_fallback_matched (P : Shared) (qq : ℕ) (first : Fin 9)
    (delay : ℕ) (hdelay : 1 ≤ delay)
    (answer : GalilScaffoldTape.Tape) (cen : Fin 3) (p q' : GalilScaffoldPlace.Place)
    (ver : PlaceHead) (radius : Counter) (hrad : 0 ≤ value radius) (u : GalilScaffoldTape.Tape)
    (h : ℕ) (ys : List (Fin 3)) (b : Fin 3)
    (hcopy : GalilScaffoldChainPeriod.Copy answer reset p (GalilScaffoldChainPeriod.start cen) h u
      (ofNat h) q' (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])))
    (hu : u.focus = 4) (hpos : positive (ofNat h) = true)
    (hfocus : (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen)
      (ys ++ [b])).focus = .plain b)
    (hback : GalilScaffoldChainPeriod.Back (GalilScaffoldChainPeriod.write
      (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])) (.last b))
      (h+1) (GalilScaffoldChainPeriod.moveRight ⟨[], .first cen,
        ys.map GalilScaffoldChainPeriod.Token.plain ++ [.last b]⟩))
    (cF' : Control) (sF : GalilVM)
    (hm : cF'.mode = .scan) (hr : cF'.replaying = false)
    (hclk1 : 1 ≤ cF'.clock) (hclk2 : cF'.clock ≤ delay)
    (hch : ChainMatched (chainStart answer cen p ver radius) sF.chain) :
    (∃ (es bs cs : List Bool) (dm : Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE P qq first delay es cF' sF c2 s2 ∧
      es = bs ++ dm :: cs ∧ es.length = 2*h+2 ∧ bs.length = h ∧ cs.length = h+1 ∧
      (∃ lag margin : Counter,
        s2.chain = ChainVM.watch ⟨⟨ver, GalilScaffoldChainConsume.ready cen ys b⟩, lag, margin⟩ ∧
        value lag = value radius + 1 + (es.count true : ℤ)) ∧
      c2.mode = .scan ∧ c2.replaying = false ∧ 1 ≤ c2.clock ∧ c2.clock ≤ delay) ∨
    (∃ (es : List Bool) (c1 : Control) (s1 : GalilVM),
      WatchSegE P qq first delay es cF' sF c1 s1 ∧ es.length < 2*h+2 ∧
      c1.mode = .scan ∧ c1.replaying = false ∧ c1.clock = 1 ∧ canRight s1.right ∧
      read (left s1.left) ≠ read (right s1.right) ∧
      PrepChain s1.chain ∧ lagv s1.chain = value radius + 1 + (es.count true : ℤ) ∧
      (∃ z, ChainTick false s1.chain z) ∧
      (∀ (vs : ScanVM) (vq : SearchVM), ChainTick false s1.chain vs.chain →
        ¬ shiftGuardVM (afterMismatch s1 vs vq))) := by
  have hchain : sF.chain = ChainVM.copy answer reset p (GalilScaffoldChainPeriod.start cen)
      (inc radius) (inc radius) ver := by
    generalize hx : sF.chain = x at hch
    cases hch
    rfl
  rcases prep_segment_construct_or_fallback P qq first delay hdelay answer cen p q' ver u h ys b
      hcopy hu hpos hfocus hback (inc radius) (inc radius) (by rw [inc_value]; omega) cF' sF hm hr
      hclk1 hclk2 hchain with
    ⟨es, bs, cs, dm, c2, s2, hseg, hes, hlen, hbs, hcs, ⟨lag, margin, hw, hv⟩, hm2, hr2, h12, h22⟩ |
    ⟨es, c1, s1, hseg, hlen, hm1, hr1, hc1, ha1, hmis, hpc, hlagv, htk, hg⟩
  · exact Or.inl ⟨es, bs, cs, dm, c2, s2, hseg, hes, hlen, hbs, hcs,
      ⟨lag, margin, hw, by rw [hv, inc_value]⟩, hm2, hr2, h12, h22⟩
  · exact Or.inr ⟨es, c1, s1, hseg, hlen, hm1, hr1, hc1, ha1, hmis, hpc,
      by rw [hlagv, inc_value], htk, hg⟩

/-! ## 5. The fallback landing from a preparing chain -/

/-- **`fallback_from_prep`.**  `fallback_landing` from the mismatch stop of
`prep_segment_construct_or_fallback`: the chain is copying or walking back,
the guard failure is *proved* (`prep_guard_false_afterMismatch`), and the
remaining hypotheses are `fallback_landing`'s input-tape facts, exactly as in
`GalilMidRoundFallback.fallback_from_watch`. -/
theorem fallback_from_prep (onLetter leftFirst : GalilVM → Prop) (rs : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (hq0 : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8) (delay : ℕ)
    (c : Control) (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (s : GalilVM) (hi : ShiftIdle s) (hav : canRight s.right)
    (hpc : PrepChain s.chain)
    (vs : ScanVM) (vq : SearchVM) (hl : vs.left = left s.left) (hrr : vs.right = right s.right)
    (hct : ChainTick false s.chain vs.chain)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hq : searchEffect (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry)
      false s vq)
    {raw : List (Fin 2)} (hrep : GalilScaffoldInputTrace.Represents (right s.right).head raw)
    (hfoc : (right s.right).head.focus ≠ none)
    (hcan : Canonical s.length) (ℓ : ℕ) (hv : value s.length = ℓ)
    (heven : ∀ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' →
      ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length % 2 = 0)
    (honL : onLetter = onLetterVM raw) (hlF : leftFirst = leftFirstVM) (hout : OutputRel raw c s) :
    ∃ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' ∧
      raw = (a :: xs).reverse ++ rs' ++ q' ∧
      ∃ (n : ℕ) (o : Bool) (t : GalilVM),
        StepsAll (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first) delay (SoundScanNR raw) (1 + (n+1)) ⟨c, s⟩
          ⟨{c with mode := .scan, clock := delay, output := o, replaying := decide (0 < chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))), odd := oddAt false (((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length - (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))+1)), pair := pairAt (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))}, t⟩ ∧
        Restarted raw t 0 reset ∧
        position t.center = position (right s.right) - chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)) ∧
        Manacher.PalAt (encoded raw) (position (right s.right) - chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))
          (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        (∀ r', 2*r'+1 ≤ ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length →
          Manacher.PalAt (encoded raw) (position (right s.right) - r') r' →
          r' ≤ chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        t.replay = ofNat (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        ShiftIdle t ∧ t.chain = ChainVM.idle ∧
        t.right = GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))] (right s.right) ∧
        t.center = t.right :=
  fallback_landing onLetter leftFirst rs centre place entry q hq0 first h7 h8
    delay c hm hr hc s hi hav vs vq hl hrr hmis hq
    (Or.inl ⟨prepChain_ne_idle hpc, hct⟩)
    (prep_guard_false_afterMismatch hpc vs vq hct) hrep hfoc hcan ℓ hv heven honL hlF hout

#print axioms watchSegE_clock_le
#print axioms hmatch_of_clock
#print axioms drive_or_mismatch
#print axioms prepChain_of_prepAt
#print axioms prep_guard_false
#print axioms prep_guard_false_afterMismatch
#print axioms prep_segment_construct_or_fallback
#print axioms prep_segment_construct_or_fallback_matched
#print axioms fallback_from_prep

end PalPeg.GalilPrepMatch
