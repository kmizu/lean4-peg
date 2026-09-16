import PalPeg.GalilPreludeEnds
import PalPeg.GalilRoundConstruct

/-!
# The preparation segment under an arbitrary clock

`GalilPrepConstruct.prep_segment_construct` drives the chain's `2h+2`-step
preparation (`h` copy ticks, `copyEnd`, `h+1` back ticks) as a *background-only*
segment, which needs `cF'.clock = delay` and `2h+2 < delay`.  Both are
restrictions of that construction, not of the model: a matched comparison
during copy/back is an ordinary chain tick (`ChainMatched.copy` / `.back`,
`lag++`, `margin++`; at the final `backDone` tick `Outer.queued`, available
because the lag is positive).

This module removes both restrictions.

* `drive` — a generic driver: if a family `R n x` ("`n` chain ticks still to
  go from `x`") admits a chain tick on *either* event, and the comparisons that
  the clock forces all match (`hmatch`, stated on the actual intermediate
  states as prefixes of the segment being built), then from any scan state with
  `1 ≤ clock ≤ delay` there is a `WatchSegE` of exactly `n` ticks.  Each tick
  is `count` (right head available, clock above one), `match` (right head
  available, clock one — a matched comparison; the search is frozen because
  the chain is active; the output refresh is `frame_refresh_exists`), or
  `wait` (right head exhausted).  Every tick is exactly one chain tick, so the
  event list has length `n`, and a measure `f` grows by `es.count true`.
* `PrepAt` / `prepAt_step` — the copy / back / watch family with `f = lagv`.
* `prep_segment_construct_general` — the preparation segment of length `2h+2`
  from any clock, split as `bs ++ dm :: cs`, landing in
  `.watch ⟨⟨ver, ready cen ys b⟩, lag, margin⟩` with
  `value lag = value lag0 + es.count true`.
* `prep_segment_construct_matched` — the same from the credited `chain.start()`
  (`ChainMatched (chainStart … radius) sF.chain`), `value lag = value radius + 1 + #true`.

## Gaps (named hypotheses)

* `hmatch` — comparisons forced by the clock inside the segment match.  To be
  discharged by `GalilMismatchCaught.no_mismatch_before_caught`.
* `hlag : 1 ≤ value lag0` — needed so that a `true` credit on the final
  `backDone` tick can be `Outer.queued`; at lag zero it would be `immediate`
  (needs `Good`) or a break.  For the background-found entry (`chainStart`
  without a credit) this is `1 ≤ value radius`.
-/

set_option autoImplicit false
namespace PalPeg.GalilPrepClock

open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilBranchInvariants
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## 1. The generic driver -/

/-- **Driving a tickable chain family through the clock.** -/
theorem drive (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ) (hdelay : 1 ≤ delay)
    (R : ℕ → ChainVM → Prop) (f : ChainVM → ℤ)
    (hstep : ∀ (n : ℕ) (x : ChainVM), R (n+1) x → x ≠ ChainVM.idle ∧
      ∀ a : Bool, ∃ y, ChainTick a x y ∧ R n y ∧ f y = f x + (if a then 1 else 0)) :
    ∀ (n : ℕ) (c : Control) (s : GalilVM), c.mode = .scan → c.replaying = false →
      1 ≤ c.clock → c.clock ≤ delay → R n s.chain →
      (∀ (es0 : List Bool) (c' : Control) (v : GalilVM),
        WatchSegE P qq first delay es0 c s c' v → es0.length < n → c'.clock = 1 →
        canRight v.right → read (left v.left) = read (right v.right)) →
      ∃ (es : List Bool) (c' : Control) (t : GalilVM),
        WatchSegE P qq first delay es c s c' t ∧ es.length = n ∧ R 0 t.chain ∧
        f t.chain = f s.chain + (es.count true : ℤ) ∧
        c'.mode = .scan ∧ c'.replaying = false ∧ 1 ≤ c'.clock ∧ c'.clock ≤ delay := by
  intro n
  induction n with
  | zero =>
    intro c s hm hr h1 h2 hR _
    exact ⟨[], c, s, .stop _ _, rfl, hR, by simp, hm, hr, h1, h2⟩
  | succ n ih =>
    intro c s hm hr h1 h2 hR hmatch
    obtain ⟨hne, htick⟩ := hstep n s.chain hR
    by_cases hav : canRight s.right
    · by_cases hc1 : c.clock = 1
      · -- a matched comparison
        obtain ⟨y, hty, hRy, hfy⟩ := htick true
        have hm0 : read (left s.left) = read (right s.right) :=
          hmatch [] c s (.stop _ _) (by simp) hc1 hav
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
        obtain ⟨es, c', t, hseg, hlen, hR0, hf, hm', hr', h1', h2'⟩ :=
          ih {c with clock := delay, output := o, replaying := false} (afterCompare s vs vq)
            hm rfl hdelay le_rfl (by rw [hch]; exact hRy)
            (fun es0 c'' v hs hl hc hv =>
              hmatch (true :: es0) c'' v (.match c s vs vq o hm hr hav hc1 hne hcmp hmt hq ho hs)
                (by simp; omega) hc hv)
        refine ⟨true :: es, c', t, .match c s vs vq o hm hr hav hc1 hne hcmp hmt hq ho hseg,
          by simp [hlen], hR0, ?_, hm', hr', h1', h2'⟩
        rw [hf, hch, hfy]; simp; ring
      · -- counting down
        obtain ⟨y, hty, hRy, hfy⟩ := htick false
        obtain ⟨m, hsm, hym⟩ := hty
        simp only [Bool.false_eq_true, if_false] at hym
        subst hym
        obtain ⟨s', hb, hch', -⟩ := GalilPrepConstruct.active_background_exists P qq first s hne hsm
        have hlt : 1 < c.clock := by omega
        obtain ⟨es, c', t, hseg, hlen, hR0, hf, hm', hr', h1', h2'⟩ :=
          ih {c with clock := c.clock - 1} s' hm hr (by simp only []; omega)
            (by simp only []; omega) (by rw [hch']; exact hRy)
            (fun es0 c'' v hs hl hc hv =>
              hmatch (false :: es0) c'' v (.count c s s' hm hr hav hlt hb hs)
                (by simp; omega) hc hv)
        refine ⟨false :: es, c', t, .count c s s' hm hr hav hlt hb hseg, by simp [hlen], hR0, ?_,
          hm', hr', h1', h2'⟩
        rw [hf, hch', hfy]; simp
    · -- waiting for input
      obtain ⟨y, hty, hRy, hfy⟩ := htick false
      obtain ⟨m, hsm, hym⟩ := hty
      simp only [Bool.false_eq_true, if_false] at hym
      subst hym
      obtain ⟨s', hb, hch', -⟩ := GalilPrepConstruct.active_background_exists P qq first s hne hsm
      obtain ⟨es, c', t, hseg, hlen, hR0, hf, hm', hr', h1', h2'⟩ :=
        ih c s' hm hr h1 h2 (by rw [hch']; exact hRy)
          (fun es0 c'' v hs hl hc hv =>
            hmatch (false :: es0) c'' v (.wait c s s' hm hr hav hb hs)
              (by simp; omega) hc hv)
      refine ⟨false :: es, c', t, .wait c s s' hm hr hav hb hseg, by simp [hlen], hR0, ?_,
        hm', hr', h1', h2'⟩
      rw [hf, hch', hfy]; simp

/-! ## 2. The copy / back / watch family -/

/-- The lag of a preparing or watching chain. -/
def lagv : ChainVM → ℤ
  | .copy _ _ _ _ lag _ _ => value lag
  | .back _ _ lag _ _ => value lag
  | .watch w => value w.lag
  | _ => 0

theorem zero_false_of_value {c : Counter} (h : 1 ≤ value c) : zero c = false := by
  rcases c with ⟨ps, ns⟩
  cases ps <;> cases ns <;> simp_all [zero, value]

section Family

variable (u : GalilScaffoldTape.Tape) (hc : Counter) (q' : GalilScaffoldPlace.Place)
  (Z W : GalilScaffoldChainPeriod.Tape) (ver : PlaceHead) (h : ℕ) (b : Fin 3)

/-- `n` preparation ticks to go: still copying (`k` copy ticks, then `copyEnd`
and the `h+1` back ticks), walking back (`n` back ticks), or watching. -/
def PrepAt (n : ℕ) (x : ChainVM) : Prop :=
  (∃ (k : ℕ) (t : GalilScaffoldTape.Tape) (c : Counter) (pp : GalilScaffoldPlace.Place)
      (v : GalilScaffoldChainPeriod.Tape) (lag margin : Counter),
    n = k + (h+2) ∧ x = .copy t c pp v lag margin ver ∧
    GalilScaffoldChainPeriod.Copy t c pp v k u hc q' Z ∧ 1 ≤ value lag) ∨
  (∃ (v : GalilScaffoldChainPeriod.Tape) (lag margin : Counter),
    x = .back v hc lag margin ver ∧ GalilScaffoldChainPeriod.Back v n W ∧ 1 ≤ value lag) ∨
  (n = 0 ∧ ∃ lag margin : Counter,
    x = .watch ⟨⟨ver, ⟨W, reset, reset, reset, 0, true, false⟩⟩, lag, margin⟩)

theorem back_pos {v W' : GalilScaffoldChainPeriod.Tape} {n : ℕ}
    (hb : GalilScaffoldChainPeriod.Back v n W') : 1 ≤ n := by
  cases hb <;> omega

theorem prepAt_step (hu : u.focus = 4) (hpos : positive hc = true) (hfocus : Z.focus = .plain b)
    (hback : GalilScaffoldChainPeriod.Back (GalilScaffoldChainPeriod.write Z (.last b)) (h+1) W)
    (n : ℕ) (x : ChainVM) (hx : PrepAt u hc q' Z W ver h (n+1) x) :
    x ≠ ChainVM.idle ∧ ∀ a : Bool, ∃ y, ChainTick a x y ∧ PrepAt u hc q' Z W ver h n y ∧
      lagv y = lagv x + (if a then 1 else 0) := by
  rcases hx with ⟨k, t, c, pp, v, lag, margin, hn, rfl, hcp, hl⟩ | ⟨v, lag, margin, rfl, hb, hl⟩ |
    ⟨hn, _⟩
  · refine ⟨fun h0 => ChainVM.noConfusion h0, ?_⟩
    intro a
    cases hcp with
    | stop =>
      have hn' : n = h + 1 := by omega
      subst hn'
      have hs := ChainStep.copyEnd u hc q' Z lag margin ver b hu hpos hfocus
      cases a with
      | false =>
        refine ⟨_, ⟨_, hs, rfl⟩, Or.inr (Or.inl ⟨_, lag, margin, rfl, hback, hl⟩), by simp [lagv]⟩
      | true =>
        refine ⟨_, ⟨_, hs, .back _ _ _ _ _⟩,
          Or.inr (Or.inl ⟨_, inc lag, inc margin, rfl, hback, by rw [inc_value]; omega⟩), ?_⟩
        simp [lagv, inc_value]
    | next a' one legal present rest =>
      have hs := ChainStep.copyBit t c pp v lag margin ver a' one legal present
      cases a with
      | false =>
        exact ⟨_, ⟨_, hs, rfl⟩, Or.inl ⟨_, _, _, _, _, lag, _, by omega, rfl, rest, hl⟩,
          by simp [lagv]⟩
      | true =>
        refine ⟨_, ⟨_, hs, .copy _ _ _ _ _ _ _⟩,
          Or.inl ⟨_, _, _, _, _, inc lag, _, by omega, rfl, rest, by rw [inc_value]; omega⟩, ?_⟩
        simp [lagv, inc_value]
  · refine ⟨fun h0 => ChainVM.noConfusion h0, ?_⟩
    intro a
    cases hb with
    | done _ hf =>
      have hs := ChainStep.backDone v hc lag margin ver hf
      cases a with
      | false =>
        exact ⟨_, ⟨_, hs, rfl⟩, Or.inr (Or.inr ⟨rfl, lag, margin, rfl⟩), by simp [lagv]⟩
      | true =>
        refine ⟨_, ⟨_, hs, .watch _ _ (.queued _ (zero_false_of_value hl))⟩,
          Or.inr (Or.inr ⟨rfl, inc lag, inc margin, rfl⟩), ?_⟩
        simp [lagv, GalilScaffoldChainWatch.queued, inc_value]
    | next _ hf hl' hr =>
      have hs := ChainStep.backStep v hc lag margin ver hf
      cases a with
      | false =>
        exact ⟨_, ⟨_, hs, rfl⟩, Or.inr (Or.inl ⟨_, lag, margin, rfl, hr, hl⟩), by simp [lagv]⟩
      | true =>
        refine ⟨_, ⟨_, hs, .back _ _ _ _ _⟩,
          Or.inr (Or.inl ⟨_, inc lag, inc margin, rfl, hr, by rw [inc_value]; omega⟩), ?_⟩
        simp [lagv, inc_value]
  · omega

end Family

/-! ## 3. The preparation segment, from any clock -/

/-- **The preparation segment under an arbitrary clock.**  From any scan state
(not replaying, `1 ≤ clock ≤ delay`) whose chain is the copy state at the start
of the period copy, with positive lag, and assuming the comparisons the clock
forces inside the segment match, there is a `WatchSegE` of exactly `2h+2`
chain ticks — background ticks and matched comparisons as the clock dictates —
split as `bs ++ dm :: cs` (`h`, `1`, `h+1`), landing in
`.watch ⟨⟨ver, ready cen ys b⟩, lag, margin⟩` with
`value lag = value lag0 + es.count true`.  No bound on `h` versus `delay`. -/
theorem prep_segment_construct_general (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
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
      lag0 margin0 ver)
    -- the comparisons the clock forces inside the segment match
    (hmatch : ∀ (es0 : List Bool) (c' : Control) (v : GalilVM),
      WatchSegE P qq first delay es0 cF' sF c' v → es0.length < 2*h+2 → c'.clock = 1 →
      canRight v.right → read (left v.left) = read (right v.right)) :
    ∃ (es bs cs : List Bool) (dm : Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE P qq first delay es cF' sF c2 s2 ∧
      es = bs ++ dm :: cs ∧ es.length = 2*h+2 ∧ bs.length = h ∧ cs.length = h+1 ∧
      (∃ lag margin : Counter,
        s2.chain = ChainVM.watch ⟨⟨ver, GalilScaffoldChainConsume.ready cen ys b⟩, lag, margin⟩ ∧
        value lag = value lag0 + (es.count true : ℤ)) ∧
      c2.mode = .scan ∧ c2.replaying = false ∧ 1 ≤ c2.clock ∧ c2.clock ≤ delay := by
  have hR : PrepAt u (ofNat h) q' (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen)
      (ys ++ [b])) (GalilScaffoldChainPeriod.moveRight ⟨[], .first cen,
        ys.map GalilScaffoldChainPeriod.Token.plain ++ [.last b]⟩) ver h (2*h+2) sF.chain :=
    Or.inl ⟨h, answer, reset, p, _, lag0, margin0, by omega, hchain, hcopy, hlag⟩
  obtain ⟨es, c2, s2, hseg, hlen, hR0, hf, hm2, hr2, h12, h22⟩ :=
    drive P qq first delay hdelay _ lagv
      (prepAt_step u (ofNat h) q' _ _ ver h b hu hpos hfocus hback)
      (2*h+2) cF' sF hm hr hclk1 hclk2 hR hmatch
  obtain ⟨bs, cs, dm, hes, hbs, hcs⟩ := GalilPreludeEnds.split_prelude es h hlen
  have hwatch : ∃ lag margin : Counter,
      s2.chain = ChainVM.watch ⟨⟨ver, GalilScaffoldChainConsume.ready cen ys b⟩, lag, margin⟩ ∧
      value lag = value lag0 + (es.count true : ℤ) := by
    rcases hR0 with ⟨k, _, _, _, _, _, _, hn, _⟩ | ⟨_, _, _, _, hb, _⟩ | ⟨_, lag, margin, hw⟩
    · omega
    · have := back_pos hb; omega
    · refine ⟨lag, margin, hw, ?_⟩
      have hf' := hf
      rw [hw, hchain] at hf'
      simpa [lagv] using hf'
  exact ⟨es, bs, cs, dm, c2, s2, hseg, hes, hlen, hbs, hcs, hwatch, hm2, hr2, h12, h22⟩

/-- **From the credited `chain.start()`** (the found-comparison entry): the
lag starts at `radius + 1`. -/
theorem prep_segment_construct_matched (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    (hdelay : 1 ≤ delay)
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
    (hch : ChainMatched (chainStart answer cen p ver radius) sF.chain)
    (hmatch : ∀ (es0 : List Bool) (c' : Control) (v : GalilVM),
      WatchSegE P qq first delay es0 cF' sF c' v → es0.length < 2*h+2 → c'.clock = 1 →
      canRight v.right → read (left v.left) = read (right v.right)) :
    ∃ (es bs cs : List Bool) (dm : Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE P qq first delay es cF' sF c2 s2 ∧
      es = bs ++ dm :: cs ∧ es.length = 2*h+2 ∧ bs.length = h ∧ cs.length = h+1 ∧
      (∃ lag margin : Counter,
        s2.chain = ChainVM.watch ⟨⟨ver, GalilScaffoldChainConsume.ready cen ys b⟩, lag, margin⟩ ∧
        value lag = value radius + 1 + (es.count true : ℤ)) ∧
      c2.mode = .scan ∧ c2.replaying = false ∧ 1 ≤ c2.clock ∧ c2.clock ≤ delay := by
  have hchain : sF.chain = ChainVM.copy answer reset p (GalilScaffoldChainPeriod.start cen)
      (inc radius) (inc radius) ver := by
    generalize hx : sF.chain = x at hch
    cases hch
    rfl
  obtain ⟨es, bs, cs, dm, c2, s2, hseg, hes, hlen, hbs, hcs, ⟨lag, margin, hw, hv⟩, hm2, hr2, h12,
      h22⟩ :=
    prep_segment_construct_general P qq first delay hdelay answer cen p q' ver u h ys b hcopy hu
      hpos hfocus hback (inc radius) (inc radius) (by rw [inc_value]; omega) cF' sF hm hr hclk1
      hclk2 hchain hmatch
  exact ⟨es, bs, cs, dm, c2, s2, hseg, hes, hlen, hbs, hcs,
    ⟨lag, margin, hw, by rw [hv, inc_value]⟩, hm2, hr2, h12, h22⟩

#print axioms drive
#print axioms prepAt_step
#print axioms prep_segment_construct_general
#print axioms prep_segment_construct_matched

end PalPeg.GalilPrepClock
