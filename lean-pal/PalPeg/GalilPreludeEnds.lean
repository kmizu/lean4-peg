import PalPeg.GalilPreludeDone
import PalPeg.GalilPrepConstruct

/-!
# `PreludeEnds`, discharged — and corrected

`PalPeg/GalilPreludeDone.lean` isolates one named hypothesis, `PreludeEnds`:
any `WatchSegE` of length `2h+2` starting at `chainStart answer cc walker ver
radius` leaves the chain in `.watch w` with `0 ≤ value w.lag ≤ 2h+2`.  This
module proves that hypothesis from the chain's own copy/back data — and in
doing so finds that **the stated lag bound is false**.

## The correction

`chainStart` (`GalilScaffoldTopChainVM.lean`) is

    chainStart answer c walker verifier radius =
      .copy answer reset walker (period.start c) radius radius verifier

i.e. `chain.start()` *aliases `lag` and `margin` to `radius`*, exactly as
`GalilScaffoldChainCredits.start radius = ⟨radius, radius⟩` records.  The
prelude's own background ticks never touch `lag`; only the interleaved scan
credits do (`ChainMatched.copy`/`.back`, `lag++` each).  Hence after `2h+2`
ticks with `k` matched events

    value w.lag = value radius + k,   k ≤ 2h + 2

(`GalilScaffoldChainCredits.prep_value` says the same thing on the ledger
side).  The entry lag is therefore `≤ value radius + (2h+2)`, **not** `≤
2h+2`; the two agree only when `value radius = 0`, which never happens at a
found comparison.  `PreludeEnds'` below is the corrected statement.

A second, smaller correction: the last of the `2h+2` ticks is `backDone`,
which *enters* `.watch`, and its credit is then `ChainMatched` on a watching
chain — which may be `ChainMatched.breaks`.  So the conclusion must allow a
`.broken` chain.  (The caller kills that disjunct with its own `hnb`, via
`broken_stays`.)

## What the correction costs downstream

`prelude_done_before_extent` collided two counts: the scan needs at least
`2*h*2048 - 2048` ticks to consume `2h` places, while the prelude costs
`2h+2` ticks and the catch-up needs `lag0` further non-matched ticks.  With
`lag0 ≤ 2h+2` the collision is trivial.  With the corrected `lag0 ≤ value
radius + (2h+2)` it closes **iff the found radius is small compared with the
scan's own pace**.  Spelling the count out (`hsp`, `hsp2`, `hbc`):

    2048 · #false(tail)  ≥  2047 · #(tail) - 2048  ≥  2047·(4094h - 2050) - 2048

so `value radius + (2h+2) ≤ #false(tail)` is implied by

    value radius ≤ 4090·h - 2052

and that is the extra hypothesis `prelude_done_before_extent'` carries.  It is
sharp to within a couple of units for this argument.  Morally it says
`radius ≲ 2·delay·h`: the chain may be `radius` places behind, it pays that
back one place per tick, and the extent it has to survive is `2h` places
`= 2h·2048` ticks.  **This is a genuine new obligation**, not an artefact:
`GalilLedger.verifier_catchup` assumes `lag0 ≤ 2h+2` and so silently models a
chain whose lag starts at `0` rather than at `radius`.  Nothing in this file
proves `value radius ≤ 4090h - 2052`; it must come from the search contract
(the found radius versus its semiperiod), and it is the one gap left here.

## Gaps (stated, not hidden)

* `value radius ≤ 4090·h - 2052` in `prelude_done_before_extent'` — see above.
* `hnb` — unchanged from `GalilPreludeDone`; a break is a real outcome.
-/

set_option autoImplicit false

namespace PalPeg.GalilPreludeEnds

open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier GalilScaffoldChainInputSupply

/-! ## 1. The copy phase, inverted -/

/-- **Copy determinism under arbitrary credits.**  `copy_ticks` *constructs* a
`ChainTicks` run through the copy phase; this inverts an arbitrary one.  The
background step is forced (`copyBit` needs `focus = 8`, `copyEnd` needs
`focus = 4`, and the copied symbol is pinned by `present`), so the only
freedom is the credit, which adds `1` to `lag` per matched event. -/
theorem copy_ticks_inv : ∀ (n : ℕ) (bs : List Bool), bs.length = n →
    ∀ {t : GalilScaffoldTape.Tape} {c : Counter} {p : GalilScaffoldPlace.Place}
      {v : GalilScaffoldChainPeriod.Tape} {u : GalilScaffoldTape.Tape} {d : Counter}
      {q : GalilScaffoldPlace.Place} {z : GalilScaffoldChainPeriod.Tape}
      {lag margin : Counter} {ver : PlaceHead} {y : ChainVM},
    GalilScaffoldChainPeriod.Copy t c p v n u d q z →
    ChainTicks bs (.copy t c p v lag margin ver) y →
    Canonical lag → Canonical margin →
    ∃ lag' margin', y = .copy u d q z lag' margin' ver ∧ Canonical lag' ∧ Canonical margin' ∧
      value lag' = value lag + (bs.count true : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro bs hbs t c p v u d q z lag margin ver y hcp htk hcl hcm
    cases hcp
    cases bs with
    | nil => cases htk; exact ⟨lag, margin, rfl, hcl, hcm, by simp⟩
    | cons _ _ => simp at hbs
  | succ n ih =>
    intro bs hbs t c p v u d q z lag margin ver y hcp htk hcl hcm
    cases hcp with
    | next a one legal present rest =>
      cases bs with
      | nil => simp at hbs
      | cons b bs' =>
        have hbs' : bs'.length = n := by simpa using hbs
        cases htk with
        | cons ht hr =>
          obtain ⟨m, hs, hm⟩ := ht
          cases hs with
          | copyEnd t' h' p' v' lag' margin' ver' b' hleft hp hv =>
            rw [one] at hleft; exact absurd hleft (by decide)
          | copyBit t' h' p' v' lag' margin' ver' a' one' legal' present' =>
            have ha : a' = a := Option.some.inj (present'.symm.trans present)
            subst ha
            have hdm : Canonical (GalilScaffoldChainCredits.decFour margin) :=
              dec_canonical _ (dec_canonical _ (dec_canonical _ (dec_canonical _ hcm)))
            cases b with
            | false =>
              simp only [Bool.false_eq_true, if_false] at hm
              subst hm
              obtain ⟨l2, m2, hy, hc2, hm2, hv2⟩ := ih bs' hbs' rest hr hcl hdm
              exact ⟨l2, m2, hy, hc2, hm2, by simpa using hv2⟩
            | true =>
              simp only [if_true] at hm
              cases hm with
              | copy _ _ _ _ _ _ _ =>
                obtain ⟨l2, m2, hy, hc2, hm2, hv2⟩ :=
                  ih bs' hbs' rest hr (inc_canonical _ hcl) (inc_canonical _ hdm)
                refine ⟨l2, m2, hy, hc2, hm2, ?_⟩
                have hcc : (((true :: bs').count true : ℕ) : ℤ) = (bs'.count true : ℕ) + 1 := by
                  simp
                rw [hv2, inc_value, hcc]
                omega

/-! ## 2. The `copyEnd` tick, inverted -/

/-- The single tick that leaves `Copy` for `Back`.  `copyBit` is impossible
(`focus = 4 ≠ 8`) and the written tail symbol is pinned by `hfocus`. -/
theorem copyEnd_tick_inv {u : GalilScaffoldTape.Tape} {d : Counter}
    {q : GalilScaffoldPlace.Place} {z : GalilScaffoldChainPeriod.Tape}
    {lag margin : Counter} {ver : PlaceHead} {b : Fin 3} {dm : Bool} {y : ChainVM}
    (hu : u.focus = 4) (hfocus : z.focus = .plain b)
    (ht : ChainTick dm (.copy u d q z lag margin ver) y)
    (hcl : Canonical lag) (hcm : Canonical margin) :
    ∃ lag' margin',
      y = .back (GalilScaffoldChainPeriod.write z (.last b)) d lag' margin' ver ∧
        Canonical lag' ∧ Canonical margin' ∧
        value lag' = value lag + ((dm :: ([] : List Bool)).count true : ℤ) := by
  obtain ⟨m, hs, hm⟩ := ht
  cases hs with
  | copyBit t' h' p' v' lag' margin' ver' a' one' legal' present' =>
    rw [hu] at one'; exact absurd one' (by decide)
  | copyEnd t' h' p' v' lag' margin' ver' b' hleft hp hv =>
    have hb : b' = b := by
      rw [hfocus] at hv; exact (GalilScaffoldChainPeriod.Token.plain.inj hv.symm)
    subst hb
    cases dm with
    | false =>
      simp only [Bool.false_eq_true, if_false] at hm
      subst hm
      exact ⟨lag, margin, rfl, hcl, hcm, by simp⟩
    | true =>
      simp only [if_true] at hm
      cases hm with
      | back _ _ _ _ _ =>
        refine ⟨inc lag, inc margin, rfl, inc_canonical _ hcl, inc_canonical _ hcm, ?_⟩
        rw [inc_value]; simp

/-! ## 3. The back phase, inverted -/

/-- **Back determinism under arbitrary credits, with the break allowed.**  The
background step is forced by `isFirst`.  The final `backDone` tick *enters*
`.watch`, so its own credit is a watch `ChainMatched`: either
`Outer … true …` (`queued`, `lag++`, or `immediate`, `lag` unchanged) or
`breaks`, which is the `.broken` disjunct. -/
theorem back_ticks_inv : ∀ (n : ℕ) (cs : List Bool), cs.length = n →
    ∀ {v u : GalilScaffoldChainPeriod.Tape} {hc lag margin : Counter} {ver : PlaceHead}
      {y : ChainVM},
    GalilScaffoldChainPeriod.Back v n u →
    ChainTicks cs (.back v hc lag margin ver) y →
    Canonical lag → Canonical margin →
    (∃ w : GalilScaffoldChainWatch.State, y = .watch w ∧
        GalilScaffoldChainWatch.CanonicalState w ∧
        value lag ≤ value w.lag ∧ value w.lag ≤ value lag + (cs.count true : ℤ))
      ∨ (∃ w : GalilScaffoldChainWatch.State, y = .broken w) := by
  intro n
  induction n with
  | zero => intro cs _ v u hc lag margin ver y hb _ _ _; cases hb
  | succ n ih =>
    intro cs hcs v u hc lag margin ver y hb htk hcl hcm
    cases cs with
    | nil => simp at hcs
    | cons b cs' =>
      have hcs' : cs'.length = n := by simpa using hcs
      cases hb with
      | done v' hf =>
        cases cs' with
        | cons _ _ => simp at hcs'
        | nil =>
          cases htk with
          | cons ht hr =>
            cases hr
            obtain ⟨m, hs, hm⟩ := ht
            cases hs with
            | backStep v'' h'' lag'' margin'' ver'' hf' =>
              rw [hf] at hf'; exact absurd hf' (by decide)
            | backDone v'' h'' lag'' margin'' ver'' hf' =>
              cases b with
              | false =>
                simp only [Bool.false_eq_true, if_false] at hm
                subst hm
                exact Or.inl ⟨_, rfl, ⟨hcl, hcm⟩, le_refl _, by simp⟩
              | true =>
                simp only [if_true] at hm
                cases hm with
                | «breaks» w0 w' hbk => exact Or.inr ⟨w', rfl⟩
                | «watch» w0 w' ho =>
                  refine Or.inl ⟨w', rfl,
                    GalilScaffoldChainWatch.outer_canonical ho ⟨hcl, hcm⟩, ?_, ?_⟩
                  · cases ho with
                    | queued hz =>
                      show _ ≤ value (GalilScaffoldChainWatch.queued _).lag
                      simp only [GalilScaffoldChainWatch.queued, inc_value]
                      omega
                    | immediate hz hg =>
                      show _ ≤ value (GalilScaffoldChainWatch.immediate _).lag
                      simp only [GalilScaffoldChainWatch.immediate]
                      exact le_refl _
                  · cases ho with
                    | queued hz =>
                      show value (GalilScaffoldChainWatch.queued _).lag ≤ _
                      simp only [GalilScaffoldChainWatch.queued, inc_value]
                      simp
                    | immediate hz hg =>
                      show value (GalilScaffoldChainWatch.immediate _).lag ≤ _
                      simp only [GalilScaffoldChainWatch.immediate]
                      simp
      | next v' hf hl hr =>
        cases htk with
        | cons ht htr =>
          obtain ⟨m, hs, hm⟩ := ht
          cases hs with
          | backDone v'' h'' lag'' margin'' ver'' hf' =>
            rw [hf] at hf'; exact absurd hf' (by decide)
          | backStep v'' h'' lag'' margin'' ver'' hf' =>
            cases b with
            | false =>
              simp only [Bool.false_eq_true, if_false] at hm
              subst hm
              rcases ih cs' hcs' hr htr hcl hcm with ⟨w, hy, hcw, hlo, hlw⟩ | ⟨w, hy⟩
              · exact Or.inl ⟨w, hy, hcw, hlo, by simpa using hlw⟩
              · exact Or.inr ⟨w, hy⟩
            | true =>
              simp only [if_true] at hm
              cases hm with
              | «back» _ _ _ _ _ =>
                rcases ih cs' hcs' hr htr (inc_canonical _ hcl) (inc_canonical _ hcm) with
                  ⟨w, hy, hcw, hlo, hlw⟩ | ⟨w, hy⟩
                · refine Or.inl ⟨w, hy, hcw, ?_, ?_⟩
                  · rw [inc_value] at hlo; omega
                  · rw [inc_value] at hlw
                    have hcc : (((true :: cs').count true : ℕ) : ℤ) = (cs'.count true : ℕ) + 1 := by
                      simp
                    rw [hcc]
                    omega
                · exact Or.inr ⟨w, hy⟩


/-! ## 4. Cutting the prelude into copy / copyEnd / back -/

theorem chainTicks_append_inv (as : List Bool) : ∀ {bs : List Bool} {x z : ChainVM},
    ChainTicks (as ++ bs) x z → ∃ y, ChainTicks as x y ∧ ChainTicks bs y z := by
  induction as with
  | nil => intro bs x z h; exact ⟨x, .nil _, by simpa using h⟩
  | cons a as ih =>
    intro bs x z h
    cases h with
    | cons ht hr =>
      obtain ⟨y, h1, h2⟩ := ih hr
      exact ⟨y, .cons ht h1, h2⟩

theorem split_prelude (es : List Bool) (h : ℕ) (hlen : es.length = 2 * h + 2) :
    ∃ (bs cs : List Bool) (dm : Bool),
      es = bs ++ dm :: cs ∧ bs.length = h ∧ cs.length = h + 1 := by
  have hlt : h < es.length := by omega
  refine ⟨es.take h, es.drop (h + 1), es[h], ?_, ?_, ?_⟩
  · conv_lhs => rw [← List.take_append_drop h es]
    rw [List.drop_eq_getElem_cons hlt]
  · rw [List.length_take]; omega
  · rw [List.length_drop]; omega

/-! ## 5. The corrected `PreludeEnds` -/

/-- **`PreludeEnds'` — the corrected form of `GalilPreludeDone.PreludeEnds`.**

Two changes, both forced by the definitions (see the module docstring):

* the entry lag is bounded by `value radius + (2h+2)`, not by `2h+2`, because
  `chainStart` aliases `lag` to `radius`;
* the chain may be `.broken` instead of `.watch`, because the last of the
  `2h+2` ticks enters `.watch` and *then* takes its credit.

Unlike `PreludeEnds` this is not assumed: `preludeEnds_of_chain` proves it. -/
def PreludeEnds' (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (answer : GalilScaffoldTape.Tape) (cc : Fin 3) (walker : GalilScaffoldPlace.Place)
    (ver : PlaceHead) (radius : Counter) (h : ℕ) : Prop :=
  ∀ {es : List Bool} {c0 c1 : Control} {v0 v1 : GalilVM},
    es.length = 2 * h + 2 → c0.clock ≤ delay →
    WatchSegE P q first delay es c0 v0 c1 v1 →
    v0.chain = chainStart answer cc walker ver radius →
    (∃ w : GalilScaffoldChainWatch.State,
        v1.chain = .watch w ∧ GalilScaffoldChainWatch.CanonicalState w ∧
          0 ≤ value w.lag ∧ value w.lag ≤ value radius + ((2 * h + 2 : ℕ) : ℤ))
      ∨ (∃ w : GalilScaffoldChainWatch.State, v1.chain = .broken w)

/-- **`PreludeEnds'`, proved.**  The copy/back data are exactly the ones
`GalilPrepConstruct.prep_segment_construct` uses (suppliers:
`GalilScaffoldChainPeriod.found_start_back` from the found DP quantum); the
positivity side condition `positive (ofNat h) = true` that the *construction*
needs is not needed here, because every background step of the prelude is
forced by the tape shapes.  The event list is arbitrary: the scan may credit
the chain at any subset of the `2h+2` ticks. -/
theorem preludeEnds_of_chain (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    (answer : GalilScaffoldTape.Tape) (cen : Fin 3) (p q' : GalilScaffoldPlace.Place)
    (ver : PlaceHead) (radius : Counter) (u : GalilScaffoldTape.Tape)
    (h : ℕ) (ys : List (Fin 3)) (b : Fin 3) (watchTape : GalilScaffoldChainPeriod.Tape)
    (hcopy : GalilScaffoldChainPeriod.Copy answer reset p (GalilScaffoldChainPeriod.start cen) h u
      (ofNat h) q' (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])))
    (hu : u.focus = 4)
    (hfocus : (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen)
      (ys ++ [b])).focus = .plain b)
    (hback : GalilScaffoldChainPeriod.Back (GalilScaffoldChainPeriod.write
      (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b]))
      (.last b)) (h + 1) watchTape)
    (hcan : Canonical radius) (hnn : 0 ≤ value radius) :
    PreludeEnds' P qq first delay answer cen p ver radius h := by
  intro es c0 c1 v0 v1 hlen hclock hseg hstart
  have hne0 : v0.chain ≠ .idle := by rw [hstart]; intro h0; cases h0
  have hticks : ChainTicks es v0.chain v1.chain :=
    (watchSegE_events P qq first delay hseg hne0).1
  rw [hstart] at hticks
  obtain ⟨bs, cs, dm, hes, hbs, hcs⟩ := split_prelude es h hlen
  subst hes
  have hstart' : chainStart answer cen p ver radius
      = ChainVM.copy answer reset p (GalilScaffoldChainPeriod.start cen) radius radius ver := rfl
  rw [hstart'] at hticks
  obtain ⟨y1, ht1, ht2⟩ := chainTicks_append_inv bs hticks
  obtain ⟨l1, m1, hy1, hc1, hm1, hv1⟩ := copy_ticks_inv h bs hbs hcopy ht1 hcan hcan
  subst hy1
  cases ht2 with
  | cons htick htail =>
    obtain ⟨l2, m2, hy2, hc2, hm2, hv2⟩ := copyEnd_tick_inv hu hfocus htick hc1 hm1
    subst hy2
    rcases back_ticks_inv (h + 1) cs hcs hback htail hc2 hm2 with
      ⟨w, hw, hcw, hlo, hlw⟩ | ⟨w, hw⟩
    · refine Or.inl ⟨w, hw, hcw, ?_, ?_⟩
      · have : (0 : ℤ) ≤ (bs.count true : ℤ) := by positivity
        omega
      · have hb1 : bs.count true ≤ h := by
          have := List.count_le_length (l := bs) (a := true); omega
        have hb2 : cs.count true ≤ h + 1 := by
          have := List.count_le_length (l := cs) (a := true); omega
        have hb3 : ((dm :: ([] : List Bool)).count true) ≤ 1 := by
          cases dm <;> simp
        have hcast1 : ((bs.count true : ℕ) : ℤ) ≤ (h : ℤ) := by exact_mod_cast hb1
        have hcast2 : ((cs.count true : ℕ) : ℤ) ≤ ((h : ℤ) + 1) := by exact_mod_cast hb2
        have hcast3 : (((dm :: ([] : List Bool)).count true : ℕ) : ℤ) ≤ 1 := by
          exact_mod_cast hb3
        push_cast
        omega
    · exact Or.inr ⟨w, hw⟩

/-! ## 6. The corrected `prelude_done_before_extent` -/

/-- **`prelude_done_before_extent'`.**  The same collision of counts as
`GalilPreludeDone.prelude_done_before_extent`, but with the corrected entry
lag — which forces the extra hypothesis `hradius`.

`hradius : value radius ≤ 4090*h - 2052` is what the arithmetic needs and
essentially all it needs: consuming `2h` places costs at least `4096h - 2048`
ticks, of which at most a `1/2048` fraction are matched, so the tail after the
`2h+2`-tick prelude offers at least `(2047·(4094h - 2050) - 2048)/2048` ticks
of catch-up, and the lag to pay is `value radius + (2h+2)`.  Morally:
`radius ≲ 2·delay·h`.

This hypothesis is *new*.  `GalilPreludeDone`'s version did not need it only
because its `PreludeEnds` asserted a lag bound (`≤ 2h+2`) that `chainStart`
falsifies.  It is not proved anywhere in this file and must be supplied by the
search contract relating a found radius to its semiperiod. -/
theorem prelude_done_before_extent' (P : Shared) (q : ℕ) (first : Fin 9)
    (answer : GalilScaffoldTape.Tape) (cc : Fin 3) (walker : GalilScaffoldPlace.Place)
    (ver : PlaceHead) (radius : Counter) (h : ℕ) (hh : 1 ≤ h)
    (hradius : value radius ≤ 4090 * (h : ℤ) - 2052)
    (hprelude : PreludeEnds' P q first 2048 answer cc walker ver radius h)
    {es : List Bool} {c0 c1 : Control} {v0 v1 : GalilVM}
    (hseg : WatchSegE P q first 2048 es c0 v0 c1 v1)
    (hclock : c0.clock ≤ 2048)
    (hstart : v0.chain = chainStart answer cc walker ver radius)
    (hrad : value v0.radius + ((2 * h : ℕ) : ℤ) ≤ value v1.radius)
    (hnb : ∀ w : GalilScaffoldChainWatch.State, v1.chain ≠ .broken w) :
    ∃ w : GalilScaffoldChainWatch.State, v1.chain = .watch w ∧ zero w.lag = true := by
  have hne0 : v0.chain ≠ .idle := by rw [hstart]; intro h0; cases h0
  have hev := watchSegE_events P q first 2048 hseg hne0
  have hcount : 2 * h ≤ es.count true := by
    have hr := hev.2.2.2.2.1
    omega
  have hsp := GalilPreludeDone.watchSegE_match_spacing P q first 2048 hseg hclock
  have hlen : 2 * h + 2 ≤ es.length := by omega
  have hcat : es.take (2 * h + 2) ++ es.drop (2 * h + 2) = es := List.take_append_drop _ _
  obtain ⟨c'', s'', seg1, seg2⟩ :=
    watchSegE_append P q first 2048 (es.take (2 * h + 2)) (by rw [hcat]; exact hseg)
  have hpre : (es.take (2 * h + 2)).length = 2 * h + 2 := by
    rw [List.length_take]; omega
  have hclock'' : c''.clock ≤ 2048 := watchSegE_clock_le P q first 2048 seg1 hclock
  have hsp2 := GalilPreludeDone.watchSegE_match_spacing P q first 2048 seg2 hclock''
  have hsplit : (es.take (2 * h + 2)).length + (es.drop (2 * h + 2)).length = es.length := by
    rw [← List.length_append, hcat]
  have hbc := GalilScaffoldChainLag.bool_counts (es.drop (2 * h + 2))
  -- the two count facts, in the form the final `omega` uses
  have hDL : 4094 * h ≤ (es.drop (2 * h + 2)).length + 2050 := by omega
  have hDF : 2047 * (es.drop (2 * h + 2)).length
      ≤ 2048 * (es.drop (2 * h + 2)).count false + 2048 := by omega
  rcases hprelude hpre hclock seg1 hstart with ⟨w, hw, hcan, hn, hlag⟩ | ⟨w, hw⟩
  · have hne1 : s''.chain ≠ .idle := by rw [hw]; intro h0; cases h0
    have hev2 := watchSegE_events P q first 2048 seg2 hne1
    have hticks : ChainTicks (es.drop (2 * h + 2)) (.watch w) v1.chain := by
      rw [← hw]; exact hev2.1
    rcases GalilPreludeDone.chainTicks_from_watch _ hticks with ⟨w', hw'⟩ | ⟨w', hw'⟩
    · refine ⟨w', hw', ?_⟩
      rw [hw'] at hticks
      have hsupply : value w.lag ≤ (((es.drop (2 * h + 2)).count false : ℕ) : ℤ) := by
        have h1 : (2047 : ℤ) * ((es.drop (2 * h + 2)).length : ℤ)
            ≤ 2048 * (((es.drop (2 * h + 2)).count false : ℕ) : ℤ) + 2048 := by exact_mod_cast hDF
        have h2 : (4094 : ℤ) * (h : ℤ) ≤ ((es.drop (2 * h + 2)).length : ℤ) + 2050 := by
          exact_mod_cast hDL
        push_cast at hlag
        omega
      exact GalilScaffoldChainLag.catches (chainTicks_watch_run _ hticks) hcan hn hsupply
    · exact absurd hw' (hnb w')
  · have hne1 : s''.chain = .broken w := hw
    have hev2 := watchSegE_events P q first 2048 seg2 (by rw [hw]; intro h0; cases h0)
    have hticks : ChainTicks (es.drop (2 * h + 2)) (.broken w) v1.chain := by
      rw [← hw]; exact hev2.1
    exact absurd (broken_stays _ hticks) (hnb w)

#print axioms copy_ticks_inv
#print axioms copyEnd_tick_inv
#print axioms back_ticks_inv
#print axioms chainTicks_append_inv
#print axioms split_prelude
#print axioms preludeEnds_of_chain
#print axioms prelude_done_before_extent'

end PalPeg.GalilPreludeEnds
