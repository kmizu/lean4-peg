import PalPeg.GalilReplayGeneral
import PalPeg.GalilWatchOkInst
import PalPeg.GalilChainTickable
import PalPeg.GalilFrontier
import PalPeg.GalilPrepMatch

/-!
# The replay with a live chain, without `WatchOk`/`hgood`

`GalilReplayGeneral.replay_after_fallback_general` is vacuous
(`GalilWatchOkInst.no_watchOk_instance`).  Here the chain is carried along the
replay by `PartS raw B s := ChainPart raw (position s.center) B (position s.right) s.chain`:

* `.copy`: verifier at the centre, lag bookkeeping `position ver + |lag| = R`,
  a `Copy` relation to the block `fill (start c) (xs ++ [b])`, `SpanWindow` for it;
* `.back`: the tape reads as `blockTokens c b xs`, same bookkeeping and window;
* `.watch w`: `SpanCore raw c b xs (C+1) w.machine`, `SpanWindow … (C+1) B`,
  bookkeeping `position verifier + |lag| = R`.

The per-tick bound is `R + 1 ≤ B` (resp. `R ≤ B`), supplied by
`Bnd B s : position s.right + replay = B` — the verifier trails the right head
exactly by the lag, so every consume reads at most the cell the right head
reaches after the tick.  `B = position t.right + r` is the landing's right end.

The only non-derived input is the named hypothesis `ReplaySpan` (the chain's
period is a period of the landing palindrome); `StartShape` supplies the answer
shape.  `replay_after_fallback_general'` is the repaired theorem.
-/

set_option autoImplicit false

namespace PalPeg.GalilReplayGeneral2

open PalPeg PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilTickFun PalPeg.GalilTickFun2
  PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct PalPeg.GalilReplayChainSeg
  PalPeg.GalilBranchInvariants PalPeg.GalilReplayGeneral PalPeg.GalilWatchOkInst
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

abbrev WState := GalilScaffoldChainWatch.State

/-! ## 1. Period-tape bookkeeping -/

/-- The tape read as one list. -/
def flat (v : GalilScaffoldChainPeriod.Tape) : List GalilScaffoldChainPeriod.Token :=
  v.left.reverse ++ v.focus :: v.right

theorem flat_moveLeft (v : GalilScaffoldChainPeriod.Tape) :
    flat (GalilScaffoldChainPeriod.moveLeft v) = flat v := by
  rcases v with ⟨ls, f, rs⟩
  cases ls with
  | nil => rfl
  | cons a ls => simp [flat, GalilScaffoldChainPeriod.moveLeft]

theorem fill_append (v : GalilScaffoldChainPeriod.Tape) (xs ys : List (Fin 3)) :
    GalilScaffoldChainPeriod.fill v (xs ++ ys) =
      GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.fill v xs) ys := by
  induction xs generalizing v with
  | nil => rfl
  | cons a xs ih => exact ih _

theorem fill_right_flat (xs : List (Fin 3)) : ∀ (v : GalilScaffoldChainPeriod.Tape), v.right = [] →
    (GalilScaffoldChainPeriod.fill v xs).right = [] ∧
      flat (GalilScaffoldChainPeriod.fill v xs) =
        flat v ++ xs.map GalilScaffoldChainPeriod.Token.plain := by
  induction xs with
  | nil => intro v hv; exact ⟨hv, by simp [GalilScaffoldChainPeriod.fill]⟩
  | cons a xs ih =>
    intro v hv
    rcases v with ⟨ls, f, rs⟩
    simp only at hv
    subst hv
    obtain ⟨h1, h2⟩ := ih (GalilScaffoldChainPeriod.put ⟨ls, f, []⟩ a) rfl
    refine ⟨h1, ?_⟩
    show flat (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.put ⟨ls, f, []⟩ a) xs) = _
    rw [h2]
    simp [flat, GalilScaffoldChainPeriod.put, GalilScaffoldChainPeriod.write,
      GalilScaffoldChainPeriod.moveRight]

theorem fill_last_focus (v : GalilScaffoldChainPeriod.Tape) (xs : List (Fin 3)) (b : Fin 3) :
    (GalilScaffoldChainPeriod.fill v (xs ++ [b])).focus = .plain b := by
  rw [fill_append]; rfl

theorem flat_block (c b : Fin 3) (xs : List (Fin 3)) :
    flat (GalilScaffoldChainPeriod.write
      (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start c) (xs ++ [b])) (.last b)) =
      blockTokens c b xs := by
  rw [fill_append]
  obtain ⟨h1, h2⟩ := fill_right_flat xs (GalilScaffoldChainPeriod.start c) rfl
  generalize hz : GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start c) xs = z at h1 h2
  rcases z with ⟨ls, f, rs⟩
  simp only at h1
  subst h1
  simp only [flat, GalilScaffoldChainPeriod.start, List.reverse_nil, List.nil_append] at h2
  simp only [flat, GalilScaffoldChainPeriod.fill, GalilScaffoldChainPeriod.put,
    GalilScaffoldChainPeriod.write, GalilScaffoldChainPeriod.moveRight, blockTokens]
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at h2 ⊢
  have e : ls.reverse ++ [f, GalilScaffoldChainPeriod.Token.last b] =
      (ls.reverse ++ [f]) ++ [GalilScaffoldChainPeriod.Token.last b] := by simp
  rw [e, h2]; simp

/-- At `isFirst`, a tape reading as a block is the rewound block. -/
theorem rewound_of_flat {v : GalilScaffoldChainPeriod.Tape} {c b : Fin 3} {xs : List (Fin 3)}
    (hv : flat v = blockTokens c b xs) (hf : GalilScaffoldChainPeriod.isFirst v.focus = true) :
    v = ⟨[], .first c, xs.map GalilScaffoldChainPeriod.Token.plain ++ [.last b]⟩ := by
  rcases v with ⟨ls, f, rs⟩
  simp only [flat, blockTokens] at hv hf
  cases ls using List.reverseRecOn with
  | nil =>
    simp only [List.reverse_nil, List.nil_append, List.cons.injEq] at hv
    rw [hv.1, hv.2]
  | append_singleton ls a _ =>
    exfalso
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.cons.injEq] at hv
    have hmem : f ∈ xs.map GalilScaffoldChainPeriod.Token.plain ++
        [GalilScaffoldChainPeriod.Token.last b] := by
      rw [← hv.2]; simp
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hmem
    rcases hmem with ⟨y, _, rfl⟩ | rfl <;> simp [GalilScaffoldChainPeriod.isFirst] at hf

/-! ## 2. Copy-relation from the answer shape -/

theorem copy_of_ahead (n : ℕ) : ∀ (t : GalilScaffoldTape.Tape) (j : ℕ)
    (p : GalilScaffoldPlace.Place) (v : GalilScaffoldChainPeriod.Tape),
    AnswerAhead t n → PlaceAhead p n →
    ∃ u q, GalilScaffoldChainPeriod.Copy t (ofNat j) p v n u (ofNat (j+n)) q
      (GalilScaffoldChainPeriod.fill v ((GalilScaffoldPlace.stream p).tail.take n)) ∧
      u.focus = 4 := by
  induction n with
  | zero =>
    intro t j p v ha _
    exact ⟨t, p, by simpa [GalilScaffoldChainPeriod.fill] using GalilScaffoldChainPeriod.Copy.stop t (ofNat j) p v,
      answerAhead_zero ha⟩
  | succ n ih =>
    intro t j p v ha hp
    have hr := placeAhead_read hp
    cases hread : GalilScaffoldPlace.read (GalilScaffoldPlace.left p) with
    | none => exact absurd hread hr
    | some a =>
      obtain ⟨u, q, hc, hu⟩ := ih (GalilScaffoldTape.moveLeft t) (j+1) (GalilScaffoldPlace.left p)
        (GalilScaffoldChainPeriod.put v a) (answerAhead_step ha) (placeAhead_step hp)
      refine ⟨u, q, ?_, hu⟩
      have hs : (GalilScaffoldPlace.stream p).tail = a :: (GalilScaffoldPlace.stream
          (GalilScaffoldPlace.left p)).tail := by
        rw [← GalilScaffoldPlace.left_stream]
        have h2 := GalilScaffoldPlace.read_stream (GalilScaffoldPlace.left p)
        rw [hread] at h2
        cases hl : GalilScaffoldPlace.stream (GalilScaffoldPlace.left p) with
        | nil => rw [hl] at h2; simp at h2
        | cons x xs => rw [hl] at h2; simp at h2; subst h2; rfl
      rw [hs, List.take_succ_cons]
      have e : j + (n+1) = j+1+n := by omega
      rw [e]
      rw [← inc_ofNat] at hc
      exact .next a (answerAhead_succ_focus ha) (answerAhead_succ_left ha) hread hc

theorem copy_cases {t : GalilScaffoldTape.Tape} {h : Counter} {p : GalilScaffoldPlace.Place}
    {v : GalilScaffoldChainPeriod.Tape} {n : ℕ} {u : GalilScaffoldTape.Tape} {d : Counter}
    {q : GalilScaffoldPlace.Place} {z : GalilScaffoldChainPeriod.Tape}
    (hc : GalilScaffoldChainPeriod.Copy t h p v n u d q z) :
    (n = 0 ∧ t = u ∧ h = d ∧ v = z) ∨
    ∃ n' a, n = n'+1 ∧ t.focus = 8 ∧ t.left ≠ [] ∧
      GalilScaffoldPlace.read (GalilScaffoldPlace.left p) = some a ∧
      GalilScaffoldChainPeriod.Copy (GalilScaffoldTape.moveLeft t) (inc h)
        (GalilScaffoldPlace.left p) (GalilScaffoldChainPeriod.put v a) n' u d q z := by
  cases hc with
  | stop => exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | next a one legal present rest => exact Or.inr ⟨_, a, rfl, one, legal, present, rest⟩

/-! ## 3. The replay chain invariant -/

/-- The verifier head: a represented, present head at place `C`. -/
def VerAt (raw : List (Fin 2)) (C : ℕ) (ver : PlaceHead) : Prop :=
  GalilScaffoldInputTrace.Represents ver.head raw ∧ ver.head.focus ≠ none ∧ position ver = C

/-- Lag bookkeeping: the lag is a unary non-negative counter and the verifier
plus the lag is the right head `R`. -/
def LagAt (lag : Counter) (ver : PlaceHead) (R : ℕ) : Prop :=
  lag.neg = [] ∧ position ver + lag.pos.length = R

/-- **The chain invariant along a replay**, relative to the centre place `C`,
the span end `B` and the right-head place `R`.  (`idle`/`broken` excluded.) -/
def ChainPart (raw : List (Fin 2)) (C B R : ℕ) : ChainVM → Prop
  | .idle => False
  | .copy t h p v lag _ ver => VerAt raw C ver ∧ LagAt lag ver R ∧
      ∃ (c b : Fin 3) (xs : List (Fin 3)), SpanWindow raw c b xs (C+1) B ∧
        ∃ n u d q, GalilScaffoldChainPeriod.Copy t h p v n u d q
          (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start c) (xs ++ [b])) ∧
          u.focus = 4 ∧ positive d = true
  | .back v _ lag _ ver => VerAt raw C ver ∧ LagAt lag ver R ∧
      ∃ (c b : Fin 3) (xs : List (Fin 3)), SpanWindow raw c b xs (C+1) B ∧ flat v = blockTokens c b xs
  | .watch w => LagAt w.lag w.machine.verifier R ∧
      ∃ (c b : Fin 3) (xs : List (Fin 3)), SpanWindow raw c b xs (C+1) B ∧
        SpanCore raw c b xs (C+1) w.machine
  | .broken _ => False

theorem chainPart_ne_idle {raw : List (Fin 2)} {C B R : ℕ} {x : ChainVM}
    (h : ChainPart raw C B R x) : x ≠ .idle := by
  intro e; rw [e] at h; exact h

theorem chainPart_ne_broken {raw : List (Fin 2)} {C B R : ℕ} {x : ChainVM}
    (h : ChainPart raw C B R x) (w : WState) : x ≠ .broken w := by
  intro e; rw [e] at h; exact h

section Tick

variable {raw : List (Fin 2)} {C B : ℕ}

theorem watch_internal {R : ℕ} {c b : Fin 3} {xs : List (Fin 3)} {w : WState}
    (hlag : LagAt w.lag w.machine.verifier R) (hc : SpanCore raw c b xs (C+1) w.machine)
    (hwin : SpanWindow raw c b xs (C+1) B) (hB : B < (encoded raw).length) (hR : R ≤ B) :
    ∃ m : WState, GalilScaffoldChainWatch.Internal w m ∧ LagAt m.lag m.machine.verifier R ∧
      SpanCore raw c b xs (C+1) m.machine := by
  obtain ⟨hneg, hpos⟩ := hlag
  rcases w with ⟨mach, ⟨ps, ns⟩, margin⟩
  simp only at hneg hpos hc
  subst hneg
  cases ps with
  | nil =>
    exact ⟨_, .idle _ rfl, ⟨rfl, hpos⟩, hc⟩
  | cons u ps =>
    have hp : positive (⟨u :: ps, []⟩ : Counter) = true := rfl
    have hg := spanCore_good (w := ⟨mach, ⟨u :: ps, []⟩, margin⟩) hc hwin hB
      (by simp at hpos ⊢; omega)
    refine ⟨_, .take _ hp hg, ⟨rfl, ?_⟩, spanCore_internal (.take _ hp hg) hc⟩
    show position (GalilScaffoldChainVerifier.consume mach).verifier + (dec ⟨u :: ps, []⟩).pos.length = R
    rw [consume_position (w := ⟨mach, ⟨u :: ps, []⟩, margin⟩) hc hg]
    simp [dec] at hpos ⊢; omega

theorem watch_credit {R : ℕ} {c b : Fin 3} {xs : List (Fin 3)} {w : WState}
    (hlag : LagAt w.lag w.machine.verifier R) (hc : SpanCore raw c b xs (C+1) w.machine)
    (hwin : SpanWindow raw c b xs (C+1) B) (hB : B < (encoded raw).length) (hR : R + 1 ≤ B) :
    ∃ w' : WState, GalilScaffoldChainWatch.Outer w true w' ∧
      LagAt w'.lag w'.machine.verifier (R+1) ∧ SpanCore raw c b xs (C+1) w'.machine := by
  obtain ⟨hneg, hpos⟩ := hlag
  rcases w with ⟨mach, ⟨ps, ns⟩, margin⟩
  simp only at hneg hpos hc
  subst hneg
  cases ps with
  | nil =>
    have hz : zero (⟨[], []⟩ : Counter) = true := rfl
    have hg := spanCore_good (w := ⟨mach, ⟨[], []⟩, margin⟩) hc hwin hB (by simp at hpos ⊢; omega)
    refine ⟨_, .immediate _ hz hg, ⟨rfl, ?_⟩, spanCore_outer (.immediate _ hz hg) hc⟩
    show position (GalilScaffoldChainVerifier.consume mach).verifier + ([] : List Unit).length = R+1
    rw [consume_position (w := ⟨mach, ⟨[], []⟩, margin⟩) hc hg]
    simp at hpos ⊢; omega
  | cons u ps =>
    have hz : zero (⟨u :: ps, []⟩ : Counter) = false := rfl
    refine ⟨_, .queued _ hz, ⟨rfl, ?_⟩, spanCore_outer (.queued _ hz) hc⟩
    show position mach.verifier + (inc ⟨u :: ps, []⟩).pos.length = R+1
    simp [inc] at hpos ⊢; omega

/-- The background step of a chain in the invariant. -/
theorem part_step {R : ℕ} {x : ChainVM} (hx : ChainPart raw C B R x)
    (hB : B < (encoded raw).length) (hR : R ≤ B) :
    ∃ y, ChainStep x y ∧ ChainPart raw C B R y := by
  cases x with
  | idle => exact hx.elim
  | broken w => exact hx.elim
  | copy t h p v lag margin ver =>
    obtain ⟨hver, hlag, c, b, xs, hwin, n, u, d, q, hcopy, hu, hd⟩ := hx
    rcases copy_cases hcopy with ⟨_, rfl, rfl, rfl⟩ | ⟨n', a, _, one, legal, present, rest⟩
    · have hf := fill_last_focus (GalilScaffoldChainPeriod.start c) xs b
      refine ⟨_, .copyEnd _ _ _ _ _ _ _ b hu hd hf, hver, hlag, c, b, xs, hwin, flat_block c b xs⟩
    · exact ⟨_, .copyBit _ _ _ _ _ _ _ a one legal present, hver, hlag, c, b, xs, hwin,
        n', u, d, q, rest, hu, hd⟩
  | back v h lag margin ver =>
    obtain ⟨hver, hlag, c, b, xs, hwin, hflat⟩ := hx
    cases hf : GalilScaffoldChainPeriod.isFirst v.focus with
    | false =>
      exact ⟨_, .backStep _ _ _ _ _ hf, hver, hlag, c, b, xs, hwin,
        by rw [flat_moveLeft]; exact hflat⟩
    | true =>
      have hv := rewound_of_flat hflat hf
      refine ⟨_, .backDone _ _ _ _ _ hf, hlag, c, b, xs, hwin, ?_⟩
      show SpanCore raw c b xs (C+1) ⟨ver, watchControl v⟩
      rw [hv]
      exact spanCore_born c b xs ver hver.1 hver.2.1 (by rw [hver.2.2])
  | watch w =>
    obtain ⟨hlag, c, b, xs, hwin, hc⟩ := hx
    obtain ⟨m, hi, hlm, hcm⟩ := watch_internal hlag hc hwin hB hR
    exact ⟨_, .watchStep _ _ hi, hlm, c, b, xs, hwin, hcm⟩

theorem lagAt_inc {lag : Counter} {ver : PlaceHead} {R : ℕ} (h : LagAt lag ver R) :
    LagAt (inc lag) ver (R+1) := by
  obtain ⟨hn, hp⟩ := h
  rcases lag with ⟨ps, ns⟩
  simp only at hn hp
  subst hn
  exact ⟨rfl, by simp [inc]; omega⟩

/-- The match credit of a chain in the invariant. -/
theorem part_matched {R : ℕ} {y : ChainVM} (hy : ChainPart raw C B R y)
    (hB : B < (encoded raw).length) (hR : R + 1 ≤ B) :
    ∃ z, ChainMatched y z ∧ ChainPart raw C B (R+1) z := by
  cases y with
  | idle => exact hy.elim
  | broken w => exact hy.elim
  | copy t h p v lag margin ver =>
    obtain ⟨hver, hlag, rest⟩ := hy
    exact ⟨_, .copy _ _ _ _ _ _ _, hver, lagAt_inc hlag, rest⟩
  | back v h lag margin ver =>
    obtain ⟨hver, hlag, rest⟩ := hy
    exact ⟨_, .back _ _ _ _ _, hver, lagAt_inc hlag, rest⟩
  | watch w =>
    obtain ⟨hlag, c, b, xs, hwin, hc⟩ := hy
    obtain ⟨w', ho, hl', hc'⟩ := watch_credit hlag hc hwin hB hR
    exact ⟨_, .watch _ _ ho, hl', c, b, xs, hwin, hc'⟩

/-- **One chain tick in the invariant** — no `WatchOk`, no `Good` hypothesis:
the room `R + 1 ≤ B` (resp. `R ≤ B`) is the per-tick bound. -/
theorem part_tick_false {R : ℕ} {x : ChainVM} (hx : ChainPart raw C B R x)
    (hB : B < (encoded raw).length) (hR : R ≤ B) :
    ∃ z, ChainTick false x z ∧ ChainPart raw C B R z := by
  obtain ⟨y, hs, hy⟩ := part_step hx hB hR
  exact ⟨y, ⟨y, hs, rfl⟩, hy⟩

theorem part_tick_true {R : ℕ} {x : ChainVM} (hx : ChainPart raw C B R x)
    (hB : B < (encoded raw).length) (hR : R + 1 ≤ B) :
    ∃ z, ChainTick true x z ∧ ChainPart raw C B (R+1) z := by
  obtain ⟨y, hs, hy⟩ := part_step hx hB (by omega)
  obtain ⟨z, hm, hz⟩ := part_matched hy hB hR
  exact ⟨z, ⟨y, hs, hm⟩, hz⟩

end Tick

/-! ## 4. The started chain, and the one named hypothesis -/

/-- **Named hypothesis (period match).**  When the search reports `found` on an
idle chain *inside a replay* — scan mode, replaying, `MInv`, the scan invariant
at radius `k`, the radius counter at `k`, `m ≥ 1` comparisons still to replay,
`Frontier` — and the DP answer carries `n ≥ 1` ones over `LEFT` with the walker
able to supply them, then the block the chain will copy, `[FIRST c, xs…, LAST b]`
with `xs ++ [b] = (stream walker).tail.take n`, spans the rest of the replay:
`encoded raw` is `2(|xs|+1)`-periodic on `[C+1, R+m]` and starts with
`bounce c b xs` at `C+1`, where `R + m` is the right end of the palindrome the
replay confirms.  This is exactly the claim that the chain's period is a period
of the landing palindrome (the DP answer's `candidate_periodOn` on the left
window, mirrored by `periodOn_mirror` through `PalAt … C (R+m)`); it is not
derived here. -/
def ReplaySpan (raw : List (Fin 2)) (P : Shared) : Prop :=
  ∀ (c : Control) (s : GalilVM) (a : Bool) (vq : SearchVM) (k m n : ℕ) (xs : List (Fin 3))
    (b : Fin 3),
    c.mode = .scan → c.replaying = true → s.chain = .idle → SearchReady (searchLens.get s) →
    searchEffect P a s vq → vq.search.mode = .found → MInv raw c s →
    ScanInvariant raw (position s.center) k s.left s.right → RadiusRep s.radius k →
    s.replay = ofNat m → 0 < m → Frontier s →
    AnswerAhead (vq.dp.config.tapes 11) n → 0 < n → PlaceAhead (P.place s) n →
    (GalilScaffoldPlace.stream (P.place s)).tail.take n = xs ++ [b] →
    SpanWindow raw (P.centre s) b xs (position s.center + 1) (position s.right + m)

theorem lagAt_radius {radius : Counter} {k : ℕ} (h : RadiusRep radius k) (ver : PlaceHead) :
    LagAt radius ver (position ver + k) := by
  obtain ⟨hc, hv⟩ := h
  rcases radius with ⟨ps, ns⟩
  simp only [value] at hv
  rcases hc with hp | hn
  · simp only at hp; subst hp
    have hv' : (0 : ℤ) - (ns.length : ℤ) = (k : ℤ) := by simpa using hv
    have : ns.length = 0 := by omega
    have hk : k = 0 := by omega
    exact ⟨List.eq_nil_of_length_eq_zero this, by simp [hk]⟩
  · simp only at hn; subst hn
    exact ⟨rfl, by simp at hv ⊢; omega⟩

/-- **The started chain is in the invariant.** -/
theorem part_start {raw : List (Fin 2)} {C B R k n : ℕ} {answer : GalilScaffoldTape.Tape}
    {cc : Fin 3} {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter}
    {xs : List (Fin 3)} {b : Fin 3}
    (hver : VerAt raw C ver) (hrad : RadiusRep radius k) (hR : C + k = R)
    (ha : AnswerAhead answer n) (hp : PlaceAhead walker n)
    (hsplit : (GalilScaffoldPlace.stream walker).tail.take n = xs ++ [b])
    (hwin : SpanWindow raw cc b xs (C+1) B) :
    ChainPart raw C B R (chainStart answer cc walker ver radius) := by
  have hlag := lagAt_radius hrad ver
  rw [hver.2.2, hR] at hlag
  obtain ⟨u, q, hcopy, hu⟩ := copy_of_ahead n answer 0 walker (GalilScaffoldChainPeriod.start cc) ha hp
  rw [hsplit] at hcopy
  have hn : 0 < n := by
    rcases n with _ | n
    · simp at hsplit
    · omega
  refine ⟨hver, hlag, cc, b, xs, hwin, n, u, ofNat (0+n), q, hcopy, hu, ?_⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n'+1 := ⟨n-1, by omega⟩
  rfl

/-- The block split of the walker stream for a positive answer. -/
theorem stream_split {walker : GalilScaffoldPlace.Place} {n : ℕ} (hp : PlaceAhead walker n)
    (hn : 0 < n) : ∃ (xs : List (Fin 3)) (b : Fin 3),
      (GalilScaffoldPlace.stream walker).tail.take n = xs ++ [b] := by
  set L := (GalilScaffoldPlace.stream walker).tail.take n with hL
  have hlen : L.length = n := by
    rw [hL, List.length_take, List.length_tail]; unfold PlaceAhead at hp; omega
  have hne : L ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
  exact ⟨L.dropLast, L.getLast hne, (List.dropLast_append_getLast hne).symm⟩

/-! ## 5. Replay with a live chain, per-tick bounds -/

/-- The replay end: the right head plus the comparisons still to replay. -/
def Bnd (B : ℕ) (s : GalilVM) : Prop :=
  ∀ m, s.replay = ofNat m → position s.right + m = B

theorem bnd_congr {B : ℕ} {s t : GalilVM} (hr : t.right = s.right) (hp : t.replay = s.replay)
    (h : Bnd B s) : Bnd B t := by
  intro m hm; rw [hr]; exact h m (by rw [← hp]; exact hm)

/-- The invariant on the whole VM state. -/
def PartS (raw : List (Fin 2)) (B : ℕ) (s : GalilVM) : Prop :=
  ChainPart raw (position s.center) B (position s.right) s.chain

theorem partS_congr {raw : List (Fin 2)} {B : ℕ} {s t : GalilVM} (hch : t.chain = s.chain)
    (hr : t.right = s.right) (hC : t.center = s.center) (h : PartS raw B s) : PartS raw B t := by
  unfold PartS; rw [hch, hr, hC]; exact h

section Chain

variable (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (B : ℕ)

theorem chain_countdown2 (hB : B < (encoded raw).length) :
    ∀ (j : ℕ) (c : Control) (s : GalilVM), c.mode = .scan → c.replaying = true →
      c.clock = j + 1 → PartS raw B s → position s.right ≤ B →
      ∃ (es : List Bool) (s' : GalilVM),
        ReplayChainSeg P q first delay es c s {c with clock := 1} s' ∧ es.count true = 0 ∧
        PartS raw B s' ∧
        s'.left = s.left ∧ s'.right = s.right ∧ s'.center = s.center ∧ s'.replay = s.replay ∧
        s'.remaining = s.remaining := by
  intro j
  induction j with
  | zero =>
    intro c s hm hrp hclk hpart _
    have hc1 : c.clock = 1 := by omega
    have hc : ({c with clock := 1} : Control) = c := by rw [← hc1]
    refine ⟨[], s, ?_, rfl, hpart, rfl, rfl, rfl, rfl, rfl⟩
    rw [hc]; exact .stop _ _
  | succ j ih =>
    intro c s hm hrp hclk hpart hRB
    have hne : s.chain ≠ .idle := chainPart_ne_idle hpart
    obtain ⟨z, htz, hz⟩ := part_tick_false hpart hB hRB
    have hstep : ChainStep s.chain z := by
      obtain ⟨y, hst, hy⟩ := htz
      have hzy : z = y := hy
      rw [hzy]; exact hst
    obtain ⟨s1, hb, hch1, hl1, hr1, hC1, hrep1⟩ :=
      GalilReplayChainSeg.active_background_exists P q first s hne hstep
    have hrem1 : s1.remaining = s.remaining :=
      (backgroundS_fields P q first hb).2.2.2.2.2.2.2.2.1
    have hp1 : PartS raw B s1 := by unfold PartS; rw [hch1, hr1, hC1]; exact hz
    obtain ⟨es, s2, hseg, hcnt, hp2, hl2, hr2, hC2, hrep2, hrem2⟩ :=
      ih {c with clock := c.clock - 1} s1 hm hrp (by simp; omega) hp1 (by rw [hr1]; exact hRB)
    refine ⟨false :: es, s2, ?_, by simpa using hcnt, hp2,
      by rw [hl2, hl1], by rw [hr2, hr1], by rw [hC2, hC1], by rw [hrep2, hrep1],
      by rw [hrem2, hrem1]⟩
    exact .countC c s s1 hm hrp (by omega) hne hb hseg

theorem chain_compare2 (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (hB : B < (encoded raw).length)
    (c : Control) (s : GalilVM) (k m : ℕ)
    (hm : c.mode = .scan) (hr : c.replaying = true) (hc : c.clock = 1)
    (hpart : PartS raw B s) (hbd : Bnd B s)
    (hM : MInv raw c s) (hi : ScanInvariant raw (position s.center) k s.left s.right)
    (hrp : s.replay = ofNat (m+1)) (hfr : Frontier s) :
    ∃ (c1 : Control) (u : GalilVM),
      ReplayChainSeg P q first delay [true] c s c1 u ∧
      c1.mode = .scan ∧ c1.clock = delay ∧ c1.replaying = decide (0 < m) ∧
      PartS raw B u ∧ Bnd B u ∧ MInv raw c1 u ∧
      ScanInvariant raw (position u.center) (k+1) u.left u.right ∧
      u.replay = ofNat m ∧ position u.right = position s.right + 1 ∧
      u.center = s.center ∧ Frontier u ∧ u.remaining = s.remaining := by
  classical
  have hne : s.chain ≠ .idle := chainPart_ne_idle hpart
  have hbound : position s.right + (m+1) ≤ 2 * arrived s.right := hfr (m+1) hrp
  have hav : canRight s.right := GalilReplaySegment.canRight_of_frontier (Nat.succ_pos m) hbound
  have hmatch : read (left s.left) = read (right s.right) := replay_match_of_minv hM hr hav hi
  have hB1 : position s.right + 1 ≤ B := by have := hbd (m+1) hrp; omega
  obtain ⟨z, htz, hz⟩ := part_tick_true hpart hB hB1
  have hnez : z ≠ .idle := chainPart_ne_idle hz
  set vs : ScanVM := ⟨left s.left, right s.right, z⟩ with hvsdef
  have hcmp : (galilFrame P q first).compare s (scanLens.set s vs) := by
    refine ⟨?_, ?_⟩
    · rw [scanLens.get_set]
      refine ⟨rfl, rfl, ?_⟩
      show ChainTick (decide (read (left s.left) = read (right s.right))) s.chain vs.chain
      rw [decide_eq_true hmatch]; exact htz
    · rw [scanLens.get_set]
  have hmt : (galilFrame P q first).matched (scanLens.set s vs) := hmatch
  set vq : SearchVM := searchLens.get s with hvqdef
  have hq : searchEffect P true s vq := Or.inr ⟨hne, rfl⟩
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
  have hpos : position (right s.right) = position s.right + 1 :=
    right_position s.right hav (represented_position _ raw hi.rightRep hi.rightPresent).1
  have hur : u.right = right s.right := by rw [hudef, replayDec_right, afterCompare_right]
  have hCu : u.center = s.center := by rw [hudef, replayDec_center, afterCompare_center]
  have hchu : u.chain = z := by rw [hudef, replayDec_chain, afterCompare_chain]
  refine ⟨{c with clock := delay, output := o, replaying := !P.replayExhausted u}, u,
    .matchC c s vs vq o hm hr hc hav hne hcmp hmt hq ho (.stop _ _), hm, rfl, hflag,
    ?_, ?_, ?_, ?_, hurep, by rw [hur]; exact hpos, hCu, ?_, rfl⟩
  · unfold PartS; rw [hchu, hur, hpos, hCu]; exact hz
  · intro m' hm'
    have hmm : m' = m := (ofNat_inj (hurep.symm.trans hm')).symm
    subst hmm
    have := hbd (m'+1) hrp
    rw [hur, hpos]; omega
  · exact minv_matchR P hex o delay hr rfl hav hi hM
  · have h0 := matched_invariant' raw vq (vs := vs) rfl rfl hmatch hav hi
    rw [hudef, replayDec_left, replayDec_right, replayDec_center, afterCompare_center]
    exact h0
  · intro m' hm'
    have hmm : m' = m := (ofNat_inj (hurep.symm.trans hm')).symm
    subst hmm
    rw [hur]
    exact right_frontier_step s.right m' hbound

theorem chain_replay_finish2 (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hB : B < (encoded raw).length) :
    ∀ (m : ℕ) (c : Control) (s : GalilVM) (k : ℕ),
      c.mode = .scan → 1 ≤ c.clock → c.replaying = decide (0 < m) → (m = 0 → c.clock = delay) →
      s.replay = ofNat m → PartS raw B s → Bnd B s →
      MInv raw c s → ScanInvariant raw (position s.center) k s.left s.right → Frontier s →
      ∃ (es : List Bool) (c' : Control) (t : GalilVM),
        ReplayChainSeg P q first delay es c s c' t ∧ es.count true = m ∧
        c'.mode = .scan ∧ c'.clock = delay ∧ c'.replaying = false ∧
        t.replay = reset ∧ PartS raw B t ∧ position t.right = B ∧
        MInv raw c' t ∧ ScanInvariant raw (position t.center) (k + m) t.left t.right ∧
        position t.right = position s.right + m ∧ t.center = s.center ∧
        Frontier t ∧ t.remaining = s.remaining := by
  intro m
  induction m with
  | zero =>
    intro c s k hm hclk hrp hc0 hrep hpart hbd hM hi hfr
    exact ⟨[], c, s, .stop _ _, rfl, hm, hc0 rfl, by simpa using hrp, hrep, hpart,
      by simpa using hbd 0 hrep, hM, by simpa using hi, by simp, rfl, hfr, rfl⟩
  | succ n ih =>
    intro c s k hm hclk hrp hc0 hrep hpart hbd hM hi hfr
    have hrt : c.replaying = true := by rw [hrp]; simp
    obtain ⟨j, hj⟩ : ∃ j, c.clock = j + 1 := ⟨c.clock - 1, by omega⟩
    have hRB : position s.right ≤ B := by have := hbd (n+1) hrep; omega
    obtain ⟨es1, s1, hseg1, hcnt1, hp1, hl1, hr1, hC1, hrep1, hrem1⟩ :=
      chain_countdown2 raw P q first delay B hB j c s hm hrt hj hpart hRB
    have hM1 : MInv raw {c with clock := 1} s1 := minv_same rfl hr1 hC1 hrep1 hM
    have hi1 : ScanInvariant raw (position s1.center) k s1.left s1.right := by
      rw [hl1, hr1, hC1]; exact hi
    have hfr1 : Frontier s1 := frontier_congr hr1 hrep1 hfr
    obtain ⟨c2, u, hseg2, hm2, hc2, hr2, hp2, hbd2, hM2, hi2, hrep2, hpos2, hC2, hfr2, hrem2⟩ :=
      chain_compare2 raw P q first delay B hex hB {c with clock := 1} s1 k n hm hrt rfl
        hp1 (bnd_congr hr1 hrep1 hbd) hM1 hi1 (by rw [hrep1, hrep]) hfr1
    obtain ⟨es3, c3, t3, hseg3, hcnt3, hm3, hc3, hr3, hrep3, hp3, hB3, hM3, hi3, hpos3, hC3,
        hfr3, hrem3⟩ :=
      ih c2 u (k+1) hm2 (by rw [hc2]; exact hd) hr2 (fun _ => hc2) hrep2 hp2 hbd2 hM2 hi2 hfr2
    refine ⟨es1 ++ ([true] ++ es3), c3, t3,
      replayChainSeg_trans P q first delay hseg1 (replayChainSeg_trans P q first delay hseg2 hseg3),
      ?_, hm3, hc3, hr3, hrep3, hp3, hB3, hM3, ?_, ?_, ?_, hfr3, ?_⟩
    · simp only [List.count_append, hcnt1, hcnt3, List.count_singleton_self]; omega
    · have e : k + (n+1) = k+1+n := by omega
      rw [e]; exact hi3
    · rw [hpos3, hpos2, hr1]; omega
    · rw [hC3, hC2, hC1]
    · rw [hrem3, hrem2, hrem1]

end Chain

/-! ## 6. The landing of branch (ii), and the idle replay split on `found` -/

/-- `FoundLanding` with `ChainOk Ok` replaced by the replay invariant at the
span end `B` (which the landing's right head has reached). -/
def FoundLanding2 (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (B : ℕ) (c : Control) (s : GalilVM) (k d : ℕ) : Prop :=
  ∃ (es1 : List Bool) (c1 : Control) (s1 : GalilVM) (c2 : Control) (s2 : GalilVM)
    (es2 : List Bool) (c' : Control) (t : GalilVM) (n : ℕ),
    WatchSegE P q first delay es1 c s c1 s1 ∧ s1.chain = .idle ∧ c1.replaying = true ∧
    FoundTick P q first delay c1 s1 c2 s2 ∧
    ReplayChainSeg P q first delay es2 c2 s2 c' t ∧
    StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, s⟩ ⟨c', t⟩ ∧
    ChainTicks es2 s2.chain t.chain ∧
    c'.mode = .scan ∧ c'.clock = delay ∧ c'.replaying = false ∧
    t.replay = reset ∧ t.chain ≠ .idle ∧ PartS raw B t ∧ position t.right = B ∧
    MInv raw c' t ∧ ScanInvariant raw (position t.center) (k + d) t.left t.right ∧
    position t.right = position s.right + d ∧ t.center = s.center ∧
    Frontier t ∧ ReplayRest c' t ∧ t.remaining = s.remaining

theorem foundLanding2_prepend {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {delay B : ℕ} {es0 : List Bool} {n0 : ℕ} {c c1 : Control} {s s1 : GalilVM}
    {k d k1 d1 : ℕ}
    (hseg : WatchSegE P q first delay es0 c s c1 s1)
    (hst : StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n0 ⟨c, s⟩ ⟨c1, s1⟩)
    (hkd : k1 + d1 = k + d) (hpd : position s1.right + d1 = position s.right + d)
    (hC : s1.center = s.center) (hrem : s1.remaining = s.remaining)
    (hL : FoundLanding2 raw P q first delay B c1 s1 k1 d1) :
    FoundLanding2 raw P q first delay B c s k d := by
  obtain ⟨es1, c2, s2, c3, s3, es2, c', t, n, hseg1, hidle, hrp, hft, hrc, hst1, htr, hm, hc, hr,
    hrep, hne, hpart, hBt, hM, hi, hpos, hC', hfr, hrr, hrem'⟩ := hL
  exact ⟨es0 ++ es1, c2, s2, c3, s3, es2, c', t, n0 + n,
    watchSegE_trans P q first delay hseg hseg1, hidle, hrp, hft, hrc, stepsAll_trans hst hst1, htr,
    hm, hc, hr, hrep, hne, hpart, hBt, hM, by rw [← hkd]; exact hi, by rw [hpos]; omega,
    by rw [hC', hC], hfr, hrr, by rw [hrem', hrem]⟩

section Idle

variable (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
  (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ) (B : ℕ)

include hP hP'

omit hP hP' in
/-- The chain started at a found search effect inside the replay is in the
invariant (from `StartShape` and `ReplaySpan`). -/
theorem start_part (hshape : StartShape P) (hspan : ReplaySpan raw P)
    (c : Control) (s : GalilVM) (a : Bool) (vq : SearchVM) (k m : ℕ)
    (hm : c.mode = .scan) (hr : c.replaying = true) (hidle : s.chain = .idle)
    (hsr : SearchReady (searchLens.get s)) (hq : searchEffect P a s vq)
    (hf : vq.search.mode = .found) (hM : MInv raw c s)
    (hi : ScanInvariant raw (position s.center) k s.left s.right) (hrad : RadiusRep s.radius k)
    (hrep : s.replay = ofNat m) (hm0 : 0 < m) (hfr : Frontier s) (hbd : Bnd B s)
    (hcen : GalilScaffoldInputTrace.Represents s.center.head raw ∧ s.center.head.focus ≠ none) :
    ChainPart raw (position s.center) B (position s.right)
      (chainStart (vq.dp.config.tapes 11) (P.centre s) (P.place s) s.center s.radius) := by
  obtain ⟨n, hn, ha, hpl, -⟩ := hshape s a vq hidle hsr hq hf
  obtain ⟨xs, b, hsplit⟩ := stream_split hpl hn
  have hwin := hspan c s a vq k m n xs b hm hr hidle hsr hq hf hM hi hrad hrep hm0 hfr ha hn hpl
    hsplit
  rw [hbd m hrep] at hwin
  exact part_start ⟨hcen.1, hcen.2, rfl⟩ hrad hi.rightPos.symm ha hpl hsplit hwin

theorem idle_countdown2 (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hshape : StartShape P) (hspan : ReplaySpan raw P) (hB : B < (encoded raw).length) :
    ∀ (j : ℕ) (c : Control) (s : GalilVM) (k m : ℕ), c.mode = .scan → c.replaying = true →
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
      FoundLanding2 raw P q first delay B c s k (m+1) := by
  intro j
  induction j with
  | zero =>
    intro c s k m hm hr hc hidle hsr _ _ _ _ _ _ _
    exact Or.inl ⟨c, s, .stop _ _, .zero _ (GalilReplaySegment.soundScanNR_replaying raw hr),
      rfl, rfl, hc, hidle, hsr, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ j ih =>
    intro c s k m hm hr hc hidle hsr hrep hM hi hfr hrad hbd hcen
    obtain ⟨v, hv⟩ := hsearch s hsr false
    have hclt : 1 < c.clock := by omega
    by_cases hf : v.search.mode = .found
    · obtain ⟨s', hb, hch', hl', hr', hC', hrep', hget'⟩ :=
        background_found_step P q first s hidle hv hf
      have hrem' : s'.remaining = s.remaining :=
        (backgroundS_fields P q first hb).2.2.2.2.2.2.2.2.1
      have hpart0 := start_part raw P B hshape hspan c s false v k (m+1) hm hr hidle hsr hv
        hf hM hi hrad hrep (Nat.succ_pos m) hfr hbd hcen
      have hne2 : s'.chain ≠ .idle := by rw [hch']; exact chainStart_ne_idle _ _ _ _ _
      have hp2 : PartS raw B s' := by unfold PartS; rw [hch', hr', hC']; exact hpart0
      have hM2 : MInv raw {c with clock := c.clock - 1} s' := minv_same rfl hr' hC' hrep' hM
      have hi2 : ScanInvariant raw (position s'.center) k s'.left s'.right := by
        rw [hl', hr', hC']; exact hi
      have hfr2 : Frontier s' := frontier_congr hr' hrep' hfr
      obtain ⟨es, c', t, hseg, -, hm', hc', hr'', hrep'', hp'', hB'', hM'', hi'', hpos'', hC'',
          hfr'', hrem''⟩ :=
        chain_replay_finish2 raw P q first delay B hex hd hB (m+1) {c with clock := c.clock - 1}
          s' k hm (by show 1 ≤ c.clock - 1; omega)
          (by show c.replaying = decide (0 < m+1); rw [hr]; simp)
          (fun h => absurd h (Nat.succ_ne_zero m)) (by rw [hrep', hrep]) hp2
          (bnd_congr hr' hrep' hbd) hM2 hi2 hfr2
      obtain ⟨n, hst⟩ := replayChainSeg_stepsAll raw P hP hP' q first delay hseg (position s'.center)
        k hi2 (GalilReplaySegment.soundScanNR_replaying raw hr)
      exact Or.inr ⟨[], c, s, {c with clock := c.clock - 1}, s', es, c', t, n+1, .stop _ _, hidle,
        hr, .bg c s s' hm hr hclt hidle hb (by rw [hget']; exact hf), hseg,
        .succ (GalilReplaySegment.soundScanNR_replaying raw hr)
          (.scan_count c s s' hm (Or.inl hr) hclt hb) hst,
        replayChainSeg_chain P q first delay hseg hne2, hm', hc', hr'', hrep'',
        chainPart_ne_idle hp'', hp'', hB'', hM'',
        hi'', by rw [hpos'', hr'], by rw [hC'', hC'], hfr'',
        replayRest_of_reset hrep'', by rw [hrem'', hrem']⟩
    · obtain ⟨s', hb, hch', hl', hr', hC', hrep', hget'⟩ :=
        idle_background_exists P q first s hidle hv hf
      have hsr' : SearchReady (searchLens.get s') := by rw [hget']; exact hpres s false v hsr hv
      have hrem' : s'.remaining = s.remaining :=
        (backgroundS_fields P q first hb).2.2.2.2.2.2.2.2.1
      have hrad' : s'.radius = s.radius := (backgroundS_fields P q first hb).2.2.2.2.2.1
      have hQ' : SoundScanNR raw ⟨{c with clock := c.clock - 1}, s'⟩ :=
        GalilReplaySegment.soundScanNR_replaying raw hr
      rcases ih {c with clock := c.clock - 1} s' k m hm hr (by simp; omega) hch' hsr'
          (by rw [hrep', hrep]) (minv_same rfl hr' hC' hrep' hM) (by rw [hl', hr', hC']; exact hi)
          (frontier_congr hr' hrep' hfr) (by rw [hrad']; exact hrad) (bnd_congr hr' hrep' hbd)
          (by rw [hC']; exact hcen) with hA | hB
      · obtain ⟨c1, t, hseg, hst, hm1, hr1, hc1, hidle1, hsr1, hl1, hrr1, hC1, hrp1, hrem1,
          hrd1⟩ := hA
        exact Or.inl ⟨c1, t, .countR c s s' hm hr hclt hidle hb hseg,
          .succ (GalilReplaySegment.soundScanNR_replaying raw hr)
            (.scan_count c s s' hm (Or.inl hr) hclt hb) hst,
          hm1, hr1, hc1, hidle1, hsr1, by rw [hl1, hl'], by rw [hrr1, hr'], by rw [hC1, hC'],
          by rw [hrp1, hrep'], by rw [hrem1, hrem'], by rw [hrd1, hrad']⟩
      · refine Or.inr (foundLanding2_prepend
          (WatchSegE.countR c s s' hm hr hclt hidle hb (.stop _ _))
          (.succ (GalilReplaySegment.soundScanNR_replaying raw hr)
            (.scan_count c s s' hm (Or.inl hr) hclt hb) (.zero _ hQ'))
          rfl (by rw [hr']) hC' hrem' hB)

theorem idle_compare2 (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hshape : StartShape P) (hspan : ReplaySpan raw P) (hB : B < (encoded raw).length)
    (c : Control) (s : GalilVM) (k m : ℕ)
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
    FoundLanding2 raw P q first delay B c s k (m+1) := by
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
    have hpart0 := start_part raw P B hshape hspan c s true vq k (m+1) hm hr hidle hsr hq
      hf hM hi hrad hrp (Nat.succ_pos m) hfr hbd hcen
    obtain ⟨z, hch, hz⟩ := part_matched hpart0 hB (by omega)
    have hnez : z ≠ ChainVM.idle := chainPart_ne_idle hz
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
    have hpu : PartS raw B u := by
      unfold PartS
      rw [hudef, replayDec_chain, afterCompare_chain, ← hudef, hur, hpos, hCu]; exact hz
    have hbdu : Bnd B u := by
      intro m' hm'
      have hmm : m' = m := (ofNat_inj (hurep.symm.trans hm')).symm
      subst hmm
      rw [hur, hpos]; omega
    have hposu : position u.right = position s.right + 1 := by rw [hur]; exact hpos
    have hfru : Frontier u := by
      intro m' hm'
      have hmm : m' = m := (ofNat_inj (hurep.symm.trans hm')).symm
      subst hmm
      rw [hur]
      exact right_frontier_step s.right m' hbound
    obtain ⟨es, c', t, hseg, -, hm', hc', hr', hrep', hp', hB', hM', hi', hpos', hC', hfr',
        hrem'⟩ :=
      chain_replay_finish2 raw P q first delay B hex hd hB m
        {c with clock := delay, output := o, replaying := !P.replayExhausted u} u (k+1) hm hd hflag
        (fun _ => rfl) hurep hpu hbdu hMu hiu hfru
    have hQu : SoundScanNR raw
        ⟨{c with clock := delay, output := o, replaying := !P.replayExhausted u}, u⟩ :=
      fun _ _ => outputRel_of_refresh' raw P hP hP' q first u c.output o hiu ho _ rfl
    obtain ⟨n, hst⟩ := replayChainSeg_stepsAll raw P hP hP' q first delay hseg _ (k+1) hiu hQu
    have ht := scan_match_found_S' P q first delay c s vs vq o hm (Or.inl hr) hc hidle rfl rfl hmt
      hq hf hch (by rw [hr]; exact ho)
    rw [hr] at ht
    exact Or.inr ⟨[], c, s, _, u, es, c', t, n+1, .stop _ _, hidle, hr,
      .cmp c s vs vq o hm hr hc hav hidle rfl rfl hmt hq hf hch ho, hseg,
      .succ (GalilReplaySegment.soundScanNR_replaying raw hr) (by simpa using ht) hst,
      replayChainSeg_chain P q first delay hseg hneu, hm', hc', hr', hrep',
      chainPart_ne_idle hp', hp', hB', hM',
      by have e : k + (m+1) = k+1+m := by omega
         rw [e]; exact hi',
      by rw [hpos', hposu]; omega, by rw [hC', hCu], hfr',
      replayRest_of_reset hrep', by rw [hrem']; rfl⟩
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

theorem replay_general_construct2 (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hshape : StartShape P) (hspan : ReplaySpan raw P) (hB : B < (encoded raw).length) :
    ∀ (r : ℕ) (c : Control) (s : GalilVM) (k : ℕ),
      c.mode = .scan → c.clock = delay → c.replaying = decide (0 < r) →
      s.replay = ofNat r → s.chain = ChainVM.idle → SearchReady (searchLens.get s) →
      MInv raw c s → ScanInvariant raw (position s.center) k s.left s.right → Frontier s →
      RadiusRep s.radius k → Bnd B s →
      (GalilScaffoldInputTrace.Represents s.center.head raw ∧ s.center.head.focus ≠ none) →
      (∃ (es : List Bool) (c' : Control) (t : GalilVM),
        WatchSegE P q first delay es c s c' t ∧
        (SoundScanNR raw ⟨c', t⟩ →
          StepsAll (galilFrameS P q first) delay (SoundScanNR raw) es.length ⟨c, s⟩ ⟨c', t⟩) ∧
        es.length = r * delay ∧ es.count true = r ∧
        c'.mode = .scan ∧ c'.clock = delay ∧ c'.replaying = false ∧
        t.replay = reset ∧ t.chain = ChainVM.idle ∧ SearchReady (searchLens.get t) ∧
        MInv raw c' t ∧ ScanInvariant raw (position t.center) (k + r) t.left t.right ∧
        position t.right = position s.right + r ∧ t.center = s.center ∧
        Frontier t ∧ ReplayRest c' t ∧ t.remaining = s.remaining) ∨
      FoundLanding2 raw P q first delay B c s k r := by
  intro r
  induction r with
  | zero =>
    intro c s k hm hc hrp hrep hidle hsr hM hi hfr _ _ _
    have hrf : c.replaying = false := by rw [hrp]; simp
    exact Or.inl ⟨[], c, s, .stop _ _, fun hlast => .zero _ hlast, by simp, by simp, hm, hc, hrf,
      hrep, hidle, hsr, hM, by simpa using hi, by simp, rfl, hfr,
      replayRest_of_reset hrep, rfl⟩
  | succ n ih =>
    intro c s k hm hc hrp hrep hidle hsr hM hi hfr hrad hbd hcen
    have hrt : c.replaying = true := by rw [hrp]; simp
    rcases idle_countdown2 raw P hP hP' q first delay B hex hd hsearch hpres hshape hspan hB
        (delay - 1) c s k n hm hrt (by omega) hidle hsr hrep hM hi hfr hrad hbd hcen with hA | hB2
    · obtain ⟨c1, t1, hseg1, hst1, hm1, hr1, hc1, hidle1, hsr1, hl1, hrr1, hC1, hrp1, hrem1,
        hrd1⟩ := hA
      have hm1' : c1.mode = Mode.scan := by rw [hm1, hm]
      have hr1' : c1.replaying = true := by rw [hr1, hrt]
      have hM1 : MInv raw c1 t1 := minv_same (by rw [hr1]) hrr1 hC1 hrp1 hM
      have hi1 : ScanInvariant raw (position t1.center) k t1.left t1.right := by
        rw [hl1, hrr1, hC1]; exact hi
      have hfr1 : Frontier t1 := frontier_congr hrr1 hrp1 hfr
      rcases idle_compare2 raw P hP hP' q first delay B hex hd hsearch hpres hshape hspan hB c1 t1
          k n hm1' hr1' hc1 hidle1 hsr1 hM1 hi1 (by rw [hrp1, hrep]) hfr1
          (by rw [hrd1]; exact hrad) (bnd_congr hrr1 hrp1 hbd) (by rw [hC1]; exact hcen)
          with hA2 | hB3
      · obtain ⟨c2, u, hseg2, hst2, hm2, hc2, hr2, hidle2, hsr2, hM2, hi2, hrep2, hpos2, hC2, hfr2,
          hrem2, hrad2, hbd2⟩ := hA2
        have hcen2 : GalilScaffoldInputTrace.Represents u.center.head raw ∧
            u.center.head.focus ≠ none := by rw [hC2, hC1]; exact hcen
        rcases ih c2 u (k+1) hm2 hc2 hr2 hrep2 hidle2 hsr2 hM2 hi2 hfr2 hrad2 hbd2 hcen2
          with hA3 | hB4
        · obtain ⟨es3, c3, t3, hseg3, hst3, hlen3, hcnt3, hm3, hc3, hr3, hrep3, hidle3, hsr3, hM3,
            hi3, hpos3, hC3, hfr3, hrr3, hrem3⟩ := hA3
          refine Or.inl ⟨List.replicate (delay - 1) false ++ true :: es3, c3, t3,
            watchSegE_trans P q first delay hseg1 (watchSegE_trans P q first delay hseg2 hseg3),
            ?_, ?_, ?_, hm3, hc3, hr3, hrep3, hidle3, hsr3, hM3, ?_, ?_, ?_, hfr3, hrr3, ?_⟩
          · intro hlast
            have hcomp := stepsAll_trans hst1 (stepsAll_trans hst2 (hst3 hlast))
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
            rw [e]; exact hi3
          · rw [hpos3, hpos2, hrr1]; omega
          · rw [hC3, hC2, hC1]
          · rw [hrem3, hrem2, hrem1]
        · exact Or.inr (foundLanding2_prepend (watchSegE_trans P q first delay hseg1 hseg2)
            (stepsAll_trans hst1 hst2) (by omega) (by rw [hpos2, hrr1]; omega)
            (by rw [hC2, hC1]) (by rw [hrem2, hrem1]) hB4)
      · exact Or.inr (foundLanding2_prepend hseg1 hst1 rfl (by rw [hrr1]) hC1 hrem1 hB3)
    · exact Or.inr hB2

end Idle

/-! ## 7. The gap-1 cycle, general, without `WatchOk`/`hgood`/`StartOk` -/

theorem arrived_le_of_represents {p : PlaceHead} {raw : List (Fin 2)}
    (h : GalilScaffoldInputTrace.Represents p.head raw) : arrived p ≤ raw.length := by
  obtain ⟨xs, rs, qs, hh, hw⟩ := h
  unfold arrived
  rw [hh, hw]
  cases xs with
  | nil => simp [layout]
  | cons a xs => simp [layout]; omega

/-- **`replay_after_fallback_general'`.**  `replay_after_fallback_general` with
`WatchOk`, `hgood` and `StartOk` replaced by `StartShape` and the named
period-match hypothesis `ReplaySpan`.  Branch (ii) lands in `FoundLanding2` at
the span end `B = position t.right + r` — the right end of the palindrome the
replay confirms (the landing has `position t'.right = B` and the scan invariant
at radius `r` about the unchanged centre) — with the chain in the replay
invariant `PartS`. -/
theorem replay_after_fallback_general' (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (delay : ℕ) (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hshape : StartShape P) (hspan : ReplaySpan raw P)
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
    FoundLanding2 raw P q first delay (position t.right + r) c t 0 r := by
  have hB : position t.right + r < (encoded raw).length := by
    have h1 := hfr r hrep
    have h2 := arrived_le_of_represents hR.2.2.2.1.rightRep
    simp only [encoded, List.length_append, List.length_singleton, pairs_length]
    omega
  have hbd : Bnd (position t.right + r) t := by
    intro m hm'
    rw [ofNat_inj (hrep.symm.trans hm')]
  rcases replay_general_construct2 raw P hP hP' q first delay (position t.right + r) hex hd hsearch
      hpres hshape hspan hB r c t 0 hm hc (by rw [hrpl]; simp [hr0]) hrep hR.1
      (searchReady_of_restarted hR) hM hR.2.2.2.1 hfr hR.2.2.2.2.1 hbd ⟨hR.2.1, hR.2.2.1⟩
      with hA | hB2
  · obtain ⟨es, c', t', hseg, hst, hlen, hcnt, hm', hc', hr', hrep', hidle', hsr', hM', hi',
        hpos', hC', hfr', hrr', hrem'⟩ := hA
    exact Or.inl ⟨es, c', t', hseg, hst, hlen, hcnt, hpos', hC',
      GalilReplaySegment.inv_after_replay delay raw c' t' r hm' hc' hr' hidle' (by simpa using hi')
        hM' hsr' hrep' (GalilReplaySegment.shiftIdle_congr hrem' hsi)⟩
  · exact Or.inr hB2

/-! ## 8. No preparation mismatch inside a replay -/

/-- **The `PrepMatch` mismatch exit cannot fire inside a replay.**  Every
comparison forced while replaying matches (`replay_match_of_minv`), so a chain
started during the replay runs its copy/back phases through `ReplayChainSeg`
(whose only comparison constructor is `matchC`) until the replay ends; the
`read (left) ≠ read (right)` stop of `prep_segment_construct_or_fallback`
(stated at `replaying = false`) is only reachable after the landing. -/
theorem no_prep_mismatch_in_replay {raw : List (Fin 2)} {c : Control} {s : GalilVM} {k : ℕ}
    (hM : MInv raw c s) (hr : c.replaying = true) (hav : canRight s.right)
    (hi : ScanInvariant raw (position s.center) k s.left s.right) :
    ¬ read (left s.left) ≠ read (right s.right) :=
  fun hne => hne (replay_match_of_minv hM hr hav hi)

/-- The landing chain ticks under the invariant for as long as the right head
stays at the span end (the first post-replay background tick). -/
theorem foundLanding2_tick_false {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {delay B : ℕ} {c : Control} {s : GalilVM} {k d : ℕ}
    (hL : FoundLanding2 raw P q first delay B c s k d) (hB : B < (encoded raw).length) :
    ∃ (t : GalilVM) (z : ChainVM), PartS raw B t ∧ ChainTick false t.chain z ∧
      ChainPart raw (position t.center) B (position t.right) z := by
  obtain ⟨-, -, -, -, -, -, -, t, -, -, -, -, -, -, -, -, -, -, -, -, -, hp, hBt, -⟩ := hL
  obtain ⟨z, hz, hzp⟩ := part_tick_false hp hB (by omega)
  exact ⟨t, z, hp, hz, hzp⟩

#print axioms flat_block
#print axioms rewound_of_flat
#print axioms copy_of_ahead
#print axioms part_step
#print axioms part_matched
#print axioms part_tick_false
#print axioms part_tick_true
#print axioms part_start
#print axioms chain_countdown2
#print axioms chain_compare2
#print axioms chain_replay_finish2
#print axioms start_part
#print axioms idle_countdown2
#print axioms idle_compare2
#print axioms replay_general_construct2
#print axioms replay_after_fallback_general'
#print axioms no_prep_mismatch_in_replay
#print axioms foundLanding2_tick_false

end PalPeg.GalilReplayGeneral2
