import PalPeg.GalilThrottledRun

set_option autoImplicit false

namespace PalPeg.GalilTruncTick

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilTickArrive PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.GalilThrottledRun

/-- The chain birth reset commutes with truncation: `truncVM` only shortens the
three heads and the chain's verifier, and `afterBirth` only touches
`periodOnly` and `cycle`. -/
theorem truncVM_afterBirth (d : ℕ) (b : Bool) (s : GalilVM) :
    truncVM d (afterBirth b s) = afterBirth b (truncVM d s) := by
  cases b <;> rfl

theorem truncVM_chain (d : ℕ) (s : GalilVM) :
    (truncVM d s).chain = truncChain d s.chain := rfl

/-- Truncation keeps the chain idle or non-idle, so it does not change whether
a chain is born. -/
theorem chainBorn_truncChain (b : Bool) (d : ℕ) (x : ChainVM) :
    chainBorn b (truncChain d x) = chainBorn b x := by
  cases x <;> simp [chainBorn, truncChain, ChainVM.isIdle]

abbrev PH := GalilScaffoldInputHead.PlaceHead

/-! ## 1. Heads -/

theorem truncPH_left (d : ℕ) (p : PH) :
    GalilScaffoldInputHead.left (truncPH d p) = truncPH d (GalilScaffoldInputHead.left p) := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g <;> cases ls <;> rfl

theorem usedPH_left (n : ℕ) (p : PH) :
    usedPH n (GalilScaffoldInputHead.left p) = usedPH n p := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g <;> cases ls <;> rfl

theorem usedPH_right_mono (n : ℕ) (p : PH) :
    usedPH n p ≤ usedPH n (GalilScaffoldChainVerifier.right p) := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g
  · exact le_rfl
  · cases rs with
    | cons a rs => exact le_rfl
    | nil =>
      cases q with
      | nil => exact le_rfl
      | cons a q =>
        simp only [usedPH, GalilScaffoldChainVerifier.right, if_true,
          GalilScaffoldChainVerifier.headRight, GalilScaffoldInputTrace.moveRight, List.length_cons]
        omega

/-- Two right moves consume at most one letter (gaps alternate). -/
theorem usedPH_right_right_le (n : ℕ) (p : PH) :
    usedPH n (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right p)) ≤ usedPH n p + 1 := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g
  · simp only [GalilScaffoldChainVerifier.right, Bool.false_eq_true, if_false, Bool.not_false, if_true]
    cases rs with
    | cons a rs => simp [usedPH, GalilScaffoldChainVerifier.headRight, GalilScaffoldInputTrace.moveRight]
    | nil =>
      cases q with
      | nil => simp [usedPH, GalilScaffoldChainVerifier.headRight, GalilScaffoldInputTrace.moveRight]
      | cons a q =>
        simp only [usedPH, GalilScaffoldChainVerifier.headRight, GalilScaffoldInputTrace.moveRight,
          List.length_cons]
        omega
  · simp only [GalilScaffoldChainVerifier.right, if_true, Bool.not_true, Bool.false_eq_true, if_false]
    cases rs with
    | cons a rs => simp [usedPH, GalilScaffoldChainVerifier.headRight, GalilScaffoldInputTrace.moveRight]
    | nil =>
      cases q with
      | nil => simp [usedPH, GalilScaffoldChainVerifier.headRight, GalilScaffoldInputTrace.moveRight]
      | cons a q =>
        simp only [usedPH, GalilScaffoldChainVerifier.headRight, GalilScaffoldInputTrace.moveRight,
          List.length_cons]
        omega

theorem truncPH_right (n j : ℕ) (p : PH)
    (h : usedPH n (GalilScaffoldChainVerifier.right p) ≤ j) :
    GalilScaffoldChainVerifier.right (truncPH (n - j) p) =
      truncPH (n - j) (GalilScaffoldChainVerifier.right p) := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g
  · rfl
  · cases rs with
    | cons a rs => rfl
    | nil =>
      cases q with
      | nil => simp [truncPH, dropN, GalilScaffoldChainVerifier.right,
          GalilScaffoldChainVerifier.headRight, GalilScaffoldInputTrace.moveRight]
      | cons a q =>
        simp only [usedPH, GalilScaffoldChainVerifier.right, if_true,
          GalilScaffoldChainVerifier.headRight, GalilScaffoldInputTrace.moveRight] at h
        have hq : n - j ≤ q.length := by omega
        have e : q.length + 1 - (n - j) = (q.length - (n - j)) + 1 := by omega
        simp only [truncPH, dropN, GalilScaffoldChainVerifier.right, if_true,
          GalilScaffoldChainVerifier.headRight, GalilScaffoldInputTrace.moveRight, List.length_cons, e,
          List.take_succ_cons]

theorem canRight_truncPH (n j : ℕ) (p : PH) (hc : GalilScaffoldChainVerifier.canRight p)
    (h : usedPH n (GalilScaffoldChainVerifier.right p) ≤ j) :
    GalilScaffoldChainVerifier.canRight (truncPH (n - j) p) := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g
  · exact Or.inl rfl
  · cases rs with
    | cons a rs => exact Or.inr (Or.inl (by simp [truncPH]))
    | nil =>
      cases q with
      | nil => simp [GalilScaffoldChainVerifier.canRight] at hc
      | cons a q =>
        simp only [usedPH, GalilScaffoldChainVerifier.right, if_true,
          GalilScaffoldChainVerifier.headRight, GalilScaffoldInputTrace.moveRight] at h
        have e : q.length + 1 - (n - j) = (q.length - (n - j)) + 1 := by omega
        refine Or.inr (Or.inr ?_)
        simp [truncPH, dropN, e]

theorem read_truncPH (d : ℕ) (p : PH) :
    GalilScaffoldInputHead.read (truncPH d p) = GalilScaffoldInputHead.read p := rfl

theorem sufPH_left {raw : List (Fin 2)} {p : PH} (h : SufPH raw p) :
    SufPH raw (GalilScaffoldInputHead.left p) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g <;> cases ls <;> exact hc

theorem sufPH_right {raw : List (Fin 2)} {p : PH} (h : SufPH raw p) :
    SufPH raw (GalilScaffoldChainVerifier.right p) := by
  obtain ⟨c, hc⟩ := h
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  simp only at hc
  cases g
  · exact ⟨c, hc⟩
  · cases rs with
    | cons a rs => exact ⟨c, hc⟩
    | nil =>
      cases q with
      | nil => exact ⟨c, hc⟩
      | cons a q =>
        refine ⟨c+1, ?_⟩
        show q = raw.drop (c+1)
        rw [← List.drop_drop, ← hc]; rfl

/-! ## 2. The chain -/

abbrev VS := GalilScaffoldChainVerifier.State
abbrev WS := GalilScaffoldChainWatch.State

/-- Letters the chain verifier would have consumed after two more moves
(a chain tick moves the verifier at most twice: `Internal` then `Outer`). -/
def lookChain (n : ℕ) (x : ChainVM) : ℕ :=
  match verOf x with
  | none => 0
  | some p => usedPH n (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right p))

def SufChain (raw : List (Fin 2)) (x : ChainVM) : Prop := ∀ p, verOf x = some p → SufPH raw p

theorem consume_trunc (n j : ℕ) (m : VS)
    (h : usedPH n (GalilScaffoldChainVerifier.right m.verifier) ≤ j) :
    GalilScaffoldChainVerifier.consume ⟨truncPH (n - j) m.verifier, m.control⟩ =
      ⟨truncPH (n - j) (GalilScaffoldChainVerifier.consume m).verifier,
        (GalilScaffoldChainVerifier.consume m).control⟩ := by
  simp only [GalilScaffoldChainVerifier.consume, truncPH_right n j _ h]
  rfl

theorem caught_trunc (n j : ℕ) (w : WS)
    (h : usedPH n (GalilScaffoldChainVerifier.right w.machine.verifier) ≤ j) :
    GalilScaffoldChainWatch.caught (truncW (n - j) w) = truncW (n - j) (GalilScaffoldChainWatch.caught w) := by
  simp only [GalilScaffoldChainWatch.caught, truncW]
  rw [consume_trunc n j w.machine h]

theorem immediate_trunc (n j : ℕ) (w : WS)
    (h : usedPH n (GalilScaffoldChainVerifier.right w.machine.verifier) ≤ j) :
    GalilScaffoldChainWatch.immediate (truncW (n - j) w) = truncW (n - j) (GalilScaffoldChainWatch.immediate w) := by
  simp only [GalilScaffoldChainWatch.immediate, truncW]
  rw [consume_trunc n j w.machine h]

theorem good_trunc (n j : ℕ) {w : WS} (hg : GalilScaffoldChainWatch.Good w)
    (h : usedPH n (GalilScaffoldChainVerifier.right w.machine.verifier) ≤ j) :
    GalilScaffoldChainWatch.Good (truncW (n - j) w) := by
  obtain ⟨hc, b, hs, hr⟩ := hg
  refine ⟨canRight_truncPH n j _ hc h, b, hs, ?_⟩
  show GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right (truncPH (n - j) w.machine.verifier)) = some b
  rw [truncPH_right n j _ h, read_truncPH]; exact hr

theorem internal_trunc (n j : ℕ) {w w' : WS} (hi : GalilScaffoldChainWatch.Internal w w')
    (h : usedPH n w'.machine.verifier ≤ j) :
    GalilScaffoldChainWatch.Internal (truncW (n - j) w) (truncW (n - j) w') := by
  cases hi with
  | idle hz => exact .idle _ hz
  | take hp hg =>
    rw [← caught_trunc n j w h]
    exact .take _ hp (good_trunc n j hg h)

theorem outer_trunc (n j : ℕ) {w w' : WS} {b : Bool} (ho : GalilScaffoldChainWatch.Outer w b w')
    (h : usedPH n w'.machine.verifier ≤ j) :
    GalilScaffoldChainWatch.Outer (truncW (n - j) w) b (truncW (n - j) w') := by
  cases ho with
  | idle => exact .idle _
  | queued hz => exact .queued _ hz
  | immediate hz hg =>
    rw [← immediate_trunc n j w h]
    exact .immediate _ hz (good_trunc n j hg h)

theorem breakStep_trunc (n j : ℕ) {w w' : WS} (hb : BreakStep w w')
    (h : usedPH n w'.machine.verifier ≤ j) : BreakStep (truncW (n - j) w) (truncW (n - j) w') := by
  obtain ⟨hz, hc, b, hs, hr, ht⟩ := hb
  subst ht
  refine ⟨hz, canRight_truncPH n j _ hc h, b, hs, ?_, ?_⟩
  · show GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right (truncPH (n - j) w.machine.verifier)) ≠ some b
    rw [truncPH_right n j _ h, read_truncPH]; exact hr
  · show truncW (n - j) ⟨_, _, _⟩ = ⟨GalilScaffoldChainVerifier.consume ⟨truncPH (n - j) w.machine.verifier, w.machine.control⟩, _, _⟩
    rw [consume_trunc n j w.machine h]
    rfl

/-- **`BreakStepPos` も truncation を通る。** `breakStep_trunc` と同じ証明
（lag は正、margin は据え置き）。 -/
theorem breakStepPos_trunc (n j : ℕ) {w w' : WS} (hb : BreakStepPos w w')
    (h : usedPH n w'.machine.verifier ≤ j) :
    BreakStepPos (truncW (n - j) w) (truncW (n - j) w') := by
  obtain ⟨hz, hc, b, hs, hr, ht⟩ := hb
  subst ht
  refine ⟨hz, canRight_truncPH n j _ hc h, b, hs, ?_, ?_⟩
  · show GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right (truncPH (n - j) w.machine.verifier)) ≠ some b
    rw [truncPH_right n j _ h, read_truncPH]; exact hr
  · show truncW (n - j) ⟨_, _, _⟩ = ⟨GalilScaffoldChainVerifier.consume ⟨truncPH (n - j) w.machine.verifier, w.machine.control⟩, _, _⟩
    rw [consume_trunc n j w.machine h]
    rfl

/-- The verifier of the target of a step is the source verifier or one move right. -/
theorem verOf_step {x y : ChainVM} (hs : ChainStep x y) (p : PH) (hp : verOf y = some p) :
    ∃ p0, verOf x = some p0 ∧ (p = p0 ∨ p = GalilScaffoldChainVerifier.right p0) := by
  cases hs with
  | idle => cases hp
  | brokenIdle => exact ⟨p, hp, Or.inl rfl⟩
  | copyBit => cases hp; exact ⟨_, rfl, Or.inl rfl⟩
  | copyEnd => cases hp; exact ⟨_, rfl, Or.inl rfl⟩
  | backStep => cases hp; exact ⟨_, rfl, Or.inl rfl⟩
  | backDone => cases hp; exact ⟨_, rfl, Or.inl rfl⟩
  | watchStep w w' ht =>
    cases hp
    cases ht with
    | idle => exact ⟨_, rfl, Or.inl rfl⟩
    | take => exact ⟨_, rfl, Or.inr rfl⟩
  | watchBreak w w' hb =>
    obtain ⟨-, -, -, -, -, heq⟩ := hb
    subst heq
    cases hp
    exact ⟨_, rfl, Or.inr rfl⟩

theorem verOf_matched {x y : ChainVM} (hm : ChainMatched x y) (p : PH) (hp : verOf y = some p) :
    ∃ p0, verOf x = some p0 ∧ (p = p0 ∨ p = GalilScaffoldChainVerifier.right p0) := by
  cases hm with
  | idle => cases hp
  | copy => cases hp; exact ⟨_, rfl, Or.inl rfl⟩
  | back => cases hp; exact ⟨_, rfl, Or.inl rfl⟩
  | watch w w' ho =>
    cases hp
    cases ho with
    | queued => exact ⟨_, rfl, Or.inl rfl⟩
    | immediate => exact ⟨_, rfl, Or.inr rfl⟩
  | breaks w w' hb =>
    cases hp
    obtain ⟨-, -, -, -, -, ht⟩ := hb
    subst ht
    exact ⟨_, rfl, Or.inr rfl⟩
  | brokenMatched w => cases hp; exact ⟨_, rfl, Or.inl rfl⟩

theorem used_of_eq_or_right (n : ℕ) {p q : PH} (h : p = q ∨ p = GalilScaffoldChainVerifier.right q) :
    usedPH n q ≤ usedPH n p ∧ usedPH n p ≤ usedPH n (GalilScaffoldChainVerifier.right q) := by
  rcases h with h | h <;> subst h
  · exact ⟨le_rfl, usedPH_right_mono n _⟩
  · exact ⟨usedPH_right_mono n _, le_rfl⟩

theorem chainStep_used (n : ℕ) {x y : ChainVM} (hs : ChainStep x y) : usedChain n y ≥ usedChain n x := by
  cases hvy : verOf y with
  | none =>
    cases hs <;> simp_all [verOf, usedChain]
  | some p =>
    obtain ⟨p0, h0, he⟩ := verOf_step hs p hvy
    simp only [usedChain, hvy, h0]
    exact (used_of_eq_or_right n he).1

theorem chainMatched_used (n : ℕ) {x y : ChainVM} (hm : ChainMatched x y) :
    usedChain n x ≤ usedChain n y := by
  cases hvy : verOf y with
  | none =>
    cases hm <;> simp_all [verOf, usedChain]
  | some p =>
    obtain ⟨p0, h0, he⟩ := verOf_matched hm p hvy
    simp only [usedChain, hvy, h0]
    exact (used_of_eq_or_right n he).1

theorem chainStep_trunc (n j : ℕ) {x y : ChainVM} (hs : ChainStep x y) (h : usedChain n y ≤ j) :
    ChainStep (truncChain (n - j) x) (truncChain (n - j) y) := by
  cases hs with
  | idle => exact .idle
  | brokenIdle w => exact .brokenIdle _
  | copyBit t hh p v lag margin ver b one legal present =>
    exact .copyBit t hh p v lag margin _ b one legal present
  | copyEnd t hh p v lag margin ver b hl hp hv => exact .copyEnd t hh p v lag margin _ b hl hp hv
  | backStep v hh lag margin ver hf => exact .backStep v hh lag margin _ hf
  | backDone v hh lag margin ver hf => exact .backDone v hh lag margin _ hf
  | watchStep w w' ht => exact .watchStep _ _ (internal_trunc n j ht h)
  | watchBreak w w' hb => exact .watchBreak _ _ (breakStepPos_trunc n j hb h)

theorem chainMatched_trunc (n j : ℕ) {x y : ChainVM} (hm : ChainMatched x y) (h : usedChain n y ≤ j) :
    ChainMatched (truncChain (n - j) x) (truncChain (n - j) y) := by
  cases hm with
  | idle => exact .idle
  | copy t hh p v lag margin ver => exact .copy t hh p v lag margin _
  | back v hh lag margin ver => exact .back v hh lag margin _
  | watch w w' ho => exact .watch _ _ (outer_trunc n j ho h)
  | breaks w w' hb => exact .breaks _ _ (breakStep_trunc n j hb h)
  | brokenMatched w => exact .brokenMatched _

theorem chainTick_trunc (n j : ℕ) {b : Bool} {x z : ChainVM} (ht : ChainTick b x z) (h : usedChain n z ≤ j) :
    ChainTick b (truncChain (n - j) x) (truncChain (n - j) z) := by
  obtain ⟨y, hs, hm⟩ := ht
  refine ⟨truncChain (n - j) y, ?_, ?_⟩
  · cases b
    · simp only [Bool.false_eq_true, if_false] at hm
      subst hm
      exact chainStep_trunc n j hs h
    · simp only [if_true] at hm
      exact chainStep_trunc n j hs (le_trans (chainMatched_used n hm) h)
  · cases b
    · simp only [Bool.false_eq_true, if_false] at hm ⊢; rw [hm]
    · simp only [if_true] at hm ⊢; exact chainMatched_trunc n j hm h

/-- A chain tick consumes at most the two-move lookahead. -/
theorem chainTick_used (n : ℕ) {b : Bool} {x z : ChainVM} (ht : ChainTick b x z) :
    usedChain n z ≤ lookChain n x := by
  obtain ⟨y, hs, hm⟩ := ht
  cases hvz : verOf z with
  | none => simp [usedChain, hvz]
  | some r =>
    simp only [usedChain, hvz]
    cases b
    · simp only [Bool.false_eq_true, if_false] at hm; subst hm
      obtain ⟨p, hp, he⟩ := verOf_step hs r hvz
      simp only [lookChain, hp]
      exact le_trans (used_of_eq_or_right n he).2 (usedPH_right_mono n _)
    · simp only [if_true] at hm
      obtain ⟨q, hq, he1⟩ := verOf_matched hm r hvz
      obtain ⟨p, hp, he2⟩ := verOf_step hs q hq
      simp only [lookChain, hp]
      rcases he1 with h1 | h1 <;> rcases he2 with h2 | h2 <;> subst h1 <;> subst h2
      · exact le_trans (usedPH_right_mono n _) (usedPH_right_mono n _)
      · exact usedPH_right_mono n _
      · exact usedPH_right_mono n _
      · exact le_rfl

theorem sufChain_step {raw : List (Fin 2)} {x y : ChainVM} (hs : ChainStep x y) (h : SufChain raw x) :
    SufChain raw y := by
  intro p hp
  obtain ⟨p0, h0, he⟩ := verOf_step hs p hp
  rcases he with he | he <;> subst he
  · exact h _ h0
  · exact sufPH_right (h _ h0)

theorem sufChain_matched {raw : List (Fin 2)} {x y : ChainVM} (hm : ChainMatched x y) (h : SufChain raw x) :
    SufChain raw y := by
  intro p hp
  obtain ⟨p0, h0, he⟩ := verOf_matched hm p hp
  rcases he with he | he <;> subst he
  · exact h _ h0
  · exact sufPH_right (h _ h0)

theorem sufChain_tick {raw : List (Fin 2)} {b : Bool} {x z : ChainVM} (ht : ChainTick b x z)
    (h : SufChain raw x) : SufChain raw z := by
  obtain ⟨y, hs, hm⟩ := ht
  have hy := sufChain_step hs h
  cases b
  · simp only [Bool.false_eq_true, if_false] at hm; subst hm; exact hy
  · simp only [if_true] at hm; exact sufChain_matched hm hy


/-! ## 3. The VM -/

section VM
variable (raw : List (Fin 2)) (j : ℕ)

theorem usedVM_left (s : GalilVM) : usedPH raw.length s.left ≤ usedVM raw s := by
  unfold usedVM; omega
theorem usedVM_center (s : GalilVM) : usedPH raw.length s.center ≤ usedVM raw s := by
  unfold usedVM; omega
theorem usedVM_right (s : GalilVM) : usedPH raw.length s.right ≤ usedVM raw s := by
  unfold usedVM; omega
theorem usedVM_chain (s : GalilVM) : usedChain raw.length s.chain ≤ usedVM raw s := by
  unfold usedVM; omega

/-- The lookahead of a scan-mode state: R one move right, the chain verifier two. -/
def look (x : State GalilVM) : ℕ :=
  if x.ctl.mode = .scan then
    max (usedPH raw.length (GalilScaffoldChainVerifier.right x.vm.right)) (lookChain raw.length x.vm.chain)
  else 0

theorem look_scan {x : State GalilVM} (hm : x.ctl.mode = .scan) :
    usedPH raw.length (GalilScaffoldChainVerifier.right x.vm.right) ≤ look raw x ∧
      lookChain raw.length x.vm.chain ≤ look raw x := by
  unfold look; rw [if_pos hm]; omega

structure SharedTrunc (P : Shared) : Prop where
  onLetter : ∀ s, P.onLetter (truncVM (raw.length - j) s) ↔ P.onLetter s
  leftFirst : ∀ s, P.leftFirst (truncVM (raw.length - j) s) ↔ P.leftFirst s
  init : ∀ s t, usedVM raw t ≤ j → P.init s t →
    P.init (truncVM (raw.length - j) s) (truncVM (raw.length - j) t)
  replayStart : ∀ s t, P.replayStart s t →
    P.replayStart (truncVM (raw.length - j) s) (truncVM (raw.length - j) t)
  replayPos : ∀ s, P.replayPos (truncVM (raw.length - j) s) = P.replayPos s
  replayExhausted : ∀ s, P.replayExhausted (truncVM (raw.length - j) s) = P.replayExhausted s
  shiftGuard : ∀ s, P.shiftGuard (truncVM (raw.length - j) s) ↔ P.shiftGuard s
  beginShift : ∀ s t, usedVM raw t ≤ j → P.beginShift s t →
    P.beginShift (truncVM (raw.length - j) s) (truncVM (raw.length - j) t)
  beginFallback : ∀ s t, P.beginFallback s t →
    P.beginFallback (truncVM (raw.length - j) s) (truncVM (raw.length - j) t)
  restart : ∀ s t, P.restart s t → P.restart (truncVM (raw.length - j) s) (truncVM (raw.length - j) t)
  centre : ∀ s, P.centre (truncVM (raw.length - j) s) = P.centre s
  place : ∀ s, P.place (truncVM (raw.length - j) s) = P.place s

theorem truncChain_idle_iff (d : ℕ) (x : ChainVM) : truncChain d x = .idle ↔ x = .idle := by
  cases x <;> simp [truncChain]

theorem truncChain_watch_iff (d : ℕ) (x : ChainVM) (w : WS) :
    truncChain d x = .watch w ↔ ∃ v, x = .watch v ∧ w = truncW d v := by
  cases x <;> simp [truncChain, eq_comm]

theorem sharedC_trunc (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (hon : ∀ s, onLetter (truncVM (raw.length - j) s) ↔ onLetter s)
    (hlf : ∀ s, leftFirst (truncVM (raw.length - j) s) ↔ leftFirst s)
    (hce : ∀ s, centre (truncVM (raw.length - j) s) = centre s)
    (hpl : ∀ s, place (truncVM (raw.length - j) s) = place s) :
    SharedTrunc raw j (sharedC onLetter leftFirst centre place entry) where
  onLetter := hon
  leftFirst := hlf
  init := by
    intro s t hu h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
    have hr : GalilScaffoldChainVerifier.right (truncPH (raw.length - j) s.right)
        = truncPH (raw.length - j) (GalilScaffoldChainVerifier.right s.right) :=
      truncPH_right raw.length j s.right (by rw [← h1]; exact usedVM_right raw t |>.trans hu)
    refine ⟨?_, ?_, ?_, h4, h5, h6, h7, h8, h9, ?_, h11, h12, h13⟩
    · show truncPH _ t.right = GalilScaffoldChainVerifier.right (truncPH _ s.right); rw [hr, h1]
    · show truncPH _ t.left = GalilScaffoldChainVerifier.right (truncPH _ s.right); rw [hr, h2]
    · show truncPH _ t.center = GalilScaffoldChainVerifier.right (truncPH _ s.right); rw [hr, h3]
    · show truncChain _ t.chain = .idle
      rw [h10]; rfl
  replayStart := by
    intro s t h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
    refine ⟨h1, ?_, ?_, ?_, h5, h6, h7, h8, h9, ?_, h11, h12, h13⟩
    · show truncPH _ _ = truncPH _ _; rw [h2]
    · show truncPH _ _ = truncPH _ _; rw [h3]
    · show truncPH _ _ = truncPH _ _; rw [h4]
    · show truncChain _ t.chain = .idle
      rw [h10]; rfl
  replayPos := fun _ => rfl
  replayExhausted := fun _ => rfl
  shiftGuard := by
    intro s
    show shiftGuardVM (truncVM (raw.length - j) s) ↔ shiftGuardVM s
    constructor
    · rintro ⟨w, hw, h1, h2, h3, h4, h5⟩
      obtain ⟨v, hv, rfl⟩ := (truncChain_watch_iff _ s.chain w).mp hw
      exact ⟨v, hv, h1, h2, h3, h4, h5⟩
    · rintro ⟨w, hw, h1, h2, h3, h4, h5⟩
      exact ⟨truncW (raw.length - j) w, by show truncChain _ s.chain = _; rw [hw]; rfl,
        h1, h2, h3, h4, h5⟩
  beginShift := by
    rintro s t hu ⟨w, hw, ht⟩
    refine ⟨truncW (raw.length - j) w, by show truncChain _ s.chain = _; rw [hw]; rfl, ?_⟩
    subst ht
    have hc := le_trans (usedVM_chain raw _) hu
    have hu' : usedPH raw.length (GalilScaffoldChainVerifier.right w.machine.verifier) ≤ j := hc
    show truncVM _ _ = _
    rw [immediate_trunc raw.length j w hu']
    rfl
  beginFallback := by
    rintro s t ⟨p, ht⟩
    exact ⟨p, by rw [ht]; rfl⟩
  restart := by
    rintro s t ⟨w, hw, h1, h2, h3, ht⟩
    exact ⟨truncW (raw.length - j) w, by show truncChain _ s.chain = _; rw [hw]; rfl, h1, h2, h3,
      by subst ht; rfl⟩
  centre := hce
  place := hpl


/-! ## 4. Frame relations under truncation -/

theorem searchEffect_trunc {P : Shared} (hP : SharedTrunc raw j P) (b : Bool) (s : GalilVM) (vq : SearchVM) :
    searchEffect P b (truncVM (raw.length - j) s) vq ↔ searchEffect P b s vq := by
  show ((truncChain _ s.chain = .idle ∧
      searchStep (P.place (truncVM (raw.length - j) s)) b (searchLens.get s) vq) ∨
      (truncChain _ s.chain ≠ .idle ∧ vq = searchLens.get s)) ↔ _
  rw [hP.place s]
  unfold searchEffect
  simp only [ne_eq, truncChain_idle_iff]

theorem chainAt_used {b found : Bool} {ans : GalilScaffoldTape.Tape} {c : Fin 3}
    {w : GalilScaffoldPlace.Place} {ver : PH} {r : GalilScaffoldCounter.Counter}
    {x z : ChainVM} (h : chainAt b found ans c w ver r x z) :
    usedChain raw.length z ≤ max (usedPH raw.length ver) (lookChain raw.length x) := by
  rcases h with ⟨_, ht⟩ | ⟨_, _, hz⟩ | ⟨_, _, hz⟩
  · exact le_trans (chainTick_used raw.length ht) (le_max_right _ _)
  · subst hz; exact Nat.zero_le _
  · cases b
    · simp only [Bool.false_eq_true, if_false] at hz; subst hz
      exact le_max_left _ _
    · simp only [if_true] at hz
      cases hz
      exact le_max_left _ _

theorem chainAt_trunc {b found : Bool} {ans : GalilScaffoldTape.Tape} {c : Fin 3}
    {w : GalilScaffoldPlace.Place} {ver : PH} {r : GalilScaffoldCounter.Counter}
    {x z : ChainVM} (h : chainAt b found ans c w ver r x z) (hz : usedChain raw.length z ≤ j) :
    chainAt b found ans c w (truncPH (raw.length - j) ver) r
      (truncChain (raw.length - j) x) (truncChain (raw.length - j) z) := by
  rcases h with ⟨hx, ht⟩ | ⟨hx, hf, hz'⟩ | ⟨hx, hf, hz'⟩
  · exact Or.inl ⟨fun e => hx ((truncChain_idle_iff _ x).mp e), chainTick_trunc raw.length j ht hz⟩
  · subst hx; subst hz'; exact Or.inr (Or.inl ⟨rfl, hf, rfl⟩)
  · subst hx
    refine Or.inr (Or.inr ⟨rfl, hf, ?_⟩)
    cases b
    · simp only [Bool.false_eq_true, if_false] at hz' ⊢; rw [hz']; rfl
    · simp only [if_true] at hz' ⊢
      exact chainMatched_trunc raw.length j hz' hz

theorem compareFound_trunc {P : Shared} (hP : SharedTrunc raw j P) (q : ℕ) (first : Fin 9)
    {s t : GalilVM} (hu : usedVM raw s ≤ j)
    (hr : usedPH raw.length (GalilScaffoldChainVerifier.right s.right) ≤ j)
    (hc : lookChain raw.length s.chain ≤ j) (h : compareFound P q first s t) :
    compareFound P q first (truncVM (raw.length - j) s) (truncVM (raw.length - j) t) := by
  obtain ⟨vs, vq, b, hl, hr', hb, hse, hch, ht⟩ := h
  have hz : usedChain raw.length vs.chain ≤ j :=
    le_trans (chainAt_used raw hch) (max_le (le_trans (usedVM_center raw s) hu) hc)
  refine ⟨⟨truncPH (raw.length - j) vs.left, truncPH (raw.length - j) vs.right,
    truncChain (raw.length - j) vs.chain⟩, vq, b, ?_, ?_, hb, (searchEffect_trunc raw j hP b s vq).mpr hse, ?_, ?_⟩
  · show truncPH _ vs.left = GalilScaffoldInputHead.left (truncPH _ s.left)
    rw [truncPH_left, hl]
  · show truncPH _ vs.right = GalilScaffoldChainVerifier.right (truncPH _ s.right)
    rw [truncPH_right raw.length j _ hr, hr']
  · rw [hP.centre, hP.place]
    exact chainAt_trunc raw j hch hz
  · subst ht
    rw [truncVM_afterBirth, truncVM_chain, chainBorn_truncChain]
    cases b <;> rfl

theorem backgroundS_trunc {P : Shared} (hP : SharedTrunc raw j P) (q : ℕ) (first : Fin 9)
    {s t : GalilVM} (hu : usedVM raw s ≤ j) (hc : lookChain raw.length s.chain ≤ j)
    (h : backgroundS P q first s t) :
    backgroundS P q first (truncVM (raw.length - j) s) (truncVM (raw.length - j) t) := by
  obtain ⟨hl, hr, hse, hch, hset⟩ := h
  have hz : usedChain raw.length t.chain ≤ j :=
    le_trans (chainAt_used raw hch) (max_le (le_trans (usedVM_center raw s) hu) hc)
  refine ⟨?_, ?_, (searchEffect_trunc raw j hP false s _).mpr hse, ?_, ?_⟩
  · show truncPH _ t.left = truncPH _ s.left
    rw [hl]
  · show truncPH _ t.right = truncPH _ s.right
    rw [hr]
  · rw [hP.centre, hP.place]
    exact chainAt_trunc raw j hch hz
  · rw [truncVM_chain, chainBorn_truncChain]
    calc truncVM (raw.length - j) t
        = truncVM (raw.length - j) (afterBirth (chainBorn (decide ((searchLens.get t).search.mode
              = GalilScaffoldSearchFinish.Mode.found)) s.chain)
            (searchLens.set (scanLens.set s (scanLens.get t)) (searchLens.get t))) :=
          congrArg _ hset
      _ = _ := by rw [truncVM_afterBirth]; rfl

theorem refresh_trunc {P : Shared} (hP : SharedTrunc raw j P) (q : ℕ) (first : Fin 9)
    {s : GalilVM} {old o : Bool} (h : refresh (galilFrameS P q first) s old o) :
    refresh (galilFrameS P q first) (truncVM (raw.length - j) s) old o := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · have := h1 ((hP.onLetter s).mp hl)
    exact this.trans (hP.leftFirst s).symm
  · exact h2 (fun hl' => hl ((hP.onLetter s).mpr hl'))

theorem matchedPlace_trunc (P : Shared) (q : ℕ) (first : Fin 9) (d : ℕ) (b : Bool)
    {s t : GalilVM} (h : (galilFrameS P q first).matchedPlace b s t) :
    (galilFrameS P q first).matchedPlace b (truncVM d s) (truncVM d t) := by
  have h' : t = (if b then {s with replay := GalilScaffoldCounter.dec s.replay} else s) := h
  show truncVM d t = (if b then {truncVM d s with replay := GalilScaffoldCounter.dec s.replay} else truncVM d s)
  subst h'
  cases b <;> rfl

theorem rel_trunc {σ' : Type} (L : Lens GalilVM σ') (tr : σ' → σ') (R : σ' → σ' → Prop) (d : ℕ)
    (hget : ∀ s, L.get (truncVM d s) = tr (L.get s))
    (hset : ∀ s v, L.set (truncVM d s) (tr v) = truncVM d (L.set s v))
    {s t : GalilVM} (h : L.rel R s t) (hR : R (L.get s) (L.get t) → R (tr (L.get s)) (tr (L.get t))) :
    L.rel R (truncVM d s) (truncVM d t) := by
  refine ⟨?_, ?_⟩
  · rw [hget, hget]; exact hR h.1
  · rw [hget, hset]; exact congrArg _ h.2

theorem fpp_rel_trunc (R : FppControl.State → FppControl.State → Prop) (d : ℕ) {s t : GalilVM}
    (h : fppLens.rel R s t) : fppLens.rel R (truncVM d s) (truncVM d t) :=
  rel_trunc fppLens id R d (fun _ => rfl) (fun _ _ => rfl) h id

def truncRewind (d : ℕ) (v : RewindVM) : RewindVM :=
  ⟨v.fpp, truncPH d v.left, truncPH d v.center, truncPH d v.right, v.length, v.radius⟩

theorem rewind_rel_trunc (d : ℕ) (R : RewindVM → RewindVM → Prop)
    (hR : ∀ u v, R u v → R (truncRewind d u) (truncRewind d v)) {s t : GalilVM}
    (h : rewindLens.rel R s t) : rewindLens.rel R (truncVM d s) (truncVM d t) :=
  rel_trunc rewindLens (truncRewind d) R d (fun _ => rfl) (fun _ _ => rfl) h (hR _ _)

theorem shiftOne_trunc (on lf : ShiftVM → Prop) {s t : GalilVM} (hu : usedVM raw t ≤ j)
    (h : shiftLens.rel (shiftFrame on lf).shiftOne s t) :
    shiftLens.rel (shiftFrame on lf).shiftOne (truncVM (raw.length - j) s) (truncVM (raw.length - j) t) := by
  obtain ⟨⟨hc, hl, hl', w, hw, hv⟩, h2⟩ := h
  have ht := h2.trans (congrArg _ hv)
  clear h2 hv
  subst ht
  have hcen := le_trans (usedVM_center raw _) hu
  have hlef := le_trans (usedVM_left raw _) hu
  have hcen' : usedPH raw.length (GalilScaffoldChainVerifier.right s.center) ≤ j := hcen
  have hlef2 : usedPH raw.length (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right s.left)) ≤ j := hlef
  have hlef1 : usedPH raw.length (GalilScaffoldChainVerifier.right s.left) ≤ j :=
    le_trans (usedPH_right_mono _ _) hlef2
  refine ⟨⟨canRight_truncPH raw.length j _ hc hcen', canRight_truncPH raw.length j _ hl hlef1, ?_,
    truncW (raw.length - j) w, ?_, ?_⟩, rfl⟩
  · show GalilScaffoldChainVerifier.canRight (GalilScaffoldChainVerifier.right (truncPH _ s.left))
    rw [truncPH_right raw.length j _ hlef1]
    exact canRight_truncPH raw.length j _ hl' hlef2
  · show truncChain _ s.chain = _
    rw [show s.chain = .watch w from hw]; rfl
  · show (⟨⟨truncPH _ (GalilScaffoldChainVerifier.right s.center),
        truncPH _ (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right s.left)), _, _, _⟩, _, _⟩ : ShiftVM) =
      ⟨⟨GalilScaffoldChainVerifier.right (truncPH _ s.center),
        GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right (truncPH _ s.left)), _, _, _⟩, _, _⟩
    rw [truncPH_right raw.length j _ hcen', truncPH_right raw.length j _ hlef1,
      truncPH_right raw.length j _ hlef2]
    rfl


theorem canRight_of_trunc (d : ℕ) (p : PH)
    (h : GalilScaffoldChainVerifier.canRight (truncPH d p)) : GalilScaffoldChainVerifier.canRight p := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ?_)
    intro hq
    apply h
    simp only at hq
    subst hq
    simp [truncPH, dropN]

/-! ## 5. **The truncated tick** -/

/-- **`tick_trunc`.** A pre-loaded tick whose endpoints consumed at most `j`
letters and whose source lookahead (`look`: in scan mode, R one move right and
the chain verifier two moves right) is at most `j` is also a tick with only `j`
letters arrived. -/
theorem tick_trunc {P : Shared} (hP : SharedTrunc raw j P) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {x y : State GalilVM} (h : Tick (galilFrameS P q first) delay x y)
    (hx : usedVM raw x.vm ≤ j) (hy : usedVM raw y.vm ≤ j) (hl : look raw x ≤ j) :
    Tick (galilFrameS P q first) delay (truncS (raw.length - j) x) (truncS (raw.length - j) y) := by
  cases h with
  | init c s s' hm h0 =>
    exact .init c _ _ hm (hP.init s s' hy h0)
  | scan_wait c s s' hm h0 hb =>
    obtain ⟨-, hc⟩ := look_scan raw (x := ⟨c, s⟩) hm
    refine .scan_wait c _ _ hm ⟨h0.1, fun hav => h0.2 (canRight_of_trunc _ _ hav)⟩
      (backgroundS_trunc raw j hP q first (s := s) hx (le_trans hc hl) hb)
  | scan_count c s s' hm h0 hc hb =>
    obtain ⟨hr, hch⟩ := look_scan raw (x := ⟨c, s⟩) hm
    refine .scan_count c _ _ hm ?_ hc (backgroundS_trunc raw j hP q first (s := s) hx (le_trans hch hl) hb)
    exact h0.imp id (fun hav => canRight_truncPH raw.length j _ hav (le_trans hr hl))
  | scan_match c s s' s'' o hm h0 hc hcmp hmt hpl ho =>
    obtain ⟨hr, hch⟩ := look_scan raw (x := ⟨c, s⟩) hm
    have ht := Tick.scan_match (F := galilFrameS P q first) (delay := delay) c (truncVM (raw.length - j) s)
      (truncVM (raw.length - j) s') (truncVM (raw.length - j) s'') o hm
      (h0.imp id (fun hav => canRight_truncPH raw.length j _ hav (le_trans hr hl))) hc
      (compareFound_trunc raw j hP q first hx (le_trans hr hl) (le_trans hch hl) hcmp) hmt
      (matchedPlace_trunc P q first _ c.replaying hpl) (refresh_trunc raw j hP q first ho)
    have he : (galilFrameS P q first).replayExhausted (truncVM (raw.length - j) s'') =
        (galilFrameS P q first).replayExhausted s'' := hP.replayExhausted s''
    rw [he] at ht
    exact ht
  | scan_shift c s s' s'' hm h0 hc hcmp hmt hr hg hb =>
    obtain ⟨hrr, hch⟩ := look_scan raw (x := ⟨c, s⟩) hm
    exact .scan_shift c _ (truncVM (raw.length - j) s') _ hm
      (h0.imp id (fun hav => canRight_truncPH raw.length j _ hav (le_trans hrr hl))) hc
      (compareFound_trunc raw j hP q first hx (le_trans hrr hl) (le_trans hch hl) hcmp) hmt hr
      ((hP.shiftGuard s').mpr hg) (hP.beginShift s' s'' hy hb)
  | scan_fallback c s s' s'' hm h0 hc hcmp hmt hg hr hb =>
    obtain ⟨hrr, hch⟩ := look_scan raw (x := ⟨c, s⟩) hm
    exact .scan_fallback c _ (truncVM (raw.length - j) s') _ hm
      (h0.imp id (fun hav => canRight_truncPH raw.length j _ hav (le_trans hrr hl))) hc
      (compareFound_trunc raw j hP q first hx (le_trans hrr hl) (le_trans hch hl) hcmp) hmt
      (hg.imp id (fun hn hs => hn ((hP.shiftGuard s').mp hs))) hr (hP.beginFallback s' s'' hb)
  | shift_one c s s' hm hp h0 =>
    exact .shift_one c _ _ hm hp (shiftOne_trunc raw j _ _ hy h0)
  | shift_done c s o hm hp ho =>
    exact .shift_done c _ o hm hp (refresh_trunc raw j hP q first ho)
  | copy_one c s s' hm hp h0 =>
    exact .copy_one c _ _ hm hp (fpp_rel_trunc _ _ h0)
  | copy_done c s s' hm hp h0 =>
    exact .copy_done c _ _ hm hp (fpp_rel_trunc _ _ h0)
  | home_start c s s' hm hl' h0 =>
    exact .home_start c _ _ hm hl' (fpp_rel_trunc _ _ h0)
  | home_step c s s' hm hl' h0 =>
    exact .home_step c _ _ hm hl' (fpp_rel_trunc _ _ h0)
  | fpp_slice c s s' hm h0 =>
    exact .fpp_slice c _ _ hm (fpp_rel_trunc _ _ h0)
  | fpp_done c s s' hm h0 =>
    exact .fpp_done c _ _ hm (fpp_rel_trunc _ _ h0)
  | markEnd_found c s s' hm he h0 =>
    refine .markEnd_found c _ _ hm he (rewind_rel_trunc _ _ ?_ h0)
    rintro u v ⟨h1, h2⟩
    exact ⟨h1, by subst h2; rfl⟩
  | markEnd_step c s s' hm he h0 =>
    exact .markEnd_step c _ _ hm he (fpp_rel_trunc _ _ h0)
  | choose_select c s s' hm ho hs h0 =>
    refine .choose_select c _ _ hm ho hs (rewind_rel_trunc _ _ ?_ h0)
    rintro u v h2
    subst h2; rfl
  | choose_step c s s' hm hs h0 =>
    refine .choose_step c _ _ hm hs (rewind_rel_trunc _ _ ?_ h0)
    rintro u v ⟨h1, h2⟩
    exact ⟨h1, by subst h2; rfl⟩
  | rewind_done c s s' hm hf h0 =>
    refine .rewind_done c _ _ hm hf (rewind_rel_trunc _ _ ?_ h0)
    rintro u v h2
    subst h2; rfl
  | rewind_one c s s' hm hf hp h0 =>
    refine .rewind_one c _ _ hm hf hp (rewind_rel_trunc _ _ ?_ h0)
    rintro u v ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    subst h2
    simp only [truncRewind, truncPH_left]
  | rewind_pair c s s' hm hf hp h0 =>
    refine .rewind_pair c _ _ hm hf hp (rewind_rel_trunc _ _ ?_ h0)
    rintro u v ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    subst h2
    simp only [truncRewind, truncPH_left]
  | replayStart c s s' o hm h0 ho ho' =>
    have hx' : (galilFrameS P q first).replayPos (truncVM (raw.length - j) s') =
        (galilFrameS P q first).replayPos s' := hP.replayPos s'
    have ht := Tick.replayStart (F := galilFrameS P q first) (delay := delay) c (truncVM (raw.length - j) s)
      (truncVM (raw.length - j) s') o hm (hP.replayStart s s' h0) (fun e => ho (hx' ▸ e))
      (fun e => refresh_trunc raw j hP q first (ho' (hx' ▸ e)))
    rw [hx'] at ht
    exact ht
  | restart c s s' hm hb =>
    exact .restart c _ _ hm (hP.restart s s' hb)


/-! ## 6. Every FIFO stays a suffix of the pre-loaded word -/

structure SharedSuf (P : Shared) : Prop where
  init : ∀ s t, SufVM raw s → P.init s t → SufVM raw t
  replayStart : ∀ s t, SufVM raw s → P.replayStart s t → SufVM raw t
  beginShift : ∀ s t, SufVM raw s → P.beginShift s t → SufVM raw t
  beginFallback : ∀ s t, SufVM raw s → P.beginFallback s t → SufVM raw t
  restart : ∀ s t, SufVM raw s → P.restart s t → SufVM raw t

theorem sufVM_congr {s t : GalilVM} (h : SufVM raw s) (hl : t.left = s.left) (hc : t.center = s.center)
    (hr : t.right = s.right) (hch : t.chain = s.chain) : SufVM raw t := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨hl ▸ h1, hc ▸ h2, hr ▸ h3, hch ▸ h4⟩

theorem sufChain_idle : SufChain raw .idle := fun p hp => by cases hp

theorem sharedC_suf (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) :
    SharedSuf raw (sharedC onLetter leftFirst centre place entry) where
  init := by
    intro s t hs h
    obtain ⟨h1, h2, h3, -, -, -, -, -, -, h10, -⟩ := h
    have hr := sufPH_right hs.2.2.1
    refine ⟨h2 ▸ hr, h3 ▸ hr, h1 ▸ hr, ?_⟩
    show SufChain raw t.chain
    rw [h10]; exact sufChain_idle raw
  replayStart := by
    intro s t hs h
    obtain ⟨-, h2, h3, h4, -, -, -, -, -, h10, -⟩ := h
    refine ⟨h3 ▸ hs.2.1, h4 ▸ hs.2.1, h2 ▸ hs.2.1, ?_⟩
    show SufChain raw t.chain
    rw [h10]; exact sufChain_idle raw
  beginShift := by
    rintro s t hs ⟨w, hw, ht⟩
    subst ht
    refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_⟩
    intro p hp
    cases hp
    exact sufPH_right (hs.2.2.2 _ (by show verOf s.chain = _; rw [hw]; rfl))
  beginFallback := by
    rintro s t hs ⟨p, ht⟩
    subst ht
    exact ⟨hs.1, hs.2.1, hs.2.2.1, sufChain_idle raw⟩
  restart := by
    rintro s t hs ⟨w, -, -, -, -, ht⟩
    subst ht
    exact ⟨hs.1, hs.2.1, hs.2.2.1, sufChain_idle raw⟩

theorem sufChain_at {b found : Bool} {ans : GalilScaffoldTape.Tape} {c : Fin 3}
    {w : GalilScaffoldPlace.Place} {ver : PH} {r : GalilScaffoldCounter.Counter}
    {x z : ChainVM} (h : chainAt b found ans c w ver r x z) (hv : SufPH raw ver) (hx : SufChain raw x) :
    SufChain raw z := by
  rcases h with ⟨_, ht⟩ | ⟨_, _, hz⟩ | ⟨_, _, hz⟩
  · exact sufChain_tick ht hx
  · subst hz; exact sufChain_idle raw
  · have hs : SufChain raw (chainStart ans c w ver r) := fun p hp => by cases hp; exact hv
    cases b
    · simp only [Bool.false_eq_true, if_false] at hz; subst hz; exact hs
    · simp only [if_true] at hz; exact sufChain_matched hz hs

theorem compareFound_suf {P : Shared} {q : ℕ} {first : Fin 9} {s t : GalilVM}
    (hs : SufVM raw s) (h : compareFound P q first s t) : SufVM raw t := by
  obtain ⟨vs, vq, b, hl, hr, -, -, hch, ht⟩ := h
  have hch' := sufChain_at raw hch hs.2.1 hs.2.2.2
  subst ht
  have hl' : SufPH raw vs.left := by rw [hl]; exact sufPH_left hs.1
  have hr' : SufPH raw vs.right := by rw [hr]; exact sufPH_right hs.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [afterBirth_left]; cases b <;> exact hl'
  · rw [afterBirth_center]; cases b <;> exact hs.2.1
  · rw [afterBirth_right]; cases b <;> exact hr'
  · rw [afterBirth_chain]; cases b <;> exact hch'

theorem backgroundS_suf {P : Shared} (q : ℕ) (first : Fin 9) {s t : GalilVM}
    (hs : SufVM raw s) (h : backgroundS P q first s t) : SufVM raw t := by
  obtain ⟨hl, hr, hch, hc, -⟩ := backgroundS_fields P q first h
  exact ⟨hl ▸ hs.1, hc ▸ hs.2.1, hr ▸ hs.2.2.1, sufChain_at raw hch hs.2.1 hs.2.2.2⟩

theorem fpp_rel_suf (R : FppControl.State → FppControl.State → Prop) {s t : GalilVM}
    (hs : SufVM raw s) (h : fppLens.rel R s t) : SufVM raw t := by
  have h3 := h.2
  have e1 := congrArg GalilVM.left h3
  have e2 := congrArg GalilVM.center h3
  have e3 := congrArg GalilVM.right h3
  have e4 := congrArg GalilVM.chain h3
  exact sufVM_congr raw hs e1 e2 e3 e4

theorem rewind_suf {s t : GalilVM} (hs : SufVM raw s) (h2 : t = rewindLens.set s (rewindLens.get t))
    (hl : SufPH raw (rewindLens.get t).left) (hc : SufPH raw (rewindLens.get t).center)
    (hr : SufPH raw (rewindLens.get t).right) : SufVM raw t := by
  refine ⟨hl, hc, hr, ?_⟩
  show SufChain raw t.chain
  rw [h2]; exact hs.2.2.2

/-- **(1) `sufVM_tick`.** -/
theorem sufVM_tick {P : Shared} (hP : SharedSuf raw P) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {x y : State GalilVM} (h : Tick (galilFrameS P q first) delay x y) (hs : SufVM raw x.vm) :
    SufVM raw y.vm := by
  cases h with
  | init c s s' hm h0 => exact hP.init s s' hs h0
  | scan_wait c s s' hm h0 hb => exact backgroundS_suf raw q first hs hb
  | scan_count c s s' hm h0 hc hb => exact backgroundS_suf raw q first hs hb
  | scan_match c s s' s'' o hm h0 hc hcmp hmt hpl ho =>
    have h1 := compareFound_suf raw hs hcmp
    have hpl' : s'' = (if c.replaying then {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    subst hpl'
    cases c.replaying <;> exact h1
  | scan_shift c s s' s'' hm h0 hc hcmp hmt hr hg hb =>
    exact hP.beginShift s' s'' (compareFound_suf raw hs hcmp) hb
  | scan_fallback c s s' s'' hm h0 hc hcmp hmt hg hr hb =>
    exact hP.beginFallback s' s'' (compareFound_suf raw hs hcmp) hb
  | shift_one c s s' hm hp h0 =>
    obtain ⟨⟨-, -, -, w, hw, hv⟩, h2⟩ := h0
    have ht := h2.trans (congrArg _ hv)
    clear h2 hv
    subst ht
    refine ⟨sufPH_right (sufPH_right hs.1), sufPH_right hs.2.1, hs.2.2.1, ?_⟩
    intro p hp
    cases hp
    exact hs.2.2.2 _ (by show verOf s.chain = _; rw [show s.chain = .watch w from hw]; rfl)
  | shift_done c s o hm hp ho => exact hs
  | copy_one c s s' hm hp h0 => exact fpp_rel_suf raw _ hs h0
  | copy_done c s s' hm hp h0 => exact fpp_rel_suf raw _ hs h0
  | home_start c s s' hm hl' h0 => exact fpp_rel_suf raw _ hs h0
  | home_step c s s' hm hl' h0 => exact fpp_rel_suf raw _ hs h0
  | fpp_slice c s s' hm h0 => exact fpp_rel_suf raw _ hs h0
  | fpp_done c s s' hm h0 => exact fpp_rel_suf raw _ hs h0
  | markEnd_step c s s' hm he h0 => exact fpp_rel_suf raw _ hs h0
  | markEnd_found c s s' hm he h0 =>
    obtain ⟨⟨-, h1⟩, h2⟩ := h0
    exact rewind_suf raw hs h2 (by rw [h1]; exact hs.1) (by rw [h1]; exact hs.2.1) (by rw [h1]; exact hs.2.2.1)
  | choose_step c s s' hm hs' h0 =>
    obtain ⟨⟨-, h1⟩, h2⟩ := h0
    exact rewind_suf raw hs h2 (by rw [h1]; exact hs.1) (by rw [h1]; exact hs.2.1) (by rw [h1]; exact hs.2.2.1)
  | choose_select c s s' hm ho hs' h0 =>
    obtain ⟨h1, h2⟩ := h0
    exact rewind_suf raw hs h2 (by rw [h1]; exact hs.2.2.1) (by rw [h1]; exact hs.2.2.1)
      (by rw [h1]; exact hs.2.2.1)
  | rewind_done c s s' hm hf h0 =>
    obtain ⟨h1, h2⟩ := h0
    exact rewind_suf raw hs h2 (by rw [h1]; exact hs.1) (by rw [h1]; exact hs.2.1) (by rw [h1]; exact hs.2.2.1)
  | rewind_one c s s' hm hf hp h0 =>
    obtain ⟨⟨-, h1⟩, h2⟩ := h0
    exact rewind_suf raw hs h2 (by rw [h1]; exact sufPH_left hs.1) (by rw [h1]; exact hs.2.1)
      (by rw [h1]; exact hs.2.2.1)
  | rewind_pair c s s' hm hf hp h0 =>
    obtain ⟨⟨-, h1⟩, h2⟩ := h0
    exact rewind_suf raw hs h2 (by rw [h1]; exact sufPH_left hs.1) (by rw [h1]; exact sufPH_left hs.2.1)
      (by rw [h1]; exact hs.2.2.1)
  | replayStart c s s' o hm h0 ho ho' => exact hP.replayStart s s' hs h0
  | restart c s s' hm hb => exact hP.restart s s' hs hb


end VM

/-! ## 7. The throttled run with the lookahead need -/

section Run
variable (raw : List (Fin 2)) (st : ℕ → State GalilVM) (e : ℕ)

/-- The need of the pre-loaded state `i`: its consumption and, in scan mode, the
one-move lookahead of R and the two-move lookahead of the chain verifier. -/
def needL (i : ℕ) : ℕ := max (needS raw st i) (look raw (st i))

/-- The need of the tick `k → k+1` (prefix maximum). -/
def needT (k : ℕ) : ℕ := pmax (needL raw st) (k+1)

theorem needS_le_needL (i : ℕ) : needS raw st i ≤ needL raw st i := le_max_left _ _

theorem needL_le_needT {i k : ℕ} (h : i ≤ k+1) : needL raw st i ≤ needT raw st k := le_pmax _ _ _ h

/-- Every FIFO stays a suffix along a trace of ticks. -/
theorem sufVM_trace {P : Shared} (hP : SharedSuf raw P) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (htick : ∀ k, k < e → Tick (galilFrameS P q first) delay (st k) (st (k+1)))
    (h0 : SufVM raw (st 0).vm) : ∀ k, k ≤ e → SufVM raw (st k).vm := by
  intro k
  induction k with
  | zero => intro _; exact h0
  | succ k ih => intro hk; exact sufVM_tick raw hP q first delay (htick k (by omega)) (ih (by omega))

abbrev cfgL (t : ℕ) : Cfg := cfg raw.length e (needT raw st) t

def stL (t : ℕ) : State GalilVM :=
  truncS (raw.length - (cfgL raw st e t).j) (st (cfgL raw st e t).k)

def arrL (t : ℕ) : ℕ := (cfgL raw st e t).j

/-- **`TruncTick` discharged, with the lookahead need.** A pre-loaded trace of
ticks, throttled by `needT`, is an `AbstractRun'`. -/
theorem abstractRun_throttledL (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hP : ∀ j, SharedTrunc raw j P) (hS : SharedSuf raw P)
    (hctl : (st 0).ctl = GalilScaffoldController.initial delay)
    (h0 : needL raw st 0 = 0) (hsuf0 : SufVM raw (st 0).vm)
    (htick : ∀ k, k < e → Tick (galilFrameS P q first) delay (st k) (st (k+1))) :
    AbstractRun' P q first delay raw (stL raw st e) (arrL raw st e) := by
  have hsuf := sufVM_trace raw st e hS q first delay htick hsuf0
  refine ⟨hctl, rfl, fun t => ?_⟩
  have hused := cfg_used raw.length e (needT raw st) (needL raw st) h0
    (fun k i hi => needL_le_needT raw st hi) t
  obtain ⟨-, hke, -, -⟩ := cfg_inv raw.length e (needT raw st) t
  rcases cfg_succ_cases raw.length e (needT raw st) t with ⟨h1, _, h3⟩ | ⟨_, h2, h3, h4⟩ | ⟨_, _, h3⟩
  · refine Or.inr ⟨by simp only [arrL, cfgL, h3], raw[(cfgL raw st e t).j], ?_, ?_⟩
    · exact List.getElem?_eq_getElem h1
    · simp only [stL, cfgL, h3]
      exact (arrive_trunc raw _ h1 _ (hsuf _ hke)
        (le_trans (needS_le_needL raw st _) (hused _ le_rfl))).symm
  · refine Or.inl ⟨by simp only [arrL, cfgL, h4], Or.inl ?_⟩
    simp only [stL, cfgL, h4]
    have hA : needL raw st (cfgL raw st e t).k ≤ (cfgL raw st e t).j := hused _ le_rfl
    have hB : needL raw st ((cfgL raw st e t).k + 1) ≤ (cfgL raw st e t).j :=
      le_trans (needL_le_needT raw st le_rfl) h3
    exact tick_trunc raw _ (hP _) q first delay (htick _ h2)
      (le_trans (needS_le_needL raw st _) hA) (le_trans (needS_le_needL raw st _) hB)
      (le_trans (le_max_right _ _) hA)
  · refine Or.inl ⟨by simp only [arrL, cfgL, h3], Or.inr ?_⟩
    simp only [stL, cfgL, h3]

open Classical in
noncomputable def TcL (Tc : ℕ → ℕ) (m : ℕ) : ℕ :=
  if h : ∃ t, Tc m ≤ (cfgL raw st e t).k then Nat.find h else 0

theorem TcL_spec (Tc : ℕ → ℕ) (m : ℕ) (h : ∃ t, Tc m ≤ (cfgL raw st e t).k) :
    Tc m ≤ (cfgL raw st e (TcL raw st e Tc m)).k ∧
      ∀ t, Tc m ≤ (cfgL raw st e t).k → TcL raw st e Tc m ≤ t := by
  unfold TcL
  rw [dif_pos h]
  exact ⟨Nat.find_spec h, fun t ht => Nat.find_min' h ht⟩

theorem TcL_exact (Tc : ℕ → ℕ) (m : ℕ) (h : ∃ t, Tc m ≤ (cfgL raw st e t).k) :
    (cfgL raw st e (TcL raw st e Tc m)).k = Tc m := by
  obtain ⟨h1, h2⟩ := TcL_spec raw st e Tc m h
  refine le_antisymm ?_ h1
  rcases hT : TcL raw st e Tc m with _ | t'
  · simp [cfgL, cfg]
  · have hlt : ¬ Tc m ≤ (cfgL raw st e t').k := fun hc => by
      have := h2 t' hc; omega
    have := (cfg_mono raw.length e (needT raw st) t').2.1
    simp only [cfgL] at hlt this ⊢
    omega

/-- Hypotheses on the pre-loaded trace for the lookahead need. -/
structure PreloadL (Tc : ℕ → ℕ) : Prop where
  tc0 : Tc 0 = 0
  mono : ∀ m, m < raw.length → Tc m ≤ Tc (m+1)
  need0 : needL raw st 0 = 0
  needLe : ∀ m, m < raw.length → ∀ k, k < Tc (m+1) → needT raw st k ≤ m+1

/-- **(4) reduction.** `needLe` follows from the pointwise bound on the states up to
the checkpoint. -/
theorem needLe_of_pointwise (Tc : ℕ → ℕ)
    (h : ∀ m, m < raw.length → ∀ i, i ≤ Tc (m+1) → needL raw st i ≤ m+1) :
    ∀ m, m < raw.length → ∀ k, k < Tc (m+1) → needT raw st k ≤ m+1 :=
  fun m hm k hk => pmax_le _ _ _ fun i hi => h m hm i (by omega)

theorem TcL_exists {Tc : ℕ → ℕ} (hp : PreloadL raw st Tc) :
    ∀ m, m ≤ raw.length → ∃ t, Tc m ≤ (cfg raw.length (Tc raw.length) (needT raw st) t).k := by
  intro m
  induction m with
  | zero => intro _; exact ⟨0, by rw [hp.tc0]; exact Nat.zero_le _⟩
  | succ m ih =>
    intro hm
    obtain ⟨hK, -⟩ := TcL_spec raw st (Tc raw.length) Tc m (ih (by omega))
    exact ⟨_, ostep raw.length _ (needT raw st) Tc m hm (hp.mono m hm)
      (GalilCheckpoints.mono_of_step Tc raw.length hp.mono (m+1) raw.length hm le_rfl)
      (hp.needLe m hm) _ hK⟩

theorem TcL_zero {Tc : ℕ → ℕ} (hp : PreloadL raw st Tc) : TcL raw st (Tc raw.length) Tc 0 = 0 := by
  have h := TcL_exists raw st hp 0 (Nat.zero_le _)
  have := (TcL_spec raw st _ Tc 0 h).2 0 (by rw [hp.tc0]; exact Nat.zero_le _)
  omega

theorem O_step_throttledL {Tc : ℕ → ℕ} (hp : PreloadL raw st Tc) (m : ℕ) (hm : m < raw.length) :
    TcL raw st (Tc raw.length) Tc (m+1) ≤
      max (TcL raw st (Tc raw.length) Tc m) ((m+1) * GalilLedgerAssembly.τ) + dwT Tc (m+1) := by
  obtain ⟨hK, -⟩ := TcL_spec raw st (Tc raw.length) Tc m (TcL_exists raw st hp m hm.le)
  have ho := ostep raw.length _ (needT raw st) Tc m hm (hp.mono m hm)
    (GalilCheckpoints.mono_of_step Tc raw.length hp.mono (m+1) raw.length hm le_rfl) (hp.needLe m hm) _ hK
  have := (TcL_spec raw st (Tc raw.length) Tc (m+1) (TcL_exists raw st hp (m+1) hm)).2 _ ho
  simpa [dwT] using this

theorem stL_at_end {Tc : ℕ → ℕ} (hp : PreloadL raw st Tc) (hn : 0 < raw.length)
    {P : Shared} {q : ℕ} {first : Fin 9}
    (hrep : GalilLedgerAssembly.ReportPointAt P q first raw raw.length (st (Tc raw.length))) :
    stL raw st (Tc raw.length) (TcL raw st (Tc raw.length) Tc raw.length) = st (Tc raw.length) := by
  have hex := TcL_exists raw st hp raw.length le_rfl
  have hk := TcL_exact raw st (Tc raw.length) Tc raw.length hex
  have hused := cfg_used raw.length (Tc raw.length) (needT raw st) (needL raw st) hp.need0
    (fun k i hi => needL_le_needT raw st hi) (TcL raw st (Tc raw.length) Tc raw.length)
    (Tc raw.length) (by simp only [cfgL] at hk; omega)
  have hu := used_of_report raw hn hrep
  have hS := needS_le_needL raw st (Tc raw.length)
  obtain ⟨i1, -, -, -⟩ := cfg_inv raw.length (Tc raw.length) (needT raw st)
    (TcL raw st (Tc raw.length) Tc raw.length)
  have hjn : (cfgL raw st (Tc raw.length) (TcL raw st (Tc raw.length) Tc raw.length)).j = raw.length := by
    simp only [cfgL, needS] at hused i1 hS ⊢
    omega
  unfold stL
  rw [hjn, hk, Nat.sub_self, truncS_zero]

/-- **Ledger obligation for the lookahead-throttled runs.** -/
theorem ledger_throttledL (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (stOf : List (Fin 2) → ℕ → State GalilVM)
    (TcOf : List (Fin 2) → ℕ → ℕ)
    (hpre : ∀ w : List (Fin 2), 0 < w.length → PreloadL w (stOf w) (TcOf w))
    (hrep : ∀ w : List (Fin 2), 0 < w.length →
      GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w w.length
        (stOf w (TcOf w w.length)))
    (O_cost : ∀ w : List (Fin 2), 0 < w.length → ∀ m, m < w.length →
      dwT (TcOf w) (m+1) ≤
        GalilLedgerQ64.alpha' 2048 * (Cw w (m+1) - Cw w m) + GalilLedgerQ64.beta' 2048) :
    LedgerObligation Pof qof firstOf
      (fun w => stL w (stOf w) (TcOf w w.length))
      (fun w => (w.length + 1) * GalilLedgerAssembly.τ) := by
  intro w hw hpal
  have hp := hpre w hw
  have hz := GalilLedgerAssembly.backlog_zero_trunc w hw hpal (dwT (TcOf w)) (O_cost w hw)
  have ht := GalilLedgerAssembly.on_time_trunc w (dwT (TcOf w))
    (TcL w (stOf w) (TcOf w w.length) (TcOf w)) (TcL_zero w (stOf w) hp)
    (O_step_throttledL w (stOf w) hp) hz
  obtain ⟨hrp, hfr⟩ := GalilLedgerAssembly.reportPoint_of_at_length hw (hrep w hw)
  refine ⟨TcL w (stOf w) (TcOf w w.length) (TcOf w) w.length, ht, ?_, ?_⟩
  · show ReportPoint w (stL w (stOf w) (TcOf w w.length) _)
    rw [stL_at_end w (stOf w) hp hw (hrep w hw)]; exact hrp
  · show Refreshed _ _ _ (stL w (stOf w) (TcOf w w.length) _)
    rw [stL_at_end w (stOf w) hp hw (hrep w hw)]; exact hfr

end Run

/-! ## 8. Tools for the pointwise need bound (4) -/

/-- The lookahead costs at most one letter. -/
theorem look_le_succ (raw : List (Fin 2)) (x : State GalilVM) : look raw x ≤ usedVM raw x.vm + 1 := by
  unfold look
  split_ifs
  · have h1 := usedPH_right_mono raw.length x.vm.right
    have h2 := usedPH_right_right_le raw.length x.vm.right
    have h3 := usedVM_right raw x.vm
    have h4 : lookChain raw.length x.vm.chain ≤ usedChain raw.length x.vm.chain + 1 := by
      unfold lookChain usedChain
      cases verOf x.vm.chain with
      | none => exact Nat.zero_le _
      | some p => exact usedPH_right_right_le raw.length p
    have h5 := usedVM_chain raw x.vm
    have h6 : usedPH raw.length (GalilScaffoldChainVerifier.right x.vm.right) ≤ usedPH raw.length x.vm.right + 1 :=
      le_trans (usedPH_right_mono _ _) h2
    omega
  · exact Nat.zero_le _

/-- A right move from a letter place (`gap = false`) pops nothing. -/
theorem usedPH_right_letter (n : ℕ) (p : PH) (hg : p.gap = false) :
    usedPH n (GalilScaffoldChainVerifier.right p) = usedPH n p := by
  rcases p with ⟨hd, g⟩
  simp only at hg
  subst hg
  rfl

/-- Under `Represents` of the whole pre-loaded word, consumption is the arrived
material (`GalilFrontier.arrived`). -/
theorem usedPH_eq_arrived (raw : List (Fin 2)) (p : PH)
    (hr : GalilScaffoldInputTrace.Represents p.head raw) : usedPH raw.length p = arrived p := by
  rcases p with ⟨hd, g⟩
  obtain ⟨xs, rs, q, hh, hw⟩ := hr
  simp only at hh
  subst hh
  have hlen : raw.length = xs.length + rs.length + q.length := by
    rw [hw]; simp only [List.length_append, List.length_reverse]
  cases xs <;> simp [usedPH, arrived, GalilScaffoldInputHead.layout, hlen]

theorem sharedC_trunc_vm (raw : List (Fin 2)) (j : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (hce : ∀ s, centre (truncVM (raw.length - j) s) = centre s)
    (hpl : ∀ s, place (truncVM (raw.length - j) s) = place s) :
    SharedTrunc raw j (sharedC (onLetterVM raw) leftFirstVM centre place entry) :=
  sharedC_trunc raw j _ _ centre place entry (onLetterVM_trunc raw _) (leftFirstVM_trunc _) hce hpl

#print axioms truncPH_right
#print axioms sharedC_trunc_vm
#print axioms chainTick_trunc
#print axioms chainTick_used
#print axioms sharedC_trunc
#print axioms compareFound_trunc
#print axioms tick_trunc
#print axioms sharedC_suf
#print axioms sufVM_tick
#print axioms sufVM_trace
#print axioms abstractRun_throttledL
#print axioms needLe_of_pointwise
#print axioms O_step_throttledL
#print axioms stL_at_end
#print axioms ledger_throttledL
#print axioms look_le_succ
#print axioms usedPH_eq_arrived

end PalPeg.GalilTruncTick
