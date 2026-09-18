import PalPeg.CloseoutPackRun47

/-!
# `CloseoutPackRun48`: `ConsumeAvail` is only ever needed where it is available

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun48

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun41 PalPeg.CloseoutPackRun44
open PalPeg.CloseoutPackRun47

/-! ## 1. `LagNonneg` is not automatic, but it is an invariant -/

/-- `value` is an *integer* difference of two stacks, and `dec` at an empty
positive stack produces a canonical counter of value `-1`.  So `LagNonneg` is
**not** derivable from `Canonical` alone. -/
theorem lagNonneg_not_of_canonical :
    ∃ c : Counter, Canonical c ∧ value c < 0 :=
  ⟨⟨[], [()]⟩, Or.inl rfl, by decide⟩

/-- **(NAMED) `LagCan`**: the watching chain's lag counter is canonical and
non-negative.  Unlike `LagPos` this is consistent with both
`Internal.take` (which needs `0 < lag`) and `Outer.immediate` (which needs
`lag = 0`). -/
def LagCan (z : ChainVM) : Prop :=
  ∀ wch : GalilScaffoldChainWatch.State, z = .watch wch →
    Canonical wch.lag ∧ 0 ≤ value wch.lag

theorem lagCan_lagNonneg {z : ChainVM} (h : LagCan z) : LagNonneg z :=
  fun wch hw => (h wch hw).2

theorem lagCan_idle : LagCan .idle := fun _ h => by cases h

theorem lagCan_broken (w : GalilScaffoldChainWatch.State) : LagCan (.broken w) :=
  fun _ h => by cases h

/-- `LagCan` is preserved by a background chain step. -/
theorem lagCan_step {x z : ChainVM} (hL : LagCan x)
    (hback : ∀ (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter) (ver : PlaceHead),
      x = .back v h lag margin ver → Canonical lag ∧ 0 ≤ value lag)
    (hst : ChainStep x z) : LagCan z := by
  cases hst with
  | idle => exact hL
  | brokenIdle w => exact lagCan_broken w
  | copyBit => exact fun _ h => by cases h
  | copyEnd => exact fun _ h => by cases h
  | backStep v h lag margin ver _ => exact fun _ hw => by cases hw
  | backDone v h lag margin ver _ =>
    intro wch hw; cases hw; exact hback v h lag margin ver rfl
  | watchStep w w' hi =>
    obtain ⟨hc, hn⟩ := hL w rfl
    cases hi with
    | idle _ => intro wch hw; cases hw; exact ⟨hc, hn⟩
    | take hp hg =>
      intro wch hw; cases hw
      have hv := (positive_iff w.lag hc).1 hp
      refine ⟨dec_canonical _ hc, ?_⟩
      show (0:ℤ) ≤ value (dec w.lag)
      rw [dec_value]; omega

/-- `LagCan` is preserved by a matched credit. -/
theorem lagCan_matched {y z : ChainVM} (hL : LagCan y) (hm : ChainMatched y z) : LagCan z := by
  cases hm with
  | idle => exact lagCan_idle
  | copy => exact fun _ h => by cases h
  | back => exact fun _ h => by cases h
  | breaks w w' hb => exact lagCan_broken w'
  | watch w w' ho =>
    obtain ⟨hc, hn⟩ := hL w rfl
    cases ho with
    | queued hz =>
      intro wch hw; cases hw
      refine ⟨inc_canonical _ hc, ?_⟩
      show (0:ℤ) ≤ value (inc w.lag)
      rw [inc_value]; omega
    | immediate hz hg =>
      intro wch hw; cases hw
      exact ⟨hc, hn⟩

#print axioms lagCan_step
#print axioms lagCan_matched


/-! ## 2. `ConsumeAvail` is needed only where the guard supplies it -/

/-- **A background chain step needs no supply beyond the scan front.**  The
*only* `ChainStep` that consumes is `Internal.take`, and its guard
`positive lag = true` means the verifier is strictly behind the right head; so
`CloseoutPackRun44.consumeAvail_of_supply` applies with the **source** state's
own supply `canRight R`.  No one-cell-ahead fact is used. -/
theorem chainPos_step_of_supply {w : List (Fin 2)} {x z : ChainVM} {R : PlaceHead}
    (hrepR : GalilScaffoldInputTrace.Represents R.head w) (hfocR : R.head.focus ≠ none)
    (hcR : canRight R)
    (hrepV : ∀ wch : GalilScaffoldChainWatch.State, x = .watch wch →
      GalilScaffoldInputTrace.Represents wch.machine.verifier.head w ∧
        wch.machine.verifier.head.focus ≠ none)
    (hL : LagCan x) (hP : ChainPositionLedger x (position R)) (hst : ChainStep x z) :
    ChainPositionLedger z (position R) := by
  cases hst with
  | idle => exact chainPos_step hP (fun _ h => by cases h) .idle
  | brokenIdle v => exact chainPos_broken v _
  | copyBit t h p v lag margin ver a h1 h2 h3 =>
    exact chainPos_step hP (fun _ hq => by cases hq) (.copyBit t h p v lag margin ver a h1 h2 h3)
  | copyEnd t h p v lag margin ver b h1 h2 h3 =>
    exact chainPos_step hP (fun _ hq => by cases hq) (.copyEnd t h p v lag margin ver b h1 h2 h3)
  | backStep v h lag margin ver hf =>
    exact chainPos_step hP (fun _ hq => by cases hq) (.backStep v h lag margin ver hf)
  | backDone v h lag margin ver hf =>
    exact chainPos_step hP (fun _ hq => by cases hq) (.backDone v h lag margin ver hf)
  | watchStep v v' hi =>
    cases hi with
    | idle hz => exact hP
    | take hp hg =>
      obtain ⟨hc, hn⟩ := hL v rfl
      have hlag : LagPos (ChainVM.watch v) := by
        intro wch hw; cases hw; exact (positive_iff v.lag hc).1 hp
      exact chainPos_step hP
        (consumeAvail_of_supply hrepR hfocR hcR hrepV hlag hP)
        (.watchStep v _ (.take v hp hg))

#print axioms chainPos_step_of_supply

/-- **A matched credit needs supply exactly one cell ahead — which the landing
has.**  The only consuming `ChainMatched` transition is `Outer.immediate`,
guarded by `zero lag`; there the verifier *is* at the scan front, so the moved
verifier lands on the landing's right head `R'`, whose `canRight` is the
target payload's `ScanPositionPayloadWithChainLedger.canR`. -/
theorem chainPos_matched_of_target {w : List (Fin 2)} {y z : ChainVM} {R R' : PlaceHead}
    (hrepR' : GalilScaffoldInputTrace.Represents R'.head w) (hfocR' : R'.head.focus ≠ none)
    (hcR' : canRight R') (hstep : position R' = position R + 1)
    (hrepV : ∀ wch : GalilScaffoldChainWatch.State, y = .watch wch →
      GalilScaffoldInputTrace.Represents wch.machine.verifier.head w ∧
        wch.machine.verifier.head.focus ≠ none)
    (hL : LagCan y) (hP : ChainPositionLedger y (position R)) (hm : ChainMatched y z) :
    ChainPositionLedger z (position R + 1) :=
  chainPos_matched hP
    (consumeAvail_of_next_supply hrepR' hfocR' hcR' hstep hrepV (lagCan_lagNonneg hL) hP) hm

#print axioms chainPos_matched_of_target


/-! ## 3. `H_BackgroundLandingChainLedger` with the supply leaf removed -/

section Bg
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`H_BackgroundLandingChainLedger` from the chain-start shape and the *source* supply only.**
`CloseoutPackRun44.h_bgP2_of_start` had to assume `ConsumeAvail s.chain`, whose
`lag = 0` instance is the one-cell-ahead fact no source state provides.  With
`chainPos_step_of_supply` that assumption disappears: the background landing
needs only the `lrep` pairs of the right head and the verifier, `LagCan`, and
`BgStartP2`. -/
theorem h_bgP2_of_supply {w : List (Fin 2)}
    (hrepR : ∀ (c : Control) (s : GalilVM), c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
      GalilScaffoldInputTrace.Represents s.right.head w ∧ s.right.head.focus ≠ none)
    (hrepV : ∀ (c : Control) (s : GalilVM), c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
      ∀ wch : GalilScaffoldChainWatch.State, s.chain = .watch wch →
        GalilScaffoldInputTrace.Represents wch.machine.verifier.head w ∧
          wch.machine.verifier.head.focus ≠ none)
    (hL : ∀ (c : Control) (s : GalilVM), c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
      LagCan s.chain)
    (hstart : BgStartP2 centre place entry q first w) :
    H_BackgroundLandingChainLedger centre place entry q first w := by
  intro c s t hm hx hb hs hni
  by_cases hi : s.chain = ChainVM.idle
  · exact hstart c s t hm hx hi hb hs hni
  · have P : ScanPositionPayloadWithChainLedger w s := hx.payload hs hi
    obtain ⟨hl, hr, -, hcen, -, hrad, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    have hstep : ChainStep s.chain t.chain := by
      obtain ⟨y, hst, hy⟩ :=
        backgroundS_chainTick (PofC centre place entry w) q first hb hi
      simp only [Bool.false_eq_true, reduceIte] at hy
      rw [hy]; exact hst
    obtain ⟨hrr, hfr⟩ := hrepR c s hm hx
    refine ⟨?_, ?_, ?_⟩
    · rw [hr]; exact P.canR
    · rw [hcen, hl, hr, hrad]; exact P.radLe
    · rw [hr]
      exact chainPos_step_of_supply hrr hfr P.canR (hrepV c s hm hx) (hL c s hm hx)
        P.chainPos hstep

end Bg

#print axioms h_bgP2_of_supply


/-! ## 4. `H_MatchLandingChainLedger` discharged at the target -/

section Match
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED residue of `H_MatchLandingChainLedger`.)**  Everything the `scan_match` landing
needs beyond `ChainPositionInvariantWithShiftPhase` at the source.  Note that the supply obligation is
stated at the **target**: `canRNext`/`repNext` are the moved right head's, i.e.
the target payload's own `ScanPositionPayloadWithChainLedger.canR` together with its `lrep` pair. -/
structure MatchRes2 (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  repR : GalilScaffoldInputTrace.Represents s.right.head w ∧ s.right.head.focus ≠ none
  repV : ∀ wch : GalilScaffoldChainWatch.State, s.chain = .watch wch →
    GalilScaffoldInputTrace.Represents wch.machine.verifier.head w ∧
      wch.machine.verifier.head.focus ≠ none
  repVmid : ∀ (y : ChainVM) (wch : GalilScaffoldChainWatch.State),
    ChainStep s.chain y → y = .watch wch →
      GalilScaffoldInputTrace.Represents wch.machine.verifier.head w ∧
        wch.machine.verifier.head.focus ≠ none
  lagCan : LagCan s.chain
  backLag : ∀ (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter) (ver : PlaceHead),
    s.chain = .back v h lag margin ver → Canonical lag ∧ 0 ≤ value lag
  replayPay : c.replaying = true → s.chain ≠ ChainVM.idle → ScanPositionPayloadWithChainLedger w s
  saneR : Sane s.right
  canR : canRight s.right
  repNext : GalilScaffoldInputTrace.Represents (right s.right).head w ∧
    (right s.right).head.focus ≠ none
  radNext : ∀ rad : ℕ,
    ScanInvariant w (position s.center) rad (GalilScaffoldInputHead.left s.left) (right s.right) →
      value s.radius + 1 ≤ (rad : ℤ)
  startLedger : s.chain = ChainVM.idle → CentreLedger s

def H_matchRes2 (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s s' t : GalilVM) (o b : Bool), c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    (galilFrameS (PofC centre place entry w) q first).matched s' →
    (galilFrameS (PofC centre place entry w) q first).matchedPlace c.replaying s' t →
    ScanNR ⟨{c with clock := 2048, output := o, replaying := c.replaying && b}, t⟩ →
    t.chain ≠ ChainVM.idle → MatchRes2 w c s

/-- **`scan_match` 着地の位置台帳、状態局所版。**  着地の消費側
（`Outer.immediate`、lag ゼロ）は**目標側**の供給 `canRNext` で、背景側
（`Internal.take`、正 lag）は源の `canR` で満たされる。だから `ConsumeAvail` は現れない。  もとの `h_matchP2_of_target` は
`hres : H_matchRes2 …`（global）を取っていたが、本体はそれを源状態 `(c, s)` でだけ
使うので、`MatchRes2 w c s` を直接取る形にした。global 版は下のラッパー。

trace 形の義務を放電するにはこの形が必要（global 形は放電の材料が run に沿ってしか
存在しないので原理的に満たせない）。 -/
theorem matchLanding_of_matchRes2 {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hres : MatchRes2 w c s) :
    ∀ (s' t : GalilVM) (o b : Bool), c.mode = Mode.scan →
      ChainPositionInvariantWithShiftPhase w c s →
      (galilFrameS (PofC centre place entry w) q first).compare s s' →
      (galilFrameS (PofC centre place entry w) q first).matched s' →
      (galilFrameS (PofC centre place entry w) q first).matchedPlace c.replaying s' t →
      ScanNR ⟨{c with clock := 2048, output := o, replaying := c.replaying && b}, t⟩ →
      t.chain ≠ ChainVM.idle → GalilScaffoldChainVerifier.canRight t.right →
      ScanPositionPayloadWithChainLedger w t := by
  intro s' t o b hm hx hcmp hmt hpl hs hni hCanRightAtTarget
  have R := hres
  have hpl' : t = (if c.replaying then {s' with replay := dec s'.replay} else s') := hpl
  have hts : t.left = s'.left ∧ t.right = s'.right ∧ t.chain = s'.chain ∧
      t.center = s'.center ∧ t.radius = s'.radius := by
    rw [hpl']
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨vs, vq, a, hvl, hvr, hiff, -, hch, hteq⟩ :
    compareFound (PofC centre place entry w) q first s s' := hcmp
  have ha : a = true := by
    cases a with
    | true => rfl
    | false =>
      rw [if_neg (by simp)] at hteq
      subst hteq
      refine absurd (hiff.2 ?_) (by simp)
      have h0 : GalilScaffoldInputHead.read (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)).left
        = GalilScaffoldInputHead.read (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)).right := hmt
      rw [afterBirth_left, afterBirth_right] at h0
      exact h0
  subst ha
  rw [if_pos rfl] at hteq
  subst hteq
  obtain ⟨htl, htr, htc, htcen, htrad⟩ := hts
  have hsl : (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).left = vs.left := afterBirth_left _ _
  have hsr : (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).right = vs.right := afterBirth_right _ _
  have hsc : (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).chain = vs.chain := afterBirth_chain _ _
  have hscen : (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).center = s.center := afterBirth_center _ _
  have hsrad : (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).radius = inc s.radius :=
    afterBirth_radius _ _
  rw [hsl, hvl] at htl
  rw [hsr, hvr] at htr
  rw [hsc] at htc
  rw [hscen] at htcen
  rw [hsrad] at htrad
  have hP : s.chain ≠ ChainVM.idle → ScanPositionPayloadWithChainLedger w s := by
    intro hne
    cases hrep : c.replaying with
    | false => exact hx.payload ⟨hm, hrep⟩ hne
    | true => exact R.replayPay hrep hne
  have hlv : 0 < s.right.head.left.length :=
    (PalPeg.CloseoutLPack3.present_iff_left R.repR.1).1 R.repR.2
  have hposR : position (right s.right) = position s.right + 1 :=
    right_position s.right R.canR hlv
  have hCanRightNext : canRight (right s.right) := by rw [← htr]; exact hCanRightAtTarget
  refine ⟨hCanRightAtTarget, ?_, ?_⟩
  · intro rad hsc'
    rw [htcen, htl, htr] at hsc'
    rw [htrad, inc_value]
    exact R.radNext rad hsc'
  · rw [htc, htr]
    rcases hch with ⟨hne, y, hst, hmy⟩ | ⟨-, -, hz⟩ | ⟨hidle, -, hz⟩
    · rw [if_pos rfl] at hmy
      have Ps := hP hne
      have hy : ChainPositionLedger y (position s.right) :=
        chainPos_step_of_supply R.repR.1 R.repR.2 Ps.canR R.repV R.lagCan Ps.chainPos hst
      have hLy : LagCan y := lagCan_step R.lagCan R.backLag hst
      have := chainPos_matched_of_target (R := s.right) (R' := right s.right)
        R.repNext.1 R.repNext.2 hCanRightNext hposR (fun wch hw => R.repVmid y wch hst hw) hLy hy hmy
      rw [hposR]
      exact this
    · rw [hz]; exact chainPos_idle _
    · rw [if_pos rfl] at hz
      obtain ⟨hc1, hc2, hc3⟩ := R.startLedger hidle
      have hstart : ∀ (ans : GalilScaffoldTape.Tape) (cc : Fin 3)
          (wk : GalilScaffoldPlace.Place),
          ChainPositionLedger (chainStart ans cc wk s.center s.radius) (position s.right) := by
        intro ans cc wk
        refine ⟨(fun _ hw => by cases hw), (fun _ _ _ _ _ hbk => by cases hbk),
          fun _ _ _ _ _ _ _ hcp => ?_⟩
        unfold chainStart at hcp
        injection hcp with _ _ _ _ h5 _ h7
        subst h5; subst h7
        exact ⟨hc1, hc2, hc3⟩
      rw [hposR]
      exact chainPos_matched (hstart _ _ _) (fun _ h => by cases h) hz

/-- **global 版**（旧 `h_matchP2_of_target` の型そのまま）。既存の呼び出し側のために残す。 -/
theorem h_matchP2_of_target {w : List (Fin 2)} (hres : H_matchRes2 centre place entry q first w) :
    H_MatchLandingChainLedger centre place entry q first w :=
  fun c s s' t o b hm hx hcmp hmt hpl hs hni hCanRightAtTarget =>
    matchLanding_of_matchRes2 centre place entry q first
      (hres c s s' t o b hm hx hcmp hmt hpl hs hni) s' t o b hm hx hcmp hmt hpl hs hni
      hCanRightAtTarget

end Match

#print axioms matchLanding_of_matchRes2
#print axioms h_matchP2_of_target


/-! ## 5. The `scan_shift` entry, by the same target-side route -/

/-- **One `immediate` consume raises the ledger by one.**  `beginShiftVM`
replaces the watch by `GalilScaffoldChainWatch.immediate w`, i.e. moves the
verifier one cell right and keeps the lag.  Exactly as at a matched landing,
the supply needed is `canRight` **one cell past** the source ledger point —
which at the `scan_shift` entry is the *moved* right head. -/
theorem chainPos_immediate {w : List (Fin 2)} {v : GalilScaffoldChainWatch.State}
    {R R' : PlaceHead}
    (hrepR' : GalilScaffoldInputTrace.Represents R'.head w) (hfocR' : R'.head.focus ≠ none)
    (hcR' : canRight R') (hstep : position R' = position R + 1)
    (hrepV : GalilScaffoldInputTrace.Represents v.machine.verifier.head w ∧
      v.machine.verifier.head.focus ≠ none)
    (hL : LagCan (ChainVM.watch v)) (hP : ChainPositionLedger (.watch v) (position R)) :
    ChainPositionLedger (.watch (GalilScaffoldChainWatch.immediate v)) (position R') := by
  obtain ⟨hcv, hsv, hpv⟩ := hP.watch v rfl
  have hav : ConsumeAvail (ChainVM.watch v) :=
    consumeAvail_of_next_supply hrepR' hfocR' hcR' hstep
      (fun wch hw => by cases hw; exact hrepV) (lagCan_lagNonneg hL) hP
  have hcn := hav v rfl
  have hr := right_sane hcv hsv
  refine ⟨fun wch hw => ?_, (fun _ _ _ _ _ hb => by cases hb),
    (fun _ _ _ _ _ _ _ hcp => by cases hcp)⟩
  cases hw
  refine ⟨hcn, hr.2, ?_⟩
  show (position (right v.machine.verifier) : ℤ) + value v.lag = position R'
  rw [hr.1, hstep]
  push_cast
  omega

#print axioms chainPos_immediate

section ShiftEntry
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- The residue of the `scan_shift` entry: the *same* `MatchRes2` pack, taken
at the source of a mismatching comparison. -/
def H_shiftRes2 (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s s' t : GalilVM), c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    ¬ (galilFrameS (PofC centre place entry w) q first).matched s' →
    shiftGuardVM s' → beginShiftVM' s' t → MatchRes2 w c s

/-- **`scan_shift` 入口の shift 相台帳、状態局所版。**  不一致比較が右ヘッドを動かして
素の `ChainStep` を 1 つ取り（源の供給）、`beginShiftVM` が `immediate` 消費を 1 回行う。
その供給は**動いた**右ヘッド `right s.right`（目標側の経路）。  入力は `matchLanding_of_matchRes2`
と**同じ `MatchRes2 w c s`**（`H_shiftRes2` の結論がそれ）。だから 2 つの義務は
`MatchRest` 1 つに合流する。 -/
theorem shiftEntryLanding_of_matchRes2 {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hres : MatchRes2 w c s) :
    ∀ s' t : GalilVM, c.mode = Mode.scan →
      ChainPositionInvariantWithShiftPhase w c s →
      (galilFrameS (PofC centre place entry w) q first).compare s s' →
      ¬ (galilFrameS (PofC centre place entry w) q first).matched s' →
      shiftGuardVM s' → beginShiftVM' s' t →
      GalilScaffoldChainVerifier.canRight t.right → ShiftPhaseChainLedger t := by
  intro s' t hm hx hcmp hmt hg hb hCanRightAtTarget
  have R := hres
  obtain ⟨vs, vq, a, hvl, hvr, hiff, -, hch, hteq⟩ :
    compareFound (PofC centre place entry w) q first s s' := hcmp
  have ha : a = false := by
    cases a with
    | false => rfl
    | true =>
      rw [if_pos rfl] at hteq
      subst hteq
      refine absurd ?_ hmt
      show GalilScaffoldInputHead.read (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).left
        = GalilScaffoldInputHead.read (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).right
      rw [afterBirth_left, afterBirth_right]
      exact hiff.1 rfl
  subst ha
  rw [if_neg (by simp)] at hteq
  subst hteq
  have hsr : (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)).right = vs.right := afterBirth_right _ _
  have hsc : (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)).chain = vs.chain := afterBirth_chain _ _
  have hPs : s.chain ≠ ChainVM.idle → ScanPositionPayloadWithChainLedger w s := by
    intro hne
    cases hrep : c.replaying with
    | false => exact hx.payload ⟨hm, hrep⟩ hne
    | true => exact R.replayPay hrep hne
  have hlv : 0 < s.right.head.left.length :=
    (PalPeg.CloseoutLPack3.present_iff_left R.repR.1).1 R.repR.2
  have hposR : position (right s.right) = position s.right + 1 :=
    right_position s.right R.canR hlv
  obtain ⟨v, hcw, hteq2⟩ := hb
  have hcw' : vs.chain = ChainVM.watch v := by
    rw [afterBirth_chain] at hcw; exact hcw
  -- the chain at a mismatching comparison is a plain `ChainStep`
  obtain ⟨y, hst, hy⟩ : ∃ y, ChainStep s.chain y ∧ vs.chain = y := by
    rcases hch with ⟨hne, y, hst, hmy⟩ | ⟨hi, -, hz⟩ | ⟨hi, -, hz⟩
    · simp only [Bool.false_eq_true, ↓reduceIte] at hmy
      exact ⟨y, hst, hmy⟩
    · rw [hz] at hcw'; exact absurd hcw' (by simp)
    · simp only [Bool.false_eq_true, ↓reduceIte] at hz
      rw [hz] at hcw'
      unfold chainStart at hcw'
      exact absurd hcw' (by simp)
  have hne : s.chain ≠ ChainVM.idle := by
    intro hi
    rcases hch with ⟨hne', -⟩ | ⟨-, -, hz⟩ | ⟨-, -, hz⟩
    · exact hne' hi
    · rw [hz] at hcw'; exact absurd hcw' (by simp)
    · simp only [Bool.false_eq_true, ↓reduceIte] at hz
      rw [hz] at hcw'
      unfold chainStart at hcw'
      exact absurd hcw' (by simp)
  have Ps := hPs hne
  have hyw : y = ChainVM.watch v := by rw [← hy]; exact hcw'
  have hPy : ChainPositionLedger (ChainVM.watch v) (position s.right) := by
    rw [← hyw]
    exact chainPos_step_of_supply R.repR.1 R.repR.2 R.canR R.repV R.lagCan Ps.chainPos hst
  have hLy : LagCan (ChainVM.watch v) := by
    rw [← hyw]; exact lagCan_step R.lagCan R.backLag hst
  show ChainPositionLedger t.chain (position t.right)
  have htc : t.chain = ChainVM.watch (GalilScaffoldChainWatch.immediate v) := by rw [hteq2]
  have htr : t.right = right s.right := by rw [hteq2]; rw [hsr, hvr]
  have hCanRightNext : canRight (right s.right) := by rw [← htr]; exact hCanRightAtTarget
  rw [htc, htr]
  exact chainPos_immediate R.repNext.1 R.repNext.2 hCanRightNext hposR
    (R.repVmid y v hst hyw) hLy hPy

/-- **(NAMED) `ShiftDoneSupply`.**  `H_ShiftExitRadiusLedger` has *no* chain content at
all: its conclusion is the scan-mode supply of the right head plus the radius
ledger at the `shift_done` exit.  So it is not a target-supply obligation but
two ordinary pack fields. -/
theorem h_shiftDoneRad2_of_supply {w : List (Fin 2)}
    (hav : ∀ (c : Control) (s : GalilVM), c.mode = Mode.shift →
      ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
      ChainPositionInvariantWithShiftPhase w c s → canRight s.right)
    (hrad : ∀ (c : Control) (s : GalilVM), c.mode = Mode.shift →
      ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
      ChainPositionInvariantWithShiftPhase w c s → ∀ rad : ℕ,
        ScanInvariant w (position s.center) rad s.left s.right → value s.radius ≤ (rad : ℤ)) :
    H_ShiftExitRadiusLedger centre place entry q first w :=
  fun c s hm hp hx _ => ⟨hav c s hm hp hx, hrad c s hm hp hx⟩

/-- **global 版**（旧 `h_shiftEntry2_of_target` の型そのまま）。 -/
theorem h_shiftEntry2_of_target {w : List (Fin 2)}
    (hres : H_shiftRes2 centre place entry q first w) :
    H_ShiftEntryChainLedger centre place entry q first w :=
  fun c s s' t hm hx hcmp hmt hg hb hCanRightAtTarget =>
    shiftEntryLanding_of_matchRes2 centre place entry q first
      (hres c s s' t hm hx hcmp hmt hg hb) s' t hm hx hcmp hmt hg hb hCanRightAtTarget

end ShiftEntry

#print axioms shiftEntryLanding_of_matchRes2
#print axioms h_shiftEntry2_of_target
#print axioms h_shiftDoneRad2_of_supply

end PalPeg.CloseoutPackRun48
