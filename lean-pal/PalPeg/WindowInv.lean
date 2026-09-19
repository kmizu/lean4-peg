import PalPeg.ShiftPalAlongTrace

/-!
# `WindowInv` — chain の一生を通して窓を運ぶ chain 側の不変量

`obligation_shiftPalResiduesAlongRun` の残差は不一致比較の直前の `WatchWindow`（誕生中心
`cen₀` に anchor した窓）を要求する。ここでは chain の一生（`chainStart` の `.copy` → `.back` →
`.watch`、途中で `.broken`）を通して運ぶ不変量 `WindowInv` と、chain 側の各遷移
（`ChainStep`／`ChainMatched`／誕生／shift 入口の `immediate`／`chainShiftOne`）での transport を
証明する。**DP の形の葉（`AnswerAhead`／`PlaceAhead`／`StartShape`）は要らない**: ブロックの中身
`b xs` は `copyEnd` で決まり、`backDone` で `coreX_born` が `CoreX`（→ `CoreP`）を作る。

run 層（`Tick` ごと）への持ち上げは次。

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false

namespace PalPeg.WindowInv

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilReplayGeneral2 PalPeg.GalilBranchInvariants PalPeg.ShiftPalAlongTrace

/-- chain の一生の不変量: 誕生中心 `cen₀`、その記号 `cc`、右ヘッド `R`。 -/
def WindowInv (raw : List (Fin 2)) (cen₀ R : ℕ) (cc : Fin 3) : ChainVM → Prop
  | ChainVM.idle => True
  | ChainVM.copy _ _ _ v lag _ ver =>
      VerAt raw cen₀ ver ∧ LagAt lag ver R ∧
      ∃ ys : List (Fin 3), v = GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cc) ys
  | ChainVM.back v _ lag _ ver =>
      VerAt raw cen₀ ver ∧ LagAt lag ver R ∧
      ∃ (b : Fin 3) (xs : List (Fin 3)), flat v = blockTokens cc b xs
  | ChainVM.watch w =>
      ∃ (b : Fin 3) (xs : List (Fin 3)), WatchWindow raw cen₀ R cc b xs (ChainVM.watch w)
  | ChainVM.broken _ => True

/-- **誕生。**  `chainStart answer cc walker ver radius` は `.copy` で、verifier は中心ヘッド、
lag は半径カウンタ（`lagAt_radius`）、period テープは `start cc = fill (start cc) []`。 -/
theorem windowInv_start {raw : List (Fin 2)} {cen₀ k : ℕ} {cc : Fin 3}
    (answer : GalilScaffoldTape.Tape) (walker : GalilScaffoldPlace.Place)
    {ver : PlaceHead} {radius : Counter}
    (hver : VerAt raw cen₀ ver) (hrad : RadiusRep radius k) :
    WindowInv raw cen₀ (cen₀ + k) cc (chainStart answer cc walker ver radius) := by
  refine ⟨hver, ?_, [], rfl⟩
  have h := lagAt_radius hrad ver
  rw [hver.2.2] at h
  exact h

#print axioms windowInv_start

/-- **background の chain 1 歩（`ChainStep`）。** -/
theorem windowInv_step {raw : List (Fin 2)} {cen₀ R : ℕ} {cc : Fin 3} {x y : ChainVM}
    (hx : WindowInv raw cen₀ R cc x) (h : ChainStep x y) : WindowInv raw cen₀ R cc y := by
  cases h with
  | idle => trivial
  | brokenIdle _ => trivial
  | copyBit t hh p v lag margin ver a one legal present =>
    obtain ⟨hver, hlag, ys, hv⟩ := hx
    refine ⟨hver, hlag, ys ++ [a], ?_⟩
    rw [hv, GalilScaffoldChainPeriod.fill_append]
    rfl
  | copyEnd t hh p v lag margin ver b hleft hp hv =>
    obtain ⟨hver, hlag, ys, hys⟩ := hx
    refine ⟨hver, hlag, ?_⟩
    rcases ys.eq_nil_or_concat with rfl | ⟨xs, a, rfl⟩
    · exfalso
      rw [hys] at hv
      simp [GalilScaffoldChainPeriod.fill, GalilScaffoldChainPeriod.start] at hv
    · rw [List.concat_eq_append] at hys
      have hfoc := fill_last_focus (GalilScaffoldChainPeriod.start cc) xs a
      rw [← hys, hv] at hfoc
      injection hfoc with hab
      subst hab
      exact ⟨_, xs, by rw [hys]; exact flat_block cc _ xs⟩
  | backStep v hh lag margin ver hf =>
    obtain ⟨hver, hlag, b, xs, hflat⟩ := hx
    exact ⟨hver, hlag, b, xs, by rw [flat_moveLeft]; exact hflat⟩
  | backDone v hh lag margin ver hf =>
    obtain ⟨hver, hlag, b, xs, hflat⟩ := hx
    have hv := rewound_of_flat hflat hf
    refine ⟨b, xs, hlag, ?_, ?_⟩
    · intro j hj
      exfalso
      rw [hver.2.2] at hj
      omega
    · rw [hv]
      exact coreP_of_coreX (PalPeg.GalilReplaySpan.coreX_born cc b xs ver hver.1 hver.2.1
        (by rw [hver.2.2]))
  | watchStep w w' hi =>
    obtain ⟨b, xs, hw⟩ := hx
    exact ⟨b, xs, watchWindow_step hw hi⟩
  | watchBreak _ _ => trivial

#print axioms windowInv_step

/-- **一致比較の chain 側（`ChainMatched`）: 右ヘッドが 1 つ進む。** -/
theorem windowInv_matched {raw : List (Fin 2)} {cen₀ R : ℕ} {cc : Fin 3} {x y : ChainVM}
    (hx : WindowInv raw cen₀ R cc x) (h : ChainMatched x y) :
    WindowInv raw cen₀ (R + 1) cc y := by
  cases h with
  | idle => trivial
  | copy t hh p v lag margin ver =>
    obtain ⟨hver, hlag, ys, hv⟩ := hx
    exact ⟨hver, lagAt_inc hlag, ys, hv⟩
  | back v hh lag margin ver =>
    obtain ⟨hver, hlag, b, xs, hflat⟩ := hx
    exact ⟨hver, lagAt_inc hlag, b, xs, hflat⟩
  | watch w w' ho =>
    obtain ⟨b, xs, hw⟩ := hx
    exact ⟨b, xs, watchWindow_outer hw ho⟩
  | breaks w w' hb => trivial
  | brokenMatched _ => trivial

#print axioms windowInv_matched

/-- **shift 入口の `immediate`**（`beginShiftVM`）: guard の lag ゼロと予測一致（`Good`）で
右ヘッドが 1 つ進む。 -/
theorem windowInv_immediate {raw : List (Fin 2)} {cen₀ R : ℕ} {cc : Fin 3}
    {w : GalilScaffoldChainWatch.State}
    (hx : WindowInv raw cen₀ R cc (ChainVM.watch w)) (hz : zero w.lag = true)
    (hg : GalilScaffoldChainWatch.Good w) :
    WindowInv raw cen₀ (R + 1) cc (ChainVM.watch (GalilScaffoldChainWatch.immediate w)) := by
  obtain ⟨b, xs, hw⟩ := hx
  exact ⟨b, xs, watchWindow_outer hw (GalilScaffoldChainWatch.Outer.immediate w hz hg)⟩

#print axioms windowInv_immediate

/-- **shift の 1 歩（`chainShiftOne`）は不変。** -/
theorem windowInv_shiftOne {raw : List (Fin 2)} {cen₀ R : ℕ} {cc : Fin 3}
    {w : GalilScaffoldChainWatch.State}
    (hx : WindowInv raw cen₀ R cc (ChainVM.watch w)) :
    WindowInv raw cen₀ R cc (ChainVM.watch (chainShiftOne w)) := by
  obtain ⟨b, xs, hw⟩ := hx
  exact ⟨b, xs, watchWindow_shiftOne hw⟩

#print axioms windowInv_shiftOne

end PalPeg.WindowInv
