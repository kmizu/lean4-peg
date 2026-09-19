import PalPeg.WindowInv
import PalPeg.GalilShiftH

/-!
# The period block is the text left of the centre

`WindowInv` knows that the period tape of a chain is a block `first cc :: xs ++ [last b]`, but
not what the letters are.  They are the places the walker read while copying: the stream of the
walker at the birth, from its second place on.  This file carries that fact through the life of
a chain (`BlockText`), one chain step and one matched event at a time.
-/

set_option autoImplicit false

namespace PalPeg.ChainBlockText

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilReplayGeneral2 PalPeg.GalilBranchInvariants PalPeg.GalilChainCoupling

/-- The letters of the block are the stream `L` of the birth walker after its first place. -/
def BlockLetters (L : List (Fin 3)) (b : Fin 3) (xs : List (Fin 3)) : Prop :=
  xs ++ [b] = (L.drop 1).take (xs.length + 1)

/-- The period tape of a live chain against the stream `L` of the walker at its birth. -/
def BlockText (L : List (Fin 3)) (cc : Fin 3) : ChainVM → Prop
  | .copy _ _ p v _ _ _ =>
      ∃ ys : List (Fin 3), v = GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cc) ys ∧
        ys = (L.drop 1).take ys.length ∧ GalilScaffoldPlace.stream p = L.drop ys.length
  | .back v _ _ _ _ => ∃ (b : Fin 3) (xs : List (Fin 3)), flat v = blockTokens cc b xs ∧
      BlockLetters L b xs
  | .watch w => ∃ (b : Fin 3) (xs : List (Fin 3)),
      flat w.machine.control.period = blockTokens cc b xs ∧ BlockLetters L b xs
  | _ => True

theorem flat_moveRight (v : GalilScaffoldChainPeriod.Tape) (hright : v.right ≠ []) :
    flat (GalilScaffoldChainPeriod.moveRight v) = flat v := by
  rcases v with ⟨ls, f, rs⟩
  cases rs with
  | nil => exact absurd rfl hright
  | cons r rs => simp [flat, GalilScaffoldChainPeriod.moveRight]

/-- A consume moves the head inside the block. -/
theorem flat_consume (s : GalilScaffoldChainConsume.State) (seen : Option (Fin 3))
    (hblock : OnBlock s.period) :
    flat (GalilScaffoldChainConsume.consume s seen).period = flat s.period := by
  cases hf : s.period.focus with
  | blank => rw [PalPeg.GalilShiftH.consume_of_none s seen (by rw [hf]; rfl)]
  | left => rw [PalPeg.GalilShiftH.consume_of_none s seen (by rw [hf]; rfl)]
  | plain a =>
    by_cases hs : seen = some a
    · subst hs
      rw [GalilScaffoldChainConsume.plain s a hf]
      cases s.forward
      · simpa using flat_moveLeft s.period
      · simp only [if_true]
        exact flat_moveRight _ (onBlock_right_ne hblock (by rw [hf]; rfl))
    · rw [GalilScaffoldChainConsume.mismatch s a seen (by rw [hf]; rfl) hs]
  | first c =>
    by_cases hs : seen = some c
    · subst hs
      rw [GalilScaffoldChainConsume.first s c hf]
      exact flat_moveRight _ (onBlock_right_ne hblock (by rw [hf]; rfl))
    · rw [GalilScaffoldChainConsume.mismatch s c seen (by rw [hf]; rfl) hs]
  | last b =>
    by_cases hs : seen = some b
    · subst hs
      rw [GalilScaffoldChainConsume.last s b hf]
      exact flat_moveLeft _
    · rw [GalilScaffoldChainConsume.mismatch s b seen (by rw [hf]; rfl) hs]

/-- A newborn chain has copied nothing and its walker is the birth walker. -/
theorem blockText_chainStart (answer : GalilScaffoldTape.Tape) (cc : Fin 3)
    (walker : GalilScaffoldPlace.Place) (ver : GalilScaffoldInputHead.PlaceHead)
    (radius : GalilScaffoldCounter.Counter) :
    BlockText (GalilScaffoldPlace.stream walker) cc (chainStart answer cc walker ver radius) :=
  ⟨[], rfl, rfl, rfl⟩

/-- One chain step keeps `BlockText`. -/
theorem blockText_step {L : List (Fin 3)} {cc : Fin 3} {x y : ChainVM}
    (htext : BlockText L cc x) (hblock : BlockInv x) (hstep : ChainStep x y) :
    BlockText L cc y := by
  cases hstep with
  | idle => trivial
  | brokenIdle _ => trivial
  | copyBit t hh p v lag margin ver a one legal present =>
    obtain ⟨ys, hv, hletters, hwalker⟩ := htext
    have hnext : L[ys.length + 1]? = some a := by
      have hread := present
      rw [GalilScaffoldPlace.read_stream, GalilScaffoldPlace.left_stream, hwalker] at hread
      rw [List.tail_drop, List.head?_drop] at hread
      exact hread
    refine ⟨ys ++ [a], ?_, ?_, ?_⟩
    · rw [hv, GalilScaffoldChainPeriod.fill_append]
      rfl
    · rw [List.length_append, List.length_singleton, List.take_succ, ← hletters]
      congr 1
      rw [List.getElem?_drop, show 1 + ys.length = ys.length + 1 from by omega, hnext]
      rfl
    · rw [GalilScaffoldPlace.left_stream, hwalker, List.tail_drop, List.length_append,
        List.length_singleton]
  | copyEnd t hh p v lag margin ver b hleft hp hv =>
    obtain ⟨ys, hys, hletters, -⟩ := htext
    rcases ys.eq_nil_or_concat with rfl | ⟨xs, a, rfl⟩
    · exfalso
      rw [hys] at hv
      simp [GalilScaffoldChainPeriod.fill, GalilScaffoldChainPeriod.start] at hv
    · rw [List.concat_eq_append] at hys hletters
      have hfoc := fill_last_focus (GalilScaffoldChainPeriod.start cc) xs a
      rw [← hys, hv] at hfoc
      injection hfoc with hab
      subst hab
      refine ⟨_, xs, by rw [hys]; exact flat_block cc _ xs, ?_⟩
      unfold BlockLetters
      rw [List.length_append, List.length_singleton] at hletters
      exact hletters
  | backStep v hh lag margin ver hf =>
    obtain ⟨b, xs, hflat, hletters⟩ := htext
    exact ⟨b, xs, by rw [flat_moveLeft]; exact hflat, hletters⟩
  | backDone v hh lag margin ver hf =>
    obtain ⟨b, xs, hflat, hletters⟩ := htext
    have hright : v.right ≠ [] := onBlock_right_ne hblock (by
      cases hv : v.focus with
      | first c => rfl
      | _ => rw [hv] at hf; simp [GalilScaffoldChainPeriod.isFirst] at hf)
    exact ⟨b, xs, by
      show flat (GalilScaffoldChainPeriod.moveRight v) = _
      rw [flat_moveRight v hright]; exact hflat, hletters⟩
  | watchStep w w' hinternal =>
    obtain ⟨b, xs, hflat, hletters⟩ := htext
    have hbw : OnBlock w.machine.control.period := hblock
    cases hinternal with
    | idle hz => exact ⟨b, xs, hflat, hletters⟩
    | take hp hg =>
      exact ⟨b, xs, by
        show flat (GalilScaffoldChainConsume.consume w.machine.control _).period = _
        rw [flat_consume _ _ hbw]; exact hflat, hletters⟩
  | watchBreak _ _ => trivial

/-- One matched event keeps `BlockText`. -/
theorem blockText_matched {L : List (Fin 3)} {cc : Fin 3} {y z : ChainVM}
    (htext : BlockText L cc y) (hblock : BlockInv y) (hmatched : ChainMatched y z) :
    BlockText L cc z := by
  cases hmatched with
  | idle => trivial
  | copy t h p v lag margin ver => exact htext
  | back v h lag margin ver => exact htext
  | watch w w' houter =>
    obtain ⟨b, xs, hflat, hletters⟩ := htext
    have hbw : OnBlock w.machine.control.period := hblock
    cases houter with
    | queued hz => exact ⟨b, xs, hflat, hletters⟩
    | immediate hz hg =>
      exact ⟨b, xs, by
        show flat (GalilScaffoldChainConsume.consume w.machine.control _).period = _
        rw [flat_consume _ _ hbw]; exact hflat, hletters⟩
  | breaks w w' hb => trivial
  | brokenMatched w => trivial

end PalPeg.ChainBlockText
