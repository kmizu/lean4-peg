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

/-! ## The predictions of a block copied from the text -/

/-- The first round trip of the predictions is the text left of the centre, read leftwards:
the block letters are that text, and the way back is its mirror image in the block palindrome
at `C - h`. -/
theorem bounce_eq_left {e : List (Fin 3)} {C : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    (hcc : e[C]? = some cc)
    (hletters : ∀ i, i < xs.length + 1 → (xs ++ [b])[i]? = e[C - 1 - i]?)
    (hblockPal : Manacher.PalAt e (C - (xs.length + 1)) (xs.length + 1))
    (hCh : xs.length + 1 ≤ C)
    {t : ℕ} (ht1 : 1 ≤ t) (ht2 : t ≤ 2 * (xs.length + 1)) :
    (GalilScaffoldChainSweep.bounce cc b xs)[t - 1]? = e[C - t]? := by
  have h2C : 2 * (xs.length + 1) ≤ C := by
    have := hblockPal.1
    omega
  unfold GalilScaffoldChainSweep.bounce
  rcases Nat.lt_or_ge (t - 1) (xs.length + 1) with hfirst | hsecond
  · rw [List.getElem?_append_left (by simpa using hfirst), hletters (t - 1) hfirst]
    congr 1
    omega
  · rw [List.getElem?_append_right (by simpa using hsecond)]
    simp only [List.length_append, List.length_singleton]
    have hmirror := hblockPal.2.2 (t - (xs.length + 1)) (by omega)
    rw [show C - (xs.length + 1) - (t - (xs.length + 1)) = C - t from by omega,
      show C - (xs.length + 1) + (t - (xs.length + 1)) = C - 2 * (xs.length + 1) + t from by
        omega] at hmirror
    rw [hmirror]
    rcases Nat.lt_or_ge (t - 1 - (xs.length + 1)) xs.length with hinside | hlast
    · rw [List.getElem?_append_left (by simpa using hinside), List.getElem?_reverse hinside]
      have hletter := hletters (xs.length - 1 - (t - 1 - (xs.length + 1))) (by omega)
      rw [List.getElem?_append_left (by omega)] at hletter
      rw [hletter]
      congr 1
      omega
    · rw [List.getElem?_append_right (by simpa using hlast)]
      have hindex : t - 1 - (xs.length + 1) - xs.reverse.length = 0 := by
        rw [List.length_reverse]
        omega
      rw [hindex]
      have ht : t = 2 * (xs.length + 1) := by omega
      rw [show C - 2 * (xs.length + 1) + t = C from by omega]
      simpa using hcc.symm

/-- **The predictions of a first-round chain are the text**, up to four semiperiods to the right
of the centre, at a place whose mirror image in the centre carries the same letter: the first
round trip by `bounce_eq_left`, the second by the left certificate (period `2h` on
`[C - 4h, C]`). -/
theorem bounce_eq_text {e : List (Fin 3)} {C : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    (hcc : e[C]? = some cc)
    (hletters : ∀ i, i < xs.length + 1 → (xs ++ [b])[i]? = e[C - 1 - i]?)
    (hblockPal : Manacher.PalAt e (C - (xs.length + 1)) (xs.length + 1))
    (hCh : xs.length + 1 ≤ C)
    (hleft : PeriodOn e (2 * (xs.length + 1)) (C - 4 * (xs.length + 1)) C)
    {t : ℕ} (ht1 : 1 ≤ t) (htC : t ≤ C) (hmirror : e[C - t]? = e[C + t]?)
    (ht4 : t + 1 ≤ 4 * (xs.length + 1)) :
    e[C + t]? = (GalilScaffoldChainSweep.bounce cc b xs)[(t - 1) % (2 * (xs.length + 1))]? := by
  rw [← hmirror]
  rcases Nat.lt_or_ge (2 * (xs.length + 1)) t with hsecond | hfirst
  · have hmod : (t - 1) % (2 * (xs.length + 1)) = t - 2 * (xs.length + 1) - 1 := by
      rw [show t - 1 = (t - 2 * (xs.length + 1) - 1) + 2 * (xs.length + 1) from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hmod, bounce_eq_left hcc hletters hblockPal hCh (t := t - 2 * (xs.length + 1))
      (by omega) (by omega)]
    have hperiod := hleft (C - t) (by omega) (by omega)
    rw [hperiod]
    congr 1
    omega
  · rw [Nat.mod_eq_of_lt (by omega), bounce_eq_left hcc hletters hblockPal hCh ht1 hfirst]

/-! ## The block of the window is the block of the tape -/

theorem flat_run {s : GalilScaffoldChainConsume.State} (pre : List (Fin 3))
    (hblock : OnBlock s.period) :
    flat (GalilScaffoldChainSweep.run s pre).period = flat s.period := by
  induction pre generalizing s with
  | nil => rfl
  | cons a pre ih =>
    exact (ih (onBlock_consume s (some a) hblock)).trans (flat_consume s (some a) hblock)

/-- The period tape of a watch whose window speaks about the block `cc b xs` is that block. -/
theorem flat_of_coreP {raw : List (Fin 2)} {cc b : Fin 3} {xs : List (Fin 3)} {anchor : ℕ}
    {m : GalilScaffoldChainVerifier.State}
    (hcore : PalPeg.ShiftPalAlongTrace.CoreP raw cc b xs anchor m) :
    flat m.control.period = blockTokens cc b xs := by
  obtain ⟨-, -, -, -, pre, hsame, -, -⟩ := hcore
  rw [hsame.1, flat_run pre (onBlock_ready cc b xs)]
  show flat (GalilScaffoldChainPeriod.moveRight
    ⟨[], GalilScaffoldChainPeriod.Token.first cc,
      xs.map GalilScaffoldChainPeriod.Token.plain ++ [GalilScaffoldChainPeriod.Token.last b]⟩) = _
  rw [flat_moveRight _ (by simp)]
  rfl

theorem blockTokens_inj {c c' b b' : Fin 3} {xs xs' : List (Fin 3)}
    (h : blockTokens c b xs = blockTokens c' b' xs') : b = b' ∧ xs = xs' := by
  unfold blockTokens at h
  have htail := (List.cons.inj h).2
  have hlength : (xs.map GalilScaffoldChainPeriod.Token.plain).length
      = (xs'.map GalilScaffoldChainPeriod.Token.plain).length := by
    have := congrArg List.length htail
    simp only [List.length_append, List.length_map, List.length_singleton] at this ⊢
    omega
  obtain ⟨hmap, hlast⟩ := List.append_inj htail hlength
  refine ⟨?_, ?_⟩
  · have := (List.cons.inj hlast).1
    exact GalilScaffoldChainPeriod.Token.last.inj this
  · exact List.map_injective_iff.mpr (fun _ _ hab => GalilScaffoldChainPeriod.Token.plain.inj hab)
      hmap

/-- **The prediction of a first-round watch is the next place of the text**, as long as that
place carries the letter of its mirror image in the centre and lies within four semiperiods of
the centre.  `L` is the stream of the centre's place (`L[i] = e[C - i]`), the window is anchored
at the centre `C`. -/
theorem prediction_eq_text_of_window {raw : List (Fin 2)} {C P : ℕ} {cc cc' : Fin 3}
    {w : GalilScaffoldChainWatch.State} {L : List (Fin 3)}
    (hwindow : PalPeg.WindowInv.WindowInv raw C P cc (.watch w))
    (htext : BlockText L cc' (.watch w))
    (hcc : (encoded raw)[C]? = some cc)
    (hL : ∀ i, i < L.length → L[i]? = (encoded raw)[C - i]?) (hLlength : L.length = C)
    (hblockPal : Manacher.PalAt (encoded raw) (C - periodLength w) (periodLength w))
    (hleft : PeriodOn (encoded raw) (2 * periodLength w) (C - 4 * periodLength w) C)
    (hroom : position w.machine.verifier + 1 ≤ 2 * C)
    (hmirror : (encoded raw)[C - (position w.machine.verifier + 1 - C)]?
      = (encoded raw)[position w.machine.verifier + 1]?)
    (hfour : position w.machine.verifier + 2 ≤ C + 4 * periodLength w) :
    GalilScaffoldChainConsume.symbol w.machine.control.period.focus
      = (encoded raw)[position w.machine.verifier + 1]? := by
  obtain ⟨b, xs, -, -, hcore⟩ := hwindow
  obtain ⟨b', xs', hflat', hletters'⟩ := htext
  have hflat := flat_of_coreP hcore
  obtain ⟨hb, hxs⟩ := blockTokens_inj (hflat.symm.trans hflat')
  subst hb
  subst hxs
  have hlength := PalPeg.ShiftPalAlongTrace.periodLength_of_coreP hcore
  rw [hlength] at hblockPal hleft hfour
  have hsymbol := PalPeg.ShiftPalAlongTrace.symbol_of_coreP hcore
  obtain ⟨-, -, -, -, pre, -, -, hindex⟩ := hcore
  have hhalf : xs.length + 1 ≤ C - (xs.length + 1) := hblockPal.1
  have hletters : ∀ i, i < xs.length + 1 → (xs ++ [b])[i]? = (encoded raw)[C - 1 - i]? := by
    intro i hi
    unfold BlockLetters at hletters'
    rw [hletters', List.getElem?_take, if_pos hi, List.getElem?_drop, hL (1 + i) (by omega)]
    congr 1
    omega
  have htext := bounce_eq_text (t := position w.machine.verifier + 1 - C)
    hcc hletters hblockPal (by omega) hleft (by omega) (by omega)
    (by rw [hmirror]; congr 1; omega) (by omega)
  rw [hsymbol,
    show position w.machine.verifier + 1 - (C + 1)
      = position w.machine.verifier + 1 - C - 1 from by omega, ← htext]
  congr 1
  omega

end PalPeg.ChainBlockText
