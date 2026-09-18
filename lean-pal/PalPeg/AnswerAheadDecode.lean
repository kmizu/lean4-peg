import PalPeg.GalilBranchInvariants
import PalPeg.GalilDpCounters
import PalPeg.GalilDpCorrect

/-!
# DP 出力テープの復号: `denote = output h` から `AnswerAhead`

n124 で特定した「節 4 / 節 7 の供給に残る唯一の未実装」。

`GalilScaffoldChainAnswer.found_output` は `SafeQuanta` ＋ `GalilDpCorrect.Result` から

    denote (y.config.tapes 11) = GalilDpCounters.output h ∧ head (y.config.tapes 11) = h ∧
    (tapes 11).focus = 8 ∧ (tapes 11).left ≠ []

を無条件に与える。一方

    output h i = if i = 0 then 4 else if i ≤ h then 8 else 6
    denote t   = read (t.left.reverse ++ t.focus :: t.right)
    head t     = t.left.length
    AnswerAhead t n := ∃ ls, t.focus :: t.left = List.replicate n 8 ++ 4 :: ls

なので、`t.left.reverse` は index `0` で `4`、index `1..h-1` で `8`、すなわち
`t.left.reverse = 4 :: replicate (h-1) 8`。反転して
`t.left = replicate (h-1) 8 ++ [4]`、`t.focus = 8` を前に付けて
`t.focus :: t.left = replicate h 8 ++ 4 :: []`。

**これで `CopyInv` の残る 2 節のうち `AnswerAhead` 側がタダになる**
（もう 1 節 `PlaceAhead` は `GalilPrepLeast.found_copy_walk_least` の `CopyWalk` から）。

**`StartShape` は使わないこと**（`GalilLeafStartShape.not_startShape` が
あらゆる `Shared` について反証済み）。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.AnswerAheadDecode

open PalPeg PalPeg.GalilBranchInvariants

/-- `read` は長さの範囲内なら添字アクセス。 -/
theorem read_getElem : ∀ (xs : List (Fin 9)) (i : ℕ) (hi : i < xs.length),
    GalilScaffoldTape.read xs i = xs[i] := by
  intro xs
  induction xs with
  | nil => intro i hi; simp at hi
  | cons a xs ih =>
    intro i hi
    cases i with
    | zero => rfl
    | succ n => exact ih n (by simpa using hi)

/-- `read` は前半の長さの範囲内なら後半を見ない。 -/
theorem read_append_lt : ∀ (xs ys : List (Fin 9)) (i : ℕ) (_hi : i < xs.length),
    GalilScaffoldTape.read (xs ++ ys) i = GalilScaffoldTape.read xs i := by
  intro xs
  induction xs with
  | nil => intro ys i hi; simp at hi
  | cons a xs ih =>
    intro ys i hi
    cases i with
    | zero => rfl
    | succ n => exact ih ys n (by simpa using hi)

/-- **DP 出力テープの復号。**  `denote t = output h`、`head t = h`、`t.focus = 8`、
`0 < h` から `AnswerAhead t h`。 -/
theorem answerAhead_of_denote {t : GalilScaffoldTape.Tape} {h : ℕ} (hPos : 0 < h)
    (hDenote : GalilScaffoldTape.denote t = GalilDpCounters.output h)
    (hHead : GalilScaffoldTape.head t = h)
    (hFocus : t.focus = 8) :
    AnswerAhead t h := by
  have hLen : t.left.length = h := hHead
  have hRevLen : t.left.reverse.length = h := by simpa using hLen
  -- 逆順の左側は `4 :: replicate (h-1) 8`
  have hIndex : ∀ i : ℕ, ∀ hi : i < h,
      t.left.reverse[i]'(by rw [hRevLen]; exact hi) = GalilDpCounters.output h i := by
    intro i hi
    have h1 : GalilScaffoldTape.read (t.left.reverse ++ t.focus :: t.right) i
        = GalilDpCounters.output h i := congrFun hDenote i
    rw [read_append_lt _ _ i (by rw [hRevLen]; exact hi)] at h1
    rw [read_getElem _ i (by rw [hRevLen]; exact hi)] at h1
    exact h1
  have hRev : t.left.reverse = (4 : Fin 9) :: List.replicate (h - 1) 8 := by
    refine List.ext_getElem (by simp [hRevLen]; omega) ?_
    intro i h1 h2
    rw [hIndex i (by rw [hRevLen] at h1; exact h1)]
    cases i with
    | zero => simp [GalilDpCounters.output]
    | succ n =>
      have hn : n < h - 1 := by simp at h2; omega
      simp only [List.getElem_cons_succ, List.getElem_replicate]
      unfold GalilDpCounters.output
      rw [if_neg (by omega), if_pos (by omega)]
  have hLeft : t.left = List.replicate (h - 1) 8 ++ [(4 : Fin 9)] := by
    have := congrArg List.reverse hRev
    simpa using this
  refine ⟨[], ?_⟩
  rw [hFocus, hLeft]
  have : h = (h - 1) + 1 := by omega
  rw [this]
  simp [List.replicate_succ]

#print axioms read_getElem
#print axioms read_append_lt
#print axioms answerAhead_of_denote


/-! ## `PlaceAhead` も `Candidate` からタダ

`GalilDpCorrect.Candidate w lower h` の第 2 節は `4*h+1 ≤ w.length`
（`GalilDpCorrect:8`）。found 経路では `w = (GalilScaffoldPlace.stream p).take (span+1)` で、
`take` の長さは元の長さ以下なので

    h + 1 ≤ 4*h + 1 ≤ w.length ≤ (stream p).length

すなわち `PlaceAhead p h`。これで `CopyInv` の 4 節がすべて found 文脈から出る。 -/

/-- **`PlaceAhead` は `Candidate` からタダ。** -/
theorem placeAhead_of_candidate {p : GalilScaffoldPlace.Place} {lower span h : ℕ}
    (hCand : GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream p).take (span + 1)) lower h) :
    PlaceAhead p h := by
  have hLong : 4 * h + 1 ≤ ((GalilScaffoldPlace.stream p).take (span + 1)).length := hCand.2.1
  have hTake : ((GalilScaffoldPlace.stream p).take (span + 1)).length
      ≤ (GalilScaffoldPlace.stream p).length := by simp
  show h + 1 ≤ (GalilScaffoldPlace.stream p).length
  omega

/-- **`CopyInv` が found 文脈から丸ごと出る。**  4 節の内訳:
`AnswerAhead`（`answerAhead_of_denote`）／`PlaceAhead`（`placeAhead_of_candidate`）／
`OnPrefix`（`onPrefix_start`）／`reset.neg = []`（計算）。 -/
theorem copyInv_of_found {answer : GalilScaffoldTape.Tape} {cen : Fin 3}
    {p : GalilScaffoldPlace.Place} {lower span h : ℕ} (hPos : 0 < h)
    (hDenote : GalilScaffoldTape.denote answer = GalilDpCounters.output h)
    (hHead : GalilScaffoldTape.head answer = h)
    (hFocus : answer.focus = 8)
    (hCand : GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream p).take (span + 1)) lower h) :
    CopyInv answer GalilScaffoldCounter.reset p (GalilScaffoldChainPeriod.start cen) h :=
  ⟨answerAhead_of_denote hPos hDenote hHead hFocus, placeAhead_of_candidate hCand,
    onPrefix_start cen, rfl, fun hz => absurd hz (by omega)⟩

#print axioms placeAhead_of_candidate
#print axioms copyInv_of_found

end PalPeg.AnswerAheadDecode
