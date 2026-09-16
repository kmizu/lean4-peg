import Mathlib.Computability.DFA
import PegSeparation.Closure.BooleanClosure
import PegSeparation.Closure.RegularToPEG
import PalPeg.Basic

/-!
# 偶数長回文と Loff–Moreira–Reis Conjecture 7

LMR 2020, Conjecture 7：「偶数長回文の言語 `P = { w wᴿ | w ∈ {0,1}* }` は PEG を持たない」。

`PAL ∈ PEG` が（`PalPeg.Existence` の仮定のもとで）成り立つなら、
正則言語 `EvenLength = { w | |w| は偶数 }` との共通部分を取ることで `P ∈ PEG` が従い、
Conjecture 7 は反駁される。閉包性は成果物の
`Closure.recognizedByTotalPEG_inter` と `Closure.recognizedByTotalPEG_of_isRegular`。
-/

namespace PalPeg

open PegSeparation

/-! ## 長さの偶奇は正則 -/

/-- 偶数長の語の言語。 -/
def EvenLength : Language (Fin 2) := { w | Even w.length }

/-- 奇数長の語の言語。 -/
def OddLength : Language (Fin 2) := { w | Odd w.length }

theorem mem_EvenLength {w : List (Fin 2)} : w ∈ EvenLength ↔ Even w.length := Iff.rfl

theorem mem_OddLength {w : List (Fin 2)} : w ∈ OddLength ↔ Odd w.length := Iff.rfl

/-- 長さの偶奇を数える 2 状態 DFA。状態 `false` = 偶数、`true` = 奇数。偶数長を受理。 -/
def evenDFA : DFA (Fin 2) Bool where
  step := fun parity _ => !parity
  start := false
  accept := {false}

/-- `evenDFA` と同じ遷移で、奇数長を受理する DFA。 -/
def oddDFA : DFA (Fin 2) Bool where
  step := fun parity _ => !parity
  start := false
  accept := {true}

/-- 状態 `parity` から `w` を読み終えて `false` にいる ⇔ 開始時の偶奇と `|w|` の偶奇が揃う。 -/
theorem evenDFA_evalFrom_eq_false (parity : Bool) (w : List (Fin 2)) :
    evenDFA.evalFrom parity w = false ↔ (parity = false ↔ Even w.length) := by
  induction w generalizing parity with
  | nil => simp [DFA.evalFrom]
  | cons a w ih =>
    have hstep : evenDFA.evalFrom parity (a :: w) = evenDFA.evalFrom (!parity) w := rfl
    rw [hstep, ih, List.length_cons]
    cases parity <;> simp [Nat.even_add_one]

theorem evenDFA_eval_eq_false (w : List (Fin 2)) :
    evenDFA.eval w = false ↔ Even w.length := by
  have h := evenDFA_evalFrom_eq_false false w
  show evenDFA.evalFrom false w = false ↔ Even w.length
  simpa using h

theorem evenDFA_accepts : evenDFA.accepts = EvenLength := by
  ext w
  rw [DFA.mem_accepts, mem_EvenLength, ← evenDFA_eval_eq_false]
  exact Set.mem_singleton_iff

theorem odd_iff_not_even (n : ℕ) : Odd n ↔ ¬ Even n := by
  rw [Nat.odd_iff, Nat.even_iff]
  omega

theorem oddDFA_accepts : oddDFA.accepts = OddLength := by
  ext w
  rw [DFA.mem_accepts, mem_OddLength, odd_iff_not_even, ← evenDFA_eval_eq_false]
  show evenDFA.eval w ∈ ({true} : Set Bool) ↔ ¬ evenDFA.eval w = false
  rw [Set.mem_singleton_iff]
  cases evenDFA.eval w <;> simp

/-- `EvenLength` は正則（2 状態 DFA `evenDFA`）。 -/
theorem evenLength_isRegular : EvenLength.IsRegular :=
  ⟨Bool, inferInstance, evenDFA, evenDFA_accepts⟩

/-- `OddLength` は正則（2 状態 DFA `oddDFA`）。 -/
theorem oddLength_isRegular : OddLength.IsRegular :=
  ⟨Bool, inferInstance, oddDFA, oddDFA_accepts⟩

/-! ## 偶数長・奇数長回文 -/

/-- LMR Conjecture 7 の条件付き反駁：`PAL ∈ PEG` ならば偶数長回文 `PAL ⊓ EvenLength ∈ PEG`。 -/
theorem evenPal_of_pal (h : RecognizedByTotalPEG PAL) :
    RecognizedByTotalPEG (PAL ⊓ EvenLength) :=
  Closure.recognizedByTotalPEG_inter h
    (Closure.recognizedByTotalPEG_of_isRegular evenLength_isRegular)

/-- 対称形：`PAL ∈ PEG` ならば奇数長回文 `PAL ⊓ OddLength ∈ PEG`。 -/
theorem oddPal_of_pal (h : RecognizedByTotalPEG PAL) :
    RecognizedByTotalPEG (PAL ⊓ OddLength) :=
  Closure.recognizedByTotalPEG_inter h
    (Closure.recognizedByTotalPEG_of_isRegular oddLength_isRegular)

/-! ## LMR の `P = { w wᴿ }` との一致 -/

/-- LMR Conjecture 7 の言語 `P = { w wᴿ | w ∈ {0,1}* }`。 -/
def EvenPal : Language (Fin 2) := { w | ∃ u : List (Fin 2), w = u ++ u.reverse }

/-- `w ∈ PAL ⊓ EvenLength ↔ ∃ u, w = u ++ uᴿ`。 -/
theorem mem_PAL_inf_EvenLength_iff (w : List (Fin 2)) :
    w ∈ PAL ⊓ EvenLength ↔ ∃ u : List (Fin 2), w = u ++ u.reverse := by
  rw [Language.mem_inf, mem_PAL, mem_EvenLength]
  constructor
  · rintro ⟨hpal, ⟨r, hr⟩⟩
    refine ⟨w.take r, ?_⟩
    have hsplit : w = w.take r ++ w.drop r := (List.take_append_drop r w).symm
    have hlenTake : (w.take r).length = r := by
      rw [List.length_take, hr]
      omega
    have hlenDrop : (w.drop r).length = r := by
      rw [List.length_drop, hr]
      omega
    have hrev : (w.drop r).reverse ++ (w.take r).reverse = w.take r ++ w.drop r := by
      calc (w.drop r).reverse ++ (w.take r).reverse
          = (w.take r ++ w.drop r).reverse := by rw [List.reverse_append]
        _ = w.reverse := by rw [← hsplit]
        _ = w := hpal
        _ = w.take r ++ w.drop r := hsplit
    have hdrop : w.drop r = (w.take r).reverse :=
      (List.append_inj_right hrev (by simp [hlenTake, hlenDrop])).symm
    calc w = w.take r ++ w.drop r := hsplit
      _ = w.take r ++ (w.take r).reverse := by rw [hdrop]
  · rintro ⟨u, rfl⟩
    refine ⟨by simp, ⟨u.length, by simp⟩⟩

theorem EvenPal_eq : EvenPal = PAL ⊓ EvenLength := by
  ext w
  exact (mem_PAL_inf_EvenLength_iff w).symm

/-- LMR Conjecture 7 の条件付き反駁（原文の形）：`PAL ∈ PEG` ならば `{ w wᴿ } ∈ PEG`。 -/
theorem evenPal_ww_reverse_of_pal (h : RecognizedByTotalPEG PAL) :
    RecognizedByTotalPEG EvenPal := by
  rw [EvenPal_eq]
  exact evenPal_of_pal h

end PalPeg
