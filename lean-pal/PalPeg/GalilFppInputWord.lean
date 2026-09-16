import PalPeg.GalilFppRetry

set_option autoImplicit false
namespace PalPeg.GalilFppInputWord
open GalilFppInstruction GalilFppCode GalilFppCompare GalilFppRetry GalilFppDelta GalilFppFallbackBits

/-- FppFinite.Tape.bounded: left marker, input letters, right marker,
then blank. The four-letter alphabet is the exported abs# alphabet. -/
def inputTape (w : List (Fin 4)) (i : ℕ) : Fin 9 :=
  if i = 0 then 4 else
  match w[i-1]? with
  | some a => letter a
  | none => if i = w.length+1 then 5 else 6

theorem input_left (w : List (Fin 4)) : inputTape w 0 = 4 := by simp [inputTape]

theorem input_end (w : List (Fin 4)) : inputTape w (w.length+1) = 5 := by simp [inputTape]

theorem input_next (w : List (Fin 4)) (k : ℕ) (hk : k < w.length) :
    inputTape w (k+1) = letter w[k] := by
  simp [inputTape, List.getElem?_eq_getElem hk]

/-- Actual tape equality tests coincide with reference word tests, also
outside the word: markers and blanks cannot equal an input letter. -/
theorem compare_iff (w : List (Fin 4)) (k : ℕ) (j : Fin 4) :
    inputTape w (k+1) = letter j ↔ w[k]? = some j := by
  cases he : w[k]? with
  | none =>
    by_cases hk : k = w.length <;> fin_cases j <;> simp [inputTape, he, letter, hk]
  | some a => simp [inputTape, he, letter, Fin.ext_iff]

theorem valid_input (w : List (Fin 4)) (p : ℕ) (hp : p < w.length) :
    ValidInput (inputTape w) p := by
  constructor
  · intro k hk
    have hkw : k < w.length := by omega
    let a := w[k]
    refine ⟨⟨a.val, by have := a.isLt; omega⟩, ?_⟩
    rw [input_next w k hkw]
    simp [symbol, letter, a.isLt, a]
  · intro k hk hkp
    have hkw : k-1 < w.length := by omega
    refine ⟨w[k-1], ?_⟩
    have he : k-1+1 = k := by omega
    have hh := input_next w (k-1) hkw
    rw [he] at hh
    exact hh

/-- The concrete word representation is preserved through every actual
execution prefix, so comparison equivalence need not be re-assumed. -/
theorem preserves_input {x y : Config} {qs : List ℕ} (hs : Steps code x qs y)
    (w : List (Fin 4)) (ht : x.tape 0 = inputTape w) : y.tape 0 = inputTape w :=
  (input_tapes hs).1.trans ht

/-- Concrete input representation removes the semantic-comparison premise
from search correctness. The endpoint computes the next proper border. -/
theorem search_word (w : List (Fin 4)) (N : ℕ) (hN : 0 < N) (hw : N < w.length)
    (x : Config) (q : List (Fin 2)) (hp : x.pc = 68+offset w[N])
    (hr : Ready w (failure w N) x) (hq : GalilFppMaterialize.QueueAt x q)
    (ht : x.tape 0 = inputTape w) :
    ∃ r y qs, r ≤ failure w N ∧ Steps code x qs y ∧
      qs.length ≤ 29*(failure w N-r) ∧ y.pc = 68+offset w[N] ∧ Ready w r y ∧
      GalilFppMaterialize.QueueAt y (q ++ List.replicate (failure w N-r) 1) ∧
      (r = 0 ∨ y.tape 0 (r+1) = letter w[N]) ∧
      failure w (N+1) = (if y.tape 0 (r+1) = letter w[N] then r+1 else 0) ∧ y.tape 2 = x.tape 2 ∧
      y.pos 1 = x.pos 1 := by
  have hf := failure_le w N
  have hv : ValidInput (x.tape 0) (failure w N) := by
    rw [ht]
    exact valid_input w _ (by omega)
  obtain ⟨r, y, qs, hrp, hs, hl, hypc, hyr, hyq, hstop, hpath, hCt, hB⟩ := search w[N] w (failure w N) x q hp hr hq hv
  have hAt := (input_tapes hs).1
  have hsem := endpoint_failure w N hN hw w[N] (x.tape 0) r hrp hpath
    (by simpa [hAt] using hstop) (by intro k hk; rw [ht]; exact compare_iff w k w[N])
  exact ⟨r, y, qs, hrp, hs, hl, hypc, hyr, hyq, hstop, by simpa [hAt] using hsem, hCt, hB⟩

#print axioms search_word
end PalPeg.GalilFppInputWord
