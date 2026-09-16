import PalPeg.GalilFppPreparation

set_option autoImplicit false
namespace PalPeg.GalilFppPrepareCopy
open GalilFppWide GalilFppPreparation

def embed (a : Fin 3) : Fin 4 := ⟨a.val, by omega⟩
def source (w : List (Fin 3)) : ℕ → Fin 9 := GalilFppInputWord.inputTape (w.map embed)

theorem source_next (w : List (Fin 3)) (k : ℕ) (hk : k < w.length) :
    source w (k+1) = symbol w[k] := by
  have h := GalilFppInputWord.input_next (w.map embed) k (by simpa using hk)
  simpa [source, embed, symbol, GalilFppRetry.letter] using h

theorem source_reverse (w : List (Fin 3)) (k : ℕ) (hk : k < w.reverse.length) :
    source w (w.length-k) = symbol w.reverse[k] := by
  have hk' : k < w.length := by simpa using hk
  have h := source_next w (w.length-1-k) (by omega)
  have he : w.length-1-k+1 = w.length-k := by omega
  rw [he] at h
  simpa [List.getElem_reverse] using h

/-- Exact final configuration of the forward, separator, reverse and
end-marker copying phases; rewind and initial setup are separate. -/
def copied (w : List (Fin 3)) (x : Config 9) : Config 9 :=
  finish (backwardMany w.reverse (turn (forwardMany w x)))

/-- The real bounded SOURCE discharges every per-letter and sentinel
read premise, including the empty source case. -/
theorem copy_run (w : List (Fin 3)) (x : Config 9) (hp : x.pc = 259)
    (hpos : x.pos 7 = 1) (ht : x.tape 7 = source w) :
    ∃ qs, Steps GalilFppMarkedCode.code x qs (copied w x) ∧
      qs.length = 14*w.length+10 ∧ (copied w x).pc = 251 ∧
      (copied w x).pos 7 = 0 ∧ (copied w x).tape 7 = source w := by
  obtain ⟨qs, hs, hl, hpc⟩ := forward_run w x hp (by
    intro k hk
    rw [ht, hpos, Nat.add_comm 1 k]
    exact source_next w k hk)
  let a := forwardMany w x
  have hAp : a.pos 7 = w.length+1 := by simp [a, forward_many_pos, hpos, Nat.add_comm]
  have hAt : a.tape 7 = source w := by simpa [a, forward_many_tape] using ht
  have hEnd : a.tape 7 (a.pos 7) = 5 := by
    rw [hAp, hAt]
    simpa [source] using GalilFppInputWord.input_end (w.map embed)
  have hturn := turn_step a hpc hEnd (by omega)
  let b := turn a
  have hBp : b.pos 7 = w.length := by simp [b, turn, left, right, written, hAp]
  have hBt : b.tape 7 = source w := by simpa [b, turn, left, right, written] using hAt
  obtain ⟨rs, hr, hrl, hrpc⟩ := backward_run w.reverse b rfl (by simp [hBp]) (by
    intro k hk
    rw [hBt, hBp]
    exact source_reverse w k hk)
  let c := backwardMany w.reverse b
  have hCp : c.pos 7 = 0 := by simp [c, backward_many_pos, hBp]
  have hCt : c.tape 7 = source w := by simpa [c, backward_many_tape] using hBt
  have hLeft : c.tape 7 (c.pos 7) = 4 := by
    rw [hCp, hCt]; exact GalilFppInputWord.input_left _
  have hfinish := finish_step c hrpc hLeft
  refine ⟨qs ++ [259,281,280,279,278,277,276] ++ rs ++ [260,258,257],
    steps_append (steps_append (steps_append hs hturn) hr) hfinish, ?_, rfl, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse] at *
    omega
  · change (finish c).pos 7 = 0
    exact hCp
  · change (finish c).tape 7 = source w
    simpa [finish, written] using hCt

theorem fill_append (as bs : List (Fin 9)) (p : ℕ) (t : ℕ → Fin 9) :
    fill (as ++ bs) p t = fill bs (p+as.length) (fill as p t) := by
  induction as generalizing p t with
  | nil => simp [fill]
  | cons a as ih =>
    simpa [fill, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (ih (p+1) (Function.update t p a))

/-- Both input copies contain exactly source, separator, reversed source
and right marker; all preexisting cells outside this write range survive. -/
theorem copied_ab (w : List (Fin 3)) (x : Config 9) (t : Fin 9) (ht : t = 0 ∨ t = 1) :
    (copied w x).tape t =
      fill (w.map symbol ++ [3] ++ w.reverse.map symbol ++ [5]) (x.pos t) (x.tape t) := by
  rcases ht with ht | ht <;> subst t <;>
    simp [copied, finish, written, backward_many_tape, backward_many_pos,
      turn, left, right, forward_many_tape, forward_many_pos, fill_append, fill,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem copied_marks (w : List (Fin 3)) (x : Config 9) :
    (copied w x).tape 8 = fill (List.replicate w.length 7 ++ [5]) (x.pos 8) (x.tape 8) := by
  simp [copied, finish, written, backward_many_tape, turn, left, right,
    forward_many_tape, forward_many_pos, fill_append, fill]

#print axioms copied_ab
#print axioms copied_marks
#print axioms copy_run
end PalPeg.GalilFppPrepareCopy
