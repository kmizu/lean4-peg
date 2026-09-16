import PalPeg.GalilFppPrepareRewind

set_option autoImplicit false
namespace PalPeg.GalilFppPrepareCells
open GalilFppWide GalilFppPreparation GalilFppPrepareCopy GalilFppPrepareRewind

theorem fill_outside (as : List (Fin 9)) (p : ℕ) (t : ℕ → Fin 9) (i : ℕ)
    (hi : i < p ∨ p+as.length ≤ i) : fill as p t i = t i := by
  induction as generalizing p t with
  | nil => rfl
  | cons a as ih =>
    rw [fill, ih (p+1) (Function.update t p a) (by simp only [List.length_cons] at hi; omega)]
    have hn : i ≠ p := by simp only [List.length_cons] at hi; omega
    simp [hn]

theorem fill_inside (as : List (Fin 9)) (p : ℕ) (t : ℕ → Fin 9) (k : ℕ)
    (hk : k < as.length) : fill as p t (p+k) = as[k] := by
  induction as generalizing p t k with
  | nil => simp at hk
  | cons a as ih =>
    cases k with
    | zero =>
      simp only [Nat.add_zero, fill]
      rw [fill_outside as (p+1) _ p (Or.inl (by omega))]
      simp
    | succ k =>
      have hk' : k < as.length := by simpa using hk
      simpa [fill, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (p+1) (Function.update t p a) k hk'

theorem copied_head (w : List (Fin 3)) (x : Config 9) (j : Fin 3) :
    (copied w x).pos (tape j) =
      if j = 2 then x.pos 8+w.length else x.pos (tape j)+2*w.length+1 := by
  fin_cases j <;> simp [copied, tape, finish, written, backward_many_pos,
    turn, left, right, forward_many_pos] <;> omega

/-- Copying itself establishes the character and sentinel conditions
required by all three real rewind loops. -/
theorem copied_rewind_conditions (w : List (Fin 3)) (x : Config 9)
    (hp : ∀ j : Fin 3, x.pos (tape j) = 1)
    (hl : ∀ j : Fin 3, x.tape (tape j) 0 = 4) :
    (∀ j : Fin 3, (copied w x).tape (tape j) 0 = 4) ∧
    (∀ (j : Fin 3) k, 0 < k → k ≤ (copied w x).pos (tape j) →
      allowed j ((copied w x).tape (tape j) k) = true) := by
  have hallowed : ∀ (j : Fin 3) (as : List (Fin 9)),
      (copied w x).tape (tape j) = fill as 1 (x.tape (tape j)) →
      (copied w x).pos (tape j) = as.length →
      (∀ a ∈ as, allowed j a = true) →
      (copied w x).tape (tape j) 0 = 4 ∧
      (∀ k, 0 < k → k ≤ (copied w x).pos (tape j) →
        allowed j ((copied w x).tape (tape j) k) = true) := by
    intro j as ht hn ha
    constructor
    · rw [ht, fill_outside as 1 _ 0 (Or.inl (by omega))]; exact hl j
    · intro k hk hkn
      have hb : k-1 < as.length := by omega
      have he : 1+(k-1) = k := by omega
      rw [ht, ← he, fill_inside as 1 _ (k-1) hb]
      exact ha _ (List.getElem_mem _)
  have hresult : ∀ j : Fin 3,
      (copied w x).tape (tape j) 0 = 4 ∧
      (∀ k, 0 < k → k ≤ (copied w x).pos (tape j) →
        allowed j ((copied w x).tape (tape j) k) = true) := by
    intro j
    by_cases hj : j = 2
    · subst j
      have h8 : x.pos 8 = 1 := hp 2
      apply hallowed 2 (List.replicate w.length 7 ++ [5])
      · simpa [tape, h8] using copied_marks w x
      · simp [copied_head, h8, Nat.add_comm]
      · intro a ha
        simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at ha
        rcases ha with ⟨_, rfl⟩ | rfl <;> decide
    · apply hallowed j (w.map symbol ++ [3] ++ w.reverse.map symbol ++ [5])
      · have ht : tape j = 0 ∨ tape j = 1 := by fin_cases j <;> simp_all [tape]
        simpa [hp j] using copied_ab w x (tape j) ht
      · simp [copied_head, hj, hp j]; omega
      · intro a ha
        simp only [List.mem_append, List.mem_map, List.mem_singleton] at ha
        rcases ha with ((⟨b, _, rfl⟩ | rfl) | ⟨b, _, rfl⟩) | rfl
        · simp [allowed, hj, symbol, show b.val ≤ 3 by omega]
        · simp [allowed, hj]
        · simp [allowed, hj, symbol, show b.val ≤ 3 by omega]
        · simp [allowed, hj]
  exact ⟨fun j => (hresult j).1, fun j => (hresult j).2⟩

/-- Copy and rewind are connected without any assumed character facts
about the intermediate tapes. The caller supplies only the source and
the setup phase's initial heads and left markers. -/
theorem copy_rewind (w : List (Fin 3)) (x : Config 9) (hpc : x.pc = 259)
    (hsource : x.tape 7 = source w) (hspos : x.pos 7 = 1)
    (hp : ∀ j : Fin 3, x.pos (tape j) = 1)
    (hl : ∀ j : Fin 3, x.tape (tape j) 0 = 4) :
    ∃ y qs, Steps GalilFppMarkedCode.code x qs y ∧ qs.length = 24*w.length+24 ∧
      y.pc = 227 ∧ y.tape = (copied w x).tape ∧
      y.pos 0 = 0 ∧ y.pos 1 = 1 ∧ y.pos 8 = 0 ∧ y.pos 7 = 0 ∧
      y.pos = Function.update (Function.update (Function.update (copied w x).pos 0 0) 1 1) 8 0 := by
  obtain ⟨qs, hs, hlen, hcopyPC, hsourcePos, _⟩ := copy_run w x hpc hspos hsource
  obtain ⟨hleft, hbody⟩ := copied_rewind_conditions w x hp hl
  obtain ⟨y, rs, hr, hrl, hypc, hyt, hyp⟩ := rewind_all (copied w x) hcopyPC hleft hbody
  have h0 : (copied w x).pos 0 = 2*w.length+2 := by
    have h := copied_head w x 0
    have hp0 : x.pos 0 = 1 := hp 0
    simp [tape, hp0] at h
    omega
  have h1 : (copied w x).pos 1 = 2*w.length+2 := by
    have h := copied_head w x 1
    have hp1 : x.pos 1 = 1 := hp 1
    simp [tape, hp1] at h
    omega
  have h8 : (copied w x).pos 8 = w.length+1 := by
    have h := copied_head w x 2
    have hp8 : x.pos 8 = 1 := hp 2
    simpa [tape, hp8, Nat.add_comm] using h
  refine ⟨y, qs ++ rs, steps_append hs hr, ?_, hypc, hyt, ?_, ?_, ?_, ?_, hyp⟩
  · simp only [List.length_append]
    rw [h0, h1, h8] at hrl
    omega
  · simp [hyp]
  · simp [hyp]
  · simp [hyp]
  · simpa [hyp] using hsourcePos

#print axioms copy_rewind
#print axioms copied_rewind_conditions
end PalPeg.GalilFppPrepareCells
