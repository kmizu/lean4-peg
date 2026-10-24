import MacroPeg.CBV.SequentialFrontScanMachine

/-! Restore a whole local front to the binary continuation. Local fields have
their last value on top, so emitting them backwards preserves stream order. -/

namespace Shallot.MacroPeg.CBV.SequentialFrontWrite

open Complexity Complexity.BinaryWord SequentialFieldFetch SequentialStackBinary
open SequentialFrontRead (locals)

def pull : LProg 11 := .loop 9 (· == 5) (moveTop 9 3)

/-- Move the final unary field's ones, stopping at its marker. The prefix of
the local field list and the binary continuation are untouched. -/
theorem pull_runs {B width a v : Nat} (tail : List Bool) (D C : List Nat)
    (hB : LenOK B (start width [] tail (D ++ 2 :: List.replicate v 1) a C))
    (hcap : a + v + 2 ≤ B) :
    ∃ T, Complexity.Runs (LenOK B) pull
      (start width [] tail (D ++ 2 :: List.replicate v 1) a C)
      (start width [] tail (D ++ [2]) (a + v) C) T := by
  induction v generalizing a with
  | zero =>
    exact ⟨1, 1, Nat.le_refl _, .loopF hB (by simp [start, lastSym])⟩
  | succ v ih =>
    let L := start width [] tail (D ++ 2 :: List.replicate (v + 1) 1) a C
    have hrep : List.replicate (v + 1) 1 = List.replicate v 1 ++ [1] := by
      simp [← List.replicate_append_replicate]
    have hL9 : L 9 = (D ++ 2 :: List.replicate v 1) ++ [1] := by
      simp [L, start, hrep, List.append_assoc]
    have hlast : (L 9).getLast?.toList = [1] := by rw [hL9, List.getLast?_concat]; rfl
    have hdrop : (L 9).dropLast = D ++ 2 :: List.replicate v 1 := by rw [hL9, List.dropLast_concat]
    obtain ⟨hcopy, hmove⟩ := lenOK_moveTop hB (by decide : (9 : Fin 11) ≠ 3)
      (by simp [start]; omega)
    have hm := runs_moveTop (L := L) (Q := LenOK B) (by decide : (9 : Fin 11) ≠ 3) hB hcopy hmove
    have he : L.moveTop 9 3 = start width [] tail (D ++ 2 :: List.replicate v 1) (a + 1) C := by
      have hL3 : L 3 = List.replicate a 1 := by simp [L, start]
      simp only [Lists.moveTop, hlast, hdrop, hL3]
      have hacc : List.replicate a 1 ++ [1] = List.replicate (a + 1) 1 := by
        simp [← List.replicate_append_replicate]
      rw [hacc]
      funext i
      by_cases hi3 : i = 3 <;> by_cases hi9 : i = 9 <;>
        simp_all [L, start, Lists.set]
    rw [he] at hm
    have hnext : LenOK B (start width [] tail (D ++ 2 :: List.replicate v 1) (a + 1) C) := by
      obtain ⟨_, _, hx⟩ := hm
      exact hx.q_end _ (Or.inl rfl)
    obtain ⟨T, hr⟩ := ih (a := a + 1) hnext (by omega)
    have haa : a + 1 + v = a + (v + 1) := by omega
    rw [haa] at hr
    obtain ⟨t1, _, hx1⟩ := hm
    obtain ⟨t2, _, hx2⟩ := hr
    exact ⟨t1 + 1 + t2, t1 + 1 + t2, Nat.le_refl _,
      .loopC hB (by
        change ((lastSym (L 9)) == 5) = true
        rw [lastSym, hL9, List.getLast?_concat]
        rfl) hx1 hx2⟩

def body : LProg 11 :=
  .seq pull (.seq (.pop 9) (.seq (copyLenP 8 1 7) (writeP 3 5 6 1 2 0)))

def writeFront : LProg 11 := .seq (clearP 3) (.loop 9 nonEmpty body)

theorem body_runs {B width v : Nat} (tail : List Bool) (D C : List Nat)
    (hv : v < 2 ^ width)
    (hB : LenOK B (start width [] tail (D ++ 2 :: List.replicate v 1) 0 C))
    (hval : v + 3 ≤ B) (hout : tail.length + width + 2 ≤ B) :
    ∃ T, Complexity.Runs (LenOK B) body (start width [] tail (D ++ 2 :: List.replicate v 1) 0 C)
      (start width [] (word width v ++ tail) D 0 C) T := by
  obtain ⟨T1, hpull⟩ := pull_runs tail D C hB (by omega)
  have hpull' : Complexity.Runs (LenOK B) pull
      (start width [] tail (D ++ 2 :: List.replicate v 1) 0 C)
      (start width [] tail (D ++ [2]) v C) T1 := by simpa only [Nat.zero_add] using hpull
  let L := start width [] tail (D ++ [2]) v C
  have hL : LenOK B L := by
    obtain ⟨_, _, hx⟩ := hpull'
    exact hx.q_end L (Or.inl rfl)
  let M := start width [] tail D v C
  have hepop : L.set 9 (L 9).dropLast = M := by
    have hdrop : (L 9).dropLast = D := by
      change (D ++ [2]).dropLast = D
      exact List.dropLast_concat
    rw [hdrop]
    funext i
    by_cases hi : i = 9 <;> simp_all [M, L, start, Lists.set]
  have hM : LenOK B M := by
    rw [← hepop]
    apply lenOK_set hL 9
    have := hL 9
    simp only [List.length_dropLast]
    omega
  have hpop := runs_pop (i := 9) hL (by rw [hepop]; exact hM)
  rw [hepop] at hpop
  have hc := copyLen_spec (by decide : ([8, 1, 7] : List (Fin 11)).Nodup)
    (L := M) (B := B) (by simp [M, start]) hM
    (by have := hM 8; simpa [M, start] using this)
  let F := M.set 1 (List.replicate width 1)
  have hc' : Complexity.Runs (LenOK B) (copyLenP 8 1 7) M F (8 * (width + 1)) := by
    simpa [M, start] using hc
  have hF : LenOK B F := by
    obtain ⟨_, _, hx⟩ := hc'
    exact hx.q_end F (Or.inl rfl)
  obtain ⟨T4, hw⟩ := SequentialWordWrite.write_word_runs (by decide :
    ([3, 5, 6, 1, 2, 0] : List (Fin 11)).Nodup) hv tail (L := F)
    (by simp [F, M, start, Lists.set]) (by simp [F, M, start, Lists.set])
    (by simp [F, M, start, Lists.set]) (by simp [F]) (by simp [F, M, start, Lists.set])
    (by simp [F, M, start, Lists.set, SequentialStackBinary.pack]) hF hval hout
  have heout : (((((F.set 3 []).set 5 []).set 6 []).set 1 []).set 2 []).set 0
      (storage (word width v ++ tail)) = start width [] (word width v ++ tail) D 0 C := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨
      i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [F, M, start, Lists.set, SequentialStackBinary.pack]
  rw [heout] at hw
  exact ⟨_, hpull'.seq (hpop.seq (hc'.seq hw))⟩

theorem loop_runs {B width : Nat} (rs : List Nat) (tail : List Bool) (C : List Nat)
    (hv : ∀ v ∈ rs, v < 2 ^ width) (hval : ∀ v ∈ rs, v + 3 ≤ B)
    (hB : LenOK B (start width [] tail (locals rs.reverse) 0 C))
    (hout : tail.length + rs.length * width + 2 ≤ B) :
    ∃ T, Complexity.Runs (LenOK B) (.loop 9 nonEmpty body)
      (start width [] tail (locals rs.reverse) 0 C)
      (start width [] (SequentialStackBinary.pack width rs.reverse ++ tail) [] 0 C) T := by
  induction rs generalizing tail with
  | nil =>
    simpa [SequentialFrontRead.locals, SequentialStackBinary.pack] using
      (show ∃ T, Complexity.Runs (LenOK B) (.loop 9 nonEmpty body) (start width [] tail [] 0 C)
        (start width [] tail [] 0 C) T from
          ⟨1, 1, Nat.le_refl _, .loopF hB (by simp [start, nonEmpty, lastSym])⟩)
  | cons v rs ih =>
    have hin : locals (v :: rs).reverse = locals rs.reverse ++ 2 :: List.replicate v 1 := by
      simp [SequentialFrontRead.locals, List.reverse_cons, List.flatMap_append]
    obtain ⟨T1, hr1⟩ := body_runs tail (locals rs.reverse) C (hv v (by simp))
      (by simpa only [hin] using hB) (hval v (by simp)) (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hout; omega)
    have hnext : LenOK B (start width [] (word width v ++ tail) (locals rs.reverse) 0 C) := by
      obtain ⟨_, _, hx⟩ := hr1
      exact hx.q_end _ (Or.inl rfl)
    obtain ⟨T2, hr2⟩ := ih (tail := word width v ++ tail)
      (fun n hn => hv n (by simp [hn])) (fun n hn => hval n (by simp [hn])) hnext (by
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hout
        simp only [List.length_append, word_length]
        omega)
    have heout : SequentialStackBinary.pack width rs.reverse ++ (word width v ++ tail) =
        SequentialStackBinary.pack width (v :: rs).reverse ++ tail := by
      simp [SequentialStackBinary.pack, List.reverse_cons, List.flatMap_append, List.append_assoc]
    rw [heout] at hr2
    have hc : nonEmpty (lastSym ((start width [] tail (locals (v :: rs).reverse) 0 C) 9)) = true := by
      have hn : (locals (v :: rs).reverse) ≠ [] := by
        intro he
        have hh := congrArg List.length he
        rw [hin] at hh
        simp at hh
      have hsym : lastSym (locals (v :: rs).reverse) ≠ 3 := fun he => hn (lastSym_eq_three.mp he)
      simpa [start, nonEmpty] using hsym
    have hr1' : Complexity.Runs (LenOK B) body (start width [] tail (locals (v :: rs).reverse) 0 C)
        (start width [] (word width v ++ tail) (locals rs.reverse) 0 C) T1 := by
      simpa only [hin] using hr1
    obtain ⟨t1, _, hx1⟩ := hr1'
    obtain ⟨t2, _, hx2⟩ := hr2
    exact ⟨t1 + 1 + t2, t1 + 1 + t2, Nat.le_refl _, .loopC hB hc hx1 hx2⟩

/-- Restore an arbitrary finite local field list. Its values are emitted from
last to first, so prepending the words restores their original order. -/
theorem write_runs {B width held : Nat} (vs : List Nat) (tail : List Bool) (C : List Nat)
    (hv : ∀ v ∈ vs, v < 2 ^ width) (hval : ∀ v ∈ vs, v + 3 ≤ B)
    (hB : LenOK B (start width [] tail (locals vs) held C))
    (hout : tail.length + vs.length * width + 2 ≤ B) :
    ∃ T, Complexity.Runs (LenOK B) writeFront (start width [] tail (locals vs) held C)
      (start width vs tail [] 0 C) T := by
  let L := start width [] tail (locals vs) held C
  have hc := clearP_spec (Q := LenOK B) (i := 3) (L := L) (by
    intro n hn
    apply lenOK_set hB 3
    have hh : (L 3).length + 2 ≤ B := hB 3
    simp only [List.length_take]
    omega)
  have he : L.set 3 [] = start width [] tail (locals vs) 0 C := by
    funext i
    by_cases hi : i = 3 <;> simp_all [L, start, Lists.set]
  rw [he] at hc
  have hnext : LenOK B (start width [] tail (locals vs) 0 C) := by
    obtain ⟨_, _, hx⟩ := hc
    exact hx.q_end _ (Or.inl rfl)
  obtain ⟨T, hr⟩ := loop_runs vs.reverse tail C
    (by simpa using hv) (by simpa using hval) (by simpa using hnext) (by simpa using hout)
  have heout : start width [] (SequentialStackBinary.pack width vs ++ tail) [] 0 C =
      start width vs tail [] 0 C := by
    funext i
    simp [start, SequentialStackBinary.pack]
  simp only [List.reverse_reverse] at hr
  rw [heout] at hr
  exact ⟨_, hc.seq hr⟩

theorem write_tape {B width held : Nat} (vs : List Nat) (tail : List Bool) (C : List Nat)
    (hv : ∀ v ∈ vs, v < 2 ^ width) (hval : ∀ v ∈ vs, v + 3 ≤ B)
    (hB : LenOK B (start width [] tail (locals vs) held C))
    (hout : tail.length + vs.length * width + 2 ≤ B)
    (τ : Tapes 11) (hτ : Rep (start width [] tail (locals vs) held C) τ) :
    ∃ t τ', Exec (TFits B) writeFront.compile τ t (.cont τ') ∧ Rep (start width vs tail [] 0 C) τ' := by
  obtain ⟨_, hr⟩ := write_runs vs tail C hv hval hB hout
  obtain ⟨t, τ', _, he, hr'⟩ := runs_tape hr τ hτ
  exact ⟨t, τ', he, hr'⟩

end Shallot.MacroPeg.CBV.SequentialFrontWrite
