import Complexity.BinaryWordWrite

/-! Compute the width of a binary field from its unary value. The program uses
four registers and preserves every other register, including the original input. -/
namespace Complexity.BinaryWord

def bitLength (n : Nat) : Nat := if n=0 then 0 else n.log2+1

theorem bitLength_step {n : Nat} (hn : 0 < n) : bitLength n = bitLength (n/2)+1 := by
  by_cases h : 2 ≤ n
  · have hhalf : n/2 ≠ 0 := by omega
    simp only [bitLength,if_neg (Nat.ne_of_gt hn),if_neg hhalf]
    rw [Nat.log2_def n,if_pos h]
  · have he : n=1 := by omega
    subst n
    decide

def widthBody {k : Nat} (a q flag out : Fin k) : LProg k :=
  .seq (digitP a q flag out) (.seq (.pop out) (.push out 1))

def widthP {k : Nat} (a q flag out : Fin k) : LProg k :=
  .loop a nonEmpty (widthBody a q flag out)

private theorem widthBody_runs {k : Nat} {a q flag out : Fin k}
    (hd : [a,q,flag,out].Nodup) {B n w : Nat} {L : Lists k}
    (ha : L a = List.replicate n 1) (hq : L q = []) (hf : L flag = [])
    (ho : L out = List.replicate w 1) (hB : LenOK B L)
    (hcap : n+3 ≤ B) (hout : w+3 ≤ B) :
    ∃ T, Runs (LenOK B) (widthBody a q flag out) L
      ((((L.set a (List.replicate (n/2) 1)).set q []).set flag []).set out
        (List.replicate (w+1) 1)) T := by
  obtain ⟨T,hr⟩ := digit_runs hd ha hq hf hB hcap (by simp [ho]; omega)
  let M := (((L.set a (List.replicate (n/2) 1)).set q []).set flag [])
  let D := M.set out (L out ++ [n%2])
  let A := M.set out (List.replicate w 1)
  let F := M.set out (List.replicate (w+1) 1)
  have hD : LenOK B D := by
    obtain ⟨_,_,he⟩ := hr
    exact he.q_end _ (Or.inl rfl)
  have hpop : D.set out (D out).dropLast = A := by simp [D,A,ho,Lists.set_set_u]
  have hA : LenOK B A := by
    simpa only [D,A,Lists.set_set_u] using lenOK_set hD out (l := List.replicate w 1) (by simp; omega)
  have hp := runs_pop (i := out) hD (by rw [hpop]; exact hA)
  rw [hpop] at hp
  have hF : LenOK B F := by
    simpa only [D,F,Lists.set_set_u] using lenOK_set hD out (l := List.replicate (w+1) 1) (by simp; omega)
  have hpush : A.set out (A out ++ [1]) = F := by
    simp [A,F,Lists.set_set_u,← List.replicate_append_replicate]
  have hh := runs_push (i := out) (e := 1) hA (by rw [hpush]; exact hF)
  rw [hpush] at hh
  exact ⟨_,hr.seq (hp.seq hh)⟩

/-- All intermediate list lengths use the stated capacity. The output may
already hold an initial unary count `w`. -/
theorem width_runs {k : Nat} {a q flag out : Fin k}
    (hd : [a,q,flag,out].Nodup) {B n w : Nat} {L : Lists k}
    (ha : L a = List.replicate n 1) (hq : L q = []) (hf : L flag = [])
    (ho : L out = List.replicate w 1) (hB : LenOK B L)
    (hcap : n+3 ≤ B) (hout : w+bitLength n+2 ≤ B) :
    ∃ T, Runs (LenOK B) (widthP a q flag out) L
      ((((L.set a []).set q []).set flag []).set out
        (List.replicate (w+bitLength n) 1)) T := by
  have haq : a ≠ q := by rintro rfl; simp at hd
  have haf : a ≠ flag := by rintro rfl; simp at hd
  have hao : a ≠ out := by rintro rfl; simp at hd
  have hqf : q ≠ flag := by rintro rfl; simp at hd
  have hqo : q ≠ out := by rintro rfl; simp at hd
  have hfo : flag ≠ out := by rintro rfl; simp at hd
  induction n using Nat.strongRecOn generalizing w L with
  | ind n ih =>
    cases n with
    | zero =>
      have he : (((L.set a []).set q []).set flag []).set out
          (List.replicate (w+bitLength 0) 1) = L := by
        funext i
        by_cases hia : i=a <;> by_cases hiq : i=q <;>
          by_cases hif : i=flag <;> by_cases hio : i=out <;>
          simp_all [Lists.set,bitLength]
      rw [he]
      exact ⟨1,1,Nat.le_refl _,.loopF hB (by simp [ha,nonEmpty,lastSym])⟩
    | succ n =>
      have hbits := bitLength_step (n := n+1) (by omega)
      obtain ⟨T,hr⟩ := widthBody_runs hd ha hq hf ho hB hcap (by omega)
      let M := (((L.set a (List.replicate ((n+1)/2) 1)).set q []).set flag []).set out
        (List.replicate (w+1) 1)
      have hM : LenOK B M := by obtain ⟨_,_,he⟩ := hr; exact he.q_end _ (Or.inl rfl)
      obtain ⟨U,hu⟩ := ih ((n+1)/2) (by omega) (w := w+1) (L := M)
        (by simp [M,Lists.set_ne _ _ hao,Lists.set_ne _ _ haf,Lists.set_ne _ _ haq])
        (by simp [M,Lists.set_ne _ _ hqo,Lists.set_ne _ _ hqf])
        (by simp [M,Lists.set_ne _ _ hfo]) (by simp [M]) hM (by omega) (by omega)
      have he : (((M.set a []).set q []).set flag []).set out
          (List.replicate (w+1+bitLength ((n+1)/2)) 1) =
          (((L.set a []).set q []).set flag []).set out
            (List.replicate (w+bitLength (n+1)) 1) := by
        have hw : w+1+bitLength ((n+1)/2) = w+bitLength (n+1) := by omega
        funext i
        by_cases hia : i=a <;> by_cases hiq : i=q <;>
          by_cases hif : i=flag <;> by_cases hio : i=out <;>
          simp_all [Lists.set,M]
      rw [he] at hu
      obtain ⟨t,_,hx⟩ := hr
      obtain ⟨u,_,hy⟩ := hu
      exact ⟨t+1+u,t+1+u,Nat.le_refl _,.loopC hB (unary_nonEmpty ha) hx hy⟩

/-- For a positive value, starting with an empty output gives exactly the field
width used by the sequential binary codec. -/
theorem positive_width_runs {k : Nat} {a q flag out : Fin k}
    (hd : [a,q,flag,out].Nodup) {B n : Nat} {L : Lists k} (hn : 0 < n)
    (ha : L a = List.replicate n 1) (hq : L q = []) (hf : L flag = [])
    (ho : L out = []) (hB : LenOK B L) (hcap : n+3 ≤ B) :
    ∃ T, Runs (LenOK B) (widthP a q flag out) L
      ((((L.set a []).set q []).set flag []).set out (List.replicate (n.log2+1) 1)) T := by
  have hb : bitLength n = n.log2+1 := by simp [bitLength,Nat.ne_of_gt hn]
  have hl := Nat.log2_le_self n
  simpa only [Nat.zero_add,hb] using width_runs hd ha hq hf
    (w := 0) ho hB hcap (by omega)

/-- The width computation's bound transfers to every intermediate tape state. -/
theorem width_tape {k : Nat} {a q flag out : Fin k}
    (hd : [a,q,flag,out].Nodup) {B n : Nat} {L : Lists k} (hn : 0 < n)
    (ha : L a = List.replicate n 1) (hq : L q = []) (hf : L flag = [])
    (ho : L out = []) (hB : LenOK B L) (hcap : n+3 ≤ B)
    (τ : Tapes k) (hτ : Rep L τ) :
    ∃ t τ', Exec (TFits B) (widthP a q flag out).compile τ t (.cont τ') ∧
      Rep ((((L.set a []).set q []).set flag []).set out (List.replicate (n.log2+1) 1)) τ' := by
  obtain ⟨T,hr⟩ := positive_width_runs hd hn ha hq hf ho hB hcap
  obtain ⟨t,τ',_,he,hrep⟩ := runs_tape hr τ hτ
  exact ⟨t,τ',he,hrep⟩

end Complexity.BinaryWord
