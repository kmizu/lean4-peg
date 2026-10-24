import Complexity.UnarySpec

/-! A fixed affine function of a runtime list length. The source and temporary
register are restored, and every intermediate list satisfies the given capacity. -/
namespace Complexity

def affineP {k : Nat} (src dst tmp : Fin k) (A b : Nat) : LProg k :=
  .seq (repeatP src (copyLenP src dst tmp) A) (repeatP src (.push dst 1) b)

theorem affine_runs {k : Nat} {src dst tmp : Fin k}
    (hd : [src,dst,tmp].Nodup) (A b : Nat) {B : Nat} {L : Lists k}
    (htmp : L tmp = []) (hL : LenOK B L)
    (hcap : (L dst).length+A*(L src).length+b+2 ≤ B) :
    Runs (LenOK B) (affineP src dst tmp A b) L
      (L.set dst (L dst ++ List.replicate (A*(L src).length+b) 1))
      ((A*(8*((L src).length+1))+1)+(b+1)) := by
  have hsd : src ≠ dst := by rintro rfl; simp at hd
  have htd : tmp ≠ dst := by rintro rfl; simp at hd
  let F := fun j => L.set dst (L dst ++ List.replicate (j*(L src).length) 1)
  have hF : ∀ j, j ≤ A → LenOK B (F j) := by
    intro j hj
    have hh := Nat.mul_le_mul_right (L src).length hj
    exact lenOK_set hL dst (by simp; omega)
  have hcopy := repeat_spec (Q := LenOK B) (i := src)
    (p := copyLenP src dst tmp) F (8*((L src).length+1)) A (by
      intro j hj
      have hh := Nat.mul_le_mul_right (L src).length (show j+1 ≤ A by omega)
      simp only [Nat.add_mul,Nat.one_mul] at hh
      have hsrc : F j src = L src := by simp [F,Lists.set_ne _ _ hsd]
      have ht : F j tmp = [] := by simp [F,Lists.set_ne _ _ htd,htmp]
      have hr := copyLen_spec hd ht (hF j (by omega)) (by simp [F,hsrc]; omega)
      simpa [F,hsrc,Lists.set_set_u,List.append_assoc,← List.replicate_append_replicate,
        Nat.add_mul,Nat.one_mul] using hr) (hF A (Nat.le_refl _))
  have hF0 : F 0 = L := by simp [F,Lists.set_get_self]
  rw [hF0] at hcopy
  let G := fun j => L.set dst (L dst ++ List.replicate (A*(L src).length+j) 1)
  have hG : ∀ j, j ≤ b → LenOK B (G j) := by
    intro j hj
    exact lenOK_set hL dst (by simp; omega)
  have hpush := repeat_spec (Q := LenOK B) (i := src) (p := .push dst 1) G 1 b (by
    intro j hj
    have he : (G j).set dst (G j dst ++ [1]) = G (j+1) := by
      simp [G,Lists.set_set_u,List.append_assoc,← List.replicate_append_replicate]
    have hr := runs_push (i := dst) (e := 1) (hG j (by omega)) (by rw [he]; exact hG (j+1) (by omega))
    rwa [he] at hr) (hG b (Nat.le_refl _))
  have hG0 : G 0 = F A := by simp [G,F]
  rw [hG0] at hpush
  simpa only [Nat.mul_one,affineP,G] using hcopy.seq hpush

end Complexity
