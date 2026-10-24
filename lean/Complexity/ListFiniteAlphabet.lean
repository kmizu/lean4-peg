import Complexity.ListIOSpec

/-! Every fixed list program uses finitely many pushed constants and therefore
compiles over some fixed finite tape alphabet. -/
namespace Complexity

theorem LProg.ConstOK.mono {k E F : Nat} (hEF : E ≤ F) {p : LProg k} (h : p.ConstOK E) :
    p.ConstOK F := by
  induction p with
  | push i e => exact Nat.lt_of_lt_of_le h hEF
  | pop => trivial
  | copy => trivial
  | halt => trivial
  | seq p q ihp ihq => exact ⟨ihp h.1,ihq h.2⟩
  | ite i c p q ihp ihq => exact ⟨ihp h.1,ihq h.2⟩
  | loop i c p ih => exact ih h

theorem LProg.exists_constOK {k : Nat} (p : LProg k) : ∃ E, 2 ≤ E ∧ p.ConstOK E := by
  induction p with
  | push i e => exact ⟨e+2,by omega,by show e < e+2; omega⟩
  | pop => exact ⟨2,Nat.le_refl _,trivial⟩
  | copy => exact ⟨2,Nat.le_refl _,trivial⟩
  | halt => exact ⟨2,Nat.le_refl _,trivial⟩
  | seq p q ihp ihq =>
    obtain ⟨E,hE,hp⟩ := ihp
    obtain ⟨F,hF,hq⟩ := ihq
    exact ⟨E+F,by omega,hp.mono (by omega),hq.mono (by omega)⟩
  | ite i c p q ihp ihq =>
    obtain ⟨E,hE,hp⟩ := ihp
    obtain ⟨F,hF,hq⟩ := ihq
    exact ⟨E+F,by omega,hp.mono (by omega),hq.mono (by omega)⟩
  | loop i c p ih => exact ih

end Complexity
