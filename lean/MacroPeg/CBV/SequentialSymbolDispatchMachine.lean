import MacroPeg.CBV.SequentialScopePackedMachine

/-! Compare two runtime symbols by a fixed finite-alphabet decision tree.
The symbols themselves are not program parameters and no tape is changed
before the selected branch. -/
namespace Shallot.MacroPeg.CBV.SequentialSymbolDispatchMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine
variable {k : Nat}

def program (src dst : Fin k) (same different : LProg k) : Nat → LProg k
  | 0 => different
  | bound+1 => .ite src (symIs bound) (.ite dst (symIs bound) same different)
      (program src dst same different bound)

theorem dispatch_runs (src dst : Fin k) (same different : LProg k) (bound value : Nat)
    (hv : value < bound) (L M : Lists k) {B T : Nat} (hsrc : lastSym (L src) = value+4)
    (hL : LenOK B L) (hp : Runs (LenOK B) (.ite dst (symIs value) same different) L M T) :
    ∃ U, Runs (LenOK B) (program src dst same different bound) L M U := by
  induction bound with
  | zero => omega
  | succ bound ih =>
    by_cases he : value=bound
    · subst value
      exact ⟨_,hp.iteT hL (by simp [hsrc,symIs])⟩
    · have hn : value < bound := by omega
      obtain ⟨U,hu⟩ := ih hn
      exact ⟨_,hu.iteF hL (by simp [hsrc,symIs,he])⟩

theorem compare_runs (src dst : Fin k) (same different : LProg k) (bound a b : Nat)
    (ha : a < bound) (L M : Lists k) {B T : Nat}
    (hsrc : lastSym (L src)=a+4) (hdst : lastSym (L dst)=b+4) (hL : LenOK B L)
    (hp : Runs (LenOK B) (if a=b then same else different) L M T) :
    ∃ U, Runs (LenOK B) (program src dst same different bound) L M U := by
  have ht : ∃ U, Runs (LenOK B) (.ite dst (symIs a) same different) L M U := by
    by_cases he : a=b
    · have hh : Runs (LenOK B) same L M T := by simpa only [if_pos he] using hp
      exact ⟨_,hh.iteT hL (by simp [hdst,symIs,he])⟩
    · have hh : Runs (LenOK B) different L M T := by simpa only [if_neg he] using hp
      exact ⟨_,hh.iteF hL (by simp [hdst,symIs,Ne.symm he])⟩
  obtain ⟨U,hu⟩ := ht
  exact dispatch_runs src dst same different bound a ha L M hsrc hL hu

theorem constOK (src dst : Fin k) (same different : LProg k) (bound E : Nat)
    (hs : same.ConstOK E) (hd : different.ConstOK E) : (program src dst same different bound).ConstOK E := by
  induction bound with
  | zero => exact hd
  | succ n ih => exact ⟨⟨hs,hd⟩,ih⟩

end Shallot.MacroPeg.CBV.SequentialSymbolDispatchMachine
