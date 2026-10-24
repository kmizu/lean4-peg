import MacroPeg.CBV.SequentialStepDispatchMachine

/-! Inspect whether a unary field is positive below source-fixed headers.
The complete original control stream is restored before either branch. -/
namespace Shallot.MacroPeg.CBV.SequentialFieldPresenceMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine

def program (saved : Nat) (positive zero : LProg 8) : LProg 8 := .seq (saveMany 2 1 saved)
  (.ite 2 (symIs 1) (.seq (moveAll 1 2) positive) (.seq (moveAll 1 2) zero))

theorem dispatch_runs (saved : List Nat) (n : Nat) (C : List Nat) (positive zero : LProg 8)
    (L M : Lists 8) {B T : Nat} (hctrl : L 2=C ++ unary n ++ blocks saved)
    (hstop : symIs 1 (lastSym C)=false) (h1 : L 1=[]) (hL : LenOK B L)
    (hp : Runs (LenOK B) (if 0<n then positive else zero) L M T) :
    ∃ U, Runs (LenOK B) (program saved.length positive zero) L M U := by
  have hh := hL 2
  rw [hctrl] at hh
  simp only [List.length_append] at hh
  obtain ⟨Ts,hs⟩ := saveMany_runs (src := (2 : Fin 8)) (tmp := 1) (by decide) saved
    (C ++ unary n) L hctrl hL (by simp only [h1,List.length_nil]; omega)
  let N := (L.set 2 (C ++ unary n)).set 1 (blocks saved).reverse
  have heN : (L.set 2 (C ++ unary n)).set 1 (L 1 ++ (blocks saved).reverse)=N := by simp [N,h1]
  rw [heN] at hs
  have hr := moveAll_runs_bounded (src := (1 : Fin 8)) (dst := 2) (by decide) (end_fits hs)
    (by simpa [N,Lists.set] using hh)
  have he : (N.set 2 (N 2 ++ (N 1).reverse)).set 1 []=L := by
    funext j
    by_cases h2 : j=2 <;> by_cases h1j : j=1 <;> simp_all [N,Lists.set,List.append_assoc]
  rw [he] at hr
  have hg : symIs 1 (lastSym (N 2))=decide (0<n) := by
    cases n with
    | zero => simpa [N,Lists.set] using hstop
    | succ n => simp [N,Lists.set,List.replicate_succ',← List.append_assoc,lastSym_append,symIs]
  by_cases hn : 0<n
  · have ht : Runs (LenOK B) positive L M T := by simpa only [if_pos hn] using hp
    exact ⟨_,hs.seq ((hr.seq ht).iteT (end_fits hs) (by simpa [hn] using hg))⟩
  · have ht : Runs (LenOK B) zero L M T := by simpa only [if_neg hn] using hp
    exact ⟨_,hs.seq ((hr.seq ht).iteF (end_fits hs) (by simpa [hn] using hg))⟩

end Shallot.MacroPeg.CBV.SequentialFieldPresenceMachine
