import MacroPeg.CBV.SequentialWordInputMachine

/-! Test a unary field against a source-fixed bound, restoring the field
before entering either branch. The field itself has no fixed upper bound. -/
namespace Shallot.MacroPeg.CBV.SequentialCountGuardMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine
open SequentialCaptureSpliceMachine (moveLast_runs)

def program (yes no : LProg 8) : Nat → LProg 8
  | 0 => .seq (moveAll 1 2) yes
  | fuel+1 => .ite 2 (symIs 1)
      (.seq (moveTop 2 1) (program yes no fuel)) (.seq (moveAll 1 2) no)

private def restored (L : Lists 8) (C : List Nat) (n d : Nat) : Lists 8 :=
  (L.set 2 (C ++ unary (n+d))).set 1 []

private theorem restore_runs (C : List Nat) (n d : Nat) (L : Lists 8) {B : Nat}
    (h2 : L 2=C ++ unary n) (h1 : L 1=unary d) (hL : LenOK B L)
    (hcap : C.length+n+d+2 ≤ B) :
    ∃ T, Runs (LenOK B) (moveAll 1 2) L (restored L C n d) T := by
  have hr := moveAll_runs_bounded (src := (1 : Fin 8)) (dst := 2) (by decide) hL (by
    simp only [h2,h1,List.length_append,List.length_replicate]; omega)
  have he : (L.set 2 (L 2 ++ (L 1).reverse)).set 1 [] = restored L C n d := by
    simp [restored,h2,h1,List.replicate_append_replicate,List.append_assoc]
  rw [he] at hr
  exact ⟨_,hr⟩

private theorem probe_runs (yes no : LProg 8) (fuel n d : Nat) (C : List Nat)
    (L M : Lists 8) {B T : Nat} (h2 : L 2=C ++ unary n) (h1 : L 1=unary d)
    (hstop : symIs 1 (lastSym C)=false) (hL : LenOK B L) (hcap : C.length+n+d+2 ≤ B)
    (hp : Runs (LenOK B) (if fuel≤n then yes else no) (restored L C n d) M T) :
    ∃ U, Runs (LenOK B) (program yes no fuel) L M U := by
  induction fuel generalizing n d L with
  | zero =>
    obtain ⟨Tr,hr⟩ := restore_runs C n d L h2 h1 hL hcap
    exact ⟨_,hr.seq (by simpa using hp)⟩
  | succ fuel ih => cases n with
    | zero =>
      obtain ⟨Tr,hr⟩ := restore_runs C 0 d L h2 h1 hL hcap
      have hc : symIs 1 (lastSym (L 2))=false := by simpa [h2] using hstop
      exact ⟨_,(hr.seq (by simpa using hp)).iteF hL hc⟩
    | succ n =>
      have hs : L 2=(C ++ unary n) ++ [1] := by simpa [List.replicate_succ',List.append_assoc] using h2
      have hr := moveLast_runs (by decide : (2 : Fin 8) ≠ 1) (C ++ unary n) 1 L hs hL
        (by simp only [h1,List.length_replicate]; omega)
      let N := (L.set 2 (C ++ unary n)).set 1 (unary (d+1))
      have heN : (L.set 2 (C ++ unary n)).set 1 (L 1 ++ [1])=N := by
        simp [N,h1,List.replicate_succ']
      rw [heN] at hr
      have heR : restored N C n (d+1)=restored L C (n+1) d := by
        funext j
        by_cases h2j : j=2 <;> by_cases h1j : j=1 <;>
          simp [restored,N,Lists.set,h2j,h1j,Nat.add_comm,Nat.add_left_comm]
      have hb : Runs (LenOK B) (if fuel≤n then yes else no) (restored N C n (d+1)) M T := by
        rw [heR]
        simpa only [Nat.succ_le_succ_iff] using hp
      obtain ⟨Ti,hi⟩ := ih n (d+1) N rfl rfl (end_fits hr) (by omega) hb
      have hc : symIs 1 (lastSym (L 2))=true := by rw [hs,lastSym_append]; rfl
      exact ⟨_,(hr.seq hi).iteT hL hc⟩

theorem guard_runs (yes no : LProg 8) (fuel n : Nat) (C : List Nat)
    (L M : Lists 8) {B T : Nat} (h2 : L 2=C ++ unary n) (h1 : L 1=[])
    (hstop : symIs 1 (lastSym C)=false) (hL : LenOK B L)
    (hp : Runs (LenOK B) (if fuel≤n then yes else no) L M T) :
    ∃ U, Runs (LenOK B) (program yes no fuel) L M U := by
  have he : restored L C n 0 = L := by
    simp [restored,Nat.add_zero,← h2,← h1,Lists.set_get_self]
  have hc := hL 2
  rw [h2] at hc
  simp only [List.length_append,List.length_replicate] at hc
  exact probe_runs yes no fuel n 0 C L M h2 (by simpa using h1) hstop hL (by omega) (by simpa [he] using hp)

theorem constOK (yes no : LProg 8) (fuel E : Nat) (hy : yes.ConstOK E) (hn : no.ConstOK E) :
    (program yes no fuel).ConstOK E := by
  induction fuel <;> simp_all [program,moveAll,moveTop,LProg.ConstOK]

end Shallot.MacroPeg.CBV.SequentialCountGuardMachine
