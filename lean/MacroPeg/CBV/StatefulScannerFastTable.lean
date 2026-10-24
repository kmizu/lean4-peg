import MacroPeg.CBV.StatefulScannerStability

/-! Executable frozen tables whose scanner rows use the proved finite-state
run. This avoids re-expanding physical scanner rounds in kernel examples. -/
namespace Shallot.MacroPeg.CBV.StatefulScannerFastTable
open StatefulScanner
open ClockFreezing (Table)

def table {n : Nat} (M : Machine n) (g : MGrammar) (x : List Char) (s : Strategy) : Nat → Table
  | 0 => fun i E => if hi : i<n then
      (List.range (x.length+1)).map (fun p => some (some (run M ⟨i,hi⟩ (sfx x p)).2.length)) else []
  | k+1 => fun i E => if hi : i<n then
      (List.range (x.length+1)).map (fun p => some (some (run M ⟨i,hi⟩ (sfx x p)).2.length))
    else ClockFreezing.step g x s (table M g x s k) i E

private theorem helper_row {n : Nat} (M : Machine n) (g : MGrammar) (x : List Char) (s : Strategy)
    (layout : ∀ q : Fin n, ruleAtM g.rules q.val=some ⟨0,branches 0 (terminal true) (M.arcs q)⟩)
    (q : Fin n) (E : List (List Char)) :
    tblV g x s (x.length+1) q.val E=
      (List.range (x.length+1)).map (fun p => some (some (run M q (sfx x p)).2.length)) := by
  have hl : ∀ q : Fin n, ruleAtM g.rules (0+q.val)=some ⟨0,branches 0 (terminal true) (M.arcs q)⟩ := by
    intro q; simpa only [Nat.zero_add] using layout q
  have hignore := StatefulScannerStability.rows_ignore_environment M (fun _ => true) g 0 hl x s (x.length+1) q E
  simp only [Nat.zero_add] at hignore
  rw [hignore]
  have hlen := StatefulScannerStability.row_length M (fun _ => true) g 0 hl x s (x.length+1) q [] (by omega)
  simp only [Nat.zero_add] at hlen
  apply List.ext_getElem
  · simpa using hlen
  · intro p hp hp'
    have hb : p≤x.length := by rw [hlen] at hp; omega
    have hh := query_eval M (fun _ => true) g 0 hl x s p hb (x.length+1) (by omega) q
    have he : (tblV g x s (x.length+1) q.val [])[p]=some (some (run M q (sfx x p)).2.length) := by
      simpa only [valAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hp,Option.getD_some,if_true,Nat.zero_add] using hh
    simpa only [List.getElem_map,List.getElem_range] using he

/-- The executable table is exactly the frozen table of this actual
installed helper prefix, independently of all following user rows. -/
theorem eq_frozen {n : Nat} (M : Machine n) (g : MGrammar) (x : List Char) (s : Strategy)
    (layout : ∀ q : Fin n, ruleAtM g.rules q.val=some ⟨0,branches 0 (terminal true) (M.arcs q)⟩)
    (k : Nat) : table M g x s k=
      ClockFreezing.frozen g x s (fun i => decide (i<n)) (x.length+1) k := by
  induction k with
  | zero =>
    funext i E
    by_cases hi : i<n
    · simp only [table,dif_pos hi,ClockFreezing.frozen,show decide (i<n)=true from by simp [hi],ite_true]
      exact (helper_row M g x s layout ⟨i,hi⟩ E).symm
    · simp [table,ClockFreezing.frozen,hi]
  | succ k ih =>
    funext i E
    by_cases hi : i<n
    · simp only [table,dif_pos hi,ClockFreezing.frozen,show decide (i<n)=true from by simp [hi],ite_true]
      exact (helper_row M g x s layout ⟨i,hi⟩ E).symm
    · simp [table,ClockFreezing.frozen,hi,ih]

theorem physical {n : Nat} (M : Machine n) (g : MGrammar) (x : List Char) (s : Strategy)
    (layout : ∀ q : Fin n, ruleAtM g.rules q.val=some ⟨0,branches 0 (terminal true) (M.arcs q)⟩)
    (k : Nat) (E : List (List Char)) (e : MExp) (p : Nat) (v : Option Nat)
    (hv : evV g x s (table M g x s k) E e p=some v) :
    evV g x s (tblV g x s (x.length+1+k)) E e p=some v := by
  rw [eq_frozen M g x s layout] at hv
  exact (evV_mono (ClockFreezing.frozen_le_physical g x s _ (x.length+1) k) e p).eq_of_some hv

end Shallot.MacroPeg.CBV.StatefulScannerFastTable
