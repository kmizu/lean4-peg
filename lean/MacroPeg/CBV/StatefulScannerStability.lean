import MacroPeg.CBV.StatefulPairArguments
import MacroPeg.CBV.ClockFreezing

/-! The generated scanner helper prefix stabilizes independently of all
user rules and capture environments. Instantiate physical/frozen cofinality
for the actual combined grammar, not an assumed lexical oracle. -/
namespace Shallot.MacroPeg.CBV.StatefulScannerStability
open StatefulScanner StatefulPairArguments

theorem rows_ignore_environment {n : Nat} (M : Machine n) (finish : Fin n → Bool)
    (g : MGrammar) (base : Nat)
    (layout : ∀ q : Fin n, ruleAtM g.rules (base+q.val) =
      some ⟨0,branches base (terminal (finish q)) (M.arcs q)⟩)
    (x : List Char) (s : Strategy) (clock : Nat) (q : Fin n) (E : List (List Char)) :
    tblV g x s clock (base+q.val) E = tblV g x s clock (base+q.val) [] := by
  cases clock with
  | zero => rfl
  | succ clock =>
    simp only [tblV,layout]
    apply List.map_congr_left
    intro p hp
    rw [branches_eval _ E base (fun q => ⟨_,layout q,rfl⟩),
      branches_eval _ [] base (fun q => ⟨_,layout q,rfl⟩)]
    cases finish q <;> cases sfx x p <;> rfl

theorem row_length {n : Nat} (M : Machine n) (finish : Fin n → Bool)
    (g : MGrammar) (base : Nat)
    (layout : ∀ q : Fin n, ruleAtM g.rules (base+q.val) =
      some ⟨0,branches base (terminal (finish q)) (M.arcs q)⟩)
    (x : List Char) (s : Strategy) (clock : Nat) (q : Fin n) (E : List (List Char))
    (hc : 0<clock) : (tblV g x s clock (base+q.val) E).length = x.length+1 := by
  cases clock with
  | zero => omega
  | succ clock => simp [tblV,layout]

/-- Every scanner row, including all capture environments and all failure
positions, is already stable after input length plus one table rounds. -/
theorem rows_stable {n : Nat} (M : Machine n) (finish : Fin n → Bool)
    (g : MGrammar) (base : Nat)
    (layout : ∀ q : Fin n, ruleAtM g.rules (base+q.val) =
      some ⟨0,branches base (terminal (finish q)) (M.arcs q)⟩)
    (x : List Char) (s : Strategy) (k l : Nat) (hk : x.length+1 ≤ k) (hl : x.length+1 ≤ l)
    (q : Fin n) (E : List (List Char)) :
    tblV g x s k (base+q.val) E = tblV g x s l (base+q.val) E := by
  rw [rows_ignore_environment M finish g base layout x s k q E,
    rows_ignore_environment M finish g base layout x s l q E]
  apply List.ext_getElem
  · rw [row_length M finish g base layout x s k q [] (by omega),
      row_length M finish g base layout x s l q [] (by omega)]
  · intro p hpk hpl
    have hp : p ≤ x.length := by
      rw [row_length M finish g base layout x s k q [] (by omega)] at hpk
      omega
    have he := (query_eval M finish g base layout x s p hp k (by omega) q).trans
      (query_eval M finish g base layout x s p hp l (by omega) q).symm
    simpa only [valAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hpk,
      List.getElem?_eq_getElem hpl,Option.getD_some] using he

def helperCount (n m : Nat) : Nat := commonSize n m+n+m
def helpers (n m : Nat) (i : Nat) : Bool := decide (i < helperCount n m)

/-- This discharges the freezing premise on the actual installed prefix,
for arbitrary recursive user tails and all captured argument environments. -/
theorem helpers_stable {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (tail : List MRule) (x : List Char) (s : Strategy) :
    ClockFreezing.StableRows (grammar A B hm tail) x s (helpers n m) (x.length+1) := by
  intro k i hi E
  have hbound : i < commonSize n m+n+m := by simpa only [helpers,helperCount,decide_eq_true_eq] using hi
  by_cases hcommon : i < commonSize n m
  · have hN : 0 < n*m := by
      by_cases hz : n*m = 0
      · simp [commonSize,hz] at hcommon
      · omega
    let target : Fin (n*m) := ⟨i/(n*m),(Nat.div_lt_iff_lt_mul hN).mpr hcommon⟩
    let q : Fin (n*m) := ⟨i%(n*m),Nat.mod_lt _ hN⟩
    have haddr : target.val*(n*m)+q.val = i := by
      simpa only [target,q,Nat.mul_comm] using Nat.div_add_mod i (n*m)
    have hh := rows_stable (StatefulScannerProduct.product A B hm) (fun r => decide (r=target))
      (grammar A B hm tail) (target.val*(n*m)) (fun q => common_rule A B hm tail q target)
      x s (x.length+1+k) (x.length+1) (by omega) (Nat.le_refl _) q E
    simpa only [haddr] using hh
  · by_cases hleft : i < commonSize n m+n
    · let q : Fin n := ⟨i-commonSize n m,by omega⟩
      have haddr : leftBase n m+q.val = i := by dsimp [leftBase,q]; omega
      have hh := rows_stable A (fun _ => true) (grammar A B hm tail) (leftBase n m)
        (left_rule A B hm tail) x s (x.length+1+k) (x.length+1) (by omega) (Nat.le_refl _) q E
      simpa only [haddr] using hh
    · let q : Fin m := ⟨i-(commonSize n m+n),by omega⟩
      have haddr : rightBase n m+q.val = i := by dsimp [rightBase,q]; omega
      have hh := rows_stable B (fun _ => true) (grammar A B hm tail) (rightBase n m)
        (right_rule A B hm tail) x s (x.length+1+k) (x.length+1) (by omega) (Nat.le_refl _) q E
      simpa only [haddr] using hh

abbrev frozen {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (tail : List MRule) (x : List Char) (s : Strategy) (k : Nat) : ClockFreezing.Table :=
  ClockFreezing.frozen (grammar A B hm tail) x s (helpers n m) (x.length+1) k

theorem frozen_le_physical {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (tail : List MRule) (x : List Char) (s : Strategy) (k : Nat) :
    TLeV (frozen A B hm tail x s k) (tblV (grammar A B hm tail) x s (x.length+1+k)) :=
  ClockFreezing.frozen_le_physical _ _ _ _ _ _

theorem physical_le_frozen {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (tail : List MRule) (x : List Char) (s : Strategy) (k : Nat) :
    TLeV (tblV (grammar A B hm tail) x s k) (frozen A B hm tail x s k) :=
  ClockFreezing.physical_le_frozen _ _ _ _ _ (helpers_stable A B hm tail x s) k

theorem defined_iff {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (tail : List MRule) (x : List Char) (s : Strategy) (E : List (List Char)) (e : MExp)
    (p : Nat) (v : Option Nat) :
    (∃ k, evV (grammar A B hm tail) x s (frozen A B hm tail x s k) E e p = some v) ↔
      ∃ k, evV (grammar A B hm tail) x s (tblV (grammar A B hm tail) x s k) E e p = some v :=
  ClockFreezing.defined_iff _ _ _ _ _ (helpers_stable A B hm tail x s) E e p v

theorem observations_iff {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (tail : List MRule) (ht : ∀ r ∈ tail, r.body.FirstOrder) (x : List Char)
    (s : Strategy) (hs : s ≠ .callByName) (e : MExp) (he : e.FirstOrder) (r : Option (List Char)) :
    SObs (grammar A B hm tail) s e x r ↔
      ∃ k v, evV (grammar A B hm tail) x s (frozen A B hm tail x s k) [] e x.length = some v ∧
        v.map (sfx x) = r :=
  ClockFreezing.observations_iff (grammar_firstOrder A B hm tail ht) x s hs _ _
    (helpers_stable A B hm tail x s) e he r

end Shallot.MacroPeg.CBV.StatefulScannerStability
