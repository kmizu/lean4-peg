import MacroPeg.CBV.RecursiveParserStability

/-! Recursive parsers whose successful consumption is absorbed by a later
scanner. The condition is syntactic and permits arbitrary negative queries. -/
namespace Shallot.MacroPeg.CBV.ScannerAbsorption
open NestedScannerArguments (accepts scan scan_eval)
open RecursiveParserStability (Installed)
open ClockFreezing (Table)

def Safe (n : Nat) (A : List Char) : MExp → Prop
  | .eps | .notP _ => True
  | .chr c => accepts A c = true
  | .lit w => w.all (accepts A) = true
  | .seq a b | .alt a b => Safe n A a ∧ Safe n A b
  | .star a => Safe n A a
  | .call i [] => i<n
  | _ => False

def RowsSafe (n : Nat) (A : List Char) (x : List Char) (T : Table) : Prop :=
  ∀ i, i<n → ∀ p q, p ≤ x.length → valAt (T i []) p = some (some q) →
    (sfx x p).dropWhile (accepts A) = (sfx x q).dropWhile (accepts A)

theorem dropWhile_append (A : List Char) : ∀ (w : List Char), w.all (accepts A) = true → ∀ (rest : List Char),
    (w++rest).dropWhile (accepts A) = rest.dropWhile (accepts A)
  | [], _, _ => rfl
  | c::w, h, rest => by
    simp only [List.all_cons,Bool.and_eq_true] at h
    simpa only [List.cons_append,List.dropWhile_cons,h.1,if_true] using dropWhile_append A w h.2 rest

theorem literal_safe (x A w : List Char) (hw : w.all (accepts A) = true) (p q : Nat)
    (hv : (match Shallot.stripPrefix? w (sfx x p) with
      | some rest => some (some rest.length) | none => some none) = some (some q)) :
    (sfx x p).dropWhile (accepts A) = (sfx x q).dropWhile (accepts A) := by
  cases hs : Shallot.stripPrefix? w (sfx x p) with
  | none => simp only [hs] at hv; cases hv
  | some rest =>
    simp only [hs,Option.some.injEq] at hv
    subst q
    have hh := (CBVtoCBN.stripPrefix_exact _ _ _).mp hs
    have hr : sfx x rest.length = rest :=
      sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨w,hh⟩).choose_spec
    rw [hh,dropWhile_append A w hw,hr]

theorem evaluator_safe {bodies : List MExp} {g : MGrammar}
    (hg : Installed bodies g) (A x : List Char) (s : Strategy) (T : Table)
    (hRows : RowsSafe bodies.length A x T) (hOk : OkTV x.length T) (E : List (List Char)) :
    ∀ e, Safe bodies.length A e → ∀ p q, p ≤ x.length → evV g x s T E e p = some (some q) →
      (sfx x p).dropWhile (accepts A) = (sfx x q).dropWhile (accepts A)
  | .eps, _, p, q, hp, hv => by cases hv; rfl
  | .chr c, hc, p, q, hp, hv => by
    simp only [evV] at hv
    cases hs : sfx x p with
    | nil => simp only [hs] at hv; cases hv
    | cons d rest =>
      simp only [hs] at hv
      split at hv
      next hd =>
        have hcd : c=d := Char.toNat_inj.mp (by simpa only [Shallot.beqChar,beq_iff_eq] using hd)
        subst d
        cases hv
        have hr : sfx x rest.length = rest :=
          sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨[c],hs⟩).choose_spec
        change (c::rest).dropWhile (accepts A) = (sfx x rest.length).dropWhile (accepts A)
        rw [hr]
        simp only [List.dropWhile_cons,show accepts A c = true from hc,if_true]
      next => cases hv
  | .lit w, hw, p, q, hp, hv => literal_safe x A w hw p q hv
  | .call i [], hi, p, q, hp, hv => by
    have hr := hg i bodies[i] (List.getElem?_eq_getElem hi)
    cases s <;> apply hRows i hi p q hp <;>
      simpa only [evV,hr,evParArgs,evSeqArgs,List.length_nil,ite_true] using hv
  | .seq a b, he, p, q, hp, hv => by
    cases ha : evV g x s T E a p with
    | none => rw [evV_seq_none ha] at hv; cases hv
    | some r => cases r with
      | none => rw [evV_seq_fail ha] at hv; cases hv
      | some j =>
        rw [evV_seq_ok ha] at hv
        exact (evaluator_safe hg A x s T hRows hOk E a he.1 p j hp ha).trans
          (evaluator_safe hg A x s T hRows hOk E b he.2 j q (evV_ok hOk a p hp j ha) hv)
  | .alt a b, he, p, q, hp, hv => by
    cases ha : evV g x s T E a p with
    | none => rw [evV_alt_none ha] at hv; cases hv
    | some r => cases r with
      | none => rw [evV_alt_fail ha] at hv
                exact evaluator_safe hg A x s T hRows hOk E b he.2 p q hp hv
      | some j => rw [evV_alt_ok ha] at hv
                  cases hv
                  exact evaluator_safe hg A x s T hRows hOk E a he.1 p q hp ha
  | .notP e, _, p, q, hp, hv => by
    cases he : evV g x s T E e p with
    | none => simp only [evV,he] at hv; cases hv
    | some r => cases r with
      | none => simp only [evV,he,Option.some.injEq] at hv; subst q; rfl
      | some j => simp only [evV,he] at hv; cases hv
  | .star e, he, p, q, hp, hv => by
    have hh : ∀ p, p ≤ x.length → evStar (fun z => evV g x s T E e z) p = some (some q) →
        (sfx x p).dropWhile (accepts A) = (sfx x q).dropWhile (accepts A) := by
      intro p
      induction p using Nat.strongRecOn with
      | ind p ih =>
        intro hp hv
        cases ha : evV g x s T E e p with
        | none => rw [evStar_none ha] at hv; cases hv
        | some r => cases r with
          | none => rw [evStar_fail ha] at hv; cases hv; rfl
          | some j =>
            by_cases hj : j<p
            · rw [evStar_ok ha hj] at hv
              exact (evaluator_safe hg A x s T hRows hOk E e he p j hp ha).trans
                (ih j hj (by omega) hv)
            · rw [evStar_stuck ha hj] at hv; cases hv
    exact hh p hp hv
  | .any, h, _, _, _, _ | .range _ _, h, _, _, _, _ | .param _, h, _, _, _, _ | .call _ (_::_), h, _, _, _, _
  | .dbg _, h, _, _, _, _ | .lam _ _, h, _, _, _, _ | .callParam _ _, h, _, _, _, _
  | .invoke _ _ _, h, _, _, _, _ => False.elim h

theorem physical_rows_safe {bodies : List MExp} {g : MGrammar}
    (hg : Installed bodies g) (A : List Char) (hf : ∀ e ∈ bodies, Safe bodies.length A e)
    (x : List Char) (s : Strategy) (k : Nat) : RowsSafe bodies.length A x (tblV g x s k) := by
  induction k with
  | zero => intro i hi p q hp hv; cases hv
  | succ k ih =>
    intro i hi p q hp hv
    rw [valAt_tblV_succ (hg i bodies[i] (List.getElem?_eq_getElem hi)) [] hp] at hv
    exact evaluator_safe hg A x s _ ih (tblV_ok _ _ _ k) [] bodies[i]
      (hf _ (List.getElem_mem hi)) p q hp hv

theorem frozen_rows_safe {bodies : List MExp} {g : MGrammar}
    (hg : Installed bodies g) (A : List Char) (hf : ∀ e ∈ bodies, Safe bodies.length A e)
    (x : List Char) (s : Strategy) (k : Nat) :
    RowsSafe bodies.length A x (RecursiveParserStability.frozen bodies g x s k) := by
  intro i hi p q hp hv
  rw [RecursiveParserStability.frozen,ClockFreezing.frozen_rows _ _ _ _ _ _ i (by simp [RecursiveParserStability.pick,hi])] at hv
  exact physical_rows_safe hg A hf x s (RecursiveParserStability.floor bodies x) i hi p q hp hv

/-- A real successful recursive capture can be absorbed by the scanner.
The parser may stop before that scanner and may have unbounded recursion. -/
theorem scan_after_success {bodies : List MExp} {g : MGrammar}
    (hg : Installed bodies g) (A : List Char) (hf : ∀ e ∈ bodies, Safe bodies.length A e)
    (x : List Char) (s : Strategy) (k : Nat) (E : List (List Char)) (e : MExp)
    (he : Safe bodies.length A e) (p q : Nat) (hp : p ≤ x.length)
    (hv : evV g x s (tblV g x s k) E e p = some (some q)) :
    evV g x s (tblV g x s k) E (scan A) p = evV g x s (tblV g x s k) E (scan A) q := by
  have hq := evV_ok (tblV_ok _ _ _ k) e p hp q hv
  rw [scan_eval _ _ _ _ _ A p hp,scan_eval _ _ _ _ _ A q hq,
    evaluator_safe hg A x s _ (physical_rows_safe hg A hf x s k) (tblV_ok _ _ _ k) E e he p q hp hv]

end Shallot.MacroPeg.CBV.ScannerAbsorption
