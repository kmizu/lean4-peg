import MacroPeg.CBV.ScannerAbsorption

namespace Shallot.MacroPeg.CBV.MaskedScannerAbsorption
open NestedScannerArguments (accepts scan scan_eval)
open RecursiveParserStability (Installed)
open ClockFreezing (Table)

def enabled (mask : List Bool) (i : Nat) := mask[i]?.getD false

def Safe (mask : List Bool) (A : List Char) : MExp → Prop
  | .eps | .notP _ => True
  | .chr c => accepts A c=true
  | .lit w => w.all (accepts A)=true
  | .seq a b | .alt a b => Safe mask A a ∧ Safe mask A b
  | .star a => Safe mask A a
  | .call i [] => enabled mask i=true
  | _ => False

def safeCheck (mask : List Bool) (A : List Char) : MExp → Bool
  | .eps | .notP _ => true
  | .chr c => accepts A c
  | .lit w => w.all (accepts A)
  | .seq a b | .alt a b => safeCheck mask A a && safeCheck mask A b
  | .star a => safeCheck mask A a
  | .call i [] => enabled mask i
  | _ => false

theorem safe_checked (mask : List Bool) (A : List Char) : ∀ e, safeCheck mask A e=true → Safe mask A e
  | .eps,_ | .notP _,_ => True.intro
  | .chr _,h | .lit _,h | .call _ [],h => h
  | .seq a b,h | .alt a b,h => ⟨safe_checked mask A a (Bool.and_eq_true_iff.mp h).1,
      safe_checked mask A b (Bool.and_eq_true_iff.mp h).2⟩
  | .star a,h => safe_checked mask A a h
  | .any,h | .range _ _,h | .param _,h | .call _ (_::_),h | .dbg _,h
  | .lam _ _,h | .invoke _ _ _,h | .callParam _ _,h => by cases h

/-- Candidate generation is a finite computation. A separate closure check
validates its output, so soundness does not assume iteration convergence. -/
def prune (bodies : List MExp) (A : List Char) : Nat → List Bool
  | 0 => List.replicate bodies.length true
  | k+1 => bodies.map (safeCheck (prune bodies A k) A)
def mask (bodies : List MExp) (A : List Char) := prune bodies A bodies.length

def Valid (bodies : List MExp) (mask : List Bool) (A : List Char) : Prop :=
  (∀ i, enabled mask i=true → i<bodies.length) ∧
  ∀ i b, bodies[i]?=some b → enabled mask i=true → Safe mask A b

def check (bodies : List MExp) (A : List Char) (e : MExp) : Bool :=
  (decide ((mask bodies A).length=bodies.length) && bodies.zipIdx.all (fun (b,i) =>
    !enabled (mask bodies A) i || safeCheck (mask bodies A) A b)) && safeCheck (mask bodies A) A e

theorem checked (bodies : List MExp) (A : List Char) (e : MExp) (hc : check bodies A e=true) :
    Valid bodies (mask bodies A) A ∧ Safe (mask bodies A) A e := by
  obtain ⟨hh,he⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hlen,hbody⟩ := Bool.and_eq_true_iff.mp hh
  have hlen := of_decide_eq_true hlen
  refine ⟨⟨?_,?_⟩,safe_checked _ _ _ he⟩
  · intro i hi
    have hb : i<(mask bodies A).length := by
      by_cases hn : i<(mask bodies A).length
      · exact hn
      · have hh : (mask bodies A)[i]?=none := List.getElem?_eq_none (by omega)
        simp [enabled,hh] at hi
    omega
  · intro i b hget hi
    have hm : (b,i)∈bodies.zipIdx := List.mem_of_getElem?
      (show bodies.zipIdx[i]?=some (b,i) from by simp [List.getElem?_zipIdx,hget])
    have hh := List.all_eq_true.mp hbody (b,i) hm
    simp only [hi,Bool.not_true,Bool.false_or] at hh
    exact safe_checked _ _ _ hh

def RowsSafe (mask : List Bool) (A x : List Char) (T : Table) : Prop :=
  ∀ i, enabled mask i=true → ∀ p q, p≤x.length → valAt (T i []) p=some (some q) →
    (sfx x p).dropWhile (accepts A)=(sfx x q).dropWhile (accepts A)

theorem evaluator_safe {g : MGrammar} (mask : List Bool)
    (hg : ∀ i, enabled mask i=true → ∃ b, ruleAtM g.rules i=some ⟨0,b⟩) (A x : List Char) (s : Strategy) (T : Table)
    (hRows : RowsSafe mask A x T) (hOk : OkTV x.length T) (E : List (List Char)) :
    ∀ e, Safe mask A e → ∀ p q, p ≤ x.length → evV g x s T E e p = some (some q) →
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
  | .lit w, hw, p, q, hp, hv => ScannerAbsorption.literal_safe x A w hw p q hv
  | .call i [], hi, p, q, hp, hv => by
    obtain ⟨b,hr⟩ := hg i hi
    cases s <;> apply hRows i hi p q hp <;>
      simpa only [evV,hr,evParArgs,evSeqArgs,List.length_nil,ite_true] using hv
  | .seq a b, he, p, q, hp, hv => by
    cases ha : evV g x s T E a p with
    | none => rw [evV_seq_none ha] at hv; cases hv
    | some r => cases r with
      | none => rw [evV_seq_fail ha] at hv; cases hv
      | some j =>
        rw [evV_seq_ok ha] at hv
        exact (evaluator_safe mask hg A x s T hRows hOk E a he.1 p j hp ha).trans
          (evaluator_safe mask hg A x s T hRows hOk E b he.2 j q (evV_ok hOk a p hp j ha) hv)
  | .alt a b, he, p, q, hp, hv => by
    cases ha : evV g x s T E a p with
    | none => rw [evV_alt_none ha] at hv; cases hv
    | some r => cases r with
      | none => rw [evV_alt_fail ha] at hv
                exact evaluator_safe mask hg A x s T hRows hOk E b he.2 p q hp hv
      | some j => rw [evV_alt_ok ha] at hv
                  cases hv
                  exact evaluator_safe mask hg A x s T hRows hOk E a he.1 p q hp ha
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
              exact (evaluator_safe mask hg A x s T hRows hOk E e he p j hp ha).trans
                (ih j hj (by omega) hv)
            · rw [evStar_stuck ha hj] at hv; cases hv
    exact hh p hp hv
  | .any, h, _, _, _, _ | .range _ _, h, _, _, _, _ | .param _, h, _, _, _, _ | .call _ (_::_), h, _, _, _, _
  | .dbg _, h, _, _, _, _ | .lam _ _, h, _, _, _, _ | .callParam _ _, h, _, _, _, _
  | .invoke _ _ _, h, _, _, _, _ => False.elim h

theorem physical_rows {bodies : List MExp} {g : MGrammar} (hg : Installed bodies g)
    (mask : List Bool) (A : List Char) (hv : Valid bodies mask A)
    (x : List Char) (s : Strategy) (k : Nat) : RowsSafe mask A x (tblV g x s k) := by
  have hi : ∀ i, enabled mask i=true → ∃ b, ruleAtM g.rules i=some ⟨0,b⟩ := by
    intro i he
    exact ⟨bodies[i]'(hv.1 i he),hg i _ (List.getElem?_eq_getElem (hv.1 i he))⟩
  induction k with
  | zero => intro i he p q hp hh; cases hh
  | succ k ih =>
    intro i he p q hp hh
    have hib := hv.1 i he
    have hb := List.getElem?_eq_getElem hib
    rw [valAt_tblV_succ (hg i bodies[i] hb) [] hp] at hh
    exact evaluator_safe mask hi A x s _ ih (tblV_ok _ _ _ k) [] bodies[i] (hv.2 i _ hb he) p q hp hh

theorem scan_after_success {bodies : List MExp} {g : MGrammar} (hg : Installed bodies g)
    (mask : List Bool) (A : List Char) (hv : Valid bodies mask A)
    (x : List Char) (s : Strategy) (k : Nat) (E : List (List Char)) (e : MExp)
    (he : Safe mask A e) (p q : Nat) (hp : p≤x.length)
    (hh : evV g x s (tblV g x s k) E e p=some (some q)) :
    evV g x s (tblV g x s k) E (scan A) p=evV g x s (tblV g x s k) E (scan A) q := by
  have hi : ∀ i, enabled mask i=true → ∃ b, ruleAtM g.rules i=some ⟨0,b⟩ := by
    intro i he
    exact ⟨bodies[i]'(hv.1 i he),hg i _ (List.getElem?_eq_getElem (hv.1 i he))⟩
  have hq := evV_ok (tblV_ok _ _ _ k) e p hp q hh
  rw [scan_eval _ _ _ _ _ A p hp,scan_eval _ _ _ _ _ A q hq,
    evaluator_safe mask hi A x s _ (physical_rows hg mask A hv x s k) (tblV_ok _ _ _ k) E e he p q hp hh]

end Shallot.MacroPeg.CBV.MaskedScannerAbsorption
