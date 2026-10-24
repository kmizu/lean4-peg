import MacroPeg.CBV.RecursiveParserStability

/-! Argument parsers may inspect retained parameters as well as call an
independent recursive helper component. Actual helper row agreement suffices
for their complete partial evaluation to agree under the same environment. -/
namespace Shallot.MacroPeg.CBV.HelperArgument
open ClockFreezing (Table)
open RecursiveParserStability (Installed)

def Syntax (n : Nat) : MExp → Prop
  | .call i [] => i<n
  | .seq a b | .alt a b => Syntax n a ∧ Syntax n b
  | .star a | .notP a => Syntax n a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => True
  | _ => False

theorem firstOrder (n : Nat) : ∀ e, Syntax n e → e.FirstOrder
  | .call _ [], _ => trivial
  | .seq a b, h | .alt a b, h => ⟨firstOrder n a h.1,firstOrder n b h.2⟩
  | .star a, h | .notP a, h => firstOrder n a h
  | .param _, _ | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
  | .call _ (_::_), h | .dbg _, h | .lam _ _, h
  | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem eval_eq {bodies : List MExp} {g h : MGrammar}
    (hg : Installed bodies g) (hh : Installed bodies h) (x : List Char) (s t : Strategy)
    (T U : Table) (hOk : OkTV x.length T)
    (hRows : ∀ i, i<bodies.length → ∀ p, p ≤ x.length → valAt (T i []) p = valAt (U i []) p)
    (E : List (List Char)) : ∀ e, Syntax bodies.length e → ∀ p, p ≤ x.length →
      evV g x s T E e p = evV h x t U E e p
  | .call i [], hi, p, hp => by
    have hr := List.getElem?_eq_getElem hi
    have hgr := hg i bodies[i] hr
    have hhr := hh i bodies[i] hr
    cases s <;> cases t <;> simpa only [evV,hgr,hhr,evParArgs,evSeqArgs,List.length_nil,ite_true] using hRows i hi p hp
  | .seq a b, he, p, hp => by
    have hh' := eval_eq hg hh x s t T U hOk hRows E a he.1 p hp
    cases hv : evV g x s T E a p with
    | none => rw [evV_seq_none hv,evV_seq_none (hh'.symm.trans hv)]
    | some r => cases r with
      | none => rw [evV_seq_fail hv,evV_seq_fail (hh'.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (hh'.symm.trans hv)]
        exact eval_eq hg hh x s t T U hOk hRows E b he.2 q (evV_ok hOk a p hp q hv)
  | .alt a b, he, p, hp => by
    have hh' := eval_eq hg hh x s t T U hOk hRows E a he.1 p hp
    cases hv : evV g x s T E a p with
    | none => rw [evV_alt_none hv,evV_alt_none (hh'.symm.trans hv)]
    | some r => cases r with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (hh'.symm.trans hv)]
        exact eval_eq hg hh x s t T U hOk hRows E b he.2 p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (hh'.symm.trans hv)]
  | .star a, he, p, hp => by
    rw [evV_star,evV_star]
    exact evStar_congr p (fun q hq => eval_eq hg hh x s t T U hOk hRows E a he q (by omega))
  | .notP a, he, p, hp => by simp only [evV]; rw [eval_eq hg hh x s t T U hOk hRows E a he p hp]
  | .param _, _, _, _ | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _ | .range _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .call _ (_::_), he, _, _ | .dbg _, he, _, _ | .lam _ _, he, _, _
  | .callParam _ _, he, _, _ | .invoke _ _ _, he, _, _ => False.elim he

end Shallot.MacroPeg.CBV.HelperArgument
