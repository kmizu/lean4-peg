import MacroPeg.CBV.SequentialTotalAtoms
import MacroPeg.CBV.SequentialTotalCalls

namespace Shallot.MacroPeg.CBV.SequentialTotalExpression
open SequentialTotalSyntax SequentialTotalControl SequentialTotalArguments SequentialTotalCalls

mutual
  theorem expression (g h : MGrammar) (x : List Char) (T U : SequentialClock.Table)
      (E : List (List Char)) (fuel p : Nat) (hp : p≤x.length)
      (hd : SequentialClock.Descending T) (rows : CallRows g h x T U E fuel p)
      (full : ∀ e, e.FirstOrder → ∀ q, q<p →
        Realizes h x U E (compile g g.rules.length e) q (evV g x .callByValueSeq T E e q)) : ∀ e, e.FirstOrder →
      Realizes h x U E (compile g fuel e) p (evV g x .callByValueSeq T E e p)
    | .eps,_ => SequentialTotalAtoms.epsilon_correct
    | .any,_ => SequentialTotalAtoms.any_correct hp
    | .chr c,_ => SequentialTotalAtoms.char_correct c hp
    | .range a b,_ => SequentialTotalAtoms.range_correct a b hp
    | .lit w,_ => SequentialTotalAtoms.literal_correct w hp
    | .param i,_ => SequentialTotalAtoms.parameter_correct i hp
    | .call i args,he =>
      call_correct hd (arguments g h x T U E fuel p hp hd rows full args he) rows
    | .seq a b,he => by
      change Realizes h x U E (seqForms (compile g fuel a) (compile g fuel b)
        (compile g g.rules.length b)) p
          (seqResult (evV g x .callByValueSeq T E a p) (fun q => evV g x .callByValueSeq T E b q))
      exact seq_correct _ _ _ _ _
        (expression g h x T U E fuel p hp hd rows full a he.1)
        (expression g h x T U E fuel p hp hd rows full b he.2)
        (full b he.2)
        (SequentialClock.expression_descending hd E a p)
        (by intro q r hq; exact SequentialClock.expression_descending hd E b q r)
    | .alt a b,he => by
      exact alt_correct _ _ _ _
        (expression g h x T U E fuel p hp hd rows full a he.1)
        (expression g h x T U E fuel p hp hd rows full b he.2)
    | .notP a,he => by
      have hn := not_correct _ _ (expression g h x T U E fuel p hp hd rows full a he)
      cases hv : evV g x .callByValueSeq T E a p with
      | none => simpa only [compile,evV,hv,notResult] using hn
      | some v => cases v <;> simpa only [compile,evV,hv,notResult] using hn
    | .star a,he => by
      exact star_correct _ _ _ (expression g h x T U E fuel p hp hd rows full a he)
        (full a he) (by intro q r hq; exact SequentialClock.expression_descending hd E a q r)
    | .dbg _,he | .lam _ _,he | .callParam _ _,he | .invoke _ _ _,he => False.elim he

  theorem arguments (g h : MGrammar) (x : List Char) (T U : SequentialClock.Table)
      (E : List (List Char)) (fuel p : Nat) (hp : p≤x.length)
      (hd : SequentialClock.Descending T) (rows : CallRows g h x T U E fuel p)
      (full : ∀ e, e.FirstOrder → ∀ q, q<p →
        Realizes h x U E (compile g g.rules.length e) q (evV g x .callByValueSeq T E e q)) : ∀ args, MExp.FirstOrderArgs args →
      Entries g h x T U E p args (compileArgs g fuel args)
    | [],_ => .nil
    | a::args,he => .cons
      ⟨expression g h x T U E fuel p hp hd rows full a he.1,full a he.1⟩
      (arguments g h x T U E fuel p hp hd rows full args he.2)
end

end Shallot.MacroPeg.CBV.SequentialTotalExpression
