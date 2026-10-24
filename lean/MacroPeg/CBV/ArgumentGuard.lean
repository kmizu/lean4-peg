import MacroPeg.CBV.CallLookahead
import MacroPeg.CBV.PartialCodewordCapture

namespace Shallot.MacroPeg.CBV.ArgumentGuard
open PartialCodewordCapture (look)

/-- A unary Par argument may test arbitrary caller-dependent computation
before capturing. Moving that test outside the call preserves its exact
failure/undefinedness and the captured value, without evaluating the callee. -/
theorem call_eq (g : MGrammar) (x : List Char) (T : ClockFreezing.Table)
    (E : List (List Char)) (i p : Nat) (body a test : MExp)
    (hr : ruleAtM g.rules i=some ⟨1,body⟩) :
    evV g x .callByValuePar T E (.call i [.seq (look test) a]) p=
      evV g x .callByValuePar T E (.seq (look test) (.call i [a])) p := by
  have hpeek : evV g x .callByValuePar T E (look test) p=
      CallLookahead.peek p (evV g x .callByValuePar T E test p) :=
    CallLookahead.evV_peek g x .callByValuePar T E test p
  rw [evV_call_par hr rfl (by decide)]
  simp only [evParArgs]
  change (match (match (match evV g x .callByValuePar T E (look test) p with
    | some (some q) => evV g x .callByValuePar T E a q | r => r) with
    | some (some q) => some (some [pre x p q])
    | some none => some none | none => none) with
    | some (some W) => valAt (T i W) p
    | some none => some none | none => none)=
    (match evV g x .callByValuePar T E (look test) p with
    | some (some q) => evV g x .callByValuePar T E (.call i [a]) q | r => r)
  rw [hpeek]
  cases ht : evV g x .callByValuePar T E test p with
  | none => rfl
  | some r => cases r with
    | none => rfl
    | some q =>
      simp only [CallLookahead.peek]
      rw [evV_call_par hr rfl (by decide)]
      simp only [evParArgs]
      cases ha : evV g x .callByValuePar T E a p with
      | none => rfl
      | some r => cases r <;> rfl

end Shallot.MacroPeg.CBV.ArgumentGuard
