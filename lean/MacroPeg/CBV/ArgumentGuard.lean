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

/-- A test at the actual capture endpoint can be previewed at the caller
origin without changing the held value. The argument is re-evaluated in
the identical environment/table; no purity or totality premise is needed. -/
theorem suffix_call_eq (g : MGrammar) (x : List Char) (T : ClockFreezing.Table)
    (E : List (List Char)) (i p : Nat) (body a test : MExp)
    (hr : ruleAtM g.rules i=some ⟨1,body⟩) :
    evV g x .callByValuePar T E (.call i [.seq a (look test)]) p=
      evV g x .callByValuePar T E (.seq (look (.seq a test)) (.call i [a])) p := by
  have hpeek (e : MExp) (q : Nat) : evV g x .callByValuePar T E (look e) q=
      CallLookahead.peek q (evV g x .callByValuePar T E e q) :=
    CallLookahead.evV_peek g x .callByValuePar T E e q
  rw [evV_call_par hr rfl (by decide)]
  simp only [evParArgs]
  change (match (match evV g x .callByValuePar T E (.seq a (look test)) p with
    | some (some q) => some (some [pre x p q])
    | some none => some none | none => none) with
    | some (some W) => valAt (T i W) p
    | some none => some none | none => none)=
    (match evV g x .callByValuePar T E (look (.seq a test)) p with
    | some (some q) => evV g x .callByValuePar T E (.call i [a]) q | r => r)
  rw [hpeek]
  cases ha : evV g x .callByValuePar T E a p with
  | none => rw [evV_seq_none ha,evV_seq_none ha]; rfl
  | some r => cases r with
    | none => rw [evV_seq_fail ha,evV_seq_fail ha]; rfl
    | some j =>
      rw [evV_seq_ok ha,evV_seq_ok ha,hpeek]
      cases ht : evV g x .callByValuePar T E test j with
      | none => rfl
      | some r => cases r with
        | none => rfl
        | some q =>
          simp only [CallLookahead.peek]
          rw [evV_call_par hr rfl (by decide)]
          simp only [evParArgs,ha]

/-- Comparing a preview and its continuation separately suffices for
complete partial correspondence. A successful preview always restores p. -/
theorem look_sequence_congr (g g' : MGrammar) (x : List Char) (s s' : Strategy)
    (T U : ClockFreezing.Table) (E E' : List (List Char)) (test test' b b' : MExp) (p : Nat)
    (ht : evV g x s T E test p=evV g' x s' U E' test' p)
    (hb : evV g x s T E b p=evV g' x s' U E' b' p) :
    evV g x s T E (.seq (look test) b) p=
      evV g' x s' U E' (.seq (look test') b') p := by
  have hpeek (g : MGrammar) (s : Strategy) (V : ClockFreezing.Table)
      (F : List (List Char)) (a : MExp) : evV g x s V F (look a) p=
        CallLookahead.peek p (evV g x s V F a p) :=
    CallLookahead.evV_peek g x s V F a p
  change (match evV g x s T E (look test) p with
    | some (some q) => evV g x s T E b q | r => r)=
    (match evV g' x s' U E' (look test') p with
    | some (some q) => evV g' x s' U E' b' q | r => r)
  rw [hpeek,hpeek,ht]
  cases hv : evV g' x s' U E' test' p with
  | none => rfl
  | some r => cases r with
    | none => rfl
    | some q => exact hb

end Shallot.MacroPeg.CBV.ArgumentGuard
