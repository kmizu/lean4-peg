import MacroPeg.CBV.ScannerAbsorption

/-! Alphabet-safe captures can be absorbed even when an argument depends on
retained captures. Argument values need not come from a fixed head parser. -/
namespace Shallot.MacroPeg.CBV.ScannerCapturedArguments
open NestedScannerArguments (accepts scan scan_eval)
open ClockFreezing (Table)

def Environment (A : List Char) (E : List (List Char)) : Prop := ∀ w∈E, w.all (accepts A)=true

def Safe (A : List Char) : MExp → Prop
  | .eps | .notP _ | .param _ => True
  | .chr c => accepts A c=true
  | .lit w => w.all (accepts A)=true
  | .seq a b | .alt a b => Safe A a ∧ Safe A b
  | .star a => Safe A a
  | _ => False

theorem subst_safe (A : List Char) (E : List (List Char)) (hE : Environment A E) :
    ∀ e, Safe A e → ScannerAbsorption.Safe 0 A (MExp.subst (E.map MExp.lit) e)
  | .eps, _ | .notP _, _ => trivial
  | .chr _, h | .lit _, h => h
  | .param k, _ => by
    simp only [MExp.subst,argAt_map_lit]
    cases hw : E[k]? with
    | none => trivial
    | some w => exact hE w (List.mem_of_getElem? hw)
  | .seq a b, h | .alt a b, h => ⟨subst_safe A E hE a h.1,subst_safe A E hE b h.2⟩
  | .star a, h => subst_safe A E hE a h
  | .any, h | .range _ _, h | .call _ _, h | .dbg _, h | .lam _ _, h
  | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem absorbed (g : MGrammar) (x A : List Char) (s : Strategy) (T : Table)
    (hOk : OkTV x.length T) (E : List (List Char)) (hE : Environment A E)
    (e : MExp) (he : e.FirstOrder) (hf : Safe A e) (p q : Nat) (hp : p≤x.length)
    (hv : evV g x s T E e p=some (some q)) :
    (sfx x p).dropWhile (accepts A)=(sfx x q).dropWhile (accepts A) := by
  have hsub : evV g x s T [] (MExp.subst (E.map MExp.lit) e) p=some (some q) := by
    rw [evV_subst E e he]; exact hv
  exact ScannerAbsorption.evaluator_safe (bodies:=[]) (by intro i e hi; simp at hi) A x s T
    (by intro i hi; simp at hi) hOk [] _ (subst_safe A E hE e hf) p q hp hsub

theorem all_of_dropWhile_append (A : List Char) : ∀ (w rest : List Char),
    (w++rest).dropWhile (accepts A)=rest.dropWhile (accepts A) → w.all (accepts A)=true
  | [], _, _ => rfl
  | c::w, rest, h => by
    cases hc : accepts A c with
    | true =>
      simp only [List.cons_append,List.dropWhile_cons,hc,if_true] at h
      simp only [List.all_cons,hc,Bool.true_and]
      exact all_of_dropWhile_append A w rest h
    | false =>
      simp only [List.cons_append,List.dropWhile_cons,hc,Bool.false_eq_true,if_false] at h
      have hl := congrArg List.length h
      have hs : (rest.dropWhile (accepts A)).length≤rest.length := by
        have hh := congrArg List.length (List.takeWhile_append_dropWhile (p:=accepts A) (l:=rest))
        simp only [List.length_append] at hh
        omega
      simp only [List.length_cons,List.length_append] at hl
      omega

theorem capture_safe (g : MGrammar) (x A : List Char) (T : Table)
    (hT : SoundTV g x .callByValuePar T) (hOk : OkTV x.length T)
    (E : List (List Char)) (hE : Environment A E) (e : MExp) (he : e.FirstOrder) (hf : Safe A e)
    (p q : Nat) (hp : p≤x.length) (hv : evV g x .callByValuePar T E e p=some (some q)) :
    (pre x p q).all (accepts A)=true := by
  have hs := absorbed g x A .callByValuePar T hOk E hE e he hf p q hp hv
  have hw := (ReplayFusion.success_prefix hT E e he p q hp hv).2
  rw [hw] at hs
  exact all_of_dropWhile_append A _ _ hs

/-- The singleton scanner is exactly ordinary literal repetition. -/
theorem singleton_scan (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (c : Char) (p : Nat) :
    evV g x s T E (.star (.lit [c])) p=evV g x s T E (scan [c]) p := by
  apply evStar_congr p
  intro q _
  simp only [NestedScannerArguments.choice,evV,MExp.failAlways]
  cases sfx x q with
  | nil => rfl
  | cons d rest =>
    simp only [Shallot.stripPrefix?]
    cases Shallot.beqChar c d <;> simp

end Shallot.MacroPeg.CBV.ScannerCapturedArguments
