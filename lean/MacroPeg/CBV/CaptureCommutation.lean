import MacroPeg.CBV.ScannerAbsorption
import MacroPeg.CBV.WordArguments

/-! Derive captured-word alphabets from recursive syntax, then commute a
unary prefix with the retained capture even when their input spans overlap. -/
namespace Shallot.MacroPeg.CBV.CaptureCommutation
open NestedScannerArguments (accepts)
open ClockFreezing (Table)

theorem all_of_dropWhile_append (A : List Char) : ∀ (w rest : List Char),
    (w++rest).dropWhile (accepts A) = rest.dropWhile (accepts A) → w.all (accepts A) = true
  | [], _, _ => rfl
  | c::w, rest, h => by
    by_cases hc : accepts A c = true
    · simp only [List.cons_append,List.dropWhile_cons,hc,if_true] at h
      simp only [List.all_cons,hc,Bool.true_and]
      exact all_of_dropWhile_append A w rest h
    · have hcf : accepts A c = false := by cases hh : accepts A c <;> simp_all
      simp only [List.cons_append,List.dropWhile_cons,hcf,Bool.false_eq_true,if_false] at h
      have hl := congrArg List.length h
      have hr := congrArg List.length (List.takeWhile_append_dropWhile (p := accepts A) (l := rest))
      simp only [List.length_cons,List.length_append] at hl hr
      omega

theorem captured_alphabet {bodies : List MExp} {g : MGrammar}
    (hg : RecursiveParserStability.Installed bodies g) (A x : List Char) (T : Table)
    (hRows : ScannerAbsorption.RowsSafe bodies.length A x T) (hOk : OkTV x.length T)
    (hT : SoundTV g x .callByValuePar T) (E : List (List Char)) (e : MExp)
    (he : e.FirstOrder) (hs : ScannerAbsorption.Safe bodies.length A e) (p q : Nat)
    (hp : p ≤ x.length) (hv : evV g x .callByValuePar T E e p = some (some q)) :
    (pre x p q).all (accepts A) = true := by
  have hh := ScannerAbsorption.evaluator_safe hg A x .callByValuePar T hRows hOk E e hs p q hp hv
  have hpref := (ReplayFusion.success_prefix hT E e he p q hp hv).2
  rw [hpref] at hh
  exact all_of_dropWhile_append A _ _ hh

theorem unary_word (c : Char) : ∀ w, w.all (accepts [c]) = true → w = List.replicate w.length c
  | [], _ => rfl
  | d::w, h => by
    simp only [List.all_cons,Bool.and_eq_true] at h
    have hd : d=c := List.mem_singleton.mp ((NestedScannerArguments.accepts_iff_mem [c] d).mp h.1)
    subst d
    rw [List.length_cons,List.replicate_succ]
    exact congrArg (List.cons c) (unary_word c w h.2)

theorem unary_commutes (c : Char) (w : List Char) (hw : w.all (accepts [c]) = true) (n : Nat) :
    List.replicate n c ++ w = w ++ List.replicate n c := by
  rw [unary_word c w hw, List.replicate_append_replicate, List.replicate_append_replicate,Nat.add_comm]

/-- This is word equality, so it preserves finite failure as well as success.
No assumption that the shifted replay is disjoint from the original capture. -/
theorem prefix_swap (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (w u : List Char) (h : u++w=w++u) (p : Nat) :
    evV g x s T [w] (.seq (.lit u) (.param 0)) p =
      evV g x s T [w] (.seq (.param 0) (.lit u)) p := by
  rw [WordArguments.word_eval g x s T [w] (.seq (.lit u) (.param 0)) ⟨True.intro,True.intro⟩,
    WordArguments.word_eval g x s T [w] (.seq (.param 0) (.lit u)) ⟨True.intro,True.intro⟩]
  simp only [WordArguments.value,List.getElem?_cons_zero,Option.bind_some,Option.map_some,h]

end Shallot.MacroPeg.CBV.CaptureCommutation
