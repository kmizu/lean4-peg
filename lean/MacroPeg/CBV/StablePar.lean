import MacroPeg.CBV.ProducedPrefixCorrespondence

namespace Shallot.MacroPeg.CBV.StablePar

abbrev table (g : MGrammar) (x : List Char) := tblV g x .callByValuePar (iterBoundV g x)

theorem agree (g : MGrammar) (x : List Char) :
    AgreeV g x (table g x) (tblV g x .callByValuePar (iterBoundV g x+1)) := by
  obtain ⟨m,hm,hf⟩ := tblV_fix_exists g x .callByValuePar
  have a := agreeV_from hf (iterBoundV g x-m)
  have b := agreeV_from hf (iterBoundV g x+1-m)
  rw [Nat.add_sub_cancel' hm] at a
  rw [Nat.add_sub_cancel' (by omega)] at b
  exact a.symm.trans b

/-- Every finite physical evaluation refines evaluation at the actual finite
stabilization bound, including under arbitrary retained environments. -/
theorem eval_le (g : MGrammar) (x : List Char) (k : Nat) (E : List (List Char))
    (e : MExp) (p : Nat) (hp : p≤x.length) :
    RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E e p)
      (evV g x .callByValuePar (table g x) E e p) := by
  obtain ⟨m,hm,hf⟩ := tblV_fix_exists g x .callByValuePar
  by_cases hk : k≤iterBoundV g x
  · exact evV_mono (tblV_le g x .callByValuePar hk) e p
  · have a := agreeV_from hf (iterBoundV g x-m)
    have b := agreeV_from hf (k-m)
    rw [Nat.add_sub_cancel' hm] at a
    rw [Nat.add_sub_cancel' (by omega)] at b
    exact Or.inr (evV_agree (b.symm.trans a) (tblV_ok g x .callByValuePar k) e p hp)

/-- Unfolding at the stable table is justified only for actual captured
substring environments, exactly the domain used by the finite decision proof. -/
theorem row_eq (g : MGrammar) (x : List Char) (i : Nat) (r : MRule)
    (hr : ruleAtM g.rules i=some r) (W : List (List Char))
    (hW : W∈words (subStrs x) r.arity) (p : Nat) (hp : p≤x.length) :
    valAt (table g x i W) p=evV g x .callByValuePar (table g x) W r.body p := by
  rw [agree g x i r W hr hW p hp,valAt_tblV_succ hr W hp]

theorem singleton_mem (x w : List Char) (hw : w∈subStrs x) : [w]∈words (subStrs x) 1 :=
  (mem_words _ _ _).mpr ⟨rfl,by simpa using hw⟩

end Shallot.MacroPeg.CBV.StablePar
