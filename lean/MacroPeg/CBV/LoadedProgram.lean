import MacroPeg.CBV.TableInit

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.KExp

def zeroHaltP {K : Nat} (out : Fin K) : NProg K := .ite out .zero (.halt true) (.halt false)

theorem zeroHalt_halts {K : Nat} (out : Fin K) (S : Lists K) (v : Nat) {l : List Nat}
    (hv : S out = l ++ [v]) : NHalts (zeroHaltP out) S (v == 0) S 2 := by
  cases v with
  | zero => exact (nhalts_halt true S).iteT (by simp [hv, NTest.eval])
  | succ v => exact (nhalts_halt false S).iteF (by simp [hv, NTest.eval])

def finishCodeP {K : Nat} (out : Fin K) : NProg K :=
  .ite out .zero (.halt false)
    (.seq (.prim (.dec out)) (.ite out .zero (.halt false)
      (.seq (.prim (.dec out)) (zeroHaltP out))))

/-- The final test accepts exactly numeric success with zero remaining input. -/
theorem finishCode_halts {K : Nat} (out : Fin K) (S : Lists K) (v : Nat) {l : List Nat}
    (hv : S out = l ++ [v]) :
    ∃ b S', NHalts (finishCodeP out) S b S' 6 ∧ (b = true ↔ v = 2) := by
  cases v with
  | zero =>
    have hx := (nhalts_halt false S).iteT (i := out) (c := .zero)
      (q := .seq (.prim (.dec out)) (.ite out .zero (.halt false) (.seq (.prim (.dec out)) (zeroHaltP out))))
      (by simp [hv, NTest.eval])
    exact ⟨false, S, hx.mono (by omega), by simp⟩
  | succ v => cases v with
    | zero =>
      have xd := nruns_dec out S hv
      let X := S.set out (l ++ [0])
      have hf := (nhalts_halt false X).iteT (i := out) (c := .zero)
        (q := .seq (.prim (.dec out)) (zeroHaltP out)) (by simp [X, NTest.eval])
      have hx := (xd.seqH hf).iteF (i := out) (c := .zero) (p := .halt false) (by simp [hv, NTest.eval])
      exact ⟨false, X, hx.mono (by omega), by simp⟩
    | succ v =>
      have xd := nruns_dec out S hv
      simp only [show v + 1 + 1 - 1 = v + 1 by omega] at xd
      let X := S.set out (l ++ [v + 1])
      have xe := nruns_dec out X (l := l) (v := v + 1) (by simp [X])
      simp only [Nat.add_sub_cancel] at xe
      let Y := X.set out (l ++ [v])
      have hf := zeroHalt_halts out Y v (l := l) (by simp [Y])
      have hb := (xe.seqH hf).iteF (i := out) (c := .zero) (p := .halt false) (by simp [X, NTest.eval])
      have hx := (xd.seqH hb).iteF (i := out) (c := .zero) (p := .halt false) (by simp [hv, NTest.eval])
      exact ⟨v == 0, Y, hx, by simp⟩

theorem resultCode_two_iff (v : Res) : resultCode v = 2 ↔ v = some (some 0) := by
  cases v with
  | none => simp [resultCode]
  | some u => cases u with
    | none => simp [resultCode]
    | some p => simp [resultCode]

def entryProgram {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (e : MExp) : NProg K :=
  .seq (.prim (.dup (r.get 20) (r.get 15) (r.ne (by decide))))
    (.seq (exprProgram r g s 0 e) (.seq (.prim (.pop (r.get 15))) (finishCodeP (r.get 16))))

def entryCost (g : MGrammar) (e : MExp) (n : Nat) : Nat := exprBudget g 0 e n + 8

/-- Evaluate the entry on the saturated table and halt with precisely the numeric acceptance answer. -/
theorem entryProgram_halts {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (e : MExp)
    (x : List Char) (S : Lists K) (ready : EvalReady r S x (pack g x (tblV g x s (iterBoundV g x))) []) :
    ∃ b S', NHalts (entryProgram r g s e) S b S' (entryCost g e x.length) ∧
      (b = true ↔ numericDecide s g x e = some (some 0)) := by
  have xd := nruns_dup (r.get 20) (r.get 15) (r.ne (by decide)) S (l := []) (v := x.length) ready.len
  let X := S.set (r.get 15) (S (r.get 15) ++ [x.length])
  have xe := exprProgram_runs r g x s (tblV g x s (iterBoundV g x)) [] (tblV_ok g x s _) (by simp)
    e X (ready.frame 15 (by simp) _) x.length (S (r.get 15)) (by simp [X]) (Nat.le_refl _)
  have he : eval g x s (pack g x (tblV g x s (iterBoundV g x))) [] e x.length = numericDecide s g x e := by
    simp only [numericDecide, numericIterate_pack]
  rw [he] at xe
  simp only [List.length_nil] at xe
  let v := resultCode (numericDecide s g x e)
  have hx16 : X (r.get 16) = S (r.get 16) := by simp [X, Lists.set]
  rw [hx16] at xe
  let Y := X.set (r.get 16) (S (r.get 16) ++ [v])
  have xp := nruns_pop (r.get 15) Y (l := S (r.get 15)) (v := x.length) (by simp [Y, X, Lists.set])
  have hout : Y.set (r.get 15) (S (r.get 15)) = S.set (r.get 16) (S (r.get 16) ++ [v]) := by
    funext z
    by_cases h15 : z = r.get 15
    · subst z; simp [Y, X, Lists.set]
    by_cases h16 : z = r.get 16
    · subst z; simp [Y, X, Lists.set]
    simp [Y, X, Lists.set, h15, h16]
  rw [hout] at xp
  obtain ⟨b, S', hf, hb⟩ := finishCode_halts (r.get 16) (S.set (r.get 16) (S (r.get 16) ++ [v])) v (l := S (r.get 16)) (by simp)
  refine ⟨b, S', (xd.seqH (xe.seqH (xp.seqH hf))).mono (by unfold entryCost; omega), ?_⟩
  exact hb.trans (resultCode_two_iff _)

def loadedProgram {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (e : MExp) : NProg K :=
  .seq (tableInitP r g) (.seq (saturationP r g s) (entryProgram r g s e))

def loadedCost (g : MGrammar) (e : MExp) (n : Nat) : Nat :=
  tableInitCost g n + saturationCost g n + entryCost g e n

/-- From a loaded word and its constructed dictionary, the complete CBV stack decider initializes,
saturates, evaluates the entry, and halts within a polynomial budget. -/
theorem loadedProgram_halts {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (e : MExp)
    (x : List Char) (S : Lists K) (ready : EvalReady r S x [] []) (hnext : S (r.get 25) = []) :
    ∃ b S', NHalts (loadedProgram r g s e) S b S' (loadedCost g e x.length) ∧
      (b = true ↔ numericDecide s g x e = some (some 0)) := by
  have xi := tableInit_runs r g s x S ready
  let X := S.set (r.get 22) (pack g x (tblV g x s 0))
  have hx := ready.withTable (pack g x (tblV g x s 0))
  have xs := saturation_runs r g s x X hx (by simp [X, Lists.set, hnext])
  have hx29 : X (r.get 29) = S (r.get 29) := by simp [X, Lists.set]
  rw [hx29] at xs
  let Y := S.set (r.get 22) (pack g x (tblV g x s (iterBoundV g x)))
  have he : X.set (r.get 22) (pack g x (tblV g x s (iterBoundV g x))) = Y := by simp only [X, Y, Lists.set_set_u]
  rw [he] at xs
  obtain ⟨b, S', hf, hb⟩ := entryProgram_halts r g s e x Y (ready.withTable _)
  exact ⟨b, S', (xi.seqH (xs.seqH hf)).mono (by unfold loadedCost; omega), hb⟩

theorem entryCost_poly (g : MGrammar) (e : MExp) : IsPoly (entryCost g e) :=
  isPoly_add (exprBudget_poly g 0 e) (isPoly_const 8)

theorem loadedCost_poly (g : MGrammar) (e : MExp) : IsPoly (loadedCost g e) :=
  isPoly_add (isPoly_add (tableInitCost_poly g) (saturationCost_poly g)) (entryCost_poly g e)

end Shallot.MacroPeg.CBV
