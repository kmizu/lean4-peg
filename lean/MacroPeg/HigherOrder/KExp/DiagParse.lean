import MacroPeg.HigherOrder.KExp.DiagArith
import MacroPeg.HigherOrder.KExp.DiagFrontSpec

/-!
# The front of the diagonal machine: reading the input

From `nInit UK w` (the bits on stack `0`, the first on top):
* `parseP` reads the bits, keeping a copy on `XB`, their number on `NN`, and the unary numbers `deUnary w` on `LL`
  (the first at the bottom) (`nruns_parse`);
* `tapeP` writes the first tape `|w| :: w.map bitSym` on `TP` (`nruns_tape`).
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Complexity.Univ
open Shallot.MacroPeg.HO

/-! ## Scratch stacks -/

abbrev XB : Fin UK := 7
abbrev YB : Fin UK := 8
abbrev CN : Fin UK := 9
abbrev LL : Fin UK := 10
abbrev NN : Fin UK := 11
abbrev MM : Fin UK := 12
abbrev CC : Fin UK := 13
abbrev DD : Fin UK := 14
abbrev K2 : Fin UK := 15
abbrev DC : Fin UK := 16
abbrev TT : Fin UK := 17
abbrev AA : Fin UK := 18
abbrev PP : Fin UK := 19
abbrev VV : Fin UK := 20
abbrev N1 : Fin UK := 21
abbrev NQ : Fin UK := 22

/-- All stacks empty. -/
def E0 : Lists UK := fun _ => []

/-! ## Reading and comparing stacks built by updates -/

@[simp] theorem v_TBL : (Complexity.Univ.TBL : Fin UK).val = 0 := rfl
@[simp] theorem v_KS : (Complexity.Univ.KS : Fin UK).val = 1 := rfl
@[simp] theorem v_NA : (Complexity.Univ.NA : Fin UK).val = 2 := rfl
@[simp] theorem v_ST : (Complexity.Univ.ST : Fin UK).val = 3 := rfl
@[simp] theorem v_POS : (Complexity.Univ.POS : Fin UK).val = 4 := rfl
@[simp] theorem v_TP : (Complexity.Univ.TP : Fin UK).val = 5 := rfl
@[simp] theorem v_CNT : (Complexity.Univ.CNT : Fin UK).val = 6 := rfl
@[simp] theorem v_XB : (Shallot.MacroPeg.KExp.XB : Fin UK).val = 7 := rfl
@[simp] theorem v_YB : (Shallot.MacroPeg.KExp.YB : Fin UK).val = 8 := rfl
@[simp] theorem v_CN : (Shallot.MacroPeg.KExp.CN : Fin UK).val = 9 := rfl
@[simp] theorem v_LL : (Shallot.MacroPeg.KExp.LL : Fin UK).val = 10 := rfl
@[simp] theorem v_NN : (Shallot.MacroPeg.KExp.NN : Fin UK).val = 11 := rfl
@[simp] theorem v_MM : (Shallot.MacroPeg.KExp.MM : Fin UK).val = 12 := rfl
@[simp] theorem v_CC : (Shallot.MacroPeg.KExp.CC : Fin UK).val = 13 := rfl
@[simp] theorem v_DD : (Shallot.MacroPeg.KExp.DD : Fin UK).val = 14 := rfl
@[simp] theorem v_K2 : (Shallot.MacroPeg.KExp.K2 : Fin UK).val = 15 := rfl
@[simp] theorem v_DC : (Shallot.MacroPeg.KExp.DC : Fin UK).val = 16 := rfl
@[simp] theorem v_TT : (Shallot.MacroPeg.KExp.TT : Fin UK).val = 17 := rfl
@[simp] theorem v_AA : (Shallot.MacroPeg.KExp.AA : Fin UK).val = 18 := rfl
@[simp] theorem v_PP : (Shallot.MacroPeg.KExp.PP : Fin UK).val = 19 := rfl
@[simp] theorem v_VV : (Shallot.MacroPeg.KExp.VV : Fin UK).val = 20 := rfl
@[simp] theorem v_N1 : (Shallot.MacroPeg.KExp.N1 : Fin UK).val = 21 := rfl
@[simp] theorem v_NQ : (Shallot.MacroPeg.KExp.NQ : Fin UK).val = 22 := rfl

theorem get_set (S : Lists UK) (i q : Fin UK) (v : List Nat) : (S.set i v) q = if q.val = i.val then v else S q := by
  simp only [Lists.set, Fin.ext_iff]

theorem uk_val : UK = 40 := rfl

/-- Equalities of stacks built by updates: compare at every index. -/
theorem lists_eq_of {S S' : Lists UK} (h : ∀ (q : Nat) (hq : q < 40), S ⟨q, hq⟩ = S' ⟨q, hq⟩) : S = S' :=
  funext fun ⟨q, hq⟩ => h q hq

macro "lsimp" : tactic =>
  `(tactic| (apply lists_eq_of; intro q hq; (simp only [get_set, E0]); (iterate 40 ((rcases q with _ | q); (next => simp))); omega))

/-- The value of stacks built by updates at a concrete index. -/
macro "stk_simp" : tactic => `(tactic| simp [get_set, E0])

theorem nInit_eq (w : List Bool) : nInit UK w = E0.set TBL (w.map bitElem).reverse := by
  funext q
  simp only [nInit, Lists.set, E0]
  by_cases h : q = TBL
  · subst h; simp
  · simp only [h, if_false]
    have : q.val ≠ 0 := fun e => h (Fin.ext e)
    simp [this]

/-! ## Reading unary numbers bit by bit -/

def pstep : Nat × List Nat → Bool → Nat × List Nat
  | (a, ns), true => (a + 1, ns)
  | (a, ns), false => (0, ns ++ [a])

theorem pfold_deUnary : ∀ (u : List Bool) (a : Nat) (ns : List Nat),
    (u.foldl pstep (a, ns)).2 = ns ++ deUnaryGo a u
  | [], a, ns => by simp [deUnaryGo]
  | true :: u, a, ns => by
    rw [List.foldl_cons, show pstep (a, ns) true = (a + 1, ns) from rfl, pfold_deUnary u (a + 1) ns]; rfl
  | false :: u, a, ns => by
    rw [List.foldl_cons, show pstep (a, ns) false = (0, ns ++ [a]) from rfl, pfold_deUnary u 0 (ns ++ [a])]
    simp [deUnaryGo]

/-- The state of the reader after the first `m` bits. -/
def pf (w : List Bool) (m : Nat) : Nat × List Nat := (w.take m).foldl pstep (0, [])

theorem pf_succ (w : List Bool) {m : Nat} (hm : m < w.length) : pf w (m + 1) = pstep (pf w m) w[m] := by
  simp only [pf]
  rw [List.take_succ_eq_append_getElem hm, List.foldl_append]
  rfl

theorem pf_end (w : List Bool) : (pf w w.length).2 = deUnary w := by
  simp only [pf, List.take_length]
  rw [pfold_deUnary]; rfl

/-! ## The reader -/

def parseBody : NProg UK :=
  .seq (.prim (.dup TBL XB (by decide))) (.seq (.prim (.inc NN))
    (.seq (.ite TBL .pos (.prim (.inc CN)) (.seq (nmv CN LL (by decide)) (.prim (.pushZ CN)))) (.prim (.pop TBL))))

def parseP : NProg UK :=
  .seq (.prim (.pushZ NN)) (.seq (.prim (.pushZ CN)) (.seq (.loop TBL .nonempty parseBody) (.prim (.pop CN))))

/-- After reading: the bits on `XB`, their number on `NN`, the numbers on `LL`. -/
def S1 (w : List Bool) : Lists UK := ((E0.set XB (w.map bitElem)).set NN [w.length]).set LL (deUnary w)

/-- The reader after `m` bits. -/
def parseF (w : List Bool) (m : Nat) : Lists UK :=
  ((((E0.set TBL ((w.map bitElem).drop m).reverse).set XB ((w.map bitElem).take m)).set NN [m]).set CN
    [(pf w m).1]).set LL (pf w m).2

theorem parseF_tbl (w : List Bool) (m : Nat) : parseF w m TBL = ((w.map bitElem).drop m).reverse := by
  simp only [parseF]; stk_simp

theorem parseF_cn (w : List Bool) (m : Nat) : parseF w m CN = [] ++ [(pf w m).1] := by
  simp only [parseF]; stk_simp

theorem parseF_nn (w : List Bool) (m : Nat) : parseF w m NN = [] ++ [m] := by
  simp only [parseF]; stk_simp

theorem parseF_xb (w : List Bool) (m : Nat) : parseF w m XB = (w.map bitElem).take m := by
  simp only [parseF]; stk_simp

theorem parseF_ll (w : List Bool) (m : Nat) : parseF w m LL = (pf w m).2 := by
  simp only [parseF]; stk_simp

theorem parse_body (w : List Bool) {m : Nat} (hm : m < w.length) :
    NRuns parseBody (parseF w m) (parseF w (m + 1)) 7 := by
  have hml : m < (w.map bitElem).length := by simpa using hm
  have hd : ((w.map bitElem).drop m).reverse = ((w.map bitElem).drop (m + 1)).reverse ++ [bitElem w[m]] := by
    rw [List.drop_eq_getElem_cons hml]; simp
  have ht : (w.map bitElem).take (m + 1) = (w.map bitElem).take m ++ [bitElem w[m]] := by
    rw [List.take_succ_eq_append_getElem hml]; simp
  have hp := pf_succ w hm
  have h0 : parseF w m TBL = ((w.map bitElem).drop (m + 1)).reverse ++ [bitElem w[m]] := by
    rw [parseF_tbl, hd]
  have d₁ := nruns_dup TBL XB (by decide) (parseF w m) h0
  rw [parseF_xb] at d₁
  let G₁ := (parseF w m).set XB ((w.map bitElem).take m ++ [bitElem w[m]])
  have d₂ := nruns_inc NN G₁ (l := []) (v := m) (by simp only [G₁]; rw [Lists.set_ne _ _ (by decide), parseF_nn])
  let G₂ := G₁.set NN ([] ++ [m + 1])
  have hG₂ : G₂ TBL = ((w.map bitElem).drop (m + 1)).reverse ++ [bitElem w[m]] := by
    simp only [G₂, G₁]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), h0]
  have hG₂c : G₂ CN = [] ++ [(pf w m).1] := by
    simp only [G₂, G₁]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), parseF_cn]
  have hG₂l : G₂ LL = (pf w m).2 := by
    simp only [G₂, G₁]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), parseF_ll]
  have hF1 : parseF w (m + 1) =
      ((((E0.set TBL ((w.map bitElem).drop (m + 1)).reverse).set XB ((w.map bitElem).take m ++ [bitElem w[m]])).set
        NN [m + 1]).set CN [(pstep (pf w m) w[m]).1]).set LL (pstep (pf w m) w[m]).2 := by
    simp only [parseF, ht, hp]
  have pt : ∀ r : Nat × List Nat, pstep r true = (r.1 + 1, r.2) := fun r => rfl
  have pfa : ∀ r : Nat × List Nat, pstep r false = (0, r.2 ++ [r.1]) := fun r => rfl
  cases hb : w[m] with
  | true =>
    rw [hb, pt] at hF1
    rw [hb] at hG₂
    have d₃ := nruns_inc CN G₂ hG₂c
    let G₃ := G₂.set CN ([] ++ [(pf w m).1 + 1])
    have hG₃ : G₃ TBL = ((w.map bitElem).drop (m + 1)).reverse ++ [bitElem true] := by
      simp only [G₃]; rw [Lists.set_ne _ _ (by decide), hG₂]
    have d₄ := nruns_pop TBL G₃ hG₃
    have e : G₃.set TBL ((w.map bitElem).drop (m + 1)).reverse = parseF w (m + 1) := by
      rw [hF1]
      simp only [G₃, G₂, G₁, parseF, hb]
      lsimp
    rw [e] at d₄
    have d₃' : NRuns (.ite TBL .pos (.prim (.inc CN)) (.seq (nmv CN LL (by decide)) (.prim (.pushZ CN)))) G₂ G₃ 2 :=
      d₃.iteT (by rw [hG₂]; simp [bitElem])
    exact (d₁.seq (d₂.seq (d₃'.seq d₄))).mono (by omega)
  | false =>
    rw [hb, pfa] at hF1
    rw [hb] at hG₂
    have d₃ := nruns_mv CN LL (by decide) G₂ hG₂c
    rw [hG₂l] at d₃
    let G₃ := (G₂.set LL ((pf w m).2 ++ [(pf w m).1])).set CN []
    have d₃b := nruns_pushZ CN G₃
    have hG₃c : G₃ CN = [] := by simp only [G₃, Lists.set_same]
    rw [hG₃c] at d₃b
    let G₄ := G₃.set CN ([] ++ [0])
    have hG₄ : G₄ TBL = ((w.map bitElem).drop (m + 1)).reverse ++ [bitElem false] := by
      simp only [G₄, G₃]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), hG₂]
    have d₄ := nruns_pop TBL G₄ hG₄
    have e : G₄.set TBL ((w.map bitElem).drop (m + 1)).reverse = parseF w (m + 1) := by
      rw [hF1]
      simp only [G₄, G₃, G₂, G₁, parseF, hb]
      lsimp
    rw [e] at d₄
    have d₃' : NRuns (.ite TBL .pos (.prim (.inc CN)) (.seq (nmv CN LL (by decide)) (.prim (.pushZ CN)))) G₂ G₄ 4 :=
      (d₃.seq d₃b).iteF (by rw [hG₂]; simp [bitElem])
    exact (d₁.seq (d₂.seq (d₃'.seq d₄))).mono (by omega)

theorem nruns_parse (w : List Bool) : NRuns parseP (nInit UK w) (S1 w) (8 * w.length + 4) := by
  rw [nInit_eq]
  have d₁ := nruns_pushZ NN (E0.set TBL (w.map bitElem).reverse)
  have d₂ := nruns_pushZ CN ((E0.set TBL (w.map bitElem).reverse).set NN
    ((E0.set TBL (w.map bitElem).reverse) NN ++ [0]))
  have e₀ : ((E0.set TBL (w.map bitElem).reverse).set NN ((E0.set TBL (w.map bitElem).reverse) NN ++ [0])).set CN
      (((E0.set TBL (w.map bitElem).reverse).set NN ((E0.set TBL (w.map bitElem).reverse) NN ++ [0])) CN ++ [0]) =
      parseF w 0 := by
    simp only [parseF, pf, List.drop_zero, List.take_zero, List.foldl_nil]
    lsimp
  rw [e₀] at d₂
  have hl := nruns_family_const (i := TBL) (c := .nonempty) (p := parseBody) (parseF w) w.length 7
    (fun m hm => by
      rw [parseF_tbl]; exact eval_nonempty_ne (by simp; omega))
    (by rw [parseF_tbl, List.drop_of_length_le (by simp)]; rfl)
    (fun m hm => parse_body w hm)
  have d₄ := nruns_pop CN (parseF w w.length) (parseF_cn w w.length)
  have e : (parseF w w.length).set CN [] = S1 w := by
    simp only [parseF, S1, pf_end]
    rw [List.take_of_length_le (by simp), List.drop_of_length_le (by simp)]
    simp only [List.reverse_nil]
    lsimp
  rw [e] at d₄
  exact (d₁.seq (d₂.seq (hl.seq d₄))).mono (by omega)

/-! ## The first tape -/

def tapeP : NProg UK :=
  .seq (.prim (.dup NN TP (by decide))) (.seq (nmvAll XB YB (by decide))
    (.loop YB .nonempty (.seq (.prim (.inc YB)) (nmv YB TP (by decide)))))

/-- The first tape written. -/
def S2 (w : List Bool) : Lists UK := ((E0.set NN [w.length]).set LL (deUnary w)).set TP (w.length :: w.map bitSym)

def tapeF (w : List Bool) (m : Nat) : Lists UK :=
  (((E0.set NN [w.length]).set LL (deUnary w)).set YB ((w.map bitElem).drop m).reverse).set TP
    (w.length :: (w.take m).map bitSym)

theorem bitElem_succ (b : Bool) : bitElem b + 1 = bitSym b := by cases b <;> rfl

theorem nruns_tape (w : List Bool) : NRuns tapeP (S1 w) (S2 w) (7 * w.length + 4) := by
  have d₁ := nruns_dup NN TP (by decide) (S1 w) (l := []) (v := w.length) (by simp only [S1]; stk_simp)
  have hTP : (S1 w) TP = [] := by simp only [S1]; stk_simp
  rw [hTP] at d₁
  have d₂ := nruns_mvAll XB YB (by decide) ((S1 w).set TP ([] ++ [w.length]))
  have hXB : ((S1 w).set TP ([] ++ [w.length])) XB = w.map bitElem := by simp only [S1]; stk_simp
  have hY0 : ((S1 w).set TP ([] ++ [w.length])) YB = [] := by simp only [S1]; stk_simp
  rw [hXB, hY0] at d₂
  have e₀ : (((S1 w).set TP ([] ++ [w.length])).set YB ([] ++ (w.map bitElem).reverse)).set XB [] = tapeF w 0 := by
    simp only [tapeF, S1, List.drop_zero, List.take_zero, List.map_nil]
    lsimp
  rw [e₀] at d₂
  have hY : ∀ m, tapeF w m YB = ((w.map bitElem).drop m).reverse := fun m => by simp only [tapeF]; stk_simp
  have hl := nruns_family_const (i := YB) (c := .nonempty) (p := .seq (.prim (.inc YB)) (nmv YB TP (by decide)))
    (tapeF w) w.length 3
    (fun m hm => by rw [hY]; exact eval_nonempty_ne (by simp; omega))
    (by rw [hY, List.drop_of_length_le (by simp)]; rfl)
    (fun m hm => by
      have hml : m < (w.map bitElem).length := by simpa using hm
      have hd : ((w.map bitElem).drop m).reverse = ((w.map bitElem).drop (m + 1)).reverse ++ [bitElem w[m]] := by
        rw [List.drop_eq_getElem_cons hml]; simp
      have e₁ := nruns_inc YB (tapeF w m) (by rw [hY, hd])
      have e₂ := nruns_mv YB TP (by decide) ((tapeF w m).set YB (((w.map bitElem).drop (m + 1)).reverse ++
        [bitElem w[m] + 1])) (by rw [Lists.set_same])
      have e : (((tapeF w m).set YB (((w.map bitElem).drop (m + 1)).reverse ++ [bitElem w[m] + 1])).set TP
          (((tapeF w m).set YB (((w.map bitElem).drop (m + 1)).reverse ++ [bitElem w[m] + 1])) TP ++
            [bitElem w[m] + 1])).set YB ((w.map bitElem).drop (m + 1)).reverse = tapeF w (m + 1) := by
        rw [bitElem_succ]
        simp only [tapeF, List.take_succ_eq_append_getElem hm, List.map_append, List.map_cons, List.map_nil]
        lsimp
      rw [e] at e₂
      exact (e₁.seq e₂).mono (by omega))
  have e : tapeF w w.length = S2 w := by
    simp only [tapeF, S2]
    rw [List.take_of_length_le (by simp), List.drop_of_length_le (by simp)]
    simp only [List.reverse_nil]
    lsimp
  rw [e] at hl
  refine (d₁.seq (d₂.seq hl)).mono ?_
  simp; omega

end Shallot.MacroPeg.KExp
