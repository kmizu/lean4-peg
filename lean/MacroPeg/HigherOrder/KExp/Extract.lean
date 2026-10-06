import MacroPeg.HigherOrder.KExp.DiagFront
import Complexity.Univ.Output

/-!
# The output of a simulation as a fresh input

`extractP` clears the table and the configuration, reads tape `0` from `TP` up to its first blank (`readOut`), and
leaves its bits on stack `0` as an input, the first bit on top, with every other stack empty (`extractP_runs`).

The cells of tape `0` are read in order through a flag on `DC` (set at the first blank); the bits go to `LL`,
which is finally turned over onto stack `0`.
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Complexity.Univ
open Shallot.MacroPeg.HO

/-! ## Reading up to the first blank, cell by cell -/

def ostep : Bool × List Nat → Nat → Bool × List Nat
  | (false, q), x => if x = 0 then (true, q) else (false, q ++ [if x = 2 then 1 else 0])
  | (true, q), _ => (true, q)

theorem ofold_true : ∀ (t : List Nat) (q : List Nat), t.foldl ostep (true, q) = (true, q)
  | [], _ => rfl
  | _ :: t, q => by rw [List.foldl_cons]; exact ofold_true t q

theorem ofold_false : ∀ (t : List Nat) (q : List Nat), (t.foldl ostep (false, q)).2 = q ++ (readOut t).map bitElem
  | [], q => by simp [readOut]
  | x :: t, q => by
    rw [List.foldl_cons]
    by_cases hx : x = 0
    · subst hx
      rw [show ostep (false, q) 0 = (true, q) from rfl, ofold_true]
      simp [readOut]
    · rw [show ostep (false, q) x = (false, q ++ [if x = 2 then 1 else 0]) by simp [ostep, hx], ofold_false t]
      have e : readOut (x :: t) = (x == 2) :: readOut t := by
        simp [readOut, hx]
      rw [e]
      by_cases h2 : x = 2 <;> simp [h2, bitElem]

theorem readOut_length (t : List Nat) : (readOut t).length ≤ t.length := by
  simp only [readOut, List.length_map]
  exact (List.takeWhile_prefix _).length_le

/-! ## One cell -/

theorem caseTop_default_runs (i : Fin UK) : ∀ (ps : List (NProg UK)) (q : NProg UK) (v : Nat) (S : Lists UK)
    (l : List Nat), S i = l ++ [v + ps.length] → ∀ (S' : Lists UK) (T : Nat),
      NRuns q (S.set i (l ++ [v])) S' T → NRuns (caseTop i ps q) S S' (T + 2 * ps.length)
  | [], q, v, S, l, hS, S', T, h => by
    simp only [List.length_nil, Nat.add_zero] at hS ⊢
    rw [← hS, Lists.set_get_self] at h; exact h
  | p :: ps, q, v, S, l, hS, S', T, h => by
    simp only [List.length_cons] at hS ⊢
    have hS' : S i = l ++ [(v + ps.length) + 1] := by rw [hS]; congr 2
    have h₁ := nruns_dec i S hS'
    simp only [Nat.add_sub_cancel] at h₁
    have h₂ := caseTop_default_runs i ps q v (S.set i (l ++ [v + ps.length])) l (by simp) S' T
      (by rw [Lists.set_set_u]; exact h)
    exact ((h₁.seq h₂).iteF (by rw [hS']; simp)).mono (by omega)

def cellPs : List (NProg UK) := [.prim (.inc DC), .prim (.pushZ LL), .seq (.prim (.pushZ LL)) (.prim (.inc LL))]

def cellQ : NProg UK := .seq (.prim (.pop YB)) (.prim (.pushZ LL))

def cellP : NProg UK := caseTop YB cellPs cellQ

/-- The stacks after one cell `x` with the flag down. -/
def cellOut (S : Lists UK) (l q : List Nat) (x : Nat) : Lists UK :=
  if x = 0 then (S.set YB l).set DC [1] else (S.set YB l).set LL (q ++ [if x = 2 then 1 else 0])

theorem cell_runs (S : Lists UK) {l q : List Nat} {x : Nat} (hy : S YB = l ++ [x]) (hl : S LL = q)
    (hd : S DC = [] ++ [0]) : NRuns cellP S (cellOut S l q x) 12 := by
  match x, hy with
  | 0, hy =>
    have h := nruns_inc DC (S.set YB l) (l := []) (v := 0) (by rw [Lists.set_ne _ _ (by decide), hd])
    have := caseTop_runs YB cellPs cellQ 0 (by decide) S l hy _ 1 h
    refine this.mono (by omega)
  | 1, hy =>
    have h := nruns_pushZ LL (S.set YB l)
    rw [Lists.set_ne _ _ (by decide), hl] at h
    have := caseTop_runs YB cellPs cellQ 1 (by decide) S l hy _ 1 h
    refine this.mono (by omega)
  | 2, hy =>
    have h₁ := nruns_pushZ LL (S.set YB l)
    rw [Lists.set_ne _ _ (by decide), hl] at h₁
    have h₂ := nruns_inc LL ((S.set YB l).set LL (q ++ [0])) (l := q) (v := 0) (by simp)
    rw [Lists.set_set_u] at h₂
    have := caseTop_runs YB cellPs cellQ 2 (by decide) S l hy _ 2 (h₁.seq h₂)
    refine this.mono (by omega)
  | v + 3, hy =>
    have h₁ := nruns_pop YB (S.set YB (l ++ [v])) (l := l) (v := v) (by simp)
    rw [Lists.set_set_u] at h₁
    have h₂ := nruns_pushZ LL (S.set YB l)
    rw [Lists.set_ne _ _ (by decide), hl] at h₂
    have := caseTop_default_runs YB cellPs cellQ v S l hy _ 2 (h₁.seq h₂)
    have e : cellOut S l q (v + 3) = (S.set YB l).set LL (q ++ [0]) := by
      simp only [cellOut, if_neg (show v + 3 ≠ 0 by omega), if_neg (show v + 3 ≠ 2 by omega)]
    rw [e]
    refine this.mono (by simp [cellPs])

/-! ## The loop over tape `0` -/

def extBody : NProg UK := .seq (.prim (.dec CN)) (.ite DC .zero cellP (.prim (.pop YB)))

def extMain : NProg UK :=
  .seq (nmv YB CN (by decide)) (.seq (.prim (.pushZ DC)) (.seq (.loop CN .pos extBody)
    (.seq (.prim (.pop CN)) (.seq (.prim (.pop DC)) (nclr YB)))))

def ofo (t : List Nat) (m : Nat) : Bool × List Nat := (t.take m).foldl ostep (false, [])

def extF (t e : List Nat) (m : Nat) : Lists UK :=
  (((E0.set YB (e ++ (t.drop m).reverse)).set CN [t.length - m]).set DC [if (ofo t m).1 then 1 else 0]).set LL
    (ofo t m).2

theorem ext_body (t e : List Nat) {m : Nat} (hm : m < t.length) :
    NRuns extBody (extF t e m) (extF t e (m + 1)) 14 := by
  have hdrop : (t.drop m).reverse = (t.drop (m + 1)).reverse ++ [t[m]] := by
    rw [List.drop_eq_getElem_cons hm]; simp
  have hof : ofo t (m + 1) = ostep (ofo t m) t[m] := by
    simp only [ofo]; rw [List.take_succ_eq_append_getElem hm, List.foldl_append]; rfl
  have d₁ := nruns_dec CN (extF t e m) (l := []) (v := t.length - m) (by simp only [extF]; stk_simp)
  let A := (extF t e m).set CN ([] ++ [t.length - m - 1])
  have hy : A YB = (e ++ (t.drop (m + 1)).reverse) ++ [t[m]] := by
    simp only [A, extF]; stk_simp; try exact hdrop
  have hl : A LL = (ofo t m).2 := by simp only [A, extF]; stk_simp
  have hF1 : extF t e (m + 1) = (((E0.set YB (e ++ (t.drop (m + 1)).reverse)).set CN [t.length - m - 1]).set DC
      [if (ostep (ofo t m) t[m]).1 then 1 else 0]).set LL (ostep (ofo t m) t[m]).2 := by
    simp only [extF, hof, show t.length - (m + 1) = t.length - m - 1 by omega]
  rcases hr : ofo t m with ⟨fl, q⟩
  rw [hr] at hl hF1
  cases fl with
  | true =>
    have hd : A DC = [] ++ [1] := by simp only [A, extF, hr]; stk_simp
    have d₂ := nruns_pop YB A hy
    have e : A.set YB (e ++ (t.drop (m + 1)).reverse) = extF t e (m + 1) := by
      rw [hF1]; simp only [A, extF, hr, ostep]; lsimp
    rw [e] at d₂
    have x := d₂.iteF (i := DC) (c := .zero) (p := cellP) (by rw [hd]; exact eval_zero_succ [] 0)
    exact (d₁.seq x).mono (by omega)
  | false =>
    have hd : A DC = [] ++ [0] := by simp only [A, extF, hr]; stk_simp
    have d₂ := cell_runs A hy hl hd
    have e : cellOut A (e ++ (t.drop (m + 1)).reverse) q t[m] = extF t e (m + 1) := by
      rw [hF1]
      by_cases h0 : t[m] = 0
      · simp only [cellOut, h0, if_true, A, extF, hr, ostep]; lsimp
      · simp only [cellOut, h0, if_false, A, extF, hr, ostep]; lsimp
    rw [e] at d₂
    have x := d₂.iteT (i := DC) (c := .zero) (q := .prim (.pop YB)) (by rw [hd]; exact eval_zero_zero [])
    exact (d₁.seq x).mono (by omega)

theorem ofo_end (t : List Nat) : (ofo t t.length).2 = (readOut t).map bitElem := by
  simp only [ofo, List.take_length]; rw [ofold_false]; rfl

/-- After the loop: the bits of tape `0` on `LL`. -/
def SQ (t : List Nat) : Lists UK := E0.set LL ((readOut t).map bitElem)

theorem nruns_extMain (t e : List Nat) :
    NRuns extMain (E0.set YB (e ++ t.reverse ++ [t.length])) (SQ t) (15 * t.length + 2 * e.length + 10) := by
  let A := E0.set YB (e ++ t.reverse ++ [t.length])
  have d₁ := nruns_mv YB CN (by decide) A (l := e ++ t.reverse) (v := t.length) (by simp only [A]; stk_simp)
  have hc : A CN = [] := by simp only [A]; stk_simp
  rw [hc] at d₁
  let A₁ := (A.set CN ([] ++ [t.length])).set YB (e ++ t.reverse)
  have d₂ := nruns_pushZ DC A₁
  have hd : A₁ DC = [] := by simp only [A₁, A]; stk_simp
  rw [hd] at d₂
  have e₀ : A₁.set DC ([] ++ [0]) = extF t e 0 := by
    simp only [A₁, A, extF, ofo, List.drop_zero, List.take_zero, List.foldl_nil, Nat.sub_zero]; lsimp
  rw [e₀] at d₂
  have hCN : ∀ m, extF t e m CN = [] ++ [t.length - m] := fun m => by simp only [extF]; stk_simp
  have hl := nruns_family_const (i := CN) (c := .pos) (p := extBody) (extF t e) t.length 14
    (fun m hm => by rw [hCN, show t.length - m = (t.length - m - 1) + 1 by omega]; exact eval_pos_succ [] _)
    (by rw [hCN, Nat.sub_self]; exact eval_pos_zero [])
    (fun m hm => ext_body t e hm)
  have d₄ := nruns_pop CN (extF t e t.length) (by rw [hCN, Nat.sub_self])
  have d₅ := nruns_pop DC ((extF t e t.length).set CN []) (l := [])
    (v := if (ofo t t.length).1 then 1 else 0) (by simp only [extF]; stk_simp)
  let B := ((extF t e t.length).set CN []).set DC []
  have d₆ := nruns_clr YB B
  have hy : B YB = e := by simp only [B, extF, List.drop_length]; stk_simp
  rw [hy] at d₆
  have e₁ : B.set YB [] = SQ t := by
    simp only [B, extF, SQ, ofo_end]; lsimp
  rw [e₁] at d₆
  exact (d₁.seq (d₂.seq (hl.seq (d₄.seq (d₅.seq d₆))))).mono (by omega)

/-! ## The whole extraction -/

def clrP : NProg UK := .seq (nclr TBL) (.seq (nclr KS) (.seq (nclr NA) (.seq (nclr ST) (nclr POS))))

def extractP : NProg UK :=
  .seq (.seq clrP (nmvAll TP YB (by decide))) (.seq (.ite YB .nonempty extMain (nskip YB)) (nmvAll LL TBL (by decide)))

def extractCost (S : Lists UK) : Nat :=
  1000 * ((S TBL).length + (S KS).length + (S NA).length + (S ST).length + (S POS).length + (S TP).length +
    (S TP).sum + 2) ^ 2

theorem rest_nil (S : Lists UK) (hC : S CNT = []) (hs : UScratch S) (q : Fin UK) (h0 : q.val ≠ 0)
    (h1 : q.val ≠ 1) (h2 : q.val ≠ 2) (h3 : q.val ≠ 3) (h4 : q.val ≠ 4) (h5 : q.val ≠ 5) : S q = [] := by
  by_cases h6 : q.val = 6
  · have : q = CNT := Fin.ext h6
    rw [this]; exact hC
  · exact hs q (by omega)

theorem nruns_clr5 (S : Lists UK) (hC : S CNT = []) (hs : UScratch S) :
    NRuns (.seq clrP (nmvAll TP YB (by decide))) S (E0.set YB (S TP).reverse)
      (2 * ((S TBL).length + (S KS).length + (S NA).length + (S ST).length + (S POS).length) + 5 +
        (3 * (S TP).length + 1)) := by
  have d₁ := nruns_clr TBL S
  have d₂ := nruns_clr KS (S.set TBL [])
  have d₃ := nruns_clr NA ((S.set TBL []).set KS [])
  have d₄ := nruns_clr ST (((S.set TBL []).set KS []).set NA [])
  have d₅ := nruns_clr POS ((((S.set TBL []).set KS []).set NA []).set ST [])
  let S₅ := ((((S.set TBL []).set KS []).set NA []).set ST []).set POS []
  have d₆ := nruns_mvAll TP YB (by decide) S₅
  have hy : S₅ YB = [] := by simp only [S₅, get_set, v_TBL, v_KS, v_NA, v_ST, v_POS, v_YB]; exact hs YB (by decide)
  have ht : S₅ TP = S TP := by simp only [S₅, get_set, v_TBL, v_KS, v_NA, v_ST, v_POS, v_TP]; rfl
  rw [hy, ht, List.nil_append] at d₆
  have e : (S₅.set YB (S TP).reverse).set TP [] = E0.set YB (S TP).reverse := by
    funext q
    simp only [S₅, get_set, E0, v_TBL, v_KS, v_NA, v_ST, v_POS, v_TP, v_YB]
    repeat' split
    all_goals first | rfl | (exfalso; omega) |
      exact rest_nil S hC hs q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [e] at d₆
  have l₂ : ((S.set TBL []) KS).length = (S KS).length := by rw [Lists.set_ne _ _ (by decide)]
  have l₃ : (((S.set TBL []).set KS []) NA).length = (S NA).length := by
    rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide)]
  have l₄ : ((((S.set TBL []).set KS []).set NA []) ST).length = (S ST).length := by
    rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide)]
  have l₅ : (((((S.set TBL []).set KS []).set NA []).set ST []) POS).length = (S POS).length := by
    rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide),
      Lists.set_ne _ _ (by decide)]
  rw [l₂] at d₂; rw [l₃] at d₃; rw [l₄] at d₄; rw [l₅] at d₅
  exact (d₁.seq (d₂.seq (d₃.seq (d₄.seq d₅)))).seq d₆ |>.mono (by omega)

/-- **The output as a fresh input.** -/
theorem extractP_runs (S : Lists UK) (ts : List (List Nat)) (hT : S TP = encTapes ts) (hC : S CNT = [])
    (hs : UScratch S) :
    NRuns extractP S (nInit UK (readOut (ts.getD 0 []))) (extractCost S) := by
  have r₁ := nruns_clr5 S hC hs
  have hX : ∀ x : Nat, 25 * x ≤ 1000 * x ^ 2 := fun x => by
    rw [Nat.pow_two]; rcases x with _ | x
    · simp
    · have := Nat.le_mul_self (x + 1); omega
  cases ts with
  | nil =>
    have hT' : S TP = [] := by rw [hT]; rfl
    rw [hT'] at r₁
    have r₂ := nruns_skip YB (E0.set YB ([] : List Nat).reverse)
    have x := r₂.iteF (i := YB) (c := .nonempty) (p := extMain) (by simp only [List.reverse_nil]; stk_simp)
    have r₃ := nruns_mvAll LL TBL (by decide) (E0.set YB ([] : List Nat).reverse)
    have e : (((E0.set YB ([] : List Nat).reverse).set TBL ((E0.set YB ([] : List Nat).reverse) TBL ++
        ((E0.set YB ([] : List Nat).reverse) LL).reverse)).set LL []) = nInit UK (readOut ((([] : List (List Nat))).getD 0 [])) := by
      rw [nInit_eq]; simp only [List.reverse_nil, List.getD_nil, readOut, List.takeWhile_nil, List.map_nil]; lsimp
    rw [e] at r₃
    refine (r₁.seq (x.seq r₃)).mono ?_
    have := hX ((S TBL).length + (S KS).length + (S NA).length + (S ST).length + (S POS).length + (S TP).length +
      (S TP).sum + 2)
    have h0 : ((E0.set YB ([] : List Nat).reverse) LL).length = 0 := by stk_simp
    unfold extractCost; rw [h0]; simp only [List.length_nil]
    omega
  | cons t ts' =>
    have hT' : (S TP).reverse = (encTapes ts').reverse ++ t.reverse ++ [t.length] := by
      rw [hT]; simp [encTapes]
    rw [hT'] at r₁
    have r₂ := nruns_extMain t (encTapes ts').reverse
    have x := r₂.iteT (i := YB) (c := .nonempty) (q := nskip YB) (eval_nonempty_ne (by simp))
    have r₃ := nruns_mvAll LL TBL (by decide) (SQ t)
    have e : (((SQ t).set TBL ((SQ t) TBL ++ ((SQ t) LL).reverse)).set LL []) =
        nInit UK (readOut ((t :: ts').getD 0 [])) := by
      rw [nInit_eq]; simp only [SQ, List.getD_cons_zero]; lsimp
    rw [e] at r₃
    refine (r₁.seq (x.seq r₃)).mono ?_
    have hlen : (S TP).length = t.length + 1 + (encTapes ts').length := by rw [hT]; simp [encTapes]; omega
    have hq : ((SQ t) LL).length ≤ t.length := by
      have : (SQ t) LL = (readOut t).map bitElem := by simp only [SQ]; stk_simp
      rw [this, List.length_map]; exact readOut_length t
    have := hX ((S TBL).length + (S KS).length + (S NA).length + (S ST).length + (S POS).length + (S TP).length +
      (S TP).sum + 2)
    unfold extractCost
    simp only [List.length_reverse]
    omega

end Shallot.MacroPeg.KExp
