import Shallot.Peg.Packrat.Machine.Read

/-!
# Prioritized choice on the stack machine

Only a semantic failure in the first row triggers a second lookup. An
unknown first result remains unknown, even if the second alternative
would succeed.
-/

namespace Shallot.Packrat.Machine

open Complexity

variable {K : Nat}

/-- Numeric choice, reading the second row only for a first-result failure. -/
def altValue (l : List Nat) (i : Nat) (a : Nat) : Nat :=
  if a = 1 then (l[i]?).getD 0 else a

/-- Consume the first result and read the second alternative if required. -/
def chooseRow (r tmp idx p work out : Fin K) (hrT : r ≠ tmp) (hTo : tmp ≠ out)
    (hpi : p ≠ idx) (hwo : work ≠ out) : NProg K :=
  .ite work .zero (nmv work out hwo)
    (.seq (.prim (.dec work))
      (.ite work .zero
        (.seq (.prim (.pop work)) (readRow r tmp idx p out hrT hTo hpi))
        (.seq (.prim (.inc work)) (nmv work out hwo))))

theorem nruns_chooseRow (r tmp idx p work out : Fin K) (hrT : r ≠ tmp) (hTo : tmp ≠ out)
    (hpi : p ≠ idx) (hwo : work ≠ out) (hd : [r, tmp, idx, p, out].Nodup)
    (hrw : r ≠ work) (hTw : tmp ≠ work) (hpw : p ≠ work)
    (S : Lists K) (hT : S tmp = []) {lp lw : List Nat} {i a : Nat}
    (hp : S p = lp ++ [i]) (hw : S work = lw ++ [a]) (hi : i < (S r).length) :
    NRuns (chooseRow r tmp idx p work out hrT hTo hpi hwo) S
      ((S.set work lw).set out (S out ++ [altValue (S r) i a]))
      (6 * (S r).length + 4 * i + 15) := by
  have how : out ≠ work := Ne.symm hwo
  cases a with
  | zero =>
    have mv := nruns_mv work out hwo S hw
    have he : (S.set out (S out ++ [0])).set work lw = (S.set work lw).set out (S out ++ [0]) := by
      lists_eq
    rw [he] at mv
    exact (mv.iteT (i := work) (c := .zero) (by rw [hw]; simp)).mono (by omega)
  | succ a =>
    have dc := nruns_dec work S hw
    simp only [Nat.add_one_sub_one] at dc
    let S₁ := S.set work (lw ++ [a])
    have hw₁ : S₁ work = lw ++ [a] := Lists.set_same _ _ _
    cases a with
    | zero =>
      have pp := nruns_pop work S₁ hw₁
      let S₂ := S₁.set work lw
      have hr₂ : S₂ r = S r := by simp only [S₂, S₁]; lists_at
      have ho₂ : S₂ out = S out := by simp only [S₂, S₁]; lists_at
      have hp₂ : S₂ p = lp ++ [i] := by
        simp only [S₂, S₁, Lists.set_ne _ _ hpw]; exact hp
      have hT₂ : S₂ tmp = [] := by
        simp only [S₂, S₁, Lists.set_ne _ _ hTw]; exact hT
      have rd := nruns_readRow r tmp idx p out hrT hTo hpi hd S₂ hT₂ hp₂
        (by rw [hr₂]; exact hi)
      have he : S₂.set out (S₂ out ++ [(S₂ r)[i]'(by rw [hr₂]; exact hi)]) =
          (S.set work lw).set out (S out ++ [altValue (S r) i 1]) := by
        simp only [hr₂, ho₂]
        simp [altValue, List.getElem?_eq_getElem hi, S₂, S₁, Lists.set_set_u]
      rw [he] at rd
      simp only [hr₂] at rd
      have br := (pp.seq rd).iteT (i := work) (c := .zero)
        (q := .seq (.prim (.inc work)) (nmv work out hwo)) (by rw [hw₁]; simp)
      exact ((dc.seq br).iteF (p := nmv work out hwo) (i := work) (c := .zero)
        (by rw [hw]; simp)).mono (by omega)
    | succ a =>
      have ic := nruns_inc work S₁ hw₁
      let S₂ := S₁.set work (lw ++ [a + 1 + 1])
      have hw₂ : S₂ work = lw ++ [a + 1 + 1] := Lists.set_same _ _ _
      have mv := nruns_mv work out hwo S₂ hw₂
      have he : (S₂.set out (S₂ out ++ [a + 1 + 1])).set work lw =
          (S.set work lw).set out (S out ++ [altValue (S r) i (a + 1 + 1)]) := by
        simp only [altValue, show a + 1 + 1 ≠ 1 by omega, if_false, S₂, S₁]
        lists_eq
      rw [he] at mv
      have br := (ic.seq mv).iteF (i := work) (c := .zero)
        (p := .seq (.prim (.pop work)) (readRow r tmp idx p out hrT hTo hpi)) (by rw [hw₁]; simp)
      exact ((dc.seq br).iteF (p := nmv work out hwo) (i := work) (c := .zero)
        (by rw [hw]; simp)).mono (by omega)

/-- Read a first alternative, then conditionally read a second one. -/
def altCell (a b tmp idx p work out : Fin K) (haT : a ≠ tmp) (hTw : tmp ≠ work)
    (hpi : p ≠ idx) (hbT : b ≠ tmp) (hTo : tmp ≠ out) (hwo : work ≠ out) : NProg K :=
  .seq (readRow a tmp idx p work haT hTw hpi) (chooseRow b tmp idx p work out hbT hTo hpi hwo)

theorem nruns_altCell (a b tmp idx p work out : Fin K) (haT : a ≠ tmp) (hTw : tmp ≠ work)
    (hpi : p ≠ idx) (hbT : b ≠ tmp) (hTo : tmp ≠ out) (hwo : work ≠ out)
    (hd₁ : [a, tmp, idx, p, work].Nodup) (hd₂ : [b, tmp, idx, p, out].Nodup)
    (hbw : b ≠ work) (S : Lists K) (hT : S tmp = []) {lp : List Nat} {i : Nat}
    (hp : S p = lp ++ [i]) (hi : i < (S a).length) (hi' : i < (S b).length) :
    NRuns (altCell a b tmp idx p work out haT hTw hpi hbT hTo hwo) S
      (S.set out (S out ++ [altValue (S b) i ((S a)[i])]))
      (6 * (S a).length + 6 * (S b).length + 8 * i + 22) := by
  have hpw : p ≠ work := by simp_all [List.nodup_cons]
  have how : out ≠ work := Ne.symm hwo
  have rd := nruns_readRow a tmp idx p work haT hTw hpi hd₁ S hT hp hi
  let S₁ := S.set work (S work ++ [(S a)[i]])
  have hb₁ : S₁ b = S b := Lists.set_ne _ _ hbw
  have ho₁ : S₁ out = S out := Lists.set_ne _ _ how
  have ch := nruns_chooseRow b tmp idx p work out hbT hTo hpi hwo hd₂ hbw hTw hpw S₁
    (by simp only [S₁, Lists.set_ne _ _ hTw]; exact hT)
    (lp := lp) (lw := S work) (i := i) (a := (S a)[i])
    (by simp only [S₁, Lists.set_ne _ _ hpw]; exact hp) (by simp [S₁]) (by rw [hb₁]; exact hi')
  have he : (S₁.set work (S work)).set out (S₁ out ++ [altValue (S₁ b) i ((S a)[i])]) =
      S.set out (S out ++ [altValue (S b) i ((S a)[i])]) := by
    simp only [hb₁, ho₁, S₁, Lists.set_set_u, Lists.set_get_self]
  rw [he] at ch
  simp only [hb₁] at ch
  exact (rd.seq ch).mono (by omega)

/-- The numeric operation implements the priority of the original PEG choice. -/
theorem altValue_row (g : Grammar) (x : List Char) (n : Nat) (a b : PExp)
    (i : Nat) (hi : i ≤ x.length) :
    altValue (row (iter g x n) b x.length) i (code i (iter g x n a i)) =
      code i (iter g x (n + 1) (.alt a b) i) := by
  have hb : (row (iter g x n) b x.length)[i]? = some (code i (iter g x n b i)) := by
    rw [List.getElem?_eq_getElem (by simp; omega), row_get _ _ _ _ hi]
  simp only [iter, F]
  cases iter g x n a i with
  | none => rfl
  | some r =>
    cases r with
    | none => simp [code, altValue, hb]
    | some k =>
      have hn : i + k + 2 ≠ 1 := by omega
      simp [code, altValue, hn]

/-- A choice cell on verified rows costs at most `20 |x| + 34` stack steps. -/
theorem nruns_altCell_round (g : Grammar) (x : List Char) (n : Nat) (ea eb : PExp)
    (a b tmp idx p work out : Fin K) (haT : a ≠ tmp) (hTw : tmp ≠ work)
    (hpi : p ≠ idx) (hbT : b ≠ tmp) (hTo : tmp ≠ out) (hwo : work ≠ out)
    (hd₁ : [a, tmp, idx, p, work].Nodup) (hd₂ : [b, tmp, idx, p, out].Nodup)
    (hbw : b ≠ work) (S : Lists K) (hT : S tmp = [])
    (hra : S a = row (iter g x n) ea x.length) (hrb : S b = row (iter g x n) eb x.length)
    {lp : List Nat} {i : Nat} (hp : S p = lp ++ [i]) (hi : i ≤ x.length) :
    NRuns (altCell a b tmp idx p work out haT hTw hpi hbT hTo hwo) S
      (S.set out (S out ++ [code i (iter g x (n + 1) (.alt ea eb) i)]))
      (20 * x.length + 34) := by
  have hai : i < (S a).length := by simp only [hra, row_length]; omega
  have hbi : i < (S b).length := by simp only [hrb, row_length]; omega
  have hv : (S a)[i] = code i (iter g x n ea i) := by simp only [hra, row_get _ _ _ _ hi]
  have hx := nruns_altCell a b tmp idx p work out haT hTw hpi hbT hTo hwo
    hd₁ hd₂ hbw S hT hp hai hbi
  have he : altValue (S b) i ((S a)[i]) = code i (iter g x (n + 1) (.alt ea eb) i) := by
    rw [hv, hrb]
    exact altValue_row g x n ea eb i hi
  rw [he] at hx
  apply hx.mono
  have hla : (S a).length = x.length + 1 := by simp [hra]
  have hlb : (S b).length = x.length + 1 := by simp [hrb]
  omega

end Shallot.Packrat.Machine
