import Shallot.Peg.Packrat.Machine.Seq
import Shallot.Peg.Packrat.Machine.Not

/-!
# Repetition on the stack machine

The first failure returns empty success. A first success follows its end
position into the preceding round's repetition row. No recursive machine
call is needed: every cell only reads already stored rows.
-/

namespace Shallot.Packrat.Machine

open Complexity

variable {K : Nat}

/-- Repetition on valid rows, where a repetition entry can never be failure. -/
def starValue (l : List Nat) (i a : Nat) : Nat :=
  if a = 1 then i + 2 else followValue l a

/-- Consume a first result and compute one repetition step. -/
def repeatRow (r tmp idx p work out : Fin K) (hrT : r ≠ tmp) (hTo : tmp ≠ out)
    (hwi : work ≠ idx) (hwo : work ≠ out) (hpo : p ≠ out) : NProg K :=
  .ite work .zero (nmv work out hwo)
    (.seq (.prim (.dec work))
      (.ite work .zero (.seq (.prim (.pop work)) (emptySuccess p out hpo))
        (.seq (.prim (.inc work)) (followRow r tmp idx work out hrT hTo hwi hwo))))

theorem nruns_repeatRow (r tmp idx p work out : Fin K) (hrT : r ≠ tmp) (hTo : tmp ≠ out)
    (hwi : work ≠ idx) (hwo : work ≠ out) (hpo : p ≠ out)
    (hd : [r, tmp, idx, work, out].Nodup) (hpw : p ≠ work)
    (S : Lists K) (hT : S tmp = []) {lp lw : List Nat} {i a : Nat}
    (hp : S p = lp ++ [i]) (hw : S work = lw ++ [a])
    (ha : ∀ j, a = j + 2 → j < (S r).length) :
    NRuns (repeatRow r tmp idx p work out hrT hTo hwi hwo hpo) S
      ((S.set work lw).set out (S out ++ [starValue (S r) i a]))
      (6 * (S r).length + 4 * a + 30) := by
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
      have es := nruns_emptySuccess p out hpo (S₁.set work lw)
        (lp := lp) (i := i) (by simp only [S₁, Lists.set_ne _ _ hpw]; exact hp)
      have he : (S₁.set work lw).set out ((S₁.set work lw) out ++ [i + 2]) =
          (S.set work lw).set out (S out ++ [i + 2]) := by
        simp only [S₁]; lists_eq
      rw [he] at es
      have br := (pp.seq es).iteT (i := work) (c := .zero)
        (q := .seq (.prim (.inc work)) (followRow r tmp idx work out hrT hTo hwi hwo))
        (by rw [hw₁]; simp)
      exact ((dc.seq br).iteF (p := nmv work out hwo) (i := work) (c := .zero)
        (by rw [hw]; simp)).mono (by omega)
    | succ j =>
      have ic := nruns_inc work S₁ hw₁
      have he : S₁.set work (lw ++ [j + 1 + 1]) = S := by
        simp only [S₁, Lists.set_set_u, ← hw, Lists.set_get_self]
      rw [he] at ic
      have fl := nruns_followRow r tmp idx work out hrT hTo hwi hwo hd S hT hw ha
      have br := (ic.seq fl).iteF (i := work) (c := .zero)
        (p := .seq (.prim (.pop work)) (emptySuccess p out hpo)) (by rw [hw₁]; simp)
      have hx := (dc.seq br).iteF (p := nmv work out hwo) (i := work) (c := .zero) (by rw [hw]; simp)
      have hv : starValue (S r) i (j + 1 + 1) = followValue (S r) (j + 1 + 1) := by
        simp [starValue]
      rw [hv]
      exact hx.mono (by omega)

/-- A repetition cell reads its body, then the previous repetition row if necessary. -/
def starCell (a b tmp idx p work out : Fin K) (haT : a ≠ tmp) (hTw : tmp ≠ work)
    (hpi : p ≠ idx) (hbT : b ≠ tmp) (hTo : tmp ≠ out) (hwi : work ≠ idx)
    (hwo : work ≠ out) (hpo : p ≠ out) : NProg K :=
  .seq (readRow a tmp idx p work haT hTw hpi) (repeatRow b tmp idx p work out hbT hTo hwi hwo hpo)

theorem nruns_starCell (a b tmp idx p work out : Fin K) (haT : a ≠ tmp) (hTw : tmp ≠ work)
    (hpi : p ≠ idx) (hbT : b ≠ tmp) (hTo : tmp ≠ out) (hwi : work ≠ idx)
    (hwo : work ≠ out) (hpo : p ≠ out) (hd₁ : [a, tmp, idx, p, work].Nodup)
    (hd₂ : [b, tmp, idx, work, out].Nodup)
    (S : Lists K) (hT : S tmp = []) {lp : List Nat} {i : Nat}
    (hp : S p = lp ++ [i]) (hi : i < (S a).length)
    (ha : ∀ j, (S a)[i] = j + 2 → j < (S b).length) :
    NRuns (starCell a b tmp idx p work out haT hTw hpi hbT hTo hwi hwo hpo) S
      (S.set out (S out ++ [starValue (S b) i ((S a)[i])]))
      (6 * (S a).length + 4 * i + 6 * (S b).length + 4 * (S a)[i] + 37) := by
  have hbw : b ≠ work := by simp_all [List.nodup_cons]
  have hpw : p ≠ work := by simp_all [List.nodup_cons]
  have how : out ≠ work := Ne.symm hwo
  have rd := nruns_readRow a tmp idx p work haT hTw hpi hd₁ S hT hp hi
  let S₁ := S.set work (S work ++ [(S a)[i]])
  have hb₁ : S₁ b = S b := Lists.set_ne _ _ hbw
  have ho₁ : S₁ out = S out := Lists.set_ne _ _ how
  have fl := nruns_repeatRow b tmp idx p work out hbT hTo hwi hwo hpo hd₂ hpw S₁
    (by simp only [S₁, Lists.set_ne _ _ hTw]; exact hT)
    (lp := lp) (lw := S work) (i := i) (a := (S a)[i])
    (by simp only [S₁, Lists.set_ne _ _ hpw]; exact hp) (by simp [S₁])
    (fun j hj => by rw [hb₁]; exact ha j hj)
  have he : (S₁.set work (S work)).set out (S₁ out ++ [starValue (S₁ b) i ((S a)[i])]) =
      S.set out (S out ++ [starValue (S b) i ((S a)[i])]) := by
    simp only [hb₁, ho₁, S₁, Lists.set_set_u, Lists.set_get_self]
  rw [he] at fl
  simp only [hb₁] at fl
  exact (rd.seq fl).mono (by omega)

/-- A repetition entry can be unknown or successful, but never semantic failure. -/
theorem iter_star_ne_fail (g : Grammar) (x : List Char) (n : Nat) (e : PExp) (i : Nat) :
    iter g x n (.star e) i ≠ some none := by
  intro h
  obtain ⟨o, hd, he⟩ := iter_sound h
  cases o with
  | fail => exact starNeverFails hd rfl
  | ok _ _ => cases he

/-- On verified rows, the machine's repetition step agrees with the original round. -/
theorem starValue_row (g : Grammar) (x : List Char) (n : Nat) (e : PExp)
    (i : Nat) (hi : i ≤ x.length) :
    starValue (row (iter g x n) (.star e) x.length) i (code i (iter g x n e i)) =
      code i (iter g x (n + 1) (.star e) i) := by
  simp only [iter, F]
  cases ha : iter g x n e i with
  | none => rfl
  | some r =>
    cases r with
    | none => simp [starValue, code]
    | some k =>
      have hk := iter_consumption ha
      have hik : i + k ≤ x.length := by simp only [List.length_drop] at hk; omega
      have hread : (row (iter g x n) (.star e) x.length)[i + k]? =
          some (code (i + k) (iter g x n (.star e) (i + k))) := by
        rw [List.getElem?_eq_getElem (by simp; omega), row_get _ _ _ _ hik]
      have hn : i + k + 2 ≠ 1 := by omega
      simp only [starValue, code, hn, if_false, Nat.add_succ, Nat.add_zero,
        followValue, hread, Option.getD_some]
      cases ht : iter g x n (.star e) (i + k) with
      | none => rfl
      | some r =>
        cases r with
        | none => exact False.elim (iter_star_ne_fail g x n e (i + k) ht)
        | some m => simp [Nat.add_assoc]

/-- On verified rows, repetition costs at most `20 |x| + 57` stack steps. -/
theorem nruns_starCell_round (g : Grammar) (x : List Char) (n : Nat) (e : PExp)
    (a b tmp idx p work out : Fin K) (haT : a ≠ tmp) (hTw : tmp ≠ work)
    (hpi : p ≠ idx) (hbT : b ≠ tmp) (hTo : tmp ≠ out) (hwi : work ≠ idx)
    (hwo : work ≠ out) (hpo : p ≠ out) (hd₁ : [a, tmp, idx, p, work].Nodup)
    (hd₂ : [b, tmp, idx, work, out].Nodup) (S : Lists K) (hT : S tmp = [])
    (hra : S a = row (iter g x n) e x.length) (hrb : S b = row (iter g x n) (.star e) x.length)
    {lp : List Nat} {i : Nat} (hp : S p = lp ++ [i]) (hi : i ≤ x.length) :
    NRuns (starCell a b tmp idx p work out haT hTw hpi hbT hTo hwi hwo hpo) S
      (S.set out (S out ++ [code i (iter g x (n + 1) (.star e) i)]))
      (20 * x.length + 57) := by
  have hai : i < (S a).length := by simp only [hra, row_length]; omega
  have hv : (S a)[i] = code i (iter g x n e i) := by simp only [hra, row_get _ _ _ _ hi]
  have hvalid : ∀ j, (S a)[i] = j + 2 → j < (S b).length := by
    intro j hj
    have hb := code_bound (g := g) (x := x) (n := n) (e := e) hi
    rw [hv] at hj
    simp only [hrb, row_length]
    omega
  have hx := nruns_starCell a b tmp idx p work out haT hTw hpi hbT hTo hwi hwo hpo
    hd₁ hd₂ S hT hp hai hvalid
  have he : starValue (S b) i ((S a)[i]) = code i (iter g x (n + 1) (.star e) i) := by
    rw [hv, hrb]
    exact starValue_row g x n e i hi
  rw [he] at hx
  apply hx.mono
  have hla : (S a).length = x.length + 1 := by simp [hra]
  have hlb : (S b).length = x.length + 1 := by simp [hrb]
  have hb : (S a)[i] ≤ x.length + 2 := by rw [hv]; exact code_bound hi
  omega

end Shallot.Packrat.Machine
