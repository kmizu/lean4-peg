import Shallot.Peg.Packrat.Machine.Read

/-!
# Sequence on the stack machine

Unknown and failure propagate immediately. A success ending at `j` reads
the second row at `j`. The temporary result is consumed and all scratch
stacks are restored, so the original rows can be reused for other cells.
-/

namespace Shallot.Packrat.Machine

open Complexity

variable {K : Nat}

/-- The second lookup for sequence, with arbitrary missing entries read as unknown. -/
def followValue (l : List Nat) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | j + 2 => (l[j]?).getD 0

/-- Consume a numeric first result on `work` and append the sequence result to `out`. -/
def followRow (r tmp idx work out : Fin K) (hrT : r ≠ tmp) (hTo : tmp ≠ out)
    (hwi : work ≠ idx) (hwo : work ≠ out) : NProg K :=
  .ite work .zero (nmv work out hwo)
    (.seq (.prim (.dec work))
      (.ite work .zero
        (.seq (.prim (.pop work)) (npushC out 1))
        (.seq (.prim (.dec work))
          (.seq (readRow r tmp idx work out hrT hTo hwi) (.prim (.pop work))))))

/-- Sequence's second lookup has a linear stack-step bound. -/
theorem nruns_followRow (r tmp idx work out : Fin K) (hrT : r ≠ tmp) (hTo : tmp ≠ out)
    (hwi : work ≠ idx) (hwo : work ≠ out) (hd : [r, tmp, idx, work, out].Nodup)
    (S : Lists K) (hT : S tmp = []) {lw : List Nat} {a : Nat}
    (hw : S work = lw ++ [a])
    (ha : ∀ j, a = j + 2 → j < (S r).length) :
    NRuns (followRow r tmp idx work out hrT hTo hwi hwo) S
      ((S.set work lw).set out (S out ++ [followValue (S r) a]))
      (6 * (S r).length + 4 * a + 20) := by
  have hrw : r ≠ work := by simp_all [List.nodup_cons]
  have hTw : tmp ≠ work := by simp_all [List.nodup_cons]
  have how : out ≠ work := Ne.symm hwo
  cases a with
  | zero =>
    have h := nruns_mv work out hwo S hw
    have he : (S.set out (S out ++ [0])).set work lw = (S.set work lw).set out (S out ++ [0]) := by
      lists_eq
    rw [he] at h
    exact (h.iteT (i := work) (c := .zero) (by rw [hw]; simp [NTest.eval])).mono (by omega)
  | succ a =>
    have d₁ := nruns_dec work S hw
    simp only [Nat.add_one_sub_one] at d₁
    let S₁ := S.set work (lw ++ [a])
    have hw₁ : S₁ work = lw ++ [a] := Lists.set_same _ _ _
    cases a with
    | zero =>
      have p := nruns_pop work S₁ hw₁
      have c := nruns_pushC out (S₁.set work lw) 1
      have he : (S₁.set work lw).set out ((S₁.set work lw) out ++ [1]) =
          (S.set work lw).set out (S out ++ [1]) := by
        simp only [S₁]; lists_eq
      rw [he] at c
      have h := (p.seq c).iteT
        (q := .seq (.prim (.dec work)) (.seq (readRow r tmp idx work out hrT hTo hwi) (.prim (.pop work))))
        (i := work) (c := .zero) (by rw [hw₁]; simp [NTest.eval])
      have h' := (d₁.seq h).iteF (p := nmv work out hwo) (i := work) (c := .zero) (by rw [hw]; simp [NTest.eval])
      exact h'.mono (by omega)
    | succ j =>
      have hj := ha j rfl
      have d₂ := nruns_dec work S₁ hw₁
      simp only [Nat.add_one_sub_one] at d₂
      let S₂ := S₁.set work (lw ++ [j])
      have hr₂ : S₂ r = S r := by simp only [S₂, S₁]; lists_at
      have hT₂ : S₂ tmp = [] := by
        simp only [S₂, S₁]
        rw [Lists.set_ne _ _ hTw, Lists.set_ne _ _ hTw]
        exact hT
      have ho₂ : S₂ out = S out := by simp only [S₂, S₁]; lists_at
      have hw₂ : S₂ work = lw ++ [j] := Lists.set_same _ _ _
      have rd := nruns_readRow r tmp idx work out hrT hTo hwi hd S₂ hT₂ hw₂
        (by rw [hr₂]; exact hj)
      have pp := nruns_pop work (S₂.set out (S₂ out ++ [(S₂ r)[j]'(by rw [hr₂]; exact hj)]))
        (l := lw) (v := j) (by rw [Lists.set_ne _ _ hwo]; exact hw₂)
      have he : (S₂.set out (S₂ out ++ [(S₂ r)[j]'(by rw [hr₂]; exact hj)])).set work lw =
          (S.set work lw).set out (S out ++ [followValue (S r) (j + 2)]) := by
        simp only [hr₂, ho₂, followValue, List.getElem?_eq_getElem hj, Option.getD_some]
        simp only [S₂, S₁]; lists_eq
      rw [he] at pp
      have h := (d₂.seq (rd.seq pp)).iteF
        (p := .seq (.prim (.pop work)) (npushC out 1)) (i := work) (c := .zero) (by rw [hw₁]; simp [NTest.eval])
      have h' := (d₁.seq h).iteF (p := nmv work out hwo) (i := work) (c := .zero) (by rw [hw]; simp [NTest.eval])
      simp only [hr₂] at h'
      exact h'.mono (by omega)

/-- Read the first row, then follow its successful end position in the second row. -/
def seqCell (a b tmp idx p work out : Fin K) (haT : a ≠ tmp) (hTw : tmp ≠ work)
    (hpi : p ≠ idx) (hbT : b ≠ tmp) (hTo : tmp ≠ out) (hwi : work ≠ idx)
    (hwo : work ≠ out) : NProg K :=
  .seq (readRow a tmp idx p work haT hTw hpi) (followRow b tmp idx work out hbT hTo hwi hwo)

/-- The machine computes the numeric sequence cell and changes only its output. -/
theorem nruns_seqCell (a b tmp idx p work out : Fin K) (haT : a ≠ tmp) (hTw : tmp ≠ work)
    (hpi : p ≠ idx) (hbT : b ≠ tmp) (hTo : tmp ≠ out) (hwi : work ≠ idx)
    (hwo : work ≠ out) (hd₁ : [a, tmp, idx, p, work].Nodup)
    (hd₂ : [b, tmp, idx, work, out].Nodup)
    (S : Lists K) (hT : S tmp = []) {lp : List Nat} {i : Nat}
    (hp : S p = lp ++ [i]) (hi : i < (S a).length)
    (ha : ∀ j, (S a)[i] = j + 2 → j < (S b).length) :
    NRuns (seqCell a b tmp idx p work out haT hTw hpi hbT hTo hwi hwo) S
      (S.set out (S out ++ [followValue (S b) ((S a)[i])]))
      (6 * (S a).length + 4 * i + 6 * (S b).length + 4 * (S a)[i] + 27) := by
  have hbw : b ≠ work := by simp_all [List.nodup_cons]
  have how : out ≠ work := Ne.symm hwo
  let v := (S a)[i]
  have rd := nruns_readRow a tmp idx p work haT hTw hpi hd₁ S hT hp hi
  let S₁ := S.set work (S work ++ [v])
  have hT₁ : S₁ tmp = [] := by simp only [S₁, Lists.set_ne _ _ hTw]; exact hT
  have hb₁ : S₁ b = S b := Lists.set_ne _ _ hbw
  have ho₁ : S₁ out = S out := Lists.set_ne _ _ how
  have fl := nruns_followRow b tmp idx work out hbT hTo hwi hwo hd₂ S₁ hT₁
    (lw := S work) (a := v) (by simp [S₁]) (fun j hj => by rw [hb₁]; exact ha j hj)
  have he : (S₁.set work (S work)).set out (S₁ out ++ [followValue (S₁ b) v]) =
      S.set out (S out ++ [followValue (S b) v]) := by
    simp only [hb₁, ho₁, S₁, Lists.set_set_u, Lists.set_get_self]
  rw [he] at fl
  simp only [hb₁] at fl
  exact (rd.seq fl).mono (by omega)

/-- Numeric sequence lookup agrees with the verified table round. -/
theorem followValue_row (g : Grammar) (x : List Char) (n : Nat)
    (a b : PExp) (i : Nat) (hi : i ≤ x.length) :
    followValue (row (iter g x n) b x.length) (code i (iter g x n a i)) =
      code i (iter g x (n + 1) (.seq a b) i) := by
  simp only [iter, F]
  cases ha : iter g x n a i with
  | none => rfl
  | some r =>
    cases r with
    | none => rfl
    | some k =>
      have hk := iter_consumption ha
      have hik : i + k ≤ x.length := by simp only [List.length_drop] at hk; omega
      have hread : (row (iter g x n) b x.length)[i + k]? =
          some (code (i + k) (iter g x n b (i + k))) := by
        rw [List.getElem?_eq_getElem (by simp; omega), row_get _ _ _ _ hik]
      simp only [code, Nat.add_succ, Nat.add_zero, followValue, hread, Option.getD_some]
      cases iter g x n b (i + k) with
      | none => rfl
      | some r => cases r <;> simp [Nat.add_assoc]

/-- On rows from a verified round, sequence costs at most `20 |x| + 47` stack steps. -/
theorem nruns_seqCell_round (g : Grammar) (x : List Char) (n : Nat) (ea eb : PExp)
    (a b tmp idx p work out : Fin K) (haT : a ≠ tmp) (hTw : tmp ≠ work)
    (hpi : p ≠ idx) (hbT : b ≠ tmp) (hTo : tmp ≠ out) (hwi : work ≠ idx)
    (hwo : work ≠ out) (hd₁ : [a, tmp, idx, p, work].Nodup)
    (hd₂ : [b, tmp, idx, work, out].Nodup) (S : Lists K) (hT : S tmp = [])
    (hra : S a = row (iter g x n) ea x.length) (hrb : S b = row (iter g x n) eb x.length)
    {lp : List Nat} {i : Nat} (hp : S p = lp ++ [i]) (hi : i ≤ x.length) :
    NRuns (seqCell a b tmp idx p work out haT hTw hpi hbT hTo hwi hwo) S
      (S.set out (S out ++ [code i (iter g x (n + 1) (.seq ea eb) i)]))
      (20 * x.length + 47) := by
  have hai : i < (S a).length := by simp only [hra, row_length]; omega
  have hvalue : (S a)[i] = code i (iter g x n ea i) := by
    simp only [hra, row_get _ _ _ _ hi]
  have hvalid : ∀ j, (S a)[i] = j + 2 → j < (S b).length := by
    intro j hj
    have hb := code_bound (g := g) (x := x) (n := n) (e := ea) hi
    rw [hvalue] at hj
    simp only [hrb, row_length]
    omega
  have hx := nruns_seqCell a b tmp idx p work out haT hTw hpi hbT hTo hwi hwo
    hd₁ hd₂ S hT hp hai hvalid
  have hresult : followValue (S b) ((S a)[i]) = code i (iter g x (n + 1) (.seq ea eb) i) := by
    rw [hvalue, hrb]
    exact followValue_row g x n ea eb i hi
  rw [hresult] at hx
  apply hx.mono
  have hla : (S a).length = x.length + 1 := by simp [hra]
  have hlb : (S b).length = x.length + 1 := by simp [hrb]
  have hb : (S a)[i] ≤ x.length + 2 := by
    rw [hvalue]
    exact code_bound hi
  omega

end Shallot.Packrat.Machine
