import MacroPeg.CBV.LiteralMachine
import Shallot.Peg.Packrat.Machine.Literal

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.Packrat.Machine Shallot.MacroPeg.KExp

/-- A constant literal scans toward smaller remaining-length positions. -/
def fixedScan : List Char → List Nat → Nat → Nat × Nat
  | [], _, q => (q + 2, q)
  | c :: cs, row, q =>
    if (chrTest c).eval (row.getD q 0) then fixedScan cs row (q - 1) else (1, q)

theorem fixedScan_bound (s : List Char) (row : List Nat) (q : Nat) : (fixedScan s row q).2 ≤ q := by
  induction s generalizing q with
  | nil => simp [fixedScan]
  | cons c cs ih =>
    simp only [fixedScan]
    split
    · exact Nat.le_trans (ih (q - 1)) (by omega)
    · exact Nat.le_refl _

theorem fixedScan_value (s x : List Char) (q : Nat) (hq : q ≤ x.length) :
    (fixedScan s (mirrorRow x) q).1 = literalCode s (sfx x q) := by
  induction s generalizing q with
  | nil => simp [fixedScan, literalCode, Shallot.stripPrefix?, sfx_length hq]
  | cons c cs ih =>
    cases hs : sfx x q with
    | nil =>
      simp only [fixedScan, mirrorRow_nil hq hs, chrTest_end, Bool.false_eq_true, if_false]
      simp [literalCode, hs, Shallot.stripPrefix?]
    | cons d ds =>
      have hh := mirrorRow_cons hq hs
      have ht := sfx_tail hq hs
      have hi := ih (q - 1) (by omega)
      rw [ht] at hi
      simp only [fixedScan, hh, chrTest_char]
      cases he : Shallot.beqChar c d with
      | false => simp [he, literalCode, hs, Shallot.stripPrefix?]
      | true => simpa [he, literalCode, hs, Shallot.stripPrefix?] using hi

def fixedLiteralBody {K : Nat} (r : LiteralRegs K) : List Char → NProg K
  | [] => emptySuccess (r.get 3) (r.get 16) (r.ne (by decide))
  | c :: cs => readTest (r.get 0) (r.get 1) (r.get 2) (r.get 3) (r.get 5)
      (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))
      (chrTest c).flags (chrTest c).fallback
      (.seq (.prim (.dec (r.get 3))) (fixedLiteralBody r cs)) (npushC (r.get 16) 1)

/-- Each constant-literal body preserves its caller's stacks and changes only cursor and answer. -/
theorem fixedLiteralBody_runs {K : Nat} (r : LiteralRegs K) (s x : List Char) (S : Lists K)
    (hrow : S (r.get 0) = mirrorRow x) (ht : S (r.get 1) = [])
    {lc : List Nat} {q : Nat} (hc : S (r.get 3) = lc ++ [q]) (hq : q ≤ x.length) :
    NRuns (fixedLiteralBody r s) S
      ((S.set (r.get 3) (lc ++ [(fixedScan s (mirrorRow x) q).2])).set (r.get 16)
        (S (r.get 16) ++ [(fixedScan s (mirrorRow x) q).1])) (literalCost s x.length) := by
  induction s generalizing S q with
  | nil =>
    simpa only [fixedLiteralBody, fixedScan, ← hc, Lists.set_get_self, literalCost] using
      nruns_emptySuccess (r.get 3) (r.get 16) (r.ne (by decide)) S hc
  | cons c cs ih =>
    have hri : q < (S (r.get 0)).length := by rw [hrow, mirrorRow_length]; omega
    have hv : (S (r.get 0))[q] = (mirrorRow x).getD q 0 := by
      exact (List.getElem_eq_getD 0).trans (congrArg (fun row : List Nat => row.getD q 0) hrow)
    have hb : NRuns
        (if (chrTest c).eval ((S (r.get 0))[q]) then
          .seq (.prim (.dec (r.get 3))) (fixedLiteralBody r cs) else npushC (r.get 16) 1) S
        ((S.set (r.get 3) (lc ++ [(fixedScan (c :: cs) (mirrorRow x) q).2])).set (r.get 16)
          (S (r.get 16) ++ [(fixedScan (c :: cs) (mirrorRow x) q).1]))
        (1 + literalCost cs x.length) := by
      rw [hv]
      cases he : (chrTest c).eval ((mirrorRow x).getD q 0) with
      | false =>
        simp only [he, Bool.false_eq_true, if_false, fixedScan, ← hc, Lists.set_get_self]
        exact (nruns_pushC (r.get 16) S 1).mono (by have := literalCost_pos cs x.length; omega)
      | true =>
        simp only [he, if_true, fixedScan]
        have xd := nruns_dec (r.get 3) S hc
        let S₁ := S.set (r.get 3) (lc ++ [q - 1])
        have xb := ih S₁ (q := q - 1) (by simp [S₁, Lists.set, hrow])
          (by simp [S₁, Lists.set, ht]) (by simp [S₁]) (by omega)
        have hout : (S₁.set (r.get 3) (lc ++ [(fixedScan cs (mirrorRow x) (q - 1)).2])).set (r.get 16)
            (S₁ (r.get 16) ++ [(fixedScan cs (mirrorRow x) (q - 1)).1]) =
            (S.set (r.get 3) (lc ++ [(fixedScan cs (mirrorRow x) (q - 1)).2])).set (r.get 16)
              (S (r.get 16) ++ [(fixedScan cs (mirrorRow x) (q - 1)).1]) := by
          simp [S₁, Lists.set_set_u, Lists.set_ne]
        rw [hout] at xb
        exact xd.seq xb
    have hd : [r.get 0, r.get 1, r.get 2, r.get 3, r.get 5].Nodup := by simp [List.nodup_cons]
    have xr := nruns_readTest (r.get 0) (r.get 1) (r.get 2) (r.get 3) (r.get 5)
      (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)) hd
      (chrTest c).flags (chrTest c).fallback _ _ S _ ht hc hri hb
    exact xr.mono (by rw [hrow, mirrorRow_length]; simp only [literalCost]; omega)

def fixedLiteralP {K : Nat} (r : LiteralRegs K) (s : List Char) : NProg K :=
  .seq (.prim (.dup (r.get 15) (r.get 3) (r.ne (by decide))))
    (.seq (fixedLiteralBody r s) (.prim (.pop (r.get 3))))

theorem fixedLiteral_runs {K : Nat} (r : LiteralRegs K) (s x : List Char) (S : Lists K)
    (hrow : S (r.get 0) = mirrorRow x) (ht : S (r.get 1) = [])
    {lp : List Nat} {q : Nat} (hp : S (r.get 15) = lp ++ [q]) (hq : q ≤ x.length) :
    NRuns (fixedLiteralP r s) S
      (S.set (r.get 16) (S (r.get 16) ++ [literalCode s (sfx x q)])) (literalCost s x.length + 2) := by
  have xd := nruns_dup (r.get 15) (r.get 3) (r.ne (by decide)) S hp
  let S₁ := S.set (r.get 3) (S (r.get 3) ++ [q])
  have xb := fixedLiteralBody_runs r s x S₁ (by simp [S₁, Lists.set, hrow])
    (by simp [S₁, Lists.set, ht]) (lc := S (r.get 3)) (by simp [S₁]) hq
  let S₂ := (S₁.set (r.get 3) (S (r.get 3) ++ [(fixedScan s (mirrorRow x) q).2])).set (r.get 16)
    (S₁ (r.get 16) ++ [(fixedScan s (mirrorRow x) q).1])
  have xp := nruns_pop (r.get 3) S₂ (l := S (r.get 3)) (v := (fixedScan s (mirrorRow x) q).2)
    (by simp [S₂, Lists.set])
  have he : S₂.set (r.get 3) (S (r.get 3)) =
      S.set (r.get 16) (S (r.get 16) ++ [(fixedScan s (mirrorRow x) q).1]) := by
    funext z
    by_cases hc : z = r.get 3
    · subst z; simp [S₂, S₁, Lists.set]
    by_cases ho : z = r.get 16
    · subst z; simp [S₂, S₁, Lists.set]
    simp [S₂, S₁, Lists.set, hc, ho]
  rw [he, fixedScan_value s x q hq] at xp
  exact (xd.seq (xb.seq xp)).mono (by omega)

theorem fixedLiteralCost_poly (s : List Char) : IsPoly (fun n => literalCost s n + 2) := by
  have he : (fun n => literalCost s n + 2) = (fun n => 10 * s.length * n + literalCost s 0 + 2) := by
    funext n; rw [literalCost_eq s n]
  rw [he]
  exact isPoly_add (isPoly_add (isPoly_mul (isPoly_const _) isPoly_id) (isPoly_const _)) (isPoly_const 2)

end Shallot.MacroPeg.CBV
