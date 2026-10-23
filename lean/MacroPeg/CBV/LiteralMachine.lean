import MacroPeg.CBV.ScanLoop
import Complexity.Univ.SimKit

namespace Shallot.MacroPeg.CBV

open Complexity Complexity.Univ Shallot.MacroPeg.KExp

/-- Scanning registers plus the two source endpoints, the target position and the returned code. -/
structure LiteralRegs (K : Nat) where
  get : Fin 17 → Fin K
  inj : ∀ i j, get i = get j → i = j

@[simp] theorem LiteralRegs.eq {K : Nat} (r : LiteralRegs K) (i j : Fin 17) :
    r.get i = r.get j ↔ i = j := ⟨r.inj i j, congrArg r.get⟩

theorem LiteralRegs.ne {K : Nat} (r : LiteralRegs K) {i j : Fin 17} (h : i ≠ j) : r.get i ≠ r.get j :=
  fun he => h (r.inj i j he)

def LiteralRegs.scan {K : Nat} (r : LiteralRegs K) : ScanRegs K where
  get i := r.get ⟨i.val, by have := i.isLt; omega⟩
  inj i j h := by
    have he := r.inj ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩ h
    exact Fin.ext (congrArg (fun k : Fin 17 => k.val) he)

theorem LiteralRegs.ans_ne {K : Nat} (r : LiteralRegs K) (i : Fin 13) : r.get 16 ≠ r.scan.get i := by
  intro he
  have hv := congrArg (fun k : Fin 17 => k.val) (r.inj 16 _ he)
  change 16 = i.val at hv
  have := i.isLt
  omega

/-- Set up local cursors and compute the source interval's length with real unary subtraction. -/
def literalPrepareP {K : Nat} (r : LiteralRegs K) : NProg K :=
  .seq (.prim (.dup (r.get 13) (r.get 3) (r.ne (by decide))))
    (.seq (.prim (.dup (r.get 15) (r.get 4) (r.ne (by decide))))
      (.seq (.prim (.dup (r.get 13) (r.get 11) (r.ne (by decide))))
        (.seq (.prim (.dup (r.get 14) (r.get 7) (r.ne (by decide))))
          (.seq (subTo (r.get 7) (r.get 11))
            (.seq (.prim (.pushZ (r.get 12))) (.prim (.inc (r.get 12))))))))

macro "literal_states " r:term : tactic => `(tactic| (
  funext z
  by_cases h3 : z = ($r).get 3
  · subst z; simp_all [Lists.set] <;> omega
  by_cases h4 : z = ($r).get 4
  · subst z; simp_all [Lists.set] <;> omega
  by_cases h7 : z = ($r).get 7
  · subst z; simp_all [Lists.set] <;> omega
  by_cases h11 : z = ($r).get 11
  · subst z; simp_all [Lists.set] <;> omega
  by_cases h12 : z = ($r).get 12
  · subst z; simp_all [Lists.set] <;> omega
  simp_all [Lists.set] <;> omega))

theorem literalPrepare_runs {K : Nat} (r : LiteralRegs K) (S : Lists K) (p j q : Nat)
    {lp lj lq : List Nat} (hp : S (r.get 13) = lp ++ [p]) (hj : S (r.get 14) = lj ++ [j])
    (hq : S (r.get 15) = lq ++ [q])
    (h3 : S (r.get 3) = []) (h4 : S (r.get 4) = []) (h11 : S (r.get 11) = []) (h12 : S (r.get 12) = []) :
    NRuns (literalPrepareP r) S (scanState r.scan S p q (p - j) true) (3 * j + 8) := by
  have x₁ := nruns_dup (r.get 13) (r.get 3) (r.ne (by decide)) S hp
  rw [h3, List.nil_append] at x₁
  let S₁ := S.set (r.get 3) [p]
  have x₂ := nruns_dup (r.get 15) (r.get 4) (r.ne (by decide)) S₁ (l := lq) (v := q)
    (by simp [S₁, Lists.set, hq])
  have h₁4 : S₁ (r.get 4) = [] := by simp [S₁, Lists.set, h4]
  rw [h₁4, List.nil_append] at x₂
  let S₂ := S₁.set (r.get 4) [q]
  have x₃ := nruns_dup (r.get 13) (r.get 11) (r.ne (by decide)) S₂ (l := lp) (v := p)
    (by simp [S₂, S₁, Lists.set, hp])
  have h₂11 : S₂ (r.get 11) = [] := by simp [S₂, S₁, Lists.set, h11]
  rw [h₂11, List.nil_append] at x₃
  let S₃ := S₂.set (r.get 11) [p]
  have x₄ := nruns_dup (r.get 14) (r.get 7) (r.ne (by decide)) S₃ (l := lj) (v := j)
    (by simp [S₃, S₂, S₁, Lists.set, hj])
  have h₃7 : S₃ (r.get 7) = S (r.get 7) := by simp [S₃, S₂, S₁, Lists.set]
  rw [h₃7] at x₄
  let S₄ := S₃.set (r.get 7) (S (r.get 7) ++ [j])
  have x₅ := nruns_subTo (r.get 7) (r.get 11) (r.ne (by decide)) S₄
    (l := S (r.get 7)) (l' := []) (a := j) (b := p) (by simp [S₄])
    (by simp [S₄, S₃, Lists.set])
  let S₅ := (S₄.set (r.get 7) (S (r.get 7))).set (r.get 11) [p - j]
  have x₆ := nruns_pushZ (r.get 12) S₅
  have h₅12 : S₅ (r.get 12) = [] := by simp [S₅, S₄, S₃, S₂, S₁, Lists.set, h12]
  rw [h₅12, List.nil_append] at x₆
  let S₆ := S₅.set (r.get 12) [0]
  have x₇ := nruns_inc (r.get 12) S₆ (l := []) (v := 0) (by simp [S₆])
  have he : S₆.set (r.get 12) ([] ++ [0 + 1]) = scanState r.scan S p q (p - j) true := by
    change S₆.set (r.get 12) ([] ++ [0 + 1]) =
      (((S.set (r.get 3) [p]).set (r.get 4) [q]).set (r.get 11) [p - j]).set (r.get 12) [1]
    simp only [S₆, S₅, S₄, S₃, S₂, S₁]
    literal_states r
  rw [he] at x₇
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq x₇)))))).mono (by omega)

def spanLiteralP {K : Nat} (r : LiteralRegs K) : NProg K :=
  .seq (literalPrepareP r) (scanCoreP r.scan (r.get 16) r.ans_ne)

def spanLiteralCost (n : Nat) : Nat := 3 * n + 8 + scanCoreCost n UInt32.size

/-- The dynamic literal cell, including preparation, full scan, answer and cleanup, is a real polynomial-time program. -/
theorem spanLiteral_runs {K : Nat} (r : LiteralRegs K) (S : Lists K) (x : List Char) (p j q : Nat)
    {lp lj lq : List Nat} (hrow : S (r.get 0) = mirrorRow x) (htmp : S (r.get 1) = [])
    (h3 : S (r.get 3) = []) (h4 : S (r.get 4) = []) (h11 : S (r.get 11) = []) (h12 : S (r.get 12) = [])
    (hp : S (r.get 13) = lp ++ [p]) (hj : S (r.get 14) = lj ++ [j]) (hq : S (r.get 15) = lq ++ [q])
    (hpn : p ≤ x.length) (hjn : j ≤ x.length) (hqn : q ≤ x.length) :
    NRuns (spanLiteralP r) S
      (S.set (r.get 16) (S (r.get 16) ++ [literalCode (literalAt x (spanId x.length p j)) (sfx x q)]))
      (spanLiteralCost x.length) := by
  have xp := literalPrepare_runs r S p j q hp hj hq h3 h4 h11 h12
  have xs := scanCore_runs r.scan (r.get 16) r.ans_ne S x (p - j) p q UInt32.size
    (by change S (r.get 0) = mirrorRow x; exact hrow) (by change S (r.get 1) = []; exact htmp)
    (by change S (r.get 3) = []; exact h3) (by change S (r.get 4) = []; exact h4)
    (by change S (r.get 11) = []; exact h11) (by change S (r.get 12) = []; exact h12)
    (by omega) hpn hqn (mirrorRow_bound x)
  rw [mirrorScan_span hpn hqn] at xs
  exact (xp.seq xs).mono (by unfold spanLiteralCost; omega)

theorem spanLiteralCost_poly : IsPoly spanLiteralCost :=
  isPoly_add (isPoly_add (isPoly_mul (isPoly_const 3) isPoly_id) (isPoly_const 8)) (scanCoreCost_poly _)

end Shallot.MacroPeg.CBV
