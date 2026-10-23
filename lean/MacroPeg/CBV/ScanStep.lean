import MacroPeg.CBV.Mirror
import MacroPeg.CBV.CompareRows

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.Mach

structure ScanRegs (K : Nat) where
  get : Fin 13 → Fin K
  inj : ∀ i j, get i = get j → i = j

@[simp] theorem ScanRegs.eq {K : Nat} (r : ScanRegs K) (i j : Fin 13) :
    r.get i = r.get j ↔ i = j := ⟨r.inj i j, congrArg r.get⟩

def ScanRegs.compare {K : Nat} (r : ScanRegs K) : CompareRegs K where
  get i := r.get ⟨i.val, by have := i.isLt; omega⟩
  inj i j h := by
    have he := r.inj ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩ h
    exact Fin.ext (congrArg (fun k : Fin 13 => k.val) he)

/-- Local source and target positions, remaining count, and the success flag. -/
def scanState {K : Nat} (r : ScanRegs K) (S : Lists K) (p q k : Nat) (ok : Bool) : Lists K :=
  (((S.set (r.get 3) [p]).set (r.get 4) [q]).set (r.get 11) [k]).set (r.get 12) [if ok then 1 else 0]

macro "scan_states " r:term : tactic => `(tactic| (
  funext z
  by_cases h3 : z = ($r).get 3
  · subst z; simp_all [Lists.set] <;> omega
  by_cases h4 : z = ($r).get 4
  · subst z; simp_all [Lists.set] <;> omega
  by_cases h11 : z = ($r).get 11
  · subst z; simp_all [Lists.set] <;> omega
  by_cases h12 : z = ($r).get 12
  · subst z; simp_all [Lists.set] <;> omega
  simp_all [Lists.set] <;> omega))

def scanGoodP {K : Nat} (r : ScanRegs K) : NProg K :=
  .seq (.prim (.dec (r.get 3))) (.seq (.prim (.dec (r.get 4))) (.prim (.dec (r.get 11))))

def scanBadP {K : Nat} (r : ScanRegs K) : NProg K :=
  .seq (toZero (r.get 11)) (.prim (.dec (r.get 12)))

theorem scanGood_runs {K : Nat} (r : ScanRegs K) (S : Lists K) (p q k : Nat) :
    NRuns (scanGoodP r) (scanState r S p q (k + 1) true) (scanState r S (p - 1) (q - 1) k true) 3 := by
  let X := scanState r S p q (k + 1) true
  have x₁ := nruns_dec (r.get 3) X (l := []) (v := p) (by simp [X, scanState, Lists.set])
  let X₁ := X.set (r.get 3) [p - 1]
  have x₂ := nruns_dec (r.get 4) X₁ (l := []) (v := q) (by simp [X₁, X, scanState, Lists.set])
  let X₂ := X₁.set (r.get 4) [q - 1]
  have x₃ := nruns_dec (r.get 11) X₂ (l := []) (v := k + 1) (by simp [X₂, X₁, X, scanState, Lists.set])
  have he : X₂.set (r.get 11) ([] ++ [k + 1 - 1]) = scanState r S (p - 1) (q - 1) k true := by
    simp only [X₂, X₁, X, scanState]
    scan_states r
  rw [he] at x₃
  exact x₁.seq (x₂.seq x₃)

theorem scanBad_runs {K : Nat} (r : ScanRegs K) (S : Lists K) (p q k : Nat) :
    NRuns (scanBadP r) (scanState r S p q k true) (scanState r S p q 0 false) (2 * k + 2) := by
  let X := scanState r S p q k true
  have x₁ := nruns_toZero (r.get 11) X (l := []) (a := k) (by simp [X, scanState, Lists.set])
  let X₁ := X.set (r.get 11) [0]
  have x₂ := nruns_dec (r.get 12) X₁ (l := []) (v := 1) (by simp [X₁, X, scanState, Lists.set])
  have he : X₁.set (r.get 12) ([] ++ [1 - 1]) = scanState r S p q 0 false := by
    simp only [X₁, X, scanState]
    scan_states r
  rw [he] at x₂
  exact (x₁.seq x₂).mono (by omega)

/-- Dispatch a freshly pushed code and restore its stack to the preceding prefix. -/
theorem caseTop_saved {K : Nat} (i : Fin K) (ps : List (NProg K)) (fallback : NProg K) (v : Nat)
    (hv : v < ps.length) (S S' : Lists K) (T : Nat) (h : NRuns ps[v] S S' T) :
    NRuns (caseTop i ps fallback) (S.set i (S i ++ [v])) S' (T + 2 * v + 2) := by
  apply caseTop_runs i ps fallback v hv (S.set i (S i ++ [v])) (S i) (by simp) S' T
  simpa only [Lists.set_set_u, Lists.set_get_self] using h

def scanStepP {K : Nat} (r : ScanRegs K) : NProg K :=
  .seq (compareRowsP r.compare)
    (caseTop (r.get 10) [scanBadP r, scanGoodP r, scanBadP r] (scanBadP r))

def scanStepCost (n B : Nat) : Nat := 30 * (n + 1) + ((2 * B + 1) * (2 * B + 6) + 20) + 40

/-- The bounded comparison step performs real reads and comparisons, and preserves their scratch stacks. -/
theorem scanStep_runs {K : Nat} (r : ScanRegs K) (S : Lists K) (x : List Char) (k p q B : Nat)
    (hrow : S (r.get 0) = mirrorRow x) (htmp : S (r.get 1) = [])
    (hk : k + 1 ≤ p) (hp : p ≤ x.length) (hq : q ≤ x.length)
    (hB : ∀ v ∈ mirrorRow x, v ≤ B) :
    NRuns (scanStepP r) (scanState r S p q (k + 1) true)
      (if (mirrorRow x).getD p 0 = (mirrorRow x).getD q 0 then scanState r S (p - 1) (q - 1) k true
       else scanState r S p q 0 false) (scanStepCost x.length B) := by
  let X := scanState r S p q (k + 1) true
  have hpi : p < (mirrorRow x).length := by simp; omega
  have hqi : q < (mirrorRow x).length := by simp; omega
  have xc := compareRows_runs r.compare X (mirrorRow x)
    (p := p) (q := q) (lp := []) (lq := [])
    (by change X (r.get 0) = mirrorRow x; simp [X, scanState, Lists.set, hrow])
    (by change X (r.get 1) = []; simp [X, scanState, Lists.set, htmp])
    (by change X (r.get 3) = [] ++ [p]; simp [X, scanState, Lists.set])
    (by change X (r.get 4) = [] ++ [q]; simp [X, scanState, Lists.set]) hpi hqi
  have hdp : (mirrorRow x)[p] = (mirrorRow x).getD p 0 := List.getElem_eq_getD 0
  have hdq : (mirrorRow x)[q] = (mirrorRow x).getD q 0 := List.getElem_eq_getD 0
  simp only [hdp, hdq] at xc
  let a := (mirrorRow x).getD p 0
  let b := (mirrorRow x).getD q 0
  have haB : a ≤ B := hB a (by change (mirrorRow x).getD p 0 ∈ mirrorRow x; rw [← hdp]; exact List.getElem_mem hpi)
  have hbB : b ≤ B := hB b (by change (mirrorRow x).getD q 0 ∈ mirrorRow x; rw [← hdq]; exact List.getElem_mem hqi)
  have hv : cmpRes a b < 3 := by have := cmpRes_le a b; omega
  have hselect : ([scanBadP r, scanGoodP r, scanBadP r] : List (NProg K))[cmpRes a b] =
      (if a = b then scanGoodP r else scanBadP r) := by
    by_cases hlt : a < b
    · have hne : a ≠ b := by omega
      simp [cmpRes, hlt, hne]
    · by_cases he : a = b <;> simp [cmpRes, hlt, he]
  have hs : NRuns ([scanBadP r, scanGoodP r, scanBadP r] : List (NProg K))[cmpRes a b] X
      (if a = b then scanState r S (p - 1) (q - 1) k true else scanState r S p q 0 false) (2 * (k + 1) + 3) := by
    rw [hselect]
    by_cases he : a = b
    · simp only [if_pos he]
      exact (scanGood_runs r S p q k).mono (by omega)
    · simp only [if_neg he]
      exact (scanBad_runs r S p q (k + 1)).mono (by omega)
  have xd := caseTop_saved (r.get 10) [scanBadP r, scanGoodP r, scanBadP r] (scanBadP r)
    (cmpRes a b) (by simpa using hv) X _ _ hs
  have hc := cmpCost_le haB hbB
  have hcost : 12 * (mirrorRow x).length + 4 * p + 4 * q + (a + b + 1) * (2 * a + 6) + 36 +
      (2 * (k + 1) + 3 + 2 * cmpRes a b + 2) ≤ scanStepCost x.length B := by
    have hv' := cmpRes_le a b
    simp only [mirrorRow_length, scanStepCost]
    omega
  exact (xc.seq xd).mono hcost

end Shallot.MacroPeg.CBV
