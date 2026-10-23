import MacroPeg.CBV.TableRead
import MacroPeg.HigherOrder.Mach.Intern

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.Packrat.Machine Shallot.MacroPeg.Mach

/-- Row, lookup scratch, index, two positions, two symbols, three comparison temporaries and its result. -/
structure CompareRegs (K : Nat) where
  get : Fin 11 → Fin K
  inj : ∀ i j, get i = get j → i = j

@[simp] theorem CompareRegs.eq {K : Nat} (r : CompareRegs K) (i j : Fin 11) :
    r.get i = r.get j ↔ i = j := ⟨r.inj i j, congrArg r.get⟩

theorem CompareRegs.ne {K : Nat} (r : CompareRegs K) {i j : Fin 11} (h : i ≠ j) : r.get i ≠ r.get j :=
  fun he => h (r.inj i j he)

def compareRowsP {K : Nat} (r : CompareRegs K) : NProg K :=
  .seq (readRow (r.get 0) (r.get 1) (r.get 2) (r.get 3) (r.get 5)
      (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)))
    (.seq (readRow (r.get 0) (r.get 1) (r.get 2) (r.get 4) (r.get 6)
      (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)))
      (.seq (cmpTop (r.get 5) (r.get 6) (r.get 7) (r.get 8) (r.get 9) (r.get 10)
        (r.ne (by decide)) (r.ne (by decide)))
        (.seq (.prim (.pop (r.get 6))) (.prim (.pop (r.get 5))))))

/-- Real row lookup and numeric comparison preserve the input, positions and all work stacks. -/
theorem compareRows_runs {K : Nat} (r : CompareRegs K) (S : Lists K) (data : List Nat)
    {p q : Nat} {lp lq : List Nat} (hrow : S (r.get 0) = data) (htmp : S (r.get 1) = [])
    (hp : S (r.get 3) = lp ++ [p]) (hq : S (r.get 4) = lq ++ [q]) (hpi : p < data.length) (hqi : q < data.length) :
    NRuns (compareRowsP r) S
      (S.set (r.get 10) (S (r.get 10) ++ [cmpRes data[p] data[q]]))
      (12 * data.length + 4 * p + 4 * q + (data[p] + data[q] + 1) * (2 * data[p] + 6) + 36) := by
  have x₁ := nruns_readRow (r.get 0) (r.get 1) (r.get 2) (r.get 3) (r.get 5)
    (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)) (by simp [List.nodup_cons]) S htmp hp
    (by rw [hrow]; exact hpi)
  simp only [hrow] at x₁
  let S₁ := S.set (r.get 5) (S (r.get 5) ++ [data[p]])
  have h₁row : S₁ (r.get 0) = data := by simp [S₁, Lists.set, hrow]
  have h₁tmp : S₁ (r.get 1) = [] := by simp [S₁, Lists.set, htmp]
  have h₁q : S₁ (r.get 4) = lq ++ [q] := by simp [S₁, Lists.set, hq]
  have x₂ := nruns_readRow (r.get 0) (r.get 1) (r.get 2) (r.get 4) (r.get 6)
    (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)) (by simp [List.nodup_cons]) S₁ h₁tmp h₁q
    (by rw [h₁row]; exact hqi)
  simp only [h₁row] at x₂
  have h₁b : S₁ (r.get 6) = S (r.get 6) := by simp [S₁, Lists.set]
  rw [h₁b] at x₂
  let S₂ := S₁.set (r.get 6) (S (r.get 6) ++ [data[q]])
  have h₂a : S₂ (r.get 5) = S (r.get 5) ++ [data[p]] := by simp [S₂, S₁, Lists.set]
  have h₂b : S₂ (r.get 6) = S (r.get 6) ++ [data[q]] := by simp [S₂]
  have x₃ := nruns_cmpTop (r.get 5) (r.get 6) (r.get 7) (r.get 8) (r.get 9) (r.get 10)
    (r.ne (by decide)) (r.ne (by decide)) (by simp [List.nodup_cons]) S₂ h₂a h₂b
  have h₂f : S₂ (r.get 10) = S (r.get 10) := by simp [S₂, S₁, Lists.set]
  rw [h₂f] at x₃
  let S₃ := S₂.set (r.get 10) (S (r.get 10) ++ [cmpRes data[p] data[q]])
  have x₄ := nruns_pop (r.get 6) S₃ (l := S (r.get 6)) (v := data[q]) (by simp [S₃, S₂, Lists.set])
  let S₄ := S₃.set (r.get 6) (S (r.get 6))
  have x₅ := nruns_pop (r.get 5) S₄ (l := S (r.get 5)) (v := data[p]) (by simp [S₄, S₃, S₂, S₁, Lists.set])
  have he : S₄.set (r.get 5) (S (r.get 5)) =
      S.set (r.get 10) (S (r.get 10) ++ [cmpRes data[p] data[q]]) := by
    simp only [S₄, S₃, S₂, S₁]
    funext k
    by_cases h5 : k = r.get 5
    · subst k; simp [Lists.set]
    by_cases h6 : k = r.get 6
    · subst k; simp [Lists.set]
    by_cases h10 : k = r.get 10
    · subst k; simp [Lists.set]
    simp [Lists.set, h5, h6, h10]
  rw [he] at x₅
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq x₅)))).mono (by omega)

end Shallot.MacroPeg.CBV
