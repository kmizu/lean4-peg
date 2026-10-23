import MacroPeg.CBV.RuleSweep
import Shallot.Peg.Packrat.Machine.Transfer

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.Packrat.Machine Shallot.MacroPeg.KExp

theorem EvalReady.withTable {K : Nat} {r : EvalRegs K} {S : Lists K} {x : List Char} {row E : List Nat}
    (h : EvalReady r S x row E) (next : List Nat) : EvalReady r (S.set (r.get 22) next) x next E := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by simp, ?_⟩
  · simpa [Lists.set] using h.word
  · simpa [Lists.set] using h.tmp
  · intro i hi
    have hn : i ≠ (22 : Fin 32) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [Lists.set, hn] using h.clean i hi
  · simpa [Lists.set] using h.dict
  · simpa [Lists.set] using h.count
  · simpa [Lists.set] using h.len
  · simpa [Lists.set] using h.env

def roundStepP {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) : NProg K :=
  .seq (roundProgram r g s)
    (.seq (replaceRow (r.get 25) (r.get 22) (r.get 1) (r.ne (by decide)) (r.ne (by decide)))
      (.prim (.dec (r.get 29))))

def roundStepCost (g : MGrammar) (n : Nat) : Nat := roundCost g n + 8 * rowCap g n + 4

/-- One round builds the next table, transfers it into the old-table stack, and decreases the round counter. -/
theorem roundStep_runs {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (x : List Char)
    (m : Nat) (S : Lists K) (ready : EvalReady r S x (pack g x (tblV g x s m)) [])
    (hnext : S (r.get 25) = []) (c : Nat) {lc : List Nat} (hc : S (r.get 29) = lc ++ [c]) :
    NRuns (roundStepP r g s) S
      ((S.set (r.get 22) (pack g x (tblV g x s (m + 1)))).set (r.get 29) (lc ++ [c - 1]))
      (roundStepCost g x.length) := by
  let next := pack g x (tblV g x s (m + 1))
  have xr := roundProgram_runs r g s x (tblV g x s m) (tblV_ok g x s m) S ready
  rw [hnext, List.nil_append, numericRound_pack] at xr
  let X := S.set (r.get 25) next
  have xt := nruns_replaceRow (r.get 25) (r.get 22) (r.get 1)
    (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)) X
    (by simp [X, Lists.set, ready.tmp])
  have hx25 : X (r.get 25) = next := by simp [X]
  have hx22 : X (r.get 22) = pack g x (tblV g x s m) := by simp [X, Lists.set, ready.table]
  rw [hx25, hx22] at xt
  have he : (X.set (r.get 22) next).set (r.get 25) [] = S.set (r.get 22) next := by
    funext z
    by_cases h22 : z = r.get 22
    · subst z; simp [X, Lists.set]
    by_cases h25 : z = r.get 25
    · subst z; simp [X, Lists.set, hnext]
    simp [X, Lists.set, h22, h25]
  rw [he] at xt
  let Y := S.set (r.get 22) next
  have xd := nruns_dec (r.get 29) Y (l := lc) (v := c) (by simp [Y, Lists.set, hc])
  have hOld := rowCap_bound g x (tblV g x s m)
  have hNew := rowCap_bound g x (tblV g x s (m + 1))
  exact (xr.seq (xt.seq xd)).mono (by unfold roundStepCost; dsimp only [next] at *; omega)

def satState {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (x : List Char) (S : Lists K)
    (m remaining : Nat) : Lists K :=
  (S.set (r.get 22) (pack g x (tblV g x s m))).set (r.get 29) (S (r.get 29) ++ [remaining])

theorem EvalReady.saturation {K : Nat} {r : EvalRegs K} {g : MGrammar} {s : Strategy} {x : List Char}
    {S : Lists K} {row : List Nat} (h : EvalReady r S x row []) (m remaining : Nat) :
    EvalReady r (satState r g s x S m remaining) x (pack g x (tblV g x s m)) [] :=
  (h.withTable _).reserved 29 (by decide) _

def saturationLoopP {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) : NProg K :=
  .loop (r.get 29) .pos (roundStepP r g s)

/-- The physical saturation loop reaches the corresponding semantic table after exactly the requested rounds. -/
theorem saturationLoop_runs {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (x : List Char)
    (S : Lists K) (row : List Nat) (ready : EvalReady r S x row []) (hnext : S (r.get 25) = []) (N : Nat) :
    NRuns (saturationLoopP r g s) (satState r g s x S 0 N) (satState r g s x S N 0)
      (N * (roundStepCost g x.length + 1) + 1) := by
  let F := fun k => satState r g s x S k (N - k)
  have hl := nruns_family_const (i := r.get 29) (c := .pos) (p := roundStepP r g s)
    F N (roundStepCost g x.length)
    (by
      intro k hk
      have he : N - k = (N - 1 - k) + 1 := by omega
      simp [F, satState, NTest.eval, he])
    (by simp [F, satState, NTest.eval])
    (by
      intro k hk
      have xb := roundStep_runs r g s x k (F k) (ready.saturation k (N - k))
        (by simp [F, satState, Lists.set, hnext]) (N - k) (lc := S (r.get 29)) (by simp [F, satState])
      have he : ((F k).set (r.get 22) (pack g x (tblV g x s (k + 1)))).set (r.get 29)
          (S (r.get 29) ++ [N - k - 1]) = F (k + 1) := by
        funext z
        by_cases h22 : z = r.get 22
        · subst z; simp [F, satState, Lists.set]
        by_cases h29 : z = r.get 29
        · subst z; simp [F, satState, Lists.set, Nat.sub_sub]
        simp [F, satState, Lists.set, h22, h29]
      rw [he] at xb
      exact xb)
  simpa [saturationLoopP, F] using hl

def saturationP {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) : NProg K :=
  .seq (saturationLoopP r g s) (.prim (.pop (r.get 29)))

def saturationCost (g : MGrammar) (n : Nat) : Nat := rowCap g n * (roundStepCost g n + 1) + 2

/-- Saturate for the proven finite bound, preserving every other caller stack and removing the counter frame. -/
theorem saturation_runs {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (x : List Char)
    (S : Lists K) (ready : EvalReady r S x (pack g x (tblV g x s 0)) []) (hnext : S (r.get 25) = []) :
    NRuns (saturationP r g s) (S.set (r.get 29) (S (r.get 29) ++ [iterBoundV g x]))
      (S.set (r.get 22) (pack g x (tblV g x s (iterBoundV g x)))) (saturationCost g x.length) := by
  have xl := saturationLoop_runs r g s x S _ ready hnext (iterBoundV g x)
  have hstart : satState r g s x S 0 (iterBoundV g x) = S.set (r.get 29) (S (r.get 29) ++ [iterBoundV g x]) := by
    simp only [satState, ← ready.table, Lists.set_get_self]
  rw [hstart] at xl
  have xp := nruns_pop (r.get 29) (satState r g s x S (iterBoundV g x) 0)
    (l := S (r.get 29)) (v := 0) (by simp [satState])
  simp only [satState, Lists.set_set_u] at xp
  have he : ((S.set (r.get 22) (pack g x (tblV g x s (iterBoundV g x))))).set (r.get 29) (S (r.get 29)) =
      S.set (r.get 22) (pack g x (tblV g x s (iterBoundV g x))) := by
    rw [show S (r.get 29) = (S.set (r.get 22) (pack g x (tblV g x s (iterBoundV g x)))) (r.get 29) by simp [Lists.set]]
    exact Lists.set_get_self _ _
  rw [he] at xp
  have hN := rowCap_bound g x (tblV g x s 0)
  rw [pack_length] at hN
  have hm := Nat.mul_le_mul_right (roundStepCost g x.length + 1) hN
  exact (xl.seq xp).mono (by unfold saturationCost; omega)

theorem roundStepCost_poly (g : MGrammar) : IsPoly (roundStepCost g) :=
  isPoly_add (isPoly_add (roundCost_poly g) (isPoly_mul (isPoly_const 8) (rowCap_poly g))) (isPoly_const 4)

theorem saturationCost_poly (g : MGrammar) : IsPoly (saturationCost g) :=
  isPoly_add (isPoly_mul (rowCap_poly g) (isPoly_add (roundStepCost_poly g) (isPoly_const 1))) (isPoly_const 2)

end Shallot.MacroPeg.CBV
