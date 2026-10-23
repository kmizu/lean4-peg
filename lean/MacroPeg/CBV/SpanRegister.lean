import MacroPeg.CBV.ParamMachine
import Complexity.Univ.SimKit

namespace Shallot.MacroPeg.CBV

open Complexity Complexity.Univ Shallot.MacroPeg.Mach Shallot.MacroPeg.KExp

/-- The parameter registers plus a preserved count of the span dictionary. -/
structure RegisterRegs (K : Nat) where
  get : Fin 20 → Fin K
  inj : ∀ i j, get i = get j → i = j

@[simp] theorem RegisterRegs.eq {K : Nat} (r : RegisterRegs K) (i j : Fin 20) :
    r.get i = r.get j ↔ i = j := ⟨r.inj i j, congrArg r.get⟩

theorem RegisterRegs.ne {K : Nat} (r : RegisterRegs K) {i j : Fin 20} (h : i ≠ j) : r.get i ≠ r.get j :=
  fun he => h (r.inj i j he)

/-- Append the normalized interval endpoints, preserving every caller prefix. -/
def registerState {K : Nat} (r : RegisterRegs K) (S : Lists K) (p j : Nat) : Lists K :=
  (S.set (r.get 13) (S (r.get 13) ++ [p])).set (r.get 14) (S (r.get 14) ++ [min j p])

macro "register_states " r:term : tactic => `(tactic| (
  funext z
  by_cases h3 : z = ($r).get 3
  · subst z; simp_all [Lists.set] <;> omega
  by_cases h13 : z = ($r).get 13
  · subst z; simp_all [Lists.set] <;> omega
  by_cases h14 : z = ($r).get 14
  · subst z; simp_all [Lists.set] <;> omega
  by_cases h18 : z = ($r).get 18
  · subst z; simp_all [Lists.set] <;> omega
  simp_all [Lists.set] <;> omega))

/-- Compute the endpoint as `p - (p - j)`, using actual truncated unary subtraction. -/
def registerPrepareP {K : Nat} (r : RegisterRegs K) : NProg K :=
  .seq (.prim (.dup (r.get 15) (r.get 13) (r.ne (by decide))))
    (.seq (.prim (.dup (r.get 15) (r.get 14) (r.ne (by decide))))
      (.seq (.prim (.dup (r.get 16) (r.get 3) (r.ne (by decide))))
        (.seq (.prim (.dec (r.get 3))) (.seq (.prim (.dec (r.get 3)))
          (.seq (subTo (r.get 3) (r.get 14))
            (.seq (.prim (.dup (r.get 15) (r.get 3) (r.ne (by decide))))
              (.seq (subTo (r.get 14) (r.get 3)) (nmv (r.get 3) (r.get 14) (r.ne (by decide))))))))))

theorem registerPrepare_runs {K : Nat} (r : RegisterRegs K) (S : Lists K) (p j n : Nat)
    {lp lr : List Nat} (hp : S (r.get 15) = lp ++ [p]) (hr : S (r.get 16) = lr ++ [j + 2])
    (hpn : p ≤ n) (hjn : j ≤ n) :
    NRuns (registerPrepareP r) S (registerState r S p j) (6 * n + 12) := by
  have x₁ := nruns_dup (r.get 15) (r.get 13) (r.ne (by decide)) S hp
  let S₁ := S.set (r.get 13) (S (r.get 13) ++ [p])
  have x₂ := nruns_dup (r.get 15) (r.get 14) (r.ne (by decide)) S₁ (l := lp) (v := p)
    (by simp [S₁, Lists.set, hp])
  have h₁14 : S₁ (r.get 14) = S (r.get 14) := by simp [S₁, Lists.set]
  rw [h₁14] at x₂
  let S₂ := S₁.set (r.get 14) (S (r.get 14) ++ [p])
  have x₃ := nruns_dup (r.get 16) (r.get 3) (r.ne (by decide)) S₂ (l := lr) (v := j + 2)
    (by simp [S₂, S₁, Lists.set, hr])
  have h₂3 : S₂ (r.get 3) = S (r.get 3) := by simp [S₂, S₁, Lists.set]
  rw [h₂3] at x₃
  let S₃ := S₂.set (r.get 3) (S (r.get 3) ++ [j + 2])
  have x₄ := nruns_dec (r.get 3) S₃ (l := S (r.get 3)) (v := j + 2) (by simp [S₃])
  simp only [show j + 2 - 1 = j + 1 by omega] at x₄
  let S₄ := S₃.set (r.get 3) (S (r.get 3) ++ [j + 1])
  have x₅ := nruns_dec (r.get 3) S₄ (l := S (r.get 3)) (v := j + 1) (by simp [S₄])
  simp only [Nat.add_sub_cancel] at x₅
  let S₅ := S₄.set (r.get 3) (S (r.get 3) ++ [j])
  have x₆ := nruns_subTo (r.get 3) (r.get 14) (r.ne (by decide)) S₅
    (l := S (r.get 3)) (l' := S (r.get 14)) (a := j) (b := p)
    (by simp [S₅]) (by simp [S₅, S₄, S₃, S₂, Lists.set])
  let S₆ := (S₅.set (r.get 3) (S (r.get 3))).set (r.get 14) (S (r.get 14) ++ [p - j])
  have x₇ := nruns_dup (r.get 15) (r.get 3) (r.ne (by decide)) S₆ (l := lp) (v := p)
    (by simp [S₆, S₅, S₄, S₃, S₂, S₁, Lists.set, hp])
  have h₆3 : S₆ (r.get 3) = S (r.get 3) := by simp [S₆, Lists.set]
  rw [h₆3] at x₇
  let S₇ := S₆.set (r.get 3) (S (r.get 3) ++ [p])
  have x₈ := nruns_subTo (r.get 14) (r.get 3) (r.ne (by decide)) S₇
    (l := S (r.get 14)) (l' := S (r.get 3)) (a := p - j) (b := p)
    (by simp [S₇, S₆, Lists.set]) (by simp [S₇])
  let S₈ := (S₇.set (r.get 14) (S (r.get 14))).set (r.get 3) (S (r.get 3) ++ [p - (p - j)])
  have x₉ := nruns_mv (r.get 3) (r.get 14) (r.ne (by decide)) S₈
    (l := S (r.get 3)) (v := p - (p - j)) (by simp [S₈])
  have he : (S₈.set (r.get 14) (S₈ (r.get 14) ++ [p - (p - j)])).set (r.get 3) (S (r.get 3)) =
      registerState r S p j := by
    simp only [S₈, S₇, S₆, S₅, S₄, S₃, S₂, S₁, registerState]
    register_states r
  rw [he] at x₉
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq (x₇.seq (x₈.seq x₉)))))))).mono (by omega)

def registerLookupP {K : Nat} (r : RegisterRegs K) : NProg K :=
  spanLookupP (r.get 17) (r.get 19) (r.get 1) (r.get 13) (r.get 14) (r.get 18)
    (r.get 2) (r.get 3) (r.get 4) (r.get 5) (r.get 6) (r.get 7) (r.get 8) (r.get 9)
    (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))
    (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))

theorem registerLookup_runs {K : Nat} (r : RegisterRegs K) (S : Lists K) (p j n : Nat)
    (hp : p ≤ n) (hrow : S (r.get 17) = encPairs (spans n)) (ht : S (r.get 1) = [])
    (hcount : S (r.get 19) = [(spans n).length]) :
    NRuns (registerLookupP r) (registerState r S p j)
      ((registerState r S p j).set (r.get 18) (S (r.get 18) ++ [spanId n p j])) (spanLookupCost n) := by
  let X := registerState r S p j
  have hx := spanLookup_runs (r.get 17) (r.get 19) (r.get 1) (r.get 13) (r.get 14) (r.get 18)
    (r.get 2) (r.get 3) (r.get 4) (r.get 5) (r.get 6) (r.get 7) (r.get 8) (r.get 9)
    (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))
    (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))
    (by simp [InternStacks, List.nodup_cons]) X (p := p) (j := min j p) hp (by omega)
    (by simp [X, registerState, Lists.set, hrow]) (by simp [X, registerState, Lists.set, ht])
    (la := S (r.get 13)) (by simp [X, registerState, Lists.set])
    (lb := S (r.get 14)) (by simp [X, registerState]) (by simp [X, registerState, Lists.set, hcount])
  have ho : X (r.get 18) = S (r.get 18) := by simp [X, registerState, Lists.set]
  have hid : spanId n p (min j p) = spanId n p j := by simp [spanId, Nat.min_assoc]
  rw [ho, hid] at hx
  exact hx.mono (spanLookupCost_bound n)

def registerCleanupP {K : Nat} (r : RegisterRegs K) : NProg K :=
  .seq (.prim (.pop (r.get 14))) (.prim (.pop (r.get 13)))

theorem registerCleanup_runs {K : Nat} (r : RegisterRegs K) (S : Lists K) (p j v : Nat) :
    NRuns (registerCleanupP r) ((registerState r S p j).set (r.get 18) (S (r.get 18) ++ [v]))
      (S.set (r.get 18) (S (r.get 18) ++ [v])) 2 := by
  let X := (registerState r S p j).set (r.get 18) (S (r.get 18) ++ [v])
  have x₁ := nruns_pop (r.get 14) X (l := S (r.get 14)) (v := min j p)
    (by simp [X, registerState, Lists.set])
  let Y := X.set (r.get 14) (S (r.get 14))
  have x₂ := nruns_pop (r.get 13) Y (l := S (r.get 13)) (v := p)
    (by simp [Y, X, registerState, Lists.set])
  have he : Y.set (r.get 13) (S (r.get 13)) = S.set (r.get 18) (S (r.get 18) ++ [v]) := by
    simp only [Y, X, registerState]
    register_states r
  rw [he] at x₂
  exact x₁.seq x₂

def registerSpanP {K : Nat} (r : RegisterRegs K) : NProg K :=
  .seq (registerPrepareP r) (.seq (registerLookupP r) (registerCleanupP r))

def registerSpanCost (n : Nat) : Nat := 6 * n + 14 + spanLookupCost n

/-- Turn the body's success code into a valid span identifier with all real dictionary costs included. -/
theorem registerSpan_runs {K : Nat} (r : RegisterRegs K) (S : Lists K) (p j n : Nat)
    {lp lr : List Nat} (hp : S (r.get 15) = lp ++ [p]) (hr : S (r.get 16) = lr ++ [j + 2])
    (hpn : p ≤ n) (hjn : j ≤ n) (hrow : S (r.get 17) = encPairs (spans n)) (ht : S (r.get 1) = [])
    (hcount : S (r.get 19) = [(spans n).length]) :
    NRuns (registerSpanP r) S (S.set (r.get 18) (S (r.get 18) ++ [spanId n p j]))
      (registerSpanCost n) := by
  have xp := registerPrepare_runs r S p j n hp hr hpn hjn
  have xl := registerLookup_runs r S p j n hpn hrow ht hcount
  have xc := registerCleanup_runs r S p j (spanId n p j)
  exact (xp.seq (xl.seq xc)).mono (by unfold registerSpanCost; omega)

theorem registerSpanCost_poly : IsPoly registerSpanCost :=
  isPoly_add (isPoly_add (isPoly_mul (isPoly_const 6) isPoly_id) (isPoly_const 14)) spanLookupCost_poly

end Shallot.MacroPeg.CBV
