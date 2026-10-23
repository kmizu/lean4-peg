import MacroPeg.CBV.ControlMachine

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.Packrat.Machine Shallot.MacroPeg.Mach Shallot.MacroPeg.KExp

/-- The literal registers and one additional stack of repetition flags. -/
structure StarRegs (K : Nat) where
  get : Fin 18 → Fin K
  inj : ∀ i j, get i = get j → i = j

@[simp] theorem StarRegs.eq {K : Nat} (r : StarRegs K) (i j : Fin 18) :
    r.get i = r.get j ↔ i = j := ⟨r.inj i j, congrArg r.get⟩

theorem StarRegs.ne {K : Nat} (r : StarRegs K) {i j : Fin 18} (h : i ≠ j) : r.get i ≠ r.get j :=
  fun he => h (r.inj i j he)

def StarRegs.literal {K : Nat} (r : StarRegs K) : LiteralRegs K where
  get i := r.get ⟨i.val, by have := i.isLt; omega⟩
  inj i j h := by
    have he := r.inj ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩ h
    exact Fin.ext (congrArg (fun k : Fin 18 => k.val) he)

/-- One private position frame and one private flag, with arbitrary caller stack prefixes. -/
def starState {K : Nat} (r : StarRegs K) (S : Lists K) (p : Nat) (active : Bool) : Lists K :=
  (S.set (r.get 15) (S (r.get 15) ++ [p])).set (r.get 17) (S (r.get 17) ++ [if active then 1 else 0])

def starResult {K : Nat} (r : StarRegs K) (S : Lists K) (p v : Nat) : Lists K :=
  (starState r S p false).set (r.get 16) (S (r.get 16) ++ [v])

macro "star_states " r:term : tactic => `(tactic| (
  funext z
  by_cases h15 : z = ($r).get 15
  · subst z; simp_all [Lists.set]
  by_cases h16 : z = ($r).get 16
  · subst z; simp_all [Lists.set]
  by_cases h17 : z = ($r).get 17
  · subst z; simp_all [Lists.set]
  simp_all [Lists.set]))

/-- Unknown stops the loop without changing the returned unknown code. -/
theorem starUnknown_runs {K : Nat} (r : StarRegs K) (S : Lists K) (p : Nat) :
    NRuns (.prim (.dec (r.get 17)))
      ((starState r S p true).set (r.get 16) (S (r.get 16) ++ [0])) (starResult r S p 0) 1 := by
  let X := (starState r S p true).set (r.get 16) (S (r.get 16) ++ [0])
  have xd := nruns_dec (r.get 17) X (l := S (r.get 17)) (v := 1)
    (by simp [X, starState, Lists.set])
  have he : X.set (r.get 17) (S (r.get 17) ++ [1 - 1]) = starResult r S p 0 := by
    simp only [X, starResult, starState]
    star_states r
  rw [he] at xd
  exact xd

def starFailureP {K : Nat} (r : StarRegs K) : NProg K :=
  .seq (.prim (.pop (r.get 16)))
    (.seq (emptySuccess (r.get 15) (r.get 16) (r.ne (by decide))) (.prim (.dec (r.get 17))))

/-- A failed body ends the repetition with the current position as a success. -/
theorem starFailure_runs {K : Nat} (r : StarRegs K) (S : Lists K) (p : Nat) :
    NRuns (starFailureP r) ((starState r S p true).set (r.get 16) (S (r.get 16) ++ [0]))
      (starResult r S p (p + 2)) 5 := by
  let X := starState r S p true
  have ho : X (r.get 16) = S (r.get 16) := by simp [X, starState, Lists.set]
  have xp := nruns_pop (r.get 16) (X.set (r.get 16) (S (r.get 16) ++ [0])) (l := S (r.get 16)) (v := 0) (by simp)
  simp only [← ho, Lists.set_set_u, Lists.set_get_self] at xp
  rw [ho] at xp
  have xe := nruns_emptySuccess (r.get 15) (r.get 16) (r.ne (by decide)) X
    (lp := S (r.get 15)) (i := p) (by simp [X, starState, Lists.set])
  rw [ho] at xe
  let Y := X.set (r.get 16) (S (r.get 16) ++ [p + 2])
  have xd := nruns_dec (r.get 17) Y (l := S (r.get 17)) (v := 1)
    (by simp [Y, X, starState, Lists.set])
  have he : Y.set (r.get 17) (S (r.get 17) ++ [1 - 1]) = starResult r S p (p + 2) := by
    simp only [Y, X, starResult, starState]
    star_states r
  rw [he] at xd
  exact xp.seq (xe.seq xd)

def starAdvanceP {K : Nat} (r : StarRegs K) : NProg K :=
  .seq (.prim (.pop (r.get 15))) (nmv (r.get 16) (r.get 15) (r.ne (by decide)))

/-- A consuming success replaces the private cursor and removes its intermediate answer. -/
theorem starAdvance_runs {K : Nat} (r : StarRegs K) (S : Lists K) (p j : Nat) :
    NRuns (starAdvanceP r) ((starState r S p true).set (r.get 16) (S (r.get 16) ++ [j]))
      (starState r S j true) 3 := by
  let X := (starState r S p true).set (r.get 16) (S (r.get 16) ++ [j])
  have xp := nruns_pop (r.get 15) X (l := S (r.get 15)) (v := p)
    (by simp [X, starState, Lists.set])
  let Y := X.set (r.get 15) (S (r.get 15))
  have xm := nruns_mv (r.get 16) (r.get 15) (r.ne (by decide)) Y
    (l := S (r.get 16)) (v := j) (by simp [Y, X, Lists.set])
  have he : (Y.set (r.get 15) (Y (r.get 15) ++ [j])).set (r.get 16) (S (r.get 16)) = starState r S j true := by
    simp only [Y, X, starState]
    star_states r
  rw [he] at xm
  exact xp.seq xm

def starStuckP {K : Nat} (r : StarRegs K) : NProg K :=
  .seq (.prim (.pop (r.get 16))) (.seq (.prim (.pushZ (r.get 16))) (.prim (.dec (r.get 17))))

/-- A nondecreasing success has no finite repetition result. -/
theorem starStuck_runs {K : Nat} (r : StarRegs K) (S : Lists K) (p j : Nat) :
    NRuns (starStuckP r) ((starState r S p true).set (r.get 16) (S (r.get 16) ++ [j]))
      (starResult r S p 0) 3 := by
  let X := starState r S p true
  have ho : X (r.get 16) = S (r.get 16) := by simp [X, starState, Lists.set]
  have xp := nruns_pop (r.get 16) (X.set (r.get 16) (S (r.get 16) ++ [j]))
    (l := S (r.get 16)) (v := j) (by simp)
  simp only [← ho, Lists.set_set_u, Lists.set_get_self] at xp
  rw [ho] at xp
  have xz := nruns_pushZ (r.get 16) X
  rw [ho] at xz
  exact xp.seq (xz.seq (starUnknown_runs r S p))

def starCompareP {K : Nat} (r : StarRegs K) : NProg K :=
  .seq (cmpTop (r.get 16) (r.get 15) (r.get 5) (r.get 6) (r.get 7) (r.get 10)
    (r.ne (by decide)) (r.ne (by decide)))
    (caseTop (r.get 10) [starAdvanceP r, starStuckP r, starStuckP r] (starStuckP r))

def starCompareCost (n : Nat) : Nat := (2 * n + 1) * (2 * n + 6) + 29

/-- The strict-progress check charges the real numeric comparison and dispatch. -/
theorem starCompare_runs {K : Nat} (r : StarRegs K) (S : Lists K) (p j n : Nat)
    (hp : p ≤ n) (hj : j ≤ n) :
    NRuns (starCompareP r) ((starState r S p true).set (r.get 16) (S (r.get 16) ++ [j]))
      (if j < p then starState r S j true else starResult r S p 0) (starCompareCost n) := by
  let X := (starState r S p true).set (r.get 16) (S (r.get 16) ++ [j])
  have xc := nruns_cmpTop (r.get 16) (r.get 15) (r.get 5) (r.get 6) (r.get 7) (r.get 10)
    (r.ne (by decide)) (r.ne (by decide)) (by simp [List.nodup_cons]) X
    (li := S (r.get 16)) (lj := S (r.get 15)) (a := j) (b := p)
    (by simp [X]) (by simp [X, starState, Lists.set])
  have h₁0 : X (r.get 10) = S (r.get 10) := by simp [X, starState, Lists.set]
  have hv : cmpRes j p < 3 := by have := cmpRes_le j p; omega
  have hs : ([starAdvanceP r, starStuckP r, starStuckP r] : List (NProg K))[cmpRes j p] =
      if j < p then starAdvanceP r else starStuckP r := by
    by_cases hlt : j < p
    · simp [cmpRes, hlt]
    · by_cases he : j = p <;> simp [cmpRes, hlt, he]
  have xb : NRuns ([starAdvanceP r, starStuckP r, starStuckP r] : List (NProg K))[cmpRes j p] X
      (if j < p then starState r S j true else starResult r S p 0) 3 := by
    rw [hs]
    by_cases hlt : j < p
    · simp only [if_pos hlt]; exact starAdvance_runs r S p j
    · simp only [if_neg hlt]; exact starStuck_runs r S p j
  have xd := caseTop_saved (r.get 10) [starAdvanceP r, starStuckP r, starStuckP r] (starStuckP r)
    (cmpRes j p) (by simpa using hv) X _ 3 xb
  have hc := cmpCost_le hj hp
  exact (xc.seq xd).mono (by unfold starCompareCost; omega)

def starAfterP {K : Nat} (r : StarRegs K) : NProg K :=
  .ite (r.get 16) .zero (.prim (.dec (r.get 17)))
    (.seq (.prim (.dec (r.get 16))) (.ite (r.get 16) .zero (starFailureP r)
      (.seq (.prim (.dec (r.get 16))) (starCompareP r))))

def starNextState {K : Nat} (r : StarRegs K) (S : Lists K) (p : Nat) : Res → Lists K
  | none => starResult r S p 0
  | some none => starResult r S p (p + 2)
  | some (some j) => if j < p then starState r S j true else starResult r S p 0

/-- The complete post-body step implements precisely the repetition's three-valued transition. -/
theorem starAfter_runs {K : Nat} (r : StarRegs K) (S : Lists K) (p n : Nat) (u : Res)
    (hp : p ≤ n) (hu : ∀ j, u = some (some j) → j ≤ n) :
    NRuns (starAfterP r) ((starState r S p true).set (r.get 16) (S (r.get 16) ++ [resultCode u]))
      (starNextState r S p u) (starCompareCost n + 5) := by
  let X := starState r S p true
  cases u with
  | none =>
    have hx := (starUnknown_runs r S p).iteT (i := r.get 16) (c := .zero)
      (q := .seq (.prim (.dec (r.get 16))) (.ite (r.get 16) .zero (starFailureP r)
        (.seq (.prim (.dec (r.get 16))) (starCompareP r)))) (by simp [NTest.eval])
    simpa only [starAfterP, starNextState, resultCode] using hx.mono (by unfold starCompareCost; omega)
  | some u =>
    cases u with
    | none =>
      have xd := nruns_dec (r.get 16) (X.set (r.get 16) (S (r.get 16) ++ [1]))
        (l := S (r.get 16)) (v := 1) (by simp)
      simp only [Lists.set_set_u, Nat.reduceSub] at xd
      have xb := (starFailure_runs r S p).iteT (i := r.get 16) (c := .zero)
        (q := .seq (.prim (.dec (r.get 16))) (starCompareP r)) (by simp [NTest.eval])
      have hx := (xd.seq xb).iteF (i := r.get 16) (c := .zero) (p := .prim (.dec (r.get 17)))
        (by simp [NTest.eval])
      simpa only [starAfterP, starNextState, resultCode, X] using hx.mono (by unfold starCompareCost; omega)
    | some j =>
      have xd := nruns_dec (r.get 16) (X.set (r.get 16) (S (r.get 16) ++ [j + 2]))
        (l := S (r.get 16)) (v := j + 2) (by simp)
      simp only [Lists.set_set_u, show j + 2 - 1 = j + 1 by omega] at xd
      have xe := nruns_dec (r.get 16) (X.set (r.get 16) (S (r.get 16) ++ [j + 1]))
        (l := S (r.get 16)) (v := j + 1) (by simp)
      simp only [Lists.set_set_u, Nat.add_sub_cancel] at xe
      have xc := starCompare_runs r S p j n hp (hu j rfl)
      have xb := (xe.seq xc).iteF (i := r.get 16) (c := .zero) (p := starFailureP r) (by simp [NTest.eval])
      have hx := (xd.seq xb).iteF (i := r.get 16) (c := .zero) (p := .prim (.dec (r.get 17))) (by simp [NTest.eval])
      simpa only [starAfterP, starNextState, resultCode, X] using hx.mono (by omega)

def starLoopP {K : Nat} (r : StarRegs K) (body : NProg K) : NProg K :=
  .loop (r.get 17) .pos (.seq body (starAfterP r))

private theorem star_loop_continue {K : Nat} (r : StarRegs K) (body : NProg K)
    (S X Y : Lists K) (A B : Nat) (ht : NTest.pos.eval (S (r.get 17)) = true)
    (ha : NRuns (.seq body (starAfterP r)) S X A) (hb : NRuns (starLoopP r body) X Y B) :
    NRuns (starLoopP r body) S Y (A + 1 + B) := by
  obtain ⟨a, hA, xa⟩ := ha
  obtain ⟨b, hB, xb⟩ := hb
  exact ⟨a + 1 + b, by omega, .loopC trivial ht xa xb⟩

/-- The real repetition loop follows `evStar`; each continued iteration strictly decreases the position. -/
theorem starLoop_runs {K : Nat} (r : StarRegs K) (body : NProg K) (S : Lists K)
    (f : Nat → Res) (n B : Nat)
    (hbody : ∀ q, q ≤ n → NRuns body (starState r S q true)
      ((starState r S q true).set (r.get 16) (S (r.get 16) ++ [resultCode (f q)])) B)
    (hbound : ∀ q, q ≤ n → ∀ j, f q = some (some j) → j ≤ n)
    (p : Nat) (hp : p ≤ n) :
    ∃ q, q ≤ p ∧ NRuns (starLoopP r body) (starState r S p true)
      (starResult r S q (resultCode (evStar f p))) ((p + 1) * (B + starCompareCost n + 6) + 1) := by
  induction p using Nat.strongRecOn with
  | _ p ih =>
    have htest : NTest.pos.eval (starState r S p true (r.get 17)) = true := by
      simp [starState, NTest.eval]
    have step := (hbody p hp).seq (starAfter_runs r S p n (f p) hp (hbound p hp))
    have stop : ∀ q v, NRuns (starLoopP r body) (starResult r S q v) (starResult r S q v) 1 := by
      intro q v
      exact nruns_loop_exit (by simp [starResult, starState, Lists.set, NTest.eval])
    have terminalCost : B + (starCompareCost n + 5) + 1 + 1 ≤
        (p + 1) * (B + starCompareCost n + 6) + 1 := by
      have hm := Nat.le_mul_of_pos_left (B + starCompareCost n + 6) (show 0 < p + 1 by omega)
      omega
    cases hf : f p with
    | none =>
      rw [hf] at step
      simp only [starNextState] at step
      have hx := star_loop_continue r body _ _ _ _ _ htest step (stop p 0)
      rw [evStar_none hf]
      exact ⟨p, Nat.le_refl _, hx.mono terminalCost⟩
    | some u =>
      cases u with
      | none =>
        rw [hf] at step
        simp only [starNextState] at step
        have hx := star_loop_continue r body _ _ _ _ _ htest step (stop p (p + 2))
        rw [evStar_fail hf]
        exact ⟨p, Nat.le_refl _, hx.mono terminalCost⟩
      | some j =>
        rw [hf] at step
        simp only [starNextState] at step
        by_cases hj : j < p
        · rw [if_pos hj] at step
          obtain ⟨q, hq, hx⟩ := ih j hj (by omega)
          have full := star_loop_continue r body _ _ _ _ _ htest step hx
          rw [evStar_ok hf hj]
          refine ⟨q, by omega, full.mono ?_⟩
          have hm := Nat.mul_le_mul_right (B + starCompareCost n + 6) (show j + 1 ≤ p by omega)
          simp only [Nat.add_mul, Nat.one_mul] at hm ⊢
          omega
        · rw [if_neg hj] at step
          have hx := star_loop_continue r body _ _ _ _ _ htest step (stop p 0)
          rw [evStar_stuck hf hj]
          exact ⟨p, Nat.le_refl _, hx.mono terminalCost⟩

/-- Remove the two local frames while preserving the final answer and every caller stack. -/
def starCleanupP {K : Nat} (r : StarRegs K) : NProg K :=
  .seq (.prim (.pop (r.get 17))) (.prim (.pop (r.get 15)))

theorem starCleanup_runs {K : Nat} (r : StarRegs K) (S : Lists K) (p v : Nat) :
    NRuns (starCleanupP r) (starResult r S p v) (S.set (r.get 16) (S (r.get 16) ++ [v])) 2 := by
  let X := starResult r S p v
  have xf := nruns_pop (r.get 17) X (l := S (r.get 17)) (v := 0)
    (by simp [X, starResult, starState, Lists.set])
  let Y := X.set (r.get 17) (S (r.get 17))
  have xp := nruns_pop (r.get 15) Y (l := S (r.get 15)) (v := p)
    (by simp [Y, X, starResult, starState, Lists.set])
  have he : Y.set (r.get 15) (S (r.get 15)) = S.set (r.get 16) (S (r.get 16) ++ [v]) := by
    simp only [Y, X, starResult, starState]
    star_states r
  rw [he] at xp
  exact xf.seq xp

def starPrepareP {K : Nat} (r : StarRegs K) : NProg K :=
  .seq (.prim (.dup (r.get 15) (r.get 3) (r.ne (by decide))))
    (.seq (nmv (r.get 3) (r.get 15) (r.ne (by decide))) (npushC (r.get 17) 1))

theorem starPrepare_runs {K : Nat} (r : StarRegs K) (S : Lists K) (p : Nat)
    {lp : List Nat} (hp : S (r.get 15) = lp ++ [p]) :
    NRuns (starPrepareP r) S (starState r S p true) 5 := by
  have xd := nruns_dup (r.get 15) (r.get 3) (r.ne (by decide)) S hp
  let X := S.set (r.get 3) (S (r.get 3) ++ [p])
  have xm := nruns_mv (r.get 3) (r.get 15) (r.ne (by decide)) X
    (l := S (r.get 3)) (v := p) (by simp [X])
  have he : (X.set (r.get 15) (X (r.get 15) ++ [p])).set (r.get 3) (S (r.get 3)) =
      S.set (r.get 15) (S (r.get 15) ++ [p]) := by
    funext z
    by_cases h3 : z = r.get 3
    · subst z; simp [X, Lists.set]
    by_cases h15 : z = r.get 15
    · subst z; simp [X, Lists.set]
    simp [X, Lists.set, h3, h15]
  rw [he] at xm
  have xf := nruns_pushC (r.get 17) (S.set (r.get 15) (S (r.get 15) ++ [p])) 1
  have hf : (S.set (r.get 15) (S (r.get 15) ++ [p])) (r.get 17) = S (r.get 17) := by simp [Lists.set]
  rw [hf] at xf
  exact xd.seq (xm.seq xf)

def starEvalP {K : Nat} (r : StarRegs K) (body : NProg K) : NProg K :=
  .seq (starPrepareP r) (.seq (starLoopP r body) (starCleanupP r))

def starEvalCost (n B : Nat) : Nat := (n + 1) * (B + starCompareCost n + 6) + 8

/-- The full repetition program, including setup and cleanup, implements the source evaluator. -/
theorem starEval_runs {K : Nat} (r : StarRegs K) (body : NProg K) (S : Lists K)
    (f : Nat → Res) (n B p : Nat) {lp : List Nat} (hp : S (r.get 15) = lp ++ [p]) (hpn : p ≤ n)
    (hbody : ∀ q, q ≤ n → NRuns body (starState r S q true)
      ((starState r S q true).set (r.get 16) (S (r.get 16) ++ [resultCode (f q)])) B)
    (hbound : ∀ q, q ≤ n → ∀ j, f q = some (some j) → j ≤ n) :
    NRuns (starEvalP r body) S (S.set (r.get 16) (S (r.get 16) ++ [resultCode (evStar f p)]))
      (starEvalCost n B) := by
  have xp := starPrepare_runs r S p hp
  obtain ⟨q, _, xl⟩ := starLoop_runs r body S f n B hbody hbound p hpn
  have xc := starCleanup_runs r S q (resultCode (evStar f p))
  have hm := Nat.mul_le_mul_right (B + starCompareCost n + 6) (show p + 1 ≤ n + 1 by omega)
  exact (xp.seq (xl.seq xc)).mono (by unfold starEvalCost; omega)

theorem starCompareCost_poly : IsPoly starCompareCost :=
  isPoly_add (isPoly_mul (isPoly_add (isPoly_mul (isPoly_const 2) isPoly_id) (isPoly_const 1))
    (isPoly_add (isPoly_mul (isPoly_const 2) isPoly_id) (isPoly_const 6))) (isPoly_const 29)

theorem starEvalCost_poly (B : Nat → Nat) (hB : IsPoly B) : IsPoly (fun n => starEvalCost n (B n)) :=
  isPoly_add (isPoly_mul (isPoly_add isPoly_id (isPoly_const 1))
    (isPoly_add (isPoly_add hB starCompareCost_poly) (isPoly_const 6))) (isPoly_const 8)

end Shallot.MacroPeg.CBV
