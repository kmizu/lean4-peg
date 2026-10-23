import MacroPeg.CBV.SpanCost

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.Mach Shallot.MacroPeg.KExp

/-- Six dedicated registers: dictionary, entry count, first end, second end, outer and inner counters. -/
structure SpanBuildRegs (K : Nat) where
  get : Fin 6 → Fin K
  inj : ∀ i j, get i = get j → i = j

@[simp] theorem SpanBuildRegs.eq {K : Nat} (r : SpanBuildRegs K) (i j : Fin 6) :
    r.get i = r.get j ↔ i = j := ⟨r.inj i j, congrArg r.get⟩

theorem SpanBuildRegs.ne {K : Nat} (r : SpanBuildRegs K) {i j : Fin 6} (h : i ≠ j) : r.get i ≠ r.get j :=
  fun he => h (r.inj i j he)

def spanBuildState {K : Nat} (r : SpanBuildRegs K) (S : Lists K)
    (row : List Nat) (count p j outer inner : Nat) : Lists K :=
  (((((S.set (r.get 0) row).set (r.get 1) [count]).set (r.get 2) [p]).set (r.get 3) [j]).set
    (r.get 4) [outer]).set (r.get 5) [inner]

@[simp] theorem spanBuildState_row {K : Nat} (r : SpanBuildRegs K) (S : Lists K) (row : List Nat) (c p j o v : Nat) :
    spanBuildState r S row c p j o v (r.get 0) = row := by simp [spanBuildState, Lists.set]
@[simp] theorem spanBuildState_count {K : Nat} (r : SpanBuildRegs K) (S : Lists K) (row : List Nat) (c p j o v : Nat) :
    spanBuildState r S row c p j o v (r.get 1) = [c] := by simp [spanBuildState, Lists.set]
@[simp] theorem spanBuildState_p {K : Nat} (r : SpanBuildRegs K) (S : Lists K) (row : List Nat) (c p j o v : Nat) :
    spanBuildState r S row c p j o v (r.get 2) = [p] := by simp [spanBuildState, Lists.set]
@[simp] theorem spanBuildState_j {K : Nat} (r : SpanBuildRegs K) (S : Lists K) (row : List Nat) (c p j o v : Nat) :
    spanBuildState r S row c p j o v (r.get 3) = [j] := by simp [spanBuildState, Lists.set]
@[simp] theorem spanBuildState_outer {K : Nat} (r : SpanBuildRegs K) (S : Lists K) (row : List Nat) (c p j o v : Nat) :
    spanBuildState r S row c p j o v (r.get 4) = [o] := by simp [spanBuildState, Lists.set]
@[simp] theorem spanBuildState_inner {K : Nat} (r : SpanBuildRegs K) (S : Lists K) (row : List Nat) (c p j o v : Nat) :
    spanBuildState r S row c p j o v (r.get 5) = [v] := by simp [spanBuildState, Lists.set]

macro "span_states " r:term : tactic => `(tactic| (
  funext k
  by_cases h0 : k = ($r).get 0
  · subst k; simp_all [Lists.set] <;> omega
  by_cases h1 : k = ($r).get 1
  · subst k; simp_all [Lists.set] <;> omega
  by_cases h2 : k = ($r).get 2
  · subst k; simp_all [Lists.set] <;> omega
  by_cases h3 : k = ($r).get 3
  · subst k; simp_all [Lists.set] <;> omega
  by_cases h4 : k = ($r).get 4
  · subst k; simp_all [Lists.set] <;> omega
  by_cases h5 : k = ($r).get 5
  · subst k; simp_all [Lists.set] <;> omega
  simp_all [Lists.set] <;> omega))

def appendSpanP {K : Nat} (r : SpanBuildRegs K) : NProg K :=
  .seq (.prim (.dup (r.get 2) (r.get 0) (r.ne (by decide))))
    (.seq (.prim (.dup (r.get 3) (r.get 0) (r.ne (by decide))))
      (.seq (.prim (.inc (r.get 1))) (.seq (.prim (.inc (r.get 3))) (.prim (.dec (r.get 5))))))

/-- One dictionary entry is emitted by five actual numeric instructions. -/
theorem appendSpan_runs {K : Nat} (r : SpanBuildRegs K) (S : Lists K)
    (row : List Nat) (c p j o v : Nat) :
    NRuns (appendSpanP r) (spanBuildState r S row c p j o v)
      (spanBuildState r S (row ++ [p, j]) (c + 1) p (j + 1) o (v - 1)) 5 := by
  let X := spanBuildState r S row c p j o v
  have x₁ := nruns_dup (r.get 2) (r.get 0) (r.ne (by decide)) X (l := []) (v := p) (by simp [X])
  have x₂ := nruns_dup (r.get 3) (r.get 0) (r.ne (by decide))
    (X.set (r.get 0) (row ++ [p])) (l := []) (v := j) (by simp [Lists.set, X])
  simp only [X, spanBuildState_row] at x₁
  simp only [Lists.set_same] at x₂
  let X₂ := (X.set (r.get 0) (row ++ [p])).set (r.get 0) ((row ++ [p]) ++ [j])
  have x₃ := nruns_inc (r.get 1) X₂ (l := []) (v := c) (by simp [X₂, Lists.set, X])
  let X₃ := X₂.set (r.get 1) [c + 1]
  have x₄ := nruns_inc (r.get 3) X₃ (l := []) (v := j) (by simp [X₃, X₂, Lists.set, X])
  let X₄ := X₃.set (r.get 3) [j + 1]
  have x₅ := nruns_dec (r.get 5) X₄ (l := []) (v := v) (by simp [X₄, X₃, X₂, Lists.set, X])
  have he : X₄.set (r.get 5) ([] ++ [v - 1]) = spanBuildState r S (row ++ [p, j]) (c + 1) p (j + 1) o (v - 1) := by
    simp only [X₄, X₃, X₂, X, spanBuildState]
    span_states r <;> omega
  rw [he] at x₅
  exact x₁.seq (x₂.seq (x₃.seq (x₄.seq x₅)))

/-- Emit every second endpoint from zero through the fixed first endpoint. -/
def innerSpansP {K : Nat} (r : SpanBuildRegs K) : NProg K := .loop (r.get 5) .pos (appendSpanP r)

theorem innerSpans_runs {K : Nat} (r : SpanBuildRegs K) (S : Lists K) (row : List Nat) (c p o : Nat) :
    NRuns (innerSpansP r) (spanBuildState r S row c p 0 o (p + 1))
      (spanBuildState r S (row ++ encPairs ((List.range (p + 1)).map (fun j => (p, j))))
        (c + (p + 1)) p (p + 1) o 0) (6 * (p + 1) + 1) := by
  let F := fun k => spanBuildState r S (row ++ encPairs ((List.range k).map (fun j => (p, j))))
    (c + k) p k o (p + 1 - k)
  have hl := nruns_family_const (i := r.get 5) (c := .pos) (p := appendSpanP r) F (p + 1) 5
    (fun k hk => by
      have he : p + 1 - k = (p - k) + 1 := by omega
      simp [F, NTest.eval, he])
    (by simp [F, NTest.eval])
    (fun k hk => by
      have hx := appendSpan_runs r S (row ++ encPairs ((List.range k).map (fun j => (p, j)))) (c + k) p k o (p + 1 - k)
      have he : spanBuildState r S ((row ++ encPairs ((List.range k).map (fun j => (p, j)))) ++ [p, k])
          (c + k + 1) p (k + 1) o (p + 1 - k - 1) = F (k + 1) := by
        simp [F, List.range_succ, encPairs, List.flatMap_append, List.map_append, List.append_assoc,
          Nat.add_assoc, Nat.sub_sub]
      rw [he] at hx
      exact hx)
  simpa [innerSpansP, F, encPairs, Nat.mul_comm] using hl

/-- Reset the inner endpoint and initialize the inner iteration count from the outer endpoint. -/
def prepareInnerP {K : Nat} (r : SpanBuildRegs K) : NProg K :=
  .seq (.prim (.pop (r.get 3))) (.seq (.prim (.pushZ (r.get 3)))
    (.seq (.prim (.pop (r.get 5)))
      (.seq (.prim (.dup (r.get 2) (r.get 5) (r.ne (by decide)))) (.prim (.inc (r.get 5))))))

theorem prepareInner_runs {K : Nat} (r : SpanBuildRegs K) (S : Lists K)
    (row : List Nat) (c p o : Nat) :
    NRuns (prepareInnerP r) (spanBuildState r S row c p p o 0)
      (spanBuildState r S row c p 0 o (p + 1)) 5 := by
  let X := spanBuildState r S row c p p o 0
  have x₁ := nruns_pop (r.get 3) X (l := []) (v := p) (by simp [X])
  let X₁ := X.set (r.get 3) []
  have x₂ := nruns_pushZ (r.get 3) X₁
  simp only [X₁, Lists.set_same, List.nil_append] at x₂
  let X₂ := X₁.set (r.get 3) [0]
  have x₃ := nruns_pop (r.get 5) X₂ (l := []) (v := 0) (by simp [X₂, X₁, X, Lists.set])
  let X₃ := X₂.set (r.get 5) []
  have x₄ := nruns_dup (r.get 2) (r.get 5) (r.ne (by decide)) X₃ (l := []) (v := p)
    (by simp [X₃, X₂, X₁, X, Lists.set])
  simp only [X₃, Lists.set_same, List.nil_append] at x₄
  let X₄ := X₃.set (r.get 5) [p]
  have x₅ := nruns_inc (r.get 5) X₄ (l := []) (v := p) (by simp [X₄])
  have he : X₄.set (r.get 5) ([] ++ [p + 1]) = spanBuildState r S row c p 0 o (p + 1) := by
    simp only [X₄, X₃, X₂, X₁, X, spanBuildState]
    span_states r <;> omega
  rw [he] at x₅
  exact x₁.seq (x₂.seq (x₃.seq (x₄.seq x₅)))

def spanPrefix (p : Nat) : List (Nat × Nat) :=
  (List.range p).flatMap (fun q => (List.range (q + 1)).map (fun j => (q, j)))

theorem spanPrefix_succ (p : Nat) :
    spanPrefix (p + 1) = spanPrefix p ++ (List.range (p + 1)).map (fun j => (p, j)) := by
  simp [spanPrefix, List.range_succ, List.flatMap_append]

def outerSpanP {K : Nat} (r : SpanBuildRegs K) : NProg K :=
  .seq (prepareInnerP r) (.seq (innerSpansP r)
    (.seq (.prim (.inc (r.get 2))) (.prim (.dec (r.get 4)))))

theorem outerSpan_runs {K : Nat} (r : SpanBuildRegs K) (S : Lists K) (n p : Nat) :
    NRuns (outerSpanP r)
      (spanBuildState r S (encPairs (spanPrefix p)) (spanPrefix p).length p p (n + 1 - p) 0)
      (spanBuildState r S (encPairs (spanPrefix (p + 1))) (spanPrefix (p + 1)).length
        (p + 1) (p + 1) (n + 1 - (p + 1)) 0) (6 * (p + 1) + 8) := by
  have x₁ := prepareInner_runs r S (encPairs (spanPrefix p)) (spanPrefix p).length p (n + 1 - p)
  have x₂ := innerSpans_runs r S (encPairs (spanPrefix p)) (spanPrefix p).length p (n + 1 - p)
  let X₂ := spanBuildState r S
    (encPairs (spanPrefix p) ++ encPairs ((List.range (p + 1)).map (fun j => (p, j))))
    ((spanPrefix p).length + (p + 1)) p (p + 1) (n + 1 - p) 0
  have x₃ := nruns_inc (r.get 2) X₂ (l := []) (v := p) (by simp [X₂])
  let X₃ := X₂.set (r.get 2) [p + 1]
  have x₄ := nruns_dec (r.get 4) X₃ (l := []) (v := n + 1 - p) (by simp [X₃, X₂, Lists.set])
  have he : X₃.set (r.get 4) ([] ++ [n + 1 - p - 1]) =
      spanBuildState r S (encPairs (spanPrefix (p + 1))) (spanPrefix (p + 1)).length
        (p + 1) (p + 1) (n + 1 - (p + 1)) 0 := by
    simp only [X₃, X₂, spanPrefix_succ, encPairs, List.flatMap_append, List.length_append,
      List.length_map, List.length_range, spanBuildState]
    span_states r <;> omega
  rw [he] at x₄
  exact (x₁.seq (x₂.seq (x₃.seq x₄))).mono (by omega)

/-- The outer loop emits all valid pairs in exactly the substring dictionary's order. -/
def allSpansP {K : Nat} (r : SpanBuildRegs K) : NProg K := .loop (r.get 4) .pos (outerSpanP r)

theorem allSpans_runs {K : Nat} (r : SpanBuildRegs K) (S : Lists K) (n : Nat) :
    NRuns (allSpansP r) (spanBuildState r S [] 0 0 0 (n + 1) 0)
      (spanBuildState r S (encPairs (spans n)) (spans n).length (n + 1) (n + 1) 0 0)
      ((n + 1) * (6 * (n + 1) + 9) + 1) := by
  let F := fun p => spanBuildState r S (encPairs (spanPrefix p)) (spanPrefix p).length p p (n + 1 - p) 0
  have hl := nruns_family_const (i := r.get 4) (c := .pos) (p := outerSpanP r) F (n + 1) (6 * (n + 1) + 8)
    (fun p hp => by
      have he : n + 1 - p = (n - p) + 1 := by omega
      simp [F, NTest.eval, he])
    (by simp [F, NTest.eval])
    (fun p hp => (outerSpan_runs r S n p).mono (by omega))
  simpa [allSpansP, F, spanPrefix, spans, encPairs] using hl

def spanBuildP {K : Nat} (r : SpanBuildRegs K) : NProg K :=
  .seq (.prim (.pushZ (r.get 1))) (.seq (.prim (.pushZ (r.get 2)))
    (.seq (.prim (.pushZ (r.get 3))) (.seq (.prim (.pushZ (r.get 5)))
      (.seq (allSpansP r) (.seq (.prim (.pop (r.get 5))) (.seq (.prim (.pop (r.get 3)))
        (.seq (.prim (.pop (r.get 2))) (.prim (.pop (r.get 4))))))))))

def spanBuildCost (n : Nat) : Nat := (n + 1) * (6 * (n + 1) + 9) + 9

/-- Construct the entire span dictionary and its entry count from the actual numeric length counter. -/
theorem spanBuild_runs {K : Nat} (r : SpanBuildRegs K) (S : Lists K) (n : Nat)
    (hrow : S (r.get 0) = []) (hc : S (r.get 1) = []) (hp : S (r.get 2) = [])
    (hj : S (r.get 3) = []) (ho : S (r.get 4) = [n + 1]) (hv : S (r.get 5) = []) :
    NRuns (spanBuildP r) S
      (((S.set (r.get 0) (encPairs (spans n))).set (r.get 1) [(spans n).length]).set (r.get 4) [])
      (spanBuildCost n) := by
  have z₁ := nruns_pushZ (r.get 1) S
  rw [hc, List.nil_append] at z₁
  let S₁ := S.set (r.get 1) [0]
  have z₂ := nruns_pushZ (r.get 2) S₁
  have h₂ : S₁ (r.get 2) = [] := by simp [S₁, Lists.set, hp]
  rw [h₂, List.nil_append] at z₂
  let S₂ := S₁.set (r.get 2) [0]
  have z₃ := nruns_pushZ (r.get 3) S₂
  have h₃ : S₂ (r.get 3) = [] := by simp [S₂, S₁, Lists.set, hj]
  rw [h₃, List.nil_append] at z₃
  let S₃ := S₂.set (r.get 3) [0]
  have z₄ := nruns_pushZ (r.get 5) S₃
  have h₄ : S₃ (r.get 5) = [] := by simp [S₃, S₂, S₁, Lists.set, hv]
  rw [h₄, List.nil_append] at z₄
  have hinit : S₃.set (r.get 5) [0] = spanBuildState r S [] 0 0 0 (n + 1) 0 := by
    simp only [S₃, S₂, S₁, spanBuildState]
    span_states r
  rw [hinit] at z₄
  have lp := allSpans_runs r S n
  let X := spanBuildState r S (encPairs (spans n)) (spans n).length (n + 1) (n + 1) 0 0
  have p₁ := nruns_pop (r.get 5) X (l := []) (v := 0) (by simp [X])
  let X₁ := X.set (r.get 5) []
  have p₂ := nruns_pop (r.get 3) X₁ (l := []) (v := n + 1) (by simp [X₁, X, Lists.set])
  let X₂ := X₁.set (r.get 3) []
  have p₃ := nruns_pop (r.get 2) X₂ (l := []) (v := n + 1) (by simp [X₂, X₁, X, Lists.set])
  let X₃ := X₂.set (r.get 2) []
  have p₄ := nruns_pop (r.get 4) X₃ (l := []) (v := 0) (by simp [X₃, X₂, X₁, X, Lists.set])
  have hend : X₃.set (r.get 4) [] =
      (((S.set (r.get 0) (encPairs (spans n))).set (r.get 1) [(spans n).length]).set (r.get 4) []) := by
    simp only [X₃, X₂, X₁, X, spanBuildState]
    span_states r
  rw [hend] at p₄
  exact (z₁.seq (z₂.seq (z₃.seq (z₄.seq (lp.seq (p₁.seq (p₂.seq (p₃.seq p₄)))))))).mono
    (by unfold spanBuildCost; omega)

/-- The complete dictionary constructor takes quadratic numeric-stack time. -/
theorem spanBuildCost_poly : IsPoly spanBuildCost := by
  have hn := isPoly_add isPoly_id (isPoly_const 1)
  exact isPoly_add (isPoly_mul hn (isPoly_add (isPoly_mul (isPoly_const 6) hn) (isPoly_const 9))) (isPoly_const 9)

end Shallot.MacroPeg.CBV
