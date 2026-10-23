import MacroPeg.CBV.PositionSweep

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.KExp

theorem EvalReady.withEnv {K : Nat} {r : EvalRegs K} {S : Lists K} {x : List Char} {row E : List Nat}
    (h : EvalReady r S x row E) (F : List Nat) : EvalReady r (S.set (r.get 24) F) x row F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp⟩
  · simpa [Lists.set] using h.word
  · simpa [Lists.set] using h.tmp
  · intro i hi
    have hn : i ≠ (24 : Fin 32) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [Lists.set, hn] using h.clean i hi
  · simpa [Lists.set] using h.dict
  · simpa [Lists.set] using h.count
  · simpa [Lists.set] using h.len
  · simpa [Lists.set] using h.table

def envValues (g : MGrammar) (s : Strategy) (x : List Char) (row E : List Nat) (e : MExp) (k : Nat) : List Nat :=
  (words (List.range (subStrs x).length) k).flatMap (fun ids => positionValues g s x row (E ++ ids) e)

@[simp] theorem envValues_zero (g : MGrammar) (s : Strategy) (x : List Char) (row E : List Nat) (e : MExp) :
    envValues g s x row E e 0 = positionValues g s x row E e := by simp [envValues, words]

theorem envValues_succ (g : MGrammar) (s : Strategy) (x : List Char) (row E : List Nat) (e : MExp) (k : Nat) :
    envValues g s x row E e (k + 1) = (List.range (subStrs x).length).flatMap
      (fun d => envValues g s x row (E ++ [d]) e k) := by
  simp [envValues, words, List.flatMap_assoc, List.flatMap_map, List.append_assoc]

def envState {K : Nat} (r : EvalRegs K) (S : Lists K) (out : List Nat) (digit remaining : Nat) : Lists K :=
  ((S.set (r.get 25) out).set (r.get 27) (S (r.get 27) ++ [digit])).set
    (r.get 26) (S (r.get 26) ++ [remaining])

theorem EvalReady.environments {K : Nat} {r : EvalRegs K} {S : Lists K} {x : List Char} {row E : List Nat}
    (h : EvalReady r S x row E) (out : List Nat) (d remaining : Nat) :
    EvalReady r (envState r S out d remaining) x row E :=
  ((h.reserved 25 (by decide) out).reserved 27 (by decide) _).reserved 26 (by decide) _

macro "env_states " r:term : tactic => `(tactic| (
  funext z
  by_cases h24 : z = ($r).get 24
  · subst z; simp_all [Lists.set] <;> omega
  by_cases h25 : z = ($r).get 25
  · subst z; simp_all [Lists.set] <;> omega
  by_cases h26 : z = ($r).get 26
  · subst z; simp_all [Lists.set] <;> omega
  by_cases h27 : z = ($r).get 27
  · subst z; simp_all [Lists.set] <;> omega
  simp_all [Lists.set] <;> omega))

def envBodyP {K : Nat} (r : EvalRegs K) (inner : NProg K) : NProg K :=
  .seq (.prim (.dup (r.get 27) (r.get 24) (r.ne (by decide))))
    (.seq inner (.seq (.prim (.pop (r.get 24)))
      (.seq (.prim (.inc (r.get 27))) (.prim (.dec (r.get 26))))))

theorem envBody_runs {K : Nat} (r : EvalRegs K) (inner : NProg K) (S : Lists K) (E out values : List Nat)
    (d remaining B : Nat) (hE : S (r.get 24) = E)
    (hi : let X := (envState r S out d remaining).set (r.get 24) (E ++ [d])
      NRuns inner X (X.set (r.get 25) (out ++ values)) B) :
    NRuns (envBodyP r inner) (envState r S out d remaining)
      (envState r S (out ++ values) (d + 1) (remaining - 1)) (B + 4) := by
  let X := envState r S out d remaining
  have xd := nruns_dup (r.get 27) (r.get 24) (r.ne (by decide)) X
    (l := S (r.get 27)) (v := d) (by simp [X, envState, Lists.set])
  have hx24 : X (r.get 24) = E := by simp [X, envState, Lists.set, hE]
  rw [hx24] at xd
  let Y := X.set (r.get 24) (E ++ [d])
  let Z := Y.set (r.get 25) (out ++ values)
  have xp := nruns_pop (r.get 24) Z (l := E) (v := d) (by simp [Z, Y, Lists.set])
  let W := Z.set (r.get 24) E
  have xi := nruns_inc (r.get 27) W (l := S (r.get 27)) (v := d)
    (by simp [W, Z, Y, X, envState, Lists.set])
  let U := W.set (r.get 27) (S (r.get 27) ++ [d + 1])
  have xc := nruns_dec (r.get 26) U (l := S (r.get 26)) (v := remaining)
    (by simp [U, W, Z, Y, X, envState, Lists.set])
  have he : U.set (r.get 26) (S (r.get 26) ++ [remaining - 1]) = envState r S (out ++ values) (d + 1) (remaining - 1) := by
    simp only [U, W, Z, Y, X, envState]
    env_states r
  rw [he] at xc
  exact (xd.seq (hi.seq (xp.seq (xi.seq xc)))).mono (by omega)

def envPrepareP {K : Nat} (r : EvalRegs K) : NProg K :=
  .seq (.prim (.pushZ (r.get 27))) (.prim (.dup (r.get 19) (r.get 26) (r.ne (by decide))))

theorem envPrepare_runs {K : Nat} (r : EvalRegs K) (S : Lists K) (D : Nat) (hD : S (r.get 19) = [D]) :
    NRuns (envPrepareP r) S (envState r S (S (r.get 25)) 0 D) 2 := by
  have xz := nruns_pushZ (r.get 27) S
  let X := S.set (r.get 27) (S (r.get 27) ++ [0])
  have xd := nruns_dup (r.get 19) (r.get 26) (r.ne (by decide)) X (l := []) (v := D)
    (by simp [X, Lists.set, hD])
  have he : X.set (r.get 26) (X (r.get 26) ++ [D]) = envState r S (S (r.get 25)) 0 D := by
    simp only [X, envState]
    env_states r
  rw [he] at xd
  exact xz.seq xd

def envCleanupP {K : Nat} (r : EvalRegs K) : NProg K :=
  .seq (.prim (.pop (r.get 26))) (.prim (.pop (r.get 27)))

theorem envCleanup_runs {K : Nat} (r : EvalRegs K) (S : Lists K) (out : List Nat) (d remaining : Nat) :
    NRuns (envCleanupP r) (envState r S out d remaining) (S.set (r.get 25) out) 2 := by
  let X := envState r S out d remaining
  have xc := nruns_pop (r.get 26) X (l := S (r.get 26)) (v := remaining) (by simp [X, envState])
  let Y := X.set (r.get 26) (S (r.get 26))
  have xd := nruns_pop (r.get 27) Y (l := S (r.get 27)) (v := d) (by simp [Y, X, envState, Lists.set])
  have he : Y.set (r.get 27) (S (r.get 27)) = S.set (r.get 25) out := by
    simp only [Y, X, envState]
    env_states r
  rw [he] at xd
  exact xc.seq xd

def envSweepP {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (m : Nat) (e : MExp) : Nat → NProg K
  | 0 => positionSweepP r g s m e
  | k + 1 => .seq (envPrepareP r)
      (.seq (.loop (r.get 26) .pos (envBodyP r (envSweepP r g s m e k))) (envCleanupP r))

def envSweepCost (g : MGrammar) (m : Nat) (e : MExp) : Nat → Nat → Nat
  | 0, n => positionSweepCost g m e n
  | k + 1, n => dictCap n * (envSweepCost g m e k n + 5) + 5

/-- Enumerate all identifier vectors in dictionary order, generating every position row for each vector. -/
theorem envSweep_runs {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (x : List Char)
    (T : Nat → List (List Char) → Val) (hT : OkTV x.length T) (m : Nat) (e : MExp) :
    ∀ (k : Nat) (E : List Nat), E.length + k = m →
    (∀ i ∈ E, i < (spans x.length).length) → ∀ (S : Lists K), EvalReady r S x (pack g x T) E →
    NRuns (envSweepP r g s m e k) S (S.set (r.get 25) (S (r.get 25) ++ envValues g s x (pack g x T) E e k))
      (envSweepCost g m e k x.length) := by
  intro k
  induction k with
  | zero =>
    intro E hm hE S ready
    simp only [Nat.add_zero] at hm
    subst m
    simpa only [envSweepP, envSweepCost, envValues_zero] using positionSweep_runs r g s x T E hT hE e S ready
  | succ k ih =>
    intro E hm hE S ready
    let D := (subStrs x).length
    let value := fun d => envValues g s x (pack g x T) (E ++ [d]) e k
    let F := fun j => envState r S (S (r.get 25) ++ (List.range j).flatMap value) j (D - j)
    have hl := nruns_family_const (i := r.get 26) (c := .pos) (p := envBodyP r (envSweepP r g s m e k))
      F D (envSweepCost g m e k x.length + 4)
      (by
        intro j hj
        have he : D - j = (D - 1 - j) + 1 := by omega
        simp [F, envState, Lists.set, NTest.eval, he])
      (by simp [F, envState, Lists.set, NTest.eval])
      (by
        intro d hd
        let out := S (r.get 25) ++ (List.range d).flatMap value
        let Y := (envState r S out d (D - d)).set (r.get 24) (E ++ [d])
        have hy := (ready.environments out d (D - d)).withEnv (E ++ [d])
        have hnew : ∀ i ∈ E ++ [d], i < (spans x.length).length := by
          intro i hi
          rcases List.mem_append.mp hi with hi | hi
          · exact hE i hi
          · have he : i = d := List.mem_singleton.mp hi
            subst i
            simpa only [spans_length] using hd
        have xm := ih (E ++ [d]) (by simp only [List.length_append, List.length_singleton]; omega) hnew Y hy
        have hy25 : Y (r.get 25) = out := by simp [Y, envState, Lists.set]
        rw [hy25] at xm
        have xb := envBody_runs r (envSweepP r g s m e k) S E out (value d) d (D - d)
          (envSweepCost g m e k x.length) ready.env xm
        have he : envState r S (out ++ value d) (d + 1) (D - d - 1) = F (d + 1) := by
          simp [F, out, List.range_succ, List.flatMap_append, List.append_assoc, Nat.sub_sub]
        rw [he] at xb
        exact xb)
    have hcount : S (r.get 19) = [D] := by simpa only [spans_length] using ready.count
    have xp := envPrepare_runs r S D hcount
    have hfirst : F 0 = envState r S (S (r.get 25)) 0 D := by simp [F]
    have hlast : F D = envState r S (S (r.get 25) ++ envValues g s x (pack g x T) E e (k + 1)) D 0 := by
      simp [F, value, D, envValues_succ]
    rw [hfirst, hlast] at hl
    have xc := envCleanup_runs r S (S (r.get 25) ++ envValues g s x (pack g x T) E e (k + 1)) D 0
    have hD := length_subStrs_le x
    have hmul := Nat.mul_le_mul_right (envSweepCost g m e k x.length + 5) hD
    exact (xp.seq (hl.seq xc)).mono (by
      change 2 + (D * (envSweepCost g m e k x.length + 4 + 1) + 1 + 2) ≤
        dictCap x.length * (envSweepCost g m e k x.length + 5) + 5
      dsimp only [D]
      unfold dictCap
      simp only [Nat.add_assoc, Nat.reduceAdd]
      omega)

theorem envSweepCost_poly (g : MGrammar) (m : Nat) (e : MExp) : ∀ k, IsPoly (envSweepCost g m e k)
  | 0 => positionSweepCost_poly g m e
  | k + 1 => isPoly_add (isPoly_mul
      (isPoly_mul (isPoly_add isPoly_id (isPoly_const 1)) (isPoly_add isPoly_id (isPoly_const 1)))
      (isPoly_add (envSweepCost_poly g m e k) (isPoly_const 5))) (isPoly_const 5)

end Shallot.MacroPeg.CBV
