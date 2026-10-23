import MacroPeg.CBV.Iteration

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.KExp

def sizeRegs {K : Nat} (r : EvalRegs K) : AddrExpr.Regs K 2 where
  out := r.get 2
  a := r.get 5
  b := r.get 6
  tmp := r.get 1
  vars i := if i.val = 0 then r.get 19 else r.get 20
  ab := r.ne (by decide)
  atmp := r.ne (by decide)
  ao := r.ne (by decide)
  btmp := r.ne (by decide)
  bo := r.ne (by decide)
  to := r.ne (by decide)
  vo i := by split <;> simp

def tableSizeExpr (g : MGrammar) : AddrExpr 2 :=
  AddrExpr.sumExpr ((List.range g.rules.length).map
    (fun i => AddrExpr.widthExpr g i (.var 0) (.add (.var 1) (.num 1))))

theorem tableSizeExpr_value (g : MGrammar) (x : List Char) (f : Fin 2 → Nat)
    (hD : f 0 = (subStrs x).length) (hn : f 1 = x.length) :
    AddrExpr.value f (tableSizeExpr g) = iterBoundV g x := by
  rw [tableSizeExpr, AddrExpr.value_sumExpr, List.map_map]
  unfold iterBoundV
  congr 1
  apply List.map_congr_left
  intro i _
  cases hr : ruleAtM g.rules i <;>
    simp [AddrExpr.widthExpr, hr, length_words, AddrExpr.value, AddrExpr.value_power, hD, hn]

def tableCountP {K : Nat} (r : EvalRegs K) (g : MGrammar) : NProg K :=
  .seq (AddrExpr.compile (sizeRegs r) (tableSizeExpr g)) (nmv (r.get 2) (r.get 29) (r.ne (by decide)))

def tableCountCost (g : MGrammar) (n : Nat) : Nat :=
  AddrExpr.cost (fun _ => varsCap g n) (tableSizeExpr g) + 2

/-- Compute the exact number of cells using unary arithmetic and keep it as the saturation counter. -/
theorem tableCount_runs {K : Nat} (r : EvalRegs K) (g : MGrammar) (x : List Char) (row E : List Nat)
    (S : Lists K) (ready : EvalReady r S x row E) :
    NRuns (tableCountP r g) S (S.set (r.get 29) (S (r.get 29) ++ [iterBoundV g x]))
      (tableCountCost g x.length) := by
  let f : Fin 2 → Nat := fun i => if i.val = 0 then (subStrs x).length else x.length
  have hf : ∀ i, ∃ l, S ((sizeRegs r).vars i) = l ++ [f i] := by
    intro i
    by_cases hi : i = 0
    · subst i
      refine ⟨[], ?_⟩
      change S (r.get 19) = [] ++ [(subStrs x).length]
      simpa only [List.nil_append, spans_length] using ready.count
    · have hiv : i.val ≠ 0 := fun he => hi (Fin.ext he)
      refine ⟨[], ?_⟩
      simpa only [sizeRegs, f, if_neg hiv, List.nil_append] using ready.len
  have he := tableSizeExpr_value g x f rfl rfl
  have xa := AddrExpr.compile_runs (sizeRegs r) f (tableSizeExpr g) S hf ready.tmp
  rw [he] at xa
  let X := S.set (r.get 2) (S (r.get 2) ++ [iterBoundV g x])
  have xm := nruns_mv (r.get 2) (r.get 29) (r.ne (by decide)) X
    (l := S (r.get 2)) (v := iterBoundV g x) (by simp [X])
  have hout : (X.set (r.get 29) (X (r.get 29) ++ [iterBoundV g x])).set (r.get 2) (S (r.get 2)) =
      S.set (r.get 29) (S (r.get 29) ++ [iterBoundV g x]) := by
    funext z
    by_cases h2 : z = r.get 2
    · subst z; simp [X, Lists.set]
    by_cases h29 : z = r.get 29
    · subst z; simp [X, Lists.set]
    simp [X, Lists.set, h2, h29]
  rw [hout] at xm
  have hD := length_subStrs_le x
  have hb : ∀ i, f i ≤ varsCap g x.length := by
    intro i
    dsimp [f]
    split <;> unfold varsCap dictCap <;> omega
  have hc := AddrExpr.cost_mono hb (tableSizeExpr g)
  exact (xa.seq xm).mono (by unfold tableCountCost; omega)

def zeroBodyP {K : Nat} (r : EvalRegs K) : NProg K :=
  .seq (.prim (.pushZ (r.get 22))) (.prim (.dec (r.get 30)))

def zeroState {K : Nat} (r : EvalRegs K) (S : Lists K) (m remaining : Nat) : Lists K :=
  (S.set (r.get 22) (S (r.get 22) ++ List.replicate m 0)).set (r.get 30) (S (r.get 30) ++ [remaining])

theorem zeroBody_runs {K : Nat} (r : EvalRegs K) (S : Lists K) (m remaining : Nat) :
    NRuns (zeroBodyP r) (zeroState r S m remaining) (zeroState r S (m + 1) (remaining - 1)) 2 := by
  let X := zeroState r S m remaining
  have xz := nruns_pushZ (r.get 22) X
  let Y := X.set (r.get 22) (X (r.get 22) ++ [0])
  have xd := nruns_dec (r.get 30) Y (l := S (r.get 30)) (v := remaining)
    (by simp [Y, X, zeroState, Lists.set])
  have he : Y.set (r.get 30) (S (r.get 30) ++ [remaining - 1]) = zeroState r S (m + 1) (remaining - 1) := by
    funext z
    by_cases h22 : z = r.get 22
    · subst z; simp [Y, X, zeroState, Lists.set, List.replicate_succ', List.append_assoc]
    by_cases h30 : z = r.get 30
    · subst z; simp [Y, X, zeroState, Lists.set]
    simp [Y, X, zeroState, Lists.set, h22, h30]
  rw [he] at xd
  exact xz.seq xd

def zeroTableP {K : Nat} (r : EvalRegs K) : NProg K :=
  .seq (.prim (.dup (r.get 29) (r.get 30) (r.ne (by decide))))
    (.seq (.loop (r.get 30) .pos (zeroBodyP r)) (.prim (.pop (r.get 30))))

/-- Allocate the actual zero table, counting every push and restoring the allocation counter. -/
theorem zeroTable_runs {K : Nat} (r : EvalRegs K) (S : Lists K) (N : Nat) {lc : List Nat}
    (hN : S (r.get 29) = lc ++ [N]) :
    NRuns (zeroTableP r) S (S.set (r.get 22) (S (r.get 22) ++ List.replicate N 0)) (3 * N + 3) := by
  have xd := nruns_dup (r.get 29) (r.get 30) (r.ne (by decide)) S hN
  let F := fun k => zeroState r S k (N - k)
  have hl := nruns_family_const (i := r.get 30) (c := .pos) (p := zeroBodyP r) F N 2
    (by
      intro k hk
      have he : N - k = (N - 1 - k) + 1 := by omega
      simp [F, zeroState, NTest.eval, he])
    (by simp [F, zeroState, NTest.eval])
    (by
      intro k hk
      have xb := zeroBody_runs r S k (N - k)
      simpa only [F, Nat.sub_sub, Nat.add_comm 1 k] using xb)
  have hfirst : F 0 = S.set (r.get 30) (S (r.get 30) ++ [N]) := by
    simp [F, zeroState, Lists.set_get_self]
  rw [hfirst] at hl
  have xp := nruns_pop (r.get 30) (F N) (l := S (r.get 30)) (v := 0) (by simp [F, zeroState])
  have hend : (F N).set (r.get 30) (S (r.get 30)) = S.set (r.get 22) (S (r.get 22) ++ List.replicate N 0) := by
    funext z
    by_cases h22 : z = r.get 22
    · subst z; simp [F, zeroState, Lists.set]
    by_cases h30 : z = r.get 30
    · subst z; simp [F, zeroState, Lists.set]
    simp [F, zeroState, Lists.set, h22, h30]
  rw [hend] at xp
  exact (xd.seq (hl.seq xp)).mono (by omega)

def tableInitP {K : Nat} (r : EvalRegs K) (g : MGrammar) : NProg K :=
  .seq (tableCountP r g) (zeroTableP r)

def tableInitCost (g : MGrammar) (n : Nat) : Nat := tableCountCost g n + 3 * rowCap g n + 3

/-- The complete initial table and exact iteration count are produced from the loaded length and dictionary. -/
theorem tableInit_runs {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (x : List Char)
    (S : Lists K) (ready : EvalReady r S x [] []) :
    NRuns (tableInitP r g) S
      ((S.set (r.get 22) (pack g x (tblV g x s 0))).set (r.get 29) (S (r.get 29) ++ [iterBoundV g x]))
      (tableInitCost g x.length) := by
  have xc := tableCount_runs r g x [] [] S ready
  let X := S.set (r.get 29) (S (r.get 29) ++ [iterBoundV g x])
  have xz := zeroTable_runs r X (iterBoundV g x) (lc := S (r.get 29)) (by simp [X])
  have hx22 : X (r.get 22) = [] := by simp [X, Lists.set, ready.table]
  rw [hx22, List.nil_append] at xz
  have hz : List.replicate (iterBoundV g x) 0 = pack g x (tblV g x s 0) := by
    simpa only [numericIterate, keys_length] using numericIterate_pack s g x 0
  rw [hz] at xz
  have he : X.set (r.get 22) (pack g x (tblV g x s 0)) =
      (S.set (r.get 22) (pack g x (tblV g x s 0))).set (r.get 29) (S (r.get 29) ++ [iterBoundV g x]) := by
    funext z
    by_cases h22 : z = r.get 22
    · subst z; simp [X, Lists.set]
    by_cases h29 : z = r.get 29
    · subst z; simp [X, Lists.set]
    simp [X, Lists.set, h22, h29]
  rw [he] at xz
  have hN := rowCap_bound g x (tblV g x s 0)
  rw [pack_length] at hN
  exact (xc.seq xz).mono (by unfold tableInitCost; omega)

theorem tableCountCost_poly (g : MGrammar) : IsPoly (tableCountCost g) :=
  isPoly_add (AddrExpr.cost_poly _ (fun _ => varsCap_poly g) _) (isPoly_const 2)

theorem tableInitCost_poly (g : MGrammar) : IsPoly (tableInitCost g) :=
  isPoly_add (isPoly_add (tableCountCost_poly g) (isPoly_mul (isPoly_const 3) (rowCap_poly g))) (isPoly_const 3)

end Shallot.MacroPeg.CBV
