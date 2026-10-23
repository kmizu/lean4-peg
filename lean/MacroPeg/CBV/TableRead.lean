import MacroPeg.CBV.Arithmetic
import Shallot.Peg.Packrat.Machine.Read

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.Packrat.Machine Shallot.MacroPeg.KExp

/-- Compute a table address, read the saved row, and restore the address stack. -/
def tableReadP {K V : Nat} (r : AddrExpr.Regs K V) (row idx ans : Fin K)
    (hrt : row ≠ r.tmp) (hta : r.tmp ≠ ans) (hpi : r.out ≠ idx) (e : AddrExpr V) : NProg K :=
  .seq (AddrExpr.compile r e)
    (.seq (readRow row r.tmp idx r.out ans hrt hta hpi) (.prim (.pop r.out)))

/-- A complete real table read charges both address calculation and the linear scan of the numeric row. -/
theorem tableRead_runs {K V : Nat} (r : AddrExpr.Regs K V) (row idx ans : Fin K)
    (hrt : row ≠ r.tmp) (hta : r.tmp ≠ ans) (hpi : r.out ≠ idx)
    (hd : [row, r.tmp, idx, r.out, ans].Nodup) (f : Fin V → Nat) (e : AddrExpr V)
    (S : Lists K) (data : List Nat) (hdata : S row = data)
    (hf : ∀ i, ∃ l, S (r.vars i) = l ++ [f i]) (ht : S r.tmp = [])
    (hi : AddrExpr.value f e < data.length) :
    NRuns (tableReadP r row idx ans hrt hta hpi e) S
      (S.set ans (S ans ++ [data[AddrExpr.value f e]]))
      (AddrExpr.cost f e + 6 * data.length + 4 * AddrExpr.value f e + 8) := by
  have hro : row ≠ r.out := by simp_all [List.nodup_cons]
  have hao : ans ≠ r.out := Ne.symm (by simp_all [List.nodup_cons])
  have hx := AddrExpr.compile_runs r f e S hf ht
  let S₁ := S.set r.out (S r.out ++ [AddrExpr.value f e])
  have h₁r : S₁ row = data := by rw [show S₁ row = S row from Lists.set_ne _ _ hro]; exact hdata
  have h₁t : S₁ r.tmp = [] := by simp [S₁, Lists.set_ne _ _ r.to, ht]
  have h₁p : S₁ r.out = S r.out ++ [AddrExpr.value f e] := by simp [S₁]
  have hr := nruns_readRow row r.tmp idx r.out ans hrt hta hpi hd S₁ h₁t h₁p (by rw [h₁r]; exact hi)
  simp only [h₁r] at hr
  have h₁a : S₁ ans = S ans := Lists.set_ne _ _ hao
  rw [h₁a] at hr
  let S₂ := S₁.set ans (S ans ++ [data[AddrExpr.value f e]])
  have h₂p : S₂ r.out = S r.out ++ [AddrExpr.value f e] := by
    rw [show S₂ r.out = S₁ r.out from Lists.set_ne _ _ hao.symm]
    exact h₁p
  have hp := nruns_pop r.out S₂ h₂p
  have he : S₂.set r.out (S r.out) = S.set ans (S ans ++ [data[AddrExpr.value f e]]) := by
    funext k
    by_cases hko : k = r.out
    · subst k; simp [S₂, S₁, Lists.set, hao.symm]
    by_cases hka : k = ans
    · subst k; simp [S₂, S₁, Lists.set, hao]
    simp [S₂, S₁, Lists.set, hko, hka]
  rw [he] at hp
  exact (hx.seq (hr.seq hp)).mono (by omega)

/-- The complete table-read budget remains polynomial when the row and the address inputs do. -/
theorem tableRead_cost_poly {V : Nat} (f : Nat → Fin V → Nat) (e : AddrExpr V) (rows : Nat → Nat)
    (hf : ∀ i, IsPoly (fun n => f n i)) (hr : IsPoly rows) :
    IsPoly (fun n => AddrExpr.cost (f n) e + 6 * rows n + 4 * AddrExpr.value (f n) e + 8) :=
  isPoly_add (isPoly_add (isPoly_add (AddrExpr.cost_poly f hf e) (isPoly_mul (isPoly_const 6) hr))
    (isPoly_mul (isPoly_const 4) (AddrExpr.value_poly f hf e))) (isPoly_const 8)

/-- Instantiate the real program at a CBV rule cell, without a lookup oracle. -/
theorem tableRead_cell {K V : Nat} (r : AddrExpr.Regs K V) (row idx ans : Fin K)
    (hrt : row ≠ r.tmp) (hta : r.tmp ≠ ans) (hpi : r.out ≠ idx)
    (hd : [row, r.tmp, idx, r.out, ans].Nodup) (f : Fin V → Nat)
    (g : MGrammar) (x : List Char) (i p : Nat) (rule : MRule)
    (base positions pos : AddrExpr V) (args : List (AddrExpr V))
    (hb : AddrExpr.value f base = (subStrs x).length)
    (hn : AddrExpr.value f positions = x.length + 1) (hp : AddrExpr.value f pos = p)
    (hRule : ruleAtM g.rules i = some rule)
    (hargs : args.map (AddrExpr.value f) ∈ words (List.range (subStrs x).length) rule.arity)
    (hpos : p ≤ x.length) (T : Nat → List (List Char) → Val) (S : Lists K)
    (hdata : S row = pack g x T) (hf : ∀ j, ∃ l, S (r.vars j) = l ++ [f j]) (ht : S r.tmp = []) :
    let e := AddrExpr.addressExpr g i base positions pos args
    ∃ v, NRuns (tableReadP r row idx ans hrt hta hpi e) S (S.set ans (S ans ++ [v]))
      (AddrExpr.cost f e + 6 * (pack g x T).length + 4 * AddrExpr.value f e + 8) ∧
      resultDecode v = valAt (T i ((args.map (AddrExpr.value f)).map (literalAt x))) p := by
  intro e
  have he : AddrExpr.value f e = address g x i (args.map (AddrExpr.value f)) p :=
    AddrExpr.value_addressExpr f g x i p base positions pos args hb hn hp
  have hi : AddrExpr.value f e < (pack g x T).length := by
    rw [he]
    have h := (List.getElem?_eq_some_iff.mp (keys_get_address hRule hargs hpos)).1
    simpa only [pack, List.length_map] using h
  have hr := tableRead_runs r row idx ans hrt hta hpi hd f e S (pack g x T) hdata hf ht hi
  refine ⟨(pack g x T)[AddrExpr.value f e], hr, ?_⟩
  have hc := pack_get_address (T := T) hRule hargs hpos
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [← he]; exact hi)] at hc
  simpa only [he, Option.getD_some] using hc

end Shallot.MacroPeg.CBV
