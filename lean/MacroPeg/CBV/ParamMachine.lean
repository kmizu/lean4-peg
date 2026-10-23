import MacroPeg.CBV.LiteralMachine
import MacroPeg.CBV.TableRead
import MacroPeg.CBV.SpanCost

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.Mach Shallot.MacroPeg.KExp

/-- Literal matching registers, a saved interval dictionary, and an argument identifier. -/
structure ParamRegs (K : Nat) where
  get : Fin 19 → Fin K
  inj : ∀ i j, get i = get j → i = j

@[simp] theorem ParamRegs.eq {K : Nat} (r : ParamRegs K) (i j : Fin 19) :
    r.get i = r.get j ↔ i = j := ⟨r.inj i j, congrArg r.get⟩

theorem ParamRegs.ne {K : Nat} (r : ParamRegs K) {i j : Fin 19} (h : i ≠ j) : r.get i ≠ r.get j :=
  fun he => h (r.inj i j he)

def ParamRegs.literal {K : Nat} (r : ParamRegs K) : LiteralRegs K where
  get i := r.get ⟨i.val, by have := i.isLt; omega⟩
  inj i j h := by
    have he := r.inj ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩ h
    exact Fin.ext (congrArg (fun k : Fin 19 => k.val) he)

def ParamRegs.address {K : Nat} (r : ParamRegs K) : AddrExpr.Regs K 1 where
  out := r.get 2
  a := r.get 5
  b := r.get 6
  tmp := r.get 1
  vars _ := r.get 18
  ab := r.ne (by decide)
  atmp := r.ne (by decide)
  ao := r.ne (by decide)
  btmp := r.ne (by decide)
  bo := r.ne (by decide)
  to := r.ne (by decide)
  vo _ := r.ne (by decide)

def pairAddress (second : Bool) : AddrExpr 1 :=
  .add (.mul (.num 2) (.var 0)) (.num (if second then 1 else 0))

@[simp] theorem pairAddress_value (f : Fin 1 → Nat) (second : Bool) :
    AddrExpr.value f (pairAddress second) = 2 * f 0 + (if second then 1 else 0) := rfl

def pairReadP {K : Nat} (r : ParamRegs K) (second : Bool) : NProg K :=
  tableReadP r.address (r.get 17) (r.get 7) (r.get (if second then 14 else 13))
    (r.ne (by decide)) (r.ne (by cases second <;> decide)) (r.ne (by decide)) (pairAddress second)

def pairReadCost (m i : Nat) (second : Bool) : Nat :=
  AddrExpr.cost (fun _ : Fin 1 => i) (pairAddress second) + 6 * (2 * m) +
    4 * (2 * i + if second then 1 else 0) + 8

/-- Fetch either endpoint of a saved interval through a calculated address and a real row scan. -/
theorem pairRead_runs {K : Nat} (r : ParamRegs K) (S : Lists K) (P : List (Nat × Nat))
    (i : Nat) (second : Bool) {li : List Nat} (hi : S (r.get 18) = li ++ [i])
    (hrow : S (r.get 17) = encPairs P) (ht : S (r.get 1) = []) (hvalid : i < P.length) :
    NRuns (pairReadP r second) S
      (S.set (r.get (if second then 14 else 13))
        (S (r.get (if second then 14 else 13)) ++ [if second then P[i].2 else P[i].1]))
      (pairReadCost P.length i second) := by
  let f : Fin 1 → Nat := fun _ => i
  have hf : ∀ j, ∃ l, S (r.address.vars j) = l ++ [f j] := fun _ => ⟨li, hi⟩
  have hd : [r.get 17, r.address.tmp, r.get 7, r.address.out,
      r.get (if second then 14 else 13)].Nodup := by
    cases second <;> simp [ParamRegs.address, List.nodup_cons]
  have hv : AddrExpr.value f (pairAddress second) < (encPairs P).length := by
    rw [pairAddress_value, encPairs_length]
    dsimp [f]
    cases second <;> simp <;> omega
  have hx := tableRead_runs r.address (r.get 17) (r.get 7) (r.get (if second then 14 else 13))
    (r.ne (by decide)) (r.ne (by cases second <;> decide)) (r.ne (by decide))
    hd f (pairAddress second) S (encPairs P) hrow hf ht hv
  have he : (encPairs P)[AddrExpr.value f (pairAddress second)] =
      if second then P[i].2 else P[i].1 := by
    have hg := List.getElem?_eq_getElem hv
    cases second with
    | false =>
      have hp := encPairs_fst P i hvalid
      simp only [pairAddress_value, f, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hg ⊢
      rw [hp] at hg
      exact Option.some.inj hg.symm
    | true =>
      have hp := encPairs_snd P i hvalid
      simp only [pairAddress_value, f, ↓reduceIte] at hg ⊢
      rw [hp] at hg
      exact Option.some.inj hg.symm
  rw [he] at hx
  simpa only [pairReadP, pairReadCost, pairAddress_value, encPairs_length, f] using hx

theorem span_endpoints {n i : Nat} (hi : i < (spans n).length) :
    (spans n)[i].2 ≤ (spans n)[i].1 ∧ (spans n)[i].1 ≤ n := by
  have hm := List.getElem_mem hi
  rcases List.mem_flatMap.mp hm with ⟨p, hp, hm⟩
  rcases List.mem_map.mp hm with ⟨j, hj, he⟩
  have hp' := List.mem_range.mp hp
  have hj' := List.mem_range.mp hj
  have he₁ := congrArg Prod.fst he
  have he₂ := congrArg Prod.snd he
  simp only at he₁ he₂
  omega

theorem literalAt_index {x : List Char} {i : Nat} (hi : i < (spans x.length).length) :
    literalAt x i = pre x (spans x.length)[i].1 (spans x.length)[i].2 := by
  unfold literalAt
  rw [← spans_subStrs]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

/-- Resolve an argument identifier, match its literal, and discard the endpoint frames. -/
def paramLiteralP {K : Nat} (r : ParamRegs K) : NProg K :=
  .seq (pairReadP r false) (.seq (pairReadP r true)
    (.seq (spanLiteralP r.literal)
      (.seq (.prim (.pop (r.get 14))) (.prim (.pop (r.get 13))))))

def paramLiteralCost (n : Nat) : Nat :=
  70 * ((n + 1) * (n + 1)) + 100 + spanLiteralCost n

macro "param_states " r:term : tactic => `(tactic| (
  funext z
  by_cases h13 : z = ($r).get 13
  · subst z; simp_all [Lists.set]
  by_cases h14 : z = ($r).get 14
  · subst z; simp_all [Lists.set]
  by_cases h16 : z = ($r).get 16
  · subst z; simp_all [Lists.set]
  simp_all [Lists.set]))

/-- Parameter evaluation, including dictionary access and matching, has no free lookup operation. -/
theorem paramLiteral_runs {K : Nat} (r : ParamRegs K) (S : Lists K) (x : List Char) (i q : Nat)
    {li lq : List Nat} (hi : S (r.get 18) = li ++ [i]) (hq : S (r.get 15) = lq ++ [q])
    (hword : S (r.get 0) = mirrorRow x) (hrow : S (r.get 17) = encPairs (spans x.length))
    (ht : S (r.get 1) = []) (h3 : S (r.get 3) = []) (h4 : S (r.get 4) = [])
    (h11 : S (r.get 11) = []) (h12 : S (r.get 12) = [])
    (h13 : S (r.get 13) = []) (h14 : S (r.get 14) = [])
    (hvalid : i < (spans x.length).length) (hqn : q ≤ x.length) :
    NRuns (paramLiteralP r) S
      (S.set (r.get 16) (S (r.get 16) ++ [literalCode (literalAt x i) (sfx x q)]))
      (paramLiteralCost x.length) := by
  let p := (spans x.length)[i].1
  let j := (spans x.length)[i].2
  have hb := span_endpoints hvalid
  have x₁ := pairRead_runs r S (spans x.length) i false hi hrow ht hvalid
  simp only [Bool.false_eq_true, ↓reduceIte, h13, List.nil_append] at x₁
  let S₁ := S.set (r.get 13) [p]
  have x₂ := pairRead_runs r S₁ (spans x.length) i true
    (li := li) (by simp [S₁, Lists.set, hi]) (by simp [S₁, Lists.set, hrow])
    (by simp [S₁, Lists.set, ht]) hvalid
  simp only [↓reduceIte] at x₂
  have h₁14 : S₁ (r.get 14) = [] := by simp [S₁, Lists.set, h14]
  rw [h₁14, List.nil_append] at x₂
  let S₂ := S₁.set (r.get 14) [j]
  have x₃ := spanLiteral_runs r.literal S₂ x p j q (lp := []) (lj := []) (lq := lq)
    (by change S₂ (r.get 0) = mirrorRow x; simp [S₂, S₁, Lists.set, hword])
    (by change S₂ (r.get 1) = []; simp [S₂, S₁, Lists.set, ht])
    (by change S₂ (r.get 3) = []; simp [S₂, S₁, Lists.set, h3])
    (by change S₂ (r.get 4) = []; simp [S₂, S₁, Lists.set, h4])
    (by change S₂ (r.get 11) = []; simp [S₂, S₁, Lists.set, h11])
    (by change S₂ (r.get 12) = []; simp [S₂, S₁, Lists.set, h12])
    (by change S₂ (r.get 13) = [] ++ [p]; simp [S₂, S₁, Lists.set])
    (by change S₂ (r.get 14) = [] ++ [j]; simp [S₂])
    (by change S₂ (r.get 15) = lq ++ [q]; simp [S₂, S₁, Lists.set, hq])
    hb.2 (Nat.le_trans hb.1 hb.2) hqn
  have he : literalAt x (spanId x.length p j) = literalAt x i :=
    (literalAt_spanId hb.2).trans (literalAt_index hvalid).symm
  rw [he] at x₃
  change NRuns (spanLiteralP r.literal) S₂
    (S₂.set (r.get 16) (S₂ (r.get 16) ++ [literalCode (literalAt x i) (sfx x q)])) _ at x₃
  let v := literalCode (literalAt x i) (sfx x q)
  have h₂16 : S₂ (r.get 16) = S (r.get 16) := by simp [S₂, S₁, Lists.set]
  rw [h₂16] at x₃
  let S₃ := S₂.set (r.get 16) (S (r.get 16) ++ [v])
  have x₄ := nruns_pop (r.get 14) S₃ (l := []) (v := j)
    (by simp [S₃, S₂, Lists.set])
  let S₄ := S₃.set (r.get 14) []
  have x₅ := nruns_pop (r.get 13) S₄ (l := []) (v := p)
    (by simp [S₄, S₃, S₂, S₁, Lists.set])
  have hout : S₄.set (r.get 13) [] = S.set (r.get 16) (S (r.get 16) ++ [v]) := by
    simp only [S₄, S₃, S₂, S₁]
    param_states r
  rw [hout] at x₅
  have hx := x₁.seq (x₂.seq (x₃.seq (x₄.seq x₅)))
  have hm := spans_length_le x.length
  exact hx.mono (by
    simp only [pairReadCost, pairAddress, AddrExpr.cost, AddrExpr.value,
      Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
    unfold paramLiteralCost
    omega)

theorem paramLiteralCost_poly : IsPoly paramLiteralCost :=
  isPoly_add (isPoly_add (isPoly_mul (isPoly_const 70)
    (isPoly_mul (isPoly_add isPoly_id (isPoly_const 1)) (isPoly_add isPoly_id (isPoly_const 1))))
    (isPoly_const 100)) spanLiteralCost_poly

end Shallot.MacroPeg.CBV
