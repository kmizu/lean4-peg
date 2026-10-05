import MacroPeg.HigherOrder.Mach.EvalTables

/-!
# Parser operations on result codes, as plain functions on numbers

The evaluator's operations `seqCodes`, `altCodes`, `notCodes`, `starCodes`, `leafCodes` go through parser values
(`pOf`, `baseVec`, `flatVal`). Here they are written directly on lists of codes (`0` = no result, `1` = failure,
`j + 2` = success leaving `j` symbols), position `q = 0, …, N`.
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO Shallot.MacroPeg.Flat

def seqC (N : Nat) (ca cb : List Nat) : List Nat :=
  (List.range (N + 1)).map (fun q => let c := ca.getD q 0; if 2 ≤ c then cb.getD (c - 2) 0 else c)
def altC (N : Nat) (ca cb : List Nat) : List Nat :=
  (List.range (N + 1)).map (fun q => let c := ca.getD q 0; if c = 1 then cb.getD q 0 else c)
def notC (N : Nat) (ca : List Nat) : List Nat :=
  (List.range (N + 1)).map (fun q => let c := ca.getD q 0; if 2 ≤ c then 1 else if c = 1 then q + 2 else 0)
/-- `a*` at position `q`. -/
def starAt (ca : List Nat) (q : Nat) : Nat :=
  let c := ca.getD q 0
  if 2 ≤ c then (if c - 2 < q then starAt ca (c - 2) else 0) else if c = 1 then q + 2 else 0
termination_by q
decreasing_by omega
def starC (N : Nat) (ca : List Nat) : List Nat := (List.range (N + 1)).map (starAt ca)
def epsC (N : Nat) : List Nat := (List.range (N + 1)).map (· + 2)
def anyC (N : Nat) : List Nat := (List.range (N + 1)).map (fun q => if q = 0 then 1 else q + 1)
/-- One character test at each position; `xs` are the codes of the input. -/
def chrC (xs : List Nat) (p : Nat → Bool) : List Nat :=
  (List.range (xs.length + 1)).map (fun q => if q ≠ 0 ∧ p (xs.getD (xs.length - q) 0) then q + 1 else 1)
def litC (xs s : List Nat) : List Nat :=
  (List.range (xs.length + 1)).map (fun q =>
    if s.length ≤ q ∧ (xs.drop (xs.length - q)).take s.length = s then q - s.length + 2 else 1)

/-! ## Helpers -/

theorem cn_resCode_resOf : ∀ c : Nat, resCode (resOf c) = c
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem cn_atq_pOf (c : List Nat) (q : Nat) : atq (pOf c) q = resOf (c.getD q 0) := by
  simp only [atq, pOf, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases c[q]? <;> rfl

theorem cn_code_atq (c : List Nat) (q : Nat) : resCode (atq (pOf c) q) = c.getD q 0 := by
  rw [cn_atq_pOf, cn_resCode_resOf]

theorem cn_flat_base (x : List Char) (f : Nat → Res) :
    flatVal x.length .p (baseVec x f) = (List.range (x.length + 1)).map (fun q => resCode (f q)) := by
  simp only [flatVal, baseVec, List.map_map, Function.comp_def]

/-! ## Operators -/

theorem seqCodes_eq (x : List Char) (ca cb : List Nat) : seqCodes x ca cb = seqC x.length ca cb := by
  simp only [seqCodes, cn_flat_base, seqC]
  apply List.map_congr_left
  intro q _
  simp only [seqRes, cn_atq_pOf]
  generalize ca.getD q 0 = c
  match c with
  | 0 => rfl
  | 1 => rfl
  | j + 2 =>
    show resCode (resOf (cb.getD j 0)) = _
    rw [cn_resCode_resOf]
    simp

theorem altCodes_eq (x : List Char) (ca cb : List Nat) : altCodes x ca cb = altC x.length ca cb := by
  simp only [altCodes, cn_flat_base, altC]
  apply List.map_congr_left
  intro q _
  simp only [altRes, cn_atq_pOf]
  generalize ca.getD q 0 = c
  match c with
  | 0 => rfl
  | 1 =>
    show resCode (resOf (cb.getD q 0)) = _
    rw [cn_resCode_resOf]
    simp
  | j + 2 => simp only [resOf, resCode]; simp

theorem notCodes_eq (x : List Char) (ca : List Nat) : notCodes x ca = notC x.length ca := by
  simp only [notCodes, cn_flat_base, notC]
  apply List.map_congr_left
  intro q _
  simp only [notRes, cn_atq_pOf]
  generalize ca.getD q 0 = c
  match c with
  | 0 => rfl
  | 1 => rfl
  | j + 2 => simp only [resOf, resCode]; simp

theorem cn_starRes (ca : List Nat) (q : Nat) : resCode (starRes (pOf ca) q) = starAt ca q := by
  induction q using Nat.strongRecOn with
  | _ q ih =>
    rw [starRes, starAt, cn_atq_pOf]
    generalize ca.getD q 0 = c
    match c with
    | 0 => rfl
    | 1 => rfl
    | j + 2 =>
      simp only [resOf, Nat.add_sub_cancel, show 2 ≤ j + 2 by omega, if_true]
      by_cases hj : j < q
      · rw [if_pos hj, if_pos hj, ih j hj]
      · rw [if_neg hj, if_neg hj]
        rfl

theorem starCodes_eq (x : List Char) (ca : List Nat) : starCodes x ca = starC x.length ca := by
  simp only [starCodes, cn_flat_base, starC, cn_starRes]

/-! ## Leaves -/

theorem cn_length_sfx (x : List Char) {q : Nat} (hq : q ≤ x.length) : (HO.sfx x q).length = q := by
  simp only [HO.sfx, List.length_drop]
  omega

theorem cn_sfx_zero (x : List Char) : HO.sfx x 0 = [] := by
  simp [HO.sfx]

/-- The suffix at a positive position, as its first symbol and the rest. -/
theorem cn_sfx_cons (x : List Char) {q : Nat} (hq : q ≤ x.length) (h0 : q ≠ 0) :
    ∃ rest, HO.sfx x q = x.getD (x.length - q) 'a' :: rest ∧ rest.length = q - 1 := by
  have hlen := cn_length_sfx x hq
  cases hs : HO.sfx x q with
  | nil => rw [hs] at hlen; simp at hlen; omega
  | cons d rest =>
    refine ⟨rest, ?_, ?_⟩
    · have hd : (HO.sfx x q)[0]? = some d := by rw [hs]; rfl
      simp only [HO.sfx, List.getElem?_drop, Nat.add_zero] at hd
      rw [List.getD_eq_getElem?_getD, hd]
      rfl
    · rw [hs] at hlen; simp at hlen; omega

theorem leafCodes_eps (x : List Char) : leafCodes x .eps = epsC x.length := by
  simp only [leafCodes, cn_flat_base, epsC]
  apply List.map_congr_left
  intro q hq
  have hq' : q ≤ x.length := Nat.lt_succ_iff.mp (List.mem_range.mp hq)
  simp [leafRes, hrun, resCode, cn_length_sfx x hq']

theorem leafCodes_any (x : List Char) : leafCodes x .any = anyC x.length := by
  simp only [leafCodes, cn_flat_base, anyC]
  apply List.map_congr_left
  intro q hq
  have hq' : q ≤ x.length := Nat.lt_succ_iff.mp (List.mem_range.mp hq)
  by_cases h0 : q = 0
  · subst h0
    simp [leafRes, hrun, cn_sfx_zero, resCode]
  · obtain ⟨rest, hs, hr⟩ := cn_sfx_cons x hq' h0
    simp only [leafRes, hrun, hs, if_neg h0]
    simp [resCode, hr]
    omega

theorem cn_getD_map (x : List Char) (i : Nat) :
    (x.map Char.toNat).getD i 0 = if i < x.length then (x.getD i 'a').toNat else 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < x.length
  · rw [if_pos h, List.getElem?_eq_getElem h]; rfl
  · rw [if_neg h, List.getElem?_eq_none (by omega)]; rfl

/-- A one-character leaf with test `t` on the codes. -/
theorem cn_chr_leaf (x : List Char) (e : HExp) (t : Nat → Bool)
    (he : ∀ d rest, hrun ⟨[]⟩ 1 e (d :: rest) = if t d.toNat then some (some rest) else some none)
    (he0 : hrun ⟨[]⟩ 1 e [] = some none) :
    leafCodes x e = chrC (x.map Char.toNat) t := by
  simp only [leafCodes, cn_flat_base, chrC, List.length_map]
  apply List.map_congr_left
  intro q hq
  have hq' : q ≤ x.length := Nat.lt_succ_iff.mp (List.mem_range.mp hq)
  by_cases h0 : q = 0
  · subst h0
    simp [leafRes, cn_sfx_zero, he0, resCode]
  · obtain ⟨rest, hs, hr⟩ := cn_sfx_cons x hq' h0
    have hg : (x.map Char.toNat).getD (x.length - q) 0 = (x.getD (x.length - q) 'a').toNat := by
      rw [cn_getD_map, if_pos (by omega)]
    simp only [leafRes, hs, he, hg]
    by_cases ht : t (x.getD (x.length - q) 'a').toNat = true
    · rw [if_pos ht, if_pos ⟨h0, ht⟩]
      simp only [Option.map, resCode, hr]
      omega
    · rw [if_neg ht, if_neg (fun h => ht h.2)]
      rfl

theorem leafCodes_chr (x : List Char) (c : Char) :
    leafCodes x (.chr c) = chrC (x.map Char.toNat) (fun d => d == c.toNat) := by
  apply cn_chr_leaf
  · intro d rest
    simp only [hrun, beqChar]
    by_cases h : c.toNat = d.toNat
    · simp [h]
    · have h' : ¬ d.toNat = c.toNat := fun e => h e.symm
      simp [h, h']
  · rfl

theorem cn_le_range (lo hi d : Char) :
    (leChar lo d && leChar d hi) = decide (lo.toNat ≤ d.toNat ∧ d.toNat ≤ hi.toNat) := by
  rw [Bool.eq_iff_iff]
  simp [leChar, Nat.ble_eq]

theorem leafCodes_range (x : List Char) (lo hi : Char) :
    leafCodes x (.range lo hi) = chrC (x.map Char.toNat) (fun d => decide (lo.toNat ≤ d ∧ d ≤ hi.toNat)) := by
  apply cn_chr_leaf
  · intro d rest
    simp only [hrun, cn_le_range]
  · rfl

/-- `stripPrefix?` on characters, through their codes. -/
theorem cn_strip (s y : List Char) :
    stripPrefix? s y = if s.length ≤ y.length ∧ (y.map Char.toNat).take s.length = s.map Char.toNat
      then some (y.drop s.length) else none := by
  induction s generalizing y with
  | nil => simp [stripPrefix?]
  | cons c cs ih =>
    cases y with
    | nil => simp [stripPrefix?]
    | cons d ds =>
      simp only [stripPrefix?, beqChar, ih, List.length_cons, List.map_cons, List.take_succ_cons,
        List.cons.injEq, List.drop_succ_cons]
      by_cases h : c.toNat = d.toNat
      · simp [h]
      · have h' : ¬ d.toNat = c.toNat := fun e => h e.symm
        simp [h, h']

theorem leafCodes_lit (x : List Char) (s : List Char) :
    leafCodes x (.lit s) = litC (x.map Char.toNat) (s.map Char.toNat) := by
  simp only [leafCodes, cn_flat_base, litC, List.length_map]
  apply List.map_congr_left
  intro q hq
  have hq' : q ≤ x.length := Nat.lt_succ_iff.mp (List.mem_range.mp hq)
  have hl := cn_length_sfx x hq'
  have hd : (x.map Char.toNat).drop (x.length - q) = (HO.sfx x q).map Char.toNat := by
    simp [HO.sfx, List.map_drop]
  simp only [leafRes, hrun, cn_strip, hl, hd]
  by_cases h : s.length ≤ q ∧ ((HO.sfx x q).map Char.toNat).take s.length = s.map Char.toNat
  · rw [if_pos h, if_pos h]
    simp [resCode, List.length_drop, hl]
  · rw [if_neg h, if_neg h]
    rfl

end Shallot.MacroPeg.Mach
