import Complexity.TmplLMSpec
import Complexity.RedTmplSpec
import Complexity.RedTmplWF
import Complexity.UnarySpec
import Complexity.TmplBound
import Complexity.TqbfDecider

/-!
# TQBF is PSPACE-hard, and PSPACE-complete

For a machine `M` and a polynomial space bound `c * (n + 1) ^ d`, the list program `redLP` computes, in polynomial
time, the encoding of `redQbf M S w` (`S = c * (|w| + 1) ^ d`): it moves the input to the template's input list,
computes `S` and `T = blockSize M S` in unary, and runs the template `redTmpl M` (`compileT_spec`,
`redTmpl_denote`). With `reduction_correct` this gives `PSPACEHard TQBF`; with `tqbf_in_pspace`,
`PSPACEComplete TQBF`.
-/

namespace Complexity

/-- The tape layout of the reduction (23 lists): `0` unused, `1` input, `2` output, … -/
def redTT : TT 23 where
  out := 2
  inr := 3
  sb := 4
  tb := 5
  bc := 6
  ta := 7
  tb' := 8
  tc := 9
  fl := 10
  ct := fun i => if h : i < 4 then ⟨11 + i, by omega⟩ else 0
  sv := fun i => if h : i < 4 then ⟨15 + i, by omega⟩ else 0

def redLP {k : Nat} (M : TM k) (c d : Nat) : LProg 23 :=
  .seq (moveAll 1 3)
  (.seq (copyLenP 3 19 7)
  (.seq (.push 19 1)
  (.seq (.push 20 1)
  (.seq (repeatP 7 (powStepP 20 19 21 7 22) d)
  (.seq (repeatP 7 (copyLenP 20 4 7) c)
  (.seq (repeatP 7 (.push 5 1) M.nq)
  (.seq (repeatP 7 (copyLenP 4 5 7) (k + k * M.na))
    (compileT redTT (redTmpl M)))))))))

theorem redTT_distinct : redTT.Distinct 4 := by unfold TT.Distinct; decide

theorem sum_replicate_nat (n a : Nat) : (List.replicate n a).sum = n * a := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]; omega

theorem blockSize_eq {k : Nat} (M : TM k) (S : Nat) : blockSize M S = M.nq + (k + k * M.na) * S := by
  simp only [blockSize, blockSuf, sSuf, hSuf, cSuf, List.length_append, List.length_map, List.length_range,
    List.length_flatMap, List.map_const', sum_replicate_nat]
  rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm M.na S, Nat.add_assoc]

section ConstOK
variable {k : Nat} (tt : TT k)

theorem constOK_seqL {E : Nat} : ∀ ps : List (LProg k), (∀ p ∈ ps, p.ConstOK E) → (seqL tt ps).ConstOK E
  | [], _ => by simp [seqL, skipP, LProg.ConstOK]
  | [p], h => by simpa [seqL] using h
  | p :: q :: ps, h => by
    simp only [seqL, LProg.ConstOK]
    exact ⟨h p List.mem_cons_self, constOK_seqL (q :: ps) (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem constOK_emitTok (t : Nat) : (emitTokP tt t).ConstOK 2 :=
  constOK_seqL tt _ (fun p hp => by
    simp only [List.mem_map] at hp
    obtain ⟨b, _, rfl⟩ := hp
    cases b <;> simp [LProg.ConstOK])

theorem constOK_moveAll (i j : Fin k) {E : Nat} : (moveAll i j).ConstOK E := by
  simp [moveAll, moveTop, LProg.ConstOK]

theorem constOK_replicate {E : Nat} (p : LProg k) (hp : p.ConstOK E) (n : Nat) :
    (seqL tt (List.replicate n p)).ConstOK E :=
  constOK_seqL tt _ (fun q hq => by rw [List.eq_of_mem_replicate hq]; exact hp)

theorem constOK_ltP (a b : Fin k) : (ltP tt a b).ConstOK 2 :=
  constOK_seqL tt _ (by simp [LProg.ConstOK, moveTop, moveAll, skipP])

theorem constOK_eqP (a b : Fin k) : (eqP tt a b).ConstOK 2 :=
  constOK_seqL tt _ (by simp [LProg.ConstOK, notFlP, constOK_ltP])

theorem constOK_condP : ∀ c : Cond, (condP tt c).ConstOK 2
  | .tt => by simp [condP, LProg.ConstOK]
  | .lt i j => constOK_ltP tt _ _
  | .eq i j => constOK_eqP tt _ _
  | .eqc i n => by
    have hf : (fillP tt n).ConstOK 2 := constOK_replicate tt (.push tt.bc 1) (by simp [LProg.ConstOK]) n
    exact constOK_seqL tt _ (by simp [LProg.ConstOK, clearP', constOK_eqP, hf])
  | .succ i j => constOK_seqL tt _ (by simp [LProg.ConstOK, constOK_eqP])
  | .inBit i b => constOK_seqL tt _ (by simp [LProg.ConstOK, moveTop, moveAll, skipP])
  | .not c => by simp [condP, LProg.ConstOK, notFlP, constOK_condP c]
  | .and c d => by simp [condP, LProg.ConstOK, skipP, constOK_condP c, constOK_condP d]
  | .or c d => by simp [condP, LProg.ConstOK, skipP, constOK_condP c, constOK_condP d]

theorem constOK_partP : ∀ p : Part, (partP tt p).ConstOK 2
  | .const n => constOK_replicate tt _ (constOK_emitTok tt _) n
  | .ctr i => by simp [partP, emitOnesP, LProg.ConstOK, moveTop, constOK_emitTok, constOK_moveAll]
  | .rev i c => constOK_seqL tt _ (by
      simp [LProg.ConstOK, moveTop, skipP, constOK_emitTok, constOK_moveAll,
        constOK_replicate tt _ (constOK_emitTok tt Tok.one)])

theorem constOK_compileT : ∀ t : Tmpl, (compileT tt t).ConstOK 2
  | .nil => by simp [compileT, skipP, LProg.ConstOK]
  | .tok t => constOK_emitTok tt t
  | .name ps => constOK_seqL tt _ (by
      intro p hp
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hp
      rcases hp with ⟨q, _, rfl⟩ | rfl
      · exact ⟨constOK_partP tt q, constOK_emitTok tt _⟩
      · exact constOK_emitTok tt _)
  | .seq a b => ⟨constOK_compileT a, constOK_compileT b⟩
  | .forR i b body => by
    have hf : ∀ n, (fillP tt n).ConstOK 2 := fun n =>
      constOK_replicate tt _ (by simp [LProg.ConstOK]) n
    simp only [compileT]
    apply constOK_seqL
    cases b <;>
    simp [LProg.ConstOK, constOK_moveAll, constOK_ltP, clearP', skipP, hf, constOK_compileT body,
      constOK_seqL]
  | .ite c a b => ⟨constOK_condP tt c, ⟨trivial, constOK_compileT a⟩, constOK_compileT b⟩

end ConstOK

/-! ## The reduction runs in polynomial time -/

section Run

variable {k : Nat} (M : TM k) (c d : Nat)

def rP (n : Nat) : Nat := (n + 1) ^ d
def rS (n : Nat) : Nat := c * rP d n
def rT (n : Nat) : Nat := M.nq + (k + k * M.na) * rS c d n
def rZ (n : Nat) : Nat := rP d n + rS c d n + rT M c d n + n + M.nq + M.na + k + 16
def rU (n : Nat) : Nat :=
  5 * (redTmpl M).size * tunit (rZ M c d n) * (rZ M c d n + 2) ^ (redTmpl M).depth
def rSpace (n : Nat) : Nat := rU M c d n + rZ M c d n + 10
def rStep (n : Nat) : Nat := 20 * (rP d n + 1) * (n + 3) + 3 * (rP d n * (n + 1) + 1)
def rTime (n : Nat) : Nat :=
  3 * (n + 1) + 8 * (n + 1) + 2 + (d * rStep d n + 1) + (c * (8 * (rP d n + 1)) + 1) + (M.nq * 1 + 1) +
    ((k + k * M.na) * (8 * (rS c d n + 1)) + 1) + rU M c d n

theorem rP_poly : IsPoly (rP d) := isPoly_pow (isPoly_add isPoly_id (isPoly_const 1)) d
theorem rS_poly : IsPoly (rS c d) := isPoly_mul (isPoly_const c) (rP_poly d)
theorem rT_poly : IsPoly (rT M c d) := isPoly_add (isPoly_const _) (isPoly_mul (isPoly_const _) (rS_poly c d))
theorem rZ_poly : IsPoly (rZ M c d) := by
  unfold rZ
  exact isPoly_add (isPoly_add (isPoly_add (isPoly_add (isPoly_add (isPoly_add (isPoly_add (rP_poly d) (rS_poly c d))
    (rT_poly M c d)) isPoly_id) (isPoly_const _)) (isPoly_const _)) (isPoly_const _)) (isPoly_const _)
theorem rU_poly : IsPoly (rU M c d) := by
  unfold rU tunit
  exact isPoly_mul (isPoly_mul (isPoly_const _) (isPoly_mul (isPoly_const 100)
    (isPoly_add (rZ_poly M c d) (isPoly_const 3)))) (isPoly_pow (isPoly_add (rZ_poly M c d) (isPoly_const 2)) _)
theorem rSpace_poly : IsPoly (rSpace M c d) :=
  isPoly_add (isPoly_add (rU_poly M c d) (rZ_poly M c d)) (isPoly_const 10)
theorem rTime_poly : IsPoly (rTime M c d) := by
  have hn1 : IsPoly (fun n => n + 1) := isPoly_add isPoly_id (isPoly_const 1)
  have hstep : IsPoly (rStep d) := by
    unfold rStep
    exact isPoly_add (isPoly_mul (isPoly_mul (isPoly_const 20) (isPoly_add (rP_poly d) (isPoly_const 1)))
      (isPoly_add isPoly_id (isPoly_const 3))) (isPoly_mul (isPoly_const 3)
      (isPoly_add (isPoly_mul (rP_poly d) hn1) (isPoly_const 1)))
  have t1 : IsPoly (fun n => 3 * (n + 1)) := isPoly_mul (isPoly_const 3) hn1
  have t2 : IsPoly (fun n => 8 * (n + 1)) := isPoly_mul (isPoly_const 8) hn1
  have t3 : IsPoly (fun n => d * rStep d n + 1) := isPoly_add (isPoly_mul (isPoly_const d) hstep) (isPoly_const 1)
  have t4 : IsPoly (fun n => c * (8 * (rP d n + 1)) + 1) :=
    isPoly_add (isPoly_mul (isPoly_const c) (isPoly_mul (isPoly_const 8) (isPoly_add (rP_poly d) (isPoly_const 1))))
      (isPoly_const 1)
  have t5 : IsPoly (fun n => (k + k * M.na) * (8 * (rS c d n + 1)) + 1) :=
    isPoly_add (isPoly_mul (isPoly_const _) (isPoly_mul (isPoly_const 8) (isPoly_add (rS_poly c d) (isPoly_const 1))))
      (isPoly_const 1)
  exact isPoly_add (isPoly_add (isPoly_add (isPoly_add (isPoly_add (isPoly_add (isPoly_add t1 t2) (isPoly_const 2))
    t3) t4) (isPoly_const (M.nq * 1 + 1))) t5) (rU_poly M c d)

end Run

/-! ## Running the reduction -/

theorem set_apply23 (L : Lists 23) (i j : Fin 23) (l : List Nat) : (L.set i l) j = if j = i then l else L j := rfl

theorem Tmpl.size_pos : ∀ t : Tmpl, 1 ≤ t.size
  | .nil | .tok _ => Nat.le_refl _
  | .name _ => by simp [Tmpl.size]
  | .seq a _ => by have := Tmpl.size_pos a; simp only [Tmpl.size]; omega
  | .forR _ _ _ => by simp [Tmpl.size]
  | .ite _ _ _ => by simp only [Tmpl.size]; omega

theorem red_runs {k : Nat} (M : TM k) (c d : Nat) (w : List Bool) :
    ∃ t L', t ≤ rTime M c d w.length ∧
      LExec (LenOK (rSpace M c d w.length)) (redLP M c d) (initLists 23 w) t (.cont L') ∧
      L' 0 = [] ∧ L' 2 = ((redQbf M (rS c d w.length) w).encode).map bitElem := by
  let n := w.length
  let P := rP d n
  let S := rS c d n
  let Z := rZ M c d n
  let B := rSpace M c d n
  have hPZ : P ≤ Z := by simp only [Z, rZ, P]; omega
  have hSZ : S ≤ Z := by simp only [Z, rZ, S]; omega
  have hTZ : rT M c d n ≤ Z := by simp only [Z, rZ]; omega
  have hnZ : n ≤ Z := by simp only [Z, rZ, n]; omega
  have hcZ : M.nq + M.na + k + 16 ≤ Z := by simp only [Z, rZ]; omega
  have hZB : Z + 10 ≤ B := by simp only [B, rSpace, Z]; omega
  have hTb : blockSize M S = rT M c d n := by rw [blockSize_eq]; rfl
  have hZU : Z ≤ rU M c d n := by
    have h1 : 1 ≤ (redTmpl M).size := Tmpl.size_pos _
    have h2 := one_le_pow2 Z (redTmpl M).depth
    simp only [rU, tunit]
    have : Z ≤ 5 * (redTmpl M).size * (100 * (Z + 3)) := by
      have := Nat.mul_le_mul (show 5 ≤ 5 * (redTmpl M).size by omega) (show Z ≤ 100 * (Z + 3) by omega)
      omega
    exact Nat.le_trans this (Nat.le_mul_of_pos_right _ h2)
  have hB2 : 2 * Z + 10 ≤ B := by simp only [B, rSpace]; omega
  -- generic facts about `set`
  have sne : ∀ (L : Lists 23) (i j : Fin 23) (l : List Nat), j.val ≠ i.val → (L.set i l) j = L j :=
    fun L i j l h => Lists.set_ne _ _ (fun e => h (by rw [e]))
  -- phase 1: input to `inr`
  let L0 := initLists 23 w
  have h0 : LenOK B L0 := lenOK_initLists w (by omega)
  have e01 : L0 1 = w.map bitElem := by simp [L0, initLists]
  have z0 : ∀ j : Fin 23, j.val ≠ 1 → L0 j = [] := fun j hj => by simp [L0, initLists, hj]
  have R1 := runs_moveAll' (i := 1) (j := 3) (by decide) h0 (by rw [e01, z0 3 (by decide)]; simp; omega)
  let L1 := L0.moveAll 1 3
  have h1 : LenOK B L1 := h0.moveAll (by rw [e01, z0 3 (by decide)]; simp; omega)
  have e13 : L1 3 = (w.map bitElem).reverse := by simp [L1, Lists.moveAll, Lists.set, e01, z0 3 (by decide)]
  have z1 : ∀ j : Fin 23, j.val ≠ 3 → L1 j = [] := by
    intro j hj
    simp only [L1, Lists.moveAll]
    by_cases h : j.val = 1
    · have : j = 1 := Fin.ext h
      subst this; simp
    · rw [sne _ _ _ _ h, sne _ _ _ _ hj]; exact z0 j h
  -- phase 2: `n + 1` on list 19, `1` on list 20
  have z119 := z1 19 (by decide)
  have z120 := z1 20 (by decide)
  have R2 := copyLen_spec (src := 3) (dst := 19) (tmp := 7) (by decide) (z1 7 (by decide)) h1
    (by rw [z119, e13]; simp; omega)
  rw [z119, e13, List.nil_append, List.length_reverse, List.length_map] at R2
  let L2 := L1.set 19 (List.replicate n 1)
  have h2 : LenOK B L2 := h1.set 19 (by simp; omega)
  have e2 : L2.set 19 (L2 19 ++ [1]) = L1.set 19 (List.replicate (n + 1) 1) := by
    simp [L2, Lists.set_set_u, List.replicate_succ']
  have R3 := runs_push (Q := LenOK B) (i := 19) (e := 1) h2 (by rw [e2]; exact h1.set 19 (by simp; omega))
  rw [e2] at R3
  let L3 := L1.set 19 (List.replicate (n + 1) 1)
  have h3 : LenOK B L3 := h1.set 19 (by simp; omega)
  have hl3 : L3 20 = [] := by simp [L3, Lists.set, z120]
  have R4 := runs_push (Q := LenOK B) (i := 20) (e := 1) h3 (by rw [hl3]; exact h3.set 20 (by simp; omega))
  rw [hl3, List.nil_append] at R4
  let L4 := L3.set 20 [1]
  have h4 : LenOK B L4 := h3.set 20 (by simp; omega)
  have z4 : ∀ j : Fin 23, j.val ≠ 3 → j.val ≠ 19 → j.val ≠ 20 → L4 j = [] := by
    intro j a b' c'
    simp only [L4, L3]
    rw [sne _ _ _ _ c', sne _ _ _ _ b']; exact z1 j a
  have e419 : L4 19 = List.replicate (n + 1) 1 := by simp [L4, L3, Lists.set]
  have e420 : L4 20 = [1] := by simp [L4]
  -- phase 3: `P = (n + 1) ^ d` on list 20
  let f : Nat → Lists 23 := fun j => L4.set 20 (List.replicate ((n + 1) ^ j) 1)
  have hf0 : f 0 = L4 := by
    simp only [f, Nat.pow_zero]
    rw [show List.replicate 1 1 = L4 20 by rw [e420]; rfl]; exact Lists.set_get_self _ _
  have hpowj : ∀ j, j ≤ d → (n + 1) ^ j ≤ P := fun j hj => Nat.pow_le_pow_right (by omega) hj
  have hfB : ∀ j, j ≤ d → LenOK B (f j) := fun j hj => h4.set 20 (by simp; have := hpowj j hj; omega)
  have hfz : ∀ j (x : Fin 23), x.val ≠ 20 → f j x = L4 x := fun j x hx => sne _ _ _ _ hx
  have R5 := repeat_spec (Q := LenOK B) (i := 7) (p := powStepP 20 19 21 7 22) f (rStep d n) d (fun j hj => by
    have hx := powStep_spec (pw := 20) (n := 19) (p2 := 21) (ta := 7) (tb := 22) (B := B) (x := (n + 1) ^ j)
      (y := n + 1) (L := f j) (by decide) (by simp [f])
      (by rw [hfz _ _ (by decide)]; exact e419)
      (by rw [hfz _ _ (by decide)]; exact z4 21 (by decide) (by decide) (by decide))
      (by rw [hfz _ _ (by decide)]; exact z4 7 (by decide) (by decide) (by decide))
      (by rw [hfz _ _ (by decide)]; exact z4 22 (by decide) (by decide) (by decide))
      (hfB j (by omega)) (by
        have h1' := hpowj (j + 1) hj
        rw [Nat.pow_succ] at h1'
        have := hpowj j (by omega)
        show (n + 1) ^ j * (n + 1) + (n + 1) ^ j + 2 ≤ B
        omega)
    have e : (f j).set 20 (List.replicate ((n + 1) ^ j * (n + 1)) 1) = f (j + 1) := by
      simp only [f, Lists.set_set_u, Nat.pow_succ]
    rw [e] at hx
    refine hx.mono ?_
    simp only [rStep, P, rP]
    have h1' : (n + 1) ^ j ≤ (n + 1) ^ d := Nat.pow_le_pow_right (by omega) (by omega)
    have h2' := Nat.mul_le_mul_right (n + 1) h1'
    have h3' : 20 * ((n + 1) ^ j + 1) * (n + 1 + 2) ≤ 20 * ((n + 1) ^ d + 1) * (n + 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    omega) (hfB d (Nat.le_refl _))
  rw [hf0] at R5
  let L5 := f d
  have h5 : LenOK B L5 := hfB d (Nat.le_refl _)
  have e520 : L5 20 = List.replicate P 1 := by simp [L5, f, P, rP]
  have z5 : ∀ j : Fin 23, j.val ≠ 3 → j.val ≠ 19 → j.val ≠ 20 → L5 j = [] := fun j a b' c' => by
    rw [show L5 j = f d j from rfl, hfz _ _ c']; exact z4 j a b' c'
  -- phase 4: `S = c * P` on list 4
  let g : Nat → Lists 23 := fun j => L5.set 4 (List.replicate (j * P) 1)
  have hg0 : g 0 = L5 := by
    simp only [g, Nat.zero_mul, List.replicate_zero]
    rw [← z5 4 (by decide) (by decide) (by decide)]; exact Lists.set_get_self _ _
  have hgB : ∀ j, j ≤ c → LenOK B (g j) := fun j hj => h5.set 4 (by
    have hjS : j * P ≤ S := Nat.mul_le_mul_right P hj
    simp only [List.length_replicate]; omega)
  have hgz : ∀ j (x : Fin 23), x.val ≠ 4 → g j x = L5 x := fun j x hx => sne _ _ _ _ hx
  have R6 := repeat_spec (Q := LenOK B) (i := 7) (p := copyLenP 20 4 7) g (8 * (P + 1)) c (fun j hj => by
    have hx := copyLen_spec (src := 20) (dst := 4) (tmp := 7) (B := B) (L := g j) (by decide)
      (by rw [hgz j 7 (by decide)]; exact z5 7 (by decide) (by decide) (by decide))
      (hgB j (by omega)) (by
        rw [hgz j 20 (by decide), e520]; simp only [g, Lists.set_same, List.length_replicate]
        have hjS : (j + 1) * P ≤ S := Nat.mul_le_mul_right P (show j + 1 ≤ c by omega)
        rw [Nat.succ_mul] at hjS; omega)
    have e : (g j).set 4 ((g j) 4 ++ List.replicate ((g j) 20).length 1) = g (j + 1) := by
      rw [hgz j 20 (by decide), e520]
      simp only [g, Lists.set_same, Lists.set_set_u, List.length_replicate, List.replicate_append_replicate, Nat.succ_mul]
    rw [e] at hx
    exact hx.mono (by rw [hgz j 20 (by decide), e520]; simp)) (hgB c (Nat.le_refl _))
  rw [hg0] at R6
  let L6 := g c
  have h6 : LenOK B L6 := hgB c (Nat.le_refl _)
  have e64 : L6 4 = List.replicate S 1 := by
    show (g c) 4 = _; simp only [g, Lists.set_same]; rfl
  have z6 : ∀ j : Fin 23, j.val ≠ 3 → j.val ≠ 4 → j.val ≠ 19 → j.val ≠ 20 → L6 j = [] := fun j a b' c' d' => by
    rw [show L6 j = g c j from rfl, hgz _ _ b']; exact z5 j a c' d'
  -- phase 5: `T` on list 5
  let hh : Nat → Lists 23 := fun j => L6.set 5 (List.replicate j 1)
  have hh0 : hh 0 = L6 := by
    simp only [hh, List.replicate_zero]
    rw [← z6 5 (by decide) (by decide) (by decide) (by decide)]; exact Lists.set_get_self _ _
  have hhB : ∀ j, j ≤ M.nq → LenOK B (hh j) := fun j hj => h6.set 5 (by simp; omega)
  have R7 := repeat_spec (Q := LenOK B) (i := 7) (p := .push 5 1) hh 1 M.nq (fun j hj => by
    have e : (hh j).set 5 ((hh j) 5 ++ [1]) = hh (j + 1) := by
      simp only [hh, Lists.set_same, Lists.set_set_u, List.replicate_succ']
    have hx := runs_push (Q := LenOK B) (i := 5) (e := 1) (hhB j (by omega)) (by rw [e]; exact hhB (j + 1) hj)
    rw [e] at hx; exact hx) (hhB M.nq (Nat.le_refl _))
  rw [hh0] at R7
  let L7 := hh M.nq
  have h7 : LenOK B L7 := hhB M.nq (Nat.le_refl _)
  have e74 : L7 4 = List.replicate S 1 := by
    rw [show L7 4 = hh M.nq 4 from rfl]; simp only [hh]; rw [sne _ _ _ _ (by decide)]; exact e64
  let u : Nat → Lists 23 := fun j => L7.set 5 (List.replicate (M.nq + j * S) 1)
  have hu0 : u 0 = L7 := by simp [u, L7, hh, Lists.set_set_u]
  have huB : ∀ j, j ≤ k + k * M.na → LenOK B (u j) := fun j hj => h7.set 5 (by
    have hjS : j * S ≤ (k + k * M.na) * S := Nat.mul_le_mul_right S hj
    have hT' : M.nq + (k + k * M.na) * S ≤ Z := hTZ
    simp only [List.length_replicate]; omega)
  have huz : ∀ j (x : Fin 23), x.val ≠ 5 → u j x = L7 x := fun j x hx => sne _ _ _ _ hx
  have z7 : ∀ j : Fin 23, j.val ≠ 3 → j.val ≠ 4 → j.val ≠ 5 → j.val ≠ 19 → j.val ≠ 20 → L7 j = [] :=
    fun j a b' c' d' e' => by
      rw [show L7 j = hh M.nq j from rfl]; simp only [hh]; rw [sne _ _ _ _ c']; exact z6 j a b' d' e'
  have R8 := repeat_spec (Q := LenOK B) (i := 7) (p := copyLenP 4 5 7) u (8 * (S + 1)) (k + k * M.na)
    (fun j hj => by
      have hx := copyLen_spec (src := 4) (dst := 5) (tmp := 7) (B := B) (L := u j) (by decide)
        (by rw [huz j 7 (by decide)]; exact z7 7 (by decide) (by decide) (by decide) (by decide) (by decide))
        (huB j (by omega)) (by
          rw [huz j 4 (by decide), e74]; simp only [u, Lists.set_same, List.length_replicate]
          have hjS : (j + 1) * S ≤ (k + k * M.na) * S := Nat.mul_le_mul_right S (show j + 1 ≤ k + k * M.na by omega)
          have hT' : M.nq + (k + k * M.na) * S ≤ Z := hTZ
          rw [Nat.succ_mul] at hjS; omega)
      have e : (u j).set 5 ((u j) 5 ++ List.replicate ((u j) 4).length 1) = u (j + 1) := by
        rw [huz j 4 (by decide), e74]
        simp only [u, Lists.set_same, Lists.set_set_u, List.length_replicate, List.replicate_append_replicate, Nat.succ_mul,
          Nat.add_assoc]
      rw [e] at hx
      exact hx.mono (by rw [huz j 4 (by decide), e74]; simp)) (huB _ (Nat.le_refl _))
  rw [hu0] at R8
  let L8 := u (k + k * M.na)
  have h8 : LenOK B L8 := huB _ (Nat.le_refl _)
  -- phase 6: the template
  let e : TEnv := ⟨w, S, blockSize M S, fun _ => 0⟩
  have zL8 : ∀ j : Fin 23, j.val ≠ 1 → j.val ≠ 3 → j.val ≠ 4 → j.val ≠ 5 → j.val ≠ 19 → j.val ≠ 20 →
      L8 j = [] := by
    intro j _ b' c' d' e' f'
    rw [show L8 j = u (k + k * M.na) j from rfl, huz _ _ d']; exact z7 j b' c' d' e' f'
  have hrep : TRep redTT 4 e [] L8 := by
    refine ⟨zL8 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, ?_,
      zL8 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      zL8 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      zL8 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      zL8 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      zL8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_⟩
    · show L8 3 = _
      rw [show L8 3 = u (k + k * M.na) 3 from rfl, huz _ _ (by decide)]
      simp [L7, hh, L6, g, L5, f, L4, L3, Lists.set, e13, bit01, bitElem]
      try rfl
    · show L8 4 = _
      rw [show L8 4 = u (k + k * M.na) 4 from rfl, huz _ _ (by decide)]; exact e74
    · show L8 5 = _
      simp only [L8, u, Lists.set_same, e, hTb, rT, S]
    · intro i hi
      show L8 (redTT.ct i) = _
      simp only [redTT, hi, dite_true, List.replicate_zero]
      exact zL8 _ (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega)
        (by simp; omega)
  have hsv : ∀ i, L8 (redTT.sv i) = [] := by
    intro i
    simp only [redTT]
    split
    · exact zL8 _ (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega)
        (by simp; omega)
    · exact zL8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hout := toBits_denote_le Z (redTmpl M) e (redTmpl_small M Z hcZ) hSZ (by show blockSize M S ≤ Z; rw [hTb]; exact hTZ)
    (fun _ => Nat.zero_le _)
  have hU := ucost_le Z (redTmpl M)
  have R9 := compileT_spec redTT 4 Z B redTT_distinct (redTmpl M) (redTmpl_WF M) (redTmpl_small M Z hcZ) e [] L8
    hrep (fun i _ => hsv i) hSZ (by show blockSize M S ≤ Z; rw [hTb]; exact hTZ) hnZ (fun _ _ => Nat.zero_le _) h8
    (by omega) (by
      have hUB : (redTmpl M).ucost Z ≤ rU M c d n := hU
      show 0 + (toBits ((redTmpl M).denote e)).length + 2 ≤ rU M c d n + Z + 10
      omega)
  have R1' := R1.mono (show ((L0 1).length + 1) * 3 ≤ 3 * (n + 1) by rw [e01]; simp [n, Nat.mul_comm])
  have R2' := R2.mono (show 8 * (w.length + 1) ≤ 8 * (n + 1) from Nat.le_refl _)
  have R9' := R9.mono (show (redTmpl M).ucost Z ≤ rU M c d n from hU)
  obtain ⟨t, ht, hx⟩ := R1'.seq (R2'.seq (R3.seq (R4.seq (R5.seq (R6.seq (R7.seq (R8.seq R9')))))))
  refine ⟨t, _, ?_, hx, ?_, ?_⟩
  · show t ≤ 3 * (n + 1) + 8 * (n + 1) + 2 + (d * rStep d n + 1) + (c * (8 * (P + 1)) + 1) + (M.nq * 1 + 1) +
      ((k + k * M.na) * (8 * (S + 1)) + 1) + rU M c d n
    omega
  · rw [sne _ _ _ _ (by decide)]; exact zL8 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · show (L8.set 2 _) 2 = _
    rw [Lists.set_same, List.nil_append, redTmpl_denote M S w (fun _ => 0)]
    rfl

theorem constOK_repeatP {k E : Nat} (i : Fin k) (p : LProg k) (hp : p.ConstOK E) :
    ∀ m, (repeatP i p m).ConstOK E
  | 0 => by simp [repeatP, skipP, LProg.ConstOK]
  | m + 1 => ⟨hp, constOK_repeatP i p hp m⟩

theorem constOK_copyLenP {k E : Nat} (a b t : Fin k) (hE : 1 < E) : (copyLenP a b t).ConstOK E := by
  simp [copyLenP, LProg.ConstOK, moveTop, moveAll, hE]

theorem redLP_constOK {k : Nat} (M : TM k) (c d : Nat) : (redLP M c d).ConstOK 2 := by
  refine ⟨constOK_moveAll _ _, constOK_copyLenP _ _ _ (by decide), by simp [LProg.ConstOK],
    by simp [LProg.ConstOK], constOK_repeatP _ _ ?_ d, constOK_repeatP _ _ (constOK_copyLenP _ _ _ (by decide)) c,
    constOK_repeatP _ _ (by simp [LProg.ConstOK]) _, constOK_repeatP _ _ (constOK_copyLenP _ _ _ (by decide)) _,
    constOK_compileT redTT _⟩
  simp [powStepP, mulP, LProg.ConstOK, moveTop, moveAll, clearP, constOK_copyLenP]

theorem red_polytime {k : Nat} (M : TM k) (c d : Nat) :
    PolyTimeComputable (fun w => (redQbf M (rS c d w.length) w).encode) :=
  lm_polytime (k := 23) (by decide) 2 (by decide) (redLP M c d) 2 (by decide) (redLP_constOK M c d)
    _ (rSpace M c d) (rTime M c d) (rSpace_poly M c d) (rTime_poly M c d) (fun w => red_runs M c d w)

theorem tqbf_hard : PSPACEHard TQBF := by
  intro L ⟨k, M, s, ⟨c, d, hs⟩, hdec, hsp⟩
  have hsp' : M.SpaceBounded (fun n => rS c d n) := fun w t i =>
    let h := hsp w t i
    ⟨Nat.lt_of_lt_of_le h.1 (hs _), fun j hj => h.2 j (Nat.le_trans (hs _) hj)⟩
  exact ⟨_, red_polytime M c d, fun w => reduction_correct M hdec hsp' w⟩

/-- **TQBF is PSPACE-complete.** -/
theorem tqbf_pspace_complete : PSPACEComplete TQBF := ⟨tqbf_in_pspace, tqbf_hard⟩

end Complexity
