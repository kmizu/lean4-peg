import MacroPeg.HigherOrder.KExp.Encode

/-!
# Writing the encoding takes polynomial time

The list program `encLP c d` moves the input to the template's input list, computes `S = c * (|w| + 1) ^ d` in unary
(the first four phases of the TQBF reduction `redLP`) and runs the template `encT` (`compileT_spec`). So
`w ↦ toBits (encT.denote ⟨w, S, 0, 0⟩)` is polynomial-time computable (`enc_polytime`).
-/

namespace Shallot.MacroPeg.KExp

open Complexity

/-- The environment of the template on input `w`. -/
def encEnv (c d : Nat) (w : List Bool) : TEnv := ⟨w, rS c d w.length, 0, fun _ => 0⟩

/-- The reduction's output: the bits of the encoding. -/
def encBits (c d : Nat) (w : List Bool) : List Bool := toBits (encT.denote (encEnv c d w))

def encLP (c d : Nat) : LProg 23 :=
  .seq (moveAll 1 3)
  (.seq (copyLenP 3 19 7)
  (.seq (.push 19 1)
  (.seq (.push 20 1)
  (.seq (repeatP 7 (powStepP 20 19 21 7 22) d)
  (.seq (repeatP 7 (copyLenP 20 4 7) c)
    (compileT redTT encT))))))

section Bounds

variable (c d : Nat)

def eZ (n : Nat) : Nat := rP d n + rS c d n + n + 16
def eU (n : Nat) : Nat := 5 * encT.size * tunit (eZ c d n) * (eZ c d n + 2) ^ encT.depth
def eSpace (n : Nat) : Nat := eU c d n + eZ c d n + 10
def eTime (n : Nat) : Nat :=
  3 * (n + 1) + 8 * (n + 1) + 2 + (d * rStep d n + 1) + (c * (8 * (rP d n + 1)) + 1) + eU c d n

theorem eZ_poly : IsPoly (eZ c d) := by
  unfold eZ
  exact isPoly_add (isPoly_add (isPoly_add (rP_poly d) (rS_poly c d)) isPoly_id) (isPoly_const _)

theorem eU_poly : IsPoly (eU c d) := by
  unfold eU tunit
  exact isPoly_mul (isPoly_mul (isPoly_const _) (isPoly_mul (isPoly_const 100)
    (isPoly_add (eZ_poly c d) (isPoly_const 3)))) (isPoly_pow (isPoly_add (eZ_poly c d) (isPoly_const 2)) _)

theorem eSpace_poly : IsPoly (eSpace c d) :=
  isPoly_add (isPoly_add (eU_poly c d) (eZ_poly c d)) (isPoly_const 10)

theorem eTime_poly : IsPoly (eTime c d) := by
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
  exact isPoly_add (isPoly_add (isPoly_add (isPoly_add (isPoly_add t1 t2) (isPoly_const 2)) t3) t4) (eU_poly c d)

end Bounds

theorem enc_runs (c d : Nat) (w : List Bool) :
    ∃ t L', t ≤ eTime c d w.length ∧
      LExec (LenOK (eSpace c d w.length)) (encLP c d) (initLists 23 w) t (.cont L') ∧
      L' 0 = [] ∧ L' 2 = (encBits c d w).map bitElem := by
  let n := w.length
  let P := rP d n
  let S := rS c d n
  let Z := eZ c d n
  let B := eSpace c d n
  have hPZ : P ≤ Z := by simp only [Z, eZ, P]; omega
  have hSZ : S ≤ Z := by simp only [Z, eZ, S]; omega
  have hnZ : n ≤ Z := by simp only [Z, eZ, n]; omega
  have hZB : Z + 10 ≤ B := by simp only [B, eSpace, Z]; omega
  have hZU : Z ≤ eU c d n := by
    have h1 : 1 ≤ encT.size := Tmpl.size_pos _
    have h2 := one_le_pow2 Z encT.depth
    simp only [eU, tunit]
    have : Z ≤ 5 * encT.size * (100 * (Z + 3)) := by
      have := Nat.mul_le_mul (show 5 ≤ 5 * encT.size by omega) (show Z ≤ 100 * (Z + 3) by omega)
      omega
    exact Nat.le_trans this (Nat.le_mul_of_pos_right _ h2)
  have hB2 : 2 * Z + 10 ≤ B := by simp only [B, eSpace]; omega
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
    simp only [rStep, rP]
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
  -- phase 5: the template
  let e : TEnv := encEnv c d w
  have hrep : TRep redTT 4 e [] L6 := by
    refine ⟨z6 2 (by decide) (by decide) (by decide) (by decide), ?_, ?_,
      z6 5 (by decide) (by decide) (by decide) (by decide),
      z6 6 (by decide) (by decide) (by decide) (by decide),
      z6 7 (by decide) (by decide) (by decide) (by decide),
      z6 8 (by decide) (by decide) (by decide) (by decide),
      z6 9 (by decide) (by decide) (by decide) (by decide),
      z6 10 (by decide) (by decide) (by decide) (by decide), ?_⟩
    · show L6 3 = _
      simp [L6, g, L5, f, L4, L3, Lists.set, e13, bit01, bitElem, e, encEnv]
      try rfl
    · exact e64
    · intro i hi
      show L6 (redTT.ct i) = _
      simp only [redTT, hi, dite_true, List.replicate_zero, e, encEnv]
      exact z6 _ (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega)
  have hsv : ∀ i, L6 (redTT.sv i) = [] := by
    intro i
    simp only [redTT]
    split
    · exact z6 _ (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega)
    · exact z6 _ (by decide) (by decide) (by decide) (by decide)
  have hout := toBits_denote_le Z encT e (encT_small Z) hSZ (Nat.zero_le _) (fun _ => Nat.zero_le _)
  have hU := ucost_le Z encT
  have R7 := compileT_spec redTT 4 Z B redTT_distinct encT encT_WF (encT_small Z) e [] L6
    hrep (fun i _ => hsv i) hSZ (Nat.zero_le _) hnZ (fun _ _ => Nat.zero_le _) h6
    (by omega) (by
      have hUB : encT.ucost Z ≤ eU c d n := hU
      show 0 + (toBits (encT.denote e)).length + 2 ≤ eU c d n + Z + 10
      omega)
  have R1' := R1.mono (show ((L0 1).length + 1) * 3 ≤ 3 * (n + 1) by rw [e01]; simp [n, Nat.mul_comm])
  have R2' := R2.mono (show 8 * (w.length + 1) ≤ 8 * (n + 1) from Nat.le_refl _)
  have R7' := R7.mono (show encT.ucost Z ≤ eU c d n from hU)
  obtain ⟨t, ht, hx⟩ := R1'.seq (R2'.seq (R3.seq (R4.seq (R5.seq (R6.seq R7')))))
  refine ⟨t, _, ?_, hx, ?_, ?_⟩
  · show t ≤ 3 * (n + 1) + 8 * (n + 1) + 2 + (d * rStep d n + 1) + (c * (8 * (P + 1)) + 1) + eU c d n
    omega
  · rw [sne _ _ _ _ (by decide)]; exact z6 0 (by decide) (by decide) (by decide) (by decide)
  · show (L6.set 2 _) 2 = _
    rw [Lists.set_same, List.nil_append]
    rfl

theorem encLP_constOK (c d : Nat) : (encLP c d).ConstOK 2 := by
  refine ⟨constOK_moveAll _ _, constOK_copyLenP _ _ _ (by decide), by simp [LProg.ConstOK],
    by simp [LProg.ConstOK], constOK_repeatP _ _ ?_ d, constOK_repeatP _ _ (constOK_copyLenP _ _ _ (by decide)) c,
    constOK_compileT redTT _⟩
  simp [powStepP, mulP, LProg.ConstOK, moveTop, moveAll, clearP, constOK_copyLenP]

/-- **The encoding is computable in polynomial time.** -/
theorem enc_polytime (c d : Nat) : PolyTimeComputable (encBits c d) :=
  lm_polytime (k := 23) (by decide) 2 (by decide) (encLP c d) 2 (by decide) (encLP_constOK c d)
    _ (eSpace c d) (eTime c d) (eSpace_poly c d) (eTime_poly c d) (fun w => enc_runs c d w)

end Shallot.MacroPeg.KExp
