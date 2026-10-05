import Complexity.TqbfDecodeSpec
import Complexity.TqbfResolveSpec
import Complexity.TqbfFramesSpec
import Complexity.ListClasses

/-!
# TQBF ∈ PSPACE

The decider is a list program over 23 lists: input bits (`1`) → tokens (`2`, `3`, `4`) → quantifier entries (`5`)
and matrix tokens (`6`, `9`) → resolved matrix (`10`, `11`) → kinds (`18`) → frame-based evaluation. Every list stays
within a quadratic bound, so `lm_pspace` gives `PSPACE TQBF`.
-/

namespace Complexity

def lseq {k : Nat} (i : Fin k) : List (LProg k) → LProg k
  | [] => skipP i
  | [p] => p
  | p :: ps => .seq p (lseq i ps)

def deciderLP : LProg 23 :=
  .seq (moveAll 1 2)
  (.seq (tokenizeP 2 3)
  (.seq (moveAll 3 4)
  (.seq (decodeP 4 5 6 7 8)
  (.seq (moveAll 6 9)
  (.seq (resolveP 9 10 13 14 5 15 16 8 17)
  (.seq (moveAll 10 11)
  (.seq (kindsP 5 18)
    (evalQP 18 19 20 21 22 11 12))))))))

/-! ## Length facts -/

theorem length_le_mtList : ∀ m : List RTok, m.length ≤ (mtList m).length
  | [] => Nat.le_refl _
  | a :: m => by
    have := length_le_mtList m
    have : 1 ≤ (RTok.enc a).length := by cases a <;> simp [RTok.enc]
    simp only [mtList, List.flatMap_cons, List.length_append, List.length_cons] at *; omega

theorem length_le_qnList : ∀ qs : List (Bool × Name), qs.length ≤ (qnList qs).length
  | [] => Nat.le_refl _
  | a :: qs => by
    have := length_le_qnList qs
    simp only [qnList, List.flatMap_cons, List.length_append, List.length_cons] at *; omega

theorem toksV_resolve_le (N : List Name) : ∀ m : List RTok,
    (toksV (m.map (resolveTok N))).length ≤ m.length * (N.length + 2)
  | [] => by simp [toksV]
  | a :: m => by
    have ih := toksV_resolve_le N m
    have h1 : (encV (resolveTok N a)).length ≤ N.length + 2 := by
      cases a with
      | var x =>
        simp only [resolveTok]
        cases h : N.findIdx? (· == x) with
        | none => simp [encV]
        | some r =>
          have : r < N.length := by
            have := List.findIdx?_eq_some_iff_getElem.1 h
            obtain ⟨hr, _⟩ := this
            exact hr
          simp [encV]; omega
      | _ => simp [resolveTok, encV]
    simp only [toksV, List.map_cons, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    rw [Nat.succ_mul]; omega

theorem ofBits_length_le : ∀ w : List Bool, (ofBits w).length ≤ w.length
  | b₃ :: b₂ :: b₁ :: b₀ :: bs => by
    have := ofBits_length_le bs
    simp only [ofBits, List.length_cons]; omega
  | [] => by simp [ofBits]
  | [_] => by simp [ofBits]
  | [_, _] => by simp [ofBits]
  | [_, _, _] => by simp [ofBits]

/-- The space bound. -/
def deciderSpace (n : Nat) : Nat := (2 * n + 3) * (2 * n + 3) + 8 * n + 40

theorem deciderSpace_poly : IsPoly deciderSpace := by
  refine ⟨100, 2, fun n => ?_⟩
  simp only [deciderSpace]
  have : (2 * n + 3) * (2 * n + 3) ≤ 9 * ((n + 1) * (n + 1)) := by
    have := Nat.mul_le_mul (show 2 * n + 3 ≤ 3 * (n + 1) by omega) (show 2 * n + 3 ≤ 3 * (n + 1) by omega)
    rw [show 3 * (n + 1) * (3 * (n + 1)) = 9 * ((n + 1) * (n + 1)) by
      rw [Nat.mul_mul_mul_comm]] at this
    exact this
  have h1 : n + 1 ≤ (n + 1) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
  rw [Nat.pow_two]; omega

/-! ## Bounds on states -/

theorem LenOK.set {k B : Nat} {L : Lists k} (h : LenOK B L) (i : Fin k) {l : List Nat} (hl : l.length + 2 ≤ B) :
    LenOK B (L.set i l) := by
  intro x
  by_cases hx : x = i
  · subst hx; simpa using hl
  · rw [Lists.set_ne _ _ hx]; exact h x

theorem LenOK.moving {k B : Nat} {L : Lists k} (h : LenOK B L) {i j : Fin k} (hij : i ≠ j)
    (hb : (L i).length + (L j).length + 2 ≤ B) (n m : Nat) : LenOK B (L.moving i j n m) := by
  unfold Lists.moving
  refine (h.set j ?_).set i ?_
  · simp only [List.length_append, List.length_take, List.length_reverse]; omega
  · simp only [List.length_take]; omega

theorem LenOK.moveAll {k B : Nat} {L : Lists k} (h : LenOK B L) {i j : Fin k}
    (hb : (L i).length + (L j).length + 2 ≤ B) : LenOK B (L.moveAll i j) := by
  unfold Lists.moveAll
  refine (h.set j ?_).set i (by simp; have := h i; omega)
  simp only [List.length_append, List.length_reverse]; omega

theorem runs_moveAll' {k B : Nat} {L : Lists k} {i j : Fin k} (hij : i ≠ j) (h : LenOK B L)
    (hb : (L i).length + (L j).length + 2 ≤ B) :
    Runs (LenOK B) (moveAll i j) L (L.moveAll i j) (((L i).length + 1) * 3) :=
  runs_moveAll hij (fun n m _ _ => h.moving hij hb n m)

theorem lenOK_initLists (w : List Bool) {B : Nat} (hB : w.length + 2 ≤ B) : LenOK B (initLists 23 w) := by
  intro j
  simp only [initLists]
  split
  · simpa using hB
  · simp; omega

/-! ## Correctness -/

theorem decider_correct (w : List Bool) :
    ∃ t b L', LExec (LenOK (deciderSpace w.length)) deciderLP (initLists 23 w) t (.stop b L') ∧
      (b = true ↔ TQBF w) := by
  -- names
  let n := w.length
  let B := deciderSpace n
  let ts := ofBits w
  let φ := decodeToks (ts.length + 1) ts
  let qs := φ.quants
  let m := φ.matrix
  let N := (qs.map Prod.snd).reverse
  let mv := m.map (resolveTok N)
  let kinds := qs.map Prod.fst
  have hts : ts.length ≤ n := ofBits_length_le w
  have hBn : (2 * n + 3) * (2 * n + 3) + 8 * n + 40 ≤ B := Nat.le_refl _
  -- states
  have sne : ∀ (L : Lists 23) (i j : Fin 23) (l : List Nat), j.val ≠ i.val → (L.set i l) j = L j :=
    fun L i j l h => Lists.set_ne _ _ (fun e => h (by rw [e]))
  let L0 := initLists 23 w
  have h0 : LenOK B L0 := lenOK_initLists w (by omega)
  have e01 : L0 1 = w.map bitElem := by simp [L0, initLists]
  have z0 : ∀ j : Fin 23, j.val ≠ 1 → L0 j = [] := fun j hj => by simp [L0, initLists, hj]
  have R1 := runs_moveAll' (i := 1) (j := 2) (by decide) h0 (by rw [e01, z0 2 (by decide)]; simp; omega)
  let L1 := L0.moveAll 1 2
  have h1 : LenOK B L1 := h0.moveAll (by rw [e01, z0 2 (by decide)]; simp; omega)
  have e12 : L1 2 = (w.map bitElem).reverse := by
    simp only [L1, Lists.moveAll]; rw [sne _ _ _ _ (by decide), Lists.set_same, z0 2 (by decide), e01]; simp
  have z1 : ∀ j : Fin 23, j.val ≠ 2 → L1 j = [] := by
    intro j hj
    simp only [L1, Lists.moveAll]
    by_cases h : j.val = 1
    · have : j = 1 := Fin.ext h
      subst this; simp
    · rw [sne _ _ _ _ h, sne _ _ _ _ hj]; exact z0 j h
  obtain ⟨T2, R2⟩ := tokenize_spec (a := 2) (tk := 3) (L := L1) (B := B) (by decide) w
    (by rw [e12]; rfl) (z1 3 (by decide)) h1 (by omega)
  let L2 := (L1.set 2 []).set 3 ts
  have h2 : LenOK B L2 := (h1.set 2 (by simp; omega)).set 3 (by omega)
  have e23 : L2 3 = ts := by simp [L2]
  have z2 : ∀ j : Fin 23, j.val ≠ 3 → L2 j = [] := by
    intro j hj
    simp only [L2]; rw [sne _ _ _ _ hj]
    by_cases h : j.val = 2
    · have : j = 2 := Fin.ext h
      subst this; simp
    · rw [sne _ _ _ _ h]; exact z1 j h
  have R3 := runs_moveAll' (i := 3) (j := 4) (by decide) h2 (by rw [e23, z2 4 (by decide)]; simp; omega)
  let L3 := L2.moveAll 3 4
  have h3 : LenOK B L3 := h2.moveAll (by rw [e23, z2 4 (by decide)]; simp; omega)
  have e34 : L3 4 = ts.reverse := by
    simp only [L3, Lists.moveAll]; rw [sne _ _ _ _ (by decide), Lists.set_same, z2 4 (by decide), e23]; simp
  have e3z : ∀ j : Fin 23, j.val ≠ 4 → L3 j = [] := by
    intro j hj
    simp only [L3, Lists.moveAll]
    by_cases h : j.val = 3
    · have : j = 3 := Fin.ext h
      subst this; simp
    · rw [sne _ _ _ _ h, sne _ _ _ _ hj]; exact z2 j h
  -- bounds on the decoded lists (run once with a small bound)
  have hd0 : [(4 : Fin 23), 5, 6, 7, 8].Nodup := by decide
  obtain ⟨T0, t0, _, hx0⟩ := decodeP_spec hd0 (B := 2 * ts.length + 3) ts (L := L3) e34
    (e3z 5 (by decide)) (e3z 6 (by decide)) (e3z 7 (by decide)) (e3z 8 (by decide))
    (by intro j; by_cases hj : j.val = 4
        · have : j = 4 := Fin.ext hj
          subst this; rw [e34]; simp; omega
        · rw [e3z j hj]; simp) (Nat.le_refl _)
  have hq0 := hx0.q_end _ (Or.inl rfl)
  have hqn : (qnList qs).length + 2 ≤ 2 * ts.length + 3 := by
    have := hq0 5; rw [sne _ _ _ _ (by decide), Lists.set_same] at this; exact this
  have hmt : (mtList m).length + 2 ≤ 2 * ts.length + 3 := by
    have := hq0 6; rw [Lists.set_same] at this; exact this
  have hm : m.length ≤ 2 * n + 1 := by have := length_le_mtList m; omega
  have hq : qs.length ≤ 2 * n + 1 := by have := length_le_qnList qs; omega
  have hN : N.length = qs.length := by simp [N]
  have htv : (toksV mv).length ≤ (2 * n + 1) * (2 * n + 3) := by
    exact Nat.le_trans (toksV_resolve_le N m) (Nat.mul_le_mul hm (by omega))
  have hsq : (2 * n + 1) * (2 * n + 3) ≤ (2 * n + 3) * (2 * n + 3) := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨T4, R4⟩ := decodeP_spec hd0 (B := B) ts (L := L3) e34
    (e3z 5 (by decide)) (e3z 6 (by decide)) (e3z 7 (by decide)) (e3z 8 (by decide)) h3 (by omega)
  let L4 := ((L3.set 4 []).set 5 (qnList qs)).set 6 (mtList m)
  have h4 : LenOK B L4 := ((h3.set 4 (by simp; omega)).set 5 (by omega)).set 6 (by omega)
  have e46 : L4 6 = mtList m := by simp [L4]
  have e49 : L4 9 = [] := by simp [L4, Lists.set]; exact e3z 9 (by decide)
  have R5 := runs_moveAll' (i := 6) (j := 9) (by decide) h4 (by rw [e46, e49]; simp; omega)
  let L5 := L4.moveAll 6 9
  have h5 : LenOK B L5 := h4.moveAll (by rw [e46, e49]; simp; omega)
  have z5 : ∀ j : Fin 23, j.val ≠ 4 → j.val ≠ 5 → j.val ≠ 6 → j.val ≠ 9 → L5 j = [] := by
    intro j h4' h5' h6' h9'
    have a1 : j ≠ 9 := fun e => h9' (by rw [e]; rfl)
    have a2 : j ≠ 6 := fun e => h6' (by rw [e]; rfl)
    have a3 : j ≠ 5 := fun e => h5' (by rw [e]; rfl)
    have a4 : j ≠ 4 := fun e => h4' (by rw [e]; rfl)
    simp only [L5, L4, Lists.moveAll]
    rw [Lists.set_ne _ _ a2, Lists.set_ne _ _ a1, Lists.set_ne _ _ a2, Lists.set_ne _ _ a3, Lists.set_ne _ _ a4]
    exact e3z j h4'
  have hd6 : [(9 : Fin 23), 10, 13, 14, 5, 15, 16, 8, 17].Nodup := by decide
  obtain ⟨T6, R6⟩ := resolveP_spec hd6 (B := B) qs m (L := L5)
    (by simp [L5, Lists.moveAll, Lists.set, e46, e49])
    (z5 10 (by decide) (by decide) (by decide) (by decide)) (z5 13 (by decide) (by decide) (by decide) (by decide))
    (z5 14 (by decide) (by decide) (by decide) (by decide)) (by simp [L5, L4, Lists.moveAll, Lists.set])
    (z5 15 (by decide) (by decide) (by decide) (by decide)) (z5 16 (by decide) (by decide) (by decide) (by decide))
    (z5 8 (by decide) (by decide) (by decide) (by decide)) (z5 17 (by decide) (by decide) (by decide) (by decide))
    h5 (by show (mtList m).length + (toksV mv).length + (qnList qs).length + 4 ≤ B; omega)
  let L6 := (L5.set 9 []).set 10 (toksV mv)
  have h6 : LenOK B L6 := (h5.set 9 (by simp; omega)).set 10 (by omega)
  have e610 : L6 10 = toksV mv := by simp [L6]
  have e611 : L6 11 = [] := by
    simp only [L6]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide)]
    exact z5 11 (by decide) (by decide) (by decide) (by decide)
  have R7 := runs_moveAll' (i := 10) (j := 11) (by decide) h6 (by rw [e610, e611]; simp; omega)
  let L7 := L6.moveAll 10 11
  have h7 : LenOK B L7 := h6.moveAll (by rw [e610, e611]; simp; omega)
  have z7 : ∀ j : Fin 23, j.val ≠ 4 → j.val ≠ 5 → j.val ≠ 6 → j.val ≠ 9 → j.val ≠ 10 → j.val ≠ 11 →
      L7 j = [] := by
    intro j a b c d e f
    have f1 : j ≠ 10 := fun h => e (by rw [h]; rfl)
    have f2 : j ≠ 11 := fun h => f (by rw [h]; rfl)
    have f3 : j ≠ 9 := fun h => d (by rw [h]; rfl)
    simp only [L7, L6, Lists.moveAll]
    rw [Lists.set_ne _ _ f1, Lists.set_ne _ _ f2, Lists.set_ne _ _ f1, Lists.set_ne _ _ f3]
    exact z5 j a b c d
  have e75 : L7 5 = qnList qs := by simp [L7, L6, L5, L4, Lists.moveAll, Lists.set]
  obtain ⟨T8, R8⟩ := kindsP_spec (qn := 5) (ks := 18) (L := L7) (B := B) (by decide) qs e75
    (z7 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) h7 (by omega)
  let L8 := (L7.set 5 []).set 18 (stackL kindElem kinds)
  have h8 : LenOK B L8 := (h7.set 5 (by simp; omega)).set 18 (by simp [stackL, kinds]; omega)
  have z8 : ∀ j : Fin 23, j.val ≠ 4 → j.val ≠ 5 → j.val ≠ 6 → j.val ≠ 9 → j.val ≠ 10 → j.val ≠ 11 →
      j.val ≠ 18 → L8 j = [] := by
    intro j a b c d e f g
    have g1 : j ≠ 18 := fun h => g (by rw [h]; rfl)
    have g2 : j ≠ 5 := fun h => b (by rw [h]; rfl)
    simp only [L8]
    rw [Lists.set_ne _ _ g1, Lists.set_ne _ _ g2]
    exact z7 j a b c d e f
  have hd9 : [(18 : Fin 23), 19, 20, 21, 22, 11, 12].Nodup := by decide
  obtain ⟨L', T9, H9⟩ := evalQP_spec hd9 (B := B) mv kinds (L := L8) (by simp [L8])
    (z8 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (z8 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (z8 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (z8 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by simp [L8, L7, L6, Lists.moveAll, Lists.set, e610, e611])
    (z8 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    h8 (by omega) (by simp [kinds]; omega) (by simp [mv]; omega)
  obtain ⟨t, _, hx⟩ := R1.seqH (R2.seqH (R3.seqH (R4.seqH (R5.seqH (R6.seqH (R7.seqH (R8.seqH H9)))))))
  refine ⟨t, _, L', hx, ?_⟩
  have hv := value_eq_qEvalV φ
  show qEvalV mv kinds [] = true ↔ (Qbf.decode w).value = true
  rw [show Qbf.decode w = φ from rfl, hv]

theorem deciderLP_constOK : deciderLP.ConstOK 24 := by
  simp [deciderLP, LProg.ConstOK, moveAll, moveTop, tokenizeP, readBitsP, bitsTokL, bitsTok, decodeP, decStepP,
    parseNameP, nameStepP, nameStepP.clearAll, skipP, resolveP, resStepP, readNameP, lookupP, searchStepP, cmpStepP,
    cmpStepP.mismatch, skipEntryP, clearP, kindsP, evalQP, roundP, descendP, evalLeafP, tokP, refP, pushBitP, negP,
    conjP, disjP, normalizeP, returnP, combineP, refreshP, answerP, Tok.one, Tok.sep, Tok.fin, Tok.all, Tok.ex,
    Tok.var, Tok.tt, Tok.ff, Tok.neg, Tok.conj, Tok.disj]

theorem tqbf_in_pspace : PSPACE TQBF :=
  lm_pspace (k := 23) (by decide) deciderLP 24 (by decide) deciderLP_constOK TQBF deciderSpace deciderSpace_poly
    (fun w => decider_correct w)

end Complexity
