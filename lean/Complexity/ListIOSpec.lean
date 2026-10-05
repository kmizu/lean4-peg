import Complexity.ListIO

/-!
# Specifications of `initP`, `finishP`, and the symbol bounds of compiled list programs
-/

namespace Complexity

variable {k : Nat}

private theorem apply_pos (τ : Tapes k) (w : Fin k → Nat) (mv : Fin k → Move) (i : Fin k) :
    (τ.apply w mv).pos i = (mv i).apply (τ.pos i) := rfl

private theorem apply_cells (τ : Tapes k) (w : Fin k → Nat) (mv : Fin k → Move) (i : Fin k) (c : Nat) :
    (τ.apply w mv).cells i c = if c = τ.pos i then w i else τ.cells i c := rfl

private theorem apply_cells_same (τ : Tapes k) (w : Fin k → Nat) (mv : Fin k → Move) (i : Fin k)
    (h : w i = τ.read i) : (τ.apply w mv).cells i = τ.cells i := by
  funext c
  rw [apply_cells]
  split
  · rename_i hc; subst hc; exact h
  · rfl

theorem exec_loop_iter {P : Tapes k → Prop} {c : (Fin k → Nat) → Bool} {p : Prog k}
    (I : Nat → Tapes k → Prop) (N : Nat)
    (hstep : ∀ m τ, I m τ → m < N → P τ ∧ c τ.read = true ∧ ∃ τ', Exec P p τ 1 (.cont τ') ∧ I (m + 1) τ')
    (hend : ∀ τ, I N τ → P τ ∧ c τ.read = false) :
    ∀ d m τ, m + d = N → I m τ → ∃ τ', Exec P (.loop c p) τ (2 * d + 1) (.cont τ') ∧ I N τ' := by
  intro d
  induction d with
  | zero =>
    intro m τ hm hI
    have hm' : m = N := by omega
    subst hm'
    obtain ⟨hP, hc⟩ := hend τ hI
    exact ⟨τ, Exec.loopF hP hc, hI⟩
  | succ d ih =>
    intro m τ hm hI
    obtain ⟨hP, hc, τ₁, hex, hI₁⟩ := hstep m τ hI (by omega)
    obtain ⟨τ₂, hex₂, hI₂⟩ := ih (m + 1) τ₁ (by omega) hI₁
    refine ⟨τ₂, ?_, hI₂⟩
    have := Exec.loopC hP hc hex hex₂
    rwa [show 1 + 1 + (2 * d + 1) = 2 * (d + 1) + 1 by omega] at this

/-! ## `initP` -/

private def symAt (w : List Bool) (c : Nat) : Nat := match w[c]? with | some b => bitSym b | none => 0
private def elemAt (w : List Bool) (c : Nat) : Nat := match w[c - 1]? with | some b => bitElem b + 4 | none => 0

private theorem symAt_ge (w : List Bool) (c : Nat) (h : w.length ≤ c) : symAt w c = 0 := by
  simp [symAt, List.getElem?_eq_none h]

private theorem symAt_lt (w : List Bool) (c : Nat) (h : c < w.length) : symAt w c = bitSym w[c] := by
  simp [symAt, List.getElem?_eq_getElem h]

private theorem bitSym_ne (b : Bool) : bitSym b ≠ 0 := by cases b <;> simp [bitSym]

private theorem elemAt_ne_three (w : List Bool) (c : Nat) : elemAt w c ≠ 3 := by
  unfold elemAt; split <;> omega

private theorem key_elem (w : List Bool) (m : Nat) (hm : m < w.length) :
    (if symAt w m = 2 then 5 else 4) = elemAt w (m + 1) := by
  simp only [symAt_lt w m hm, elemAt, Nat.add_sub_cancel, List.getElem?_eq_getElem hm]
  cases w[m] <;> simp [bitSym, bitElem]

private def ICells (w : List Bool) (m : Nat) (τ : Tapes k) : Prop :=
  (∀ i : Fin k, i.val = 0 → ∀ c, τ.cells i c = if c < m then 0 else symAt w c) ∧
  (∀ i : Fin k, i.val = 1 → ∀ c, τ.cells i c = if c = 0 then 3 else if c ≤ m then elemAt w c else 0) ∧
  (∀ i : Fin k, 2 ≤ i.val → ∀ c, τ.cells i c = if c = 0 then 3 else 0)

private def IB (w : List Bool) (m : Nat) (τ : Tapes k) : Prop :=
  ICells w m τ ∧ (∀ i : Fin k, i.val = 0 → τ.pos i = m) ∧ (∀ i : Fin k, i.val = 1 → τ.pos i = m + 1) ∧
    (∀ i : Fin k, 2 ≤ i.val → τ.pos i = 0)

private def ICpos (w : List Bool) (m : Nat) (τ : Tapes k) : Prop :=
  ICells w w.length τ ∧ (∀ i : Fin k, i.val = 0 → τ.pos i = w.length - m) ∧
    (∀ i : Fin k, i.val = 1 → τ.pos i = w.length + 1 - m) ∧ (∀ i : Fin k, 2 ≤ i.val → τ.pos i = 0)

private theorem tfits_of (w : List Bool) (m : Nat) (τ : Tapes k) (hc : ICells w m τ) (hm : m ≤ w.length)
    (hpos : ∀ i, τ.pos i < w.length + 2) : TFits (w.length + 2) τ := by
  intro i
  refine ⟨hpos i, fun j hj => ?_⟩
  rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ 2 ≤ i.val) with h | h | h
  · rw [hc.1 i h j, if_neg (by omega)]; exact symAt_ge w j (by omega)
  · rw [hc.2.1 i h j, if_neg (by omega), if_neg (by omega)]
  · rw [hc.2.2 i h j, if_neg (by omega)]

private theorem tfits_IB (w : List Bool) (m : Nat) (τ : Tapes k) (hI : IB w m τ) (hm : m ≤ w.length) :
    TFits (w.length + 2) τ := by
  refine tfits_of w m τ hI.1 hm (fun i => ?_)
  rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ 2 ≤ i.val) with h | h | h
  · rw [hI.2.1 i h]; omega
  · rw [hI.2.2.1 i h]; omega
  · rw [hI.2.2.2 i h]; omega

private theorem tfits_ICpos (w : List Bool) (m : Nat) (τ : Tapes k) (hI : ICpos w m τ) :
    TFits (w.length + 2) τ := by
  refine tfits_of w w.length τ hI.1 (Nat.le_refl _) (fun i => ?_)
  rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ 2 ≤ i.val) with h | h | h
  · rw [hI.2.1 i h]; omega
  · rw [hI.2.2.1 i h]; omega
  · rw [hI.2.2.2 i h]; omega

private theorem tfits_init (w : List Bool) : TFits (w.length + 2) (initTapes k w) := by
  intro i
  refine ⟨by show 0 < _; omega, fun j hj => ?_⟩
  show (if i.val = 0 then (match w[j]? with | some b => bitSym b | none => 0) else 0) = 0
  rw [List.getElem?_eq_none (by omega)]
  split <;> rfl

section
variable (h1 : 1 < k)

private theorem initA_w0 (r : Fin k → Nat) (i : Fin k) (hi : i.val = 0) : (initA r).1 i = r i := by
  simp [initA, hi]
private theorem initA_wO (r : Fin k → Nat) (i : Fin k) (hi : i.val ≠ 0) : (initA r).1 i = 3 := by
  simp [initA, hi]
private theorem initA_m1 (r : Fin k → Nat) (i : Fin k) (hi : i.val = 1) : (initA r).2 i = .R := by
  simp [initA, hi]
private theorem initA_mO (r : Fin k → Nat) (i : Fin k) (hi : i.val ≠ 1) : (initA r).2 i = .S := by
  simp [initA, hi]

private theorem initB_w0 (r : Fin k → Nat) (i : Fin k) (hi : i.val = 0) : (initB h1 r).1 i = 0 := by
  simp [initB, hi]
private theorem initB_w1 (r : Fin k → Nat) (i : Fin k) (hi : i.val = 1) :
    (initB h1 r).1 i = if r (t0 h1) = 2 then 5 else 4 := by
  simp [initB, hi]
private theorem initB_wO (r : Fin k → Nat) (i : Fin k) (hi : 2 ≤ i.val) : (initB h1 r).1 i = r i := by
  have a : ¬ i.val = 0 := by omega
  have b : ¬ i.val = 1 := by omega
  simp [initB, a, b]
private theorem initB_m01 (r : Fin k → Nat) (i : Fin k) (hi : i.val = 0 ∨ i.val = 1) :
    (initB h1 r).2 i = .R := by
  simp [initB, hi]
private theorem initB_mO (r : Fin k → Nat) (i : Fin k) (hi : 2 ≤ i.val) : (initB h1 r).2 i = .S := by
  have a : ¬ i.val = 0 := by omega
  have b : ¬ i.val = 1 := by omega
  simp [initB, a, b]

private theorem IB_zero (w : List Bool) :
    IB w 0 ((initTapes k w).apply (initA (initTapes k w).read).1 (initA (initTapes k w).read).2) := by
  have hp : ∀ i, (initTapes k w).pos i = 0 := fun _ => rfl
  have hcl : ∀ (i : Fin k) c, (initTapes k w).cells i c =
      if i.val = 0 then symAt w c else 0 := fun _ _ => rfl
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i hi c
    rw [apply_cells, hp]
    split
    · rename_i hc; subst hc
      rw [initA_w0 _ _ hi]
      show (initTapes k w).cells i 0 = _
      rw [hcl]; simp [hi]
    · rw [hcl]; simp [hi]
  · intro i hi c
    rw [apply_cells, hp]
    split
    · rename_i hc; subst hc
      rw [initA_wO _ _ (show i.val ≠ 0 by omega)]
    · rename_i hc
      simp [hcl, hc, show ¬ i.val = 0 by omega]
  · intro i hi c
    rw [apply_cells, hp]
    split
    · rename_i hc; subst hc
      rw [initA_wO _ _ (show i.val ≠ 0 by omega)]
    · rename_i hc
      simp [hcl, show ¬ i.val = 0 by omega]
  · intro i hi
    rw [apply_pos, initA_mO _ _ (by omega)]; rfl
  · intro i hi
    rw [apply_pos, initA_m1 _ _ hi]; rfl
  · intro i hi
    rw [apply_pos, initA_mO _ _ (by omega)]; rfl

private theorem IB_step (w : List Bool) (m : Nat) (τ : Tapes k) (hm : m < w.length) (hI : IB w m τ) :
    IB w (m + 1) (τ.apply (initB h1 τ.read).1 (initB h1 τ.read).2) := by
  obtain ⟨⟨hc0, hc1, hcO⟩, hp0, hp1, hpO⟩ := hI
  have hr0 : τ.read (t0 h1) = symAt w m := by
    show τ.cells (t0 h1) (τ.pos (t0 h1)) = _
    rw [hp0 _ rfl, hc0 _ rfl, if_neg (by omega)]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i hi c
    rw [apply_cells, hp0 i hi, initB_w0 h1 _ _ hi, hc0 i hi]
    repeat' split
    all_goals first | rfl | (exfalso; omega)
  · intro i hi c
    rw [apply_cells, hp1 i hi, initB_w1 h1 _ _ hi, hc1 i hi, hr0, key_elem w m hm]
    repeat' split
    all_goals first | rfl | (exfalso; omega) | (subst_vars; rfl)
  · intro i hi c
    rw [apply_cells_same τ _ _ i (initB_wO h1 _ _ hi)]
    exact hcO i hi c
  · intro i hi
    rw [apply_pos, initB_m01 h1 _ _ (Or.inl hi), hp0 i hi]; rfl
  · intro i hi
    rw [apply_pos, initB_m01 h1 _ _ (Or.inr hi), hp1 i hi]; rfl
  · intro i hi
    rw [apply_pos, initB_mO h1 _ _ hi, hpO i hi]; rfl


private theorem initC_m01 (r : Fin k → Nat) (i : Fin k) (hi : i.val = 0 ∨ i.val = 1) :
    (initC r).2 i = .L := by simp [initC, hi]
private theorem initC_mO (r : Fin k → Nat) (i : Fin k) (hi : 2 ≤ i.val) : (initC r).2 i = .S := by
  have a : ¬ i.val = 0 := by omega
  have b : ¬ i.val = 1 := by omega
  simp [initC, a, b]

private theorem initD_w0 (r : Fin k → Nat) (i : Fin k) (hi : i.val = 0) : (initD r).1 i = 3 := by
  simp [initD, hi]
private theorem initD_wO (r : Fin k → Nat) (i : Fin k) (hi : i.val ≠ 0) : (initD r).1 i = r i := by
  simp [initD, hi]

private theorem IB_read0 (w : List Bool) (m : Nat) (τ : Tapes k) (hI : IB w m τ) (h1 : 1 < k) :
    τ.read (t0 h1) = symAt w m := by
  show τ.cells (t0 h1) (τ.pos (t0 h1)) = _
  rw [hI.2.1 _ rfl, hI.1.1 _ rfl, if_neg (by omega)]

private theorem loopB_step (w : List Bool) (m : Nat) (τ : Tapes k) (hm : m < w.length) (hI : IB w m τ) :
    TFits (w.length + 2) τ ∧ ((fun r : Fin k → Nat => r (t0 h1) != 0) τ.read) = true ∧
      ∃ τ', Exec (TFits (w.length + 2)) (.act (initB h1)) τ 1 (.cont τ') ∧ IB w (m + 1) τ' := by
  have hI' := IB_step h1 w m τ hm hI
  refine ⟨tfits_IB w m τ hI (by omega), ?_, _, Exec.act (tfits_IB w m τ hI (by omega))
    (tfits_IB w (m + 1) _ hI' (by omega)), hI'⟩
  show (τ.read (t0 h1) != 0) = true
  rw [IB_read0 w m τ hI h1, symAt_lt w m hm]
  exact bne_iff_ne.2 (bitSym_ne _)

private theorem loopB_end (w : List Bool) (τ : Tapes k) (hI : IB w w.length τ) :
    TFits (w.length + 2) τ ∧ ((fun r : Fin k → Nat => r (t0 h1) != 0) τ.read) = false := by
  refine ⟨tfits_IB w _ τ hI (Nat.le_refl _), ?_⟩
  show (τ.read (t0 h1) != 0) = false
  rw [IB_read0 w _ τ hI h1, symAt_ge w _ (Nat.le_refl _)]
  rfl

private theorem ICpos_of_IB (w : List Bool) (τ : Tapes k) (hI : IB w w.length τ) : ICpos w 0 τ := by
  obtain ⟨hc, hp0, hp1, hpO⟩ := hI
  exact ⟨hc, fun i hi => by rw [hp0 i hi]; omega, fun i hi => by rw [hp1 i hi]; omega, hpO⟩

private theorem ICpos_read1 (w : List Bool) (m : Nat) (τ : Tapes k) (hI : ICpos w m τ) (h1 : 1 < k) :
    τ.read (t1 h1) = if w.length + 1 - m = 0 then 3 else
      if w.length + 1 - m ≤ w.length then elemAt w (w.length + 1 - m) else 0 := by
  show τ.cells (t1 h1) (τ.pos (t1 h1)) = _
  rw [hI.2.2.1 _ rfl, hI.1.2.1 _ rfl]

private theorem ICpos_step (w : List Bool) (m : Nat) (τ : Tapes k) (hI : ICpos w m τ) :
    ICpos w (m + 1) (τ.apply (initC τ.read).1 (initC τ.read).2) := by
  have hcells : (τ.apply (initC τ.read).1 (initC τ.read).2).cells = τ.cells := by
    funext i
    exact apply_cells_same τ _ _ i rfl
  obtain ⟨hc, hp0, hp1, hpO⟩ := hI
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold ICells; rw [hcells]; exact hc
  · intro i hi
    rw [apply_pos, initC_m01 _ _ (Or.inl hi)]
    show τ.pos i - 1 = _
    rw [hp0 i hi]; omega
  · intro i hi
    rw [apply_pos, initC_m01 _ _ (Or.inr hi)]
    show τ.pos i - 1 = _
    rw [hp1 i hi]; omega
  · intro i hi
    rw [apply_pos, initC_mO _ _ hi]
    exact hpO i hi

private theorem loopC_step (w : List Bool) (m : Nat) (τ : Tapes k) (hm : m < w.length + 1) (hI : ICpos w m τ) :
    TFits (w.length + 2) τ ∧ ((fun r : Fin k → Nat => r (t1 h1) != 3) τ.read) = true ∧
      ∃ τ', Exec (TFits (w.length + 2)) (.act initC) τ 1 (.cont τ') ∧ ICpos w (m + 1) τ' := by
  have hI' := ICpos_step w m τ hI
  refine ⟨tfits_ICpos w m τ hI, ?_, _, Exec.act (tfits_ICpos w m τ hI) (tfits_ICpos w (m + 1) _ hI'), hI'⟩
  show (τ.read (t1 h1) != 3) = true
  rw [ICpos_read1 w m τ hI h1, if_neg (by omega)]
  apply bne_iff_ne.2
  split
  · exact elemAt_ne_three _ _
  · omega

private theorem loopC_end (w : List Bool) (τ : Tapes k) (hI : ICpos w (w.length + 1) τ) :
    TFits (w.length + 2) τ ∧ ((fun r : Fin k → Nat => r (t1 h1) != 3) τ.read) = false := by
  refine ⟨tfits_ICpos w _ τ hI, ?_⟩
  show (τ.read (t1 h1) != 3) = false
  rw [ICpos_read1 w _ τ hI h1, if_pos (by omega)]
  rfl

private theorem tfits_D (w : List Bool) (τ : Tapes k) (hP : TFits (w.length + 2) τ) :
    TFits (w.length + 2) (τ.apply (initD τ.read).1 (initD τ.read).2) := by
  intro i
  refine ⟨(hP i).1, fun j hj => ?_⟩
  rw [apply_cells, if_neg (by have := (hP i).1; omega)]
  exact (hP i).2 j hj

private theorem rep_D (w : List Bool) (τ : Tapes k) (hI : ICpos w (w.length + 1) τ) :
    Rep (initLists k w) (τ.apply (initD τ.read).1 (initD τ.read).2) := by
  obtain ⟨⟨hc0, hc1, hcO⟩, hp0, hp1, hpO⟩ := hI
  intro i
  have hpos : τ.pos i = 0 := by
    rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ 2 ≤ i.val) with h | h | h
    · rw [hp0 i h]; omega
    · rw [hp1 i h]; omega
    · exact hpO i h
  refine ⟨?_, ?_⟩
  · show τ.pos i = 0
    exact hpos
  rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ 2 ≤ i.val) with h | h | h
  · have hl : initLists k w i = [] := by unfold initLists; rw [if_neg (by omega)]
    rw [hl]
    refine ⟨?_, fun j hj => absurd hj (by simp), fun j hj => ?_⟩
    · rw [apply_cells, hpos, if_pos rfl, initD_w0 _ _ h]
    · rw [apply_cells, hpos, if_neg (by simp at hj; omega), hc0 i h]
      by_cases hh : j < w.length
      · rw [if_pos hh]
      · rw [if_neg hh]; exact symAt_ge w j (by omega)
  · have hl : initLists k w i = w.map bitElem := by unfold initLists; rw [if_pos h]
    rw [hl]
    refine ⟨?_, fun j hj => ?_, fun j hj => ?_⟩
    · rw [apply_cells, hpos, if_pos rfl, initD_wO _ _ (by omega)]
      show τ.cells i (τ.pos i) = 3
      rw [hpos, hc1 i h]; rfl
    · have hj' : j < w.length := by simpa using hj
      rw [apply_cells, hpos, if_neg (by omega), hc1 i h, if_neg (by omega), if_pos (by omega)]
      simp [elemAt, List.getElem?_eq_getElem hj']
    · have hj' : w.length < j := by simpa using hj
      rw [apply_cells, hpos, if_neg (by omega), hc1 i h, if_neg (by omega), if_neg (by omega)]
  · have hl : initLists k w i = [] := by unfold initLists; rw [if_neg (by omega)]
    rw [hl]
    refine ⟨?_, fun j hj => absurd hj (by simp), fun j hj => ?_⟩
    · rw [apply_cells, hpos, if_pos rfl, initD_wO _ _ (by omega)]
      show τ.cells i (τ.pos i) = 3
      rw [hpos, hcO i h]; rfl
    · rw [apply_cells, hpos, if_neg (by simp at hj; omega), hcO i h, if_neg (by simp at hj; omega)]

theorem initP_spec (h1 : 1 < k) (w : List Bool) :
    ∃ t τ, t ≤ 4 * w.length + 8 ∧ Exec (TFits (w.length + 2)) (initP h1) (initTapes k w) t (.cont τ) ∧
      Rep (initLists k w) τ := by
  have hP0 := tfits_init (k := k) w
  have hIA := IB_zero (k := k) w
  have hPA := tfits_IB w 0 _ hIA (by omega)
  obtain ⟨τB, hexB, hIB⟩ := exec_loop_iter (P := TFits (w.length + 2))
    (c := fun r : Fin k → Nat => r (t0 h1) != 0) (p := Prog.act (initB h1)) (IB w) w.length
    (fun m τ hI hm => loopB_step h1 w m τ hm hI) (fun τ hI => loopB_end h1 w τ hI) w.length 0 _ (by omega) hIA
  obtain ⟨τC, hexC, hIC⟩ := exec_loop_iter (P := TFits (w.length + 2))
    (c := fun r : Fin k → Nat => r (t1 h1) != 3) (p := Prog.act initC) (ICpos w) (w.length + 1)
    (fun m τ hI hm => loopC_step h1 w m τ hm hI) (fun τ hI => loopC_end h1 w τ hI) (w.length + 1) 0 τB
    (by omega) (ICpos_of_IB w τB hIB)
  have hPC := tfits_ICpos w _ τC hIC
  refine ⟨1 + ((2 * w.length + 1) + ((2 * (w.length + 1) + 1) + 1)), _, by omega, ?_, rep_D w τC hIC⟩
  exact Exec.seqC (Exec.act hP0 hPA) (Exec.seqC hexB (Exec.seqC hexC (Exec.act hPC (tfits_D w τC hPC))))


theorem initP_symOK (h1 : 1 < k) (na : Nat) (hna : 6 ≤ na) : (initP h1).SymOK na := by
  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · intro r hr i
    by_cases hi : i.val = 0
    · rw [initA_w0 _ _ hi]; exact hr i
    · rw [initA_wO _ _ hi]; omega
  · intro r hr i
    rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ 2 ≤ i.val) with h | h | h
    · rw [initB_w0 h1 _ _ h]; omega
    · rw [initB_w1 h1 _ _ h]; split <;> omega
    · rw [initB_wO h1 _ _ h]; exact hr i
  · intro r hr i; exact hr i
  · intro r hr i
    by_cases hi : i.val = 0
    · rw [initD_w0 _ _ hi]; omega
    · rw [initD_wO _ _ hi]; exact hr i

end

/-! ## `finishP` -/

section
variable (o : Fin k)

private theorem finA_w0 (r : Fin k → Nat) (i : Fin k) (hi : i.val = 0) : (finA o r).1 i = 0 := by
  simp [finA, hi]
private theorem finA_wO (r : Fin k → Nat) (i : Fin k) (hi : i.val ≠ 0) : (finA o r).1 i = r i := by
  simp [finA, hi]
private theorem finA_mo (r : Fin k → Nat) : (finA o r).2 o = .R := by simp [finA]
private theorem finA_mn (r : Fin k → Nat) (i : Fin k) (hi : i ≠ o) : (finA o r).2 i = .S := by
  simp [finA, hi]
private theorem finB_w0 (r : Fin k → Nat) (i : Fin k) (hi : i.val = 0) : (finB o r).1 i = r o - 3 := by
  simp [finB, hi]
private theorem finB_wO (r : Fin k → Nat) (i : Fin k) (hi : i.val ≠ 0) : (finB o r).1 i = r i := by
  simp [finB, hi]
private theorem finB_mR (r : Fin k → Nat) (i : Fin k) (hi : i.val = 0 ∨ i = o) : (finB o r).2 i = .R := by
  simp [finB, hi]
private theorem finB_mS (r : Fin k → Nat) (i : Fin k) (hi : ¬ (i.val = 0 ∨ i = o)) : (finB o r).2 i = .S := by
  simp [finB, hi]

private def outAt (out : List Bool) (c : Nat) : Nat := match out[c]? with | some b => bitSym b | none => 0

private def FI (L : Lists k) (out : List Bool) (m : Nat) (τ : Tapes k) : Prop :=
  (∀ i : Fin k, i.val = 0 → τ.pos i = m) ∧ τ.pos o = m + 1 ∧
  (∀ i : Fin k, i.val ≠ 0 → i ≠ o → τ.pos i = 0) ∧
  (∀ i : Fin k, i.val = 0 → ∀ c, τ.cells i c = if c < m then outAt out c else 0) ∧
  (∀ i : Fin k, i.val ≠ 0 → TapeRep (L i) (τ.cells i))

private theorem tfits_FI {L : Lists k} {B : Nat} (hB : LenOK B L) (out : List Bool) (hout : L o = out.map bitElem)
    (m : Nat) (τ : Tapes k) (hm : m ≤ out.length) (hI : FI o L out m τ) : TFits B τ := by
  have hlen : out.length + 2 ≤ B := by have := hB o; rw [hout] at this; simpa using this
  intro i
  by_cases hi : i.val = 0
  · refine ⟨by rw [hI.1 i hi]; omega, fun j hj => ?_⟩
    rw [hI.2.2.2.1 i hi j, if_neg (by omega)]
  · refine ⟨?_, fun j hj => (hI.2.2.2.2 i hi).2.2 j (by have := hB i; omega)⟩
    by_cases hio : i = o
    · subst hio; rw [hI.2.1]; omega
    · rw [hI.2.2.1 i hi hio]; have := hB i; omega

private theorem tfits_rep {L : Lists k} {B : Nat} (hB : LenOK B L) {τ : Tapes k} (hR : Rep L τ) :
    TFits B τ := by
  intro i
  refine ⟨by rw [(hR i).1]; have := hB i; omega, fun j hj => (hR i).2.2.2 j (by have := hB i; omega)⟩

private theorem FI_zero (h0 : 0 < k) (ho : o.val ≠ 0) {L : Lists k} {τ : Tapes k} (hR : Rep L τ)
    (hL0 : L ⟨0, h0⟩ = []) (out : List Bool) :
    FI o L out 0 (τ.apply (finA o τ.read).1 (finA o τ.read).2) := by
  have hne : ∀ i : Fin k, i.val = 0 → i ≠ o := fun i hi h => ho (h ▸ hi)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [apply_pos, finA_mn o _ _ (hne i hi)]
    exact (hR i).1
  · rw [apply_pos, finA_mo]
    show τ.pos o + 1 = 0 + 1
    rw [(hR o).1]
  · intro i hi hio
    rw [apply_pos, finA_mn o _ _ hio]
    exact (hR i).1
  · intro i hi c
    have hLi : L i = [] := by rw [show i = ⟨0, h0⟩ from Fin.ext hi]; exact hL0
    have hT := (hR i).2
    rw [hLi] at hT
    rw [apply_cells, (hR i).1, if_neg (Nat.not_lt_zero _)]
    split
    · exact finA_w0 o _ _ hi
    · exact hT.2.2 c (by simp; omega)
  · intro i hi
    rw [apply_cells_same τ _ _ i (finA_wO o _ _ hi)]
    exact (hR i).2

private theorem FI_step {L : Lists k} (ho : o.val ≠ 0) (out : List Bool) (hout : L o = out.map bitElem)
    (m : Nat) (τ : Tapes k) (hm : m < out.length) (hI : FI o L out m τ) :
    FI o L out (m + 1) (τ.apply (finB o τ.read).1 (finB o τ.read).2) := by
  have hT : TapeRep (out.map bitElem) (τ.cells o) := by
    have := hI.2.2.2.2 o ho; rw [hout] at this; exact this
  have hr : τ.read o = bitElem out[m] + 4 := by
    show τ.cells o (τ.pos o) = _
    rw [hI.2.1, hT.2.1 m (by simpa using hm)]
    simp
  have key : bitElem out[m] + 4 - 3 = outAt out m := by
    simp only [outAt, List.getElem?_eq_getElem hm]
    cases out[m] <;> simp [bitSym, bitElem]
  have hne : ∀ i : Fin k, i.val = 0 → i ≠ o := fun i hi h => ho (h ▸ hi)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [apply_pos, finB_mR o _ _ (Or.inl hi)]
    show τ.pos i + 1 = m + 1
    rw [hI.1 i hi]
  · rw [apply_pos, finB_mR o _ _ (Or.inr rfl)]
    show τ.pos o + 1 = m + 1 + 1
    rw [hI.2.1]
  · intro i hi hio
    rw [apply_pos, finB_mS o _ _ (by omega)]
    exact hI.2.2.1 i hi hio
  · intro i hi c
    rw [apply_cells, hI.1 i hi, finB_w0 o _ _ hi, hr, hI.2.2.2.1 i hi c]
    repeat' split
    all_goals first | rfl | (exfalso; omega) | (subst_vars; exact key)
  · intro i hi
    rw [apply_cells_same τ _ _ i (finB_wO o _ _ hi)]
    exact hI.2.2.2.2 i hi

private theorem finLoop_step {L : Lists k} {B : Nat} (hB : LenOK B L) (ho : o.val ≠ 0) (out : List Bool)
    (hout : L o = out.map bitElem) (m : Nat) (τ : Tapes k) (hm : m < out.length) (hI : FI o L out m τ) :
    TFits B τ ∧ ((fun r : Fin k → Nat => r o != 0) τ.read) = true ∧
      ∃ τ', Exec (TFits B) (.act (finB o)) τ 1 (.cont τ') ∧ FI o L out (m + 1) τ' := by
  have hI' := FI_step o ho out hout m τ hm hI
  refine ⟨tfits_FI o hB out hout m τ (by omega) hI, ?_, _,
    Exec.act (tfits_FI o hB out hout m τ (by omega) hI) (tfits_FI o hB out hout (m + 1) _ (by omega) hI'), hI'⟩
  have hT : TapeRep (out.map bitElem) (τ.cells o) := by
    have := hI.2.2.2.2 o ho; rw [hout] at this; exact this
  show (τ.cells o (τ.pos o) != 0) = true
  rw [hI.2.1, hT.2.1 m (by simpa using hm)]
  exact bne_iff_ne.2 (by omega)

private theorem finLoop_end {L : Lists k} {B : Nat} (hB : LenOK B L) (ho : o.val ≠ 0) (out : List Bool)
    (hout : L o = out.map bitElem) (τ : Tapes k) (hI : FI o L out out.length τ) :
    TFits B τ ∧ ((fun r : Fin k → Nat => r o != 0) τ.read) = false := by
  refine ⟨tfits_FI o hB out hout _ τ (Nat.le_refl _) hI, ?_⟩
  have hT : TapeRep (out.map bitElem) (τ.cells o) := by
    have := hI.2.2.2.2 o ho; rw [hout] at this; exact this
  show (τ.cells o (τ.pos o) != 0) = false
  rw [hI.2.1, hT.2.2 _ (by simp)]
  rfl

end

theorem finishP_spec (h0 : 0 < k) (o : Fin k) (ho : o.val ≠ 0) {L : Lists k} {τ : Tapes k} {B : Nat}
    (hR : Rep L τ) (hB : LenOK B L) (hL0 : L ⟨0, h0⟩ = []) (out : List Bool) (hout : L o = out.map bitElem) :
    ∃ t τ', t ≤ 2 * out.length + 4 ∧ Exec (TFits B) (finishP o) τ t (.stop true τ') ∧
      OutputIs h0 (toCfg 0 τ') out := by
  have hI0 := FI_zero o h0 ho hR hL0 out
  have hP0 := tfits_rep hB hR
  have hPA := tfits_FI o hB out hout 0 _ (by omega) hI0
  obtain ⟨τL, hexL, hIL⟩ := exec_loop_iter (P := TFits B) (c := fun r : Fin k → Nat => r o != 0)
    (p := Prog.act (finB o)) (FI o L out) out.length
    (fun m τ hI hm => finLoop_step o hB ho out hout m τ hm hI) (fun τ hI => finLoop_end o hB ho out hout τ hI)
    out.length 0 _ (by omega) hI0
  have hPL := tfits_FI o hB out hout _ τL (Nat.le_refl _) hIL
  refine ⟨1 + ((2 * out.length + 1) + 1), τL, by omega, ?_, ?_, ?_⟩
  · exact Exec.seqC (Exec.act hP0 hPA) (Exec.seqC hexL (Exec.halt hPL))
  · intro j hj
    show τL.cells ⟨0, h0⟩ j = _
    rw [hIL.2.2.2.1 ⟨0, h0⟩ rfl j, if_pos hj]
    simp [outAt, List.getElem?_eq_getElem hj]
  · show τL.cells ⟨0, h0⟩ out.length = 0
    rw [hIL.2.2.2.1 ⟨0, h0⟩ rfl, if_neg (Nat.lt_irrefl _)]

theorem finishP_symOK (o : Fin k) (na : Nat) : (finishP o).SymOK na := by
  refine ⟨?_, ⟨?_, trivial⟩⟩
  · intro r hr i
    by_cases hi : i.val = 0
    · rw [finA_w0 o _ _ hi]; have := hr o; omega
    · rw [finA_wO o _ _ hi]; exact hr i
  · intro r hr i
    by_cases hi : i.val = 0
    · rw [finB_w0 o _ _ hi]; have := hr o; omega
    · rw [finB_wO o _ _ hi]; exact hr i

/-! ## Compiled programs stay within the alphabet -/

private theorem mv_symOK (i : Fin k) (m : Move) (na : Nat) : (mv i m).SymOK na := fun _ hr j => hr j

private theorem goEnd_symOK (i : Fin k) (na : Nat) : (goEnd i).SymOK na := mv_symOK i _ na
private theorem goHome_symOK (i : Fin k) (na : Nat) : (goHome i).SymOK na := mv_symOK i _ na
private theorem goLast_symOK (i : Fin k) (na : Nat) : (goLast i).SymOK na :=
  ⟨goEnd_symOK i na, mv_symOK i _ na⟩

theorem compile_symOK (E : Nat) : ∀ p : LProg k, p.ConstOK E → p.compile.SymOK (E + 4)
  | .push i e, h => by
    refine ⟨goEnd_symOK i _, ⟨?_, goHome_symOK i _⟩⟩
    intro r hr j
    show (if j = i then e + 4 else r j) < E + 4
    split
    · exact Nat.add_lt_add_right h 4
    · exact hr j
  | .pop i, _ => by
    refine ⟨goLast_symOK i _, ⟨?_, goHome_symOK i _⟩⟩
    intro r hr j
    show (if j = i ∧ r i ≠ 3 then 0 else r j) < E + 4
    split
    · omega
    · exact hr j
  | .copy i j, _ => by
    refine ⟨goEnd_symOK j _, goLast_symOK i _, ?_, goHome_symOK i _, goHome_symOK j _⟩
    intro r hr x
    show (if x = j ∧ r i ≠ 3 then r i else r x) < E + 4
    split
    · exact hr i
    · exact hr x
  | .seq p q, h => ⟨compile_symOK E p h.1, compile_symOK E q h.2⟩
  | .ite i c p q, h =>
    ⟨goLast_symOK i _, ⟨goHome_symOK i _, compile_symOK E p h.1⟩, ⟨goHome_symOK i _, compile_symOK E q h.2⟩⟩
  | .loop i c p, h =>
    ⟨goLast_symOK i _, ⟨goHome_symOK i _, compile_symOK E p h, goLast_symOK i _⟩, goHome_symOK i _⟩
  | .halt _, _ => trivial

end Complexity
