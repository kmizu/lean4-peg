import Complexity.Univ.Table

/-!
# Tables run like their machines

A finite configuration represents a configuration of `M` (`FRep`) when the states and heads agree and every tape
reads the same cells (blank past its end). One step of the table of `M` keeps the representation
(`fstep_rep`), so the table runs like the machine from the initial configuration (`frun_rep`, `frun_state`).
-/

namespace Complexity

/-- `fc` represents the configuration `c` of `M`. -/
structure FRep {k : Nat} (M : TM k) (c : Cfg k) (fc : FCfg) : Prop where
  state : fc.state = c.state
  qlt : c.state < M.nq
  pos : fc.pos = List.ofFn c.pos
  len : fc.tapes.length = k
  cells : ∀ (i : Fin k) (j : Nat), (fc.tapes.getD i.val []).getD j 0 = c.cells i j
  sym : ∀ (i : Fin k) (j : Nat), c.cells i j < M.na

theorem writeAt_getD (t : List Nat) (p a j : Nat) :
    (writeAt t p a).getD j 0 = if j = p then a else t.getD j 0 := by
  unfold writeAt
  simp only [List.getD_eq_getElem?_getD]
  split
  · rename_i hp
    rw [List.getElem?_set]
    by_cases hj : j = p
    · subst hj; simp [hp]
    · simp [Ne.symm hj, hj]
  · rename_i hp
    rw [List.append_assoc]
    by_cases hl : j < t.length
    · have : j ≠ p := by omega
      rw [List.getElem?_append_left hl]; simp [this]
    · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := t) (by omega)]
      by_cases hr : j - t.length < p - t.length
      · have : j ≠ p := by omega
        rw [List.getElem?_append_left (by simpa using hr)]
        simp [hr, this]
      · rw [List.getElem?_append_right (by simp; omega)]
        simp only [List.length_replicate]
        by_cases hj : j = p
        · subst hj; simp
        · have : j - t.length - (p - t.length) ≠ 0 := by omega
          simp [hj, this]

section Rep

variable {k : Nat} {M : TM k} {c : Cfg k} {fc : FCfg}

theorem FRep.tape_eq (h : FRep M c fc) (i : Fin k) : fc.tapes[i.val]'(by rw [h.len]; exact i.isLt) =
    fc.tapes.getD i.val [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl

/-- The symbols under the heads are the symbols the machine reads. -/
theorem FRep.reads (h : FRep M c fc) : fc.reads = List.ofFn c.read := by
  apply List.ext_getElem
  · simp [FCfg.reads, h.pos, h.len]
  · intro n h₁ h₂
    have hn : n < k := by simpa using h₂
    simp only [FCfg.reads, List.getElem_map, List.getElem_zip, h.pos, List.getElem_ofFn]
    have e : fc.tapes[n]'(by rw [h.len]; exact hn) = fc.tapes.getD n [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [h.len]; exact hn)]; rfl
    rw [e, h.cells ⟨n, hn⟩]; rfl

theorem ofFn_getD {n : Nat} (f : Fin n → Nat) (i : Fin n) : (List.ofFn f).getD i.val 0 = f i := by
  simp [List.getD_eq_getElem?_getD]

/-- One step of the table keeps the representation. -/
theorem fstep_rep (h : FRep M c fc) : FRep M (M.step c) (fstep (tableOf M) fc) := by
  unfold TM.step fstep
  by_cases hh : c.halted
  · have : fc.state = 0 ∨ fc.state = 1 := by rw [h.state]; exact hh
    simp only [hh, this, if_true]; exact h
  · have hn : ¬ (fc.state = 0 ∨ fc.state = 1) := by rw [h.state]; exact hh
    simp only [hh, hn, if_false]
    have hrd := h.reads
    have hsym : ∀ i, c.read i < M.na := fun i => h.sym i _
    have hrow := tableOf_row M (q := c.state) (rs := fc.reads) h.qlt (by rw [hrd]; simp)
      (by rw [hrd]; intro a ha; obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact hsym i)
    rw [h.state, hrow]
    have hr : (fun i : Fin k => fc.reads.getD i.val 0) = c.read := by
      funext i; rw [hrd]; exact ofFn_getD _ i
    simp only [rowOf, hr]
    have hq' := M.delta_state c.state c.read h.qlt hsym
    have hw := M.delta_sym c.state c.read h.qlt hsym
    rcases hd : M.delta c.state c.read with ⟨q', ws, ms⟩
    rw [hd] at hq' hw
    have hlen : ∀ i : Fin k, i.val < fc.tapes.length := fun i => by rw [h.len]; exact i.isLt
    refine ⟨rfl, hq', ?_, by simp [h.len, h.pos], ?_, ?_⟩
    · rw [h.pos]
      apply List.ext_getElem
      · simp
      · intro n h₁ h₂
        simp [List.getElem_zip, Move.ofCode_code]
    · intro i j
      have e : (((fc.tapes.zip fc.pos).zip (List.ofFn ws)).map fun x => writeAt x.1.1 x.1.2 x.2).getD i.val [] =
          writeAt (fc.tapes.getD i.val []) (c.pos i) (ws i) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [h.len, h.pos])]
        simp [List.getElem_zip, h.pos, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen i)]
      simp only at e ⊢
      rw [e, writeAt_getD, h.cells i j]
    · intro i j
      simp only
      split
      · exact hw i
      · exact h.sym i j

theorem frun_rep_of (h : FRep M c fc) : ∀ t, FRep M (M.run c t) (frun (tableOf M) fc t)
  | 0 => h
  | t + 1 => fstep_rep (frun_rep_of h t)

end Rep

/-- The finite initial configuration represents the initial configuration. -/
theorem finit_rep {k : Nat} (M : TM k) (w : List Bool) : FRep M (initCfg k w) (finit k w) where
  state := rfl
  qlt := by have := M.three_le_nq; simp [initCfg]; omega
  pos := by apply List.ext_getElem <;> simp [finit, initCfg]
  len := by simp [finit]
  cells := by
    intro i j
    by_cases hi : i.val = 0
    · have hk : 0 < k := hi ▸ i.isLt
      simp only [finit, initCfg, hi, if_true, List.getD_eq_getElem?_getD]
      rw [List.getElem?_ofFn]
      cases hw : w[j]? <;> simp [hw, hk, List.getElem?_map]
    · simp [finit, initCfg, hi, List.getD_eq_getElem?_getD]
  sym := by
    intro i j
    have := M.three_le_na
    simp only [initCfg]
    split
    · split
      · rename_i b _; cases b <;> simp [bitSym] <;> omega
      · omega
    · omega

/-- **The table of a machine runs like the machine.** -/
theorem frun_rep {k : Nat} (M : TM k) (w : List Bool) (t : Nat) :
    FRep M (M.run (initCfg k w) t) (frun (tableOf M) (finit k w) t) :=
  frun_rep_of (finit_rep M w) t

theorem frun_state {k : Nat} (M : TM k) (w : List Bool) (t : Nat) :
    (frun (tableOf M) (finit k w) t).state = (M.run (initCfg k w) t).state :=
  (frun_rep M w t).state

end Complexity
