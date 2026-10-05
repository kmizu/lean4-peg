import MacroPeg.HigherOrder.Mach.ValueInv
import MacroPeg.HigherOrder.Mach.Inv

/-!
# Sizes in a reading

Along a run of the reading machine on `L` tokens the tokens never grow (`rs_pstep_tk`), so every step adds at most
`L + 2` table entries (`pstep_size`) and at most one item (`rs_pstep_items`). After `4 L + 1` steps:
`finalSt_tsize_le`, `finalSt_items_le`. Every number in a new item is `0`, a character code, a variable number
(below the current context), a rule number (below the rule count), the literal count, or a type number (at most the
type table length, by `MInv`); so all are at most `1114112 + tsize`, which stays below `itemValBound L`
(`finalSt_itemVals`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.Flat

theorem rs_pruns_succ' (s : PSt) (n : Nat) : pruns s (n + 1) = pstep (pruns s n) := by
  rw [pruns_add]; rfl

theorem rs_readExpr_tk (s : PSt) (K : List Nat) : (readExpr s K).tk.length ≤ s.tk.length := by
  unfold readExpr
  split
  next r h => simp [PSt.leaf, h]
  next r h => simp [PSt.leaf, h]
  next r h =>
    split
    next c r₁ h1 => have := parseChar_shorter h1; simp [PSt.leaf, h]; omega
    next => simp [PSt.fail]
  next r h =>
    split
    next c r₁ h1 =>
      split
      next c' r₂ h2 => have := parseChar_shorter h1; have := parseChar_shorter h2; simp [PSt.leaf, h]; omega
      next => simp [PSt.fail]
    next => simp [PSt.fail]
  next r h =>
    split
    next str r₁ h1 => have := parseStr_shorter h1; simp [PSt.leaf, h]; omega
    next => simp [PSt.fail]
  next r h => simp [h]
  next r h => simp [h]
  next r h => simp [h]
  next r h => simp [h]
  next r h =>
    split
    next i r₁ h1 =>
      split
      next => have := parseNat_shorter h1; simp [PSt.leaf, h]; omega
      next => simp [PSt.fail]
    next => simp [PSt.fail]
  next r h =>
    split
    next i r₁ h1 =>
      split
      next => have := parseNat_shorter h1; simp [PSt.leaf, h]; omega
      next => simp [PSt.fail]
    next => simp [PSt.fail]
  next r h => simp [h]
  next r h => simp [h]
  next => simp [PSt.fail]

set_option linter.unusedSimpArgs false in
/-- The tokens never grow. -/
theorem rs_pstep_tk (s : PSt) : (pstep s).tk.length ≤ s.tk.length := by
  unfold pstep readType binDone unDone
  repeat' split
  all_goals first
    | exact rs_readExpr_tk _ _
    | (simp [PSt.fail]; done)
    | (simp_all [PSt.fail]; done)
    | (simp_all [PSt.fail]; omega)

/-- The number of items. -/
def rs_items (s : PSt) : Nat := s.bodies.flatten.length + s.out.length + s.start.length

set_option linter.unusedSimpArgs false in
theorem rs_pstep_items (s : PSt) : rs_items (pstep s) ≤ rs_items s + 1 := by
  unfold pstep readExpr readType binDone unDone
  repeat' split
  all_goals first
    | (simp [rs_items, PSt.fail, PSt.leaf]; done)
    | (simp [rs_items, PSt.fail, PSt.leaf]; omega)

/-! ## Along the run -/

theorem rs_run_tsize (L : Nat) : ∀ (m : Nat) (s : PSt), s.tk.length ≤ L →
    tsize (pruns s m) ≤ tsize s + m * (L + 2)
  | 0, s, _ => by simp [pruns]
  | m + 1, s, h => by
    rw [pruns_succ]
    have h1 := pstep_size s
    have h2 := rs_run_tsize L m (pstep s) (Nat.le_trans (rs_pstep_tk s) h)
    rw [Nat.succ_mul]; omega

theorem rs_run_items : ∀ (m : Nat) (s : PSt), rs_items (pruns s m) ≤ rs_items s + m
  | 0, s => by simp [pruns]
  | m + 1, s => by
    rw [pruns_succ]
    have h1 := rs_pstep_items s
    have h2 := rs_run_items m (pstep s)
    omega

theorem finalSt_tsize_le (tk : List Nat) : tsize (finalSt tk) ≤ (4 * tk.length + 1) * (tk.length + 2) := by
  have := rs_run_tsize tk.length (4 * tk.length + 1) (pinit tk) (by simp [pinit])
  have h0 : tsize (pinit tk) = 0 := by simp [tsize, pinit]
  unfold finalSt; omega

theorem finalSt_items_le (tk : List Nat) :
    (finalSt tk).bodies.flatten.length + (finalSt tk).out.length + (finalSt tk).start.length ≤ 4 * tk.length + 1 := by
  have := rs_run_items (4 * tk.length + 1) (pinit tk)
  have h0 : rs_items (pinit tk) = 0 := by simp [rs_items, pinit]
  unfold finalSt; unfold rs_items at this h0; omega

/-! ## The numbers in the items -/

/-- All numbers in the items of the current body, the bodies and the start are at most `B`. -/
def rs_ok (B : Nat) (o : List MItem) (bs : List (List MItem)) (st : List MItem) : Prop :=
  (∀ it ∈ o, it.a ≤ B ∧ it.b ≤ B) ∧ (∀ it ∈ bs.flatten, it.a ≤ B ∧ it.b ≤ B) ∧ (∀ it ∈ st, it.a ≤ B ∧ it.b ≤ B)

theorem rs_ok_cons {B : Nat} {o st : List MItem} {bs : List (List MItem)} (h : rs_ok B o bs st) {it : MItem}
    (ha : it.a ≤ B) (hb : it.b ≤ B) : rs_ok B (it :: o) bs st := by
  refine ⟨fun x hx => ?_, h.2.1, h.2.2⟩
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ⟨ha, hb⟩
  · exact h.1 x hx

theorem rs_ok_body {B : Nat} {o st : List MItem} {bs : List (List MItem)} (h : rs_ok B o bs st) :
    rs_ok B [] (bs ++ [o.reverse]) st := by
  refine ⟨by simp, fun x hx => ?_, h.2.2⟩
  simp only [List.flatten_append, List.flatten_singleton, List.mem_append, List.mem_reverse] at hx
  rcases hx with hx | hx
  · exact h.2.1 x hx
  · exact h.1 x hx

theorem rs_ok_start {B : Nat} {o st : List MItem} {bs : List (List MItem)} (h : rs_ok B o bs st) :
    rs_ok B [] bs o.reverse :=
  ⟨by simp, h.2.1, fun x hx => h.1 x (List.mem_reverse.1 hx)⟩

theorem rs_varTy_lt {ct : List (Nat × Nat)} (c i : Nat) {τ : Nat} (h : varTy ct c i = some τ) : i < c := by
  fun_induction varTy ct c i with
  | case1 => simp at h
  | case2 => omega
  | case3 c i par _ _ hp ih => have := ih h; omega
  | case4 => simp at h
  | case5 => simp at h

theorem rs_char_le {B t : Nat} (hB : 1114112 + t ≤ B) (c : Char) : c.toNat ≤ B := by
  have := toNat_lt c; omega

theorem rs_readExpr_ok {B : Nat} {s : PSt} {K : List Nat} (h : MInv s) (hB : 1114112 + tsize s ≤ B)
    (hok : rs_ok B s.out s.bodies s.start) :
    rs_ok B (readExpr s K).out (readExpr s K).bodies (readExpr s K).start := by
  have hlt : s.lt.length ≤ B := by unfold tsize at hB; omega
  have hct : s.ct.length ≤ B := by unfold tsize at hB; omega
  have hrt : s.rt.length ≤ B := by unfold tsize at hB; omega
  have hcur := h.cur
  unfold readExpr
  repeat' split
  all_goals first
    | exact hok
    | (dsimp only [PSt.leaf]; apply rs_ok_cons hok <;> dsimp only <;> first
        | exact Nat.zero_le _
        | exact rs_char_le hB _
        | exact hlt
        | (have := rs_varTy_lt _ _ ‹varTy _ _ _ = some _›; omega)
        | (have := (List.getElem?_eq_some_iff.1 ‹s.rt[_]? = some _›).1; omega))

theorem rs_tt_snd {tt : List (Nat × Nat)} (hw : TTWF tt) {k x β : Nat} (hk : tt[k]? = some (x, β)) :
    β ≤ tt.length := by
  have hlt : k < tt.length := (List.getElem?_eq_some_iff.1 hk).1
  have := (hw.2 k hlt).2
  rw [show tt[k] = (x, β) from (List.getElem?_eq_some_iff.1 hk).2] at this
  simp at this; omega

theorem rs_ty_mem {s : PSt} (h : MInv s) {x : Nat} {l : List Nat} (hty : s.ty = l) (hx : x ∈ l) : x ≤ s.tt.length :=
  h.ty x (hty ▸ hx)

theorem rs_pstep_ok {B : Nat} {s : PSt} (h : MInv s) (hB : 1114112 + tsize s ≤ B)
    (hok : rs_ok B s.out s.bodies s.start) :
    rs_ok B (pstep s).out (pstep s).bodies (pstep s).start := by
  have htt : s.tt.length ≤ B := by unfold tsize at hB; omega
  unfold pstep binDone unDone
  repeat' split
  all_goals first
    | exact hok
    | exact rs_readExpr_ok h hB hok
    | exact rs_ok_body hok
    | exact rs_ok_start hok
    | ((unfold readType; repeat' split) <;> exact hok)
    | (apply rs_ok_cons hok <;> (try dsimp only) <;> first
        | exact Nat.zero_le _
        | exact Nat.le_trans (rs_ty_mem h ‹s.ty = _› List.mem_cons_self) htt
        | exact Nat.le_trans (rs_tt_snd h.tt ‹s.tt[_]? = some _›) htt
        | (have hk := h.ctl; rw [‹s.ctl = 9 :: _›] at hk; simp only [ctlOK] at hk; exact Nat.le_trans hk.1 htt))

/-- A bound on the numbers in the items of a reading of `L` tokens. -/
def itemValBound (L : Nat) : Nat := 1114112 + 100 * (L + 1) * (L + 1) * (L + 1)

theorem rs_poly (L : Nat) : (4 * L + 1) * (L + 2) ≤ 100 * (L + 1) * (L + 1) * (L + 1) := by
  have h1 : (4 * L + 1) * (L + 2) ≤ 100 * (L + 1) * (L + 1) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_assoc]
    omega
  exact Nat.le_trans h1 (Nat.le_mul_of_pos_right _ (by omega))

/-- The tables stay below the final bound all along the run. -/
theorem rs_tsize_all (tk : List Nat) (m : Nat) :
    tsize (pruns (pinit tk) m) ≤ (4 * tk.length + 1) * (tk.length + 2) := by
  by_cases hm : m ≤ 4 * tk.length + 1
  · have h := rs_run_tsize tk.length m (pinit tk) (by simp [pinit])
    have h0 : tsize (pinit tk) = 0 := by simp [tsize, pinit]
    rw [h0, Nat.zero_add] at h
    exact Nat.le_trans h (Nat.mul_le_mul_right _ hm)
  · rw [pruns_after (pinit_stops tk) m (by omega)]
    exact finalSt_tsize_le tk

theorem rs_ok_all (tk : List Nat) : ∀ m, rs_ok (itemValBound tk.length) (pruns (pinit tk) m).out
    (pruns (pinit tk) m).bodies (pruns (pinit tk) m).start
  | 0 => ⟨by simp [pruns, pinit], by simp [pruns, pinit], by simp [pruns, pinit]⟩
  | m + 1 => by
    rw [rs_pruns_succ']
    have hB : 1114112 + tsize (pruns (pinit tk) m) ≤ itemValBound tk.length := by
      have := rs_tsize_all tk m; have := rs_poly tk.length; unfold itemValBound; omega
    exact rs_pstep_ok (minv_pruns (minv_pinit tk) m) hB (rs_ok_all tk m)

theorem finalSt_itemVals (tk : List Nat) :
    ∀ it ∈ (finalSt tk).bodies.flatten ++ (finalSt tk).start,
      it.a ≤ itemValBound tk.length ∧ it.b ≤ itemValBound tk.length := by
  intro it hit
  have h := rs_ok_all tk (4 * tk.length + 1)
  rcases List.mem_append.1 hit with hit | hit
  · exact h.2.1 it hit
  · exact h.2.2 it hit

end Shallot.MacroPeg.Mach
