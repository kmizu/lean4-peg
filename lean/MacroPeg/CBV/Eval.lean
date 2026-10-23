import MacroPeg.CBV.Spans

namespace Shallot.MacroPeg.CBV

open Shallot (beqChar leChar stripPrefix?)

section Eval
variable (g : MGrammar) (x : List Char)

mutual
  def eval (s : Strategy) (row : List Nat) (E : List Nat) : MExp → Nat → Res
    | .eps, p => some (some p)
    | .any, p =>
      match sfx x p with
      | _ :: r => some (some r.length)
      | [] => some none
    | .chr c, p =>
      match sfx x p with
      | d :: r => if beqChar c d then some (some r.length) else some none
      | [] => some none
    | .range lo hi, p =>
      match sfx x p with
      | d :: r => if (leChar lo d && leChar d hi) then some (some r.length) else some none
      | [] => some none
    | .lit w, p =>
      match stripPrefix? w (sfx x p) with
      | some r => some (some r.length)
      | none => some none
    | .param k, p =>
      match E[k]? with
      | some i =>
        match stripPrefix? (literalAt x i) (sfx x p) with
        | some r => some (some r.length)
        | none => some none
      | none => some none
    | .call i args, p =>
      match ruleAtM g.rules i with
      | some r =>
        if r.arity = args.length then
          match s with
          | .callByValueSeq =>
            match seqArgs s row E args p with
            | some (some (W, q)) => lookup g x row i W q
            | some none => some none
            | none => none
          | _ =>
            match parArgs s row E args p with
            | some (some W) => lookup g x row i W p
            | some none => some none
            | none => none
        else some none
      | none => some none
    | .seq a b, p =>
      match eval s row E a p with
      | some (some j) => eval s row E b j
      | r => r
    | .alt a b, p =>
      match eval s row E a p with
      | some none => eval s row E b p
      | r => r
    | .star a, p => evStar (fun q => eval s row E a q) p
    | .notP a, p =>
      match eval s row E a p with
      | some (some _) => some none
      | some none => some (some p)
      | none => none
    | .dbg _, p => some (some p)
    | .lam _ _, p => some (some p)
    | .callParam _ _, _ => some none
    | .invoke _ _ _, _ => none

  /-- Par: every argument at the same position, left to right, stopping at the first failure. -/
  def parArgs (s : Strategy) (row : List Nat) (E : List Nat) :
      List MExp → Nat → Option (Option (List Nat))
    | [], _ => some (some [])
    | a :: as, p =>
      match eval s row E a p with
      | some (some j) =>
        match parArgs s row E as p with
        | some (some W) => some (some (spanId x.length p j :: W))
        | r => r
      | some none => some none
      | none => none

  /-- Seq: arguments threaded through the input; returns the values and the final position. -/
  def seqArgs (s : Strategy) (row : List Nat) (E : List Nat) :
      List MExp → Nat → Option (Option (List Nat × Nat))
    | [], p => some (some ([], p))
    | a :: as, p =>
      match eval s row E a p with
      | some (some j) =>
        match seqArgs s row E as j with
        | some (some (W, q)) => some (some (spanId x.length p j :: W, q))
        | r => r
      | some none => some none
      | none => none
end
end Eval

/-- Every table entry is a bounded code, including the unknown and failure codes. -/
def RowBound (n : Nat) (row : List Nat) : Prop := ∀ v ∈ row, v ≤ n + 2

theorem decode_ok {n v : Nat} (h : v ≤ n + 2) : OkR n (resultDecode v) := by
  intro j hj
  cases v with
  | zero => cases hj
  | succ v => cases v with
    | zero => cases hj
    | succ v => have hv : v = j := Option.some.inj (Option.some.inj hj); omega

theorem lookup_ok {g : MGrammar} {x : List Char} {row : List Nat} (h : RowBound x.length row)
    (i : Nat) (ids : List Nat) (p : Nat) : OkR x.length (lookup g x row i ids p) := by
  unfold lookup
  apply decode_ok
  rw [List.getD_eq_getElem?_getD]
  cases hv : row[(keys g x).idxOf (i, ids, p)]? with
  | none => simp
  | some v => exact h v (List.mem_of_getElem? hv)

/-- Intermediate positions remain within the original input, even during table iteration. -/
theorem eval_ok {g : MGrammar} {x : List Char} {s : Strategy} {row E : List Nat}
    (hrow : RowBound x.length row) :
    ∀ (e : MExp) (p : Nat), p ≤ x.length → OkR x.length (eval g x s row E e p)
  | .eps, p, hp | .dbg _, p, hp | .lam _ _, p, hp => by simp only [eval]; exact okR_ok hp
  | .callParam _ _, _, _ => by simp only [eval]; exact okR_fail _
  | .invoke _ _ _, _, _ => by simp only [eval]; exact okR_none _
  | .any, p, _ => by
    simp only [eval]
    have := length_sfx_le x p
    split
    · rename_i r h; rw [h] at this; exact okR_ok (by simp at this; omega)
    · exact okR_fail _
  | .chr c, p, _ => by
    simp only [eval]
    have := length_sfx_le x p
    split
    · rename_i d r h
      rw [h] at this
      split
      · exact okR_ok (by simp at this; omega)
      · exact okR_fail _
    · exact okR_fail _
  | .range lo hi, p, _ => by
    simp only [eval]
    have := length_sfx_le x p
    split
    · rename_i d r h
      rw [h] at this
      split
      · exact okR_ok (by simp at this; omega)
      · exact okR_fail _
    · exact okR_fail _
  | .lit w, p, _ => by
    simp only [eval]
    split
    · rename_i r h; exact okR_ok (Nat.le_trans (stripPrefix_length _ _ _ h) (length_sfx_le x p))
    · exact okR_fail _
  | .param k, p, _ => by
    simp only [eval]
    split
    · split
      · rename_i r h; exact okR_ok (Nat.le_trans (stripPrefix_length _ _ _ h) (length_sfx_le x p))
      · exact okR_fail _
    · exact okR_fail _
  | .call i args, p, _ => by
    simp only [eval]
    split
    · split
      · split
        · split
          · exact lookup_ok hrow _ _ _
          · exact okR_fail _
          · exact okR_none _
        · split
          · exact lookup_ok hrow _ _ _
          · exact okR_fail _
          · exact okR_none _
      · exact okR_fail _
    · exact okR_fail _
  | .seq a b, p, hp => by
    have ha := eval_ok (g := g) (s := s) (E := E) hrow a p hp
    simp only [eval]
    cases h : eval g x s row E a p with
    | none => exact okR_none _
    | some r => cases r with
      | none => exact okR_fail _
      | some j => exact eval_ok hrow b j (ha j h)
  | .alt a b, p, hp => by
    have ha := eval_ok (g := g) (s := s) (E := E) hrow a p hp
    simp only [eval]
    cases h : eval g x s row E a p with
    | none => exact okR_none _
    | some r => cases r with
      | none => exact eval_ok hrow b p hp
      | some j => exact okR_ok (ha j h)
  | .notP a, p, hp => by
    simp only [eval]
    cases h : eval g x s row E a p with
    | none => exact okR_none _
    | some r => cases r with
      | none => exact okR_ok hp
      | some j => exact okR_fail _
  | .star a, p, hp => by
    simp only [eval]
    intro j h
    have := evStar_le p j h; omega

def ValidIds (x : List Char) (ids : List Nat) : Prop := ∀ i ∈ ids, i < (subStrs x).length

theorem parArgs_valid {g : MGrammar} {x : List Char} {s : Strategy} {row E : List Nat} :
    ∀ (args : List MExp) (p : Nat), p ≤ x.length → ∀ ids,
      parArgs g x s row E args p = some (some ids) → ids.length = args.length ∧ ValidIds x ids
  | [], p, hp, ids, h => by simp only [parArgs, Option.some.injEq] at h; subst ids; exact ⟨rfl, by simp [ValidIds]⟩
  | a :: args, p, hp, ids, h => by
    cases hv : eval g x s row E a p with
    | none => simp [parArgs, hv] at h
    | some v => cases v with
      | none => simp [parArgs, hv] at h
      | some j =>
        cases ht : parArgs g x s row E args p with
        | none => simp [parArgs, hv, ht] at h
        | some v => cases v with
          | none => simp [parArgs, hv, ht] at h
          | some js =>
            simp only [parArgs, hv, ht, Option.some.injEq] at h
            subst ids
            have hs := parArgs_valid args p hp js ht
            exact ⟨by simp [hs.1], by intro i hi; rcases List.mem_cons.mp hi with rfl | hi; exact spanId_lt hp; exact hs.2 i hi⟩

theorem seqArgs_valid {g : MGrammar} {x : List Char} {s : Strategy} {row E : List Nat}
    (hrow : RowBound x.length row) :
    ∀ (args : List MExp) (p : Nat), p ≤ x.length → ∀ ids q,
      seqArgs g x s row E args p = some (some (ids, q)) →
      ids.length = args.length ∧ ValidIds x ids ∧ q ≤ x.length
  | [], p, hp, ids, q, h => by
    have he : ([], p) = (ids, q) := Option.some.inj (Option.some.inj h)
    cases he
    exact ⟨rfl, by simp [ValidIds], hp⟩
  | a :: args, p, hp, ids, q, h => by
    cases hv : eval g x s row E a p with
    | none => simp [seqArgs, hv] at h
    | some v => cases v with
      | none => simp [seqArgs, hv] at h
      | some j =>
        cases ht : seqArgs g x s row E args j with
        | none => simp [seqArgs, hv, ht] at h
        | some v => cases v with
          | none => simp [seqArgs, hv, ht] at h
          | some v =>
            obtain ⟨js, q'⟩ := v
            simp only [seqArgs, hv, ht, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hids, hq⟩ := h
            subst ids q'
            have hs := seqArgs_valid hrow args j (eval_ok hrow a p hp j hv) js q ht
            exact ⟨by simp [hs.1], by intro i hi; rcases List.mem_cons.mp hi with rfl | hi; exact spanId_lt hp; exact hs.2.1 i hi, hs.2.2⟩

end Shallot.MacroPeg.CBV
