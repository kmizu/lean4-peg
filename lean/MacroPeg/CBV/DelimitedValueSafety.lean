import MacroPeg.CBV.CopyFieldCapture

/-! Newly captured words stay delimiter-free even when queries contain
arbitrary recursive calls. Positive actuals here use literals, retained
parameters and ordinary PEG control; consuming calls are checked elsewhere. -/
namespace Shallot.MacroPeg.CBV.DelimitedValueSafety
open ClockFreezing (Table)
open DelimitedCopyProjection (Free)

def Environment (d : Char) (E : List (List Char)) : Prop := ∀ w∈E, Free d w

def Safe (d : Char) : MExp → Prop
  | .eps | .notP _ | .param _ => True
  | .lit w => Free d w
  | .seq a b | .alt a b => Safe d a ∧ Safe d b
  | .star a => Safe d a
  | _ => False

def check (d : Char) : MExp → Bool
  | .eps | .notP _ | .param _ => true
  | .lit w => decide (d∉w)
  | .seq a b | .alt a b => check d a && check d b
  | .star a => check d a
  | _ => false

theorem checked (d : Char) : ∀ e, check d e=true → Safe d e
  | .eps,_ | .notP _,_ | .param _,_ => trivial
  | .lit w,h => (of_decide_eq_true h : d∉w)
  | .seq a b,h | .alt a b,h => ⟨checked d a (Bool.and_eq_true_iff.mp h).1,checked d b (Bool.and_eq_true_iff.mp h).2⟩
  | .star a,h => checked d a h
  | .call _ _,h | .any,h | .chr _,h | .range _ _,h | .dbg _,h | .lam _ _,h | .callParam _ _,h | .invoke _ _ _,h => by cases h

private theorem literal_shape (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (w : List Char) (p q : Nat) (hp : p≤x.length)
    (hv : evV g x s T E (.lit w) p=some (some q)) :
    q≤p ∧ sfx x p=w++sfx x q := by
  cases hs : Shallot.stripPrefix? w (sfx x p) with
  | none => simp [evV,hs] at hv
  | some rest =>
    have hq : rest.length=q := by simpa only [evV,hs,Option.some.injEq] using hv
    have hh := (CBVtoCBN.stripPrefix_exact w (sfx x p) rest).mp hs
    have hr : sfx x rest.length=rest :=
      sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨w,hh⟩).choose_spec
    have hl := congrArg List.length hh
    rw [length_sfx x hp,List.length_append] at hl
    exact ⟨by omega,by rw [←hq,hr]; exact hh⟩

theorem suffix_shape (d : Char)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (hE : Environment d E)
    :
    ∀ e, Safe d e → ∀ p q, p≤x.length →
      evV g x s T E e p=some (some q) →
      q≤p ∧ ∃ w, Free d w ∧ sfx x p=w++sfx x q
  | .eps, _, p, q, hp, h => by
    have hq : p=q := by simpa only [evV,if_pos hp,Option.some.injEq] using h
    subst q; exact ⟨Nat.le_refl _,[],(by simp [Free]),rfl⟩
  | .lit w, hw, p, q, hp, h => by
    obtain ⟨hq,hs⟩ := literal_shape g x s T E w p q hp h
    exact ⟨hq,w,hw,hs⟩
  | .param k, _, p, q, hp, h => by
    cases hw : E[k]? with
    | none => simp [evV,hw] at h
    | some w =>
      have hl : evV g x s T E (.lit w) p=some (some q) := by
        simpa only [evV,hw] using h
      obtain ⟨hq,hs⟩ := literal_shape g x s T E w p q hp hl
      exact ⟨hq,w,hE w (List.mem_of_getElem? hw),hs⟩
  | .notP a, _, p, q, hp, h => by
    cases ha : evV g x s T E a p with
    | none => simp [evV,ha] at h
    | some v => cases v with
      | some j => simp [evV,ha] at h
      | none =>
        have hq : p=q := by simpa only [evV,ha,Option.some.injEq] using h
        subst q; exact ⟨Nat.le_refl _,[],(by simp [Free]),rfl⟩
  | .seq a b, he, p, q, hp, h => by
    cases ha : evV g x s T E a p with
    | none => rw [evV_seq_none ha] at h; cases h
    | some v => cases v with
      | none => rw [evV_seq_fail ha] at h; cases h
      | some j =>
        rw [evV_seq_ok ha] at h
        obtain ⟨hjp,u,hu,hs⟩ := suffix_shape d g x s T E hE a he.1 p j hp ha
        obtain ⟨hqj,v,hv,ht⟩ := suffix_shape d g x s T E hE b he.2 j q (Nat.le_trans hjp hp) h
        exact ⟨Nat.le_trans hqj hjp,u++v,(by simpa only [Free,List.mem_append,not_or] using And.intro hu hv),by rw [hs,ht,List.append_assoc]⟩
  | .alt a b, he, p, q, hp, h => by
    cases ha : evV g x s T E a p with
    | none => simp [evV,ha] at h
    | some v => cases v with
      | none => exact suffix_shape d g x s T E hE b he.2 p q hp (by simpa only [evV,ha] using h)
      | some j =>
        have hj : j=q := by simpa only [evV,ha,Option.some.injEq] using h
        subst q; exact suffix_shape d g x s T E hE a he.1 p j hp ha
  | .star a, he, p, q, hp, h => by
    have hh : ∀ p q, p≤x.length → evStar (fun z => evV g x s T E a z) p=some (some q) →
        q≤p ∧ ∃ w, Free d w ∧ sfx x p=w++sfx x q := by
      intro p
      induction p using Nat.strongRecOn with
      | ind p ih =>
        intro q hp h
        cases ha : evV g x s T E a p with
        | none => rw [evStar_none ha] at h; cases h
        | some v => cases v with
          | none =>
            rw [evStar_fail ha] at h
            have hq : p=q := by simpa using h
            subst q; exact ⟨Nat.le_refl _,[],(by simp [Free]),rfl⟩
          | some j =>
            by_cases hj : j<p
            · rw [evStar_ok ha hj] at h
              obtain ⟨hjp,u,hu,hs⟩ := suffix_shape d g x s T E hE a he p j hp ha
              obtain ⟨hqj,v,hv,ht⟩ := ih j hj q (Nat.le_trans hjp hp) h
              exact ⟨Nat.le_trans hqj hjp,u++v,(by simpa only [Free,List.mem_append,not_or] using And.intro hu hv),by rw [hs,ht,List.append_assoc]⟩
            · rw [evStar_stuck ha hj] at h; cases h
    exact hh p q hp h
  | .chr _, h, _, _, _, _ | .any, h, _, _, _, _ | .range _ _, h, _, _, _, _
  | .call _ _, h, _, _, _, _ | .dbg _, h, _, _, _, _ | .lam _ _, h, _, _, _, _
  | .callParam _ _, h, _, _, _, _ | .invoke _ _ _, h, _, _, _, _ => False.elim h

theorem captured_free (d : Char) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (hE : Environment d E)
    (e : MExp) (he : check d e=true) (p q : Nat) (hp : p≤x.length)
    (hv : evV g x s T E e p=some (some q)) : Free d (pre x p q) := by
  obtain ⟨hqp,w,hw,hs⟩ := suffix_shape d g x s T E hE e (checked d e he) p q hp hv
  have hpre : pre x p q=w := by
    simpa only [length_sfx x hp,length_sfx x (Nat.le_trans hqp hp)] using pre_eq (sfx_is_suffix x p) hs
  rw [hpre]; exact hw

end Shallot.MacroPeg.CBV.DelimitedValueSafety
