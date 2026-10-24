import MacroPeg.CBV.LoopCaptureSafety

namespace Shallot.MacroPeg.CBV.TotalCaptureSafety
open StatefulScanner
open ClockFreezing (Table)

/-- The word stays within the scanner frontier from every starting state.
Its final state and complete action may vary on every successful capture. -/
def Total {n : Nat} (M : Machine n) (w : List Char) : Prop :=
  ∀ q, advance M q w≠none

theorem total_nil {n : Nat} (M : Machine n) : Total M [] := by
  intro q; simp [advance]

theorem total_append {n : Nat} (M : Machine n) (u v : List Char)
    (hu : Total M u) (hv : Total M v) : Total M (u++v) := by
  intro q
  rw [LoopCaptureSafety.advance_append]
  cases ht : advance M q u with
  | none => exact False.elim (hu q ht)
  | some r => exact hv r

def Environment {n : Nat} (M : Machine n) (E : List (List Char)) : Prop :=
  ∀ w∈E, Total M w

/-- Queries consume no capture characters. Their recursive computations
are preserved; no totality assumption is made about their evaluation. -/
def Safe {n : Nat} (M : Machine n) : MExp → Prop
  | .eps | .notP _ | .param _ => True
  | .lit w => Total M w
  | .seq a b | .alt a b => Safe M a ∧ Safe M b
  | .star a => Safe M a
  | _ => False

def wordCheck {n : Nat} (M : Machine n) (w : List Char) : Bool :=
  (List.ofFn (fun q : Fin n => (advance M q w).isSome)).all id

theorem wordCheck_sound {n : Nat} (M : Machine n) (w : List Char)
    (h : wordCheck M w=true) : Total M w := by
  intro q hn
  have hh := (List.all_eq_true.mp h) ((advance M q w).isSome) (List.mem_ofFn.mpr ⟨q,rfl⟩)
  simp only [hn,Option.isSome_none,id_eq,Bool.false_eq_true] at hh

/-- A finite syntax check on literal transitions, independent of input
strings, successful argument evaluations or a fixed eventual action. -/
def check {n : Nat} (M : Machine n) : MExp → Bool
  | .eps | .notP _ | .param _ => true
  | .lit w => wordCheck M w
  | .seq a b | .alt a b => check M a && check M b
  | .star a => check M a
  | _ => false

theorem check_sound {n : Nat} (M : Machine n) : ∀ e, check M e=true → Safe M e
  | .eps, _ | .notP _, _ | .param _, _ => True.intro
  | .lit w, h => wordCheck_sound M w h
  | .seq a b, h | .alt a b, h =>
    ⟨check_sound M a (Bool.and_eq_true_iff.mp h).1,check_sound M b (Bool.and_eq_true_iff.mp h).2⟩
  | .star a, h => check_sound M a h
  | .chr _, h | .any, h | .range _ _, h | .call _ _, h | .dbg _, h
  | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => by cases h

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

/-- Successful evaluation derives an actual frontier-safe captured word. -/
theorem suffix_shape {n : Nat} (M : Machine n) 
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (hE : Environment M E) :
    ∀ e, Safe M e → ∀ p q, p≤x.length →
      evV g x s T E e p=some (some q) →
      q≤p ∧ ∃ w, Total M w ∧ sfx x p=w++sfx x q
  | .eps, _, p, q, hp, h => by
    have hq : p=q := by simpa only [evV,if_pos hp,Option.some.injEq] using h
    subst q; exact ⟨Nat.le_refl _,[],total_nil M,rfl⟩
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
        subst q; exact ⟨Nat.le_refl _,[],total_nil M,rfl⟩
  | .seq a b, he, p, q, hp, h => by
    cases ha : evV g x s T E a p with
    | none => rw [evV_seq_none ha] at h; cases h
    | some v => cases v with
      | none => rw [evV_seq_fail ha] at h; cases h
      | some j =>
        rw [evV_seq_ok ha] at h
        obtain ⟨hjp,u,hu,hs⟩ := suffix_shape M g x s T E hE a he.1 p j hp ha
        obtain ⟨hqj,v,hv,ht⟩ := suffix_shape M g x s T E hE b he.2 j q (Nat.le_trans hjp hp) h
        exact ⟨Nat.le_trans hqj hjp,u++v,total_append M u v hu hv,by rw [hs,ht,List.append_assoc]⟩
  | .alt a b, he, p, q, hp, h => by
    cases ha : evV g x s T E a p with
    | none => simp [evV,ha] at h
    | some v => cases v with
      | none => exact suffix_shape M g x s T E hE b he.2 p q hp (by simpa only [evV,ha] using h)
      | some j =>
        have hj : j=q := by simpa only [evV,ha,Option.some.injEq] using h
        subst q; exact suffix_shape M g x s T E hE a he.1 p j hp ha
  | .star a, he, p, q, hp, h => by
    have hh : ∀ p q, p≤x.length → evStar (fun z => evV g x s T E a z) p=some (some q) →
        q≤p ∧ ∃ w, Total M w ∧ sfx x p=w++sfx x q := by
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
            subst q; exact ⟨Nat.le_refl _,[],total_nil M,rfl⟩
          | some j =>
            by_cases hj : j<p
            · rw [evStar_ok ha hj] at h
              obtain ⟨hjp,u,hu,hs⟩ := suffix_shape M g x s T E hE a he p j hp ha
              obtain ⟨hqj,v,hv,ht⟩ := ih j hj q (Nat.le_trans hjp hp) h
              exact ⟨Nat.le_trans hqj hjp,u++v,total_append M u v hu hv,by rw [hs,ht,List.append_assoc]⟩
            · rw [evStar_stuck ha hj] at h; cases h
    exact hh p q hp h
  | .chr _, h, _, _, _, _ | .any, h, _, _, _, _ | .range _ _, h, _, _, _, _
  | .call _ _, h, _, _, _, _ | .dbg _, h, _, _, _, _ | .lam _ _, h, _, _, _, _
  | .callParam _ _, h, _, _, _, _ | .invoke _ _ _, h, _, _, _, _ => False.elim h

theorem capture_total {n : Nat} (M : Machine n)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (hE : Environment M E) (e : MExp) (he : Safe M e)
    (p q : Nat) (hp : p≤x.length) (h : evV g x s T E e p=some (some q)) :
    Total M (pre x p q) ∧ sfx x p=pre x p q++sfx x q := by
  obtain ⟨hqp,w,hw,hs⟩ := suffix_shape M g x s T E hE e he p q hp h
  have hpw : pre x p q=w := by
    simpa only [length_sfx x hp,length_sfx x (Nat.le_trans hqp hp)] using
      pre_eq (sfx_is_suffix x p) hs
  exact ⟨hpw.symm ▸ hw,hpw.symm ▸ hs⟩

end Shallot.MacroPeg.CBV.TotalCaptureSafety
