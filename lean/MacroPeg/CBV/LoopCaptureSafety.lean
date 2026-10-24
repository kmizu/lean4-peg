import MacroPeg.CBV.StatefulScannerStability
import MacroPeg.CBV.ReplayFusion

namespace Shallot.MacroPeg.CBV.LoopCaptureSafety
open StatefulScanner
open ClockFreezing (Table)

def Loop {n : Nat} (M : Machine n) (q : Fin n) (w : List Char) : Prop :=
  advance M q w=some q

theorem advance_append {n : Nat} (M : Machine n) (u v : List Char) (q : Fin n) :
    advance M q (u++v)=(advance M q u).bind (fun r => advance M r v) := by
  induction u generalizing q with
  | nil => rfl
  | cons c u ih =>
    simp only [List.cons_append,advance]
    cases next (M.arcs q) c <;> simp only [Option.bind_none,Option.bind_some,ih]

theorem loop_append {n : Nat} (M : Machine n) (q : Fin n) (u v : List Char)
    (hu : Loop M q u) (hv : Loop M q v) : Loop M q (u++v) := by
  unfold Loop at *
  rw [advance_append,hu,Option.bind_some,hv]

def Environment {n : Nat} (M : Machine n) (q : Fin n) (E : List (List Char)) : Prop :=
  ∀ w∈E, Loop M q w

/-- The consumed words are loops of the fixed scanner. Queries may contain
arbitrary recursive calls; nullable stars retain their ordinary semantics. -/
def Safe {n : Nat} (M : Machine n) (q : Fin n) : MExp → Prop
  | .eps | .notP _ | .param _ => True
  | .lit w => Loop M q w
  | .seq a b | .alt a b => Safe M q a ∧ Safe M q b
  | .star a => Safe M q a
  | _ => False

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

/-- Actual successful evaluation, rather than a supplied capture shape,
determines a word returning the scanner to q. -/
theorem suffix_shape {n : Nat} (M : Machine n) (state : Fin n)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (hE : Environment M state E) :
    ∀ e, Safe M state e → ∀ p q, p≤x.length →
      evV g x s T E e p=some (some q) →
      q≤p ∧ ∃ w, Loop M state w ∧ sfx x p=w++sfx x q
  | .eps, _, p, q, hp, h => by
    have hq : p=q := by simpa only [evV,if_pos hp,Option.some.injEq] using h
    subst q; exact ⟨Nat.le_refl _,[],rfl,rfl⟩
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
        subst q; exact ⟨Nat.le_refl _,[],rfl,rfl⟩
  | .seq a b, he, p, q, hp, h => by
    cases ha : evV g x s T E a p with
    | none => rw [evV_seq_none ha] at h; cases h
    | some v => cases v with
      | none => rw [evV_seq_fail ha] at h; cases h
      | some j =>
        rw [evV_seq_ok ha] at h
        obtain ⟨hjp,u,hu,hs⟩ := suffix_shape M state g x s T E hE a he.1 p j hp ha
        obtain ⟨hqj,v,hv,ht⟩ := suffix_shape M state g x s T E hE b he.2 j q (Nat.le_trans hjp hp) h
        exact ⟨Nat.le_trans hqj hjp,u++v,loop_append M state u v hu hv,by rw [hs,ht,List.append_assoc]⟩
  | .alt a b, he, p, q, hp, h => by
    cases ha : evV g x s T E a p with
    | none => simp [evV,ha] at h
    | some v => cases v with
      | none => exact suffix_shape M state g x s T E hE b he.2 p q hp (by simpa only [evV,ha] using h)
      | some j =>
        have hj : j=q := by simpa only [evV,ha,Option.some.injEq] using h
        subst q; exact suffix_shape M state g x s T E hE a he.1 p j hp ha
  | .star a, he, p, q, hp, h => by
    have hh : ∀ p q, p≤x.length → evStar (fun z => evV g x s T E a z) p=some (some q) →
        q≤p ∧ ∃ w, Loop M state w ∧ sfx x p=w++sfx x q := by
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
            subst q; exact ⟨Nat.le_refl _,[],rfl,rfl⟩
          | some j =>
            by_cases hj : j<p
            · rw [evStar_ok ha hj] at h
              obtain ⟨hjp,u,hu,hs⟩ := suffix_shape M state g x s T E hE a he p j hp ha
              obtain ⟨hqj,v,hv,ht⟩ := ih j hj q (Nat.le_trans hjp hp) h
              exact ⟨Nat.le_trans hqj hjp,u++v,loop_append M state u v hu hv,by rw [hs,ht,List.append_assoc]⟩
            · rw [evStar_stuck ha hj] at h; cases h
    exact hh p q hp h
  | .chr _, h, _, _, _, _ | .any, h, _, _, _, _ | .range _ _, h, _, _, _, _
  | .call _ _, h, _, _, _, _ | .dbg _, h, _, _, _, _ | .lam _ _, h, _, _, _, _
  | .callParam _ _, h, _, _, _, _ | .invoke _ _ _, h, _, _, _, _ => False.elim h

theorem capture_loop {n : Nat} (M : Machine n) (state : Fin n)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (hE : Environment M state E) (e : MExp) (he : Safe M state e)
    (p q : Nat) (hp : p≤x.length) (h : evV g x s T E e p=some (some q)) :
    Loop M state (pre x p q) ∧ run M state (sfx x p)=run M state (sfx x q) := by
  obtain ⟨hqp,w,hw,hs⟩ := suffix_shape M state g x s T E hE e he p q hp h
  have hpw : pre x p q=w := by
    simpa only [length_sfx x hp,length_sfx x (Nat.le_trans hqp hp)] using
      pre_eq (sfx_is_suffix x p) hs
  exact ⟨hpw.symm ▸ hw,by rw [hs,run_after_prefix M w (sfx x q) state state hw]⟩

end Shallot.MacroPeg.CBV.LoopCaptureSafety
