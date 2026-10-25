import MacroPeg.CBV.SelectedCaptureSafety

namespace Shallot.MacroPeg.CBV.CaptureInputSafety
open TotalCaptureSafety (Total Environment total_nil total_append wordCheck wordCheck_sound)
open ClockFreezing (Table)
open StatefulScanner (Machine)
open ParameterizedCaptureSafety (par_arguments seq_arguments capture_of_shape)
open SelectedCaptureSafety (Rows)

/-- Untrusted retained values may affect queries but cannot contribute
consumed characters to an argument requiring scanner safety. -/
def withoutParams {n : Nat} (M : StatefulScanner.Machine n) (active : Nat → Bool) : MExp → Bool
  | .eps | .notP _ => true
  | .param _ => false
  | .lit w => wordCheck M w
  | .chr c => wordCheck M [c]
  | .seq a b | .alt a b => withoutParams M active a && withoutParams M active b
  | .star a => withoutParams M active a
  | .call i args => active i && args.attach.all (fun a => withoutParams M active a.val)
  | _ => false
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals first | omega | exact Nat.lt_trans (List.sizeOf_lt_of_mem a.property) (by simp; omega)

abbrev Safe {n : Nat} (M : Machine n) (active : Nat → Bool) (e : MExp) := withoutParams M active e=true

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
theorem without_shape {n : Nat} (M : Machine n)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char))
    (active : Nat → Bool) (hRows : Rows M active x T) :
    ∀ e, Safe M active e → ∀ p q, p≤x.length →
      evV g x s T E e p=some (some q) →
      q≤p ∧ ∃ w, Total M w ∧ sfx x p=w++sfx x q
  | .eps, _, p, q, hp, h => by
    have hq : p=q := by simpa only [evV,if_pos hp,Option.some.injEq] using h
    subst q; exact ⟨Nat.le_refl _,[],total_nil M,rfl⟩
  | .lit w, hw, p, q, hp, h => by
    have hw := wordCheck_sound M w (by simpa only [Safe,withoutParams] using hw)
    obtain ⟨hq,hs⟩ := literal_shape g x s T E w p q hp h
    exact ⟨hq,w,hw,hs⟩
  | .chr c, hc, p, q, hp, h => by
    have hw := wordCheck_sound M [c] (by simpa only [Safe,withoutParams] using hc)
    have hl : evV g x s T E (.lit [c]) p=some (some q) := by
      cases hs : sfx x p with
      | nil => simp [evV,hs] at h
      | cons d rest =>
        cases hb : Shallot.beqChar c d <;>
          simpa [evV,hs,Shallot.stripPrefix?,hb] using h
    obtain ⟨hq,hs⟩ := literal_shape g x s T E [c] p q hp hl
    exact ⟨hq,[c],hw,hs⟩
  | .param _, h, _, _, _, _ => by simp only [Safe,withoutParams,Bool.false_eq_true] at h
  | .notP a, _, p, q, hp, h => by
    cases ha : evV g x s T E a p with
    | none => simp [evV,ha] at h
    | some v => cases v with
      | some j => simp [evV,ha] at h
      | none =>
        have hq : p=q := by simpa only [evV,ha,Option.some.injEq] using h
        subst q; exact ⟨Nat.le_refl _,[],total_nil M,rfl⟩
  | .seq a b, he, p, q, hp, h => by
    have he := Bool.and_eq_true_iff.mp (show (withoutParams M active a && withoutParams M active b)=true from by simpa only [Safe,withoutParams] using he)
    cases ha : evV g x s T E a p with
    | none => rw [evV_seq_none ha] at h; cases h
    | some v => cases v with
      | none => rw [evV_seq_fail ha] at h; cases h
      | some j =>
        rw [evV_seq_ok ha] at h
        obtain ⟨hjp,u,hu,hs⟩ := without_shape M g x s T E active hRows a he.1 p j hp ha
        obtain ⟨hqj,v,hv,ht⟩ := without_shape M g x s T E active hRows b he.2 j q (Nat.le_trans hjp hp) h
        exact ⟨Nat.le_trans hqj hjp,u++v,total_append M u v hu hv,by rw [hs,ht,List.append_assoc]⟩
  | .alt a b, he, p, q, hp, h => by
    have he := Bool.and_eq_true_iff.mp (show (withoutParams M active a && withoutParams M active b)=true from by simpa only [Safe,withoutParams] using he)
    cases ha : evV g x s T E a p with
    | none => simp [evV,ha] at h
    | some v => cases v with
      | none => exact without_shape M g x s T E active hRows b he.2 p q hp (by simpa only [evV,ha] using h)
      | some j =>
        have hj : j=q := by simpa only [evV,ha,Option.some.injEq] using h
        subst q; exact without_shape M g x s T E active hRows a he.1 p j hp ha
  | .star a, he, p, q, hp, h => by
    have he : Safe M active a := by simpa only [Safe,withoutParams] using he
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
              obtain ⟨hjp,u,hu,hs⟩ := without_shape M g x s T E active hRows a he p j hp ha
              obtain ⟨hqj,v,hv,ht⟩ := ih j hj q (Nat.le_trans hjp hp) h
              exact ⟨Nat.le_trans hqj hjp,u++v,total_append M u v hu hv,by rw [hs,ht,List.append_assoc]⟩
            · rw [evStar_stuck ha hj] at h; cases h
    exact hh p q hp h
  | .call i args, he, p, q, hp, h => by
    have he : (active i && args.attach.all (fun a => withoutParams M active a.val))=true := by
      simpa only [Safe,withoutParams] using he
    have hi : active i=true := (Bool.and_eq_true_iff.mp he).1
    have hArgs : ∀ a∈args, Safe M active a := by
      intro a ha
      exact (List.all_eq_true.mp (Bool.and_eq_true_iff.mp he).2) ⟨a,ha⟩ (by simp)
    have hArgShape := fun a ha => without_shape M g x s T E active hRows a (hArgs a ha)
    cases hr : ruleAtM g.rules i with
    | none => simp [evV,hr] at h
    | some r =>
      by_cases hn : r.arity=args.length
      · by_cases hs : s=.callByValueSeq
        · subst s
          rw [evV_call_seq hr hn] at h
          cases hv : evSeqArgs g x .callByValueSeq T E args p with
          | none => simp [hv] at h
          | some v => cases v with
            | none => simp [hv] at h
            | some pair =>
              obtain ⟨W,j⟩ := pair
              simp only [hv] at h
              obtain ⟨hW,hjp,u,hu,hs⟩ := seq_arguments M g x .callByValueSeq T E args hArgShape p j hp W hv
              obtain ⟨hqj,v,hv,ht⟩ := hRows i hi W hW j q (Nat.le_trans hjp hp) h
              exact ⟨Nat.le_trans hqj hjp,u++v,total_append M u v hu hv,by rw [hs,ht,List.append_assoc]⟩
        · rw [evV_call_par hr hn hs] at h
          cases hv : evParArgs g x s T E args p with
          | none => simp [hv] at h
          | some v => cases v with
            | none => simp [hv] at h
            | some W =>
              simp only [hv] at h
              exact hRows i hi W (par_arguments M g x s T E args hArgShape p hp W hv) p q hp h
      · simp [evV,hr,hn] at h
  | .any, h, _, _, _, _ | .range _ _, h, _, _, _, _
  | .dbg _, h, _, _, _, _ | .lam _ _, h, _, _, _, _
  | .callParam _ _, h, _, _, _, _ | .invoke _ _ _, h, _, _, _, _ => by simp only [Safe,withoutParams,Bool.false_eq_true] at h
termination_by e => sizeOf e


def EnvironmentFor {n : Nat} (M : Machine n) (trusted : Bool) (E : List (List Char)) : Prop :=
  trusted=true → Environment M E

def check {n : Nat} (M : Machine n) (active : Nat → Bool) (trusted : Bool) (e : MExp) : Bool :=
  if trusted then SelectedCaptureSafety.check M active e else withoutParams M active e

theorem suffix_shape {n : Nat} (M : Machine n) (g : MGrammar) (x : List Char)
    (s : Strategy) (T : Table) (E : List (List Char)) (trusted : Bool)
    (hE : EnvironmentFor M trusted E) (active : Nat → Bool) (hRows : Rows M active x T)
    (e : MExp) (he : check M active trusted e=true) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s T E e p=some (some q)) :
    q≤p ∧ ∃ w, Total M w ∧ sfx x p=w++sfx x q := by
  cases trusted with
  | false => exact without_shape M g x s T E active hRows e he p q hp h
  | true => exact SelectedCaptureSafety.suffix_shape M g x s T E (hE rfl) active hRows e he p q hp h

end Shallot.MacroPeg.CBV.CaptureInputSafety
