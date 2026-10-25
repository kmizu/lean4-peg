import MacroPeg.CBV.ParameterizedCaptureSafety

namespace Shallot.MacroPeg.CBV.SelectedCaptureSafety
open TotalCaptureSafety (Total Environment total_nil total_append wordCheck wordCheck_sound)
open ClockFreezing (Table)
open StatefulScanner (Machine)
open ParameterizedCaptureSafety (par_arguments seq_arguments capture_of_shape)

/-- Consuming calls need a selected safe row. Queries may use any actual
row and preserve their full partial computation. -/
def check {n : Nat} (M : StatefulScanner.Machine n) (active : Nat → Bool) : MExp → Bool
  | .eps | .notP _ | .param _ => true
  | .lit w => wordCheck M w
  | .chr c => wordCheck M [c]
  | .seq a b | .alt a b => check M active a && check M active b
  | .star a => check M active a
  | .call i args => active i && args.attach.all (fun a => check M active a.val)
  | _ => false
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals first | omega | exact Nat.lt_trans (List.sizeOf_lt_of_mem a.property) (by simp; omega)

abbrev Safe {n : Nat} (M : StatefulScanner.Machine n) (active : Nat → Bool) (e : MExp) := check M active e=true

/-- The invariant quantifies over actual retained values, including all
new argument captures; no row result is supplied to the final theorem. -/
def Rows {n : Nat} (M : StatefulScanner.Machine n) (active : Nat → Bool) (x : List Char) (T : Table) : Prop :=
  ∀ i, active i=true → ∀ E, Environment M E → ∀ p q, p≤x.length →
    valAt (T i E) p=some (some q) →
    q≤p ∧ ∃ w, Total M w ∧ sfx x p=w++sfx x q

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
    (E : List (List Char)) (hE : Environment M E)
    (active : Nat → Bool) (hRows : Rows M active x T) :
    ∀ e, Safe M active e → ∀ p q, p≤x.length →
      evV g x s T E e p=some (some q) →
      q≤p ∧ ∃ w, Total M w ∧ sfx x p=w++sfx x q
  | .eps, _, p, q, hp, h => by
    have hq : p=q := by simpa only [evV,if_pos hp,Option.some.injEq] using h
    subst q; exact ⟨Nat.le_refl _,[],total_nil M,rfl⟩
  | .lit w, hw, p, q, hp, h => by
    have hw := wordCheck_sound M w (by simpa only [Safe,check] using hw)
    obtain ⟨hq,hs⟩ := literal_shape g x s T E w p q hp h
    exact ⟨hq,w,hw,hs⟩
  | .chr c, hc, p, q, hp, h => by
    have hw := wordCheck_sound M [c] (by simpa only [Safe,check] using hc)
    have hl : evV g x s T E (.lit [c]) p=some (some q) := by
      cases hs : sfx x p with
      | nil => simp [evV,hs] at h
      | cons d rest =>
        cases hb : Shallot.beqChar c d <;>
          simpa [evV,hs,Shallot.stripPrefix?,hb] using h
    obtain ⟨hq,hs⟩ := literal_shape g x s T E [c] p q hp hl
    exact ⟨hq,[c],hw,hs⟩
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
    have he := Bool.and_eq_true_iff.mp (show (check M active a && check M active b)=true from by simpa only [Safe,check] using he)
    cases ha : evV g x s T E a p with
    | none => rw [evV_seq_none ha] at h; cases h
    | some v => cases v with
      | none => rw [evV_seq_fail ha] at h; cases h
      | some j =>
        rw [evV_seq_ok ha] at h
        obtain ⟨hjp,u,hu,hs⟩ := suffix_shape M g x s T E hE active hRows a he.1 p j hp ha
        obtain ⟨hqj,v,hv,ht⟩ := suffix_shape M g x s T E hE active hRows b he.2 j q (Nat.le_trans hjp hp) h
        exact ⟨Nat.le_trans hqj hjp,u++v,total_append M u v hu hv,by rw [hs,ht,List.append_assoc]⟩
  | .alt a b, he, p, q, hp, h => by
    have he := Bool.and_eq_true_iff.mp (show (check M active a && check M active b)=true from by simpa only [Safe,check] using he)
    cases ha : evV g x s T E a p with
    | none => simp [evV,ha] at h
    | some v => cases v with
      | none => exact suffix_shape M g x s T E hE active hRows b he.2 p q hp (by simpa only [evV,ha] using h)
      | some j =>
        have hj : j=q := by simpa only [evV,ha,Option.some.injEq] using h
        subst q; exact suffix_shape M g x s T E hE active hRows a he.1 p j hp ha
  | .star a, he, p, q, hp, h => by
    have he : Safe M active a := by simpa only [Safe,check] using he
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
              obtain ⟨hjp,u,hu,hs⟩ := suffix_shape M g x s T E hE active hRows a he p j hp ha
              obtain ⟨hqj,v,hv,ht⟩ := ih j hj q (Nat.le_trans hjp hp) h
              exact ⟨Nat.le_trans hqj hjp,u++v,total_append M u v hu hv,by rw [hs,ht,List.append_assoc]⟩
            · rw [evStar_stuck ha hj] at h; cases h
    exact hh p q hp h
  | .call i args, he, p, q, hp, h => by
    have he : (active i && args.attach.all (fun a => check M active a.val))=true := by
      simpa only [Safe,check] using he
    have hi : active i=true := (Bool.and_eq_true_iff.mp he).1
    have hArgs : ∀ a∈args, Safe M active a := by
      intro a ha
      exact (List.all_eq_true.mp (Bool.and_eq_true_iff.mp he).2) ⟨a,ha⟩ (by simp)
    have hArgShape := fun a ha => suffix_shape M g x s T E hE active hRows a (hArgs a ha)
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
  | .callParam _ _, h, _, _, _, _ | .invoke _ _ _, h, _, _, _, _ => by simp only [Safe,check,Bool.false_eq_true] at h
termination_by e => sizeOf e

/-- The finite selected rule set need not include the helper prefix. -/
def grammarCheck {n : Nat} (M : Machine n) (g : MGrammar) (active : Nat → Bool) : Bool :=
  g.rules.zipIdx.all (fun (r,i) => !active i || check M active r.body)

theorem grammarCheck_sound {n : Nat} (M : Machine n) (g : MGrammar) (active : Nat → Bool)
    (h : grammarCheck M g active=true) (i : Nat) (hi : active i=true) (r : MRule)
    (hr : ruleAtM g.rules i=some r) : Safe M active r.body := by
  rw [ruleAtM_eq_getElem?] at hr
  have hm : (r,i)∈g.rules.zipIdx := List.mem_of_getElem? (show g.rules.zipIdx[i]?=some (r,i) from by
    simp [List.getElem?_zipIdx,hr])
  have hh := (List.all_eq_true.mp h) (r,i) hm
  simpa [hi] using hh

theorem physical_rows {n : Nat} (M : Machine n) (g : MGrammar) (active : Nat → Bool)
    (hg : grammarCheck M g active=true) (x : List Char) (s : Strategy) (k : Nat) :
    Rows M active x (tblV g x s k) := by
  induction k with
  | zero => intro i hi E hE p q hp h; simp [tblV,valAt_nil] at h
  | succ k ih =>
    intro i hi E hE p q hp h
    cases hr : ruleAtM g.rules i with
    | none => simp [tblV,hr,valAt_nil] at h
    | some r =>
      rw [valAt_tblV_succ hr E hp] at h
      exact suffix_shape M g x s _ E hE active ih r.body
        (grammarCheck_sound M g active hg i hi r hr) p q hp h

theorem frozen_rows {n : Nat} (M : Machine n) (g : MGrammar) (active : Nat → Bool)
    (hg : grammarCheck M g active=true) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor k : Nat) : Rows M active x (ClockFreezing.frozen g x s pick floor k) := by
  induction k with
  | zero =>
    intro i hi E hE p q hp h
    by_cases hb : pick i=true
    · simp only [ClockFreezing.frozen,hb,if_true] at h
      exact physical_rows M g active hg x s floor i hi E hE p q hp h
    · simp only [ClockFreezing.frozen,hb,Bool.false_eq_true,if_false,valAt_nil] at h
      cases h
  | succ k ih =>
    intro i hi E hE p q hp h
    by_cases hb : pick i=true
    · rw [ClockFreezing.frozen_rows g x s pick floor (k+1) i hb E] at h
      exact physical_rows M g active hg x s floor i hi E hE p q hp h
    · simp only [ClockFreezing.frozen,hb,Bool.false_eq_true,if_false,ClockFreezing.step] at h
      cases hr : ruleAtM g.rules i with
      | none => simp [hr,valAt_nil] at h
      | some r =>
        simp only [hr,valAt_rangeMap,if_pos hp] at h
        exact suffix_shape M g x s _ E hE active ih r.body
          (grammarCheck_sound M g active hg i hi r hr) p q hp h

theorem capture {n : Nat} (M : Machine n) (g : MGrammar) (active : Nat → Bool)
    (hg : grammarCheck M g active=true) (x : List Char) (s : Strategy) (k : Nat)
    (E : List (List Char)) (hE : Environment M E) (e : MExp) (he : check M active e=true)
    (p q : Nat) (hp : p≤x.length)
    (h : evV g x s (tblV g x s k) E e p=some (some q)) :
    Total M (pre x p q) ∧ sfx x p=pre x p q++sfx x q :=
  capture_of_shape M x p q hp (suffix_shape M g x s _ E hE active
    (physical_rows M g active hg x s k) e he p q hp h)

theorem frozen_capture {n : Nat} (M : Machine n) (g : MGrammar) (active : Nat → Bool)
    (hg : grammarCheck M g active=true) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor k : Nat) (E : List (List Char)) (hE : Environment M E) (e : MExp)
    (he : check M active e=true) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s (ClockFreezing.frozen g x s pick floor k) E e p=some (some q)) :
    Total M (pre x p q) ∧ sfx x p=pre x p q++sfx x q :=
  capture_of_shape M x p q hp (suffix_shape M g x s _ E hE active
    (frozen_rows M g active hg x s pick floor k) e he p q hp h)

/-- Primitive rows have an independently derived actual capture invariant;
all other selected rows are checked structurally. -/
def certifiedCheck {n : Nat} (M : Machine n) (g : MGrammar)
    (active primitive : Nat → Bool) : Bool :=
  g.rules.zipIdx.all (fun (r,i) => !active i || primitive i || check M active r.body)

theorem certifiedCheck_sound {n : Nat} (M : Machine n) (g : MGrammar)
    (active primitive : Nat → Bool) (hg : certifiedCheck M g active primitive=true)
    (i : Nat) (hi : active i=true) (hn : primitive i=false) (r : MRule)
    (hr : ruleAtM g.rules i=some r) : Safe M active r.body := by
  rw [ruleAtM_eq_getElem?] at hr
  have hm : (r,i)∈g.rules.zipIdx := List.mem_of_getElem? (show g.rules.zipIdx[i]?=some (r,i) from by
    simp [List.getElem?_zipIdx,hr])
  have hh := (List.all_eq_true.mp hg) (r,i) hm
  simpa [hi,hn] using hh

theorem certified_physical_rows {n : Nat} (M : Machine n) (g : MGrammar)
    (active primitive : Nat → Bool) (hg : certifiedCheck M g active primitive=true)
    (x : List Char) (s : Strategy)
    (hPrim : ∀ k, Rows M primitive x (tblV g x s k)) (k : Nat) :
    Rows M active x (tblV g x s k) := by
  induction k with
  | zero => intro i hi E hE p q hp h; simp [tblV,valAt_nil] at h
  | succ k ih =>
    intro i hi E hE p q hp h
    cases hs : primitive i with
    | true => exact hPrim (k+1) i hs E hE p q hp h
    | false =>
      cases hr : ruleAtM g.rules i with
      | none => simp [tblV,hr,valAt_nil] at h
      | some r =>
        rw [valAt_tblV_succ hr E hp] at h
        exact suffix_shape M g x s _ E hE active ih r.body
          (certifiedCheck_sound M g active primitive hg i hi hs r hr) p q hp h

theorem certified_frozen_rows {n : Nat} (M : Machine n) (g : MGrammar)
    (active primitive : Nat → Bool) (hg : certifiedCheck M g active primitive=true)
    (x : List Char) (s : Strategy) (pick : Nat → Bool) (floor : Nat)
    (hPrim : ∀ k, Rows M primitive x (tblV g x s k))
    (hPick : ∀ i, primitive i=true → pick i=true) (k : Nat) :
    Rows M active x (ClockFreezing.frozen g x s pick floor k) := by
  induction k with
  | zero =>
    intro i hi E hE p q hp h
    by_cases hb : pick i=true
    · simp only [ClockFreezing.frozen,hb,if_true] at h
      exact certified_physical_rows M g active primitive hg x s hPrim floor i hi E hE p q hp h
    · simp only [ClockFreezing.frozen,hb,Bool.false_eq_true,if_false,valAt_nil] at h
      cases h
  | succ k ih =>
    intro i hi E hE p q hp h
    by_cases hb : pick i=true
    · rw [ClockFreezing.frozen_rows g x s pick floor (k+1) i hb E] at h
      exact certified_physical_rows M g active primitive hg x s hPrim floor i hi E hE p q hp h
    · have hn : primitive i=false := by
        cases hs : primitive i with
        | false => rfl
        | true => exact False.elim (hb (hPick i hs))
      simp only [ClockFreezing.frozen,hb,Bool.false_eq_true,if_false,ClockFreezing.step] at h
      cases hr : ruleAtM g.rules i with
      | none => simp [hr,valAt_nil] at h
      | some r =>
        simp only [hr,valAt_rangeMap,if_pos hp] at h
        exact suffix_shape M g x s _ E hE active ih r.body
          (certifiedCheck_sound M g active primitive hg i hi hn r hr) p q hp h

end Shallot.MacroPeg.CBV.SelectedCaptureSafety
