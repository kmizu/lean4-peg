import MacroPeg.CBV.LoopCaptureSafety

namespace Shallot.MacroPeg.CBV.CaptureActionSafety
open StatefulScanner
open ClockFreezing (Table)
abbrev Profile (n : Nat) := Fin n → Option (Fin n)
def identity {n : Nat} : Profile n := fun q => some q
def action {n : Nat} (M : Machine n) (w : List Char) : Profile n := fun q => advance M q w
def compose {n : Nat} (P Q : Profile n) : Profile n := fun q => (P q).bind Q

theorem action_append {n : Nat} (M : Machine n) (u v : List Char) :
    action M (u++v)=compose (action M u) (action M v) := by
  funext q; exact LoopCaptureSafety.advance_append M u v q

theorem compose_identity {n : Nat} : compose (identity (n:=n)) identity=identity := rfl

/-- A finite syntax derivation computes the whole transition action of a
successful capture. Parent values may change state; no loop condition is used. -/
inductive Typed {n : Nat} (M : Machine n) (parent : Profile n) : MExp → Profile n → Prop where
  | eps : Typed M parent .eps identity
  | lit (w : List Char) : Typed M parent (.lit w) (action M w)
  | param : Typed M parent (.param 0) parent
  | query (a : MExp) : Typed M parent (.notP a) identity
  | seq {a b P Q} : Typed M parent a P → Typed M parent b Q →
      Typed M parent (.seq a b) (compose P Q)
  | alt {a b P} : Typed M parent a P → Typed M parent b P → Typed M parent (.alt a b) P
  | star {a} : Typed M parent a identity → Typed M parent (.star a) identity

/-- Equality is an executable finite check, not function extensionality
supplied by a caller or a test of the eventual captured value. -/
def equal {n : Nat} (P Q : Profile n) : Bool :=
  (List.ofFn (fun q : Fin n => decide (P q=Q q))).all id

theorem equal_sound {n : Nat} (P Q : Profile n) (h : equal P Q=true) : P=Q := by
  funext q
  have hm : decide (P q=Q q)∈List.ofFn (fun t : Fin n => decide (P t=Q t)) :=
    List.mem_ofFn.mpr ⟨q,rfl⟩
  exact of_decide_eq_true ((List.all_eq_true.mp h) _ hm)

def infer {n : Nat} (M : Machine n) (parent : Profile n) : MExp → Option (Profile n)
  | .eps | .notP _ => some identity
  | .lit w => some (action M w)
  | .param 0 => some parent
  | .seq a b => match infer M parent a,infer M parent b with
    | some P,some Q => some (compose P Q) | _,_ => none
  | .alt a b => match infer M parent a,infer M parent b with
    | some P,some Q => if equal P Q then some P else none | _,_ => none
  | .star a => match infer M parent a with
    | some P => if equal P identity then some identity else none | none => none
  | _ => none

theorem infer_sound {n : Nat} (M : Machine n) (parent : Profile n) :
    ∀ e P, infer M parent e=some P → Typed M parent e P
  | .eps, P, h => by cases h; exact .eps
  | .lit w, P, h => by cases h; exact .lit w
  | .param 0, P, h => by cases h; exact .param
  | .notP a, P, h => by cases h; exact .query a
  | .seq a b, P, h => by
    cases ha : infer M parent a with
    | none => simp [infer,ha] at h
    | some A => cases hb : infer M parent b with
      | none => simp [infer,hb] at h
      | some B =>
        simp only [infer,ha,hb,Option.some.injEq] at h
        subst P
        exact .seq (infer_sound M parent a A ha) (infer_sound M parent b B hb)
  | .alt a b, P, h => by
    cases ha : infer M parent a with
    | none => simp [infer,ha] at h
    | some A => cases hb : infer M parent b with
      | none => simp [infer,hb] at h
      | some B =>
        by_cases he : equal A B=true
        · simp only [infer,ha,hb,he,ite_true,Option.some.injEq] at h
          subst P
          exact .alt (infer_sound M parent a A ha)
            ((equal_sound A B he).symm ▸ infer_sound M parent b B hb)
        · simp [infer,ha,hb,he] at h
  | .star a, P, h => by
    cases ha : infer M parent a with
    | none => simp [infer,ha] at h
    | some A =>
      by_cases he : equal A identity=true
      · simp only [infer,ha,he,ite_true,Option.some.injEq] at h
        subst P
        exact .star ((equal_sound A identity he) ▸ infer_sound M parent a A ha)
      · simp [infer,ha,he] at h
  | .param (_+1), _, h | .chr _, _, h | .any, _, h | .range _ _, _, h
  | .call _ _, _, h | .dbg _, _, h | .lam _ _, _, h | .callParam _ _, _, h | .invoke _ _ _, _, h => by
    cases h

def fits {n : Nat} (M : Machine n) (parent : Profile n) (e : MExp) (P : Profile n) : Bool :=
  match infer M parent e with | none => false | some Q => equal Q P

theorem fits_sound {n : Nat} (M : Machine n) (parent : Profile n) (e : MExp) (P : Profile n)
    (h : fits M parent e P=true) : Typed M parent e P := by
  cases hi : infer M parent e with
  | none => simp [fits,hi] at h
  | some Q =>
    have he : Q=P := equal_sound Q P (by simpa only [fits,hi] using h)
    exact he ▸ infer_sound M parent e Q hi

def Accurate {n : Nat} (M : Machine n) (P : Profile n) (E : List (List Char)) : Prop :=
  ∀ w, E[0]?=some w → action M w=P

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

theorem suffix_shape {n : Nat} (M : Machine n) (parent : Profile n)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (hE : Accurate M parent E) {e : MExp} {P : Profile n}
    (he : Typed M parent e P) : ∀ p q, p≤x.length → evV g x s T E e p=some (some q) →
      q≤p ∧ ∃ w, action M w=P ∧ sfx x p=w++sfx x q := by
  induction he with
  | eps =>
    intro p q hp h
    have hq : p=q := by simpa only [evV,if_pos hp,Option.some.injEq] using h
    subst q; exact ⟨Nat.le_refl _,[],rfl,rfl⟩
  | lit w =>
    intro p q hp h
    obtain ⟨hq,hs⟩ := literal_shape g x s T E w p q hp h
    exact ⟨hq,w,rfl,hs⟩
  | param =>
    intro p q hp h
    cases hw : E[0]? with
    | none => simp [evV,hw] at h
    | some w =>
      have hl : evV g x s T E (.lit w) p=some (some q) := by simpa only [evV,hw] using h
      obtain ⟨hq,hs⟩ := literal_shape g x s T E w p q hp hl
      exact ⟨hq,w,hE w hw,hs⟩
  | query a =>
    intro p q hp h
    cases ha : evV g x s T E a p with
    | none => simp [evV,ha] at h
    | some v => cases v with
      | some j => simp [evV,ha] at h
      | none =>
        have hq : p=q := by simpa only [evV,ha,Option.some.injEq] using h
        subst q; exact ⟨Nat.le_refl _,[],rfl,rfl⟩
  | @seq a b P Q _ _ ia ib =>
    intro p q hp h
    cases ha : evV g x s T E a p with
    | none => rw [evV_seq_none ha] at h; cases h
    | some v => cases v with
      | none => rw [evV_seq_fail ha] at h; cases h
      | some j =>
        rw [evV_seq_ok ha] at h
        obtain ⟨hjp,u,hu,hs⟩ := ia p j hp ha
        obtain ⟨hqj,v,hv,ht⟩ := ib j q (Nat.le_trans hjp hp) h
        exact ⟨Nat.le_trans hqj hjp,u++v,by rw [action_append,hu,hv],by rw [hs,ht,List.append_assoc]⟩
  | @alt a b P _ _ ia ib =>
    intro p q hp h
    cases ha : evV g x s T E a p with
    | none => simp [evV,ha] at h
    | some v => cases v with
      | none => exact ib p q hp (by simpa only [evV,ha] using h)
      | some j =>
        have hj : j=q := by simpa only [evV,ha,Option.some.injEq] using h
        subst q; exact ia p j hp ha
  | @star a _ ia =>
    intro p
    induction p using Nat.strongRecOn with
    | ind p ih =>
      intro q hp h
      change evStar (fun z => evV g x s T E a z) p=_ at h
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
            obtain ⟨hjp,u,hu,hs⟩ := ia p j hp ha
            obtain ⟨hqj,v,hv,ht⟩ := ih j hj q (Nat.le_trans hjp hp) h
            exact ⟨Nat.le_trans hqj hjp,u++v,by rw [action_append,hu,hv,compose_identity],by rw [hs,ht,List.append_assoc]⟩
          · rw [evStar_stuck ha hj] at h; cases h

theorem capture_action {n : Nat} (M : Machine n) (parent : Profile n)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (hE : Accurate M parent E) {e : MExp} {P : Profile n}
    (he : Typed M parent e P) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s T E e p=some (some q)) :
    action M (pre x p q)=P ∧ sfx x p=pre x p q++sfx x q := by
  obtain ⟨hqp,w,hw,hs⟩ := suffix_shape M parent g x s T E hE he p q hp h
  have hpw : pre x p q=w := by
    simpa only [length_sfx x hp,length_sfx x (Nat.le_trans hqp hp)] using pre_eq (sfx_is_suffix x p) hs
  exact ⟨hpw.symm ▸ hw,by rw [hpw]; exact hs⟩

end Shallot.MacroPeg.CBV.CaptureActionSafety
