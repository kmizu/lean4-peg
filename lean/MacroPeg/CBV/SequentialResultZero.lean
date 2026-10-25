import MacroPeg.CBV.SequentialResultNormal

namespace Shallot.MacroPeg.CBV.SequentialResultZero
open SequentialResultSyntax SequentialResultNormal
open EmptyResultObservation (project gate star_empty_test)
open ClockFreezing (Table)

theorem any_star_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char)) :
    ∀ p, p≤x.length → evV g x s T E (.star .any) p=some (some 0) := by
  intro p
  induction p with
  | zero =>
    intro hp
    rw [evV_star,evStar_fail (show evV g x s T E .any 0=some none from by simp [evV,sfx])]
  | succ p ih =>
    intro hp
    have hl := length_sfx x hp
    cases hx : sfx x (p+1) with
    | nil => rw [hx] at hl; simp at hl
    | cons c rest =>
      rw [hx] at hl
      have he : rest.length=p := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hl
      have ha : evV g x s T E .any (p+1)=some (some p) := by simp [evV,hx,he]
      rw [evV_star,evStar_ok ha (by omega)]
      exact ih (by omega)

theorem emptyParameter_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (i p : Nat) (hp : p≤x.length) :
    evV g x s T E (emptyParameter i) p=project p (evV g x s T E (.param i) p) := by
  rw [emptyParameter,CallLookahead.evV_peek,evV_seq_ok (any_star_eval g x s T E p hp)]
  have h0 : sfx x 0=[] := by simp [sfx]
  cases hw : E[i]? with
  | none => simp [evV,hw,CallLookahead.peek,project]
  | some w =>
    cases w with
    | nil => simp only [evV,hw,Shallot.stripPrefix?,h0,length_sfx x hp,List.length_nil,CallLookahead.peek,project,↓reduceIte]
    | cons c w =>
      simp only [evV,hw,h0,Shallot.stripPrefix?,CallLookahead.peek]
      cases h : Shallot.stripPrefix? (c::w) (sfx x p) with
      | none => rfl
      | some rest =>
        have hh := congrArg List.length ((CBVtoCBN.stripPrefix_exact _ _ _).mp h)
        rw [length_sfx x hp,List.length_append,List.length_cons] at hh
        simp only [project,if_neg (show rest.length≠p by omega)]

theorem gate_project (g h : MGrammar) (x : List Char) (T U : Table) (E : List (List Char))
    (a b c : MExp) (p : Nat)
    (hn : evV h x .callByValueSeq U E b p=evV g x .callByValueSeq T E a p)
    (hc : ∀ q, evV g x .callByValueSeq T E a p=some (some q) →
      evV h x .callByValueSeq U E c p=project p (some (some q))) :
    evV h x .callByValueSeq U E (gate b c) p=project p (evV g x .callByValueSeq T E a p) := by
  unfold gate
  change (match evV h x .callByValueSeq U E (.andP b) p with
    | some (some j) => evV h x .callByValueSeq U E c j | other => other)=_
  rw [CallLookahead.evV_peek,hn]
  cases ha : evV g x .callByValueSeq T E a p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some q => exact hc q ha

mutual
  theorem zero_eval (g : MGrammar) (x : List Char) (T U : Table)
      (rows : Rows g x T U) (ht : OkTV x.length T) (hd : SequentialClock.Descending T)
      (E : List (List Char)) : ∀ e, e.FirstOrder → ∀ p, p≤x.length →
      evV (target g) x .callByValueSeq U E (SequentialResultSyntax.zero e) p=project p (evV g x .callByValueSeq T E e p)
    | .call i args,he,p,hp => by
      apply gate_project g (target g) x T U E _ _ _ p (normal_eval g x T U rows ht hd E (.call i args) he p hp)
      intro q hq
      cases hr : ruleAtM g.rules i with
      | none => simp [evV,hr] at hq
      | some r =>
        by_cases ha : r.arity=args.length
        · rw [evV_call_seq hr ha] at hq
          cases hargs : evSeqArgs g x .callByValueSeq T E args p with
          | none => simp [hargs] at hq
          | some v => cases v with
            | none => simp [hargs] at hq
            | some pair =>
              obtain ⟨W,j⟩ := pair
              simp only [hargs] at hq
              change valAt (T i W) j=some (some q) at hq
              have hm := SequentialClock.arguments_metadata hd E args p W j hargs
              have hz := zero_args_success g x T U rows ht hd E args he p hp W j hargs
              have hqj := hd i W j q hq
              by_cases hj : j=p
              · subst j
                have hW := hm.2 rfl
                have hv : valAt (T i (List.replicate r.arity [])) p=some (some q) := by simpa only [ha,hW] using hq
                have hrow := target_rule g i true
                simp only [if_true,hr,Option.map_some] at hrow
                have hz0 : evV (target g) x .callByValueSeq U E (zeroArgs args) p=some (some p) := by simpa using hz
                rw [evV_seq_ok hz0,evV_call_seq hrow rfl,evSeq_nil]
                change valAt (U (2*i+1) []) p=_
                rw [rows.zero i r hr p hp,hv]
              · simp only [if_neg hj] at hz
                rw [evV_seq_fail hz]
                simp only [project,if_neg (show q≠p by omega)]
        · simp [evV,hr,ha] at hq
    | .seq a b,he,p,hp => by
      apply gate_project g (target g) x T U E _ _ _ p (normal_eval g x T U rows ht hd E (.seq a b) he p hp)
      intro q hq
      cases ha : evV g x .callByValueSeq T E a p with
      | none => rw [evV_seq_none ha] at hq; cases hq
      | some v => cases v with
        | none => rw [evV_seq_fail ha] at hq; cases hq
        | some j =>
          rw [evV_seq_ok ha] at hq
          have hj := evV_ok ht _ p hp j ha
          have hdown := SequentialClock.expression_descending hd E b j q hq
          have hza := (zero_eval g x T U rows ht hd E a he.1 p hp).trans (congrArg (project p) ha)
          by_cases h : j=p
          · subst j
            simp only [project,if_true] at hza
            rw [evV_seq_ok hza,zero_eval g x T U rows ht hd E b he.2 p hp,hq]
          · simp only [project,if_neg h] at hza
            rw [evV_seq_fail hza]
            simp only [project,if_neg (show q≠p by have := SequentialClock.expression_descending hd E a p j ha; omega)]
    | .alt a b,he,p,hp => by
      apply gate_project g (target g) x T U E _ _ _ p (normal_eval g x T U rows ht hd E (.alt a b) he p hp)
      intro q hq
      have hza := zero_eval g x T U rows ht hd E a he.1 p hp
      have hna := normal_eval g x T U rows ht hd E a he.1 p hp
      cases ha : evV g x .callByValueSeq T E a p with
      | none => rw [evV_alt_none ha] at hq; cases hq
      | some v => cases v with
        | none =>
          rw [evV_alt_fail ha] at hq
          rw [ha] at hza hna
          rw [evV_alt_fail hza,evV_seq_ok (evV_not_fail hna),zero_eval g x T U rows ht hd E b he.2 p hp,hq]
        | some j =>
          rw [evV_alt_ok ha] at hq
          have h : j=q := by simpa only [Option.some.injEq] using hq
          subst j
          rw [ha] at hza hna
          by_cases h : q=p
          · simp only [project,if_pos h] at hza
            rw [evV_alt_ok hza]; simp [project,h]
          · simp only [project,if_neg h] at hza
            rw [evV_alt_fail hza,evV_seq_fail (evV_not_ok hna)]
            simp [project,h]
    | .notP a,he,p,hp => by
      rw [show SequentialResultSyntax.zero (.notP a)=normal (.notP a) from rfl,normal_eval g x T U rows ht hd E (.notP a) he p hp]
      cases ha : evV g x .callByValueSeq T E a p with
      | none => rw [evV_not_none ha]; rfl
      | some v => cases v with
        | none => rw [evV_not_fail ha]; simp [project]
        | some j => rw [evV_not_ok ha]; rfl
    | .star a,he,p,hp => by
      apply gate_project g (target g) x T U E _ _ _ p (normal_eval g x T U rows ht hd E (.star a) he p hp)
      intro q hq
      change evV _ _ _ _ _ (.notP (normal a)) p=_
      simp only [evV,normal_eval g x T U rows ht hd E a he p hp]
      have hh := star_empty_test _ p q hq
      cases hv : evV g x .callByValueSeq T E a p with
      | none => simpa [hv] using hh
      | some v => cases v <;> simpa [hv] using hh
    | .param i,_,p,hp => by exact emptyParameter_eval (target g) x .callByValueSeq U E i p hp
    | .eps,_,p,hp => by simp [SequentialResultSyntax.zero,evV,project]
    | .any,_,p,hp => by
      have hl := length_sfx x hp
      cases hx : sfx x p with
      | nil => simp [SequentialResultSyntax.zero,evV,hx,project,MExp.failAlways]
      | cons c rest =>
        rw [hx] at hl
        have hn : rest.length≠p := by simp only [List.length_cons] at hl; omega
        simp [SequentialResultSyntax.zero,evV,hx,project,hn,MExp.failAlways]
    | .chr c,_,p,hp => by
      have hl := length_sfx x hp
      cases hx : sfx x p with
      | nil => simp [SequentialResultSyntax.zero,evV,hx,project,MExp.failAlways]
      | cons d rest =>
        rw [hx] at hl
        have hn : rest.length≠p := by simp only [List.length_cons] at hl; omega
        cases h : Shallot.beqChar c d <;> simp [SequentialResultSyntax.zero,evV,hx,h,project,hn,MExp.failAlways]
    | .range a b,_,p,hp => by
      have hl := length_sfx x hp
      cases hx : sfx x p with
      | nil => simp [SequentialResultSyntax.zero,evV,hx,project,MExp.failAlways]
      | cons d rest =>
        rw [hx] at hl
        have hn : rest.length≠p := by simp only [List.length_cons] at hl; omega
        cases h : (Shallot.leChar a d && Shallot.leChar d b) <;> simp [SequentialResultSyntax.zero,evV,hx,h,project,hn,MExp.failAlways]
    | .lit w,_,p,hp => by
      by_cases hw : w=[]
      · subst w; simp [SequentialResultSyntax.zero,evV,Shallot.stripPrefix?,length_sfx x hp,project]
      · simp only [SequentialResultSyntax.zero,if_neg hw,MExp.failAlways,evV]
        cases hh : Shallot.stripPrefix? w (sfx x p) with
        | none => rfl
        | some rest =>
          have he := congrArg List.length ((CBVtoCBN.stripPrefix_exact _ _ _).mp hh)
          rw [length_sfx x hp,List.length_append] at he
          have hn : 0<w.length := List.length_pos_iff.mpr hw
          simp only [project,if_neg (show rest.length≠p by omega)]
    | .dbg _,he,_,_ | .lam _ _,he,_,_ | .callParam _ _,he,_,_ | .invoke _ _ _,he,_,_ => False.elim he

  theorem zero_args_success (g : MGrammar) (x : List Char) (T U : Table)
      (rows : Rows g x T U) (ht : OkTV x.length T) (hd : SequentialClock.Descending T)
      (E : List (List Char)) : ∀ args, MExp.FirstOrderArgs args → ∀ p, p≤x.length → ∀ W q,
      evSeqArgs g x .callByValueSeq T E args p=some (some (W,q)) →
      evV (target g) x .callByValueSeq U E (zeroArgs args) p=
        if q=p then some (some p) else some none
    | [],_,p,_,W,q,h => by cases h; simp [zeroArgs,evV]
    | a::args,he,p,hp,W,q,h => by
      cases ha : evV g x .callByValueSeq T E a p with
      | none => simp [evSeqArgs,ha] at h
      | some v => cases v with
        | none => simp [evSeqArgs,ha] at h
        | some j =>
          cases htargs : evSeqArgs g x .callByValueSeq T E args j with
          | none => simp [evSeqArgs,ha,htargs] at h
          | some v => cases v with
            | none => simp [evSeqArgs,ha,htargs] at h
            | some pair =>
              obtain ⟨V,r⟩ := pair
              have heq : (pre x p j::V,r)=(W,q) := by simpa only [evSeqArgs,ha,htargs,Option.some.injEq] using h
              have hrq : r=q := congrArg Prod.snd heq
              subst q
              have hz := (zero_eval g x T U rows ht hd E a he.1 p hp).trans (congrArg (project p) ha)
              have hj := SequentialClock.expression_descending hd E a p j ha
              by_cases hsame : j=p
              · subst j
                simp only [project] at hz
                rw [zeroArgs,evV_seq_ok hz]
                exact zero_args_success g x T U rows ht hd E args he.2 p hp V r htargs
              · simp only [project,if_neg hsame] at hz
                rw [zeroArgs,evV_seq_fail hz]
                have hr := (SequentialClock.arguments_metadata hd E args j V r htargs).1
                rw [if_neg (show r≠p by omega)]
end

end Shallot.MacroPeg.CBV.SequentialResultZero
