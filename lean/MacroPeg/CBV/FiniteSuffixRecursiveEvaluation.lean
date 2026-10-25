import MacroPeg.CBV.FiniteSuffixRecursiveSelection

namespace Shallot.MacroPeg.CBV.FiniteSuffixRecursiveEvaluation
open FiniteSuffixRecursiveSyntax FiniteSuffixRecursiveHelpers FiniteSuffixRecursiveSelection
open FiniteSuffixReplay (views)
open RegularCaptureProduct (Node)
abbrev Spec := FiniteSuffixRecursiveSyntax.Rule
abbrev Term := FiniteSuffixRecursiveSyntax.Expr

/-- User rows cover every retained tuple of the declared arity, including
arbitrary long values in the same other class. -/
def Rows (nodes : List Node) (R : List (List Char)) (rs : List Spec) (x : List Char) (k : Nat) : Prop :=
  ∀ i r, rs[i]?=some r → ∀ E, E.length=r.arity → ∀ p, p≤x.length →
    valAt (sourceTable nodes R rs x k (nodes.length+i) E) p=
      valAt (targetTable nodes R rs x k (address nodes R rs i (views R E)) []) p

theorem call_eq (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (x : List Char) (k : Nat) (rows : Rows nodes R rs x k) (E : List (List Char)) (i : Nat) (ids : List Nat)
    (p : Nat) (hp : p≤x.length) :
    evV (source nodes R rs) x .callByValuePar (sourceTable nodes R rs x k) E (render nodes R rs none (.user i ids)) p=
      evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (render nodes R rs (some (views R E)) (.user i ids)) p := by
  by_cases hc : permitted nodes.length rs i ids=true
  · obtain ⟨r,hr,ha,hi⟩ := permitted_checked nodes.length rs i ids hc
    simp only [render,hc,if_true]
    rw [evV_call_par (source_rule nodes R rs i r hr) (by simpa using ha) (by decide),
      gather_at nodes hn R rs x k ids hi p hp,
      arguments_eq nodes hn R rs x k E p hp ids hi]
    cases hv : evParArgs (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (ids.map (fun j => .call j [])) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some W =>
        have hl : W.length=r.arity := by simpa only [List.length_map,ha] using evPar_length _ W hv
        have ht := target_rule nodes R rs i r hr W hl
        dsimp only []
        rw [evV_call_seq ht (args := []) rfl]
        exact rows i r hr W hl p hp
  · simp [render,hc,MExp.failAlways,evV]

/-- Parent specialization is lexical in the target expression, so it is
restored after nested user calls without reusing the child's view. -/
theorem evaluator (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (x : List Char) (k : Nat) (rows : Rows nodes R rs x k) (E : List (List Char)) :
    ∀ (e : Term) p, p≤x.length →
    evV (source nodes R rs) x .callByValuePar (sourceTable nodes R rs x k) E (render nodes R rs none e) p=
      evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (render nodes R rs (some (views R E)) e) p
  | .user i ids,p,hp => call_eq nodes hn R rs x k rows E i ids p hp
  | .helper i,p,hp => by
    by_cases hi : i<nodes.length
    · simp only [render,if_pos hi]; exact helper_eq nodes hn R rs x k E i p hi hp
    · simp [render,hi,MExp.failAlways,evV]
  | .replay i,p,hp => FiniteSuffixReplay.replay_eval _ _ x _ _ _ _ E R i p hp
  | .seq a b,p,hp => by
    have ha := evaluator nodes hn R rs x k rows E a p hp
    cases he : evV (source nodes R rs) x .callByValuePar (sourceTable nodes R rs x k) E (render nodes R rs none a) p with
    | none => simp only [render,evV_seq_none he,evV_seq_none (ha.symm.trans he)]
    | some v => cases v with
      | none => simp only [render,evV_seq_fail he,evV_seq_fail (ha.symm.trans he)]
      | some j =>
        simp only [render,evV_seq_ok he,evV_seq_ok (ha.symm.trans he)]
        exact evaluator nodes hn R rs x k rows E b j (evV_ok (source_ok nodes R rs x k) _ p hp j he)
  | .alt a b,p,hp => by
    have ha := evaluator nodes hn R rs x k rows E a p hp
    cases he : evV (source nodes R rs) x .callByValuePar (sourceTable nodes R rs x k) E (render nodes R rs none a) p with
    | none => simp only [render,evV_alt_none he,evV_alt_none (ha.symm.trans he)]
    | some v => cases v with
      | none =>
        simp only [render,evV_alt_fail he,evV_alt_fail (ha.symm.trans he)]
        exact evaluator nodes hn R rs x k rows E b p hp
      | some j => simp only [render,evV_alt_ok he,evV_alt_ok (ha.symm.trans he)]
  | .notP a,p,hp => by simp only [render,evV,evaluator nodes hn R rs x k rows E a p hp]
  | .star a,p,hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator nodes hn R rs x k rows E a q (by omega))
  | .eps,_,_ | .any,_,_ | .chr _,_,_ | .range _ _,_,_ | .lit _,_,_ => rfl

/-- The independent helper clocks may differ, but the genuine user stages
advance together. This is not a same-physical-clock claim. -/
theorem rows_related (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (x : List Char) (k : Nat) : Rows nodes R rs x k := by
  induction k with
  | zero =>
    intro i r hr E he p hp
    have hs : RecursiveParserStability.pick (sourceBodies nodes) (nodes.length+i)=false := by
      simp [RecursiveParserStability.pick,sourceBodies]
    have ht : RecursiveParserStability.pick (targetBodies nodes R) (address nodes R rs i (views R E))=false := by
      simp [RecursiveParserStability.pick,targetBodies,RegularCaptureProduct.component,address]
    simp only [sourceTable,targetTable,RecursiveParserStability.frozen,ClockFreezing.frozen,
      hs,ht,Bool.false_eq_true,if_false,valAt_nil]
  | succ k ih =>
    intro i r hr E he p hp
    have hs : RecursiveParserStability.pick (sourceBodies nodes) (nodes.length+i)=false := by
      simp [RecursiveParserStability.pick,sourceBodies]
    have ht : RecursiveParserStability.pick (targetBodies nodes R) (address nodes R rs i (views R E))=false := by
      simp [RecursiveParserStability.pick,targetBodies,RegularCaptureProduct.component,address]
    have htRule := target_rule nodes R rs i r hr E he
    rw [ClockFreezing.frozen_user_step _ x .callByValuePar _ _ k (nodes.length+i) hs _ (source_rule nodes R rs i r hr) E p hp,
      ClockFreezing.frozen_user_step _ x .callByValueSeq _ _ k _ ht _ htRule [] p hp]
    exact evaluator nodes hn R rs x k ih E r.body p hp

theorem frozen_equality (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (x : List Char) (k : Nat) (e : Term) (p : Nat) (hp : p≤x.length) :
    evV (source nodes R rs) x .callByValuePar (sourceTable nodes R rs x k) [] (render nodes R rs none e) p=
      evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (render nodes R rs (some []) e) p := by
  simpa only [views,List.map_nil] using evaluator nodes hn R rs x k (rows_related nodes hn R rs x k) [] e p hp

end Shallot.MacroPeg.CBV.FiniteSuffixRecursiveEvaluation
