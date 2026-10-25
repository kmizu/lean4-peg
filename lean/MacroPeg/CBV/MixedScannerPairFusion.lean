import MacroPeg.CBV.ScannerPairFusion

namespace Shallot.MacroPeg.CBV.MixedScannerPairFusion
open NestedScannerArguments ScannerFrontier

/-- Nullary recursive helpers coexist with two-capture users. -/
structure Entry where
  pairing : Option (List Char × List Char)
  tail : MExp

def arity (r : Entry) := if r.pairing.isSome then 2 else 0

def render (es : List Entry) (parallel : Bool) : MExp → MExp
  | .call i [] => match es[i]? with
    | none => MExp.failAlways
    | some r => match r.pairing with
      | none => .call (if parallel then i else 2*i) []
      | some (A,B) => if parallel then .call i [scan A,scan B] else dispatch A B (2*i) (2*i+1)
  | .call _ (_::_) => MExp.failAlways
  | .seq a b => .seq (render es parallel a) (render es parallel b)
  | .alt a b => .alt (render es parallel a) (render es parallel b)
  | .star a => .star (render es parallel a)
  | .notP a => .notP (render es parallel a)
  | .param k => .param k
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

theorem render_firstOrder (es : List Entry) (parallel : Bool) : ∀ e, (render es parallel e).FirstOrder
  | .call i [] => by
    simp only [render]
    cases hr : es[i]? with
    | none => trivial
    | some r =>
      simp only [hr]
      cases hc : r.pairing with
      | none => trivial
      | some pair =>
        obtain ⟨A,B⟩ := pair
        simp only [hc]
        cases parallel with
        | false => exact dispatch_firstOrder _ _ _ _
        | true => exact ⟨scan_firstOrder A,scan_firstOrder B,True.intro⟩
  | .call _ (_::_) => trivial
  | .seq a b | .alt a b => ⟨render_firstOrder es parallel a,render_firstOrder es parallel b⟩
  | .star a | .notP a => render_firstOrder es parallel a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

def sourceBody (es : List Entry) (r : Entry) : MExp := match r.pairing with
  | none => render es true r.tail
  | some (A,B) => RootObservation.branch (guard A B)
      (.seq (.param 1) (render es true r.tail)) (.seq (.param 0) (render es true r.tail))
def sourceRule (es : List Entry) (r : Entry) : MRule := ⟨arity r,sourceBody es r⟩
def targetRule (es : List Entry) (first : Bool) (r : Entry) : MRule :=
  ⟨arity r,match r.pairing with
    | none => render es false r.tail
    | some _ => body first (render es false r.tail)⟩
def parGrammar (es : List Entry) : MGrammar := ⟨es.map (sourceRule es)⟩
def seqGrammar (es : List Entry) : MGrammar := ⟨es.flatMap (fun r => [targetRule es true r,targetRule es false r])⟩

theorem par_rule (es : List Entry) (i : Nat) : ruleAtM (parGrammar es).rules i=(es[i]?).map (sourceRule es) := by
  simp [parGrammar,ruleAtM_eq_getElem?]

private theorem pair_lookup (entries es : List Entry) (first : Bool) (i : Nat) :
    (entries.flatMap (fun r => [targetRule es true r,targetRule es false r]))[2*i+(if first then 0 else 1)]?=
      (entries[i]?).map (targetRule es first) := by
  induction entries generalizing i with
  | nil => simp
  | cons r entries ih =>
    cases i with
    | zero => cases first <;> rfl
    | succ i =>
      rw [show 2*(i+1)+(if first then 0 else 1)=(2*i+(if first then 0 else 1))+2 by omega]
      simpa only [List.flatMap_cons,List.cons_append,List.nil_append,List.getElem?_cons_succ,
        List.getElem?_cons_zero,Nat.add_succ,Nat.add_zero] using ih i

theorem seq_rule (es : List Entry) (first : Bool) (i : Nat) :
    ruleAtM (seqGrammar es).rules (2*i+(if first then 0 else 1))=(es[i]?).map (targetRule es first) := by
  simpa only [seqGrammar,ruleAtM_eq_getElem?] using pair_lookup es es first i

theorem par_firstOrder (es : List Entry) : (parGrammar es).FirstOrder := by
  intro r hr
  obtain ⟨a,ha,he⟩ := List.mem_map.mp hr
  subst r
  dsimp only [sourceRule,sourceBody]
  cases a.pairing with
  | none => exact render_firstOrder _ _ _
  | some pair => obtain ⟨A,B⟩ := pair; exact ⟨⟨guard_firstOrder _ _,⟨trivial,render_firstOrder _ _ _⟩⟩,
      ⟨guard_firstOrder _ _,⟨trivial,render_firstOrder _ _ _⟩⟩⟩

theorem seq_firstOrder (es : List Entry) : (seqGrammar es).FirstOrder := by
  intro r hr
  obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp hr
  have hh (first : Bool) : (targetRule es first a).body.FirstOrder := by
    dsimp only [targetRule]
    cases a.pairing with
    | none => exact render_firstOrder _ _ _
    | some pair => exact body_firstOrder _ _ (render_firstOrder _ _ _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl <;> exact hh _

def Related (es : List Entry) (x : List Char) (T U : (Nat → List (List Char) → Val)) : Prop :=
  ∀ (i : Nat) (r : Entry), es[i]?=some r → match r.pairing with
    | none => ∀ p, p≤x.length → valAt (T i []) p=valAt (U (2*i) []) p
    | some (A,B) => ∀ first u v p q, p≤x.length → q≤x.length → sfx x p=(u++v)++sfx x q →
        firstStops A B (sfx x p)=first → valAt (T i (restore first u v)) p=
          valAt (U (2*i+(if first then 0 else 1)) [u,v]) q

theorem evaluator_of_rows {es : List Entry} {x : List Char} {T U : (Nat → List (List Char) → Val)}
    (hok : OkTV x.length T) (hrel : Related es x T U) : ∀ e E p, p≤x.length →
    evV (parGrammar es) x .callByValuePar T E (render es true e) p=
      evV (seqGrammar es) x .callByValueSeq U E (render es false e) p
  | .call i [],E,p,hp => by
    cases hr : es[i]? with
    | none => simp [render,hr,evV,MExp.failAlways]
    | some r =>
      have hs : ruleAtM (parGrammar es).rules i=some (sourceRule es r) := by rw [par_rule,hr]; rfl
      have hl : ruleAtM (seqGrammar es).rules (2*i)=some (targetRule es true r) := by
        simpa only [if_true,Nat.add_zero,hr,Option.map_some] using seq_rule es true i
      have ht : ruleAtM (seqGrammar es).rules (2*i+1)=some (targetRule es false r) := by
        simpa only [Bool.false_eq_true,if_false,hr,Option.map_some] using seq_rule es false i
      cases hc : r.pairing with
      | none =>
        simp only [render,hr,hc,if_true,Bool.false_eq_true,if_false]
        rw [evV_call_par hs (by simp [sourceRule,arity,hc]) (by decide),evV_call_seq hl (by simp [targetRule,arity,hc])]
        simpa only [evParArgs,evSeqArgs] using (show ∀ p, p≤x.length → valAt (T i []) p=valAt (U (2*i) []) p from by
          simpa only [hc] using hrel i r hr) p hp
      | some pair =>
        obtain ⟨A,B⟩ := pair
        simp only [render,hr,hc,if_true,Bool.false_eq_true,if_false]
        apply call_of_body_relation T U E E A B i (2*i) (2*i+1) _ _ _ hs hl ht
          (by simp [sourceRule,arity,hc]) (by simp [targetRule,arity,hc]) (by simp [targetRule,arity,hc]) p hp
        have hh := hrel i r hr
        simp only [hc] at hh
        have hq := Nat.le_trans (finalPos_le A B x p hp) (commonPos_le A B x p hp)
        have hbody := hh (firstStops A B (sfx x p)) (pre x p (commonPos A B x p))
          (pre x (commonPos A B x p) (finalPos A B x p)) p (finalPos A B x p) hp
          (Nat.le_trans hq hp) (ScannerPairFusion.chunks_split A B x p hp) rfl
        cases hf : firstStops A B (sfx x p) <;> simpa only [hf,chunks,if_true,Bool.false_eq_true,if_false,Nat.add_zero] using hbody
  | .seq a b,E,p,hp => by
    have hh := evaluator_of_rows hok hrel a E p hp
    cases ha : evV (parGrammar es) x .callByValuePar T E (render es true a) p with
    | none => simp only [render,evV_seq_none ha,evV_seq_none (hh.symm.trans ha)]
    | some v => cases v with
      | none => simp only [render,evV_seq_fail ha,evV_seq_fail (hh.symm.trans ha)]
      | some j =>
        simp only [render,evV_seq_ok ha,evV_seq_ok (hh.symm.trans ha)]
        exact evaluator_of_rows hok hrel b E j (evV_ok hok _ p hp j ha)
  | .alt a b,E,p,hp => by
    have hh := evaluator_of_rows hok hrel a E p hp
    cases ha : evV (parGrammar es) x .callByValuePar T E (render es true a) p with
    | none => simp only [render,evV_alt_none ha,evV_alt_none (hh.symm.trans ha)]
    | some v => cases v with
      | none => simp only [render,evV_alt_fail ha,evV_alt_fail (hh.symm.trans ha)]; exact evaluator_of_rows hok hrel b E p hp
      | some j => simp only [render,evV_alt_ok ha,evV_alt_ok (hh.symm.trans ha)]
  | .notP a,E,p,hp => by simp only [render,evV]; rw [evaluator_of_rows hok hrel a E p hp]
  | .star a,E,p,hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_rows hok hrel a E q (by omega))
  | .call _ (_::_),_,_,_ | .eps,_,_,_ | .any,_,_,_ | .chr _,_,_,_ | .range _ _,_,_,_
  | .lit _,_,_,_ | .param _,_,_,_ | .dbg _,_,_,_ | .lam _ _,_,_,_ | .invoke _ _ _,_,_,_ | .callParam _ _,_,_,_ => rfl

theorem tables_related (es : List Entry) (x : List Char) (k : Nat) :
    Related es x (tblV (parGrammar es) x .callByValuePar k) (tblV (seqGrammar es) x .callByValueSeq k) := by
  induction k with
  | zero =>
    intro i r hr
    cases r.pairing with
    | none => intro p hp; rfl
    | some pair =>
      obtain ⟨A,B⟩ := pair
      intro first u v p q hp hq hs hf
      rfl
  | succ k ih =>
    intro i r hr
    have hs : ruleAtM (parGrammar es).rules i=some (sourceRule es r) := by rw [par_rule,hr]; rfl
    cases hc : r.pairing with
    | none =>
      intro p hp
      have ht : ruleAtM (seqGrammar es).rules (2*i)=some (targetRule es true r) := by
        simpa only [if_true,Nat.add_zero,hr,Option.map_some] using seq_rule es true i
      rw [valAt_tblV_succ hs [] hp,valAt_tblV_succ ht [] hp]
      simpa only [sourceRule,sourceBody,targetRule,hc] using evaluator_of_rows (tblV_ok _ _ _ k) ih r.tail [] p hp
    | some pair =>
      obtain ⟨A,B⟩ := pair
      intro first u v p q hp hq hsplit hf
      have ht : ruleAtM (seqGrammar es).rules (2*i+(if first then 0 else 1))=some (targetRule es first r) := by rw [seq_rule,hr]; rfl
      rw [valAt_tblV_succ hs _ hp,valAt_tblV_succ ht _ hq]
      change evV _ _ _ _ (restore first u v) (sourceBody es r) p=evV _ _ _ _ [u,v] (targetRule es first r).body q
      simp only [sourceBody,targetRule,hc]
      rw [body_eval _ _ _ _ first u v _ (render_firstOrder _ _ _) q]
      rw [branch_eval _ _ _ p _ (guard_eval _ _ _ _ _ A B p hp),hf]
      have hstrip := (CBVtoCBN.stripPrefix_exact (u++v) (sfx x p) (sfx x q)).mpr hsplit
      have he := evaluator_of_rows (tblV_ok _ _ _ k) ih r.tail (restore first u v) q hq
      cases first <;> simpa only [restore,if_true,Bool.false_eq_true,if_false,evV,
        List.getElem?_cons_zero,List.getElem?_cons_succ,hstrip,length_sfx x hq] using he

theorem evaluator_eq (es : List Entry) (x : List Char) (k : Nat) (e : MExp) :
    evV (parGrammar es) x .callByValuePar (tblV (parGrammar es) x .callByValuePar k) [] (render es true e) x.length=
      evV (seqGrammar es) x .callByValueSeq (tblV (seqGrammar es) x .callByValueSeq k) [] (render es false e) x.length :=
  evaluator_of_rows (tblV_ok _ _ _ k) (tables_related es x k) e [] x.length (Nat.le_refl _)

theorem observations_iff (es : List Entry) (e : MExp) (x : List Char) (rest : Option (List Char)) :
    SObs (parGrammar es) .callByValuePar (render es true e) x rest ↔
      SObs (seqGrammar es) .callByValueSeq (render es false e) x rest := by
  rw [←decideObsV_iff (par_firstOrder es) (by decide) (render_firstOrder es true e),
    ←decideObsV_iff (seq_firstOrder es) (by decide) (render_firstOrder es false e)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => evaluator_eq es x k e)]

end Shallot.MacroPeg.CBV.MixedScannerPairFusion
