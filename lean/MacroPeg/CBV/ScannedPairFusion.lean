import MacroPeg.CBV.MixedScannerPairFusion

namespace Shallot.MacroPeg.CBV.ScannedPairFusion
open NestedScannerArguments ScannerFrontier
open MixedScannerPairFusion (Entry arity render render_firstOrder targetRule seqGrammar seq_rule seq_firstOrder)

/-- An actual closed parser for the longer independent scanner prefix.
No retained parameter occurs in this expression. -/
def maxScanner (A B : List Char) : MExp := RootObservation.branch (guard A B) (scan B) (scan A)

theorem maxScanner_firstOrder (A B : List Char) : (maxScanner A B).FirstOrder :=
  ⟨⟨guard_firstOrder _ _,scan_firstOrder _⟩,⟨guard_firstOrder _ _,scan_firstOrder _⟩⟩

theorem maxScanner_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (A B : List Char)
    (p : Nat) (hp : p≤x.length) :
    evV g x s T E (maxScanner A B) p=some (some (finalPos A B x p)) := by
  rw [maxScanner,branch_eval _ _ _ p _ (guard_eval g x s T E A B p hp)]
  cases hf : firstStops A B (sfx x p) <;>
    simp only [hf,Bool.false_eq_true,if_false,if_true,finalPos,lastClass,remainder,scan_eval g x s T E _ p hp]

def sourceBody (es : List Entry) (r : Entry) : MExp := match r.pairing with
  | none => render es true r.tail
  | some (A,B) => .seq (maxScanner A B) (render es true r.tail)
def sourceRule (es : List Entry) (r : Entry) : MRule := ⟨arity r,sourceBody es r⟩
def parGrammar (es : List Entry) : MGrammar := ⟨es.map (sourceRule es)⟩

theorem par_rule (es : List Entry) (i : Nat) : ruleAtM (parGrammar es).rules i=(es[i]?).map (sourceRule es) := by
  simp [parGrammar,ruleAtM_eq_getElem?]

theorem par_firstOrder (es : List Entry) : (parGrammar es).FirstOrder := by
  intro r hr
  obtain ⟨a,ha,he⟩ := List.mem_map.mp hr
  subst r
  dsimp only [sourceRule,sourceBody]
  cases a.pairing with
  | none => exact render_firstOrder _ _ _
  | some pair => exact ⟨maxScanner_firstOrder _ _,render_firstOrder _ _ _⟩

/-- Pair rows are related at the endpoints derived from actual scanner
arguments, rather than at arbitrary hypothetical replay alignments. -/
def Related (es : List Entry) (x : List Char) (T U : Nat → List (List Char) → Val) : Prop :=
  ∀ (i : Nat) (r : Entry), es[i]?=some r → match r.pairing with
    | none => ∀ p, p≤x.length → valAt (T i []) p=valAt (U (2*i) []) p
    | some (A,B) => ∀ p, p≤x.length →
        valAt (T i (restore (firstStops A B (sfx x p)) (pre x p (commonPos A B x p))
          (pre x (commonPos A B x p) (finalPos A B x p)))) p=
        valAt (U (2*i+(if firstStops A B (sfx x p) then 0 else 1)) (chunks A B x p)) (finalPos A B x p)

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
        have hbody := hh p hp
        cases hf : firstStops A B (sfx x p) <;>
          simpa only [hf,chunks,if_true,Bool.false_eq_true,if_false,Nat.add_zero] using hbody

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
    | some pair => obtain ⟨A,B⟩ := pair; intro p hp; rfl
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
      intro p hp
      let first := firstStops A B (sfx x p)
      let u := pre x p (commonPos A B x p)
      let v := pre x (commonPos A B x p) (finalPos A B x p)
      let q := finalPos A B x p
      have hq : q≤x.length := Nat.le_trans (finalPos_le A B x p hp)
        (Nat.le_trans (commonPos_le A B x p hp) hp)
      have ht : ruleAtM (seqGrammar es).rules (2*i+(if first then 0 else 1))=some (targetRule es first r) := by rw [seq_rule,hr]; rfl
      change valAt (tblV (parGrammar es) x .callByValuePar (k+1) i (restore first u v)) p=
        valAt (tblV (seqGrammar es) x .callByValueSeq (k+1) (2*i+(if first then 0 else 1)) [u,v]) q
      rw [valAt_tblV_succ hs _ hp,valAt_tblV_succ ht _ hq]
      change evV _ _ _ _ (restore first u v) (sourceBody es r) p=evV _ _ _ _ [u,v] (targetRule es first r).body q
      simp only [sourceBody,targetRule,hc]
      rw [evV_seq_ok (maxScanner_eval _ x .callByValuePar _ (restore first u v) A B p hp)]
      rw [body_eval _ _ _ _ first u v _ (render_firstOrder _ _ _) q]
      exact evaluator_of_rows (tblV_ok _ _ _ k) ih r.tail (restore first u v) q hq

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

end Shallot.MacroPeg.CBV.ScannedPairFusion
