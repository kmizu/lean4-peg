import MacroPeg.CBV.FrozenPairArguments

/-! A recursive reverse compiler for replay-shaped finite-state scanner pairs.
Both machines are fixed in the grammar; rule specifications choose initial
states. Captures and observations remain on the original character input. -/
namespace Shallot.MacroPeg.CBV.StatefulPairFusion
open StatefulScanner StatefulScannerProduct StatefulPairArguments
open StatefulScannerStability (helperCount helpers frozen)
open ScannerFrontier (restore body body_eval body_firstOrder)

structure Spec (n m : Nat) where
  left : Fin n
  right : Fin m
  tail : MExp

def replay {n m : Nat} (A : Machine n) (a : Fin n) (b : Fin m) (e : MExp) :
    List (Control n m) → MExp
  | [] => MExp.failAlways
  | (c,d,first)::rest => RootObservation.branch (caseGuard A a c b d first)
      (.seq (.param (if first then 1 else 0)) e) (replay A a b e rest)

theorem replay_firstOrder {n m : Nat} (A : Machine n) (a : Fin n) (b : Fin m)
    (e : MExp) (he : e.FirstOrder) (cs : List (Control n m)) :
    (replay A a b e cs).FirstOrder := by
  induction cs with
  | nil => trivial
  | cons control rest ih =>
    obtain ⟨c,d,first⟩ := control
    exact ⟨⟨caseGuard_firstOrder _ _ _ _ _ _,⟨True.intro,he⟩⟩,
      ⟨caseGuard_firstOrder _ _ _ _ _ _,ih⟩⟩

theorem replay_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (tail : List MRule) (x : List Char) (s : Strategy) (k : Nat) (E : List (List Char))
    (a : Fin n) (b : Fin m) (e : MExp) (cs : List (Control n m)) (p : Nat)
    (hp : p ≤ x.length) (hmem : actual A B a b (sfx x p) ∈ cs) :
    evV (grammar A B hm tail) x s (frozen A B hm tail x s k) E (replay A a b e cs) p =
      evV (grammar A B hm tail) x s (frozen A B hm tail x s k) E
        (.seq (.param (if firstStops A B a b (sfx x p) then 1 else 0)) e) p := by
  induction cs with
  | nil => cases hmem
  | cons control rest ih =>
    obtain ⟨c,d,first⟩ := control
    rw [replay,ScannerFrontier.branch_eval _ _ _ p (decide (GoodCase A B a c b d first (sfx x p)))
      (by simpa only [decide_eq_true_eq] using
        FrozenPairArguments.caseGuard_eval A B hm tail x s E a c b d first p k hp)]
    simp only [decide_eq_true_eq]
    by_cases hg : GoodCase A B a c b d first (sfx x p)
    · rw [if_pos hg,hg.2]
    · rw [if_neg hg]
      apply ih
      rcases List.mem_cons.mp hmem with h | h
      · exact False.elim (hg ((goodCase_iff_eq A B a c b d first (sfx x p)).mpr h.symm))
      · exact h

def render {n m : Nat} (A : Machine n) (specs : List (Spec n m)) (parallel : Bool) : MExp → MExp
  | .call i [] => match specs[i]? with
    | none => MExp.failAlways
    | some r => if parallel then
        .call (helperCount n m+i) [leftEntry (m := m) r.left,rightEntry (n := n) r.right]
      else dispatch A r.left r.right
        (fun control => helperCount n m+2*i+(if control.2.2 then 0 else 1)) (controls n m)
  | .call _ (_::_) => MExp.failAlways
  | .param k => .param k
  | .seq a b => .seq (render A specs parallel a) (render A specs parallel b)
  | .alt a b => .alt (render A specs parallel a) (render A specs parallel b)
  | .star a => .star (render A specs parallel a)
  | .notP a => .notP (render A specs parallel a)
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit w => .lit w
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

theorem render_firstOrder {n m : Nat} (A : Machine n) (specs : List (Spec n m)) (parallel : Bool) :
    ∀ e, (render A specs parallel e).FirstOrder
  | .call i [] => by
    simp only [render]
    cases specs[i]? with
    | none => trivial
    | some r => cases parallel <;> first | exact dispatch_firstOrder _ _ _ _ _ | trivial
  | .call _ (_::_) => trivial
  | .seq a b | .alt a b => ⟨render_firstOrder A specs parallel a,render_firstOrder A specs parallel b⟩
  | .star a | .notP a => render_firstOrder A specs parallel a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

def sourceBody {n m : Nat} (A : Machine n) (specs : List (Spec n m)) (r : Spec n m) : MExp :=
  replay A r.left r.right (render A specs true r.tail) (controls n m)

def parTail {n m : Nat} (A : Machine n) (specs : List (Spec n m)) : List MRule :=
  specs.map (fun r => ⟨2,sourceBody A specs r⟩)

def targetRule {n m : Nat} (A : Machine n) (specs : List (Spec n m)) (first : Bool) (r : Spec n m) : MRule :=
  ⟨2,body first (render A specs false r.tail)⟩

def seqTail {n m : Nat} (A : Machine n) (specs : List (Spec n m)) : List MRule :=
  specs.flatMap (fun r => [targetRule A specs true r,targetRule A specs false r])

def parGrammar {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (specs : List (Spec n m)) : MGrammar :=
  grammar A B hm (parTail A specs)

def seqGrammar {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (specs : List (Spec n m)) : MGrammar :=
  grammar A B hm (seqTail A specs)

theorem user_rule {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (tail : List MRule) (i : Nat) :
    ruleAtM (grammar A B hm tail).rules (helperCount n m+i) = ruleAtM tail i := by
  rw [ruleAtM_eq_getElem?,ruleAtM_eq_getElem?]
  simp only [StatefulPairArguments.grammar]
  rw [List.getElem?_append_right (by simp [StatefulScannerFamily.grammar_length,helperCount,commonSize]; omega)]
  rw [List.getElem?_append_right (by simp [StatefulScannerFamily.grammar_length,block_length,helperCount,commonSize]; omega)]
  rw [List.getElem?_append_right (by simp [StatefulScannerFamily.grammar_length,block_length,helperCount,commonSize]; omega)]
  congr 1
  simp only [StatefulScannerFamily.grammar_length,block_length,helperCount,commonSize]
  omega

theorem par_rule {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (specs : List (Spec n m)) (i : Nat) :
    ruleAtM (parGrammar A B hm specs).rules (helperCount n m+i) =
      (specs[i]?).map (fun r => ⟨2,sourceBody A specs r⟩) := by
  rw [parGrammar,user_rule]
  simp [parTail,ruleAtM_eq_getElem?]

private theorem pair_lookup {n m : Nat} (A : Machine n) (entries all : List (Spec n m)) (first : Bool) (i : Nat) :
    (entries.flatMap (fun r => [targetRule A all true r,targetRule A all false r]))[2*i + (if first then 0 else 1)]? =
      (entries[i]?).map (targetRule A all first) := by
  induction entries generalizing i with
  | nil => simp
  | cons r entries ih =>
    cases i with
    | zero => cases first <;> rfl
    | succ i =>
      have hn : 2*(i+1)+(if first then 0 else 1) = (2*i+(if first then 0 else 1))+2 := by omega
      rw [hn]
      simpa only [List.flatMap_cons,List.cons_append,List.nil_append,
        List.getElem?_cons_succ,List.getElem?_cons_zero,Nat.add_succ,Nat.add_zero] using ih i

theorem seq_rule {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (specs : List (Spec n m)) (first : Bool) (i : Nat) :
    ruleAtM (seqGrammar A B hm specs).rules (helperCount n m+2*i+(if first then 0 else 1)) =
      (specs[i]?).map (targetRule A specs first) := by
  rw [seqGrammar,Nat.add_assoc,user_rule,ruleAtM_eq_getElem?]
  exact pair_lookup A specs specs first i

theorem par_firstOrder {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (specs : List (Spec n m)) : (parGrammar A B hm specs).FirstOrder := by
  apply StatefulPairArguments.grammar_firstOrder
  intro r hr
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
  exact replay_firstOrder _ _ _ _ (render_firstOrder _ _ _ _) _

theorem seq_firstOrder {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (specs : List (Spec n m)) : (seqGrammar A B hm specs).FirstOrder := by
  apply StatefulPairArguments.grammar_firstOrder
  intro r hr
  obtain ⟨r,_,hmem⟩ := List.mem_flatMap.mp hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with rfl | rfl <;> exact body_firstOrder _ _ (render_firstOrder _ _ _ _)


theorem chunks_split {n m : Nat} (A : Machine n) (B : Machine m) (a : Fin n) (b : Fin m)
    (x : List Char) (p : Nat) (hp : p ≤ x.length) :
    sfx x p = (pre x p (commonPos A B a b x p) ++
      pre x (commonPos A B a b x p) (finalPos A B a b (firstStops A B a b (sfx x p)) x p)) ++
        sfx x (finalPos A B a b (firstStops A B a b (sfx x p)) x p) := by
  have hc := common_bound A B a b x p hp
  have hq := final_bound A B a b (firstStops A B a b (sfx x p)) x p
  have hs (q : Nat) (hq : q ≤ p) : sfx x q = (sfx x p).drop (p-q) := by
    simp only [sfx,List.drop_drop]
    congr 1
    omega
  rw [← ScannerFrontier.pre_concat x p _ _ hp hc hq,hs _ (Nat.le_trans hq hc)]
  exact (List.take_append_drop _ _).symm

abbrev parTable {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (specs : List (Spec n m)) (x : List Char) (k : Nat) :=
  frozen A B hm (parTail A specs) x .callByValuePar k

abbrev seqTable {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (specs : List (Spec n m)) (x : List Char) (k : Nat) :=
  frozen A B hm (seqTail A specs) x .callByValueSeq k

def Shifted {n m : Nat} (A : Machine n) (B : Machine m) (specs : List (Spec n m)) (x : List Char)
    (T U : ClockFreezing.Table) : Prop :=
  ∀ i r, specs[i]? = some r → ∀ first u v p q,
    p ≤ x.length → q ≤ x.length → sfx x p = (u++v) ++ sfx x q →
    firstStops A B r.left r.right (sfx x p) = first →
    valAt (T (helperCount n m+i) (restore first u v)) p =
      valAt (U (helperCount n m+2*i+(if first then 0 else 1)) [u,v]) q

theorem evaluator_of_shift {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (specs : List (Spec n m)) (x : List Char) (k : Nat)
    (hShift : Shifted A B specs x (parTable A B hm specs x k) (seqTable A B hm specs x k)) :
    ∀ e E p, p ≤ x.length →
      evV (parGrammar A B hm specs) x .callByValuePar (parTable A B hm specs x k) E (render A specs true e) p =
        evV (seqGrammar A B hm specs) x .callByValueSeq (seqTable A B hm specs x k) E (render A specs false e) p
  | .param _, _, _, _ | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _
  | .range _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .dbg _, _, _, _ | .lam _ _, _, _, _ | .callParam _ _, _, _, _
  | .invoke _ _ _, _, _, _ | .call _ (_::_), _, _, _ => rfl
  | .call i [], E, p, hp => by
    cases hr : specs[i]? with
    | none => simp [render,hr,evV,MExp.failAlways]
    | some r =>
      have hs : ruleAtM (parGrammar A B hm specs).rules (helperCount n m+i) = some ⟨2,sourceBody A specs r⟩ := by
        rw [par_rule,hr]; rfl
      have valid : ∀ control : Control n m, ∃ rule,
          ruleAtM (seqGrammar A B hm specs).rules
            (helperCount n m+2*i+(if control.2.2 then 0 else 1)) = some rule ∧ rule.arity=2 := by
        intro control
        refine ⟨targetRule A specs control.2.2 r,?_,rfl⟩
        rw [seq_rule,hr]; rfl
      simp only [render,hr,if_true,Bool.false_eq_true,if_false]
      rw [evV_call_par hs rfl (by decide)]
      have hg : GoodCase A B r.left (common A B r.left r.right (sfx x p)).1.1
          r.right (common A B r.left r.right (sfx x p)).1.2
          (firstStops A B r.left r.right (sfx x p)) (sfx x p) := ⟨⟨rfl,rfl⟩,rfl⟩
      unfold parGrammar seqGrammar parTable seqTable
      rw [FrozenPairArguments.capture_reconstruction A B hm (parTail A specs) x .callByValuePar E
        r.left _ r.right _ _ p k hp hg]
      dsimp only []
      rw [FrozenPairArguments.complete_dispatch_eval A B hm (seqTail A specs) x E r.left r.right _ valid p k hp]
      exact hShift i r hr (firstStops A B r.left r.right (sfx x p))
        (pre x p (commonPos A B r.left r.right x p))
        (pre x (commonPos A B r.left r.right x p) (finalPos A B r.left r.right (firstStops A B r.left r.right (sfx x p)) x p))
        p _ hp (Nat.le_trans (final_bound _ _ _ _ _ _ _) (Nat.le_trans (common_bound _ _ _ _ _ _ hp) hp))
        (chunks_split _ _ _ _ _ _ hp) rfl
  | .seq a b, E, p, hp => by
    have heq := evaluator_of_shift A B hm specs x k hShift a E p hp
    cases hv : evV (parGrammar A B hm specs) x .callByValuePar (parTable A B hm specs x k) E (render A specs true a) p with
    | none => simp only [render,evV_seq_none hv,evV_seq_none (heq.symm.trans hv)]
    | some result => cases result with
      | none => simp only [render,evV_seq_fail hv,evV_seq_fail (heq.symm.trans hv)]
      | some q =>
        simp only [render,evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
        exact evaluator_of_shift A B hm specs x k hShift b E q
          (evV_ok (ClockFreezing.frozen_ok _ _ _ _ _ _) _ p hp q hv)
  | .alt a b, E, p, hp => by
    have heq := evaluator_of_shift A B hm specs x k hShift a E p hp
    cases hv : evV (parGrammar A B hm specs) x .callByValuePar (parTable A B hm specs x k) E (render A specs true a) p with
    | none => simp only [render,evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
    | some result => cases result with
      | none =>
        simp only [render,evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
        exact evaluator_of_shift A B hm specs x k hShift b E p hp
      | some q => simp only [render,evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
  | .notP a, E, p, hp => by
    simp only [render,evV]
    rw [evaluator_of_shift A B hm specs x k hShift a E p hp]
  | .star a, E, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift A B hm specs x k hShift a E q (by omega))


/-- The recursive user-table relation follows by induction; no simulation
premise on user calls is left to the caller. -/
theorem tables_shifted {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (specs : List (Spec n m)) (x : List Char) (k : Nat) :
    Shifted A B specs x (parTable A B hm specs x k) (seqTable A B hm specs x k) := by
  induction k with
  | zero =>
    intro i r hr first u v p q hp hq hs hf
    have hleft : helpers n m (helperCount n m+i) = false := by simp [helpers] <;> omega
    have hright : helpers n m (helperCount n m+2*i+(if first then 0 else 1)) = false := by
      simp [helpers]; omega
    simp [parTable,seqTable,StatefulScannerStability.frozen,ClockFreezing.frozen,hleft,hright,valAt_nil]
  | succ k ih =>
    intro i r hr first u v p q hp hq hs hf
    have hpar : ruleAtM (parGrammar A B hm specs).rules (helperCount n m+i) = some ⟨2,sourceBody A specs r⟩ := by
      rw [par_rule,hr]; rfl
    have hseq : ruleAtM (seqGrammar A B hm specs).rules (helperCount n m+2*i+(if first then 0 else 1)) =
        some (targetRule A specs first r) := by rw [seq_rule,hr]; rfl
    unfold parGrammar at hpar
    unfold seqGrammar at hseq
    unfold parTable seqTable StatefulScannerStability.frozen
    rw [ClockFreezing.frozen_user_step _ _ _ _ _ k _ (by simp [helpers] <;> omega) _ hpar _ p hp,
      ClockFreezing.frozen_user_step _ _ _ _ _ k _ (by simp [helpers] <;> omega) _ hseq _ q hq]
    change evV (parGrammar A B hm specs) x .callByValuePar (parTable A B hm specs x k)
        (restore first u v) (sourceBody A specs r) p =
      evV (seqGrammar A B hm specs) x .callByValueSeq (seqTable A B hm specs x k)
        [u,v] (body first (render A specs false r.tail)) q
    rw [body_eval _ _ _ _ first u v _ (render_firstOrder _ _ _ _) q]
    unfold sourceBody parGrammar parTable
    rw [replay_eval A B hm (parTail A specs) x .callByValuePar k (restore first u v)
      r.left r.right _ _ p hp (controls_mem _ _ _),hf]
    have hstrip := (CBVtoCBN.stripPrefix_exact (u++v) (sfx x p) (sfx x q)).mpr hs
    have he := evaluator_of_shift A B hm specs x k ih r.tail (restore first u v) q hq
    unfold parGrammar parTable at he
    cases first <;> simpa only [restore,Bool.false_eq_true,if_false,if_true,evV,
      List.getElem?_cons_zero,List.getElem?_cons_succ,hstrip,length_sfx x hq] using he

theorem evaluator_eq {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (specs : List (Spec n m)) (x : List Char) (k : Nat)
    (E : List (List Char)) (e : MExp) (p : Nat) (hp : p ≤ x.length) :
    evV (parGrammar A B hm specs) x .callByValuePar (parTable A B hm specs x k) E (render A specs true e) p =
      evV (seqGrammar A B hm specs) x .callByValueSeq (seqTable A B hm specs x k) E (render A specs false e) p :=
  evaluator_of_shift A B hm specs x k (tables_shifted A B hm specs x k) e E p hp

/-- Full finite observations on unchanged input strings, including failure.
The frozen stages are eliminated using actual helper stability. -/
theorem observations_iff {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (specs : List (Spec n m)) (e : MExp) (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar A B hm specs) .callByValuePar (render A specs true e) x r ↔
      SObs (seqGrammar A B hm specs) .callByValueSeq (render A specs false e) x r := by
  rw [ClockFreezing.observations_iff (par_firstOrder A B hm specs) x .callByValuePar (by decide)
      (helpers n m) (x.length+1) (StatefulScannerStability.helpers_stable A B hm (parTail A specs) x .callByValuePar)
      _ (render_firstOrder _ _ _ _) r,
    ClockFreezing.observations_iff (seq_firstOrder A B hm specs) x .callByValueSeq (by decide)
      (helpers n m) (x.length+1) (StatefulScannerStability.helpers_stable A B hm (seqTail A specs) x .callByValueSeq)
      _ (render_firstOrder _ _ _ _) r]
  change (∃ k v, evV (parGrammar A B hm specs) x .callByValuePar (parTable A B hm specs x k) []
    (render A specs true e) x.length = some v ∧ v.map (sfx x) = r) ↔ _
  constructor
  · rintro ⟨k,v,hk,hr⟩
    exact ⟨k,v,(evaluator_eq A B hm specs x k [] e x.length (Nat.le_refl _)).symm.trans hk,hr⟩
  · rintro ⟨k,v,hk,hr⟩
    exact ⟨k,v,(evaluator_eq A B hm specs x k [] e x.length (Nat.le_refl _)).trans hk,hr⟩

theorem language_translation {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (specs : List (Spec n m)) (e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (parGrammar A B hm specs) .callByValuePar (render A specs true e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar A B hm specs,render A specs false e,seq_firstOrder A B hm specs,render_firstOrder _ _ _ _,
    fun x => observations_iff A B hm specs e x (some [])⟩

end Shallot.MacroPeg.CBV.StatefulPairFusion
