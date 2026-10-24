import MacroPeg.CBV.ScannerFrontier

/-! A fixed recursive reverse compiler for independent scanner pairs.
The source replays the longer captured prefix before its tail. Target rule
variants select their capture views using the runtime endpoint-order test.
This is a replay-shaped source family, not arbitrary Par normalization. -/
namespace Shallot.MacroPeg.CBV.ScannerPairFusion
open NestedScannerArguments ScannerFrontier

structure Spec where
  left : List Char
  right : List Char
  tail : MExp

/-- Template calls `call i []` invoke the scanner pair of specification i.
Nonempty template call argument lists and higher-order forms are rejected. -/
def render (specs : List Spec) (parallel : Bool) : MExp → MExp
  | .call i [] =>
    match specs[i]? with
    | none => MExp.failAlways
    | some r => if parallel then .call i [scan r.left,scan r.right]
      else dispatch r.left r.right (2*i) (2*i+1)
  | .call _ (_::_) => MExp.failAlways
  | .param k => .param k
  | .seq a b => .seq (render specs parallel a) (render specs parallel b)
  | .alt a b => .alt (render specs parallel a) (render specs parallel b)
  | .star a => .star (render specs parallel a)
  | .notP a => .notP (render specs parallel a)
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit w => .lit w
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

theorem render_firstOrder (specs : List Spec) (parallel : Bool) :
    ∀ e, (render specs parallel e).FirstOrder
  | .call i [] => by
    simp only [render]
    cases specs[i]? with
    | none => trivial
    | some r =>
      cases parallel
      · exact dispatch_firstOrder _ _ _ _
      · exact ⟨scan_firstOrder _,scan_firstOrder _,trivial⟩
  | .call _ (_::_) => trivial
  | .seq a b | .alt a b => ⟨render_firstOrder specs parallel a,render_firstOrder specs parallel b⟩
  | .star a | .notP a => render_firstOrder specs parallel a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

def sourceBody (specs : List Spec) (r : Spec) : MExp :=
  RootObservation.branch (guard r.left r.right)
    (.seq (.param 1) (render specs true r.tail))
    (.seq (.param 0) (render specs true r.tail))

def parGrammar (specs : List Spec) : MGrammar :=
  ⟨specs.map (fun r => ⟨2,sourceBody specs r⟩)⟩

def targetRule (specs : List Spec) (first : Bool) (r : Spec) : MRule :=
  ⟨2,body first (render specs false r.tail)⟩

def seqGrammar (specs : List Spec) : MGrammar :=
  ⟨specs.flatMap (fun r => [targetRule specs true r,targetRule specs false r])⟩

theorem par_rule_count (specs : List Spec) : (parGrammar specs).rules.length = specs.length := by
  simp [parGrammar]

theorem seq_rule_count (specs : List Spec) : (seqGrammar specs).rules.length = 2*specs.length := by
  unfold seqGrammar
  induction specs <;> simp_all [List.flatMap_cons,Nat.mul_add,Nat.add_comm] <;> omega

theorem par_rule (specs : List Spec) (i : Nat) :
    ruleAtM (parGrammar specs).rules i = (specs[i]?).map (fun r => ⟨2,sourceBody specs r⟩) := by
  simp [parGrammar,ruleAtM_eq_getElem?]

private theorem pair_lookup (entries all : List Spec) (first : Bool) (i : Nat) :
    (entries.flatMap (fun r => [targetRule all true r,targetRule all false r]))[2*i + (if first then 0 else 1)]? = (entries[i]?).map (targetRule all first) := by
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

theorem seq_rule (specs : List Spec) (first : Bool) (i : Nat) :
    ruleAtM (seqGrammar specs).rules (2*i+(if first then 0 else 1)) =
      (specs[i]?).map (targetRule specs first) := by
  simpa only [ruleAtM_eq_getElem?,seqGrammar] using pair_lookup specs specs first i

theorem sourceBody_firstOrder (specs : List Spec) (r : Spec) : (sourceBody specs r).FirstOrder :=
  ⟨⟨guard_firstOrder _ _,⟨trivial,render_firstOrder _ _ _⟩⟩,
    ⟨guard_firstOrder _ _,⟨trivial,render_firstOrder _ _ _⟩⟩⟩

theorem par_firstOrder (specs : List Spec) : (parGrammar specs).FirstOrder := by
  intro r hr
  change r ∈ specs.map (fun r => ⟨2,sourceBody specs r⟩) at hr
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hr
  exact sourceBody_firstOrder _ _

theorem seq_firstOrder (specs : List Spec) : (seqGrammar specs).FirstOrder := by
  intro r hr
  change r ∈ specs.flatMap (fun r => [targetRule specs true r,targetRule specs false r]) at hr
  obtain ⟨r,hr,hmem⟩ := List.mem_flatMap.mp hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with rfl | rfl <;> exact body_firstOrder _ _ (render_firstOrder _ _ _)

theorem chunks_split (A B : List Char) (x : List Char) (p : Nat) (hp : p ≤ x.length) :
    sfx x p = (pre x p (commonPos A B x p) ++
      pre x (commonPos A B x p) (finalPos A B x p)) ++ sfx x (finalPos A B x p) := by
  have hc := commonPos_le A B x p hp
  have hq := finalPos_le A B x p hp
  have hs : sfx x (finalPos A B x p) = (sfx x p).drop (p-finalPos A B x p) := by
    simp only [sfx,List.drop_drop]
    congr 1
    omega
  rw [← pre_concat x p _ _ hp hc hq,hs]
  exact (List.take_append_drop _ _).symm

def Shifted (specs : List Spec) (x : List Char)
    (T U : Nat → List (List Char) → Val) : Prop :=
  ∀ i r, specs[i]? = some r → ∀ first u v p q,
    p ≤ x.length → q ≤ x.length → sfx x p = (u++v) ++ sfx x q →
    firstStops r.left r.right (sfx x p) = first →
    valAt (T i (restore first u v)) p =
      valAt (U (2*i+(if first then 0 else 1)) [u,v]) q

theorem evaluator_of_shift {specs : List Spec} {x : List Char}
    {T U : Nat → List (List Char) → Val}
    (hOk : OkTV x.length T) (hShift : Shifted specs x T U) :
    ∀ e E p, p ≤ x.length →
      evV (parGrammar specs) x .callByValuePar T E (render specs true e) p =
        evV (seqGrammar specs) x .callByValueSeq U E (render specs false e) p
  | .param _, _, _, _ | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _
  | .range _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .dbg _, _, _, _ | .lam _ _, _, _, _ | .callParam _ _, _, _, _
  | .invoke _ _ _, _, _, _ | .call _ (_::_), _, _, _ => rfl
  | .call i [], E, p, hp => by
    cases hr : specs[i]? with
    | none => simp [render,hr,evV,MExp.failAlways]
    | some r =>
      have hs : ruleAtM (parGrammar specs).rules i = some ⟨2,sourceBody specs r⟩ := by
        rw [par_rule,hr]; rfl
      have hl : ruleAtM (seqGrammar specs).rules (2*i) = some (targetRule specs true r) := by
        simpa only [if_true,Nat.add_zero,hr,Option.map_some] using seq_rule specs true i
      have ht : ruleAtM (seqGrammar specs).rules (2*i+1) = some (targetRule specs false r) := by
        simpa only [Bool.false_eq_true,if_false,hr,Option.map_some] using seq_rule specs false i
      simp only [render,hr,if_true,Bool.false_eq_true,if_false]
      apply call_of_body_relation T U E E r.left r.right i (2*i) (2*i+1) _ _ _ hs hl ht rfl rfl rfl p hp
      have hh := hShift i r hr (firstStops r.left r.right (sfx x p))
        (pre x p (commonPos r.left r.right x p))
        (pre x (commonPos r.left r.right x p) (finalPos r.left r.right x p))
        p (finalPos r.left r.right x p) hp
        (Nat.le_trans (finalPos_le _ _ _ _ hp) (Nat.le_trans (commonPos_le _ _ _ _ hp) hp))
        (chunks_split _ _ _ _ hp) rfl
      cases hf : firstStops r.left r.right (sfx x p) <;> simpa only [hf,chunks,if_true,
        Bool.false_eq_true,if_false,Nat.add_zero] using hh
  | .seq a b, E, p, hp => by
    have heq := evaluator_of_shift hOk hShift a E p hp
    cases hv : evV (parGrammar specs) x .callByValuePar T E (render specs true a) p with
    | none => simp only [render,evV_seq_none hv,evV_seq_none (heq.symm.trans hv)]
    | some result => cases result with
      | none => simp only [render,evV_seq_fail hv,evV_seq_fail (heq.symm.trans hv)]
      | some q =>
        simp only [render,evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
        exact evaluator_of_shift hOk hShift b E q (evV_ok hOk _ p hp q hv)
  | .alt a b, E, p, hp => by
    have heq := evaluator_of_shift hOk hShift a E p hp
    cases hv : evV (parGrammar specs) x .callByValuePar T E (render specs true a) p with
    | none => simp only [render,evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
    | some result => cases result with
      | none =>
        simp only [render,evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
        exact evaluator_of_shift hOk hShift b E p hp
      | some q => simp only [render,evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
  | .notP a, E, p, hp => by
    simp only [render,evV]
    rw [evaluator_of_shift hOk hShift a E p hp]
  | .star a, E, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift hOk hShift a E q (by omega))

theorem tables_shifted (specs : List Spec) (x : List Char) (m : Nat) :
    Shifted specs x (tblV (parGrammar specs) x .callByValuePar m)
      (tblV (seqGrammar specs) x .callByValueSeq m) := by
  induction m with
  | zero => intro i r hr first u v p q hp hq hs hf; simp [tblV,valAt_nil]
  | succ m ih =>
    intro i r hr first u v p q hp hq hs hf
    have hpar : ruleAtM (parGrammar specs).rules i = some ⟨2,sourceBody specs r⟩ := by
      rw [par_rule,hr]; rfl
    have hseq : ruleAtM (seqGrammar specs).rules (2*i+(if first then 0 else 1)) =
        some (targetRule specs first r) := by rw [seq_rule,hr]; rfl
    rw [valAt_tblV_succ hpar _ hp,valAt_tblV_succ hseq _ hq]
    change evV (parGrammar specs) x .callByValuePar (tblV (parGrammar specs) x .callByValuePar m)
        (restore first u v) (sourceBody specs r) p =
      evV (seqGrammar specs) x .callByValueSeq (tblV (seqGrammar specs) x .callByValueSeq m)
        [u,v] (body first (render specs false r.tail)) q
    rw [body_eval _ _ _ _ first u v _ (render_firstOrder _ _ _) q]
    rw [sourceBody,branch_eval _ _ _ p _ (guard_eval _ _ _ _ _ _ _ p hp),hf]
    have hstrip := (CBVtoCBN.stripPrefix_exact (u++v) (sfx x p) (sfx x q)).mpr hs
    have he := evaluator_of_shift (tblV_ok _ _ _ m) ih r.tail (restore first u v) q hq
    cases first <;> simpa only [restore,Bool.false_eq_true,if_false,if_true,evV,
      List.getElem?_cons_zero,List.getElem?_cons_succ,hstrip,length_sfx x hq] using he

/-- The recursive body-table relation is proved, not assumed. -/
theorem evaluator_eq (specs : List Spec) (x : List Char) (m : Nat)
    (E : List (List Char)) (e : MExp) (p : Nat) (hp : p ≤ x.length) :
    evV (parGrammar specs) x .callByValuePar (tblV (parGrammar specs) x .callByValuePar m)
      E (render specs true e) p =
      evV (seqGrammar specs) x .callByValueSeq (tblV (seqGrammar specs) x .callByValueSeq m)
        E (render specs false e) p :=
  evaluator_of_shift (tblV_ok _ _ _ m) (tables_shifted specs x m) e E p hp


/-- Equal iterated evaluators have equal stable results even when the two
finite grammars have different rule counts and stabilization bounds. -/
theorem stable_result_eq (g h : MGrammar) (x : List Char) (s t : Strategy) (a b : MExp)
    (heq : ∀ m, evV g x s (tblV g x s m) [] a x.length =
      evV h x t (tblV h x t m) [] b x.length) :
    evV g x s (tblV g x s (iterBoundV g x)) [] a x.length =
      evV h x t (tblV h x t (iterBoundV h x)) [] b x.length := by
  cases ha : evV g x s (tblV g x s (iterBoundV g x)) [] a x.length with
  | some v =>
    have hb := (tblV_stable h x t (Nat.le_refl x.length)).mp
      ⟨iterBoundV g x,(heq (iterBoundV g x)).symm.trans ha⟩
    exact hb.symm
  | none =>
    cases hb : evV h x t (tblV h x t (iterBoundV h x)) [] b x.length with
    | none => rfl
    | some v =>
      have hc := (tblV_stable g x s (Nat.le_refl x.length)).mp
        ⟨iterBoundV h x,(heq (iterBoundV h x)).trans hb⟩
      rw [ha] at hc
      cases hc

theorem decide_eq (specs : List Spec) (e : MExp) (x : List Char) :
    decideObsV .callByValuePar (parGrammar specs) x (render specs true e) =
      decideObsV .callByValueSeq (seqGrammar specs) x (render specs false e) := by
  unfold decideObsV
  rw [stable_result_eq (parGrammar specs) (seqGrammar specs) x .callByValuePar .callByValueSeq
    (render specs true e) (render specs false e)
    (fun m => evaluator_eq specs x m [] e x.length (Nat.le_refl _))]

/-- Every finite observation on the original strings is preserved by the
fixed recursive compiler, including finite failure. Neither source capture
ordering nor the source-to-target table relation is an external premise. -/
theorem observations_iff (specs : List Spec) (e : MExp) (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar specs) .callByValuePar (render specs true e) x r ↔
      SObs (seqGrammar specs) .callByValueSeq (render specs false e) x r := by
  rw [← decideObsV_iff (par_firstOrder specs) (by decide) (render_firstOrder specs true e),
    ← decideObsV_iff (seq_firstOrder specs) (by decide) (render_firstOrder specs false e),
    decide_eq specs e x]

theorem language_translation (specs : List Spec) (e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (parGrammar specs) .callByValuePar (render specs true e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar specs,render specs false e,seq_firstOrder specs,render_firstOrder specs false e,
    fun x => observations_iff specs e x (some [])⟩

end Shallot.MacroPeg.CBV.ScannerPairFusion
