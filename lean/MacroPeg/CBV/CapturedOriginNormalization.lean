import MacroPeg.CBV.CapturedOriginQuery

namespace Shallot.MacroPeg.CBV.CapturedOriginNormalization
open CapturedOriginQuery (Plan compile)
open GuardedPairSyntax (render query parGrammar sourceRule sourceBody)
open GuardedPairSimulation (values)
open MixedScannerPairFusion (Entry)
open ClockFreezing (Table)

def plan (ps : List Plan) (i : Nat) := ps[i]?.getD (.test .eps)
def generatedQueries (es : List Entry) (ps : List Plan) (canonical : Bool) :=
  es.mapIdx (fun i r => compile (r.pairing.getD ([],[])).1 (r.pairing.getD ([],[])).2 canonical (plan ps i))
abbrev source (es : List Entry) (ps : List Plan) := parGrammar es (generatedQueries es ps false)
abbrev prepared (es : List Entry) (ps : List Plan) := parGrammar es (generatedQueries es ps true)
def check (es : List Entry) (ps : List Plan) : Bool :=
  es.zipIdx.all (fun (_,i) => CapturedOriginQuery.check es (plan ps i)) &&
    GuardedPairSyntax.check es (generatedQueries es ps true)

theorem query_lookup (es : List Entry) (ps : List Plan) (canonical : Bool) (i : Nat) (r : Entry) (hr : es[i]?=some r) :
    query (generatedQueries es ps canonical) i=
      compile (r.pairing.getD ([],[])).1 (r.pairing.getD ([],[])).2 canonical (plan ps i) := by
  simp [query,generatedQueries,List.getElem?_mapIdx,hr]

theorem paired_lookup (es : List Entry) (ps : List Plan) (canonical : Bool) (i : Nat) (r : Entry)
    (hr : es[i]?=some r) (A B : List Char) (hb : r.pairing=some (A,B)) :
    query (generatedQueries es ps canonical) i=compile A B canonical (plan ps i) := by
  rw [query_lookup es ps canonical i r hr,hb]; rfl

theorem checked (es : List Entry) (ps : List Plan) (hc : check es ps=true) (i : Nat) (r : Entry) (hr : es[i]?=some r) :
    CapturedOriginQuery.check es (plan ps i)=true := by
  have hm : (r,i)∈es.zipIdx := List.mem_of_getElem?
    (show es.zipIdx[i]?=some (r,i) from by simp [List.getElem?_zipIdx,hr])
  exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).1 (r,i) hm

def Rows (es : List Entry) (x : List Char) (T U : Table) : Prop :=
  ∀ (i : Nat) (r : Entry), es[i]?=some r → ∀ p, p≤x.length →
    valAt (T i (values r x p)) p=valAt (U i (values r x p)) p

theorem evaluator (es : List Entry) (ps : List Plan) (x : List Char) (T U : Table)
    (ht : OkTV x.length T) (hu : OkTV x.length U) (rows : Rows es x T U)
    (e : MExp) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source es ps) x .callByValuePar T E (render es true e) p=
      evV (prepared es ps) x .callByValuePar U E (render es true e) p := by
  have hf := GuardedPairSimulation.evaluator es (source es ps) (prepared es ps) x .callByValuePar .callByValuePar
    T U true true ht (by
      intro i E p hp
      cases hr : es[i]? with
      | none => simp only [render,hr,evV,MExp.failAlways]; exact RLe.refl _
      | some r =>
        rw [GuardedPairSimulation.source_call es _ x T E i r hr p hp,GuardedPairSimulation.source_call es _ x U E i r hr p hp,
          rows i r hr p hp]; exact RLe.refl _) e E p hp
  have hb := GuardedPairSimulation.evaluator es (prepared es ps) (source es ps) x .callByValuePar .callByValuePar
    U T true true hu (by
      intro i E p hp
      cases hr : es[i]? with
      | none => simp only [render,hr,evV,MExp.failAlways]; exact RLe.refl _
      | some r =>
        rw [GuardedPairSimulation.source_call es _ x T E i r hr p hp,GuardedPairSimulation.source_call es _ x U E i r hr p hp,
          rows i r hr p hp]; exact RLe.refl _) e E p hp
  rcases hf with hn|he
  · rcases hb with hm|he
    · exact hn.trans hm.symm
    · exact he.symm
  · exact he

theorem guarded_seq_eq (g h : MGrammar) (x : List Char) (T U : Table) (E F : List (List Char))
    (a b c d : MExp) (p : Nat)
    (hq : evV g x .callByValuePar T E a p=evV h x .callByValuePar U F b p)
    (ht : evV g x .callByValuePar T E c p=evV h x .callByValuePar U F d p) :
    evV g x .callByValuePar T E (.seq (.andP a) c) p=
      evV h x .callByValuePar U F (.seq (.andP b) d) p := by
  change (match evV g x .callByValuePar T E (.andP a) p with | some (some j) => evV g x .callByValuePar T E c j | r => r)=
    (match evV h x .callByValuePar U F (.andP b) p with | some (some j) => evV h x .callByValuePar U F d j | r => r)
  rw [CallLookahead.evV_peek,CallLookahead.evV_peek,hq]
  cases evV h x .callByValuePar U F b p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some j => exact ht

theorem tables_related (es : List Entry) (ps : List Plan) (hc : check es ps=true) (x : List Char) (k : Nat) :
    Rows es x (tblV (source es ps) x .callByValuePar k) (tblV (prepared es ps) x .callByValuePar k) := by
  induction k with
  | zero => intro i r hr p hp; rfl
  | succ k ih =>
    intro i r hr p hp
    have hs : ruleAtM (source es ps).rules i=some (sourceRule es (generatedQueries es ps false) i r) := by rw [GuardedPairSyntax.par_rule,hr]; rfl
    have ht : ruleAtM (prepared es ps).rules i=some (sourceRule es (generatedQueries es ps true) i r) := by rw [GuardedPairSyntax.par_rule,hr]; rfl
    rw [valAt_tblV_succ hs _ hp,valAt_tblV_succ ht _ hp]
    cases hb : r.pairing with
    | none =>
      simp only [sourceRule,sourceBody,hb,values]
      exact evaluator es ps x _ _ (tblV_ok _ _ _ k) (tblV_ok _ _ _ k) ih r.tail [] p hp
    | some pair =>
      obtain ⟨A,B⟩ := pair
      simp only [sourceRule,sourceBody,hb]
      apply guarded_seq_eq
      · rw [paired_lookup es ps false i r hr A B hb,paired_lookup es ps true i r hr A B hb]
        have halign := CapturedOriginQuery.aligned es (source es ps) x (tblV (source es ps) x .callByValuePar k)
          (tblV_sound (GuardedPairSyntax.par_firstOrder es _) (by decide) k) r A B hb (plan ps i) (checked es ps hc i r hr) p hp
        have hclosed := (GuardedPairSyntax.checked es (generatedQueries es ps true) (Bool.and_eq_true_iff.mp hc).2 i r hr).1
        rw [paired_lookup es ps true i r hr A B hb] at hclosed
        exact halign.trans ((evaluator es ps x _ _ (tblV_ok _ _ _ k) (tblV_ok _ _ _ k) ih _ [] p hp).trans
          (ReplayFallbackFusion.closed_env (prepared es ps) x .callByValuePar _ _ hclosed (values r x p) p).symm)
      · rw [evV_seq_ok (ScannedPairFusion.maxScanner_eval _ x .callByValuePar _ (values r x p) A B p hp),
          evV_seq_ok (ScannedPairFusion.maxScanner_eval _ x .callByValuePar _ (values r x p) A B p hp)]
        exact evaluator es ps x _ _ (tblV_ok _ _ _ k) (tblV_ok _ _ _ k) ih r.tail (values r x p) _
          (Nat.le_trans (ScannerFrontier.finalPos_le A B x p hp) (Nat.le_trans (ScannerFrontier.commonPos_le A B x p hp) hp))

theorem physical (es : List Entry) (ps : List Plan) (hc : check es ps=true) (x : List Char) (k : Nat)
    (E : List (List Char)) (e : MExp) (p : Nat) (hp : p≤x.length) :
    evV (source es ps) x .callByValuePar (tblV (source es ps) x .callByValuePar k) E (render es true e) p=
      evV (prepared es ps) x .callByValuePar (tblV (prepared es ps) x .callByValuePar k) E (render es true e) p :=
  evaluator es ps x _ _ (tblV_ok _ _ _ k) (tblV_ok _ _ _ k) (tables_related es ps hc x k) e E p hp

theorem observations_iff (es : List Entry) (ps : List Plan) (hc : check es ps=true) (e : MExp)
    (x : List Char) (rest : Option (List Char)) :
    SObs (source es ps) .callByValuePar (render es true e) x rest ↔
      SObs (prepared es ps) .callByValuePar (render es true e) x rest := by
  rw [←decideObsV_iff (GuardedPairSyntax.par_firstOrder es _) (by decide) (GuardedPairSyntax.render_firstOrder _ _ _),
    ←decideObsV_iff (GuardedPairSyntax.par_firstOrder es _) (by decide) (GuardedPairSyntax.render_firstOrder _ _ _)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => physical es ps hc x k [] e x.length (Nat.le_refl _))]

end Shallot.MacroPeg.CBV.CapturedOriginNormalization
