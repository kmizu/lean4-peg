import MacroPeg.CBV.ProfileCheckedScannerCorrespondence
import MacroPeg.CBV.MixedOriginControl

namespace Shallot.MacroPeg.CBV.ScannerOriginControl
open RecursiveScannerProductCompiler (Arg Entry Entries helpers helperBodies offset sourceExpr sourceHeader)
open ReplayControlFusion (Plan)
open StatefulScanner (Machine)

/-- Every occurrence of the caller's retained values is excluded, including
lookahead tests and actual arguments. Called users may inspect their fresh captures. -/
def independent : Arg → Bool
  | .param _ => false
  | .user _ a | .star a | .notP a => independent a
  | .seq a b | .alt a b => independent a && independent b
  | .lit _ => true

/-- Capture independence is structural; no assumption about callee rows or
successful evaluations is needed. -/
theorem independent_environment {n : Nat} (M : Machine n) (g : MGrammar)
    (x : List Char) (T : ClockFreezing.Table) (E F : List (List Char)) :
    ∀ e, independent e=true → ∀ p,
    evV g x .callByValuePar T E (sourceExpr M e) p=
    evV g x .callByValuePar T F (sourceExpr M e) p
  | .lit _,_,_ => rfl
  | .param _,h,_ => by cases h
  | .user i a,h,p => by
    simp only [sourceExpr,evV,evParArgs,independent_environment M g x T E F a h]
  | .seq a b,h,p | .alt a b,h,p => by
    have ha := independent_environment M g x T E F a (Bool.and_eq_true_iff.mp h).1
    have hb := independent_environment M g x T E F b (Bool.and_eq_true_iff.mp h).2
    simp only [sourceExpr,evV,ha,hb]
  | .notP a,h,p => by
    simp only [sourceExpr,evV,independent_environment M g x T E F a h]
  | .star a,h,p =>
    evStar_congr p (fun q _ => independent_environment M g x T E F a h q)

structure Part (n : Nat) where
  entry : Entry n
  body : Arg
  /-- Omit the entry and erase the old capture, checked by `independent`. -/
  closed : Bool := false

def callArg {n : Nat} (parts : List (Part n)) (j : Nat) (a : Arg) : Arg :=
  match parts[j]? with
  | some r => if r.closed then .lit [] else a
  | none => a

def captureValue {n : Nat} (parts : List (Part n)) (j : Nat) (w : List Char) : List Char :=
  match parts[j]? with
  | some r => if r.closed then [] else w
  | none => w

def expand {n : Nat} (parts : List (Part n)) (a : Arg) : Plan → Arg
  | .leaf j => .user j (callArg parts j a)
  | .alt p q => .alt (expand parts a p) (expand parts a q)
  | .notP p => .notP (expand parts a p)
  | .guard p q => .seq (.notP (.notP (expand parts a p))) (expand parts a q)

/-- Argument evaluation precedes every caller-side control tree. Dependent
leaves recapture that argument; independent leaves receive an empty capture. -/
def normalize {n : Nat} (parts : List (Part n)) (plans : List Plan) : Arg → Arg
  | .user i a => match plans[i]? with
    | none => .notP (.lit [])
    | some p => .seq (.notP (.notP (normalize parts plans a))) (expand parts (normalize parts plans a) p)
  | .seq a b => .seq (normalize parts plans a) (normalize parts plans b)
  | .alt a b => .alt (normalize parts plans a) (normalize parts plans b)
  | .notP a => .notP (normalize parts plans a)
  | .star a => .star (normalize parts plans a)
  | .lit w => .lit w
  | .param k => .param k

def coreEntries {n : Nat} (parts : List (Part n)) : Entries n := fun i =>
  match parts[i]? with | some r => if r.closed then .replay else r.entry | none => .replay

def coreBodies {n : Nat} (parts : List (Part n)) (plans : List Plan) : List Arg :=
  parts.map (fun r => normalize parts plans r.body)

abbrev core {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan) :=
  RecursiveScannerProductCompiler.source M (coreEntries parts) (coreBodies parts plans)

abbrev target {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan) :=
  RecursiveScannerProductCompiler.target M (coreEntries parts) (coreBodies parts plans)
abbrev targetExpr {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan) (e : Arg) :=
  RecursiveScannerProductCompiler.plain M (coreBodies parts plans) [] (normalize parts plans e)

def sourceLeaf {n : Nat} (M : Machine n) (parts : List (Part n)) (j : Nat) : MExp :=
  match parts[j]? with
  | none => MExp.failAlways
  | some r => if r.closed then sourceExpr M r.body else .seq (sourceHeader r.entry) (sourceExpr M r.body)

def rules {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan) : List MRule :=
  plans.map (fun p => ⟨1,p.exp (sourceLeaf M parts)⟩)

def original {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan) : MGrammar :=
  ⟨helpers M++rules M parts plans⟩

def Scoped (plans : List Plan) : Arg → Prop
  | .user i a => i<plans.length ∧ Scoped plans a
  | .seq a b | .alt a b => Scoped plans a ∧ Scoped plans b
  | .star a | .notP a => Scoped plans a
  | _ => True

def scopeCheck (plans : List Plan) : Arg → Bool
  | .user i a => decide (i<plans.length) && scopeCheck plans a
  | .seq a b | .alt a b => scopeCheck plans a && scopeCheck plans b
  | .star a | .notP a => scopeCheck plans a
  | _ => true

theorem scope_sound (plans : List Plan) : ∀ a, scopeCheck plans a=true → Scoped plans a
  | .user _i a,h => ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h).1,scope_sound plans a (Bool.and_eq_true_iff.mp h).2⟩
  | .seq a b,h | .alt a b,h => ⟨scope_sound plans a (Bool.and_eq_true_iff.mp h).1,scope_sound plans b (Bool.and_eq_true_iff.mp h).2⟩
  | .notP a,h | .star a,h => scope_sound plans a h
  | .lit _,_ | .param _,_ => True.intro

def planCheck {n : Nat} (parts : List (Part n)) : Plan → Bool
  | .leaf i => decide (i<parts.length)
  | .alt a b | .guard a b => planCheck parts a && planCheck parts b
  | .notP a => planCheck parts a

def readyCheck {n : Nat} (parts : List (Part n)) (plans : List Plan) : Bool :=
  plans.all (planCheck parts) && parts.all (fun r => scopeCheck plans r.body && (!r.closed || independent r.body))

def Ready {n : Nat} (parts : List (Part n)) (plans : List Plan) : Prop :=
  (∀ p∈plans, p.All (fun j => ∃ r, parts[j]?=some r)) ∧
  (∀ r∈parts, Scoped plans r.body ∧ (r.closed=true → independent r.body=true))

theorem plan_sound {n : Nat} (parts : List (Part n)) :
    ∀ p, planCheck parts p=true → p.All (fun j => ∃ r, parts[j]?=some r)
  | .leaf i,h => by
    have hi : i<parts.length := of_decide_eq_true h
    exact ⟨parts[i],List.getElem?_eq_getElem hi⟩
  | .alt a b,h | .guard a b,h => ⟨plan_sound parts a (Bool.and_eq_true_iff.mp h).1,plan_sound parts b (Bool.and_eq_true_iff.mp h).2⟩
  | .notP a,h => plan_sound parts a h

theorem ready_sound {n : Nat} (parts : List (Part n)) (plans : List Plan)
    (h : readyCheck parts plans=true) : Ready parts plans := by
  have hh := Bool.and_eq_true_iff.mp h
  exact ⟨fun p hp => plan_sound parts p ((List.all_eq_true.mp hh.1) p hp),
    fun r hr => by
      have hpart := Bool.and_eq_true_iff.mp ((List.all_eq_true.mp hh.2) r hr)
      exact ⟨scope_sound plans r.body hpart.1,fun hc => by simpa [hc] using hpart.2⟩⟩

theorem expand_source {n : Nat} (M : Machine n) (parts : List (Part n)) (a : Arg) : ∀ p,
    sourceExpr M (expand parts a p)=p.exp (fun j => sourceExpr M (.user j (callArg parts j a)))
  | .leaf _ => rfl
  | .alt p q | .guard p q => by simp only [expand,sourceExpr,Plan.exp,MExp.andP,expand_source M parts a p,expand_source M parts a q]
  | .notP p => by simp only [expand,sourceExpr,Plan.exp,expand_source M parts a p]

theorem original_firstOrder {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan) :
    (original M parts plans).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact RecursiveScannerProductCompiler.helpers_firstOrder M r hr
  · obtain ⟨p,_,rfl⟩ := List.mem_map.mp hr
    apply Plan.exp_firstOrder
    intro j
    simp only [sourceLeaf]
    cases parts[j]? with
    | none => trivial
    | some r =>
      change (if r.closed then sourceExpr M r.body else .seq (sourceHeader r.entry) (sourceExpr M r.body)).FirstOrder
      split
      · exact RecursiveScannerProductCompiler.sourceExpr_firstOrder M r.body
      · exact ⟨RecursiveScannerProductCompiler.sourceHeader_firstOrder r.entry,
          RecursiveScannerProductCompiler.sourceExpr_firstOrder M r.body⟩

theorem original_rule {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan)
    (i : Nat) (p : Plan) (hi : plans[i]?=some p) :
    ruleAtM (original M parts plans).rules (offset M+i)=some ⟨1,p.exp (sourceLeaf M parts)⟩ := by
  simp [original,rules,offset,ruleAtM_eq_getElem?,List.getElem?_append_right (by omega : (helpers M).length≤(helpers M).length+i),hi]

theorem core_lookup {n : Nat} (parts : List (Part n)) (plans : List Plan)
    (j : Nat) (r : Part n) (hr : parts[j]?=some r) :
    (coreBodies parts plans)[j]?=some (normalize parts plans r.body) := by simp [coreBodies,hr]

/-- Closed scanner rows agree across these two actual grammar extensions;
replayed values and all origin guards are evaluated in the same environment. -/
theorem header_extension {n : Nat} (M : Machine n) (left right : List MRule)
    (x : List Char) (k : Nat) (E : List (List Char)) (entry : Entry n) (p : Nat) :
    evV (RecursiveScannerProductHelpers.grammar M left) x .callByValuePar
      (tblV (RecursiveScannerProductHelpers.grammar M left) x .callByValuePar k) E (sourceHeader entry) p=
    evV (RecursiveScannerProductHelpers.grammar M right) x .callByValuePar
      (tblV (RecursiveScannerProductHelpers.grammar M right) x .callByValuePar k) E (sourceHeader entry) p := by
  induction entry with
  | replay | safeReplay | shift _ _ => rfl
  | aligned c => exact GuardedReplayControl.header_independent _ _ x _ _ _ _ E c p
  | iterate q R =>
    simp only [sourceHeader,GuardedReplayIteration.header,GuardedReplayIteration.step,MExp.andP,evV]
  | scan q =>
    rw [show sourceHeader (.scan q)=.call q.val [] from rfl,
      evV_call_par (RecursiveScannerProductHelpers.scanner_rule M left q) rfl (by decide),
      evV_call_par (RecursiveScannerProductHelpers.scanner_rule M right q) rfl (by decide)]
    simp only [evParArgs]
    exact congrArg (fun row => valAt row p) (RecursiveParserStability.helper_rows_eq
      (RecursiveScannerProductHelpers.lexical M) (RecursiveScannerProductHelpers.installed M left)
      (RecursiveScannerProductHelpers.installed M right) x .callByValuePar .callByValuePar k q.val
      (by rw [RecursiveScannerProductHelpers.helperBodies_length]; have := q.isLt; omega) [] [])
  | alt a b ha hb => simp only [sourceHeader,evV,ha,hb]
  | guard positive a b ha hb =>
    cases positive <;> cases hv : evV (RecursiveScannerProductHelpers.grammar M left) x .callByValuePar
      (tblV (RecursiveScannerProductHelpers.grammar M left) x .callByValuePar k) E (sourceHeader a) p with
      | none => simp only [sourceHeader,Bool.false_eq_true,if_false,if_true,MExp.andP,evV,←ha,hv]
      | some result => cases result <;> simp only [sourceHeader,Bool.false_eq_true,if_false,if_true,MExp.andP,evV,←ha,hv,hb]

def Rows {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan) (x : List Char) (k : Nat) : Prop :=
  ∀ i p, plans[i]?=some p → ∀ w pos, pos≤x.length →
    valAt (tblV (original M parts plans) x .callByValuePar k (offset M+i) [w]) pos=
      p.eval (fun j => valAt (tblV (core M parts plans) x .callByValuePar k (offset M+j) [captureValue parts j w]) pos) pos

theorem leaf_call {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan)
    (x : List Char) (k : Nat) (E : List (List Char)) (a : Arg) (p q j : Nat)
    (r : Part n) (hr : parts[j]?=some r) (hp : p≤x.length)
    (harg : evV (core M parts plans) x .callByValuePar
      (tblV (core M parts plans) x .callByValuePar k) E (sourceExpr M a) p=some (some q)) :
    evV (core M parts plans) x .callByValuePar (tblV (core M parts plans) x .callByValuePar k) E
      (sourceExpr M (.user j (callArg parts j a))) p=
      valAt (tblV (core M parts plans) x .callByValuePar k (offset M+j) [captureValue parts j (pre x p q)]) p := by
  rw [show sourceExpr M (.user j (callArg parts j a))=
      .call (offset M+j) [sourceExpr M (callArg parts j a)] from rfl,
    evV_call_par (RecursiveScannerProductCompiler.source_rule M (coreEntries parts) (coreBodies parts plans)
      j (normalize parts plans r.body) (core_lookup parts plans j r hr)) rfl (by decide)]
  cases hc : r.closed with
  | false => simp [callArg,captureValue,hr,hc,evParArgs,harg]
  | true => simp [callArg,captureValue,hr,hc,sourceExpr,evParArgs,evV,Shallot.stripPrefix?,length_sfx x hp,pre]

theorem evaluator_of_rows {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan)
    (hReady : Ready parts plans) (x : List Char) (k : Nat) (hRows : Rows M parts plans x k) :
    ∀ e, Scoped plans e → ∀ E p, p≤x.length →
    evV (original M parts plans) x .callByValuePar (tblV (original M parts plans) x .callByValuePar k) E (sourceExpr M e) p=
    evV (core M parts plans) x .callByValuePar (tblV (core M parts plans) x .callByValuePar k) E (sourceExpr M (normalize parts plans e)) p
  | .user i a,he,E,p,hp => by
    obtain ⟨P,hP⟩ : ∃ P, plans[i]?=some P := ⟨plans[i]'he.1,List.getElem?_eq_getElem he.1⟩
    simp only [normalize,hP,sourceExpr,expand_source]
    apply MixedOriginControl.call_plan_eq
    · exact ⟨_,original_rule M parts plans i P hP⟩
    · exact evaluator_of_rows M parts plans hReady x k hRows a he.2 E p hp
    · intro w; exact hRows i P hP w p hp
    · intro q harg
      apply Plan.all_imp (t:=P) _ (hReady.1 P (List.mem_of_getElem? hP))
      intro j hj
      obtain ⟨r,hr⟩ := hj
      exact leaf_call M parts plans x k E (normalize parts plans a) p q j r hr hp harg
  | .lit _,_,_,_,_ | .param _,_,_,_,_ => rfl
  | .seq a b,he,E,p,hp => by
    have hh := evaluator_of_rows M parts plans hReady x k hRows a he.1 E p hp
    cases hv : evV (original M parts plans) x .callByValuePar (tblV (original M parts plans) x .callByValuePar k) E (sourceExpr M a) p with
    | none => simp only [normalize,sourceExpr,evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => simp only [normalize,sourceExpr,evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        simp only [normalize,sourceExpr,evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_rows M parts plans hReady x k hRows b he.2 E q
          (evV_ok (tblV_ok _ _ _ k) _ p hp q hv)
  | .alt a b,he,E,p,hp => by
    have hh := evaluator_of_rows M parts plans hReady x k hRows a he.1 E p hp
    cases hv : evV (original M parts plans) x .callByValuePar (tblV (original M parts plans) x .callByValuePar k) E (sourceExpr M a) p with
    | none => simp only [normalize,sourceExpr,evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some result => cases result with
      | none =>
        simp only [normalize,sourceExpr,evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]
        exact evaluator_of_rows M parts plans hReady x k hRows b he.2 E p hp
      | some q => simp only [normalize,sourceExpr,evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | .star a,he,E,p,hp =>
    evStar_congr p (fun q hq => evaluator_of_rows M parts plans hReady x k hRows a he E q (by omega))
  | .notP a,he,E,p,hp => by
    simp only [normalize,sourceExpr,evV]
    rw [evaluator_of_rows M parts plans hReady x k hRows a he E p hp]

/-- The row relation is derived from actual source and generated rules,
with the same ordinary user clock and no row or success oracle. -/
theorem tables_rows {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan)
    (hReady : Ready parts plans) (x : List Char) (k : Nat) : Rows M parts plans x k := by
  induction k with
  | zero =>
    intro i P hP w p hp
    change none=P.eval (fun _ => none) p
    exact (Plan.eval_none P (Plan.all_of_forall (fun _ => rfl) P)).symm
  | succ k ih =>
    intro i P hP w p hp
    rw [valAt_tblV_succ (original_rule M parts plans i P hP) [w] hp,Plan.exp_eval]
    apply Plan.eval_congr
    apply Plan.all_imp (t:=P) _ (hReady.1 P (List.mem_of_getElem? hP))
    intro j hj
    obtain ⟨r,hr⟩ := hj
    cases hc : r.closed with
    | true =>
      rw [show sourceLeaf M parts j=sourceExpr M r.body from by simp [sourceLeaf,hr,hc]]
      rw [show captureValue parts j w=[] from by simp [captureValue,hr,hc]]
      rw [valAt_tblV_succ (RecursiveScannerProductCompiler.source_rule M (coreEntries parts) (coreBodies parts plans)
        j (normalize parts plans r.body) (core_lookup parts plans j r hr)) [[]] hp]
      have he : evV (core M parts plans) x .callByValuePar
          (tblV (core M parts plans) x .callByValuePar k) [[]] (sourceHeader (coreEntries parts j)) p=some (some p) := by
        simp [coreEntries,hr,hc,sourceHeader,evV,Shallot.stripPrefix?,length_sfx x hp]
      rw [evV_seq_ok he]
      rw [independent_environment M (original M parts plans) x
        (tblV (original M parts plans) x .callByValuePar k) [w] [[]] r.body
        ((hReady.2 r (List.mem_of_getElem? hr)).2 hc)]
      exact evaluator_of_rows M parts plans hReady x k ih r.body
        (hReady.2 r (List.mem_of_getElem? hr)).1 [[]] p hp
    | false =>
      rw [show captureValue parts j w=w from by simp [captureValue,hr,hc]]
      rw [show sourceLeaf M parts j=.seq (sourceHeader r.entry) (sourceExpr M r.body) from by simp [sourceLeaf,hr,hc],
        valAt_tblV_succ (RecursiveScannerProductCompiler.source_rule M (coreEntries parts) (coreBodies parts plans)
          j (normalize parts plans r.body) (core_lookup parts plans j r hr)) [w] hp]
      simp only [coreEntries,hr,hc,Bool.false_eq_true,if_false]
      have hh := header_extension M (rules M parts plans)
        (RecursiveScannerProductCompiler.sourceRules M (coreEntries parts) (coreBodies parts plans)) x k [w] r.entry p
      change evV (original M parts plans) x .callByValuePar (tblV (original M parts plans) x .callByValuePar k) [w] (sourceHeader r.entry) p=
        evV (core M parts plans) x .callByValuePar (tblV (core M parts plans) x .callByValuePar k) [w] (sourceHeader r.entry) p at hh
      cases hv : evV (original M parts plans) x .callByValuePar (tblV (original M parts plans) x .callByValuePar k) [w] (sourceHeader r.entry) p with
      | none => rw [evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
      | some result => cases result with
        | none => rw [evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
        | some q =>
          rw [evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
          exact evaluator_of_rows M parts plans hReady x k ih r.body (hReady.2 r (List.mem_of_getElem? hr)).1 [w] q
            (evV_ok (tblV_ok _ _ _ k) _ p hp q hv)

theorem evaluator_eq {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan)
    (hReady : readyCheck parts plans=true) (e : Arg) (he : scopeCheck plans e=true)
    (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (original M parts plans) x .callByValuePar (tblV (original M parts plans) x .callByValuePar k) E (sourceExpr M e) p=
    evV (core M parts plans) x .callByValuePar (tblV (core M parts plans) x .callByValuePar k) E (sourceExpr M (normalize parts plans e)) p :=
  evaluator_of_rows M parts plans (ready_sound parts plans hReady) x k
    (tables_rows M parts plans (ready_sound parts plans hReady) x k) e (scope_sound plans e he) E p hp

theorem normalized_observations_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan)
    (hReady : readyCheck parts plans=true) (e : Arg) (he : scopeCheck plans e=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs (original M parts plans) .callByValuePar (sourceExpr M e) x rest ↔
      SObs (core M parts plans) .callByValuePar (sourceExpr M (normalize parts plans e)) x rest := by
  rw [←decideObsV_iff (original_firstOrder M parts plans) (by decide)
      (RecursiveScannerProductCompiler.sourceExpr_firstOrder M e),
    ←decideObsV_iff (RecursiveScannerProductCompiler.source_firstOrder M (coreEntries parts) (coreBodies parts plans))
      (by decide) (RecursiveScannerProductCompiler.sourceExpr_firstOrder M (normalize parts plans e))]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq (original M parts plans) (core M parts plans) x .callByValuePar .callByValuePar
    (sourceExpr M e) (sourceExpr M (normalize parts plans e))
    (fun k => evaluator_eq M parts plans hReady e he x k [] x.length (Nat.le_refl _))]

/-- One actual fixed first-order Seq grammar preserves all finite
observations of the original grammar, including origin-returning control. -/
theorem observations_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan)
    (hReady : readyCheck parts plans=true) (e : Arg) (he : scopeCheck plans e=true)
    (H : RecursiveCaptureProfiles.ScannerSummary n) (C : RecursiveCaptureProfiles.Summary)
    (A : ProfileCheckedScannerCorrespondence.Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M (coreEntries parts) (coreBodies parts plans) H C=true)
    (hB : ProfileCheckedScannerCorrespondence.bodiesCheck M (coreEntries parts) (coreBodies parts plans) C A=true)
    (hRoot : ProfileCheckedScannerCorrespondence.check M (coreEntries parts) (coreBodies parts plans) C A [] (normalize parts plans e)=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs (original M parts plans) .callByValuePar (sourceExpr M e) x rest ↔
      SObs (RecursiveScannerProductCompiler.target M (coreEntries parts) (coreBodies parts plans)) .callByValueSeq
        (RecursiveScannerProductCompiler.plain M (coreBodies parts plans) [] (normalize parts plans e)) x rest :=
  (normalized_observations_iff M parts plans hReady e he x rest).trans
    (ProfileCheckedScannerCorrespondence.observations_iff M (coreEntries parts) (coreBodies parts plans)
      H C A hH hC hB (normalize parts plans e) hRoot x rest)

theorem language_translation {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan)
    (hReady : readyCheck parts plans=true) (e : Arg) (he : scopeCheck plans e=true)
    (H : RecursiveCaptureProfiles.ScannerSummary n) (C : RecursiveCaptureProfiles.Summary)
    (A : ProfileCheckedScannerCorrespondence.Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M (coreEntries parts) (coreBodies parts plans) H C=true)
    (hB : ProfileCheckedScannerCorrespondence.bodiesCheck M (coreEntries parts) (coreBodies parts plans) C A=true)
    (hRoot : ProfileCheckedScannerCorrespondence.check M (coreEntries parts) (coreBodies parts plans) C A [] (normalize parts plans e)=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (original M parts plans) .callByValuePar (sourceExpr M e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨_,_,RecursiveScannerProductCompiler.target_firstOrder M (coreEntries parts) (coreBodies parts plans),
    RecursiveScannerProductCompiler.plain_firstOrder M (coreBodies parts plans) [] (normalize parts plans e),
    fun x => observations_iff M parts plans hReady e he H C A hH hC hB hRoot x (some [])⟩

theorem defined_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan)
    (hReady : readyCheck parts plans=true) (e : Arg) (he : scopeCheck plans e=true)
    (H : RecursiveCaptureProfiles.ScannerSummary n) (C : RecursiveCaptureProfiles.Summary)
    (A : ProfileCheckedScannerCorrespondence.Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M (coreEntries parts) (coreBodies parts plans) H C=true)
    (hB : ProfileCheckedScannerCorrespondence.bodiesCheck M (coreEntries parts) (coreBodies parts plans) C A=true)
    (hRoot : ProfileCheckedScannerCorrespondence.check M (coreEntries parts) (coreBodies parts plans) C A [] (normalize parts plans e)=true)
    (x : List Char) (v : Option Nat) :
    (∃ k, evV (original M parts plans) x .callByValuePar
      (tblV (original M parts plans) x .callByValuePar k) [] (sourceExpr M e) x.length=some v) ↔
    (∃ k, evV (target M parts plans) x .callByValueSeq
      (tblV (target M parts plans) x .callByValueSeq k) [] (targetExpr M parts plans e) x.length=some v) := by
  have hb := ProfileCheckedScannerCorrespondence.defined_iff M (coreEntries parts) (coreBodies parts plans)
    H C A hH hC hB (normalize parts plans e) hRoot x v
  constructor
  · rintro ⟨k,hk⟩
    exact hb.mp ⟨k,(evaluator_eq M parts plans hReady e he x k [] x.length (Nat.le_refl _)).symm.trans hk⟩
  · intro h
    obtain ⟨k,hk⟩ := hb.mpr h
    exact ⟨k,(evaluator_eq M parts plans hReady e he x k [] x.length (Nat.le_refl _)).trans hk⟩

theorem undefined_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan)
    (hReady : readyCheck parts plans=true) (e : Arg) (he : scopeCheck plans e=true)
    (H : RecursiveCaptureProfiles.ScannerSummary n) (C : RecursiveCaptureProfiles.Summary)
    (A : ProfileCheckedScannerCorrespondence.Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M (coreEntries parts) (coreBodies parts plans) H C=true)
    (hB : ProfileCheckedScannerCorrespondence.bodiesCheck M (coreEntries parts) (coreBodies parts plans) C A=true)
    (hRoot : ProfileCheckedScannerCorrespondence.check M (coreEntries parts) (coreBodies parts plans) C A [] (normalize parts plans e)=true)
    (x : List Char) :
    (∀ k, evV (original M parts plans) x .callByValuePar
      (tblV (original M parts plans) x .callByValuePar k) [] (sourceExpr M e) x.length=none) ↔
    (∀ k, evV (target M parts plans) x .callByValueSeq
      (tblV (target M parts plans) x .callByValueSeq k) [] (targetExpr M parts plans e) x.length=none) := by
  constructor
  · intro h k
    cases hv : evV (target M parts plans) x .callByValueSeq
        (tblV (target M parts plans) x .callByValueSeq k) [] (targetExpr M parts plans e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨l,hl⟩ := (defined_iff M parts plans hReady e he H C A hH hC hB hRoot x v).mpr ⟨k,hv⟩
      rw [h l] at hl
      cases hl
  · intro h k
    cases hv : evV (original M parts plans) x .callByValuePar
        (tblV (original M parts plans) x .callByValuePar k) [] (sourceExpr M e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨l,hl⟩ := (defined_iff M parts plans hReady e he H C A hH hC hB hRoot x v).mp ⟨k,hv⟩
      rw [h l] at hl
      cases hl

end Shallot.MacroPeg.CBV.ScannerOriginControl
