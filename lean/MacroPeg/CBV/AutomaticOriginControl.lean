import MacroPeg.CBV.UniversalCaptureProfiles
import MacroPeg.CBV.PrefixCaptureQuery

/-! Syntactic source checks suffice for origin-returning body control and
raw retained-value queries. All finite capture annotations are generated. -/
namespace Shallot.MacroPeg.CBV.AutomaticOriginControl
open ScannerOriginControl (Part coreEntries coreBodies normalize expand callArg)
open RecursiveScannerProductCompiler (Arg Entry Entries sourceExpr)
open ReplayControlFusion (Plan)
open StatefulScanner (Machine)

private theorem callArg_scope {n : Nat} (parts : List (Part n)) (bodies : List Arg)
    (j : Nat) (a : Arg) (ha : RecursiveCaptureProfiles.scopeCheck bodies a=true) :
    RecursiveCaptureProfiles.scopeCheck bodies (callArg parts j a)=true := by
  cases hr : parts[j]? with
  | none => simpa [callArg,hr] using ha
  | some r =>
    cases hc : r.closed <;> simp [callArg,hr,hc,ha,RecursiveCaptureProfiles.scopeCheck]

theorem expand_scope {n : Nat} (parts : List (Part n)) (plans : List Plan)
    (a : Arg) (ha : RecursiveCaptureProfiles.scopeCheck (coreBodies parts plans) a=true) :
    ∀ p, ScannerOriginControl.planCheck parts p=true →
      RecursiveCaptureProfiles.scopeCheck (coreBodies parts plans) (expand parts a p)=true
  | .leaf j,h => by
    have hj : j<(coreBodies parts plans).length := by
      simpa [coreBodies] using (of_decide_eq_true h : j<parts.length)
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hj,callArg_scope parts _ j a ha⟩
  | .alt p q,h | .guard p q,h =>
    Bool.and_eq_true_iff.mpr ⟨expand_scope parts plans a ha p (Bool.and_eq_true_iff.mp h).1,
      expand_scope parts plans a ha q (Bool.and_eq_true_iff.mp h).2⟩
  | .notP p,h => expand_scope parts plans a ha p h

theorem normalize_scope {n : Nat} (parts : List (Part n)) (plans : List Plan)
    (hReady : ScannerOriginControl.readyCheck parts plans=true) :
    ∀ e, ScannerOriginControl.scopeCheck plans e=true →
      RecursiveCaptureProfiles.scopeCheck (coreBodies parts plans) (normalize parts plans e)=true
  | .lit _,_ | .param _,_ => rfl
  | .seq a b,h | .alt a b,h =>
    Bool.and_eq_true_iff.mpr ⟨normalize_scope parts plans hReady a (Bool.and_eq_true_iff.mp h).1,
      normalize_scope parts plans hReady b (Bool.and_eq_true_iff.mp h).2⟩
  | .notP a,h | .star a,h => normalize_scope parts plans hReady a h
  | .user i a,h => by
    have hi : i<plans.length := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    have ha := normalize_scope parts plans hReady a (Bool.and_eq_true_iff.mp h).2
    have hr := List.getElem?_eq_getElem hi
    have hp := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hReady).1) plans[i] (List.getElem_mem hi)
    simp only [normalize,hr]
    exact Bool.and_eq_true_iff.mpr ⟨ha,expand_scope parts plans _ ha plans[i] hp⟩

/-- Closed parts use an empty replay entry and need no residual machine.
Other parts require complete fixed shifts or replay/guard/choice entries. -/
def check {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan) : Bool :=
  ScannerOriginControl.readyCheck parts plans &&
    parts.all (fun r => r.closed || UniversalCaptureProfiles.entryCheck M r.entry)

theorem core_checked {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan)
    (h : check M parts plans=true) :
    UniversalCaptureProfiles.check M (coreEntries parts) (coreBodies parts plans)=true := by
  obtain ⟨hr,he⟩ := Bool.and_eq_true_iff.mp h
  unfold UniversalCaptureProfiles.check coreBodies
  rw [List.zipIdx_map]
  apply List.all_eq_true.mpr
  intro bi hbi
  obtain ⟨r,hrm,rfl⟩ := List.mem_map.mp hbi
  have hz := List.mem_zipIdx hrm
  have hb : r.2<parts.length := by simpa using hz.2.1
  have hh : parts[r.2]?=some r.1 := by
    rw [List.getElem?_eq_getElem hb]
    simpa using congrArg some hz.2.2.symm
  have hm : r.1∈parts := List.mem_of_getElem? hh
  have hscope := (Bool.and_eq_true_iff.mp ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp hr).2) r.1 hm)).1
  have hentry := (List.all_eq_true.mp he) r.1 hm
  refine Bool.and_eq_true_iff.mpr ⟨?_,normalize_scope parts plans hr r.1.body hscope⟩
  change UniversalCaptureProfiles.entryCheck M (coreEntries parts r.2)=true
  simp only [coreEntries,hh]
  cases hc : r.1.closed with
  | false => simpa [hc] using hentry
  | true => simp [UniversalCaptureProfiles.entryCheck]

theorem observations_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan)
    (h : check M parts plans=true) (e : Arg) (he : ScannerOriginControl.scopeCheck plans e=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs (ScannerOriginControl.original M parts plans) .callByValuePar (sourceExpr M e) x rest ↔
      SObs (ScannerOriginControl.target M parts plans) .callByValueSeq
        (ScannerOriginControl.targetExpr M parts plans e) x rest :=
  (ScannerOriginControl.normalized_observations_iff M parts plans (Bool.and_eq_true_iff.mp h).1 e he x rest).trans
    (UniversalCaptureProfiles.observations_iff M (coreEntries parts) (coreBodies parts plans)
      (core_checked M parts plans h) (normalize parts plans e)
      (normalize_scope parts plans (Bool.and_eq_true_iff.mp h).1 e he) x rest)

theorem language_translation {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan)
    (h : check M parts plans=true) (e : Arg) (he : ScannerOriginControl.scopeCheck plans e=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (ScannerOriginControl.original M parts plans) .callByValuePar (sourceExpr M e) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  ⟨_,_,RecursiveScannerProductCompiler.target_firstOrder M _ _,
    RecursiveScannerProductCompiler.plain_firstOrder M _ [] _,
    fun x => observations_iff M parts plans h e he x (some [])⟩

theorem certificates {n : Nat} (M : Machine n) (parts : List (Part n)) (plans : List Plan)
    (h : check M parts plans=true) (e : Arg) (he : ScannerOriginControl.scopeCheck plans e=true) :
    RecursiveCaptureProfiles.scannerCheck M (UniversalCaptureProfiles.scannerSummary M)=true ∧
    RecursiveCaptureProfiles.grammarCheck M (coreEntries parts) (coreBodies parts plans)
      (UniversalCaptureProfiles.scannerSummary M) (UniversalCaptureProfiles.summary M)=true ∧
    ProfileCheckedScannerCorrespondence.bodiesCheck M (coreEntries parts) (coreBodies parts plans)
      (UniversalCaptureProfiles.summary M) (UniversalCaptureProfiles.inputs M)=true ∧
    ProfileCheckedScannerCorrespondence.check M (coreEntries parts) (coreBodies parts plans)
      (UniversalCaptureProfiles.summary M) (UniversalCaptureProfiles.inputs M) [] (normalize parts plans e)=true :=
  let hc := core_checked M parts plans h
  ⟨UniversalCaptureProfiles.scanner_checked M,UniversalCaptureProfiles.grammar_checked M _ _ hc,
    UniversalCaptureProfiles.bodies_checked M _ _ hc,
    UniversalCaptureProfiles.expression_checked M _ _ hc [] (by simp [UniversalCaptureProfiles.AllIn]) _
      (normalize_scope parts plans (Bool.and_eq_true_iff.mp h).1 e he)⟩

/-- Raw literal-prefix positive/negative queries can stop before their
actual capture endpoint. Only finite source syntax/entry checks remain. -/
def prefixCheck {n : Nat} (M : Machine n) (parts : List (Part n)) (bodies : List PrefixCaptureQuery.Body) : Bool :=
  PrefixCaptureQuery.syntaxCheck parts bodies && check M parts (PrefixCaptureQuery.plans bodies)

theorem prefix_observations_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (bodies : List PrefixCaptureQuery.Body)
    (h : prefixCheck M parts bodies=true) (e : Arg)
    (he : ScannerOriginControl.scopeCheck (PrefixCaptureQuery.plans bodies) e=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs (PrefixCaptureQuery.source M parts bodies) .callByValuePar (sourceExpr M e) x rest ↔
      SObs (ScannerOriginControl.target M parts (PrefixCaptureQuery.plans bodies)) .callByValueSeq
        (ScannerOriginControl.targetExpr M parts (PrefixCaptureQuery.plans bodies) e) x rest :=
  (PrefixCaptureQuery.normalized_observations_iff M parts bodies (Bool.and_eq_true_iff.mp h).1 e x rest).trans
    (observations_iff M parts (PrefixCaptureQuery.plans bodies) (Bool.and_eq_true_iff.mp h).2 e he x rest)

theorem prefix_language_translation {n : Nat} (M : Machine n) (parts : List (Part n)) (bodies : List PrefixCaptureQuery.Body)
    (h : prefixCheck M parts bodies=true) (e : Arg)
    (he : ScannerOriginControl.scopeCheck (PrefixCaptureQuery.plans bodies) e=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (PrefixCaptureQuery.source M parts bodies) .callByValuePar (sourceExpr M e) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  ⟨_,_,RecursiveScannerProductCompiler.target_firstOrder M _ _,
    RecursiveScannerProductCompiler.plain_firstOrder M _ [] _,
    fun x => prefix_observations_iff M parts bodies h e he x (some [])⟩

theorem prefix_defined_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (bodies : List PrefixCaptureQuery.Body)
    (h : prefixCheck M parts bodies=true) (e : Arg)
    (he : ScannerOriginControl.scopeCheck (PrefixCaptureQuery.plans bodies) e=true)
    (x : List Char) (v : Option Nat) :
    (∃ k, evV (PrefixCaptureQuery.source M parts bodies) x .callByValuePar
      (tblV (PrefixCaptureQuery.source M parts bodies) x .callByValuePar k) [] (sourceExpr M e) x.length=some v) ↔
    (∃ k, evV (ScannerOriginControl.target M parts (PrefixCaptureQuery.plans bodies)) x .callByValueSeq
      (tblV (ScannerOriginControl.target M parts (PrefixCaptureQuery.plans bodies)) x .callByValueSeq k) []
      (ScannerOriginControl.targetExpr M parts (PrefixCaptureQuery.plans bodies) e) x.length=some v) := by
  obtain ⟨hs,hc⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hH,hC,hB,hRoot⟩ := certificates M parts (PrefixCaptureQuery.plans bodies) hc e he
  exact PrefixCaptureQuery.defined_iff M parts bodies hs (Bool.and_eq_true_iff.mp hc).1 e he
    _ _ _ hH hC hB hRoot x v

theorem prefix_undefined_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (bodies : List PrefixCaptureQuery.Body)
    (h : prefixCheck M parts bodies=true) (e : Arg)
    (he : ScannerOriginControl.scopeCheck (PrefixCaptureQuery.plans bodies) e=true) (x : List Char) :
    (∀ k, evV (PrefixCaptureQuery.source M parts bodies) x .callByValuePar
      (tblV (PrefixCaptureQuery.source M parts bodies) x .callByValuePar k) [] (sourceExpr M e) x.length=none) ↔
    (∀ k, evV (ScannerOriginControl.target M parts (PrefixCaptureQuery.plans bodies)) x .callByValueSeq
      (tblV (ScannerOriginControl.target M parts (PrefixCaptureQuery.plans bodies)) x .callByValueSeq k) []
      (ScannerOriginControl.targetExpr M parts (PrefixCaptureQuery.plans bodies) e) x.length=none) := by
  obtain ⟨hs,hc⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hH,hC,hB,hRoot⟩ := certificates M parts (PrefixCaptureQuery.plans bodies) hc e he
  exact PrefixCaptureQuery.undefined_iff M parts bodies hs (Bool.and_eq_true_iff.mp hc).1 e he
    _ _ _ hH hC hB hRoot x

end Shallot.MacroPeg.CBV.AutomaticOriginControl
