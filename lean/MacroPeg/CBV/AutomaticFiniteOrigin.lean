import MacroPeg.CBV.AlphabetOriginControl
import MacroPeg.CBV.AutomaticFinitePrefix

namespace Shallot.MacroPeg.CBV.AutomaticFiniteOrigin
open RecursiveScannerProductCompiler (Arg sourceExpr helpers)
open ReplayControlFusion (Plan)
open FinitePrefixMachines (Word machine read finish)

/-- A dependent leaf has a raw guarded-control header and a recursive body.
A closed leaf has only its body; capture independence is checked structurally. -/
structure Part where
  control : AutomaticFinitePrefix.Control
  body : Arg
  closed : Bool := false

def scripts (parts : List Part) := parts.map Part.control
def pool (parts : List Part) := AutomaticFinitePrefix.words (scripts parts)
abbrev size (parts : List Part) := FinitePrefixMachines.Size (pool parts)

def annotated (alphabet : List Char) (parts : List Part) : List (ScannerOriginControl.Part (size parts)) :=
  parts.map (fun r => ⟨.aligned (AutomaticFinitePrefix.normalized alphabet (pool parts) r.control),r.body,r.closed⟩)

def planCheck (parts : List Part) : Plan → Bool
  | .leaf i => decide (i<parts.length)
  | .alt a b | .guard a b => planCheck parts a && planCheck parts b
  | .notP a => planCheck parts a

def readyCheck (parts : List Part) (plans : List Plan) : Bool :=
  plans.all (planCheck parts) && parts.all (fun r =>
    ScannerOriginControl.scopeCheck plans r.body && (!r.closed || ScannerOriginControl.independent r.body))

theorem plan_annotation (alphabet : List Char) (parts : List Part) : ∀ p,
    ScannerOriginControl.planCheck (annotated alphabet parts) p=planCheck parts p
  | .leaf _ => by simp [planCheck,ScannerOriginControl.planCheck,annotated]
  | .alt a b | .guard a b => by
    simp only [planCheck,ScannerOriginControl.planCheck,plan_annotation alphabet parts a,plan_annotation alphabet parts b]
  | .notP a => plan_annotation alphabet parts a

theorem ready_annotation (alphabet : List Char) (parts : List Part) (plans : List Plan) :
    ScannerOriginControl.readyCheck (annotated alphabet parts) plans=readyCheck parts plans := by
  unfold ScannerOriginControl.readyCheck readyCheck
  rw [show ScannerOriginControl.planCheck (annotated alphabet parts)=planCheck parts from funext (plan_annotation alphabet parts)]
  simp only [annotated,List.all_map,Function.comp_def]

theorem annotated_lookup (alphabet : List Char) (parts : List Part) (j : Nat) :
    (annotated alphabet parts)[j]?=parts[j]?.map (fun r =>
      ⟨.aligned (AutomaticFinitePrefix.normalized alphabet (pool parts) r.control),r.body,r.closed⟩) :=
  List.getElem?_map

theorem supported (parts : List Part) (r : Part) (hr : r∈parts) :
    AutomaticFinitePrefix.controlSupport r.control⊆pool parts :=
  fun _ hv => List.mem_flatMap.mpr ⟨r.control,List.mem_map.mpr ⟨r,hr,rfl⟩,hv⟩

def check (alphabet : List Char) (parts : List Part) (plans : List Plan) : Bool :=
  readyCheck parts plans && ((pool parts).all (fun w => w.all (fun c => alphabet.contains c)) &&
    parts.all (fun r => AlphabetCaptureProfiles.literalCheck alphabet r.body))

theorem certificates (alphabet : List Char) (parts : List Part) (plans : List Plan)
    (h : check alphabet parts plans=true) :
    AlphabetOriginControl.check (machine alphabet (pool parts)) (annotated alphabet parts) plans alphabet=true := by
  obtain ⟨hr,hw⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hw,hb⟩ := Bool.and_eq_true_iff.mp hw
  have hW : ∀ w∈pool parts, Word alphabet w := fun w hw' c hc =>
    List.contains_iff_mem.mp ((List.all_eq_true.mp ((List.all_eq_true.mp hw) w hw')) c hc)
  refine Bool.and_eq_true_iff.mpr ⟨by simpa only [ready_annotation] using hr,?_⟩
  refine Bool.and_eq_true_iff.mpr ⟨FinitePrefixMachines.machine_alphabet alphabet (pool parts) hW,?_⟩
  apply List.all_eq_true.mpr
  intro s hs
  obtain ⟨r,hrm,rfl⟩ := List.mem_map.mp hs
  have hG := AutomaticFinitePrefix.normalized_good alphabet (pool parts) hW r.control (supported parts r hrm)
  exact Bool.and_eq_true_iff.mpr ⟨(List.all_eq_true.mp hb) r hrm,
    Bool.or_eq_true_iff.mpr (Or.inr (Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨hG.1,hG.2.1⟩,List.all_eq_true.mpr hG.2.2⟩))⟩

def rawLeaf (alphabet : List Char) (parts : List Part) (j : Nat) : MExp :=
  match parts[j]? with
  | none => MExp.failAlways
  | some r => if r.closed then sourceExpr (machine alphabet (pool parts)) r.body
    else .seq (.seq (AutomaticFinitePrefix.rawControl r.control) (.param 0))
      (sourceExpr (machine alphabet (pool parts)) r.body)

def source (alphabet : List Char) (parts : List Part) (plans : List Plan) : MGrammar :=
  ⟨helpers (machine alphabet (pool parts)) ++ plans.map (fun p => ⟨1,p.exp (rawLeaf alphabet parts)⟩)⟩

theorem source_rule (alphabet : List Char) (parts : List Part) (plans : List Plan)
    (i : Nat) (plan : Plan) (hi : plans[i]?=some plan) :
    ruleAtM (source alphabet parts plans).rules
      (RecursiveScannerProductCompiler.offset (machine alphabet (pool parts))+i)=
        some ⟨1,plan.exp (rawLeaf alphabet parts)⟩ := by
  simp only [source,RecursiveScannerProductCompiler.offset,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,List.getElem?_map,hi,Option.map_some]

abbrev compiled (alphabet : List Char) (parts : List Part) (plans : List Plan) :=
  ScannerOriginControl.target (machine alphabet (pool parts)) (annotated alphabet parts) plans
abbrev targetExpr (alphabet : List Char) (parts : List Part) (plans : List Plan) (e : Arg) :=
  ScannerOriginControl.targetExpr (machine alphabet (pool parts)) (annotated alphabet parts) plans e

/-- Actual raw source leaf equality holds under arbitrary environments and
tables; alphabet/capture certificates are only needed by the later backend. -/
theorem leaf_eval (alphabet : List Char) (parts : List Part) (g : MGrammar) (x : List Char)
    (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) (hp : p≤x.length) (j : Nat) :
    evV g x s T E (rawLeaf alphabet parts j) p=
      evV g x s T E (ScannerOriginControl.sourceLeaf (machine alphabet (pool parts)) (annotated alphabet parts) j) p := by
  cases hr : parts[j]? with
  | none => simp only [rawLeaf,ScannerOriginControl.sourceLeaf,annotated_lookup,hr,Option.map_none]
  | some r =>
    have hN := GuardedFinitePrefix.normalize_eval (read alphabet (pool parts)) (finish (pool parts)) g x s T E
      (AutomaticFinitePrefix.annotate alphabet (pool parts) r.control)
      (AutomaticFinitePrefix.control_checked alphabet (pool parts) r.control (supported parts r (List.mem_of_getElem? hr))) p hp
    rw [AutomaticFinitePrefix.original_annotate] at hN
    simp only [rawLeaf,ScannerOriginControl.sourceLeaf,annotated_lookup,hr,Option.map_some]
    cases hc : r.closed with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true,ite_false,RecursiveScannerProductCompiler.sourceHeader,
        GuardedReplayControl.header,AutomaticFinitePrefix.normalized,evV,hN]

theorem body_eval (alphabet : List Char) (parts : List Part) (g : MGrammar) (x : List Char)
    (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) (hp : p≤x.length) (plan : Plan) :
    evV g x s T E (plan.exp (rawLeaf alphabet parts)) p=
      evV g x s T E (plan.exp (ScannerOriginControl.sourceLeaf (machine alphabet (pool parts)) (annotated alphabet parts))) p := by
  rw [Plan.exp_eval,Plan.exp_eval]
  exact Plan.eval_congr plan (Plan.all_of_forall (fun j => leaf_eval alphabet parts g x s T E p hp j) plan)

theorem rawLeaf_firstOrder (alphabet : List Char) (parts : List Part) (j : Nat) :
    (rawLeaf alphabet parts j).FirstOrder := by
  unfold rawLeaf
  cases hr : parts[j]? with
  | none => trivial
  | some r =>
    have hb := RecursiveScannerProductCompiler.sourceExpr_firstOrder (machine alphabet (pool parts)) r.body
    have hc : (AutomaticFinitePrefix.rawControl r.control).FirstOrder :=
      AutomaticFinitePrefix.original_annotate alphabet (pool parts) r.control ▸
        GuardedFinitePrefix.original_firstOrder (AutomaticFinitePrefix.annotate alphabet (pool parts) r.control)
    cases hd : r.closed
    · simpa only [hd,Bool.false_eq_true,ite_false,MExp.FirstOrder] using And.intro (And.intro hc True.intro) hb
    · simpa only [hd,ite_true] using hb

theorem source_firstOrder (alphabet : List Char) (parts : List Part) (plans : List Plan) :
    (source alphabet parts plans).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact RecursiveScannerProductCompiler.helpers_firstOrder _ r hr
  · obtain ⟨plan,_,rfl⟩ := List.mem_map.mp hr
    exact Plan.exp_firstOrder (rawLeaf_firstOrder alphabet parts) plan

theorem related (alphabet : List Char) (parts : List Part) (plans : List Plan) :
    SemanticBodyRewrite.Related (source alphabet parts plans)
      (ScannerOriginControl.original (machine alphabet (pool parts)) (annotated alphabet parts) plans) .callByValuePar := by
  intro i
  unfold source ScannerOriginControl.original ScannerOriginControl.rules
  simp only [ruleAtM_eq_getElem?]
  by_cases hi : i<(helpers (machine alphabet (pool parts))).length
  · simp only [List.getElem?_append_left hi]
    cases (helpers (machine alphabet (pool parts)))[i]? with
    | none => trivial
    | some r => exact ⟨rfl,fun _ _ _ _ _ => rfl⟩
  · have hi' : (helpers (machine alphabet (pool parts))).length≤i := by omega
    simp only [List.getElem?_append_right hi',List.getElem?_map]
    cases hp : plans[i-(helpers (machine alphabet (pool parts))).length]? with
    | none => trivial
    | some plan => exact ⟨rfl,fun x T E p hp => body_eval alphabet parts _ x .callByValuePar T E p hp plan⟩

theorem observations_iff (alphabet : List Char) (parts : List Part) (plans : List Plan)
    (h : check alphabet parts plans=true) (e : Arg) (he : ScannerOriginControl.scopeCheck plans e=true)
    (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source alphabet parts plans) .callByValuePar (sourceExpr (machine alphabet (pool parts)) e) x rest ↔
      SObs (compiled alphabet parts plans) .callByValueSeq (targetExpr alphabet parts plans e) x rest :=
  (SemanticBodyRewrite.observations (related alphabet parts plans) (source_firstOrder alphabet parts plans)
    (ScannerOriginControl.original_firstOrder _ _ plans) (by decide) _
    (RecursiveScannerProductCompiler.sourceExpr_firstOrder _ e) x rest).trans
      (AlphabetOriginControl.observations_iff _ _ plans alphabet (certificates alphabet parts plans h) e he ha x rest)

theorem language_translation (alphabet : List Char) (parts : List Part) (plans : List Plan)
    (h : check alphabet parts plans=true) (e : Arg) (he : ScannerOriginControl.scopeCheck plans e=true)
    (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (source alphabet parts plans) .callByValuePar (sourceExpr (machine alphabet (pool parts)) e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨_,_,RecursiveScannerProductCompiler.target_firstOrder _ _ _,
    RecursiveScannerProductCompiler.plain_firstOrder _ _ [] _,
    fun x => observations_iff alphabet parts plans h e he ha x (some [])⟩

theorem defined_iff (alphabet : List Char) (parts : List Part) (plans : List Plan)
    (h : check alphabet parts plans=true) (e : Arg) (he : ScannerOriginControl.scopeCheck plans e=true)
    (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true) (x : List Char) (v : Option Nat) :
    (∃ k, evV (source alphabet parts plans) x .callByValuePar (tblV (source alphabet parts plans) x .callByValuePar k)
      [] (sourceExpr (machine alphabet (pool parts)) e) x.length=some v) ↔
    (∃ k, evV (compiled alphabet parts plans) x .callByValueSeq (tblV (compiled alphabet parts plans) x .callByValueSeq k)
      [] (targetExpr alphabet parts plans e) x.length=some v) := by
  have hc := AlphabetOriginControl.defined_iff _ _ plans alphabet (certificates alphabet parts plans h) e he ha x v
  have hp := fun k => SemanticBodyRewrite.physical (related alphabet parts plans) x k []
    (sourceExpr (machine alphabet (pool parts)) e) x.length
  constructor
  · rintro ⟨k,hk⟩
    exact hc.mp ⟨k,(hp k).symm.trans hk⟩
  · intro ht
    obtain ⟨k,hk⟩ := hc.mpr ht
    exact ⟨k,(hp k).trans hk⟩

theorem undefined_iff (alphabet : List Char) (parts : List Part) (plans : List Plan)
    (h : check alphabet parts plans=true) (e : Arg) (he : ScannerOriginControl.scopeCheck plans e=true)
    (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true) (x : List Char) :
    (∀ k, evV (source alphabet parts plans) x .callByValuePar (tblV (source alphabet parts plans) x .callByValuePar k)
      [] (sourceExpr (machine alphabet (pool parts)) e) x.length=none) ↔
    (∀ k, evV (compiled alphabet parts plans) x .callByValueSeq (tblV (compiled alphabet parts plans) x .callByValueSeq k)
      [] (targetExpr alphabet parts plans e) x.length=none) := by
  constructor
  · intro hs k
    cases hv : evV (compiled alphabet parts plans) x .callByValueSeq
        (tblV (compiled alphabet parts plans) x .callByValueSeq k) [] (targetExpr alphabet parts plans e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff alphabet parts plans h e he ha x v).mpr ⟨k,hv⟩
      rw [hs j] at hj
      cases hj
  · intro ht k
    cases hv : evV (source alphabet parts plans) x .callByValuePar
        (tblV (source alphabet parts plans) x .callByValuePar k) [] (sourceExpr (machine alphabet (pool parts)) e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff alphabet parts plans h e he ha x v).mp ⟨k,hv⟩
      rw [ht j] at hj
      cases hj

/-- Source letters, including independent leaves, are collected automatically. -/
def alphabet (parts : List Part) (root : Arg) : List Char :=
  ((pool parts).flatten ++ parts.flatMap (fun r => AutomaticFinitePrefix.argAlphabet r.body) ++
    AutomaticFinitePrefix.argAlphabet root).eraseDups

theorem automatic_check (parts : List Part) (plans : List Plan) (root : Arg)
    (hr : readyCheck parts plans=true) : check (alphabet parts root) parts plans=true := by
  refine Bool.and_eq_true_iff.mpr ⟨hr,Bool.and_eq_true_iff.mpr ⟨?_,?_⟩⟩
  · apply List.all_eq_true.mpr
    intro w hw
    apply List.all_eq_true.mpr
    intro c hc
    exact List.contains_iff_mem.mpr (List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatten.mpr ⟨w,hw,hc⟩))))
  · apply List.all_eq_true.mpr
    intro r hR
    apply AutomaticFinitePrefix.arg_literal_checked
    intro c hc
    exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨r,hR,hc⟩)))

theorem root_literal_checked (parts : List Part) (root : Arg) :
    AlphabetCaptureProfiles.literalCheck (alphabet parts root) root=true :=
  AutomaticFinitePrefix.arg_literal_checked _ root (fun _ hc => List.mem_eraseDups.mpr (List.mem_append_right _ hc))

theorem automatic_language_translation (parts : List Part) (plans : List Plan) (root : Arg)
    (hr : readyCheck parts plans=true) (he : ScannerOriginControl.scopeCheck plans root=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (source (alphabet parts root) parts plans) .callByValuePar
        (sourceExpr (machine (alphabet parts root) (pool parts)) root) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  language_translation _ parts plans (automatic_check parts plans root hr) root he (root_literal_checked parts root)

end Shallot.MacroPeg.CBV.AutomaticFiniteOrigin
