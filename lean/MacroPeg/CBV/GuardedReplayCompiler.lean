import MacroPeg.CBV.GuardedReplayIteration
import MacroPeg.CBV.RecursiveFinitePrefix

namespace Shallot.MacroPeg.CBV.GuardedReplayCompiler
open ScannerOriginControl (Part sourceLeaf)
open RecursiveScannerProductCompiler (Arg sourceExpr)
open ReplayControlFusion (Plan)
open StatefulScanner (Machine)

inductive Body where
  | control (body : RecursiveFinitePrefix.Body)
  | repeated (char : Char) (tail : Arg) (test yes no : Nat)

def rawBody {n : Nat} (M : Machine n) : Body → MExp
  | .control b => RecursiveFinitePrefix.rawBody M b
  | .repeated c tail _ _ _ => .seq (GuardedReplayIteration.header [c]) (sourceExpr M tail)

def bodyPlan (read copy : List Char → Nat) : Body → Plan
  | .control b => RecursiveFinitePrefix.bodyPlan read copy b
  | .repeated _ _ test yes no => FinitePrefixControl.choose (.leaf test) (.leaf yes) (.leaf no)

def bodyCheck {n : Nat} (parts : List (Part n)) (read copy : List Char → Nat) : Body → Bool
  | .control b => RecursiveFinitePrefix.bodyCheck parts read copy b
  | .repeated c tail test yes no =>
      RecursiveFinitePrefix.resumeCheck parts (.lit []) (fun _ => test) [c] &&
      RecursiveFinitePrefix.resumeCheck parts (.seq (.star (.lit [c])) tail) (fun _ => yes) [c] &&
      RecursiveFinitePrefix.resumeCheck parts tail (fun _ => no) []

private theorem nil_tail (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (tail : MExp) (p : Nat) :
    evV g x s T E (.seq (.lit []) (.seq (.param 0) tail)) p=evV g x s T E (.seq (.param 0) tail) p := by
  rw [←LeadingReplayStar.sequence_assoc]
  have hv : evV g x s T E (.seq (.lit []) (.param 0)) p=evV g x s T E (.param 0) p := by
    rw [WordArguments.word_eval g x s T E (.seq (.lit []) (.param 0)) ⟨True.intro,True.intro⟩ p,
      WordArguments.word_eval g x s T E (.param 0) True.intro p]
    simp [WordArguments.value]
  change (match evV g x s T E (.seq (.lit []) (.param 0)) p with
    | some (some q) => evV g x s T E tail q | other => other)=_
  rw [hv]
  rfl

theorem body_eval {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (b : Body) (h : bodyCheck parts read copy b=true) (g : MGrammar) (x : List Char)
    (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) (hp : p≤x.length)
    (hE : CaptureOriginRewrite.Captured x E p) :
    evV g x s T E (rawBody M b) p=evV g x s T E ((bodyPlan read copy b).exp (sourceLeaf M parts)) p := by
  cases b with
  | control b => exact RecursiveFinitePrefix.body_eval M parts read copy b h g x s T E p hp
  | repeated c tail test yes no =>
    obtain ⟨hTy,hN⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hT,hY⟩ := Bool.and_eq_true_iff.mp hTy
    have ht := RecursiveFinitePrefix.resume_sound M parts (.lit []) (fun _ => test) [c] hT g x s T E p
    simp only [sourceExpr] at ht
    rw [←LeadingReplayStar.sequence_assoc,PrefixCaptureQuery.word_empty g x s T E
      (.seq (.lit [c]) (.param 0)) ⟨True.intro,True.intro⟩ p] at ht
    have hy := RecursiveFinitePrefix.resume_sound M parts (.seq (.star (.lit [c])) tail) (fun _ => yes) [c] hY g x s T E p
    simp only [sourceExpr] at hy
    rw [←LeadingReplayStar.sequence_assoc] at hy
    have hn := RecursiveFinitePrefix.resume_sound M parts tail (fun _ => no) [] hN g x s T E p
    rw [nil_tail] at hn
    rw [Plan.exp_eval]
    simp only [bodyPlan,FinitePrefixControl.choose_eval,Plan.eval,ht,hy,hn]
    have hh := GuardedReplayIteration.body_result_captured g x s T E c (sourceExpr M tail) p hp hE
    rw [GuardedReplayIteration.normalized,ChoiceArguments.branch_eval] at hh
    exact hh

def plans (read copy : List Char → Nat) (bodies : List Body) : List Plan := bodies.map (bodyPlan read copy)

def source {n : Nat} (M : Machine n) (bodies : List Body) : MGrammar :=
  ⟨RecursiveScannerProductCompiler.helpers M++bodies.map (fun b => ⟨1,rawBody M b⟩)⟩

def check {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (bodies : List Body) : Bool :=
  bodies.all (bodyCheck parts read copy) &&
    AutomaticOriginControl.check M parts (plans read copy bodies)

theorem raw_firstOrder {n : Nat} (M : Machine n) : ∀ b, (rawBody M b).FirstOrder
  | .control b => RecursiveFinitePrefix.raw_firstOrder M b
  | .repeated _ tail _ _ _ => ⟨⟨⟨True.intro,True.intro⟩,True.intro⟩,RecursiveScannerProductCompiler.sourceExpr_firstOrder M tail⟩

theorem source_firstOrder {n : Nat} (M : Machine n) (bodies : List Body) : (source M bodies).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact RecursiveScannerProductCompiler.helpers_firstOrder M r hr
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    exact raw_firstOrder M b

theorem source_rule {n : Nat} (M : Machine n) (bodies : List Body) (i : Nat) (b : Body)
    (hi : bodies[i]?=some b) :
    ruleAtM (source M bodies).rules (RecursiveScannerProductCompiler.offset M+i)=some ⟨1,rawBody M b⟩ := by
  simp [source,RecursiveScannerProductCompiler.offset,ruleAtM_eq_getElem?,
    List.getElem?_append_right (by omega : (RecursiveScannerProductCompiler.helpers M).length≤(RecursiveScannerProductCompiler.helpers M).length+i),hi]

theorem related {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (bodies : List Body) (h : check M parts read copy bodies=true) :
    CaptureOriginRewrite.Related (source M bodies)
      (ScannerOriginControl.original M parts (plans read copy bodies)) := by
  intro i
  unfold source ScannerOriginControl.original ScannerOriginControl.rules plans
  simp only [ruleAtM_eq_getElem?,List.map_map]
  by_cases hi : i<(RecursiveScannerProductCompiler.helpers M).length
  · simp only [List.getElem?_append_left hi]
    cases (RecursiveScannerProductCompiler.helpers M)[i]? with
    | none => trivial
    | some r => exact ⟨rfl,fun _ _ _ _ _ _ => rfl⟩
  · have hi' : (RecursiveScannerProductCompiler.helpers M).length≤i := by omega
    simp only [List.getElem?_append_right hi',List.getElem?_map]
    cases hb : bodies[i-(RecursiveScannerProductCompiler.helpers M).length]? with
    | none => trivial
    | some b =>
      exact ⟨rfl,fun x T E p hp hE => body_eval M parts read copy b
        ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1) b (List.mem_of_getElem? hb)) _ x .callByValuePar T E p hp hE⟩

theorem observations_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (bodies : List Body) (h : check M parts read copy bodies=true) (e : Arg)
    (he : ScannerOriginControl.scopeCheck (plans read copy bodies) e=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source M bodies) .callByValuePar (RecursiveScannerProductCompiler.sourceExpr M e) x rest ↔
      SObs (ScannerOriginControl.target M parts (plans read copy bodies)) .callByValueSeq
        (ScannerOriginControl.targetExpr M parts (plans read copy bodies) e) x rest :=
  (CaptureOriginRewrite.observations (related M parts read copy bodies h) (source_firstOrder M bodies)
    (ScannerOriginControl.original_firstOrder M parts (plans read copy bodies)) _
    (RecursiveScannerProductCompiler.sourceExpr_firstOrder M e) x rest).trans
      (AutomaticOriginControl.observations_iff M parts _ (Bool.and_eq_true_iff.mp h).2 e he x rest)

theorem language_translation {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (bodies : List Body) (h : check M parts read copy bodies=true) (e : Arg)
    (he : ScannerOriginControl.scopeCheck (plans read copy bodies) e=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source M bodies) .callByValuePar (RecursiveScannerProductCompiler.sourceExpr M e) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  ⟨_,_,RecursiveScannerProductCompiler.target_firstOrder M _ _,
    RecursiveScannerProductCompiler.plain_firstOrder M _ [] _,
    fun x => observations_iff M parts read copy bodies h e he x (some [])⟩

theorem defined_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (bodies : List Body) (h : check M parts read copy bodies=true) (e : Arg)
    (he : ScannerOriginControl.scopeCheck (plans read copy bodies) e=true) (x : List Char) (v : Option Nat) :
    (∃ k, evV (source M bodies) x .callByValuePar (tblV (source M bodies) x .callByValuePar k)
      [] (RecursiveScannerProductCompiler.sourceExpr M e) x.length=some v) ↔
    (∃ k, evV (ScannerOriginControl.target M parts (plans read copy bodies)) x .callByValueSeq
      (tblV (ScannerOriginControl.target M parts (plans read copy bodies)) x .callByValueSeq k) []
      (ScannerOriginControl.targetExpr M parts (plans read copy bodies) e) x.length=some v) := by
  have ha := (Bool.and_eq_true_iff.mp h).2
  obtain ⟨hH,hC,hB,hRoot⟩ := AutomaticOriginControl.certificates M parts _ ha e he
  have hc := ScannerOriginControl.defined_iff M parts _ (Bool.and_eq_true_iff.mp ha).1 e he _ _ _ hH hC hB hRoot x v
  have hp := fun k => CaptureOriginRewrite.physical (related M parts read copy bodies h)
    (source_firstOrder M bodies) (ScannerOriginControl.original_firstOrder M parts (plans read copy bodies)) x k []
    (RecursiveScannerProductCompiler.sourceExpr M e) (RecursiveScannerProductCompiler.sourceExpr_firstOrder M e) x.length (Nat.le_refl _)
  constructor
  · rintro ⟨k,hk⟩
    exact hc.mp ⟨k,(hp k).symm.trans hk⟩
  · intro ht
    obtain ⟨k,hk⟩ := hc.mpr ht
    exact ⟨k,(hp k).trans hk⟩

theorem undefined_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (bodies : List Body) (h : check M parts read copy bodies=true) (e : Arg)
    (he : ScannerOriginControl.scopeCheck (plans read copy bodies) e=true) (x : List Char) :
    (∀ k, evV (source M bodies) x .callByValuePar (tblV (source M bodies) x .callByValuePar k)
      [] (RecursiveScannerProductCompiler.sourceExpr M e) x.length=none) ↔
    (∀ k, evV (ScannerOriginControl.target M parts (plans read copy bodies)) x .callByValueSeq
      (tblV (ScannerOriginControl.target M parts (plans read copy bodies)) x .callByValueSeq k) []
      (ScannerOriginControl.targetExpr M parts (plans read copy bodies) e) x.length=none) := by
  constructor
  · intro hs k
    cases hv : evV (ScannerOriginControl.target M parts (plans read copy bodies)) x .callByValueSeq
        (tblV (ScannerOriginControl.target M parts (plans read copy bodies)) x .callByValueSeq k) []
        (ScannerOriginControl.targetExpr M parts (plans read copy bodies) e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff M parts read copy bodies h e he x v).mpr ⟨k,hv⟩
      rw [hs j] at hj
      cases hj
  · intro ht k
    cases hv : evV (source M bodies) x .callByValuePar (tblV (source M bodies) x .callByValuePar k)
        [] (RecursiveScannerProductCompiler.sourceExpr M e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff M parts read copy bodies h e he x v).mp ⟨k,hv⟩
      rw [ht j] at hj
      cases hj

end Shallot.MacroPeg.CBV.GuardedReplayCompiler
