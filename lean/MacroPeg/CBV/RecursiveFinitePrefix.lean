import MacroPeg.CBV.FinitePrefixControl

namespace Shallot.MacroPeg.CBV.RecursiveFinitePrefix
open FinitePrefixControl (Prefix raw outputs compile checkAt)
open ScannerOriginControl (Part sourceLeaf)
open RecursiveScannerProductCompiler (Arg Entry sourceExpr)
open ReplayControlFusion (Plan)
open StatefulScanner (Machine)

deriving instance DecidableEq for SequentialRecursiveObserver.Expr

/-- A prefix may finish directly, or replay its complete retained value
and enter an arbitrary recursive continuation. Links are finite syntax data. -/
inductive Body where
  | finish (head : Prefix)
  | resume (head : Prefix) (tail : Arg) (links : List Char → Nat)

def rawBody {n : Nat} (M : Machine n) : Body → MExp
  | .finish e => raw e
  | .resume e tail _ => .seq (raw e) (.seq (.param 0) (sourceExpr M tail))

def bodyPlan (read copy : List Char → Nat) : Body → Plan
  | .finish e => FinitePrefixControl.plan read copy e
  | .resume e _ links => compile read copy e [] (fun u => .leaf (links u))

def resumeCheck {n : Nat} (parts : List (Part n)) (tail : Arg) (links : List Char → Nat) (u : List Char) : Bool :=
  match parts[links u]? with
  | none => false
  | some r => !r.closed && decide (r.body=tail) && match r.entry with
    | .replay => decide (u=[])
    | .shift q R => decide ((R q).getD []=u)
    | _ => false

def bodyCheck {n : Nat} (parts : List (Part n)) (read copy : List Char → Nat) : Body → Bool
  | .finish e => checkAt parts read copy e []
  | .resume e tail links => checkAt parts read copy e [] && (outputs e).all (resumeCheck parts tail links)

theorem resume_sound {n : Nat} (M : Machine n) (parts : List (Part n)) (tail : Arg)
    (links : List Char → Nat) (u : List Char) (h : resumeCheck parts tail links u=true)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (p : Nat) :
    evV g x s T E (sourceLeaf M parts (links u)) p=
      evV g x s T E (.seq (.lit u) (.seq (.param 0) (sourceExpr M tail))) p := by
  unfold resumeCheck at h
  cases hr : parts[links u]? with
  | none => simp [hr] at h
  | some r =>
    simp only [hr] at h
    obtain ⟨hf,he⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hc,hb⟩ := Bool.and_eq_true_iff.mp hf
    have hclosed : r.closed=false := by simpa using hc
    have hbody : r.body=tail := of_decide_eq_true hb
    cases hent : r.entry <;> simp only [hent] at he
    all_goals try contradiction
    case replay =>
      have hu : u=[] := of_decide_eq_true he
      subst u
      simp only [sourceLeaf,hr,hclosed,Bool.false_eq_true,ite_false,hent,hbody,
        RecursiveScannerProductCompiler.sourceHeader]
      rw [←LeadingReplayStar.sequence_assoc g x s T E (.lit []) (.param 0) (sourceExpr M tail) p]
      have hv : evV g x s T E (.seq (.lit []) (.param 0)) p=evV g x s T E (.param 0) p := by
        rw [WordArguments.word_eval g x s T E (.seq (.lit []) (.param 0)) ⟨True.intro,True.intro⟩ p,
          WordArguments.word_eval g x s T E (.param 0) True.intro p]
        simp [WordArguments.value]
      change (match evV g x s T E (.param 0) p with
        | some (some q) => evV g x s T E (sourceExpr M tail) q | other => other)=
        (match evV g x s T E (.seq (.lit []) (.param 0)) p with
        | some (some q) => evV g x s T E (sourceExpr M tail) q | other => other)
      rw [hv]
    case shift q R =>
      have hu := of_decide_eq_true he
      simp only [sourceLeaf,hr,hclosed,Bool.false_eq_true,ite_false,hent,hbody,
        RecursiveScannerProductCompiler.sourceHeader,hu]
      exact LeadingReplayStar.sequence_assoc g x s T E (.lit u) (.param 0) (sourceExpr M tail) p

theorem body_eval {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (b : Body) (h : bodyCheck parts read copy b=true) (g : MGrammar) (x : List Char)
    (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (rawBody M b) p=evV g x s T E ((bodyPlan read copy b).exp (sourceLeaf M parts)) p := by
  cases b with
  | finish e => exact FinitePrefixControl.body_eval M parts read copy e h g x s T E p hp
  | resume e tail links =>
    obtain ⟨he,hl⟩ := Bool.and_eq_true_iff.mp h
    rw [Plan.exp_eval]
    have hc := FinitePrefixControl.compile_eval M parts read copy g x s T E p hp e [] he p hp
      (by simp [evV,Shallot.stripPrefix?,length_sfx x hp]) (fun u => .leaf (links u))
      (fun q => evV g x s T E (.seq (.param 0) (sourceExpr M tail)) q) (by
        intro v hv q hq
        change evV g x s T E (sourceLeaf M parts (links ([]++v))) p=_
        simp only [List.nil_append] at hq ⊢
        rw [resume_sound M parts tail links _ ((List.all_eq_true.mp hl) v hv) g x s T E p,evV_seq_ok hq])
    exact hc.symm

def plans (read copy : List Char → Nat) (bodies : List Body) : List Plan := bodies.map (bodyPlan read copy)

def source {n : Nat} (M : Machine n) (bodies : List Body) : MGrammar :=
  ⟨RecursiveScannerProductCompiler.helpers M++bodies.map (fun b => ⟨1,rawBody M b⟩)⟩

def check {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (bodies : List Body) : Bool :=
  bodies.all (bodyCheck parts read copy) &&
    AutomaticOriginControl.check M parts (plans read copy bodies)

theorem raw_firstOrder {n : Nat} (M : Machine n) : ∀ b, (rawBody M b).FirstOrder
  | .finish e => FinitePrefixControl.raw_firstOrder e
  | .resume e tail _ => ⟨FinitePrefixControl.raw_firstOrder e,True.intro,RecursiveScannerProductCompiler.sourceExpr_firstOrder M tail⟩

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
    SemanticBodyRewrite.Related (source M bodies)
      (ScannerOriginControl.original M parts (plans read copy bodies)) .callByValuePar := by
  intro i
  unfold source ScannerOriginControl.original ScannerOriginControl.rules plans
  simp only [ruleAtM_eq_getElem?,List.map_map]
  by_cases hi : i<(RecursiveScannerProductCompiler.helpers M).length
  · simp only [List.getElem?_append_left hi]
    cases (RecursiveScannerProductCompiler.helpers M)[i]? with
    | none => trivial
    | some r => exact ⟨rfl,fun _ _ _ _ _ => rfl⟩
  · have hi' : (RecursiveScannerProductCompiler.helpers M).length≤i := by omega
    simp only [List.getElem?_append_right hi',List.getElem?_map]
    cases hb : bodies[i-(RecursiveScannerProductCompiler.helpers M).length]? with
    | none => trivial
    | some b =>
      exact ⟨rfl,fun x T E p hp => body_eval M parts read copy b
        ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1) b (List.mem_of_getElem? hb)) _ x .callByValuePar T E p hp⟩

theorem observations_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (bodies : List Body) (h : check M parts read copy bodies=true) (e : Arg)
    (he : ScannerOriginControl.scopeCheck (plans read copy bodies) e=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source M bodies) .callByValuePar (RecursiveScannerProductCompiler.sourceExpr M e) x rest ↔
      SObs (ScannerOriginControl.target M parts (plans read copy bodies)) .callByValueSeq
        (ScannerOriginControl.targetExpr M parts (plans read copy bodies) e) x rest :=
  (SemanticBodyRewrite.observations (related M parts read copy bodies h) (source_firstOrder M bodies)
    (ScannerOriginControl.original_firstOrder M parts _) (by decide) _
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
  have hp := fun k => SemanticBodyRewrite.physical (related M parts read copy bodies h) x k []
    (RecursiveScannerProductCompiler.sourceExpr M e) x.length
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

end Shallot.MacroPeg.CBV.RecursiveFinitePrefix
