import MacroPeg.CBV.ScannerOriginControl
import MacroPeg.CBV.SemanticBodyRewrite

namespace Shallot.MacroPeg.CBV.PrefixCaptureQuery
open ScannerOriginControl (Part sourceLeaf coreEntries coreBodies normalize target targetExpr readyCheck scopeCheck)
open RecursiveScannerProductCompiler (Arg sourceExpr helpers offset)
open ReplayControlFusion (Plan)
open StatefulScanner (Machine)

def query (positive : Bool) (e : MExp) : MExp := if positive then .andP e else .notP e

def afterPlan (positive : Bool) (read copy : Nat) : Plan :=
  .guard (if positive then .leaf copy else .notP (.leaf copy)) (.leaf read)

/-- Test the combined prefix/query at the old origin, then consume the
same prefix. Deterministic re-evaluation preserves all partial results.
The identity holds for arbitrary prefixes and queries, not just literals. -/
theorem prefix_query (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (a b : MExp) (positive : Bool)
    (L : Nat → MExp) (read copy p : Nat)
    (hr : evV g x s T E (L read) p=evV g x s T E a p)
    (hc : evV g x s T E (L copy) p=evV g x s T E (.seq a b) p) :
    evV g x s T E (.seq a (query positive b)) p=
      evV g x s T E ((afterPlan positive read copy).exp L) p := by
  rw [Plan.exp_eval]
  cases ha : evV g x s T E a p with
  | none => cases positive <;> simp [afterPlan,Plan.eval,hc,evV,ha]
  | some result => cases result with
    | none => cases positive <;> simp [afterPlan,Plan.eval,hr,hc,evV,ha]
    | some q =>
      cases hb : evV g x s T E b q with
      | none => cases positive <;> simp [afterPlan,Plan.eval,hc,query,evV,ha,hb,MExp.andP]
      | some v => cases v <;> cases positive <;> simp [afterPlan,Plan.eval,hr,hc,query,evV,ha,hb,MExp.andP]

/-- A trailing empty literal is removed from actual word evaluation,
without a table validity or successful-evaluation assumption. -/
theorem word_empty (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (e : MExp) (he : WordArguments.Word e) (p : Nat) :
    evV g x s T E (.seq e (.lit [])) p=evV g x s T E e p := by
  rw [WordArguments.word_eval g x s T E (.seq e (.lit [])) ⟨he,True.intro⟩ p,
    WordArguments.word_eval g x s T E e he p]
  cases hw : WordArguments.value E e <;> simp [WordArguments.value,hw,WordArguments.literal]

structure Link where
  read : Nat
  copy : Nat

def prefixWord {n : Nat} (parts : List (Part n)) (link : Link) : List Char :=
  match parts[link.copy]? with
  | some r => match r.entry with | .shift q R => (R q).getD [] | _ => []
  | none => []

/-- These are finite syntax links to an independent literal leaf and an
actual shifted replay leaf with empty continuation. -/
def linkCheck {n : Nat} (parts : List (Part n)) (link : Link) : Bool :=
  match parts[link.copy]?,parts[link.read]? with
  | some c,some r => !c.closed && r.closed && match c.entry,c.body,r.body with
    | .shift q R,.lit [],.lit u => decide (u=(R q).getD [])
    | _,_,_ => false
  | _,_ => false

theorem link_sound {n : Nat} (M : Machine n) (parts : List (Part n)) (link : Link)
    (h : linkCheck parts link=true) :
    sourceLeaf M parts link.read=.lit (prefixWord parts link) ∧
    sourceLeaf M parts link.copy=.seq (.seq (.lit (prefixWord parts link)) (.param 0)) (.lit []) := by
  unfold linkCheck at h
  cases hc : parts[link.copy]? with
  | none => simp [hc] at h
  | some c =>
    cases hr : parts[link.read]? with
    | none => simp [hc,hr] at h
    | some r =>
      simp only [hc,hr] at h
      have hflags := Bool.and_eq_true_iff.mp h
      have hcf : c.closed=false := by simpa using (Bool.and_eq_true_iff.mp hflags.1).1
      have hrt : r.closed=true := (Bool.and_eq_true_iff.mp hflags.1).2
      have hh := hflags.2
      cases he : c.entry <;> cases hb : c.body <;> cases hd : r.body <;>
        simp only [he,hb,hd] at hh
      all_goals try contradiction
      rename_i q R v u
      cases v with
      | cons a v => simp at hh
      | nil =>
        have hu : u=(R q).getD [] := of_decide_eq_true hh
        simp [sourceLeaf,hc,hr,hcf,hrt,prefixWord,he,hb,hd,hu,RecursiveScannerProductCompiler.sourceHeader,sourceExpr]

inductive Body where
  | leaf : Nat → Body
  | after (positive : Bool) (link : Link)
  | alt : Body → Body → Body
  | notP : Body → Body
  | guard : Body → Body → Body

def lower : Body → Plan
  | .leaf j => .leaf j
  | .after positive link => afterPlan positive link.read link.copy
  | .alt a b => .alt (lower a) (lower b)
  | .notP a => .notP (lower a)
  | .guard a b => .guard (lower a) (lower b)

def raw {n : Nat} (M : Machine n) (parts : List (Part n)) : Body → MExp
  | .leaf j => sourceLeaf M parts j
  | .after positive link => .seq (.lit (prefixWord parts link)) (query positive (.param 0))
  | .alt a b => .alt (raw M parts a) (raw M parts b)
  | .notP a => .notP (raw M parts a)
  | .guard a b => .seq (.andP (raw M parts a)) (raw M parts b)

def bodyCheck {n : Nat} (parts : List (Part n)) : Body → Bool
  | .leaf _ => true
  | .after _ link => linkCheck parts link
  | .alt a b | .guard a b => bodyCheck parts a && bodyCheck parts b
  | .notP a => bodyCheck parts a

theorem body_eval {n : Nat} (M : Machine n) (parts : List (Part n))
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) :
    ∀ b, bodyCheck parts b=true → ∀ p,
    evV g x s T E (raw M parts b) p=
      evV g x s T E ((lower b).exp (sourceLeaf M parts)) p
  | .leaf _,_,_ => rfl
  | .after positive link,h,p => by
    have hh := link_sound M parts link h
    apply prefix_query g x s T E (.lit (prefixWord parts link)) (.param 0) positive
      (sourceLeaf M parts) link.read link.copy p
    · rw [hh.1]
    · rw [hh.2]
      exact word_empty g x s T E (.seq (.lit (prefixWord parts link)) (.param 0)) ⟨True.intro,True.intro⟩ p
  | .alt a b,h,p | .guard a b,h,p => by
    have ha := body_eval M parts g x s T E a (Bool.and_eq_true_iff.mp h).1
    have hb := body_eval M parts g x s T E b (Bool.and_eq_true_iff.mp h).2
    simp only [raw,lower,Plan.exp,MExp.andP,evV,ha,hb]
  | .notP a,h,p => by simp only [raw,lower,Plan.exp,evV,body_eval M parts g x s T E a h]

def liftPlan : Plan → Body
  | .leaf j => .leaf j
  | .alt a b => .alt (liftPlan a) (liftPlan b)
  | .notP a => .notP (liftPlan a)
  | .guard a b => .guard (liftPlan a) (liftPlan b)

theorem lower_lift : ∀ p, lower (liftPlan p)=p
  | .leaf _ => rfl
  | .alt a b | .guard a b => by simp only [liftPlan,lower,lower_lift a,lower_lift b]
  | .notP a => by simp only [liftPlan,lower,lower_lift a]

def plans (bodies : List Body) : List Plan := bodies.map lower

def source {n : Nat} (M : Machine n) (parts : List (Part n)) (bodies : List Body) : MGrammar :=
  ⟨helpers M++bodies.map (fun b => ⟨1,raw M parts b⟩)⟩

def syntaxCheck {n : Nat} (parts : List (Part n)) (bodies : List Body) : Bool :=
  bodies.all (bodyCheck parts)

theorem sourceLeaf_firstOrder {n : Nat} (M : Machine n) (parts : List (Part n)) (j : Nat) :
    (sourceLeaf M parts j).FirstOrder := by
  unfold sourceLeaf
  cases parts[j]? with
  | none => trivial
  | some r =>
    change (if r.closed then sourceExpr M r.body else .seq
      (RecursiveScannerProductCompiler.sourceHeader r.entry) (sourceExpr M r.body)).FirstOrder
    split
    · exact RecursiveScannerProductCompiler.sourceExpr_firstOrder M r.body
    · exact ⟨RecursiveScannerProductCompiler.sourceHeader_firstOrder r.entry,
        RecursiveScannerProductCompiler.sourceExpr_firstOrder M r.body⟩

theorem raw_firstOrder {n : Nat} (M : Machine n) (parts : List (Part n)) : ∀ b, (raw M parts b).FirstOrder
  | .leaf j => sourceLeaf_firstOrder M parts j
  | .after positive _ => by cases positive <;> trivial
  | .alt a b | .guard a b => ⟨raw_firstOrder M parts a,raw_firstOrder M parts b⟩
  | .notP a => raw_firstOrder M parts a

theorem source_firstOrder {n : Nat} (M : Machine n) (parts : List (Part n)) (bodies : List Body) :
    (source M parts bodies).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact RecursiveScannerProductCompiler.helpers_firstOrder M r hr
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    exact raw_firstOrder M parts b

/-- The finite link checker supplies every body rewrite of the actual
recursive grammar. No table equality is assumed. -/
theorem related {n : Nat} (M : Machine n) (parts : List (Part n)) (bodies : List Body)
    (h : syntaxCheck parts bodies=true) :
    SemanticBodyRewrite.Related (source M parts bodies)
      (ScannerOriginControl.original M parts (plans bodies)) .callByValuePar := by
  intro i
  unfold source ScannerOriginControl.original ScannerOriginControl.rules plans
  simp only [ruleAtM_eq_getElem?,List.map_map]
  by_cases hi : i<(helpers M).length
  · simp only [List.getElem?_append_left hi]
    cases (helpers M)[i]? with
    | none => trivial
    | some r => exact ⟨rfl,fun _ _ _ _ _ => rfl⟩
  · have hi' : (helpers M).length≤i := by omega
    simp only [List.getElem?_append_right hi',List.getElem?_map]
    cases hb : bodies[i-(helpers M).length]? with
    | none => trivial
    | some b =>
      exact ⟨rfl,fun x T E p _ => body_eval M parts _ x .callByValuePar T E b
        ((List.all_eq_true.mp h) b (List.mem_of_getElem? hb)) p⟩

theorem physical {n : Nat} (M : Machine n) (parts : List (Part n)) (bodies : List Body)
    (h : syntaxCheck parts bodies=true) (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp) (p : Nat) :
    evV (source M parts bodies) x .callByValuePar (tblV (source M parts bodies) x .callByValuePar k) E e p=
    evV (ScannerOriginControl.original M parts (plans bodies)) x .callByValuePar
      (tblV (ScannerOriginControl.original M parts (plans bodies)) x .callByValuePar k) E e p :=
  SemanticBodyRewrite.physical (related M parts bodies h) x k E e p

theorem normalized_observations_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (bodies : List Body)
    (h : syntaxCheck parts bodies=true) (e : Arg) (x : List Char) (rest : Option (List Char)) :
    SObs (source M parts bodies) .callByValuePar (sourceExpr M e) x rest ↔
    SObs (ScannerOriginControl.original M parts (plans bodies)) .callByValuePar (sourceExpr M e) x rest :=
  SemanticBodyRewrite.observations (related M parts bodies h) (source_firstOrder M parts bodies)
    (ScannerOriginControl.original_firstOrder M parts (plans bodies)) (by decide) _
    (RecursiveScannerProductCompiler.sourceExpr_firstOrder M e) x rest

theorem observations_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (bodies : List Body)
    (hSyntax : syntaxCheck parts bodies=true)
    (hReady : readyCheck parts (plans bodies)=true) (e : Arg) (he : scopeCheck (plans bodies) e=true)
    (H : RecursiveCaptureProfiles.ScannerSummary n) (C : RecursiveCaptureProfiles.Summary)
    (A : ProfileCheckedScannerCorrespondence.Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M (coreEntries parts) (coreBodies parts (plans bodies)) H C=true)
    (hB : ProfileCheckedScannerCorrespondence.bodiesCheck M (coreEntries parts) (coreBodies parts (plans bodies)) C A=true)
    (hRoot : ProfileCheckedScannerCorrespondence.check M (coreEntries parts) (coreBodies parts (plans bodies)) C A [] (normalize parts (plans bodies) e)=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs (source M parts bodies) .callByValuePar (sourceExpr M e) x rest ↔
      SObs (RecursiveScannerProductCompiler.target M (coreEntries parts) (coreBodies parts (plans bodies))) .callByValueSeq
        (RecursiveScannerProductCompiler.plain M (coreBodies parts (plans bodies)) [] (normalize parts (plans bodies) e)) x rest :=
  (normalized_observations_iff M parts bodies hSyntax e x rest).trans
    (ScannerOriginControl.observations_iff M parts (plans bodies) hReady e he H C A hH hC hB hRoot x rest)

theorem language_translation {n : Nat} (M : Machine n) (parts : List (Part n)) (bodies : List Body)
    (hSyntax : syntaxCheck parts bodies=true)
    (hReady : readyCheck parts (plans bodies)=true) (e : Arg) (he : scopeCheck (plans bodies) e=true)
    (H : RecursiveCaptureProfiles.ScannerSummary n) (C : RecursiveCaptureProfiles.Summary)
    (A : ProfileCheckedScannerCorrespondence.Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M (coreEntries parts) (coreBodies parts (plans bodies)) H C=true)
    (hB : ProfileCheckedScannerCorrespondence.bodiesCheck M (coreEntries parts) (coreBodies parts (plans bodies)) C A=true)
    (hRoot : ProfileCheckedScannerCorrespondence.check M (coreEntries parts) (coreBodies parts (plans bodies)) C A [] (normalize parts (plans bodies) e)=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (source M parts bodies) .callByValuePar (sourceExpr M e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨_,_,RecursiveScannerProductCompiler.target_firstOrder M (coreEntries parts) (coreBodies parts (plans bodies)),
    RecursiveScannerProductCompiler.plain_firstOrder M (coreBodies parts (plans bodies)) [] (normalize parts (plans bodies) e),
    fun x => observations_iff M parts bodies hSyntax hReady e he H C A hH hC hB hRoot x (some [])⟩

theorem defined_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (bodies : List Body)
    (hSyntax : syntaxCheck parts bodies=true)
    (hReady : readyCheck parts (plans bodies)=true) (e : Arg) (he : scopeCheck (plans bodies) e=true)
    (H : RecursiveCaptureProfiles.ScannerSummary n) (C : RecursiveCaptureProfiles.Summary)
    (A : ProfileCheckedScannerCorrespondence.Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M (coreEntries parts) (coreBodies parts (plans bodies)) H C=true)
    (hB : ProfileCheckedScannerCorrespondence.bodiesCheck M (coreEntries parts) (coreBodies parts (plans bodies)) C A=true)
    (hRoot : ProfileCheckedScannerCorrespondence.check M (coreEntries parts) (coreBodies parts (plans bodies)) C A [] (normalize parts (plans bodies) e)=true)
    (x : List Char) (v : Option Nat) :
    (∃ k, evV (source M parts bodies) x .callByValuePar
      (tblV (source M parts bodies) x .callByValuePar k) [] (sourceExpr M e) x.length=some v) ↔
    (∃ k, evV (target M parts (plans bodies)) x .callByValueSeq
      (tblV (target M parts (plans bodies)) x .callByValueSeq k) [] (targetExpr M parts (plans bodies) e) x.length=some v) := by
  have hb := ScannerOriginControl.defined_iff M parts (plans bodies) hReady e he H C A hH hC hB hRoot x v
  constructor
  · rintro ⟨k,hk⟩
    exact hb.mp ⟨k,(physical M parts bodies hSyntax x k [] (sourceExpr M e) x.length).symm.trans hk⟩
  · intro h
    obtain ⟨k,hk⟩ := hb.mpr h
    exact ⟨k,(physical M parts bodies hSyntax x k [] (sourceExpr M e) x.length).trans hk⟩

theorem undefined_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (bodies : List Body)
    (hSyntax : syntaxCheck parts bodies=true)
    (hReady : readyCheck parts (plans bodies)=true) (e : Arg) (he : scopeCheck (plans bodies) e=true)
    (H : RecursiveCaptureProfiles.ScannerSummary n) (C : RecursiveCaptureProfiles.Summary)
    (A : ProfileCheckedScannerCorrespondence.Inputs)
    (hH : RecursiveCaptureProfiles.scannerCheck M H=true)
    (hC : RecursiveCaptureProfiles.grammarCheck M (coreEntries parts) (coreBodies parts (plans bodies)) H C=true)
    (hB : ProfileCheckedScannerCorrespondence.bodiesCheck M (coreEntries parts) (coreBodies parts (plans bodies)) C A=true)
    (hRoot : ProfileCheckedScannerCorrespondence.check M (coreEntries parts) (coreBodies parts (plans bodies)) C A [] (normalize parts (plans bodies) e)=true)
    (x : List Char) :
    (∀ k, evV (source M parts bodies) x .callByValuePar
      (tblV (source M parts bodies) x .callByValuePar k) [] (sourceExpr M e) x.length=none) ↔
    (∀ k, evV (target M parts (plans bodies)) x .callByValueSeq
      (tblV (target M parts (plans bodies)) x .callByValueSeq k) [] (targetExpr M parts (plans bodies) e) x.length=none) := by
  constructor
  · intro h k
    cases hv : evV (target M parts (plans bodies)) x .callByValueSeq
        (tblV (target M parts (plans bodies)) x .callByValueSeq k) [] (targetExpr M parts (plans bodies) e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨l,hl⟩ := (defined_iff M parts bodies hSyntax hReady e he H C A hH hC hB hRoot x v).mpr ⟨k,hv⟩
      rw [h l] at hl
      cases hl
  · intro h k
    cases hv : evV (source M parts bodies) x .callByValuePar
        (tblV (source M parts bodies) x .callByValuePar k) [] (sourceExpr M e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨l,hl⟩ := (defined_iff M parts bodies hSyntax hReady e he H C A hH hC hB hRoot x v).mp ⟨k,hv⟩
      rw [h l] at hl
      cases hl

end Shallot.MacroPeg.CBV.PrefixCaptureQuery
