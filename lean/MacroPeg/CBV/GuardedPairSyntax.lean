import MacroPeg.CBV.ScannedPairFusion
import MacroPeg.CBV.ZeroResetOrigin

namespace Shallot.MacroPeg.CBV.GuardedPairSyntax
open NestedScannerArguments ScannerFrontier
open MixedScannerPairFusion (Entry arity)

def query (qs : List MExp) (i : Nat) := qs[i]?.getD .eps

def render (es : List Entry) (parallel : Bool) : MExp → MExp
  | .call i [] => match es[i]? with
    | none => MExp.failAlways
    | some r => if parallel then match r.pairing with
      | none => .call i []
      | some (A,B) => .call i [scan A,scan B]
      else .call (3*i) []
  | .call _ (_::_) => MExp.failAlways
  | .seq a b => .seq (render es parallel a) (render es parallel b)
  | .alt a b => .alt (render es parallel a) (render es parallel b)
  | .star a => .star (render es parallel a)
  | .notP a => .notP (render es parallel a)
  | .param k => .param k
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

theorem render_firstOrder (es : List Entry) (parallel : Bool) : ∀ e, (render es parallel e).FirstOrder
  | .call i [] => by
    simp only [render]
    cases hr : es[i]? with
    | none => trivial
    | some r =>
      simp only [hr]
      cases parallel with
      | false => trivial
      | true => cases r.pairing with
        | none => trivial
        | some pair => exact ⟨scan_firstOrder _,scan_firstOrder _,True.intro⟩
  | .call _ (_::_) => trivial
  | .seq a b | .alt a b => ⟨render_firstOrder _ _ a,render_firstOrder _ _ b⟩
  | .star a | .notP a => render_firstOrder _ _ a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

def sourceBody (es : List Entry) (qs : List MExp) (i : Nat) (r : Entry) : MExp := match r.pairing with
  | none => render es true r.tail
  | some (A,B) => .seq (.andP (render es true (query qs i)))
      (.seq (ScannedPairFusion.maxScanner A B) (render es true r.tail))
def sourceRule (es : List Entry) (qs : List MExp) (i : Nat) (r : Entry) : MRule := ⟨arity r,sourceBody es qs i r⟩
def parGrammar (es : List Entry) (qs : List MExp) : MGrammar := ⟨es.mapIdx (sourceRule es qs)⟩

def header (es : List Entry) (qs : List MExp) (i : Nat) (r : Entry) : MRule := ⟨0,match r.pairing with
  | none => render es false r.tail
  | some (A,B) => .seq (.andP (render es false (query qs i))) (dispatch A B (3*i+1) (3*i+2))⟩
def caseRule (es : List Entry) (first : Bool) (r : Entry) : MRule := ⟨arity r,match r.pairing with
  | none => render es false r.tail
  | some _ => body first (render es false r.tail)⟩
def slot (es : List Entry) (qs : List MExp) (i offset : Nat) (r : Entry) :=
  if offset=0 then header es qs i r else caseRule es (offset==1) r

def rules (es : List Entry) (qs : List MExp) : Nat → List Entry → List MRule
  | _,[] => []
  | i,r::rest => header es qs i r :: caseRule es true r :: caseRule es false r :: rules es qs (i+1) rest
def seqGrammar (es : List Entry) (qs : List MExp) : MGrammar := ⟨rules es qs 0 es⟩

def check (es : List Entry) (qs : List MExp) : Bool := es.zipIdx.all (fun (_,i) =>
  ZeroResetOrigin.closedCheck (render es true (query qs i)) && ZeroResetOrigin.closedCheck (render es false (query qs i)))

theorem checked (es : List Entry) (qs : List MExp) (hc : check es qs=true)
    (i : Nat) (r : Entry) (hr : es[i]?=some r) :
    ReplayFallbackFusion.Closed (render es true (query qs i)) ∧ ReplayFallbackFusion.Closed (render es false (query qs i)) := by
  have hm : (r,i)∈es.zipIdx := List.mem_of_getElem?
    (show es.zipIdx[i]?=some (r,i) from by simp [List.getElem?_zipIdx,hr])
  have hh := List.all_eq_true.mp hc (r,i) hm
  exact ⟨ZeroResetOrigin.closed_checked _ (Bool.and_eq_true_iff.mp hh).1,
    ZeroResetOrigin.closed_checked _ (Bool.and_eq_true_iff.mp hh).2⟩

theorem par_rule (es : List Entry) (qs : List MExp) (i : Nat) :
    ruleAtM (parGrammar es qs).rules i=(es[i]?).map (sourceRule es qs i) := by
  simp [parGrammar,ruleAtM_eq_getElem?,List.getElem?_mapIdx]

private theorem slot_lookup (es : List Entry) (qs : List MExp) (entries : List Entry)
    (i offset : Nat) (ho : offset<3) (start : Nat) :
    (rules es qs start entries)[3*i+offset]?=(entries[i]?).map (slot es qs (start+i) offset) := by
  induction entries generalizing start i with
  | nil => simp [rules]
  | cons r entries ih =>
    cases i with
    | zero =>
      cases offset with
      | zero => rfl
      | succ offset => cases offset with
        | zero => rfl
        | succ offset => cases offset with
          | zero => rfl
          | succ offset => omega
    | succ i =>
      rw [show 3*(i+1)+offset=(3*i+offset)+3 by omega]
      simpa only [rules,List.getElem?_cons_succ,Nat.add_succ,Nat.add_zero,Nat.zero_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        using ih i (start+1)

theorem seq_rule (es : List Entry) (qs : List MExp) (i offset : Nat) (ho : offset<3) :
    ruleAtM (seqGrammar es qs).rules (3*i+offset)=(es[i]?).map (slot es qs i offset) := by
  simpa only [seqGrammar,ruleAtM_eq_getElem?,Nat.zero_add] using slot_lookup es qs es i offset ho 0

theorem par_firstOrder (es : List Entry) (qs : List MExp) : (parGrammar es qs).FirstOrder := by
  intro r hr
  obtain ⟨i,hi⟩ := List.getElem?_of_mem hr
  have hp : ruleAtM (parGrammar es qs).rules i=some r := by simpa only [ruleAtM_eq_getElem?] using hi
  rw [par_rule] at hp
  cases hh : es[i]? with
  | none => simp [hh] at hp
  | some a =>
    simp only [hh,Option.map_some,Option.some.injEq] at hp
    subst r
    dsimp only [sourceRule,sourceBody]
    cases a.pairing with
    | none => exact render_firstOrder _ _ _
    | some pair => exact ⟨render_firstOrder _ _ _,ScannedPairFusion.maxScanner_firstOrder _ _,render_firstOrder _ _ _⟩

theorem seq_firstOrder (es : List Entry) (qs : List MExp) : (seqGrammar es qs).FirstOrder := by
  have hhead (i : Nat) (r : Entry) : (header es qs i r).body.FirstOrder := by
    dsimp only [header]
    cases r.pairing with
    | none => exact render_firstOrder _ _ _
    | some pair => exact ⟨render_firstOrder _ _ _,dispatch_firstOrder _ _ _ _⟩
  have hcase (b : Bool) (r : Entry) : (caseRule es b r).body.FirstOrder := by
    dsimp only [caseRule]
    cases r.pairing with
    | none => exact render_firstOrder _ _ _
    | some pair => exact body_firstOrder _ _ (render_firstOrder _ _ _)
  have hh : ∀ entries start r, r∈rules es qs start entries → r.body.FirstOrder := by
    intro entries
    induction entries with
    | nil => intro start r hr; cases hr
    | cons a entries ih =>
      intro start r hr
      simp only [rules,List.mem_cons] at hr
      rcases hr with rfl|rfl|rfl|hr
      · exact hhead _ _
      · exact hcase _ _
      · exact hcase _ _
      · exact ih _ _ hr
  exact hh es 0

end Shallot.MacroPeg.CBV.GuardedPairSyntax
