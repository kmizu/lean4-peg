import MacroPeg.CBV.RecursiveProducedCorrespondence

namespace Shallot.MacroPeg.CBV.SelectedProducerNormalization

structure Producer where
  head : MExp
  tail : MExp
abbrev Selection := List (Option Producer)
def selected (ps : Selection) (i : Nat) := (ps[i]?).getD none

def body (ps : Selection) (i : Nat) (r : MRule) : MExp := match selected ps i with
  | none => r.body
  | some p => .seq (.param (r.arity-1)) p.tail

def target (g : MGrammar) (ps : Selection) : MGrammar := ⟨g.rules.mapIdx (fun i r => ⟨r.arity,body ps i r⟩)⟩

mutual
  def conforms (ps : Selection) : MExp → Bool
    | .call i args => arguments ps args && (match selected ps i with
      | some p => match args[args.length-1]? with
        | some a => MExp.beqE a p.head
        | none => true
      | none => true)
    | .seq a b | .alt a b => conforms ps a && conforms ps b
    | .notP a | .star a => conforms ps a
    | _ => true
  def arguments (ps : Selection) : List MExp → Bool
    | [] => true
    | a::args => conforms ps a && arguments ps args
end

def check (g : MGrammar) (ps : Selection) : Bool := decide (ps.length≤g.rules.length) &&
  g.rules.zipIdx.all (fun (r,i) => (MixedGrowthChecks.firstOrderCheck r.body && conforms ps r.body) &&
    match selected ps i with
    | none => true
    | some p => (decide (0<r.arity) && MExp.beqE r.body (.seq p.head p.tail)) && ZeroResetOrigin.closedCheck p.head)

theorem source_firstOrder (g : MGrammar) (ps : Selection) (hc : check g ps=true) : g.FirstOrder := by
  intro r hr
  obtain ⟨i,hi⟩ := List.getElem?_of_mem hr
  have hm : (r,i)∈g.rules.zipIdx := List.mem_of_getElem? (show g.rules.zipIdx[i]?=some (r,i) from by simp [List.getElem?_zipIdx,hi])
  exact MixedGrowthChecks.firstOrder_checked _
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2 (r,i) hm)).1).1

theorem body_conforms (g : MGrammar) (ps : Selection) (hc : check g ps=true)
    (i : Nat) (r : MRule) (hr : ruleAtM g.rules i=some r) : conforms ps r.body=true := by
  have hi : g.rules[i]?=some r := by simpa only [ruleAtM_eq_getElem?] using hr
  have hm : (r,i)∈g.rules.zipIdx := List.mem_of_getElem?
    (show g.rules.zipIdx[i]?=some (r,i) from by simp [List.getElem?_zipIdx,hi])
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2 (r,i) hm)).1).2

theorem checked (g : MGrammar) (ps : Selection) (hc : check g ps=true)
    (i : Nat) (r : MRule) (hr : ruleAtM g.rules i=some r) (p : Producer) (hp : selected ps i=some p) :
    0<r.arity ∧ r.body=.seq p.head p.tail ∧ ReplayFallbackFusion.Closed p.head := by
  have hi : g.rules[i]?=some r := by simpa only [ruleAtM_eq_getElem?] using hr
  have hm : (r,i)∈g.rules.zipIdx := List.mem_of_getElem? (show g.rules.zipIdx[i]?=some (r,i) from by simp [List.getElem?_zipIdx,hi])
  have h := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2 (r,i) hm)).2
  simp only [hp] at h
  obtain ⟨ha,hd⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp ha
  exact ⟨of_decide_eq_true ha,(MExp.beqE_iff _ _).mp hb,ZeroResetOrigin.closed_checked _ hd⟩

theorem target_rule (g : MGrammar) (ps : Selection) (i : Nat) :
    ruleAtM (target g ps).rules i=(ruleAtM g.rules i).map (fun r => ⟨r.arity,body ps i r⟩) := by
  simp [target,ruleAtM_eq_getElem?,List.getElem?_mapIdx]

theorem arities (g : MGrammar) (ps : Selection) : SemanticBodyRewrite.ArityEq g (target g ps) := by
  intro i
  rw [target_rule]
  cases ruleAtM g.rules i <;> rfl

theorem target_firstOrder (g : MGrammar) (ps : Selection) (hc : check g ps=true) : (target g ps).FirstOrder := by
  intro r hr
  obtain ⟨i,hi⟩ := List.getElem?_of_mem hr
  have hi' : ruleAtM (target g ps).rules i=some r := by simpa only [ruleAtM_eq_getElem?] using hi
  rw [target_rule] at hi'
  cases hg : ruleAtM g.rules i with
  | none => simp [hg] at hi'
  | some a =>
    simp only [hg,Option.map_some,Option.some.injEq] at hi'
    subst r
    cases hp : selected ps i with
    | none => simp only [body,hp]; exact source_firstOrder g ps hc a (ruleAtM_mem hg)
    | some p =>
      have hbody := (checked g ps hc i a hg p hp).2.1
      have hfo := source_firstOrder g ps hc a (ruleAtM_mem hg)
      rw [hbody] at hfo
      simp only [body,hp]
      exact ⟨True.intro,hfo.2⟩

end Shallot.MacroPeg.CBV.SelectedProducerNormalization
