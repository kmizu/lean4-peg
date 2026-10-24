import MacroPeg.CBV.ParTableau.Compiler

namespace Shallot.MacroPeg.CBV.ParTableau

open PrefixCounters RootObservation
open CBVtoCBN (paramsFrom_firstOrder)
open Complexity (TM)

@[local simp] private theorem foArgs_append (a b : List MExp) :
    MExp.FirstOrderArgs (a ++ b) ↔ MExp.FirstOrderArgs a ∧ MExp.FirstOrderArgs b := by
  induction a with
  | nil => simp [MExp.FirstOrderArgs]
  | cons a as ih => simp [MExp.FirstOrderArgs, ih, and_assoc]

@[local simp] private theorem foArgs_replicate (a : MExp) (ha : a.FirstOrder) (n : Nat) :
    MExp.FirstOrderArgs (List.replicate n a) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ha, ih⟩

attribute [local simp] MExp.FirstOrder MExp.FirstOrderArgs paramsFrom_firstOrder
attribute [local simp] allRefs timeRefs posRefs swappedRefs MExp.failAlways MExp.andP atEnd atPosition

theorem conjunction_firstOrder (es : List MExp) (h : ∀ e ∈ es, e.FirstOrder) :
    (conjunction es).FirstOrder := by
  induction es with
  | nil => trivial
  | cons e es ih => exact ⟨h e (by simp), ih (fun a ha => h a (by simp [ha]))⟩

private theorem args_fo_mem {ds : List MExp} {a : MExp} (h : MExp.FirstOrderArgs ds)
    (ha : a ∈ ds) : a.FirstOrder := by
  induction ds with
  | nil => cases ha
  | cons b ds ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact ih h.2 ha

@[local simp] theorem zeroDigits_firstOrder (ds : List MExp) (h : MExp.FirstOrderArgs ds) :
    (zeroDigits ds).FirstOrder := by
  apply conjunction_firstOrder
  intro e he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  exact ⟨args_fo_mem h ha, trivial, trivial⟩

@[local simp] theorem truth_firstOrder (b : Bool) : (truth b).FirstOrder := by
  cases b <;> trivial

@[local simp] theorem initialCell_firstOrder (digits symbol : Nat) :
    (initialCell digits symbol).FirstOrder := by
  have hl : (lowDigit digits).FirstOrder := by unfold lowDigit; split <;> trivial
  have hh := zeroDigits_firstOrder (CBVtoCBN.paramsFrom 1 (digits - 1)) (paramsFrom_firstOrder _ _)
  by_cases h0 : symbol = 0
  · simp [initialCell, h0, hl]
  · by_cases h1 : symbol = 1
    · simp [initialCell, h1, hl]
    · by_cases h2 : symbol = 2 <;> simp [initialCell, h0, h1, h2, hl]

@[local simp] theorem zeroBody_firstOrder {k : Nat} (digits : Nat) (node : Node k) :
    (zeroBody digits node).FirstOrder := by
  cases node with
  | cell i s =>
    simp only [zeroBody]
    split
    · exact initialCell_firstOrder digits s
    · exact truth_firstOrder (s == 0)
  | state _ | head _ | read _ _ | incHead _ | decHead _ => simp [zeroBody]

@[local simp] theorem caseTest_firstOrder {k : Nat} (M : TM k) (digits q : Nat) (r : Fin k → Nat) :
    (caseTest M digits q r).FirstOrder := by
  apply conjunction_firstOrder
  simp only [List.mem_cons, List.mem_map]
  intro e he
  rcases he with rfl | ⟨i, _, rfl⟩ <;> simp

@[local simp] theorem movedHead_firstOrder {k : Nat} (M : TM k) (digits : Nat) (i : Fin k)
    (mv : Complexity.Move) : (movedHead M digits i mv).FirstOrder := by
  cases mv <;> simp [movedHead]

@[local simp] theorem nextBody_firstOrder {k : Nat} (M : TM k) (digits : Nat) (node : Node k) :
    (nextBody M digits node).FirstOrder := by
  cases node with
  | state q =>
    apply alternatives_firstOrder
    intro e he
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp he
    exact caseTest_firstOrder _ _ _ _
  | head i =>
    apply alternatives_firstOrder
    intro e he
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp he
    exact ⟨caseTest_firstOrder _ _ _ _, movedHead_firstOrder _ _ _ _⟩
  | cell i s =>
    have ha : (alternatives (((Complexity.combos M).filter
        (fun p => Complexity.writeSym M p.1 p.2 i == s)).map
          (fun p => caseTest M digits p.1 p.2))).FirstOrder := by
      apply alternatives_firstOrder
      intro e he
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp he
      exact caseTest_firstOrder _ _ _ _
    simpa [nextBody] using ha
  | read _ _ | incHead _ | decHead _ => trivial

theorem rawRules_firstOrder {k : Nat} (M : TM k) (digits base : Nat) (node : Node k) :
    ∀ r ∈ rawRules M digits base node, r.body.FirstOrder := by
  have ht : ∀ node : Node k, ∀ r ∈ timeRules M digits base node, r.body.FirstOrder := by
    intro node r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact clockBlock_firstOrder _ _ _ _ _ _ r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  cases node with
  | state _ | head _ | cell _ _ => exact ht _
  | incHead i =>
    intro r hr
    simp only [rawRules, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact successorBody_firstOrder _ _ _ _ _
    · simp [headAdapter]
  | decHead i =>
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact clockBlock_firstOrder _ _ _ _ _ _ r hr
    · have he := List.mem_singleton.mp hr
      subst r
      simp [headAdapter]
  | read i s =>
    intro r hr
    simp only [rawRules, List.singleton_append] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact tupleSearch_firstOrder _ _ _ _ (by simp)
    · rcases List.mem_append.mp hr with hr | hr
      · exact tupleRules_firstOrder _ _ _ _ r hr
      · have he := List.mem_singleton.mp hr
        subst r
        simp [readLeaf]

theorem compile_firstOrder {k : Nat} (M : TM k) (digits : Nat) : (compile M digits).FirstOrder := by
  intro rule hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact equalBody_firstOrder 0
  rcases List.mem_cons.mp hr with rfl | hr
  · trivial
  obtain ⟨node, _, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨j, _, he⟩ := List.mem_map.mp hr
  subst rule
  cases hh : (rawRules M digits (address M digits node) node)[j]? with
  | none => trivial
  | some rule => exact rawRules_firstOrder _ _ _ _ rule (List.mem_of_getElem? hh)

theorem start_firstOrder {k : Nat} (M : TM k) (digits : Nat) : (start M digits).FirstOrder := by
  simp [start]

end Shallot.MacroPeg.CBV.ParTableau
