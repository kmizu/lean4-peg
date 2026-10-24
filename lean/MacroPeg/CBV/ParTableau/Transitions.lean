import MacroPeg.CBV.ParTableau.Layout

namespace Shallot.MacroPeg.CBV.ParTableau

open PrefixCounters RootObservation
open Complexity (TM Cfg Move)

theorem conjunction_subst (args es : List MExp) :
    MExp.subst args (conjunction es) = conjunction (es.map (MExp.subst args)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [conjunction, MExp.subst, List.map_cons, ih]

theorem conjunction_test {α : Type} {g : MGrammar} {x : List Char}
    (as : List α) (E : α → MExp) (B : α → Bool)
    (h : ∀ a ∈ as, Test g .callByValuePar (E a) x (B a)) :
    Test g .callByValuePar (conjunction (as.map E)) x (as.all B) := by
  induction as with
  | nil => exact ⟨_, .eps x, rfl⟩
  | cons a as ih =>
    exact test_seq (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

def caseValue {k : Nat} (c : Cfg k) (p : Nat × (Fin k → Nat)) : Bool :=
  (c.state == p.1) && (List.finRange k).all (fun i => c.read i == p.2 i)

theorem caseValue_iff {k : Nat} (c : Cfg k) (p : Nat × (Fin k → Nat)) :
    caseValue c p = true ↔ p = (c.state, c.read) := by
  simp only [caseValue, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange,
    forall_const]
  constructor
  · rintro ⟨hs, hr⟩
    exact Prod.ext hs.symm (funext fun i => (hr i).symm)
  · rintro rfl
    exact ⟨rfl, fun _ => rfl⟩

/-- Only the actual state/read vector contributes to a finite TM case split. -/
theorem select_case {k : Nat} (M : TM k) (c : Cfg k)
    (hc : c.state < M.nq) (hr : ∀ i, c.read i < M.na)
    (F : Nat × (Fin k → Nat) → Bool) :
    (Complexity.combos M).any (fun p => caseValue c p && F p) = F (c.state, c.read) := by
  rw [Bool.eq_iff_iff, List.any_eq_true]
  constructor
  · rintro ⟨p, _, hp⟩
    obtain ⟨hcase, hf⟩ := Bool.and_eq_true_iff.mp hp
    rw [(caseValue_iff c p).mp hcase] at hf
    exact hf
  · intro hf
    exact ⟨(c.state, c.read), (Complexity.mem_combos M _).mpr ⟨hc, hr⟩,
      Bool.and_eq_true_iff.mpr ⟨(caseValue_iff c _).mpr rfl, hf⟩⟩

theorem select_filtered_case {k : Nat} (M : TM k) (c : Cfg k)
    (hc : c.state < M.nq) (hr : ∀ i, c.read i < M.na)
    (F : Nat × (Fin k → Nat) → Bool) :
    ((Complexity.combos M).filter F).any (caseValue c) = F (c.state, c.read) := by
  have hh := select_case M c hc hr F
  rw [← hh, Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  simp only [List.mem_filter, Bool.and_eq_true]
  constructor
  · rintro ⟨p, ⟨hm, hf⟩, hp⟩; exact ⟨p, hm, hp, hf⟩
  · rintro ⟨p, hm, hp, hf⟩; exact ⟨p, ⟨hm, hf⟩, hp⟩

theorem subst_allRefs (args : List MExp) (digits : Nat) (hl : args.length = width digits) :
    MExp.substArgs args (allRefs digits) = args := by
  rw [allRefs, ← hl, CBVtoCBN.subst_paramsFrom]

theorem caseTest_test {k : Nat} {g : MGrammar} {x : List Char} (M : TM k) (digits : Nat)
    (args : List MExp) (hl : args.length = width digits) (c : Cfg k) (q : Nat) (hq : q < M.nq)
    (r : Fin k → Nat) (hr : ∀ i, r i < M.na)
    (hst : ∀ q, q < M.nq → Test g .callByValuePar (.call (address M digits (.state q)) args) x
      (c.state == q))
    (hrd : ∀ i s, s < M.na → Test g .callByValuePar (.call (address M digits (.read i s)) args) x
      (c.read i == s)) :
    Test g .callByValuePar (MExp.subst args (caseTest M digits q r)) x (caseValue c (q, r)) := by
  simp only [caseTest, conjunction_subst, List.map_cons, List.map_map, Function.comp_def, MExp.subst,
    subst_allRefs args digits hl]
  apply test_seq (hst q hq)
  exact conjunction_test (List.finRange k) _ _ (fun i _ => hrd i (r i) (hr i))

/-- State/read/position/cell tests at the predecessor time. The arithmetic
field is a separate obligation, not a claim about the complete simulator. -/
structure Previous {k : Nat} (g : MGrammar) (M : TM k) (digits : Nat) (args : List MExp)
    (x : List Char) (c : Cfg k) (position : Nat) : Prop where
  state : ∀ q, q < M.nq → Test g .callByValuePar (.call (address M digits (.state q)) args) x
    (c.state == q)
  read : ∀ i s, s < M.na → Test g .callByValuePar (.call (address M digits (.read i s)) args) x
    (c.read i == s)
  head : ∀ i, Test g .callByValuePar (.call (address M digits (.head i)) args) x
    (c.pos i == position)
  cell : ∀ i s, s < M.na → Test g .callByValuePar (.call (address M digits (.cell i s)) args) x
    (c.cells i position == s)
  moved : ∀ i mv, Test g .callByValuePar (MExp.subst args (movedHead M digits i mv)) x
    (mv.apply (c.pos i) == position)

theorem stateNext_test {k : Nat} {g : MGrammar} {x : List Char} (M : TM k) (digits : Nat)
    (args : List MExp) (hl : args.length = width digits) (c : Cfg k) (position q : Nat)
    (hc : c.state < M.nq) (hr : ∀ i, c.read i < M.na)
    (h : Previous g M digits args x c position) :
    Test g .callByValuePar (MExp.subst args (nextBody M digits (.state q))) x
      ((M.step c).state == q) := by
  let F := fun p : Nat × (Fin k → Nat) => Complexity.nextState M p.1 p.2 == q
  have ht := alternatives_test ((Complexity.combos M).filter F)
    (fun p => MExp.subst args (caseTest M digits p.1 p.2)) (caseValue c) (by
      intro p hp
      have hm := (Complexity.mem_combos M p).mp (List.mem_filter.mp hp).1
      exact caseTest_test M digits args hl c p.1 hm.1 p.2 hm.2 h.state h.read)
  rw [select_filtered_case M c hc hr F] at ht
  simpa only [nextBody, alternatives_subst, List.map_map, Function.comp_def, Complexity.step_state, F] using ht

theorem headNext_test {k : Nat} {g : MGrammar} {x : List Char} (M : TM k) (digits : Nat)
    (args : List MExp) (hl : args.length = width digits) (c : Cfg k) (position : Nat) (i : Fin k)
    (hc : c.state < M.nq) (hr : ∀ j, c.read j < M.na)
    (h : Previous g M digits args x c position) :
    Test g .callByValuePar (MExp.subst args (nextBody M digits (.head i))) x
      ((M.step c).pos i == position) := by
  let F := fun p : Nat × (Fin k → Nat) =>
    (Complexity.moveOf M p.1 p.2 i).apply (c.pos i) == position
  have ht := alternatives_test (Complexity.combos M)
    (fun p => .seq (MExp.subst args (caseTest M digits p.1 p.2))
      (MExp.subst args (movedHead M digits i (Complexity.moveOf M p.1 p.2 i))))
    (fun p => caseValue c p && F p) (by
      intro p hp
      have hm := (Complexity.mem_combos M p).mp hp
      exact test_seq (caseTest_test M digits args hl c p.1 hm.1 p.2 hm.2 h.state h.read)
        (h.moved i _))
  rw [select_case M c hc hr F] at ht
  simpa only [nextBody, alternatives_subst, List.map_map, Function.comp_def, MExp.subst, Complexity.step_pos, F] using ht

theorem cellNext_test {k : Nat} {g : MGrammar} {x : List Char} (M : TM k) (digits : Nat)
    (args : List MExp) (hl : args.length = width digits) (c : Cfg k) (position s : Nat) (i : Fin k)
    (hc : c.state < M.nq) (hr : ∀ j, c.read j < M.na) (hs : s < M.na)
    (h : Previous g M digits args x c position) :
    Test g .callByValuePar (MExp.subst args (nextBody M digits (.cell i s))) x
      ((M.step c).cells i position == s) := by
  let F := fun p : Nat × (Fin k → Nat) => Complexity.writeSym M p.1 p.2 i == s
  have ht := alternatives_test ((Complexity.combos M).filter F)
    (fun p => MExp.subst args (caseTest M digits p.1 p.2)) (caseValue c) (by
      intro p hp
      have hm := (Complexity.mem_combos M p).mp (List.mem_filter.mp hp).1
      exact caseTest_test M digits args hl c p.1 hm.1 p.2 hm.2 h.state h.read)
  rw [select_filtered_case M c hc hr F] at ht
  have ha := test_alt (test_seq (test_not (h.head i)) (h.cell i s hs)) (test_seq (h.head i) ht)
  have hv : ((! (c.pos i == position) && (c.cells i position == s)) ||
      ((c.pos i == position) && F (c.state, c.read))) = ((M.step c).cells i position == s) := by
    rw [Complexity.step_cells]
    by_cases he : position = c.pos i
    · simp [he, F]
    · have hn : c.pos i ≠ position := Ne.symm he
      have hb : (c.pos i == position) = false := Bool.eq_false_iff.mpr (fun hb => hn (eq_of_beq hb))
      simp [he, hb]
  rw [hv] at ha
  simpa only [nextBody, MExp.subst, subst_allRefs args digits hl, alternatives_subst,
    List.map_map, Function.comp_def, F] using ha

end Shallot.MacroPeg.CBV.ParTableau
