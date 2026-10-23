import MacroPeg.CBVtoCBN.PairSearch
import MacroPeg.CBVtoCBN.SpanValues

namespace Shallot.MacroPeg.CBVtoCBN

/-- Explicit failure permits the right alternative; an unknown result does not. -/
def altResult (a b : Res) : Res := match a with
  | some none => b
  | r => r

/-- Only a successful left result permits evaluation of the right sequence component. -/
def seqResult (a : Res) (b : Nat → Res) : Res := match a with
  | some (some j) => b j
  | r => r

def notResult (p : Nat) (a : Res) : Res := match a with
  | some (some _) => some none
  | some none => some (some p)
  | none => none

theorem altResult_success (a b : Res) (q : Nat) :
    altResult a b = some (some q) ↔ a = some (some q) ∨ (a = some none ∧ b = some (some q)) := by
  cases a with
  | none => simp [altResult]
  | some a => cases a <;> simp [altResult]

theorem altResult_failure (a b : Res) :
    altResult a b = some none ↔ a = some none ∧ b = some none := by
  cases a with
  | none => simp [altResult]
  | some a => cases a <;> simp [altResult]

theorem seqResult_success (n : Nat) (a : Res) (b : Nat → Res) (ha : OkR n a) (q : Nat) :
    seqResult a b = some (some q) ↔
      ∃ j, j ≤ n ∧ a = some (some j) ∧ b j = some (some q) := by
  cases a with
  | none => simp [seqResult]
  | some a => cases a with
    | none => simp [seqResult]
    | some j =>
      have hj := ha j rfl
      simp only [seqResult, Option.some.injEq]
      constructor
      · intro hb; exact ⟨j, hj, rfl, hb⟩
      · rintro ⟨k, _, he, hb⟩; subst k; exact hb

theorem seqResult_failure (n : Nat) (a : Res) (b : Nat → Res) (ha : OkR n a) :
    seqResult a b = some none ↔ a = some none ∨
      ∃ j, j ≤ n ∧ a = some (some j) ∧ b j = some none := by
  cases a with
  | none => simp [seqResult]
  | some a => cases a with
    | none => simp [seqResult]
    | some j =>
      have hj := ha j rfl
      simp only [seqResult, Option.some.injEq, reduceCtorEq, false_or]
      constructor
      · intro hb; exact ⟨j, hj, rfl, hb⟩
      · rintro ⟨k, _, he, hb⟩; subst k; exact hb

theorem notResult_success (p q : Nat) (a : Res) :
    notResult p a = some (some q) ↔ p = q ∧ a = some none := by
  cases a with
  | none => simp [notResult]
  | some a => cases a <;> simp [notResult]

theorem notResult_failure (n p : Nat) (a : Res) (ha : OkR n a) :
    notResult p a = some none ↔ ∃ j, j ≤ n ∧ a = some (some j) := by
  cases a with
  | none => simp [notResult]
  | some a => cases a with
    | none => simp [notResult]
    | some j => have hj := ha j rfl; simp [notResult, hj]

/-- Actual CBN expression for a successful PEG alternative, retaining explicit source failure. -/
def altSuccessP (leftOk leftFail rightOk : MExp) : MExp := .alt leftOk (.seq leftFail rightOk)

theorem altSuccess_test {g : MGrammar} {x : List Char} {a b : Res} {q : Nat}
    {leftOk leftFail rightOk : MExp}
    (ho : RootTest g leftOk x (a = some (some q)))
    (hf : RootTest g leftFail x (a = some none))
    (hb : RootTest g rightOk x (b = some (some q))) :
    RootTest g (altSuccessP leftOk leftFail rightOk) x (altResult a b = some (some q)) :=
  (ho.alt (hf.seq hb)).congr (altResult_success a b q).symm

theorem altFailure_test {g : MGrammar} {x : List Char} {a b : Res} {leftFail rightFail : MExp}
    (ha : RootTest g leftFail x (a = some none)) (hb : RootTest g rightFail x (b = some none)) :
    RootTest g (.seq leftFail rightFail) x (altResult a b = some none) :=
  (ha.seq hb).congr (altResult_failure a b).symm

theorem notSuccess_test {g : MGrammar} {x : List Char} {a : Res} {p q : Nat}
    {equalPos failure : MExp} (he : RootTest g equalPos x (p = q))
    (hf : RootTest g failure x (a = some none)) :
    RootTest g (.seq equalPos failure) x (notResult p a = some (some q)) :=
  (he.seq hf).congr (notResult_success p q a).symm

/-- A translated negation fails only for a successful source result. Bottom remains distinct. -/
theorem notFailure_test {g : MGrammar} {x : List Char} {a : Res} {p : Nat} {success : MExp}
    (ha : OkR x.length a)
    (hs : RootTest g success x (∃ j, j ≤ x.length ∧ a = some (some j))) :
    RootTest g success x (notResult p a = some none) :=
  hs.congr (notResult_failure x.length p a ha).symm

/-- These partial-result operations are exactly the corresponding source evaluator clauses. -/
theorem evV_altResult (source : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (a b : MExp) (p : Nat) :
    evV source x s T E (.alt a b) p = altResult (evV source x s T E a p) (evV source x s T E b p) := rfl

theorem evV_seqResult (source : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (a b : MExp) (p : Nat) :
    evV source x s T E (.seq a b) p = seqResult (evV source x s T E a p) (fun j => evV source x s T E b j) := rfl

theorem evV_notResult (source : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (a : MExp) (p : Nat) :
    evV source x s T E (.notP a) p = notResult p (evV source x s T E a p) := rfl

/-- Static routing for a sequence candidate: left at `(p,j)`, right at `(j,q)`.
The rest of the tuple contains the clock and captured environment and is shared unchanged. -/
def sequenceCandidateBody (left right restSize : Nat) : MExp :=
  .seq (.call left (.param 2 :: .param 3 :: .param 0 :: .param 1 :: paramsFrom 6 restSize))
    (.call right (.param 0 :: .param 1 :: .param 4 :: .param 5 :: paramsFrom 6 restSize))

theorem sequenceCandidateBody_firstOrder (left right restSize : Nat) :
    (sequenceCandidateBody left right restSize).FirstOrder :=
  ⟨⟨trivial, trivial, trivial, trivial, paramsFrom_firstOrder 6 restSize⟩,
    ⟨trivial, trivial, trivial, trivial, paramsFrom_firstOrder 6 restSize⟩⟩

theorem sequenceCandidateBody_subst (left right : Nat) (j j' p p' q q' : MExp) (rest : List MExp) :
    MExp.subst (j :: j' :: p :: p' :: q :: q' :: rest) (sequenceCandidateBody left right rest.length) =
      .seq (.call left (p :: p' :: j :: j' :: rest)) (.call right (j :: j' :: q :: q' :: rest)) := by
  simp [sequenceCandidateBody, MExp.subst, MExp.substArgs, argAt, subst_paramsFrom_cons, subst_paramsFrom]

/-- Four generated rules implement the success clause of source sequencing. -/
def sequenceSuccessBlock (entry left right restSize : Nat) : List MRule :=
  pairSearchBlock entry (entry + 3) (restSize + 4) ++
    [⟨restSize + 6, sequenceCandidateBody left right restSize⟩]

theorem sequenceSuccessBlock_firstOrder (entry left right restSize : Nat) :
    ∀ rule ∈ sequenceSuccessBlock entry left right restSize, rule.body.FirstOrder := by
  intro rule hr
  rcases List.mem_append.mp hr with hr | hr
  · exact pairSearchBlock_firstOrder _ _ _ rule hr
  · have he := List.mem_singleton.mp hr
    subst rule
    exact sequenceCandidateBody_firstOrder _ _ _

/-- The generated sequence-success fragment is correct for bounded partial source results.
The two supplied subexpression predicates are total, including when their source approximant is bottom. -/
theorem sequenceSuccessBlock_test (pre tail : List MRule) (left right : Nat) (rest : List MExp)
    (x : List Char) (p q : Nat) (a : Res) (b : Nat → Res) (ha : OkR x.length a)
    (hl : ∀ j, j ≤ x.length → RootTest
      ⟨pre ++ (sequenceSuccessBlock pre.length left right rest.length ++ tail)⟩
      (.call left (skipN p :: skipN (x.length - p) :: skipN j :: skipN (x.length - j) :: rest)) x
      (a = some (some j)))
    (hr : ∀ j, j ≤ x.length → RootTest
      ⟨pre ++ (sequenceSuccessBlock pre.length left right rest.length ++ tail)⟩
      (.call right (skipN j :: skipN (x.length - j) :: skipN q :: skipN (x.length - q) :: rest)) x
      (b j = some (some q))) :
    RootTest ⟨pre ++ (sequenceSuccessBlock pre.length left right rest.length ++ tail)⟩
      (.call pre.length (.eps :: skipN p :: skipN (x.length - p) :: skipN q :: skipN (x.length - q) :: rest)) x
      (seqResult a b = some (some q)) := by
  let g : MGrammar := ⟨pre ++ (sequenceSuccessBlock pre.length left right rest.length ++ tail)⟩
  let ctx := skipN p :: skipN (x.length - p) :: skipN q :: skipN (x.length - q) :: rest
  have hg : g.rules = pre ++ (pairSearchBlock pre.length (pre.length + 3) ctx.length ++
      (⟨rest.length + 6, sequenceCandidateBody left right rest.length⟩ :: tail)) := by
    simp [g, sequenceSuccessBlock, ctx, List.append_assoc, Nat.add_comm, Nat.add_left_comm]
  have hc : ruleAtM g.rules (pre.length + 3) = some
      ⟨rest.length + 6, sequenceCandidateBody left right rest.length⟩ := by
    rw [hg, ruleAtM_append_offset]
    rfl
  have ht : ∀ j, j ≤ x.length → RootTest g
      (.call (pre.length + 3) (skipN j :: skipN (x.length - j) :: ctx)) x
      (a = some (some j) ∧ b j = some (some q)) := by
    intro j hj
    have hs := (hl j hj).seq (hr j hj)
    constructor
    · intro hp
      apply (obs_call_iff hc (by simp [ctx]) x (some x)).mpr
      rw [sequenceCandidateBody_subst]
      exact hs.1 hp
    · intro hp
      apply (obs_call_iff hc (by simp [ctx]) x none).mpr
      rw [sequenceCandidateBody_subst]
      exact hs.2 hp
  have h := pairSearchBlock_test pre (⟨rest.length + 6, sequenceCandidateBody left right rest.length⟩ :: tail)
    (pre.length + 3) ctx x (fun j => a = some (some j) ∧ b j = some (some q)) (by simpa only [← hg] using ht)
  have hout : RootTest g (.call pre.length (.eps :: ctx)) x
      (∃ j, j ≤ x.length ∧ a = some (some j) ∧ b j = some (some q)) := by
    simpa only [← hg] using h
  exact hout.congr (seqResult_success x.length a b ha q).symm

/-- Candidate for the right component's explicit failure after a successful left match. -/
def sequenceFailureCandidateBody (leftOk rightFail restSize : Nat) : MExp :=
  .seq (.call leftOk (.param 2 :: .param 3 :: .param 0 :: .param 1 :: paramsFrom 4 restSize))
    (.call rightFail (.param 0 :: .param 1 :: paramsFrom 4 restSize))

def sequenceFailureBody (leftFail search restSize : Nat) : MExp :=
  .alt (.call leftFail (paramsFrom 0 (restSize + 2)))
    (.call search (.eps :: paramsFrom 0 (restSize + 2)))

theorem sequenceFailureCandidate_subst (leftOk rightFail : Nat) (j j' p p' : MExp) (rest : List MExp) :
    MExp.subst (j :: j' :: p :: p' :: rest) (sequenceFailureCandidateBody leftOk rightFail rest.length) =
      .seq (.call leftOk (p :: p' :: j :: j' :: rest)) (.call rightFail (j :: j' :: rest)) := by
  simp [sequenceFailureCandidateBody, MExp.subst, MExp.substArgs, argAt,
    subst_paramsFrom_cons, subst_paramsFrom]

theorem sequenceFailureBody_subst (leftFail search : Nat) (p p' : MExp) (rest : List MExp) :
    MExp.subst (p :: p' :: rest) (sequenceFailureBody leftFail search rest.length) =
      .alt (.call leftFail (p :: p' :: rest)) (.call search (.eps :: p :: p' :: rest)) := by
  have h := subst_paramsFrom (p :: p' :: rest)
  simp only [List.length_cons] at h
  simp only [sequenceFailureBody, MExp.subst, MExp.substArgs]
  rw [show rest.length + 2 = rest.length + 1 + 1 by omega, h]

def sequenceFailureBlock (entry leftOk leftFail rightFail restSize : Nat) : List MRule :=
  ⟨restSize + 2, sequenceFailureBody leftFail (entry + 1) restSize⟩ ::
    (pairSearchBlock (entry + 1) (entry + 4) (restSize + 2) ++
      [⟨restSize + 4, sequenceFailureCandidateBody leftOk rightFail restSize⟩])

theorem sequenceFailureBlock_firstOrder (entry leftOk leftFail rightFail restSize : Nat) :
    ∀ rule ∈ sequenceFailureBlock entry leftOk leftFail rightFail restSize, rule.body.FirstOrder := by
  intro rule hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨paramsFrom_firstOrder _ _, ⟨trivial, paramsFrom_firstOrder _ _⟩⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact pairSearchBlock_firstOrder _ _ _ rule hr
  · have he := List.mem_singleton.mp hr
    subst rule
    exact ⟨⟨trivial, trivial, trivial, trivial, paramsFrom_firstOrder _ _⟩,
      ⟨trivial, trivial, paramsFrom_firstOrder _ _⟩⟩

theorem sequenceFailureBlock_test (pre tail : List MRule) (leftOk leftFail rightFail : Nat) (rest : List MExp)
    (x : List Char) (p : Nat) (a : Res) (b : Nat → Res) (ha : OkR x.length a)
    (hl : ∀ j, j ≤ x.length → RootTest
      ⟨pre ++ (sequenceFailureBlock pre.length leftOk leftFail rightFail rest.length ++ tail)⟩
      (.call leftOk (skipN p :: skipN (x.length - p) :: skipN j :: skipN (x.length - j) :: rest)) x
      (a = some (some j)))
    (hf : RootTest ⟨pre ++ (sequenceFailureBlock pre.length leftOk leftFail rightFail rest.length ++ tail)⟩
      (.call leftFail (skipN p :: skipN (x.length - p) :: rest)) x (a = some none))
    (hr : ∀ j, j ≤ x.length → RootTest
      ⟨pre ++ (sequenceFailureBlock pre.length leftOk leftFail rightFail rest.length ++ tail)⟩
      (.call rightFail (skipN j :: skipN (x.length - j) :: rest)) x (b j = some none)) :
    RootTest ⟨pre ++ (sequenceFailureBlock pre.length leftOk leftFail rightFail rest.length ++ tail)⟩
      (.call pre.length (skipN p :: skipN (x.length - p) :: rest)) x (seqResult a b = some none) := by
  let g : MGrammar := ⟨pre ++ (sequenceFailureBlock pre.length leftOk leftFail rightFail rest.length ++ tail)⟩
  let ctx := skipN p :: skipN (x.length - p) :: rest
  have h0 : ruleAtM g.rules pre.length = some
      ⟨rest.length + 2, sequenceFailureBody leftFail (pre.length + 1) rest.length⟩ := by
    rw [show pre.length = pre.length + 0 by omega]
    exact (ruleAtM_append_offset pre _ 0).trans rfl
  have h1 : ruleAtM g.rules (pre.length + 1) = some
      ⟨ctx.length + 1, anyPositionBody (pre.length + 1) (pre.length + 2) ctx.length⟩ := by
    rw [ruleAtM_append_offset]
    simp [sequenceFailureBlock, pairSearchBlock, ctx, ruleAtM, Nat.add_comm, Nat.add_left_comm]
  have h2 : ruleAtM g.rules (pre.length + 2) = some
      ⟨ctx.length + 1, pairSeedBody (pre.length + 3) ctx.length⟩ := by
    rw [ruleAtM_append_offset]
    simp [sequenceFailureBlock, pairSearchBlock, ctx, ruleAtM, Nat.add_comm, Nat.add_left_comm]
  have h3 : ruleAtM g.rules (pre.length + 3) = some
      ⟨ctx.length + 2, complementContextBody (pre.length + 3) (pre.length + 4) ctx.length⟩ := by
    rw [ruleAtM_append_offset]
    simp [sequenceFailureBlock, pairSearchBlock, ctx, ruleAtM, Nat.add_comm, Nat.add_left_comm]
  have h4 : ruleAtM g.rules (pre.length + 4) = some
      ⟨rest.length + 4, sequenceFailureCandidateBody leftOk rightFail rest.length⟩ := by
    rw [ruleAtM_append_offset]
    rfl
  have ht : ∀ j, j ≤ x.length → RootTest g
      (.call (pre.length + 4) (skipN j :: skipN (x.length - j) :: ctx)) x
      (a = some (some j) ∧ b j = some none) := by
    intro j hj
    rw [rootTest_call_iff h4 (by simp [ctx]), sequenceFailureCandidate_subst]
    exact (hl j hj).seq (hr j hj)
  have hs := anyPair_test ctx h1 h2 h3 x (fun j => a = some (some j) ∧ b j = some none) ht
  rw [rootTest_call_iff h0 (by simp), sequenceFailureBody_subst]
  exact (hf.alt hs).congr (seqResult_failure x.length a b ha).symm

end Shallot.MacroPeg.CBVtoCBN
