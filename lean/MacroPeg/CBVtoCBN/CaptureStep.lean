import MacroPeg.CBVtoCBN.PartialTests

namespace Shallot.MacroPeg.CBVtoCBN

/-- Resume a call after parallel argument evaluation. Unknown and failure remain distinct. -/
def finishPar (F : List (List Char) → Res) : Option (Option (List (List Char))) → Res
  | none => none
  | some none => some none
  | some (some W) => F W

/-- Resume a call after sequential argument evaluation, retaining the final input position. -/
def finishSeq (F : List (List Char) → Nat → Res) : Option (Option (List (List Char) × Nat)) → Res
  | none => none
  | some none => some none
  | some (some (W, q)) => F W q

theorem finishPar_cons (source : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char))
    (F : List (List Char) → Res) (a : MExp) (args : List MExp) (p : Nat) :
    finishPar F (evParArgs source x s T E (a :: args) p) =
      seqResult (evV source x s T E a p) (fun j =>
        finishPar (fun W => F (pre x p j :: W)) (evParArgs source x s T E args p)) := by
  cases ha : evV source x s T E a p with
  | none => simp [evParArgs, ha, finishPar, seqResult]
  | some a => cases a with
    | none => simp [evParArgs, ha, finishPar, seqResult]
    | some j =>
      cases ht : evParArgs source x s T E args p with
      | none => simp [evParArgs, ha, ht, finishPar, seqResult]
      | some r => cases r <;> simp [evParArgs, ha, ht, finishPar, seqResult]

theorem finishSeq_cons (source : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char))
    (F : List (List Char) → Nat → Res) (a : MExp) (args : List MExp) (p : Nat) :
    finishSeq F (evSeqArgs source x s T E (a :: args) p) =
      seqResult (evV source x s T E a p) (fun j =>
        finishSeq (fun W q => F (pre x p j :: W) q) (evSeqArgs source x s T E args j)) := by
  cases ha : evV source x s T E a p with
  | none => simp [evSeqArgs, ha, finishSeq, seqResult]
  | some a => cases a with
    | none => simp [evSeqArgs, ha, finishSeq, seqResult]
    | some j =>
      cases ht : evSeqArgs source x s T E args j with
      | none => simp [evSeqArgs, ha, ht, finishSeq, seqResult]
      | some r => cases r <;> simp [evSeqArgs, ha, ht, finishSeq, seqResult]

theorem evV_call_finishPar {source : MGrammar} {x : List Char} {s : Strategy}
    {T : Nat → List (List Char) → Val} {E : List (List Char)} {i : Nat} {args : List MExp} {rule : MRule}
    (hr : ruleAtM source.rules i = some rule) (ha : rule.arity = args.length) (hs : s ≠ .callByValueSeq)
    (p : Nat) :
    evV source x s T E (.call i args) p =
      finishPar (fun W => valAt (T i W) p) (evParArgs source x s T E args p) := by
  rw [evV_call_par hr ha hs]
  cases evParArgs source x s T E args p with
  | none => rfl
  | some r => cases r <;> rfl

theorem evV_call_finishSeq {source : MGrammar} {x : List Char}
    {T : Nat → List (List Char) → Val} {E : List (List Char)} {i : Nat} {args : List MExp} {rule : MRule}
    (hr : ruleAtM source.rules i = some rule) (ha : rule.arity = args.length) (p : Nat) :
    evV source x .callByValueSeq T E (.call i args) p =
      finishSeq (fun W q => valAt (T i W) q) (evSeqArgs source x .callByValueSeq T E args p) := by
  rw [evV_call_seq hr ha]
  cases evSeqArgs source x .callByValueSeq T E args p with
  | none => rfl
  | some r => cases r <;> rfl

/-- Every successful finite source approximation consumes an actual prefix, for any literal environment. -/
theorem evaluatedCapture_le {source : MGrammar} {x : List Char} {s : Strategy}
    (hg : source.FirstOrder) (hs : s ≠ .callByName) {e : MExp} (he : e.FirstOrder)
    (E : List (List Char)) (m : Nat) {p j : Nat} (hp : p ≤ x.length)
    (hv : evV source x s (tblV source x s m) E e p = some (some j)) : j ≤ p := by
  have hsub : evV source x s (tblV source x s m) [] (MExp.subst (E.map MExp.lit) e) p = some (some j) := by
    rw [evV_subst E e he]
    exact hv
  obtain ⟨o, hd, ho⟩ := evV_derives hg hs (firstOrder_subst (firstOrderArgs_lits E) e he) m hp hsub
  obtain ⟨t, rest, rfl, hlen⟩ := obsR_ok ho
  obtain ⟨consumed, hsplit⟩ := mderives_suffix hd t rest rfl
  have htotal := length_sfx x hp
  rw [hsplit, List.length_append] at htotal
  omega

/-- The continuation receives the captured interval, then the next current position, then the unchanged context. -/
def captureNextArgs (thread : Bool) (j j' p p' : MExp) (rest : List MExp) : List MExp :=
  p :: p' :: j :: j' :: (if thread then j else p) :: (if thread then j' else p') :: rest

def captureCandidateBody (argument next : Nat) (thread : Bool) (restSize : Nat) : MExp :=
  .seq (.call argument (.param 2 :: .param 3 :: .param 0 :: .param 1 :: paramsFrom 4 restSize))
    (.call next (captureNextArgs thread (.param 0) (.param 1) (.param 2) (.param 3) (paramsFrom 4 restSize)))

theorem captureCandidate_subst (argument next : Nat) (thread : Bool)
    (j j' p p' : MExp) (rest : List MExp) :
    MExp.subst (j :: j' :: p :: p' :: rest) (captureCandidateBody argument next thread rest.length) =
      .seq (.call argument (p :: p' :: j :: j' :: rest))
        (.call next (captureNextArgs thread j j' p p' rest)) := by
  cases thread <;> simp [captureCandidateBody, captureNextArgs, MExp.subst, MExp.substArgs,
    argAt, subst_paramsFrom_cons, subst_paramsFrom]

theorem captureCandidate_firstOrder (argument next : Nat) (thread : Bool) (restSize : Nat) :
    (captureCandidateBody argument next thread restSize).FirstOrder := by
  cases thread <;> exact
    ⟨⟨trivial, trivial, trivial, trivial, paramsFrom_firstOrder _ _⟩,
      ⟨trivial, trivial, trivial, trivial, trivial, trivial, paramsFrom_firstOrder _ _⟩⟩

/-- Four static rules capture one evaluated argument before invoking a fixed continuation.
`thread=false` is Par; `thread=true` is Seq. -/
def captureBlock (entry argument next : Nat) (thread : Bool) (restSize : Nat) : List MRule :=
  pairSearchBlock entry (entry + 3) (restSize + 2) ++
    [⟨restSize + 4, captureCandidateBody argument next thread restSize⟩]

theorem captureBlock_firstOrder (entry argument next : Nat) (thread : Bool) (restSize : Nat) :
    ∀ rule ∈ captureBlock entry argument next thread restSize, rule.body.FirstOrder := by
  intro rule hr
  rcases List.mem_append.mp hr with hr | hr
  · exact pairSearchBlock_firstOrder _ _ _ rule hr
  · have he := List.mem_singleton.mp hr
    subst rule
    exact captureCandidate_firstOrder _ _ _ _

/-- An actual CBN grammar fragment realizes one call-by-value capture transition.
The continuation's source result is indexed by the consumed string and by the correct Par/Seq next position. -/
theorem captureBlock_test (preRules tail : List MRule) (argument next : Nat) (thread : Bool)
    (rest : List MExp) (x : List Char) (p : Nat) (v : Option Nat) (a : Res)
    (F : List Char → Nat → Res)
    (hl : ∀ j, j ≤ x.length → RootTest
      ⟨preRules ++ (captureBlock preRules.length argument next thread rest.length ++ tail)⟩
      (.call argument (skipN p :: skipN (x.length - p) :: skipN j :: skipN (x.length - j) :: rest)) x
      (a = some (some j)))
    (hn : ∀ j, j ≤ x.length → RootTest
      ⟨preRules ++ (captureBlock preRules.length argument next thread rest.length ++ tail)⟩
      (.call next (captureNextArgs thread (skipN j) (skipN (x.length - j))
        (skipN p) (skipN (x.length - p)) rest)) x
      (F (pre x p j) (if thread then j else p) = some v)) :
    RootTest ⟨preRules ++ (captureBlock preRules.length argument next thread rest.length ++ tail)⟩
      (.call preRules.length (.eps :: skipN p :: skipN (x.length - p) :: rest)) x
      (∃ j, j ≤ x.length ∧ a = some (some j) ∧ F (pre x p j) (if thread then j else p) = some v) := by
  let g : MGrammar := ⟨preRules ++ (captureBlock preRules.length argument next thread rest.length ++ tail)⟩
  let ctx := skipN p :: skipN (x.length - p) :: rest
  have hg : g.rules = preRules ++ (pairSearchBlock preRules.length (preRules.length + 3) ctx.length ++
      (⟨rest.length + 4, captureCandidateBody argument next thread rest.length⟩ :: tail)) := by
    simp [g, captureBlock, ctx, List.append_assoc, Nat.add_comm, Nat.add_left_comm]
  have hc : ruleAtM g.rules (preRules.length + 3) = some
      ⟨rest.length + 4, captureCandidateBody argument next thread rest.length⟩ := by
    rw [hg, ruleAtM_append_offset]
    rfl
  have ht : ∀ j, j ≤ x.length → RootTest g
      (.call (preRules.length + 3) (skipN j :: skipN (x.length - j) :: ctx)) x
      (a = some (some j) ∧ F (pre x p j) (if thread then j else p) = some v) := by
    intro j hj
    rw [rootTest_call_iff hc (by simp [ctx]), captureCandidate_subst]
    exact (hl j hj).seq (hn j hj)
  have h := pairSearchBlock_test preRules
    (⟨rest.length + 4, captureCandidateBody argument next thread rest.length⟩ :: tail)
    (preRules.length + 3) ctx x
    (fun j => a = some (some j) ∧ F (pre x p j) (if thread then j else p) = some v)
    (by simpa only [← hg] using ht)
  have hout : RootTest g (.call preRules.length (.eps :: ctx)) x
      (∃ j, j ≤ x.length ∧ a = some (some j) ∧
        F (pre x p j) (if thread then j else p) = some v) := by
    simpa only [← hg] using h
  exact hout

/-- The capture block's bounded success relation gives the source transition's success predicate. -/
theorem captureSuccess_test {g : MGrammar} {x : List Char} {e : MExp} {a : Res} {b : Nat → Res} {q : Nat}
    (ha : OkR x.length a)
    (h : RootTest g e x (∃ j, j ≤ x.length ∧ a = some (some j) ∧ b j = some (some q))) :
    RootTest g e x (seqResult a b = some (some q)) :=
  h.congr (seqResult_success x.length a b ha q).symm

/-- Argument failure short-circuits; otherwise the captured continuation must explicitly fail.
Both tests fail for an unknown source result, so unknown is never mistaken for source failure. -/
theorem captureFailure_test {g : MGrammar} {x : List Char} {failed captured : MExp} {a : Res} {b : Nat → Res}
    (ha : OkR x.length a) (hf : RootTest g failed x (a = some none))
    (hc : RootTest g captured x (∃ j, j ≤ x.length ∧ a = some (some j) ∧ b j = some none)) :
    RootTest g (.alt failed captured) x (seqResult a b = some none) :=
  (hf.alt hc).congr (seqResult_failure x.length a b ha).symm

end Shallot.MacroPeg.CBVtoCBN
