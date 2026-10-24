import MacroPeg.CBV.ContinuationPlan

/-! Factor consuming continuations through replay leaves. Guard tests can be
arbitrary origin-control plans; every successful output path must select a
leaf. The continuation itself may contain retained values and recursive calls. -/
namespace Shallot.MacroPeg.CBV.LeafContinuation
open ReplayControlFusion (Plan)
open OriginControlNormalization
open ContinuationPlan
abbrev Arg := RecursiveArgumentCompiler.Expr

/-- A predicate may test a branch, but cannot itself be its consuming result. -/
def Consumer : Plan → Prop
  | .leaf _ => True
  | .alt a b => Consumer a ∧ Consumer b
  | .guard _ b => Consumer b
  | .notP _ => False

def chain (offset : Nat) (P : Plan) : Plan := bind offset P (.leaf 0)

theorem chain_correct (n offset : Nat) (L R : Nat → Nat → Res) (K : Nat → Res)
    (hQuery : ∀ i, i<n → ∀ p, R i p=L i p)
    (hTail : ∀ i, i<n → ∀ p, R (offset+i) p=sequence (L i) K p) :
    ∀ P, Consumer P → P.All (fun i => i<n) → ∀ p,
      sem R (chain offset P) p=sequence (sem L P) K p
  | .leaf i, _, hi, p => hTail i hi p
  | .notP _, hc, _, _ => False.elim hc
  | .guard a b, hc, hP, p => by
    have ha := sem_congr n R L hQuery a hP.1 p
    have ib := chain_correct n offset L R K hQuery hTail b hc hP.2 p
    change (match sem R a p with | some (some _) => sem R (chain offset b) p | other => other)=_
    rw [ha,ib]
    simp only [sequence,sem,Plan.eval]
    cases Plan.eval (fun i => L i p) p a with
    | none => rfl
    | some result => cases result <;> rfl
  | .alt a b, hc, hP, p => by
    have ha := sem_congr n R L hQuery a hP.1 p
    have ia := chain_correct n offset L R K hQuery hTail a hc.1 hP.1 p
    have ib := chain_correct n offset L R K hQuery hTail b hc.2 hP.2 p
    change ReplayFallbackFusion.orElse
      (match sem R a p with | some (some _) => sem R (chain offset a) p | other => other)
      (match (match sem R a p with | some (some _) => some none | some none => some (some p) | none => none) with
        | some (some _) => sem R (chain offset b) p | other => other)=_
    rw [ha,ia,ib]
    simp only [sequence,sem,Plan.eval,ReplayFallbackFusion.orElse]
    cases Plan.eval (fun i => L i p) p a with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some j =>
        dsimp only []
        cases K j with
        | none => rfl
        | some result => cases result <;> rfl

theorem chain_bounded (n : Nat) : ∀ P, Consumer P → P.All (fun i => i<n) →
    (chain n P).All (fun i => i<2*n)
  | .leaf i, _, hi => by change i<n at hi; change n+i<2*n; omega
  | .notP _, hc, _ => False.elim hc
  | .guard a b, hc, hp =>
    ⟨Plan.all_imp (fun i (hi : i<n) => show i<2*n by omega) a hp.1,
     chain_bounded n b hc hp.2⟩
  | .alt a b, hc, hp => by
    have ha := Plan.all_imp (fun i (hi : i<n) => show i<2*n by omega) a hp.1
    exact ⟨⟨ha,chain_bounded n a hc.1 hp.1⟩,ha,chain_bounded n b hc.2 hp.2⟩

def raw (r : Leaf) : Arg :=
  if r.shift=none then r.body else .seq (.seq (.lit (r.shift.getD [])) (.param 0)) r.body

def lookup (leaves : List Leaf) (i : Nat) : Arg :=
  match leaves[i]? with | some r => raw r | none => .notP (.lit [])

def appendBody (tail : Arg) (r : Leaf) : Leaf := ⟨r.shift,.seq r.body tail⟩
def continued (leaves : List Leaf) (tail : Arg) : List Leaf := leaves ++ leaves.map (appendBody tail)

theorem continued_length (leaves : List Leaf) (tail : Arg) :
    (continued leaves tail).length=2*leaves.length := by simp [continued]; omega

theorem lookup_old (leaves : List Leaf) (tail : Arg) (i : Nat) (hi : i<leaves.length) :
    lookup (continued leaves tail) i=lookup leaves i := by
  simp only [lookup,continued,List.getElem?_append_left hi]

theorem lookup_new (leaves : List Leaf) (tail : Arg) (i : Nat) (hi : i<leaves.length) :
    lookup (continued leaves tail) (leaves.length+i)=raw (appendBody tail leaves[i]) := by
  simp [lookup,continued,List.getElem?_append_right (by omega : leaves.length ≤ leaves.length+i),
    List.getElem?_eq_getElem hi]

/-- This is actual evaluator associativity, including failure/undefinedness;
no physical capture or supplied row-correctness assumption is needed. -/
theorem append_eval (nodes : List RegularCaptureProduct.Node) (ambient : List Leaf) (specs : List Plan)
    (r : Leaf) (tail : Arg) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (render nodes ambient specs (raw (appendBody tail r))) p=
      sequence (fun q => evV g x s T E (render nodes ambient specs (raw r)) q)
        (fun q => evV g x s T E (render nodes ambient specs tail) q) p := by
  unfold raw appendBody
  dsimp only []
  split
  · rfl
  · change (match evV g x s T E (.seq (.lit (r.shift.getD [])) (.param 0)) p with
      | some (some j) => evV g x s T E (.seq (render nodes ambient specs r.body) (render nodes ambient specs tail)) j
      | other => other)=_
    unfold sequence
    change _=(match (match evV g x s T E (.seq (.lit (r.shift.getD [])) (.param 0)) p with
      | some (some j) => evV g x s T E (render nodes ambient specs r.body) j
      | other => other) with
      | some (some j) => evV g x s T E (render nodes ambient specs tail) j
      | other => other)
    cases evV g x s T E (.seq (.lit (r.shift.getD [])) (.param 0)) p with
    | none => rfl
    | some result => cases result <;> rfl

/-- Every finite control tree selecting consuming leaves followed by an
arbitrary continuation has a finite guarded-leaf normal form. Both sides use
the same actual renderer, so recursive call addresses and capture environments
are unchanged. Whole recursive grammar transport is a separate step. -/
theorem body_eq (nodes : List RegularCaptureProduct.Node) (ambient leaves : List Leaf) (specs : List Plan)
    (P : Plan) (hc : Consumer P) (hp : P.All (fun i => i<leaves.length)) (tail : Arg)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E ((chain leaves.length P).exp
      (fun i => render nodes ambient specs (lookup (continued leaves tail) i))) p=
    evV g x s T E (.seq (P.exp (fun i => render nodes ambient specs (lookup leaves i)))
      (render nodes ambient specs tail)) p := by
  have h := chain_correct leaves.length leaves.length
    (fun i q => evV g x s T E (render nodes ambient specs (lookup leaves i)) q)
    (fun i q => evV g x s T E (render nodes ambient specs (lookup (continued leaves tail) i)) q)
    (fun q => evV g x s T E (render nodes ambient specs tail) q)
    (by intro i hi q; rw [lookup_old leaves tail i hi])
    (by
      intro i hi q
      rw [lookup_new leaves tail i hi]
      have hl : lookup leaves i=raw leaves[i] := by simp [lookup,List.getElem?_eq_getElem hi]
      rw [hl]
      exact append_eval nodes ambient specs leaves[i] tail g x s T E q) P hc hp p
  rw [Plan.exp_eval]
  change sem _ (chain leaves.length P) p=_
  rw [h]
  simp only [sequence,sem,evV,Plan.exp_eval]
  rfl


theorem lookup_render (nodes : List RegularCaptureProduct.Node) (leaves : List Leaf) (specs : List Plan)
    (i : Nat) (hi : i<leaves.length) :
    render nodes leaves specs (lookup leaves i)=sourceLeaf nodes leaves specs i := by
  simp only [lookup,sourceLeaf,List.getElem?_eq_getElem hi]
  unfold raw
  split <;> rfl

/-- The generated side is exactly a body of the existing origin-control
source grammar. The common ambient renderer keeps all user-call addresses. -/
theorem source_body_eq (nodes : List RegularCaptureProduct.Node) (leaves : List Leaf) (specs : List Plan)
    (P : Plan) (hc : Consumer P) (hp : P.All (fun i => i<leaves.length)) (tail : Arg)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E ((chain leaves.length P).exp (sourceLeaf nodes (continued leaves tail) specs)) p=
    evV g x s T E (.seq
      (P.exp (fun i => render nodes (continued leaves tail) specs (lookup leaves i)))
      (render nodes (continued leaves tail) specs tail)) p := by
  calc
    _ = evV g x s T E ((chain leaves.length P).exp
        (fun i => render nodes (continued leaves tail) specs (lookup (continued leaves tail) i))) p := by
      rw [Plan.exp_eval,Plan.exp_eval]
      apply Plan.eval_congr
      apply Plan.all_imp _ _ (chain_bounded leaves.length P hc hp)
      intro i hi
      exact congrArg (fun e => evV g x s T E e p)
        (lookup_render nodes (continued leaves tail) specs i (by rw [continued_length]; exact hi)).symm
    _ = _ := body_eq nodes (continued leaves tail) leaves specs P hc hp tail g x s T E p

/-- Capture-dependent tails are allowed whenever a closed leaf cannot be
selected. A closed selected leaf instead requires a closed continuation. -/
theorem continued_valid (nodes : List RegularCaptureProduct.Node) (leaves : List Leaf) (specs : List Plan)
    (hv : LeavesValid nodes leaves specs) (tail : Arg) (ht : Valid nodes specs tail)
    (hc : ∀ r∈leaves, r.shift=none → OriginControlNormalization.Closed tail) :
    LeavesValid nodes (continued leaves tail) specs := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · exact hv r hr
  · obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hr
    exact ⟨fun hn => ⟨(hv r hm).1 hn,hc r hm hn⟩,⟨(hv r hm).2,ht⟩⟩

end Shallot.MacroPeg.CBV.LeafContinuation
