import MacroPeg.CBV.FiniteSuffixRecursiveHelpers

namespace Shallot.MacroPeg.CBV.FiniteSuffixRecursiveSelection
open FiniteSuffixRecursiveSyntax FiniteSuffixRecursiveHelpers
open RegularCaptureProduct (Node)
open FiniteSuffixReplay (palette)
open FiniteWordCaptureSelection (test choose select gather classify)
abbrev Spec := FiniteSuffixRecursiveSyntax.Rule

theorem helper_eq (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (x : List Char) (k : Nat) (E : List (List Char)) (i p : Nat) (hi : i<nodes.length) (hp : p≤x.length) :
    evV (source nodes R rs) x .callByValuePar (sourceTable nodes R rs x k) E (.call i []) p=
      evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (.call i []) p := by
  have hb : i<(base nodes R).rules.length := Nat.lt_of_lt_of_le hi (by simp [RegularCaptureProduct.grammar])
  exact (source_query nodes hn R rs x k E i p hi hp).trans (target_query nodes hn R rs x k i p hb hp).symm

theorem test_at (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (x : List Char) (k i j p q : Nat) (hi : i<nodes.length) (hp : p≤x.length) (u : List Char)
    (hu : (palette R)[j]?=some u)
    (hv : evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (.call i []) p=some (some q)) :
    evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (test nodes (palette R) i j u) p=
      if pre x p q=u then some (some p) else some none := by
  have hb : i<(base nodes R).rules.length := Nat.lt_of_lt_of_le hi (by simp [RegularCaptureProduct.grammar])
  have hbase := (target_query nodes hn R rs x k i p hb hp).symm.trans hv
  have ht := target_lexical nodes hn R rs x k (test nodes (palette R) i j u) (by
    change RegularCaptureProduct.key nodes (ExactWordCaptureMachine.observer (palette R)) i
      (ExactWordCaptureMachine.start (palette R) j) (ExactWordCaptureMachine.start (palette R) j+u.length)<(base nodes R).rules.length
    exact RegularCaptureProduct.key_bound nodes _ (ExactWordCaptureMachine.observer_valid _).1 i _ _ hi
      (ExactWordCaptureMachine.start_bound _ j u hu) (ExactWordCaptureMachine.accept_bound _ j u hu)) p hp
  exact ht.trans (FiniteWordCaptureSelection.test_eval nodes hn (palette R) x i j p q hi hp u hu hbase)

theorem choose_at (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (x : List Char) (k i p q : Nat) (hi : i<nodes.length) (hp : p≤x.length)
    (hv : evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (.call i []) p=some (some q))
    (K : Option (List Char) → MExp) : ∀ entries,
    (∀ pair∈entries, (palette R)[pair.2]?=some pair.1) →
    evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (choose nodes (palette R) i K entries) p=
      evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) []
        (K (if pre x p q∈entries.map Prod.fst then some (pre x p q) else none)) p
  | [],_ => rfl
  | (u,j)::rest,h => by
    have hh := test_at nodes hn R rs x k i j p q hi hp u (h (u,j) (by simp)) hv
    rw [choose]
    by_cases he : pre x p q=u
    · rw [if_pos he] at hh
      rw [ScannerFrontier.branch_eval _ _ _ p true hh]; simp [he]
    · rw [if_neg he] at hh
      rw [ScannerFrontier.branch_eval _ _ _ p false hh]
      simp only [Bool.false_eq_true,if_false]
      rw [choose_at nodes hn R rs x k i p q hi hp hv K rest (by intro a ha; exact h a (by simp [ha]))]
      simp only [List.map_cons,Prod.fst,List.mem_cons,he,false_or]

theorem select_at (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (x : List Char) (k i p : Nat) (hi : i<nodes.length) (hp : p≤x.length) (K : Option (List Char) → MExp) :
    evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (select nodes (palette R) i K) p=
      match evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (.call i []) p with
      | some (some q) => evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (K (classify (palette R) (pre x p q))) p
      | other => other := by
  unfold select
  change (match evV _ _ _ _ [] (.andP (.call i [])) p with
    | some (some j) => evV _ _ _ _ [] (choose nodes (palette R) i K (palette R).zipIdx) j | other => other)=_
  rw [CallLookahead.evV_peek]
  cases hv : evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (.call i []) p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some q =>
      simp only [CallLookahead.peek]
      rw [choose_at nodes hn R rs x k i p q hi hp hv K (palette R).zipIdx (by
        intro pair hm
        obtain ⟨a,j⟩ := pair
        simpa only [List.mk_mem_zipIdx_iff_getElem?,Nat.sub_zero,Nat.zero_le,and_true,true_and] using hm)]
      simp only [List.zipIdx_map_fst,classify]

/-- The continuation may call the mutually recursive user component.
Only the original/filtered helper queries are frozen. -/
theorem gather_at (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (x : List Char) (k : Nat) (ids : List Nat) (hids : ∀ i∈ids, i<nodes.length) (p : Nat) (hp : p≤x.length)
    (K : View → MExp) :
    evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (gather nodes (palette R) ids K) p=
      match evParArgs (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (ids.map (fun i => .call i [])) p with
      | some (some W) => evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (K (FiniteSuffixReplay.views R W)) p
      | some none => some none | none => none := by
  induction ids generalizing K with
  | nil => rfl
  | cons i ids ih =>
    rw [gather,select_at nodes hn R rs x k i p (hids i (by simp)) hp]
    simp only [List.map_cons,evParArgs]
    cases hv : evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (.call i []) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some q =>
        dsimp only []
        rw [ih (by intro j hj; exact hids j (by simp [hj]))]
        cases ht : evParArgs (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (ids.map (fun j => .call j [])) p with
        | none => rfl
        | some v => cases v <;> rfl

theorem arguments_eq (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    ∀ (ids : List Nat), (∀ i∈ids, i<nodes.length) →
    evParArgs (source nodes R rs) x .callByValuePar (sourceTable nodes R rs x k) E (ids.map (fun i => .call i [])) p=
      evParArgs (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (ids.map (fun i => .call i [])) p
  | [],_ => rfl
  | i::ids,h => by
    simp only [List.map_cons,evParArgs]
    rw [helper_eq nodes hn R rs x k E i p (h i (by simp)) hp]
    cases hv : evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (.call i []) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some q => rw [arguments_eq nodes hn R rs x k E p hp ids (by intro j hj; exact h j (by simp [hj]))]

end Shallot.MacroPeg.CBV.FiniteSuffixRecursiveSelection
