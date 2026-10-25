import MacroPeg.CBV.FiniteSuffixReplay
import MacroPeg.CBV.CaptureProductExtension

namespace Shallot.MacroPeg.CBV.FiniteWordCaptureSelection
open RegularCaptureProduct (Node grammar call filtered)
open ExactWordCaptureMachine (observer start)
open ClockFreezing (Table)

abbrev table (nodes : List Node) (ws : List (List Char)) (x : List Char) :=
  tblV (grammar nodes (observer ws)) x .callByValueSeq (iterBoundV (grammar nodes (observer ws)) x)

def classify (ws : List (List Char)) (w : List Char) : Option (List Char) := if w∈ws then some w else none

def test (nodes : List Node) (ws : List (List Char)) (i j : Nat) (u : List Char) : MExp :=
  .andP (call nodes (observer ws) i (start ws j) (start ws j+u.length))

def choose (nodes : List Node) (ws : List (List Char)) (i : Nat)
    (K : Option (List Char) → MExp) : List (List Char × Nat) → MExp
  | [] => K none
  | (u,j)::rest => RootObservation.branch (test nodes ws i j u) (K (some u)) (choose nodes ws i K rest)

def select (nodes : List Node) (ws : List (List Char)) (i : Nat) (K : Option (List Char) → MExp) : MExp :=
  .seq (.andP (.call i [])) (choose nodes ws i K ws.zipIdx)

/-- Each equality probe observes the original committed capture, including
captures outside the entire dictionary. -/
theorem test_eval (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (ws : List (List Char))
    (x : List Char) (i j p q : Nat) (hi : i<nodes.length) (hp : p≤x.length) (u : List Char)
    (hu : ws[j]?=some u)
    (hv : evV (grammar nodes (observer ws)) x .callByValueSeq (table nodes ws x) [] (.call i []) p=some (some q)) :
    evV (grammar nodes (observer ws)) x .callByValueSeq (table nodes ws x) [] (test nodes ws i j u) p=
      if pre x p q=u then some (some p) else some none := by
  have hh := RegularCaptureProduct.product_correct nodes hn (observer ws) (ExactWordCaptureMachine.observer_valid ws)
    x i (start ws j) (start ws j+u.length) p hi
    (ExactWordCaptureMachine.start_bound ws j u hu) (ExactWordCaptureMachine.accept_bound ws j u hu) hp
  change evV _ _ _ _ [] (call nodes (observer ws) i (start ws j) (start ws j+u.length)) p=
    filtered (observer ws) x (start ws j) (start ws j+u.length) p
      (evV _ _ _ _ [] (.call i []) p) at hh
  rw [hv] at hh
  rw [test,CallLookahead.evV_peek,hh]
  have he := ExactWordCaptureMachine.observes_exact ws j u (pre x p q) hu
  by_cases hw : pre x p q=u
  · rw [filtered,if_pos (he.mpr hw)]; simp [CallLookahead.peek,hw]
  · rw [filtered,if_neg (fun h => hw (he.mp h))]; simp [CallLookahead.peek,hw]

theorem choose_eval (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (ws : List (List Char))
    (x : List Char) (i p q : Nat) (hi : i<nodes.length) (hp : p≤x.length)
    (hv : evV (grammar nodes (observer ws)) x .callByValueSeq (table nodes ws x) [] (.call i []) p=some (some q))
    (K : Option (List Char) → MExp) : ∀ entries,
    (∀ pair∈entries, ws[pair.2]?=some pair.1) →
    evV (grammar nodes (observer ws)) x .callByValueSeq (table nodes ws x) [] (choose nodes ws i K entries) p=
      evV (grammar nodes (observer ws)) x .callByValueSeq (table nodes ws x) []
        (K (if pre x p q∈entries.map Prod.fst then some (pre x p q) else none)) p
  | [],_ => rfl
  | (u,j)::rest,h => by
    have hh := test_eval nodes hn ws x i j p q hi hp u (h (u,j) (by simp)) hv
    rw [choose]
    by_cases he : pre x p q=u
    · rw [if_pos he] at hh
      rw [ScannerFrontier.branch_eval _ _ _ p true hh]
      simp [he]
    · rw [if_neg he] at hh
      rw [ScannerFrontier.branch_eval _ _ _ p false hh]
      simp only [Bool.false_eq_true,if_false]
      rw [choose_eval nodes hn ws x i p q hi hp hv K rest (by intro a ha; exact h a (by simp [ha]))]
      simp only [List.map_cons,Prod.fst,List.mem_cons,he,false_or]

theorem select_eval (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (ws : List (List Char))
    (x : List Char) (i p : Nat) (hi : i<nodes.length) (hp : p≤x.length) (K : Option (List Char) → MExp) :
    evV (grammar nodes (observer ws)) x .callByValueSeq (table nodes ws x) [] (select nodes ws i K) p=
      match evV (grammar nodes (observer ws)) x .callByValueSeq (table nodes ws x) [] (.call i []) p with
      | some (some q) => evV (grammar nodes (observer ws)) x .callByValueSeq (table nodes ws x) [] (K (classify ws (pre x p q))) p
      | other => other := by
  unfold select
  change (match evV _ _ _ _ [] (.andP (.call i [])) p with
    | some (some j) => evV _ _ _ _ [] (choose nodes ws i K ws.zipIdx) j | other => other)=_
  rw [CallLookahead.evV_peek]
  cases hv : evV (grammar nodes (observer ws)) x .callByValueSeq (table nodes ws x) [] (.call i []) p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some q =>
      simp only [CallLookahead.peek]
      rw [choose_eval nodes hn ws x i p q hi hp hv K ws.zipIdx (by
        intro pair hm
        obtain ⟨a,j⟩ := pair
        simpa only [List.mk_mem_zipIdx_iff_getElem?,Nat.sub_zero,Nat.zero_le,and_true,true_and] using hm)]
      simp only [List.zipIdx_map_fst,classify]

def gather (nodes : List Node) (ws : List (List Char)) : List Nat → (List (Option (List Char)) → MExp) → MExp
  | [],K => K []
  | i::ids,K => select nodes ws i (fun v => gather nodes ws ids (fun V => K (v::V)))

theorem gather_eval (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (ws : List (List Char))
    (x : List Char) (ids : List Nat) (hids : ∀ i∈ids, i<nodes.length) (p : Nat) (hp : p≤x.length)
    (K : List (Option (List Char)) → MExp) :
    evV (grammar nodes (observer ws)) x .callByValueSeq (table nodes ws x) [] (gather nodes ws ids K) p=
      match evParArgs (grammar nodes (observer ws)) x .callByValueSeq (table nodes ws x) [] (ids.map (fun i => .call i [])) p with
      | some (some W) => evV (grammar nodes (observer ws)) x .callByValueSeq (table nodes ws x) [] (K (W.map (classify ws))) p
      | some none => some none | none => none := by
  induction ids generalizing K with
  | nil => rfl
  | cons i ids ih =>
    rw [gather,select_eval nodes hn ws x i p (hids i (by simp)) hp]
    simp only [List.map_cons,evParArgs]
    cases hv : evV (grammar nodes (observer ws)) x .callByValueSeq (table nodes ws x) [] (.call i []) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some q =>
        dsimp only []
        rw [ih (by intro j hj; exact hids j (by simp [hj]))]
        cases ht : evParArgs (grammar nodes (observer ws)) x .callByValueSeq (table nodes ws x) [] (ids.map (fun j => .call j [])) p with
        | none => rfl
        | some v => cases v <;> rfl


theorem choose_firstOrder (nodes : List Node) (ws : List (List Char)) (i : Nat)
    (K : Option (List Char) → MExp) (hK : ∀ v, (K v).FirstOrder) :
    ∀ entries, (choose nodes ws i K entries).FirstOrder
  | [] => hK none
  | (u,j)::rest => ⟨⟨True.intro,hK (some u)⟩,True.intro,choose_firstOrder nodes ws i K hK rest⟩

theorem select_firstOrder (nodes : List Node) (ws : List (List Char)) (i : Nat)
    (K : Option (List Char) → MExp) (hK : ∀ v, (K v).FirstOrder) :
    (select nodes ws i K).FirstOrder := ⟨True.intro,choose_firstOrder nodes ws i K hK _⟩

theorem gather_firstOrder (nodes : List Node) (ws : List (List Char)) :
    ∀ ids K, (∀ V, (K V).FirstOrder) → (gather nodes ws ids K).FirstOrder
  | [],K,hK => hK []
  | i::ids,K,hK => select_firstOrder nodes ws i _ (fun v => gather_firstOrder nodes ws ids _ (fun V => hK (v::V)))

end Shallot.MacroPeg.CBV.FiniteWordCaptureSelection
