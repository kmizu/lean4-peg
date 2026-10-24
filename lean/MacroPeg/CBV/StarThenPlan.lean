import MacroPeg.CBV.GuardedStarFactor
import MacroPeg.CBV.LeadingReplayStar
import MacroPeg.CBV.ConsumingPlanOutputs

/-! Inline leaf layout for a leading greedy star with an arbitrary final
origin-control plan. No final replay after the star is required. -/
namespace Shallot.MacroPeg.CBV.StarThenPlan
open ReplayControlFusion (Plan)
open OriginControlNormalization
open LeafContinuation
open ContinuationPlan (sequence sem)
open RegularCaptureProduct (Node)
abbrev Arg := RecursiveArgumentCompiler.Expr

def control (ls : List Leaf) (P : Plan) : Arg := expand (lookup ls) P

def tail (ls : List Leaf) (P Q : Plan) (B : Arg) : Arg :=
  let A := control ls P
  let C := control ls Q
  let G := .seq (.notP (.notP (.seq A B))) A
  .seq (.star (.seq B G)) (.seq B C)

def copies (ls : List Leaf) (P : Plan) (K : Arg) : List Leaf :=
  ls.mapIdx (fun i r => if i∈ConsumingPlanOutputs.outputs P then appendBody K r else r)

def layout (ls : List Leaf) (P Q : Plan) (B : Arg) : List Leaf :=
  (ls ++ copies ls P B) ++ copies ls P (tail ls P Q B)

def plan (ls : List Leaf) (P Q : Plan) : Plan :=
  .alt (.guard (chain ls.length P) (chain (2*ls.length) P))
    (.guard (.notP (chain ls.length P)) Q)

def user (ls : List Leaf) (P Q : Plan) (B : Arg) : ContinuationFamily.User :=
  ⟨layout ls P Q B,plan ls P Q,none⟩

theorem lookup_prefix (ls rs : List Leaf) (i : Nat) (hi : i<ls.length) : lookup (ls++rs) i=lookup ls i := by
  simp only [lookup,List.getElem?_append_left hi]

theorem copies_length (ls : List Leaf) (P : Plan) (K : Arg) :
    (copies ls P K).length=ls.length := by simp [copies]

theorem lookup_mapped (pre ls : List Leaf) (P : Plan) (K : Arg) (i : Nat)
    (ho : i∈ConsumingPlanOutputs.outputs P) (hi : i<ls.length) :
    lookup (pre++copies ls P K) (pre.length+i)=raw (appendBody K ls[i]) := by
  simp [lookup,copies,List.getElem?_append_right (by omega : pre.length≤pre.length+i),
    List.getElem?_mapIdx,List.getElem?_eq_getElem hi,ho]

theorem lookup_original (ls : List Leaf) (P Q : Plan) (B : Arg) (i : Nat) (hi : i<ls.length) :
    lookup (layout ls P Q B) i=lookup ls i := by
  rw [layout,lookup_prefix _ _ _ (by simp only [List.length_append,copies_length]; omega),
    lookup_prefix _ _ i hi]

theorem lookup_test (ls : List Leaf) (P Q : Plan) (B : Arg) (i : Nat)
    (ho : i∈ConsumingPlanOutputs.outputs P) (hi : i<ls.length) :
    lookup (layout ls P Q B) (ls.length+i)=raw (appendBody B ls[i]) := by
  rw [layout,lookup_prefix _ _ _ (by simp only [List.length_append,copies_length]; omega)]
  exact lookup_mapped ls ls P B i ho hi

theorem lookup_tail (ls : List Leaf) (P Q : Plan) (B : Arg) (i : Nat)
    (ho : i∈ConsumingPlanOutputs.outputs P) (hi : i<ls.length) :
    lookup (layout ls P Q B) (2*ls.length+i)=raw (appendBody (tail ls P Q B) ls[i]) := by
  have hlen : (ls++copies ls P B).length=2*ls.length := by
    simp only [List.length_append,copies_length]; omega
  rw [layout,←hlen]
  exact lookup_mapped _ ls P (tail ls P Q B) i ho hi

theorem control_eval (nodes : List Node) (ambient : List Leaf) (ps : List Plan) (ls : List Leaf)
    (P : Plan) (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (render nodes ambient ps (control ls P)) p=
    sem (fun i q => evV g x s T E (render nodes ambient ps (lookup ls i)) q) P p := by
  rw [control,LeadingReplayStar.render_expand,Plan.exp_eval]
  rfl

/-- Actual source `(A B)* C` versus the compiled finite control plan. Local
row premises of `chain_correct` are discharged by the generated leaf syntax. -/
theorem body_eq (nodes : List Node) (ambient : List Leaf) (ps : List Plan) (ls : List Leaf)
    (P Q : Plan) (B : Arg) (hc : Consumer P)
    (hp : P.All (fun i => i<ls.length)) (hq : Q.All (fun i => i<ls.length))
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName) (T : ClockFreezing.Table)
    (hT : SoundTV g x s T) (E : List (List Char)) (p : Nat) (hpn : p≤x.length) :
    evV g x s T E (.seq (.star (.seq (render nodes ambient ps (control ls P)) (render nodes ambient ps B)))
      (render nodes ambient ps (control ls Q))) p=
    evV g x s T E (ContinuationFamily.body nodes ambient ps (user ls P Q B)) p := by
  let L := fun i q => evV g x s T E (render nodes ambient ps (lookup ls i)) q
  let R := fun i q => evV g x s T E (render nodes ambient ps (lookup (layout ls P Q B) i)) q
  let a := fun q => evV g x s T E (render nodes ambient ps (control ls P)) q
  let b := fun q => evV g x s T E (render nodes ambient ps B) q
  let c := fun q => evV g x s T E (render nodes ambient ps (control ls Q)) q
  let k := fun q => evV g x s T E (render nodes ambient ps (tail ls P Q B)) q
  have hOrig : ∀ i, i<ls.length → ∀ q, R i q=L i q := by
    intro i hi q
    dsimp only [R,L]
    rw [lookup_original ls P Q B i hi]
  have hAppend (offset : Nat) (K : Arg)
      (hl : ∀ i, i∈ConsumingPlanOutputs.outputs P → ∀ (hi : i<ls.length), lookup (layout ls P Q B) (offset+i)=raw (appendBody K ls[i])) :
      ∀ i, i∈ConsumingPlanOutputs.outputs P → i<ls.length → ∀ q, R (offset+i) q=
        sequence (L i) (fun q => evV g x s T E (render nodes ambient ps K) q) q := by
    intro i ho hi q
    dsimp only [R,L]
    rw [hl i ho hi]
    have hold : lookup ls i=raw ls[i] := by simp [lookup,List.getElem?_eq_getElem hi]
    rw [hold]
    exact append_eval nodes ambient ps ls[i] K g x s T E q
  have ha : sem L P=a := by funext q; exact (control_eval nodes ambient ps ls P g x s T E q).symm
  have hc' : sem L Q=c := by funext q; exact (control_eval nodes ambient ps ls Q g x s T E q).symm
  have ht (q : Nat) := ConsumingPlanOutputs.chain_correct ls.length ls.length L R b hOrig P hc hp
    (hAppend ls.length B (lookup_test ls P Q B)) q
  have hk := ConsumingPlanOutputs.chain_correct ls.length (2*ls.length) L R k hOrig P hc hp
    (hAppend (2*ls.length) (tail ls P Q B) (lookup_tail ls P Q B)) p
  rw [ha] at ht hk
  have htf : (fun q => sem R (chain ls.length P) q)=sequence a b := by funext q; exact ht q
  have hq' := ContinuationPlan.sem_congr ls.length R L hOrig Q hq p
  rw [hc'] at hq'
  let G : MExp := .seq (.andP (.seq (render nodes ambient ps (control ls P)) (render nodes ambient ps B)))
    (render nodes ambient ps (control ls P))
  have hg : (fun q => evV g x s T E G q)=GuardedStarFactor.eligible a b := by
    funext q
    exact GuardedStarFactor.eligible_eval g x s T E _ _ q
  have hK : k=sequence (evStar (sequence b (GuardedStarFactor.eligible a b))) (sequence b c) := by
    change (fun q => evV g x s T E (.seq (.star (.seq (render nodes ambient ps B) G))
      (.seq (render nodes ambient ps B) (render nodes ambient ps (control ls Q)))) q)=_
    change sequence (evStar (sequence b (fun q => evV g x s T E G q))) (sequence b c)=_
    rw [hg]
  have he := GuardedStarFactor.correct_guarded x.length a b c
    (GreedyRotation.evaluator_decreasing g x s hs T hT E _ (render_firstOrder nodes ambient ps (control ls P)))
    (GreedyRotation.evaluator_decreasing g x s hs T hT E _ (render_firstOrder nodes ambient ps B)) p hpn
  change sequence (evStar (sequence a b)) c p=_
  rw [he]
  change _=evV g x s T E ((plan ls P Q).exp (fun i => render nodes ambient ps (lookup (layout ls P Q B) i))) p
  rw [Plan.exp_eval]
  change _=ReplayFallbackFusion.orElse
    (match sem R (chain ls.length P) p with | some (some _) => sem R (chain (2*ls.length) P) p | other => other)
    (match (GreedyRotation.negative (fun q => sem R (chain ls.length P) q) p) with
      | some (some _) => sem R Q p | other => other)
  rw [ht p,hk,hq',hK,htf]
  unfold GuardedStarFactor.guarded
  congr 1
  change (match GreedyRotation.negative (sequence a b) p with
    | some (some j) => c j | other => other)=_
  unfold GreedyRotation.negative
  cases sequence a b p with
  | none => rfl
  | some result => cases result <;> rfl

end Shallot.MacroPeg.CBV.StarThenPlan
