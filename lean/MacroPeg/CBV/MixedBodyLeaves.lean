import MacroPeg.CBV.MixedOriginControl
import MacroPeg.CBV.StarThenPlan

namespace Shallot.MacroPeg.CBV.MixedBodyLeaves
open AdjacentCallsiteRecursive (Header)
open MixedAdjacentRecursive (Body sourcePrefix)
open MixedOriginControl (Part Spec render embed render_firstOrder)
open ReplayControlFusion (Plan)
open LeafContinuation (Consumer chain)
open ContinuationPlan (sem sequence)
variable {H : Header}

def raw (r : Part H) : Body H :=
  if r.stuck then .star .eps else
    .seq (if r.split then .seq (embed H H.head) (.param 0) else .param 0) r.body

def lookup (ls : List (Part H)) (i : Nat) : Body H :=
  match ls[i]? with | some r => raw r | none => .notP .eps

def appendBody (tail : Body H) (r : Part H) : Part H := {r with body := .seq r.body tail}

theorem render_embed (H : Header) (ps : List Spec) :
    ∀ e, HelperArgument.Syntax 0 e → render H ps (embed H e)=e
  | .seq a b, h | .alt a b, h => by simp only [embed,render,render_embed H ps a h.1,render_embed H ps b h.2]
  | .star a, h | .notP a, h => by simp only [embed,render,render_embed H ps a h]
  | .param _, _ | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => rfl
  | .call i [], h => by simp [HelperArgument.Syntax] at h
  | .call _ (_::_), h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem raw_render (H : Header) (ps : List Spec) (r : Part H) :
    render H ps (raw r)=if r.stuck then .star .eps else .seq (sourcePrefix H r.split) (render H ps r.body) := by
  cases hd : r.stuck <;> cases hs : r.split <;>
    simp only [raw,hd,hs,Bool.false_eq_true,ite_false,ite_true,render,sourcePrefix,
      render_embed H ps H.head (LastCodewordGrammar.pure_syntax _ H.pure)]

theorem append_eval (H : Header) (ps : List Spec) (r : Part H) (tail : Body H)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (p : Nat) :
    evV g x s T E (render H ps (raw (appendBody tail r))) p=
      sequence (fun q => evV g x s T E (render H ps (raw r)) q)
        (fun q => evV g x s T E (render H ps tail) q) p := by
  rw [raw_render,raw_render]
  cases hd : r.stuck
  · simp only [appendBody,hd,Bool.false_eq_true,ite_false,render]
    change (match evV g x s T E (sourcePrefix H r.split) p with
      | some (some q) => evV g x s T E (.seq (render H ps r.body) (render H ps tail)) q
      | other => other)=_
    unfold sequence
    change _=(match (match evV g x s T E (sourcePrefix H r.split) p with
      | some (some q) => evV g x s T E (render H ps r.body) q | other => other) with
      | some (some q) => evV g x s T E (render H ps tail) q | other => other)
    cases evV g x s T E (sourcePrefix H r.split) p with
    | none => rfl
    | some v => cases v <;> rfl
  · simp only [appendBody,hd,ite_true,MixedOriginControl.stuck_eval,sequence]

def control (ls : List (Part H)) (P : Plan) : Body H := MixedOriginControl.expand (lookup ls) P

def tail (ls : List (Part H)) (P Q : Plan) (B : Body H) : Body H :=
  let A := control ls P
  let C := control ls Q
  let G := .seq (.notP (.notP (.seq A B))) A
  .seq (.star (.seq B G)) (.seq B C)

def copies (ls : List (Part H)) (P : Plan) (K : Body H) : List (Part H) :=
  ls.mapIdx (fun i r => if i∈ConsumingPlanOutputs.outputs P then appendBody K r else r)

def layout (ls : List (Part H)) (P Q : Plan) (B : Body H) : List (Part H) :=
  (ls ++ copies ls P B) ++ copies ls P (tail ls P Q B)

def plan (ls : List (Part H)) (P Q : Plan) : Plan :=
  .alt (.guard (chain ls.length P) (chain (2*ls.length) P))
    (.guard (.notP (chain ls.length P)) Q)

theorem lookup_prefix (ls rs : List (Part H)) (i : Nat) (hi : i<ls.length) : lookup (ls++rs) i=lookup ls i := by
  simp only [lookup,List.getElem?_append_left hi]

theorem copies_length (ls : List (Part H)) (P : Plan) (K : Body H) :
    (copies ls P K).length=ls.length := by simp [copies]

theorem lookup_mapped (pre ls : List (Part H)) (P : Plan) (K : Body H) (i : Nat)
    (ho : i∈ConsumingPlanOutputs.outputs P) (hi : i<ls.length) :
    lookup (pre++copies ls P K) (pre.length+i)=raw (appendBody K ls[i]) := by
  simp [lookup,copies,List.getElem?_append_right (by omega : pre.length≤pre.length+i),
    List.getElem?_mapIdx,List.getElem?_eq_getElem hi,ho]

theorem lookup_original (ls : List (Part H)) (P Q : Plan) (B : Body H) (i : Nat) (hi : i<ls.length) :
    lookup (layout ls P Q B) i=lookup ls i := by
  rw [layout,lookup_prefix _ _ _ (by simp only [List.length_append,copies_length]; omega),
    lookup_prefix _ _ i hi]

theorem lookup_test (ls : List (Part H)) (P Q : Plan) (B : Body H) (i : Nat)
    (ho : i∈ConsumingPlanOutputs.outputs P) (hi : i<ls.length) :
    lookup (layout ls P Q B) (ls.length+i)=raw (appendBody B ls[i]) := by
  rw [layout,lookup_prefix _ _ _ (by simp only [List.length_append,copies_length]; omega)]
  exact lookup_mapped ls ls P B i ho hi

theorem lookup_tail (ls : List (Part H)) (P Q : Plan) (B : Body H) (i : Nat)
    (ho : i∈ConsumingPlanOutputs.outputs P) (hi : i<ls.length) :
    lookup (layout ls P Q B) (2*ls.length+i)=raw (appendBody (tail ls P Q B) ls[i]) := by
  have hlen : (ls++copies ls P B).length=2*ls.length := by
    simp only [List.length_append,copies_length]; omega
  rw [layout,←hlen]
  exact lookup_mapped _ ls P (tail ls P Q B) i ho hi

theorem render_expand (H : Header) (ps : List Spec) (L : Nat → Body H) :
    ∀ P, render H ps (MixedOriginControl.expand L P)=P.exp (fun i => render H ps (L i))
  | .leaf _ => rfl
  | .alt a b | .guard a b => by simp only [MixedOriginControl.expand,render,Plan.exp,MExp.andP,render_expand H ps L a,render_expand H ps L b]
  | .notP a => by simp only [MixedOriginControl.expand,render,Plan.exp,render_expand H ps L a]

theorem control_eval (H : Header) (ps : List Spec) (ls : List (Part H))
    (P : Plan) (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (render H ps (control ls P)) p=
    sem (fun i q => evV g x s T E (render H ps (lookup ls i)) q) P p := by
  rw [control,render_expand,Plan.exp_eval]
  rfl

/-- Actual source `(A B)* C` versus the compiled finite control plan. Local
row premises of `chain_correct` are discharged by the generated leaf syntax. -/
theorem body_eq (H : Header) (ps : List Spec) (ls : List (Part H))
    (P Q : Plan) (B : Body H) (hc : Consumer P)
    (hp : P.All (fun i => i<ls.length)) (hq : Q.All (fun i => i<ls.length))
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName) (T : ClockFreezing.Table)
    (hT : SoundTV g x s T) (E : List (List Char)) (p : Nat) (hpn : p≤x.length) :
    evV g x s T E (.seq (.star (.seq (render H ps (control ls P)) (render H ps B)))
      (render H ps (control ls Q))) p=
    evV g x s T E (((plan ls P Q).exp (fun i => render H ps (lookup (layout ls P Q B) i)))) p := by
  let L := fun i q => evV g x s T E (render H ps (lookup ls i)) q
  let R := fun i q => evV g x s T E (render H ps (lookup (layout ls P Q B) i)) q
  let a := fun q => evV g x s T E (render H ps (control ls P)) q
  let b := fun q => evV g x s T E (render H ps B) q
  let c := fun q => evV g x s T E (render H ps (control ls Q)) q
  let k := fun q => evV g x s T E (render H ps (tail ls P Q B)) q
  have hOrig : ∀ i, i<ls.length → ∀ q, R i q=L i q := by
    intro i hi q
    dsimp only [R,L]
    rw [lookup_original ls P Q B i hi]
  have hAppend (offset : Nat) (K : Body H)
      (hl : ∀ i, i∈ConsumingPlanOutputs.outputs P → ∀ (hi : i<ls.length), lookup (layout ls P Q B) (offset+i)=raw (appendBody K ls[i])) :
      ∀ i, i∈ConsumingPlanOutputs.outputs P → i<ls.length → ∀ q, R (offset+i) q=
        sequence (L i) (fun q => evV g x s T E (render H ps K) q) q := by
    intro i ho hi q
    dsimp only [R,L]
    rw [hl i ho hi]
    have hold : lookup ls i=raw ls[i] := by simp [lookup,List.getElem?_eq_getElem hi]
    rw [hold]
    exact append_eval H ps ls[i] K g x s T E q
  have ha : sem L P=a := by funext q; exact (control_eval H ps ls P g x s T E q).symm
  have hc' : sem L Q=c := by funext q; exact (control_eval H ps ls Q g x s T E q).symm
  have ht (q : Nat) := ConsumingPlanOutputs.chain_correct ls.length ls.length L R b hOrig P hc hp
    (hAppend ls.length B (lookup_test ls P Q B)) q
  have hk := ConsumingPlanOutputs.chain_correct ls.length (2*ls.length) L R k hOrig P hc hp
    (hAppend (2*ls.length) (tail ls P Q B) (lookup_tail ls P Q B)) p
  rw [ha] at ht hk
  have htf : (fun q => sem R (chain ls.length P) q)=sequence a b := by funext q; exact ht q
  have hq' := ContinuationPlan.sem_congr ls.length R L hOrig Q hq p
  rw [hc'] at hq'
  let G : MExp := .seq (.andP (.seq (render H ps (control ls P)) (render H ps B)))
    (render H ps (control ls P))
  have hg : (fun q => evV g x s T E G q)=GuardedStarFactor.eligible a b := by
    funext q
    exact GuardedStarFactor.eligible_eval g x s T E _ _ q
  have hK : k=sequence (evStar (sequence b (GuardedStarFactor.eligible a b))) (sequence b c) := by
    change (fun q => evV g x s T E (.seq (.star (.seq (render H ps B) G))
      (.seq (render H ps B) (render H ps (control ls Q)))) q)=_
    change sequence (evStar (sequence b (fun q => evV g x s T E G q))) (sequence b c)=_
    rw [hg]
  have he := GuardedStarFactor.correct_guarded x.length a b c
    (GreedyRotation.evaluator_decreasing g x s hs T hT E _ (render_firstOrder H ps (control ls P)))
    (GreedyRotation.evaluator_decreasing g x s hs T hT E _ (render_firstOrder H ps B)) p hpn
  change sequence (evStar (sequence a b)) c p=_
  rw [he]
  change _=evV g x s T E ((plan ls P Q).exp (fun i => render H ps (lookup (layout ls P Q B) i))) p
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

end Shallot.MacroPeg.CBV.MixedBodyLeaves
