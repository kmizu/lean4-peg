import MacroPeg.CBV.FragmentMixedRecursive
import MacroPeg.CBV.NullableStarControl
import MacroPeg.CBV.ContinuationFamily

namespace Shallot.MacroPeg.CBV.FragmentMixedForm
open ReplayControlFusion (Plan)
open ContinuationFamily (shift)
open ContinuationPlan (sem sequence bind)
open RuntimeShiftFilter (scanner)
open FragmentMixedRecursive (Part head render stuck)

def raw : Option Part → MExp
  | some b => .seq (head b.1) (.seq (.param 0) b.2)
  | none => stuck
def lookup (ls : List (Option Part)) (i : Nat) : MExp :=
  match ls[i]? with | some b => raw b | none => MExp.failAlways

def copies (ls : List (Option Part)) (K : MExp) : List (Option Part) := ls.map (fun b => b.map (fun b => (b.1,.seq b.2 K)))

structure Form where
  leaves : List (Option Part)
  plan : Plan
  bounded : plan.All (fun i => i<leaves.length)
  positive : 0<leaves.length

def Form.syntax (f : Form) : MExp := f.plan.exp (lookup f.leaves)
def atom (b : Part) : Form := ⟨[some b],.leaf 0,by simp [Plan.All],by simp⟩
def neg (f : Form) : Form := ⟨f.leaves,.notP f.plan,f.bounded,f.positive⟩

structure Pair where
  leaves : List (Option Part)
  left : Plan
  right : Plan
  left_bound : left.All (fun i => i<leaves.length)
  right_bound : right.All (fun i => i<leaves.length)
  positive : 0<leaves.length

def join (f g : Form) : Pair where
  leaves := f.leaves++g.leaves
  left := f.plan
  right := shift f.leaves.length g.plan
  left_bound := Plan.all_imp (fun i hi => by simp only [List.length_append]; omega) _ f.bounded
  right_bound := ContinuationFamily.shift_all _ _ _ (by simp) _ g.bounded
  positive := by simp only [List.length_append]; have := f.positive; omega

def choice (f g : Form) : Form :=
  let j := join f g
  ⟨j.leaves,.alt j.left j.right,⟨j.left_bound,j.right_bound⟩,j.positive⟩

/-- Guard the selected branch before running its continuation copy. A
negative zero-consuming output instead runs Q at the unchanged position. -/
def compose (f g : Form) : Form :=
  let j := join f g
  let C := j.right.exp (lookup j.leaves)
  ⟨j.leaves++copies j.leaves C,bind j.leaves.length j.left j.right,
    by simpa [copies,Nat.two_mul] using ContinuationPlan.bind_bounded j.leaves.length j.right j.right_bound j.left j.left_bound,
    by simp only [List.length_append]; have := j.positive; omega⟩

theorem lookup_prefix (ls rs : List (Option Part)) (i : Nat) (hi : i<ls.length) :
    lookup (ls++rs) i=lookup ls i := by simp only [lookup,List.getElem?_append_left hi]

theorem lookup_copy (ls : List (Option Part)) (K : MExp) (i : Nat) (hi : i<ls.length) :
    lookup (ls++copies ls K) (ls.length+i)=raw (ls[i].map (fun b => (b.1,.seq b.2 K))) := by
  simp [lookup,copies,List.getElem?_append_right,List.getElem?_map,List.getElem?_eq_getElem hi]

theorem render_scanner (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool) : render kinds n plans par false scanner=scanner := by
  simp [scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,MExp.failAlways,render]

theorem render_head (kinds : List Bool) (n : Nat) (plans : List Plan) (par split : Bool) :
    render kinds n plans par false (head split)=head split := by
  cases split
  · rfl
  · exact render_scanner kinds n plans par

theorem render_raw (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool) (b : Part) :
    render kinds n plans par false (raw (some b))=.seq (head b.1) (.seq (.param 0) (render kinds n plans par false b.2)) := by
  simp only [raw,render,render_head]

theorem render_plan (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool) (L : Nat → MExp) :
    ∀ (P : Plan), render kinds n plans par false (P.exp L)=P.exp (fun i => render kinds n plans par false (L i))
  | .leaf _ => rfl
  | .alt a b | .guard a b => by simp only [Plan.exp,MExp.andP,render,render_plan kinds n plans par L a,render_plan kinds n plans par L b]
  | .notP a => by simp only [Plan.exp,render,render_plan kinds n plans par L a]

theorem append_eval (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool) (b : Option Part) (K : MExp)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (p : Nat) :
    evV g x s T E (render kinds n plans par false (raw (b.map (fun b => (b.1,.seq b.2 K))))) p=
      sequence (fun q => evV g x s T E (render kinds n plans par false (raw b)) q)
        (fun q => evV g x s T E (render kinds n plans par false K) q) p := by
  cases b with
  | none =>
    change evV g x s T E stuck p=sequence (fun q => evV g x s T E stuck q)
      (fun q => evV g x s T E (render kinds n plans par false K) q) p
    simp only [stuck,MixedOriginControl.stuck_eval,sequence]
  | some b =>
    simp only [Option.map_some]
    rw [render_raw,render_raw]
    simp only [render]
    unfold sequence
    change (match evV g x s T E (head b.1) p with
      | some (some q) => evV g x s T E (.seq (.param 0) (.seq (render kinds n plans par false b.2) (render kinds n plans par false K))) q
      | other => other)=
      (match (match evV g x s T E (head b.1) p with
        | some (some q) => evV g x s T E (.seq (.param 0) (render kinds n plans par false b.2)) q
        | other => other) with
        | some (some q) => evV g x s T E (render kinds n plans par false K) q | other => other)
    cases evV g x s T E (head b.1) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some q =>
        change (match evV g x s T E (.param 0) q with
          | some (some j) => evV g x s T E (.seq (render kinds n plans par false b.2) (render kinds n plans par false K)) j
          | other => other)=
          (match (match evV g x s T E (.param 0) q with
            | some (some j) => evV g x s T E (render kinds n plans par false b.2) j | other => other) with
            | some (some j) => evV g x s T E (render kinds n plans par false K) j | other => other)
        cases evV g x s T E (.param 0) q with
        | none => rfl
        | some v => cases v <;> rfl

theorem control_eval (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool) (ls : List (Option Part)) (P : Plan)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (render kinds n plans par false (P.exp (lookup ls))) p=
      sem (fun i q => evV g x s T E (render kinds n plans par false (lookup ls i)) q) P p := by
  rw [render_plan,Plan.exp_eval]; rfl

private theorem exp_congr (L R : Nat → MExp) : ∀ (P : Plan), P.All (fun i => L i=R i) → P.exp L=P.exp R
  | .leaf _, h => h
  | .alt a b, h | .guard a b, h => by simp only [Plan.exp,exp_congr L R a h.1,exp_congr L R b h.2]
  | .notP a, h => by simp only [Plan.exp,exp_congr L R a h]
private theorem exp_shift (L : Nat → MExp) (offset : Nat) :
    ∀ P, (shift offset P).exp L=P.exp (fun i => L (offset+i))
  | .leaf _ => rfl
  | .alt a b | .guard a b => by simp only [shift,Plan.exp,exp_shift L offset a,exp_shift L offset b]
  | .notP a => by simp only [shift,Plan.exp,exp_shift L offset a]

theorem join_left (f g : Form) : (join f g).left.exp (lookup (join f g).leaves)=f.syntax := by
  apply exp_congr
  exact Plan.all_imp (fun i hi => lookup_prefix _ _ i hi) _ f.bounded

theorem join_right (f g : Form) : (join f g).right.exp (lookup (join f g).leaves)=g.syntax := by
  change (shift _ g.plan).exp _=_
  rw [exp_shift]
  apply exp_congr
  apply Plan.all_imp _ _ g.bounded
  intro i hi
  simp [lookup,join,List.getElem?_append_right (by omega : f.leaves.length≤f.leaves.length+i)]

theorem compose_eval (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool) (f h : Form)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (render kinds n plans par false (compose f h).syntax) p=
      evV g x s T E (.seq (render kinds n plans par false f.syntax) (render kinds n plans par false h.syntax)) p := by
  let j := join f h
  let C := j.right.exp (lookup j.leaves)
  let L := fun i q => evV g x s T E (render kinds n plans par false (lookup j.leaves i)) q
  let R := fun i q => evV g x s T E (render kinds n plans par false (lookup (j.leaves++copies j.leaves C) i)) q
  have hOrig : ∀ i, i<j.leaves.length → ∀ q, R i q=L i q := by
    intro i hi q; dsimp only [R,L]; rw [lookup_prefix _ _ i hi]
  have ht : ∀ i, i<j.leaves.length → ∀ q, R (j.leaves.length+i) q=sequence (L i) (sem L j.right) q := by
    intro i hi q
    dsimp only [R,L]
    rw [lookup_copy _ _ i hi]
    have hl : lookup j.leaves i=raw j.leaves[i] := by simp [lookup,List.getElem?_eq_getElem hi]
    rw [hl,append_eval]
    apply congrArg (fun K => sequence (fun q => evV g x s T E (render kinds n plans par false (raw j.leaves[i])) q) K q)
    funext q
    exact control_eval kinds n plans par j.leaves j.right g x s T E q
  have he := ContinuationPlan.bind_correct j.leaves.length j.leaves.length L R hOrig j.right j.right_bound ht j.left j.left_bound p
  change evV g x s T E (render kinds n plans par false ((bind j.leaves.length j.left j.right).exp
    (lookup (j.leaves++copies j.leaves C)))) p=_
  rw [control_eval]
  change sem R (bind j.leaves.length j.left j.right) p=_
  rw [he]
  have ha : sem L j.left=(fun q => evV g x s T E (render kinds n plans par false f.syntax) q) := by
    funext q; rw [←control_eval kinds n plans par j.leaves j.left g x s T E q,join_left]
  have hb : sem L j.right=(fun q => evV g x s T E (render kinds n plans par false h.syntax) q) := by
    funext q; rw [←control_eval kinds n plans par j.leaves j.right g x s T E q,join_right]
  rw [ha,hb]; rfl


/-- Appending a continuation to a divergent leaf keeps divergence at origin. -/
def tail (ls : List (Option Part)) (P Q : Plan) (B : MExp) : MExp :=
  let A := P.exp (lookup ls)
  let C := Q.exp (lookup ls)
  let G := .seq (.andP (.seq A B)) A
  .seq (.star (.seq B G)) (.seq B C)

def layout (ls : List (Option Part)) (P Q : Plan) (B : MExp) : List (Option Part) :=
  (ls++copies ls B)++copies ls (tail ls P Q B)
def loopPlan (n : Nat) (P Q : Plan) : Plan :=
  .alt (.guard (LeafContinuation.chain n P) (LeafContinuation.chain (2*n) P))
    (.guard (.notP (LeafContinuation.chain n P)) Q)

def repeatThen (f : Form) (B : MExp) (g : Form) : Form :=
  let j := join f g
  let n := j.leaves.length
  ⟨layout j.leaves j.left j.right B,loopPlan n j.left j.right,
    by
      have hlen : (layout j.leaves j.left j.right B).length=3*n := by
        simp [layout,copies]; omega
      rw [hlen]
      have hp := j.positive
      have hzero : (Plan.leaf 0).All (fun i => i<3*n) := by change 0<3*n; omega
      have ht := ConsumingPlanOutputs.bind_bound n n (3*n) (by omega) (by omega) (.leaf 0) hzero _ j.left_bound
      have hk := ConsumingPlanOutputs.bind_bound n (2*n) (3*n) (by omega) (by omega) (.leaf 0) hzero _ j.left_bound
      exact ⟨⟨ht,hk⟩,ht,Plan.all_imp (fun i hi => by omega) _ j.right_bound⟩,
    by simp only [layout,List.length_append]; have := j.positive; omega⟩

theorem lookup_original (ls : List (Option Part)) (P Q : Plan) (B : MExp) (i : Nat) (hi : i<ls.length) :
    lookup (layout ls P Q B) i=lookup ls i := by
  rw [layout,lookup_prefix _ _ i (by simp only [List.length_append]; omega),lookup_prefix _ _ i hi]
theorem lookup_test (ls : List (Option Part)) (P Q : Plan) (B : MExp) (i : Nat) (hi : i<ls.length) :
    lookup (layout ls P Q B) (ls.length+i)=raw (ls[i].map (fun b => (b.1,.seq b.2 B))) := by
  rw [layout,lookup_prefix _ _ _ (by simp [copies]; omega),lookup_copy ls B i hi]
theorem lookup_tail (ls : List (Option Part)) (P Q : Plan) (B : MExp) (i : Nat) (hi : i<ls.length) :
    lookup (layout ls P Q B) (2*ls.length+i)=raw (ls[i].map (fun b => (b.1,.seq b.2 (tail ls P Q B)))) := by
  have hlen : (ls++copies ls B).length=2*ls.length := by simp [copies]; omega
  rw [layout,←hlen]
  unfold lookup
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,copies,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some]

theorem loop_eval (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool) (ls : List (Option Part))
    (P Q : Plan) (B : MExp) (hc : LeafContinuation.Consumer P)
    (hp : P.All (fun i => i<ls.length)) (hq : Q.All (fun i => i<ls.length))
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName) (T : ClockFreezing.Table)
    (hT : SoundTV g x s T) (E : List (List Char)) (p : Nat) (hpn : p≤x.length) :
    evV g x s T E (.seq (.star (.seq (render kinds n plans par false (P.exp (lookup ls))) (render kinds n plans par false B)))
      (render kinds n plans par false (Q.exp (lookup ls)))) p=
    evV g x s T E (render kinds n plans par false ((loopPlan ls.length P Q).exp (lookup (layout ls P Q B)))) p := by
  let L := fun i q => evV g x s T E (render kinds n plans par false (lookup ls i)) q
  let R := fun i q => evV g x s T E (render kinds n plans par false (lookup (layout ls P Q B) i)) q
  let a := fun q => evV g x s T E (render kinds n plans par false (P.exp (lookup ls))) q
  let b := fun q => evV g x s T E (render kinds n plans par false B) q
  let c := fun q => evV g x s T E (render kinds n plans par false (Q.exp (lookup ls))) q
  let k := fun q => evV g x s T E (render kinds n plans par false (tail ls P Q B)) q
  have hOrig : ∀ i, i<ls.length → ∀ q, R i q=L i q := by
    intro i hi q; dsimp only [R,L]; rw [lookup_original ls P Q B i hi]
  have hAppend (offset : Nat) (K : MExp)
      (hl : ∀ i, ∀ (hi : i<ls.length), lookup (layout ls P Q B) (offset+i)=raw (ls[i].map (fun b => (b.1,.seq b.2 K)))) :
      ∀ i, i∈ConsumingPlanOutputs.outputs P → i<ls.length → ∀ q,
        R (offset+i) q=sequence (L i) (fun q => evV g x s T E (render kinds n plans par false K) q) q := by
    intro i _ hi q
    dsimp only [R,L]
    rw [hl i hi]
    have hold : lookup ls i=raw ls[i] := by simp [lookup,List.getElem?_eq_getElem hi]
    rw [hold]
    exact append_eval kinds n plans par ls[i] K g x s T E q
  have ha : sem L P=a := by funext q; exact (control_eval kinds n plans par ls P g x s T E q).symm
  have hc' : sem L Q=c := by funext q; exact (control_eval kinds n plans par ls Q g x s T E q).symm
  have ht (q : Nat) := ConsumingPlanOutputs.chain_correct ls.length ls.length L R b hOrig P hc hp
    (hAppend ls.length B (lookup_test ls P Q B)) q
  have hk := ConsumingPlanOutputs.chain_correct ls.length (2*ls.length) L R k hOrig P hc hp
    (hAppend (2*ls.length) (tail ls P Q B) (lookup_tail ls P Q B)) p
  rw [ha] at ht hk
  have htf : (fun q => sem R (LeafContinuation.chain ls.length P) q)=sequence a b := by funext q; exact ht q
  have hq' := ContinuationPlan.sem_congr ls.length R L hOrig Q hq p
  rw [hc'] at hq'
  let G : MExp := .seq (.andP (.seq (render kinds n plans par false (P.exp (lookup ls))) (render kinds n plans par false B)))
    (render kinds n plans par false (P.exp (lookup ls)))
  have hg : (fun q => evV g x s T E G q)=GuardedStarFactor.eligible a b := by
    funext q; exact GuardedStarFactor.eligible_eval g x s T E _ _ q
  have hK : k=sequence (evStar (sequence b (GuardedStarFactor.eligible a b))) (sequence b c) := by
    change (fun q => evV g x s T E (.seq (.star (.seq (render kinds n plans par false B) G))
      (.seq (render kinds n plans par false B) (render kinds n plans par false (Q.exp (lookup ls))))) q)=_
    change sequence (evStar (sequence b (fun q => evV g x s T E G q))) (sequence b c)=_
    rw [hg]
  have he := GuardedStarFactor.correct_guarded x.length a b c
    (GreedyRotation.evaluator_decreasing g x s hs T hT E _ (FragmentMixedRecursive.render_firstOrder kinds n plans par false _))
    (GreedyRotation.evaluator_decreasing g x s hs T hT E _ (FragmentMixedRecursive.render_firstOrder kinds n plans par false B)) p hpn
  change sequence (evStar (sequence a b)) c p=_
  rw [he,render_plan,Plan.exp_eval]
  change _=ReplayFallbackFusion.orElse
    (match sem R (LeafContinuation.chain ls.length P) p with | some (some _) => sem R (LeafContinuation.chain (2*ls.length) P) p | other => other)
    (match (GreedyRotation.negative (fun q => sem R (LeafContinuation.chain ls.length P) q) p) with
      | some (some _) => sem R Q p | other => other)
  rw [ht p,hk,hq',hK,htf]
  unfold GuardedStarFactor.guarded
  congr 1
  change (match GreedyRotation.negative (sequence a b) p with | some (some j) => c j | other => other)=_
  unfold GreedyRotation.negative
  cases sequence a b p with
  | none => rfl
  | some result => cases result <;> rfl

theorem repeatThen_eval (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool) (f h : Form) (B : MExp)
    (hc : LeafContinuation.Consumer f.plan) (g : MGrammar) (x : List Char) (s : Strategy)
    (hs : s≠.callByName) (T : ClockFreezing.Table) (hT : SoundTV g x s T)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.seq (.star (.seq (render kinds n plans par false f.syntax) (render kinds n plans par false B)))
      (render kinds n plans par false h.syntax)) p=
    evV g x s T E (render kinds n plans par false (repeatThen f B h).syntax) p := by
  have he := loop_eval kinds n plans par (join f h).leaves (join f h).left (join f h).right B
    hc (join f h).left_bound (join f h).right_bound g x s hs T hT E p hp
  rw [join_left,join_right] at he
  exact he

def strict (f : Form) : Form :=
  ⟨f.leaves++[none,some (false,.eps)],NullableStarControl.freeze f.leaves.length (f.leaves.length+1) f.plan,
    by simpa only [List.length_append,List.length_cons,List.length_nil,Nat.add_zero]
      using NullableStarControl.bounded _ _ f.bounded,
    by simp⟩
def identity : MExp := .notP (.notP (.lit []))
def iterate (f : Form) : Form := repeatThen (strict f) identity (neg (strict f))

theorem strict_change (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool) (f : Form)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    NullableStarControl.Change p (evV g x s T E (render kinds n plans par false f.syntax) p)
      (evV g x s T E (render kinds n plans par false (strict f).syntax) p) := by
  rw [Form.syntax,Form.syntax,control_eval,control_eval]
  apply NullableStarControl.eval_change _ _ _ _ _ _ _ f.bounded p
  · intro i hi q
    rw [show (strict f).leaves=f.leaves++[none,some (false,.eps)] from rfl,lookup_prefix _ _ i hi]
  · intro q
    have hd : lookup (strict f).leaves f.leaves.length=stuck := by simp [strict,lookup,raw]
    rw [hd]
    exact MixedOriginControl.stuck_eval _ _ _ _ _ _

/-- A terminating greedy star already ends where its operand fails. -/
theorem star_negative (A : Nat → Res) : ∀ p,
    sequence (evStar A) (GreedyRotation.negative A) p=evStar A p := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    change (match evStar A p with | some (some q) => GreedyRotation.negative A q | other => other)=evStar A p
    cases ha : A p with
    | none => rw [evStar_none ha]
    | some v => cases v with
      | none => simp only [evStar_fail ha,GreedyRotation.negative,ha]
      | some q =>
        by_cases hq : q<p
        · rw [evStar_ok ha hq]; exact ih q hq
        · rw [evStar_stuck ha hq]

theorem iterate_eval (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool) (f : Form)
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.star (render kinds n plans par false f.syntax)) p=
      evV g x s T E (render kinds n plans par false (iterate f).syntax) p := by
  have hstar := NullableStarControl.star_change (fun q => evV g x s T E (render kinds n plans par false f.syntax) q)
    (fun q => evV g x s T E (render kinds n plans par false (strict f).syntax) q) p
    (fun q _ => strict_change kinds n plans par f g x s T E q)
  have he := repeatThen_eval kinds n plans par (strict f) (neg (strict f)) identity
    (NullableStarControl.consumer _ _ _) g x s hs T hT E p hp
  have hi : (fun q => evV g x s T E (render kinds n plans par false identity) q)=(fun q => some (some q)) := by
    funext q; simp [identity,render,evV,stripPrefix?]
  change sequence (evStar (sequence (fun q => evV g x s T E (render kinds n plans par false (strict f).syntax) q)
    (fun q => evV g x s T E (render kinds n plans par false identity) q)))
    (GreedyRotation.negative (fun q => evV g x s T E (render kinds n plans par false (strict f).syntax) q)) p=_ at he
  have hid := funext (NullableStarControl.sequence_identity (fun q => evV g x s T E (render kinds n plans par false (strict f).syntax) q))
  rw [hi,hid,star_negative] at he
  exact hstar.trans he

/-- Source bodies retain nested sequence, prioritized choice, negation, and general star. -/
inductive Body where
  | leaf : Part → Body
  | seq : Body → Body → Body
  | alt : Body → Body → Body
  | notP : Body → Body
  | star : Body → Body

def Body.syntax : Body → MExp
  | .leaf b => raw (some b)
  | .seq a b => .seq a.syntax b.syntax
  | .alt a b => .alt a.syntax b.syntax
  | .notP a => .notP a.syntax
  | .star a => .star a.syntax

def normalize : Body → Form
  | .leaf b => atom b
  | .seq a b => compose (normalize a) (normalize b)
  | .alt a b => choice (normalize a) (normalize b)
  | .notP a => neg (normalize a)
  | .star a => iterate (normalize a)

theorem evaluator_eq (kinds : List Bool) (n : Nat) (plans : List Plan) (par : Bool) (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char)) : ∀ e p, p≤x.length →
    evV g x s T E (render kinds n plans par false (normalize e).syntax) p=
      evV g x s T E (render kinds n plans par false e.syntax) p
  | .leaf b, p, _ => rfl
  | .seq a b, p, hp => by
    rw [normalize,compose_eval]
    simp only [Body.syntax,render]
    change (match evV g x s T E (render kinds n plans par false (normalize a).syntax) p with
      | some (some q) => evV g x s T E (render kinds n plans par false (normalize b).syntax) q | other => other)=
      (match evV g x s T E (render kinds n plans par false a.syntax) p with
        | some (some q) => evV g x s T E (render kinds n plans par false b.syntax) q | other => other)
    rw [evaluator_eq kinds n plans par g x s hs T hT E a p hp]
    cases hv : evV g x s T E (render kinds n plans par false a.syntax) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some q => exact evaluator_eq kinds n plans par g x s hs T hT E b q (Nat.le_trans
          (GreedyRotation.evaluator_decreasing g x s hs T hT E _
            (FragmentMixedRecursive.render_firstOrder kinds n plans par false a.syntax) p hp q (by assumption)) hp)
  | .alt a b, p, hp => by
    have hchoice : (choice (normalize a) (normalize b)).syntax=
        .alt (normalize a).syntax (normalize b).syntax := by
      change MExp.alt
        ((join (normalize a) (normalize b)).left.exp (lookup (join (normalize a) (normalize b)).leaves))
        ((join (normalize a) (normalize b)).right.exp (lookup (join (normalize a) (normalize b)).leaves))=_
      rw [join_left,join_right]
    rw [normalize,hchoice]
    simp only [Body.syntax,render,evV,evaluator_eq kinds n plans par g x s hs T hT E a p hp]
    cases hv : evV g x s T E (render kinds n plans par false a.syntax) p with
    | none => rfl
    | some v => cases v with
      | none => exact evaluator_eq kinds n plans par g x s hs T hT E b p hp
      | some _ => rfl
  | .notP a, p, hp => by
    change evV g x s T E (render kinds n plans par false (.notP (normalize a).syntax)) p=
      evV g x s T E (render kinds n plans par false (.notP a.syntax)) p
    simp only [render,evV]
    rw [evaluator_eq kinds n plans par g x s hs T hT E a p hp]
  | .star a, p, hp => by
    rw [normalize,←iterate_eval kinds n plans par (normalize a) g x s hs T hT E p hp]
    simp only [Body.syntax,render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_eq kinds n plans par g x s hs T hT E a q (by omega))

end Shallot.MacroPeg.CBV.FragmentMixedForm
