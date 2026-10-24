import MacroPeg.CBV.FragmentOriginRecursive
import MacroPeg.CBV.ContinuationFamily

namespace Shallot.MacroPeg.CBV.FragmentBodyForm
open ReplayControlFusion (Plan)
open ContinuationFamily (shift)
open ContinuationPlan (sem sequence bind)
open RuntimeShiftFilter (scanner)
open FragmentOriginRecursive (render)

def raw (b : MExp) : MExp := .seq scanner (.seq (.param 0) b)
def lookup (ls : List MExp) (i : Nat) : MExp :=
  match ls[i]? with | some b => raw b | none => MExp.failAlways

def copies (ls : List MExp) (K : MExp) : List MExp := ls.map (fun b => .seq b K)

structure Form where
  leaves : List MExp
  plan : Plan
  bounded : plan.All (fun i => i<leaves.length)
  positive : 0<leaves.length

def Form.syntax (f : Form) : MExp := f.plan.exp (lookup f.leaves)
def atom (b : MExp) : Form := ⟨[b],.leaf 0,by simp [Plan.All],by simp⟩
def neg (f : Form) : Form := ⟨f.leaves,.notP f.plan,f.bounded,f.positive⟩

structure Pair where
  leaves : List MExp
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

theorem lookup_prefix (ls rs : List MExp) (i : Nat) (hi : i<ls.length) :
    lookup (ls++rs) i=lookup ls i := by simp only [lookup,List.getElem?_append_left hi]

theorem lookup_copy (ls : List MExp) (K : MExp) (i : Nat) (hi : i<ls.length) :
    lookup (ls++copies ls K) (ls.length+i)=raw (.seq ls[i] K) := by
  simp [lookup,copies,List.getElem?_append_right,List.getElem?_map,List.getElem?_eq_getElem hi]

theorem render_scanner (plans : List Plan) (par : Bool) : render plans par false scanner=scanner := by
  simp [scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,MExp.failAlways,render]

theorem render_raw (plans : List Plan) (par : Bool) (b : MExp) :
    render plans par false (raw b)=.seq scanner (.seq (.param 0) (render plans par false b)) := by
  simp only [raw,render,render_scanner]

theorem render_plan (plans : List Plan) (par : Bool) (L : Nat → MExp) :
    ∀ (P : Plan), render plans par false (P.exp L)=P.exp (fun i => render plans par false (L i))
  | .leaf _ => rfl
  | .alt a b | .guard a b => by simp only [Plan.exp,MExp.andP,render,render_plan plans par L a,render_plan plans par L b]
  | .notP a => by simp only [Plan.exp,render,render_plan plans par L a]

theorem append_eval (plans : List Plan) (par : Bool) (b K : MExp)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (p : Nat) :
    evV g x s T E (render plans par false (raw (.seq b K))) p=
      sequence (fun q => evV g x s T E (render plans par false (raw b)) q)
        (fun q => evV g x s T E (render plans par false K) q) p := by
  rw [render_raw,render_raw]
  simp only [render]
  unfold sequence
  change (match evV g x s T E scanner p with
    | some (some q) => evV g x s T E (.seq (.param 0) (.seq (render plans par false b) (render plans par false K))) q
    | other => other)=
    (match (match evV g x s T E scanner p with
      | some (some q) => evV g x s T E (.seq (.param 0) (render plans par false b)) q
      | other => other) with
      | some (some q) => evV g x s T E (render plans par false K) q | other => other)
  cases evV g x s T E scanner p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some q =>
      change (match evV g x s T E (.param 0) q with
        | some (some j) => evV g x s T E (.seq (render plans par false b) (render plans par false K)) j
        | other => other)=
        (match (match evV g x s T E (.param 0) q with
          | some (some j) => evV g x s T E (render plans par false b) j | other => other) with
          | some (some j) => evV g x s T E (render plans par false K) j | other => other)
      cases evV g x s T E (.param 0) q with
      | none => rfl
      | some v => cases v <;> rfl

theorem control_eval (plans : List Plan) (par : Bool) (ls : List MExp) (P : Plan)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (render plans par false (P.exp (lookup ls))) p=
      sem (fun i q => evV g x s T E (render plans par false (lookup ls i)) q) P p := by
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

theorem compose_eval (plans : List Plan) (par : Bool) (f h : Form)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (render plans par false (compose f h).syntax) p=
      evV g x s T E (.seq (render plans par false f.syntax) (render plans par false h.syntax)) p := by
  let j := join f h
  let C := j.right.exp (lookup j.leaves)
  let L := fun i q => evV g x s T E (render plans par false (lookup j.leaves i)) q
  let R := fun i q => evV g x s T E (render plans par false (lookup (j.leaves++copies j.leaves C) i)) q
  have hOrig : ∀ i, i<j.leaves.length → ∀ q, R i q=L i q := by
    intro i hi q; dsimp only [R,L]; rw [lookup_prefix _ _ i hi]
  have ht : ∀ i, i<j.leaves.length → ∀ q, R (j.leaves.length+i) q=sequence (L i) (sem L j.right) q := by
    intro i hi q
    dsimp only [R,L]
    rw [lookup_copy _ _ i hi]
    have hl : lookup j.leaves i=raw j.leaves[i] := by simp [lookup,List.getElem?_eq_getElem hi]
    rw [hl,append_eval]
    apply congrArg (fun K => sequence (fun q => evV g x s T E (render plans par false (raw j.leaves[i])) q) K q)
    funext q
    exact control_eval plans par j.leaves j.right g x s T E q
  have he := ContinuationPlan.bind_correct j.leaves.length j.leaves.length L R hOrig j.right j.right_bound ht j.left j.left_bound p
  change evV g x s T E (render plans par false ((bind j.leaves.length j.left j.right).exp
    (lookup (j.leaves++copies j.leaves C)))) p=_
  rw [control_eval]
  change sem R (bind j.leaves.length j.left j.right) p=_
  rw [he]
  have ha : sem L j.left=(fun q => evV g x s T E (render plans par false f.syntax) q) := by
    funext q; rw [←control_eval plans par j.leaves j.left g x s T E q,join_left]
  have hb : sem L j.right=(fun q => evV g x s T E (render plans par false h.syntax) q) := by
    funext q; rw [←control_eval plans par j.leaves j.right g x s T E q,join_right]
  rw [ha,hb]; rfl

/-- Finite source bodies retain their original nested consuming syntax. -/
inductive Body where
  | leaf : MExp → Body
  | seq : Body → Body → Body
  | alt : Body → Body → Body
  | notP : Body → Body

def Body.syntax : Body → MExp
  | .leaf b => raw b
  | .seq a b => .seq a.syntax b.syntax
  | .alt a b => .alt a.syntax b.syntax
  | .notP a => .notP a.syntax

def normalize : Body → Form
  | .leaf b => atom b
  | .seq a b => compose (normalize a) (normalize b)
  | .alt a b => choice (normalize a) (normalize b)
  | .notP a => neg (normalize a)

theorem evaluator_eq (plans : List Plan) (par : Bool) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) : ∀ e p,
    evV g x s T E (render plans par false (normalize e).syntax) p=
      evV g x s T E (render plans par false e.syntax) p
  | .leaf b, p => rfl
  | .seq a b, p => by
    rw [normalize,compose_eval]
    simp only [Body.syntax,render]
    change (match evV g x s T E (render plans par false (normalize a).syntax) p with
      | some (some q) => evV g x s T E (render plans par false (normalize b).syntax) q | other => other)=
      (match evV g x s T E (render plans par false a.syntax) p with
        | some (some q) => evV g x s T E (render plans par false b.syntax) q | other => other)
    rw [evaluator_eq plans par g x s T E a p]
    cases evV g x s T E (render plans par false a.syntax) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some q => exact evaluator_eq plans par g x s T E b q
  | .alt a b, p => by
    have hchoice : (choice (normalize a) (normalize b)).syntax=
        .alt (normalize a).syntax (normalize b).syntax := by
      change MExp.alt
        ((join (normalize a) (normalize b)).left.exp (lookup (join (normalize a) (normalize b)).leaves))
        ((join (normalize a) (normalize b)).right.exp (lookup (join (normalize a) (normalize b)).leaves))=_
      rw [join_left,join_right]
    rw [normalize,hchoice]
    simp only [Body.syntax,render,evV,evaluator_eq plans par g x s T E a p]
    cases evV g x s T E (render plans par false a.syntax) p with
    | none => rfl
    | some v => cases v with
      | none => exact evaluator_eq plans par g x s T E b p
      | some _ => rfl
  | .notP a, p => by
    change evV g x s T E (render plans par false (.notP (normalize a).syntax)) p=
      evV g x s T E (render plans par false (.notP a.syntax)) p
    simp only [render,evV]
    rw [evaluator_eq plans par g x s T E a p]

end Shallot.MacroPeg.CBV.FragmentBodyForm
