import MacroPeg.CBV.StarThenCompiler

/-! Compositional normal forms for source body syntax. The leaf array is
computed from the tree, rather than supplied by a replacement-source oracle. -/
namespace Shallot.MacroPeg.CBV.BodyNormalForm
open OriginControlNormalization (Leaf render expand)
open ReplayControlFusion (Plan)
open LeafContinuation (lookup raw appendBody)
open ContinuationFamily (shift)
open ContinuationPlan (sem sequence bind)
open RegularCaptureProduct (Node)
abbrev Arg := RecursiveArgumentCompiler.Expr

structure Form where
  leaves : List Leaf
  plan : Plan
  bounded : plan.All (fun i => i<leaves.length)
  positive : 0<leaves.length

def Form.syntax (f : Form) : Arg := StarThenPlan.control f.leaves f.plan

def atom (r : Leaf) : Form := ⟨[r],.leaf 0,by simp [Plan.All],by simp⟩
def neg (f : Form) : Form := ⟨f.leaves,.notP f.plan,f.bounded,f.positive⟩

structure Pair where
  leaves : List Leaf
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

def compose (f g : Form) : Form :=
  let j := join f g
  let C := StarThenPlan.control j.leaves j.right
  ⟨j.leaves++StarThenPlan.copies j.leaves j.left C,bind j.leaves.length j.left j.right,
    ConsumingPlanOutputs.bind_bound _ _ _ (by simp [StarThenPlan.copies_length])
      (by simp [StarThenPlan.copies_length]) _
      (Plan.all_imp (fun i hi => by simp only [List.length_append,StarThenPlan.copies_length]; omega) _ j.right_bound)
      _ j.left_bound,
    by simp only [List.length_append,StarThenPlan.copies_length]; have := j.positive; omega⟩

def repeatThen (f : Form) (B : Arg) (g : Form) : Form :=
  let j := join f g
  let n := j.leaves.length
  ⟨StarThenPlan.layout j.leaves j.left j.right B,StarThenPlan.plan j.leaves j.left j.right,
    by
      have hlen : (StarThenPlan.layout j.leaves j.left j.right B).length=3*n := by
        simp only [StarThenPlan.layout,List.length_append,StarThenPlan.copies_length]; omega
      rw [hlen]
      have hp := j.positive
      have hQ := Plan.all_imp (fun i (hi : i<n) => show i<3*n by omega) _ j.right_bound
      have hzero : (Plan.leaf 0).All (fun i => i<3*n) := by change 0<3*n; omega
      have htest := ConsumingPlanOutputs.bind_bound n n (3*n) (by omega) (by omega) (.leaf 0) hzero _ j.left_bound
      have htail := ConsumingPlanOutputs.bind_bound n (2*n) (3*n) (by omega) (by omega) (.leaf 0) hzero _ j.left_bound
      exact ⟨⟨htest,htail⟩,htest,hQ⟩,
    by simp only [StarThenPlan.layout,List.length_append,StarThenPlan.copies_length]; have := j.positive; omega⟩

theorem expand_congr (L R : Nat → Arg) : ∀ P, P.All (fun i => L i=R i) → expand L P=expand R P
  | .leaf _, h => h
  | .alt a b, h | .guard a b, h => by simp only [expand,expand_congr L R a h.1,expand_congr L R b h.2]
  | .notP a, h => by simp only [expand,expand_congr L R a h]

theorem expand_shift (L : Nat → Arg) (offset : Nat) :
    ∀ P, expand L (shift offset P)=expand (fun i => L (offset+i)) P
  | .leaf _ => rfl
  | .alt a b | .guard a b => by simp only [shift,expand,expand_shift L offset a,expand_shift L offset b]
  | .notP a => by simp only [shift,expand,expand_shift L offset a]

theorem join_left (f g : Form) : StarThenPlan.control (join f g).leaves (join f g).left=f.syntax := by
  apply expand_congr
  exact Plan.all_imp (fun i hi => StarThenPlan.lookup_prefix _ _ i hi) _ f.bounded

theorem join_right (f g : Form) : StarThenPlan.control (join f g).leaves (join f g).right=g.syntax := by
  change expand _ (shift _ g.plan)=_
  rw [expand_shift]
  apply expand_congr
  apply Plan.all_imp _ _ g.bounded
  intro i hi
  simp [lookup,join,List.getElem?_append_right (by omega : f.leaves.length≤f.leaves.length+i)]

theorem atom_syntax (r : Leaf) : (atom r).syntax=raw r := rfl

theorem choice_syntax (f g : Form) : (choice f g).syntax=.alt f.syntax g.syntax := by
  change RecursiveArgumentCompiler.Expr.alt (StarThenPlan.control (join f g).leaves (join f g).left)
    (StarThenPlan.control (join f g).leaves (join f g).right)=_
  rw [join_left,join_right]

theorem neg_syntax (f : Form) : (neg f).syntax=.notP f.syntax := rfl

/-- Seq of arbitrary finite control plans, including zero-consuming negative
outputs, with selective continuation copies. -/
theorem compose_eval (nodes : List Node) (ambient : List Leaf) (ps : List Plan) (f h : Form)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (render nodes ambient ps (compose f h).syntax) p=
    evV g x s T E (.seq (render nodes ambient ps f.syntax) (render nodes ambient ps h.syntax)) p := by
  let j := join f h
  let C := StarThenPlan.control j.leaves j.right
  let L := fun i q => evV g x s T E (render nodes ambient ps (lookup j.leaves i)) q
  let R := fun i q => evV g x s T E
    (render nodes ambient ps (lookup (j.leaves++StarThenPlan.copies j.leaves j.left C) i)) q
  have hOrig : ∀ i, i<j.leaves.length → ∀ q, R i q=L i q := by
    intro i hi q
    dsimp only [R,L]
    rw [StarThenPlan.lookup_prefix _ _ i hi]
  have ht : ∀ i, i∈ConsumingPlanOutputs.outputs j.left → i<j.leaves.length → ∀ q,
      R (j.leaves.length+i) q=sequence (L i) (sem L j.right) q := by
    intro i ho hi q
    dsimp only [R,L]
    rw [StarThenPlan.lookup_mapped _ _ _ _ i ho hi]
    have hlookup : lookup j.leaves i=raw j.leaves[i] := by simp [lookup,List.getElem?_eq_getElem hi]
    rw [hlookup,LeafContinuation.append_eval]
    apply congrArg (fun K => sequence (fun q => evV g x s T E (render nodes ambient ps (raw j.leaves[i])) q) K q)
    funext q
    exact StarThenPlan.control_eval nodes ambient ps j.leaves j.right g x s T E q
  have he := ConsumingPlanOutputs.bind_correct j.leaves.length j.leaves.length L R hOrig
    j.right j.right_bound j.left j.left_bound ht p
  change evV g x s T E (render nodes ambient ps
    (StarThenPlan.control (j.leaves++StarThenPlan.copies j.leaves j.left C) (bind j.leaves.length j.left j.right))) p=_
  rw [StarThenPlan.control_eval]
  change sem R (bind j.leaves.length j.left j.right) p=_
  rw [he]
  have hl := StarThenPlan.control_eval nodes ambient ps j.leaves j.left g x s T E
  have hr := StarThenPlan.control_eval nodes ambient ps j.leaves j.right g x s T E
  have ha : sem L j.left=(fun q => evV g x s T E (render nodes ambient ps f.syntax) q) := by
    funext q
    rw [←hl q,show StarThenPlan.control j.leaves j.left=f.syntax from join_left f h]
  have hb : sem L j.right=(fun q => evV g x s T E (render nodes ambient ps h.syntax) q) := by
    funext q
    rw [←hr q,show StarThenPlan.control j.leaves j.right=h.syntax from join_right f h]
  rw [ha,hb]
  rfl

theorem repeatThen_eval (nodes : List Node) (ambient : List Leaf) (ps : List Plan) (f h : Form)
    (B : Arg) (hc : LeafContinuation.Consumer f.plan) (g : MGrammar) (x : List Char)
    (s : Strategy) (hs : s≠.callByName) (T : ClockFreezing.Table) (hT : SoundTV g x s T)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.seq (.star (.seq (render nodes ambient ps f.syntax) (render nodes ambient ps B)))
      (render nodes ambient ps h.syntax)) p=
    evV g x s T E (render nodes ambient ps (repeatThen f B h).syntax) p := by
  have he := StarThenPlan.body_eq nodes ambient ps (join f h).leaves (join f h).left (join f h).right B
    hc (join f h).left_bound (join f h).right_bound g x s hs T hT E p hp
  rw [join_left,join_right] at he
  change _=evV g x s T E (render nodes ambient ps
    (StarThenPlan.control (StarThenPlan.layout (join f h).leaves (join f h).left (join f h).right B)
      (StarThenPlan.plan (join f h).leaves (join f h).left (join f h).right))) p
  rw [StarThenPlan.control,LeadingReplayStar.render_expand]
  exact he

end Shallot.MacroPeg.CBV.BodyNormalForm
