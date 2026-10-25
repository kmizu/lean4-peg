import MacroPeg.CBV.SubstringCaptureView
import MacroPeg.CBV.ReplayFusion
import MacroPeg.CBV.ControlFilter

namespace Shallot.MacroPeg.CBV.RetainedViewFusionSyntax
open RegularCaptureProduct (run choice)
open FiniteSuffixReplay (palette views)
inductive Expr where
  | eps | any | chr (c : Char) | range (a b : Char) | lit (w : List Char)
  | retained | replay (i : Nat)
  | call (i : Nat) (args : List Expr)
  | seq (a b : Expr) | alt (a b : Expr) | notP (a : Expr) | star (a : Expr)
  deriving Repr
structure Rule where
  arity : Nat
  body : Expr
  deriving Repr
abbrev Term := Expr
abbrev Spec := Rule
abbrev View := List (Option (List Char))
abbrev Mode := Option (List Char × Nat × Nat)

structure Key where
  user : Nat
  value : View
  mode : Mode
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def modes (R : List (List Char)) : List Mode := none::(palette R).flatMap (fun u =>
  (List.range (u.length+2)).flatMap (fun q => (List.range (u.length+2)).map (fun r => some (u,q,r))))
def keys (R : List (List Char)) (rs : List Spec) : List Key := rs.zipIdx.flatMap (fun (r,i) =>
  (words (FiniteSuffixRecursiveSyntax.states R) r.arity).flatMap (fun V => (modes R).map (fun m => ⟨i,V,m⟩)))
def address (R : List (List Char)) (rs : List Spec) (i : Nat) (V : View) (m : Mode) :=
  (keys R rs).idxOf ⟨i,V,m⟩

/-- Every actual is probed before a selected continuation can run.
Branches commit to its exact word or Other even if that continuation fails. -/
def choose (ws : List (List Char)) (F : List Char → Nat → Nat → MExp)
    (K : Option (List Char) → MExp) : MExp :=
  match ws with
  | [] => K none
  | u::ws => RootObservation.branch (.andP (F u 0 u.length)) (K (some u)) (choose ws F K)
def select (R : List (List Char)) (a : MExp) (F : List Char → Nat → Nat → MExp)
    (K : Option (List Char) → MExp) : MExp := .seq (.andP a) (choose (palette R) F K)

abbrev atom := FiniteSuffixObservedSyntax.atom
abbrev character := FiniteSuffixObservedSyntax.character

def main (E : List (List Char)) := E[0]?.getD []
def payload (E : List (List Char)) := [main E]
def state (u : List Char) (q : Nat) (V : View) :=
  if V=[] then q else SubstringCaptureView.advance u q V[0]?.join
def advance (V : View) : Mode → Mode
  | none => none
  | some (u,q,r) => some (u,state u q V,r)
def retained (V : View) : MExp := if V=[] then MExp.failAlways else .param 0

def retainedFilter (V : View) (m : Mode) : MExp := match m with
  | none => retained V
  | some (u,q,r) => .seq (retained V) (if state u q V=r then .eps else MExp.failAlways)

mutual
  def emit (R : List (List Char)) (rs : List Spec) (V : View) (m : Mode) : Term → MExp
    | .eps => atom m .eps []
    | .any => character m .any
    | .chr c => character m (.chr c)
    | .range a b => character m (.range a b)
    | .lit w => atom m (.lit w) w
    | .retained => retainedFilter V m
    | .replay i => atom m (.seq (FiniteSuffixReplay.guard R) (FiniteSuffixReplay.literal V i)) (V[i]?.join.getD [])
    | .call i args => match rs[i]? with
      | none => MExp.failAlways
      | some r => if r.arity=args.length then gather R rs V args (fun W => .call (address R rs i W m) [first R rs V args]) else MExp.failAlways
    | .seq a b => match m with
      | none => .seq (emit R rs V none a) (emit R rs V none b)
      | some (u,q,r) => choice ((List.range (u.length+2)).map (fun t => .seq (emit R rs V (some (u,q,t)) a) (emit R rs V (some (u,t,r)) b)))
    | .alt a b => match m with
      | none => .alt (emit R rs V none a) (emit R rs V none b)
      | some (u,q,r) => RootObservation.branch (.andP (emit R rs V none a)) (emit R rs V (some (u,q,r)) a) (emit R rs V (some (u,q,r)) b)
    | .notP a => atom m (.notP (emit R rs V none a)) []
    | .star a => match m with
      | none => .star (emit R rs V none a)
      | some (u,q,r) => GeneralStarFilter.filter (u.length+2) (emit R rs V none a) (fun q r => emit R rs V (some (u,q,r)) a) q r
  def gather (R : List (List Char)) (rs : List Spec) (V : View) : List Term → (View → MExp) → MExp
    | [],K => K []
    | a::args,K => select R (emit R rs V none a) (fun u q r => emit R rs V (some (u,q,r)) a)
        (fun v => gather R rs V args (fun W => K (v::W)))
  def first (R : List (List Char)) (rs : List Spec) (V : View) : List Term → MExp
    | [] => .eps
    | a::_ => emit R rs V none a
end

mutual
  def original (R : List (List Char)) : Term → MExp
    | .eps => .eps
    | .any => .any
    | .chr c => .chr c
    | .range a b => .range a b
    | .lit w => .lit w
    | .retained => .param 0
    | .replay i => .seq (FiniteSuffixReplay.guard R) (.param i)
    | .call i args => .call i (originalArgs R args)
    | .seq a b => .seq (original R a) (original R b)
    | .alt a b => .alt (original R a) (original R b)
    | .notP a => .notP (original R a)
    | .star a => .star (original R a)
  def originalArgs (R : List (List Char)) : List Term → List MExp
    | [] => []
    | a::args => original R a::originalArgs R args
end

def head (r : Spec) : MExp := if r.arity=0 then .eps else .param 0
def source (R : List (List Char)) (rs : List Spec) : MGrammar :=
  ⟨rs.map (fun r => ⟨r.arity,.seq (head r) (original R r.body)⟩)⟩
def tails (R : List (List Char)) (rs : List Spec) : List MExp := (keys R rs).map (fun key =>
  emit R rs key.value (advance key.value key.mode) ((rs[key.user]?).map Rule.body |>.getD .eps))
def intermediate (R : List (List Char)) (rs : List Spec) := ReplayFusion.parGrammar (tails R rs)
def target (R : List (List Char)) (rs : List Spec) := ReplayFusion.seqGrammar (tails R rs)

end Shallot.MacroPeg.CBV.RetainedViewFusionSyntax
