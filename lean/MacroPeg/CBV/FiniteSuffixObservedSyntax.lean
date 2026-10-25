import MacroPeg.CBV.FiniteSuffixDependentView
import MacroPeg.CBV.ControlFilter

namespace Shallot.MacroPeg.CBV.FiniteSuffixObservedSyntax
open RegularCaptureProduct (run choice)
open FiniteSuffixReplay (palette views)
abbrev Term := FiniteSuffixDependentView.Expr
abbrev Spec := FiniteSuffixDependentView.Rule
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

def atom (m : Mode) (e : MExp) (w : List Char) : MExp := match m with
  | none => e
  | some (u,q,r) => .seq e (if run (ExactWordCaptureMachine.machine u) q w=r then .eps else MExp.failAlways)

def charFilter (u : List Char) (q r : Nat) : MExp :=
  if q<u.length then RootObservation.branch (.andP (.chr (u[q]?.getD '\x00')))
    (if q+1=r then .any else MExp.failAlways)
    (if u.length+1=r then .any else MExp.failAlways)
  else if u.length+1=r then .any else MExp.failAlways

def character (m : Mode) (e : MExp) : MExp := match m with
  | none => e
  | some (u,q,r) => .seq (.andP e) (charFilter u q r)

mutual
  def emit (R : List (List Char)) (rs : List Spec) (V : View) (m : Mode) : Term → MExp
    | .eps => atom m .eps []
    | .any => character m .any
    | .chr c => character m (.chr c)
    | .range a b => character m (.range a b)
    | .lit w => atom m (.lit w) w
    | .replay i => atom m (.seq (FiniteSuffixReplay.guard R) (FiniteSuffixReplay.literal V i)) (V[i]?.join.getD [])
    | .call i args => match rs[i]? with
      | none => MExp.failAlways
      | some r => if r.arity=args.length then gather R rs V args (fun W => .call (address R rs i W m) []) else MExp.failAlways
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
end

abbrev source := FiniteSuffixDependentView.source
abbrev original (R : List (List Char)) := FiniteSuffixDependentView.render R none

def targetRule (R : List (List Char)) (rs : List Spec) (key : Key) : MRule :=
  ⟨0,emit R rs key.value key.mode ((rs[key.user]?).map FiniteSuffixDependentView.Rule.body |>.getD .eps)⟩
def target (R : List (List Char)) (rs : List Spec) : MGrammar := ⟨(keys R rs).map (targetRule R rs)⟩

end Shallot.MacroPeg.CBV.FiniteSuffixObservedSyntax
