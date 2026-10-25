import MacroPeg.CBV.SequentialResultSyntax

/-! Candidate fixed-grammar totalization of arbitrary first-order Seq syntax.
This module proves syntactic properties only. General semantic correctness
and termination of the generated grammar remain obligations: the already
verified position evaluator does not discharge them automatically. -/
namespace Shallot.MacroPeg.CBV.SequentialTotalSyntax

inductive Mode where
  | success | zero | positive | failure
  deriving DecidableEq

def Mode.code : Mode → Nat
  | .success => 0 | .zero => 1 | .positive => 2 | .failure => 3

structure Forms where
  zero : MExp
  positive : MExp
  failure : MExp

def Forms.success (f : Forms) : MExp := .alt f.positive f.zero
def Forms.get (f : Forms) : Mode → MExp
  | .success => f.success | .zero => f.zero | .positive => f.positive | .failure => f.failure

def blockSize (g : MGrammar) : Nat := 4*(g.rules.length+2)
def ordinaryIndex (g : MGrammar) (i : Nat) (m : Mode) : Nat := blockSize g*i+m.code
def emptyIndex (g : MGrammar) (i fuel : Nat) (m : Mode) : Nat :=
  blockSize g*i+4*(fuel+1)+m.code

def choices : List MExp → MExp
  | [] => MExp.failAlways
  | a::as => .alt a (choices as)

/-- Entries contain both the current local stage and the full stage used
after the first positive argument. Every route retains each separate capture. -/
def positiveRoutes : List (Forms × Forms) → List (List MExp)
  | [] => []
  | (a,_)::as => (a.positive::as.map (fun b => b.2.success)) ::
      (positiveRoutes as).map (fun bs => a.zero::bs)

def zeroArgs (as : List (Forms × Forms)) : MExp :=
  as.foldr (fun a b => .seq a.1.zero b) .eps

def failureArgs : List (Forms × Forms) → MExp
  | [] => MExp.failAlways
  | (a,_)::as => .alt a.failure (.alt
      (.seq a.zero (failureArgs as))
      (.andP (.seq a.positive (failureArgs (as.map (fun b => (b.2,b.2)))))))
termination_by as => as.length

def invalid : Forms := ⟨MExp.failAlways,MExp.failAlways,.eps⟩
def emptyCall (g : MGrammar) (i fuel : Nat) (m : Mode) : MExp :=
  .call (emptyIndex g i fuel m) []

def callForms (g : MGrammar) (fuel i : Nat) (as : List (Forms × Forms)) : Forms :=
  match ruleAtM g.rules i with
  | none => invalid
  | some r => if r.arity=as.length then
      let routes := positiveRoutes as
      let z := zeroArgs as
      ⟨.seq z (emptyCall g i fuel .zero),
       .alt (choices (routes.map (fun args => .call (ordinaryIndex g i .success) args)))
         (.seq z (emptyCall g i fuel .positive)),
       .alt (failureArgs as) (.alt
         (choices (routes.map (fun args => .andP (.call (ordinaryIndex g i .failure) args))))
         (.seq z (emptyCall g i fuel .failure)))⟩
    else invalid

def seqForms (a b bN : Forms) : Forms :=
  ⟨.seq a.zero b.zero,
   .alt (.seq a.positive bN.success) (.seq a.zero b.positive),
   .alt a.failure (.alt (.andP (.seq a.positive bN.failure)) (.seq a.zero b.failure))⟩
def altForms (a b : Forms) : Forms :=
  ⟨.alt a.zero (.seq a.failure b.zero),
   .alt a.positive (.seq a.failure b.positive),.seq a.failure b.failure⟩
def notForms (a : Forms) : Forms := ⟨a.failure,MExp.failAlways,.andP a.success⟩
def starForms (a aN : Forms) : Forms :=
  ⟨a.failure,.seq a.positive (.seq (.star aN.positive) aN.failure),MExp.failAlways⟩

mutual
  def compile (g : MGrammar) (fuel : Nat) : MExp → Forms
    | .eps => ⟨.eps,MExp.failAlways,MExp.failAlways⟩
    | .any => ⟨MExp.failAlways,.any,.notP .any⟩
    | .chr c => ⟨MExp.failAlways,.chr c,.notP (.chr c)⟩
    | .range l h => ⟨MExp.failAlways,.range l h,.notP (.range l h)⟩
    | .lit w => if w=[] then ⟨.eps,MExp.failAlways,MExp.failAlways⟩
        else ⟨MExp.failAlways,.lit w,.notP (.lit w)⟩
    | .param i =>
      let z := SequentialResultSyntax.emptyParameter i
      ⟨z,.seq (.notP z) (.param i),.notP (.param i)⟩
    | .call i args => callForms g fuel i (compileArgs g fuel args)
    | .seq a b => seqForms (compile g fuel a) (compile g fuel b) (compile g g.rules.length b)
    | .alt a b => altForms (compile g fuel a) (compile g fuel b)
    | .notP a => notForms (compile g fuel a)
    | .star a => starForms (compile g fuel a) (compile g g.rules.length a)
    | _ => invalid
  def compileArgs (g : MGrammar) (fuel : Nat) : List MExp → List (Forms × Forms)
    | [] => []
    | a::as => (compile g fuel a,compile g g.rules.length a)::compileArgs g fuel as
end

def modes : List Mode := [.success,.zero,.positive,.failure]
def ordinaryRules (g : MGrammar) (r : MRule) : List MRule :=
  modes.map (fun m => ⟨r.arity,(compile g g.rules.length r.body).get m⟩)
def emptyRules (g : MGrammar) (r : MRule) (fuel : Nat) : List MRule :=
  modes.map (fun m => ⟨0,match fuel with
    | 0 => MExp.failAlways
    | j+1 => (compile g j (SequentialResultSyntax.emptyBody r)).get m⟩)
def ruleBlock (g : MGrammar) (r : MRule) : List MRule :=
  ordinaryRules g r ++ (List.range (g.rules.length+1)).flatMap (emptyRules g r)
def target (g : MGrammar) : MGrammar := ⟨g.rules.flatMap (ruleBlock g)⟩
def start (g : MGrammar) (e : MExp) : MExp := (compile g g.rules.length e).success

theorem compileArgs_length (g : MGrammar) (fuel : Nat) (as : List MExp) :
    (compileArgs g fuel as).length=as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [compileArgs,List.length_cons,ih]

theorem positiveRoutes_count (as : List (Forms × Forms)) :
    (positiveRoutes as).length=as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [positiveRoutes,ih]

theorem positiveRoutes_arity (as : List (Forms × Forms)) (bs : List MExp)
    (hb : bs∈positiveRoutes as) : bs.length=as.length := by
  induction as generalizing bs with
  | nil => simp [positiveRoutes] at hb
  | cons a as ih =>
    simp only [positiveRoutes,List.mem_cons,List.mem_map] at hb
    rcases hb with rfl|⟨cs,hcs,rfl⟩
    · simp
    · simp only [List.length_cons,ih _ hcs]

theorem emptyRules_nullary (g : MGrammar) (r : MRule) (fuel : Nat) :
    (emptyRules g r fuel).map MRule.arity=[0,0,0,0] := by rfl

theorem block_length (g : MGrammar) (r : MRule) :
    (ruleBlock g r).length=blockSize g := by
  simp [ruleBlock,ordinaryRules,emptyRules,modes,List.length_flatMap,blockSize,
    List.map_const',List.sum_replicate_nat]
  omega

theorem rule_count (g : MGrammar) : (target g).rules.length=g.rules.length*blockSize g := by
  simp only [target,List.length_flatMap]
  simp only [block_length,List.map_const',List.sum_replicate_nat]

end Shallot.MacroPeg.CBV.SequentialTotalSyntax
