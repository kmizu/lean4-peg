import MacroPeg.CBV.FiniteSuffixCallCompiler

/-! Mutually recursive retained-value users over independent recursive PEG
arguments. Finite suffix replay views become fixed nullary user variants. -/
namespace Shallot.MacroPeg.CBV.FiniteSuffixRecursiveSyntax
open RegularCaptureProduct (Node)
open FiniteSuffixReplay (palette views)

inductive Expr where
  | eps | any | chr (c : Char) | range (a b : Char) | lit (w : List Char)
  | helper (i : Nat) | replay (i : Nat)
  | user (i : Nat) (args : List Nat)
  | seq (a b : Expr) | alt (a b : Expr) | notP (a : Expr) | star (a : Expr)
  deriving Repr

structure Rule where
  arity : Nat
  body : Expr
  deriving Repr

abbrev View := List (Option (List Char))
structure Key where
  user : Nat
  value : View
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def states (R : List (List Char)) := none::(palette R).map some

theorem observe_mem (R : List (List Char)) (w : List Char) : FiniteSuffixReplay.observe R w∈states R := by
  unfold FiniteSuffixReplay.observe
  split
  · simp_all [states]
  · simp [states]

theorem views_mem (R : List (List Char)) (E : List (List Char)) : views R E∈words (states R) E.length := by
  apply (mem_words _ _ _).mpr
  refine ⟨by simp [views],?_⟩
  intro v hv
  obtain ⟨w,_,rfl⟩ := List.mem_map.mp hv
  exact observe_mem R w

def keys (R : List (List Char)) (rs : List Rule) : List Key := rs.zipIdx.flatMap (fun (r,i) =>
  (words (states R) r.arity).map (fun V => ⟨i,V⟩))
abbrev base (nodes : List Node) (R : List (List Char)) := FiniteSuffixCallCompiler.target nodes R
def address (nodes : List Node) (R : List (List Char)) (rs : List Rule) (i : Nat) (V : View) :=
  (base nodes R).rules.length+(keys R rs).idxOf ⟨i,V⟩

theorem key_mem (R : List (List Char)) (rs : List Rule) (i : Nat) (r : Rule) (hr : rs[i]?=some r)
    (E : List (List Char)) (he : E.length=r.arity) : (⟨i,views R E⟩ : Key)∈keys R rs := by
  apply List.mem_flatMap.mpr
  refine ⟨(r,i),List.mem_of_getElem? (show rs.zipIdx[i]?=some (r,i) from by simp [List.getElem?_zipIdx,hr]),?_⟩
  apply List.mem_map.mpr
  exact ⟨views R E,by simpa only [he] using views_mem R E,rfl⟩

def permitted (n : Nat) (rs : List Rule) (i : Nat) (args : List Nat) : Bool :=
  match rs[i]? with
  | none => false
  | some r => decide (r.arity=args.length) && args.all (fun j => decide (j<n))

theorem permitted_checked (n : Nat) (rs : List Rule) (i : Nat) (args : List Nat) (hp : permitted n rs i args=true) :
    ∃ r, rs[i]?=some r ∧ r.arity=args.length ∧ ∀ j∈args, j<n := by
  cases hr : rs[i]? with
  | none => simp [permitted,hr] at hp
  | some r =>
    have hh := Bool.and_eq_true_iff.mp (show (decide (r.arity=args.length) && args.all (fun j => decide (j<n)))=true from by simpa [permitted,hr] using hp)
    exact ⟨r,rfl,of_decide_eq_true hh.1,fun j hj => of_decide_eq_true (List.all_eq_true.mp hh.2 j hj)⟩

def render (nodes : List Node) (R : List (List Char)) (rs : List Rule) (V : Option View) : Expr → MExp
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w
  | .helper i => if i<nodes.length then .call i [] else MExp.failAlways
  | .replay i => .seq (FiniteSuffixReplay.guard R) (match V with
      | none => .param i | some V => FiniteSuffixReplay.literal V i)
  | .user i args => if permitted nodes.length rs i args then match V with
      | none => .call (nodes.length+i) (args.map (fun j => .call j []))
      | some _ => FiniteWordCaptureSelection.gather nodes (palette R) args
          (fun W => .call (address nodes R rs i W) [])
      else MExp.failAlways
  | .seq a b => .seq (render nodes R rs V a) (render nodes R rs V b)
  | .alt a b => .alt (render nodes R rs V a) (render nodes R rs V b)
  | .notP a => .notP (render nodes R rs V a)
  | .star a => .star (render nodes R rs V a)

def source (nodes : List Node) (R : List (List Char)) (rs : List Rule) : MGrammar :=
  ⟨nodes.map (fun n => ⟨0,RegularCaptureProduct.body n⟩)++rs.map (fun r => ⟨r.arity,render nodes R rs none r.body⟩)⟩
def targetRule (nodes : List Node) (R : List (List Char)) (rs : List Rule) (key : Key) : MRule :=
  ⟨0,render nodes R rs (some key.value) ((rs[key.user]?).map Rule.body |>.getD .eps)⟩
def target (nodes : List Node) (R : List (List Char)) (rs : List Rule) : MGrammar :=
  ⟨(base nodes R).rules++(keys R rs).map (targetRule nodes R rs)⟩

abbrev sourceBodies (nodes : List Node) := nodes.map RegularCaptureProduct.body
abbrev targetBodies (nodes : List Node) (R : List (List Char)) :=
  RegularCaptureProduct.component nodes (ExactWordCaptureMachine.observer (palette R))

theorem source_rule (nodes : List Node) (R : List (List Char)) (rs : List Rule) (i : Nat) (r : Rule) (hr : rs[i]?=some r) :
    ruleAtM (source nodes R rs).rules (nodes.length+i)=some ⟨r.arity,render nodes R rs none r.body⟩ := by
  simp only [source,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp)]
  simp [List.length_map,List.getElem?_map,hr]

private theorem lookup_key (xs : List Key) (k : Key) (hm : k∈xs) : xs[xs.idxOf k]?=some k := by
  induction xs with
  | nil => cases hm
  | cons a xs ih =>
    by_cases he : a=k
    · subst a; simp
    · have ht : k∈xs := by
        rcases List.mem_cons.mp hm with he'|ht
        · exact False.elim (he he'.symm)
        · exact ht
      simp [List.idxOf_cons,cond_eq_ite,beq_iff_eq,he,ih ht]

theorem target_rule (nodes : List Node) (R : List (List Char)) (rs : List Rule) (i : Nat) (r : Rule) (hr : rs[i]?=some r)
    (E : List (List Char)) (he : E.length=r.arity) :
    ruleAtM (target nodes R rs).rules (address nodes R rs i (views R E))=
      some ⟨0,render nodes R rs (some (views R E)) r.body⟩ := by
  have hh := lookup_key (keys R rs) ⟨i,views R E⟩ (key_mem R rs i r hr E he)
  simp only [target,address,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by omega)]
  simp [List.getElem?_map,hh,targetRule,hr]

theorem source_installed (nodes : List Node) (R : List (List Char)) (rs : List Rule) :
    RecursiveParserStability.Installed (sourceBodies nodes) (source nodes R rs) := by
  intro i e hi
  have hb : i<nodes.length := by simpa using (List.getElem?_eq_some_iff.mp hi).1
  have he : RegularCaptureProduct.body nodes[i]=e := by
    simpa only [sourceBodies,List.getElem?_map,List.getElem?_eq_getElem hb,Option.map_some,Option.some.injEq] using hi
  simp only [source,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hb)]
  simp [List.getElem?_eq_getElem hb,he]

theorem target_installed (nodes : List Node) (R : List (List Char)) (rs : List Rule) :
    RecursiveParserStability.Installed (targetBodies nodes R) (target nodes R rs) :=
  RegularCaptureProduct.component_installed nodes _ _

theorem arguments_firstOrder (args : List Nat) : MExp.FirstOrderArgs (args.map (fun j => .call j [])) := by
  induction args with
  | nil => trivial
  | cons j args ih => exact ⟨True.intro,ih⟩

theorem firstOrder (nodes : List Node) (R : List (List Char)) (rs : List Rule) (V : Option View) :
    ∀ e, (render nodes R rs V e).FirstOrder
  | .seq a b | .alt a b => ⟨firstOrder nodes R rs V a,firstOrder nodes R rs V b⟩
  | .notP a | .star a => firstOrder nodes R rs V a
  | .helper i => by simp only [render]; split <;> trivial
  | .replay i => by
    cases V with
    | none => exact ⟨FiniteSuffixReplay.guard_firstOrder R,True.intro⟩
    | some V => exact ⟨FiniteSuffixReplay.guard_firstOrder R,FiniteSuffixReplay.literal_firstOrder V i⟩
  | .user i args => by
    simp only [render]
    split
    · cases V with
      | none =>
        change MExp.FirstOrderArgs (args.map (fun j => .call j []))
        exact arguments_firstOrder args
      | some V => exact FiniteWordCaptureSelection.gather_firstOrder nodes (palette R) args _ (by intro W; trivial)
    · trivial
  | .eps | .any | .chr _ | .range _ _ | .lit _ => True.intro

theorem source_firstOrder (nodes : List Node) (R : List (List Char)) (rs : List Rule) : (source nodes R rs).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · obtain ⟨n,_,rfl⟩ := List.mem_map.mp hr
    cases n <;> trivial
  · obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    exact firstOrder _ _ _ _ _

theorem target_firstOrder (nodes : List Node) (R : List (List Char)) (rs : List Rule) : (target nodes R rs).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · exact RegularCaptureProduct.grammar_firstOrder nodes _ r hr
  · obtain ⟨key,_,rfl⟩ := List.mem_map.mp hr
    exact firstOrder _ _ _ _ _

end Shallot.MacroPeg.CBV.FiniteSuffixRecursiveSyntax
