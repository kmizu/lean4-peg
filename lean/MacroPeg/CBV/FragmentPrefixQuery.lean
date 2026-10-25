import MacroPeg.CBV.FragmentMixedRecursive
import MacroPeg.CBV.PrefixCaptureQuery

namespace Shallot.MacroPeg.CBV.FragmentPrefixQuery
open FragmentMixedRecursive (Part render leaf)
open RuntimeShiftFilter (scanner)
open ReplayControlFusion (Plan)
open ClockFreezing (Table)

inductive Body where
  | leaf : Nat → Body
  | after (positive : Bool) (copy : Nat)
  | alt : Body → Body → Body
  | notP : Body → Body
  | guard : Body → Body → Body

def lower (n : Nat) : Body → Plan
  | .leaf j => .leaf j
  | .after positive copy => PrefixCaptureQuery.afterPlan positive (n+1) copy
  | .alt a b => .alt (lower n a) (lower n b)
  | .notP a => .notP (lower n a)
  | .guard a b => .guard (lower n a) (lower n b)

def liftPlan : Plan → Body
  | .leaf j => .leaf j
  | .alt a b => .alt (liftPlan a) (liftPlan b)
  | .notP a => .notP (liftPlan a)
  | .guard a b => .guard (liftPlan a) (liftPlan b)

def raw (plans : List Plan) (tails : List Part) : Body → MExp
  | .leaf j => leaf plans tails j
  | .after positive _ => .seq scanner (PrefixCaptureQuery.query positive (.param 0))
  | .alt a b => .alt (raw plans tails a) (raw plans tails b)
  | .notP a => .notP (raw plans tails a)
  | .guard a b => .seq (.andP (raw plans tails a)) (raw plans tails b)

def copyCheck (tails : List Part) (j : Nat) : Bool :=
  match tails[j]? with | some (true,.eps) => true | _ => false

def bodyCheck (tails : List Part) : Body → Bool
  | .leaf j => decide (j≤tails.length+1)
  | .after _ j => copyCheck tails j
  | .alt a b | .guard a b => bodyCheck tails a && bodyCheck tails b
  | .notP a => bodyCheck tails a

def check (tails : List Part) (bodies : List Body) : Bool := bodies.all (bodyCheck tails)
def plans (tails : List Part) (bodies : List Body) : List Plan := bodies.map (lower tails.length)

theorem copy_sound (tails : List Part) (j : Nat) (h : copyCheck tails j=true) :
    tails[j]?=some (true,.eps) := by
  unfold copyCheck at h
  cases hl : tails[j]? with
  | none => simp [hl] at h
  | some b =>
    obtain ⟨split,e⟩ := b
    cases split <;> cases e <;> simp_all

theorem lower_bound (tails : List Part) : ∀ b, bodyCheck tails b=true →
    (lower tails.length b).All (fun j => j≤tails.length+1)
  | .leaf j,h => by
    change j≤tails.length+1
    exact of_decide_eq_true h
  | .after positive j,h => by
    have hj : j<tails.length := (List.getElem?_eq_some_iff.mp (copy_sound tails j h)).choose
    cases positive <;> change (j≤tails.length+1 ∧ tails.length+1≤tails.length+1) <;> exact ⟨by omega,Nat.le_refl _⟩
  | .alt a b,h | .guard a b,h =>
    ⟨lower_bound tails a (Bool.and_eq_true_iff.mp h).1,lower_bound tails b (Bool.and_eq_true_iff.mp h).2⟩
  | .notP a,h => lower_bound tails a h

theorem valid (tails : List Part) (bodies : List Body) (h : check tails bodies=true) :
    FragmentMixedRecursive.Valid (plans tails bodies) tails := by
  intro P hp
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
  exact lower_bound tails b ((List.all_eq_true.mp h) b hb)

private theorem seq_eps (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (e : MExp) (p : Nat) :
    evV g x s T E (.seq e .eps) p=evV g x s T E e p := by
  cases hv : evV g x s T E e p with
  | none => rw [evV_seq_none hv]
  | some v => cases v with
    | none => rw [evV_seq_fail hv]
    | some q => rw [evV_seq_ok hv]; rfl

theorem body_eval (ps : List Plan) (tails : List Part) (g : MGrammar) (x : List Char)
    (s : Strategy) (T : Table) (E : List (List Char)) : ∀ b, bodyCheck tails b=true → ∀ p,
    evV g x s T E (raw ps tails b) p=
      evV g x s T E ((lower tails.length b).exp (leaf ps tails)) p
  | .leaf _,_,_ => rfl
  | .after positive j,h,p => by
    have hj := copy_sound tails j h
    have hlt : j<tails.length := (List.getElem?_eq_some_iff.mp hj).choose
    apply PrefixCaptureQuery.prefix_query g x s T E scanner (.param 0) positive (leaf ps tails) (tails.length+1) j p
    · simp [leaf]
    · have hn : j≠tails.length+1 := by omega
      simp only [leaf,hn,ite_false,hj,FragmentMixedRecursive.head,ite_true,render]
      rw [←LeadingReplayStar.sequence_assoc g x s T E scanner (.param 0) .eps p]
      exact seq_eps g x s T E _ p
  | .alt a b,h,p | .guard a b,h,p => by
    have ha := body_eval ps tails g x s T E a (Bool.and_eq_true_iff.mp h).1
    have hb := body_eval ps tails g x s T E b (Bool.and_eq_true_iff.mp h).2
    simp only [raw,lower,Plan.exp,MExp.andP,evV,ha,hb]
  | .notP a,h,p => by simp only [raw,lower,Plan.exp,evV,body_eval ps tails g x s T E a h]

/-- Replace the actual logical user bodies and retain every appended
fragment/replay/independent helper rule at its original address. -/
def source (tails : List Part) (bodies : List Body) : MGrammar :=
  ⟨bodies.map (fun b => ⟨1,raw (plans tails bodies) tails b⟩)++
    (FragmentMixedRecursive.source (plans tails bodies) tails).rules.drop bodies.length⟩
abbrev target (tails : List Part) (bodies : List Body) := FragmentMixedRecursive.target (plans tails bodies) tails
def sourceRender (tails : List Part) (bodies : List Body) (e : MExp) :=
  render (tails.map Prod.fst) tails.length (plans tails bodies) true false e
def targetRender (tails : List Part) (bodies : List Body) (e : MExp) :=
  render (tails.map Prod.fst) tails.length (plans tails bodies) false false e

theorem raw_firstOrder (ps : List Plan) (tails : List Part) : ∀ b, (raw ps tails b).FirstOrder
  | .leaf j => FragmentMixedRecursive.leaf_firstOrder ps tails j
  | .after positive _ => by
    cases positive <;> exact ⟨by simp [scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,MExp.FirstOrder,MExp.failAlways],True.intro⟩
  | .alt a b | .guard a b => ⟨raw_firstOrder ps tails a,raw_firstOrder ps tails b⟩
  | .notP a => raw_firstOrder ps tails a

theorem source_firstOrder (tails : List Part) (bodies : List Body) : (source tails bodies).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    exact raw_firstOrder _ tails b
  · exact FragmentMixedRecursive.source_firstOrder _ tails r (List.mem_of_mem_drop hr)

theorem source_rule (tails : List Part) (bodies : List Body) (i : Nat) (b : Body) (hb : bodies[i]?=some b) :
    ruleAtM (source tails bodies).rules i=some ⟨1,raw (plans tails bodies) tails b⟩ := by
  have hi : i<bodies.length := (List.getElem?_eq_some_iff.mp hb).choose
  simp only [source,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [hb]

theorem related (tails : List Part) (bodies : List Body) (h : check tails bodies=true) :
    SemanticBodyRewrite.Related (source tails bodies)
      (FragmentMixedRecursive.source (plans tails bodies) tails) .callByValuePar := by
  intro i
  by_cases hi : i<bodies.length
  · have hb := List.getElem?_eq_getElem hi
    have hn : (plans tails bodies)[i]?=some (lower tails.length bodies[i]) := by simp [plans,hb]
    rw [source_rule tails bodies i bodies[i] hb,FragmentMixedRecursive.source_rule _ tails i _ hn]
    exact ⟨rfl,fun x T E p _ => body_eval _ tails _ x .callByValuePar T E bodies[i]
      ((List.all_eq_true.mp h) _ (List.mem_of_getElem? hb)) p⟩
  · have hh : bodies.length≤i := by omega
    simp only [source,ruleAtM_eq_getElem?]
    rw [List.getElem?_append_right (by simpa using hh)]
    simp only [List.length_map,List.getElem?_drop]
    rw [show bodies.length+(i-bodies.length)=i from by omega]
    cases (FragmentMixedRecursive.source (plans tails bodies) tails).rules[i]? with
    | none => trivial
    | some r => exact ⟨rfl,fun _ _ _ _ _ => rfl⟩

theorem physical (tails : List Part) (bodies : List Body) (h : check tails bodies=true)
    (x : List Char) (k : Nat) (e : MExp) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source tails bodies) x .callByValuePar (tblV (source tails bodies) x .callByValuePar k) E (sourceRender tails bodies e) p=
      evV (target tails bodies) x .callByValueSeq (tblV (target tails bodies) x .callByValueSeq k) E (targetRender tails bodies e) p :=
  (SemanticBodyRewrite.physical (related tails bodies h) x k E _ p).trans
    (FragmentMixedRecursive.evaluator_eq _ tails (valid tails bodies h) x k false e E p hp)

theorem observations_iff (tails : List Part) (bodies : List Body) (h : check tails bodies=true)
    (e : MExp) (x : List Char) (rest : Option (List Char)) :
    SObs (source tails bodies) .callByValuePar (sourceRender tails bodies e) x rest ↔
      SObs (target tails bodies) .callByValueSeq (targetRender tails bodies e) x rest :=
  (SemanticBodyRewrite.observations (related tails bodies h) (source_firstOrder tails bodies)
    (FragmentMixedRecursive.source_firstOrder _ tails) (by decide) _
    (FragmentMixedRecursive.render_firstOrder _ _ _ true false e) x rest).trans
    (FragmentMixedRecursive.observations_iff _ tails (valid tails bodies h) e x rest)

theorem language_translation (tails : List Part) (bodies : List Body) (h : check tails bodies=true) (e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (source tails bodies) .callByValuePar (sourceRender tails bodies e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨_,_,FragmentMixedRecursive.target_firstOrder _ tails,
    FragmentMixedRecursive.render_firstOrder _ _ _ false false e,
    fun x => observations_iff tails bodies h e x (some [])⟩

theorem defined_iff (tails : List Part) (bodies : List Body) (h : check tails bodies=true)
    (e : MExp) (x : List Char) (v : Option Nat) :
    (∃ k, evV (source tails bodies) x .callByValuePar (tblV (source tails bodies) x .callByValuePar k)
      [] (sourceRender tails bodies e) x.length=some v) ↔
    (∃ k, evV (target tails bodies) x .callByValueSeq (tblV (target tails bodies) x .callByValueSeq k)
      [] (targetRender tails bodies e) x.length=some v) :=
  exists_congr (fun k => by rw [physical tails bodies h x k e [] x.length (Nat.le_refl _)])

theorem undefined_iff (tails : List Part) (bodies : List Body) (h : check tails bodies=true)
    (e : MExp) (x : List Char) :
    (∀ k, evV (source tails bodies) x .callByValuePar (tblV (source tails bodies) x .callByValuePar k)
      [] (sourceRender tails bodies e) x.length=none) ↔
    (∀ k, evV (target tails bodies) x .callByValueSeq (tblV (target tails bodies) x .callByValueSeq k)
      [] (targetRender tails bodies e) x.length=none) :=
  forall_congr' (fun k => by rw [physical tails bodies h x k e [] x.length (Nat.le_refl _)])

end Shallot.MacroPeg.CBV.FragmentPrefixQuery
