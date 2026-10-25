import MacroPeg.CBV.WordViewSubstitution
import MacroPeg.CBV.ScannerPairFusion

namespace Shallot.MacroPeg.CBV.EmptyArgumentSpecialization

/-- Input-dependent queries may fail or diverge. Every successful result
of a checked expression is nevertheless at its entry position. -/
def zeroCheck : MExp → Bool
  | .eps | .notP _ => true
  | .lit w => w.isEmpty
  | .seq a b | .alt a b => zeroCheck a && zeroCheck b
  | .star a => zeroCheck a
  | _ => false

theorem zero_success (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) : ∀ e, zeroCheck e=true → ∀ p q, p≤x.length →
    evV g x s T E e p=some (some q) → q=p
  | .eps,_,p,q,_,h => by simpa only [evV,Option.some.injEq] using h.symm
  | .lit w,h,p,q,hp,he => by
    have hw : w=[] := List.isEmpty_iff.mp h
    subst w
    simpa only [evV,Shallot.stripPrefix?,length_sfx x hp,Option.some.injEq] using he.symm
  | .notP a,_,p,q,_,he => by
    cases ha : evV g x s T E a p with
    | none => simp [evV,ha] at he
    | some v => cases v <;> simp [evV,ha] at he
                exact he.symm
  | .seq a b,h,p,q,hp,he => by
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    cases hx : evV g x s T E a p with
    | none => rw [evV_seq_none hx] at he; cases he
    | some v => cases v with
      | none => rw [evV_seq_fail hx] at he; cases he
      | some j =>
        have hj := zero_success g x s T E a ha p j hp hx
        subst j
        rw [evV_seq_ok hx] at he
        exact zero_success g x s T E b hb p q hp he
  | .alt a b,h,p,q,hp,he => by
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    cases hx : evV g x s T E a p with
    | none => rw [evV_alt_none hx] at he; cases he
    | some v => cases v with
      | none => rw [evV_alt_fail hx] at he; exact zero_success g x s T E b hb p q hp he
      | some j =>
        rw [evV_alt_ok hx] at he
        have hq : j=q := by simpa only [Option.some.injEq] using he
        exact hq.symm.trans (zero_success g x s T E a ha p j hp hx)
  | .star a,h,p,q,hp,he => by
    rw [evV_star] at he
    cases hx : evV g x s T E a p with
    | none => rw [evStar_none hx] at he; cases he
    | some v => cases v with
      | none => rw [evStar_fail hx] at he; simpa only [Option.some.injEq] using he.symm
      | some j =>
        have hj := zero_success g x s T E a h p j hp hx
        rw [evStar_stuck hx (by omega)] at he
        cases he
  | .any,h,_,_,_,_ | .chr _,h,_,_,_,_ | .range _ _,h,_,_,_,_ | .param _,h,_,_,_,_
  | .call _ _,h,_,_,_,_ | .dbg _,h,_,_,_,_ | .lam _ _,h,_,_,_,_
  | .callParam _ _,h,_,_,_,_ | .invoke _ _ _,h,_,_,_,_ => by cases h

mutual
  def render (g : MGrammar) : MExp → MExp
    | .call i args => match ruleAtM g.rules i with
      | none => MExp.failAlways
      | some r => match args with
        | [a] => if r.arity=1 ∧ zeroCheck a=true then .seq (render g a) (.call (g.rules.length+i) []) else .call i [render g a]
        | args => .call i (arguments g args)
    | .seq a b => .seq (render g a) (render g b)
    | .alt a b => .alt (render g a) (render g b)
    | .notP a => .notP (render g a)
    | .star a => .star (render g a)
    | .eps => .eps
    | .any => .any
    | .chr c => .chr c
    | .range a b => .range a b
    | .lit w => .lit w
    | .param k => .param k
    | _ => MExp.failAlways
  def arguments (g : MGrammar) : List MExp → List MExp
    | [] => []
    | a::args => render g a::arguments g args
end

def target (g : MGrammar) : MGrammar := ⟨
  g.rules.map (fun r => ⟨r.arity,render g r.body⟩) ++
  g.rules.map (fun r => ⟨0,render g (MExp.subst [.lit []] r.body)⟩)⟩

abbrev sourceTable (g : MGrammar) (x : List Char) (s : Strategy) (k : Nat) := tblV g x s k
abbrev targetTable (g : MGrammar) (x : List Char) (s : Strategy) (k : Nat) := tblV (target g) x s k

theorem arguments_length (g : MGrammar) (args : List MExp) : (arguments g args).length=args.length := by
  induction args with
  | nil => rfl
  | cons a args ih => simp only [arguments,List.length_cons,ih]

mutual
  theorem render_firstOrder (g : MGrammar) : ∀ e, (render g e).FirstOrder
    | .call i [] => by
      cases hr : ruleAtM g.rules i <;> simp only [render,hr] <;> trivial
    | .call i [a] => by
      cases hr : ruleAtM g.rules i with
      | none => simp only [render,hr]; trivial
      | some r =>
        simp only [render,hr]
        split
        · exact ⟨render_firstOrder g a,True.intro⟩
        · exact ⟨render_firstOrder g a,True.intro⟩
    | .call i (a::b::args) => by
      cases hr : ruleAtM g.rules i with
      | none => simp only [render,hr]; trivial
      | some r => simpa only [render,hr,MExp.FirstOrder] using arguments_firstOrder g (a::b::args)
    | .seq a b | .alt a b => ⟨render_firstOrder g a,render_firstOrder g b⟩
    | .star a | .notP a => render_firstOrder g a
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => trivial
    | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial
  termination_by e => sizeOf e
  decreasing_by all_goals simp_wf; all_goals omega
  theorem arguments_firstOrder (g : MGrammar) : ∀ args, MExp.FirstOrderArgs (arguments g args)
    | [] => True.intro
    | a::args => ⟨render_firstOrder g a,arguments_firstOrder g args⟩
  termination_by args => sizeOf args
  decreasing_by all_goals simp_wf; all_goals omega
end

theorem target_firstOrder (g : MGrammar) : (target g).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr <;> obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
  · exact render_firstOrder _ _
  · exact render_firstOrder _ _

theorem rule_count (g : MGrammar) : (target g).rules.length=2*g.rules.length := by simp [target]; omega

theorem original_rule (g : MGrammar) (i : Nat) (r : MRule) (hr : ruleAtM g.rules i=some r) :
    ruleAtM (target g).rules i=some ⟨r.arity,render g r.body⟩ := by
  have hr' : g.rules[i]?=some r := by simpa only [ruleAtM_eq_getElem?] using hr
  have hi := (List.getElem?_eq_some_iff.mp hr').1
  simp only [target,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa only [List.length_map] using hi)]
  simp only [List.getElem?_map,←ruleAtM_eq_getElem?,hr,Option.map_some]

theorem clone_rule (g : MGrammar) (i : Nat) (r : MRule) (hr : ruleAtM g.rules i=some r) :
    ruleAtM (target g).rules (g.rules.length+i)=some ⟨0,render g (MExp.subst [.lit []] r.body)⟩ := by
  simp only [target,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map,Nat.add_sub_cancel_left,List.getElem?_map,←ruleAtM_eq_getElem?,hr,Option.map_some]

def Rows (g : MGrammar) (x : List Char) (s : Strategy) (k : Nat) : Prop :=
  (∀ i r, ruleAtM g.rules i=some r → ∀ E p, p≤x.length →
    valAt (sourceTable g x s k i E) p=valAt (targetTable g x s k i E) p) ∧
  (∀ i r, ruleAtM g.rules i=some r → ∀ E p, p≤x.length →
    valAt (sourceTable g x s k i [[]]) p=valAt (targetTable g x s k (g.rules.length+i) E) p)

end Shallot.MacroPeg.CBV.EmptyArgumentSpecialization
