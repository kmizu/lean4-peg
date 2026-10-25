import MacroPeg.CBV.EmptyArgumentCorrespondence
import MacroPeg.Properties.MExpEq

namespace Shallot.MacroPeg.CBV.ParReturnEffects

/-- These effects constrain successful results, not termination or failure.
Dead may be undefined; Zero may fail or be undefined. -/
inductive Effect where
  | dead | zero | any
  deriving DecidableEq, Repr

def Good : Effect → Nat → Nat → Prop
  | .dead,_,_ => False
  | .zero,p,q => q=p
  | .any,_,_ => True

def sequence : Effect → Effect → Effect
  | .dead,_ | _,.dead => .dead
  | .zero,.zero => .zero
  | _,_ => .any

def choice : Effect → Effect → Effect
  | .any,_ | _,.any => .any
  | .dead,.dead => .dead
  | _,_ => .zero

def analyze (g : MGrammar) (zeros deads : List Nat) : MExp → Effect
  | .eps => .zero
  | .lit w => if w.isEmpty then .zero else .any
  | .notP a => if a=.eps then .dead else .zero
  | .seq a b => sequence (analyze g zeros deads a) (analyze g zeros deads b)
  | .alt a b => choice (analyze g zeros deads a) (analyze g zeros deads b)
  | .star a => if analyze g zeros deads a=.any then .any else .zero
  | .call i args => match ruleAtM g.rules i with
    | none => .dead
    | some r => if r.arity=args.length then
        if i∈deads then .dead else if i∈zeros then .zero else .any
      else .dead
  | _ => .any

def RowFacts (x : List Char) (T : ClockFreezing.Table) (ids : List Nat) (e : Effect) :=
  ∀ i∈ids, ∀ W p q, p≤x.length → valAt (T i W) p=some (some q) → Good e p q

theorem sequence_good (a b : Effect) (p j q : Nat) : Good a p j → Good b j q → Good (sequence a b) p q := by
  cases a <;> cases b <;> simp_all [Good,sequence]

theorem choice_left (a b : Effect) (p q : Nat) : Good a p q → Good (choice a b) p q := by
  cases a <;> cases b <;> simp_all [Good,choice]

theorem choice_right (a b : Effect) (p q : Nat) : Good b p q → Good (choice a b) p q := by
  cases a <;> cases b <;> simp_all [Good,choice]

theorem zero_of_not_any (a : Effect) (ha : a≠.any) (p q : Nat) : Good a p q → q=p := by
  cases a <;> simp_all [Good]

/-- Calls use their original Par entry position. The statement intentionally
does not assert a corresponding Seq call effect. -/
theorem eval_success (g : MGrammar) (zeros deads : List Nat) (x : List Char) (T : ClockFreezing.Table)
    (hT : OkTV x.length T) (hz : RowFacts x T zeros .zero) (hd : RowFacts x T deads .dead)
    (E : List (List Char)) : ∀ e p q, p≤x.length → evV g x .callByValuePar T E e p=some (some q) →
      Good (analyze g zeros deads e) p q
  | .eps,p,q,_,he => by simpa only [analyze,evV,Good,Option.some.injEq] using he.symm
  | .lit w,p,q,hp,he => by
    by_cases hw : w.isEmpty=true
    · have hh : w=[] := List.isEmpty_iff.mp hw
      subst w
      simpa only [analyze,List.isEmpty_nil,if_true,Good,evV,Shallot.stripPrefix?,length_sfx x hp,Option.some.injEq] using he.symm
    · simp only [analyze,hw,Bool.false_eq_true,if_false,Good]
  | .notP a,p,q,_,he => by
    by_cases hz : a=.eps
    · subst a; simp [evV] at he
    · simp only [analyze,if_neg hz,Good]
      cases ha : evV g x .callByValuePar T E a p with
      | none => simp [evV,ha] at he
      | some v => cases v <;> simp [evV,ha] at he
                  exact he.symm
  | .seq a b,p,q,hp,he => by
    cases ha : evV g x .callByValuePar T E a p with
    | none => rw [evV_seq_none ha] at he; cases he
    | some v => cases v with
      | none => rw [evV_seq_fail ha] at he; cases he
      | some j =>
        rw [evV_seq_ok ha] at he
        exact sequence_good _ _ p j q (eval_success g zeros deads x T hT hz hd E a p j hp ha)
          (eval_success g zeros deads x T hT hz hd E b j q (evV_ok hT a p hp j ha) he)
  | .alt a b,p,q,hp,he => by
    cases ha : evV g x .callByValuePar T E a p with
    | none => rw [evV_alt_none ha] at he; cases he
    | some v => cases v with
      | none =>
        rw [evV_alt_fail ha] at he
        exact choice_right _ _ p q (eval_success g zeros deads x T hT hz hd E b p q hp he)
      | some j =>
        rw [evV_alt_ok ha] at he
        have hq : j=q := by simpa only [Option.some.injEq] using he
        subst j
        exact choice_left _ _ p q (eval_success g zeros deads x T hT hz hd E a p q hp ha)
  | .star a,p,q,hp,he => by
    by_cases hc : analyze g zeros deads a=.any
    · simp only [analyze,if_pos hc,Good]
    · simp only [analyze,if_neg hc,Good]
      rw [evV_star] at he
      cases ha : evV g x .callByValuePar T E a p with
      | none => rw [evStar_none ha] at he; cases he
      | some v => cases v with
        | none => rw [evStar_fail ha] at he; simpa only [Option.some.injEq] using he.symm
        | some j =>
          have hj := zero_of_not_any _ hc p j (eval_success g zeros deads x T hT hz hd E a p j hp ha)
          rw [evStar_stuck ha (by omega)] at he
          cases he
  | .call i args,p,q,hp,he => by
    cases hr : ruleAtM g.rules i with
    | none => simp [evV,hr] at he
    | some r =>
      by_cases hlen : r.arity=args.length
      · rw [evV_call_par hr hlen (by decide)] at he
        simp only [analyze,hr,if_pos hlen]
        cases hargs : evParArgs g x .callByValuePar T E args p with
        | none => simp [hargs] at he
        | some W => cases W with
          | none => simp [hargs] at he
          | some W =>
            simp only [hargs] at he
            by_cases hdead : i∈deads
            · simp only [if_pos hdead]; exact hd i hdead W p q hp he
            · simp only [if_neg hdead]
              by_cases hzero : i∈zeros
              · simp only [if_pos hzero]; exact hz i hzero W p q hp he
              · simp only [if_neg hzero,Good]
      · simp [evV,hr,hlen] at he
  | .any,_,_,_,_ | .chr _,_,_,_,_ | .range _ _,_,_,_,_ | .param _,_,_,_,_
  | .dbg _,_,_,_,_ | .lam _ _,_,_,_,_ | .callParam _ _,_,_,_,_ | .invoke _ _ _,_,_,_,_ => True.intro

/-- A finite, mutually recursive certificate. Missing rows cannot succeed.
`dead` permits divergence and must never be treated as finite failure. -/
def check (g : MGrammar) (zeros deads : List Nat) : Bool :=
  zeros.all (fun i => match ruleAtM g.rules i with
    | none => true
    | some r => decide (analyze g zeros deads r.body ≠ .any)) &&
  deads.all (fun i => match ruleAtM g.rules i with
    | none => true
    | some r => decide (analyze g zeros deads r.body = .dead))

theorem checked_zero (g : MGrammar) (zeros deads : List Nat) (hc : check g zeros deads=true)
    (i : Nat) (hi : i∈zeros) (r : MRule) (hr : ruleAtM g.rules i=some r) :
    analyze g zeros deads r.body ≠ .any := by
  have h := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).1 i hi
  simpa only [hr,decide_eq_true_eq] using h

theorem checked_dead (g : MGrammar) (zeros deads : List Nat) (hc : check g zeros deads=true)
    (i : Nat) (hi : i∈deads) (r : MRule) (hr : ruleAtM g.rules i=some r) :
    analyze g zeros deads r.body = .dead := by
  have h := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2 i hi
  simpa only [hr,decide_eq_true_eq] using h

/-- Closes the finite certificate over the actual recursive Par tables at
all physical clocks, all inputs, and arbitrary retained environments. -/
theorem tables (g : MGrammar) (zeros deads : List Nat) (hc : check g zeros deads=true)
    (x : List Char) (k : Nat) :
    RowFacts x (tblV g x .callByValuePar k) zeros .zero ∧
    RowFacts x (tblV g x .callByValuePar k) deads .dead := by
  induction k with
  | zero => constructor <;> intro i hi W p q hp he <;> simp [tblV,valAt] at he
  | succ k ih =>
    constructor
    · intro i hi W p q hp he
      cases hr : ruleAtM g.rules i with
      | none => simp [tblV,hr,valAt] at he
      | some r =>
        rw [valAt_tblV_succ hr W hp] at he
        exact zero_of_not_any _ (checked_zero g zeros deads hc i hi r hr) p q
          (eval_success g zeros deads x _ (tblV_ok g x .callByValuePar k) ih.1 ih.2 W r.body p q hp he)
    · intro i hi W p q hp he
      cases hr : ruleAtM g.rules i with
      | none => simp [tblV,hr,valAt] at he
      | some r =>
        rw [valAt_tblV_succ hr W hp] at he
        have h := eval_success g zeros deads x _ (tblV_ok g x .callByValuePar k) ih.1 ih.2 W r.body p q hp he
        rwa [checked_dead g zeros deads hc i hi r hr] at h

theorem checked_success (g : MGrammar) (zeros deads : List Nat) (hc : check g zeros deads=true)
    (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp)
    (p q : Nat) (hp : p≤x.length)
    (he : evV g x .callByValuePar (tblV g x .callByValuePar k) E e p=some (some q)) :
    Good (analyze g zeros deads e) p q :=
  eval_success g zeros deads x _ (tblV_ok g x .callByValuePar k)
    (tables g zeros deads hc x k).1 (tables g zeros deads hc x k).2 E e p q hp he

/-- Candidate pruning concerns rule identifiers, never captured words. The
final check is authoritative even when the chosen iteration budget is small. -/
def prune (g : MGrammar) (zs ds : List Nat) : List Nat × List Nat :=
  (zs.filter (fun i => match ruleAtM g.rules i with
    | none => true | some r => decide (analyze g zs ds r.body ≠ .any)),
   ds.filter (fun i => match ruleAtM g.rules i with
    | none => true | some r => decide (analyze g zs ds r.body = .dead)))

def candidates (g : MGrammar) : Nat → List Nat × List Nat
  | 0 => (List.range g.rules.length,List.range g.rules.length)
  | k+1 => let old := candidates g k; prune g old.1 old.2

def infer (g : MGrammar) : List Nat × List Nat :=
  let c := candidates g (2*g.rules.length+1)
  if check g c.1 c.2 then c else ([],[])

theorem infer_checked (g : MGrammar) : check g (infer g).1 (infer g).2=true := by
  unfold infer
  dsimp only
  split
  · assumption
  · rfl

/-- Analyze the rendered expression in the grammar's actual nullary-clone
specialization. This permits empty-bound callees whose ordinary retained-word
rows consume input. All original arguments and rows remain in the semantics. -/
def emptyEffect (g : MGrammar) (e : MExp) : Effect :=
  let h := EmptyArgumentSpecialization.target g
  analyze h (infer h).1 (infer h).2 (EmptyArgumentSpecialization.render g e)

theorem empty_success (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (k : Nat) (E : List (List Char)) (p q : Nat) (hp : p≤x.length)
    (hs : evV g x .callByValuePar (tblV g x .callByValuePar k) E e p=some (some q)) :
    Good (emptyEffect g e) p q := by
  rw [EmptyArgumentCorrespondence.evaluator_eq g hg x .callByValuePar k E e he p hp] at hs
  exact checked_success _ _ _ (infer_checked _) x k E _ p q hp hs

end Shallot.MacroPeg.CBV.ParReturnEffects
