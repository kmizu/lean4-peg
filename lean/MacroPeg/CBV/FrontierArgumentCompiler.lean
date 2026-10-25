import MacroPeg.CBV.FrontierArgumentNormalization
import MacroPeg.CBV.MixedGrowthChecks

namespace Shallot.MacroPeg.CBV.FrontierArgumentCompiler
open FrontierArgumentNormalization (Argument argument arguments scans preflight guarded)

abbrev Selection := List (Option (List Argument))
def selected (ps : Selection) (i : Nat) := ps[i]?.getD none

def ready (g : MGrammar) (ps : Selection) : Bool := ps.zipIdx.all (fun (entry,i) => match entry with
  | none => true
  | some ds => match ruleAtM g.rules i with
    | none => false
    | some r => decide (r.arity=ds.length) && ds.all (FrontierArgumentNormalization.check g))

def check (g : MGrammar) (ps : Selection) : Bool := ready g ps &&
  g.rules.all (fun r => MixedGrowthChecks.firstOrderCheck r.body)

def render (ps : Selection) : MExp → MExp
  | .call i args => match selected ps i with
    | some ds => if MExp.beqArgs args (arguments ds) then guarded i ds else .call i args
    | none => .call i args
  | .seq a b => .seq (render ps a) (render ps b)
  | .alt a b => .alt (render ps a) (render ps b)
  | .notP a => .notP (render ps a)
  | .star a => .star (render ps a)
  | e => e

def target (g : MGrammar) (ps : Selection) : MGrammar :=
  ⟨g.rules.map (fun r => ⟨r.arity,render ps r.body⟩)⟩

theorem source_firstOrder (g : MGrammar) (ps : Selection) (hc : check g ps=true) : g.FirstOrder := by
  intro r hr
  exact MixedGrowthChecks.firstOrder_checked _ (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2 r hr)

theorem ready_checked (g : MGrammar) (ps : Selection) (hc : check g ps=true)
    (i : Nat) (ds : List Argument) (hs : selected ps i=some ds) :
    ∃ r, ruleAtM g.rules i=some r ∧ r.arity=ds.length ∧ ds.all (FrontierArgumentNormalization.check g)=true := by
  have hget : ps[i]?=some (some ds) := by
    cases hh : ps[i]? <;> simp [selected,hh] at hs
    rename_i entry
    cases entry <;> simp_all [selected]
  have hm : (some ds,i)∈ps.zipIdx := List.mem_of_getElem?
    (show ps.zipIdx[i]?=some (some ds,i) from by simp [List.getElem?_zipIdx,hget])
  have hh := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).1 (some ds,i) hm
  cases hr : ruleAtM g.rules i with
  | none => simp [hr] at hh
  | some r =>
    simp only [hr] at hh
    exact ⟨r,rfl,of_decide_eq_true (Bool.and_eq_true_iff.mp hh).1,(Bool.and_eq_true_iff.mp hh).2⟩

theorem preflight_firstOrder : ∀ ds : List Argument, MExp.FirstOrderArgs (arguments ds) → (preflight ds).FirstOrder
  | [],_ => True.intro
  | a::ds,h => ⟨h.1,preflight_firstOrder ds h.2⟩

theorem scans_firstOrder (ds : List Argument) : MExp.FirstOrderArgs (scans ds) := by
  induction ds with
  | nil => trivial
  | cons a ds ih => exact ⟨NestedScannerArguments.scan_firstOrder _,ih⟩

theorem render_firstOrder (ps : Selection) : ∀ e, e.FirstOrder → (render ps e).FirstOrder
  | .call i args,h => by
    simp only [render]
    cases hs : selected ps i with
    | none => exact h
    | some ds =>
      simp only [hs]
      split
      next heq =>
        have heq := (MExp.beqArgs_iff _ _).mp heq
        subst args
        exact ⟨preflight_firstOrder ds h,scans_firstOrder ds⟩
      next => exact h
  | .seq a b,h | .alt a b,h => ⟨render_firstOrder ps a h.1,render_firstOrder ps b h.2⟩
  | .notP a,h | .star a,h => render_firstOrder ps a h
  | .eps,h | .any,h | .chr _,h | .range _ _,h | .lit _,h | .param _,h
  | .dbg _,h | .lam _ _,h | .callParam _ _,h | .invoke _ _ _,h => h

theorem target_rule (g : MGrammar) (ps : Selection) (i : Nat) :
    ruleAtM (target g ps).rules i=(ruleAtM g.rules i).map (fun r => ⟨r.arity,render ps r.body⟩) := by
  simp [target,ruleAtM_eq_getElem?]

theorem target_firstOrder (g : MGrammar) (ps : Selection) (hc : check g ps=true) : (target g ps).FirstOrder := by
  intro r hr
  change r∈g.rules.map (fun r => ⟨r.arity,render ps r.body⟩) at hr
  obtain ⟨a,ha,heq⟩ := List.mem_map.mp hr
  subst r
  exact render_firstOrder ps _ (source_firstOrder g ps hc a ha)

/-- This equality is proved on the original physical tables. Recursive
helpers are checked against their actual source declarations. -/
theorem evaluator (g : MGrammar) (ps : Selection) (hc : check g ps=true)
    (x : List Char) (k : Nat) (E : List (List Char)) : ∀ e p, p≤x.length →
    evV g x .callByValuePar (tblV g x .callByValuePar k) E e p=
      evV g x .callByValuePar (tblV g x .callByValuePar k) E (render ps e) p
  | .call i args,p,hp => by
    simp only [render]
    cases hs : selected ps i with
    | none => rfl
    | some ds =>
      simp only [hs]
      split
      next heq =>
        have heq := (MExp.beqArgs_iff _ _).mp heq
        subst args
        obtain ⟨r,hr,ha,hd⟩ := ready_checked g ps hc i ds hs
        exact FrontierArgumentNormalization.call_eq g ds hd i r hr ha x k E p hp
      next => rfl
  | .seq a b,p,hp => by
    have hh := evaluator g ps hc x k E a p hp
    cases ha : evV g x .callByValuePar (tblV g x .callByValuePar k) E a p with
    | none => simp only [render,evV_seq_none ha,evV_seq_none (hh.symm.trans ha)]
    | some v => cases v with
      | none => simp only [render,evV_seq_fail ha,evV_seq_fail (hh.symm.trans ha)]
      | some j =>
        simp only [render,evV_seq_ok ha,evV_seq_ok (hh.symm.trans ha)]
        exact evaluator g ps hc x k E b j (evV_ok (tblV_ok _ _ _ k) a p hp j ha)
  | .alt a b,p,hp => by
    have hh := evaluator g ps hc x k E a p hp
    cases ha : evV g x .callByValuePar (tblV g x .callByValuePar k) E a p with
    | none => simp only [render,evV_alt_none ha,evV_alt_none (hh.symm.trans ha)]
    | some v => cases v with
      | none =>
        simp only [render,evV_alt_fail ha,evV_alt_fail (hh.symm.trans ha)]
        exact evaluator g ps hc x k E b p hp
      | some j => simp only [render,evV_alt_ok ha,evV_alt_ok (hh.symm.trans ha)]
  | .notP a,p,hp => by simp only [render,evV]; rw [evaluator g ps hc x k E a p hp]
  | .star a,p,hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator g ps hc x k E a q (by omega))
  | .eps,_,_ | .any,_,_ | .chr _,_,_ | .range _ _,_,_ | .lit _,_,_ | .param _,_,_
  | .dbg _,_,_ | .lam _ _,_,_ | .callParam _ _,_,_ | .invoke _ _ _,_,_ => rfl

theorem related (g : MGrammar) (ps : Selection) (hc : check g ps=true) :
    BoundedBodyRewrite.Related g (target g ps) .callByValuePar := by
  intro i
  rw [target_rule]
  cases hr : ruleAtM g.rules i with
  | none => trivial
  | some r =>
    refine ⟨rfl,?_⟩
    intro x k E p hp
    have he := evaluator g ps hc x k E r.body p hp
    refine ⟨?_,?_⟩
    · rw [he]; exact RLe.refl _
    · rw [←he]; exact evV_mono (tblV_step g x .callByValuePar k) r.body p

/-- The local canonical argument rewrite is exact at a physical clock.
Consequently the two ordinary-grammar table approximants agree exactly. -/
theorem tables_equal (g : MGrammar) (ps : Selection) (hc : check g ps=true) (x : List Char) (k : Nat) :
    tblV g x .callByValuePar k=tblV (target g ps) x .callByValuePar k := by
  have ha := BoundedBodyRewrite.arities (related g ps hc)
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i E
    have ht := target_rule g ps i
    cases hr : ruleAtM g.rules i with
    | none =>
      have ht : ruleAtM (target g ps).rules i=none := by rw [ht,hr]; rfl
      simp only [tblV,hr,ht]
    | some r =>
      have ht : ruleAtM (target g ps).rules i=some ⟨r.arity,render ps r.body⟩ := by rw [ht,hr]; rfl
      simp only [tblV,hr,ht,ih]
      apply List.map_congr_left
      intro p hp
      have hp : p≤x.length := by have hh := List.mem_range.mp hp; omega
      have he := evaluator g ps hc x k E r.body p hp
      rw [ih] at he
      exact he.trans (SemanticBodyRewrite.evaluator g (target g ps) ha x .callByValuePar
        (tblV (target g ps) x .callByValuePar k) E (render ps r.body) p)

theorem physical (g : MGrammar) (ps : Selection) (hc : check g ps=true)
    (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp) (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) E e p=
      evV (target g ps) x .callByValuePar (tblV (target g ps) x .callByValuePar k) E (render ps e) p := by
  have he := evaluator g ps hc x k E e p hp
  rw [tables_equal g ps hc x k] at he
  rw [tables_equal g ps hc x k]
  exact he.trans (SemanticBodyRewrite.evaluator g (target g ps) (BoundedBodyRewrite.arities (related g ps hc))
    x .callByValuePar (tblV (target g ps) x .callByValuePar k) E (render ps e) p)

theorem observations_iff (g : MGrammar) (ps : Selection) (hc : check g ps=true)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar e x rest ↔ SObs (target g ps) .callByValuePar (render ps e) x rest := by
  have hg := source_firstOrder g ps hc
  have ht := target_firstOrder g ps hc
  have hf := render_firstOrder ps e he
  have hs : SObs g .callByValuePar e x rest ↔ SObs g .callByValuePar (render ps e) x rest := by
    rw [←decideObsV_iff hg (by decide) he,←decideObsV_iff hg (by decide) hf]
    unfold decideObsV
    rw [evaluator g ps hc x (iterBoundV g x) [] e x.length (Nat.le_refl _)]
  exact hs.trans (BoundedBodyRewrite.observations (related g ps hc) hg ht (by decide) _ hf x rest)

theorem undefined_iff (g : MGrammar) (ps : Selection) (hc : check g ps=true)
    (e : MExp) (he : e.FirstOrder) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] e x.length=none) ↔
      ∀ k, evV (target g ps) x .callByValuePar (tblV (target g ps) x .callByValuePar k) [] (render ps e) x.length=none :=
  BoundedBodyRewrite.undefined_of_observations _ _ (source_firstOrder g ps hc) (target_firstOrder g ps hc)
    _ _ (by decide) (by decide) _ _ he (render_firstOrder ps e he) x
    (fun rest => observations_iff g ps hc e he x rest)

end Shallot.MacroPeg.CBV.FrontierArgumentCompiler
