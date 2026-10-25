import MacroPeg.CBV.FiniteSuffixRecursiveCompiler

/-! Exact finite-view substitution inside arbitrary recursive actuals.
This is an expression theorem over a shared table, not yet an elimination
of the parameterized callee declarations into a nullary Seq grammar. -/
namespace Shallot.MacroPeg.CBV.FiniteSuffixDependentView
open ClockFreezing (Table)

inductive Expr where
  | eps | any | chr (c : Char) | range (a b : Char) | lit (w : List Char)
  | replay (i : Nat)
  | call (i : Nat) (args : List Expr)
  | seq (a b : Expr) | alt (a b : Expr) | notP (a : Expr) | star (a : Expr)
  deriving Repr

mutual
  def render (R : List (List Char)) (V : Option (List (Option (List Char)))) : Expr → MExp
    | .eps => .eps
    | .any => .any
    | .chr c => .chr c
    | .range a b => .range a b
    | .lit w => .lit w
    | .replay i => .seq (FiniteSuffixReplay.guard R) (match V with
        | none => .param i | some W => FiniteSuffixReplay.literal W i)
    | .call i args => .call i (renderArgs R V args)
    | .seq a b => .seq (render R V a) (render R V b)
    | .alt a b => .alt (render R V a) (render R V b)
    | .notP a => .notP (render R V a)
    | .star a => .star (render R V a)
  def renderArgs (R : List (List Char)) (V : Option (List (Option (List Char)))) : List Expr → List MExp
    | [] => []
    | a::args => render R V a::renderArgs R V args
end

theorem renderArgs_length (R : List (List Char)) (V : Option (List (Option (List Char)))) :
    ∀ args, (renderArgs R V args).length=args.length
  | [] => rfl
  | a::args => by simp only [renderArgs,List.length_cons,renderArgs_length R V args]

mutual
  /-- Nested calls retain their real actual captured words and use the same
  callee table. Only the current parent's guarded references are specialized. -/
  theorem specialize (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
      (ht : OkTV x.length T) (R : List (List Char)) (E : List (List Char)) :
      ∀ e p, p≤x.length →
      evV g x s T E (render R none e) p=
        evV g x s T [] (render R (some (FiniteSuffixReplay.views R E)) e) p
    | .replay i,p,hp => FiniteSuffixReplay.replay_eval g g x s s T T E R i p hp
    | .call i args,p,hp => by
      simp only [render,evV]
      cases hr : ruleAtM g.rules i with
      | none => rfl
      | some r =>
        have hl : (renderArgs R none args).length=(renderArgs R (some (FiniteSuffixReplay.views R E)) args).length := by
          rw [renderArgs_length,renderArgs_length]
        rw [hl]
        split
        · cases s <;> simp only [specializePar g x _ T ht R E args p hp,specializeSeq g x _ T ht R E args p hp]
        · rfl
    | .seq a b,p,hp => by
      have ha := specialize g x s T ht R E a p hp
      cases he : evV g x s T E (render R none a) p with
      | none => simp only [render,evV_seq_none he,evV_seq_none (ha.symm.trans he)]
      | some v => cases v with
        | none => simp only [render,evV_seq_fail he,evV_seq_fail (ha.symm.trans he)]
        | some j =>
          simp only [render,evV_seq_ok he,evV_seq_ok (ha.symm.trans he)]
          exact specialize g x s T ht R E b j (evV_ok ht _ p hp j he)
    | .alt a b,p,hp => by
      have ha := specialize g x s T ht R E a p hp
      cases he : evV g x s T E (render R none a) p with
      | none => simp only [render,evV_alt_none he,evV_alt_none (ha.symm.trans he)]
      | some v => cases v with
        | none =>
          simp only [render,evV_alt_fail he,evV_alt_fail (ha.symm.trans he)]
          exact specialize g x s T ht R E b p hp
        | some j => simp only [render,evV_alt_ok he,evV_alt_ok (ha.symm.trans he)]
    | .notP a,p,hp => by simp only [render,evV,specialize g x s T ht R E a p hp]
    | .star a,p,hp => by
      simp only [render,evV_star]
      exact evStar_congr p (fun q hq => specialize g x s T ht R E a q (by omega))
    | .eps,_,_ | .any,_,_ | .chr _,_,_ | .range _ _,_,_ | .lit _,_,_ => rfl

  theorem specializePar (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
      (ht : OkTV x.length T) (R : List (List Char)) (E : List (List Char)) :
      ∀ args p, p≤x.length →
      evParArgs g x s T E (renderArgs R none args) p=
        evParArgs g x s T [] (renderArgs R (some (FiniteSuffixReplay.views R E)) args) p
    | [],_,_ => rfl
    | a::args,p,hp => by
      simp only [renderArgs,evParArgs,specialize g x s T ht R E a p hp]
      rw [specializePar g x s T ht R E args p hp]

  theorem specializeSeq (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
      (ht : OkTV x.length T) (R : List (List Char)) (E : List (List Char)) :
      ∀ args p, p≤x.length →
      evSeqArgs g x s T E (renderArgs R none args) p=
        evSeqArgs g x s T [] (renderArgs R (some (FiniteSuffixReplay.views R E)) args) p
    | [],_,_ => rfl
    | a::args,p,hp => by
      have ha := specialize g x s T ht R E a p hp
      simp only [renderArgs,evSeqArgs,←ha]
      cases he : evV g x s T E (render R none a) p with
      | none => rfl
      | some v => cases v with
        | none => rfl
        | some j =>
          dsimp only []
          rw [specializeSeq g x s T ht R E args j (evV_ok ht _ p hp j he)]
end

/-- Equal finite views suffice even for parent-dependent actuals and calls
inside actuals, at every table satisfying the ordinary position invariant. -/
theorem environment_congr (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (ht : OkTV x.length T) (R : List (List Char)) (E F : List (List Char))
    (hv : FiniteSuffixReplay.views R E=FiniteSuffixReplay.views R F) (e : Expr) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (render R none e) p=evV g x s T F (render R none e) p := by
  rw [specialize g x s T ht R E e p hp,specialize g x s T ht R F e p hp,hv]


theorem physical_environment_congr (g : MGrammar) (x : List Char) (s : Strategy) (k : Nat)
    (R : List (List Char)) (E F : List (List Char))
    (hv : FiniteSuffixReplay.views R E=FiniteSuffixReplay.views R F) (e : Expr) (p : Nat) (hp : p≤x.length) :
    evV g x s (tblV g x s k) E (render R none e) p=
      evV g x s (tblV g x s k) F (render R none e) p :=
  environment_congr g x s _ (tblV_ok g x s k) R E F hv e p hp

structure Rule where
  arity : Nat
  body : Expr
  deriving Repr

def source (R : List (List Char)) (rs : List Rule) : MGrammar :=
  ⟨rs.map (fun r => ⟨r.arity,render R none r.body⟩)⟩

theorem source_rule (R : List (List Char)) (rs : List Rule) (i : Nat) (r : Rule) (hr : rs[i]?=some r) :
    ruleAtM (source R rs).rules i=some ⟨r.arity,render R none r.body⟩ := by
  simp [source,ruleAtM_eq_getElem?,List.getElem?_map,hr]

/-- Full mutually recursive source rows factor through the finite view,
including when actuals inspect parent values and invoke other users. -/
theorem rows_factor (R : List (List Char)) (rs : List Rule) (i : Nat) (r : Rule) (hr : rs[i]?=some r)
    (x : List Char) (s : Strategy) (E F : List (List Char))
    (hv : FiniteSuffixReplay.views R E=FiniteSuffixReplay.views R F) (p : Nat) (hp : p≤x.length) :
    ∀ k, valAt (tblV (source R rs) x s k i E) p=valAt (tblV (source R rs) x s k i F) p
  | 0 => rfl
  | k+1 => by
    rw [valAt_tblV_succ (source_rule R rs i r hr) E hp,valAt_tblV_succ (source_rule R rs i r hr) F hp]
    exact physical_environment_congr _ x s k R E F hv r.body p hp

namespace Examples
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def region := [['a','b']]
def specs : List Rule := [⟨1,.replay 0⟩,⟨1,.replay 0⟩]
def nestedActual : Expr := .call 0 [.call 1 [.seq (.notP (.replay 0)) (.lit ['a'])]]

theorem actual_parent_dependent_capture :
    evParArgs (source region specs) ['a','b'] .callByValuePar
      (tblV (source region specs) ['a','b'] .callByValuePar 2) [['a','a','b','b']]
      (renderArgs region none [.call 1 [.seq (.notP (.replay 0)) (.lit ['a'])]]) 2=some (some [['a']]) := by decide +kernel

theorem dependent_nested_runs :
    evV (source region specs) ['a','b'] .callByValuePar
      (tblV (source region specs) ['a','b'] .callByValuePar 2) [['a','a','b','b']]
      (render region none nestedActual) 2=some (some 1) ∧
    evV (source region specs) ['a','b'] .callByValuePar
      (tblV (source region specs) ['a','b'] .callByValuePar 2) []
      (render region (some [none]) nestedActual) 2=some (some 1) ∧
    evV (source region specs) ['a','b'] .callByValuePar
      (tblV (source region specs) ['a','b'] .callByValuePar 2) [['a','b']]
      (render region none nestedActual) 2=some none := by decide +kernel

/-- Two different long parent values agree at every physical clock, while
short ab changes the actual's negative replay result in the direct run. -/
theorem different_other_parents (k : Nat) :
    evV (source region specs) ['a','b'] .callByValuePar
      (tblV (source region specs) ['a','b'] .callByValuePar k) [['a','a','b','b']]
      (render region none nestedActual) 2=
    evV (source region specs) ['a','b'] .callByValuePar
      (tblV (source region specs) ['a','b'] .callByValuePar k) [['b','b','a','a']]
      (render region none nestedActual) 2 :=
  physical_environment_congr _ _ _ k region _ _ (by decide +kernel) nestedActual 2 (by decide)

end Examples

end Shallot.MacroPeg.CBV.FiniteSuffixDependentView
