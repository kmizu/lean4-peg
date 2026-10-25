import MacroPeg.CBV.DelimitedCopyEvaluation
import MacroPeg.CBV.ScannerPairFusion

namespace Shallot.MacroPeg.CBV.DelimitedCopyCompiler
open DelimitedCopySyntax

/-- Closed control may interleave, repeat, negate or choose copy blocks.
Their independent actuals are arbitrary checked nullary recursive parsers. -/
inductive Term where
  | eps | any | chr (c : Char) | range (a b : Char) | lit (w : List Char)
  | helper (i : Nat) | copy (a b : MExp)
  | seq (a b : Term) | alt (a b : Term) | notP (a : Term) | star (a : Term)

def render (bodies : List MExp) (parallel : Bool) : Term → MExp
  | .eps => .eps | .any => .any | .chr c => .chr c | .range a b => .range a b | .lit w => .lit w
  | .helper i => .call i []
  | .copy a b => if parallel then root bodies a b else targetRoot bodies a b
  | .seq a b => .seq (render bodies parallel a) (render bodies parallel b)
  | .alt a b => .alt (render bodies parallel a) (render bodies parallel b)
  | .notP a => .notP (render bodies parallel a)
  | .star a => .star (render bodies parallel a)

def termCheck (bodies : List MExp) (alphabet : List Char) (d : Char) : Term → Bool
  | .helper i => decide (i<bodies.length)
  | .copy a b => DelimitedCopySyntax.check bodies alphabet d a b
  | .seq a b | .alt a b => termCheck bodies alphabet d a && termCheck bodies alphabet d b
  | .notP a | .star a => termCheck bodies alphabet d a
  | _ => true

theorem render_firstOrder (bodies : List MExp) (alphabet : List Char) (d : Char) (parallel : Bool) :
    ∀ e, termCheck bodies alphabet d e=true → (render bodies parallel e).FirstOrder
  | .helper _,_ | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ => True.intro
  | .copy a b,hc => by
    have hh := DelimitedCopySyntax.checked bodies alphabet d a b hc
    have ha := RecursiveParserStability.lexical_firstOrder _ a hh.left
    have hb := RecursiveParserStability.lexical_firstOrder _ b hh.right
    cases parallel with
    | true => exact root_firstOrder bodies a b ha hb
    | false => exact targetRoot_firstOrder bodies a b ha hb
  | .seq a b,hc | .alt a b,hc =>
    ⟨render_firstOrder bodies alphabet d parallel a (Bool.and_eq_true_iff.mp hc).1,
      render_firstOrder bodies alphabet d parallel b (Bool.and_eq_true_iff.mp hc).2⟩
  | .notP a,hc | .star a,hc => render_firstOrder bodies alphabet d parallel a hc

theorem expression_physical (bodies : List MExp) (alphabet : List Char) (d : Char)
    (hb : RecursiveParserStability.Valid bodies) (x : List Char) (k : Nat) :
    ∀ e, termCheck bodies alphabet d e=true → ∀ p, p≤x.length →
    evV (source bodies d) x .callByValuePar (tblV (source bodies d) x .callByValuePar k) [] (render bodies true e) p=
      evV (target bodies d) x .callByValueSeq (tblV (target bodies d) x .callByValueSeq k) [] (render bodies false e) p
  | .helper i,hc,p,hp => queries_eq bodies d hb (.call i []) (show i<bodies.length from of_decide_eq_true (show decide (i<bodies.length)=true from hc)) x k p hp
  | .copy a b,hc,p,hp => DelimitedCopyEvaluation.physical bodies alphabet d a b (DelimitedCopySyntax.checked _ _ _ _ _ hc) x k p hp
  | .seq a b,hc,p,hp => by
    have ha := expression_physical bodies alphabet d hb x k a (Bool.and_eq_true_iff.mp hc).1 p hp
    cases hv : evV (source bodies d) x .callByValuePar (tblV (source bodies d) x .callByValuePar k) [] (render bodies true a) p with
    | none => simp only [render,evV_seq_none hv,evV_seq_none (ha.symm.trans hv)]
    | some v => cases v with
      | none => simp only [render,evV_seq_fail hv,evV_seq_fail (ha.symm.trans hv)]
      | some q =>
        simp only [render,evV_seq_ok hv,evV_seq_ok (ha.symm.trans hv)]
        exact expression_physical bodies alphabet d hb x k b (Bool.and_eq_true_iff.mp hc).2 q (evV_ok (tblV_ok _ _ _ k) _ p hp q hv)
  | .alt a b,hc,p,hp => by
    have ha := expression_physical bodies alphabet d hb x k a (Bool.and_eq_true_iff.mp hc).1 p hp
    cases hv : evV (source bodies d) x .callByValuePar (tblV (source bodies d) x .callByValuePar k) [] (render bodies true a) p with
    | none => simp only [render,evV_alt_none hv,evV_alt_none (ha.symm.trans hv)]
    | some v => cases v with
      | none =>
        simp only [render,evV_alt_fail hv,evV_alt_fail (ha.symm.trans hv)]
        exact expression_physical bodies alphabet d hb x k b (Bool.and_eq_true_iff.mp hc).2 p hp
      | some q => simp only [render,evV_alt_ok hv,evV_alt_ok (ha.symm.trans hv)]
  | .notP a,hc,p,hp => by simp only [render,evV,expression_physical bodies alphabet d hb x k a hc p hp]
  | .star a,hc,p,hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => expression_physical bodies alphabet d hb x k a hc q (by omega))
  | .eps,_,_,_ | .any,_,_,_ | .chr _,_,_,_ | .range _ _,_,_,_ | .lit _,_,_,_ => rfl

/-- All actual declarations, the complete root, dependency ranges and
positive capture alphabets are checked by finite computations. -/
def check (g : MGrammar) (start : MExp) (bodies : List MExp) (alphabet : List Char) (d : Char) (e : Term) : Bool :=
  bodies.all (lexicalCheck bodies.length) && FiniteSuffixCallCompiler.sameRules g.rules (source bodies d).rules &&
    MExp.beqE start (render bodies true e) && termCheck bodies alphabet d e

theorem checked (g : MGrammar) (start : MExp) (bodies : List MExp) (alphabet : List Char) (d : Char) (e : Term)
    (hc : check g start bodies alphabet d e=true) :
    RecursiveParserStability.Valid bodies ∧ g=source bodies d ∧ start=render bodies true e ∧ termCheck bodies alphabet d e=true := by
  simp only [check,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hb,hg⟩,hs⟩,he⟩ := hc
  have hg := FiniteSuffixCallCompiler.sameRules_checked _ _ hg
  refine ⟨fun b h => lexical_checked _ b (List.all_eq_true.mp hb b h),?_,(MExp.beqE_iff _ _).mp hs,he⟩
  cases g
  simp_all

theorem physical (g : MGrammar) (start : MExp) (bodies : List MExp) (alphabet : List Char) (d : Char) (e : Term)
    (hc : check g start bodies alphabet d e=true) (x : List Char) (k : Nat) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=
      evV (target bodies d) x .callByValueSeq (tblV (target bodies d) x .callByValueSeq k) [] (render bodies false e) x.length := by
  obtain ⟨hb,hg,hs,he⟩ := checked g start bodies alphabet d e hc
  rw [hg,hs]
  exact expression_physical bodies alphabet d hb x k e he _ (Nat.le_refl _)

theorem observations_iff (g : MGrammar) (start : MExp) (bodies : List MExp) (alphabet : List Char) (d : Char) (e : Term)
    (hc : check g start bodies alphabet d e=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar start x rest ↔ SObs (target bodies d) .callByValueSeq (render bodies false e) x rest := by
  obtain ⟨hb,hg,hs,he⟩ := checked g start bodies alphabet d e hc
  rw [hg,hs]
  rw [←decideObsV_iff (source_firstOrder bodies d hb) (by decide) (render_firstOrder bodies alphabet d true e he),
    ←decideObsV_iff (target_firstOrder bodies d hb) (by decide) (render_firstOrder bodies alphabet d false e he)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => expression_physical bodies alphabet d hb x k e he _ (Nat.le_refl _))]

theorem language_translation (g : MGrammar) (start : MExp) (bodies : List MExp) (alphabet : List Char) (d : Char) (e : Term)
    (hc : check g start bodies alphabet d e=true) :
    (fun x => SObs g .callByValuePar start x (some []))=
      (fun x => SObs (target bodies d) .callByValueSeq (render bodies false e) x (some [])) := by
  funext x
  exact propext (observations_iff g start bodies alphabet d e hc x (some []))

theorem defined_iff (g : MGrammar) (start : MExp) (bodies : List MExp) (alphabet : List Char) (d : Char) (e : Term)
    (hc : check g start bodies alphabet d e=true) (x : List Char) (v : Option Nat) :
    (∃ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=some v) ↔
      ∃ k, evV (target bodies d) x .callByValueSeq (tblV (target bodies d) x .callByValueSeq k) [] (render bodies false e) x.length=some v := by
  constructor
  · rintro ⟨k,hk⟩; exact ⟨k,(physical g start bodies alphabet d e hc x k).symm.trans hk⟩
  · rintro ⟨k,hk⟩; exact ⟨k,(physical g start bodies alphabet d e hc x k).trans hk⟩

theorem undefined_iff (g : MGrammar) (start : MExp) (bodies : List MExp) (alphabet : List Char) (d : Char) (e : Term)
    (hc : check g start bodies alphabet d e=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=none) ↔
      ∀ k, evV (target bodies d) x .callByValueSeq (tblV (target bodies d) x .callByValueSeq k) [] (render bodies false e) x.length=none := by
  constructor
  · intro h k; rw [←physical g start bodies alphabet d e hc x k]; exact h k
  · intro h k; rw [physical g start bodies alphabet d e hc x k]; exact h k

end Shallot.MacroPeg.CBV.DelimitedCopyCompiler
