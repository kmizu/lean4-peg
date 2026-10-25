import MacroPeg.CBV.OriginTailInlining
import MacroPeg.CBV.OriginHeadRawCompiler

namespace Shallot.MacroPeg.CBV.OriginTailRawCompiler
open MultiplyingPrefixCompiler (Spec source sourceBody source_rule)
open ReplayControlFusion (Part Plan)

export OriginHeadRawCompiler (parts entries prepared prepared_related prepared_firstOrder)
abbrev target (rs : List Spec) (i : Nat) (r : Spec) (P : Plan) := OriginTailInlining.target (parts rs) (entries rs) i r P
abbrev render (rs : List Spec) (i : Nat) (r : Spec) (P : Plan) := OriginTailInlining.render (parts rs) (entries rs) i r P
abbrev check (rs : List Spec) (i : Nat) := OriginTailInlining.check (parts rs) (entries rs) i

theorem observations_iff (rs : List Spec) (i : Nat) (r : Spec) (P : Plan)
    (hi : (entries rs)[i]?=some (.growth r)) (hj : (entries rs)[r.callee]?=some (.origin P))
    (hg : (source rs).FirstOrder) (hc : check rs i=true)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (source rs) .callByValuePar e x rest ↔
      SObs (target rs i r P) .callByValueSeq (render rs i r P e) x rest :=
  (FiniteBodyRewrite.observations (prepared_related rs hg) hg (prepared_firstOrder rs hg) (by decide) e he x rest).trans
    (OriginTailInlining.observations_iff _ _ i r P hi hj (prepared_firstOrder rs hg) hc e he x rest)

theorem undefined_iff (rs : List Spec) (i : Nat) (r : Spec) (P : Plan)
    (hi : (entries rs)[i]?=some (.growth r)) (hj : (entries rs)[r.callee]?=some (.origin P))
    (hg : (source rs).FirstOrder) (hc : check rs i=true) (e : MExp) (he : e.FirstOrder) (x : List Char) :
    (∀ k, evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) [] e x.length=none) ↔
      (∀ k, evV (target rs i r P) x .callByValueSeq (tblV (target rs i r P) x .callByValueSeq k) [] (render rs i r P e) x.length=none) :=
  (FiniteBodyRewrite.undefined_iff (prepared_related rs hg) x [] e x.length).trans
    (OriginTailInlining.undefined_iff _ _ i r P hi hj (prepared_firstOrder rs hg) hc e he x)

theorem language_translation (rs : List Spec) (i : Nat) (r : Spec) (P : Plan)
    (hi : (entries rs)[i]?=some (.growth r)) (hj : (entries rs)[r.callee]?=some (.origin P))
    (hg : (source rs).FirstOrder) (hc : check rs i=true) (e : MExp) (he : e.FirstOrder) :
    ∃ (g : MGrammar) (entry : MExp), g.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs (source rs) .callByValuePar e x (some []) ↔ SObs g .callByValueSeq entry x (some []) :=
  ⟨target rs i r P,render rs i r P e,MixedForwardingCompiler.target_firstOrder _ _,MixedForwardingCompiler.render_firstOrder _ _ e,
    fun x => observations_iff rs i r P hi hj hg hc e he x (some [])⟩

end Shallot.MacroPeg.CBV.OriginTailRawCompiler
