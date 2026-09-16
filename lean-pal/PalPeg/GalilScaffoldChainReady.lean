import PalPeg.GalilScaffoldChainCredits

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainReady
open GalilScaffoldCounter GalilScaffoldChainCredits

/-- Complete decoded preparation witness, including start/done assertions
and all matched updates. It assumes uninterrupted enabled preparation. -/
def Prepared (p : GalilScaffoldPlace.Place) (answer : GalilScaffoldTape.Tape)
    (radius : Counter) (h : ℕ) (sm dm : Bool) (bs cs : List Bool) : Prop :=
  ∃ center u q ys b copied final,
    GalilScaffoldPlace.read p = some center ∧
    PacedCopy ⟨answer,reset,p,GalilScaffoldChainPeriod.start center,
      step (start radius) (false,sm)⟩ bs
      ⟨u,ofNat h,q,GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start center)
        (ys ++ [b]),copied⟩ ∧
    u.focus = 4 ∧ positive (ofNat h) = true ∧
    (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start center)
      (ys ++ [b])).focus = .plain b ∧
    PacedBack (GalilScaffoldChainPeriod.write
      (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start center) (ys ++ [b])) (.last b))
      (step copied (false,dm)) cs
      (GalilScaffoldChainPeriod.moveRight ⟨[], .first center,
        ys.map GalilScaffoldChainPeriod.Token.plain ++ [.last b]⟩) final ∧
    Canonical final.margin ∧ Canonical final.lag ∧ zero final.lag = false ∧
    value final.margin = value radius - 4*(h : ℤ) + ((sm :: (bs ++ dm :: cs)).count true : ℤ) ∧
    value final.lag = value radius + ((sm :: (bs ++ dm :: cs)).count true : ℤ) ∧
    ys ++ [b] = ((GalilScaffoldPlace.stream p).drop 1).take h ∧
    GalilScaffoldPlace.stream q = (GalilScaffoldPlace.stream p).drop h

theorem found_prepared
    {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ}
    (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run)
    (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (radius : Counter) (hc : Canonical radius) (hp : 0 < value radius) :
    ∃ h, GalilDpCorrect.Candidate w lower h ∧
      ∀ (sm dm : Bool) (bs cs : List Bool), bs.length = h → cs.length = h+1 →
        Prepared p (y.config.tapes 11) radius h sm dm bs cs := by
  obtain ⟨h,center,u,q,ys,b,hcand,hread,hcopy,hleft,hpositive,hplain,hback,hxs,hq⟩ :=
    GalilScaffoldChainPeriod.found_start_back p hw hr hs ht hv
  refine ⟨h,hcand,?_⟩
  intro sm dm bs cs hb hcs
  obtain ⟨copied,final,hrcopy,hrback,heq,hm,hl,hzero⟩ :=
    prepare_paced hcopy b hback radius hc hp sm dm bs cs hb hcs
  have hvalues := prep_value radius sm dm bs cs
  dsimp only at hvalues
  rw [← heq, hb] at hvalues
  exact ⟨center,u,q,ys,b,copied,final,hread,hrcopy,hleft,hpositive,hplain,
    hrback,hm,hl,hzero,hvalues.1,hvalues.2,hxs,hq⟩

#print axioms found_prepared
end PalPeg.GalilScaffoldChainReady
