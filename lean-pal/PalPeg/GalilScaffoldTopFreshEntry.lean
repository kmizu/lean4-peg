import PalPeg.GalilScaffoldTopRoundBreak

/-!
# The read origin of the first shift

The first (fresh) shift of a watching chain, as `scan_prediction_shift`
analyses it, yields a read origin whose `Entry` holds at the state after the
shift. Here the shift is the one the actual machine performs (a given
`ChainShiftRun` with the same start), identified with the analysed one by
`chain_shift_unique`; the resulting `Entry` is what `rounds_lift` /
`rounds_break` carry across the subsequent rounds.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldChainVerifier

theorem fresh_shift_entry {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t)
    (a : Fin 2) (ls suffix : List (Fin 2)) (gap : Bool)
    (w : List (Fin 3)) (span lower radius : ℕ) (c b : Fin 3) (xs : List (Fin 3))
    (hw : w = (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take span)
    (hc : GalilDpCorrect.Candidate w lower (xs.length+1))
    (hh : GalilScaffoldInputTrace.Represents s.machine.verifier.head ((a :: ls).reverse ++ suffix))
    (hp : s.machine.verifier.head.focus ≠ none)
    (hs : s.machine.control = GalilScaffoldChainConsume.ready c xs b)
    (hstart : position s.machine.verifier =
      if gap then 2*(ls.length+1) else 2*(ls.length+1)-1)
    (l outer : PlaceHead)
    (hi : ScanInvariant ((a :: ls).reverse ++ suffix) (position s.machine.verifier) radius l outer)
    (hphase : t.machine.control.phase = 4)
    (initialRadius : ℕ) (hlag : GalilScaffoldCounter.value s.lag = initialRadius)
    (hzero : GalilScaffoldCounter.zero t.lag = true)
    (hcount : initialRadius+bs.count true = radius)
    (hcan : canRight outer) (predicted : Fin 3)
    (hpred : GalilScaffoldChainConsume.symbol t.machine.control.period.focus = some predicted)
    (hread : GalilScaffoldInputHead.read (right outer) = some predicted)
    (radiusCounter lengthCounter : GalilScaffoldCounter.Counter)
    (hcounter : GalilScaffoldCounter.value radiusCounter = (radius : ℤ)+1)
    (hrcanon : GalilScaffoldCounter.Canonical radiusCounter)
    (hlcanon : GalilScaffoldCounter.Canonical lengthCounter)
    (prepRadius : GalilScaffoldCounter.Counter)
    (hprepCanonical : GalilScaffoldCounter.Canonical prepRadius)
    (startMatch doneMatch : Bool) (copyMatches backMatches : List Bool)
    (hcopyLength : copyMatches.length = xs.length+1)
    (hprepLag : s.lag = (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start prepRadius)
      (GalilScaffoldChainCredits.prepEvents startMatch doneMatch copyMatches backMatches)).lag)
    (hprepMargin : s.margin = (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start prepRadius)
      (GalilScaffoldChainCredits.prepEvents startMatch doneMatch copyMatches backMatches)).margin)
    (hmismatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) ≠
      GalilScaffoldInputHead.read (right outer))
    {endpoint : ShiftState} {watchEnd : GalilScaffoldChainWatch.State}
    {cycleEnd : GalilScaffoldCounter.Counter}
    (hchain : ChainShiftRun ⟨s.machine.verifier,GalilScaffoldInputHead.left l,
        GalilScaffoldCounter.ofNat (xs.length+1),radiusCounter,lengthCounter⟩
        (GalilScaffoldChainWatch.immediate t) GalilScaffoldCounter.reset (xs.length+1)
        endpoint watchEnd cycleEnd) :
    ∃ o : ReadOrigin ((a :: ls).reverse ++ suffix),
      Entry ((a :: ls).reverse ++ suffix) o
        ⟨endpoint.center,endpoint.left,right outer,watchEnd,cycleEnd,endpoint.radius⟩ ∧
      o.interior.length+1 = xs.length+1 ∧ o.center = position s.machine.verifier ∧
      o.radius = radius ∧ o.shifts = 0 ∧
      GalilScaffoldInputHead.read endpoint.center ≠ none := by
  obtain ⟨_,endpoint0,watchEnd0,cycleEnd0,hshift,hchain0,_,_,_,hscan,hcredit,hrad,_,_,hcen,origin,
      hostart,howatched,hoshifted,_,horesume,hointerior,hosteps,_,hocenter,horadius,hd,_⟩ :=
    scan_prediction_shift hr a ls suffix gap w span lower radius c b xs hw hc hh hp hs hstart
      l outer hi hphase initialRadius hlag hzero hcount hcan predicted hpred hread
      radiusCounter lengthCounter hcounter hrcanon hlcanon prepRadius hprepCanonical
      startMatch doneMatch copyMatches backMatches hcopyLength hprepLag hprepMargin hmismatch
  obtain ⟨he1,he2,he3⟩ := chain_shift_unique hchain0 hchain
  subst he1; subst he2; subst he3
  have hsteps' : origin.steps = origin.interior.length+1 := by rw [hosteps,hointerior]
  have hd' : 4*(origin.interior.length+1) ≤
      GalilScaffoldCounter.value origin.watched.machine.control.distance := by
    rw [hointerior,howatched]; exact hd
  have hrun' : ShiftRun ⟨origin.start.machine.verifier,GalilScaffoldInputHead.left l,
      GalilScaffoldCounter.ofNat (origin.interior.length+1),radiusCounter,lengthCounter⟩
      (origin.interior.length+1) endpoint0 := by
    rw [hostart,hointerior]; exact hshift
  have hscan' : OnlyScan ((a :: ls).reverse ++ suffix) (position endpoint0.center)
      (origin.radius+1-(origin.interior.length+1)) (2*(origin.interior.length+1)) 0
      endpoint0.left (right outer) origin.shifted cycleEnd0 := by
    rw [hoshifted,hointerior,horadius]; exact hscan
  have hcredit' : OnlyCredit origin.shifted cycleEnd0 := by rw [hoshifted]; exact hcredit
  have hrad' : RadiusRep endpoint0.radius (origin.radius+1-(origin.interior.length+1)) := by
    rw [hointerior,horadius]; exact hrad
  have hphase' : origin.watched.machine.control.phase = 4 := by
    rw [howatched]
    exact phase_four_consume _ _ hphase
  obtain ⟨o,he,_,hshifts,hinterior,hcenter',hradius'⟩ :=
    entry_of_only origin hsteps' hd' hphase' hrun' hscan' hcredit' hrad' horesume
  rw [hoshifted] at he
  refine ⟨o,he,?_,?_,?_,hshifts,hcen⟩
  · rw [hinterior,hointerior]
  · rw [hcenter',hocenter]
  · rw [hradius',horadius]

#print axioms fresh_shift_entry


/-- `found_rounds_restart`'s entry, for the shift the actual machine performs:
the read origin of the first shift with its `Entry` at the state after it. -/
theorem found_shift_entry {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {as : List Bool}
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool) (cen : PlaceHead)
    (hcen : cen = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some c)
    (span lower : ℕ)
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run)
    (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0
      (GalilScaffoldProgram.denote y.config))
    (radius : GalilScaffoldCounter.Counter) (hrc : GalilScaffoldCounter.Canonical radius)
    (hrp : 0 < GalilScaffoldCounter.value radius) (sm dm : Bool) :
    ∀ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower h →
      ys.length+1 = h →
      ∀ (copyMatches backMatches : List Bool), copyMatches.length = h → backMatches.length = h+1 →
      let final := GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
        (GalilScaffoldChainCredits.prepEvents sm dm copyMatches backMatches)
      let s0 := watchStart cen c ys b final
      ∀ {t' : GalilScaffoldChainWatch.State} {bs : List Bool}
        (hrun : GalilScaffoldChainWatch.Run s0 bs t') (hphase : t'.machine.control.phase = 4)
        (initialRadius scanRadius : ℕ)
        (hlag : GalilScaffoldCounter.value s0.lag = initialRadius)
        (hzero : GalilScaffoldCounter.zero t'.lag = true)
        (hcount : initialRadius+bs.count true = scanRadius)
        (l outer : PlaceHead)
        (hi : ScanInvariant ((a :: ls).reverse ++ (rs ++ q)) (position cen) scanRadius l outer)
        (hcan : canRight outer) (predicted : Fin 3)
        (hpred : GalilScaffoldChainConsume.symbol t'.machine.control.period.focus = some predicted)
        (hread : GalilScaffoldInputHead.read (right outer) = some predicted)
        (radiusCounter lengthCounter : GalilScaffoldCounter.Counter)
        (hcounter : GalilScaffoldCounter.value radiusCounter = (scanRadius : ℤ)+1)
        (hrcanon : GalilScaffoldCounter.Canonical radiusCounter)
        (hlcanon : GalilScaffoldCounter.Canonical lengthCounter)
        (hmismatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) ≠
          GalilScaffoldInputHead.read (right outer)),
      ∀ {endpoint : ShiftState} {watchEnd : GalilScaffoldChainWatch.State}
        {cycleEnd : GalilScaffoldCounter.Counter}
        (hchain : ChainShiftRun ⟨cen,GalilScaffoldInputHead.left l,
          GalilScaffoldCounter.ofNat h,radiusCounter,lengthCounter⟩
          (GalilScaffoldChainWatch.immediate t') GalilScaffoldCounter.reset h
          endpoint watchEnd cycleEnd),
      ∃ o : ReadOrigin ((a :: ls).reverse ++ (rs ++ q)),
        Entry ((a :: ls).reverse ++ (rs ++ q)) o
          ⟨endpoint.center,endpoint.left,right outer,watchEnd,cycleEnd,endpoint.radius⟩ ∧
        o.interior.length+1 = h ∧ o.center = position cen ∧ o.radius = scanRadius ∧
        o.shifts = 0 ∧ GalilScaffoldInputHead.read endpoint.center ≠ none := by
  intro h ys b hcand hys copyMatches backMatches hcl hbl final s0
  intro t' bs hrun hphase initialRadius scanRadius hlag hzero hcount l outer hi hcan predicted
    hpred hread radiusCounter lengthCounter hcounter hrcanon hlcanon hmismatch
    endpoint watchEnd cycleEnd hchain
  have hh : GalilScaffoldInputTrace.Represents s0.machine.verifier.head
      ((a :: ls).reverse ++ (rs ++ q)) := by
    show GalilScaffoldInputTrace.Represents cen.head _
    rw [hcen]
    exact ⟨a :: ls,rs,q,rfl,by simp [List.append_assoc]⟩
  have hp : s0.machine.verifier.head.focus ≠ none := by
    show cen.head.focus ≠ none
    rw [hcen]; simp [represent,layout]
  have hstart : position s0.machine.verifier = if gap then 2*(ls.length+1) else 2*(ls.length+1)-1 := by
    show position cen = _
    rw [hcen,position_represent,stream_length]
    cases gap <;> simp <;> omega
  have hpos : position s0.machine.verifier = position cen := rfl
  have hcand' : GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1))
      lower (ys.length+1) := by rw [hys]; exact hcand
  have hcl' : copyMatches.length = ys.length+1 := by rw [hcl,hys]
  have hi' : ScanInvariant ((a :: ls).reverse ++ (rs ++ q)) (position s0.machine.verifier)
      scanRadius l outer := by rw [hpos]; exact hi
  have hchain' : ChainShiftRun ⟨s0.machine.verifier,GalilScaffoldInputHead.left l,
      GalilScaffoldCounter.ofNat (ys.length+1),radiusCounter,lengthCounter⟩
      (GalilScaffoldChainWatch.immediate t') GalilScaffoldCounter.reset (ys.length+1)
      endpoint watchEnd cycleEnd := by
    rw [hys]; exact hchain
  have := fresh_shift_entry hrun a ls (rs ++ q) gap _ (span+1) lower scanRadius c b ys rfl hcand'
    hh hp rfl hstart l outer hi' hphase initialRadius hlag hzero hcount hcan predicted hpred hread
    radiusCounter lengthCounter hcounter hrcanon hlcanon radius hrc sm dm copyMatches backMatches
    hcl' (by simp [s0,watchStart,final]) (by simp [s0,watchStart,final]) hmismatch hchain'
  rw [hys] at this
  exact this

#print axioms found_shift_entry

end PalPeg.GalilScaffoldChainInputSupply
