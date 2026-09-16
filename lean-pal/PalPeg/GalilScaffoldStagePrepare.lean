import PalPeg.GalilScaffoldPrepareControl
import PalPeg.GalilScaffoldGrow
import PalPeg.GalilScaffoldPreparePaced
import PalPeg.GalilScaffoldAdvanceClock
import PalPeg.GalilScaffoldSearchRun
import PalPeg.GalilScaffoldDouble
import PalPeg.GalilScaffoldWaitInterrupt

set_option autoImplicit false
namespace PalPeg.GalilScaffoldStagePrepare
open GalilScaffoldPrepareControl
open GalilScaffoldCounter

theorem add_ofNat (k n : ℕ) : GalilScaffoldGrow.add k (ofNat n) = ofNat (n+k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change inc (GalilScaffoldGrow.add k (ofNat n)) = _
    rw [ih,inc_ofNat]
    rfl

def growStep (s : State) : State :=
  {s with work := dec s.work,span := GalilScaffoldGrow.add 8 s.span,debt := GalilScaffoldGrow.add 2 s.debt}

/-- Only positive grow ticks; the zero test belongs to prepare's dispatch. -/
inductive Growing : State → ℕ → State → Prop
  | stop (s : State) (hm : s.mode = .grow) (hz : positive s.work = false) : Growing s 0 s
  | next (s t : State) (n : ℕ) (hm : s.mode = .grow) (hp : positive s.work = true)
      (hr : Growing (growStep s) n t) : Growing s (n+1) t

theorem growing_complete (s : State) (g span : ℕ) (hm : s.mode = .grow)
    (hw : s.work = ofNat g) (hs : s.span = ofNat span) :
    ∃ t, Growing s g t ∧ t.mode = .grow ∧ t.work = ofNat 0 ∧
      t.span = ofNat (span+8*g) ∧ value t.debt = value s.debt+2*g := by
  induction g generalizing s span with
  | zero =>
    refine ⟨s,.stop s hm (by simp [hw,positive,ofNat]),hm,hw,?_,?_⟩ <;> simpa using hs
  | succ g ih =>
    obtain ⟨t,hr,htm,htw,hts,htd⟩ := ih (growStep s) (span+8) hm
      (by simp [growStep,hw,dec_ofNat_succ]) (by simp [growStep,hs,add_ofNat])
    refine ⟨t,.next s t g hm (by simp [hw,positive,ofNat,List.replicate_succ]) hr,
      htm,htw,?_,?_⟩
    · convert hts using 1 <;> congr 1 <;> omega
    · simp only [growStep,GalilScaffoldGrow.add_value] at htd
      push_cast
      omega

/-- A grow run reaches the real zero-work prepare boundary and then uses
the same controller state for the full preparation. No advance interleaving yet. -/
theorem grow_then_prepare (s : State) (g span lower : ℕ) (center : GalilScaffoldPlace.Place)
    (hm : s.mode = .grow) (hw : s.work = ofNat g) (hs : s.span = ofNat span) :
    let w := (GalilScaffoldPlace.stream center).take (span+8*g+1)
    ∃ u t, Growing s g u ∧ u.mode = .grow ∧ positive u.work = false ∧
      PreparedRun (ofNat lower) center u (2*lower+2*w.length+7) t ∧
      t.mode = .run ∧ t.program.config = GalilScaffoldPreload.initial w lower ∧
      t.program.done = false ∧ value t.debt = value s.debt+2*g ∧
      (t.finalStage = true ↔ (GalilScaffoldPlace.stream center).length ≤ span+8*g+1) := by
  obtain ⟨u,hg,hum,huw,hus,hud⟩ := growing_complete s g span hm hw hs
  obtain ⟨t,hp,htm,htp,htd,htdebt,htf⟩ := prepare_complete u lower (span+8*g) center hus
  exact ⟨u,t,hg,hum,by simp [huw,positive,ofNat],hp,htm,htp,htd,htdebt ▸ hud,htf⟩

inductive PacedGrowing : State → List Bool → State → Prop
  | stop (s : State) (hm : s.mode = .grow) (hz : positive s.work = false) :
      PacedGrowing s [] s
  | next (s t : State) (a : Bool) (as : List Bool)
      (hm : s.mode = .grow) (hp : positive s.work = true)
      (hr : PacedGrowing (GalilScaffoldPreparePaced.afterAdvance a (growStep s)) as t) :
      PacedGrowing s (a :: as) t

theorem paced_growing_canonical {s t : State} {as : List Bool}
    (hr : PacedGrowing s as t) (hc : Canonical s.debt) : Canonical t.debt := by
  induction hr with
  | stop => exact hc
  | next s t a as hm hp hr ih =>
    apply ih
    have h := GalilScaffoldGrow.add_canonical 2 s.debt hc
    cases a
    · exact h
    · exact dec_canonical _ h

theorem paced_growing_complete (as : List Bool) (s : State) (span : ℕ)
    (hm : s.mode = .grow) (hw : s.work = ofNat as.length) (hs : s.span = ofNat span) :
    ∃ t, PacedGrowing s as t ∧ t.mode = .grow ∧ t.work = ofNat 0 ∧
      t.span = ofNat (span+8*as.length) ∧
      value t.debt = value s.debt+2*as.length-as.count true := by
  induction as generalizing s span with
  | nil =>
    refine ⟨s,.stop s hm (by simp [hw,positive,ofNat]),hm,hw,?_,?_⟩
    · simpa using hs
    · simp
  | cons a as ih =>
    have hmode : (GalilScaffoldPreparePaced.afterAdvance a (growStep s)).mode = .grow := by
      cases a <;> simpa [GalilScaffoldPreparePaced.afterAdvance,growStep] using hm
    have hwork : (GalilScaffoldPreparePaced.afterAdvance a (growStep s)).work = ofNat as.length := by
      cases a <;> simp [GalilScaffoldPreparePaced.afterAdvance,growStep,hw,dec_ofNat_succ]
    have hspan : (GalilScaffoldPreparePaced.afterAdvance a (growStep s)).span = ofNat (span+8) := by
      cases a <;> simp [GalilScaffoldPreparePaced.afterAdvance,growStep,hs,add_ofNat]
    obtain ⟨t,hr,htm,htw,hts,htd⟩ := ih _ (span+8) hmode hwork hspan
    refine ⟨t,.next s t a as hm (by simp [hw,positive,ofNat,List.replicate_succ]) hr,
      htm,htw,?_,?_⟩
    · convert hts using 1 <;> congr 1 <;> simp <;> omega
    · cases a <;> simp [GalilScaffoldPreparePaced.afterAdvance,growStep,
        GalilScaffoldGrow.add_value,dec_value] at htd ⊢ <;> omega

theorem paced_grow_then_prepare (as bs : List Bool) (s : State) (span lower : ℕ)
    (center : GalilScaffoldPlace.Place) (hm : s.mode = .grow)
    (hw : s.work = ofNat as.length) (hs : s.span = ofNat span)
    (hb : bs.length = 2*lower+2*((GalilScaffoldPlace.stream center).take
      (span+8*as.length+1)).length+7) :
    let w := (GalilScaffoldPlace.stream center).take (span+8*as.length+1)
    ∃ u t, PacedGrowing s as u ∧ u.mode = .grow ∧ positive u.work = false ∧
      GalilScaffoldPreparePaced.PacedPrepared (ofNat lower) center u bs t ∧
      t.mode = .run ∧ t.program.config = GalilScaffoldPreload.initial w lower ∧
      t.program.done = false ∧
      value t.debt = value s.debt+2*as.length-(as++bs).count true ∧
      (t.finalStage = true ↔ (GalilScaffoldPlace.stream center).length ≤ span+8*as.length+1) := by
  obtain ⟨u,hg,hum,huw,hus,hud⟩ := paced_growing_complete as s span hm hw hs
  obtain ⟨t,hp,htm,htp,htd,htdebt,htf⟩ := prepare_complete u lower (span+8*as.length) center hus
  have hr := GalilScaffoldPreparePaced.prepared_interleave hp bs hb
  refine ⟨u,{t with debt := GalilScaffoldPreparePaced.spend bs u.debt},hg,hum,
    by simp [huw,positive,ofNat],hr,htm,htp,htd,?_,htf⟩
  simp only [GalilScaffoldPreparePaced.spend_value,List.count_append,Nat.cast_add]
  omega

/-- Clock correspondence and initial radius remain explicit source obligations;
the final debt assertion is derived, not assumed. -/
theorem first_prepared_safe (as bs : List Bool) (es : List (Bool × Bool))
    (s : State) (r radius : ℕ) (center : GalilScaffoldPlace.Place)
    (hm : s.mode = .grow) (hw : s.work = ofNat (max r 1)) (hs : s.span = ofNat 0)
    (hd : value s.debt = -(radius : ℤ)) (hc : Canonical s.debt)
    (ha : as.length = max r 1)
    (hb : bs.length = 2*r+2*((GalilScaffoldPlace.stream center).take (8*max r 1+1)).length+7)
    (he : as++bs = GalilScaffoldAdvanceClock.advances 2048 2048 es)
    (hr : 3*radius ≤ 5*r) (ht : es.length ≤ 63*(8*max r 1)) :
    let w := (GalilScaffoldPlace.stream center).take (8*max r 1+1)
    ∃ u t, PacedGrowing s as u ∧
      GalilScaffoldPreparePaced.PacedPrepared (ofNat r) center u bs t ∧
      t.mode = .run ∧ t.program.config = GalilScaffoldPreload.initial w r ∧
      t.program.done = false ∧ negative t.debt ≠ true := by
  obtain ⟨u,hg,hum,huw,hus,hud⟩ := paced_growing_complete as s 0 hm (by simpa [ha] using hw) hs
  obtain ⟨t,hp,htm,htp,htd,htdebt,htf⟩ := prepare_complete u r (8*max r 1) center (by simpa [ha] using hus)
  have hpaced := GalilScaffoldPreparePaced.prepared_interleave hp bs hb
  have huc := paced_growing_canonical hg hc
  have htc := GalilScaffoldPreparePaced.spend_canonical bs u.debt huc
  refine ⟨u,{t with debt := GalilScaffoldPreparePaced.spend bs u.debt},hg,hpaced,htm,htp,htd,?_⟩
  apply GalilScaffoldAdvanceClock.first_stage_debt r radius es _ hr ht htc
  rw [GalilScaffoldPreparePaced.spend_value]
  have hn : (as++bs).count true = (GalilScaffoldAdvanceClock.advances 2048 2048 es).count true := congrArg (List.count true) he
  simp only [List.count_append] at hn
  rw [ha,hd] at hud
  omega

def runState (s : State) (quarter : Fin 4) : GalilScaffoldSearchFinish.State :=
  ⟨s.mode,s.finalStage,s.span,s.work,s.debt,quarter⟩

/-- A complete first-stage prefix, conditional on actual clock-event correspondence
and the source's initial radius contract. Neither run debt nor stage time is assumed. -/
theorem first_stage_safe (as bs cs : List Bool) (es : List (Bool × Bool))
    (s : State) (r radius : ℕ) (center : GalilScaffoldPlace.Place) (quarter : Fin 4)
    (hm : s.mode = .grow) (hw : s.work = ofNat (max r 1)) (hs : s.span = ofNat 0)
    (hd : value s.debt = -(radius : ℤ)) (hc : Canonical s.debt)
    (ha : as.length = max r 1)
    (hb : bs.length = 2*r+2*((GalilScaffoldPlace.stream center).take (8*max r 1+1)).length+7)
    (hcs : cs.length = GalilScaffoldTimingCost.runBudget (8*max r 1))
    (he : as++bs++cs = GalilScaffoldAdvanceClock.advances 2048 2048 es)
    (hr : 3*radius ≤ 5*r) :
    let w := (GalilScaffoldPlace.stream center).take (8*max r 1+1)
    ∃ u p used rest t v, PacedGrowing s as u ∧
      GalilScaffoldPreparePaced.PacedPrepared (ofNat r) center u bs p ∧
      cs = used++rest ∧
      GalilScaffoldSearchRun.SafeQuanta (runState p quarter) p.program used t ⟨v,true⟩ ∧
      t.mode ≠ .run ∧ GalilDpCorrect.Result w r 0 (GalilScaffoldProgram.denote v) ∧
      value t.debt = -(radius : ℤ)+2*(max r 1 : ℕ)-(as++bs++used).count true ∧
      Canonical t.debt ∧ 0 ≤ value t.debt := by
  let w := (GalilScaffoldPlace.stream center).take (8*max r 1+1)
  have hwl : w.length ≤ 8*max r 1+1 := List.length_take_le _ _
  have hlen : es.length = as.length+bs.length+cs.length := by
    have h := congrArg List.length he
    simpa [List.length_append,GalilScaffoldAdvanceClock.advances_length,Nat.add_assoc] using h.symm
  have htime : es.length ≤ 63*(8*max r 1) := by
    rw [hlen,ha,hb,hcs]
    have h := GalilScaffoldTimingCost.first_stage_ticks r w.length hwl
    dsimp [w] at h
    omega
  have hbar := GalilScaffoldAdvanceClock.first_stage_barrier r radius es hr htime
  have hcount := congrArg (List.count true) he
  simp only [List.count_append] at hcount
  obtain ⟨u,hg,hum,huw,hus,hud⟩ := paced_growing_complete as s 0 hm (by simpa [ha] using hw) hs
  obtain ⟨p,hp,hpm,hpp,hpd,hpdebt,hpf⟩ := prepare_complete u r (8*max r 1) center (by simpa [ha] using hus)
  let p' : State := {p with debt := GalilScaffoldPreparePaced.spend bs u.debt}
  have hprep : GalilScaffoldPreparePaced.PacedPrepared (ofNat r) center u bs p' :=
    GalilScaffoldPreparePaced.prepared_interleave hp bs hb
  have hpc : Canonical p'.debt :=
    GalilScaffoldPreparePaced.spend_canonical bs u.debt (paced_growing_canonical hg hc)
  have hpvalue : value p'.debt = -(radius : ℤ)+2*(max r 1 : ℕ)-(as++bs).count true := by
    dsimp [p']
    rw [GalilScaffoldPreparePaced.spend_value]
    rw [ha,hd] at hud
    simp only [List.count_append,Nat.cast_add]
    omega
  have hbudget : (cs.count true : ℤ) ≤ value (runState p' quarter).debt := by
    change (cs.count true : ℤ) ≤ value p'.debt
    rw [hpvalue]
    simp only [List.count_append,Nat.cast_add]
    omega
  obtain ⟨used,rest,t,v,hused,ht,htm,hv,htdebt,htc,htn⟩ :=
    GalilScaffoldSearchRun.calibrated_quanta_safe w r (8*max r 1) cs hwl hcs
      (runState p' quarter) hpm hpc hbudget
  have hprogram : p'.program = ⟨GalilScaffoldPreload.initial w r,false⟩ := by
    change p.program = _
    calc
      p.program = ⟨p.program.config,p.program.done⟩ := rfl
      _ = _ := by rw [hpp,hpd]
  refine ⟨u,p',used,rest,t,v,hg,hprep,hused,?_,htm,hv,?_,htc,htn⟩
  · rw [hprogram]
    exact ht
  · change value t.debt = _
    change value t.debt = value p'.debt-used.count true at htdebt
    rw [hpvalue] at htdebt
    simpa [List.count_append,Nat.cast_add,sub_sub,add_assoc] using htdebt

/-- Restore controller fields without replacing the retained program or walker. -/
def restoreState (base : State) (s : GalilScaffoldSearchFinish.State) : State :=
  {base with mode := s.mode,work := s.work,span := s.span,debt := s.debt,finalStage := s.finalStage}

theorem restore_runState (base : State) (s : GalilScaffoldSearchFinish.State) :
    runState (restoreState base s) s.quarter = s := by cases s; rfl

theorem double_then_prepare (as bs : List Bool) (s : State) (lower : ℕ)
    (center : GalilScaffoldPlace.Place) (hm : s.mode = .double)
    (hw : s.work = ofNat as.length) (hs : s.span = ofNat 0)
    (hc : Canonical s.debt) (ha : as.length % 4 = 0)
    (hb : bs.length = 2*lower+2*((GalilScaffoldPlace.stream center).take (2*as.length+1)).length+7) :
    let w := (GalilScaffoldPlace.stream center).take (2*as.length+1)
    ∃ u p, GalilScaffoldDouble.Run (runState s 0) as u ∧ u.quarter = 0 ∧
      u.mode = .double ∧ positive u.work = false ∧
      GalilScaffoldPreparePaced.PacedPrepared (ofNat lower) center (restoreState s u) bs p ∧
      p.mode = .run ∧ p.program.config = GalilScaffoldPreload.initial w lower ∧
      p.program.done = false ∧ Canonical p.debt ∧
      value p.debt = value s.debt+as.length/4-(as++bs).count true ∧
      (p.finalStage = true ↔ (GalilScaffoldPlace.stream center).length ≤ 2*as.length+1) := by
  obtain ⟨u,hu,hum,huw,hus⟩ := GalilScaffoldDouble.complete as (runState s 0) 0 hm hw hs
  obtain ⟨huq,hud⟩ := GalilScaffoldDouble.completed_credit hu rfl ha
  have huc := GalilScaffoldDouble.canonical hu hc
  obtain ⟨p,hp,hpm,hpp,hpd,hpdebt,hpf⟩ := prepare_complete (restoreState s u) lower (2*as.length) center
    (by simpa [restoreState] using hus)
  have hprep := GalilScaffoldPreparePaced.prepared_interleave hp bs hb
  refine ⟨u,{p with debt := GalilScaffoldPreparePaced.spend bs u.debt},hu,huq,hum,
    by simp [huw,positive,ofNat],hprep,hpm,hpp,hpd,
    GalilScaffoldPreparePaced.spend_canonical bs u.debt huc,?_,hpf⟩
  simp only [GalilScaffoldPreparePaced.spend_value,List.count_append,Nat.cast_add]
  change value u.debt = value s.debt+as.length/4-as.count true at hud
  omega

/-- Later-stage execution with a non-reset clock. The source must still supply
the actual event correspondence and the double-entry invariants. -/
theorem later_stage_safe (as bs cs : List Bool) (es : List (Bool × Bool))
    (s : State) (lower clock : ℕ) (center : GalilScaffoldPlace.Place)
    (hm : s.mode = .double) (hw : s.work = ofNat as.length) (hs : s.span = ofNat 0)
    (hc : Canonical s.debt) (hd : 0 ≤ value s.debt ∨ (-1 ≤ value s.debt ∧ clock = 2048))
    (ha : as.length % 4 = 0) (hn : 8 ≤ as.length) (hl : 4*lower ≤ as.length)
    (hb : bs.length = 2*lower+2*((GalilScaffoldPlace.stream center).take (2*as.length+1)).length+7)
    (hcs : cs.length = GalilScaffoldTimingCost.runBudget (2*as.length))
    (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    (he : as++bs++cs = GalilScaffoldAdvanceClock.advances 2048 clock es) :
    let w := (GalilScaffoldPlace.stream center).take (2*as.length+1)
    ∃ u p used rest t v, GalilScaffoldDouble.Run (runState s 0) as u ∧ u.quarter = 0 ∧
      GalilScaffoldPreparePaced.PacedPrepared (ofNat lower) center (restoreState s u) bs p ∧
      cs = used++rest ∧
      GalilScaffoldSearchRun.SafeQuanta (runState p u.quarter) p.program used t ⟨v,true⟩ ∧
      t.mode ≠ .run ∧ GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote v) ∧
      value t.debt = value s.debt+as.length/4-(as++bs++used).count true ∧
      Canonical t.debt ∧ 0 ≤ value t.debt := by
  let w := (GalilScaffoldPlace.stream center).take (2*as.length+1)
  have hwl : w.length ≤ 2*as.length+1 := List.length_take_le _ _
  have hlen : es.length = as.length+bs.length+cs.length := by
    have h := congrArg List.length he
    simpa [List.length_append,GalilScaffoldAdvanceClock.advances_length,Nat.add_assoc] using h.symm
  have htime : es.length ≤ 63*(2*as.length) := by
    rw [hlen,hb,hcs]
    have h := GalilScaffoldTimingCost.later_stage_ticks as.length lower w.length hn hl hwl
    dsimp [w] at h
    omega
  have hbar := GalilScaffoldAdvanceClock.later_stage_advances (2*as.length) clock es (by omega) hclock htime
  have hcount := congrArg (List.count true) he
  simp only [List.count_append] at hcount
  obtain ⟨u,p,hu,huq,hum,huw,hp,hpm,hpp,hpd,hpc,hpvalue,hpf⟩ :=
    double_then_prepare as bs s lower center hm hw hs hc ha hb
  have hroom : ((GalilScaffoldAdvanceClock.advances 2048 clock es).count true : ℤ) ≤
      value s.debt+as.length/4 := by
    rcases hd with hd | ⟨hd,hreset⟩
    · omega
    · subst clock
      have hbudget := GalilScaffoldAdvanceClock.advances_budget 2048 es (by decide)
      have havail : (es.map Prod.fst).count true ≤ es.length := by
        simpa using List.count_le_length (l := es.map Prod.fst) (a := true)
      omega
  have hbudget : (cs.count true : ℤ) ≤ value (runState p u.quarter).debt := by
    change (cs.count true : ℤ) ≤ value p.debt
    rw [hpvalue]
    simp only [List.count_append,Nat.cast_add]
    omega
  obtain ⟨used,rest,t,v,hused,ht,htm,hv,htdebt,htc,htn⟩ :=
    GalilScaffoldSearchRun.calibrated_quanta_safe w lower (2*as.length) cs hwl hcs
      (runState p u.quarter) hpm hpc hbudget
  have hprogram : p.program = ⟨GalilScaffoldPreload.initial w lower,false⟩ := by
    calc
      p.program = ⟨p.program.config,p.program.done⟩ := rfl
      _ = _ := by rw [hpp,hpd]
  refine ⟨u,p,used,rest,t,v,hu,huq,hp,hused,?_,htm,hv,?_,htc,htn⟩
  · rw [hprogram]; exact ht
  · change value t.debt = value p.debt-used.count true at htdebt
    rw [hpvalue] at htdebt
    simpa [List.count_append,Nat.cast_add,sub_sub,add_assoc] using htdebt

theorem prepared_double_work {lower : Counter} {center : GalilScaffoldPlace.Place}
    {s p : State} {bs cs : List Bool} {q : Fin 4}
    {t : GalilScaffoldSearchFinish.State} {y : GalilScaffoldControl.Machine 12}
    (hp : GalilScaffoldPreparePaced.PacedPrepared lower center s bs p)
    (hr : GalilScaffoldSearchRun.SafeQuanta (runState p q) p.program cs t y)
    (hm : p.mode = .run) (ht : t.mode = .double) : t.work = s.span := by
  exact (GalilScaffoldSearchRun.double_work_of_quanta hr hm ht).trans
    (GalilScaffoldPreparePaced.prepared_span hp)

/-- Numeric preconditions needed at every later double entry. -/
def StageSize (lower n : ℕ) : Prop := 8 ≤ n ∧ n%4 = 0 ∧ 4*lower ≤ n

theorem initial_stage_size (lower : ℕ) : StageSize lower (8*max lower 1) := by
  have h := le_max_left lower 1
  have h1 := le_max_right lower 1
  unfold StageSize
  omega

theorem doubled_stage_size {lower n : ℕ} (h : StageSize lower n) : StageSize lower (2*n) := by
  unfold StageSize at *
  omega

/-- Transfer the later-stage size contract through the actual preparation/run trace. -/
theorem prepared_double_size {lower n : ℕ} {center : GalilScaffoldPlace.Place}
    {s p : State} {bs cs : List Bool} {q : Fin 4}
    {t : GalilScaffoldSearchFinish.State} {y : GalilScaffoldControl.Machine 12}
    (hp : GalilScaffoldPreparePaced.PacedPrepared (ofNat lower) center s bs p)
    (hr : GalilScaffoldSearchRun.SafeQuanta (runState p q) p.program cs t y)
    (hm : p.mode = .run) (ht : t.mode = .double)
    (hs : s.span = ofNat (2*n)) (hn : StageSize lower n) :
    t.work = ofNat (2*n) ∧ StageSize lower (2*n) := by
  exact ⟨(prepared_double_work hp hr hm ht).trans hs,doubled_stage_size hn⟩

theorem double_stage_next_size {lower : ℕ} {center : GalilScaffoldPlace.Place}
    {s p : State} {as bs cs : List Bool}
    {u t : GalilScaffoldSearchFinish.State} {y : GalilScaffoldControl.Machine 12}
    (hd : GalilScaffoldDouble.Run (runState s 0) as u)
    (hp : GalilScaffoldPreparePaced.PacedPrepared (ofNat lower) center (restoreState s u) bs p)
    (hr : GalilScaffoldSearchRun.SafeQuanta (runState p u.quarter) p.program cs t y)
    (hm : p.mode = .run) (ht : t.mode = .double)
    (hs : s.span = ofNat 0) (hn : StageSize lower as.length) :
    t.work = ofNat (2*as.length) ∧ StageSize lower (2*as.length) := by
  have hus := GalilScaffoldDouble.span_of_run hd 0 hs
  apply prepared_double_size hp hr hm ht ?_ hn
  simpa [restoreState] using hus

theorem prepared_wait_double_work {lower : Counter} {center : GalilScaffoldPlace.Place}
    {s p : State} {bs cs : List Bool} {q : Fin 4}
    {u t : GalilScaffoldSearchFinish.State} {y : GalilScaffoldControl.Machine 12}
    {c d : ℕ} {es : List (Bool × Bool)}
    (hp : GalilScaffoldPreparePaced.PacedPrepared lower center s bs p)
    (hr : GalilScaffoldSearchRun.SafeQuanta (runState p q) p.program cs u y)
    (hw : GalilScaffoldWaitInterrupt.Run u c es t d)
    (hm : p.mode = .run) (hu : u.mode = .wait) (ht : t.mode = .double) :
    t.work = s.span := by
  have hframe := (GalilScaffoldSearchRun.safe_quanta_frame hr).2
  have hus : u.span = p.span := by
    simpa [GalilScaffoldSearchRun.stageSpan,runState,hm,hu] using hframe
  exact (GalilScaffoldWaitInterrupt.double_work hw hu ht).trans
    (hus.trans (GalilScaffoldPreparePaced.prepared_span hp))

/-- The complete decoded entry contract for the next later stage. -/
def NextStage (lower n : ℕ) (s : GalilScaffoldSearchFinish.State) (clock : ℕ) : Prop :=
  s.mode = .double ∧ s.work = ofNat n ∧ s.span = ofNat 0 ∧ s.quarter = 0 ∧
    Canonical s.debt ∧ (0 ≤ value s.debt ∨ (-1 ≤ value s.debt ∧ clock = 2048)) ∧
    (1 ≤ clock ∧ clock ≤ 2048) ∧ StageSize lower n

theorem prepared_wait_next {lower n : ℕ} {center : GalilScaffoldPlace.Place}
    {s p : State} {bs cs : List Bool} {q : Fin 4}
    {u : GalilScaffoldSearchFinish.State} {y : GalilScaffoldControl.Machine 12}
    (hp : GalilScaffoldPreparePaced.PacedPrepared (ofNat lower) center s bs p)
    (hr : GalilScaffoldSearchRun.SafeQuanta (runState p q) p.program cs u y)
    (hm : p.mode = .run) (hu : u.mode = .wait)
    (hs : s.span = ofNat n) (hn : StageSize lower n)
    (hc : Canonical u.debt) (hv : 0 ≤ value u.debt)
    (es : List (Bool × Bool)) (clock : ℕ) (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    (hb : ((value u.debt).toNat+1)*2048 ≤ (es.map Prod.fst).count true) :
    ∃ used rest t d, es = used++rest ∧ GalilScaffoldWaitInterrupt.Run u clock used t d ∧
      (t.mode = .idle ∨ NextStage lower n t d) := by
  have hvalue : value u.debt = ((value u.debt).toNat : ℤ) := by omega
  obtain ⟨used,rest,t,d,he,hw,htc,hd,hout,hnotwait⟩ :=
    GalilScaffoldWaitInterrupt.supplied_exit es u clock (value u.debt).toNat hu hc hvalue hclock hb
  refine ⟨used,rest,t,d,he,hw,?_⟩
  rcases hout with hi | hwait | hdouble
  · exact Or.inl hi
  · exact False.elim (hnotwait hwait.1)
  · have hwork := (prepared_wait_double_work hp hr hw hm hu hdouble.1).trans hs
    obtain ⟨hspan,hquarter⟩ := GalilScaffoldWaitInterrupt.double_reset hw hu hdouble.1
    exact Or.inr ⟨hdouble.1,hwork,hspan,hquarter,htc,hdouble.2,hd,hn⟩

/-- Consume NextStage on the exact controller state produced by the previous
boundary. The retained program/walker live in base and are reset by prepare. -/
theorem next_stage_safe (base : State) (s : GalilScaffoldSearchFinish.State)
    (lower n clock : ℕ) (center : GalilScaffoldPlace.Place) (hs : NextStage lower n s clock)
    (as bs cs : List Bool) (es : List (Bool × Bool)) (ha : as.length = n)
    (hb : bs.length = 2*lower+2*((GalilScaffoldPlace.stream center).take (2*n+1)).length+7)
    (hcs : cs.length = GalilScaffoldTimingCost.runBudget (2*n))
    (he : as++bs++cs = GalilScaffoldAdvanceClock.advances 2048 clock es) :
    let w := (GalilScaffoldPlace.stream center).take (2*n+1)
    ∃ u p used rest t v, GalilScaffoldDouble.Run s as u ∧ u.quarter = 0 ∧
      GalilScaffoldPreparePaced.PacedPrepared (ofNat lower) center (restoreState base u) bs p ∧
      cs = used++rest ∧
      GalilScaffoldSearchRun.SafeQuanta (runState p u.quarter) p.program used t ⟨v,true⟩ ∧
      t.mode ≠ .run ∧ GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote v) ∧
      value t.debt = value s.debt+n/4-(as++bs++used).count true ∧
      Canonical t.debt ∧ 0 ≤ value t.debt := by
  obtain ⟨hm,hw,hspan,hq,hc,hd,hclock,hsize⟩ := hs
  obtain ⟨hn,hfour,hl⟩ := hsize
  have h := later_stage_safe as bs cs es (restoreState base s) lower clock center hm
    (by simpa [restoreState,ha] using hw) hspan hc hd
    (by simpa [ha] using hfour) (by simpa [ha] using hn) (by simpa [ha] using hl)
    (by simpa [ha] using hb) (by simpa [ha] using hcs) hclock he
  have hentry : runState (restoreState base s) 0 = s := by
    rw [← hq]
    exact restore_runState base s
  rw [hentry] at h
  simpa only [ha,restoreState] using h

/-- Classify a completed run and consume wait only if needed. Empty wait traces
leave terminal/direct-double states untouched. Fallback remains an explicit exit. -/
theorem prepared_exit {lower n : ℕ} {center : GalilScaffoldPlace.Place}
    {s p : State} {bs cs : List Bool} {q : Fin 4}
    {u : GalilScaffoldSearchFinish.State} {y : GalilScaffoldControl.Machine 12}
    (hp : GalilScaffoldPreparePaced.PacedPrepared (ofNat lower) center s bs p)
    (hr : GalilScaffoldSearchRun.SafeQuanta (runState p q) p.program cs u y)
    (hm : p.mode = .run) (hu : u.mode ≠ .run)
    (hs : s.span = ofNat n) (hn : StageSize lower n)
    (hc : Canonical u.debt) (hv : 0 ≤ value u.debt)
    (es : List (Bool × Bool)) (clock : ℕ) (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    (hb : u.mode = .wait → ((value u.debt).toNat+1)*2048 ≤ (es.map Prod.fst).count true) :
    ∃ used rest t d, es = used++rest ∧ GalilScaffoldWaitInterrupt.Run u clock used t d ∧
      (t.mode = .found ∨ t.mode = .missed ∨ t.mode = .idle ∨ NextStage lower n t d) := by
  have hmode := GalilScaffoldSearchRun.quanta_exit_mode hr hm hu
  rcases hmode with hf | hmiss | hw | hd
  · exact ⟨[],es,u,clock,rfl,.nil _ _,Or.inl hf⟩
  · exact ⟨[],es,u,clock,rfl,.nil _ _,Or.inr (Or.inl hmiss)⟩
  · obtain ⟨used,rest,t,d,he,ht,hout⟩ := prepared_wait_next hp hr hm hw hs hn hc hv es clock hclock (hb hw)
    exact ⟨used,rest,t,d,he,ht,Or.inr (Or.inr hout)⟩
  · have hwork := (prepared_double_work hp hr hm hd).trans hs
    obtain ⟨hspan,hq⟩ := GalilScaffoldSearchRun.double_reset_of_quanta hr hm hd
    exact ⟨[],es,u,clock,rfl,.nil _ _,Or.inr (Or.inr (Or.inr
      ⟨hd,hwork,hspan,hq,hc,Or.inl hv,hclock,hn⟩))⟩

#print axioms prepared_exit
#print axioms next_stage_safe
#print axioms prepared_wait_next
#print axioms prepared_wait_double_work
#print axioms double_stage_next_size
#print axioms prepared_double_size
#print axioms later_stage_safe
#print axioms double_then_prepare
#print axioms first_stage_safe
#print axioms first_prepared_safe
#print axioms paced_grow_then_prepare
#print axioms paced_growing_complete
#print axioms grow_then_prepare
end PalPeg.GalilScaffoldStagePrepare
