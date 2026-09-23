import PalPeg.PhysicalEraseBatch
import PalPeg.PhysicalRetiredDpFrame
import PalPeg.PhysicalLoanDispatch

/-! Retired DP cleanup runs in parallel with the common dispatcher. Both
read the source windows. Each physical tape takes one of their results, so
one macro sweep and the existing radius suffice. The retirement trace and
reuse deadline remain obligations of the surrounding program schedule. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace PalPeg.PhysicalDpCleanup
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalProgramErase (Phase Raw run Stored dpCarrier carrier_at carrier_some)
open PalPeg.PhysicalShiftDispatch (RoutedControl RoutedState RoutedStep RoutedCore liftConfig)
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12

abbrev Phases := Fin 12 → Phase
abbrev Control := RoutedControl × Phases
abbrev Config := Control × (Fin tapeCountM → STape Γm)
abbrev Step := LocalStep (Fin 2) Control Γm tapeCountM macroRadius

noncomputable instance : Fintype Control := inferInstanceAs (Fintype (RoutedControl × Phases))
instance : DecidableEq Control := inferInstanceAs (DecidableEq (RoutedControl × Phases))

def forget (p : Config) : RoutedState := (p.1.1,p.2)

noncomputable def selected (q : CoreControl) (j : Fin tapeCountM) : Bool :=
  (dpCarrier (!q.dpLive) (slotIndex.symm j)).isSome

theorem selected_iff (q : CoreControl) (j : Fin tapeCountM) :
    selected q j = true ↔ PalPeg.PhysicalRetiredDpFrame.Retired q j := by
  unfold selected
  cases h : dpCarrier (!q.dpLive) (slotIndex.symm j) with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨i,hi⟩
    rw [hi,Equiv.symm_apply_apply,carrier_at] at h
    contradiction
  | some i =>
    simp only [Option.isSome_some, true_iff]
    exact ⟨i, by rw [← (carrier_some _ _ _).mp h, Equiv.apply_symm_apply]⟩

def start (old new : CoreControl) (phases : Phases) : Phases :=
  if old.dpLive = new.dpLive then phases else fun _ => .rewind

/-- The extra control is finite; no tape lengths or elapsed counts occur. -/
noncomputable def wrap (L : RoutedStep) : Step where
  next := fun q a ws =>
    let target := L.next q.1 a ws
    match q.1.2, target.1.2 with
    | .inr old, .inr new =>
      let erased := (PalPeg.PhysicalEraseBatch.step macroRadius).next
        (new,start old new q.2) none (fun j => ws (target.1.1 j))
      ((target.1,erased.1.2), fun j =>
        if selected new (target.1.1.symm j) then erased.2 (target.1.1.symm j) else target.2 j)
    | _, _ => ((target.1,fun _ => .done),target.2)
  disp_le := by
    intro q a ws j
    dsimp only
    split
    · dsimp only
      split
      · exact (PalPeg.PhysicalEraseBatch.step macroRadius).disp_le _ _ _ _
      · exact L.disp_le _ _ _ _
    · exact L.disp_le _ _ _ _

noncomputable def machine (rest : PalPeg.PhysicalScanCount.RestCommands) : Step :=
  wrap (PalPeg.PhysicalLoanDispatch.machine rest)

noncomputable def erase (source target : RoutedCore) (phases : Phases) :=
  (PalPeg.PhysicalEraseBatch.step macroRadius).apply blankM
    ((target.1.2,start source.1.2 target.1.2 phases),fun j => source.2 (target.1.1 j)) none

noncomputable def overlay (target : RoutedCore) (U : Fin tapeCountM → STape Γm) : Fin tapeCountM → STape Γm :=
  fun j => if selected target.1.2 (target.1.1.symm j) then U (target.1.1.symm j) else target.2 j

/-- The two components each sweep the original physical tape. No sequential
sweep, extra tick, or sum of their radii appears in this equality. -/
theorem apply_running (L : RoutedStep) (source target : RoutedCore) (phases : Phases)
    (a : Option (Fin 2)) (h : L.apply blankM (liftConfig source) a = liftConfig target) :
    (wrap L).apply blankM (((liftConfig source).1,phases),source.2) a =
      (((liftConfig target).1,(erase source target phases).1.2),
        overlay target (erase source target phases).2) := by
  have hq := congrArg Prod.fst h
  have ht := congrArg Prod.snd h
  change (L.next (liftConfig source).1 a (fun j => readWin blankM macroRadius (source.2 j))).1 =
    (liftConfig target).1 at hq
  simp only [liftConfig] at hq ht ⊢
  apply Prod.ext
  · simp only [LocalStep.apply,wrap,hq,erase]
  · funext j
    simp only [LocalStep.apply,wrap,hq,overlay,erase]
    split
    · simp only [Equiv.apply_symm_apply]
    · exact congrFun ht j

/-- Observational storage suffices for physical erasing. -/
def View (raw : Fin 12 → Raw) (q : CoreControl) (phases : Phases)
    (T : Fin tapeCountM → STape Γm) : Prop :=
  ∀ i, phases i = (raw i).1 ∧ TEqG blankM (padLeft margin (mapTape encProg (raw i).2))
    (T (slotIndex (dpSlotOf (!q.dpLive) i)))

theorem view_stored (raw : Fin 12 → Raw) (q : CoreControl) (phases : Phases)
    (T : Fin tapeCountM → STape Γm) (hv : View raw q phases T) (hm : ∀ j, 1 ≤ pos (T j)) :
    Stored margin raw ((q,phases),T) := by
  let V := fun j => match dpCarrier (!q.dpLive) (slotIndex.symm j) with
    | none => T j
    | some i => padLeft margin (mapTape encProg (raw i).2)
  refine ⟨V,?_,?_,?_⟩
  · intro i
    exact ⟨(hv i).1,by simp only [V,Equiv.symm_apply_apply,carrier_at]⟩
  · intro j
    dsimp only [V]
    split
    · exact hm j
    · rw [pos_padLeft]; omega
  · intro j
    dsimp only [V]
    split
    · exact ⟨rfl,fun _ => rfl⟩
    · rename_i i hi
      have hj : j = slotIndex (dpSlotOf (!q.dpLive) i) := by
        rw [← (carrier_some _ _ _).mp hi,Equiv.apply_symm_apply]
      rw [hj]
      exact (hv i).2

theorem stored_view (raw : Fin 12 → Raw)
    (p : PalPeg.PhysicalProgramErase.Control fppBound dpBound × (Fin tapeCountM → STape Γm))
    (he : Stored margin raw p) : View raw p.1.1 p.1.2 p.2 := by
  obtain ⟨T,hT,_,ht⟩ := he
  intro i
  refine ⟨(hT i).1,?_⟩
  have h := ht (slotIndex (dpSlotOf (!p.1.1.dpLive) i))
  have hi : T (slotIndex (dpSlotOf (!p.1.1.dpLive) i)) = _ := (hT i).2
  rw [hi] at h
  exact h

theorem loan_margin (w : List (Fin 2)) (x : PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (p : RoutedCore) (he : PalPeg.PhysicalLoanInvariant.Enc w x (liftConfig p)) :
    ∀ j, margin ≤ pos (p.2 j) := by
  suffices h : ∀ j, margin ≤ pos (p.2 (p.1.1 j)) by
    intro j; simpa only [Equiv.apply_symm_apply] using h (p.1.1.symm j)
  by_cases hn : PalPeg.PhysicalLoanInvariant.NeedsLoan x
  · obtain ⟨_,T,hT,ht⟩ := (PalPeg.PhysicalLoanInvariant.enc_partial w x _ hn).mp he
    intro j
    exact (ht j).1 ▸ PalPeg.PhysicalDebtRebuild.core_margin w x (p.1.2,T) hT j
  · obtain ⟨⟨y,_,T,hT,ht⟩,_⟩ := (PalPeg.PhysicalLoanInvariant.enc_full w x _ hn).mp he
    intro j
    have hm := hT.1.1.1.2.margins (slotIndex.symm j)
    have hm' : margin ≤ pos (T j) := by simpa only [Equiv.apply_symm_apply] using hm
    exact (ht j).1 ▸ hm'

/-- Source storage yields both the new phases and every cleaned tape. -/
theorem erase_view (source target : RoutedCore) (phases : Phases) (raw : Fin 12 → Raw)
    (hv : View raw target.1.2 (start source.1.2 target.1.2 phases) (fun j => source.2 (target.1.1 j)))
    (hm : ∀ j, margin ≤ pos (source.2 j)) :
    View (fun i => run macroRadius (raw i)) target.1.2
      (erase source target phases).1.2 (erase source target phases).2 := by
  let p := ((target.1.2,start source.1.2 target.1.2 phases),fun j => source.2 (target.1.1 j))
  have hmp : ∀ j, macroRadius ≤ pos (p.2 j) := fun j => hm (target.1.1 j)
  have hs := view_stored raw p.1.1 p.1.2 p.2 hv (fun j => (by decide : 1 ≤ macroRadius).trans (hmp j))
  have hv' := stored_view _ _ (PalPeg.PhysicalEraseBatch.stored margin macroRadius raw p hs hmp)
  rw [PalPeg.PhysicalEraseBatch.control macroRadius p hmp] at hv'
  exact hv'

/-- Concurrent cleanup preserves the actual shared encoding. The only new
source premise describes the bank selected for retirement, before the sweep. -/
theorem forward (L : RoutedStep) (w : List (Fin 2))
    (x y : PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (source target : RoutedCore) (phases : Phases) (a : Option (Fin 2))
    (raw : Fin 12 → Raw)
    (hx : PalPeg.PhysicalLoanInvariant.Enc w x (liftConfig source))
    (hy : PalPeg.PhysicalLoanInvariant.Enc w y (liftConfig target))
    (hstep : L.apply blankM (liftConfig source) a = liftConfig target)
    (hv : View raw target.1.2 (start source.1.2 target.1.2 phases) (fun j => source.2 (target.1.1 j))) :
    let result := (wrap L).apply blankM (((liftConfig source).1,phases),source.2) a
    PalPeg.PhysicalLoanInvariant.Enc w y (forget result) ∧
      View (fun i => run macroRadius (raw i)) target.1.2 result.1.2 (fun j => result.2 (target.1.1 j)) := by
  dsimp only
  rw [apply_running L source target phases a hstep]
  have he := erase_view source target phases raw hv (loan_margin w x source hx)
  have hview : View (fun i => run macroRadius (raw i)) target.1.2 (erase source target phases).1.2
      (fun j => overlay target (erase source target phases).2 (target.1.1 j)) := by
    intro i
    simpa only [overlay,Equiv.symm_apply_apply,selected,carrier_at,Option.isSome_some,if_true]
      using he i
  refine ⟨?_,hview⟩
  change PalPeg.PhysicalLoanInvariant.Enc w y
    (liftConfig (target.1,overlay target (erase source target phases).2))
  apply PalPeg.PhysicalRetiredDpFrame.loan w y target _ hy
  · intro j hj
    simp only [overlay,Equiv.symm_apply_apply,show selected target.1.2 j = false from
      Bool.eq_false_iff.mpr (fun h => hj ((selected_iff _ _).mp h)),Bool.false_eq_true,if_false]
    exact ⟨rfl,fun _ => rfl⟩
  · rintro j ⟨i,rfl⟩
    have hp := (hview i).2.1
    rw [← hp,pos_padLeft]
    omega

/-- The proof history certifies that a done bit really denotes a clean bank.
It is not stored in the machine's finite control. -/
def Progress (p : Config) : Prop := match p.1.1.2 with
  | .inl _ => True
  | .inr q => ∃ raw, (∀ i, PalPeg.PhysicalEraseBatch.Good (raw i)) ∧
      View raw q p.1.2 (fun j => p.2 (p.1.1.1 j))

noncomputable def Enc (w : List (Fin 2))
    (x : PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM) (p : Config) : Prop :=
  PalPeg.PhysicalLoanInvariant.Enc w x (forget p) ∧ Progress p

def initialControl : Control := (PalPeg.PhysicalRoles.initialControl,fun _ => .done)

theorem enc_initial (w : List (Fin 2)) :
    Enc w initialState (initialControl,fun _ => STape.blankTape blankM) :=
  ⟨PalPeg.PhysicalLoanInvariant.enc_initial w,trivial⟩

/-- A represented done bit exposes the reset bank needed by its next owner. -/
theorem ready (p : RoutedCore) (phases : Phases)
    (hp : Progress (((liftConfig p).1,phases),p.2)) (hd : ∀ i, phases i = .done) :
    ∀ i, TEqG blankM (padLeft margin (mapTape encProg (STape.blankTape 6)))
      (p.2 (p.1.1 (slotIndex (dpSlotOf (!p.1.2.dpLive) i)))) := by
  obtain ⟨raw,hg,hv⟩ := hp
  intro i
  have hclean := PalPeg.PhysicalEraseBatch.done_clean (raw i) (hg i) ((hv i).1.symm.trans (hd i))
  exact PalPeg.MachineStep.teqG_trans (PalPeg.PhysicalProgramErase.padded_blankEq margin hclean.symm) (hv i).2

/-- Any already-proved dispatcher row that keeps the selected DP bank carries
cleanup progress automatically. Counter and mirror role changes are allowed. -/
theorem forward_kept (L : RoutedStep) (w : List (Fin 2))
    (x y : PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (source target : RoutedCore) (phases : Phases) (a : Option (Fin 2))
    (hx : Enc w x (((liftConfig source).1,phases),source.2))
    (hy : PalPeg.PhysicalLoanInvariant.Enc w y (liftConfig target))
    (hstep : L.apply blankM (liftConfig source) a = liftConfig target)
    (hbank : target.1.2.dpLive = source.1.2.dpLive)
    (hroles : ∀ i, target.1.1 (slotIndex (dpSlotOf (!target.1.2.dpLive) i)) =
      source.1.1 (slotIndex (dpSlotOf (!source.1.2.dpLive) i))) :
    Enc w y ((wrap L).apply blankM (((liftConfig source).1,phases),source.2) a) := by
  obtain ⟨raw,hg,hv⟩ := hx.2
  have hstart : start source.1.2 target.1.2 phases = phases := by simp only [start,hbank,if_true]
  have hsrc : View raw target.1.2 (start source.1.2 target.1.2 phases)
      (fun j => source.2 (target.1.1 j)) := by
    intro i
    rw [hstart]
    exact ⟨(hv i).1,by simpa only [hroles i,liftConfig] using (hv i).2⟩
  have hh := forward L w x y source target phases a raw hx.1 hy hstep hsrc
  refine ⟨hh.1,?_⟩
  have hv' := hh.2
  rw [apply_running L source target phases a hstep] at hv' ⊢
  exact ⟨fun i => run macroRadius (raw i),
    fun i => PalPeg.PhysicalEraseBatch.good_run (raw i) (hg i) macroRadius,hv'⟩

/-- A bank flip restarts the finite eraser on the newly retired source tapes.
Density is required of those source tapes, before the ordinary row runs. -/
theorem forward_retired (L : RoutedStep) (w : List (Fin 2))
    (x y : PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (source target : RoutedCore) (phases : Phases) (a : Option (Fin 2))
    (raw : Fin 12 → STape (Fin 9))
    (hx : Enc w x (((liftConfig source).1,phases),source.2))
    (hy : PalPeg.PhysicalLoanInvariant.Enc w y (liftConfig target))
    (hstep : L.apply blankM (liftConfig source) a = liftConfig target)
    (hflip : source.1.2.dpLive ≠ target.1.2.dpLive)
    (hd : ∀ i, PalPeg.PhysicalProgramErase.Dense (raw i))
    (ht : ∀ i, TEqG blankM (padLeft margin (mapTape encProg (raw i)))
      (source.2 (target.1.1 (slotIndex (dpSlotOf (!target.1.2.dpLive) i))))) :
    Enc w y ((wrap L).apply blankM (((liftConfig source).1,phases),source.2) a) := by
  have hv : View (fun i => (.rewind,raw i)) target.1.2 (start source.1.2 target.1.2 phases)
      (fun j => source.2 (target.1.1 j)) := by
    intro i
    exact ⟨by simp only [start,if_neg hflip],ht i⟩
  have hh := forward L w x y source target phases a (fun i => (.rewind,raw i)) hx.1 hy hstep hv
  refine ⟨hh.1,?_⟩
  have hv' := hh.2
  rw [apply_running L source target phases a hstep] at hv' ⊢
  exact ⟨fun i => run macroRadius (.rewind,raw i),fun i =>
    PalPeg.PhysicalEraseBatch.good_run _ (PalPeg.PhysicalEraseBatch.good_start (raw i) (hd i)) macroRadius,hv'⟩

theorem loan_boundary (w : List (Fin 2))
    (x : PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (p : RoutedCore) (he : PalPeg.PhysicalLoanInvariant.Enc w x (liftConfig p)) : MacroBoundary p.1.2 := by
  by_cases hn : PalPeg.PhysicalLoanInvariant.NeedsLoan x
  · obtain ⟨_,T,hT,_⟩ := (PalPeg.PhysicalLoanInvariant.enc_partial w x _ hn).mp he
    exact hT.1.1.1.2
  · obtain ⟨⟨_,_,T,hT,_⟩,_⟩ := (PalPeg.PhysicalLoanInvariant.enc_full w x _ hn).mp he
    exact hT.1.1.2

theorem feed_bank (p : CoreState) (a : Option (Fin 2))
    (hm : ∀ j, macroRadius ≤ pos (p.2 j)) (hs : p.1.slot.val = 0) :
    (PalPeg.PhysicalBootFeed.feedStep.apply blankM p a).1.dpLive = p.1.dpLive := by
  have hr := PalPeg.LocalStepFusion.compStep_iterRule blankM PalPeg.PhysicalFeed.feedRule 12 p a hm
  rw [PalPeg.LocalStepFusion.idealIter_eq_idealRun] at hr
  have hf := tickRule_headFree (by decide : 2 ≤ microRadius) (fun q _ _ => q)
    PalPeg.PhysicalFeed.commands (fun _ _ _ _ => []) (by intros; simp) p a hs
  change headFreeFields (PalPeg.LocalStepFusion.idealRun PalPeg.PhysicalFeed.feedRule blankM p a 12).1 = _ at hf
  generalize PalPeg.LocalStepFusion.idealRun PalPeg.PhysicalFeed.feedRule blankM p a 12 = result at hf hr
  have hreal : (PalPeg.PhysicalBootFeed.feedStep.apply blankM p a).1 = result.1 := hr.1
  have hc := congrArg QPhys.dpLive hreal
  simp only [headFreeFields,Prod.mk.injEq] at hf
  exact hc.trans hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem held_bank (L : PalPeg.PhysicalBootFeed.CoreStep) (p : RoutedCore) (a : Option (Fin 2)) :
    ((PalPeg.LocalRoleRouting.hold L).apply blankM p a).1.2.dpLive =
      (L.apply blankM (PalPeg.LocalRoleRouting.decode p) a).1.dpLive := rfl

theorem held_roles (L : PalPeg.PhysicalBootFeed.CoreStep) (p : RoutedCore) (a : Option (Fin 2)) :
    ((PalPeg.LocalRoleRouting.hold L).apply blankM p a).1.1 = p.1.1 := rfl

/-- Running input arrival and quiet ticks execute cleanup in the same sweep;
all storage premises come from the shared source invariant. -/
theorem forward_transport (rest : PalPeg.PhysicalScanCount.RestCommands)
    (w : List (Fin 2)) (x : PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (p : RoutedCore) (phases : Phases) (a : Option (Fin 2))
    (he : Enc w x (((liftConfig p).1,phases),p.2))
    (hselect : PalPeg.PhysicalLoanDispatch.transportTest (liftConfig p).1 a
      (fun j => readWin blankM macroRadius (p.2 j)) = true) :
    Enc w (PalPeg.PhysicalFeed.feedState a x)
      ((machine rest).apply blankM (((liftConfig p).1,phases),p.2) a) := by
  let target := (PalPeg.LocalRoleRouting.hold PalPeg.PhysicalBootFeed.feedStep).apply blankM p a
  have hselect' : PalPeg.PhysicalLoanDispatch.transportTest (liftConfig p).1 a
      (fun j => readWin blankM macroRadius ((liftConfig p).2 j)) = true := hselect
  have hstep : (PalPeg.PhysicalLoanDispatch.machine rest).apply blankM (liftConfig p) a = liftConfig target := by
    rw [PalPeg.PhysicalLoanDispatch.machine,PalPeg.PhysicalShiftDispatch.select_apply,hselect',if_pos rfl,
      PalPeg.PhysicalShiftDispatch.lift_apply]
  have hm := loan_margin w x p he.1
  have hb : target.1.2.dpLive = p.1.2.dpLive :=
    (held_bank PalPeg.PhysicalBootFeed.feedStep p a).trans
      (feed_bank (PalPeg.LocalRoleRouting.decode p) a (fun j => hm (p.1.1 j)) (loan_boundary w x p he.1).1)
  have hr : target.1.1 = p.1.1 := held_roles PalPeg.PhysicalBootFeed.feedStep p a
  have hy := PalPeg.PhysicalLoanInvariant.running_feed w x p a he.1
  change PalPeg.PhysicalLoanInvariant.Enc w _ (liftConfig target) at hy
  generalize ht : target = result at hstep hb hr hy
  exact forward_kept (PalPeg.PhysicalLoanDispatch.machine rest) w x _ p result phases a he
    hy hstep hb (fun i => by rw [hr,hb])

theorem forward_feed_running (rest : PalPeg.PhysicalScanCount.RestCommands)
    (w : List (Fin 2)) (x : PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (p : RoutedCore) (phases : Phases) (a : Fin 2)
    (he : Enc w x (((liftConfig p).1,phases),p.2)) :
    Enc w (PalPeg.GalilArriveChain.arriveState' a x)
      ((machine rest).apply blankM (((liftConfig p).1,phases),p.2) (some a)) :=
  forward_transport rest w x p phases (some a) he rfl

theorem forward_starved_running (rest : PalPeg.PhysicalScanCount.RestCommands)
    (w : List (Fin 2)) (x : PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (p : RoutedCore) (phases : Phases)
    (he : Enc w x (((liftConfig p).1,phases),p.2)) (hs : PalPeg.FrameFunction.starvedTest x = true) :
    Enc w x ((machine rest).apply blankM (((liftConfig p).1,phases),p.2) none) :=
  forward_transport rest w x p phases none he
    ((PalPeg.PhysicalLoanInvariant.starved_running w x p he.1).trans hs)

/-- info: 'PalPeg.PhysicalDpCleanup.apply_running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms apply_running

/-- info: 'PalPeg.PhysicalDpCleanup.forward_kept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_kept

/-- info: 'PalPeg.PhysicalDpCleanup.ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ready

/-- info: 'PalPeg.PhysicalDpCleanup.forward_feed_running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_feed_running

/-- info: 'PalPeg.PhysicalDpCleanup.forward_starved_running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_starved_running

/-- info: 'PalPeg.PhysicalDpCleanup.forward_retired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_retired

end PalPeg.PhysicalDpCleanup
