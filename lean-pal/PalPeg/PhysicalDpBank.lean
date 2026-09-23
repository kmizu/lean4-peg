import PalPeg.PhysicalDpCleanupBoot

/-! The current common dispatcher preserves DP bank identities. This is a
structural property of its actual finite control, not an assumption on a
simulated successor. It will need an explicit retirement case when reset rows
are installed. -/
set_option autoImplicit false
namespace PalPeg.PhysicalDpBank
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.PhysicalShiftDispatch (RoutedStep RoutedControl RoutedCore liftConfig)

variable {Q D : Type} {K H : ℕ}
def RuleKeeps (f : Q → D) (R : ActRule (Fin 2) Q Γm tapeCountM K) : Prop :=
  ∀ q a ws, f (R.nq q a ws) = f q

def StepKeeps (f : Q → D) (L : LocalStep (Fin 2) Q Γm tapeCountM K) : Prop :=
  ∀ q a ws, f (L.next q a ws).1 = f q

theorem seq_keeps (f : Q → D) (R : ActRule (Fin 2) Q Γm tapeCountM K)
    (S : ActRule (Fin 2) Q Γm tapeCountM H) (hr : RuleKeeps f R) (hs : RuleKeeps f S) :
    RuleKeeps f (seqRule R S) := by
  intro q a ws
  exact (hs _ _ _).trans (hr _ _ _)

theorem iter_keeps (f : Q → D) (R : ActRule (Fin 2) Q Γm tapeCountM K)
    (hr : RuleKeeps f R) (n : ℕ) : RuleKeeps f (iterRule R n) := by
  induction n with
  | zero => intro q a ws; rfl
  | succ n ih => exact seq_keeps f R _ hr ih

theorem comp_keeps (f : Q → D) (R : ActRule (Fin 2) Q Γm tapeCountM K)
    (hr : RuleKeeps f R) : StepKeeps f (compStep R) := hr

abbrev DP (R : ActRule (Fin 2) CoreControl Γm tapeCountM K) := RuleKeeps QPhys.dpLive R
abbrev DPstep (L : LocalStep (Fin 2) CoreControl Γm tapeCountM K) := StepKeeps QPhys.dpLive L

theorem tick_keeps (hK : 2 ≤ K) (base commands acts)
    (hlen : ∀ q a ws j, (acts q a ws j).length ≤ K)
    (hb : ∀ q a ws, (base q a ws : CoreControl).dpLive = q.dpLive) :
    DP (tickRule hK base commands acts hlen) := by
  intro q a ws
  simp only [tickRule]
  split
  · exact hb q a ws
  · rfl

theorem consume_dp (q : CoreControl) (ws : Fin tapeCountM → Window Γm K) :
    (scanConsumeNext q ws).dpLive = q.dpLive := by
  unfold scanConsumeNext
  split <;> rfl

theorem scan_dp (q : CoreControl) (ws : Fin tapeCountM → Window Γm K) :
    (scanNext q ws).dpLive = q.dpLive := by
  unfold scanNext
  split <;> dsimp only <;> split <;> simp only [consume_dp]

theorem ruleNext_dp (q : CoreControl) (ws : Fin tapeCountM → Window Γm K) :
    (ruleNext 1 0 fppBound_gt_start q ws).dpLive = q.dpLive := by
  cases hm : q.ctl.mode <;>
    simp only [ruleNext, hm, markEndNext, homeNext, chooseBackNext, rewindNext,
      rewindPairNext, rewindOneNext, fppNext, copyNext, shiftNext, shiftExitNext, scan_dp]
  all_goals split_ifs <;> rfl

theorem work (rest : PalPeg.PhysicalScanCount.RestCommands) :
    DPstep (PalPeg.PhysicalScanCount.workStep rest) := by
  apply comp_keeps
  apply iter_keeps
  exact tick_keeps (by decide : 2 ≤ microRadius) _ _ _
    (fun q _ ws j => ruleActs_length 1 0 (by decide : 1 + 3 ≤ microRadius) q ws j)
    (fun q _ ws => ruleNext_dp q ws)

theorem feed : DPstep PalPeg.PhysicalBootFeed.feedStep := by
  apply comp_keeps
  apply iter_keeps
  apply tick_keeps
  intros; rfl

attribute [local irreducible] PalPeg.PhysicalBootFeed.feedStep

theorem growBody : DP PalPeg.PhysicalGrowCount.body :=
  seq_keeps _ _ _ (fun _ _ _ => rfl)
    (seq_keeps _ _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl))

theorem grow : DPstep PalPeg.PhysicalGrowCount.step := by
  intro q a ws
  exact growBody q a (PalPeg.PhysicalGrowCount.windows ws)

theorem growMatchBody : DP PalPeg.PhysicalGrowMatch.body :=
  seq_keeps _ _ _ growBody (fun _ _ _ => rfl)

theorem growMatchRule : DP PalPeg.PhysicalGrowMatchTick.rule := by
  apply tick_keeps
  intro q a ws
  exact growMatchBody q a ws

theorem counted (L : PalPeg.PhysicalBootFeed.CoreStep) (hl : DPstep L) :
    DPstep (PalPeg.PhysicalScanCount.countedStep L) := by
  intro q a ws
  simp only [PalPeg.PhysicalScanCount.countedStep]
  split <;> exact hl q a ws

theorem branch (test : CoreControl → (Fin tapeCountM → Window Γm macroRadius) → Bool)
    (L M : PalPeg.PhysicalBootFeed.CoreStep) (hl : DPstep L) (hm : DPstep M) :
    DPstep (PalPeg.PhysicalTickDispatch.branchStep test L M) := by
  intro q a ws
  simp only [PalPeg.PhysicalTickDispatch.branchStep]
  split
  · exact hl q a ws
  · exact hm q a ws

theorem spare (L : PalPeg.PhysicalBootFeed.CoreStep) (hl : DPstep L) :
    DPstep (PalPeg.PhysicalSpare.overlay L) := hl

theorem snapshots (L U : PalPeg.PhysicalBootFeed.CoreStep) (hl : DPstep L) :
    DPstep (PalPeg.PhysicalSearchSnapshots.overlayWith U L) := hl

theorem recycle (L : PalPeg.PhysicalBootFeed.CoreStep) (hl : DPstep L) :
    DPstep (PalPeg.PhysicalSearchRecycle.overlay L) := hl

theorem watchEntry : DPstep PalPeg.PhysicalWatchEntry.entryStep := fun _ _ _ => rfl

theorem watchEntryBranch (L : PalPeg.PhysicalBootFeed.CoreStep) (hl : DPstep L) :
    DPstep (PalPeg.PhysicalWatchEntry.withWatchEntry L) := branch _ _ _ (counted _ watchEntry) hl

theorem cache (rest : PalPeg.PhysicalScanCount.RestCommands) :
    DPstep (PalPeg.PhysicalCacheMachine.activeStep rest) :=
  watchEntryBranch _ (branch _ _ _ (spare _ (counted _ (work rest))) (counted _ (work rest)))

theorem snapshotShift (rest : PalPeg.PhysicalScanCount.RestCommands) :
    DPstep (PalPeg.PhysicalSnapshotShift.step rest) :=
  branch _ _ _ (snapshots _ _ (work rest)) (work rest)

theorem recycleEntry : DPstep PalPeg.PhysicalSearchRecycle.entryStep :=
  recycle _ (counted _ watchEntry)

/-- DP addresses are fixed by each finite counter/mirror permutation. -/
def Fixes (r : Equiv.Perm (Fin tapeCountM)) : Prop :=
  ∀ bank i, r (slotIndex (dpSlotOf bank i)) = slotIndex (dpSlotOf bank i)

theorem fixes_refl : Fixes (Equiv.refl _) := fun _ _ => rfl

theorem fixes_trans (r s : Equiv.Perm (Fin tapeCountM)) (hr : Fixes r) (hs : Fixes s) :
    Fixes (r.trans s) := by intro bank i; simp only [Equiv.trans_apply,hr bank i,hs bank i]

theorem fixes_boundary : Fixes PalPeg.PhysicalRoles.boundaryRoles := by
  intro bank i
  apply PalPeg.PhysicalRoles.boundaryRoles_other
  all_goals intro h; have hh := slotIndex.injective h; cases bank <;> simp [dpSlotOf,counterSlot] at hh

theorem fixes_snapshot : Fixes PalPeg.PhysicalSearchSnapshots.rotateRoles := by
  intro bank i
  simp only [PalPeg.PhysicalSearchSnapshots.rotateRoles,Equiv.trans_apply,Equiv.symm_apply_apply]
  rw [PalPeg.PhysicalSearchSnapshots.rotate_other _ (by cases bank <;> rfl)]

theorem fixes_entry : Fixes PalPeg.PhysicalShiftEntry.entryRoles := by
  intro bank i
  apply PalPeg.PhysicalShiftEntry.roles_other
  all_goals intro h; have hh := slotIndex.injective h; cases bank <;> simp [dpSlotOf,counterSlot,mirrorSlot] at hh

abbrev Roles := Equiv.Perm (Fin tapeCountM)
abbrev CoreRouted := Roles × CoreControl

noncomputable def coreKey (q : CoreRouted) := (q.2.dpLive,fun bank i => q.1 (slotIndex (dpSlotOf bank i)))

theorem routeRule_keeps (R : ActRule (Fin 2) CoreControl Γm tapeCountM K)
    (change : PalPeg.LocalRoleRouting.RoleChange (Fin 2) CoreControl Γm tapeCountM K)
    (hr : DP R) (hc : ∀ q a ws, Fixes (change q a ws)) :
    RuleKeeps coreKey (PalPeg.LocalRoleFusion.routeRule R change) := by
  intro q a ws
  apply Prod.ext
  · exact hr _ _ _
  · funext bank i
    change q.1 (change q.2 a (fun j => ws (q.1 j)) (slotIndex (dpSlotOf bank i))) = _
    rw [hc _ _ _ bank i]
    rfl

theorem route_keeps (L : LocalStep (Fin 2) CoreControl Γm tapeCountM K)
    (change : PalPeg.LocalRoleRouting.RoleChange (Fin 2) CoreControl Γm tapeCountM K)
    (hl : DPstep L) (hc : ∀ q a ws, Fixes (change q a ws)) :
    StepKeeps coreKey (PalPeg.LocalRoleRouting.route L change) := by
  intro q a ws
  apply Prod.ext
  · exact hl _ _ _
  · funext bank i
    change q.1 (change q.2 a (fun j => ws (q.1 j)) (slotIndex (dpSlotOf bank i))) = _
    rw [hc _ _ _ bank i]
    rfl

theorem hold_keeps (L : LocalStep (Fin 2) CoreControl Γm tapeCountM K) (hl : DPstep L) :
    StepKeeps coreKey (PalPeg.LocalRoleRouting.hold L) := route_keeps L _ hl (fun _ _ _ => fixes_refl)

theorem flatten_keeps (R : ActRule (Fin 2) CoreRouted Γm tapeCountM K)
    (hr : RuleKeeps coreKey R) : DP (PalPeg.LocalRoleFusion.flatten R) := by
  intro q a ws
  exact congrArg Prod.fst (hr (Equiv.refl _,q) a ws)

theorem finalRoles_fixes (R : ActRule (Fin 2) CoreRouted Γm tapeCountM K)
    (hr : RuleKeeps coreKey R) (q : CoreControl) (a : Option (Fin 2)) (ws : Fin tapeCountM → Window Γm K) :
    Fixes (PalPeg.LocalRoleFusion.finalRoles R q a ws) := by
  intro bank i
  exact congrFun (congrFun (congrArg Prod.snd (hr (Equiv.refl _,q) a ws)) bank) i

theorem watchRule (hK : 3 ≤ K) (internal : Bool) : DP (PalPeg.PhysicalWatchActions.rule internal hK) :=
  fun _ _ _ => rfl

theorem watchChange (q : CoreControl) (a : Option (Fin 2)) (ws : Fin tapeCountM → Window Γm K) :
    Fixes (PalPeg.PhysicalWatchActions.change q a ws) := by
  unfold PalPeg.PhysicalWatchActions.change
  split
  · exact fixes_boundary
  · exact fixes_refl

theorem watchPlan (consume : Bool) : RuleKeeps coreKey (PalPeg.PhysicalWatchActions.plan consume) := by
  apply seq_keeps
  · apply routeRule_keeps
    · intro q a ws
      cases consume <;> rfl
    · intro q a ws
      cases consume
      · exact fixes_refl
      · exact watchChange q a ws
  · exact routeRule_keeps _ _ (watchRule (by decide) false) watchChange

theorem snapshotWatchRule (hK : 3 ≤ K) (internal : Bool) : DP (PalPeg.PhysicalSnapshotWatch.rule hK internal) := by
  intro q a ws
  simp only [PalPeg.PhysicalSnapshotWatch.rule]
  split <;> rfl

theorem snapshotWatchChange (q : CoreControl) (a : Option (Fin 2)) (ws : Fin tapeCountM → Window Γm K) :
    Fixes (PalPeg.PhysicalSnapshotWatch.change q a ws) := by
  unfold PalPeg.PhysicalSnapshotWatch.change
  split
  · exact fixes_trans _ _ fixes_snapshot fixes_boundary
  · exact fixes_refl

theorem snapshotWatchPlan (consume : Bool) : RuleKeeps coreKey (PalPeg.PhysicalSnapshotWatch.plan consume) := by
  apply seq_keeps
  · apply routeRule_keeps
    · intro q a ws
      cases consume
      · rfl
      · exact snapshotWatchRule (by decide) true q a ws
    · intro q a ws
      cases consume
      · exact fixes_refl
      · exact snapshotWatchChange q a ws
  · exact routeRule_keeps _ _ (snapshotWatchRule (by decide) false) snapshotWatchChange

theorem shiftStart : RuleKeeps coreKey (PalPeg.LocalRoleFusion.routeRule
    PalPeg.PhysicalShiftStart.entryRule PalPeg.PhysicalShiftStart.entryChange) :=
  routeRule_keeps _ _ (fun _ _ _ => rfl) (fun _ _ _ => fixes_entry)

theorem shiftPlan (consume : Bool) : RuleKeeps coreKey (PalPeg.PhysicalShiftStart.plan consume) :=
  seq_keeps _ _ _ (watchPlan consume) shiftStart

theorem snapshotEntryPlan (consume : Bool) : RuleKeeps coreKey (PalPeg.PhysicalSnapshotEntry.plan consume) :=
  seq_keeps _ _ _ (snapshotWatchPlan consume) shiftStart

theorem shiftRule (consume : Bool) : DP (PalPeg.PhysicalShiftTick.rule consume) := by
  apply tick_keeps
  intro q a ws
  exact flatten_keeps _ (shiftPlan consume) q a ws

theorem snapshotEntryRule (consume : Bool) : DP (PalPeg.PhysicalSnapshotEntryTick.rule consume) := by
  apply tick_keeps
  intro q a ws
  exact flatten_keeps _ (snapshotEntryPlan consume) q a ws

theorem shiftEntry (consume : Bool) : StepKeeps coreKey (PalPeg.PhysicalShiftTick.step consume) :=
  route_keeps _ _ (comp_keeps _ _ (iter_keeps _ _ (shiftRule consume) 12))
    (fun q a _ => finalRoles_fixes _ (shiftPlan consume) q a _)

theorem snapshotEntry (consume : Bool) : StepKeeps coreKey (PalPeg.PhysicalSnapshotEntryTick.step consume) :=
  route_keeps _ _ (comp_keeps _ _ (iter_keeps _ _ (snapshotEntryRule consume) 12))
    (fun q a _ => finalRoles_fixes _ (snapshotEntryPlan consume) q a _)

theorem growMatch : StepKeeps coreKey PalPeg.PhysicalGrowMatchTick.step :=
  route_keeps _ _ (comp_keeps _ _ (iter_keeps _ _ growMatchRule 12)) (fun _ _ _ => fixes_refl)

theorem snapshotCount (rest : PalPeg.PhysicalScanCount.RestCommands) :
    StepKeeps coreKey (PalPeg.PhysicalSnapshotCount.step rest) := by
  have hrow (phase : Fin 5) (event : Bool) : StepKeeps coreKey (PalPeg.PhysicalSnapshotCount.row rest phase event) := by
    apply route_keeps
    · intro q a ws
      simp only [PalPeg.PhysicalSnapshotCount.signed,PalPeg.PhysicalSnapshotCount.finishControl]
      split <;> exact spare _ (counted _ (work rest)) q a ws
    · intro q a ws
      cases event
      · exact fixes_refl
      · exact fixes_trans _ _ fixes_snapshot fixes_boundary
  intro q a ws
  exact hrow _ _ q a ws

def bankBit : PalPeg.PhysicalContract.Control → Option Bool
  | .inl _ => none
  | .inr q => some q.dpLive

noncomputable def key (q : RoutedControl) :=
  (bankBit q.2,fun bank i => q.1 (slotIndex (dpSlotOf bank i)))

def RunningKeeps (L : RoutedStep) : Prop :=
  ∀ roles (q : CoreControl) a ws, key (L.next (roles,.inr q) a ws).1 = key (roles,.inr q)

theorem lift_keeps (L : LocalStep (Fin 2) CoreRouted Γm tapeCountM macroRadius)
    (fallback : RoutedStep) (hl : StepKeeps coreKey L) : RunningKeeps (PalPeg.PhysicalShiftDispatch.liftStep L fallback) := by
  intro roles q a ws
  apply Prod.ext
  · exact congrArg some (congrArg Prod.fst (hl (roles,q) a ws))
  · have hr := congrArg Prod.snd (hl (roles,q) a ws)
    exact hr

theorem select_keeps
    (test : RoutedControl → Option (Fin 2) → (Fin tapeCountM → Window Γm macroRadius) → Bool)
    (L M : RoutedStep) (hl : RunningKeeps L) (hm : RunningKeeps M) :
    RunningKeeps (PalPeg.PhysicalShiftDispatch.select test L M) := by
  intro roles q a ws
  simp only [PalPeg.PhysicalShiftDispatch.select]
  split
  · exact hl roles q a ws
  · exact hm roles q a ws

theorem bootFeed_keeps (L : PalPeg.PhysicalBootFeed.CoreStep) (hl : DPstep L)
    (q : CoreControl) (a : Option (Fin 2)) (ws : Fin tapeCountM → Window Γm macroRadius) :
    bankBit ((PalPeg.PhysicalBootFeed.machineStep L).next (.inr q) a ws).1 = some q.dpLive := by
  cases a with
  | none => exact congrArg some (hl q none ws)
  | some b => exact congrArg some (feed q (some b) ws)

theorem boundary (rest : PalPeg.PhysicalScanCount.RestCommands) :
    RunningKeeps (PalPeg.PhysicalBoundaryCount.machine rest) := by
  have hc (q : CoreControl) (a : Option (Fin 2)) (ws : Fin tapeCountM → Window Γm macroRadius) :
      bankBit ((PalPeg.PhysicalCacheMachine.machine rest).next (.inr q) a ws).1 = some q.dpLive :=
    bootFeed_keeps _ (branch _ _ _ feed (cache rest)) q a ws
  have ht (q : PalPeg.PhysicalContract.Control) : bankBit (PalPeg.PhysicalBoundaryCount.turnControl q) = bankBit q := by
    cases q <;> rfl
  have hs (q : CoreControl) (a : Option (Fin 2)) (ws : Fin tapeCountM → Window Γm macroRadius) :
      bankBit ((PalPeg.PhysicalBoundaryCount.signedStep rest).next (.inr q) a ws).1 = some q.dpLive := by
    simp only [PalPeg.PhysicalBoundaryCount.signedStep]
    split
    · exact (ht _).trans (hc q a ws)
    · exact hc q a ws
  have hroles (q : PalPeg.PhysicalContract.Control) (a : Option (Fin 2)) (ws : Fin tapeCountM → Window Γm macroRadius) :
      Fixes (PalPeg.PhysicalBoundaryCount.roleChange q a ws) := by
    unfold PalPeg.PhysicalBoundaryCount.roleChange
    split
    · exact fixes_boundary
    · exact fixes_refl
  intro roles q a ws
  apply Prod.ext
  · exact hs q a (fun j => ws (roles j))
  · funext bank i
    change roles (PalPeg.PhysicalBoundaryCount.roleChange (.inr q) a (fun j => ws (roles j))
      (slotIndex (dpSlotOf bank i))) = roles (slotIndex (dpSlotOf bank i))
    rw [hroles _ _ _ bank i]

theorem shiftDispatch (rest : PalPeg.PhysicalScanCount.RestCommands) :
    RunningKeeps (PalPeg.PhysicalShiftDispatch.machine rest) :=
  select_keeps _ _ _ (select_keeps _ _ _ (lift_keeps _ _ (shiftEntry true)) (lift_keeps _ _ (shiftEntry false))) (boundary rest)

theorem snapshotMachine (rest : PalPeg.PhysicalScanCount.RestCommands) :
    RunningKeeps (PalPeg.PhysicalSnapshotMachine.machine rest) :=
  select_keeps _ _ _ (lift_keeps _ _ (hold_keeps _ recycleEntry))
    (select_keeps _ _ _ (lift_keeps _ _ (snapshotCount rest)) (shiftDispatch rest))

theorem snapshotShiftDispatch (rest : PalPeg.PhysicalScanCount.RestCommands) :
    RunningKeeps (PalPeg.PhysicalSnapshotShiftDispatch.machine rest) :=
  select_keeps _ _ _ (lift_keeps _ _ (hold_keeps _ (snapshotShift rest))) (snapshotMachine rest)

theorem snapshotEntryDispatch (rest : PalPeg.PhysicalScanCount.RestCommands) :
    RunningKeeps (PalPeg.PhysicalSnapshotEntryDispatch.machine rest) :=
  select_keeps _ _ _ (select_keeps _ _ _ (lift_keeps _ _ (snapshotEntry true)) (lift_keeps _ _ (snapshotEntry false)))
    (snapshotShiftDispatch rest)

/-- This theorem concerns the actual current dispatcher, including every
finite-window guard and role update. No encoding or reachability premise. -/
theorem machine (rest : PalPeg.PhysicalScanCount.RestCommands) :
    RunningKeeps (PalPeg.PhysicalLoanDispatch.machine rest) :=
  select_keeps _ _ _ (lift_keeps _ _ (hold_keeps _ feed))
    (select_keeps _ _ _ (lift_keeps _ _ (hold_keeps _ grow))
      (select_keeps _ _ _ (lift_keeps _ _ growMatch) (snapshotEntryDispatch rest)))

/-- info: 'PalPeg.PhysicalDpBank.machine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms machine

end PalPeg.PhysicalDpBank
