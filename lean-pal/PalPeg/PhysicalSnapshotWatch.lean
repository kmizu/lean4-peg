import PalPeg.PhysicalSnapshotCount

/-! # Comparison watch quanta carrying the restart snapshots

The original nonhead watch row and its six snapshot carriers share a radius-32
action rule. The original boundary permutation and both extra permutations are
installed together before the next quantum reads its windows.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalSnapshotWatch
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalSearchSnapshots
open PalPeg.PhysicalSearchRecycle (resetSlot)
open PalPeg.PhysicalCacheInvariant (Running running_core)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter)
open PalPeg.ChainBoundaryCache (Inv boundaryEvent nextSpare nextAge advanceCounter)
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.LocalRoleFusion (logicalStep routeRule)
open PalPeg.PhysicalWatchStep (watchAfter stateAfter beforeImmediate beforeImmediateWatch)
variable {K : ℕ}

noncomputable def incrementsRule (hK : 3 ≤ K) : ActRule (Fin 2) CoreControl Γm tapeCountM K where
  nq := fun q input ws => (boundedRule hK (spareCounts q.chainPhase)).nq q input ws
  acts := fun q input ws => (boundedRule hK (spareCounts q.chainPhase)).acts q input ws
  len_le := fun q input ws j => (boundedRule hK (spareCounts q.chainPhase)).len_le q input ws j

theorem increments_ideal (hK : 3 ≤ K) (p : CoreState) (input : Option (Fin 2)) :
    idealStep (incrementsRule hK) blankM p input =
      idealStep (boundedRule hK (spareCounts p.1.chainPhase)) blankM p input := rfl

noncomputable def mixedRule (hK : 3 ≤ K) (internal : Bool) :
    ActRule (Fin 2) CoreControl Γm tapeCountM K where
  nq := fun q input ws =>
    let base := (PalPeg.PhysicalWatchActions.rule internal hK).nq q input ws
    let update := (incrementsRule hK).nq q input ws
    withSigns base (fun i => update.polarity (index i))
  acts := fun q input ws j =>
    if resetSlot (slotIndex.symm j) then (incrementsRule hK).acts q input ws j
    else (PalPeg.PhysicalWatchActions.rule internal hK).acts q input ws j
  len_le := by
    intro q input ws j
    split
    · exact (incrementsRule hK).len_le q input ws j
    · exact (PalPeg.PhysicalWatchActions.rule internal hK).len_le q input ws j

theorem mixed_ideal (hK : 3 ≤ K) (internal : Bool) (p : CoreState) (input : Option (Fin 2)) :
    idealStep (mixedRule hK internal) blankM p input =
      mix (idealStep (PalPeg.PhysicalWatchActions.rule internal hK) blankM p input)
        (idealStep (incrementsRule hK) blankM p input) := by
  apply Prod.ext
  · rfl
  · funext j
    simp only [idealStep, mixedRule, mix]
    split_ifs <;> rfl

/-- Original role routing commutes with the new carriers; the original row
has already supplied its own sign changes. -/
theorem mixed_logical (hK : 3 ≤ K) (internal : Bool) (p : CoreState) (input : Option (Fin 2)) :
    logicalStep (mixedRule hK internal) PalPeg.PhysicalWatchActions.change blankM p input =
      mix (logicalStep (PalPeg.PhysicalWatchActions.rule internal hK)
        PalPeg.PhysicalWatchActions.change blankM p input)
        (idealStep (incrementsRule hK) blankM p input) := by
  unfold logicalStep
  rw [mixed_ideal]
  apply Prod.ext
  · rfl
  · funext j
    simp only [PalPeg.PhysicalWatchActions.change]
    split_ifs
    · simp only [mix, PalPeg.PhysicalSnapshotCount.mask_boundary]
      by_cases hselected : resetSlot (slotIndex.symm j) = true
      · simp only [hselected, if_true, PalPeg.PhysicalSnapshotCount.boundary_keeps j hselected]
      · simp only [hselected, Bool.false_eq_true, if_false]
    · rfl

noncomputable def rule (hK : 3 ≤ K) (internal : Bool) :
    ActRule (Fin 2) CoreControl Γm tapeCountM K where
  nq := fun q input ws =>
    let mixed := (mixedRule hK internal).nq q input ws
    if PalPeg.PhysicalWatchActions.event ws then withSigns mixed (rotatedBits mixed) else mixed
  acts := (mixedRule hK internal).acts
  len_le := (mixedRule hK internal).len_le

noncomputable def change : PalPeg.LocalRoleRouting.RoleChange (Fin 2) CoreControl Γm tapeCountM K :=
  fun _ _ ws => if PalPeg.PhysicalWatchActions.event ws then
    rotateRoles.trans PalPeg.PhysicalRoles.boundaryRoles else Equiv.refl _

theorem logical_completed (hK : 3 ≤ K) (internal : Bool) (p : CoreState) (input : Option (Fin 2)) :
    logicalStep (rule hK internal) change blankM p input =
      completed (PalPeg.PhysicalWatchActions.event (fun j => readWin blankM K (p.2 j)))
        (logicalStep (mixedRule hK internal) PalPeg.PhysicalWatchActions.change blankM p input) := by
  cases hevent : PalPeg.PhysicalWatchActions.event (fun j => readWin blankM K (p.2 j)) <;>
    simp only [logicalStep, idealStep, rule, change, PalPeg.PhysicalWatchActions.change,
      completed, rotateCore, hevent, Bool.false_eq_true, if_false, if_true, Equiv.refl_apply,
      Equiv.trans_apply]

theorem source_reads (hpad : K ≤ margin) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (henc : Running w x p) :
    p.1.chainPhase = wm.machine.control.phase ∧
      PalPeg.PhysicalWatchActions.event (fun j => readWin blankM K (p.2 j)) = boundaryEvent wm.machine.control := by
  constructor
  · obtain ⟨T, hT, _⟩ := running_core henc
    simpa only [chainConsumeOf, hchain] using hT.1.1.chainPhase
  · apply PalPeg.PhysicalTickDispatch.read_from_running
      (fun _ ws => PalPeg.PhysicalWatchActions.event ws) (fun _ => boundaryEvent wm.machine.control)
      w x p (running_core henc)
    intro T hT
    have hread := PalPeg.PhysicalWatchStep.event_read hpad x p.1
      (fun slot => T (slotIndex slot)) wm hchain hT.1.2
    simpa only [tapesOf, Equiv.apply_symm_apply] using hread

/-- One comparison quantum prepares and rotates all copies. Its VM base
is the existing proved watch row, with no output-encoding premise. -/
theorem running (hK : 3 ≤ K) (hpad : K ≤ margin) (internal : Bool)
    (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (spare : Counter) (h age : ℕ) (hInv : Inv h age wm.machine.control spare)
    (henc : Running w (saved x wm.machine.control.boundary wm.machine.control.last spare) p)
    (a : Fin 3) (htoken : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a) :
    let next := watchAfter internal wm a
    Running w (saved (stateAfter internal x wm a) next.machine.control.boundary next.machine.control.last
      (nextSpare wm.machine.control spare)) (logicalStep (rule hK internal) change blankM p none) ∧
      Inv h (nextAge wm.machine.control age) next.machine.control (nextSpare wm.machine.control spare) := by
  let sx := saved x wm.machine.control.boundary wm.machine.control.last spare
  obtain ⟨hphase, hevent⟩ := source_reads hpad w sx p wm hchain henc
  have hbase := PalPeg.PhysicalWatchStep.running hK hpad internal w sx p henc wm hchain a htoken
  have hupdate : Running w (saved x wm.machine.control.boundary wm.machine.control.last
      (advanceCounter (PalPeg.ChainBoundaryCache.rate wm.machine.control.phase) spare))
      (idealStep (incrementsRule hK) blankM p none) := by
    rw [increments_ideal, hphase]
    simpa [sx, saved, put, values, spareCounts, PalPeg.PhysicalRestartStorage.replace, advanceCounter] using
      running_increment_ideal hK hpad (spareCounts wm.machine.control.phase) w sx p henc none
  have hcanonical : PalPeg.GalilScaffoldCounter.Canonical wm.machine.control.distance := by
    obtain ⟨T, hT, _⟩ := henc
    obtain ⟨seg, ha, _⟩ := hT.1.1.1.2.counters 13 wm.machine.control.distance
      (by simp [counterOf, saved, put, PalPeg.PhysicalRestartStorage.replace, hchain])
    exact ha ▸ PalPeg.LocalCounter.absCtr_canonical seg _
  have hout := consume_updated w x (stateAfter internal sx wm a) p _ _ wm.machine.control
    spare h age hInv hcanonical henc hbase hupdate a htoken
  rw [logical_completed, mixed_logical, hevent]
  simpa only [sx, stateAfter, saved, put, PalPeg.PhysicalRestartStorage.replace, watchAfter] using hout

noncomputable def firstRule (consume : Bool) : ActRule (Fin 2) CoreControl Γm tapeCountM 32 where
  nq := fun q input ws => if consume then (rule (by decide) true).nq q input ws else q
  acts := fun q input ws j => if consume then (rule (by decide) true).acts q input ws j else []
  len_le := by
    intro q input ws j
    split
    · exact (rule (by decide) true).len_le q input ws j
    · simp

noncomputable def firstChange (consume : Bool) :
    PalPeg.LocalRoleRouting.RoleChange (Fin 2) CoreControl Γm tapeCountM 32 :=
  fun q input ws => if consume then change q input ws else Equiv.refl _

noncomputable def plan (consume : Bool) :
    ActRule (Fin 2) (PalPeg.LocalRoleRouting.Control CoreControl tapeCountM) Γm tapeCountM 64 :=
  seqRule (routeRule (firstRule consume) (firstChange consume))
    (routeRule (rule (K := 32) (by decide) false) change)

def firstSpare (consume : Bool) (wm : PalPeg.GalilScaffoldChainWatch.State) (spare : Counter) : Counter :=
  if consume then nextSpare wm.machine.control spare else spare

def firstAge (consume : Bool) (wm : PalPeg.GalilScaffoldChainWatch.State) (age : ℕ) : ℕ :=
  if consume then nextAge wm.machine.control age else age

def pairSpare (consume : Bool) (wm : PalPeg.GalilScaffoldChainWatch.State) (a : Fin 3) (spare : Counter) : Counter :=
  nextSpare (beforeImmediateWatch consume wm a).machine.control (firstSpare consume wm spare)

def pairAge (consume : Bool) (wm : PalPeg.GalilScaffoldChainWatch.State) (a : Fin 3) (age : ℕ) : ℕ :=
  nextAge (beforeImmediateWatch consume wm a).machine.control (firstAge consume wm age)

def pairState (consume : Bool) (x : State GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State) (a b : Fin 3) :=
  stateAfter false (beforeImmediate consume x wm a) (beforeImmediateWatch consume wm a) b

def pairWatch (consume : Bool) (wm : PalPeg.GalilScaffoldChainWatch.State) (a b : Fin 3) :=
  watchAfter false (beforeImmediateWatch consume wm a) b

/-- The second quantum reads the phase, token and renamed snapshots produced
by the first. Both may cross a boundary, in either traversal direction. -/
theorem running_pair_ideal (consume : Bool) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (spare : Counter) (h age : ℕ) (hInv : Inv h age wm.machine.control spare)
    (henc : Running w (saved x wm.machine.control.boundary wm.machine.control.last spare) p)
    (a b : Fin 3)
    (hfirst : consume = true → PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hsecond : PalPeg.GalilScaffoldChainConsume.symbol
      (beforeImmediateWatch consume wm a).machine.control.period.focus = some b) :
    let next := pairWatch consume wm a b
    Running w (saved (pairState consume x wm a b) next.machine.control.boundary next.machine.control.last
      (pairSpare consume wm a spare))
      (PalPeg.LocalRoleRouting.decode (idealStep (plan consume) blankM ((Equiv.refl _, p.1), p.2) none)) ∧
      Inv h (pairAge consume wm a age) next.machine.control (pairSpare consume wm a spare) := by
  have hfirstResult :
      Running w (saved (beforeImmediate consume x wm a)
        (beforeImmediateWatch consume wm a).machine.control.boundary
        (beforeImmediateWatch consume wm a).machine.control.last (firstSpare consume wm spare))
        (logicalStep (firstRule consume) (firstChange consume) blankM p none) ∧
      Inv h (firstAge consume wm age) (beforeImmediateWatch consume wm a).machine.control
        (firstSpare consume wm spare) := by
    cases consume with
    | false =>
      simpa only [beforeImmediate, beforeImmediateWatch, firstSpare, firstAge,
        Bool.false_eq_true, if_false, logicalStep, idealStep, firstRule, firstChange,
        Equiv.refl_apply, actList, Prod.eta] using And.intro henc hInv
    | true =>
      exact running (K := 32) (by decide) (by decide) true w x p wm hchain spare h age hInv henc a (hfirst rfl)
  have hwatch : (beforeImmediate consume x wm a).vm.chain = .watch (beforeImmediateWatch consume wm a) := by
    cases consume <;> simp [beforeImmediate, beforeImmediateWatch, stateAfter, hchain]
  have hsecondResult := running (K := 32) (by decide) (by decide) false w
    (beforeImmediate consume x wm a) (logicalStep (firstRule consume) (firstChange consume) blankM p none)
    (beforeImmediateWatch consume wm a) hwatch (firstSpare consume wm spare) h (firstAge consume wm age)
    hfirstResult.2 hfirstResult.1 b hsecond
  have hmargin : ∀ j, 32 + 32 ≤ pos (p.2 j) := fun j =>
    (show 64 ≤ margin by decide).trans (running_margin (running_core henc) j)
  rw [plan, PalPeg.LocalRoleFusion.decode_seqRule _ _ _ _ blankM _ none hmargin]
  exact hsecondResult

/-- A single compiled sweep implements the optional internal quantum followed
by the immediate quantum, with all snapshot copies and the next invariant. -/
theorem running_pair (consume : Bool) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalShiftDispatch.RoutedCore)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (spare : Counter) (h age : ℕ) (hInv : Inv h age wm.machine.control spare)
    (henc : Running w (saved x wm.machine.control.boundary wm.machine.control.last spare)
      (PalPeg.LocalRoleRouting.decode p)) (a b : Fin 3)
    (hfirst : consume = true → PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hsecond : PalPeg.GalilScaffoldChainConsume.symbol
      (beforeImmediateWatch consume wm a).machine.control.period.focus = some b) :
    let next := pairWatch consume wm a b
    Running w (saved (pairState consume x wm a b) next.machine.control.boundary next.machine.control.last
      (pairSpare consume wm a spare))
      (PalPeg.LocalRoleRouting.decode ((PalPeg.LocalRoleFusion.compiled (plan consume)).apply blankM p none)) ∧
      Inv h (pairAge consume wm a age) next.machine.control (pairSpare consume wm a spare) := by
  obtain ⟨hideal, hInvNext⟩ := running_pair_ideal consume w x (PalPeg.LocalRoleRouting.decode p)
    wm hchain spare h age hInv henc a b hfirst hsecond
  have hmargin : ∀ j, 64 ≤ pos ((PalPeg.LocalRoleRouting.decode p).2 j) := fun j =>
    (show 64 ≤ margin by decide).trans (running_margin (running_core henc) j)
  obtain ⟨hcontrol, htapes⟩ := PalPeg.LocalRoleFusion.compiled_apply (plan consume) blankM p none hmargin
  refine ⟨?_, hInvNext⟩
  exact PalPeg.MachineStep.sweepClosed_sweepClosure blankM (PalPeg.PhysicalCacheInvariant.CoreInv w)
    _ _ _ hideal hcontrol.symm htapes

theorem pair_control (consume : Bool) (x : State GalilVM)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (a b : Fin 3)
    (hfirst : consume = true → PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hsecond : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right (PalPeg.PhysicalWatchStep.afterInternal consume wm).machine.verifier) = some b) :
    (pairWatch consume wm a b).machine.control =
      (PalPeg.GalilScaffoldChainWatch.immediate (PalPeg.PhysicalWatchStep.afterInternal consume wm)).machine.control := by
  have hstates := congrArg (fun z : State GalilVM => match z.vm.chain with
    | .watch v => some v.machine.control
    | _ => none) (PalPeg.PhysicalWatchStep.pair_state consume x wm a b hfirst hsecond)
  change some (pairWatch consume wm a b).machine.control = some _ at hstates
  exact Option.some.inj hstates

def goodSpare (consume : Bool) (wm : PalPeg.GalilScaffoldChainWatch.State) (spare : Counter) : Counter :=
  nextSpare (PalPeg.PhysicalWatchStep.afterInternal consume wm).machine.control (firstSpare consume wm spare)

def goodAge (consume : Bool) (wm : PalPeg.GalilScaffoldChainWatch.State) (age : ℕ) : ℕ :=
  nextAge (PalPeg.PhysicalWatchStep.afterInternal consume wm).machine.control (firstAge consume wm age)

theorem before_control (consume : Bool) (wm : PalPeg.GalilScaffoldChainWatch.State) (a : Fin 3)
    (hread : consume = true → PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a) :
    (beforeImmediateWatch consume wm a).machine.control =
      (PalPeg.PhysicalWatchStep.afterInternal consume wm).machine.control := by
  cases consume with
  | false => rfl
  | true =>
    simp [beforeImmediateWatch, watchAfter, PalPeg.PhysicalWatchStep.afterInternal,
      PalPeg.GalilScaffoldChainWatch.caught, PalPeg.GalilScaffoldChainVerifier.consume, hread rfl]

/-- The source Good facts identify this fused row with the actual two watch
consumes. The verifier is held only until the existing view stage runs. -/
theorem running_good_ideal (consume : Bool) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (spare : Counter) (h age : ℕ) (hInv : Inv h age wm.machine.control spare)
    (henc : Running w (saved x wm.machine.control.boundary wm.machine.control.last spare) p)
    (hfirst : consume = true → PalPeg.GalilScaffoldChainWatch.Good wm)
    (hsecond : PalPeg.GalilScaffoldChainWatch.Good (PalPeg.PhysicalWatchStep.afterInternal consume wm)) :
    let next := PalPeg.GalilScaffoldChainWatch.immediate (PalPeg.PhysicalWatchStep.afterInternal consume wm)
    Inv h (goodAge consume wm age) next.machine.control (goodSpare consume wm spare) ∧
      Running w (saved (PalPeg.PhysicalShiftStart.pairedState consume x wm)
        next.machine.control.boundary next.machine.control.last (goodSpare consume wm spare))
        (PalPeg.LocalRoleRouting.decode (idealStep (plan consume) blankM ((Equiv.refl _, p.1), p.2) none)) := by
  obtain ⟨_, b, htokenB, hreadB⟩ := hsecond
  have finish (a : Fin 3)
      (htokenA : consume = true → PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
      (hreadA : consume = true → PalPeg.GalilScaffoldInputHead.read
        (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
      (hnext : PalPeg.GalilScaffoldChainConsume.symbol
        (beforeImmediateWatch consume wm a).machine.control.period.focus = some b) :
      let next := PalPeg.GalilScaffoldChainWatch.immediate (PalPeg.PhysicalWatchStep.afterInternal consume wm)
      Inv h (goodAge consume wm age) next.machine.control (goodSpare consume wm spare) ∧
        Running w (saved (PalPeg.PhysicalShiftStart.pairedState consume x wm)
          next.machine.control.boundary next.machine.control.last (goodSpare consume wm spare))
          (PalPeg.LocalRoleRouting.decode (idealStep (plan consume) blankM ((Equiv.refl _, p.1), p.2) none)) := by
    obtain ⟨hresult, hnextInv⟩ := running_pair_ideal consume w x p wm hchain spare h age hInv henc a b htokenA hnext
    have hcontrol := pair_control consume x wm a b hreadA hreadB
    have hstate : pairState consume x wm a b = PalPeg.PhysicalShiftStart.pairedState consume x wm :=
      PalPeg.PhysicalWatchStep.pair_state consume x wm a b hreadA hreadB
    rw [hcontrol] at hnextInv hresult
    rw [hstate] at hresult
    have hbefore := before_control consume wm a hreadA
    simpa only [pairAge, pairSpare, hbefore, goodAge, goodSpare] using And.intro hnextInv hresult
  cases consume with
  | false => exact finish b (by simp) (by simp) htokenB
  | true =>
    obtain ⟨_, a, htokenA, hreadA⟩ := hfirst rfl
    apply finish a (fun _ => htokenA) (fun _ => hreadA)
    simpa [beforeImmediateWatch, watchAfter, PalPeg.PhysicalWatchStep.afterInternal,
      PalPeg.GalilScaffoldChainWatch.caught, PalPeg.GalilScaffoldChainVerifier.consume, hreadA] using htokenB

/-- info: 'PalPeg.PhysicalSnapshotWatch.running_good_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_good_ideal

/-- info: 'PalPeg.PhysicalSnapshotWatch.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running

/-- info: 'PalPeg.PhysicalSnapshotWatch.running_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_pair

end PalPeg.PhysicalSnapshotWatch
