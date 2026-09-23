import PalPeg.LocalRoleFusion
import PalPeg.PhysicalBoundaryRotate

/-!
# The two successful watch consumes within a comparison tick

The first consume pays lag; the immediate consume credits margin. Each updates
its distance, period and spare before renaming the boundary snapshots. The
second reads the renamed intermediate tapes through LocalRoleFusion. The
flattened plan has the existing micro radius 128 and uses the same 118 slots.

This is the nonhead action plan. Selecting it in the comparison dispatcher,
combining its counters with the entry updates and completing CoreInv remain
separate obligations. No extra physical tick or verifier movement is introduced.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalWatchActions
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalCounterCache (increments increments_length)
open PalPeg.PhysicalBoundaryRotate (rotatePol)
open PalPeg.GalilScaffoldCounter (Counter inc dec)
open PalPeg.LocalCounter (Seg absCtr)
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.LocalRoleFusion (routeRule logicalStep)
variable {fb db K : ℕ}

noncomputable def event (ws : Fin tapeCountM → Window Γm K) : Bool :=
  PalPeg.GalilScaffoldChainPeriod.isFirst (decToken (centreRead ws periodSlot)) ||
    PalPeg.GalilScaffoldChainConsume.isLast (decToken (centreRead ws periodSlot))

noncomputable def forward (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm K) : Bool :=
  if event ws then PalPeg.GalilScaffoldChainPeriod.isFirst (decToken (centreRead ws periodSlot))
  else q.chainForward

/-- Internal consumption debits lag; immediate consumption credits margin. -/
def balanceIndex (internal : Bool) : Fin 16 := if internal then 11 else 12

noncomputable def spare (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm K) :=
  increments (PalPeg.ChainBoundaryCache.rate q.chainPhase) (q.polarity 10)
    (ws (slotIndex (counterSlot 10)))

noncomputable def balanceSign (internal : Bool) (q : QPhys fb db)
    (ws : Fin tapeCountM → Window Γm K) : Bool :=
  if internal then decSignAt (q.polarity 11) (counterSlot 11) ws else incSign q.polarity 12 ws

noncomputable def signs (internal : Bool) (q : QPhys fb db)
    (ws : Fin tapeCountM → Window Γm K) : Fin 16 → Bool := fun c =>
  if c = 10 then (spare q ws).1 else if c = 13 then incSign q.polarity 13 ws
  else if c = balanceIndex internal then balanceSign internal q ws else q.polarity c

noncomputable def next (internal : Bool) (q : QPhys fb db)
    (ws : Fin tapeCountM → Window Γm K) : QPhys fb db :=
  {q with chainPhase := if event ws then PalPeg.GalilScaffoldChainConsume.advancePhase q.chainPhase else q.chainPhase, chainForward := forward q ws, polarity := if event ws then rotatePol (signs internal q ws) else signs internal q ws}

noncomputable def actions (internal : Bool) (q : QPhys fb db)
    (ws : Fin tapeCountM → Window Γm K) (j : Fin tapeCountM) : List (Act Γm) :=
  if j = slotIndex (counterSlot 10) then (spare q ws).2
  else if j = slotIndex (counterSlot 13) then [incAct q 13 ws]
  else if j = slotIndex (counterSlot (balanceIndex internal)) then
    [if internal then decAct q 11 ws else incAct q 12 ws]
  else if j = slotIndex periodSlot then [some (centreRead ws periodSlot, if forward q ws then .right else .left)]
  else []

theorem actions_length (internal : Bool) (q : QPhys fb db)
    (ws : Fin tapeCountM → Window Γm K) (j : Fin tapeCountM) :
    (actions internal q ws j).length ≤ 3 := by
  unfold actions
  split_ifs
  · rw [spare, increments_length]
    exact PalPeg.ChainBoundaryCache.rate_le _
  all_goals simp

noncomputable def rule (internal : Bool) (hK : 3 ≤ K) :
    ActRule (Fin 2) (QPhys fb db) Γm tapeCountM K where
  nq := fun q _ ws => next internal q ws
  acts := fun q _ ws => actions internal q ws
  len_le := fun q _ ws j => (actions_length internal q ws j).trans hK

noncomputable def change : PalPeg.LocalRoleRouting.RoleChange (Fin 2) (QPhys fb db) Γm tapeCountM K :=
  fun _ _ ws => if event ws then PalPeg.PhysicalRoles.boundaryRoles else Equiv.refl _

/-- The internal row is the existing successful consume row with its spare
prepared concurrently. This equality includes period direction at boundaries. -/
theorem internal_actions_eq (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm K)
    (hc : chainConsumesTest q ws = true) (hm : watchVerdictTest q ws = some true) :
    actions true q ws = fun j => if j = slotIndex (counterSlot 10) then (spare q ws).2
      else scanConsumeActs q ws j := by
  funext j
  have hf : (scanConsumeNext q ws).chainForward = forward q ws := by
    simp only [scanConsumeNext, hm, forward, event]
    rfl
  by_cases h10 : j = slotIndex (counterSlot 10)
  · simp only [actions, h10, if_true]
  · simp only [actions, h10, if_false, scanConsumeActs, hc, hm, if_true,
      balanceIndex, hf]
    by_cases h11 : j = slotIndex (counterSlot 11)
    · subst j
      simp [counterSlot]
    · simp only [h11, if_false]

/-- The actions for the counter which distinguishes internal from immediate
consumption are selected independently of the boundary event. -/
theorem actions_balance (internal : Bool) (q : QPhys fb db)
    (ws : Fin tapeCountM → Window Γm K) :
    actions internal q ws (slotIndex (counterSlot (balanceIndex internal))) =
      [if internal then decAct q 11 ws else incAct q 12 ws] := by
  cases internal <;> simp [actions, balanceIndex, counterSlot]

theorem actions_distance (internal : Bool) (q : QPhys fb db)
    (ws : Fin tapeCountM → Window Γm K) :
    actions internal q ws (slotIndex (counterSlot 13)) = [incAct q 13 ws] := by
  simp [actions, counterSlot]

theorem actions_period (internal : Bool) (q : QPhys fb db)
    (ws : Fin tapeCountM → Window Γm K) :
    actions internal q ws (slotIndex periodSlot) =
      [some (centreRead ws periodSlot, if forward q ws then .right else .left)] := by
  simp [actions, counterSlot, periodSlot]

theorem signs_balance (internal : Bool) (q : QPhys fb db)
    (ws : Fin tapeCountM → Window Γm K) :
    (next internal q ws).polarity (balanceIndex internal) = balanceSign internal q ws := by
  cases internal <;> cases he : event ws <;> simp [next, he, rotatePol, signs, balanceIndex]

theorem signs_distance (internal : Bool) (q : QPhys fb db)
    (ws : Fin tapeCountM → Window Γm K) :
    (next internal q ws).polarity 13 = incSign q.polarity 13 ws := by
  cases he : event ws <;> simp [next, he, rotatePol, signs]

/-- Signed lag decrement or margin increment, including zero crossings. -/
theorem balance_tape {padding : ℕ} (hK : 1 ≤ K) (hpad : K ≤ padding + 1)
    (internal : Bool) (q : QPhys fb db) (T : Slot → STape Γm)
    (seg : STape Seg) (value : Counter)
    (ha : absCtr seg (q.polarity (balanceIndex internal)) = value)
    (ht : T (counterSlot (balanceIndex internal)) = padLeft padding (mapTape encSeg seg)) :
    let ws := fun j => readWin blankM K (tapesOf T j)
    ∃ result : STape Seg,
      absCtr result ((next internal q ws).polarity (balanceIndex internal)) =
        (if internal then dec value else inc value) ∧
      actList blankM (T (counterSlot (balanceIndex internal)))
        (actions internal q ws (slotIndex (counterSlot (balanceIndex internal)))) =
          padLeft padding (mapTape encSeg result) := by
  dsimp only
  rw [actions_balance, signs_balance]
  cases internal with
  | false =>
    simp only [balanceIndex, Bool.false_eq_true, if_false, balanceSign]
    exact counter_inc_at q.polarity 12 _ seg value ha
      (incSign_eq hK hpad q.polarity 12 T seg ht) _ ht
  | true =>
    simpa only [balanceIndex, if_true, balanceSign, decAct, decActAt] using
      counter_dec_at q.polarity 11 _ seg value ha
        (decSignAt_eq hK hpad (q.polarity 11) 11 T seg ht) _ ht

theorem distance_tape {padding : ℕ} (hK : 1 ≤ K) (hpad : K ≤ padding + 1)
    (internal : Bool) (q : QPhys fb db) (T : Slot → STape Γm)
    (seg : STape Seg) (value : Counter)
    (ha : absCtr seg (q.polarity 13) = value)
    (ht : T (counterSlot 13) = padLeft padding (mapTape encSeg seg)) :
    let ws := fun j => readWin blankM K (tapesOf T j)
    ∃ result : STape Seg, absCtr result ((next internal q ws).polarity 13) = inc value ∧
      actList blankM (T (counterSlot 13)) (actions internal q ws (slotIndex (counterSlot 13))) =
        padLeft padding (mapTape encSeg result) := by
  dsimp only
  rw [actions_distance, signs_distance]
  exact counter_inc_at q.polarity 13 _ seg value ha
    (incSign_eq hK hpad q.polarity 13 T seg ht) _ ht

/-- The period action works in either direction. Its only left-side condition
is the existing cursor invariant, which supplies a real cell before the head. -/
theorem period_tape {padding : ℕ} (hpad : K ≤ padding)
    (internal : Bool) (x : PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (q : QPhys fb db) (T : Slot → STape Γm)
    (he : EncTapes padding x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (tape : PalPeg.GalilScaffoldChainPeriod.Tape) (hp : periodOf x = some tape)
    (hl : forward q (fun j => readWin blankM K (tapesOf T j)) = false → tape.left ≠ []) :
    let ws := fun j => readWin blankM K (tapesOf T j)
    actList blankM (T periodSlot) (actions internal q ws (slotIndex periodSlot)) =
      padLeft padding (mapTape encToken (encPeriod
        (if forward q ws then PalPeg.GalilScaffoldChainPeriod.moveRight tape
         else PalPeg.GalilScaffoldChainPeriod.moveLeft tape))) := by
  dsimp only
  rw [actions_period, centreRead_periodSlot he hpad tape hp]
  cases hf : forward q (fun j => readWin blankM K (tapesOf T j)) with
  | true =>
    simp only [if_true]
    rw [encPeriod_moveRight, padded_token_right, ← he.period tape hp]
    rfl
  | false =>
    simp only [Bool.false_eq_true, if_false]
    rw [PalPeg.PhysicalConsumeStage.encPeriod_moveLeft tape (hl hf),
      PalPeg.PhysicalConsumeStage.padded_token_left padding (encPeriod tape) tape.focus (hl hf),
      ← he.period tape hp]
    rfl

/-- The bounded spare update is valid on swept tapes as well as ideal witnesses. -/
theorem spare_advance (hK : 3 ≤ K) (hpad : K ≤ margin) (q : QPhys fb db)
    (T : Fin tapeCountM → STape Γm) (value : Counter)
    (hr : PalPeg.PhysicalSpare.Rep (q.polarity 10) value (T (slotIndex (counterSlot 10)))) :
    let ws := fun j => readWin blankM K (T j)
    PalPeg.PhysicalSpare.Rep (spare q ws).1
      (PalPeg.ChainBoundaryCache.advanceCounter (PalPeg.ChainBoundaryCache.rate q.chainPhase) value)
      (actList blankM (T (slotIndex (counterSlot 10))) (spare q ws).2) := by
  obtain ⟨seg, ha, ht⟩ := hr
  have hw := readWin_congr_teqG (K := K) ht
  have hc : spare q (fun j => readWin blankM K (T j)) =
      increments (PalPeg.ChainBoundaryCache.rate q.chainPhase) (q.polarity 10)
        (readWin blankM K (padLeft margin (mapTape encSeg seg))) := by
    unfold spare
    rw [hw]
  dsimp only
  rw [hc]
  obtain ⟨result, habs, hacts⟩ := PalPeg.PhysicalCounterCache.increments_encode
    (PalPeg.ChainBoundaryCache.rate q.chainPhase)
    ((PalPeg.ChainBoundaryCache.rate_le _).trans hK) hpad (q.polarity 10) seg seg value ha ha
  refine ⟨result, habs, ?_⟩
  rw [← hacts]
  exact PalPeg.PhysicalSpare.actList_teq blankM ht _

/-- The same cache invariant survives either consume, including a boundary
exchange between the two stages. No verifier movement is assumed here. -/
theorem logical_cache (hK : 3 ≤ K) (hpad : K ≤ margin) (internal : Bool)
    (q : QPhys fb db) (T : Fin tapeCountM → STape Γm)
    (s : PalPeg.GalilScaffoldChainConsume.State) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol s.period.focus = some a)
    (hphase : q.chainPhase = s.phase)
    (hevent : event (fun j => readWin blankM K (T j)) = PalPeg.ChainBoundaryCache.boundaryEvent s)
    (h age : ℕ) (value : Counter) (hi : PalPeg.ChainBoundaryCache.Inv h age s value)
    (hr : PalPeg.PhysicalSpare.Rep (q.polarity 10) value (T (slotIndex (counterSlot 10))))
    (hlast : PalPeg.PhysicalSpare.Rep (q.polarity 15) s.last (T (slotIndex (counterSlot 15)))) :
    let result := logicalStep (rule internal hK) change blankM (q,T) none
    PalPeg.ChainBoundaryCache.Inv h (PalPeg.ChainBoundaryCache.nextAge s age)
      (PalPeg.GalilScaffoldChainConsume.consume s (some a)) (PalPeg.ChainBoundaryCache.nextSpare s value) ∧
    PalPeg.PhysicalSpare.Rep (result.1.polarity 10) (PalPeg.ChainBoundaryCache.nextSpare s value)
      (result.2 (slotIndex (counterSlot 10))) := by
  dsimp only
  refine ⟨PalPeg.ChainBoundaryCache.inv_consume hi a htok, ?_⟩
  cases hb : PalPeg.ChainBoundaryCache.boundaryEvent s with
  | false =>
    have hn := spare_advance hK hpad q T value hr
    simp only [PalPeg.ChainBoundaryCache.nextSpare, hb, Bool.false_eq_true, if_false]
    simpa only [logicalStep, idealStep, rule, next, change, hevent, hb, Bool.false_eq_true,
      if_false, Equiv.refl_apply, signs, actions, if_true, hphase] using hn
  | true =>
    cases internal <;> simpa [logicalStep, idealStep, rule, next, change, hevent, hb,
      PalPeg.ChainBoundaryCache.nextSpare, PalPeg.PhysicalRoles.boundaryRoles_spare,
      rotatePol, signs, actions, balanceIndex, counterSlot] using hlast

/-- At FIRST/LAST the rebuilt spare becomes the new distance snapshot and
the old boundary becomes last. The control signs follow the very same roles. -/
theorem logical_boundary (hK : 3 ≤ K) (hpad : K ≤ margin) (internal : Bool)
    (q : QPhys fb db) (T : Fin tapeCountM → STape Γm)
    (s : PalPeg.GalilScaffoldChainConsume.State)
    (hphase : q.chainPhase = s.phase)
    (hevent : event (fun j => readWin blankM K (T j)) = true)
    (hb : PalPeg.ChainBoundaryCache.boundaryEvent s = true)
    (h age : ℕ) (value : Counter) (hi : PalPeg.ChainBoundaryCache.Inv h age s value)
    (hd : PalPeg.GalilScaffoldCounter.Canonical s.distance)
    (hr : PalPeg.PhysicalSpare.Rep (q.polarity 10) value (T (slotIndex (counterSlot 10))))
    (hboundary : PalPeg.PhysicalSpare.Rep (q.polarity 14) s.boundary (T (slotIndex (counterSlot 14)))) :
    let result := logicalStep (rule internal hK) change blankM (q,T) none
    PalPeg.PhysicalSpare.Rep (result.1.polarity 14) (inc s.distance)
      (result.2 (slotIndex (counterSlot 14))) ∧
    PalPeg.PhysicalSpare.Rep (result.1.polarity 15) s.boundary
      (result.2 (slotIndex (counterSlot 15))) := by
  have hcanonical : PalPeg.GalilScaffoldCounter.Canonical value := by
    obtain ⟨seg, ha, _⟩ := hr
    rw [← ha]
    exact PalPeg.LocalCounter.absCtr_canonical _ _
  have hn := spare_advance hK hpad q T value hr
  dsimp only at hn
  rw [hphase, PalPeg.ChainBoundaryCache.spare_eq_at_boundary hi hb hcanonical hd] at hn
  dsimp only
  constructor
  · simpa [logicalStep, idealStep, rule, next, change, hevent,
      PalPeg.PhysicalRoles.boundaryRoles_boundary, rotatePol, signs, actions] using hn
  · cases internal <;> simpa [logicalStep, idealStep, rule, next, change, hevent,
      PalPeg.PhysicalRoles.boundaryRoles_last, rotatePol, signs, actions,
      balanceIndex, counterSlot] using hboundary

/-- The finite phase and direction agree with successful abstract consumption,
for plain, FIRST and LAST symbols in either walking direction. -/
theorem control_matches (internal : Bool) (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm K)
    (s : PalPeg.GalilScaffoldChainConsume.State) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol s.period.focus = some a)
    (hread : decToken (centreRead ws periodSlot) = s.period.focus)
    (hphase : q.chainPhase = s.phase) (hforward : q.chainForward = s.forward)
    (hbroken : q.chainBroken = s.broken) :
    ((next internal q ws).chainPhase, (next internal q ws).chainForward, (next internal q ws).chainBroken) =
      ((PalPeg.GalilScaffoldChainConsume.consume s (some a)).phase,
        (PalPeg.GalilScaffoldChainConsume.consume s (some a)).forward,
        (PalPeg.GalilScaffoldChainConsume.consume s (some a)).broken) := by
  simp [next, event, forward, PalPeg.GalilScaffoldChainConsume.consume, htok,
    hread, hphase, hforward, hbroken]

theorem actions_other (internal : Bool) (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm K)
    (j : Fin tapeCountM) (h10 : j ≠ slotIndex (counterSlot 10))
    (h11 : j ≠ slotIndex (counterSlot 11)) (h12 : j ≠ slotIndex (counterSlot 12))
    (h13 : j ≠ slotIndex (counterSlot 13)) (hp : j ≠ slotIndex periodSlot) :
    actions internal q ws j = [] := by
  cases internal <;> simp [actions, balanceIndex, h10, h11, h12, h13, hp]

theorem change_other (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm K) (input : Option (Fin 2))
    (j : Fin tapeCountM) (h10 : j ≠ slotIndex (counterSlot 10))
    (h14 : j ≠ slotIndex (counterSlot 14)) (h15 : j ≠ slotIndex (counterSlot 15)) :
    change q input ws j = j := by
  unfold change
  split
  · exact PalPeg.PhysicalRoles.boundaryRoles_other j h14 h15 h10
  · rfl

/-- Every head, program, mirror and non-chain counter retains its own tape. -/
theorem logical_other (hK : 3 ≤ K) (internal : Bool)
    (p : QPhys fb db × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (j : Fin tapeCountM) (h10 : j ≠ slotIndex (counterSlot 10))
    (h11 : j ≠ slotIndex (counterSlot 11)) (h12 : j ≠ slotIndex (counterSlot 12))
    (h13 : j ≠ slotIndex (counterSlot 13)) (h14 : j ≠ slotIndex (counterSlot 14))
    (h15 : j ≠ slotIndex (counterSlot 15)) (hp : j ≠ slotIndex periodSlot) :
    (logicalStep (rule internal hK) change blankM p input).2 j = p.2 j := by
  dsimp only [logicalStep, idealStep, rule]
  rw [change_other _ _ _ j h10 h14 h15, actions_other internal _ _ j h10 h11 h12 h13 hp]
  rfl

/-- The pre-comparison consume may be absent when lag is already zero. -/
noncomputable def firstRule (consume : Bool) :
    ActRule (Fin 2) (QPhys fb db) Γm tapeCountM 32 where
  nq := fun q input ws => if consume then (rule true (by decide)).nq q input ws else q
  acts := fun q input ws j => if consume then (rule true (by decide)).acts q input ws j else []
  len_le := by
    intro q input ws j
    split
    · exact (rule true (by decide)).len_le q input ws j
    · simp

noncomputable def firstChange (consume : Bool) :
    PalPeg.LocalRoleRouting.RoleChange (Fin 2) (QPhys fb db) Γm tapeCountM 32 :=
  fun q input ws => if consume then change q input ws else Equiv.refl _

theorem firstChange_other (consume : Bool) (q : QPhys fb db)
    (ws : Fin tapeCountM → Window Γm 32) (input : Option (Fin 2))
    (j : Fin tapeCountM) (h10 : j ≠ slotIndex (counterSlot 10))
    (h14 : j ≠ slotIndex (counterSlot 14)) (h15 : j ≠ slotIndex (counterSlot 15)) :
    firstChange consume q input ws j = j := by
  unfold firstChange
  split
  · exact change_other q ws input j h10 h14 h15
  · rfl

theorem first_logical_other (consume : Bool)
    (p : QPhys fb db × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (j : Fin tapeCountM) (h10 : j ≠ slotIndex (counterSlot 10))
    (h11 : j ≠ slotIndex (counterSlot 11)) (h12 : j ≠ slotIndex (counterSlot 12))
    (h13 : j ≠ slotIndex (counterSlot 13)) (h14 : j ≠ slotIndex (counterSlot 14))
    (h15 : j ≠ slotIndex (counterSlot 15)) (hp : j ≠ slotIndex periodSlot) :
    (logicalStep (firstRule consume) (firstChange consume) blankM p input).2 j = p.2 j := by
  dsimp only [logicalStep, idealStep]
  rw [firstChange_other _ _ _ _ j h10 h14 h15]
  cases consume with
  | false => rfl
  | true =>
    change actList blankM (p.2 j) (actions true p.1 _ j) = p.2 j
    rw [actions_other true _ _ j h10 h11 h12 h13 hp]
    rfl

/-- The temporary role register is compiled away before emitting QPhys. -/
noncomputable def plan (consume : Bool) :
    ActRule (Fin 2) (PalPeg.LocalRoleRouting.Control (QPhys fb db) tapeCountM) Γm tapeCountM 64 :=
  seqRule (routeRule (firstRule consume) (firstChange consume))
    (routeRule (rule (K := 32) false (by decide)) change)

noncomputable def fusedRule (consume : Bool) :
    ActRule (Fin 2) (QPhys fb db) Γm tapeCountM 64 :=
  PalPeg.LocalRoleFusion.flatten (plan consume)

noncomputable def fusedRoles (consume : Bool) :
    PalPeg.LocalRoleRouting.RoleChange (Fin 2) (QPhys fb db) Γm tapeCountM 64 :=
  PalPeg.LocalRoleFusion.finalRoles (plan consume)

theorem fusedRoles_other (consume : Bool) (q : QPhys fb db)
    (ws : Fin tapeCountM → Window Γm 64) (input : Option (Fin 2))
    (j : Fin tapeCountM) (h10 : j ≠ slotIndex (counterSlot 10))
    (h14 : j ≠ slotIndex (counterSlot 14)) (h15 : j ≠ slotIndex (counterSlot 15)) :
    fusedRoles consume q input ws j = j := by
  simp only [fusedRoles, PalPeg.LocalRoleFusion.finalRoles, plan, seqRule, routeRule,
    Equiv.trans_apply, change_other _ _ _ j h10 h14 h15,
    firstChange_other _ _ _ _ j h10 h14 h15, Equiv.refl_apply]

/-- Even if both consumes cross a boundary, no tape receives more than six
primitive actions. The larger radius is used to read the intermediate windows. -/
theorem fused_actions_length (consume : Bool) (q : QPhys fb db)
    (ws : Fin tapeCountM → Window Γm 64) (input : Option (Fin 2)) (j : Fin tapeCountM) :
    ((fusedRule consume).acts q input ws j).length ≤ 6 := by
  simp only [fusedRule, PalPeg.LocalRoleFusion.flatten, plan, seqRule, routeRule, firstRule, rule,
    List.length_append]
  split
  · exact Nat.add_le_add (actions_length _ _ _ _) (actions_length _ _ _ _)
  · simpa using (actions_length false _ _ _).trans (by decide : 3 ≤ 6)

/-- Exact two-stage nonhead semantics before the one real sweep. -/
theorem plan_ideal (consume : Bool) (p : QPhys fb db × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (hm : ∀ j, 64 ≤ pos (p.2 j)) :
    PalPeg.LocalRoleRouting.decode
      (idealStep (plan consume) blankM ((Equiv.refl _,p.1),p.2) input) =
    logicalStep (rule (K := 32) false (by decide)) change blankM
      (logicalStep (firstRule consume) (firstChange consume) blankM p input) none := by
  exact PalPeg.LocalRoleFusion.decode_seqRule _ _ _ _ blankM _ input hm

/-- The concrete plan survives the actual routed sweep, for arbitrary source
roles. The right-hand side includes the intermediate boundary exchange. -/
theorem fused_apply (consume : Bool)
    (p : PalPeg.LocalRoleRouting.Config (QPhys fb db) Γm tapeCountM) (input : Option (Fin 2))
    (hm : ∀ j, 64 ≤ pos ((PalPeg.LocalRoleRouting.decode p).2 j)) :
    let ideal := logicalStep (rule (K := 32) false (by decide)) change blankM
      (logicalStep (firstRule consume) (firstChange consume) blankM
        (PalPeg.LocalRoleRouting.decode p) input) none
    let actual := PalPeg.LocalRoleRouting.decode
      ((PalPeg.LocalRoleFusion.compiled (plan consume)).apply blankM p input)
    actual.1 = ideal.1 ∧ ∀ j, TEqG blankM (ideal.2 j) (actual.2 j) := by
  exact PalPeg.LocalRoleFusion.compiled_seq _ _ _ _ blankM p input hm

/-- The actual single sweep leaves unrelated logical tapes observationally
unchanged, so the existing view executor can still own all four head banks. -/
theorem fused_other (consume : Bool)
    (p : PalPeg.LocalRoleRouting.Config (QPhys fb db) Γm tapeCountM) (input : Option (Fin 2))
    (hm : ∀ j, 64 ≤ pos ((PalPeg.LocalRoleRouting.decode p).2 j))
    (j : Fin tapeCountM) (h10 : j ≠ slotIndex (counterSlot 10))
    (h11 : j ≠ slotIndex (counterSlot 11)) (h12 : j ≠ slotIndex (counterSlot 12))
    (h13 : j ≠ slotIndex (counterSlot 13)) (h14 : j ≠ slotIndex (counterSlot 14))
    (h15 : j ≠ slotIndex (counterSlot 15)) (hp : j ≠ slotIndex periodSlot) :
    TEqG blankM ((PalPeg.LocalRoleRouting.decode p).2 j)
      ((PalPeg.LocalRoleRouting.decode
        ((PalPeg.LocalRoleFusion.compiled (plan consume)).apply blankM p input)).2 j) := by
  have ht := (fused_apply consume p input hm).2 j
  rw [logical_other (by decide) false _ _ j h10 h11 h12 h13 h14 h15 hp,
    first_logical_other consume _ _ j h10 h11 h12 h13 h14 h15 hp] at ht
  exact ht

/-- info: 'PalPeg.PhysicalWatchActions.logical_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms logical_boundary

/-- info: 'PalPeg.PhysicalWatchActions.logical_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms logical_cache

/-- info: 'PalPeg.PhysicalWatchActions.fused_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fused_apply

end PalPeg.PhysicalWatchActions
