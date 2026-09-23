import PalPeg.PhysicalSearchRecycle
import PalPeg.PhysicalBoundaryCount

/-! # Independent boundary snapshots on the reclaimed search tapes

The four search counters and the lower/span mirrors keep their existing slots.
The storage representative permits their values to change while search is
suspended. All six updates use the source windows of one bounded physical step.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalSearchSnapshots
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalRestartStorage
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter)
open PalPeg.Program (STape)
open PalPeg.Local (pos readWin Window)
open PalPeg.LocalCounter (Seg absCtr)
open PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.PhysicalCacheInvariant (CoreInv Running)
open PalPeg.PhysicalSearchRecycle (resetSlot)
open PalPeg.PhysicalCounterCache (increments increments_length increments_encode)
open PalPeg.ChainBoundaryCache (advanceCounter)

/-- Search storage, in the existing lower/span/work/debt order. -/
def index (i : Fin 4) : Fin 16 := ⟨5 + i.val, by omega⟩

def values (x : State GalilVM) (i : Fin 4) : Counter :=
  if i = 0 then x.vm.lower else if i = 1 then x.vm.search.span
  else if i = 2 then x.vm.search.work else x.vm.search.debt

def put (x : State GalilVM) (v : Fin 4 → Counter) : State GalilVM :=
  ⟨x.ctl, replace x.vm (v 0) (v 1) (v 2) (v 3)⟩

def signs (pol : Fin 16 → Bool) (bits : Fin 4 → Bool) (c : Fin 16) : Bool :=
  if c = 5 then bits 0 else if c = 6 then bits 1
  else if c = 7 then bits 2 else if c = 8 then bits 3 else pol c

def withSigns (q : CoreControl) (bits : Fin 4 → Bool) : CoreControl :=
  {q with polarity := signs q.polarity bits}

@[simp] theorem signs_index (pol : Fin 16 → Bool) (bits : Fin 4 → Bool) (i : Fin 4) :
    signs pol bits (index i) = bits i := by fin_cases i <;> rfl

@[simp] theorem counter_index (x : State GalilVM) (i : Fin 4) :
    counterOf x (index i) = some (values x i) := by fin_cases i <;> rfl

@[simp] theorem values_put (x : State GalilVM) (v : Fin 4 → Counter) (i : Fin 4) :
    values (put x v) i = v i := by fin_cases i <;> rfl

/-- Only the six reclaimed tapes and their four signs may differ. Certificates
for those tapes are supplied by the concrete update, never by a target Enc. -/
theorem tapes_put (x : State GalilVM) (q : CoreControl) (T U : Slot → STape Γm)
    (v : Fin 4 → Counter) (bits : Fin 4 → Bool)
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (hkeep : ∀ slot, resetSlot slot = false → U slot = T slot)
    (hc : ∀ i, ∃ seg : STape Seg, absCtr seg (bits i) = v i ∧
      U (counterSlot (index i)) = padLeft margin (mapTape encSeg seg))
    (hm : ∀ i : Fin 2, ∃ seg : STape Seg, absCtr seg (bits i.castSucc.castSucc) = v i.castSucc.castSucc ∧
      U (mirrorSlot ⟨3 + i.val, by omega⟩) = padLeft margin (mapTape encSeg seg)) :
    EncTapes margin (put x v) (signs q.polarity bits) q.gap q.micro q.fppLive q.dpLive U := by
  have hmargin : ∀ slot, margin ≤ pos (U slot) := by
    intro slot
    by_cases hr : resetSlot slot = false
    · rw [hkeep slot hr]; exact he.margins slot
    · unfold resetSlot at hr
      split at hr <;> try exact (hr rfl).elim
      · simp only [Bool.not_eq_false, decide_eq_true_eq] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · obtain ⟨seg, _, ht⟩ := hc 0
          simp [index, counterSlot, mirrorSlot] at ht
          rw [ht, pos_padLeft]; omega
        · obtain ⟨seg, _, ht⟩ := hc 1
          simp [index, counterSlot, mirrorSlot] at ht
          rw [ht, pos_padLeft]; omega
        · obtain ⟨seg, _, ht⟩ := hc 2
          simp [index, counterSlot, mirrorSlot] at ht
          rw [ht, pos_padLeft]; omega
        · obtain ⟨seg, _, ht⟩ := hc 3
          simp [index, counterSlot, mirrorSlot] at ht
          rw [ht, pos_padLeft]; omega
      · simp only [Bool.not_eq_false, decide_eq_true_eq] at hr
        rcases hr with rfl | rfl
        · obtain ⟨seg, _, ht⟩ := hm 0
          simp [index, counterSlot, mirrorSlot] at ht
          rw [ht, pos_padLeft]; omega
        · obtain ⟨seg, _, ht⟩ := hm 1
          simp [index, counterSlot, mirrorSlot] at ht
          rw [ht, pos_padLeft]; omega
  refine { margins := hmargin, heads := ?_, idleHead := ?_, fpp := ?_, dp := ?_, idleShape := ?_, counters := ?_, places := ?_, mirrors := ?_, period := ?_, answer := ?_ }
  · intro k head hh
    obtain ⟨view, vt, ha, hv, ht, hcells, hw⟩ := he.heads k head hh
    exact ⟨view, vt, ha, hv, fun j => by rw [hkeep _ rfl]; exact ht j, hcells, hw⟩
  · intro hh
    obtain ⟨view, vt, hv, ht, hcells, hw⟩ := he.idleHead hh
    exact ⟨view, vt, hv, fun j => by rw [hkeep _ rfl]; exact ht j, hcells, hw⟩
  · intro j
    rw [hkeep _ (by cases q.fppLive <;> rfl)]
    exact he.fpp j
  · intro j
    rw [hkeep _ (by cases q.dpLive <;> rfl)]
    exact he.dp j
  · intro j
    rw [hkeep _ (by cases q.fppLive <;> rfl)]
    exact he.idleShape j
  · intro c value hv
    by_cases h5 : c = 5
    · subst c; have hv' : v 0 = value := Option.some.inj hv
      simpa [← hv', signs, index, counterSlot, mirrorSource, mirrorSlot] using hc 0
    by_cases h6 : c = 6
    · subst c; have hv' : v 1 = value := Option.some.inj hv
      simpa [← hv', signs, index, counterSlot, mirrorSource, mirrorSlot] using hc 1
    by_cases h7 : c = 7
    · subst c; have hv' : v 2 = value := Option.some.inj hv
      simpa [← hv', signs, index, counterSlot, mirrorSource, mirrorSlot] using hc 2
    by_cases h8 : c = 8
    · subst c; have hv' : v 3 = value := Option.some.inj hv
      simpa [← hv', signs, index, counterSlot, mirrorSource, mirrorSlot] using hc 3
    have hv' : counterOf x c = some value := by
      simpa only [put, counterOf_replace, if_neg h5, if_neg h6, if_neg h7, if_neg h8] using hv
    obtain ⟨seg, ha, ht⟩ := he.counters c value hv'
    exact ⟨seg, by simpa [signs, h5, h6, h7, h8] using ha,
      by rw [hkeep _ (by simp [resetSlot, h5, h6, h7, h8]), ht]⟩
  · intro i place hp
    obtain ⟨stack, junk, hj, ht, hs⟩ := he.places i place hp
    exact ⟨stack, junk, hj, ht, by rw [hkeep _ rfl]; exact hs⟩
  · intro m value hv
    by_cases h3 : m = 3
    · subst m; have hv' : v 0 = value := Option.some.inj hv
      simpa [← hv', signs, index, counterSlot, mirrorSource, mirrorSlot] using hm 0
    by_cases h4 : m = 4
    · subst m; have hv' : v 1 = value := Option.some.inj hv
      simpa [← hv', signs, index, counterSlot, mirrorSource, mirrorSlot] using hm 1
    have hv' : counterOf x (mirrorSource m) = some value := by
      fin_cases m <;> first | exact (h3 rfl).elim | exact (h4 rfl).elim | exact hv
    obtain ⟨seg, ha, ht⟩ := he.mirrors m value hv'
    refine ⟨seg, ?_, ?_⟩
    · fin_cases m <;> first | exact (h3 rfl).elim | exact (h4 rfl).elim | exact ha
    · rw [hkeep _ (by simp [resetSlot, h3, h4]), ht]
  · intro t ht; rw [hkeep _ rfl]; exact he.period t ht
  · intro t ht; rw [hkeep _ rfl]; exact he.answer t ht

/-- The old boundary cache, every unused counter shape, and the twelve-slot
macro boundary survive an update of the six dormant carriers. -/
theorem core_put (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (U : Slot → STape Γm) (v : Fin 4 → Counter) (bits : Fin 4 → Bool)
    (he : CoreInv w x p)
    (hkeep : ∀ slot, resetSlot slot = false → U slot = p.2 (slotIndex slot))
    (hc : ∀ i, ∃ seg : STape Seg, absCtr seg (bits i) = v i ∧
      U (counterSlot (index i)) = padLeft margin (mapTape encSeg seg))
    (hm : ∀ i : Fin 2, ∃ seg : STape Seg, absCtr seg (bits i.castSucc.castSucc) = v i.castSucc.castSucc ∧
      U (mirrorSlot ⟨3 + i.val, by omega⟩) = padLeft margin (mapTape encSeg seg)) :
    CoreInv w (put x v) (withSigns p.1 bits, fun j => U (slotIndex.symm j)) := by
  refine ⟨⟨⟨⟨PalPeg.PhysicalFreeCounter.encControl_polarity
    (control_replace w x p.1 he.1.1.1.1 _ _ _ _) _, ?_⟩, he.1.1.2⟩, ?_⟩, ?_⟩
  · simpa only [Equiv.symm_apply_apply, withSigns] using tapes_put x p.1 _ U v bits he.1.1.1.2 hkeep hc hm
  · intro c
    simp only [Equiv.symm_apply_apply]
    by_cases h5 : c = 5
    · subst c; obtain ⟨seg, _, ht⟩ := hc 0; exact ⟨seg, ht⟩
    by_cases h6 : c = 6
    · subst c; obtain ⟨seg, _, ht⟩ := hc 1; exact ⟨seg, ht⟩
    by_cases h7 : c = 7
    · subst c; obtain ⟨seg, _, ht⟩ := hc 2; exact ⟨seg, ht⟩
    by_cases h8 : c = 8
    · subst c; obtain ⟨seg, _, ht⟩ := hc 3; exact ⟨seg, ht⟩
    rw [hkeep _ (by simp [resetSlot, counterSlot, h5, h6, h7, h8])]
    exact he.1.2 c
  · simpa only [PalPeg.PhysicalCacheInvariant.Cache, put, replace,
      PalPeg.PhysicalCacheInvariant.mirrorMagnitude, withSigns, signs,
      show (10 : Fin 16) ≠ 5 by decide, show (10 : Fin 16) ≠ 6 by decide,
      show (10 : Fin 16) ≠ 7 by decide, show (10 : Fin 16) ≠ 8 by decide,
      if_false, PalPeg.PhysicalSpare.spareIndex, PalPeg.PhysicalPeriodMirror.mirrorIndex,
      Equiv.symm_apply_apply, hkeep (counterSlot 10) rfl, hkeep (mirrorSlot 5) rfl] using he.2

/-- Each counter may advance zero to three units. Mirrors use the source
counter's decisions even when their sealed old segments differ. -/
noncomputable def compiled {K : ℕ} (counts : Fin 4 → Fin 4) (q : CoreControl)
    (ws : Fin tapeCountM → Window Γm K) (i : Fin 4) :=
  increments (counts i).val (q.polarity (index i)) (ws (slotIndex (counterSlot (index i))))

/-- Select the original six carriers without introducing any new tapes. -/
def carrier : Slot → Option (Fin 4)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl c)))))) =>
    if c = 5 then some 0 else if c = 6 then some 1
    else if c = 7 then some 2 else if c = 8 then some 3 else none
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl m))))))) =>
    if m = 3 then some 0 else if m = 4 then some 1 else none
  | _ => none

@[simp] theorem carrier_index (i : Fin 4) : carrier (counterSlot (index i)) = some i := by
  fin_cases i <;> rfl

@[simp] theorem carrier_mirror (i : Fin 2) :
    carrier (mirrorSlot ⟨3 + i.val, by omega⟩) = some i.castSucc.castSucc := by
  fin_cases i <;> rfl

theorem carrier_none {slot : Slot} (h : resetSlot slot = false) : carrier slot = none := by
  unfold resetSlot at h
  split at h <;> simp_all [carrier]


noncomputable def boundedRule {K : ℕ} (hK : 3 ≤ K) (counts : Fin 4 → Fin 4) :
    ActRule (Fin 2) CoreControl Γm tapeCountM K where
  nq := fun q _ ws => withSigns q (fun i => (compiled counts q ws i).1)
  acts := fun q _ ws j => match carrier (slotIndex.symm j) with
    | some i => (compiled counts q ws i).2
    | none => []
  len_le := by
    intro q input ws j
    split
    · rw [compiled, increments_length]; exact Nat.le_trans (Nat.le_of_lt_succ (counts _).isLt) hK
    · simp

noncomputable def rule (counts : Fin 4 → Fin 4) :
    ActRule (Fin 2) CoreControl Γm tapeCountM macroRadius := boundedRule (by decide) counts

noncomputable def step (counts : Fin 4 → Fin 4) : PalPeg.PhysicalBootFeed.CoreStep := compStep (rule counts)

/-- Exact result of the bounded action lists on a source with the full existing
encoding. The witnesses for every updated tape come from increments_encode. -/
theorem ideal_increment_bounded {K : ℕ} (hK : 3 ≤ K) (hpad : K ≤ margin) (counts : Fin 4 → Fin 4) (w : List (Fin 2))
    (x : State GalilVM) (p : CoreState) (he : CoreInv w x p) (input : Option (Fin 2)) :
    CoreInv w (put x (fun i => advanceCounter (counts i).val (values x i)))
      (idealStep (boundedRule hK counts) blankM p input) := by
  let ws := fun j => readWin blankM K (p.2 j)
  let U := fun slot => actList blankM (p.2 (slotIndex slot))
    ((boundedRule hK counts).acts p.1 input ws (slotIndex slot))
  have hc : ∀ i, ∃ seg : STape Seg, absCtr seg (p.1.polarity (index i)) = values x i ∧
      p.2 (slotIndex (counterSlot (index i))) = padLeft margin (mapTape encSeg seg) :=
    fun i => he.1.1.1.2.counters (index i) (values x i) (counter_index x i)
  have hw (i : Fin 4) (seg : STape Seg)
      (ht : p.2 (slotIndex (counterSlot (index i))) = padLeft margin (mapTape encSeg seg)) :
      compiled counts p.1 ws i = increments (counts i).val (p.1.polarity (index i))
        (readWin blankM K (padLeft margin (mapTape encSeg seg))) := by
    unfold compiled; dsimp only [ws]; rw [ht]
  have hcore := core_put w x p U (fun i => advanceCounter (counts i).val (values x i))
    (fun i => (compiled counts p.1 ws i).1) he
  have hout : CoreInv w (put x (fun i => advanceCounter (counts i).val (values x i)))
      (withSigns p.1 (fun i => (compiled counts p.1 ws i).1), fun j => U (slotIndex.symm j)) := by
    apply hcore
    · intro slot hk
      simp only [U, boundedRule, Equiv.symm_apply_apply, carrier_none hk, actList]
    · intro i
      obtain ⟨seg, ha, ht⟩ := hc i
      obtain ⟨result, hv, hacts⟩ := increments_encode (K := K) (margin := margin) (counts i).val
        (by have := (counts i).isLt; omega)
        hpad (p.1.polarity (index i)) seg seg (values x i) ha ha
      exact ⟨result, by rw [hw i seg ht]; exact hv,
        by dsimp only [U, boundedRule]; simp only [Equiv.symm_apply_apply, carrier_index]; rw [ht, hw i seg ht]; exact hacts⟩
    · intro i
      obtain ⟨source, ha, ht⟩ := hc i.castSucc.castSucc
      have hm : counterOf x (mirrorSource ⟨3 + i.val, by omega⟩) =
          some (values x i.castSucc.castSucc) := by fin_cases i <;> rfl
      obtain ⟨seg, hs, hseg⟩ := he.1.1.1.2.mirrors ⟨3 + i.val, by omega⟩ _ hm
      have hp : mirrorSource ⟨3 + i.val, by omega⟩ = index i.castSucc.castSucc := by fin_cases i <;> rfl
      rw [hp] at hs
      obtain ⟨result, hv, hacts⟩ := increments_encode (K := K) (margin := margin) (counts i.castSucc.castSucc).val
        (by have := (counts i.castSucc.castSucc).isLt; omega)
        hpad (p.1.polarity (index i.castSucc.castSucc)) source seg _ ha hs
      exact ⟨result, by rw [hw _ source ht]; exact hv,
        by dsimp only [U, boundedRule]; simp only [Equiv.symm_apply_apply, carrier_mirror]; rw [hseg, hw _ source ht]; exact hacts⟩
  simpa only [idealStep, boundedRule, U, ws, Equiv.apply_symm_apply] using hout

theorem ideal_increment (counts : Fin 4 → Fin 4) (w : List (Fin 2))
    (x : State GalilVM) (p : CoreState) (he : CoreInv w x p) (input : Option (Fin 2)) :
    CoreInv w (put x (fun i => advanceCounter (counts i).val (values x i)))
      (idealStep (rule counts) blankM p input) :=
  ideal_increment_bounded (by decide) (le_refl margin) counts w x p he input

/-- Small-radius increment rows preserve the swept encoding already before
compilation. This is the interface used to fuse two comparison quanta. -/
theorem running_increment_ideal {K : ℕ} (hK : 3 ≤ K) (hpad : K ≤ margin)
    (counts : Fin 4 → Fin 4) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (henc : Running w x p) (input : Option (Fin 2)) :
    Running w (put x (fun i => advanceCounter (counts i).val (values x i)))
      (idealStep (boundedRule hK counts) blankM p input) := by
  obtain ⟨T, hT, hteq⟩ := henc
  have hresult := ideal_increment_bounded hK hpad counts w x (p.1, T) hT input
  have hclosed : Running w _ (idealStep (boundedRule hK counts) blankM (p.1, T) input) :=
    ⟨_, hresult, fun _ => ⟨rfl, fun _ => rfl⟩⟩
  obtain ⟨hcontrol, htapes⟩ := idealStep_congr_teqG (boundedRule hK counts) blankM p.1 T p.2 hteq input
  exact PalPeg.MachineStep.sweepClosed_sweepClosure blankM (CoreInv w) _ _ _ hclosed hcontrol htapes

/-- Actual sweep, including signed zero crossings and independently padded
mirrors. No extra VM tick is required when this step is overlaid on a base row. -/
theorem running_increment (counts : Fin 4 → Fin 4) (w : List (Fin 2))
    (x : State GalilVM) (p : CoreState) (he : Running w x p) (input : Option (Fin 2)) :
    Running w (put x (fun i => advanceCounter (counts i).val (values x i)))
      ((step counts).apply blankM p input) := by
  obtain ⟨T, hT, ht⟩ := he
  have hm : ∀ j, macroRadius ≤ pos (p.2 j) := by
    intro j; rw [← (ht j).1]
    simpa only [margin, Equiv.apply_symm_apply] using hT.1.1.1.2.margins (slotIndex.symm j)
  obtain ⟨hq, hteq⟩ := idealStep_congr_teqG (rule counts) blankM p.1 T p.2 ht input
  obtain ⟨hc, hsweep⟩ := compStep_apply (rule counts) blankM p input hm
  refine ⟨(idealStep (rule counts) blankM (p.1, T) input).2, ?_,
    fun j => PalPeg.MachineStep.teqG_trans (hteq j) (hsweep j)⟩
  rw [show ((step counts).apply blankM p input).1 =
    (idealStep (rule counts) blankM (p.1, T) input).1 from hc.trans hq.symm]
  exact ideal_increment counts w x (p.1, T) hT input

/-- The canonical state stays fixed while its dormant storage performs the
bounded rebuild. Live search can never enter this operation. -/
theorem stored_increment (counts : Fin 4 → Fin 4) (w : List (Fin 2))
    (x : State GalilVM) (p : CoreState) (he : Stored w x p)
    (hd : Dormant x.vm) (input : Option (Fin 2)) :
    Stored w x ((step counts).apply blankM p input) := by
  obtain ⟨y, hr, hy⟩ := he
  have hdy : Dormant y.vm := by
    have hs := hr.2.1; unfold Same at hs; rw [hs]; exact hd
  refine ⟨put y (fun i => advanceCounter (counts i).val (values y i)),
    ⟨hr.1, related_trans hr.2 (related_replace y.vm _ _ _ _ hdy)⟩,
    running_increment counts w y p hy input⟩

/-- Equality of canonical values determines magnitude even when zero is
represented with opposite signs. Reset need not normalize old polarity bits. -/
theorem repolarize {a b : STape Seg} {sa sb : Bool} {value : Counter}
    (ha : absCtr a sa = value) (hb : absCtr b sb = value) : absCtr b sa = value := by
  have hh := congrArg (fun c : Counter => c.pos.length + c.neg.length) (hb.trans ha.symm)
  have hv : PalPeg.LocalCounter.val b = PalPeg.LocalCounter.val a := by
    cases sa <;> cases sb <;>
      simpa [absCtr, PalPeg.LocalCounter.negOfNat, PalPeg.GalilScaffoldCounter.ofNat] using hh
  simpa only [absCtr, hv] using ha

/-- Two disjoint triples, both on the original physical layout:
boundary/last/spare are (5,6,7) and (mirror3,mirror4,8). -/
def rotateSlot : Equiv.Perm Slot :=
  (((Equiv.swap (counterSlot 5) (counterSlot 7)).trans
      (Equiv.swap (counterSlot 5) (counterSlot 6))).trans
      (Equiv.swap (mirrorSlot 3) (counterSlot 8))).trans
      (Equiv.swap (mirrorSlot 3) (mirrorSlot 4))

@[simp] theorem rotate_counter (i : Fin 4) :
    rotateSlot (counterSlot (index i)) =
      if i = 0 then counterSlot 7 else if i = 1 then counterSlot 5
      else if i = 2 then counterSlot 6 else mirrorSlot 4 := by
  fin_cases i <;> simp [rotateSlot, Equiv.swap_apply_def, index, counterSlot, mirrorSlot]

@[simp] theorem rotate_mirror (i : Fin 2) :
    rotateSlot (mirrorSlot ⟨3 + i.val, by omega⟩) =
      if i = 0 then counterSlot 8 else mirrorSlot 3 := by
  fin_cases i <;> simp [rotateSlot, Equiv.swap_apply_def, counterSlot, mirrorSlot]

theorem rotate_other (slot : Slot) (h : resetSlot slot = false) : rotateSlot slot = slot := by
  have h5 : slot ≠ counterSlot 5 := by rintro rfl; cases h
  have h6 : slot ≠ counterSlot 6 := by rintro rfl; cases h
  have h7 : slot ≠ counterSlot 7 := by rintro rfl; cases h
  have h8 : slot ≠ counterSlot 8 := by rintro rfl; cases h
  have hm3 : slot ≠ mirrorSlot 3 := by rintro rfl; cases h
  have hm4 : slot ≠ mirrorSlot 4 := by rintro rfl; cases h
  simp [rotateSlot, Equiv.swap_apply_def, h5, h6, h7, h8, hm3, hm4]

noncomputable def rotateRoles : PalPeg.PhysicalRoles.Roles :=
  (slotIndex.symm.trans rotateSlot).trans slotIndex

def rotatedValues (x : State GalilVM) (i : Fin 4) : Counter :=
  if i = 0 then values x 2 else if i = 1 then values x 0 else values x 1

def rotatedBits (q : CoreControl) (i : Fin 4) : Bool :=
  if i = 0 then q.polarity 7 else if i = 1 then q.polarity 5 else q.polarity 6

noncomputable def rotateCore (p : CoreState) : CoreState :=
  (withSigns p.1 (rotatedBits p.1), fun j => p.2 (rotateRoles j))

/-- Rotation preserves the complete encoding. The independent second spare
becomes lower's mirror, so subsequent independent updates remain possible. -/
theorem core_rotate (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : CoreInv w x p) (hdup : x.vm.search.debt = x.vm.search.work) :
    CoreInv w (put x (rotatedValues x)) (rotateCore p) := by
  have hc (i : Fin 4) := he.1.1.1.2.counters (index i) (values x i) (counter_index x i)
  have hm3 := he.1.1.1.2.mirrors 3 x.vm.lower rfl
  have hm4 := he.1.1.1.2.mirrors 4 x.vm.search.span rfl
  have hout := core_put w x p (fun slot => p.2 (slotIndex (rotateSlot slot)))
    (rotatedValues x) (rotatedBits p.1) he
  apply hout
  · intro slot hk; rw [rotate_other slot hk]
  · intro i
    rw [rotate_counter]
    fin_cases i
    · exact hc 2
    · exact hc 0
    · exact hc 1
    · exact hm4
  · intro i
    rw [rotate_mirror]
    fin_cases i
    · obtain ⟨a, ha, _⟩ := hc 2
      obtain ⟨b, hb, ht⟩ := hc 3
      have hba : absCtr b (p.1.polarity 8) = x.vm.search.work := hb.trans hdup
      exact ⟨b, repolarize ha hba, ht⟩
    · exact hm3

/-- Real sweep tapes can be rotated with exactly the same role permutation;
TEqG is used throughout, with no literal physical copy operation. -/
theorem running_rotate (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) (hdup : x.vm.search.debt = x.vm.search.work) :
    Running w (put x (rotatedValues x)) (rotateCore p) := by
  obtain ⟨T, hT, ht⟩ := he
  exact ⟨fun j => T (rotateRoles j), core_rotate w x (p.1, T) hT hdup,
    fun j => ht (rotateRoles j)⟩

/-- A concrete pair of boundary/last/spare snapshots. The ordinary EncTapes
mirrors supply the two extra boundary and last copies. -/
def saved (x : State GalilVM) (boundary last spare : Counter) : State GalilVM :=
  put x (fun i => if i = 0 then boundary else if i = 1 then last else spare)

/-- Readiness follows from the actual reset step already proved on watch entry;
all six independent carriers contain zero, irrespective of previous signs. -/
theorem saved_ready (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w (PalPeg.PhysicalSearchRecycle.clearedState x) p) :
    Running w (saved x PalPeg.GalilScaffoldCounter.reset PalPeg.GalilScaffoldCounter.reset
      PalPeg.GalilScaffoldCounter.reset) p := he

/-- At a boundary both extra copies of last become the old boundary. The old
last becomes the spare for the next traversal; no linear-time copy occurs. -/
theorem saved_rotate (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (boundary last spare : Counter) (he : Running w (saved x boundary last spare) p) :
    Running w (saved x spare boundary last) (rotateCore p) := by
  simpa [put, saved, rotatedValues, values, replace] using
    running_rotate w (saved x boundary last spare) p he rfl

/-- Execute the VM row and the six snapshot updates with the same source
windows and one sweep. This is the same overlay construction used by entry. -/
noncomputable def overlayWith (update base : PalPeg.PhysicalBootFeed.CoreStep) :
    PalPeg.PhysicalBootFeed.CoreStep where
  next := fun q input ws =>
    let result := base.next q input ws
    let updated := update.next q input ws
    (withSigns result.1 (fun i => updated.1.polarity (index i)),
      fun j => if resetSlot (slotIndex.symm j) then updated.2 j else result.2 j)
  disp_le := by
    intro q input ws j
    dsimp only
    split
    · exact update.disp_le q input ws j
    · exact base.disp_le q input ws j

theorem overlayWith_apply (update base : PalPeg.PhysicalBootFeed.CoreStep)
    (p : CoreState) (input : Option (Fin 2)) :
    (overlayWith update base).apply blankM p input =
      (withSigns (base.apply blankM p input).1
          (fun i => (update.apply blankM p input).1.polarity (index i)),
        fun j => if resetSlot (slotIndex.symm j) then
          (update.apply blankM p input).2 j else (base.apply blankM p input).2 j) := by
  apply Prod.ext
  · rfl
  · funext j; simp only [PalPeg.Local.LocalStep.apply, overlayWith]; split_ifs <;> rfl

/-- Logical output assembly on already proved configurations. The real overlay
realizes this operation using the same source windows and sweep. -/
noncomputable def mix (base update : CoreState) : CoreState :=
  (withSigns base.1 (fun i => update.1.polarity (index i)), fun j =>
    if resetSlot (slotIndex.symm j) then update.2 j else base.2 j)

/-- Combining the proved VM row and snapshot row preserves the full encoding.
The update row supplies the six carrier certificates independently of the
base row. Both component proofs are about their real source-window sweeps. -/
theorem running_mix (w : List (Fin 2)) (x y : State GalilVM) (base update : CoreState)
    (v : Fin 4 → Counter) (hupdate : Running w (put x v) update)
    (hbase : Running w y base) : Running w (put y v) (mix base update) := by
  obtain ⟨S, hS, hs⟩ := hupdate
  obtain ⟨T, hT, ht⟩ := hbase
  let q := base.1
  let r := update.1
  let U := fun slot => if resetSlot slot then S (slotIndex slot) else T (slotIndex slot)
  let bits := fun i => r.polarity (index i)
  have hcore : CoreInv w (put y v)
      (withSigns q bits, fun j => U (slotIndex.symm j)) := by
    apply core_put w y (q, T) U _ bits hT
    · intro slot hk; simp only [U, hk, Bool.false_eq_true, if_false]
    · intro i
      have hv : counterOf (put x v) (index i) =
          some (v i) := by rw [counter_index, values_put]
      obtain ⟨seg, ha, hh⟩ := hS.1.1.1.2.counters (index i) _ hv
      refine ⟨seg, ha, ?_⟩
      have hk : resetSlot (counterSlot (index i)) = true := by fin_cases i <;> rfl
      simpa only [U, hk, if_true] using hh
    · intro i
      have hp : mirrorSource ⟨3 + i.val, by omega⟩ = index i.castSucc.castSucc := by fin_cases i <;> rfl
      have hv : counterOf (put x v)
          (mirrorSource ⟨3 + i.val, by omega⟩) =
          some (v i.castSucc.castSucc) := by
        rw [hp, counter_index, values_put]
      obtain ⟨seg, ha, hh⟩ := hS.1.1.1.2.mirrors ⟨3 + i.val, by omega⟩ _ hv
      refine ⟨seg, by simpa only [hp] using ha, ?_⟩
      have hk : resetSlot (mirrorSlot ⟨3 + i.val, by omega⟩) = true := by fin_cases i <;> rfl
      simpa only [U, hk, if_true] using hh
  unfold mix
  refine ⟨fun j => U (slotIndex.symm j), hcore, ?_⟩
  intro j
  simp only [U, Equiv.apply_symm_apply]
  split_ifs
  · exact hs j
  · exact ht j

theorem overlayWith_running (update base : PalPeg.PhysicalBootFeed.CoreStep)
    (w : List (Fin 2)) (x y : State GalilVM) (p : CoreState) (input : Option (Fin 2))
    (v : Fin 4 → Counter) (hupdate : Running w (put x v) (update.apply blankM p input))
    (hbase : Running w y (base.apply blankM p input)) :
    Running w (put y v) ((overlayWith update base).apply blankM p input) := by
  rw [overlayWith_apply]
  exact running_mix w x y _ _ v hupdate hbase

/-- Bounded increments are one instance of the common source-window overlay. -/
noncomputable def overlay (counts : Fin 4 → Fin 4) (base : PalPeg.PhysicalBootFeed.CoreStep) :
    PalPeg.PhysicalBootFeed.CoreStep := overlayWith (step counts) base

theorem overlay_running (counts : Fin 4 → Fin 4) (base : PalPeg.PhysicalBootFeed.CoreStep)
    (w : List (Fin 2)) (x y : State GalilVM) (p : CoreState) (input : Option (Fin 2))
    (he : Running w x p) (hbase : Running w y (base.apply blankM p input)) :
    Running w (put y (fun i => advanceCounter (counts i).val (values x i)))
      ((overlay counts base).apply blankM p input) :=
  overlayWith_running (step counts) base w x y p input _
    (running_increment counts w x p he input) hbase

/-- The actual phase-dependent preparation rate, on the two independent spare
carriers only. Bounds are finite before any input is read. -/
def spareCounts (phase : Fin 5) (i : Fin 4) : Fin 4 :=
  if i = 2 ∨ i = 3 then ⟨PalPeg.ChainBoundaryCache.rate phase,
    Nat.lt_succ_of_le (PalPeg.ChainBoundaryCache.rate_le phase)⟩ else 0

theorem saved_increment (phase : Fin 5) (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (boundary last spare : Counter)
    (he : Running w (saved x boundary last spare) p) (input : Option (Fin 2)) :
    Running w (saved x boundary last (advanceCounter (PalPeg.ChainBoundaryCache.rate phase) spare))
      ((step (spareCounts phase)).apply blankM p input) := by
  simpa [put, saved, values, spareCounts, replace, advanceCounter] using
    running_increment (spareCounts phase) w (saved x boundary last spare) p he input

/-- Overlay on a proved VM row establishes the next copies in the same tick,
with no extra background step. Its canonical VM state is the base row's state. -/
theorem saved_overlay (phase : Fin 5) (base : PalPeg.PhysicalBootFeed.CoreStep)
    (w : List (Fin 2)) (x y : State GalilVM) (p : CoreState) (boundary last spare : Counter)
    (he : Running w (saved x boundary last spare) p)
    (hbase : Running w y (base.apply blankM p none)) :
    Running w (saved y boundary last (advanceCounter (PalPeg.ChainBoundaryCache.rate phase) spare))
      ((overlay (spareCounts phase) base).apply blankM p none) := by
  simpa [put, saved, values, spareCounts, replace, advanceCounter] using
    overlay_running (spareCounts phase) base w (saved x boundary last spare) y p none he hbase

noncomputable def completed (event : Bool) (p : CoreState) : CoreState :=
  if event then rotateCore p else p

/-- Sign changes and the two disjoint role rotations accompany the same sweep
that runs the base row and prepares its copies. -/
noncomputable def signedOverlay (phase : Fin 5) (event : Bool)
    (base : PalPeg.PhysicalBootFeed.CoreStep) : PalPeg.PhysicalBootFeed.CoreStep where
  next := fun q input ws =>
    let result := (overlay (spareCounts phase) base).next q input ws
    (if event then withSigns result.1 (rotatedBits result.1) else result.1, result.2)
  disp_le := (overlay (spareCounts phase) base).disp_le

noncomputable def row (phase : Fin 5) (event : Bool) (base : PalPeg.PhysicalBootFeed.CoreStep) :=
  PalPeg.LocalRoleRouting.route (signedOverlay phase event base)
    (fun _ _ _ => if event then rotateRoles else Equiv.refl _)

theorem row_apply (phase : Fin 5) (event : Bool) (base : PalPeg.PhysicalBootFeed.CoreStep)
    (p : PalPeg.LocalRoleRouting.Config CoreControl Γm tapeCountM) (input : Option (Fin 2)) :
    PalPeg.LocalRoleRouting.decode ((row phase event base).apply blankM p input) =
      completed event ((overlay (spareCounts phase) base).apply blankM
        (PalPeg.LocalRoleRouting.decode p) input) := by
  rw [row, PalPeg.LocalRoleRouting.decode_route]
  cases event <;> rfl

/-- Successful consumption rebuilds both next-boundary copies and rotates them
at FIRST or LAST. The returned Inv proves the next traversal can reuse them.
The base row's VM encoding is the sole compositional premise. -/
theorem consume_updated (w : List (Fin 2)) (x y : State GalilVM) (p base update : CoreState)
    (s : PalPeg.GalilScaffoldChainConsume.State) (spare : Counter) (h age : ℕ)
    (hi : PalPeg.ChainBoundaryCache.Inv h age s spare)
    (hd : PalPeg.GalilScaffoldCounter.Canonical s.distance)
    (he : Running w (saved x s.boundary s.last spare) p)
    (hbase : Running w y base)
    (hupdate : Running w (saved x s.boundary s.last
      (advanceCounter (PalPeg.ChainBoundaryCache.rate s.phase) spare)) update)
    (a : Fin 3) (ha : PalPeg.GalilScaffoldChainConsume.symbol s.period.focus = some a) :
    let t := PalPeg.GalilScaffoldChainConsume.consume s (some a)
    let next := PalPeg.ChainBoundaryCache.nextSpare s spare
    Running w (saved y t.boundary t.last next)
      (completed (PalPeg.ChainBoundaryCache.boundaryEvent s)
        (mix base update)) ∧
      PalPeg.ChainBoundaryCache.Inv h (PalPeg.ChainBoundaryCache.nextAge s age) t next := by
  refine ⟨?_, PalPeg.ChainBoundaryCache.inv_consume hi a ha⟩
  have hs : Running w (saved y s.boundary s.last (advanceCounter (PalPeg.ChainBoundaryCache.rate s.phase) spare))
      (mix base update) := by
    exact running_mix w x y base update _ hupdate hbase
  have hevent : (PalPeg.GalilScaffoldChainPeriod.isFirst s.period.focus ||
      PalPeg.GalilScaffoldChainConsume.isLast s.period.focus) = PalPeg.ChainBoundaryCache.boundaryEvent s := rfl
  cases hb : PalPeg.ChainBoundaryCache.boundaryEvent s with
  | false =>
    simpa only [completed, hb, Bool.false_eq_true, if_false,
      PalPeg.ChainBoundaryCache.nextSpare, PalPeg.GalilScaffoldChainConsume.consume,
      ha, decide_true, if_true, hevent, hb, if_false] using hs
  | true =>
    have hc : PalPeg.GalilScaffoldCounter.Canonical spare := by
      obtain ⟨T, hT, _⟩ := he
      obtain ⟨seg, ha, _⟩ := hT.1.1.1.2.counters 7 spare rfl
      exact ha ▸ PalPeg.LocalCounter.absCtr_canonical seg _
    have hv := PalPeg.ChainBoundaryCache.spare_eq_at_boundary hi hb hc hd
    have hr := saved_rotate w y _ s.boundary s.last
      (advanceCounter (PalPeg.ChainBoundaryCache.rate s.phase) spare) hs
    simpa only [completed, hb, if_true, PalPeg.ChainBoundaryCache.nextSpare,
      PalPeg.GalilScaffoldChainConsume.consume, ha, decide_true,
      hevent, hb, if_true, hv] using hr

theorem consume_mix (w : List (Fin 2)) (x y : State GalilVM) (p base : CoreState)
    (s : PalPeg.GalilScaffoldChainConsume.State) (spare : Counter) (h age : ℕ)
    (hi : PalPeg.ChainBoundaryCache.Inv h age s spare)
    (hd : PalPeg.GalilScaffoldCounter.Canonical s.distance)
    (he : Running w (saved x s.boundary s.last spare) p)
    (hbase : Running w y base)
    (a : Fin 3) (ha : PalPeg.GalilScaffoldChainConsume.symbol s.period.focus = some a) :
    let t := PalPeg.GalilScaffoldChainConsume.consume s (some a)
    let next := PalPeg.ChainBoundaryCache.nextSpare s spare
    Running w (saved y t.boundary t.last next)
      (completed (PalPeg.ChainBoundaryCache.boundaryEvent s)
        (mix base ((step (spareCounts s.phase)).apply blankM p none))) ∧
      PalPeg.ChainBoundaryCache.Inv h (PalPeg.ChainBoundaryCache.nextAge s age) t next := by
  apply consume_updated w x y p base _ s spare h age hi hd he hbase
    (saved_increment s.phase w x p s.boundary s.last spare he none) a ha

/-- Successful consumption rebuilds both next-boundary copies and rotates them
at FIRST or LAST. The returned Inv proves the next traversal can reuse them.
The base row's VM encoding is the sole compositional premise. -/
theorem consume_running (base : PalPeg.PhysicalBootFeed.CoreStep)
    (w : List (Fin 2)) (x y : State GalilVM)
    (p : PalPeg.LocalRoleRouting.Config CoreControl Γm tapeCountM)
    (s : PalPeg.GalilScaffoldChainConsume.State) (spare : Counter) (h age : ℕ)
    (hi : PalPeg.ChainBoundaryCache.Inv h age s spare)
    (hd : PalPeg.GalilScaffoldCounter.Canonical s.distance)
    (he : Running w (saved x s.boundary s.last spare) (PalPeg.LocalRoleRouting.decode p))
    (hbase : Running w y (base.apply blankM (PalPeg.LocalRoleRouting.decode p) none))
    (a : Fin 3) (ha : PalPeg.GalilScaffoldChainConsume.symbol s.period.focus = some a) :
    let t := PalPeg.GalilScaffoldChainConsume.consume s (some a)
    let next := PalPeg.ChainBoundaryCache.nextSpare s spare
    Running w (saved y t.boundary t.last next)
      (PalPeg.LocalRoleRouting.decode
        ((row s.phase (PalPeg.ChainBoundaryCache.boundaryEvent s) base).apply blankM p none)) ∧
      PalPeg.ChainBoundaryCache.Inv h (PalPeg.ChainBoundaryCache.nextAge s age) t next := by
  rw [row_apply]
  change _ ∧ _
  rw [overlay, overlayWith_apply]
  exact consume_mix w x y (PalPeg.LocalRoleRouting.decode p)
    (base.apply blankM (PalPeg.LocalRoleRouting.decode p) none) s spare h age hi hd he hbase a ha

/-- The entry implementation supplies the exact saved representation used by
consume_running, not merely six independently asserted post-state copies. -/
theorem entry_saved (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (first last : Fin 3) (xs : List (Fin 3)) (h lag credit : Counter)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hb : x.vm.chain = .back ⟨[], .first first,
      xs.map PalPeg.GalilScaffoldChainPeriod.Token.plain ++ [.last last]⟩ h lag credit ver)
    (he : Running w x p) (hm : x.ctl.mode = .scan)
    (hs : PalPeg.FrameFunction.starvedTest x = false) (hc : 1 < x.ctl.clock)
    (hp : PalPeg.ChainStoredPeriod.Stored x.vm.chain) :
    Running w (saved (PalPeg.PhysicalCacheMachine.successor w x)
      PalPeg.GalilScaffoldCounter.reset PalPeg.GalilScaffoldCounter.reset PalPeg.GalilScaffoldCounter.reset)
      (PalPeg.PhysicalSearchRecycle.entryStep.apply blankM p none) :=
  saved_ready w _ _ (PalPeg.PhysicalSearchRecycle.running_watch_entry w x p first last xs
    h lag credit ver hb he hm hs hc hp)

@[simp] theorem put_put (x : State GalilVM) (v u : Fin 4 → Counter) :
    put (put x v) u = put x u := rfl

/-- Finite sign reversal costs no tape action. It is internal to the decrement
row and is never emitted as a separate physical or abstract tick. -/
def flipCore (p : CoreState) : CoreState :=
  (withSigns p.1 (fun i => !p.1.polarity (index i)), p.2)

theorem core_negate (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : CoreInv w x p) :
    CoreInv w (put x (fun i => PalPeg.LocalCounter.negate (values x i))) (flipCore p) := by
  have hh := core_put w x p (fun slot => p.2 (slotIndex slot))
    (fun i => PalPeg.LocalCounter.negate (values x i)) (fun i => !p.1.polarity (index i)) he
  simp only [Equiv.apply_symm_apply] at hh
  apply hh
  · intro slot hk; trivial
  · intro i
    obtain ⟨seg, ha, ht⟩ := he.1.1.1.2.counters (index i) _ (counter_index x i)
    exact ⟨seg, by rw [PalPeg.LocalCounter.neg_flip, ha], ht⟩
  · intro i
    have hp : mirrorSource ⟨3 + i.val, by omega⟩ = index i.castSucc.castSucc := by fin_cases i <;> rfl
    have hv : counterOf x (mirrorSource ⟨3 + i.val, by omega⟩) = some (values x i.castSucc.castSucc) := by
      rw [hp, counter_index]
    obtain ⟨seg, ha, ht⟩ := he.1.1.1.2.mirrors ⟨3 + i.val, by omega⟩ _ hv
    rw [hp] at ha
    exact ⟨seg, by rw [PalPeg.LocalCounter.neg_flip, ha], ht⟩

theorem running_negate (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) :
    Running w (put x (fun i => PalPeg.LocalCounter.negate (values x i))) (flipCore p) := by
  obtain ⟨T, hT, ht⟩ := he
  exact ⟨T, core_negate w x (p.1, T) hT, ht⟩

theorem negate_inc_negate (c : Counter) :
    PalPeg.LocalCounter.negate (PalPeg.GalilScaffoldCounter.inc (PalPeg.LocalCounter.negate c)) =
      PalPeg.GalilScaffoldCounter.dec c := by
  rcases c with ⟨ps, ns⟩
  cases ps <;> rfl

/-- One physical action on each carrier implements decrement by reusing the
already verified increment compiler with reversed signs. -/
noncomputable def decrement : PalPeg.PhysicalBootFeed.CoreStep where
  next := fun q input ws =>
    let result := (step (fun _ => 1)).next (withSigns q (fun i => !q.polarity (index i))) input ws
    (withSigns result.1 (fun i => !result.1.polarity (index i)), result.2)
  disp_le := fun q input ws j => (step (fun _ => 1)).disp_le
    (withSigns q (fun i => !q.polarity (index i))) input ws j

theorem decrement_apply (p : CoreState) (input : Option (Fin 2)) :
    decrement.apply blankM p input = flipCore ((step (fun _ => 1)).apply blankM (flipCore p) input) := rfl

theorem running_decrement (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) (input : Option (Fin 2)) :
    Running w (put x (fun i => PalPeg.GalilScaffoldCounter.dec (values x i)))
      (decrement.apply blankM p input) := by
  have hneg := running_negate w x p he
  have hinc := running_increment (fun _ => 1) w _ _ hneg input
  have hout := running_negate w _ _ hinc
  rw [decrement_apply]
  simpa only [values_put, advanceCounter, negate_inc_negate, put_put] using hout

/-- Uniform centre shift decrements both extra boundary/last/spare triples in
the same sweep as the base row. Negative values and zero crossings are included. -/
theorem shift_running (base : PalPeg.PhysicalBootFeed.CoreStep)
    (w : List (Fin 2)) (x y : State GalilVM) (p : CoreState)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (spare : Counter) (h age : ℕ)
    (hi : PalPeg.ChainBoundaryCache.Inv h age wm.machine.control spare)
    (he : Running w (saved x wm.machine.control.boundary wm.machine.control.last spare) p)
    (hbase : Running w y (base.apply blankM p none)) :
    let t := (chainShiftOne wm).machine.control
    Running w (saved y t.boundary t.last (PalPeg.GalilScaffoldCounter.dec spare))
      ((overlayWith decrement base).apply blankM p none) ∧
      PalPeg.ChainBoundaryCache.Inv h age t (PalPeg.GalilScaffoldCounter.dec spare) := by
  refine ⟨?_, PalPeg.ChainBoundaryCache.inv_shift hi⟩
  have hout := overlayWith_running decrement base w _ y p none _
    (running_decrement w (saved x wm.machine.control.boundary wm.machine.control.last spare) p he none) hbase
  simpa [saved, put, values, replace, chainShiftOne] using hout

/-- The three restart copies are on distinct original tapes. Counter 15 remains
available for the third copy; the two shown here can become lower and its mirror. -/
theorem saved_last_copies (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (boundary last spare : Counter) (he : Running w (saved x boundary last spare) p) :
    PalPeg.PhysicalSpare.Rep (p.1.polarity 6) last (p.2 (slotIndex (counterSlot 6))) ∧
    PalPeg.PhysicalSpare.Rep (p.1.polarity 6) last (p.2 (slotIndex (mirrorSlot 4))) := by
  obtain ⟨T, hT, ht⟩ := he
  constructor
  · obtain ⟨seg, ha, hs⟩ := hT.1.1.1.2.counters 6 last rfl
    exact ⟨seg, ha, hs ▸ ht _⟩
  · obtain ⟨seg, ha, hs⟩ := hT.1.1.1.2.mirrors 4 last rfl
    exact ⟨seg, ha, hs ▸ ht _⟩

/-- The rebuild rate and boundary event are read from finite source control
and the existing period window. They do not depend on the input word parameter. -/
noncomputable def watchRow (base : PalPeg.PhysicalBootFeed.CoreStep) :
    PalPeg.Local.LocalStep (Fin 2) (PalPeg.LocalRoleRouting.Control CoreControl tapeCountM)
      Γm tapeCountM macroRadius where
  next := fun q input ws =>
    let event := PalPeg.PhysicalBoundaryCount.eventRead q.2 (fun j => ws (q.1 j))
    (row q.2.chainPhase event base).next q input ws
  disp_le := fun q input ws j =>
    (row q.2.chainPhase (PalPeg.PhysicalBoundaryCount.eventRead q.2 (fun k => ws (q.1 k))) base).disp_le q input ws j

set_option maxRecDepth 2048 in
theorem watchRow_apply (base : PalPeg.PhysicalBootFeed.CoreStep)
    (p : PalPeg.LocalRoleRouting.Config CoreControl Γm tapeCountM) (input : Option (Fin 2)) :
    (watchRow base).apply blankM p input =
      (row p.1.2.chainPhase
        (PalPeg.PhysicalBoundaryCount.eventRead p.1.2
          (fun j => readWin blankM macroRadius ((PalPeg.LocalRoleRouting.decode p).2 j)))
        base).apply blankM p input := by
  simp only [PalPeg.Local.LocalStep.apply, watchRow, PalPeg.LocalRoleRouting.decode]

/-- Source encoding supplies both finite decisions for the actual consuming
row, including either marker and either traversal direction. -/
theorem source_reads (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = .watch wm) (he : Running w x p) :
    p.1.chainPhase = wm.machine.control.phase ∧
    PalPeg.PhysicalBoundaryCount.eventRead p.1 (fun j => readWin blankM macroRadius (p.2 j)) =
      PalPeg.ChainBoundaryCache.boundaryEvent wm.machine.control := by
  constructor
  · obtain ⟨T, hT, _⟩ := PalPeg.PhysicalCacheInvariant.running_core he
    simpa only [chainConsumeOf, hchain] using hT.1.1.chainPhase
  · apply PalPeg.PhysicalTickDispatch.read_from_running PalPeg.PhysicalBoundaryCount.eventRead
      (fun _ => PalPeg.ChainBoundaryCache.boundaryEvent wm.machine.control) w x p
      (PalPeg.PhysicalCacheInvariant.running_core he)
    intro T hT
    have hp : periodOf x = some wm.machine.control.period := by simp [periodOf, hchain]
    have hr := centreRead_periodSlot (K := macroRadius) hT.1.2 (le_refl margin) _ hp
    have hh : decToken (centreRead (fun j => readWin blankM macroRadius (T j)) periodSlot) =
        wm.machine.control.period.focus := by
      simpa only [tapesOf, Equiv.apply_symm_apply, decToken_encToken, encPeriod] using congrArg decToken hr
    simp only [PalPeg.PhysicalBoundaryCount.eventRead, hh, PalPeg.ChainBoundaryCache.boundaryEvent]

/-- The concrete source-window-selected sweep maintains both independent
snapshot triples. The remaining assembly obligation is the VM base row, whose
proof is explicit; no target snapshot encoding or copy-readiness is assumed. -/
theorem watch_consume (base : PalPeg.PhysicalBootFeed.CoreStep)
    (w : List (Fin 2)) (x y : State GalilVM)
    (p : PalPeg.LocalRoleRouting.Config CoreControl Γm tapeCountM)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (spare : Counter) (h age : ℕ)
    (hi : PalPeg.ChainBoundaryCache.Inv h age wm.machine.control spare)
    (he : Running w (saved x wm.machine.control.boundary wm.machine.control.last spare)
      (PalPeg.LocalRoleRouting.decode p))
    (hbase : Running w y (base.apply blankM (PalPeg.LocalRoleRouting.decode p) none))
    (a : Fin 3) (ha : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a) :
    let t := PalPeg.GalilScaffoldChainConsume.consume wm.machine.control (some a)
    let next := PalPeg.ChainBoundaryCache.nextSpare wm.machine.control spare
    Running w (saved y t.boundary t.last next)
      (PalPeg.LocalRoleRouting.decode ((watchRow base).apply blankM p none)) ∧
      PalPeg.ChainBoundaryCache.Inv h (PalPeg.ChainBoundaryCache.nextAge wm.machine.control age) t next := by
  have hsaved : (saved x wm.machine.control.boundary wm.machine.control.last spare).vm.chain = .watch wm := hchain
  obtain ⟨hp, hb⟩ := source_reads w _ _ wm hsaved he
  have hd : PalPeg.GalilScaffoldCounter.Canonical wm.machine.control.distance := by
    obtain ⟨T, hT, _⟩ := he
    obtain ⟨seg, hs, _⟩ := hT.1.1.1.2.counters 13 wm.machine.control.distance
      (by simp [counterOf, hsaved])
    exact hs ▸ PalPeg.LocalCounter.absCtr_canonical seg _
  change PalPeg.PhysicalBoundaryCount.eventRead p.1.2
    (fun j => readWin blankM macroRadius ((PalPeg.LocalRoleRouting.decode p).2 j)) = _ at hb
  rw [watchRow_apply, show p.1.2.chainPhase = wm.machine.control.phase from hp, hb]
  exact consume_running base w x y p wm.machine.control spare h age hi hd he hbase a ha

/-- A saved representation still denotes the canonical VM whenever its search
storage is dormant. No canonical search values have been silently changed. -/
theorem stored_saved (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (boundary last spare : Counter) (hd : Dormant x.vm)
    (he : Running w (saved x boundary last spare) p) : Stored w x p :=
  ⟨saved x boundary last spare, ⟨rfl, related_replace x.vm _ _ _ _ hd⟩, he⟩

/-- info: 'PalPeg.PhysicalSearchSnapshots.entry_saved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entry_saved

/-- info: 'PalPeg.PhysicalSearchSnapshots.watch_consume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms watch_consume

/-- info: 'PalPeg.PhysicalSearchSnapshots.shift_running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shift_running

/-- info: 'PalPeg.PhysicalSearchSnapshots.saved_last_copies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms saved_last_copies

end PalPeg.PhysicalSearchSnapshots
