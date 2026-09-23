import PalPeg.PhysicalEncoding
import PalPeg.ProgramBlankEq

/-! # A finite eraser for program tapes with a dense nonblank prefix

The old left-only action preserves shape but does not clear arbitrary right
contents. This eraser seeks the floor, clears the dense prefix to its first
blank, then returns to the floor. Its control contains no lengths. The source
density and the available time must still be supplied by the program trace.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalProgramErase
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.PhysicalEncoding
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply

inductive Phase | rewind | clear | home | done
  deriving DecidableEq, Fintype

abbrev Raw := Phase × STape (Fin 9)

def nextRaw (p : Raw) : Raw :=
  match p.1 with
  | .rewind => if p.2.left = [] then (.clear, p.2)
      else (.rewind, p.2.applyAction 6 (p.2.focus, .left))
  | .clear => if p.2.focus = 6 then (.home, p.2)
      else (.clear, p.2.applyAction 6 (6, .right))
  | .home => if p.2.left = [] then (.done, p.2)
      else (.home, p.2.applyAction 6 (6, .left))
  | .done => p

def run : ℕ → Raw → Raw
  | 0, p => p
  | n+1, p => run n (nextRaw p)

theorem run_add (n m : ℕ) (p : Raw) : run (n+m) p = run m (run n p) := by
  induction n generalizing p with
  | zero => simp [run]
  | succ n ih => simpa only [Nat.succ_add, run] using ih (nextRaw p)

theorem done_run (n : ℕ) (t : STape (Fin 9)) : run n (.done, t) = (.done, t) := by
  induction n <;> simp_all [run, nextRaw]

def rootWord (t : STape (Fin 9)) : List (Fin 9) := t.left.reverse ++ t.focus :: t.right

def fromWord (w : List (Fin 9)) : STape (Fin 9) := ⟨[], w.headD 6, w.tail⟩

theorem rewind_to_root (l : List (Fin 9)) (f : Fin 9) (r : List (Fin 9)) :
    run l.length (.rewind, ⟨l, f, r⟩) = (.rewind, fromWord (l.reverse ++ f :: r)) := by
  induction l generalizing f r with
  | nil => rfl
  | cons a l ih =>
    change run l.length (.rewind, ⟨l, a, f :: r⟩) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

def segment (l body : List (Fin 9)) (n : ℕ) : STape (Fin 9) :=
  ⟨l, (body ++ List.replicate n 6).headD 6, (body ++ List.replicate n 6).tail⟩

theorem segment_empty (l : List (Fin 9)) (n : ℕ) :
    segment l [] n = ⟨l, 6, List.replicate (n-1) 6⟩ := by
  cases n <;> simp [segment, List.replicate_succ]

theorem clear_prefix (l body : List (Fin 9)) (n : ℕ) (hd : (6 : Fin 9) ∉ body) :
    run body.length (.clear, segment l body n) =
      (.clear, ⟨List.replicate body.length 6 ++ l, 6, List.replicate (n-1) 6⟩) := by
  induction body generalizing l with
  | nil => simp [run, segment_empty]
  | cons a body ih =>
    have ha : a ≠ 6 := by intro ha; apply hd; simp [ha]
    have hb : (6 : Fin 9) ∉ body := fun h => hd (by simp [h])
    have hs : nextRaw (.clear, segment l (a :: body) n) = (.clear, segment (6 :: l) body n) := by
      cases body <;> cases n <;> simp [nextRaw, segment, ha, STape.applyAction, List.replicate_succ]
    rw [List.length_cons, run, hs, ih _ hb]
    simp [List.replicate_succ', List.append_assoc]

theorem home_blank (l r : ℕ) :
    run l (.home, ⟨List.replicate l 6, 6, List.replicate r 6⟩) =
      (.home, ⟨[], 6, List.replicate (l+r) 6⟩) := by
  induction l generalizing r with
  | zero => simp [run]
  | succ l ih =>
    have hs : nextRaw (.home, ⟨List.replicate (l+1) 6, 6, List.replicate r 6⟩) =
        (.home, ⟨List.replicate l 6, 6, List.replicate (r+1) 6⟩) := by
      simp [nextRaw, List.replicate_succ, STape.applyAction]
    rw [run, hs, ih]
    congr 3; omega

theorem clear_finish (body : List (Fin 9)) (n : ℕ) (hd : (6 : Fin 9) ∉ body) :
    run (2*body.length+2) (.clear, segment [] body n) =
      (.done, ⟨[], 6, List.replicate (body.length+(n-1)) 6⟩) := by
  rw [show 2*body.length+2 = body.length + (1 + (body.length+1)) by omega, run_add,
    clear_prefix [] body n hd]
  simp only [List.append_nil]
  rw [Nat.one_add]
  change run (body.length+1) (.home, ⟨List.replicate body.length 6, 6, List.replicate (n-1) 6⟩) = _
  rw [run_add body.length 1, home_blank]
  rfl

def Dense (t : STape (Fin 9)) : Prop :=
  ∃ body n, (6 : Fin 9) ∉ body ∧ rootWord t = body ++ List.replicate n 6

/-- The stopping test is justified by the source's dense-prefix property.
An arbitrary dirty tape is deliberately not accepted by this theorem. -/
theorem completes (t : STape (Fin 9)) (hd : Dense t) :
    ∃ steps r, steps ≤ 3*(t.left.length+t.right.length)+5 ∧
      run steps (.rewind, t) = (.done, ⟨[], 6, List.replicate r 6⟩) := by
  obtain ⟨body, n, hd, hw⟩ := hd
  refine ⟨t.left.length + 1 + (2*body.length+2), body.length+(n-1), ?_, ?_⟩
  · have hlen := congrArg List.length hw
    simp only [rootWord, List.length_append, List.length_reverse, List.length_cons, List.length_replicate] at hlen
    omega
  · rcases t with ⟨l, f, r⟩
    rw [show l.length + 1 + (2*body.length+2) = l.length + (1+(2*body.length+2)) by omega,
      run_add, rewind_to_root]
    change l.reverse ++ f :: r = _ at hw
    rw [hw]
    rw [Nat.one_add]
    change run (2*body.length+2) (.clear, segment [] body n) = _
    exact clear_finish body n hd

/-- Blank right padding is represented by the existing observational relation. -/
theorem reusable (t : STape (Fin 9)) (hd : Dense t) (n : ℕ)
    (hn : 3*(t.left.length+t.right.length)+5 ≤ n) :
    (run n (.rewind, t)).1 = .done ∧
      STape.BlankEq 6 (run n (.rewind, t)).2 (STape.blankTape 6) := by
  obtain ⟨k, r, hk, he⟩ := completes t hd
  rw [show n = k+(n-k) by omega, run_add, he, done_run]
  exact ⟨rfl, (STape.BlankEq.padRight 6 (STape.blankTape 6) r).symm⟩

noncomputable def phaseNext (phase : Phase) (below focus : Γm) : Phase :=
  match phase with
  | .rewind => if below = bottomM then .clear else .rewind
  | .clear => if focus = blankM then .home else .clear
  | .home => if below = bottomM then .done else .home
  | .done => .done

noncomputable def actions (phase : Phase) (below focus : Γm) : List (Act Γm) :=
  match phase with
  | .rewind => if below = bottomM then [] else [some (focus, .left)]
  | .clear => if focus = blankM then [] else [some (blankM, .right)]
  | .home => if below = bottomM then [] else [some (blankM, .left)]
  | .done => []

theorem actions_length (phase : Phase) (below focus : Γm) : (actions phase below focus).length ≤ 1 := by
  cases phase <;> simp only [actions] <;> (try split_ifs) <;> simp

theorem prog_blank (a : Fin 9) : encProg a = blankM ↔ a = 6 := by
  fin_cases a <;> decide

theorem padded_left (n : ℕ) (t : STape (Fin 9)) (a : Fin 9) (hl : t.left ≠ []) :
    padLeft n (mapTape encProg (t.applyAction 6 (a, .left))) =
      (padLeft n (mapTape encProg t)).applyAction blankM (encProg a, .left) := by
  rw [mapTape_applyAction encProg (by rfl), padLeft_applyAction_left]
  simpa [mapTape] using hl

theorem padded_right (n : ℕ) (t : STape (Fin 9)) (a : Fin 9) :
    padLeft n (mapTape encProg (t.applyAction 6 (a, .right))) =
      (padLeft n (mapTape encProg t)).applyAction blankM (encProg a, .right) := by
  rw [mapTape_applyAction encProg (by rfl), padLeft_applyAction_right]

theorem scalar_step (n : ℕ) (phase : Phase) (t : STape (Fin 9)) :
    let w := readWin blankM 1 (padLeft n (mapTape encProg t))
    phaseNext phase (w 0) (w 1) = (nextRaw (phase,t)).1 ∧
      actList blankM (padLeft n (mapTape encProg t)) (actions phase (w 0) (w 1)) =
        padLeft n (mapTape encProg (nextRaw (phase,t)).2) := by
  have hb : readWin blankM 1 (padLeft n (mapTape encProg t)) 0 = (t.left.map encProg).headD bottomM :=
    window_below n 1 _ (by decide) (by omega)
  have hf : readWin blankM 1 (padLeft n (mapTape encProg t)) 1 = encProg t.focus := by
    apply window_centre
    rw [pos_padLeft]
    omega
  have hfloor : (t.left.map encProg).headD bottomM = bottomM ↔ t.left = [] := by
    cases h : t.left with
    | nil => simp
    | cons a l => simp [encProg_ne_bottom]
  dsimp only
  rw [hb, hf]
  cases phase
  · by_cases hl : t.left = []
    · simp [nextRaw, phaseNext, actions, hl]
    · simp only [phaseNext, actions, hfloor, nextRaw, hl, if_false]
      exact ⟨trivial, (padded_left n t t.focus hl).symm⟩
  · by_cases hz : t.focus = 6
    · simp [nextRaw, phaseNext, actions, hz, encProg]
    · simp only [phaseNext, actions, prog_blank, nextRaw, hz, if_false]
      exact ⟨trivial, (padded_right n t 6).symm⟩
  · by_cases hl : t.left = []
    · simp [nextRaw, phaseNext, actions, hl]
    · simp only [phaseNext, actions, hfloor, nextRaw, hl, if_false]
      exact ⟨trivial, (padded_left n t 6 hl).symm⟩
  · exact ⟨rfl, rfl⟩

/-- Identify one of the already allocated DP banks; no new tapes are used. -/
def dpCarrier (bank : Bool) : Slot → Option (Fin 12)
  | .inr (.inr (.inl i)) => if bank then none else some i
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i)))))))) => if bank then some i else none
  | _ => none

theorem carrier_at (bank : Bool) (i : Fin 12) : dpCarrier bank (dpSlotOf bank i) = some i := by
  cases bank <;> rfl

theorem carrier_some (bank : Bool) (slot : Slot) (i : Fin 12) :
    dpCarrier bank slot = some i ↔ slot = dpSlotOf bank i := by
  rcases slot with head | prog | dp | answer | period | place | counter | mirror | retired | retiredDP
  all_goals cases bank <;> simp [dpCarrier, dpSlotOf]

variable {fb db : ℕ}
abbrev Control (fb db : ℕ) := QPhys fb db × (Fin 12 → Phase)

noncomputable def bankRule : ActRule (Fin 2) (Control fb db) Γm tapeCountM 1 where
  nq := fun q _ ws => (q.1, fun i =>
    phaseNext (q.2 i) (ws (slotIndex (dpSlotOf (!q.1.dpLive) i)) 0)
      (ws (slotIndex (dpSlotOf (!q.1.dpLive) i)) 1))
  acts := fun q _ ws j => match dpCarrier (!q.1.dpLive) (slotIndex.symm j) with
    | none => []
    | some i => actions (q.2 i) (ws j 0) (ws j 1)
  len_le := by
    intro q input ws j
    split
    · simp
    · exact actions_length _ _ _

def BankRep (n : ℕ) (raw : Fin 12 → Raw)
    (p : Control fb db × (Fin tapeCountM → STape Γm)) : Prop :=
  ∀ i, p.1.2 i = (raw i).1 ∧
    p.2 (slotIndex (dpSlotOf (!p.1.1.dpLive) i)) = padLeft n (mapTape encProg (raw i).2)

theorem bank_ideal (n : ℕ) (raw : Fin 12 → Raw)
    (p : Control fb db × (Fin tapeCountM → STape Γm)) (he : BankRep n raw p) :
    BankRep n (fun i => nextRaw (raw i)) (idealStep bankRule blankM p none) := by
  unfold BankRep
  intro i
  obtain ⟨hc, ht⟩ := he i
  have hs := scalar_step n (raw i).1 (raw i).2
  simp only [idealStep, bankRule, Equiv.symm_apply_apply, carrier_at, hc, ht]
  exact hs

theorem bank_kept (p : Control fb db × (Fin tapeCountM → STape Γm)) (slot : Slot)
    (hn : ∀ i : Fin 12, slot ≠ dpSlotOf (!p.1.1.dpLive) i) :
    (idealStep bankRule blankM p none).2 (slotIndex slot) = p.2 (slotIndex slot) := by
  have hh : dpCarrier (!p.1.1.dpLive) slot = none := by
    cases h : dpCarrier (!p.1.1.dpLive) slot with
    | none => rfl
    | some i => exact False.elim (hn i ((carrier_some _ _ _).mp h))
  simp [idealStep, bankRule, hh]

theorem bank_ideal_run (n steps : ℕ) (raw : Fin 12 → Raw)
    (p : Control fb db × (Fin tapeCountM → STape Γm)) (he : BankRep n raw p) :
    BankRep n (fun i => run steps (raw i)) (idealRun bankRule blankM p none steps) := by
  induction steps generalizing raw p with
  | zero => exact he
  | succ steps ih =>
    rw [idealRun_succ]
    exact ih (fun i => nextRaw (raw i)) _ (bank_ideal n raw p he)

theorem bank_completion (n steps : ℕ) (raw : Fin 12 → STape (Fin 9))
    (p : Control fb db × (Fin tapeCountM → STape Γm))
    (he : BankRep n (fun i => (.rewind, raw i)) p)
    (hd : ∀ i, Dense (raw i))
    (htime : ∀ i, 3*((raw i).left.length+(raw i).right.length)+5 ≤ steps) :
    let result := idealRun bankRule blankM p none steps
    (∀ i, result.1.2 i = .done) ∧
      ∀ i, ∃ t, STape.BlankEq 6 t (STape.blankTape 6) ∧
        result.2 (slotIndex (dpSlotOf (!result.1.1.dpLive) i)) = padLeft n (mapTape encProg t) := by
  have hr := bank_ideal_run n steps (fun i => (.rewind, raw i)) p he
  constructor
  · intro i
    exact (hr i).1.trans (reusable (raw i) (hd i) steps (htime i)).1
  · intro i
    exact ⟨_, (reusable (raw i) (hd i) steps (htime i)).2, (hr i).2⟩

/-- The physical sweep preserves every non-retired-DP tape up to TEqG. -/
theorem bank_sweep (n : ℕ) (raw : Fin 12 → Raw)
    (p : Control fb db × (Fin tapeCountM → STape Γm)) (he : BankRep n raw p)
    (hm : ∀ j, 1 ≤ pos (p.2 j)) :
    let result := (compStep bankRule).apply blankM p none
    ∃ ideal, BankRep n (fun i => nextRaw (raw i)) (result.1, ideal) ∧
      ∀ j, TEqG blankM (ideal j) (result.2 j) := by
  obtain ⟨hc, ht⟩ := compStep_apply bankRule blankM p none hm
  refine ⟨(idealStep bankRule blankM p none).2, ?_, ht⟩
  rw [hc]
  exact bank_ideal n raw p he

theorem bank_sweep_kept (p : Control fb db × (Fin tapeCountM → STape Γm))
    (hm : ∀ j, 1 ≤ pos (p.2 j)) (slot : Slot)
    (hn : ∀ i : Fin 12, slot ≠ dpSlotOf (!p.1.1.dpLive) i) :
    TEqG blankM (p.2 (slotIndex slot))
      (((compStep bankRule).apply blankM p none).2 (slotIndex slot)) := by
  have ht := (compStep_apply bankRule blankM p none hm).2 (slotIndex slot)
  change TEqG blankM ((idealStep bankRule blankM p none).2 (slotIndex slot)) _ at ht
  rw [bank_kept p slot hn] at ht
  exact ht

theorem bank_margin (n : ℕ) (raw : Fin 12 → Raw)
    (p : Control fb db × (Fin tapeCountM → STape Γm)) (he : BankRep n raw p)
    (hm : ∀ j, 1 ≤ pos (p.2 j)) :
    ∀ j, 1 ≤ pos ((idealStep bankRule blankM p none).2 j) := by
  intro j
  by_cases hj : ∃ i, j = slotIndex (dpSlotOf (!p.1.1.dpLive) i)
  · obtain ⟨i, rfl⟩ := hj
    have h := (bank_ideal n raw p he i).2
    change (idealStep bankRule blankM p none).2 (slotIndex (dpSlotOf (!p.1.1.dpLive) i)) = _ at h
    rw [h, pos_padLeft]
    omega
  · have h := bank_kept p (slotIndex.symm j) (by
      intro i hi
      apply hj
      exact ⟨i, by rw [← hi, Equiv.apply_symm_apply]⟩)
    rw [Equiv.apply_symm_apply] at h
    rw [h]
    exact hm j

/-- Retired DP cells have no abstract value in the current encoding. Clearing
them must still preserve its margin and every represented component. -/
theorem encTapes_retired_dp {n : ℕ} {x : State GalilVM} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fl dl : Bool} {T U : Slot → STape Γm}
    (he : EncTapes n x polarity gap micro fl dl T)
    (hk : ∀ slot, dpCarrier (!dl) slot = none → U slot = T slot)
    (hm : ∀ slot, n ≤ pos (U slot)) : EncTapes n x polarity gap micro fl dl U where
  margins := hm
  heads := by
    intro v head hh
    obtain ⟨view, vt, ha, hv, hs, hc, hw⟩ := he.heads v head hh
    refine ⟨view, vt, ha, hv, ?_, hc, hw⟩
    intro i
    rw [hk _ rfl]
    exact hs i
  idleHead := by
    intro hh
    obtain ⟨view, vt, hv, hs, hc, hw⟩ := he.idleHead hh
    refine ⟨view, vt, hv, ?_, hc, hw⟩
    intro i
    rw [hk _ rfl]
    exact hs i
  fpp := by
    intro i
    rw [hk _ (by cases fl <;> rfl)]
    exact he.fpp i
  dp := by
    intro i
    rw [hk _ (by cases dl <;> rfl)]
    exact he.dp i
  idleShape := by
    intro i
    rw [hk _ (by cases fl <;> rfl)]
    exact he.idleShape i
  counters := by
    intro c value hv
    rw [hk _ rfl]
    exact he.counters c value hv
  places := by
    intro i place hp
    rw [hk _ rfl]
    exact he.places i place hp
  mirrors := by
    intro m value hv
    rw [hk _ rfl]
    exact he.mirrors m value hv
  period := by
    intro t ht
    rw [hk _ rfl]
    exact he.period t ht
  answer := by
    intro t ht
    rw [hk _ rfl]
    exact he.answer t ht

theorem bank_enc (n : ℕ) (w : List (Fin 2)) (x : State GalilVM) (raw : Fin 12 → Raw)
    (p : Control fb db × (Fin tapeCountM → STape Γm)) (hb : BankRep n raw p)
    (he : Enc w n x (p.1.1, fun slot => p.2 (slotIndex slot))) :
    let result := idealStep bankRule blankM p none
    Enc w n x (result.1.1, fun slot => result.2 (slotIndex slot)) := by
  refine ⟨he.1, encTapes_retired_dp he.2 ?_ ?_⟩
  · intro slot hs
    change dpCarrier (!p.1.1.dpLive) slot = none at hs
    apply bank_kept p slot
    intro i hi
    rw [hi, carrier_at] at hs
    contradiction
  · intro slot
    by_cases hs : ∃ i, slot = dpSlotOf (!p.1.1.dpLive) i
    · obtain ⟨i, rfl⟩ := hs
      have ht := (bank_ideal n raw p hb i).2
      change (idealStep bankRule blankM p none).2 (slotIndex (dpSlotOf (!p.1.1.dpLive) i)) = _ at ht
      rw [ht, pos_padLeft]
      omega
    · rw [bank_kept p slot (by intro i hi; exact hs ⟨i,hi⟩)]
      exact he.2.margins slot

theorem bank_sweep_enc (n : ℕ) (w : List (Fin 2)) (x : State GalilVM) (raw : Fin 12 → Raw)
    (p : Control fb db × (Fin tapeCountM → STape Γm)) (hb : BankRep n raw p)
    (he : Enc w n x (p.1.1, fun slot => p.2 (slotIndex slot))) (hn : 1 ≤ n) :
    let result := (compStep bankRule).apply blankM p none
    ∃ ideal : Fin tapeCountM → STape Γm,
      Enc w n x (result.1.1, fun slot => ideal (slotIndex slot)) ∧
      BankRep n (fun i => nextRaw (raw i)) (result.1, ideal) ∧
      ∀ j, TEqG blankM (ideal j) (result.2 j) := by
  have hm : ∀ j, 1 ≤ pos (p.2 j) := by
    intro j
    have h := hn.trans (he.2.margins (slotIndex.symm j))
    simpa only [Equiv.apply_symm_apply] using h
  obtain ⟨hc, ht⟩ := compStep_apply bankRule blankM p none hm
  refine ⟨(idealStep bankRule blankM p none).2, ?_, ?_, ht⟩
  · rw [hc]
    exact bank_enc n w x raw p hb he
  · rw [hc]
    exact bank_ideal n raw p hb

def Stored (n : ℕ) (raw : Fin 12 → Raw)
    (p : Control fb db × (Fin tapeCountM → STape Γm)) : Prop :=
  ∃ T, BankRep n raw (p.1,T) ∧ (∀ j, 1 ≤ pos (T j)) ∧ ∀ j, TEqG blankM (T j) (p.2 j)

theorem stored_step (n : ℕ) (raw : Fin 12 → Raw)
    (p : Control fb db × (Fin tapeCountM → STape Γm)) (he : Stored n raw p) :
    Stored n (fun i => nextRaw (raw i)) ((compStep bankRule).apply blankM p none) := by
  obtain ⟨T, hT, hm, ht⟩ := he
  have hmp : ∀ j, 1 ≤ pos (p.2 j) := fun j => (ht j).1 ▸ hm j
  have hb := bank_ideal n raw (p.1,T) hT
  have hbm := bank_margin n raw (p.1,T) hT hm
  obtain ⟨hc, hteq⟩ := idealStep_congr_teqG bankRule blankM p.1 T p.2 ht none
  obtain ⟨hr, hs⟩ := compStep_apply bankRule blankM p none hmp
  refine ⟨(idealStep bankRule blankM (p.1,T) none).2, ?_, hbm, fun j =>
    PalPeg.MachineStep.teqG_trans (hteq j) (hs j)⟩
  change ((compStep bankRule).apply blankM p none).1 =
    (idealStep bankRule blankM (p.1,p.2) none).1 at hr
  rw [hr, ← hc]
  exact hb

noncomputable def sweepRun : ℕ → (Control fb db × (Fin tapeCountM → STape Γm)) →
    (Control fb db × (Fin tapeCountM → STape Γm))
  | 0, p => p
  | n+1, p => sweepRun n ((compStep bankRule).apply blankM p none)

theorem stored_run (n steps : ℕ) (raw : Fin 12 → Raw)
    (p : Control fb db × (Fin tapeCountM → STape Γm)) (he : Stored n raw p) :
    Stored n (fun i => run steps (raw i)) (sweepRun steps p) := by
  induction steps generalizing raw p with
  | zero => exact he
  | succ steps ih => exact ih _ _ (stored_step n raw p he)

/-- Actual one-cell sweeps, not a variable-length instruction in one tick.
The twelve retired tapes are cleared in parallel and the source deadline is
uniform over them. Both source premises remain explicit until trace supply. -/
theorem bank_real_completion (n steps : ℕ) (raw : Fin 12 → STape (Fin 9))
    (p : Control fb db × (Fin tapeCountM → STape Γm))
    (he : Stored n (fun i => (.rewind, raw i)) p) (hd : ∀ i, Dense (raw i))
    (htime : ∀ i, 3*((raw i).left.length+(raw i).right.length)+5 ≤ steps) :
    let result := sweepRun steps p
    (∀ i, result.1.2 i = .done) ∧ ∃ T : Fin tapeCountM → STape Γm,
      (∀ i, ∃ t, STape.BlankEq 6 t (STape.blankTape 6) ∧
        T (slotIndex (dpSlotOf (!result.1.1.dpLive) i)) = padLeft n (mapTape encProg t)) ∧
      ∀ j, TEqG blankM (T j) (result.2 j) := by
  obtain ⟨T, hT, _, ht⟩ := stored_run n steps (fun i => (.rewind,raw i)) p he
  constructor
  · intro i
    exact (hT i).1.trans (reusable (raw i) (hd i) steps (htime i)).1
  · refine ⟨T, ?_, ht⟩
    intro i
    exact ⟨_, (reusable (raw i) (hd i) steps (htime i)).2, (hT i).2⟩

theorem blankEq_teq {Γ : Type} {blank : Γ} {t u : STape Γ}
    (h : STape.BlankEq blank t u) : TEqG blank t u := by
  refine ⟨congrArg List.length h.left, ?_⟩
  intro k
  unfold rd toList
  rw [h.left, h.focus]
  by_cases hk : k < u.left.reverse.length
  · rw [List.getD_append _ _ _ _ hk, List.getD_append _ _ _ _ hk]
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    exact (h.right.cons) (k-u.left.reverse.length)

theorem padded_blankEq (n : ℕ) {t u : STape (Fin 9)} (h : STape.BlankEq 6 t u) :
    TEqG blankM (padLeft n (mapTape encProg t)) (padLeft n (mapTape encProg u)) := by
  apply blankEq_teq
  refine ⟨by simp only [padLeft, mapTape, h.left], by exact congrArg encProg h.focus, ?_⟩
  intro k
  change (t.right.map encProg).getD k blankM = (u.right.map encProg).getD k blankM
  rw [show blankM = encProg 6 from rfl, List.getD_map, List.getD_map]
  exact congrArg encProg (h.right k)

/-- Reuse needs the canonical reset only up to the existing tape relation;
the finite blank suffix left by physical clearing is harmless. -/
theorem bank_real_reset (n steps : ℕ) (raw : Fin 12 → STape (Fin 9))
    (p : Control fb db × (Fin tapeCountM → STape Γm))
    (he : Stored n (fun i => (.rewind, raw i)) p) (hd : ∀ i, Dense (raw i))
    (htime : ∀ i, 3*((raw i).left.length+(raw i).right.length)+5 ≤ steps) :
    let result := sweepRun steps p
    (∀ i, result.1.2 i = .done) ∧ ∀ i,
      TEqG blankM (padLeft n (mapTape encProg (STape.blankTape 6)))
        (result.2 (slotIndex (dpSlotOf (!result.1.1.dpLive) i))) := by
  obtain ⟨hc, T, hT, ht⟩ := bank_real_completion n steps raw p he hd htime
  refine ⟨hc, ?_⟩
  intro i
  obtain ⟨t, heq, hslot⟩ := hT i
  have hs := ht (slotIndex (dpSlotOf (!(sweepRun steps p).1.1.dpLive) i))
  rw [hslot] at hs
  exact PalPeg.MachineStep.teqG_trans (padded_blankEq n heq.symm) hs

/-- The existing floor test alone does not even erase a nonblank root. -/
theorem left_only_stuck (n : ℕ) (j : Fin tapeCountM) :
    let t := padLeft n (mapTape encProg (⟨[], 0, [1]⟩ : STape (Fin 9)))
    eraseAct (fun _ => readWin blankM 1 t) j = [] ∧ t.focus ≠ blankM := by
  dsimp only
  have hb := window_below n 1 (mapTape encProg (⟨[], 0, [1]⟩ : STape (Fin 9))) (by decide) (by omega)
  constructor
  · unfold eraseAct
    apply if_pos
    exact hb
  · change encProg 0 ≠ blankM
    decide

/-- info: 'PalPeg.PhysicalProgramErase.reusable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reusable

/-- info: 'PalPeg.PhysicalProgramErase.bank_sweep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bank_sweep

/-- info: 'PalPeg.PhysicalProgramErase.bank_sweep_enc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bank_sweep_enc

/-- info: 'PalPeg.PhysicalProgramErase.bank_real_reset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bank_real_reset

/-- info: 'PalPeg.PhysicalProgramErase.left_only_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms left_only_stuck

end PalPeg.PhysicalProgramErase
