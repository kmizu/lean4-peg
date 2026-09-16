import PalPeg.GalilScaffoldHeapProgram

set_option autoImplicit false
namespace PalPeg.GalilScaffoldMoveGuards
open GalilFppWide (Instruction)
open GalilScaffoldHeap

/-- Disjunction of the raw instruction events collected for a tape/direction
by ScaffoldCircuitProgram.instructionStep. -/
def MoveEvent {n : ℕ} (code : List (Instruction n)) (pc : ℕ) (active : Bool)
    (t : Fin n) (direction : Bool) : Prop :=
  ∃ i next, active = true ∧ pc = i ∧ code[i]? = some (.move t direction next)

theorem event_iff {n : ℕ} (code : List (Instruction n)) (pc : ℕ) (active : Bool)
    (t : Fin n) (direction : Bool) :
    MoveEvent code pc active t direction ↔
      active = true ∧ ∃ next, code[pc]? = some (.move t direction next) := by
  constructor
  · rintro ⟨i,next,ha,he,hi⟩
    subst i
    exact ⟨ha,next,hi⟩
  · rintro ⟨ha,next,hi⟩
    exact ⟨pc,next,ha,rfl,hi⟩

/-- Different tape/direction groups cannot allocate the common instruction
slot simultaneously, assuming one concrete, decoded PC. -/
theorem move_unique {n : ℕ} {code : List (Instruction n)} {pc : ℕ} {active : Bool}
    {t u : Fin n} {d e : Bool} (ht : MoveEvent code pc active t d)
    (hu : MoveEvent code pc active u e) : t = u ∧ d = e := by
  obtain ⟨_,a,ha⟩ := (event_iff _ _ _ _ _).mp ht
  obtain ⟨_,b,hb⟩ := (event_iff _ _ _ _ _).mp hu
  rw [ha] at hb
  cases hb
  exact ⟨rfl,rfl⟩

theorem selected_move {n : ℕ} {code : List (Instruction n)} {pc next : ℕ}
    {t : Fin n} {d : Bool} (hi : code[pc]? = some (.move t d next))
    (u : Fin n) (e : Bool) : MoveEvent code pc true u e ↔ u = t ∧ e = d := by
  constructor
  · intro hu
    exact move_unique hu ((event_iff _ _ _ _ _).mpr ⟨rfl,next,hi⟩)
  · rintro ⟨rfl,rfl⟩
    exact (event_iff _ _ _ _ _).mpr ⟨rfl,next,hi⟩

def guardedPut {slots : ℕ} {α : Type} (h : Heap slots α) (a : Address slots)
    (c : Cell slots α) (enabled : Bool) : Heap slots α :=
  if enabled then put h a c else h

/-- Disabled writes to a shared slot do not reserve or overwrite its contents.
Hence mutually exclusive branches can use the same physical address. -/
theorem exclusive_writes {slots : ℕ} {α : Type} (h : Heap slots α) (a : Address slots)
    (c d : Cell slots α) (e f : Bool) (hx : ¬ (e = true ∧ f = true)) :
    guardedPut (guardedPut h a c e) a d f =
      if e then put h a c else if f then put h a d else h := by
  cases e <;> cases f <;> simp_all [guardedPut]

/-- A loop whose guards are evaluated from the instruction-entry snapshot.
Only the selected key changes the state. -/
def dispatch {κ σ : Type} [DecidableEq κ] (chosen : κ) (step : κ → σ → σ) :
    List κ → σ → σ
  | [], x => x
  | k :: ks, x => dispatch chosen step ks (if k = chosen then step k x else x)

theorem dispatch_absent {κ σ : Type} [DecidableEq κ] (chosen : κ) (step : κ → σ → σ)
    (ks : List κ) (ha : chosen ∉ ks) (x : σ) : dispatch chosen step ks x = x := by
  induction ks generalizing x with
  | nil => rfl
  | cons k ks ih =>
    have hk : k ≠ chosen := by intro he; subst k; exact ha (by simp)
    have ht : chosen ∉ ks := by intro hm; exact ha (List.mem_cons_of_mem _ hm)
    simpa [dispatch,hk] using ih ht x

theorem dispatch_once {κ σ : Type} [DecidableEq κ] (chosen : κ) (step : κ → σ → σ)
    (ks : List κ) (hn : ks.Nodup) (hm : chosen ∈ ks) (x : σ) :
    dispatch chosen step ks x = step chosen x := by
  induction ks generalizing x with
  | nil => simp at hm
  | cons k ks ih =>
    obtain ⟨hk,ht⟩ := List.nodup_cons.mp hn
    by_cases he : k = chosen
    · subst k
      simpa [dispatch] using dispatch_absent chosen step ks hk (step chosen x)
    · have hm' : chosen ∈ ks := (List.mem_cons.mp hm).resolve_left (Ne.symm he)
      simpa [dispatch,he] using ih ht hm' x

/-- After move-event decoding, the complete tape/direction loop performs
exactly one shared-heap move, not one allocation per syntactic branch. -/
theorem dispatch_heap_move {n slots : ℕ} (x : GalilScaffoldHeapProgram.Config n slots)
    (a : Address slots) (chosen : Fin n × Bool) (ks : List (Fin n × Bool))
    (hn : ks.Nodup) (hm : chosen ∈ ks) :
    dispatch chosen (fun k y => GalilScaffoldHeapProgram.moved y k.1 a k.2 x.pc) ks x =
      GalilScaffoldHeapProgram.moved x chosen.1 a chosen.2 x.pc :=
  dispatch_once chosen _ ks hn hm x

noncomputable def eventLoop {n : ℕ} {σ : Type} (code : List (Instruction n)) (pc : ℕ)
    (active : Bool) (step : (Fin n × Bool) → σ → σ) (ks : List (Fin n × Bool)) (x : σ) : σ := by
  classical
  exact ks.foldl (fun y k => if MoveEvent code pc active k.1 k.2 then step k y else y) x

theorem eventLoop_selected {n : ℕ} {σ : Type} {code : List (Instruction n)} {pc next : ℕ}
    {t : Fin n} {d : Bool} (hi : code[pc]? = some (.move t d next))
    (step : (Fin n × Bool) → σ → σ) (ks : List (Fin n × Bool)) (x : σ) :
    eventLoop code pc true step ks x = dispatch (t,d) step ks x := by
  classical
  induction ks generalizing x with
  | nil => rfl
  | cons k ks ih =>
    have hg : MoveEvent code pc true k.1 k.2 ↔ k = (t,d) := by
      rw [selected_move hi]
      constructor
      · rintro ⟨h₁,h₂⟩; exact Prod.ext h₁ h₂
      · intro h; cases h; exact ⟨rfl,rfl⟩
    simpa [eventLoop,dispatch,List.foldl_cons,hg] using
      ih (if k = (t,d) then step k x else x)

theorem eventLoop_once {n : ℕ} {σ : Type} {code : List (Instruction n)} {pc next : ℕ}
    {t : Fin n} {d : Bool} (hi : code[pc]? = some (.move t d next))
    (step : (Fin n × Bool) → σ → σ) (ks : List (Fin n × Bool))
    (hn : ks.Nodup) (hm : (t,d) ∈ ks) (x : σ) :
    eventLoop code pc true step ks x = step (t,d) x := by
  rw [eventLoop_selected hi]
  exact dispatch_once _ _ _ hn hm x

/-- Exactly Scala's tape index order, left then right at each tape. -/
def keys (n : ℕ) : List (Fin n × Bool) := (List.finRange n).product [false,true]

theorem keys_nodup (n : ℕ) : (keys n).Nodup :=
  (List.nodup_finRange n).product (by simp)

theorem mem_keys {n : ℕ} (k : Fin n × Bool) : k ∈ keys n := by
  rcases k with ⟨t,d⟩
  cases d <;> simp [keys]

theorem concrete_loop_move {n : ℕ} {σ : Type} {code : List (Instruction n)} {pc next : ℕ}
    {t : Fin n} {d : Bool} (hi : code[pc]? = some (.move t d next))
    (step : (Fin n × Bool) → σ → σ) (x : σ) :
    eventLoop code pc true step (keys n) x = step (t,d) x :=
  eventLoop_once hi step _ (keys_nodup n) (mem_keys _) x

theorem eventLoop_idle {n : ℕ} {σ : Type} (code : List (Instruction n)) (pc : ℕ)
    (active : Bool) (step : (Fin n × Bool) → σ → σ) (ks : List (Fin n × Bool))
    (hh : ∀ t d, ¬ MoveEvent code pc active t d) (x : σ) :
    eventLoop code pc active step ks x = x := by
  classical
  induction ks generalizing x with
  | nil => rfl
  | cons k ks ih => simpa [eventLoop,hh] using ih x

theorem inactive_loop {n : ℕ} {σ : Type} (code : List (Instruction n)) (pc : ℕ)
    (step : (Fin n × Bool) → σ → σ) (x : σ) :
    eventLoop code pc false step (keys n) x = x := by
  apply eventLoop_idle
  intro t d
  simp [event_iff]

theorem nonmove_loop {n : ℕ} {σ : Type} {code : List (Instruction n)} {pc : ℕ}
    {i : Instruction n} (hi : code[pc]? = some i)
    (hn : ∀ t d next, i ≠ .move t d next) (active : Bool)
    (step : (Fin n × Bool) → σ → σ) (x : σ) :
    eventLoop code pc active step (keys n) x = x := by
  apply eventLoop_idle
  intro t d he
  obtain ⟨_,next,hm⟩ := (event_iff _ _ _ _ _).mp he
  rw [hi] at hm
  exact hn t d next (Option.some.inj hm)

#print axioms concrete_loop_move
#print axioms inactive_loop
#print axioms nonmove_loop
#print axioms eventLoop_once
#print axioms dispatch_heap_move
#print axioms move_unique
#print axioms selected_move
#print axioms exclusive_writes
end PalPeg.GalilScaffoldMoveGuards
