import PalPeg.ScaWorkerCoroutine

/-!
# The window worker's distance registers are head differences

`ScaWindowWorker` keeps Scala's register-transfer semantics for the distance registers
(`WindowLiveDistances`, `ScaffoldWindowLive.scala`): each ROM row carries, per register, a source
register, a sign and a delta, derived from the liveness sets of the row's successors. This file
shows that these transfers compute what the head program means.

**The ghost.** The head program moves *logical* head positions `pos : String → ℤ`
(`headStep`: `move` adds the batch delta, `copy t s` sets `pos t := pos s`, every other event
leaves `pos` alone). Many heads (`KP`, `Upper`, `Lower`, …) have no physical cursor in the
worker; they exist only through their differences. So `pos` is a ghost, carried next to the
worker state together with `markEnd`, the `end` cursor at the last `mark` / `resetFlags`.

**The invariant** (`Inv`):

* `RegInv` — for every pair `p` live before the current row (`liveAt spec s.pc`, the backward
  liveness fixpoint `liveDistances`), the register of `p`'s colour holds
  `pos p.1 - pos p.2` (`Tracks`). The pc is a row of the program, and there are
  `registers` registers.
* `KeyInv` — `length = end - begin` (the number of letters since the last `resetFlags`), and
  `h = end - markEnd` for a flag worker (arrivals since the last `mark` / `resetFlags`),
  `h = 0` for the matcher; `begin ≤ markEnd ≤ end`.

**What preserves it.** `initial_inv` (all heads at `0`), `start_inv` (the ghost restarts at
`startPos`: `Tail = length` for the matcher; `OriginalEnd = Upper = length`,
`Lower = length - h` for the flag worker, every other head `0`), `step_inv` (the ghost takes
`headStep` of the executed row when active), `service_inv`, `arrive_inv`, `mark_inv`,
`resetFlags_inv`.

**Consequence.** `compare_eq` / `decision_equal` / `decision_less`: at a row `less a b`,
`equal a b` or `assertEqual a b` the worker's `compare` is
`(pos a = pos b, pos a < pos b)`; the coroutine worker decides the same
(`coDecision_equal` / `coDecision_less`).

**Table facts.** The generic proofs use eleven facts about the ROM (`TableFacts`): targets and
start in range, every pair live after a row has a colour below `registers`, colours are
injective on each after-set, after-sets hold canonical pairs, the liveness transfer of a row is
contained in its before-set, target-less rows have nothing live, and the start mappings cover
the start's live set with distinct colours. `checkTables` is a Boolean version;
`tableFacts_of_check` turns it into `TableFacts`. For `matcherWorker` and `flagsWorker` it is
evaluated by the kernel (`matcher_checkTables`, `flags_checkTables`).
-/

set_option autoImplicit false

namespace PalPeg.ScaWorkerRegs

open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaGsCert PalPeg.ScaWindowWorker
  PalPeg.ScaWorkerCoroutine

/-! ## Head-program semantics on logical positions -/

/-- The displacement of `head` by a batch move, as the ROM reads it (`lookupLast`: Scala's
`toMap`, the last binding wins; `ScaWindowWorker.lean:233-236`). -/
def moveDelta (moves : List Movement) (head : String) : Int :=
  (lookupLast head (moves.map fun m => (m.head, m.delta))).getD 0

/-- One event of the head program on the logical positions: `move` adds the batch delta,
`copy target source` sets `target := source`, the other events move no head. -/
def headStep : Event → (String → Int) → String → Int
  | .move moves, pos => fun head => pos head + moveDelta moves head
  | .copy target source, pos => fun head => if head = target then pos source else pos head
  | _, pos => pos

/-- The head a copy row substitutes into a pair component (`distanceTransfer`, `fieldsAt`). -/
def substHead (target source head : String) : String :=
  if head = target then source else head

theorem headStep_copy (target source : String) (pos : String → Int) (head : String) :
    headStep (.copy target source) pos head = pos (substHead target source head) := by
  show (if head = target then pos source else pos head) = _
  unfold substHead
  split <;> rfl

/-! ## The invariant -/

/-- The ghost: logical head positions, and the `end` cursor at the last `mark`/`resetFlags`. -/
structure Ghost where
  pos : String → Int
  markEnd : Nat

/-- The pairs live before row `pc` (`Liveness.before`). -/
def liveAt (spec : WorkerSpec) (pc : Nat) : List Pair := (liveDistances spec).getD pc []

/-- The pairs live after `row` (`Liveness.after`, the union over the row's successors). -/
def afterAt (spec : WorkerSpec) (row : Row) : List Pair :=
  successorsUnion (liveDistances spec) row.targets

/-- The register of `p`'s colour holds `pos p.1 - pos p.2`. -/
def Tracks (spec : WorkerSpec) (pos : String → Int) (regs : List Int) (p : Pair) : Prop :=
  ∃ i, lookupFirst p spec.distances.colors = some i ∧ regs.getD i 0 = pos p.1 - pos p.2

/-- The distance registers track the pairs live at the current row. -/
structure RegInv (spec : WorkerSpec) (pos : String → Int) (s : WorkerState) : Prop where
  regsLength : s.regs.length = spec.distances.registers
  pcInRange : s.pc < spec.program.code.length
  live : ∀ p ∈ liveAt spec s.pc, Tracks spec pos s.regs p

/-- The special keys: `length` counts the letters since the last `resetFlags`, `h` the
arrivals since the last `mark`/`resetFlags` (flag workers; the matcher never raises `h`). -/
structure KeyInv (spec : WorkerSpec) (markEnd : Nat) (s : WorkerState) : Prop where
  lengthEq : s.length = (s.end : Int) - s.begin
  beginLeMark : s.begin ≤ markEnd
  markLeEnd : markEnd ≤ s.end
  hEq : s.h = if spec.isFlags then (s.end : Int) - markEnd else 0

structure Inv (spec : WorkerSpec) (g : Ghost) (s : WorkerState) : Prop where
  regs : RegInv spec g.pos s
  keys : KeyInv spec g.markEnd s

/-! ## Facts about the ROM -/

/-- The `start` mapping of `initializeValues` (`ScaWindowWorker.lean:461-473`). -/
def startMapping (spec : WorkerSpec) : List (Pair × Option (DistKey × Int)) :=
  if spec.isFlags then flagsStartMapping else matcherStartMapping

/-- `p` has a colour, and the colour is a register. -/
def ColorOk (spec : WorkerSpec) (p : Pair) : Prop :=
  ∃ i, lookupFirst p spec.distances.colors = some i ∧ i < spec.distances.registers

/-- What the invariant needs from the liveness tables and the colouring. -/
structure TableFacts (spec : WorkerSpec) : Prop where
  startInRange : spec.program.start < spec.program.code.length
  targetsInRange : ∀ (r : Nat) (row : Row), spec.program.code[r]? = some row →
    ∀ t ∈ row.targets, t < spec.program.code.length
  afterColored : ∀ (r : Nat) (row : Row), spec.program.code[r]? = some row → ∀ p ∈ afterAt spec row, ColorOk spec p
  afterColorsInjective : ∀ (r : Nat) (row : Row), spec.program.code[r]? = some row →
    ∀ p ∈ afterAt spec row, ∀ p' ∈ afterAt spec row,
      lookupFirst p spec.distances.colors = lookupFirst p' spec.distances.colors → p = p'
  afterCanonical : ∀ (r : Nat) (row : Row), spec.program.code[r]? = some row →
    ∀ p ∈ afterAt spec row, pairOf spec.names p.1 p.2 = some p
  transferLive : ∀ (r : Nat) (row : Row), spec.program.code[r]? = some row →
    ∀ p ∈ distanceTransfer spec.names row (afterAt spec row), p ∈ liveAt spec r
  targetlessDead : ∀ (r : Nat) (row : Row), spec.program.code[r]? = some row → row.targets = [] →
    liveAt spec r = []
  startLiveMapped : ∀ p ∈ liveAt spec spec.program.start, ∃ v, (p, v) ∈ startMapping spec
  startColorsNodup :
    ((startMapping spec).map fun e => lookupFirst e.1 spec.distances.colors).Nodup
  startColored : ∀ e ∈ startMapping spec, ColorOk spec e.1

/-! ## List lemmas -/

theorem mem_union {α : Type} [DecidableEq α] (x : α) (xs ys : List α) :
    x ∈ union xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  unfold union
  induction ys generalizing xs with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rw [ih]
    by_cases hy : y ∈ xs
    · rw [if_pos hy]
      simp only [List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inl (h ▸ hy)
        · exact Or.inr h
    · rw [if_neg hy]
      simp only [List.mem_append, List.mem_cons]
      tauto

theorem mem_successorsUnion {α : Type} [DecidableEq α] (before : Array (List α))
    (targets : List Nat) (x : α) :
    x ∈ successorsUnion before targets ↔ ∃ t ∈ targets, x ∈ before.getD t [] := by
  unfold successorsUnion
  suffices hacc : ∀ acc : List α,
      x ∈ targets.foldl (fun live t => union live (before.getD t [])) acc ↔
        x ∈ acc ∨ ∃ t ∈ targets, x ∈ before.getD t [] by
    simpa using hacc []
  induction targets with
  | nil => intro acc; simp
  | cons t ts ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih, mem_union]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem liveAt_subset_afterAt {spec : WorkerSpec} {row : Row} {t : Nat} (ht : t ∈ row.targets)
    {p : Pair} (hp : p ∈ liveAt spec t) : p ∈ afterAt spec row :=
  (mem_successorsUnion _ _ _).mpr ⟨t, ht, hp⟩

/-- A fold that overwrites with `set p` at every `p` satisfying `P`, when no `p` does. -/
theorem foldl_ite_none {α β : Type} (P : α → Prop) [DecidablePred P] (set : α → β → β)
    (L : List α) (u : β) (hnone : ∀ p ∈ L, ¬ P p) :
    L.foldl (fun u p => if P p then set p u else u) u = u := by
  induction L generalizing u with
  | nil => rfl
  | cons p L ih =>
    simp only [List.foldl_cons]
    rw [if_neg (hnone p (List.mem_cons_self ..))]
    exact ih u fun p' hp' => hnone p' (List.mem_cons_of_mem _ hp')

/-- The same fold when exactly one element `q` satisfies `P` and a later `set` overwrites an
earlier one. -/
theorem foldl_ite_unique {α β : Type} (P : α → Prop) [DecidablePred P] (set : α → β → β)
    (hoverwrite : ∀ a a' u, set a (set a' u) = set a u) (L : List α) (q : α) (hqL : q ∈ L)
    (hPq : P q) (hunique : ∀ p ∈ L, P p → p = q) (u : β) :
    L.foldl (fun u p => if P p then set p u else u) u = set q u := by
  induction L generalizing u with
  | nil => simp at hqL
  | cons p L ih =>
    simp only [List.foldl_cons]
    have huniqueTail : ∀ p' ∈ L, P p' → p' = q :=
      fun p' hp' => hunique p' (List.mem_cons_of_mem _ hp')
    by_cases hPp : P p
    · rw [if_pos hPp]
      have hpq : p = q := hunique p (List.mem_cons_self ..) hPp
      subst hpq
      by_cases hqTail : p ∈ L
      · rw [ih hqTail huniqueTail, hoverwrite]
      · exact foldl_ite_none P set L _ fun p' hp' hPp' => hqTail (huniqueTail p' hp' hPp' ▸ hp')
    · rw [if_neg hPp]
      have hqTail : q ∈ L := by
        rcases List.mem_cons.mp hqL with hqp | hqTail
        · exact absurd (hqp ▸ hPq) hPp
        · exact hqTail
      exact ih hqTail huniqueTail u

/-! ## The liveness transfer -/

/-- Membership in a fold whose step keeps the accumulator and adds `g p` when it is defined. -/
theorem mem_foldl_of_step {α β : Type} (step : List β → α → List β) (g : α → Option β)
    (hkeep : ∀ acc p y, y ∈ acc → y ∈ step acc p)
    (hadd : ∀ acc p y, g p = some y → y ∈ step acc p)
    (L : List α) (acc : List β) {p : α} (hp : p ∈ L) {y : β} (hg : g p = some y) :
    y ∈ L.foldl step acc := by
  induction L generalizing acc with
  | nil => simp at hp
  | cons p' L ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hpTail
    · have hkeepAll : ∀ (L : List α) (acc : List β), y ∈ acc → y ∈ L.foldl step acc := by
        intro L
        induction L with
        | nil => intro acc hy; exact hy
        | cons a L ihL => intro acc hy; exact ihL _ (hkeep acc a y hy)
      exact hkeepAll L _ (hadd acc p y hg)
    · exact ih _ hpTail

/-- A copy row keeps the substituted image of every live pair. -/
theorem mem_transfer_copy {names : List String} {target source : String} {targets : List Nat}
    {succ : List Pair} {q q' : Pair} (hq : q ∈ succ)
    (hpair : pairOf names (substHead target source q.1) (substHead target source q.2) = some q') :
    q' ∈ distanceTransfer names ⟨.copy target source, targets⟩ succ := by
  show q' ∈ succ.foldl (fun acc p =>
    match pairOf names (if p.1 = target then source else p.1)
                        (if p.2 = target then source else p.2) with
    | some q => union acc [q]
    | none => acc) []
  refine mem_foldl_of_step _ (fun p : Pair => pairOf names (substHead target source p.1)
    (substHead target source p.2)) ?_ ?_ succ [] hq hpair
  · intro acc p y hy
    show y ∈ (match pairOf names (substHead target source p.1) (substHead target source p.2) with
      | some q => union acc [q]
      | none => acc)
    split
    · exact (mem_union _ _ _).mpr (Or.inl hy)
    · exact hy
  · intro acc p y hg
    show y ∈ (match pairOf names (substHead target source p.1) (substHead target source p.2) with
      | some q => union acc [q]
      | none => acc)
    split
    · rename_i q'' hq''
      have hsame : q'' = y := Option.some.inj (hq''.symm.trans hg)
      exact (mem_union _ _ _).mpr (Or.inr (List.mem_singleton.mpr hsame.symm))
    · rename_i hnone
      exact absurd (hnone.symm.trans hg) (by simp)

/-- Every row but a copy keeps its successors' live pairs. -/
theorem mem_transfer_of_not_copy {names : List String} {event : Event} {targets : List Nat}
    (hnotCopy : ∀ t s, event ≠ .copy t s) {succ : List Pair} {q : Pair} (hq : q ∈ succ) :
    q ∈ distanceTransfer names ⟨event, targets⟩ succ := by
  cases event with
  | copy t s => exact absurd rfl (hnotCopy t s)
  | less l r | equal l r | assertEqual l r =>
    show q ∈ (match pairOf names l r with | some q' => union succ [q'] | none => succ)
    split
    · exact (mem_union _ _ _).mpr (Or.inl hq)
    · exact hq
  | _ => exact hq

/-- A comparison row makes its own pair live. -/
theorem mem_transfer_compare {names : List String} {event : Event} {targets : List Nat}
    {a b : String}
    (hcompare : event = .less a b ∨ event = .equal a b ∨ event = .assertEqual a b)
    {succ : List Pair} {q : Pair} (hpair : pairOf names a b = some q) :
    q ∈ distanceTransfer names ⟨event, targets⟩ succ := by
  rcases hcompare with rfl | rfl | rfl <;>
  · show q ∈ (match pairOf names a b with | some q' => union succ [q'] | none => succ)
    rw [hpair]
    exact (mem_union _ _ _).mpr (Or.inr (List.mem_singleton.mpr rfl))

/-- `canonical` and `pairOf` agree (`ScaWindowWorker.lean:65-75`). -/
theorem canonical_cases (names : List String) (a b : String) :
    (a = b ∧ canonical names a b = (none, 1) ∧ pairOf names a b = none) ∨
    (canonical names a b = (some (a, b), 1) ∧ pairOf names a b = some (a, b)) ∨
    (canonical names a b = (some (b, a), -1) ∧ pairOf names a b = some (b, a)) := by
  unfold canonical pairOf
  by_cases hab : a = b
  · exact Or.inl ⟨hab, by simp [hab]⟩
  · by_cases hlt : names.idxOf a < names.idxOf b
    · exact Or.inr (Or.inl (by simp [hab, hlt]))
    · exact Or.inr (Or.inr (by simp [hab, hlt]))

/-! ## The register transfer columns of a row -/

/-- The `r_i` columns of `fieldsAt` (`ScaWindowWorker.lean:228-245`), for one register. -/
def regUpdateAt (spec : WorkerSpec) (distanceBefore : Array (List Pair)) (row : Row) (i : Nat) :
    RegUpdate :=
  let distanceAfter := successorsUnion distanceBefore row.targets
  let dcolor (p : Pair) : Option Nat := lookupFirst p spec.distances.colors
  let default : RegUpdate := { source := some i, reverse := false, delta := 0 }
  match row.event with
  | .move moves =>
    let deltas := moves.map (fun m => (m.head, m.delta))
    distanceAfter.foldl (fun u p =>
      if dcolor p = some i then
        { u with delta := (lookupLast p.1 deltas).getD 0 - (lookupLast p.2 deltas).getD 0 }
      else u) default
  | .copy target source =>
    distanceAfter.foldl (fun u p =>
      if (p.1 = target ∨ p.2 = target) ∧ dcolor p = some i then
        let (original, sign) := canonical spec.names
          (if p.1 = target then source else p.1) (if p.2 = target then source else p.2)
        { u with source := original.bind dcolor, reverse := decide (sign = -1) }
      else u) default
  | _ => default

theorem fieldsAt_regs (spec : WorkerSpec) (rb : Array (List String)) (db : Array (List Pair))
    (state : Nat) (row : Row) :
    (fieldsAt spec rb db state row).regs =
      (List.range spec.distances.registers).map (regUpdateAt spec db row) :=
  rfl

theorem fieldsAt_regs_getElem? (spec : WorkerSpec) (rb : Array (List String))
    (db : Array (List Pair)) (state : Nat) (row : Row) {i : Nat}
    (hi : i < spec.distances.registers) :
    (fieldsAt spec rb db state row).regs[i]? = some (regUpdateAt spec db row i) := by
  rw [fieldsAt_regs, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem regUpdateAt_move (spec : WorkerSpec) (db : Array (List Pair)) (moves : List Movement)
    (targets : List Nat) {i : Nat} {q : Pair} (hq : q ∈ successorsUnion db targets)
    (hcolor : lookupFirst q spec.distances.colors = some i)
    (hunique : ∀ p ∈ successorsUnion db targets,
      lookupFirst p spec.distances.colors = some i → p = q) :
    regUpdateAt spec db ⟨.move moves, targets⟩ i =
      { source := some i, reverse := false,
        delta := moveDelta moves q.1 - moveDelta moves q.2 } :=
  foldl_ite_unique (fun p : Pair => lookupFirst p spec.distances.colors = some i)
    (fun p (u : RegUpdate) => { u with delta := moveDelta moves p.1 - moveDelta moves p.2 })
    (fun _ _ _ => rfl) (successorsUnion db targets) q hq hcolor hunique
    { source := some i, reverse := false, delta := 0 }

theorem regUpdateAt_copy_involved (spec : WorkerSpec) (db : Array (List Pair))
    (target source : String) (targets : List Nat) {i : Nat} {q : Pair}
    (hq : q ∈ successorsUnion db targets) (hcolor : lookupFirst q spec.distances.colors = some i)
    (hinvolved : q.1 = target ∨ q.2 = target)
    (hunique : ∀ p ∈ successorsUnion db targets,
      lookupFirst p spec.distances.colors = some i → p = q) :
    regUpdateAt spec db ⟨.copy target source, targets⟩ i =
      { source := (canonical spec.names (substHead target source q.1)
            (substHead target source q.2)).1.bind (fun p => lookupFirst p spec.distances.colors),
        reverse := decide ((canonical spec.names (substHead target source q.1)
            (substHead target source q.2)).2 = -1),
        delta := 0 } :=
  foldl_ite_unique
    (fun p : Pair => (p.1 = target ∨ p.2 = target) ∧ lookupFirst p spec.distances.colors = some i)
    (fun p (u : RegUpdate) =>
      { u with
        source := (canonical spec.names (substHead target source p.1)
          (substHead target source p.2)).1.bind (fun p => lookupFirst p spec.distances.colors),
        reverse := decide ((canonical spec.names (substHead target source p.1)
          (substHead target source p.2)).2 = -1) })
    (fun _ _ _ => rfl) (successorsUnion db targets) q hq ⟨hinvolved, hcolor⟩
    (fun p hp hPp => hunique p hp hPp.2)
    { source := some i, reverse := false, delta := 0 }

theorem regUpdateAt_copy_uninvolved (spec : WorkerSpec) (db : Array (List Pair))
    (target source : String) (targets : List Nat) {i : Nat} {q : Pair}
    (huninvolved : ¬ (q.1 = target ∨ q.2 = target))
    (hunique : ∀ p ∈ successorsUnion db targets,
      lookupFirst p spec.distances.colors = some i → p = q) :
    regUpdateAt spec db ⟨.copy target source, targets⟩ i =
      { source := some i, reverse := false, delta := 0 } :=
  foldl_ite_none
    (fun p : Pair => (p.1 = target ∨ p.2 = target) ∧ lookupFirst p spec.distances.colors = some i)
    (fun p (u : RegUpdate) =>
      { u with
        source := (canonical spec.names (substHead target source p.1)
          (substHead target source p.2)).1.bind (fun p => lookupFirst p spec.distances.colors),
        reverse := decide ((canonical spec.names (substHead target source p.1)
          (substHead target source p.2)).2 = -1) })
    (successorsUnion db targets) { source := some i, reverse := false, delta := 0 }
    (fun p hp hPp => huninvolved (hunique p hp hPp.2 ▸ hPp.1))

theorem regUpdateAt_other (spec : WorkerSpec) (db : Array (List Pair)) {event : Event}
    (targets : List Nat) (i : Nat) (hnotMove : ∀ moves, event ≠ .move moves)
    (hnotCopy : ∀ t s, event ≠ .copy t s) :
    regUpdateAt spec db ⟨event, targets⟩ i = { source := some i, reverse := false, delta := 0 } := by
  cases event with
  | move moves => exact absurd rfl (hnotMove moves)
  | copy t s => exact absurd rfl (hnotCopy t s)
  | _ => rfl

theorem headStep_other {event : Event} (pos : String → Int) (hnotMove : ∀ moves, event ≠ .move moves)
    (hnotCopy : ∀ t s, event ≠ .copy t s) : headStep event pos = pos := by
  cases event with
  | move moves => exact absurd rfl (hnotMove moves)
  | copy t s => exact absurd rfl (hnotCopy t s)
  | _ => rfl

/-! ## The effects of a step on the registers and the special keys -/

/-- The fields a worker effect other than `execute` never writes. -/
def counters (s : WorkerState) : Nat × Nat × Int × Int := (s.begin, s.end, s.length, s.h)

/-- `counters`, the registers and the pc. -/
def frame (s : WorkerState) : List Int × (Nat × Nat × Int × Int) × Nat :=
  (s.regs, counters s, s.pc)

theorem checks_frame (spec : WorkerSpec) (f : Fields) (active : Bool) (s : WorkerState) :
    frame (checks spec f active s) = frame s :=
  rfl

theorem moveReg_frame (f : Fields) (active : Bool) (srcPos : Option Nat) (srcRev : Option Bool)
    (s : WorkerState) (i : Nat) : frame (moveReg f active srcPos srcRev s i) = frame s := by
  simp only [moveReg]
  split <;> rfl

theorem foldl_frame {α : Type} (g : WorkerState → α → WorkerState)
    (hg : ∀ s a, frame (g s a) = frame s) (l : List α) (s : WorkerState) :
    frame (l.foldl g s) = frame s := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => exact (ih (g s a)).trans (hg s a)

theorem moves_frame (spec : WorkerSpec) (f : Fields) (active : Bool) (s : WorkerState) :
    frame (moves spec f active s) = frame s :=
  foldl_frame _ (fun s i => moveReg_frame f active _ _ s i) _ s

theorem finish_frame (spec : WorkerSpec) (f : Fields) (active : Bool) (s : WorkerState) :
    frame (finish spec f active s) = frame s := by
  simp only [finish]
  split <;> (try split) <;> (try split) <;> rfl

theorem execute_counters (f : Fields) (active : Bool) (s : WorkerState) :
    counters (execute f active s) = counters s ∧ (execute f active s).pc = s.pc := by
  cases active <;> exact ⟨rfl, rfl⟩

theorem effect_regs (spec : WorkerSpec) (f : Fields) (active : Bool) (s : WorkerState) :
    (effect spec f active s).regs = (execute f active s).regs := by
  have hfinish := congrArg (·.1) (finish_frame spec f active
    (moves spec f active (execute f active (checks spec f active s))))
  have hmoves := congrArg (·.1) (moves_frame spec f active
    (execute f active (checks spec f active s)))
  simp only [frame] at hfinish hmoves
  unfold effect
  rw [hfinish, hmoves]
  cases active <;> rfl

theorem effect_counters (spec : WorkerSpec) (f : Fields) (active : Bool) (s : WorkerState) :
    counters (effect spec f active s) = counters s ∧ (effect spec f active s).pc = s.pc := by
  have hfinish := finish_frame spec f active
    (moves spec f active (execute f active (checks spec f active s)))
  have hmoves := moves_frame spec f active (execute f active (checks spec f active s))
  obtain ⟨hexecCounters, hexecPc⟩ := execute_counters f active (checks spec f active s)
  simp only [frame, Prod.mk.injEq] at hfinish hmoves
  unfold effect
  rw [hfinish.2.1, hfinish.2.2, hmoves.2.1, hmoves.2.2, hexecCounters, hexecPc]
  exact ⟨rfl, rfl⟩

theorem execute_getD (f : Fields) (s : WorkerState) {i : Nat} (hi : i < s.regs.length)
    {u : RegUpdate} (hu : f.regs[i]? = some u) :
    (execute f true s).regs.getD i 0 =
      (if u.reverse then -selectReg s.regs u.source else selectReg s.regs u.source) + u.delta := by
  simp [execute, List.getD_eq_getElem?_getD, hi, hu]

theorem execute_length (f : Fields) (active : Bool) (s : WorkerState) :
    (execute f active s).regs.length = s.regs.length := by
  cases active
  · rfl
  · simp [execute]

/-! ## Transport of the invariant along frame-preserving maps -/

theorem RegInv.congr {spec : WorkerSpec} {pos : String → Int} {s t : WorkerState}
    (hinv : RegInv spec pos s) (hregs : t.regs = s.regs) (hpc : t.pc = s.pc) :
    RegInv spec pos t :=
  ⟨hregs ▸ hinv.regsLength, hpc ▸ hinv.pcInRange,
    fun p hp => hregs ▸ hinv.live p (hpc ▸ hp)⟩

theorem KeyInv.congr {spec : WorkerSpec} {markEnd : Nat} {s t : WorkerState}
    (hinv : KeyInv spec markEnd s) (hcounters : counters t = counters s) :
    KeyInv spec markEnd t := by
  simp only [counters, Prod.mk.injEq] at hcounters
  obtain ⟨hbegin, hend, hlength, hh⟩ := hcounters
  exact ⟨by rw [hlength, hend, hbegin]; exact hinv.lengthEq, hbegin ▸ hinv.beginLeMark,
    hend ▸ hinv.markLeEnd, by rw [hh, hend]; exact hinv.hEq⟩

theorem Inv.of_frame {spec : WorkerSpec} {g : Ghost} {s t : WorkerState} (hinv : Inv spec g s)
    (hframe : frame t = frame s) : Inv spec g t := by
  simp only [frame, Prod.mk.injEq] at hframe
  exact ⟨hinv.regs.congr hframe.1 hframe.2.2, hinv.keys.congr hframe.2.1⟩

/-! ## One step -/

section Step

variable {spec : WorkerSpec}

/-- Registers after the row: every pair live after row `r` is tracked, for the positions
moved by the row's event. -/
theorem tracks_after_move (tables : TableFacts spec) {r : Nat} {moves : List Movement}
    {targets : List Nat} (hrow : spec.program.code[r]? = some ⟨.move moves, targets⟩)
    {pos : String → Int} {s : WorkerState}
    (hregsLength : s.regs.length = spec.distances.registers)
    (hlive : ∀ p ∈ liveAt spec r, Tracks spec pos s.regs p)
    {q : Pair} (hq : q ∈ afterAt spec ⟨.move moves, targets⟩) :
    Tracks spec (headStep (.move moves) pos)
      (execute (fieldsAt spec (liveReaders spec) (liveDistances spec) r ⟨.move moves, targets⟩)
        true s).regs q := by
  obtain ⟨i, hcolor, hi⟩ := tables.afterColored r _ hrow q hq
  have hunique : ∀ p ∈ afterAt spec ⟨.move moves, targets⟩,
      lookupFirst p spec.distances.colors = some i → p = q :=
    fun p hp hpc => tables.afterColorsInjective r _ hrow p hp q hq (hpc.trans hcolor.symm)
  refine ⟨i, hcolor, ?_⟩
  rw [execute_getD _ s (hregsLength ▸ hi) (fieldsAt_regs_getElem? _ _ _ _ _ hi),
    regUpdateAt_move spec _ moves targets hq hcolor hunique]
  have hqLive : q ∈ liveAt spec r :=
    tables.transferLive r _ hrow q (mem_transfer_of_not_copy (by intro _ _ h; cases h) hq)
  obtain ⟨j, hj, hval⟩ := hlive q hqLive
  have hji : j = i := Option.some.inj (hj.symm.trans hcolor)
  subst hji
  simp only [selectReg, Bool.false_eq_true, if_false, hval, headStep]
  ring

theorem tracks_after_copy (tables : TableFacts spec) {r : Nat} {target source : String}
    {targets : List Nat} (hrow : spec.program.code[r]? = some ⟨.copy target source, targets⟩)
    {pos : String → Int} {s : WorkerState}
    (hregsLength : s.regs.length = spec.distances.registers)
    (hlive : ∀ p ∈ liveAt spec r, Tracks spec pos s.regs p)
    {q : Pair} (hq : q ∈ afterAt spec ⟨.copy target source, targets⟩) :
    Tracks spec (headStep (.copy target source) pos)
      (execute (fieldsAt spec (liveReaders spec) (liveDistances spec) r
        ⟨.copy target source, targets⟩) true s).regs q := by
  obtain ⟨i, hcolor, hi⟩ := tables.afterColored r _ hrow q hq
  have hunique : ∀ p ∈ afterAt spec ⟨.copy target source, targets⟩,
      lookupFirst p spec.distances.colors = some i → p = q :=
    fun p hp hpc => tables.afterColorsInjective r _ hrow p hp q hq (hpc.trans hcolor.symm)
  refine ⟨i, hcolor, ?_⟩
  rw [execute_getD _ s (hregsLength ▸ hi) (fieldsAt_regs_getElem? _ _ _ _ _ hi),
    headStep_copy, headStep_copy]
  have hliveOf : ∀ {q' : Pair},
      pairOf spec.names (substHead target source q.1) (substHead target source q.2) = some q' →
        Tracks spec pos s.regs q' :=
    fun hpair => hlive _ (tables.transferLive r _ hrow _ (mem_transfer_copy hq hpair))
  by_cases hinvolved : q.1 = target ∨ q.2 = target
  · rw [regUpdateAt_copy_involved spec _ target source targets hq hcolor hinvolved hunique]
    rcases canonical_cases spec.names (substHead target source q.1) (substHead target source q.2)
      with ⟨hsame, hcan, _⟩ | ⟨hcan, hpair⟩ | ⟨hcan, hpair⟩
    · rw [hcan, hsame]
      simp [selectReg]
    · obtain ⟨j, hj, hval⟩ := hliveOf hpair
      rw [hcan]
      simp only [Option.bind_some, hj, selectReg]
      rw [hval]
      norm_num
    · obtain ⟨j, hj, hval⟩ := hliveOf hpair
      rw [hcan]
      simp only [Option.bind_some, hj, selectReg]
      rw [hval]
      norm_num
  · rw [regUpdateAt_copy_uninvolved spec _ target source targets hinvolved hunique]
    have hsubst1 : substHead target source q.1 = q.1 := by
      unfold substHead; rw [if_neg fun h => hinvolved (Or.inl h)]
    have hsubst2 : substHead target source q.2 = q.2 := by
      unfold substHead; rw [if_neg fun h => hinvolved (Or.inr h)]
    have hcanonical := tables.afterCanonical r _ hrow q hq
    obtain ⟨j, hj, hval⟩ := hliveOf (by rw [hsubst1, hsubst2]; exact hcanonical)
    have hji : j = i := Option.some.inj (hj.symm.trans hcolor)
    subst hji
    simp only [selectReg, Bool.false_eq_true, if_false, hval, hsubst1, hsubst2, add_zero]

theorem tracks_after_other (tables : TableFacts spec) {r : Nat} {event : Event}
    {targets : List Nat} (hrow : spec.program.code[r]? = some ⟨event, targets⟩)
    (hnotMove : ∀ moves, event ≠ .move moves) (hnotCopy : ∀ t s, event ≠ .copy t s)
    {pos : String → Int} {s : WorkerState}
    (hregsLength : s.regs.length = spec.distances.registers)
    (hlive : ∀ p ∈ liveAt spec r, Tracks spec pos s.regs p)
    {q : Pair} (hq : q ∈ afterAt spec ⟨event, targets⟩) :
    Tracks spec (headStep event pos)
      (execute (fieldsAt spec (liveReaders spec) (liveDistances spec) r ⟨event, targets⟩)
        true s).regs q := by
  obtain ⟨i, hcolor, hi⟩ := tables.afterColored r _ hrow q hq
  refine ⟨i, hcolor, ?_⟩
  rw [execute_getD _ s (hregsLength ▸ hi) (fieldsAt_regs_getElem? _ _ _ _ _ hi),
    regUpdateAt_other spec _ targets i hnotMove hnotCopy, headStep_other pos hnotMove hnotCopy]
  have hqLive : q ∈ liveAt spec r :=
    tables.transferLive r _ hrow q (mem_transfer_of_not_copy hnotCopy hq)
  obtain ⟨j, hj, hval⟩ := hlive q hqLive
  have hji : j = i := Option.some.inj (hj.symm.trans hcolor)
  subst hji
  simp only [selectReg, Bool.false_eq_true, if_false, hval, add_zero]

/-- **The register transfer of one row.** Every pair live after row `r` is tracked after
`execute`, for the positions moved by the row's event. -/
theorem tracks_after (tables : TableFacts spec) {r : Nat} {row : Row}
    (hrow : spec.program.code[r]? = some row) {pos : String → Int} {s : WorkerState}
    (hregsLength : s.regs.length = spec.distances.registers)
    (hlive : ∀ p ∈ liveAt spec r, Tracks spec pos s.regs p)
    {q : Pair} (hq : q ∈ afterAt spec row) :
    Tracks spec (headStep row.event pos)
      (execute (fieldsAt spec (liveReaders spec) (liveDistances spec) r row) true s).regs q := by
  obtain ⟨event, targets⟩ := row
  cases event
  case move moves => exact tracks_after_move tables hrow hregsLength hlive hq
  case copy target source => exact tracks_after_copy tables hrow hregsLength hlive hq
  all_goals
    exact tracks_after_other tables hrow (fun _ h => by cases h) (fun _ _ h => by cases h)
      hregsLength hlive hq

/-- The row a step jumps to is a successor, or the row itself when it has none. -/
theorem jump_cases (spec : WorkerSpec) (rb : Array (List String)) (db : Array (List Pair))
    (r : Nat) (row : Row) (decided : Bool) :
    (if decided then (fieldsAt spec rb db r row).yes else (fieldsAt spec rb db r row).no)
        ∈ row.targets ∨
      (row.targets = [] ∧
        (if decided then (fieldsAt spec rb db r row).yes else (fieldsAt spec rb db r row).no) = r) := by
  rw [fieldsAt_yes, fieldsAt_no]
  obtain ⟨event, targets⟩ := row
  cases targets with
  | nil => right; cases decided <;> cases isTest event <;> simp
  | cons t ts =>
    left
    cases decided
    · simp
    · cases isTest event
      · simp
      · cases ts <;> simp

/-- The ghost after one step: the executed row's event, if active. -/
def ghostStep (spec : WorkerSpec) (active : Bool) (s : WorkerState) (g : Ghost) : Ghost :=
  if active then { g with pos := headStep ((Worker.ofSpec spec).fields s.pc).event g.pos } else g

/-- **One step** preserves the invariant, the ghost following the head program. -/
theorem step_inv (tables : TableFacts spec) {g : Ghost} {s : WorkerState} (hinv : Inv spec g s)
    (active : Bool) :
    Inv spec (ghostStep spec active s g) (step (Worker.ofSpec spec) active s) := by
  obtain ⟨row, hrow⟩ : ∃ row, spec.program.code[s.pc]? = some row :=
    ⟨_, List.getElem?_eq_getElem hinv.regs.pcInRange⟩
  have hfields : (Worker.ofSpec spec).fields s.pc =
      fieldsAt spec (liveReaders spec) (liveDistances spec) s.pc row := fields_ofSpec spec hrow
  obtain ⟨hcounters, hpc⟩ := effect_counters spec ((Worker.ofSpec spec).fields s.pc) active s
  rw [step_eq]
  cases active
  · have hframe : frame (effect (Worker.ofSpec spec).spec ((Worker.ofSpec spec).fields s.pc)
        false s) = frame s := by
      simp only [frame, Prod.mk.injEq]
      exact ⟨effect_regs .., hcounters, hpc⟩
    exact hinv.of_frame hframe
  · simp only [if_true, ghostStep]
    have hregs := effect_regs spec ((Worker.ofSpec spec).fields s.pc) true s
    refine ⟨⟨?_, ?_, ?_⟩, hinv.keys.congr hcounters⟩
    · show (effect spec _ true s).regs.length = _
      rw [hregs, execute_length]
      exact hinv.regs.regsLength
    · show (if decision _ s then _ else _) < _
      rw [hfields]
      rcases jump_cases spec (liveReaders spec) (liveDistances spec) s.pc row (decision _ s)
        with hmem | ⟨_, hself⟩
      · exact tables.targetsInRange s.pc row hrow _ hmem
      · rw [hself]; exact hinv.regs.pcInRange
    · show ∀ p ∈ liveAt spec (if decision _ s then _ else _), Tracks spec _
        (effect spec _ true s).regs p
      rw [hregs, hfields, fieldsAt_event]
      intro p hp
      rcases jump_cases spec (liveReaders spec) (liveDistances spec) s.pc row
          (decision (fieldsAt spec (liveReaders spec) (liveDistances spec) s.pc row) s)
        with hmem | ⟨hnoTargets, hself⟩
      · exact tracks_after tables hrow hinv.regs.regsLength hinv.regs.live
          (liveAt_subset_afterAt hmem hp)
      · rw [hself, tables.targetlessDead s.pc row hrow hnoTargets] at hp
        simp at hp

/-- The ghost along a service quantum. -/
def ghostService (spec : WorkerSpec) (s : WorkerState) (g : Ghost) : WorkerState × Ghost :=
  (List.range spec.quantum).foldl
    (fun sg _ =>
      let active := decide (sg.1.mode = .run)
      (step (Worker.ofSpec spec) active sg.1, ghostStep spec active sg.1 sg.2))
    (s, g)

theorem ghostService_fst (s : WorkerState) (g : Ghost) :
    (ghostService spec s g).1 = service (Worker.ofSpec spec) s := by
  unfold ghostService service
  rw [ofSpec_spec]
  generalize List.range spec.quantum = steps
  induction steps generalizing s g with
  | nil => rfl
  | cons _ steps ih => exact ih _ _

/-- **One service quantum** preserves the invariant. -/
theorem service_inv (tables : TableFacts spec) {g : Ghost} {s : WorkerState}
    (hinv : Inv spec g s) :
    Inv spec (ghostService spec s g).2 (service (Worker.ofSpec spec) s) := by
  rw [← ghostService_fst s g]
  unfold ghostService
  generalize List.range spec.quantum = steps
  induction steps generalizing s g with
  | nil => exact hinv
  | cons _ steps ih => exact ih (step_inv tables hinv _)

end Step

/-! ## `arrive`, `mark`, `resetFlags` -/

section Stream

variable {spec : WorkerSpec}

/-- `arrive` keeps the registers and the pc; `end` and `length` (and a flag worker's `h`)
count the new letter. The ghost is unchanged. -/
theorem arrive_inv {g : Ghost} {s : WorkerState} (hinv : Inv spec g s) (c : Fin 2) :
    Inv spec g (arrive (Worker.ofSpec spec) c s) := by
  obtain ⟨hregs, ⟨hlength, hbeginMark, hmarkEnd, hh⟩⟩ := hinv
  unfold arrive
  rw [ofSpec_spec]
  cases hflags : spec.isFlags
  · refine ⟨hregs.congr rfl rfl, ⟨?_, hbeginMark, ?_, ?_⟩⟩
    · show s.length + 1 = ((s.end + 1 : Nat) : Int) - s.begin
      push_cast; omega
    · show g.markEnd ≤ s.end + 1
      omega
    · show s.h = if spec.isFlags then ((s.end + 1 : Nat) : Int) - g.markEnd else 0
      rw [hflags] at hh ⊢
      exact hh
  · refine ⟨hregs.congr rfl rfl, ⟨?_, hbeginMark, ?_, ?_⟩⟩
    · show s.length + 1 = ((s.end + 1 : Nat) : Int) - s.begin
      push_cast; omega
    · show g.markEnd ≤ s.end + 1
      omega
    · show s.h + 1 = if spec.isFlags then ((s.end + 1 : Nat) : Int) - g.markEnd else 0
      rw [hflags] at hh ⊢
      simp only [if_true] at hh ⊢
      push_cast; omega

/-- The ghost after `mark`/`resetFlags`: `markEnd := end`. -/
def ghostMark (enabled : Bool) (s : WorkerState) (g : Ghost) : Ghost :=
  if enabled then { g with markEnd := s.end } else g

theorem mark_inv {g : Ghost} {s : WorkerState} (hinv : Inv spec g s) (enabled : Bool) :
    Inv spec (ghostMark enabled s g) (mark (Worker.ofSpec spec) enabled s) := by
  cases enabled
  · exact hinv
  · obtain ⟨hregs, ⟨hlength, hbeginMark, hmarkEnd, _⟩⟩ := hinv
    refine ⟨hregs.congr rfl rfl, ⟨hlength, ?_, le_refl _, ?_⟩⟩
    · exact le_trans hbeginMark hmarkEnd
    · show (0 : Int) = if spec.isFlags then (s.end : Int) - s.end else 0
      split <;> simp

theorem resetFlags_inv {g : Ghost} {s : WorkerState} (hinv : Inv spec g s) (enabled : Bool) :
    Inv spec (ghostMark enabled s g) (resetFlags (Worker.ofSpec spec) enabled s) := by
  cases enabled
  · exact hinv
  · obtain ⟨hregs, _⟩ := hinv
    refine ⟨hregs.congr rfl rfl, ⟨?_, le_refl _, le_refl _, ?_⟩⟩
    · show (0 : Int) = (s.end : Int) - s.end
      simp
    · show (0 : Int) = if spec.isFlags then (s.end : Int) - s.end else 0
      split <;> simp

end Stream

/-! ## `start` and the initial state -/

section Start

variable {spec : WorkerSpec}

/-- The logical positions `start` sets up (`SCA_GS_MAPPING.md` §0): the matcher's `Tail` at
`length`, every other head at `0`; the flag worker's `OriginalEnd` and `Upper` at `length`,
`Lower` at `length - h`, every other head at `0`. -/
def startPos (spec : WorkerSpec) (len h : Int) (head : String) : Int :=
  if spec.isFlags then
    if head = "OriginalEnd" ∨ head = "Upper" then len else if head = "Lower" then len - h else 0
  else if head = "Tail" then len else 0

/-- The value `initializeValues` assigns for one mapping entry (`ScaWindowWorker.lean:412-416`). -/
def initValue (s : WorkerState) : Option (DistKey × Int) → Int
  | none => 0
  | some (k, sign) => if sign = -1 then -s.getDist k else s.getDist k

/-- A mapping value reads `length` or `h`, not a distance register. -/
def readsCounter : Option (DistKey × Int) → Bool
  | some (.reg _, _) => false
  | _ => true

/-- One assignment of `initializeValues` (`ScaWindowWorker.lean:408-416`). -/
def initStep (spec : WorkerSpec) (s : WorkerState) (e : Pair × Option (DistKey × Int)) :
    WorkerState :=
  match lookupFirst e.1 spec.distances.colors with
  | none => s
  | some i =>
    match e.2 with
    | none => s.setDist (.reg i) 0
    | some (k, sign) =>
      let v := s.getDist k
      s.setDist (.reg i) (if sign = -1 then -v else v)

theorem initializeValues_true (M : List (Pair × Option (DistKey × Int))) (s : WorkerState) :
    initializeValues spec M true s = M.foldl (initStep spec) s :=
  rfl

theorem initStep_frame (s : WorkerState) (e : Pair × Option (DistKey × Int)) :
    counters (initStep spec s e) = counters s ∧ (initStep spec s e).pc = s.pc ∧
      (initStep spec s e).regs.length = s.regs.length := by
  unfold initStep
  split
  · exact ⟨rfl, rfl, rfl⟩
  · split <;> simp [WorkerState.setDist, counters]

theorem initStep_getD_other (s : WorkerState) (e : Pair × Option (DistKey × Int)) {j : Nat}
    (hother : lookupFirst e.1 spec.distances.colors ≠ some j) :
    (initStep spec s e).regs.getD j 0 = s.regs.getD j 0 := by
  unfold initStep
  split
  · rfl
  · rename_i i hcolor
    have hij : i ≠ j := fun hij => hother (hij ▸ hcolor)
    split <;> simp [WorkerState.setDist, List.getD_eq_getElem?_getD, List.getElem?_set_ne hij]

theorem initStep_getD_self (s : WorkerState) (e : Pair × Option (DistKey × Int)) {i : Nat}
    (hcolor : lookupFirst e.1 spec.distances.colors = some i) (hlt : i < s.regs.length) :
    (initStep spec s e).regs.getD i 0 = initValue s e.2 := by
  unfold initStep
  rw [hcolor]
  obtain ⟨pair, value⟩ := e
  cases value with
  | none => simp [WorkerState.setDist, initValue, List.getD_eq_getElem?_getD, hlt]
  | some kv =>
    obtain ⟨k, sign⟩ := kv
    simp [WorkerState.setDist, initValue, List.getD_eq_getElem?_getD, hlt]

theorem initValue_congr {s t : WorkerState} (hcounters : counters t = counters s)
    {v : Option (DistKey × Int)} (hreads : readsCounter v = true) :
    initValue t v = initValue s v := by
  simp only [counters, Prod.mk.injEq] at hcounters
  obtain ⟨-, -, hlength, hh⟩ := hcounters
  rcases v with _ | ⟨k, sign⟩
  · rfl
  · cases k with
    | reg i => simp [readsCounter] at hreads
    | length => simp [initValue, WorkerState.getDist, hlength]
    | h => simp [initValue, WorkerState.getDist, hh]

theorem initFold_frame (M : List (Pair × Option (DistKey × Int))) (s : WorkerState) :
    counters (M.foldl (initStep spec) s) = counters s ∧ (M.foldl (initStep spec) s).pc = s.pc ∧
      (M.foldl (initStep spec) s).regs.length = s.regs.length := by
  induction M generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons e M ih =>
    obtain ⟨hcounters, hpc, hlength⟩ := ih (initStep spec s e)
    obtain ⟨hcounters', hpc', hlength'⟩ := initStep_frame (spec := spec) s e
    exact ⟨hcounters.trans hcounters', hpc.trans hpc', hlength.trans hlength'⟩

theorem initFold_getD_other (M : List (Pair × Option (DistKey × Int))) (s : WorkerState)
    {j : Nat} (hother : ∀ e ∈ M, lookupFirst e.1 spec.distances.colors ≠ some j) :
    (M.foldl (initStep spec) s).regs.getD j 0 = s.regs.getD j 0 := by
  induction M generalizing s with
  | nil => rfl
  | cons e M ih =>
    rw [List.foldl_cons, ih _ fun e' he' => hother e' (List.mem_cons_of_mem _ he'),
      initStep_getD_other s e (hother e (List.mem_cons_self ..))]

theorem initFold_getD (M : List (Pair × Option (DistKey × Int)))
    (hreads : ∀ e ∈ M, readsCounter e.2 = true)
    (hnodup : (M.map fun e => lookupFirst e.1 spec.distances.colors).Nodup) (s : WorkerState)
    {e : Pair × Option (DistKey × Int)} (he : e ∈ M) {i : Nat}
    (hcolor : lookupFirst e.1 spec.distances.colors = some i) (hlt : i < s.regs.length) :
    (M.foldl (initStep spec) s).regs.getD i 0 = initValue s e.2 := by
  induction M generalizing s with
  | nil => simp at he
  | cons e₀ M ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    rw [List.foldl_cons]
    rcases List.mem_cons.mp he with rfl | heTail
    · rw [initFold_getD_other M _ fun e' he' hcolor' =>
        hnodup.1 (hcolor ▸ hcolor' ▸ List.mem_map_of_mem he'),
        initStep_getD_self s e hcolor hlt]
    · rw [ih (fun e' he' => hreads e' (List.mem_cons_of_mem _ he')) hnodup.2 _ heTail
        ((initStep_frame s e₀).2.2 ▸ hlt)]
      exact initValue_congr (initStep_frame s e₀).1 (hreads e (List.mem_cons_of_mem _ heTail))

theorem rawStart_frame (w : Worker) (head : String) (source : Nat) (reversed enabled : Bool)
    (s : WorkerState) : frame (rawStart w head source reversed enabled s) = frame s := by
  unfold rawStart
  split
  · rfl
  · split <;> rfl

/-- `startBody` is `initializeValues` of the start mapping on a state with the same registers,
counters and pc, up to fields outside the frame. -/
theorem startBody_frame (enabled : Bool) (s : WorkerState) :
    ∃ t, frame t = frame s ∧
      frame (startBody (Worker.ofSpec spec) enabled s) =
        frame (initializeValues spec (startMapping spec) enabled t) := by
  unfold startBody startMapping
  rw [ofSpec_spec]
  cases hflags : spec.isFlags
  · simp only [Bool.false_eq_true, if_false]
    exact ⟨_, (rawStart_frame ..).trans (rawStart_frame ..), rfl⟩
  · simp only [if_true]
    refine ⟨rawStart (Worker.ofSpec spec) "OriginalEnd" s.begin true enabled
      (rawStart (Worker.ofSpec spec) "TextOrigin" s.end true enabled
        (rawStart (Worker.ofSpec spec) "Origin" s.begin false enabled
          { s with fault := s.fault || (enabled && decide (s.mode = .run)) })), ?_, ?_⟩
    · rw [rawStart_frame, rawStart_frame, rawStart_frame]
      rfl
    · cases enabled <;> rfl

theorem initializeValues_frame_false (M : List (Pair × Option (DistKey × Int)))
    (s : WorkerState) : initializeValues spec M false s = s :=
  rfl

theorem startMapping_readsCounter : ∀ e ∈ startMapping spec, readsCounter e.2 = true := by
  unfold startMapping
  split <;> decide

theorem startMapping_sound (s : WorkerState) :
    ∀ e ∈ startMapping spec,
      initValue s e.2 = startPos spec s.length s.h e.1.1 - startPos spec s.length s.h e.1.2 := by
  unfold startMapping startPos
  cases hflags : spec.isFlags
  · simp [matcherStartMapping, initValue, WorkerState.getDist]
  · simp [flagsStartMapping, initValue, WorkerState.getDist]

/-- The ghost after `start`: the positions it sets up, if enabled. -/
def ghostStart (spec : WorkerSpec) (enabled : Bool) (s : WorkerState) (g : Ghost) : Ghost :=
  if enabled then { g with pos := startPos spec s.length s.h } else g

/-- **`start`** establishes the invariant (when enabled) or keeps it. -/
theorem start_inv (tables : TableFacts spec) {g : Ghost} {s : WorkerState} (hinv : Inv spec g s)
    (enabled : Bool) :
    Inv spec (ghostStart spec enabled s g) (start (Worker.ofSpec spec) enabled s) := by
  obtain ⟨t, hframeT, hframeBody⟩ := startBody_frame (spec := spec) enabled s
  rw [start_eq]
  cases enabled
  · simp only [Bool.false_eq_true, if_false, ghostStart]
    rw [initializeValues_frame_false] at hframeBody
    exact hinv.of_frame (hframeBody.trans hframeT)
  · simp only [if_true, ghostStart]
    rw [initializeValues_true] at hframeBody
    obtain ⟨hcountersFold, -, hlengthFold⟩ := initFold_frame (spec := spec) (startMapping spec) t
    simp only [frame, Prod.mk.injEq] at hframeT hframeBody
    obtain ⟨hregsT, hcountersT, -⟩ := hframeT
    obtain ⟨hregsBody, hcountersBody, -⟩ := hframeBody
    have hcounters : counters (startBody (Worker.ofSpec spec) true s) = counters s :=
      hcountersBody.trans (hcountersFold.trans hcountersT)
    refine ⟨⟨?_, tables.startInRange, ?_⟩, hinv.keys.congr hcounters⟩
    · show (startBody (Worker.ofSpec spec) true s).regs.length = _
      rw [hregsBody, hlengthFold, hregsT]
      exact hinv.regs.regsLength
    · intro p hp
      obtain ⟨value, hmem⟩ := tables.startLiveMapped p hp
      obtain ⟨i, hcolor, hi⟩ := tables.startColored _ hmem
      refine ⟨i, hcolor, ?_⟩
      show (startBody (Worker.ofSpec spec) true s).regs.getD i 0 = _
      rw [hregsBody, initFold_getD _ startMapping_readsCounter tables.startColorsNodup t hmem
        hcolor (by rw [hregsT, hinv.regs.regsLength]; exact hi),
        initValue_congr hcountersT (startMapping_readsCounter _ hmem)]
      simp only [counters, Prod.mk.injEq] at hcounters
      exact startMapping_sound s _ hmem

/-- **The initial state** satisfies the invariant: every head at `0`, no mark yet. -/
theorem initial_inv (tables : TableFacts spec) :
    Inv spec ⟨fun _ => 0, 0⟩ (WorkerState.initial spec) := by
  refine ⟨⟨by simp [WorkerState.initial], tables.startInRange, ?_⟩, ⟨by simp [WorkerState.initial],
    le_refl _, le_refl _, by simp [WorkerState.initial]⟩⟩
  intro p hp
  obtain ⟨value, hmem⟩ := tables.startLiveMapped p hp
  obtain ⟨i, hcolor, hi⟩ := tables.startColored _ hmem
  refine ⟨i, hcolor, ?_⟩
  simp [WorkerState.initial, List.getD_eq_getElem?_getD, hi]

end Start

/-! ## Consequence: the tests compare head positions -/

section Decisions

variable {spec : WorkerSpec}

theorem fieldsAt_test (rb : Array (List String)) (db : Array (List Pair)) (state : Nat)
    {event : Event} (targets : List Nat) {a b : String}
    (hcompare : event = .less a b ∨ event = .equal a b ∨ event = .assertEqual a b) :
    (fieldsAt spec rb db state ⟨event, targets⟩).distanceTest =
        (canonical spec.names a b).1.bind (fun p => lookupFirst p spec.distances.colors) ∧
      (fieldsAt spec rb db state ⟨event, targets⟩).distanceReverse =
        decide ((canonical spec.names a b).2 = -1) := by
  rcases hcompare with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- **The distance test.** At a row `less a b`, `equal a b` or `assertEqual a b`, the worker's
`compare` (`ScaWindowWorker.lean:385-387`) returns `(pos a = pos b, pos a < pos b)`. -/
theorem compare_eq (tables : TableFacts spec) {pos : String → Int} {s : WorkerState}
    (hinv : RegInv spec pos s) {row : Row} (hrow : spec.program.code[s.pc]? = some row)
    {a b : String}
    (hcompare : row.event = .less a b ∨ row.event = .equal a b ∨ row.event = .assertEqual a b) :
    ScaWindowWorker.compare ((Worker.ofSpec spec).fields s.pc) s =
      (decide (pos a = pos b), decide (pos a < pos b)) := by
  rw [fields_ofSpec spec hrow]
  obtain ⟨event, targets⟩ := row
  obtain ⟨htest, hreverse⟩ := fieldsAt_test (spec := spec) (liveReaders spec) (liveDistances spec)
    s.pc targets hcompare
  have hlive : ∀ {q : Pair}, pairOf spec.names a b = some q → Tracks spec pos s.regs q :=
    fun hpair => hinv.live _ (tables.transferLive s.pc _ hrow _
      (mem_transfer_compare hcompare hpair))
  unfold ScaWindowWorker.compare
  rw [htest, hreverse]
  rcases canonical_cases spec.names a b with ⟨hsame, hcan, _⟩ | ⟨hcan, hpair⟩ | ⟨hcan, hpair⟩
  · rw [hcan, hsame]
    simp [selectReg]
  · obtain ⟨j, hj, hval⟩ := hlive hpair
    rw [hcan]
    simp only [Option.bind_some, hj, selectReg, hval, Prod.mk.injEq]
    refine ⟨decide_eq_decide.mpr (by omega), ?_⟩
    split
    · rename_i hsign
      simp at hsign
    · exact decide_eq_decide.mpr (by omega)
  · obtain ⟨j, hj, hval⟩ := hlive hpair
    rw [hcan]
    simp only [Option.bind_some, hj, selectReg, hval, Prod.mk.injEq]
    refine ⟨decide_eq_decide.mpr (by omega), ?_⟩
    split
    · exact decide_eq_decide.mpr (by omega)
    · rename_i hsign
      simp at hsign

theorem decision_equal (tables : TableFacts spec) {pos : String → Int} {s : WorkerState}
    (hinv : RegInv spec pos s) {row : Row} (hrow : spec.program.code[s.pc]? = some row)
    {a b : String} (hevent : row.event = .equal a b) :
    decision ((Worker.ofSpec spec).fields s.pc) s = decide (pos a = pos b) := by
  have hcompare := compare_eq tables hinv hrow (Or.inr (Or.inl hevent))
  have hfieldsEvent : ((Worker.ofSpec spec).fields s.pc).event = .equal a b := by
    rw [fields_ofSpec spec hrow, fieldsAt_event, hevent]
  unfold decision
  rw [hcompare, hfieldsEvent]
  simp [isOp, Event.op]

theorem decision_less (tables : TableFacts spec) {pos : String → Int} {s : WorkerState}
    (hinv : RegInv spec pos s) {row : Row} (hrow : spec.program.code[s.pc]? = some row)
    {a b : String} (hevent : row.event = .less a b) :
    decision ((Worker.ofSpec spec).fields s.pc) s = decide (pos a < pos b) := by
  have hcompare := compare_eq tables hinv hrow (Or.inl hevent)
  have hfieldsEvent : ((Worker.ofSpec spec).fields s.pc).event = .less a b := by
    rw [fields_ofSpec spec hrow, fieldsAt_event, hevent]
  unfold decision
  rw [hcompare, hfieldsEvent]
  simp [isOp, Event.op]

/-- The coroutine worker reads the same decision as the table worker it is related to. -/
theorem coDecision_eq {cw : CoWorker} {vs : List Entry} (hcw : Certified spec cw vs)
    {s : WorkerState} {t : CoState} (hrel : Rel vs s t) :
    decision (cw.rom t.ctl) t.body = decision ((Worker.ofSpec spec).fields s.pc) s := by
  rw [hcw.rom_eq hrel.sim]
  exact ((congrArg (decision _) hrel.agree).trans (decision_setPc _ t.body s.pc)).symm

theorem coDecision_equal {cw : CoWorker} {vs : List Entry} (hcw : Certified spec cw vs)
    (tables : TableFacts spec) {s : WorkerState} {t : CoState} (hrel : Rel vs s t)
    {pos : String → Int} (hinv : RegInv spec pos s) {row : Row}
    (hrow : spec.program.code[s.pc]? = some row) {a b : String} (hevent : row.event = .equal a b) :
    decision (cw.rom t.ctl) t.body = decide (pos a = pos b) :=
  (coDecision_eq hcw hrel).trans (decision_equal tables hinv hrow hevent)

theorem coDecision_less {cw : CoWorker} {vs : List Entry} (hcw : Certified spec cw vs)
    (tables : TableFacts spec) {s : WorkerState} {t : CoState} (hrel : Rel vs s t)
    {pos : String → Int} (hinv : RegInv spec pos s) {row : Row}
    (hrow : spec.program.code[s.pc]? = some row) {a b : String} (hevent : row.event = .less a b) :
    decision (cw.rom t.ctl) t.body = decide (pos a < pos b) :=
  (coDecision_eq hcw hrel).trans (decision_less tables hinv hrow hevent)

end Decisions

/-! ## The liveness iteration against a certificate

`liveDistances` is a Gauss–Seidel iteration (`ScaWindowWorker.fixpoint`) with fuel. Computing it
in the kernel is too expensive, so it is related to a certificate `C` instead: if the transfer is
monotone and keeps lists duplicate-free, and `C` is a post-fixpoint whose total size is below the
fuel, then the iteration stays below `C` and stops at a post-fixpoint (`fixpoint_spec`). -/

section GaussSeidel

variable {α : Type} [DecidableEq α]

theorem union_nodup (xs ys : List α) (hxs : xs.Nodup) : (union xs ys).Nodup := by
  unfold union
  induction ys generalizing xs with
  | nil => exact hxs
  | cons y ys ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact hxs
    · rename_i hy
      rw [List.nodup_append]
      exact ⟨hxs, List.nodup_singleton y, fun a ha b hb hab => hy (by
        rw [List.mem_singleton] at hb
        exact hb ▸ hab ▸ ha)⟩

theorem successorsUnion_nodup (before : Array (List α)) (targets : List Nat) :
    (successorsUnion before targets).Nodup := by
  unfold successorsUnion
  suffices hacc : ∀ acc : List α, acc.Nodup →
      (targets.foldl (fun live t => union live (before.getD t [])) acc).Nodup from
    hacc [] List.nodup_nil
  induction targets with
  | nil => intro acc hacc; exact hacc
  | cons t ts ih => intro acc hacc; exact ih _ (union_nodup _ _ hacc)

theorem successorsUnion_mono {before before' : Array (List α)}
    (hle : ∀ t, before.getD t [] ⊆ before'.getD t []) (targets : List Nat) :
    successorsUnion before targets ⊆ successorsUnion before' targets := by
  intro x hx
  obtain ⟨t, ht, hxt⟩ := (mem_successorsUnion _ _ _).mp hx
  exact (mem_successorsUnion _ _ _).mpr ⟨t, ht, hle t hxt⟩

theorem setEq_iff (xs ys : List α) : setEq xs ys = true ↔ xs ⊆ ys ∧ ys ⊆ xs := by
  simp [setEq, List.all_eq_true, List.subset_def]

omit [DecidableEq α] in
theorem length_le_of_subset {xs ys : List α} (hnodup : xs.Nodup) (hsub : xs ⊆ ys) :
    xs.length ≤ ys.length :=
  (hnodup.subperm hsub).length_le

theorem length_lt_of_subset {xs ys : List α} (hnodup : xs.Nodup) (hsub : xs ⊆ ys) {x : α}
    (hxys : x ∈ ys) (hxxs : x ∉ xs) : xs.length < ys.length := by
  have hsubErase : xs ⊆ ys.erase x := fun y hy =>
    (List.mem_erase_of_ne (fun hyx : y = x => hxxs (hyx ▸ hy))).mpr (hsub hy)
  have hle := length_le_of_subset hnodup hsubErase
  rw [List.length_erase_of_mem hxys] at hle
  have hpos : 0 < ys.length := List.length_pos_of_mem hxys
  omega

variable (code : List Row) (transfer : Row → List α → List α)

/-- The live set of `row` recomputed from the table `bs` (one Gauss–Seidel update). -/
def recompute (bs : Array (List α)) (row : Row) : List α :=
  transfer row (successorsUnion bs row.targets)

/-- Every row's recomputed set is contained in its entry. -/
def PostFix (bs : Array (List α)) : Prop :=
  ∀ r row, code[r]? = some row → recompute transfer bs row ⊆ bs.getD r []

/-- An iterate below the certificate `C`, below its own recomputation, duplicate-free. -/
structure Approx (C bs : Array (List α)) : Prop where
  size : bs.size = code.length
  below : ∀ r, bs.getD r [] ⊆ C.getD r []
  pre : ∀ r row, code[r]? = some row → bs.getD r [] ⊆ recompute transfer bs row
  nodup : ∀ r, (bs.getD r []).Nodup

/-- The total size of the rows' entries. -/
def weight (bs : Array (List α)) : Nat :=
  ∑ r ∈ Finset.range code.length, (bs.getD r []).length

/-- The loop body of `ScaWindowWorker.sweep`. -/
def sweepStep (acc : Array (List α) × Bool) (state : Nat) : Array (List α) × Bool :=
  let (bs, changed) := acc
  match code[state]? with
  | none => acc
  | some row =>
    let live := transfer row (successorsUnion bs row.targets)
    if setEq live (bs.getD state []) then (bs, changed)
    else (bs.set! state live, true)

theorem sweep_eq_foldl (before : Array (List α)) :
    sweep code transfer before =
      (List.range code.length).reverse.foldl (sweepStep code transfer) (before, false) :=
  rfl

/-- The accumulator of a sweep started from `b₀`. -/
structure SweepAcc (C b₀ : Array (List α)) (acc : Array (List α) × Bool) : Prop where
  approx : Approx code transfer C acc.1
  weightLe : weight code b₀ ≤ weight code acc.1
  grown : acc.2 = true → weight code b₀ + 1 ≤ weight code acc.1
  same : acc.2 = false → acc.1 = b₀

variable {code transfer}

theorem recompute_mono (hmono : ∀ row xs ys, xs ⊆ ys → transfer row xs ⊆ transfer row ys)
    {bs bs' : Array (List α)} (hle : ∀ t, bs.getD t [] ⊆ bs'.getD t []) (row : Row) :
    recompute transfer bs row ⊆ recompute transfer bs' row :=
  hmono row _ _ (successorsUnion_mono hle row.targets)

omit [DecidableEq α] in
theorem getD_set! (bs : Array (List α)) {state : Nat} (hlt : state < bs.size) (live : List α)
    (r : Nat) : (bs.set! state live).getD r [] = if r = state then live else bs.getD r [] := by
  by_cases hr : r = state
  · subst hr
    simp [hlt]
  · simp [Array.getElem?_setIfInBounds_ne (Ne.symm hr), hr]

theorem sweepStep_spec (hmono : ∀ row xs ys, xs ⊆ ys → transfer row xs ⊆ transfer row ys)
    (hnodup : ∀ row xs, xs.Nodup → (transfer row xs).Nodup) {C b₀ : Array (List α)}
    (hpost : PostFix code transfer C) {acc : Array (List α) × Bool}
    (hacc : SweepAcc code transfer C b₀ acc) (state : Nat) :
    SweepAcc code transfer C b₀ (sweepStep code transfer acc state) ∧
      ((sweepStep code transfer acc state).2 = false →
        acc.2 = false ∧
          ∀ row, code[state]? = some row → recompute transfer b₀ row ⊆ b₀.getD state []) := by
  obtain ⟨bs, ch⟩ := acc
  obtain ⟨happrox, hweightLe, hgrown, hsame⟩ := hacc
  dsimp only at happrox hweightLe hgrown hsame
  unfold sweepStep
  cases hrow : code[state]? with
  | none =>
    refine ⟨⟨happrox, hweightLe, hgrown, hsame⟩, fun hch => ⟨hch, fun row hrow' => ?_⟩⟩
    cases hrow'
  | some row =>
    have hlt : state < bs.size := by
      rw [happrox.size]
      exact (List.getElem?_eq_some_iff.mp hrow).1
    by_cases hset : setEq (transfer row (successorsUnion bs row.targets)) (bs.getD state []) = true
    · simp only [hset, if_true]
      refine ⟨⟨happrox, hweightLe, hgrown, hsame⟩, fun hch => ⟨hch, fun row' hrow' => ?_⟩⟩
      cases hrow'
      rw [← hsame hch]
      exact ((setEq_iff _ _).mp hset).1
    · simp only [hset, Bool.false_eq_true, if_false]
      set live := transfer row (successorsUnion bs row.targets) with hlive
      have hentry : bs.getD state [] ⊆ live := happrox.pre state row hrow
      have hgrow : ∀ t, bs.getD t [] ⊆ (bs.set! state live).getD t [] := by
        intro t
        rw [getD_set! bs hlt live t]
        split
        · rename_i ht; subst ht; exact hentry
        · exact List.Subset.refl _
      have hliveNodup : live.Nodup := hnodup row _ (successorsUnion_nodup _ _)
      obtain ⟨x, hxLive, hxEntry⟩ : ∃ x ∈ live, x ∉ bs.getD state [] := by
        by_contra hnone
        push Not at hnone
        exact hset ((setEq_iff _ _).mpr ⟨hnone, hentry⟩)
      have hstrict : (bs.getD state []).length < live.length :=
        length_lt_of_subset (happrox.nodup state) hentry hxLive hxEntry
      have hstateRange : state ∈ Finset.range code.length := by
        rw [Finset.mem_range, ← happrox.size]; exact hlt
      have hweightLt : weight code bs < weight code (bs.set! state live) := by
        unfold weight
        apply Finset.sum_lt_sum
        · intro t _
          exact length_le_of_subset (happrox.nodup t) (hgrow t)
        · refine ⟨state, hstateRange, ?_⟩
          rw [getD_set! bs hlt live state, if_pos rfl]
          exact hstrict
      refine ⟨⟨⟨?_, ?_, ?_, ?_⟩,
        show weight code b₀ ≤ weight code (bs.set! state live) by omega,
        fun _ => show weight code b₀ + 1 ≤ weight code (bs.set! state live) by omega,
        fun h => (by cases h)⟩, fun h => (by cases h)⟩
      · simp [happrox.size]
      · intro t
        rw [getD_set! bs hlt live t]
        split
        · rename_i ht
          subst ht
          exact (recompute_mono hmono happrox.below row).trans (hpost t row hrow)
        · exact happrox.below t
      · intro t row' hrow'
        rw [getD_set! bs hlt live t]
        split
        · rename_i ht
          subst ht
          rw [hrow] at hrow'
          cases hrow'
          exact recompute_mono hmono hgrow row
        · exact (happrox.pre t row' hrow').trans (recompute_mono hmono hgrow row')
      · intro t
        rw [getD_set! bs hlt live t]
        split
        · exact hliveNodup
        · exact happrox.nodup t

theorem sweepFold_spec (hmono : ∀ row xs ys, xs ⊆ ys → transfer row xs ⊆ transfer row ys)
    (hnodup : ∀ row xs, xs.Nodup → (transfer row xs).Nodup) {C b₀ : Array (List α)}
    (hpost : PostFix code transfer C) (states : List Nat) {acc : Array (List α) × Bool}
    (hacc : SweepAcc code transfer C b₀ acc) :
    SweepAcc code transfer C b₀ (states.foldl (sweepStep code transfer) acc) ∧
      ((states.foldl (sweepStep code transfer) acc).2 = false →
        acc.2 = false ∧ ∀ state ∈ states, ∀ row, code[state]? = some row →
          recompute transfer b₀ row ⊆ b₀.getD state []) := by
  induction states generalizing acc with
  | nil => exact ⟨hacc, fun hch => ⟨hch, fun _ h => by cases h⟩⟩
  | cons state states ih =>
    obtain ⟨hstep, hstepSame⟩ := sweepStep_spec hmono hnodup hpost hacc state
    obtain ⟨hres, hresSame⟩ := ih hstep
    refine ⟨hres, fun hch => ?_⟩
    obtain ⟨hstepCh, hrest⟩ := hresSame hch
    obtain ⟨haccCh, hhere⟩ := hstepSame hstepCh
    refine ⟨haccCh, fun state' hmem row hrow => ?_⟩
    rcases List.mem_cons.mp hmem with rfl | hmemTail
    · exact hhere row hrow
    · exact hrest state' hmemTail row hrow

theorem weight_le_of_approx {C bs : Array (List α)} (happrox : Approx code transfer C bs) :
    weight code bs ≤ weight code C :=
  Finset.sum_le_sum fun r _ => length_le_of_subset (happrox.nodup r) (happrox.below r)

theorem fixpoint_go_spec (hmono : ∀ row xs ys, xs ⊆ ys → transfer row xs ⊆ transfer row ys)
    (hnodup : ∀ row xs, xs.Nodup → (transfer row xs).Nodup) {C : Array (List α)}
    (hpost : PostFix code transfer C) (fuel : Nat) {bs : Array (List α)}
    (happrox : Approx code transfer C bs) (hfuel : weight code C < weight code bs + fuel) :
    Approx code transfer C (fixpoint.go code transfer fuel bs) ∧
      PostFix code transfer (fixpoint.go code transfer fuel bs) := by
  induction fuel generalizing bs with
  | zero =>
    have := weight_le_of_approx happrox
    omega
  | succ fuel ih =>
    have hstart : SweepAcc code transfer C bs (bs, false) :=
      ⟨happrox, le_refl _, fun h => (by cases h), fun _ => rfl⟩
    obtain ⟨hres, hresSame⟩ := sweepFold_spec hmono hnodup hpost
      (List.range code.length).reverse hstart
    rw [fixpoint.go, sweep_eq_foldl]
    generalize hsweep : (List.range code.length).reverse.foldl (sweepStep code transfer)
      (bs, false) = res at hres hresSame
    obtain ⟨bs', ch⟩ := res
    cases ch
    · obtain ⟨-, hall⟩ := hresSame rfl
      have hbs' : bs' = bs := hres.same rfl
      subst hbs'
      refine ⟨hres.approx, fun r row hrow => hall r ?_ row hrow⟩
      rw [List.mem_reverse, List.mem_range]
      exact (List.getElem?_eq_some_iff.mp hrow).1
    · have hgrown : weight code bs + 1 ≤ weight code bs' := hres.grown rfl
      exact ih hres.approx (by omega)

/-- **The liveness iteration against a certificate.** For a monotone, duplicate-free transfer and
a post-fixpoint certificate `C` of total size below the fuel, the iteration ends below `C` at a
post-fixpoint. -/
theorem fixpoint_spec (hmono : ∀ row xs ys, xs ⊆ ys → transfer row xs ⊆ transfer row ys)
    (hnodup : ∀ row xs, xs.Nodup → (transfer row xs).Nodup) {C : Array (List α)}
    (hpost : PostFix code transfer C) {fuel : Nat} (hfuel : weight code C < fuel) :
    Approx code transfer C (fixpoint code transfer fuel) ∧
      PostFix code transfer (fixpoint code transfer fuel) := by
  have hzero : weight code (Array.replicate code.length ([] : List α)) = 0 := by
    unfold weight
    apply Finset.sum_eq_zero
    intro r _
    simp [Array.getElem?_replicate]
    split <;> rfl
  have happrox : Approx code transfer C (Array.replicate code.length ([] : List α)) := by
    refine ⟨by simp, fun r => ?_, fun r row _ => ?_, fun r => ?_⟩ <;>
      simp [Array.getElem?_replicate] <;> split <;> simp
  exact fixpoint_go_spec hmono hnodup hpost fuel happrox (by omega)

end GaussSeidel

/-! ## The distance transfer is monotone and duplicate-free -/

section TransferShape

theorem mem_foldl_iff {α β : Type} (step : List β → α → List β) (g : α → Option β)
    (hstep : ∀ acc p y, y ∈ step acc p ↔ y ∈ acc ∨ g p = some y) (L : List α) (acc : List β)
    (y : β) : y ∈ L.foldl step acc ↔ y ∈ acc ∨ ∃ p ∈ L, g p = some y := by
  induction L generalizing acc with
  | nil => simp
  | cons p L ih =>
    rw [List.foldl_cons, ih, hstep]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem foldl_nodup {α β : Type} (step : List β → α → List β)
    (hstep : ∀ acc p, acc.Nodup → (step acc p).Nodup) (L : List α) (acc : List β)
    (hacc : acc.Nodup) : (L.foldl step acc).Nodup := by
  induction L generalizing acc with
  | nil => exact hacc
  | cons p L ih => exact ih _ (hstep acc p hacc)

theorem copyStep_mem (names : List String) (target source : String) (acc : List Pair) (p y : Pair) :
    y ∈ (match pairOf names (substHead target source p.1) (substHead target source p.2) with
      | some q => union acc [q]
      | none => acc) ↔
      y ∈ acc ∨ pairOf names (substHead target source p.1) (substHead target source p.2) = some y := by
  split
  · rename_i q hq
    rw [mem_union, List.mem_singleton, hq, Option.some.injEq]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr h.symm
  · rename_i hq
    rw [hq]
    simp

theorem mem_transfer_copy_iff {names : List String} {target source : String} {targets : List Nat}
    {succ : List Pair} {y : Pair} :
    y ∈ distanceTransfer names ⟨.copy target source, targets⟩ succ ↔
      ∃ q ∈ succ, pairOf names (substHead target source q.1) (substHead target source q.2) =
        some y := by
  show y ∈ succ.foldl (fun acc p =>
    match pairOf names (substHead target source p.1) (substHead target source p.2) with
    | some q => union acc [q]
    | none => acc) [] ↔ _
  rw [mem_foldl_iff _ (fun p : Pair => pairOf names (substHead target source p.1)
    (substHead target source p.2)) (copyStep_mem names target source)]
  simp

theorem transfer_nodup (names : List String) (row : Row) (succ : List Pair) (hsucc : succ.Nodup) :
    (distanceTransfer names row succ).Nodup := by
  obtain ⟨event, targets⟩ := row
  cases event
  case copy target source =>
    show (succ.foldl (fun acc p =>
      match pairOf names (substHead target source p.1) (substHead target source p.2) with
      | some q => union acc [q]
      | none => acc) []).Nodup
    refine foldl_nodup _ (fun acc p hacc => ?_) succ [] List.nodup_nil
    split
    · exact union_nodup _ _ hacc
    · exact hacc
  case less l r | equal l r | assertEqual l r =>
    show (match pairOf names l r with | some q => union succ [q] | none => succ).Nodup
    split
    · exact union_nodup _ _ hsucc
    · exact hsucc
  all_goals exact hsucc

theorem transfer_mono (names : List String) (row : Row) (xs ys : List Pair) (hsub : xs ⊆ ys) :
    distanceTransfer names row xs ⊆ distanceTransfer names row ys := by
  obtain ⟨event, targets⟩ := row
  cases event
  case copy target source =>
    intro y hy
    obtain ⟨q, hq, hpair⟩ := mem_transfer_copy_iff.mp hy
    exact mem_transfer_copy_iff.mpr ⟨q, hsub hq, hpair⟩
  case less l r | equal l r | assertEqual l r =>
    show (match pairOf names l r with | some q => union xs [q] | none => xs) ⊆
      (match pairOf names l r with | some q => union ys [q] | none => ys)
    split
    · intro y hy
      rw [mem_union] at hy ⊢
      exact hy.imp_left (hsub ·)
    · exact hsub
  all_goals exact hsub

end TransferShape

end PalPeg.ScaWorkerRegs
