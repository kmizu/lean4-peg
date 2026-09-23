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

**Table facts.** The generic proofs use ten facts about the ROM (`TableFacts`): targets and
start in range, every pair live after a row has a colour below `registers`, colours are
injective on each after-set, after-sets hold canonical pairs, the liveness transfer of a row is
contained in its before-set, target-less rows have nothing live, and the start mappings cover
the start's live set with distinct colours. Running `liveDistances` in the kernel is too costly
(string comparisons inside the Gauss–Seidel iteration: > 5 GB), so the facts come from a
certificate of live pairs on head indices: `fixpoint_spec` shows the iteration stays below any
post-fixpoint certificate and stops at a post-fixpoint, and `tableFacts_of_certificate` turns the
Boolean checks `globalCheck` / `rowsCheck` into `TableFacts`. For `matcherWorker` and
`flagsWorker` the checks are evaluated by `decide +kernel` (`matcher_tableFacts`,
`flags_tableFacts`).
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
  afterColored : ∀ (r : Nat) (row : Row), spec.program.code[r]? = some row →
    ∀ p ∈ afterAt spec row, ColorOk spec p
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
    regUpdateAt spec db ⟨event, targets⟩ i =
      { source := some i, reverse := false, delta := 0 } := by
  cases event with
  | move moves => exact absurd rfl (hnotMove moves)
  | copy t s => exact absurd rfl (hnotCopy t s)
  | _ => rfl

theorem headStep_other {event : Event} (pos : String → Int)
    (hnotMove : ∀ moves, event ≠ .move moves)
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
        (if decided then (fieldsAt spec rb db r row).yes
          else (fieldsAt spec rb db r row).no) = r) := by
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
      y ∈ acc ∨
        pairOf names (substHead target source p.1) (substHead target source p.2) = some y := by
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

/-! ## A certificate for the liveness tables

The kernel cannot afford to run `liveDistances` on the real programs (string comparisons inside a
Gauss–Seidel iteration). Instead a certificate `CN` lists the live pairs of every row as pairs of
head indices (positions in `names`), and `rowCheck` / `globalCheck` verify, on indices, that its
decoding is a post-fixpoint with the colour and range facts. `fixpoint_spec` then puts
`liveDistances` below the certificate. -/

section Certificate

variable (names : List String)

/-- The head with index `i`. -/
def headName (i : Nat) : String := names.getD i ""

/-- The pair with index pair `q`. -/
def pairName (q : Nat × Nat) : Pair := (headName names q.1, headName names q.2)

/-- `pairOf` on indices. -/
def pairOfN (i j : Nat) : Option (Nat × Nat) :=
  if i = j then none else if i < j then some (i, j) else some (j, i)

/-- `substHead` on indices. -/
def substN (target source i : Nat) : Nat := if i = target then source else i

/-- The decoded certificate table. -/
def certTable (CN : List (List (Nat × Nat))) : Array (List Pair) :=
  (CN.map fun l => l.map (pairName names)).toArray

variable {names}

theorem headName_idxOf {h : String} (hmem : h ∈ names) : headName names (names.idxOf h) = h := by
  unfold headName
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem),
    Option.getD_some]
  exact List.getElem_idxOf _

theorem idxOf_headName (hnodup : names.Nodup) {i : Nat} (hi : i < names.length) :
    names.idxOf (headName names i) = i := by
  unfold headName
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.Nodup.idxOf_getElem hnodup i hi

theorem headName_inj (hnodup : names.Nodup) {i j : Nat} (hi : i < names.length)
    (hj : j < names.length) : headName names i = headName names j ↔ i = j :=
  ⟨fun h => by rw [← idxOf_headName hnodup hi, h, idxOf_headName hnodup hj], fun h => h ▸ rfl⟩

theorem pairName_inj (hnodup : names.Nodup) {q q' : Nat × Nat}
    (hq : q.1 < names.length ∧ q.2 < names.length)
    (hq' : q'.1 < names.length ∧ q'.2 < names.length) :
    pairName names q = pairName names q' ↔ q = q' := by
  unfold pairName
  rw [Prod.mk.injEq, headName_inj hnodup hq.1 hq'.1, headName_inj hnodup hq.2 hq'.2]
  exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

theorem pairOf_headName (hnodup : names.Nodup) {i j : Nat} (hi : i < names.length)
    (hj : j < names.length) :
    pairOf names (headName names i) (headName names j) = (pairOfN i j).map (pairName names) := by
  unfold pairOf pairOfN
  rw [idxOf_headName hnodup hi, idxOf_headName hnodup hj]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (mt (headName_inj hnodup hi hj).mp hij), if_neg hij]
    split <;> rfl

theorem substHead_headName (hnodup : names.Nodup) {target source : String}
    (htarget : target ∈ names) (hsource : source ∈ names) {i : Nat} (hi : i < names.length) :
    substHead target source (headName names i) =
      headName names (substN (names.idxOf target) (names.idxOf source) i) := by
  unfold substHead substN
  by_cases hit : i = names.idxOf target
  · rw [if_pos hit, if_pos (by rw [hit, headName_idxOf htarget]), headName_idxOf hsource]
  · rw [if_neg hit, if_neg fun h => hit (by rw [← h, idxOf_headName hnodup hi])]

theorem substN_lt {target source : String} (hsource : source ∈ names) {i : Nat}
    (hi : i < names.length) :
    substN (names.idxOf target) (names.idxOf source) i < names.length := by
  unfold substN
  split
  · exact List.idxOf_lt_length_of_mem hsource
  · exact hi

theorem lookupFirst_pairName (hnodup : names.Nodup) (colorsN : List ((Nat × Nat) × Nat))
    (hcolorsRange : ∀ e ∈ colorsN, e.1.1 < names.length ∧ e.1.2 < names.length)
    {q : Nat × Nat} (hq : q.1 < names.length ∧ q.2 < names.length) :
    lookupFirst (pairName names q) (colorsN.map fun e => (pairName names e.1, e.2)) =
      lookupFirst q colorsN := by
  induction colorsN with
  | nil => rfl
  | cons e rest ih =>
    have hkey : pairName names e.1 = pairName names q ↔ e.1 = q :=
      pairName_inj hnodup (hcolorsRange e (List.mem_cons_self ..)) hq
    have ihRest := ih fun e' he' => hcolorsRange e' (List.mem_cons_of_mem _ he')
    unfold lookupFirst at ihRest ⊢
    rw [List.map_cons, List.find?_cons, List.find?_cons]
    by_cases hkeyEq : e.1 = q
    · simp [hkeyEq]
    · have hnameNe : ¬ pairName names e.1 = pairName names q := fun h => hkeyEq (hkey.mp h)
      simp only [hnameNe, hkeyEq, decide_false]
      exact ihRest

theorem certTable_getD (CN : List (List (Nat × Nat))) (r : Nat) :
    (certTable names CN).getD r [] = (CN.getD r []).map (pairName names) := by
  unfold certTable
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getD_eq_getElem?_getD]
  cases CN[r]? <;> rfl

theorem mem_getD_of_mem {β : Type} {CN : List (List β)} {r : Nat} {q : β}
    (hq : q ∈ CN.getD r []) : ∃ l ∈ CN, q ∈ l := by
  rw [List.getD_eq_getElem?_getD] at hq
  cases hr : CN[r]? with
  | none => rw [hr] at hq; simp at hq
  | some l =>
    rw [hr, Option.getD_some] at hq
    exact ⟨l, List.mem_of_getElem? hr, hq⟩

theorem sum_range_getD_length {β : Type} (L : List (List β)) :
    ∑ r ∈ Finset.range L.length, (L.getD r []).length = (L.map List.length).sum := by
  induction L with
  | nil => simp
  | cons l L ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]
    omega

end Certificate

/-- The heads a row names in a copy or a comparison. -/
def eventHeads : Event → List String
  | .copy target source => [target, source]
  | .less a b | .equal a b | .assertEqual a b => [a, b]
  | _ => []

/-- The two heads of a comparison row. -/
def compareHeads : Event → Option (String × String)
  | .less a b | .equal a b | .assertEqual a b => some (a, b)
  | _ => none

theorem mem_transfer_inv {names : List String} {event : Event} {targets : List Nat}
    (hnotCopy : ∀ t s, event ≠ .copy t s) {succ : List Pair} {y : Pair}
    (hy : y ∈ distanceTransfer names ⟨event, targets⟩ succ) :
    y ∈ succ ∨ ∃ a b, compareHeads event = some (a, b) ∧ pairOf names a b = some y := by
  cases event with
  | copy t s => exact absurd rfl (hnotCopy t s)
  | less a b | equal a b | assertEqual a b =>
    change y ∈ (match pairOf names a b with | some q => union succ [q] | none => succ) at hy
    split at hy
    · rename_i q hq
      rcases (mem_union _ _ _).mp hy with h | h
      · exact Or.inl h
      · exact Or.inr ⟨a, b, rfl, by rw [hq, List.mem_singleton.mp h]⟩
    · exact Or.inl hy
  | _ => exact Or.inl hy

/-- The pair a row keeps live for a successor pair `q`, on indices: a copy's substitution
image, `q` itself otherwise. -/
def imageN (names : List String) (event : Event) (q : Nat × Nat) : Option (Nat × Nat) :=
  match event with
  | .copy target source =>
    pairOfN (substN (names.idxOf target) (names.idxOf source) q.1)
      (substN (names.idxOf target) (names.idxOf source) q.2)
  | _ => some q

/-- The pair a comparison row makes live, on indices. -/
def comparePairN (names : List String) (event : Event) : Option (Nat × Nat) :=
  match compareHeads event with
  | some (a, b) => pairOfN (names.idxOf a) (names.idxOf b)
  | none => none

/-- The optional pair is in `before`. -/
def optMem (y : Option (Nat × Nat)) (before : List (Nat × Nat)) : Bool :=
  match y with
  | some p => decide (p ∈ before)
  | none => true

/-- `p` has a colour below `registers` (on `String` pairs). -/
def colorOk (spec : WorkerSpec) (p : Pair) : Bool :=
  match lookupFirst p spec.distances.colors with
  | some i => decide (i < spec.distances.registers)
  | none => false

theorem colorOk_iff {spec : WorkerSpec} {p : Pair} : colorOk spec p = true ↔ ColorOk spec p := by
  unfold colorOk ColorOk
  split <;> simp_all

/-- The facts of one row, on the index certificate. -/
def rowCheck (spec : WorkerSpec) (colorsN : List ((Nat × Nat) × Nat))
    (CN : List (List (Nat × Nat))) (r : Nat) (row : Row) : Bool :=
  let before := CN.getD r []
  let succs := row.targets.flatMap fun t => CN.getD t []
  let colored := succs.map fun q => (q, lookupFirst q colorsN)
  row.targets.all (fun t => decide (t < spec.program.code.length)) &&
  (eventHeads row.event).all (fun h => decide (h ∈ spec.names)) &&
  colored.all (fun c => match c.2 with
    | some i => decide (i < spec.distances.registers)
    | none => false) &&
  colored.all (fun c => colored.all fun c' => !decide (c.2 = c'.2) || decide (c.1 = c'.1)) &&
  succs.all (fun q => optMem (imageN spec.names row.event q) before) &&
  optMem (comparePairN spec.names row.event) before &&
  (!row.targets.isEmpty || before.isEmpty)

/-- `rowCheck` on the rows `lo, …, lo + n - 1` (split so that the kernel checks it in pieces). -/
def rowsCheck (spec : WorkerSpec) (colorsN : List ((Nat × Nat) × Nat))
    (CN : List (List (Nat × Nat))) (lo n : Nat) : Bool :=
  (List.range' lo n).all fun r =>
    match spec.program.code[r]? with
    | some row => rowCheck spec colorsN CN r row
    | none => true

theorem rowsCheck_append (spec : WorkerSpec) (colorsN : List ((Nat × Nat) × Nat))
    (CN : List (List (Nat × Nat))) (lo a b : Nat) :
    rowsCheck spec colorsN CN lo (a + b) =
      (rowsCheck spec colorsN CN lo a && rowsCheck spec colorsN CN (lo + a) b) := by
  unfold rowsCheck
  rw [← List.all_append]
  congr 1
  simp

/-- The global facts: names, colours, ranges, sizes, and the `start` mapping. -/
def globalCheck (spec : WorkerSpec) (colorsN : List ((Nat × Nat) × Nat))
    (CN : List (List (Nat × Nat))) : Bool :=
  decide spec.names.Nodup &&
  decide (spec.distances.colors = colorsN.map fun e => (pairName spec.names e.1, e.2)) &&
  colorsN.all (fun e => decide (e.1.1 < spec.names.length) && decide (e.1.2 < spec.names.length)) &&
  CN.all (fun l => l.all fun q => decide (q.1 < q.2) && decide (q.2 < spec.names.length)) &&
  decide (CN.length = spec.program.code.length) &&
  decide ((CN.map List.length).sum <
    spec.program.code.length * spec.names.length * spec.names.length + 1) &&
  decide (spec.program.start < spec.program.code.length) &&
  (CN.getD spec.program.start []).all (fun q =>
    (startMapping spec).any fun e => decide (e.1 = pairName spec.names q)) &&
  decide (((startMapping spec).map fun e => lookupFirst e.1 spec.distances.colors).Nodup) &&
  (startMapping spec).all (fun e => colorOk spec e.1)

/-! ## The certificate checks give the table facts -/

section CertificateSound

variable {spec : WorkerSpec} {colorsN : List ((Nat × Nat) × Nat)} {CN : List (List (Nat × Nat))}

/-- `globalCheck`, unpacked. -/
structure GlobalFacts (spec : WorkerSpec) (colorsN : List ((Nat × Nat) × Nat))
    (CN : List (List (Nat × Nat))) : Prop where
  namesNodup : spec.names.Nodup
  colorsEq : spec.distances.colors = colorsN.map fun e => (pairName spec.names e.1, e.2)
  colorsRange : ∀ e ∈ colorsN, e.1.1 < spec.names.length ∧ e.1.2 < spec.names.length
  certRange : ∀ l ∈ CN, ∀ q ∈ l, q.1 < q.2 ∧ q.2 < spec.names.length
  certLength : CN.length = spec.program.code.length
  certWeight : (CN.map List.length).sum <
    spec.program.code.length * spec.names.length * spec.names.length + 1
  startInRange : spec.program.start < spec.program.code.length
  startMapped : ∀ q ∈ CN.getD spec.program.start [],
    ∃ e ∈ startMapping spec, e.1 = pairName spec.names q
  startColorsNodup :
    ((startMapping spec).map fun e => lookupFirst e.1 spec.distances.colors).Nodup
  startColored : ∀ e ∈ startMapping spec, colorOk spec e.1 = true

theorem globalFacts_of_check (hcheck : globalCheck spec colorsN CN = true) :
    GlobalFacts spec colorsN CN := by
  simp only [globalCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true] at hcheck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hnodup, hcolorsEq⟩, hcolorsRange⟩, hcertRange⟩, hcertLength⟩, hcertWeight⟩,
    hstart⟩, hstartMapped⟩, hstartNodup⟩, hstartColored⟩ := hcheck
  exact ⟨hnodup, hcolorsEq, hcolorsRange, hcertRange, hcertLength, hcertWeight, hstart,
    hstartMapped, hstartNodup, hstartColored⟩

/-- `rowCheck`, unpacked. -/
structure RowFacts (spec : WorkerSpec) (colorsN : List ((Nat × Nat) × Nat))
    (CN : List (List (Nat × Nat))) (r : Nat) (row : Row) : Prop where
  targetsInRange : ∀ t ∈ row.targets, t < spec.program.code.length
  headsKnown : ∀ h ∈ eventHeads row.event, h ∈ spec.names
  colored : ∀ t ∈ row.targets, ∀ q ∈ CN.getD t [],
    ∃ i, lookupFirst q colorsN = some i ∧ i < spec.distances.registers
  injective : ∀ t ∈ row.targets, ∀ q ∈ CN.getD t [], ∀ t' ∈ row.targets, ∀ q' ∈ CN.getD t' [],
    lookupFirst q colorsN = lookupFirst q' colorsN → q = q'
  image : ∀ t ∈ row.targets, ∀ q ∈ CN.getD t [], ∀ y,
    imageN spec.names row.event q = some y → y ∈ CN.getD r []
  compare : ∀ y, comparePairN spec.names row.event = some y → y ∈ CN.getD r []
  targetless : row.targets = [] → CN.getD r [] = []

theorem optMem_iff {y : Option (Nat × Nat)} {before : List (Nat × Nat)} :
    optMem y before = true ↔ ∀ p, y = some p → p ∈ before := by
  cases y <;> simp [optMem]

theorem rowFacts_of_check {r : Nat} {row : Row} (hcheck : rowCheck spec colorsN CN r row = true) :
    RowFacts spec colorsN CN r row := by
  simp only [rowCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨⟨⟨⟨htargets, hheads⟩, hcolored⟩, hinjective⟩, himage⟩, hcompare⟩, htargetless⟩ :=
    hcheck
  have hsucc : ∀ {t q}, t ∈ row.targets → q ∈ CN.getD t [] →
      q ∈ row.targets.flatMap fun t => CN.getD t [] :=
    fun ht hq => List.mem_flatMap.mpr ⟨_, ht, hq⟩
  refine ⟨htargets, hheads, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht q hq
    have hq' := hcolored _ (List.mem_map_of_mem (f := fun q => (q, lookupFirst q colorsN))
      (hsucc ht hq))
    revert hq'
    cases lookupFirst q colorsN <;> simp
  · intro t ht q hq t' ht' q' hq' hcolorEq
    have hpair := hinjective _ (List.mem_map_of_mem (f := fun q => (q, lookupFirst q colorsN))
      (hsucc ht hq)) _ (List.mem_map_of_mem (f := fun q => (q, lookupFirst q colorsN))
      (hsucc ht' hq'))
    simpa [hcolorEq] using hpair
  · intro t ht q hq y hy
    exact optMem_iff.mp (himage q (hsucc ht hq)) y hy
  · intro y hy
    exact optMem_iff.mp hcompare y hy
  · intro hnil
    rw [hnil] at htargetless
    simpa using htargetless

theorem imageN_of_not_copy {names : List String} {event : Event}
    (hnotCopy : ∀ t s, event ≠ .copy t s) (q : Nat × Nat) : imageN names event q = some q := by
  cases event with
  | copy t s => exact absurd rfl (hnotCopy t s)
  | _ => rfl

theorem compareHeads_mem {event : Event} {a b : String}
    (hcompare : compareHeads event = some (a, b)) :
    a ∈ eventHeads event ∧ b ∈ eventHeads event := by
  cases event <;> simp only [compareHeads, reduceCtorEq, Option.some.injEq, Prod.mk.injEq]
    at hcompare <;> obtain ⟨rfl, rfl⟩ := hcompare <;> simp [eventHeads]

theorem pairOf_eq_map {names : List String} (hnodup : names.Nodup) {a b : String}
    (ha : a ∈ names) (hb : b ∈ names) :
    pairOf names a b = (pairOfN (names.idxOf a) (names.idxOf b)).map (pairName names) := by
  have hpair := pairOf_headName hnodup (List.idxOf_lt_length_of_mem ha)
    (List.idxOf_lt_length_of_mem hb)
  rwa [headName_idxOf ha, headName_idxOf hb] at hpair

/-- The decoded certificate is a post-fixpoint of the liveness transfer. -/
theorem postFix_certTable (hglobal : GlobalFacts spec colorsN CN)
    (hrows : ∀ (r : Nat) (row : Row), spec.program.code[r]? = some row →
      RowFacts spec colorsN CN r row) :
    PostFix spec.program.code (distanceTransfer spec.names) (certTable spec.names CN) := by
  intro r row hrow y hy
  have hrowFacts := hrows r row hrow
  have hsucc : ∀ {p : Pair}, p ∈ successorsUnion (certTable spec.names CN) row.targets →
      ∃ t ∈ row.targets, ∃ q ∈ CN.getD t [], pairName spec.names q = p := by
    intro p hp
    obtain ⟨t, ht, hpt⟩ := (mem_successorsUnion _ _ _).mp hp
    rw [certTable_getD, List.mem_map] at hpt
    obtain ⟨q, hq, rfl⟩ := hpt
    exact ⟨t, ht, q, hq, rfl⟩
  have hrange : ∀ {t : Nat} {q : Nat × Nat}, q ∈ CN.getD t [] →
      q.1 < q.2 ∧ q.2 < spec.names.length := fun hq => by
    obtain ⟨l, hl, hql⟩ := mem_getD_of_mem hq
    exact hglobal.certRange l hl _ hql
  rw [certTable_getD, List.mem_map]
  unfold recompute at hy
  obtain ⟨event, targets⟩ := row
  by_cases hcopy : ∃ t s, event = .copy t s
  · obtain ⟨target, source, rfl⟩ := hcopy
    obtain ⟨p, hp, hpair⟩ := mem_transfer_copy_iff.mp hy
    obtain ⟨t, ht, q, hq, rfl⟩ := hsucc hp
    have hqRange := hrange hq
    have htarget : target ∈ spec.names := hrowFacts.headsKnown target (by simp [eventHeads])
    have hsource : source ∈ spec.names := hrowFacts.headsKnown source (by simp [eventHeads])
    have hfirst : q.1 < spec.names.length := by omega
    have hpair' : pairOf spec.names (substHead target source (headName spec.names q.1))
        (substHead target source (headName spec.names q.2)) = some y := hpair
    rw [substHead_headName hglobal.namesNodup htarget hsource hfirst,
      substHead_headName hglobal.namesNodup htarget hsource hqRange.2,
      pairOf_headName hglobal.namesNodup (substN_lt hsource hfirst)
        (substN_lt hsource hqRange.2)] at hpair'
    obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.mp hpair'
    exact ⟨y₀, hrowFacts.image t ht q hq y₀ hy₀, rfl⟩
  · have hnotCopy : ∀ t s, event ≠ .copy t s := fun t s h => hcopy ⟨t, s, h⟩
    rcases mem_transfer_inv hnotCopy hy with hy | ⟨a, b, hab, hpair⟩
    · obtain ⟨t, ht, q, hq, rfl⟩ := hsucc hy
      exact ⟨q, hrowFacts.image t ht q hq q (imageN_of_not_copy hnotCopy q), rfl⟩
    · obtain ⟨haHeads, hbHeads⟩ := compareHeads_mem hab
      rw [pairOf_eq_map hglobal.namesNodup (hrowFacts.headsKnown a haHeads)
        (hrowFacts.headsKnown b hbHeads)] at hpair
      obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.mp hpair
      refine ⟨y₀, hrowFacts.compare y₀ ?_, rfl⟩
      unfold comparePairN
      rw [hab]
      exact hy₀

theorem weight_certTable (code : List Row) (names : List String)
    (hlength : CN.length = code.length) :
    weight code (certTable names CN) = (CN.map List.length).sum := by
  unfold weight
  simp only [certTable_getD, List.length_map]
  rw [← hlength]
  exact sum_range_getD_length CN

/-- **The certificate checks give the table facts.** -/
theorem tableFacts_of_certificate (hglobalCheck : globalCheck spec colorsN CN = true)
    (hrowsCheck : rowsCheck spec colorsN CN 0 spec.program.code.length = true) :
    TableFacts spec := by
  have hglobal := globalFacts_of_check hglobalCheck
  have hrows : ∀ (r : Nat) (row : Row), spec.program.code[r]? = some row →
      RowFacts spec colorsN CN r row := by
    intro r row hrow
    have hrlt : r < spec.program.code.length := (List.getElem?_eq_some_iff.mp hrow).1
    unfold rowsCheck at hrowsCheck
    rw [List.all_eq_true] at hrowsCheck
    have hr := hrowsCheck r (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
    rw [hrow] at hr
    exact rowFacts_of_check hr
  obtain ⟨happrox, hpostLive⟩ := fixpoint_spec (code := spec.program.code)
    (transfer := distanceTransfer spec.names) (transfer_mono spec.names)
    (transfer_nodup spec.names) (postFix_certTable hglobal hrows)
    (fuel := spec.program.code.length * spec.names.length * spec.names.length + 1)
    (by rw [weight_certTable _ _ hglobal.certLength]; exact hglobal.certWeight)
  have hrange : ∀ {t : Nat} {q : Nat × Nat}, q ∈ CN.getD t [] →
      q.1 < q.2 ∧ q.2 < spec.names.length := fun hq => by
    obtain ⟨l, hl, hql⟩ := mem_getD_of_mem hq
    exact hglobal.certRange l hl _ hql
  have hbelow : ∀ (t : Nat) {p : Pair}, p ∈ liveAt spec t →
      ∃ q ∈ CN.getD t [], pairName spec.names q = p := by
    intro t p hp
    have hpC := happrox.below t hp
    rw [certTable_getD, List.mem_map] at hpC
    exact hpC
  have hafter : ∀ (row : Row) {p : Pair}, p ∈ afterAt spec row →
      ∃ t ∈ row.targets, ∃ q ∈ CN.getD t [], pairName spec.names q = p := by
    intro row p hp
    obtain ⟨t, ht, hpt⟩ := (mem_successorsUnion _ _ _).mp hp
    exact ⟨t, ht, hbelow t hpt⟩
  have hlookup : ∀ {t : Nat} {q : Nat × Nat}, q ∈ CN.getD t [] →
      lookupFirst (pairName spec.names q) spec.distances.colors = lookupFirst q colorsN := by
    intro t q hq
    have hqRange := hrange hq
    rw [hglobal.colorsEq]
    exact lookupFirst_pairName hglobal.namesNodup colorsN hglobal.colorsRange
      ⟨by omega, hqRange.2⟩
  refine
    { startInRange := hglobal.startInRange
      targetsInRange := fun r row hrow => (hrows r row hrow).targetsInRange
      afterColored := ?_
      afterColorsInjective := ?_
      afterCanonical := ?_
      transferLive := fun r row hrow p hp => hpostLive r row hrow hp
      targetlessDead := ?_
      startLiveMapped := ?_
      startColorsNodup := hglobal.startColorsNodup
      startColored := fun e he => colorOk_iff.mp (hglobal.startColored e he) }
  · intro r row hrow p hp
    obtain ⟨t, ht, q, hq, rfl⟩ := hafter row hp
    obtain ⟨i, hi, hlt⟩ := (hrows r row hrow).colored t ht q hq
    exact ⟨i, (hlookup hq).trans hi, hlt⟩
  · intro r row hrow p hp p' hp' hcolorEq
    obtain ⟨t, ht, q, hq, rfl⟩ := hafter row hp
    obtain ⟨t', ht', q', hq', rfl⟩ := hafter row hp'
    rw [hlookup hq, hlookup hq'] at hcolorEq
    rw [(hrows r row hrow).injective t ht q hq t' ht' q' hq' hcolorEq]
  · intro r row hrow p hp
    obtain ⟨t, ht, q, hq, rfl⟩ := hafter row hp
    have hqRange := hrange hq
    have hpairN : pairOfN q.1 q.2 = some q := by
      unfold pairOfN
      rw [if_neg (by omega), if_pos hqRange.1]
    show pairOf spec.names (headName spec.names q.1) (headName spec.names q.2) = _
    rw [pairOf_headName hglobal.namesNodup (by omega) hqRange.2, hpairN]
    rfl
  · intro r row hrow hnil
    have hcert := (hrows r row hrow).targetless hnil
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro p hp
    obtain ⟨q, hq, -⟩ := hbelow r hp
    rw [hcert] at hq
    simp at hq
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := hbelow _ hp
    obtain ⟨e, he, hkey⟩ := hglobal.startMapped q hq
    exact ⟨e.2, by rw [← hkey]; exact he⟩

end CertificateSound

/-! ## The concrete workers

The certificates were generated by evaluating `liveDistances` on the two workers and writing each
pair as head indices (`names.idxOf`); they are trusted only through `globalCheck` / `rowsCheck`,
which the kernel evaluates below (in pieces of 50 rows). -/

section Concrete

open PalPeg.ScaGsTables

set_option maxRecDepth 100000

theorem rowsCheck_split {spec : WorkerSpec} {colorsN : List ((Nat × Nat) × Nat)}
    {CN : List (List (Nat × Nat))} (lo a b : Nat)
    (hfirst : rowsCheck spec colorsN CN lo a = true)
    (hrest : rowsCheck spec colorsN CN (lo + a) b = true) :
    rowsCheck spec colorsN CN lo (a + b) = true := by
  rw [rowsCheck_append, hfirst, hrest]
  rfl

/-- The matcher's live pairs by row, as head-index pairs (generated from `liveDistances`). -/
def matcherLive : List (List (Nat × Nat)) := [
  /- 0 -/ [],
  /- 1 -/ [(0, 4)],
  /- 2 -/ [(0, 2)],
  /- 3 -/ [(0, 3), (2, 3)],
  /- 4 -/ [(0, 3), (2, 3), (3, 5)],
  /- 5 -/ [(0, 3), (2, 3), (3, 5), (3, 7), (2, 7)],
  /- 6 -/ [(0, 3), (2, 3), (3, 5), (3, 7), (2, 7)],
  /- 7 -/ [(0, 3), (2, 3), (3, 5), (3, 7), (3, 6), (2, 6), (2, 7)],
  /- 8 -/ [(0, 3), (2, 3), (3, 5), (3, 7), (2, 7), (7, 11), (3, 6), (2, 6), (6, 11)],
  /- 9 -/ [(0, 3), (2, 3), (3, 5), (3, 7), (2, 7), (7, 11), (3, 6), (2, 6), (6, 11)],
  /- 10 -/ [(0, 3), (2, 3)],
  /- 11 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11), (3, 6), (2, 6), (6, 11)],
  /- 12 -/ [(0, 3), (2, 3)],
  /- 13 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11), (3, 6), (2, 6), (6, 11)],
  /- 14 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11), (3, 6), (2, 6), (6, 11)],
  /- 15 -/ [(0, 3), (2, 3)],
  /- 16 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 17 -/ [(3, 7), (3, 6), (0, 3), (2, 3), (2, 6)],
  /- 18 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11), (3, 6), (2, 6), (6, 11)],
  /- 19 -/ [(3, 5), (0, 3), (2, 5)],
  /- 20 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 21 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 22 -/ [(3, 8), (3, 6), (0, 3), (2, 3), (2, 6)],
  /- 23 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11), (3, 6), (2, 6), (6, 11)],
  /- 24 -/ [(3, 5), (0, 3), (2, 5)],
  /- 25 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 26 -/ [(0, 3), (2, 3), (3, 5), (3, 7), (2, 7), (7, 11)],
  /- 27 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 28 -/ [(0, 3), (2, 3), (3, 5), (3, 7), (2, 7), (7, 11)],
  /- 29 -/ [(3, 8), (3, 6), (3, 12), (0, 3), (2, 3), (2, 6)],
  /- 30 -/ [(3, 5), (0, 3), (2, 5), (3, 10)],
  /- 31 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 32 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 33 -/ [(3, 8), (3, 6), (3, 12), (0, 3), (2, 3)],
  /- 34 -/ [(3, 8), (3, 6), (3, 12), (0, 3), (2, 3), (2, 6)],
  /- 35 -/ [(3, 5), (0, 3), (2, 5)],
  /- 36 -/ [(3, 5), (0, 3), (2, 5), (3, 10)],
  /- 37 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 38 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 39 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3)],
  /- 40 -/ [(3, 8), (3, 6), (3, 12), (0, 3), (2, 3), (2, 6)],
  /- 41 -/ [(3, 5), (3, 10), (2, 5), (0, 3)],
  /- 42 -/ [(3, 5), (0, 3), (2, 5), (3, 10)],
  /- 43 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 44 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 45 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12)],
  /- 46 -/ [(3, 5), (3, 10), (2, 5), (0, 3)],
  /- 47 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 48 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 49 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12), (3, 7),
      (7, 9), (2, 7)],
  /- 50 -/ [(3, 5), (0, 3), (2, 5), (3, 10)],
  /- 51 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 52 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 53 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12), (3, 7),
      (7, 9), (2, 7)],
  /- 54 -/ [(3, 5), (0, 3), (2, 5)],
  /- 55 -/ [(3, 5), (3, 10), (2, 5), (0, 3)],
  /- 56 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 57 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 58 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12), (3, 7),
      (3, 6), (6, 9), (2, 6), (2, 7), (7, 9)],
  /- 59 -/ [(3, 5), (0, 3), (2, 5)],
  /- 60 -/ [(3, 5), (0, 3), (2, 5)],
  /- 61 -/ [(3, 5), (3, 10), (2, 5), (0, 3)],
  /- 62 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 63 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 64 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12), (3, 7),
      (6, 11), (6, 9), (2, 6), (2, 7), (7, 11), (7, 9)],
  /- 65 -/ [(3, 5), (0, 3), (2, 5)],
  /- 66 -/ [(3, 5), (0, 3), (2, 5)],
  /- 67 -/ [(3, 5), (0, 3), (2, 5)],
  /- 68 -/ [(3, 5), (3, 10), (2, 5), (0, 3)],
  /- 69 -/ [(3, 5), (2, 5), (0, 3), (3, 10)],
  /- 70 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 71 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 72 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12), (3, 7),
      (6, 11), (6, 9), (2, 6), (2, 7), (7, 11), (7, 9)],
  /- 73 -/ [(3, 5), (0, 3), (2, 5)],
  /- 74 -/ [(3, 5), (0, 3), (2, 5)],
  /- 75 -/ [(3, 5), (0, 3), (2, 5), (3, 10)],
  /- 76 -/ [(3, 5), (2, 5), (0, 3)],
  /- 77 -/ [(3, 5), (3, 10), (2, 5), (0, 3)],
  /- 78 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 79 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 80 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3)],
  /- 81 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12), (3, 7),
      (6, 11), (6, 9), (2, 6), (2, 7), (7, 11), (7, 9)],
  /- 82 -/ [(3, 5), (0, 3), (2, 5)],
  /- 83 -/ [(3, 5), (0, 3), (2, 5)],
  /- 84 -/ [(3, 5), (0, 3), (2, 5)],
  /- 85 -/ [(3, 5), (2, 5), (0, 3)],
  /- 86 -/ [(3, 5), (3, 10), (2, 5), (0, 3)],
  /- 87 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 88 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 89 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3)],
  /- 90 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12), (3, 7),
      (6, 11), (6, 9), (2, 6), (2, 7), (7, 11), (7, 9)],
  /- 91 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12), (3, 7),
      (6, 11), (6, 9), (2, 6), (2, 7), (7, 11), (7, 9)],
  /- 92 -/ [(3, 5), (0, 3), (2, 5)],
  /- 93 -/ [(3, 5), (0, 3), (2, 5)],
  /- 94 -/ [(3, 5), (0, 3), (2, 5)],
  /- 95 -/ [(3, 5), (2, 5), (0, 3), (3, 10)],
  /- 96 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 97 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 98 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3)],
  /- 99 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12), (3, 7),
      (6, 11), (6, 9), (2, 6), (2, 7), (7, 11), (7, 9)],
  /- 100 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 101 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12), (3, 7),
      (6, 11), (6, 9), (2, 6), (2, 7), (7, 11), (7, 9)],
  /- 102 -/ [(3, 5), (0, 3), (2, 5)],
  /- 103 -/ [(3, 5), (0, 3), (2, 5)],
  /- 104 -/ [(3, 5), (2, 5), (0, 3)],
  /- 105 -/ [(3, 5), (3, 10), (2, 5), (0, 3)],
  /- 106 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 107 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 108 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 109 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12), (3, 7),
      (6, 11), (6, 9), (2, 6), (2, 7), (7, 11), (7, 9)],
  /- 110 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 111 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 112 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12), (3, 7),
      (6, 11), (6, 9), (2, 6), (2, 7), (7, 11), (7, 9)],
  /- 113 -/ [(3, 5), (0, 3), (2, 5)],
  /- 114 -/ [(3, 5), (0, 3), (2, 5)],
  /- 115 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 116 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 117 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 118 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12), (3, 7),
      (6, 11), (6, 9), (2, 6), (2, 7), (7, 11), (7, 9), (8, 10)],
  /- 119 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 120 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 121 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 122 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 123 -/ [(0, 3), (2, 3), (3, 7), (3, 8), (3, 9), (3, 12), (3, 5), (5, 9), (5, 12),
      (6, 11), (6, 9), (2, 6), (2, 7), (7, 11), (7, 9)],
  /- 124 -/ [(3, 5), (0, 3), (2, 5)],
  /- 125 -/ [(3, 5), (0, 3), (2, 5)],
  /- 126 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 127 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 128 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (0, 3), (2, 5), (3, 10)],
  /- 129 -/ [(3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (3, 5), (5, 9), (5, 12), (3, 7),
      (6, 11), (6, 9), (2, 6), (2, 7), (7, 11), (7, 9), (8, 10)],
  /- 130 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 131 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 132 -/ [(0, 3), (2, 3), (3, 7)],
  /- 133 -/ [(3, 5), (0, 3), (2, 5)],
  /- 134 -/ [(3, 5), (0, 3), (2, 5)],
  /- 135 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 136 -/ [(3, 5), (0, 3), (2, 3), (3, 7), (2, 7), (7, 11)],
  /- 137 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 138 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (0, 3), (2, 5), (3, 10)],
  /- 139 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 140 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 141 -/ [(0, 3), (2, 3), (3, 13)],
  /- 142 -/ [(3, 5), (0, 3), (2, 5)],
  /- 143 -/ [(3, 5), (0, 3), (2, 5)],
  /- 144 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (3, 10), (2, 5), (0, 3)],
  /- 145 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (0, 3), (2, 5), (3, 10)],
  /- 146 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 147 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 148 -/ [(0, 3), (2, 3), (3, 5), (3, 13)],
  /- 149 -/ [(3, 5), (0, 3), (2, 5)],
  /- 150 -/ [(3, 5), (0, 3), (2, 5)],
  /- 151 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (3, 10), (2, 5), (0, 3)],
  /- 152 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 153 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 154 -/ [(0, 3), (2, 3), (3, 5), (3, 7), (2, 7), (7, 13), (3, 13)],
  /- 155 -/ [(3, 5), (0, 3), (2, 5)],
  /- 156 -/ [(3, 5), (0, 3), (2, 5)],
  /- 157 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (0, 3), (2, 5), (3, 10)],
  /- 158 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 159 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 160 -/ [(0, 3), (2, 3), (3, 5), (3, 7), (2, 7), (7, 13), (3, 13)],
  /- 161 -/ [(3, 5), (0, 3), (2, 5)],
  /- 162 -/ [(3, 5), (0, 3), (2, 5)],
  /- 163 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 164 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (3, 10), (2, 5), (0, 3)],
  /- 165 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 166 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 167 -/ [(0, 3), (2, 3), (3, 5), (3, 7), (2, 7), (7, 13), (3, 13), (3, 6), (2, 6)],
  /- 168 -/ [(3, 5), (0, 3), (2, 5)],
  /- 169 -/ [(3, 5), (0, 3), (2, 5)],
  /- 170 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 171 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 172 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (3, 10), (2, 5), (0, 3)],
  /- 173 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 174 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 175 -/ [(0, 3), (2, 3), (3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (3, 13), (6, 11), (2, 6)],
  /- 176 -/ [(3, 5), (0, 3), (2, 5)],
  /- 177 -/ [(3, 5), (0, 3), (2, 5)],
  /- 178 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 179 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 180 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 181 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (3, 10), (2, 5), (0, 3)],
  /- 182 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (2, 5), (0, 3), (3, 10)],
  /- 183 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 184 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 185 -/ [(0, 3), (2, 3), (3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (3, 13), (6, 11), (2, 6)],
  /- 186 -/ [(3, 5), (0, 3), (2, 5)],
  /- 187 -/ [(3, 5), (0, 3), (2, 5)],
  /- 188 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (0, 3), (2, 5), (8, 10)],
  /- 189 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 190 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 191 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 192 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (0, 3), (2, 5), (3, 10)],
  /- 193 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (2, 5), (0, 3)],
  /- 194 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (3, 10), (2, 5), (0, 3)],
  /- 195 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 196 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 197 -/ [(0, 3), (2, 3), (3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (3, 13), (6, 11), (2, 6)],
  /- 198 -/ [(3, 5), (0, 3), (2, 5)],
  /- 199 -/ [(3, 5), (0, 3), (2, 5)],
  /- 200 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (0, 3), (2, 5), (8, 10)],
  /- 201 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 202 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 203 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 204 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (2, 5), (0, 3)],
  /- 205 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (3, 10), (2, 5), (0, 3)],
  /- 206 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 207 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 208 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13), (6, 11), (2, 6)],
  /- 209 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 210 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 211 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 212 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (2, 5), (0, 3), (3, 10)],
  /- 213 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 214 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 215 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13), (6, 11)],
  /- 216 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13), (6, 11), (2, 6)],
  /- 217 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 218 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 219 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (2, 5), (0, 3)],
  /- 220 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (3, 10), (2, 5), (0, 3)],
  /- 221 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 222 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 223 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 224 -/ [(0, 3), (2, 3), (3, 13), (3, 7)],
  /- 225 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13), (6, 11), (2, 6)],
  /- 226 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 227 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 228 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 229 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 230 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 231 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 232 -/ [(0, 3), (2, 3), (3, 13), (3, 7)],
  /- 233 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13), (6, 11), (2, 6)],
  /- 234 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 235 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 236 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 237 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 238 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 239 -/ [(0, 3), (2, 3), (3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (3, 13)],
  /- 240 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 241 -/ [(0, 3), (2, 3), (3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (3, 13)],
  /- 242 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 243 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 244 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 245 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (0, 3), (2, 3), (5, 9), (5, 12), (3, 7),
      (7, 11), (7, 9), (2, 7)],
  /- 246 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 247 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 248 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 249 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 250 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 251 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 252 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 253 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 254 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 255 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 256 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 257 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 258 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 259 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 260 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 261 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 262 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 263 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 264 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 265 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 266 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 267 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 268 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 269 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 270 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 271 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 272 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 273 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 274 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 275 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 276 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 277 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 278 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 279 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 280 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 281 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (0, 3), (2, 5)],
  /- 282 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 283 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 284 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 285 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 286 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 287 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 288 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 289 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 290 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 291 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 292 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)],
  /- 293 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (0, 3), (2, 3), (3, 13)]]

/-- The matcher's colours on head indices. -/
def matcherColors : List ((Nat × Nat) × Nat) :=
  [((3, 5), 0), ((0, 3), 1), ((7, 11), 2), ((6, 11), 3), ((5, 12), 4), ((5, 9), 5),
   ((3, 8), 6), ((3, 7), 7), ((2, 7), 8), ((2, 6), 9), ((2, 3), 10), ((3, 6), 11),
   ((7, 9), 12), ((6, 9), 13), ((3, 12), 14), ((3, 9), 15), ((8, 10), 11), ((7, 13), 4),
   ((3, 13), 5), ((2, 5), 2), ((3, 10), 3), ((0, 4), 0), ((0, 2), 0)]

/-- The flag worker's live pairs by row, as head-index pairs (generated from `liveDistances`). -/
def flagsLive : List (List (Nat × Nat)) := [
  /- 0 -/ [],
  /- 1 -/ [(0, 16), (15, 16), (1, 16), (1, 15), (1, 14), (0, 1)],
  /- 2 -/ [(0, 17), (15, 17), (1, 17), (1, 15), (1, 14), (0, 1)],
  /- 3 -/ [(0, 17), (15, 17), (1, 17), (1, 15), (1, 14), (0, 1)],
  /- 4 -/ [(0, 17), (15, 17), (1, 17), (1, 15), (1, 14), (0, 1)],
  /- 5 -/ [(0, 17), (15, 17), (2, 17), (2, 15), (1, 14), (0, 2)],
  /- 6 -/ [(0, 17), (15, 17), (2, 17), (2, 15), (1, 4), (0, 2)],
  /- 7 -/ [(0, 17), (15, 17)],
  /- 8 -/ [(2, 17), (15, 17), (2, 15), (1, 4), (0, 2), (0, 17)],
  /- 9 -/ [(0, 17), (15, 17)],
  /- 10 -/ [(2, 17), (15, 17), (2, 15), (1, 4), (0, 2), (0, 17)],
  /- 11 -/ [(0, 17), (15, 17)],
  /- 12 -/ [(0, 17), (15, 17)],
  /- 13 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3)],
  /- 14 -/ [(0, 17), (15, 17)],
  /- 15 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (3, 5), (2, 3)],
  /- 16 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (3, 5), (3, 7),
      (2, 3), (2, 7)],
  /- 17 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (3, 5), (3, 7),
      (2, 3), (2, 7)],
  /- 18 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (3, 5), (3, 7),
      (2, 3), (2, 7), (3, 6), (2, 6)],
  /- 19 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (3, 5), (3, 7),
      (2, 3), (2, 7), (7, 11), (3, 6), (2, 6), (6, 11)],
  /- 20 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (3, 5), (3, 7),
      (2, 3), (2, 7), (7, 11), (3, 6), (2, 6), (6, 11)],
  /- 21 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 22 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (3, 6), (0, 17), (2, 6), (6, 11)],
  /- 23 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 7), (0, 2), (0, 17), (1, 4)],
  /- 24 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (3, 6), (0, 17), (2, 6), (6, 11)],
  /- 25 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (3, 6), (0, 17), (2, 6), (6, 11)],
  /- 26 -/ [(11, 17), (15, 17), (11, 15), (0, 3), (1, 7), (0, 2), (2, 15), (0, 17), (2, 17),
      (1, 4)],
  /- 27 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 28 -/ [(3, 7), (3, 6), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2),
      (2, 3), (2, 6)],
  /- 29 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (3, 6), (0, 17), (2, 6), (6, 11)],
  /- 30 -/ [(11, 17), (15, 17), (11, 15), (0, 3), (1, 7), (0, 2), (2, 15), (0, 17), (2, 17),
      (1, 4)],
  /- 31 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 32 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 33 -/ [(3, 8), (3, 6), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2),
      (2, 3), (2, 6)],
  /- 34 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (3, 6), (0, 17), (2, 6), (6, 11)],
  /- 35 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 7), (0, 2), (2, 15), (0, 17),
      (2, 17), (1, 4)],
  /- 36 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 37 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (3, 5), (3, 7),
      (2, 3), (2, 7), (7, 11)],
  /- 38 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 39 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (3, 5), (3, 7),
      (2, 3), (2, 7), (7, 11)],
  /- 40 -/ [(3, 8), (3, 6), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (2, 3), (2, 6)],
  /- 41 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (1, 7),
      (0, 17), (2, 17), (1, 4)],
  /- 42 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 43 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 44 -/ [(3, 8), (3, 6), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (2, 3)],
  /- 45 -/ [(3, 8), (3, 6), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (2, 3), (2, 6)],
  /- 46 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 47 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 48 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 49 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (2, 3)],
  /- 50 -/ [(3, 8), (3, 6), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (2, 3), (2, 6)],
  /- 51 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4), (3, 10)],
  /- 52 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 53 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 54 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3)],
  /- 55 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 56 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4), (3, 10)],
  /- 57 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 58 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 59 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (7, 9), (2, 7)],
  /- 60 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 61 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 62 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 63 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 64 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (7, 9), (2, 7)],
  /- 65 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 66 -/ [(0, 17), (15, 17), (2, 17), (2, 15), (1, 4), (0, 2), (0, 3)],
  /- 67 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 68 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 69 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (3, 6), (6, 9), (2, 6),
      (2, 7), (7, 9)],
  /- 70 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 71 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 72 -/ [(0, 17), (15, 17), (2, 17), (2, 15), (1, 4), (0, 2), (2, 13), (0, 3)],
  /- 73 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 74 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 75 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9)],
  /- 76 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 77 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (0, 2), (2, 15), (7, 13), (0, 17),
      (2, 17), (1, 4)],
  /- 78 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 79 -/ [(0, 17), (15, 17), (2, 17), (2, 15), (1, 4), (0, 2), (2, 13), (0, 3), (3, 10)],
  /- 80 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 81 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 82 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9)],
  /- 83 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 84 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 85 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (0, 2), (2, 15), (7, 13), (0, 17),
      (2, 17), (1, 4), (3, 10)],
  /- 86 -/ [(0, 17), (15, 17), (2, 17), (2, 15), (1, 4), (0, 2), (2, 13), (0, 3)],
  /- 87 -/ [(0, 17), (15, 17), (2, 17), (2, 15), (1, 4), (0, 2), (2, 13), (0, 3), (3, 10)],
  /- 88 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 89 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 90 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 91 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9)],
  /- 92 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 93 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 94 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 95 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (0, 2), (2, 15), (7, 13), (0, 17),
      (2, 17), (1, 4), (3, 10)],
  /- 96 -/ [(0, 17), (15, 17), (2, 17), (2, 15), (1, 4), (0, 2), (2, 13)],
  /- 97 -/ [(0, 17), (15, 17), (2, 17), (2, 15), (1, 4), (0, 2), (2, 13)],
  /- 98 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 99 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 100 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 7), (0, 17),
      (0, 2), (1, 4)],
  /- 101 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9)],
  /- 102 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (3, 5),
      (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6), (2, 7), (7, 11),
      (7, 9), (0, 2), (0, 17)],
  /- 103 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 104 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 105 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (0, 2), (2, 15), (7, 13), (0, 17),
      (2, 17), (1, 4), (3, 10)],
  /- 106 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (0, 2), (2, 15), (7, 13), (0, 17),
      (2, 17), (1, 4), (3, 10)],
  /- 107 -/ [(0, 17), (15, 17), (2, 17), (2, 15), (1, 4), (0, 2)],
  /- 108 -/ [(0, 17), (15, 17), (2, 17), (2, 15), (1, 4), (0, 2), (2, 13)],
  /- 109 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 110 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 111 -/ [(3, 8), (3, 9), (3, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 7), (0, 17),
      (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 112 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9)],
  /- 113 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 114 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (3, 5),
      (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6), (2, 7), (7, 11),
      (7, 9), (0, 2), (0, 17)],
  /- 115 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 116 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 117 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (0, 2), (2, 15), (7, 13), (0, 17),
      (2, 17), (1, 4)],
  /- 118 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (0, 2), (2, 15), (7, 13), (0, 17),
      (2, 17), (1, 4)],
  /- 119 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (0, 2), (2, 15), (7, 13), (0, 17),
      (2, 17), (1, 4), (3, 10)],
  /- 120 -/ [(2, 17), (15, 17), (2, 15), (1, 4), (0, 2), (0, 17)],
  /- 121 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 122 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 123 -/ [(3, 8), (3, 9), (3, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 7), (0, 17),
      (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 124 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9)],
  /- 125 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 126 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 127 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (3, 5),
      (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6), (2, 7), (7, 11),
      (7, 9), (0, 2), (0, 17)],
  /- 128 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 129 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 130 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (0, 2), (2, 15), (7, 13), (0, 17),
      (2, 17), (1, 4)],
  /- 131 -/ [(2, 17), (15, 17), (2, 15), (1, 4), (0, 2), (0, 17)],
  /- 132 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 133 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 134 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 7),
      (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 135 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9), (8, 10)],
  /- 136 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 137 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7)],
  /- 138 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 139 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7)],
  /- 140 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 7),
      (3, 8), (3, 9), (3, 12), (3, 5), (5, 9), (5, 12), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9)],
  /- 141 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 142 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 143 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (0, 2), (2, 15), (7, 13), (0, 17),
      (2, 17), (1, 4)],
  /- 144 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (0, 2), (2, 15), (7, 13), (0, 17),
      (2, 17), (1, 4)],
  /- 145 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3)],
  /- 146 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 147 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 148 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (1, 7), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 149 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9), (8, 10)],
  /- 150 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 151 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 152 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 7)],
  /- 153 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 154 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 155 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (0, 2), (2, 15), (7, 13), (0, 17),
      (2, 17), (1, 4)],
  /- 156 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (0, 2), (2, 15), (7, 13), (0, 17),
      (2, 17), (1, 4)],
  /- 157 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (3, 5), (2, 3)],
  /- 158 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 159 -/ [(3, 5), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (3, 7), (2, 3),
      (2, 7), (7, 11), (0, 17)],
  /- 160 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 161 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 162 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 163 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 13)],
  /- 164 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 165 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 166 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (0, 2), (2, 15), (7, 13), (0, 17),
      (2, 17), (1, 4)],
  /- 167 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (0, 2), (2, 15), (7, 13), (0, 17),
      (2, 17), (1, 4)],
  /- 168 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (3, 5), (3, 7),
      (2, 3), (2, 7)],
  /- 169 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4), (3, 10)],
  /- 170 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 171 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 172 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5), (3, 13)],
  /- 173 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 174 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 175 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (3, 5), (3, 7),
      (2, 3), (2, 7)],
  /- 176 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 177 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4), (3, 10)],
  /- 178 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 179 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 180 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5),
      (3, 7), (2, 7), (7, 13), (3, 13)],
  /- 181 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 182 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 183 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (3, 5), (3, 7),
      (2, 3), (2, 7), (3, 6), (2, 6)],
  /- 184 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 185 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 186 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 187 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 188 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5),
      (3, 7), (2, 7), (7, 13), (3, 13)],
  /- 189 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 190 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 191 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (3, 5), (3, 7),
      (2, 3), (2, 7), (7, 11), (3, 6), (2, 6), (6, 11)],
  /- 192 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 193 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 194 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 195 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5),
      (3, 7), (2, 7), (7, 13), (3, 13), (3, 6), (2, 6)],
  /- 196 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 197 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 198 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (3, 5), (3, 7),
      (2, 3), (2, 7), (7, 11), (3, 6), (2, 6), (6, 11)],
  /- 199 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 200 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 201 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 202 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 203 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5),
      (3, 7), (7, 11), (2, 7), (7, 13), (3, 13), (6, 11), (2, 6)],
  /- 204 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 205 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 206 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 207 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (3, 6), (0, 17), (2, 6), (6, 11)],
  /- 208 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 209 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (7, 13),
      (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 210 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 211 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 212 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 213 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5),
      (3, 7), (7, 11), (2, 7), (7, 13), (3, 13), (6, 11), (2, 6)],
  /- 214 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 215 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 216 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 7), (0, 2), (0, 17), (1, 4)],
  /- 217 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (3, 6), (0, 17), (2, 6), (6, 11)],
  /- 218 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (3, 6), (0, 17), (2, 6), (6, 11)],
  /- 219 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 220 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 221 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (7, 13),
      (0, 17), (0, 2), (2, 15), (2, 17), (1, 4), (3, 10)],
  /- 222 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 223 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 224 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5),
      (3, 7), (7, 11), (2, 7), (7, 13), (3, 13), (6, 11), (2, 6)],
  /- 225 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 226 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 227 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 228 -/ [(3, 7), (3, 6), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2),
      (2, 3), (2, 6)],
  /- 229 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (3, 6), (0, 17), (2, 6), (6, 11)],
  /- 230 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 231 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 232 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 233 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (7, 13),
      (0, 17), (0, 2), (2, 15), (2, 17), (1, 4), (3, 10)],
  /- 234 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 235 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 236 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17), (6, 11), (2, 6)],
  /- 237 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 238 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 239 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 240 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 241 -/ [(3, 8), (3, 6), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2),
      (2, 3), (2, 6)],
  /- 242 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (3, 6), (0, 17), (2, 6), (6, 11)],
  /- 243 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4), (8, 10)],
  /- 244 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 245 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 246 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 247 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (7, 13),
      (0, 17), (0, 2), (2, 15), (2, 17), (1, 4), (3, 10)],
  /- 248 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (7, 13),
      (0, 17), (0, 2), (2, 15), (2, 17), (1, 4), (3, 10)],
  /- 249 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 250 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 251 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17), (6, 11)],
  /- 252 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17), (6, 11), (2, 6)],
  /- 253 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 254 -/ [(3, 5), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6), (0, 2), (2, 15), (7, 13),
      (0, 17), (2, 17), (1, 4)],
  /- 255 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 256 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (3, 5), (3, 7),
      (2, 3), (2, 7), (7, 11)],
  /- 257 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 258 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (3, 5), (3, 7),
      (2, 3), (2, 7), (7, 11)],
  /- 259 -/ [(3, 8), (3, 6), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (2, 3), (2, 6)],
  /- 260 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4), (8, 10)],
  /- 261 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 262 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 263 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (7, 13),
      (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 264 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (7, 13),
      (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 265 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (7, 13),
      (0, 17), (0, 2), (2, 15), (2, 17), (1, 4), (3, 10)],
  /- 266 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 267 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 268 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 269 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 13), (3, 7)],
  /- 270 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17), (6, 11), (2, 6)],
  /- 271 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 272 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 273 -/ [(3, 8), (3, 6), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (2, 3)],
  /- 274 -/ [(3, 8), (3, 6), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (2, 3), (2, 6)],
  /- 275 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 276 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 277 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (7, 13),
      (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 278 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 279 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 280 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 281 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 282 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 13), (3, 7)],
  /- 283 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17), (6, 11), (2, 6)],
  /- 284 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 285 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 286 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (2, 3)],
  /- 287 -/ [(3, 8), (3, 6), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (2, 3), (2, 6)],
  /- 288 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 289 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 290 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (7, 13),
      (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 291 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (7, 13),
      (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 292 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 293 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 294 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 295 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5),
      (3, 7), (7, 11), (2, 7), (7, 13), (3, 13)],
  /- 296 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 297 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5),
      (3, 7), (7, 11), (2, 7), (7, 13), (3, 13)],
  /- 298 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 299 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 300 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3)],
  /- 301 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 302 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 303 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (7, 13),
      (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 304 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (7, 13),
      (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 305 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 306 -/ [(3, 5), (3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4),
      (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7), (0, 17), (0, 2)],
  /- 307 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 308 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 309 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 310 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 311 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (7, 9), (2, 7)],
  /- 312 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 313 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 314 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (7, 13),
      (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 315 -/ [(3, 8), (3, 5), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (7, 13),
      (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 316 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 317 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 318 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 319 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 320 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (7, 9), (2, 7)],
  /- 321 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 322 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 323 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 324 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 325 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 326 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 327 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (3, 6), (6, 9), (2, 6),
      (2, 7), (7, 9)],
  /- 328 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 329 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 330 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 331 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 332 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 333 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 334 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9)],
  /- 335 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 336 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 337 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 338 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 339 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 340 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 341 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9)],
  /- 342 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 343 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 344 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 345 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 346 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 347 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 348 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 349 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9)],
  /- 350 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 351 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 352 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 353 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 354 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 355 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 356 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 7), (0, 17),
      (0, 2), (1, 4)],
  /- 357 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9)],
  /- 358 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (3, 5),
      (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6), (2, 7), (7, 11),
      (7, 9), (0, 2), (0, 17)],
  /- 359 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 360 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 361 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 362 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 363 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 364 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 365 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9)],
  /- 366 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 367 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (3, 5),
      (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6), (2, 7), (7, 11),
      (7, 9), (0, 2), (0, 17)],
  /- 368 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 369 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 370 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 371 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 372 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 373 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 374 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9)],
  /- 375 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 376 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 377 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (3, 5),
      (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6), (2, 7), (7, 11),
      (7, 9), (0, 2), (0, 17)],
  /- 378 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 379 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 380 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 381 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 382 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 383 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 384 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9), (8, 10)],
  /- 385 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 386 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7)],
  /- 387 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 388 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7)],
  /- 389 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 7),
      (3, 8), (3, 9), (3, 12), (3, 5), (5, 9), (5, 12), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9)],
  /- 390 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 391 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 392 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 393 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 394 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 395 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 396 -/ [(3, 8), (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17),
      (0, 2), (3, 5), (5, 9), (5, 12), (2, 3), (3, 7), (6, 11), (6, 9), (2, 6),
      (2, 7), (7, 11), (7, 9), (8, 10)],
  /- 397 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 398 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 399 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 7)],
  /- 400 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 401 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (11, 17), (15, 17), (11, 15), (0, 3), (1, 6),
      (7, 13), (0, 17), (0, 2), (2, 15), (2, 17), (1, 4)],
  /- 402 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 403 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 404 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 405 -/ [(3, 5), (3, 7), (2, 3), (2, 7), (7, 11), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (0, 17)],
  /- 406 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 407 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 408 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 13)],
  /- 409 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 410 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 411 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 412 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 413 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5), (3, 13)],
  /- 414 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 415 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 416 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 417 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 418 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5),
      (3, 7), (2, 7), (7, 13), (3, 13)],
  /- 419 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 420 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 17), (15, 17), (2, 15), (0, 3),
      (1, 4), (0, 2), (2, 3), (3, 13), (0, 17)],
  /- 421 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 422 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 423 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5),
      (3, 7), (2, 7), (7, 13), (3, 13)],
  /- 424 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 425 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 426 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5),
      (3, 7), (2, 7), (7, 13), (3, 13), (3, 6), (2, 6)],
  /- 427 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 428 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 429 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5),
      (3, 7), (7, 11), (2, 7), (7, 13), (3, 13), (6, 11), (2, 6)],
  /- 430 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 431 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 432 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5),
      (3, 7), (7, 11), (2, 7), (7, 13), (3, 13), (6, 11), (2, 6)],
  /- 433 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 434 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 435 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5),
      (3, 7), (7, 11), (2, 7), (7, 13), (3, 13), (6, 11), (2, 6)],
  /- 436 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 437 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 438 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (6, 11), (2, 6)],
  /- 439 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 440 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 441 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (6, 11)],
  /- 442 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (6, 11), (2, 6)],
  /- 443 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 444 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 445 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 446 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 13), (3, 7)],
  /- 447 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (6, 11), (2, 6)],
  /- 448 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 449 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 450 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 451 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 452 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 13), (3, 7)],
  /- 453 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (6, 11), (2, 6)],
  /- 454 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 455 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 456 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 457 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5),
      (3, 7), (7, 11), (2, 7), (7, 13), (3, 13)],
  /- 458 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 459 -/ [(2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 2), (0, 17), (2, 3), (3, 5),
      (3, 7), (7, 11), (2, 7), (7, 13), (3, 13)],
  /- 460 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 461 -/ [(3, 5), (3, 8), (5, 9), (5, 12), (2, 3), (3, 7), (7, 11), (7, 9), (2, 7),
      (3, 9), (3, 12), (2, 17), (15, 17), (2, 15), (0, 3), (1, 4), (0, 17), (0, 2)],
  /- 462 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 463 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 464 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 465 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 466 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 467 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 468 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 469 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 470 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 471 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 472 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 473 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 474 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 475 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 476 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 477 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 478 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 479 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 480 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 481 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 482 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 483 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 484 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 485 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 486 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 487 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 488 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 489 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 490 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)],
  /- 491 -/ [(3, 5), (3, 7), (7, 11), (2, 7), (7, 13), (2, 3), (3, 13), (2, 17), (15, 17),
      (2, 15), (0, 3), (1, 4), (0, 2), (0, 17)]]

/-- The flag worker's colours on head indices. -/
def flagsColors : List ((Nat × Nat) × Nat) :=
  [((15, 17), 0), ((0, 17), 1), ((2, 17), 2), ((2, 15), 3), ((0, 2), 4), ((1, 4), 5),
   ((0, 3), 6), ((3, 5), 7), ((5, 12), 8), ((5, 9), 9), ((3, 8), 10), ((8, 10), 11),
   ((3, 12), 12), ((3, 9), 13), ((7, 11), 14), ((6, 11), 15), ((3, 7), 16), ((2, 7), 17),
   ((2, 6), 18), ((2, 3), 19), ((7, 9), 20), ((6, 9), 21), ((3, 6), 11), ((7, 13), 12),
   ((3, 13), 8), ((11, 17), 14), ((11, 15), 15), ((1, 6), 13), ((3, 10), 11), ((1, 7), 11),
   ((2, 13), 7), ((1, 14), 5), ((1, 15), 2), ((0, 1), 3), ((1, 17), 4), ((15, 16), 0),
   ((1, 16), 1), ((0, 16), 4)]

theorem matcher_rows_0 : rowsCheck matcherWorker matcherColors matcherLive 0 50 = true := by
  decide +kernel

theorem matcher_rows_50 : rowsCheck matcherWorker matcherColors matcherLive 50 50 = true := by
  decide +kernel

theorem matcher_rows_100 : rowsCheck matcherWorker matcherColors matcherLive 100 50 = true := by
  decide +kernel

theorem matcher_rows_150 : rowsCheck matcherWorker matcherColors matcherLive 150 50 = true := by
  decide +kernel

theorem matcher_rows_200 : rowsCheck matcherWorker matcherColors matcherLive 200 50 = true := by
  decide +kernel

theorem matcher_rows_250 : rowsCheck matcherWorker matcherColors matcherLive 250 44 = true := by
  decide +kernel

theorem matcher_global : globalCheck matcherWorker matcherColors matcherLive = true := by
  decide +kernel

theorem matcher_code_length : matcherWorker.program.code.length = 294 := by
  decide

theorem matcher_rows :
    rowsCheck matcherWorker matcherColors matcherLive 0
      matcherWorker.program.code.length = true := by
  rw [matcher_code_length]
  exact rowsCheck_split 0 50 244 matcher_rows_0
    (rowsCheck_split 50 50 194 matcher_rows_50
    (rowsCheck_split 100 50 144 matcher_rows_100
    (rowsCheck_split 150 50 94 matcher_rows_150
    (rowsCheck_split 200 50 44 matcher_rows_200
    (matcher_rows_250)))))

/-- **The table facts of the matcher**, from the kernel-checked certificate. -/
theorem matcher_tableFacts : TableFacts matcherWorker :=
  tableFacts_of_certificate matcher_global matcher_rows

theorem flags_rows_0 : rowsCheck flagsWorker flagsColors flagsLive 0 50 = true := by
  decide +kernel

theorem flags_rows_50 : rowsCheck flagsWorker flagsColors flagsLive 50 50 = true := by
  decide +kernel

theorem flags_rows_100 : rowsCheck flagsWorker flagsColors flagsLive 100 50 = true := by
  decide +kernel

theorem flags_rows_150 : rowsCheck flagsWorker flagsColors flagsLive 150 50 = true := by
  decide +kernel

theorem flags_rows_200 : rowsCheck flagsWorker flagsColors flagsLive 200 50 = true := by
  decide +kernel

theorem flags_rows_250 : rowsCheck flagsWorker flagsColors flagsLive 250 50 = true := by
  decide +kernel

theorem flags_rows_300 : rowsCheck flagsWorker flagsColors flagsLive 300 50 = true := by
  decide +kernel

theorem flags_rows_350 : rowsCheck flagsWorker flagsColors flagsLive 350 50 = true := by
  decide +kernel

theorem flags_rows_400 : rowsCheck flagsWorker flagsColors flagsLive 400 50 = true := by
  decide +kernel

theorem flags_rows_450 : rowsCheck flagsWorker flagsColors flagsLive 450 42 = true := by
  decide +kernel

theorem flags_global : globalCheck flagsWorker flagsColors flagsLive = true := by
  decide +kernel

theorem flags_code_length : flagsWorker.program.code.length = 492 := by
  decide

theorem flags_rows :
    rowsCheck flagsWorker flagsColors flagsLive 0
      flagsWorker.program.code.length = true := by
  rw [flags_code_length]
  exact rowsCheck_split 0 50 442 flags_rows_0
    (rowsCheck_split 50 50 392 flags_rows_50
    (rowsCheck_split 100 50 342 flags_rows_100
    (rowsCheck_split 150 50 292 flags_rows_150
    (rowsCheck_split 200 50 242 flags_rows_200
    (rowsCheck_split 250 50 192 flags_rows_250
    (rowsCheck_split 300 50 142 flags_rows_300
    (rowsCheck_split 350 50 92 flags_rows_350
    (rowsCheck_split 400 50 42 flags_rows_400
    (flags_rows_450)))))))))

/-- **The table facts of the flag worker**, from the kernel-checked certificate. -/
theorem flags_tableFacts : TableFacts flagsWorker :=
  tableFacts_of_certificate flags_global flags_rows

/-- The invariant holds along every run of the matcher: initially, and after any sequence of
`start` / `service` / `arrive` / `mark` / `resetFlags` (each lemma above with
`matcher_tableFacts`). For instance, one service quantum: -/
theorem matcher_service_inv {g : Ghost} {s : WorkerState} (hinv : Inv matcherWorker g s) :
    Inv matcherWorker (ghostService matcherWorker s g).2
      (service (Worker.ofSpec matcherWorker) s) :=
  service_inv matcher_tableFacts hinv

theorem flags_service_inv {g : Ghost} {s : WorkerState} (hinv : Inv flagsWorker g s) :
    Inv flagsWorker (ghostService flagsWorker s g).2 (service (Worker.ofSpec flagsWorker) s) :=
  service_inv flags_tableFacts hinv

end Concrete

end PalPeg.ScaWorkerRegs
