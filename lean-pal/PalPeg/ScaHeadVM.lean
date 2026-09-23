import PalPeg.ScaWorkerCoroutine

/-!
# The logical head VM, and the coroutine worker as its physical encoding

Python has no table-free semantics of the GS head programs: the head VMs
`StreamingMatcher` (`docs/palindromes-in-peg/gs_match_heads.py:66-128`) and `DualFlagVM`
(`gs_dual_flags.py:30-73`, over `HeadVM`, `gs_heads.py:318-376`) interpret a *table*, on integer
head positions over one word. This file gives the same VMs driven by the coroutine
(`PalPeg.ScaGsCoroutine.next`, via `ScaWorkerCoroutine.Ctl.resume`), and relates them to the
coroutine worker `ScaWorkerCoroutine.CoWorker`, whose heads are colored reader registers
holding physical cursors with `reverse` bits.

## The logical VMs

* `HVM`: control `Ctl`, positions `pos : String → ℤ`, the word, outputs, flags. `rev` is
  `DualFlagVM.reverse`; `StreamingMatcher` has no orientation and `stepMatch` never touches it.
* `stepMatch` = `StreamingMatcher.step` (`gs_match_heads.py:89-120`), `waiting`/`append`
  (`gs_match_heads.py:80-87`). `stepFlags` = `DualFlagVM.step` (`gs_dual_flags.py:40-68`) with the
  `HeadVM.step` fallback (`gs_heads.py:331-365`). `none` = a Python exception (`AssertionError`,
  or `ValueError` for an instruction the VM does not know). A move is Python's sequential loop
  (`moveSeq`).

## The correspondence (derived from `ScaWindowWorker.start`, `ScaWindowWorker.lean:453-473`)

`Emb.phys E r i = if r then E.top - i else E.base + i`: a reversed register holds `top - i`, a
forward one `base + i`.

* **Matcher.** `start` puts Origin (logical `0`) reversed at `end = W` and Tail (logical `W`,
  since the `(Origin, Tail)` register gets `-length`) forward at `W`. So `base = 0`, `top = W`:
  a forward head at logical `i` sits at physical `i` (not `W + i`), a reversed one at `W - i`.
  The word is `X = (text.take W).reverse ++ text.drop W` (`MatchRel.word`); a reversed head at
  `i < W` reads `text[W-1-i] = X[i]` and a forward head at `i ≥ W` reads `text[i] = X[i]`.
* **Flags.** Origin `(begin, fwd)`, TextOrigin `(end, rev)`, OriginalEnd `(begin, rev)` are the
  logical `0`, `0`, `b` of `DualFlagVM` with `b = end - begin`: `base = begin`,
  `top = begin + b`, word `y = (text.drop begin).take b`, and `reverse` bits = `DualFlagVM.reverse`.

Only reader heads have registers (`spec.readers.colors`), and a register holds a head only while
it is live (register coloring). The relations (`MatchRel`, `FlagRel`) therefore constrain the
heads of a live set `L`; `Decodes`/`Covers`/`Proper` state what the ROM row and the liveness give
(the certified worker's ROM satisfies `Decodes` by `decodes_fieldsAt`). Blind heads and `End`
etc. are seen only through the distance registers: `RegsValue` (the hypothesis `hregs`) says the
selected register is the logical difference of the compared heads.

## Results

* `match_step` / `flags_step`: if the Python step succeeds, one active coroutine-worker step
  reaches the same coroutine control, keeps the relation for the live-after readers, and adds no
  fault (the matcher: except `matchLate`); the matcher's `output` bit is raised exactly on `match`,
  the flag stack gets the `flag` bit.
* `match_step_certified` / `flags_step_certified`: the same for a `Certified` worker, with the
  relation indexed by the reader-live set (`liveReaders`) of the simulating table row.
* `match_step_error`: a `symbols`/`assert_equal` that makes `StreamingMatcher.step` raise makes
  the worker fault; `match_step_returned` / `flags_step_returned`: the halting sink.
* `match_arrive` (`arrive` = `append`), `flags_arrive`, `match_waiting_iff`, `match_start`,
  `flags_start`.
* Core: `posAgree_after` (Lemma A: the colored register loop moves every live register to the
  physical image of the logical post-position, without a move fault).

## Mismatches between the Scala-derived worker and the Python VMs

* **Sides (matcher).** A forward head below `W` reads `text[i] ≠ X[i]`; a reversed head at `W`
  faults on a read Python accepts; reversed cursors cannot pass `W`. `MatchSide` assumes the
  program keeps reversed readers on the pattern side and forward readers on the text side.
* **`match` timing.** The worker faults on `match` while `B` is still available
  (`ScaWindowWorker.lean:141-146`); `StreamingMatcher.step` has no such check.
* **Unchecked heads.** Python range-checks every non-blind head on a move; the worker checks
  only moved reader registers, against the arrived text instead of the logical word. Likewise a
  flag-worker read outside `[0, b)` reads arrived text past the segment instead of faulting.
* **Unknown instructions.** The worker ignores instructions a Python VM rejects with
  `ValueError` (`flag`/`border` in the matcher; `available`/`assert_equal`/`match` in the flags VM).
-/

set_option autoImplicit false

namespace PalPeg.ScaHeadVM

open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWindowWorker PalPeg.ScaWorkerCoroutine

/-! ## The logical VMs -/

/-- `BLIND` (`gs_heads.py:14`): coordinates that never read. -/
def blind : List String := ["KP", "KFirst", "Second"]

/-- `FLAG_BLIND` (`gs_flag_heads.py:13`). -/
def flagBlind : List String := ["KP", "KFirst", "Second", "Lower", "Upper", "Cursor"]

/-- The logical head VM. -/
structure HVM where
  /-- The coroutine control, in place of the Python table `state`. -/
  ctl : Ctl
  /-- `self.positions`. -/
  pos : String → ℤ
  /-- `DualFlagVM.reverse` (not read or written by the matcher). -/
  rev : String → Bool
  /-- `self.word`. -/
  word : List (Fin 2)
  /-- `StreamingMatcher.pattern_size`. -/
  patternSize : ℤ
  /-- `self.outputs` (`match` / `border` values), in append order. -/
  outputs : List ℤ
  /-- `DualFlagVM.flags`, in append order. -/
  flags : List Bool

/-- `len(self.word)`. -/
def HVM.len (v : HVM) : ℤ := v.word.length

/-- `0 <= position < len(self.word)`. -/
def HVM.inRange (v : HVM) (h : String) : Prop := 0 ≤ v.pos h ∧ v.pos h < v.len

instance (v : HVM) (h : String) : Decidable (v.inRange h) := by
  unfold HVM.inRange; infer_instance

/-- The pending event; a returned coroutine sits in the halting sink (`GsProgram.scala:324`). -/
def ctlEvent : Ctl → Option Event
  | .pending _ e => some e
  | .returned _ => some .halt
  | .failed => none

/-- Net displacement of `h` in a move batch. -/
def sumDelta (ms : List Movement) (h : String) : ℤ :=
  (ms.filter fun m => decide (m.head = h)).foldl (fun acc m => acc + m.delta) 0

/-- Python's move loop: `positions[head] += delta`, then the range check of every head outside
`blindHeads` (`gs_match_heads.py:95-99`, `gs_dual_flags.py:57-62`). -/
def moveSeq (blindHeads : List String) (len : ℤ) : List Movement → (String → ℤ) → Option (String → ℤ)
  | [], π => some π
  | m :: ms, π =>
    let π' := Function.update π m.head (π m.head + m.delta)
    if m.head ∉ blindHeads ∧ ¬(0 ≤ π' m.head ∧ π' m.head ≤ len) then none
    else moveSeq blindHeads len ms π'

/-- `StreamingMatcher.step` (`gs_match_heads.py:89-120`). The next control is the coroutine
resumed with the decision (`targets[int(decision)] if op in MATCH_TESTS else targets[0]`). -/
def stepMatch (v : HVM) : Option HVM :=
  match v.ctl with
  | .pending _ e =>
    let go (d : Bool) : Ctl := v.ctl.resume matchTests d
    match e with
    | .move ms => (moveSeq blind v.len ms v.pos).map fun π => { v with pos := π, ctl := go false }
    | .copy t s => some { v with pos := Function.update v.pos t (v.pos s), ctl := go false }
    | .equal a b => some { v with ctl := go (decide (v.pos a = v.pos b)) }
    | .less a b => some { v with ctl := go (decide (v.pos a < v.pos b)) }
    | .assertEqual a b => if v.pos a = v.pos b then some { v with ctl := go false } else none
    | .symbols a b =>
      if v.inRange a ∧ v.inRange b then
        some { v with ctl := go (decide (v.word[(v.pos a).toNat]? = v.word[(v.pos b).toNat]?)) }
      else none
    | .available h => some { v with ctl := go (decide (v.pos h < v.len)) }
    | .«match» h => some { v with outputs := v.outputs ++ [v.pos h - v.patternSize], ctl := go false }
    | _ => none
  | _ => none

/-- `StreamingMatcher.waiting` (`gs_match_heads.py:80-83`). -/
def HVM.waiting (v : HVM) : Prop :=
  ∃ c h, v.ctl = .pending c (.available h) ∧ v.len ≤ v.pos h

/-- `StreamingMatcher.append` (`gs_match_heads.py:85-87`). -/
def HVM.append (v : HVM) (c : Fin 2) : HVM :=
  { v with word := v.word ++ [c],
           pos := Function.update v.pos "OriginalEnd" (v.pos "OriginalEnd" + 1) }

/-- `StreamingMatcher(pattern)` (`gs_match_heads.py:69-78`) with the coroutine control. -/
def matchInitial (pattern : List (Fin 2)) (ctl : Ctl) : HVM :=
  { ctl, word := pattern, patternSize := pattern.length, outputs := [], flags := [],
    rev := fun _ => false,
    pos := fun h => if h = "Tail" ∨ h = "OriginalEnd" then pattern.length else 0 }

/-- `DualFlagVM`'s oriented read (`gs_dual_flags.py:44-46`). -/
def HVM.view (v : HVM) (h : String) : Option (Fin 2) :=
  if v.rev h then v.word[(v.len - 1 - v.pos h).toNat]? else v.word[(v.pos h).toNat]?

/-- `DualFlagVM.step` (`gs_dual_flags.py:40-68`), falling back to `HeadVM.step`
(`gs_heads.py:331-365`) for `equal`/`less`/`border`. `HeadVM.step` raises at `halt`
(`gs_heads.py:332`): the VM is then `done` (`flagsDone`), not stepped. -/
def stepFlags (v : HVM) : Option HVM :=
  match v.ctl with
  | .pending _ e =>
    let go (d : Bool) : Ctl := v.ctl.resume tests d
    match e with
    | .symbols a b =>
      if a ∉ flagBlind ∧ b ∉ flagBlind ∧ v.inRange a ∧ v.inRange b then
        some { v with ctl := go (decide (v.view a = v.view b)) }
      else none
    | .copy t s =>
      some { v with pos := Function.update v.pos t (v.pos s),
                    rev := Function.update v.rev t (v.rev s), ctl := go false }
    | .move ms => (moveSeq flagBlind v.len ms v.pos).map fun π => { v with pos := π, ctl := go false }
    | .flag b => some { v with flags := v.flags ++ [b], ctl := go false }
    | .equal a b => some { v with ctl := go (decide (v.pos a = v.pos b)) }
    | .less a b => some { v with ctl := go (decide (v.pos a < v.pos b)) }
    | .border h => some { v with outputs := v.outputs ++ [v.pos h], ctl := go false }
    | _ => none
  | _ => none

/-- `HeadVM.done` (`gs_heads.py:327-329`): the control is the halting sink. -/
def HVM.flagsDone (v : HVM) : Prop := ∃ val, v.ctl = .returned val

/-- `DualFlagVM(word, lower, upper)` (`gs_dual_flags.py:31-37`) with the coroutine control. -/
def flagsInitialVM (word : List (Fin 2)) (lower upper : ℤ) (ctl : Ctl) : HVM :=
  { ctl, word, patternSize := 0, outputs := [], flags := [],
    rev := fun h => decide (h = "OriginalEnd" ∨ h = "TextOrigin"),
    pos := fun h =>
      if h = "OriginalEnd" then word.length
      else if h = "Lower" then lower else if h = "Upper" then upper else 0 }

/-! ## The worker's head registers, one register at a time -/

/-- The effect of `moveReg` on register `i` (cursor `p`, reverse bit `r`), with the arrived text
of length `n`: new cursor, new reverse bit, fault. -/
def cellStep (f : Fields) (active : Bool) (srcPos : Option Nat) (srcRev : Option Bool) (n : Nat)
    (i p : Nat) (r : Bool) : Nat × Bool × Bool :=
  let raw := f.dataDelta.getD i 0
  let δ : Int := if r then -raw else raw
  let moving := active && decide (δ ≠ 0)
  let fault := moving && !(decide (0 ≤ (p : Int) + δ) && decide ((p : Int) + δ ≤ n))
  let p1 := if moving then ((p : Int) + δ).toNat else p
  match active && isOp f.event "copy" && decide (f.dataTarget = some i), srcPos, srcRev with
  | true, some q, some rv => (q, rv, fault)
  | _, _, _ => (p1, r, fault)

theorem set_getD_self {α : Type} (l : List α) (i : Nat) (d : α) : l.set i (l.getD i d) = l := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.set_getElem_self hi
  · exact List.set_eq_of_length_le (by omega)

theorem set_getElem?_getD_self {α : Type} (l : List α) (i : Nat) (d : α) :
    l.set i (l[i]?.getD d) = l := by
  rw [← List.getD_eq_getElem?_getD]; exact set_getD_self l i d

theorem moveReg_eq (f : Fields) (active : Bool) (srcPos : Option Nat) (srcRev : Option Bool)
    (s : WorkerState) (i : Nat) :
    moveReg f active srcPos srcRev s i =
      let c := cellStep f active srcPos srcRev s.text.length i (s.data.getD i 0) (s.reverse.getD i false)
      { s with data := s.data.set i c.1, reverse := s.reverse.set i c.2.1, fault := s.fault || c.2.2 } := by
  unfold moveReg cellStep
  simp only [WorkerState.canMoveTo]
  generalize (active && isOp f.event "copy" && decide (f.dataTarget = some i)) = copying
  generalize (if s.reverse.getD i false = true then -f.dataDelta.getD i 0 else f.dataDelta.getD i 0) = δ
  cases copying <;> cases srcPos <;> cases srcRev <;>
    by_cases hmv : (active && decide (δ ≠ 0)) = true <;>
    simp only [hmv] <;> simp [set_getElem?_getD_self, List.set_set]

/-- `moves`' register loop, in closed form: register `j < k` is updated by `cellStep` from the
original cursor and bit (each index is touched once), faults accumulate. -/
theorem foldl_moveReg (f : Fields) (active : Bool) (sp : Option Nat) (sr : Option Bool)
    (s : WorkerState) (k : Nat) :
    (List.range k).foldl (moveReg f active sp sr) s =
      { s with
        data := s.data.mapIdx fun j p =>
          if j < k then (cellStep f active sp sr s.text.length j p (s.reverse.getD j false)).1 else p,
        reverse := s.reverse.mapIdx fun j r =>
          if j < k then (cellStep f active sp sr s.text.length j (s.data.getD j 0) r).2.1 else r,
        fault := s.fault || (List.range k).any fun j =>
          (cellStep f active sp sr s.text.length j (s.data.getD j 0) (s.reverse.getD j false)).2.2 } := by
  induction k with
  | zero =>
    have hd : s.data.mapIdx (fun j p => if j < 0 then
        (cellStep f active sp sr s.text.length j p (s.reverse.getD j false)).1 else p) = s.data := by
      apply List.ext_getElem?; intro j; simp [List.getElem?_mapIdx]
    have hr : s.reverse.mapIdx (fun j r => if j < 0 then
        (cellStep f active sp sr s.text.length j (s.data.getD j 0) r).2.1 else r) = s.reverse := by
      apply List.ext_getElem?; intro j; simp [List.getElem?_mapIdx]
    simp only [List.range_zero, List.foldl_nil, hd, hr, List.any_nil, Bool.or_false]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, moveReg_eq]
    simp only
    have hdk : (s.data.mapIdx fun j p => if j < k then
        (cellStep f active sp sr s.text.length j p (s.reverse.getD j false)).1 else p).getD k 0 =
        s.data.getD k 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
    have hrk : (s.reverse.mapIdx fun j r => if j < k then
        (cellStep f active sp sr s.text.length j (s.data.getD j 0) r).2.1 else r).getD k false =
        s.reverse.getD k false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
    rw [hdk, hrk]
    congr 1
    · apply List.ext_getElem?; intro j
      rw [List.getElem?_set, List.getElem?_mapIdx, List.getElem?_mapIdx, List.length_mapIdx]
      by_cases hj : k = j
      · subst hj
        by_cases hk : k < s.data.length
        · simp [hk, List.getD_eq_getElem?_getD]
        · simp [hk]
      · rw [if_neg hj]
        cases s.data[j]? with
        | none => rfl
        | some p =>
          simp only [Option.map_some]
          congr 1
          by_cases hjk : j < k
          · simp [hjk, show j < k + 1 by omega]
          · simp [hjk, show ¬ j < k + 1 by omega]
    · apply List.ext_getElem?; intro j
      rw [List.getElem?_set, List.getElem?_mapIdx, List.getElem?_mapIdx, List.length_mapIdx]
      by_cases hj : k = j
      · subst hj
        by_cases hk : k < s.reverse.length
        · simp [hk, List.getD_eq_getElem?_getD]
        · simp [hk]
      · rw [if_neg hj]
        cases s.reverse[j]? with
        | none => rfl
        | some p =>
          simp only [Option.map_some]
          congr 1
          by_cases hjk : j < k
          · simp [hjk, show j < k + 1 by omega]
          · simp [hjk, show ¬ j < k + 1 by omega]
    · rw [List.any_append, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]

/-- `moves` in closed form. -/
theorem moves_eq (spec : WorkerSpec) (f : Fields) (active : Bool) (s : WorkerState) :
    moves spec f active s =
      let sp := f.dataSource.map fun j => s.data.getD j 0
      let sr := f.dataSource.map fun j => s.reverse.getD j false
      let n := spec.readers.registers
      { s with
        data := s.data.mapIdx fun j p =>
          if j < n then (cellStep f active sp sr s.text.length j p (s.reverse.getD j false)).1 else p,
        reverse := s.reverse.mapIdx fun j r =>
          if j < n then (cellStep f active sp sr s.text.length j (s.data.getD j 0) r).2.1 else r,
        fault := s.fault || (List.range n).any fun j =>
          (cellStep f active sp sr s.text.length j (s.data.getD j 0) (s.reverse.getD j false)).2.2 } :=
  foldl_moveReg _ _ _ _ s _

theorem getD_mapIdx {α : Type} (l : List α) (g : Nat → α → α) (i : Nat) (d : α) :
    (l.mapIdx g).getD i d = if i < l.length then g i (l.getD i d) else d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  by_cases hi : i < l.length
  · simp [hi]
  · simp [hi]

/-! ## What a ROM row says about the reader registers -/

/-- The reader register of `h` (`ScaffoldWindowWorkers.scala:33`). -/
def color (spec : WorkerSpec) (h : String) : Option Nat := lookupFirst h spec.readers.colors

/-- The reader-register columns of a ROM row executing `e`, given the heads `after` live after
it: exactly what `fieldsAt` decodes (`ScaffoldRom.scala:108-125`; `decodes_fieldsAt`). -/
structure Decodes (spec : WorkerSpec) (after : List String) (e : Event) (f : Fields) : Prop where
  event : f.event = e
  symbols : ∀ a b, e = .symbols a b → f.dataLeft = color spec a ∧ f.dataRight = color spec b
  available : ∀ h, e = .available h → f.dataLeft = color spec h
  copyLive : ∀ t s, e = .copy t s → t ∈ after →
    f.dataTarget = color spec t ∧ f.dataSource = color spec s
  copyDead : ∀ t s, e = .copy t s → t ∉ after → f.dataTarget = none
  move : ∀ ms, e = .move ms → ∀ i, i < spec.readers.registers → f.dataDelta.getD i 0 =
    (ms.filter fun m => decide (m.head ∈ after ∧ color spec m.head = some i)).foldl
      (fun acc m => acc + m.delta) 0
  still : (∀ ms, e ≠ .move ms) → ∀ i, i < spec.readers.registers → f.dataDelta.getD i 0 = 0
  bit : ∀ b, e = .flag b → f.bit = b

/-- The reader liveness across a row: `readerTransfer` (`GsHeadLiveness.scala:145-155`) of the
live-after set `A` is contained in the live-before set `L`. -/
structure Covers (e : Event) (L A : List String) : Prop where
  keep : ∀ h ∈ A, (∀ t s, e = .copy t s → h ≠ t) → h ∈ L
  source : ∀ t s, e = .copy t s → t ∈ A → s ∈ L
  reads : ∀ a b, e = .symbols a b → a ∈ L ∧ b ∈ L
  avail : ∀ h, e = .available h → h ∈ L

/-- Distinct live heads have distinct registers (the coloring is proper on `A`). -/
def Proper (spec : WorkerSpec) (A : List String) : Prop :=
  ∀ h ∈ A, ∀ h' ∈ A, ∀ i, color spec h = some i → color spec h' = some i → h = h'

/-- Every live head has a register. -/
def Colored (spec : WorkerSpec) (L : List String) : Prop := ∀ h ∈ L, ∃ i, color spec h = some i

/-- Register indices are in range. -/
def ColorsBound (spec : WorkerSpec) : Prop :=
  ∀ h i, color spec h = some i → i < spec.readers.registers

/-- Reader heads are not blind. -/
def ReadersNotBlind (spec : WorkerSpec) (blindHeads : List String) : Prop :=
  ∀ h i, color spec h = some i → h ∉ blindHeads

/-- **The register hypothesis `hregs`.** For the compared heads `a`, `b` of the pending event,
the distance register the row selects holds the logical difference, signed by the row's
`distance.reverse` (the canonical pair of `fieldsAt`). -/
def RegsValue (f : Fields) (s : WorkerState) (pos : String → ℤ) (e : Event) : Prop :=
  ∀ a b, (e = .equal a b ∨ e = .less a b ∨ e = .assertEqual a b) →
    selectReg s.regs f.distanceTest = if f.distanceReverse then pos b - pos a else pos a - pos b

theorem compare_of_regsValue {f : Fields} {s : WorkerState} {pos : String → ℤ} {e : Event}
    (hregs : RegsValue f s pos e) {a b : String}
    (he : e = .equal a b ∨ e = .less a b ∨ e = .assertEqual a b) :
    ScaWindowWorker.compare f s = (decide (pos a = pos b), decide (pos a < pos b)) := by
  have hv := hregs a b he
  unfold ScaWindowWorker.compare
  rw [hv]
  cases f.distanceReverse
  · simp only [Bool.false_eq_true, if_false, Prod.mk.injEq]
    constructor
    · exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
    · exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  · simp only [if_true, Prod.mk.injEq]
    constructor
    · exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
    · exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩

/-! ## Physical cursors -/

/-- The affine placement of logical coordinates: reversed at `top - i`, forward at `base + i`. -/
structure Emb where
  base : ℤ
  top : ℤ

def Emb.phys (E : Emb) (r : Bool) (i : ℤ) : ℤ := if r then E.top - i else E.base + i

/-- The registers of the live heads hold their logical positions, through `E`. -/
def PosAgree (spec : WorkerSpec) (E : Emb) (L : List String) (s : WorkerState)
    (pos : String → ℤ) : Prop :=
  ∀ h ∈ L, ∀ i, color spec h = some i →
    (s.data.getD i 0 : ℤ) = E.phys (s.reverse.getD i false) (pos h)

/-- The reverse bits of the live heads are the logical orientations (`DualFlagVM.reverse`). -/
def RevAgree (spec : WorkerSpec) (L : List String) (s : WorkerState) (rev : String → Bool) : Prop :=
  ∀ h ∈ L, ∀ i, color spec h = some i → s.reverse.getD i false = rev h

/-! ## The effect, field by field -/

theorem checks_data (spec : WorkerSpec) (f : Fields) (a : Bool) (s : WorkerState) :
    (checks spec f a s).data = s.data ∧ (checks spec f a s).reverse = s.reverse ∧
      (checks spec f a s).text = s.text ∧ (checks spec f a s).flags = s.flags ∧
      (checks spec f a s).mode = s.mode := by
  unfold checks; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem execute_data (f : Fields) (a : Bool) (s : WorkerState) :
    (execute f a s).data = s.data ∧ (execute f a s).reverse = s.reverse ∧
      (execute f a s).text = s.text ∧ (execute f a s).flags = s.flags ∧
      (execute f a s).mode = s.mode ∧ (execute f a s).fault = s.fault ∧
      (execute f a s).output = s.output := by
  unfold execute; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem finish_data (spec : WorkerSpec) (f : Fields) (a : Bool) (s : WorkerState) :
    (finish spec f a s).data = s.data ∧ (finish spec f a s).reverse = s.reverse ∧
      (finish spec f a s).text = s.text ∧ (finish spec f a s).output = s.output := by
  unfold finish
  split
  · split <;> split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The fault of `checks` on a matcher. -/
theorem checks_fault_matcher (spec : WorkerSpec) (hflags : spec.isFlags = false) (f : Fields)
    (a : Bool) (s : WorkerState) :
    (checks spec f a s).fault =
      (s.fault || (a && isOp f.event "symbols" && !(s.readAt f.dataLeft).2) ||
        (a && isOp f.event "symbols" && !(s.readAt f.dataRight).2) ||
        (a && isOp f.event "assert_equal" && !(compare f s).1) ||
        (a && isOp f.event "match" && s.availableAt (lookupFirst "B" spec.readers.colors))) ∧
    (checks spec f a s).output = (s.output || (a && isOp f.event "match")) := by
  unfold checks; simp only [hflags, Bool.false_eq_true, if_false]; exact ⟨trivial, trivial⟩

/-- The fault of `checks` on a flag worker. -/
theorem checks_fault_flags (spec : WorkerSpec) (hflags : spec.isFlags = true) (f : Fields)
    (a : Bool) (s : WorkerState) :
    (checks spec f a s).fault =
      (s.fault || (a && isOp f.event "symbols" && !(s.readAt f.dataLeft).2) ||
        (a && isOp f.event "symbols" && !(s.readAt f.dataRight).2) ||
        (a && isOp f.event "assert_equal" && !(compare f s).1)) ∧
    (checks spec f a s).output = s.output := by
  unfold checks; simp only [hflags, if_true]; exact ⟨trivial, trivial⟩

theorem finish_matcher (spec : WorkerSpec) (hflags : spec.isFlags = false) (f : Fields)
    (a : Bool) (s : WorkerState) :
    (finish spec f a s).fault = (s.fault || (a && isOp f.event "halt")) ∧
      (finish spec f a s).flags = s.flags ∧ (finish spec f a s).mode = s.mode := by
  unfold finish; simp only [hflags, Bool.false_eq_true, if_false]; exact ⟨trivial, trivial, trivial⟩

theorem finish_flags (spec : WorkerSpec) (hflags : spec.isFlags = true) (f : Fields)
    (a : Bool) (s : WorkerState) :
    (finish spec f a s).fault = s.fault ∧
      (finish spec f a s).flags =
        (if a && isOp f.event "flag" then f.bit :: s.flags else s.flags) ∧
      (finish spec f a s).mode = (if a && isOp f.event "halt" then .done else s.mode) := by
  unfold finish; simp only [hflags, if_true]
  split <;> split <;> simp_all

/-- Register `j` under an active step of row `f` from state `s`. -/
def cellOf (f : Fields) (s : WorkerState) (j : Nat) : Nat × Bool × Bool :=
  cellStep f true (f.dataSource.map fun k => s.data.getD k 0)
    (f.dataSource.map fun k => s.reverse.getD k false) s.text.length j (s.data.getD j 0)
    (s.reverse.getD j false)

/-- The active effect: `checks`, `execute`, the register loop in closed form, then `finish`. -/
theorem effect_eq (spec : WorkerSpec) (f : Fields) (s : WorkerState) :
    effect spec f true s = finish spec f true
      { execute f true (checks spec f true s) with
        data := s.data.mapIdx fun j p =>
          if j < spec.readers.registers then (cellStep f true (f.dataSource.map fun k => s.data.getD k 0)
            (f.dataSource.map fun k => s.reverse.getD k false) s.text.length j p
            (s.reverse.getD j false)).1 else p,
        reverse := s.reverse.mapIdx fun j r =>
          if j < spec.readers.registers then (cellStep f true (f.dataSource.map fun k => s.data.getD k 0)
            (f.dataSource.map fun k => s.reverse.getD k false) s.text.length j (s.data.getD j 0) r).2.1
          else r,
        fault := (checks spec f true s).fault ||
          (List.range spec.readers.registers).any fun j => (cellOf f s j).2.2 } := by
  obtain ⟨hd1, hr1, ht1, -, -⟩ := checks_data spec f true s
  obtain ⟨hd2, hr2, ht2, -, -, hf2, -⟩ := execute_data f true (checks spec f true s)
  unfold effect
  rw [moves_eq]
  simp only [hd2, hr2, ht2, hf2, hd1, hr1, ht1, cellOf]

theorem effect_data (spec : WorkerSpec) (f : Fields) (s : WorkerState) :
    (effect spec f true s).text = s.text ∧
      (effect spec f true s).data.length = s.data.length ∧
      (effect spec f true s).reverse.length = s.reverse.length ∧
      (∀ j, j < spec.readers.registers → j < s.data.length →
        (effect spec f true s).data.getD j 0 = (cellOf f s j).1) ∧
      (∀ j, j < spec.readers.registers → j < s.reverse.length →
        (effect spec f true s).reverse.getD j false = (cellOf f s j).2.1) := by
  rw [effect_eq]
  obtain ⟨hd, hr, ht, -⟩ := finish_data spec f true
    { execute f true (checks spec f true s) with
        data := s.data.mapIdx fun j p =>
          if j < spec.readers.registers then (cellStep f true (f.dataSource.map fun k => s.data.getD k 0)
            (f.dataSource.map fun k => s.reverse.getD k false) s.text.length j p
            (s.reverse.getD j false)).1 else p,
        reverse := s.reverse.mapIdx fun j r =>
          if j < spec.readers.registers then (cellStep f true (f.dataSource.map fun k => s.data.getD k 0)
            (f.dataSource.map fun k => s.reverse.getD k false) s.text.length j (s.data.getD j 0) r).2.1
          else r,
        fault := (checks spec f true s).fault ||
          (List.range spec.readers.registers).any fun j => (cellOf f s j).2.2 }
  obtain ⟨-, -, ht2, -, -, -, -⟩ := execute_data f true (checks spec f true s)
  obtain ⟨-, -, ht1, -, -⟩ := checks_data spec f true s
  rw [hd, hr, ht]
  refine ⟨ht2.trans ht1, List.length_mapIdx, List.length_mapIdx, ?_, ?_⟩
  · intro j hj hjl
    rw [getD_mapIdx, if_pos hjl, if_pos hj]; rfl
  · intro j hj hjl
    rw [getD_mapIdx, if_pos hjl, if_pos hj]; rfl

/-! ## One register -/

theorem cellStep_still (f : Fields) (sp : Option Nat) (sr : Option Bool) (n i p : Nat) (r : Bool)
    (hraw : f.dataDelta.getD i 0 = 0)
    (hcopy : (isOp f.event "copy" && decide (f.dataTarget = some i)) = false) :
    cellStep f true sp sr n i p r = (p, r, false) := by
  unfold cellStep
  simp only [hraw, neg_zero, ite_self, ne_eq, not_true_eq_false, decide_false, Bool.and_false,
    Bool.false_and, Bool.false_eq_true, if_false, Bool.true_and, hcopy]

theorem cellStep_copy (f : Fields) (n i p q : Nat) (r rv : Bool)
    (hraw : f.dataDelta.getD i 0 = 0) (hcopy : isOp f.event "copy" = true)
    (htarget : f.dataTarget = some i) :
    cellStep f true (some q) (some rv) n i p r = (q, rv, false) := by
  unfold cellStep
  simp only [hraw, neg_zero, ite_self, ne_eq, not_true_eq_false, decide_false, Bool.and_false,
    Bool.false_and, Bool.true_and, hcopy, htarget, decide_true]

theorem cellStep_move (f : Fields) (sp : Option Nat) (sr : Option Bool) (n i p : Nat) (r : Bool)
    (hcopy : isOp f.event "copy" = false) :
    cellStep f true sp sr n i p r =
      let δ : Int := if r then -(f.dataDelta.getD i 0) else f.dataDelta.getD i 0
      (if δ ≠ 0 then ((p : Int) + δ).toNat else p, r,
        decide (δ ≠ 0) && !(decide (0 ≤ (p : Int) + δ) && decide ((p : Int) + δ ≤ n))) := by
  unfold cellStep
  simp only [hcopy, Bool.true_and, Bool.false_and]
  by_cases hδ : (if r = true then -f.dataDelta.getD i 0 else f.dataDelta.getD i 0) = 0 <;>
    simp

/-! ## The live registers across one step -/

/-- The logical positions after the instruction `e` (for the instructions that move heads). -/
def movePos (e : Event) (π : String → ℤ) : String → ℤ :=
  match e with
  | .move ms => fun h => π h + sumDelta ms h
  | .copy t s => Function.update π t (π s)
  | _ => π

/-- The orientations after `e` (`DualFlagVM`: copies carry the view). -/
def moveRev (e : Event) (rev : String → Bool) : String → Bool :=
  match e with
  | .copy t s => Function.update rev t (rev s)
  | _ => rev

/-- Every live register that a move displaces lands inside the arrived text. -/
def MoveFits (spec : WorkerSpec) (E : Emb) (A : List String) (s : WorkerState) (π : String → ℤ)
    (e : Event) : Prop :=
  ∀ ms, e = .move ms → ∀ h ∈ A, ∀ i, color spec h = some i → sumDelta ms h ≠ 0 →
    0 ≤ E.phys (s.reverse.getD i false) (π h + sumDelta ms h) ∧
      E.phys (s.reverse.getD i false) (π h + sumDelta ms h) ≤ s.text.length

theorem filter_live_eq {spec : WorkerSpec} {A : List String} (hproper : Proper spec A)
    {h : String} (hA : h ∈ A) {i : Nat} (hc : color spec h = some i) (ms : List Movement) :
    ms.filter (fun m => decide (m.head ∈ A ∧ color spec m.head = some i)) =
      ms.filter (fun m => decide (m.head = h)) := by
  apply List.filter_congr
  intro m _
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨hmA, hmc⟩; exact hproper _ hmA _ hA _ hmc hc
  · rintro rfl; exact ⟨hA, hc⟩

theorem filter_dead_eq {spec : WorkerSpec} {A : List String} {i : Nat}
    (hno : ∀ h ∈ A, color spec h ≠ some i) (ms : List Movement) :
    ms.filter (fun m => decide (m.head ∈ A ∧ color spec m.head = some i)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro m _
  simp only [decide_eq_true_eq, not_and]
  exact fun hmA hmc => hno _ hmA hmc

theorem exists_of_sumDelta_ne {ms : List Movement} {h : String} (hne : sumDelta ms h ≠ 0) :
    ∃ m ∈ ms, m.head = h := by
  by_contra hno
  apply hne
  have hnil : ms.filter (fun m => decide (m.head = h)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro m hm
    simp only [decide_eq_true_eq]
    exact fun hmh => hno ⟨m, hm, hmh⟩
  unfold sumDelta; rw [hnil]; rfl

theorem isOp_move_copy (ms : List Movement) : isOp (.move ms) "copy" = false := rfl
theorem isOp_copy_copy (t s : String) : isOp (.copy t s) "copy" = true := rfl

/-- One register of a move row. -/
theorem move_cell {f : Fields} {s : WorkerState} {i : Nat} {E : Emb} {x d : ℤ}
    (hcopy : isOp f.event "copy" = false) (hraw : f.dataDelta.getD i 0 = d)
    (hp : (s.data.getD i 0 : ℤ) = E.phys (s.reverse.getD i false) x)
    (hfit : d ≠ 0 → 0 ≤ E.phys (s.reverse.getD i false) (x + d) ∧
      E.phys (s.reverse.getD i false) (x + d) ≤ s.text.length) :
    ((cellOf f s i).1 : ℤ) = E.phys (s.reverse.getD i false) (x + d) ∧
      (cellOf f s i).2.1 = s.reverse.getD i false ∧ (cellOf f s i).2.2 = false := by
  unfold cellOf
  rw [cellStep_move _ _ _ _ _ _ _ hcopy, hraw]
  generalize s.reverse.getD i false = r at hp hfit ⊢
  generalize s.data.getD i 0 = p at hp ⊢
  by_cases hd : d = 0
  · subst hd
    cases r <;> simp_all [Emb.phys]
  · obtain ⟨hlo, hhi⟩ := hfit hd
    cases r
    · have hδ : (p : ℤ) + d = E.phys false (x + d) := by
        rw [hp]; unfold Emb.phys; simp only [Bool.false_eq_true, if_false]; ring
      simp only [Bool.false_eq_true, if_false, ne_eq, hd, not_false_eq_true, if_true,
        decide_true, Bool.true_and, true_and]
      rw [hδ, Int.toNat_of_nonneg hlo]
      simp [hlo, hhi]
    · have hδ : (p : ℤ) + -d = E.phys true (x + d) := by
        rw [hp]; unfold Emb.phys; simp only [if_true]; ring
      have hnd : -d ≠ 0 := by omega
      simp only [if_true, ne_eq, hnd, not_false_eq_true, decide_true, Bool.true_and, true_and]
      rw [hδ, Int.toNat_of_nonneg hlo]
      simp [hlo, hhi]

/-- A register that neither moves nor receives a copy. -/
theorem still_cell {f : Fields} {s : WorkerState} {i : Nat}
    (hraw : f.dataDelta.getD i 0 = 0)
    (hcopy : (isOp f.event "copy" && decide (f.dataTarget = some i)) = false) :
    cellOf f s i = (s.data.getD i 0, s.reverse.getD i false, false) :=
  cellStep_still _ _ _ _ _ _ _ hraw hcopy

/-- **Lemma A.** Under the decoded row, the liveness and a proper coloring, an active step
leaves every live-after register at the physical image of the logical post-position, carries
the orientations as `DualFlagVM` does, and raises no move fault. -/
theorem regs_after {spec : WorkerSpec} {E : Emb} {L A : List String} {e : Event} {f : Fields}
    {s : WorkerState} {π : String → ℤ}
    (hdec : Decodes spec A e f) (hcov : Covers e L A) (hproper : Proper spec A)
    (hcolored : Colored spec L)
    (hpos : PosAgree spec E L s π) (hfit : MoveFits spec E A s π e) :
    (∀ j, j < spec.readers.registers → (cellOf f s j).2.2 = false) ∧
    (∀ h ∈ A, ∀ i, color spec h = some i → i < spec.readers.registers →
      ((cellOf f s i).1 : ℤ) = E.phys (cellOf f s i).2.1 (movePos e π h)) ∧
    (∀ rev, RevAgree spec L s rev → ∀ h ∈ A, ∀ i, color spec h = some i →
      i < spec.readers.registers → (cellOf f s i).2.1 = moveRev e rev h) := by
  have hev := hdec.event
  cases e with
  | move ms =>
    have hcopy : isOp f.event "copy" = false := by rw [hev]; rfl
    have hkeep : ∀ h ∈ A, h ∈ L := fun h hA => hcov.keep h hA (fun t s he => by cases he)
    -- a live register moves by its head's net displacement
    have hlive : ∀ h ∈ A, ∀ i, color spec h = some i → i < spec.readers.registers →
        ((cellOf f s i).1 : ℤ) = E.phys (s.reverse.getD i false) (π h + sumDelta ms h) ∧
          (cellOf f s i).2.1 = s.reverse.getD i false ∧ (cellOf f s i).2.2 = false := by
      intro h hA i hc hi
      have hraw : f.dataDelta.getD i 0 = sumDelta ms h := by
        rw [hdec.move ms rfl i hi, filter_live_eq hproper hA hc]; rfl
      exact move_cell hcopy hraw (hpos h (hkeep h hA) i hc) (hfit ms rfl h hA i hc)
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      by_cases hsome : ∃ h ∈ A, color spec h = some j
      · obtain ⟨h, hA, hc⟩ := hsome
        exact (hlive h hA j hc hj).2.2
      · have hno : ∀ h ∈ A, color spec h ≠ some j := fun h hA hc => hsome ⟨h, hA, hc⟩
        have hraw : f.dataDelta.getD j 0 = 0 := by
          rw [hdec.move ms rfl j hj, filter_dead_eq hno]; rfl
        rw [still_cell hraw (by rw [hcopy]; rfl)]
    · intro h hA i hc hi
      obtain ⟨hp, hr, -⟩ := hlive h hA i hc hi
      rw [hr]; exact hp
    · intro rev hrev h hA i hc hi
      rw [(hlive h hA i hc hi).2.1]
      exact hrev h (hkeep h hA) i hc
  | copy t src =>
    have hnm : ∀ ms, Event.copy t src ≠ .move ms := fun ms he => by cases he
    have hraw : ∀ j, j < spec.readers.registers → f.dataDelta.getD j 0 = 0 :=
      hdec.still hnm
    have hiscopy : isOp f.event "copy" = true := by rw [hev]; rfl
    by_cases htA : t ∈ A
    · obtain ⟨htarget, hsource⟩ := hdec.copyLive t src rfl htA
      have hsrcL := hcov.source t src rfl htA
      obtain ⟨cs, hcs⟩ := hcolored src hsrcL
      have hsrcPos := hpos src hsrcL cs hcs
      -- the register of the target receives the source's cursor and bit
      have htcell : ∀ i, color spec t = some i → i < spec.readers.registers →
          cellOf f s i = (s.data.getD cs 0, s.reverse.getD cs false, false) := by
        intro i hct hi
        unfold cellOf
        rw [hsource, hcs]
        exact cellStep_copy f _ i _ _ _ _ (hraw i hi) hiscopy (by rw [htarget, hct])
      have hother : ∀ j, j < spec.readers.registers → color spec t ≠ some j →
          cellOf f s j = (s.data.getD j 0, s.reverse.getD j false, false) := by
        intro j hj hne
        exact still_cell (hraw j hj) (by rw [hiscopy, htarget]; simp [hne])
      have hkeep : ∀ h ∈ A, h ≠ t → h ∈ L := fun h hA hne =>
        hcov.keep h hA (fun t' s' he => by cases he; exact hne)
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        by_cases hct : color spec t = some j
        · rw [htcell j hct hj]
        · rw [hother j hj hct]
      · intro h hA i hc hi
        by_cases hht : h = t
        · subst hht
          rw [htcell i hc hi]
          simp only [movePos, Function.update_self]
          exact hsrcPos
        · have hct : color spec t ≠ some i := fun hct => hht (hproper h hA t htA i hc hct)
          rw [hother i hi hct]
          simp only [movePos, Function.update_of_ne hht]
          exact hpos h (hkeep h hA hht) i hc
      · intro rev hrev h hA i hc hi
        by_cases hht : h = t
        · subst hht
          rw [htcell i hc hi]
          simp only [moveRev, Function.update_self]
          exact hrev src hsrcL cs hcs
        · have hct : color spec t ≠ some i := fun hct => hht (hproper h hA t htA i hc hct)
          rw [hother i hi hct]
          simp only [moveRev, Function.update_of_ne hht]
          exact hrev h (hkeep h hA hht) i hc
    · have htarget := hdec.copyDead t src rfl htA
      have hid : ∀ j, j < spec.readers.registers →
          cellOf f s j = (s.data.getD j 0, s.reverse.getD j false, false) := fun j hj =>
        still_cell (hraw j hj) (by rw [htarget]; simp)
      have hne : ∀ h ∈ A, h ≠ t := fun h hA hht => htA (hht ▸ hA)
      have hkeep : ∀ h ∈ A, h ∈ L := fun h hA =>
        hcov.keep h hA (fun t' s' he => by cases he; exact hne h hA)
      refine ⟨fun j hj => by rw [hid j hj], ?_, ?_⟩
      · intro h hA i hc hi
        rw [hid i hi]
        simp only [movePos, Function.update_of_ne (hne h hA)]
        exact hpos h (hkeep h hA) i hc
      · intro rev hrev h hA i hc hi
        rw [hid i hi]
        simp only [moveRev, Function.update_of_ne (hne h hA)]
        exact hrev h (hkeep h hA) i hc
  | _ =>
    all_goals
      have hraw : ∀ j, j < spec.readers.registers → f.dataDelta.getD j 0 = 0 :=
        hdec.still (fun ms he => by cases he)
      have hnotcopy : isOp f.event "copy" = false := by rw [hev]; rfl
      have hid : ∀ j, j < spec.readers.registers →
          cellOf f s j = (s.data.getD j 0, s.reverse.getD j false, false) := fun j hj =>
        still_cell (hraw j hj) (by rw [hnotcopy]; rfl)
      have hkeep : ∀ h ∈ A, h ∈ L := fun h hA => hcov.keep h hA (fun t' s' he => by cases he)
      refine ⟨fun j hj => by rw [hid j hj], ?_, ?_⟩
      · intro h hA i hc hi
        rw [hid i hi]
        exact hpos h (hkeep h hA) i hc
      · intro rev hrev h hA i hc hi
        rw [hid i hi]
        exact hrev h (hkeep h hA) i hc

/-- **Lemma A, on the worker state.** The live-after registers of the post-state agree with the
logical post-positions, lengths and text are kept, and no register faults. -/
theorem posAgree_after {spec : WorkerSpec} {E : Emb} {L A : List String} {e : Event} {f : Fields}
    {s : WorkerState} {π : String → ℤ}
    (hdec : Decodes spec A e f) (hcov : Covers e L A) (hproper : Proper spec A)
    (hcolored : Colored spec L) (hbound : ColorsBound spec)
    (hdlen : s.data.length = spec.readers.registers)
    (hrlen : s.reverse.length = spec.readers.registers)
    (hpos : PosAgree spec E L s π) (hfit : MoveFits spec E A s π e) :
    PosAgree spec E A (effect spec f true s) (movePos e π) ∧
      (effect spec f true s).data.length = spec.readers.registers ∧
      (effect spec f true s).reverse.length = spec.readers.registers ∧
      (effect spec f true s).text = s.text ∧
      ((List.range spec.readers.registers).any fun j => (cellOf f s j).2.2) = false ∧
      (∀ rev, RevAgree spec L s rev → RevAgree spec A (effect spec f true s) (moveRev e rev)) := by
  obtain ⟨hnofault, hposA, hrevA⟩ := regs_after hdec hcov hproper hcolored hpos hfit
  obtain ⟨htext, hdl, hrl, hdget, hrget⟩ := effect_data spec f s
  refine ⟨?_, hdl.trans hdlen, hrl.trans hrlen, htext, ?_, ?_⟩
  · intro h hA i hc
    have hi := hbound h i hc
    rw [hdget i hi (by omega), hrget i hi (by omega)]
    exact hposA h hA i hc hi
  · rw [List.any_eq_false]
    intro j hj
    rw [hnofault j (List.mem_range.mp hj)]
    simp
  · intro rev hrev h hA i hc
    have hi := hbound h i hc
    rw [hrget i hi (by omega)]
    exact hrevA rev hrev h hA i hc hi

/-! ## Python's move loop -/

theorem foldl_delta_init (l : List Movement) (a : ℤ) :
    l.foldl (fun acc m => acc + m.delta) a = a + l.foldl (fun acc m => acc + m.delta) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons m l ih =>
    simp only [List.foldl_cons]
    rw [ih (a + m.delta), ih (0 + m.delta)]
    ring

theorem sumDelta_nil (h : String) : sumDelta [] h = 0 := rfl

theorem sumDelta_cons (m : Movement) (ms : List Movement) (h : String) :
    sumDelta (m :: ms) h = (if m.head = h then m.delta else 0) + sumDelta ms h := by
  unfold sumDelta
  rw [List.filter_cons]
  by_cases hm : m.head = h
  · simp only [hm, decide_true, if_true, List.foldl_cons]
    rw [foldl_delta_init]; ring
  · simp [hm]

/-- A successful Python move displaces every head by its net delta, and leaves every non-blind
moved head inside `[0, len]`. -/
theorem moveSeq_some {bl : List String} {len : ℤ} :
    ∀ {ms : List Movement} {π π' : String → ℤ}, moveSeq bl len ms π = some π' →
      π' = (fun h => π h + sumDelta ms h) ∧
        ∀ m ∈ ms, m.head ∉ bl → 0 ≤ π' m.head ∧ π' m.head ≤ len
  | [], π, π', h => by
    simp only [moveSeq, Option.some.injEq] at h
    subst h
    exact ⟨by funext x; simp [sumDelta_nil], fun m hm => by cases hm⟩
  | m :: ms, π, π', h => by
    simp only [moveSeq] at h
    split at h
    · cases h
    · next hcheck =>
      obtain ⟨hπ', hin⟩ := moveSeq_some h
      have hform : π' = fun x => π x + sumDelta (m :: ms) x := by
        rw [hπ']; funext x
        rw [sumDelta_cons, Function.update_apply]
        by_cases hx : x = m.head
        · subst hx; simp; ring
        · simp only [hx, if_false, show ¬ m.head = x from fun h => hx h.symm]; ring
      refine ⟨hform, ?_⟩
      intro m' hm' hnb
      rcases List.mem_cons.mp hm' with rfl | hm'
      · by_cases hlater : ∃ k ∈ ms, k.head = m'.head
        · obtain ⟨k, hk, hkh⟩ := hlater
          have := hin k hk (hkh ▸ hnb)
          rw [hkh] at this; exact this
        · have hzero : sumDelta ms m'.head = 0 := by
            by_contra hne
            exact hlater (exists_of_sumDelta_ne hne)
          have hval : π' m'.head = Function.update π m'.head (π m'.head + m'.delta) m'.head := by
            rw [hπ']; simp only [hzero, add_zero]
          push Not at hcheck
          rw [hval]
          exact hcheck hnb
      · exact hin m' hm' hnb

/-! ## Matcher coordinates -/

/-- The matcher's word `X = x ++ T` with `x = (text.take W).reverse`, `T = text.drop W`. -/
def matchWord (text : List (Fin 2)) (W : Nat) : List (Fin 2) := (text.take W).reverse ++ text.drop W

theorem matchWord_length {text : List (Fin 2)} {W : Nat} (hW : W ≤ text.length) :
    (matchWord text W).length = text.length := by
  simp [matchWord, List.length_take, List.length_drop]; omega

theorem matchWord_fwd {text : List (Fin 2)} {W k : Nat} (hW : W ≤ text.length) (hk : W ≤ k) :
    (matchWord text W)[k]? = text[k]? := by
  unfold matchWord
  have hlen : (text.take W).reverse.length = W := by simp; omega
  rw [List.getElem?_append_right (by omega), hlen, List.getElem?_drop]
  congr 1; omega

theorem matchWord_rev {text : List (Fin 2)} {W k : Nat} (hW : W ≤ text.length) (hk : k < W) :
    (matchWord text W)[k]? = text[W - 1 - k]? := by
  unfold matchWord
  have hlen : (text.take W).reverse.length = W := by simp; omega
  rw [List.getElem?_append_left (by omega), List.getElem?_reverse (by simp; omega),
    List.getElem?_take]
  simp only [List.length_take, Nat.min_eq_left hW]
  rw [if_pos (by omega)]

/-- Reversed readers hold pattern cells `[0, W)`, forward readers text cells `≥ W`
(`SCA_GS_MAPPING.md` §0). -/
def OnSide (W : Nat) (r : Bool) (x : ℤ) : Prop := if r then 0 ≤ x ∧ x < W else (W : ℤ) ≤ x

/-- A matcher register reads the logical word, and its read is valid exactly when the logical
position has arrived. -/
theorem readAt_matcher {s : WorkerState} {W i : Nat} {x : ℤ} (hW : W ≤ s.text.length)
    (hp : (s.data.getD i 0 : ℤ) = (⟨0, W⟩ : Emb).phys (s.reverse.getD i false) x)
    (hside : OnSide W (s.reverse.getD i false) x) :
    s.readAt (some i) =
      if 0 ≤ x ∧ x < s.text.length then ((matchWord s.text W)[x.toNat]?, true) else (none, false) := by
  unfold WorkerState.readAt
  simp only
  generalize s.reverse.getD i false = r at hp hside ⊢
  generalize s.data.getD i 0 = p at hp ⊢
  unfold Emb.phys at hp
  unfold OnSide at hside
  cases r
  · simp only [Bool.false_eq_true, if_false, zero_add] at hp hside ⊢
    have hx0 : 0 ≤ x := by omega
    by_cases hlt : p < s.text.length
    · rw [if_pos hlt, if_pos ⟨hx0, by omega⟩, matchWord_fwd hW (by omega)]
      congr 2; omega
    · rw [if_neg hlt, if_neg (by omega)]
  · simp only [if_true] at hp hside ⊢
    obtain ⟨hx0, hxW⟩ := hside
    rw [if_neg (by omega), if_pos (by omega), if_pos ⟨hx0, by omega⟩,
      matchWord_rev hW (by omega)]
    congr 2; omega

/-! ## The matcher VM, case by case -/

/-- The decision `StreamingMatcher.step` takes on a test. -/
def matchDecision (v : HVM) : Event → Bool
  | .equal a b => decide (v.pos a = v.pos b)
  | .less a b => decide (v.pos a < v.pos b)
  | .symbols a b => decide (v.word[(v.pos a).toNat]? = v.word[(v.pos b).toNat]?)
  | .available h => decide (v.pos h < v.len)
  | _ => false

/-- The instructions `StreamingMatcher.step` executes without an exception. -/
def matchOk (v : HVM) : Event → Prop
  | .move ms => (moveSeq blind v.len ms v.pos).isSome
  | .copy _ _ | .equal _ _ | .less _ _ | .available _ | .«match» _ => True
  | .assertEqual a b => v.pos a = v.pos b
  | .symbols a b => v.inRange a ∧ v.inRange b
  | _ => False

/-- The value `StreamingMatcher.step` appends to `outputs`. -/
def matchOut (v : HVM) : Event → List ℤ
  | .«match» h => [v.pos h - v.patternSize]
  | _ => []

/-- `StreamingMatcher.step` without an exception, in closed form. -/
theorem stepMatch_some {v v' : HVM} {c : Config} {e : Event} (hctl : v.ctl = .pending c e)
    (hstep : stepMatch v = some v') :
    matchOk v e ∧ v' = { v with
      pos := movePos e v.pos,
      outputs := v.outputs ++ matchOut v e,
      ctl := v.ctl.resume matchTests (matchDecision v e) } := by
  unfold stepMatch at hstep
  rw [hctl] at hstep ⊢
  cases e with
  | move ms =>
    simp only [Option.map_eq_some_iff] at hstep
    obtain ⟨π', hms, rfl⟩ := hstep
    refine ⟨by simp [matchOk, hms], ?_⟩
    rw [(moveSeq_some hms).1]
    simp [movePos, matchOut, matchDecision]
  | copy t src =>
    simp only [Option.some.injEq] at hstep
    subst hstep
    exact ⟨trivial, by simp [movePos, matchOut, matchDecision]⟩
  | equal a b =>
    simp only [Option.some.injEq] at hstep
    subst hstep
    exact ⟨trivial, by simp [movePos, matchOut, matchDecision]⟩
  | less a b =>
    simp only [Option.some.injEq] at hstep
    subst hstep
    exact ⟨trivial, by simp [movePos, matchOut, matchDecision]⟩
  | assertEqual a b =>
    simp only at hstep
    split at hstep
    · next heq =>
      simp only [Option.some.injEq] at hstep
      subst hstep
      exact ⟨heq, by simp [movePos, matchOut, matchDecision]⟩
    · cases hstep
  | symbols a b =>
    simp only at hstep
    split at hstep
    · next hin =>
      simp only [Option.some.injEq] at hstep
      subst hstep
      exact ⟨hin, by simp [movePos, matchOut, matchDecision]⟩
    · cases hstep
  | available h =>
    simp only [Option.some.injEq] at hstep
    subst hstep
    exact ⟨trivial, by simp [movePos, matchOut, matchDecision]⟩
  | «match» h =>
    simp only [Option.some.injEq] at hstep
    subst hstep
    exact ⟨trivial, by simp [movePos, matchOut, matchDecision]⟩
  | border h => cases hstep
  | flag b => cases hstep
  | halt => cases hstep

/-- `StreamingMatcher.step` raises exactly when `matchOk` fails. -/
theorem stepMatch_none {v : HVM} {c : Config} {e : Event} (hctl : v.ctl = .pending c e)
    (hstep : stepMatch v = none) : ¬ matchOk v e := by
  unfold stepMatch at hstep
  rw [hctl] at hstep
  cases e <;> simp_all [matchOk, HVM.inRange]

/-- Commands ignore the decision; tests are resumed with it. -/
theorem resume_congr {tests : List String} {c : Config} {e : Event} {d d' : Bool}
    (h : tests.contains e.op = true → d = d') :
    (Ctl.pending c e).resume tests d = (Ctl.pending c e).resume tests d' := by
  unfold Ctl.resume respond
  by_cases ht : tests.contains e.op = true
  · rw [h ht]
  · simp only [ht, Bool.false_eq_true, if_false]

theorem decision_equal {f : Fields} {s : WorkerState} {a b : String} (he : f.event = .equal a b) :
    decision f s = (ScaWindowWorker.compare f s).1 := by
  unfold decision; rw [he]; rfl

theorem decision_less {f : Fields} {s : WorkerState} {a b : String} (he : f.event = .less a b) :
    decision f s = (ScaWindowWorker.compare f s).2 := by
  unfold decision; rw [he]; rfl

theorem decision_available {f : Fields} {s : WorkerState} {h : String}
    (he : f.event = .available h) : decision f s = s.availableAt f.dataLeft := by
  unfold decision; rw [he]; rfl

theorem decision_symbols {f : Fields} {s : WorkerState} {a b : String}
    (he : f.event = .symbols a b) :
    decision f s = decide ((s.readAt f.dataLeft).1 = (s.readAt f.dataRight).1) := by
  unfold decision; rw [he]; rfl

/-- The record `effect_eq` hands to `finish`. -/
def preFinish (spec : WorkerSpec) (f : Fields) (s : WorkerState) : WorkerState :=
  { execute f true (checks spec f true s) with
    data := s.data.mapIdx fun j p =>
      if j < spec.readers.registers then (cellStep f true (f.dataSource.map fun k => s.data.getD k 0)
        (f.dataSource.map fun k => s.reverse.getD k false) s.text.length j p
        (s.reverse.getD j false)).1 else p,
    reverse := s.reverse.mapIdx fun j r =>
      if j < spec.readers.registers then (cellStep f true (f.dataSource.map fun k => s.data.getD k 0)
        (f.dataSource.map fun k => s.reverse.getD k false) s.text.length j (s.data.getD j 0) r).2.1
      else r,
    fault := (checks spec f true s).fault ||
      (List.range spec.readers.registers).any fun j => (cellOf f s j).2.2 }

theorem effect_eq' (spec : WorkerSpec) (f : Fields) (s : WorkerState) :
    effect spec f true s = finish spec f true (preFinish spec f s) :=
  effect_eq spec f s

theorem preFinish_proj (spec : WorkerSpec) (f : Fields) (s : WorkerState) :
    (preFinish spec f s).fault = ((checks spec f true s).fault ||
      (List.range spec.readers.registers).any fun j => (cellOf f s j).2.2) ∧
    (preFinish spec f s).output = (checks spec f true s).output ∧
    (preFinish spec f s).flags = s.flags ∧ (preFinish spec f s).mode = s.mode := by
  obtain ⟨-, -, -, hfl, hmo, -, hout⟩ := execute_data f true (checks spec f true s)
  obtain ⟨-, -, -, hfl', hmo'⟩ := checks_data spec f true s
  exact ⟨rfl, hout, hfl.trans hfl', hmo.trans hmo'⟩

theorem effect_fault_matcher (spec : WorkerSpec) (hflags : spec.isFlags = false) (f : Fields)
    (s : WorkerState) :
    (effect spec f true s).fault = (((checks spec f true s).fault ||
      (List.range spec.readers.registers).any fun j => (cellOf f s j).2.2) ||
        isOp f.event "halt") ∧
    (effect spec f true s).output = (checks spec f true s).output := by
  rw [effect_eq']
  obtain ⟨hfault, -, -⟩ := finish_matcher spec hflags f true (preFinish spec f s)
  obtain ⟨hpf, hpo, -, -⟩ := preFinish_proj spec f s
  refine ⟨by rw [hfault, hpf]; rfl, ?_⟩
  rw [(finish_data spec f true _).2.2.2, hpo]

/-! ## The matcher correspondence -/

/-- The coroutine matcher worker `t` encodes the logical matcher `v`, for the live readers `L`,
with the pattern boundary at `W` (the `end` at `start`). -/
structure MatchRel (spec : WorkerSpec) (L : List String) (W : Nat) (t : CoState) (v : HVM) :
    Prop where
  ctl : t.ctl = v.ctl
  dataLen : t.body.data.length = spec.readers.registers
  revLen : t.body.reverse.length = spec.readers.registers
  frontier : W ≤ t.body.text.length
  word : v.word = matchWord t.body.text W
  patternSize : v.patternSize = W
  heads : PosAgree spec ⟨0, W⟩ L t.body v.pos

theorem MatchRel.mono {spec : WorkerSpec} {L L' : List String} {W : Nat} {t : CoState} {v : HVM}
    (hrel : MatchRel spec L W t v) (hsub : ∀ h ∈ L', h ∈ L) : MatchRel spec L' W t v :=
  { hrel with heads := fun h hL' i hc => hrel.heads h (hsub h hL') i hc }

theorem MatchRel.len_eq {spec : WorkerSpec} {L : List String} {W : Nat} {t : CoState} {v : HVM}
    (hrel : MatchRel spec L W t v) : v.len = t.body.text.length := by
  unfold HVM.len; rw [hrel.word, matchWord_length hrel.frontier]

/-- The side conditions the matcher program is expected to keep (`SCA_GS_MAPPING.md` §0): read
heads on their side, `available` on forward heads, reversed heads stay in the pattern, and
`match B` on the live forward head `B`. -/
structure MatchSide (spec : WorkerSpec) (W : Nat) (L A : List String) (s : WorkerState)
    (pos : String → ℤ) (e : Event) : Prop where
  reads : ∀ a b, e = .symbols a b → ∀ h, (h = a ∨ h = b) → ∀ i, color spec h = some i →
    OnSide W (s.reverse.getD i false) (pos h)
  available : ∀ h, e = .available h → ∀ i, color spec h = some i → s.reverse.getD i false = false
  moves : ∀ ms, e = .move ms → ∀ h ∈ A, ∀ i, color spec h = some i →
    s.reverse.getD i false = true → pos h + sumDelta ms h ≤ W
  matchB : ∀ h, e = .«match» h →
    "B" ∈ L ∧ ∃ i, color spec "B" = some i ∧ s.reverse.getD i false = false

/-- The worker's extra `match` requirement (`ScaWindowWorker.lean:141-146`): `B` has not reached
the arrival frontier. `StreamingMatcher.step` has no such check. -/
def matchLate (v : HVM) : Event → Bool
  | .«match» _ => decide (v.pos "B" < v.len)
  | _ => false

theorem isOp_ne {e : Event} {op : String} (h : e.op ≠ op) : isOp e op = false := by
  unfold isOp; simpa using h

/-- A forward live register is available exactly when its logical cell has arrived. -/
theorem availableAt_matcher {s : WorkerState} {W i : Nat} {x : ℤ}
    (hp : (s.data.getD i 0 : ℤ) = (⟨0, W⟩ : Emb).phys (s.reverse.getD i false) x)
    (hfwd : s.reverse.getD i false = false) :
    s.availableAt (some i) = decide (x < s.text.length) := by
  rw [hfwd] at hp
  simp only [Emb.phys, Bool.false_eq_true, if_false, zero_add] at hp
  simp only [WorkerState.availableAt]
  exact decide_eq_decide.mpr ⟨fun h' => by omega, fun h' => by omega⟩

/-- **The matcher step.** When `StreamingMatcher.step` succeeds (`stepMatch v = some v'`), one
active step of the coroutine worker lands in the same coroutine control, keeps the encoding (for
the live-after readers `A`), raises no fault except the worker's `match` timing check, and
raises its `output` bit exactly on `match` (whose value `stepMatch` appends to `outputs`). -/
theorem match_step {spec : WorkerSpec} {cw : CoWorker} {L A : List String} {W : Nat}
    {t : CoState} {v v' : HVM} {c : Config} {e : Event}
    (hspec : cw.spec = spec) (hflags : spec.isFlags = false) (htests : cw.tests = matchTests)
    (hrel : MatchRel spec L W t v) (hctl : t.ctl = .pending c e)
    (hdec : Decodes spec A e (cw.rom t.ctl)) (hcov : Covers e L A) (hproper : Proper spec A)
    (hcolored : Colored spec L) (hbound : ColorsBound spec)
    (hnotBlind : ReadersNotBlind spec blind)
    (hregs : RegsValue (cw.rom t.ctl) t.body v.pos e)
    (hside : MatchSide spec W L A t.body v.pos e)
    (hstep : stepMatch v = some v') :
    MatchRel spec A W (cw.step true t) v' ∧
      (cw.step true t).body.fault = (t.body.fault || matchLate v e) ∧
      (cw.step true t).body.output = (t.body.output || isOp e "match") := by
  have hvctl : v.ctl = .pending c e := hrel.ctl ▸ hctl
  obtain ⟨hok, hv'⟩ := stepMatch_some hvctl hstep
  subst hv'
  have hbody : (cw.step true t).body = effect spec (cw.rom t.ctl) true t.body := by
    rw [CoWorker.step_body, hspec]
  have hctl' : (cw.step true t).ctl =
      t.ctl.resume matchTests (decision (cw.rom t.ctl) t.body) := by
    rw [CoWorker.step_ctl, htests]; rfl
  generalize cw.rom t.ctl = f at hdec hregs hbody hctl'
  have hev := hdec.event
  have hlen := hrel.len_eq
  have hfit : MoveFits spec ⟨0, W⟩ A t.body v.pos e := by
    intro ms hms h hA i hc hne
    subst hms
    obtain ⟨π', hπ'⟩ := Option.isSome_iff_exists.mp hok
    obtain ⟨hform, hrange⟩ := moveSeq_some hπ'
    obtain ⟨m, hm, hmh⟩ := exists_of_sumDelta_ne hne
    have hin := hrange m hm (hmh ▸ hnotBlind h i hc)
    rw [hmh, hform, hlen] at hin
    simp only at hin
    have hfr := hrel.frontier
    unfold Emb.phys
    cases hr : t.body.reverse.getD i false
    · simp only [Bool.false_eq_true, if_false, zero_add]; exact hin
    · have hle := hside.moves ms rfl h hA i hc hr
      simp only [if_true]
      constructor <;> omega
  obtain ⟨hposA, hdl, hrl, htext, hnoMove, -⟩ :=
    posAgree_after hdec hcov hproper hcolored hbound hrel.dataLen hrel.revLen hrel.heads hfit
  have hdecide : matchTests.contains e.op = true → decision f t.body = matchDecision v e := by
    intro htest
    cases e with
    | equal a b =>
      rw [decision_equal hev, compare_of_regsValue hregs (Or.inl rfl)]; rfl
    | less a b =>
      rw [decision_less hev, compare_of_regsValue hregs (Or.inr (Or.inl rfl))]; rfl
    | available h =>
      rw [decision_available hev, hdec.available h rfl]
      obtain ⟨i, hc⟩ := hcolored h (hcov.avail h rfl)
      rw [hc, availableAt_matcher (hrel.heads h (hcov.avail h rfl) i hc)
        (hside.available h rfl i hc), ← hlen]
      rfl
    | symbols a b =>
      rw [decision_symbols hev]
      obtain ⟨hdl', hdr'⟩ := hdec.symbols a b rfl
      obtain ⟨haL, hbL⟩ := hcov.reads a b rfl
      obtain ⟨ia, hca⟩ := hcolored a haL
      obtain ⟨ib, hcb⟩ := hcolored b hbL
      rw [hdl', hdr', hca, hcb,
        readAt_matcher hrel.frontier (hrel.heads a haL ia hca)
          (hside.reads a b rfl a (Or.inl rfl) ia hca),
        readAt_matcher hrel.frontier (hrel.heads b hbL ib hcb)
          (hside.reads a b rfl b (Or.inr rfl) ib hcb)]
      obtain ⟨⟨ha0, hal⟩, ⟨hb0, hbl⟩⟩ := hok
      rw [hlen] at hal hbl
      rw [if_pos ⟨ha0, hal⟩, if_pos ⟨hb0, hbl⟩, ← hrel.word]
      rfl
    | move ms => simp only [Event.op] at htest; exact absurd htest (by decide)
    | copy t' s' => simp only [Event.op] at htest; exact absurd htest (by decide)
    | assertEqual a b => simp only [Event.op] at htest; exact absurd htest (by decide)
    | border h => simp only [Event.op] at htest; exact absurd htest (by decide)
    | flag b => simp only [Event.op] at htest; exact absurd htest (by decide)
    | «match» h => simp only [Event.op] at htest; exact absurd htest (by decide)
    | halt => simp only [Event.op] at htest; exact absurd htest (by decide)
  have hfault : (effect spec f true t.body).fault = (t.body.fault || matchLate v e) := by
    rw [(effect_fault_matcher spec hflags f t.body).1,
      (checks_fault_matcher spec hflags f true t.body).1, hnoMove, hev]
    cases e with
    | symbols a b =>
      obtain ⟨hdl', hdr'⟩ := hdec.symbols a b rfl
      obtain ⟨haL, hbL⟩ := hcov.reads a b rfl
      obtain ⟨ia, hca⟩ := hcolored a haL
      obtain ⟨ib, hcb⟩ := hcolored b hbL
      rw [hdl', hdr', hca, hcb,
        readAt_matcher hrel.frontier (hrel.heads a haL ia hca)
          (hside.reads a b rfl a (Or.inl rfl) ia hca),
        readAt_matcher hrel.frontier (hrel.heads b hbL ib hcb)
          (hside.reads a b rfl b (Or.inr rfl) ib hcb)]
      obtain ⟨⟨ha0, hal⟩, ⟨hb0, hbl⟩⟩ := hok
      rw [hlen] at hal hbl
      rw [if_pos ⟨ha0, hal⟩, if_pos ⟨hb0, hbl⟩]
      simp [isOp, Event.op, matchLate]
    | assertEqual a b =>
      rw [compare_of_regsValue hregs (Or.inr (Or.inr rfl))]
      have heq : v.pos a = v.pos b := hok
      simp [isOp, Event.op, matchLate, heq]
    | «match» h =>
      obtain ⟨hBL, i, hc, hfwd⟩ := hside.matchB h rfl
      have hB : lookupFirst "B" spec.readers.colors = some i := hc
      rw [hB, availableAt_matcher (hrel.heads "B" hBL i hc) hfwd, ← hlen]
      simp [isOp, Event.op, matchLate]
    | move ms => simp [isOp, Event.op, matchLate]
    | copy t' s' => simp [isOp, Event.op, matchLate]
    | equal a b => simp [isOp, Event.op, matchLate]
    | less a b => simp [isOp, Event.op, matchLate]
    | available h => simp [isOp, Event.op, matchLate]
    | border h => exact hok.elim
    | flag b => exact hok.elim
    | halt => exact hok.elim
  have hout : (effect spec f true t.body).output = (t.body.output || isOp e "match") := by
    rw [(effect_fault_matcher spec hflags f t.body).2,
      (checks_fault_matcher spec hflags f true t.body).2, hev, Bool.true_and]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hrel.patternSize, ?_⟩, by rw [hbody]; exact hfault,
    by rw [hbody]; exact hout⟩
  · rw [hctl', hrel.ctl]
    show v.ctl.resume matchTests (decision f t.body) = v.ctl.resume matchTests (matchDecision v e)
    rw [hvctl]
    exact resume_congr hdecide
  · rw [hbody]; exact hdl
  · rw [hbody]; exact hrl
  · rw [hbody, htext]; exact hrel.frontier
  · show v.word = matchWord (cw.step true t).body.text W
    rw [hbody, htext]; exact hrel.word
  · rw [hbody]; exact hposA

/-- **Matcher faults ↔ `AssertionError`s**, on the queries both sides check: when a `symbols`
or `assert_equal` makes `StreamingMatcher.step` raise, the worker faults. -/
theorem match_step_error {spec : WorkerSpec} {cw : CoWorker} {L A : List String} {W : Nat}
    {t : CoState} {v : HVM} {c : Config} {e : Event}
    (hspec : cw.spec = spec) (hflags : spec.isFlags = false)
    (hrel : MatchRel spec L W t v) (hctl : t.ctl = .pending c e)
    (hdec : Decodes spec A e (cw.rom t.ctl)) (hcov : Covers e L A)
    (hcolored : Colored spec L)
    (hregs : RegsValue (cw.rom t.ctl) t.body v.pos e)
    (hside : MatchSide spec W L A t.body v.pos e)
    (hquery : (∃ a b, e = .symbols a b) ∨ (∃ a b, e = .assertEqual a b))
    (hstep : stepMatch v = none) :
    (cw.step true t).body.fault = true := by
  have hvctl : v.ctl = .pending c e := hrel.ctl ▸ hctl
  have hnok := stepMatch_none hvctl hstep
  rw [CoWorker.step_body, hspec]
  generalize cw.rom t.ctl = f at hdec hregs
  have hev := hdec.event
  have hlen := hrel.len_eq
  rw [(effect_fault_matcher spec hflags f t.body).1,
    (checks_fault_matcher spec hflags f true t.body).1, hev]
  rcases hquery with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
  · obtain ⟨hdl', hdr'⟩ := hdec.symbols a b rfl
    obtain ⟨haL, hbL⟩ := hcov.reads a b rfl
    obtain ⟨ia, hca⟩ := hcolored a haL
    obtain ⟨ib, hcb⟩ := hcolored b hbL
    rw [hdl', hdr', hca, hcb,
      readAt_matcher hrel.frontier (hrel.heads a haL ia hca)
        (hside.reads a b rfl a (Or.inl rfl) ia hca),
      readAt_matcher hrel.frontier (hrel.heads b hbL ib hcb)
        (hside.reads a b rfl b (Or.inr rfl) ib hcb)]
    simp only [matchOk, HVM.inRange, hlen] at hnok
    by_cases ha : 0 ≤ v.pos a ∧ v.pos a < t.body.text.length
    · have hb : ¬ (0 ≤ v.pos b ∧ v.pos b < t.body.text.length) := fun hb => hnok ⟨ha, hb⟩
      rw [if_neg hb]
      simp [isOp, Event.op]
    · rw [if_neg ha]
      simp [isOp, Event.op]
  · rw [compare_of_regsValue hregs (Or.inr (Or.inr rfl))]
    have hne : v.pos a ≠ v.pos b := hnok
    simp [isOp, Event.op, hne]

/-- A returned coroutine is the table's halting sink: the logical matcher raises (`halt` is an
unknown instruction to `StreamingMatcher.step`), and the worker faults. -/
theorem match_step_returned {spec : WorkerSpec} {cw : CoWorker} {t : CoState} {v : HVM}
    {val : Value} (hspec : cw.spec = spec) (hflags : spec.isFlags = false)
    (hctl : t.ctl = .returned val) (hvctl : v.ctl = t.ctl)
    (hhalt : (cw.rom t.ctl).event = .halt) :
    stepMatch v = none ∧ (cw.step true t).ctl = t.ctl ∧ (cw.step true t).body.fault = true := by
  refine ⟨by unfold stepMatch; rw [hvctl, hctl], ?_, ?_⟩
  · rw [CoWorker.step_ctl, hctl]; rfl
  · rw [CoWorker.step_body, hspec, (effect_fault_matcher spec hflags _ t.body).1, hhalt]
    simp [isOp, Event.op]

/-! ## Arrivals, waiting, start -/

theorem arrive_proj (w : Worker) (c : Fin 2) (s : WorkerState) :
    (ScaWindowWorker.arrive w c s).data = s.data ∧ (ScaWindowWorker.arrive w c s).reverse = s.reverse ∧
      (ScaWindowWorker.arrive w c s).text = s.text ++ [c] ∧
      (ScaWindowWorker.arrive w c s).output = false ∧
      (ScaWindowWorker.arrive w c s).flags = s.flags ∧ (ScaWindowWorker.arrive w c s).mode = s.mode := by
  unfold ScaWindowWorker.arrive; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem matchWord_append {text : List (Fin 2)} {W : Nat} (hW : W ≤ text.length) (c : Fin 2) :
    matchWord (text ++ [c]) W = matchWord text W ++ [c] := by
  unfold matchWord
  rw [List.take_append_of_le_length hW, List.drop_append_of_le_length hW, List.append_assoc]

/-- **`arrive` is `append`.** A letter arriving at the worker is `StreamingMatcher.append` of
the same letter; the per-tick `output` bit restarts. (`OriginalEnd` is not a matcher reader.) -/
theorem match_arrive {spec : WorkerSpec} {cw : CoWorker} {L : List String} {W : Nat}
    {t : CoState} {v : HVM} (hrel : MatchRel spec L W t v) (hOriginalEnd : "OriginalEnd" ∉ L)
    (c : Fin 2) :
    MatchRel spec L W (cw.arrive c t) (v.append c) ∧ (cw.arrive c t).body.output = false := by
  obtain ⟨hd, hr, ht, hout, -, -⟩ := arrive_proj (specWorker cw.spec) c t.body
  have hbody : (cw.arrive c t).body = ScaWindowWorker.arrive (specWorker cw.spec) c t.body := rfl
  refine ⟨⟨hrel.ctl, ?_, ?_, ?_, ?_, hrel.patternSize, ?_⟩, by rw [hbody, hout]⟩
  · rw [hbody, hd]; exact hrel.dataLen
  · rw [hbody, hr]; exact hrel.revLen
  · rw [hbody, ht, List.length_append]; have := hrel.frontier; omega
  · show v.word ++ [c] = matchWord (cw.arrive c t).body.text W
    rw [hbody, ht, matchWord_append hrel.frontier, hrel.word]
  · intro h hL i hc
    have hne : h ≠ "OriginalEnd" := fun heq => hOriginalEnd (heq ▸ hL)
    rw [hbody, hd, hr]
    simp only [HVM.append, Function.update_of_ne hne]
    exact hrel.heads h hL i hc

/-- **`waiting`.** At a pending `available h` on a live forward register, the logical matcher
waits exactly when the worker's test answers `false` (and the coroutine spins). -/
theorem match_waiting_iff {spec : WorkerSpec} {cw : CoWorker} {L A : List String} {W : Nat}
    {t : CoState} {v : HVM} {c : Config} {h : String}
    (hrel : MatchRel spec L W t v) (hctl : t.ctl = .pending c (.available h))
    (hdec : Decodes spec A (.available h) (cw.rom t.ctl)) (hcov : Covers (.available h) L A)
    (hcolored : Colored spec L)
    (hfwd : ∀ i, color spec h = some i → t.body.reverse.getD i false = false) :
    v.waiting ↔ decision (cw.rom t.ctl) t.body = false := by
  obtain ⟨i, hc⟩ := hcolored h (hcov.avail h rfl)
  rw [decision_available hdec.event, hdec.available h rfl, hc,
    availableAt_matcher (hrel.heads h (hcov.avail h rfl) i hc) (hfwd i hc), ← hrel.len_eq]
  have hvctl : v.ctl = .pending c (.available h) := hrel.ctl ▸ hctl
  constructor
  · rintro ⟨c', h', hctl', hle⟩
    rw [hvctl] at hctl'
    cases hctl'
    simpa using hle
  · intro hdec'
    exact ⟨c, h, hvctl, by simpa using hdec'⟩

/-- The fields `initializeValues` leaves alone. -/
theorem initializeValues_frame (spec : WorkerSpec) (mapping : List (Pair × Option (DistKey × Int)))
    (enabled : Bool) (s : WorkerState) :
    (initializeValues spec mapping enabled s).data = s.data ∧
      (initializeValues spec mapping enabled s).reverse = s.reverse ∧
      (initializeValues spec mapping enabled s).text = s.text ∧
      (initializeValues spec mapping enabled s).flags = s.flags ∧
      (initializeValues spec mapping enabled s).«end» = s.«end» := by
  unfold initializeValues
  cases enabled
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp only [if_true]
    induction mapping generalizing s with
    | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | cons a rest ih =>
      simp only [List.foldl_cons]
      obtain ⟨pair, value⟩ := a
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih (match lookupFirst pair spec.distances.colors with
        | none => s
        | some i =>
          match value with
          | none => s.setDist (.reg i) 0
          | some (k, sign) => s.setDist (.reg i) (if sign = -1 then -s.getDist k else s.getDist k))
      refine ⟨h1.trans ?_, h2.trans ?_, h3.trans ?_, h4.trans ?_, h5.trans ?_⟩ <;>
        (split <;> [rfl; (split <;> rfl)])

theorem rawStart_some {spec : WorkerSpec} {head : String} {i : Nat} (hc : color spec head = some i)
    (src : Nat) (r : Bool) (s : WorkerState) :
    rawStart (specWorker spec) head src r true s =
      { s with data := s.data.set i src, reverse := s.reverse.set i r } := by
  unfold rawStart
  have hl : lookupFirst head (specWorker spec).spec.readers.colors = some i := hc
  rw [hl]; rfl

theorem getD_set_self {α : Type} {l : List α} {i : Nat} (hi : i < l.length) (x d : α) :
    (l.set i x).getD i d = x := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_set_ne {α : Type} (l : List α) {i j : Nat} (hne : i ≠ j) (x d : α) :
    (l.set i x).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, hne]

/-- **`start` is `StreamingMatcher(pattern)`.** Started when all `W = end` letters have arrived,
the worker encodes the logical matcher on `x = (text.take W).reverse` (Origin reversed at `W`,
Tail forward at `W`), for any start-live set inside `{Origin, Tail}`. -/
theorem match_start {spec : WorkerSpec} {cw : CoWorker} {t : CoState} {L : List String}
    {io it : Nat} (hspec : cw.spec = spec) (hflags : spec.isFlags = false)
    (hdlen : t.body.data.length = spec.readers.registers)
    (hrlen : t.body.reverse.length = spec.readers.registers)
    (hend : t.body.end = t.body.text.length)
    (horigin : color spec "Origin" = some io) (htail : color spec "Tail" = some it)
    (hne : io ≠ it) (hio : io < spec.readers.registers) (hit : it < spec.readers.registers)
    (hstartLive : ∀ h ∈ L, h = "Origin" ∨ h = "Tail") :
    MatchRel spec L t.body.end (cw.start true t)
      (matchInitial (t.body.text.take t.body.end).reverse (cw.start true t).ctl) := by
  have hbody : (cw.start true t).body =
      { startBody (specWorker spec) true t.body with mode := .run } := by
    unfold CoWorker.start; rw [hspec]; rfl
  have hstart : startBody (specWorker spec) true t.body =
      initializeValues spec matcherStartMapping true
        (rawStart (specWorker spec) "Tail" t.body.end false true
          (rawStart (specWorker spec) "Origin" t.body.end true true t.body)) := by
    unfold startBody
    have hf : (specWorker spec).spec.isFlags = false := hflags
    simp only [hf, Bool.false_eq_true, if_false]
    rfl
  rw [rawStart_some horigin, rawStart_some htail] at hstart
  obtain ⟨hd, hr, ht, -, -⟩ := initializeValues_frame spec matcherStartMapping true
    { { t.body with data := t.body.data.set io t.body.end,
                    reverse := t.body.reverse.set io true } with
      data := (t.body.data.set io t.body.end).set it t.body.end,
      reverse := (t.body.reverse.set io true).set it false }
  have hdata : (cw.start true t).body.data = (t.body.data.set io t.body.end).set it t.body.end := by
    rw [hbody]; show (startBody (specWorker spec) true t.body).data = _; rw [hstart, hd]
  have hrev : (cw.start true t).body.reverse = (t.body.reverse.set io true).set it false := by
    rw [hbody]; show (startBody (specWorker spec) true t.body).reverse = _; rw [hstart, hr]
  have htext : (cw.start true t).body.text = t.body.text := by
    rw [hbody]; show (startBody (specWorker spec) true t.body).text = _; rw [hstart, ht]
  have hW : t.body.end ≤ t.body.text.length := hend.le
  have hpatLen : ((t.body.text.take t.body.end).reverse.length : ℤ) = t.body.end := by
    simp [List.length_take]; omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdata]; simp [hdlen]
  · rw [hrev]; simp [hrlen]
  · rw [htext]; exact hW
  · show (t.body.text.take t.body.end).reverse = matchWord (cw.start true t).body.text t.body.end
    rw [htext]; unfold matchWord; rw [hend, List.drop_length, List.append_nil]
  · exact hpatLen
  · intro h hL i hc
    rw [hdata, hrev]
    rcases hstartLive h hL with rfl | rfl
    · rw [horigin] at hc; cases hc
      rw [getD_set_ne _ (Ne.symm hne), getD_set_self (by omega),
        getD_set_ne _ (Ne.symm hne), getD_set_self (by omega)]
      simp [Emb.phys, matchInitial]
    · rw [htail] at hc; cases hc
      rw [getD_set_self (by simp only [List.length_set]; omega),
        getD_set_self (by simp only [List.length_set]; omega)]
      simp only [Emb.phys, Bool.false_eq_true, if_false, zero_add, matchInitial]
      simp only [true_or, if_true]
      exact hpatLen.symm

/-! ## The flags VM, case by case -/

/-- The decision `DualFlagVM.step` takes on a test. -/
def flagsDecision (v : HVM) : Event → Bool
  | .equal a b => decide (v.pos a = v.pos b)
  | .less a b => decide (v.pos a < v.pos b)
  | .symbols a b => decide (v.view a = v.view b)
  | _ => false

/-- The instructions `DualFlagVM.step` executes without an exception. -/
def flagsOk (v : HVM) : Event → Prop
  | .move ms => (moveSeq flagBlind v.len ms v.pos).isSome
  | .copy _ _ | .equal _ _ | .less _ _ | .flag _ | .border _ => True
  | .symbols a b => a ∉ flagBlind ∧ b ∉ flagBlind ∧ v.inRange a ∧ v.inRange b
  | _ => False

/-- The bit `DualFlagVM.step` appends to `flags`. -/
def flagOut : Event → List Bool
  | .flag b => [b]
  | _ => []

/-- The value `HeadVM.step` appends to `outputs` (`border`). -/
def borderOut (v : HVM) : Event → List ℤ
  | .border h => [v.pos h]
  | _ => []

/-- `DualFlagVM.step` without an exception, in closed form. -/
theorem stepFlags_some {v v' : HVM} {c : Config} {e : Event} (hctl : v.ctl = .pending c e)
    (hstep : stepFlags v = some v') :
    flagsOk v e ∧ v' = { v with
      pos := movePos e v.pos,
      rev := moveRev e v.rev,
      flags := v.flags ++ flagOut e,
      outputs := v.outputs ++ borderOut v e,
      ctl := v.ctl.resume tests (flagsDecision v e) } := by
  unfold stepFlags at hstep
  rw [hctl] at hstep ⊢
  cases e with
  | move ms =>
    simp only [Option.map_eq_some_iff] at hstep
    obtain ⟨π', hms, rfl⟩ := hstep
    refine ⟨by simp [flagsOk, hms], ?_⟩
    rw [(moveSeq_some hms).1]
    simp [movePos, moveRev, flagOut, borderOut, flagsDecision]
  | symbols a b =>
    simp only at hstep
    split at hstep
    · next hin =>
      simp only [Option.some.injEq] at hstep
      subst hstep
      exact ⟨hin, by simp [movePos, moveRev, flagOut, borderOut, flagsDecision]⟩
    · cases hstep
  | copy t src =>
    simp only [Option.some.injEq] at hstep
    subst hstep
    exact ⟨trivial, by simp [movePos, moveRev, flagOut, borderOut, flagsDecision]⟩
  | equal a b =>
    simp only [Option.some.injEq] at hstep
    subst hstep
    exact ⟨trivial, by simp [movePos, moveRev, flagOut, borderOut, flagsDecision]⟩
  | less a b =>
    simp only [Option.some.injEq] at hstep
    subst hstep
    exact ⟨trivial, by simp [movePos, moveRev, flagOut, borderOut, flagsDecision]⟩
  | flag b =>
    simp only [Option.some.injEq] at hstep
    subst hstep
    exact ⟨trivial, by simp [movePos, moveRev, flagOut, borderOut, flagsDecision]⟩
  | border h =>
    simp only [Option.some.injEq] at hstep
    subst hstep
    exact ⟨trivial, by simp [movePos, moveRev, flagOut, borderOut, flagsDecision]⟩
  | available h => cases hstep
  | assertEqual a b => cases hstep
  | «match» h => cases hstep
  | halt => cases hstep

/-- The segment `y = (text.drop begin).take b` the flag worker runs on. -/
def flagWord (text : List (Fin 2)) (bg b : Nat) : List (Fin 2) := (text.drop bg).take b

theorem flagWord_length {text : List (Fin 2)} {bg b : Nat} (hfr : bg + b ≤ text.length) :
    (flagWord text bg b).length = b := by
  simp [flagWord, List.length_take, List.length_drop]; omega

theorem flagWord_get {text : List (Fin 2)} {bg b k : Nat} (hk : k < b) :
    (flagWord text bg b)[k]? = text[bg + k]? := by
  unfold flagWord; rw [List.getElem?_take, if_pos hk, List.getElem?_drop]

/-- A flag-worker register inside the segment reads `DualFlagVM`'s oriented view. -/
theorem readAt_flags {s : WorkerState} {bg b i : Nat} {x : ℤ} (hfr : bg + b ≤ s.text.length)
    (hp : (s.data.getD i 0 : ℤ) = (⟨bg, bg + b⟩ : Emb).phys (s.reverse.getD i false) x)
    (hx0 : 0 ≤ x) (hxb : x < b) :
    s.readAt (some i) =
      ((if s.reverse.getD i false then (flagWord s.text bg b)[((b : ℤ) - 1 - x).toNat]?
        else (flagWord s.text bg b)[x.toNat]?), true) := by
  unfold WorkerState.readAt
  simp only
  generalize s.reverse.getD i false = r at hp ⊢
  generalize s.data.getD i 0 = p at hp ⊢
  unfold Emb.phys at hp
  cases r
  · simp only [Bool.false_eq_true, if_false] at hp ⊢
    rw [if_pos (by omega), flagWord_get (by omega)]
    congr 2; omega
  · simp only [if_true] at hp ⊢
    rw [if_neg (by omega), if_pos (by omega), flagWord_get (by omega)]
    congr 2; omega

/-- The coroutine flag worker `t` encodes `DualFlagVM` `v` on the segment `[bg, bg + b)`, for the
live readers `L`. -/
structure FlagRel (spec : WorkerSpec) (L : List String) (bg b : Nat) (t : CoState) (v : HVM) :
    Prop where
  ctl : t.ctl = v.ctl
  dataLen : t.body.data.length = spec.readers.registers
  revLen : t.body.reverse.length = spec.readers.registers
  frontier : bg + b ≤ t.body.text.length
  word : v.word = flagWord t.body.text bg b
  heads : PosAgree spec ⟨bg, bg + b⟩ L t.body v.pos
  orient : RevAgree spec L t.body v.rev
  /-- The `FlagStack` (top first) is `DualFlagVM.flags` (append order) reversed. -/
  flags : t.body.flags = v.flags.reverse

theorem FlagRel.mono {spec : WorkerSpec} {L L' : List String} {bg b : Nat} {t : CoState}
    {v : HVM} (hrel : FlagRel spec L bg b t v) (hsub : ∀ h ∈ L', h ∈ L) :
    FlagRel spec L' bg b t v :=
  { hrel with heads := fun h hL' i hc => hrel.heads h (hsub h hL') i hc,
              orient := fun h hL' i hc => hrel.orient h (hsub h hL') i hc }

theorem FlagRel.len_eq {spec : WorkerSpec} {L : List String} {bg b : Nat} {t : CoState}
    {v : HVM} (hrel : FlagRel spec L bg b t v) : v.len = b := by
  unfold HVM.len; rw [hrel.word, flagWord_length hrel.frontier]

theorem effect_flags_proj (spec : WorkerSpec) (hflags : spec.isFlags = true) (f : Fields)
    (s : WorkerState) :
    (effect spec f true s).fault = ((checks spec f true s).fault ||
      (List.range spec.readers.registers).any fun j => (cellOf f s j).2.2) ∧
    (effect spec f true s).flags = (if isOp f.event "flag" then f.bit :: s.flags else s.flags) ∧
    (effect spec f true s).mode = (if isOp f.event "halt" then .done else s.mode) := by
  rw [effect_eq']
  obtain ⟨hfault, hfl, hmo⟩ := finish_flags spec hflags f true (preFinish spec f s)
  obtain ⟨hpf, -, hpfl, hpmo⟩ := preFinish_proj spec f s
  rw [hfault, hfl, hmo, hpf, hpfl, hpmo]
  simp only [Bool.true_and]
  exact ⟨trivial, trivial, trivial⟩

/-- **The flags step.** When `DualFlagVM.step` succeeds, one active step of the coroutine flag
worker lands in the same coroutine control, keeps the encoding (positions and orientations of
the live-after readers, the flag stack), and raises no fault. No side conditions are needed:
inside `[0, b]` both orientations are faithful. -/
theorem flags_step {spec : WorkerSpec} {cw : CoWorker} {L A : List String} {bg b : Nat}
    {t : CoState} {v v' : HVM} {c : Config} {e : Event}
    (hspec : cw.spec = spec) (hflags : spec.isFlags = true) (htests : cw.tests = tests)
    (hrel : FlagRel spec L bg b t v) (hctl : t.ctl = .pending c e)
    (hdec : Decodes spec A e (cw.rom t.ctl)) (hcov : Covers e L A) (hproper : Proper spec A)
    (hcolored : Colored spec L) (hbound : ColorsBound spec)
    (hnotBlind : ReadersNotBlind spec flagBlind)
    (hregs : RegsValue (cw.rom t.ctl) t.body v.pos e)
    (hstep : stepFlags v = some v') :
    FlagRel spec A bg b (cw.step true t) v' ∧ (cw.step true t).body.fault = t.body.fault ∧
      (cw.step true t).body.mode = t.body.mode := by
  have hvctl : v.ctl = .pending c e := hrel.ctl ▸ hctl
  obtain ⟨hok, hv'⟩ := stepFlags_some hvctl hstep
  subst hv'
  have hbody : (cw.step true t).body = effect spec (cw.rom t.ctl) true t.body := by
    rw [CoWorker.step_body, hspec]
  have hctl' : (cw.step true t).ctl =
      t.ctl.resume tests (decision (cw.rom t.ctl) t.body) := by
    rw [CoWorker.step_ctl, htests]; rfl
  generalize cw.rom t.ctl = f at hdec hregs hbody hctl'
  have hev := hdec.event
  have hlen := hrel.len_eq
  have hfr := hrel.frontier
  have hfit : MoveFits spec ⟨bg, bg + b⟩ A t.body v.pos e := by
    intro ms hms h hA i hc hne
    subst hms
    obtain ⟨π', hπ'⟩ := Option.isSome_iff_exists.mp hok
    obtain ⟨hform, hrange⟩ := moveSeq_some hπ'
    obtain ⟨m, hm, hmh⟩ := exists_of_sumDelta_ne hne
    have hin := hrange m hm (hmh ▸ hnotBlind h i hc)
    rw [hmh, hform, hlen] at hin
    simp only at hin
    unfold Emb.phys
    cases t.body.reverse.getD i false
    · simp only [Bool.false_eq_true, if_false]; constructor <;> omega
    · simp only [if_true]; constructor <;> omega
  obtain ⟨hposA, hdl, hrl, htext, hnoMove, hrevA⟩ :=
    posAgree_after hdec hcov hproper hcolored hbound hrel.dataLen hrel.revLen hrel.heads hfit
  -- the reads of a symbol test are valid and are the oriented views
  have hread : ∀ a b', e = .symbols a b' → ∀ h, (h = a ∨ h = b') →
      (t.body.readAt (color spec h)).2 = true ∧ (t.body.readAt (color spec h)).1 = v.view h := by
    intro a b' he h hh
    subst he
    obtain ⟨-, -, hina, hinb⟩ := hok
    have hL : h ∈ L := by
      rcases hh with rfl | rfl
      · exact (hcov.reads _ _ rfl).1
      · exact (hcov.reads _ _ rfl).2
    have hin : v.inRange h := by rcases hh with rfl | rfl <;> assumption
    obtain ⟨i, hc⟩ := hcolored h hL
    obtain ⟨hx0, hxb⟩ := hin
    rw [hlen] at hxb
    rw [hc, readAt_flags hfr (hrel.heads h hL i hc) hx0 hxb]
    refine ⟨rfl, ?_⟩
    simp only [HVM.view, hrel.orient h hL i hc, hrel.word, hlen]
  have hdecide : tests.contains e.op = true → decision f t.body = flagsDecision v e := by
    intro htest
    cases e with
    | equal a b' =>
      rw [decision_equal hev, compare_of_regsValue hregs (Or.inl rfl)]; rfl
    | less a b' =>
      rw [decision_less hev, compare_of_regsValue hregs (Or.inr (Or.inl rfl))]; rfl
    | symbols a b' =>
      rw [decision_symbols hev]
      obtain ⟨hdl', hdr'⟩ := hdec.symbols a b' rfl
      rw [hdl', hdr', (hread a b' rfl a (Or.inl rfl)).2, (hread a b' rfl b' (Or.inr rfl)).2]
      rfl
    | move ms => simp only [Event.op] at htest; exact absurd htest (by decide)
    | copy t' s' => simp only [Event.op] at htest; exact absurd htest (by decide)
    | available h => simp only [Event.op] at htest; exact absurd htest (by decide)
    | assertEqual a b' => simp only [Event.op] at htest; exact absurd htest (by decide)
    | border h => simp only [Event.op] at htest; exact absurd htest (by decide)
    | flag b' => simp only [Event.op] at htest; exact absurd htest (by decide)
    | «match» h => simp only [Event.op] at htest; exact absurd htest (by decide)
    | halt => simp only [Event.op] at htest; exact absurd htest (by decide)
  obtain ⟨hfault, hflagsEq, hmode⟩ := effect_flags_proj spec hflags f t.body
  have hcheck : (checks spec f true t.body).fault = t.body.fault := by
    rw [(checks_fault_flags spec hflags f true t.body).1, hev]
    cases e with
    | symbols a b' =>
      obtain ⟨hdl', hdr'⟩ := hdec.symbols a b' rfl
      rw [hdl', hdr', (hread a b' rfl a (Or.inl rfl)).1, (hread a b' rfl b' (Or.inr rfl)).1]
      simp [isOp, Event.op]
    | assertEqual a b' => exact hok.elim
    | move ms => simp [isOp, Event.op]
    | copy t' s' => simp [isOp, Event.op]
    | equal a b' => simp [isOp, Event.op]
    | less a b' => simp [isOp, Event.op]
    | available h => simp [isOp, Event.op]
    | border h => simp [isOp, Event.op]
    | flag b' => simp [isOp, Event.op]
    | «match» h => simp [isOp, Event.op]
    | halt => simp [isOp, Event.op]
  have hnothalt : isOp f.event "halt" = false := by
    rw [hev]; cases e <;> first | rfl | exact hok.elim
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hctl', hrel.ctl]
    show v.ctl.resume tests (decision f t.body) = v.ctl.resume tests (flagsDecision v e)
    rw [hvctl]
    exact resume_congr hdecide
  · rw [hbody]; exact hdl
  · rw [hbody]; exact hrl
  · rw [hbody, htext]; exact hfr
  · show v.word = flagWord (cw.step true t).body.text bg b
    rw [hbody, htext]; exact hrel.word
  · rw [hbody]; exact hposA
  · rw [hbody]; exact hrevA v.rev hrel.orient
  · rw [hbody, hflagsEq, hrel.flags, hev]
    show _ = (v.flags ++ flagOut e).reverse
    cases e with
    | flag bit =>
      rw [hdec.bit bit rfl]
      simp [isOp, Event.op, flagOut]
    | _ => simp [isOp, Event.op, flagOut]
  · rw [hbody, hfault, hcheck, hnoMove, Bool.or_false]
  · rw [hbody, hmode, hnothalt]; rfl

/-- **Halting.** A returned coroutine is the halting sink: `DualFlagVM` is `done` (and must not
be stepped), and the worker's step there sets `mode := done`, changing nothing else that the
relation sees. -/
theorem flags_step_returned {spec : WorkerSpec} {cw : CoWorker} {L : List String} {bg b : Nat}
    {t : CoState} {v : HVM} {val : Value}
    (hspec : cw.spec = spec) (hflags : spec.isFlags = true)
    (hrel : FlagRel spec L bg b t v) (hctl : t.ctl = .returned val)
    (hdec : Decodes spec L .halt (cw.rom t.ctl)) (hproper : Proper spec L)
    (hcolored : Colored spec L) (hbound : ColorsBound spec) :
    v.flagsDone ∧ stepFlags v = none ∧ FlagRel spec L bg b (cw.step true t) v ∧
      (cw.step true t).body.mode = .done ∧ (cw.step true t).body.fault = t.body.fault := by
  have hvctl : v.ctl = .returned val := hrel.ctl ▸ hctl
  have hbody : (cw.step true t).body = effect spec (cw.rom t.ctl) true t.body := by
    rw [CoWorker.step_body, hspec]
  have hctl' : (cw.step true t).ctl = t.ctl := by
    rw [CoWorker.step_ctl, hctl]; rfl
  generalize cw.rom t.ctl = f at hdec hbody
  have hev := hdec.event
  have hcov : Covers .halt L L :=
    ⟨fun h hL _ => hL, fun _ _ he => (by cases he), fun _ _ he => (by cases he),
      fun _ he => (by cases he)⟩
  have hfit : MoveFits spec ⟨bg, bg + b⟩ L t.body v.pos .halt := fun _ he => by cases he
  obtain ⟨hposA, hdl, hrl, htext, hnoMove, hrevA⟩ :=
    posAgree_after hdec hcov hproper hcolored hbound hrel.dataLen hrel.revLen hrel.heads hfit
  obtain ⟨hfault, hflagsEq, hmode⟩ := effect_flags_proj spec hflags f t.body
  refine ⟨⟨val, hvctl⟩, by unfold stepFlags; rw [hvctl], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hctl']; exact hrel.ctl
  · rw [hbody]; exact hdl
  · rw [hbody]; exact hrl
  · rw [hbody, htext]; exact hrel.frontier
  · rw [hbody, htext]; exact hrel.word
  · rw [hbody]; exact hposA
  · rw [hbody]; exact hrevA v.rev hrel.orient
  · rw [hbody, hflagsEq, hev]; simp only [isOp, Event.op]; exact hrel.flags
  · rw [hbody, hmode, hev]; rfl
  · rw [hbody, hfault, (checks_fault_flags spec hflags f true t.body).1, hev, hnoMove]
    simp [isOp, Event.op]

/-- Arrivals during a flag batch do not touch `DualFlagVM`: the segment is already there. -/
theorem flags_arrive {spec : WorkerSpec} {cw : CoWorker} {L : List String} {bg b : Nat}
    {t : CoState} {v : HVM} (hrel : FlagRel spec L bg b t v) (c : Fin 2) :
    FlagRel spec L bg b (cw.arrive c t) v := by
  obtain ⟨hd, hr, ht, -, hfl, -⟩ := arrive_proj (specWorker cw.spec) c t.body
  have hbody : (cw.arrive c t).body = ScaWindowWorker.arrive (specWorker cw.spec) c t.body := rfl
  have hfr := hrel.frontier
  refine ⟨hrel.ctl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbody, hd]; exact hrel.dataLen
  · rw [hbody, hr]; exact hrel.revLen
  · rw [hbody, ht, List.length_append]; omega
  · rw [hbody, ht, hrel.word]
    unfold flagWord
    rw [List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by rw [List.length_drop]; omega)]
  · intro h hL i hc; rw [hbody, hd, hr]; exact hrel.heads h hL i hc
  · intro h hL i hc; rw [hbody, hr]; exact hrel.orient h hL i hc
  · rw [hbody, hfl]; exact hrel.flags

/-! ## The certified table worker supplies `Decodes` and `Covers` -/

theorem mem_union {x : String} : ∀ {xs ys : List String}, x ∈ union xs ys ↔ x ∈ xs ∨ x ∈ ys
  | xs, [] => by simp [union]
  | xs, y :: ys => by
    have ih := @mem_union x (if y ∈ xs then xs else xs ++ [y]) ys
    unfold union at ih ⊢
    rw [List.foldl_cons, ih]
    by_cases hy : y ∈ xs
    · simp only [hy, if_true, List.mem_cons]
      constructor
      · rintro (h | h); exact Or.inl h; exact Or.inr (Or.inr h)
      · rintro (h | rfl | h); exact Or.inl h; exact Or.inl hy; exact Or.inr h
    · simp only [hy, if_false, List.mem_append, List.mem_cons]
      tauto

theorem mem_successorsUnion_foldl {x : String} (before : Array (List String)) :
    ∀ (targets : List Nat) (acc : List String),
      x ∈ targets.foldl (fun live t => union live (before.getD t [])) acc ↔
        x ∈ acc ∨ ∃ t ∈ targets, x ∈ before.getD t []
  | [], acc => by simp
  | t :: ts, acc => by
    rw [List.foldl_cons, mem_successorsUnion_foldl before ts, mem_union]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

/-- The live-before set of a successor is inside the live-after set. -/
theorem live_sub_successorsUnion (before : Array (List String)) {targets : List Nat} {t : Nat}
    (ht : t ∈ targets) : ∀ x ∈ before.getD t [], x ∈ successorsUnion before targets := by
  intro x hx
  unfold successorsUnion
  rw [mem_successorsUnion_foldl]
  exact Or.inr ⟨t, ht, hx⟩

/-- `readerTransfer` of `A` inside `L` is `Covers`. -/
theorem covers_of_transfer {row : Row} {L A : List String}
    (hfix : ∀ x ∈ readerTransfer row A, x ∈ L) : Covers row.event L A := by
  obtain ⟨ev, targets⟩ := row
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h hA hnot
    apply hfix
    cases ev with
    | copy t s =>
      have hne := hnot t s rfl
      by_cases htA : t ∈ A
      · simp [readerTransfer, htA, mem_union, List.mem_filter, hA, hne]
      · simp [readerTransfer, htA, hA]
    | symbols l r => simp [readerTransfer, mem_union, hA]
    | available g => simp [readerTransfer, mem_union, hA]
    | _ => simpa [readerTransfer] using hA
  · intro t s he htA
    subst he
    apply hfix
    simp [readerTransfer, htA, mem_union]
  · intro a b he
    subst he
    exact ⟨hfix a (by simp [readerTransfer, mem_union]), hfix b (by simp [readerTransfer, mem_union])⟩
  · intro h he
    subst he
    exact hfix h (by simp [readerTransfer, mem_union])

theorem getD_map_range {α : Type} (n i : Nat) (g : Nat → α) (d : α) (hi : i < n) :
    ((List.range n).map g).getD i d = g i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

/-- The ROM row `fieldsAt` decodes its event against the live-after readers. -/
theorem decodes_fieldsAt (spec : WorkerSpec) (rb : Array (List String))
    (db : Array (List Pair)) (r : Nat) (row : Row) :
    Decodes spec (successorsUnion rb row.targets) row.event (fieldsAt spec rb db r row) := by
  obtain ⟨ev, targets⟩ := row
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b he; subst he; exact ⟨rfl, rfl⟩
  · intro h he; subst he; rfl
  · intro t s he htA; subst he
    simp only [fieldsAt, htA, if_true]
    exact ⟨rfl, rfl⟩
  · intro t s he htA; subst he
    simp only [fieldsAt, htA, if_false]
  · intro ms he i hi; subst he
    simp only [fieldsAt]
    rw [getD_map_range _ _ _ _ hi]
    rfl
  · intro hnm i hi
    cases ev with
    | move ms => exact absurd rfl (hnm ms)
    | _ => simp only [fieldsAt]; rw [getD_map_range _ _ _ _ hi]
  · intro b he; subst he; rfl

/-- A pending row has successors, and the worker jumps to one of them. -/
theorem next_mem_targets {spec : WorkerSpec} {r : Nat} {row : Row}
    (hrow : spec.program.code[r]? = some row) (hne : row.targets ≠ []) (d : Bool) :
    (if d then ((Worker.ofSpec spec).fields r).yes else ((Worker.ofSpec spec).fields r).no) ∈
      row.targets := by
  obtain ⟨t0, rest, hcons⟩ := List.exists_cons_of_ne_nil hne
  have hno : ((Worker.ofSpec spec).fields r).no ∈ row.targets := by
    rw [fields_ofSpec spec hrow, fieldsAt_no, hcons]; simp
  have hyes : ((Worker.ofSpec spec).fields r).yes ∈ row.targets := by
    rw [fields_ofSpec spec hrow, fieldsAt_yes, hcons]
    cases rest with
    | nil => split <;> simp
    | cons t1 rest => split <;> simp
  cases d
  · exact hno
  · exact hyes

/-- **The certified matcher step.** The coroutine worker certified against the matcher table,
at a pending control simulated by row `r`, with the encoding for the reader-live set of `r`:
if `StreamingMatcher.step` succeeds, the worker steps to a control simulated by a successor row
`r'` and keeps the encoding for the reader-live set of `r'`. The table-level hypotheses are
finite checks on the table (`hfix`: `liveReaders` is a post-fixpoint at `r`; `hproper`,
`hcolored`, `hbound`, `hnotBlind`: the coloring); `hregs` is the distance-register invariant;
`hside` is the matcher's side discipline. -/
theorem match_step_certified {spec : WorkerSpec} {cw : CoWorker} {vs : List ScaGsCert.Entry}
    {r W : Nat} {t : CoState} {v v' : HVM} {c : Config} {e : Event} {row : Row}
    (hcw : Certified spec cw vs) (hflags : spec.isFlags = false)
    (htests : cw.tests = matchTests)
    (hsim : ScaGsCert.Sim vs c e r) (hctl : t.ctl = .pending c e)
    (hrow : spec.program.code[r]? = some row)
    (hrel : MatchRel spec ((liveReaders spec).getD r []) W t v)
    (hfix : ∀ x ∈ readerTransfer row (successorsUnion (liveReaders spec) row.targets),
      x ∈ (liveReaders spec).getD r [])
    (hproper : Proper spec (successorsUnion (liveReaders spec) row.targets))
    (hcolored : Colored spec ((liveReaders spec).getD r []))
    (hbound : ColorsBound spec) (hnotBlind : ReadersNotBlind spec blind)
    (hregs : RegsValue (cw.rom t.ctl) t.body v.pos e)
    (hside : MatchSide spec W ((liveReaders spec).getD r [])
      (successorsUnion (liveReaders spec) row.targets) t.body v.pos e)
    (hstep : stepMatch v = some v') :
    ∃ r', SimCtl vs (cw.step true t).ctl r' ∧
      MatchRel spec ((liveReaders spec).getD r' []) W (cw.step true t) v' ∧
      (cw.step true t).body.fault = (t.body.fault || matchLate v e) ∧
      (cw.step true t).body.output = (t.body.output || isOp e "match") := by
  obtain ⟨row', hrow', hevent, hlen, -⟩ := ScaGsCert.sim_step hcw.certOk hsim
  rw [hrow] at hrow'
  cases hrow'
  have hrom : cw.rom t.ctl = fieldsAt spec (liveReaders spec) (liveDistances spec) r row := by
    rw [hctl, hcw.romAtPending c e r hsim, fields_ofSpec spec hrow]
  have hdec : Decodes spec (successorsUnion (liveReaders spec) row.targets) e (cw.rom t.ctl) := by
    rw [hrom, ← hevent]; exact decodes_fieldsAt _ _ _ _ _
  have hcov : Covers e ((liveReaders spec).getD r []) (successorsUnion (liveReaders spec) row.targets) := by
    rw [← hevent]; exact covers_of_transfer hfix
  obtain ⟨hmrel, hfault, hout⟩ := match_step hcw.specEq hflags htests hrel hctl hdec hcov hproper
    hcolored hbound hnotBlind hregs hside hstep
  have hne : row.targets ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    unfold responsesFor at hlen
    split at hlen <;> simp at hlen
  refine ⟨_, ?_, hmrel.mono (live_sub_successorsUnion _ (next_mem_targets hrow hne
    (decision (cw.rom t.ctl) t.body))), hfault, hout⟩
  rw [CoWorker.step_ctl, hctl]
  exact resume_sim hcw.certOk hcw.coroutineTestsAreTableTests hsim _

/-- **The certified flags step**, as `match_step_certified`. -/
theorem flags_step_certified {spec : WorkerSpec} {cw : CoWorker} {vs : List ScaGsCert.Entry}
    {r bg b : Nat} {t : CoState} {v v' : HVM} {c : Config} {e : Event} {row : Row}
    (hcw : Certified spec cw vs) (hflags : spec.isFlags = true)
    (htests : cw.tests = tests)
    (hsim : ScaGsCert.Sim vs c e r) (hctl : t.ctl = .pending c e)
    (hrow : spec.program.code[r]? = some row)
    (hrel : FlagRel spec ((liveReaders spec).getD r []) bg b t v)
    (hfix : ∀ x ∈ readerTransfer row (successorsUnion (liveReaders spec) row.targets),
      x ∈ (liveReaders spec).getD r [])
    (hproper : Proper spec (successorsUnion (liveReaders spec) row.targets))
    (hcolored : Colored spec ((liveReaders spec).getD r []))
    (hbound : ColorsBound spec) (hnotBlind : ReadersNotBlind spec flagBlind)
    (hregs : RegsValue (cw.rom t.ctl) t.body v.pos e)
    (hstep : stepFlags v = some v') :
    ∃ r', SimCtl vs (cw.step true t).ctl r' ∧
      FlagRel spec ((liveReaders spec).getD r' []) bg b (cw.step true t) v' ∧
      (cw.step true t).body.fault = t.body.fault ∧ (cw.step true t).body.mode = t.body.mode := by
  obtain ⟨row', hrow', hevent, hlen, -⟩ := ScaGsCert.sim_step hcw.certOk hsim
  rw [hrow] at hrow'
  cases hrow'
  have hrom : cw.rom t.ctl = fieldsAt spec (liveReaders spec) (liveDistances spec) r row := by
    rw [hctl, hcw.romAtPending c e r hsim, fields_ofSpec spec hrow]
  have hdec : Decodes spec (successorsUnion (liveReaders spec) row.targets) e (cw.rom t.ctl) := by
    rw [hrom, ← hevent]; exact decodes_fieldsAt _ _ _ _ _
  have hcov : Covers e ((liveReaders spec).getD r []) (successorsUnion (liveReaders spec) row.targets) := by
    rw [← hevent]; exact covers_of_transfer hfix
  obtain ⟨hfrel, hfault, hmode⟩ := flags_step hcw.specEq hflags htests hrel hctl hdec hcov
    hproper hcolored hbound hnotBlind hregs hstep
  have hne : row.targets ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    unfold responsesFor at hlen
    split at hlen <;> simp at hlen
  refine ⟨_, ?_, hfrel.mono (live_sub_successorsUnion _ (next_mem_targets hrow hne
    (decision (cw.rom t.ctl) t.body))), hfault, hmode⟩
  rw [CoWorker.step_ctl, hctl]
  exact resume_sim hcw.certOk hcw.coroutineTestsAreTableTests hsim _

/-- **`start` is `DualFlagVM(y, lower, upper)`.** Started on the segment `[begin, end)`, the flag
worker encodes `DualFlagVM` on `y = (text.drop begin).take (end - begin)`: Origin forward at
`begin` (logical `0`), TextOrigin reversed at `end` (logical `0`), OriginalEnd reversed at
`begin` (logical `b`), for any start-live set inside those three. -/
theorem flags_start {spec : WorkerSpec} {cw : CoWorker} {t : CoState} {L : List String}
    {io it ie : Nat} (hspec : cw.spec = spec) (hflags : spec.isFlags = true)
    (hdlen : t.body.data.length = spec.readers.registers)
    (hrlen : t.body.reverse.length = spec.readers.registers)
    (hbe : t.body.begin ≤ t.body.end) (hend : t.body.end ≤ t.body.text.length)
    (horigin : color spec "Origin" = some io) (htextOrigin : color spec "TextOrigin" = some it)
    (horiginalEnd : color spec "OriginalEnd" = some ie)
    (hot : io ≠ it) (hoe : io ≠ ie) (hte : it ≠ ie)
    (hio : io < spec.readers.registers) (hit : it < spec.readers.registers)
    (hie : ie < spec.readers.registers)
    (hstartLive : ∀ h ∈ L, h = "Origin" ∨ h = "TextOrigin" ∨ h = "OriginalEnd")
    (lower upper : ℤ) :
    FlagRel spec L t.body.begin (t.body.end - t.body.begin) (cw.start true t)
      (flagsInitialVM (flagWord t.body.text t.body.begin (t.body.end - t.body.begin)) lower upper
        (cw.start true t).ctl) := by
  have hbody : (cw.start true t).body =
      { startBody (specWorker spec) true t.body with mode := .run } := by
    unfold CoWorker.start; rw [hspec]; rfl
  set s0 : WorkerState := { t.body with fault := t.body.fault || decide (t.body.mode = .run) }
    with hs0
  have hstart : startBody (specWorker spec) true t.body =
      { initializeValues spec flagsStartMapping true
          (rawStart (specWorker spec) "OriginalEnd" t.body.begin true true
            (rawStart (specWorker spec) "TextOrigin" t.body.end true true
              (rawStart (specWorker spec) "Origin" t.body.begin false true s0))) with
        flags := [] } := by
    unfold startBody
    have hf : (specWorker spec).spec.isFlags = true := hflags
    simp only [hf, if_true, Bool.true_and]
    rfl
  rw [rawStart_some horigin, rawStart_some htextOrigin, rawStart_some horiginalEnd] at hstart
  obtain ⟨hd, hr, ht, -, -⟩ := initializeValues_frame spec flagsStartMapping true
    { { { s0 with data := s0.data.set io t.body.begin, reverse := s0.reverse.set io false } with
          data := (s0.data.set io t.body.begin).set it t.body.end,
          reverse := (s0.reverse.set io false).set it true } with
      data := ((s0.data.set io t.body.begin).set it t.body.end).set ie t.body.begin,
      reverse := ((s0.reverse.set io false).set it true).set ie true }
  have hdata : (cw.start true t).body.data =
      ((t.body.data.set io t.body.begin).set it t.body.end).set ie t.body.begin := by
    rw [hbody]; show (startBody (specWorker spec) true t.body).data = _; rw [hstart]
    exact hd
  have hrev : (cw.start true t).body.reverse =
      ((t.body.reverse.set io false).set it true).set ie true := by
    rw [hbody]; show (startBody (specWorker spec) true t.body).reverse = _; rw [hstart]
    exact hr
  have htext : (cw.start true t).body.text = t.body.text := by
    rw [hbody]; show (startBody (specWorker spec) true t.body).text = _; rw [hstart]
    exact ht
  have hflagsNil : (cw.start true t).body.flags = [] := by
    rw [hbody]; show (startBody (specWorker spec) true t.body).flags = _; rw [hstart]
  have hfr : t.body.begin + (t.body.end - t.body.begin) ≤ t.body.text.length := by omega
  have hwlen := flagWord_length hfr
  have hdl1 : (t.body.data.set io t.body.begin).length = spec.readers.registers := by
    rw [List.length_set]; exact hdlen
  have hdl2 : ((t.body.data.set io t.body.begin).set it t.body.end).length =
      spec.readers.registers := by rw [List.length_set]; exact hdl1
  have hrl1 : (t.body.reverse.set io false).length = spec.readers.registers := by
    rw [List.length_set]; exact hrlen
  have hrl2 : ((t.body.reverse.set io false).set it true).length = spec.readers.registers := by
    rw [List.length_set]; exact hrl1
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdata, List.length_set]; exact hdl2
  · rw [hrev, List.length_set]; exact hrl2
  · rw [htext]; exact hfr
  · rw [htext]; rfl
  · intro h hL i hc
    rw [hdata, hrev]
    rcases hstartLive h hL with rfl | rfl | rfl
    · rw [horigin] at hc; cases hc
      rw [getD_set_ne _ (Ne.symm hoe), getD_set_ne _ (Ne.symm hot), getD_set_self (by omega),
        getD_set_ne _ (Ne.symm hoe), getD_set_ne _ (Ne.symm hot), getD_set_self (by omega)]
      simp [Emb.phys, flagsInitialVM]
    · rw [htextOrigin] at hc; cases hc
      rw [getD_set_ne _ (Ne.symm hte), getD_set_self (by omega),
        getD_set_ne _ (Ne.symm hte), getD_set_self (by omega)]
      simp only [Emb.phys, if_true, flagsInitialVM]
      simp only [show ("TextOrigin" = "OriginalEnd") = False from by decide,
        show ("TextOrigin" = "Lower") = False from by decide,
        show ("TextOrigin" = "Upper") = False from by decide, if_false]
      omega
    · rw [horiginalEnd] at hc; cases hc
      rw [getD_set_self (by omega), getD_set_self (by omega)]
      simp only [Emb.phys, if_true, flagsInitialVM, hwlen]
      omega
  · intro h hL i hc
    rw [hrev]
    rcases hstartLive h hL with rfl | rfl | rfl
    · rw [horigin] at hc; cases hc
      rw [getD_set_ne _ (Ne.symm hoe), getD_set_ne _ (Ne.symm hot), getD_set_self (by omega)]
      simp only [flagsInitialVM]; decide
    · rw [htextOrigin] at hc; cases hc
      rw [getD_set_ne _ (Ne.symm hte), getD_set_self (by omega)]
      simp only [flagsInitialVM]; decide
    · rw [horiginalEnd] at hc; cases hc
      rw [getD_set_self (by omega)]
      simp only [flagsInitialVM]; decide
  · rw [hflagsNil]; rfl

end PalPeg.ScaHeadVM
