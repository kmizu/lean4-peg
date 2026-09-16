import PalPeg.LocalCounter

/-!
# K-local refinement, piece 2: eagerly mirrored counters

`PalPeg.LocalCounter` realizes one logical `Counter` on one physical tape with
`push`/`pop`/`resetSeg` each costing a single `STape.applyAction`.  The Galil
scaffold, however, repeatedly *copies* a counter whose source keeps living:

* `Search.start` sets `work := lower` (the lower root is aliased, not consumed);
* a chain start sets `lag := radius` and `margin := radius`;
* and the debt is started at
  `initialDebt radius = ⟨radius.neg, radius.pos⟩`, i.e. at `negate radius`.

A copy of a unary counter costs `Θ(value)` if it is made on demand, which a
strictly real-time machine cannot afford.  This file implements the standard fix
— **eager mirroring** — at the level of `STape`s:

a source tape `src` is carried together with `k` mirror tapes `mir i`, and every
counter operation is applied to *all* `k + 1` tapes in the **same** micro-step.
`StructuredMachine` writes and moves on every tape at every micro-transition, so
this costs nothing extra: each tape still gets exactly one write and one move
(`pushAll_src`/`pushAll_mir` etc. are definitional).

"Making a copy" is then a purely *control-level* act: `take i` stops updating
mirror `i` and hands it over as an independent counter (`abs_take`).  Because the
sign bit lives in the finite control, the *negated* copy needed for `initialDebt`
is obtained by handing over the same tape with the opposite polarity bit
(`negate_via_pol`).

The detached slot has to be refilled before the next `take`.  §Rebuild does that
one mark per tick.  Note the obstruction recorded in `read_costs_value`: `val` is
head-relative, so a single head cannot *read* its own marks without lowering its
own value; the refill therefore consumes a second, sacrificial duplicate of the
source (`don`), which is what the mirror bank provides anyway.
-/

set_option autoImplicit false

namespace PalPeg.LocalMirror

open PalPeg.Program
open PalPeg.LocalCounter
open PegSeparation.RealTimeTM

/-! ## A source with `k` eagerly synchronized mirrors -/

/-- A counter tape together with `k` mirror tapes. -/
structure Mirrored (k : ℕ) where
  src : STape Seg
  mir : Fin k → STape Seg

variable {k : ℕ}

/-- The mirrors agree with the source *as counters*.  The tapes themselves may
differ arbitrarily below the live segment (abandoned garbage). -/
def Synced (m : Mirrored k) : Prop := ∀ i, val (m.mir i) = val m.src

/-- The shape invariant, held by every tape of the bank at the common value `v`.
It is what `pop` needs, and it implies `Synced`. -/
def Shaped (m : Mirrored k) (v : ℕ) : Prop :=
  SegCtr m.src v ∧ ∀ i, SegCtr (m.mir i) v

theorem Shaped.synced {m : Mirrored k} {v : ℕ} (h : Shaped m v) : Synced m := by
  intro i
  rw [val_eq_of_segCtr (h.2 i), val_eq_of_segCtr h.1]

/-! ## The three bank actions — one `applyAction` per tape -/

/-- `push` on every tape of the bank. -/
def pushAll (m : Mirrored k) : Mirrored k := ⟨push m.src, fun i => push (m.mir i)⟩

/-- `pop` on every tape of the bank. -/
def popAll (m : Mirrored k) : Mirrored k := ⟨pop m.src, fun i => pop (m.mir i)⟩

/-- `resetSeg` on every tape of the bank. -/
def resetAll (m : Mirrored k) : Mirrored k := ⟨resetSeg m.src, fun i => resetSeg (m.mir i)⟩

theorem pushAll_src (m : Mirrored k) :
    (pushAll m).src = STape.applyAction blank m.src (mark, Move.right) := rfl
theorem pushAll_mir (m : Mirrored k) (i : Fin k) :
    (pushAll m).mir i = STape.applyAction blank (m.mir i) (mark, Move.right) := rfl
theorem popAll_src (m : Mirrored k) :
    (popAll m).src = STape.applyAction blank m.src (blank, Move.left) := rfl
theorem popAll_mir (m : Mirrored k) (i : Fin k) :
    (popAll m).mir i = STape.applyAction blank (m.mir i) (blank, Move.left) := rfl
theorem resetAll_src (m : Mirrored k) :
    (resetAll m).src = STape.applyAction blank m.src (sep, Move.right) := rfl
theorem resetAll_mir (m : Mirrored k) (i : Fin k) :
    (resetAll m).mir i = STape.applyAction blank (m.mir i) (sep, Move.right) := rfl

/-! ### Preservation of the invariants -/

theorem shaped_pushAll {m : Mirrored k} {v : ℕ} (h : Shaped m v) :
    Shaped (pushAll m) (v + 1) :=
  ⟨segCtr_push h.1, fun i => segCtr_push (h.2 i)⟩

theorem shaped_popAll {m : Mirrored k} {v : ℕ} (h : Shaped m (v + 1)) :
    Shaped (popAll m) v :=
  ⟨segCtr_pop h.1, fun i => segCtr_pop (h.2 i)⟩

theorem shaped_resetAll (m : Mirrored k) : Shaped (resetAll m) 0 :=
  ⟨segCtr_reset _, fun _ => segCtr_reset _⟩

theorem synced_pushAll {m : Mirrored k} (h : Synced m) : Synced (pushAll m) := by
  intro i
  simp [pushAll, h i]

theorem synced_popAll {m : Mirrored k} {v : ℕ} (h : Shaped m (v + 1)) :
    Synced (popAll m) :=
  (shaped_popAll h).synced

theorem synced_resetAll (m : Mirrored k) : Synced (resetAll m) :=
  (shaped_resetAll m).synced

/-! ## Abstraction: a mirror *is* the source -/

/-- Since `absCtr` depends on the tape only through `val`, a synchronized mirror
abstracts to the very same logical `Counter` as the source. -/
theorem absCtr_mirror {m : Mirrored k} (h : Synced m) (i : Fin k) (b : Bool) :
    absCtr (m.mir i) b = absCtr m.src b := by
  simp [absCtr, h i]

/-- Detach mirror `i`: at the control level nothing happens to the tape, it
merely stops being included in `pushAll`/`popAll`/`resetAll`. -/
def take (m : Mirrored k) (i : Fin k) : STape Seg := m.mir i

/-- The detached tape is a copy of the source, made in zero extra time. -/
theorem abs_take {m : Mirrored k} (h : Synced m) (i : Fin k) (b : Bool) :
    absCtr (take m i) b = absCtr m.src b :=
  absCtr_mirror h i b

/-- Detaching the same tape with the opposite polarity bit yields the *negated*
copy.  With `absCtr m.src b = radius` this is exactly
`initialDebt radius = ⟨radius.neg, radius.pos⟩`. -/
theorem negate_via_pol {m : Mirrored k} (h : Synced m) (i : Fin k) (b : Bool) :
    absCtr (take m i) (!b) = negate (absCtr m.src b) := by
  rw [take, neg_flip, absCtr_mirror h i b]

/-- `negate` is literally the `initialDebt` swap, spelled out so that no further
import is needed. -/
theorem negate_eq (c : PalPeg.GalilScaffoldCounter.Counter) :
    negate c = ⟨c.neg, c.pos⟩ := rfl

/-! ## Refilling a detached slot

### The obstruction for a single head

`val` is *head-relative*: it is the mark-run at the top of `left`.  A
non-destructive read step (write back what is under the head, move left) therefore
lowers the counter's own value by one, exactly like `pop` — indeed `pop` and
`peek` are the same action. -/

/-- The cheapest possible "read" step: rewrite the focus and step left. -/
def stepLeft (t : STape Seg) : STape Seg := STape.applyAction blank t (t.focus, Move.left)

theorem pop_eq_peek : (pop : STape Seg → STape Seg) = peek := rfl

/-- **Obstruction.**  Walking the head one cell down the stored segment costs one
unit of the *stored value*, whether or not the cell is rewritten.  Hence a single
head cannot scan its own marks while remaining a valid counter, and a rebuild job
cannot read the live source: it must consume a sacrificial duplicate. -/
theorem read_costs_value {t : STape Seg} {v : ℕ} (h : SegCtr t (v + 1)) :
    val (stepLeft t) = v ∧ val (pop t) = v := by
  have hv : val t = v + 1 := val_eq_of_segCtr h
  refine ⟨?_, val_pop hv⟩
  obtain ⟨g, hg⟩ := h
  have hL : t.left = mark :: (List.replicate v mark ++ sep :: g) := by
    simpa [List.replicate_succ] using hg
  cases t with
  | mk L f R =>
      cases L with
      | nil => exact absurd hL (by simp)
      | cons a as =>
          cases hL
          simpa [val, stepLeft, STape.applyAction] using markRun_replicate_sep v g

/-! ### The two-head rebuild job

The donor `don` is a second synchronized duplicate of the source (another mirror,
detached at the same moment), which the job destroys; the source's head is never
moved, because the source does not occur in `Rebuild` at all.  Each tick performs
one `pop` on the donor and one `push` on the spare — one action per tape.  The
finite control needs no counter of its own: `pop = peek`, so the symbol the donor
lands on after its `pop` is the symbol just consumed, and it is `sep` exactly when
the donor was already empty (`rebuild_finished_sep`).  `pending` is proof-level
bookkeeping only. -/

/-- State of a refill job: a sacrificial duplicate, the spare being filled, and
the number of marks still to move. -/
structure Rebuild where
  don : STape Seg
  spare : STape Seg
  pending : ℕ

/-- Invariant of a refill job that is reconstructing the value `v`. -/
def RebuildInv (r : Rebuild) (v : ℕ) : Prop :=
  SegCtr r.don r.pending ∧ SegCtr r.spare (v - r.pending) ∧ r.pending ≤ v

/-- Start the job: blank out the spare with a fresh separator (one action). -/
def rebuildInit (don spare : STape Seg) (v : ℕ) : Rebuild :=
  ⟨don, resetSeg spare, v⟩

theorem rebuildInv_init {don spare : STape Seg} {v : ℕ} (h : SegCtr don v) :
    RebuildInv (rebuildInit don spare v) v :=
  ⟨h, by simpa [rebuildInit] using segCtr_reset spare, le_rfl⟩

/-- One tick: move one mark from the donor to the spare. -/
def rebuildStep (r : Rebuild) : Rebuild :=
  ⟨pop r.don, push r.spare, r.pending - 1⟩

theorem rebuildStep_don (r : Rebuild) :
    (rebuildStep r).don = STape.applyAction blank r.don (blank, Move.left) := rfl
theorem rebuildStep_spare (r : Rebuild) :
    (rebuildStep r).spare = STape.applyAction blank r.spare (mark, Move.right) := rfl

theorem rebuildInv_step {r : Rebuild} {v p : ℕ} (h : RebuildInv r v)
    (hp : r.pending = p + 1) : RebuildInv (rebuildStep r) v := by
  obtain ⟨hd, hs, hle⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simpa [rebuildStep, hp] using segCtr_pop (hp ▸ hd)
  · have hgrow : SegCtr (push r.spare) (v - (p + 1) + 1) := segCtr_push (hp ▸ hs)
    have harith : v - (p + 1) + 1 = v - p := by omega
    simpa [rebuildStep, hp, harith] using hgrow
  · simp only [rebuildStep, hp]
    omega

/-- Run the job for `n` ticks. -/
def rebuildRun : ℕ → Rebuild → Rebuild
  | 0, r => r
  | n + 1, r => rebuildRun n (rebuildStep r)

theorem rebuildRun_pending (n : ℕ) (r : Rebuild) :
    (rebuildRun n r).pending = r.pending - n := by
  induction n generalizing r with
  | zero => simp [rebuildRun]
  | succ n ih => simp [rebuildRun, ih, rebuildStep]; omega

/-- **Rebuild.**  After `val don = v` ticks the spare holds the value `v` in
proper counter shape, i.e. it is again a synchronized copy of the source. -/
theorem rebuild_done {r : Rebuild} {v : ℕ} (h : RebuildInv r v) (hp : r.pending = v) :
    SegCtr (rebuildRun v r).spare v ∧ (rebuildRun v r).pending = 0 := by
  have key : ∀ n (r : Rebuild), RebuildInv r v → r.pending = n →
      RebuildInv (rebuildRun n r) v := by
    intro n
    induction n with
    | zero => intro r hr _; simpa [rebuildRun] using hr
    | succ n ih =>
        intro r hr hrp
        refine ih _ (rebuildInv_step hr hrp) ?_
        simp [rebuildStep, hrp]
  have hinv := key v r h hp
  have hz : (rebuildRun v r).pending = 0 := by
    rw [rebuildRun_pending, hp]; omega
  refine ⟨?_, hz⟩
  have := hinv.2.1
  rwa [hz, Nat.sub_zero] at this

/-- …and therefore abstracts to the same logical `Counter` as the source. -/
theorem absCtr_rebuild {r : Rebuild} {t : STape Seg} {v : ℕ} (h : RebuildInv r v)
    (hp : r.pending = v) (ht : SegCtr t v) (b : Bool) :
    absCtr (rebuildRun v r).spare b = absCtr t b := by
  have h1 := val_eq_of_segCtr (rebuild_done h hp).1
  have h2 := val_eq_of_segCtr ht
  simp [absCtr, h1, h2]

/-- Termination signal: the donor's `pop` doubles as the zero test, because
`pop = peek`.  It shows `sep` exactly when the donor was already empty. -/
theorem rebuild_finished_sep {r : Rebuild} {v : ℕ} (h : RebuildInv r v)
    (hp : r.pending = 0) : (pop r.don).focus = sep := by
  have hd : SegCtr r.don 0 := hp ▸ h.1
  rw [pop_eq_peek]
  exact (peek_focus_sep hd).2 rfl

/-- Re-attaching a rebuilt spare: the bank is shaped again at the common value. -/
theorem shaped_attach {m : Mirrored k} {v : ℕ} (hsrc : SegCtr m.src v)
    (hmir : ∀ i, SegCtr (m.mir i) v) {s : STape Seg} (hs : SegCtr s v) (j : Fin k) :
    Shaped ⟨m.src, Function.update m.mir j s⟩ v := by
  refine ⟨hsrc, fun i => ?_⟩
  by_cases hij : i = j
  · subst hij; simpa using hs
  · simpa [Function.update_of_ne hij] using hmir i

#print axioms Shaped.synced
#print axioms shaped_pushAll
#print axioms shaped_popAll
#print axioms shaped_resetAll
#print axioms synced_pushAll
#print axioms synced_popAll
#print axioms synced_resetAll
#print axioms absCtr_mirror
#print axioms abs_take
#print axioms negate_via_pol
#print axioms read_costs_value
#print axioms rebuildInv_init
#print axioms rebuildInv_step
#print axioms rebuild_done
#print axioms absCtr_rebuild
#print axioms rebuild_finished_sep
#print axioms shaped_attach

end PalPeg.LocalMirror
