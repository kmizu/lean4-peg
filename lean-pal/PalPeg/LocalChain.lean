import PalPeg.GalilChainEncode
import PalPeg.LocalState
import PalPeg.LocalCounter
import PalPeg.LocalMirror
import PalPeg.LocalInputView
import PalPeg.GalilBranchInvariants

/-!
# 局所化計画, piece 7: the chain component, locally realized (`ChainL`)

`PalPeg.LocalState` assembles the `K`-local realization `GalilVML` of the Galil
scaffold VM and leaves exactly **one** component abstract:

```
  /-- (e) the chain view, still abstract. -/
  chain : ChainVM
```

This file removes that last abstraction.  `GalilChainEncode` already shows the
chain is finitely tape-encodable (`encodeChain`, eight tapes plus a finite
control `chainCtl`); what was missing is that every `ChainStep` / `ChainMatched`
constructor is realizable in **`O(1)` single-tape actions**, i.e. that no chain
transition hides a whole-counter copy, a whole-tape wipe, or a head copy.

## The local state

`ChainL` carries, in the shape suggested by `encodeChain`:

* `tag`, `phase`, `forward`, `broken` — the finite control (`chainCtl`);
* `verifier : InputView` — the chain's verifier head, as a `LocalInputView`
  cursor owning its own maintained copy of the input, with `vpending` the
  arrivals not yet delivered to it;
* `walkerV : InputView` — the copy walker of the `copy` phase;
* `period : GalilScaffoldChainPeriod.Tape` — the period tape, already a zipper;
  `GalilChainEncode.periodTape` is its injective `STape Sym2` reading, so its
  three primitives (`write`, `moveLeft`, `moveRight`) are genuine tape actions;
* `answer : GalilScaffoldTape.Tape` — **the DP answer tape.**  In the abstract
  model `chainStart` is handed `vq.dp.config.tapes 11`, i.e. the chain *aliases*
  the DP's answer tape.  The local model makes that explicit: the chain **owns
  tape 11's head during the copy phase**, which is sound because the DP is
  terminal (`.found`) exactly then and never moves that head again.  So the
  answer is a field here, moved by `copyBit`, rather than a pointer into
  `dpBuf`;
* `tape : CtrL → STape Seg` and `pol : CtrL → Bool` — the six counters
  (`lag margin h distance boundary last`) as segmented unary tapes
  (`LocalCounter`), one tape each, the sign bit in the finite control;
* `spare : STape Seg` — one extra physical tape, kept eagerly synchronized with
  `distance` (`LocalMirror`'s technique at bank size one).

## The one genuine non-locality: `alias(last, boundary)`

`GalilScaffoldChainConsume.consume` performs, at a FRONT/TAIL boundary event,

```
  last     := boundary        -- whole-counter copy, source dies
  boundary := inc distance    -- whole-counter copy, source survives
```

two `Θ(value)` copies in one step.  They are realized here by the
**mirror/role technique** of `LocalMirror` / `LocalRoles`:

* `last := boundary` — the source *dies*, so it is a pure **role move**: the
  physical tape that was `boundary` is renamed `last`;
* `boundary := inc distance` — the source *survives*, so it is a **detached
  mirror**: `spare` is pushed in lockstep with `distance` (one `applyAction` per
  tape, which a `StructuredMachine` micro-step affords for free) and is simply
  renamed `boundary` at the event (`LocalMirror.take`);
* the tape freed by the first move (the old `last`) becomes the new `spare`,
  **stale**, and has to be rebuilt before the next boundary event.

So a boundary event is the 3-cycle `rotPerm` on the seven physical slots and
costs **zero** tape actions beyond the single `push` on `distance`/`spare`.
The rebuild obligation is *stated, not discharged*: `Refilled` and
`refill_of_rebuild` reduce it to `LocalMirror.rebuild_done`, and every consume
lemma below takes `SpareSynced` as a hypothesis.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.LocalChain

open PalPeg.Program
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldInputHead (PlaceHead Head)
open PalPeg.GalilScaffoldPlace (Place)
open PalPeg.GalilScaffoldCounter (Counter)
open PalPeg.LocalCounter (Seg)
open PalPeg.LocalInputView (InputView absHead)
open PalPeg.LocalState (absPlace placeLetters)

/-! ## 1. The finite control -/

/-- The six logical counters of the chain. -/
inductive CtrL
  | lag | margin | h | distance | boundary | last
  deriving DecidableEq, Fintype

/-- The constructor tag of `ChainVM`. -/
inductive TagL
  | idle | copy | back | watch | broken
  deriving DecidableEq, Fintype

/-- The physical counter slots: one per role, plus the spare that mirrors
`distance`. -/
abbrev SlotL : Type := CtrL ⊕ Unit

instance : Fintype SlotL := inferInstance
instance : DecidableEq SlotL := inferInstance

/-! ## 2. The local chain state -/

/-- The `K`-local realization of `ChainVM`. -/
structure ChainL where
  /-- Constructor tag (finite control). -/
  tag : TagL
  /-- The chain's verifier head, owning its own copy of the input. -/
  verifier : InputView
  /-- Arrivals not yet delivered to the verifier view. -/
  vpending : List (Fin 2)
  /-- The copy walker of the `copy` phase. -/
  walkerV : InputView
  /-- The period tape. -/
  period : GalilScaffoldChainPeriod.Tape
  /-- The DP answer tape, owned by the chain during `copy`. -/
  answer : GalilScaffoldTape.Tape
  /-- The six counter tapes. -/
  tape : CtrL → STape Seg
  /-- Their sign bits, in the finite control. -/
  pol : CtrL → Bool
  /-- The eagerly synchronized mirror of `distance`. -/
  spare : STape Seg
  /-- The consume phase. -/
  phase : Fin 5
  /-- The consume direction. -/
  forward : Bool
  /-- The consume break flag. -/
  broken : Bool

/-- The physical tape sitting in a slot. -/
def slot (x : ChainL) : SlotL → STape Seg
  | .inl k => x.tape k
  | .inr _ => x.spare

/-! ## 3. Abstraction -/

/-- The logical value of a counter role. -/
def absC (x : ChainL) (k : CtrL) : Counter := LocalCounter.absCtr (x.tape k) (x.pol k)

/-- The abstract verifier head. -/
def absVer (x : ChainL) : PlaceHead := absHead x.verifier x.vpending

/-- The abstract consume control. -/
def absCons (x : ChainL) : GalilScaffoldChainConsume.State :=
  ⟨x.period, absC x .distance, absC x .boundary, absC x .last, x.phase, x.forward, x.broken⟩

/-- The abstract verifier machine. -/
def absMach (x : ChainL) : GalilScaffoldChainVerifier.State := ⟨absVer x, absCons x⟩

/-- The abstract watch state. -/
def absWatch (x : ChainL) : GalilScaffoldChainWatch.State :=
  ⟨absMach x, absC x .lag, absC x .margin⟩

/-- **The abstraction map onto `ChainVM`.** -/
def absChain (x : ChainL) : ChainVM :=
  match x.tag with
  | .idle => .idle
  | .copy =>
      .copy x.answer (absC x .h) (absPlace x.walkerV) x.period (absC x .lag) (absC x .margin)
        (absVer x)
  | .back => .back x.period (absC x .h) (absC x .lag) (absC x .margin) (absVer x)
  | .watch => .watch (absWatch x)
  | .broken => .broken (absWatch x)

/-! ### Well-definedness

`absChain` is total and reads only `tag`, the cursors, the period/answer tapes
and the `tape`/`pol` bundle — never the `spare`, never a rebuild job.  So the
background mirror maintenance is invisible at the abstract level. -/

/-- The spare is invisible to `absChain`. -/
theorem absChain_spare_irrelevant (x : ChainL) (t : STape Seg) :
    absChain { x with spare := t } = absChain x := rfl

/-- The numeric tag `absChain` produces. -/
def tagCode : TagL → Fin 5
  | .idle => 0 | .copy => 1 | .back => 2 | .watch => 3 | .broken => 4

theorem tagCode_injective : Function.Injective tagCode := by decide

/-- `absChain` lands on the constructor named by `tag`. -/
theorem absChain_tag (x : ChainL) :
    PalPeg.GalilChainEncode.chainTag (absChain x) = tagCode x.tag := by
  cases h : x.tag <;> simp [absChain, h, PalPeg.GalilChainEncode.chainTag, tagCode]

/-- **`absChain_injective`-style well-definedness, part 1:** the tag is recovered
from the image. -/
theorem absChain_tag_inj {x y : ChainL} (h : absChain x = absChain y) : x.tag = y.tag :=
  tagCode_injective (by rw [← absChain_tag, ← absChain_tag, h])

/-- **Part 2:** on `watch` the whole watch state is recovered. -/
theorem absChain_watch_inj {x y : ChainL} (hx : x.tag = .watch) (hy : y.tag = .watch)
    (h : absChain x = absChain y) : absWatch x = absWatch y := by
  rw [absChain, absChain, hx, hy] at h
  exact ChainVM.watch.inj h

/-- **Part 3:** on `copy` every abstract payload is recovered. -/
theorem absChain_copy_inj {x y : ChainL} (hx : x.tag = .copy) (hy : y.tag = .copy)
    (h : absChain x = absChain y) :
    x.answer = y.answer ∧ absC x .h = absC y .h ∧ absPlace x.walkerV = absPlace y.walkerV ∧
      x.period = y.period ∧ absC x .lag = absC y .lag ∧ absC x .margin = absC y .margin ∧
      absVer x = absVer y := by
  rw [absChain, absChain, hx, hy] at h
  injection h with h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- Every abstracted chain counter is canonical, with no hypothesis. -/
theorem absC_canonical (x : ChainL) (k : CtrL) :
    GalilScaffoldCounter.Canonical (absC x k) := LocalCounter.absCtr_canonical _ _

/-! ## 4. Well-formedness of the bank and of the cursors -/

/-- The spare mirrors `distance` as a counter (`LocalMirror.Synced` at `k = 1`). -/
def SpareSynced (x : ChainL) : Prop :=
  LocalCounter.val x.spare = LocalCounter.val (x.tape .distance)

/-- The stronger, shape-level form: the spare is a *usable* counter tape holding
the current `distance`.  This is what a `take` needs and what the background
rebuild re-establishes. -/
def Refilled (x : ChainL) : Prop :=
  LocalCounter.SegCtr x.spare (LocalCounter.val (x.tape .distance))

theorem refilled_synced {x : ChainL} (h : Refilled x) : SpareSynced x :=
  LocalCounter.val_eq_of_segCtr h

/-- The verifier view's queue is Hood–Melville well formed. -/
def VerWF (x : ChainL) : Prop := LocalInputView.WF x.verifier

/-- **Timing hypothesis (arrivals).**  The verifier view has absorbed every
arrival before the chain consumes.  Without it the abstract
`GalilScaffoldChainVerifier.right`, which pulls from `incoming`, and the local
`LocalInputView.moveRight`, which does not, disagree. -/
def Fed (x : ChainL) : Prop := x.vpending = []

/-- The sentinel `none` is the unique leftmost cell of a cursor's copy: the head
sits on it exactly at position `0`. -/
def Anchored : Option (Fin 2) → List (Option (Fin 2)) → Prop
  | none, bs => bs = []
  | some _, [] => False
  | some _, b :: bs => Anchored b bs

/-- A cursor whose stored copy is anchored. -/
def ProperView (v : InputView) : Prop := Anchored v.focus v.back

/-! ## 5. Locality: at most `c₂` single-tape actions per chain transition -/

/-- The three `O(1)` actions of a segmented unary counter tape. -/
inductive CtrAct : STape Seg → STape Seg → Prop
  | push (t) : CtrAct t (LocalCounter.push t)
  | pop (t) : CtrAct t (LocalCounter.pop t)
  | resetSeg (t) : CtrAct t (LocalCounter.resetSeg t)

/-- The three primitive actions of the period tape. -/
inductive PerAct : GalilScaffoldChainPeriod.Tape → GalilScaffoldChainPeriod.Tape → Prop
  | write (t a) : PerAct t (GalilScaffoldChainPeriod.write t a)
  | moveLeft (t) : PerAct t (GalilScaffoldChainPeriod.moveLeft t)
  | moveRight (t) : PerAct t (GalilScaffoldChainPeriod.moveRight t)

/-- The three primitive actions of the DP answer tape. -/
inductive AnsAct : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape → Prop
  | write (t s) : AnsAct t (GalilScaffoldTape.write t s)
  | moveLeft (t) : AnsAct t (GalilScaffoldTape.moveLeft t)
  | moveRight (t) : AnsAct t (GalilScaffoldTape.moveRight t)

/-- The four `O(1)` actions of a `LocalInputView` cursor. -/
inductive ViewAct : InputView → InputView → Prop
  | arrive (a t) : ViewAct t (LocalInputView.arrive a t)
  | moveRight (t) : ViewAct t (LocalInputView.moveRight t)
  | moveLeft (t) : ViewAct t (LocalInputView.moveLeftV t)
  | reposition (target t) : ViewAct t (LocalInputView.repositionStep target t)

/-- "`b` is reachable from `a` by **at most** `n` actions of `R`". -/
inductive Acts {α : Type} (R : α → α → Prop) : ℕ → α → α → Prop
  | refl (n : ℕ) (a : α) : Acts R n a a
  | step {n : ℕ} {a b c : α} (h : R a b) (hr : Acts R n b c) : Acts R (n + 1) a c

theorem Acts.mono {α : Type} {R : α → α → Prop} {n m : ℕ} {a b : α}
    (h : Acts R n a b) (hnm : n ≤ m) : Acts R m a b := by
  induction h generalizing m with
  | refl n a => exact .refl m a
  | @step n a b c hr _ ih =>
      cases m with
      | zero => omega
      | succ m => exact .step hr (ih (by omega))

theorem Acts.one {α : Type} {R : α → α → Prop} {a b : α} (h : R a b) : Acts R 1 a b :=
  .step h (.refl 0 b)

theorem Acts.trans {α : Type} {R : α → α → Prop} {n m : ℕ} {a b c : α}
    (h1 : Acts R n a b) (h2 : Acts R m b c) : Acts R (n + m) a c := by
  induction h1 with
  | refl n a => exact h2.mono (by omega)
  | @step n a b' c' hr _ ih => exact (Acts.step hr (ih h2)).mono (by omega)

/-- **The locality budget of one chain transition.**  Four actions suffice: the
widest single-tape burst in the whole chain is `margin -= 4` of `stepCopy`
(`GalilScaffoldChainCredits.decFour`: four `pop`s on the margin tape); every
other tape receives at most two (`put` on the period tape = one move plus one
write). -/
def c₂ : ℕ := 4

/-- **Locality of a chain transition.**  Every physical counter slot undergoes at
most `c` actions *up to a renaming of the slots*: the renaming `σ` is the finite
control's role table, and it is what makes `last := boundary` and
`boundary := take spare` cost nothing. -/
def ChainLocal (c : ℕ) (x y : ChainL) : Prop :=
  (∃ σ : Equiv.Perm SlotL, ∀ s, Acts CtrAct c (slot x s) (slot y (σ s))) ∧
  Acts PerAct c x.period y.period ∧
  Acts AnsAct c x.answer y.answer ∧
  Acts ViewAct c x.verifier y.verifier ∧
  Acts ViewAct c x.walkerV y.walkerV

/-- A local chain step transformer. -/
def LocalStep (f : ChainL → ChainL) : Prop := ∀ x, ChainLocal c₂ x (f x)

theorem chainLocal_refl (c : ℕ) (x : ChainL) : ChainLocal c x x :=
  ⟨⟨Equiv.refl _, fun _ => Acts.refl _ _⟩, Acts.refl _ _, Acts.refl _ _,
    Acts.refl _ _, Acts.refl _ _⟩

/-! ## 6. Counter micro-operations -/

/-- Four `pop`s: the local realization of `GalilScaffoldChainCredits.decFour`. -/
def pop4 (t : STape Seg) : STape Seg :=
  LocalCounter.pop (LocalCounter.pop (LocalCounter.pop (LocalCounter.pop t)))

theorem acts_pop4 (t : STape Seg) : Acts CtrAct 4 t (pop4 t) :=
  .step (.pop _) (.step (.pop _) (.step (.pop _) (.step (.pop _) (.refl 0 _))))

/-- `push` on a non-negative counter tape is `inc`. -/
theorem absCtr_push_pos (t : STape Seg) :
    LocalCounter.absCtr (LocalCounter.push t) true
      = GalilScaffoldCounter.inc (LocalCounter.absCtr t true) := by
  simpa using LocalCounter.absCtr_push t true

/-- `pop` on a positive counter tape is `dec`. -/
theorem absCtr_pop_pos {t : STape Seg} {v : ℕ} (h : LocalCounter.val t = v + 1) :
    LocalCounter.absCtr (LocalCounter.pop t) true
      = GalilScaffoldCounter.dec (LocalCounter.absCtr t true) := by
  simpa using LocalCounter.absCtr_pop h true

/-- Four `pop`s on a tape holding at least four are `decFour`. -/
theorem absCtr_pop4 {t : STape Seg} {v : ℕ} (h : LocalCounter.SegCtr t (v + 4)) :
    LocalCounter.absCtr (pop4 t) true
      = GalilScaffoldChainCredits.decFour (LocalCounter.absCtr t true) := by
  have h4 : LocalCounter.SegCtr t ((v + 3) + 1) := by
    have : v + 4 = (v + 3) + 1 := by omega
    rwa [this] at h
  have h3 : LocalCounter.SegCtr (LocalCounter.pop t) ((v + 2) + 1) := by
    have := LocalCounter.segCtr_pop h4
    have e : v + 3 = (v + 2) + 1 := by omega
    rwa [e] at this
  have h2 : LocalCounter.SegCtr (LocalCounter.pop (LocalCounter.pop t)) ((v + 1) + 1) := by
    have := LocalCounter.segCtr_pop h3
    have e : v + 2 = (v + 1) + 1 := by omega
    rwa [e] at this
  have h1 : LocalCounter.SegCtr
      (LocalCounter.pop (LocalCounter.pop (LocalCounter.pop t))) (v + 1) :=
    LocalCounter.segCtr_pop h2
  have e0 := absCtr_pop_pos (t := t) (v := v + 3) (LocalCounter.val_eq_of_segCtr h4)
  have e1 := absCtr_pop_pos (t := LocalCounter.pop t) (v := v + 2)
    (LocalCounter.val_eq_of_segCtr h3)
  have e2 := absCtr_pop_pos (t := LocalCounter.pop (LocalCounter.pop t)) (v := v + 1)
    (LocalCounter.val_eq_of_segCtr h2)
  have e3 := absCtr_pop_pos (t := LocalCounter.pop (LocalCounter.pop (LocalCounter.pop t)))
    (v := v) (LocalCounter.val_eq_of_segCtr h1)
  simp only [pop4, GalilScaffoldChainCredits.decFour, e3, e2, e1, e0]

/-- A positive tape abstracts to a positive counter. -/
theorem positive_absCtr {t : STape Seg} {n : ℕ} (h : LocalCounter.val t = n + 1) :
    GalilScaffoldCounter.positive (LocalCounter.absCtr t true) = true := by
  simp [LocalCounter.absCtr, GalilScaffoldCounter.positive, GalilScaffoldCounter.ofNat, h]

/-! ## 7. Cursor micro-operations -/

/-- The letter a cursor reads, as the finite control sees it (the focus cell plus
the gap bit). -/
def readV (v : InputView) : Option (Fin 3) :=
  v.focus.map (fun a => if v.gap then (2 : Fin 3) else GalilScaffoldPlace.letter a)

theorem read_absHead (v : InputView) (q : List (Fin 2)) :
    GalilScaffoldInputHead.read (absHead v q) = readV v := rfl

/-- With no arrival pending, `GalilScaffoldChainVerifier.right` — which pulls
from `incoming` — coincides with `LocalInputView.rightPH`, which does not. -/
theorem right_eq_rightPH {p : PlaceHead} (hq : p.head.incoming = []) :
    GalilScaffoldChainVerifier.right p = LocalInputView.rightPH p := by
  rcases p with ⟨⟨f, ls, rs, qs⟩, g⟩
  cases hq
  cases g <;> cases rs <;> rfl

/-- **One local right move of the verifier realizes the abstract one.** -/
theorem absVer_moveRight {x : ChainL} (hw : VerWF x) (hf : Fed x) :
    absHead (LocalInputView.moveRight x.verifier) x.vpending
      = GalilScaffoldChainVerifier.right (absVer x) := by
  have hq : (absVer x).head.incoming = [] := hf
  rw [right_eq_rightPH (p := absVer x) hq, LocalInputView.absHead_moveRight hw]
  rfl

/-- A left move of a cursor realizes `GalilScaffoldPlace.left` on its `Place`. -/
theorem absPlace_moveLeftV {v : InputView} (h : ProperView v) :
    absPlace (LocalInputView.moveLeftV v) = GalilScaffoldPlace.left (absPlace v) := by
  rcases v with ⟨back, focus, near, far, gap⟩
  cases gap with
  | true => rfl
  | false =>
      cases back with
      | nil =>
          cases focus with
          | none => rfl
          | some a => exact (h : False).elim
      | cons b bs =>
          cases focus with
          | none => exact absurd (h : (b :: bs) = []) (List.cons_ne_nil b bs)
          | some a => rfl

theorem properView_stepLeft {v : InputView} (h : ProperView v) :
    ProperView (LocalInputView.stepLeft v) := by
  rcases v with ⟨back, focus, near, far, gap⟩
  cases back with
  | nil => exact h
  | cons b bs =>
      cases focus with
      | none => exact absurd (h : (b :: bs) = []) (List.cons_ne_nil b bs)
      | some a => exact h

theorem properView_moveLeftV {v : InputView} (h : ProperView v) :
    ProperView (LocalInputView.moveLeftV v) := by
  unfold LocalInputView.moveLeftV
  split
  · exact h
  · exact properView_stepLeft h

/-! ## 8. The local steps for `ChainStep`

Each constructor gets one transformer, a locality proof at budget `c₂`, and a
simulation theorem `ChainStep (absChain x) (absChain (step x))`. -/

/-! ### `idle` / `brokenIdle` -/

theorem absChain_idle {x : ChainL} (htag : x.tag = .idle) :
    ChainStep (absChain x) (absChain x) := by
  rw [absChain, htag]; exact ChainStep.idle

theorem absChain_brokenIdle {x : ChainL} (htag : x.tag = .broken) :
    ChainStep (absChain x) (absChain x) := by
  rw [absChain, htag]; exact ChainStep.brokenIdle _

/-! ### `copyBit` — copy one bit of the DP answer onto the period tape -/

/-- `stepCopy`: move the answer head, write one period cell, `inc h`,
`margin -= 4`, walk one cell left. -/
def stepCopyBit (a : Fin 3) (x : ChainL) : ChainL :=
  { x with
    answer := GalilScaffoldTape.moveLeft x.answer
    walkerV := LocalInputView.moveLeftV x.walkerV
    period := GalilScaffoldChainPeriod.put x.period a
    tape := fun k => match k with
      | .h => LocalCounter.push (x.tape .h)
      | .margin => pop4 (x.tape .margin)
      | k => x.tape k }

theorem local_stepCopyBit (a : Fin 3) : LocalStep (stepCopyBit a) := by
  intro x
  refine ⟨⟨Equiv.refl _, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rintro (k | u)
    · cases k <;>
        first
          | exact Acts.refl _ _
          | exact (Acts.one (CtrAct.push _)).mono (by simp [c₂])
          | exact (acts_pop4 _).mono (by simp [c₂])
    · exact Acts.refl _ _
  · exact ((Acts.one (PerAct.moveRight _)).trans
      (Acts.one (PerAct.write _ _))).mono (by simp [c₂])
  · exact (Acts.one (AnsAct.moveLeft _)).mono (by simp [c₂])
  · exact Acts.refl _ _
  · exact (Acts.one (ViewAct.moveLeft _)).mono (by simp [c₂])

/-- **Simulation.**  Hypotheses: the answer head is on a `1` with tape to its
left (`GalilScaffoldTape`'s `8` / `legal` guards), the walker reads the next
letter, the walker's copy is anchored, `h` is non-negative and `margin ≥ 4`. -/
theorem absChain_copyBit {x : ChainL} {a : Fin 3} {v : ℕ}
    (htag : x.tag = .copy)
    (hone : x.answer.focus = 8) (hleg : x.answer.left ≠ [])
    (hpv : ProperView x.walkerV)
    (hread : GalilScaffoldPlace.read (GalilScaffoldPlace.left (absPlace x.walkerV)) = some a)
    (hhp : x.pol .h = true) (hmp : x.pol .margin = true)
    (hm : LocalCounter.SegCtr (x.tape .margin) (v + 4)) :
    ChainStep (absChain x) (absChain (stepCopyBit a x)) := by
  have hstep := ChainStep.copyBit x.answer (absC x .h) (absPlace x.walkerV) x.period
    (absC x .lag) (absC x .margin) (absVer x) a hone hleg hread
  have hh : absC (stepCopyBit a x) .h = GalilScaffoldCounter.inc (absC x .h) := by
    show LocalCounter.absCtr (LocalCounter.push (x.tape .h)) (x.pol .h)
        = GalilScaffoldCounter.inc (LocalCounter.absCtr (x.tape .h) (x.pol .h))
    rw [hhp]; exact absCtr_push_pos _
  have hmarg : absC (stepCopyBit a x) .margin
      = GalilScaffoldChainCredits.decFour (absC x .margin) := by
    show LocalCounter.absCtr (pop4 (x.tape .margin)) (x.pol .margin)
        = GalilScaffoldChainCredits.decFour (LocalCounter.absCtr (x.tape .margin) (x.pol .margin))
    rw [hmp]; exact absCtr_pop4 hm
  have hw : absPlace (LocalInputView.moveLeftV x.walkerV)
      = GalilScaffoldPlace.left (absPlace x.walkerV) := absPlace_moveLeftV hpv
  have htag' : (stepCopyBit a x).tag = TagL.copy := htag
  rw [absChain, htag, absChain, htag']
  show ChainStep _ (ChainVM.copy _ (absC (stepCopyBit a x) .h) (absPlace (LocalInputView.moveLeftV x.walkerV))
    _ (absC (stepCopyBit a x) .lag) (absC (stepCopyBit a x) .margin) _)
  rw [hh, hmarg, hw]
  exact hstep

/-! ### `copyEnd` — mark the tail and turn around -/

/-- `write_last`: one write on the period tape, and the tag flips to `back`. -/
def stepCopyEnd (b : Fin 3) (x : ChainL) : ChainL :=
  { x with tag := .back
           period := GalilScaffoldChainPeriod.write x.period (.last b) }

theorem local_stepCopyEnd (b : Fin 3) : LocalStep (stepCopyEnd b) :=
  fun x => ⟨⟨Equiv.refl _, fun s => by cases s <;> exact Acts.refl _ _⟩,
    (Acts.one (PerAct.write _ _)).mono (by simp [c₂]),
    Acts.refl _ _, Acts.refl _ _, Acts.refl _ _⟩

theorem absChain_copyEnd {x : ChainL} {b : Fin 3}
    (htag : x.tag = .copy)
    (hleft : x.answer.focus = 4)
    (hp : GalilScaffoldCounter.positive (absC x .h) = true)
    (hv : x.period.focus = .plain b) :
    ChainStep (absChain x) (absChain (stepCopyEnd b x)) := by
  have hstep := ChainStep.copyEnd x.answer (absC x .h) (absPlace x.walkerV) x.period
    (absC x .lag) (absC x .margin) (absVer x) b hleft hp hv
  have htag' : (stepCopyEnd b x).tag = TagL.back := rfl
  rw [absChain, htag, absChain, htag']
  exact hstep

/-! ### `backStep` / `backDone` — rewind to the front mark -/

/-- One rewind tick: a single `moveLeft` on the period tape. -/
def stepBack (x : ChainL) : ChainL :=
  { x with period := GalilScaffoldChainPeriod.moveLeft x.period }

theorem local_stepBack : LocalStep stepBack :=
  fun x => ⟨⟨Equiv.refl _, fun s => by cases s <;> exact Acts.refl _ _⟩,
    (Acts.one (PerAct.moveLeft _)).mono (by simp [c₂]),
    Acts.refl _ _, Acts.refl _ _, Acts.refl _ _⟩

theorem absChain_backStep {x : ChainL} (htag : x.tag = .back)
    (hf : GalilScaffoldChainPeriod.isFirst x.period.focus = false) :
    ChainStep (absChain x) (absChain (stepBack x)) := by
  have hstep := ChainStep.backStep x.period (absC x .h) (absC x .lag) (absC x .margin)
    (absVer x) hf
  have htag' : (stepBack x).tag = TagL.back := htag
  rw [absChain, htag, absChain, htag']
  exact hstep

/-- Entering `watch`: one move right on the period tape, and
`distance` / `boundary` / `last` (and the spare, to stay synchronized) each reset
in **one** action — the segmented-unary trick of `LocalCounter.resetSeg`. -/
def stepBackDone (x : ChainL) : ChainL :=
  { x with tag := .watch
           period := GalilScaffoldChainPeriod.moveRight x.period
           tape := fun k => match k with
             | .distance => LocalCounter.resetSeg (x.tape .distance)
             | .boundary => LocalCounter.resetSeg (x.tape .boundary)
             | .last => LocalCounter.resetSeg (x.tape .last)
             | k => x.tape k
           spare := LocalCounter.resetSeg x.spare
           phase := 0
           forward := true
           broken := false }

theorem local_stepBackDone : LocalStep stepBackDone := by
  intro x
  refine ⟨⟨Equiv.refl _, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rintro (k | u)
    · cases k <;>
        first
          | exact Acts.refl _ _
          | exact (Acts.one (CtrAct.resetSeg _)).mono (by simp [c₂])
    · exact (Acts.one (CtrAct.resetSeg _)).mono (by simp [c₂])
  · exact (Acts.one (PerAct.moveRight _)).mono (by simp [c₂])
  · exact Acts.refl _ _
  · exact Acts.refl _ _
  · exact Acts.refl _ _

/-- `stepBackDone` re-establishes the mirror invariant for free: everything is
zero again, so the rebuild job starts idle. -/
theorem refilled_stepBackDone (x : ChainL) : Refilled (stepBackDone x) := by
  show LocalCounter.SegCtr (LocalCounter.resetSeg x.spare)
    (LocalCounter.val (LocalCounter.resetSeg (x.tape .distance)))
  rw [LocalCounter.val_resetSeg]
  exact LocalCounter.segCtr_reset _

theorem absChain_backDone {x : ChainL} (htag : x.tag = .back)
    (hf : GalilScaffoldChainPeriod.isFirst x.period.focus = true) :
    ChainStep (absChain x) (absChain (stepBackDone x)) := by
  have hstep := ChainStep.backDone x.period (absC x .h) (absC x .lag) (absC x .margin)
    (absVer x) hf
  have hd : absC (stepBackDone x) .distance = GalilScaffoldCounter.reset :=
    LocalCounter.absCtr_reset _ _
  have hb : absC (stepBackDone x) .boundary = GalilScaffoldCounter.reset :=
    LocalCounter.absCtr_reset _ _
  have hl : absC (stepBackDone x) .last = GalilScaffoldCounter.reset :=
    LocalCounter.absCtr_reset _ _
  have htag' : (stepBackDone x).tag = TagL.watch := rfl
  rw [absChain, htag, absChain, htag']
  show ChainStep _ (ChainVM.watch ⟨⟨absVer x,
    ⟨GalilScaffoldChainPeriod.moveRight x.period, absC (stepBackDone x) .distance,
      absC (stepBackDone x) .boundary, absC (stepBackDone x) .last, 0, true, false⟩⟩,
    absC x .lag, absC x .margin⟩)
  rw [hd, hb, hl]
  exact hstep

/-! ## 9. `consume` — the one genuinely non-local transition -/

/-- One local right move of the verifier cursor. -/
def moveVer (x : ChainL) : ChainL := { x with verifier := LocalInputView.moveRight x.verifier }

/-- The letter the moved verifier lands on, as the finite control reads it. -/
def seenL (x : ChainL) : Option (Fin 3) := readV (LocalInputView.moveRight x.verifier)

/-- The comparison the finite control performs: the period focus against the
letter the moved verifier lands on. -/
def sameL (x : ChainL) : Bool :=
  match GalilScaffoldChainConsume.symbol x.period.focus with
  | none => false
  | some a => decide (seenL x = some a)

/-- The FRONT/TAIL boundary test, a finite-control read of the period focus. -/
def boundaryL (x : ChainL) : Bool :=
  GalilScaffoldChainPeriod.isFirst x.period.focus || GalilScaffoldChainConsume.isLast x.period.focus

/-- The new direction bit after a successful consume. -/
def fwL (x : ChainL) : Bool :=
  if boundaryL x = true then GalilScaffoldChainPeriod.isFirst x.period.focus else x.forward

/-- `inc distance`, applied to the distance tape **and its mirror** in the same
micro-step: one `applyAction` per tape, which a `StructuredMachine` affords for
free (`LocalMirror.pushAll`). -/
def pushDist (x : ChainL) : ChainL :=
  { x with tape := fun k => match k with
             | .distance => LocalCounter.push (x.tape .distance)
             | k => x.tape k
           spare := LocalCounter.push x.spare }

/-- **The role rotation of a boundary event.**  `last := boundary` (the source
dies: a role move), `boundary := spare` (the detached mirror:
`LocalMirror.take`), and the freed tape becomes the new, *stale*, spare. -/
def rotate (x : ChainL) : ChainL :=
  { x with tape := fun k => match k with
             | .boundary => x.spare
             | .last => x.tape .boundary
             | k => x.tape k
           pol := fun k => match k with
             | .boundary => x.pol .distance
             | .last => x.pol .boundary
             | k => x.pol k
           spare := x.tape .last }

/-- The 3-cycle on the physical slots that `rotate` performs. -/
def rotPerm : Equiv.Perm SlotL where
  toFun s := match s with
    | .inl .boundary => .inl .last
    | .inl .last => .inr ()
    | .inr () => .inl .boundary
    | s => s
  invFun s := match s with
    | .inl .last => .inl .boundary
    | .inr () => .inl .last
    | .inl .boundary => .inr ()
    | s => s
  left_inv := by decide
  right_inv := by decide

/-- `rotate` moves no tape: it renames three slots. -/
theorem slot_rotate (x : ChainL) (s : SlotL) : slot (rotate x) (rotPerm s) = slot x s := by
  rcases s with (k | u)
  · cases k <;> rfl
  · cases u; rfl

/-- **The new spare is stale.**  After a boundary event the spare is the recycled
`last` tape, which holds the *old* `boundary` value, not `distance`.  This is the
obligation that `refill_of_rebuild` discharges. -/
theorem rotate_spare (x : ChainL) : (rotate x).spare = x.tape .last := rfl

/-- One `push` per physical slot is all `pushDist` costs. -/
theorem acts_pushDist (x : ChainL) (s : SlotL) :
    Acts CtrAct 1 (slot x s) (slot (pushDist (moveVer x)) s) := by
  rcases s with (k | u)
  · cases k <;>
      first
        | exact Acts.refl _ _
        | exact Acts.one (CtrAct.push _)
  · cases u; exact Acts.one (CtrAct.push _)

/-- The successful branch of a local consume. -/
def consumeOK (x : ChainL) : ChainL :=
  { (if boundaryL x = true then rotate (pushDist (moveVer x)) else pushDist (moveVer x)) with
    phase := if boundaryL x = true then GalilScaffoldChainConsume.advancePhase x.phase else x.phase
    forward := fwL x
    period := if fwL x = true then GalilScaffoldChainPeriod.moveRight x.period
              else GalilScaffoldChainPeriod.moveLeft x.period }

/-- **Local `consume`.** -/
def consumeL (x : ChainL) : ChainL :=
  if sameL x = true then consumeOK x else { moveVer x with broken := true }

theorem consumeL_eq_ok {x : ChainL} (hc : sameL x = true) : consumeL x = consumeOK x := if_pos hc

theorem consumeL_eq_break {x : ChainL} (hc : sameL x = true → False) :
    consumeL x = { moveVer x with broken := true } := if_neg hc

/-! ### The fields a consume does not touch -/

theorem consumeOK_slot (x : ChainL) (s : SlotL) :
    slot (consumeOK x) s
      = slot (if boundaryL x = true then rotate (pushDist (moveVer x))
              else pushDist (moveVer x)) s := by
  rcases s with (k | u) <;> rfl

theorem consumeOK_period (x : ChainL) :
    (consumeOK x).period = if fwL x = true then GalilScaffoldChainPeriod.moveRight x.period
      else GalilScaffoldChainPeriod.moveLeft x.period := rfl

theorem consumeOK_phase (x : ChainL) :
    (consumeOK x).phase = if boundaryL x = true
      then GalilScaffoldChainConsume.advancePhase x.phase else x.phase := rfl

theorem consumeOK_forward (x : ChainL) : (consumeOK x).forward = fwL x := rfl

theorem consumeL_tag (x : ChainL) : (consumeL x).tag = x.tag := by
  cases hc : sameL x <;> cases hb : boundaryL x <;>
    simp [consumeL, consumeOK, rotate, pushDist, moveVer, hc, hb]

theorem consumeL_answer (x : ChainL) : (consumeL x).answer = x.answer := by
  cases hc : sameL x <;> cases hb : boundaryL x <;>
    simp [consumeL, consumeOK, rotate, pushDist, moveVer, hc, hb]

theorem consumeL_walkerV (x : ChainL) : (consumeL x).walkerV = x.walkerV := by
  cases hc : sameL x <;> cases hb : boundaryL x <;>
    simp [consumeL, consumeOK, rotate, pushDist, moveVer, hc, hb]

theorem consumeL_vpending (x : ChainL) : (consumeL x).vpending = x.vpending := by
  cases hc : sameL x <;> cases hb : boundaryL x <;>
    simp [consumeL, consumeOK, rotate, pushDist, moveVer, hc, hb]

theorem consumeL_verifier (x : ChainL) :
    (consumeL x).verifier = LocalInputView.moveRight x.verifier := by
  cases hc : sameL x <;> cases hb : boundaryL x <;>
    simp [consumeL, consumeOK, rotate, pushDist, moveVer, hc, hb]

theorem consumeL_tape_lag (x : ChainL) : (consumeL x).tape .lag = x.tape .lag := by
  cases hc : sameL x <;> cases hb : boundaryL x <;>
    simp [consumeL, consumeOK, rotate, pushDist, moveVer, hc, hb]

theorem consumeL_pol_lag (x : ChainL) : (consumeL x).pol .lag = x.pol .lag := by
  cases hc : sameL x <;> cases hb : boundaryL x <;>
    simp [consumeL, consumeOK, rotate, pushDist, moveVer, hc, hb]

theorem consumeL_tape_margin (x : ChainL) : (consumeL x).tape .margin = x.tape .margin := by
  cases hc : sameL x <;> cases hb : boundaryL x <;>
    simp [consumeL, consumeOK, rotate, pushDist, moveVer, hc, hb]

theorem consumeL_pol_margin (x : ChainL) : (consumeL x).pol .margin = x.pol .margin := by
  cases hc : sameL x <;> cases hb : boundaryL x <;>
    simp [consumeL, consumeOK, rotate, pushDist, moveVer, hc, hb]

theorem consumeL_broken_of_ok {x : ChainL} (hc : sameL x = true) :
    (consumeL x).broken = x.broken := by
  cases hb : boundaryL x <;>
    simp [consumeL, consumeOK, rotate, pushDist, moveVer, hc, hb]

/-! ### Locality: a consume costs **one** action per physical slot -/

theorem consumeL_slots (x : ChainL) : ∃ σ : Equiv.Perm SlotL,
    ∀ s, Acts CtrAct 1 (slot x s) (slot (consumeL x) (σ s)) := by
  by_cases hc : sameL x = true
  · by_cases hb : boundaryL x = true
    · refine ⟨rotPerm, fun s => ?_⟩
      have h : slot (consumeL x) (rotPerm s) = slot (pushDist (moveVer x)) s := by
        rw [consumeL_eq_ok hc, consumeOK_slot, if_pos hb]; exact slot_rotate _ s
      rw [h]; exact acts_pushDist x s
    · refine ⟨Equiv.refl _, fun s => ?_⟩
      have h : slot (consumeL x) (Equiv.refl SlotL s) = slot (pushDist (moveVer x)) s := by
        show slot (consumeL x) s = _
        rw [consumeL_eq_ok hc, consumeOK_slot, if_neg hb]
      rw [h]; exact acts_pushDist x s
  · refine ⟨Equiv.refl _, fun s => ?_⟩
    have h : slot (consumeL x) (Equiv.refl SlotL s) = slot x s := by
      show slot (consumeL x) s = _
      rcases s with (k | u) <;> simp [slot, consumeL, moveVer, hc]
    rw [h]; exact Acts.refl _ _

theorem acts_consumeL_period (x : ChainL) : Acts PerAct 1 x.period (consumeL x).period := by
  by_cases hc : sameL x = true
  · rw [consumeL_eq_ok hc, consumeOK_period]
    by_cases hf : fwL x = true
    · rw [if_pos hf]; exact Acts.one (PerAct.moveRight _)
    · rw [if_neg hf]; exact Acts.one (PerAct.moveLeft _)
  · have h : (consumeL x).period = x.period := by simp [consumeL, moveVer, hc]
    rw [h]; exact Acts.refl _ _

theorem local_consumeL : LocalStep consumeL := by
  intro x
  obtain ⟨σ, hσ⟩ := consumeL_slots x
  refine ⟨⟨σ, fun s => (hσ s).mono (by simp [c₂])⟩, ?_, ?_, ?_, ?_⟩
  · exact (acts_consumeL_period x).mono (by simp [c₂])
  · rw [consumeL_answer]; exact Acts.refl _ _
  · rw [consumeL_verifier]; exact (Acts.one (ViewAct.moveRight _)).mono (by simp [c₂])
  · rw [consumeL_walkerV]; exact Acts.refl _ _

/-! ### The abstract consume, unfolded into its two branches -/

theorem consume_break_eq {x : ChainL} (hc : sameL x = false) :
    GalilScaffoldChainConsume.consume (absCons x) (seenL x)
      = { absCons x with broken := true } := by
  cases hsym : GalilScaffoldChainConsume.symbol x.period.focus with
  | none => simp [GalilScaffoldChainConsume.consume, absCons, hsym]
  | some a =>
      have hne : seenL x ≠ some a := by
        intro h
        rw [show sameL x = decide (seenL x = some a) by simp [sameL, hsym], h] at hc
        simp at hc
      exact GalilScaffoldChainConsume.mismatch (absCons x) a (seenL x) hsym hne

theorem consume_ok_eq {x : ChainL} (hc : sameL x = true) :
    GalilScaffoldChainConsume.consume (absCons x) (seenL x)
      = ⟨(if fwL x = true then GalilScaffoldChainPeriod.moveRight x.period
            else GalilScaffoldChainPeriod.moveLeft x.period),
          GalilScaffoldCounter.inc (absC x .distance),
          (if boundaryL x = true then GalilScaffoldCounter.inc (absC x .distance)
            else absC x .boundary),
          (if boundaryL x = true then absC x .boundary else absC x .last),
          (if boundaryL x = true then GalilScaffoldChainConsume.advancePhase x.phase
            else x.phase),
          fwL x, x.broken⟩ := by
  cases hsym : GalilScaffoldChainConsume.symbol x.period.focus with
  | none => simp [sameL, hsym] at hc
  | some a =>
      have hseen : seenL x = some a := by simpa [sameL, hsym] using hc
      simp [GalilScaffoldChainConsume.consume, absCons, hsym, hseen, boundaryL, fwL]

/-- **The mirror pays for `boundary := inc distance`.**  The detached spare,
pushed in lockstep, abstracts to exactly the incremented distance. -/
theorem absCtr_spare_take {x : ChainL} (hd : x.pol .distance = true) (hs : SpareSynced x) :
    LocalCounter.absCtr (LocalCounter.push x.spare) (x.pol .distance)
      = GalilScaffoldCounter.inc (absC x .distance) := by
  rw [hd]
  show LocalCounter.absCtr (LocalCounter.push x.spare) true
      = GalilScaffoldCounter.inc (LocalCounter.absCtr (x.tape .distance) (x.pol .distance))
  rw [hd, absCtr_push_pos]
  unfold LocalCounter.absCtr
  rw [hs]

/-! ### The three counters a consume touches -/

theorem absC_consumeOK_distance {x : ChainL} (hd : x.pol .distance = true) :
    absC (consumeOK x) .distance = GalilScaffoldCounter.inc (absC x .distance) := by
  have ht : (consumeOK x).tape .distance = LocalCounter.push (x.tape .distance) := by
    cases hb : boundaryL x <;> simp [consumeOK, rotate, pushDist, moveVer, hb]
  have hp : (consumeOK x).pol .distance = x.pol .distance := by
    cases hb : boundaryL x <;> simp [consumeOK, rotate, pushDist, moveVer, hb]
  show LocalCounter.absCtr ((consumeOK x).tape .distance) ((consumeOK x).pol .distance)
      = GalilScaffoldCounter.inc (LocalCounter.absCtr (x.tape .distance) (x.pol .distance))
  rw [ht, hp, hd]
  exact absCtr_push_pos _

theorem absC_consumeOK_boundary {x : ChainL} (hd : x.pol .distance = true) (hs : SpareSynced x) :
    absC (consumeOK x) .boundary
      = if boundaryL x = true then GalilScaffoldCounter.inc (absC x .distance)
        else absC x .boundary := by
  by_cases hb : boundaryL x = true
  · rw [if_pos hb]
    have ht : (consumeOK x).tape .boundary = LocalCounter.push x.spare := by
      simp [consumeOK, rotate, pushDist, moveVer, hb]
    have hp : (consumeOK x).pol .boundary = x.pol .distance := by
      simp [consumeOK, rotate, pushDist, moveVer, hb]
    show LocalCounter.absCtr ((consumeOK x).tape .boundary) ((consumeOK x).pol .boundary) = _
    rw [ht, hp]
    exact absCtr_spare_take hd hs
  · rw [if_neg hb]
    have ht : (consumeOK x).tape .boundary = x.tape .boundary := by
      simp [consumeOK, pushDist, moveVer, hb]
    have hp : (consumeOK x).pol .boundary = x.pol .boundary := by
      simp [consumeOK, pushDist, moveVer, hb]
    show LocalCounter.absCtr ((consumeOK x).tape .boundary) ((consumeOK x).pol .boundary)
        = LocalCounter.absCtr (x.tape .boundary) (x.pol .boundary)
    rw [ht, hp]

theorem absC_consumeOK_last {x : ChainL} :
    absC (consumeOK x) .last
      = if boundaryL x = true then absC x .boundary else absC x .last := by
  by_cases hb : boundaryL x = true
  · rw [if_pos hb]
    have ht : (consumeOK x).tape .last = x.tape .boundary := by
      simp [consumeOK, rotate, pushDist, moveVer, hb]
    have hp : (consumeOK x).pol .last = x.pol .boundary := by
      simp [consumeOK, rotate, pushDist, moveVer, hb]
    show LocalCounter.absCtr ((consumeOK x).tape .last) ((consumeOK x).pol .last)
        = LocalCounter.absCtr (x.tape .boundary) (x.pol .boundary)
    rw [ht, hp]
  · rw [if_neg hb]
    have ht : (consumeOK x).tape .last = x.tape .last := by
      simp [consumeOK, pushDist, moveVer, hb]
    have hp : (consumeOK x).pol .last = x.pol .last := by
      simp [consumeOK, pushDist, moveVer, hb]
    show LocalCounter.absCtr ((consumeOK x).tape .last) ((consumeOK x).pol .last)
        = LocalCounter.absCtr (x.tape .last) (x.pol .last)
    rw [ht, hp]

/-- **The central simulation lemma: one local consume is one abstract consume.**

The `boundary` copy is discharged by `SpareSynced`; the timing obligation that
re-establishes it after the event is `Refilled` / `refill_of_rebuild`. -/
theorem absCons_consumeL {x : ChainL} (hd : x.pol .distance = true) (hs : SpareSynced x) :
    absCons (consumeL x)
      = GalilScaffoldChainConsume.consume (absCons x) (seenL x) := by
  by_cases hc : sameL x = true
  · rw [consume_ok_eq hc, consumeL_eq_ok hc]
    show GalilScaffoldChainConsume.State.mk (consumeOK x).period (absC (consumeOK x) .distance)
        (absC (consumeOK x) .boundary) (absC (consumeOK x) .last) (consumeOK x).phase
        (consumeOK x).forward (consumeOK x).broken = _
    rw [consumeOK_period, consumeOK_phase, consumeOK_forward, absC_consumeOK_distance hd,
      absC_consumeOK_boundary hd hs, absC_consumeOK_last,
      show (consumeOK x).broken = x.broken from
        (consumeL_eq_ok hc) ▸ consumeL_broken_of_ok hc]
  · rw [consume_break_eq (by simpa using hc), consumeL_eq_break (fun h => hc h)]
    rfl

theorem absMach_consumeL {x : ChainL} (hw : VerWF x) (hf : Fed x)
    (hd : x.pol .distance = true) (hs : SpareSynced x) :
    absMach (consumeL x) = GalilScaffoldChainVerifier.consume (absMach x) := by
  have hver : absVer (consumeL x) = GalilScaffoldChainVerifier.right (absVer x) := by
    show absHead (consumeL x).verifier (consumeL x).vpending = _
    rw [consumeL_verifier, consumeL_vpending]
    exact absVer_moveRight hw hf
  have hseen : GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right (absVer x))
      = seenL x := by
    rw [← absVer_moveRight hw hf]
    exact read_absHead _ _
  show GalilScaffoldChainVerifier.State.mk (absVer (consumeL x)) (absCons (consumeL x))
      = ⟨GalilScaffoldChainVerifier.right (absVer x),
         GalilScaffoldChainConsume.consume (absCons x)
           (GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right (absVer x)))⟩
  rw [hver, hseen, absCons_consumeL hd hs]

/-! ## 10. The watch transitions -/

/-- The local form of `GalilScaffoldChainWatch.Good`. -/
def GoodL (x : ChainL) : Prop :=
  GalilScaffoldChainVerifier.canRight (absVer x) ∧
  ∃ a, GalilScaffoldChainConsume.symbol x.period.focus = some a ∧
    readV (LocalInputView.moveRight x.verifier) = some a

theorem sameL_of_goodL {x : ChainL} (h : GoodL x) : sameL x = true := by
  obtain ⟨_, a, hsym, hread⟩ := h
  simp [sameL, seenL, hsym, hread]

theorem good_of_goodL {x : ChainL} (hw : VerWF x) (hf : Fed x) (h : GoodL x) :
    GalilScaffoldChainWatch.Good (absWatch x) := by
  obtain ⟨hcan, a, hsym, hread⟩ := h
  refine ⟨hcan, a, hsym, ?_⟩
  show GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right (absVer x)) = some a
  rw [← absVer_moveRight hw hf, read_absHead]
  exact hread

/-- The local form of the `JointBreak` guard. -/
def BreakL (x : ChainL) : Prop :=
  GalilScaffoldChainVerifier.canRight (absVer x) ∧
  ∃ a, GalilScaffoldChainConsume.symbol x.period.focus = some a ∧
    readV (LocalInputView.moveRight x.verifier) ≠ some a

theorem sameL_of_breakL {x : ChainL} (h : BreakL x) : sameL x = false := by
  obtain ⟨_, a, hsym, hread⟩ := h
  simp [sameL, seenL, hsym, hread]

/-! ### `watchStep` with `Internal.idle` -/

theorem absChain_watchIdle {x : ChainL} (htag : x.tag = .watch)
    (hz : GalilScaffoldCounter.positive (absC x .lag) = false) :
    ChainStep (absChain x) (absChain x) := by
  rw [absChain, htag]
  exact ChainStep.watchStep _ _ (GalilScaffoldChainWatch.Internal.idle _ hz)

/-! ### `watchStep` with `Internal.take` (`caught`) -/

/-- `caught`: a local consume plus `dec lag`. -/
def stepWatchTake (x : ChainL) : ChainL :=
  { consumeL x with
    tape := fun k => match k with
      | .lag => LocalCounter.pop ((consumeL x).tape .lag)
      | k => (consumeL x).tape k }

theorem local_stepWatchTake : LocalStep stepWatchTake := by
  intro x
  obtain ⟨σ, hσ⟩ := consumeL_slots x
  refine ⟨⟨σ, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro s
    have hslot : ∀ t : SlotL, slot (stepWatchTake x) t
        = (if t = Sum.inl CtrL.lag then LocalCounter.pop ((consumeL x).tape .lag)
           else slot (consumeL x) t) := by
      rintro (k | u)
      · cases k <;> rfl
      · cases u; rfl
    rw [hslot]
    by_cases hs : σ s = Sum.inl CtrL.lag
    · rw [if_pos hs]
      have h1 := hσ s
      rw [hs] at h1
      exact (h1.trans (Acts.one (CtrAct.pop _))).mono (by simp [c₂])
    · rw [if_neg hs]
      exact (hσ s).mono (by simp [c₂])
  · show Acts PerAct c₂ x.period (consumeL x).period
    exact (acts_consumeL_period x).mono (by simp [c₂])
  · show Acts AnsAct c₂ x.answer (consumeL x).answer
    rw [consumeL_answer]; exact Acts.refl _ _
  · show Acts ViewAct c₂ x.verifier (consumeL x).verifier
    rw [consumeL_verifier]; exact (Acts.one (ViewAct.moveRight _)).mono (by simp [c₂])
  · show Acts ViewAct c₂ x.walkerV (consumeL x).walkerV
    rw [consumeL_walkerV]; exact Acts.refl _ _

theorem absChain_watchTake {x : ChainL} {n : ℕ} (htag : x.tag = .watch)
    (hw : VerWF x) (hf : Fed x) (hd : x.pol .distance = true) (hs : SpareSynced x)
    (hlp : x.pol .lag = true) (hlv : LocalCounter.val (x.tape .lag) = n + 1)
    (hg : GoodL x) :
    ChainStep (absChain x) (absChain (stepWatchTake x)) := by
  have hpos : GalilScaffoldCounter.positive (absC x .lag) = true := by
    show GalilScaffoldCounter.positive (LocalCounter.absCtr (x.tape .lag) (x.pol .lag)) = true
    rw [hlp]; exact positive_absCtr hlv
  have hstep := ChainStep.watchStep (absWatch x) (GalilScaffoldChainWatch.caught (absWatch x))
    (GalilScaffoldChainWatch.Internal.take _ hpos (good_of_goodL hw hf hg))
  have htag' : (stepWatchTake x).tag = TagL.watch := by
    show (consumeL x).tag = TagL.watch
    rw [consumeL_tag]; exact htag
  rw [absChain, htag, absChain, htag']
  have hmach : absMach (stepWatchTake x) = GalilScaffoldChainVerifier.consume (absMach x) := by
    rw [← absMach_consumeL hw hf hd hs]; rfl
  have hlag : absC (stepWatchTake x) .lag = GalilScaffoldCounter.dec (absC x .lag) := by
    show LocalCounter.absCtr (LocalCounter.pop ((consumeL x).tape .lag))
        ((consumeL x).pol .lag)
        = GalilScaffoldCounter.dec (LocalCounter.absCtr (x.tape .lag) (x.pol .lag))
    rw [consumeL_tape_lag, consumeL_pol_lag, hlp]
    exact absCtr_pop_pos hlv
  have hmar : absC (stepWatchTake x) .margin = absC x .margin := by
    show LocalCounter.absCtr ((consumeL x).tape .margin) ((consumeL x).pol .margin)
        = LocalCounter.absCtr (x.tape .margin) (x.pol .margin)
    rw [consumeL_tape_margin, consumeL_pol_margin]
  show ChainStep _ (ChainVM.watch ⟨absMach (stepWatchTake x),
    absC (stepWatchTake x) .lag, absC (stepWatchTake x) .margin⟩)
  rw [hmach, hlag, hmar]
  exact hstep

/-! ## 11. The local steps for `ChainMatched` -/

/-- `inc lag` and `inc margin`: the credit bump shared by `copy`, `back` and the
`queued` branch of `Outer`. -/
def bumpCredits (x : ChainL) : ChainL :=
  { x with tape := fun k => match k with
      | .lag => LocalCounter.push (x.tape .lag)
      | .margin => LocalCounter.push (x.tape .margin)
      | k => x.tape k }

theorem local_bumpCredits : LocalStep bumpCredits := by
  intro x
  refine ⟨⟨Equiv.refl _, ?_⟩, Acts.refl _ _, Acts.refl _ _, Acts.refl _ _, Acts.refl _ _⟩
  rintro (k | u)
  · cases k <;>
      first
        | exact Acts.refl _ _
        | exact (Acts.one (CtrAct.push _)).mono (by simp [c₂])
  · exact Acts.refl _ _

theorem absC_bump_lag {x : ChainL} (hlp : x.pol .lag = true) :
    absC (bumpCredits x) .lag = GalilScaffoldCounter.inc (absC x .lag) := by
  show LocalCounter.absCtr (LocalCounter.push (x.tape .lag)) (x.pol .lag)
      = GalilScaffoldCounter.inc (LocalCounter.absCtr (x.tape .lag) (x.pol .lag))
  rw [hlp]; exact absCtr_push_pos _

theorem absC_bump_margin {x : ChainL} (hmp : x.pol .margin = true) :
    absC (bumpCredits x) .margin = GalilScaffoldCounter.inc (absC x .margin) := by
  show LocalCounter.absCtr (LocalCounter.push (x.tape .margin)) (x.pol .margin)
      = GalilScaffoldCounter.inc (LocalCounter.absCtr (x.tape .margin) (x.pol .margin))
  rw [hmp]; exact absCtr_push_pos _

theorem absChain_matchedCopy {x : ChainL} (htag : x.tag = .copy)
    (hlp : x.pol .lag = true) (hmp : x.pol .margin = true) :
    ChainMatched (absChain x) (absChain (bumpCredits x)) := by
  have hstep := ChainMatched.copy x.answer (absC x .h) (absPlace x.walkerV) x.period
    (absC x .lag) (absC x .margin) (absVer x)
  have htag' : (bumpCredits x).tag = TagL.copy := htag
  rw [absChain, htag, absChain, htag']
  show ChainMatched _ (ChainVM.copy _ _ _ _ (absC (bumpCredits x) .lag)
    (absC (bumpCredits x) .margin) _)
  rw [absC_bump_lag hlp, absC_bump_margin hmp]
  exact hstep

theorem absChain_matchedBack {x : ChainL} (htag : x.tag = .back)
    (hlp : x.pol .lag = true) (hmp : x.pol .margin = true) :
    ChainMatched (absChain x) (absChain (bumpCredits x)) := by
  have hstep := ChainMatched.back x.period (absC x .h) (absC x .lag) (absC x .margin) (absVer x)
  have htag' : (bumpCredits x).tag = TagL.back := htag
  rw [absChain, htag, absChain, htag']
  show ChainMatched _ (ChainVM.back _ _ (absC (bumpCredits x) .lag)
    (absC (bumpCredits x) .margin) _)
  rw [absC_bump_lag hlp, absC_bump_margin hmp]
  exact hstep

/-- `Outer.queued`: `inc lag`, `inc margin`, no consume. -/
theorem absChain_queued {x : ChainL} (htag : x.tag = .watch)
    (hz : GalilScaffoldCounter.zero (absC x .lag) = false)
    (hlp : x.pol .lag = true) (hmp : x.pol .margin = true) :
    ChainMatched (absChain x) (absChain (bumpCredits x)) := by
  have hstep := ChainMatched.watch (absWatch x) (GalilScaffoldChainWatch.queued (absWatch x))
    (GalilScaffoldChainWatch.Outer.queued _ hz)
  have htag' : (bumpCredits x).tag = TagL.watch := htag
  rw [absChain, htag, absChain, htag']
  show ChainMatched _ (ChainVM.watch ⟨absMach (bumpCredits x),
    absC (bumpCredits x) .lag, absC (bumpCredits x) .margin⟩)
  have hmach : absMach (bumpCredits x) = absMach x := rfl
  rw [hmach, absC_bump_lag hlp, absC_bump_margin hmp]
  exact hstep

/-- `immediate` / the `JointBreak` payload: a local consume plus `inc margin`. -/
def stepImmediate (x : ChainL) : ChainL :=
  { consumeL x with
    tape := fun k => match k with
      | .margin => LocalCounter.push ((consumeL x).tape .margin)
      | k => (consumeL x).tape k }

theorem local_stepImmediate : LocalStep stepImmediate := by
  intro x
  obtain ⟨σ, hσ⟩ := consumeL_slots x
  refine ⟨⟨σ, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro s
    have hslot : ∀ t : SlotL, slot (stepImmediate x) t
        = (if t = Sum.inl CtrL.margin then LocalCounter.push ((consumeL x).tape .margin)
           else slot (consumeL x) t) := by
      rintro (k | u)
      · cases k <;> rfl
      · cases u; rfl
    rw [hslot]
    by_cases hs : σ s = Sum.inl CtrL.margin
    · rw [if_pos hs]
      have h1 := hσ s
      rw [hs] at h1
      exact (h1.trans (Acts.one (CtrAct.push _))).mono (by simp [c₂])
    · rw [if_neg hs]
      exact (hσ s).mono (by simp [c₂])
  · show Acts PerAct c₂ x.period (consumeL x).period
    exact (acts_consumeL_period x).mono (by simp [c₂])
  · show Acts AnsAct c₂ x.answer (consumeL x).answer
    rw [consumeL_answer]; exact Acts.refl _ _
  · show Acts ViewAct c₂ x.verifier (consumeL x).verifier
    rw [consumeL_verifier]; exact (Acts.one (ViewAct.moveRight _)).mono (by simp [c₂])
  · show Acts ViewAct c₂ x.walkerV (consumeL x).walkerV
    rw [consumeL_walkerV]; exact Acts.refl _ _

theorem consumeL_lag (x : ChainL) : absC (consumeL x) .lag = absC x .lag := by
  show LocalCounter.absCtr ((consumeL x).tape .lag) ((consumeL x).pol .lag)
      = LocalCounter.absCtr (x.tape .lag) (x.pol .lag)
  rw [consumeL_tape_lag, consumeL_pol_lag]

theorem absC_immediate_margin {x : ChainL} (hmp : x.pol .margin = true) :
    absC (stepImmediate x) .margin = GalilScaffoldCounter.inc (absC x .margin) := by
  show LocalCounter.absCtr (LocalCounter.push ((consumeL x).tape .margin))
      ((consumeL x).pol .margin) = _
  rw [consumeL_tape_margin, consumeL_pol_margin, hmp]
  show LocalCounter.absCtr (LocalCounter.push (x.tape .margin)) true
      = GalilScaffoldCounter.inc (LocalCounter.absCtr (x.tape .margin) (x.pol .margin))
  rw [hmp]
  exact absCtr_push_pos _

theorem absMach_stepImmediate {x : ChainL} (hw : VerWF x) (hf : Fed x)
    (hd : x.pol .distance = true) (hs : SpareSynced x) :
    absMach (stepImmediate x) = GalilScaffoldChainVerifier.consume (absMach x) := by
  rw [← absMach_consumeL hw hf hd hs]; rfl

theorem absChain_immediate {x : ChainL} (htag : x.tag = .watch)
    (hw : VerWF x) (hf : Fed x) (hd : x.pol .distance = true) (hs : SpareSynced x)
    (hmp : x.pol .margin = true)
    (hz : GalilScaffoldCounter.zero (absC x .lag) = true) (hg : GoodL x) :
    ChainMatched (absChain x) (absChain (stepImmediate x)) := by
  have hstep := ChainMatched.watch (absWatch x) (GalilScaffoldChainWatch.immediate (absWatch x))
    (GalilScaffoldChainWatch.Outer.immediate _ hz (good_of_goodL hw hf hg))
  have htag' : (stepImmediate x).tag = TagL.watch := by
    show (consumeL x).tag = TagL.watch
    rw [consumeL_tag]; exact htag
  rw [absChain, htag, absChain, htag']
  show ChainMatched _ (ChainVM.watch ⟨absMach (stepImmediate x),
    absC (stepImmediate x) .lag, absC (stepImmediate x) .margin⟩)
  have hlag : absC (stepImmediate x) .lag = absC x .lag := consumeL_lag x
  rw [absMach_stepImmediate hw hf hd hs, hlag, absC_immediate_margin hmp]
  exact hstep

/-- The break: the same payload as `immediate`, with the tag flipped to
`broken`. -/
def stepBreak (x : ChainL) : ChainL := { stepImmediate x with tag := .broken }

theorem local_stepBreak : LocalStep stepBreak := by
  intro x
  obtain ⟨hσ, hp, ha, hv, hwk⟩ := local_stepImmediate x
  exact ⟨hσ, hp, ha, hv, hwk⟩

theorem absChain_break {x : ChainL} (htag : x.tag = .watch)
    (hw : VerWF x) (hf : Fed x) (hd : x.pol .distance = true) (hs : SpareSynced x)
    (hmp : x.pol .margin = true)
    (hz : GalilScaffoldCounter.zero (absC x .lag) = true) (hbk : BreakL x) :
    ChainMatched (absChain x) (absChain (stepBreak x)) := by
  obtain ⟨hcan, a, hsym, hne⟩ := hbk
  have hne' : GalilScaffoldInputHead.read
      (GalilScaffoldChainVerifier.right (absWatch x).machine.verifier) ≠ some a := by
    rw [show (absWatch x).machine.verifier = absVer x from rfl, ← absVer_moveRight hw hf,
      read_absHead]
    exact hne
  have hbs : BreakStep (absWatch x)
      ⟨GalilScaffoldChainVerifier.consume (absWatch x).machine, (absWatch x).lag,
        GalilScaffoldCounter.inc (absWatch x).margin⟩ :=
    ⟨hz, hcan, a, hsym, hne', rfl⟩
  have hstep := ChainMatched.breaks (absWatch x) _ hbs
  have htag' : (stepBreak x).tag = TagL.broken := rfl
  rw [absChain, htag, absChain, htag']
  show ChainMatched _ (ChainVM.broken ⟨absMach (stepImmediate x),
    absC (stepImmediate x) .lag, absC (stepImmediate x) .margin⟩)
  have hlag : absC (stepImmediate x) .lag = absC x .lag := consumeL_lag x
  rw [absMach_stepImmediate hw hf hd hs, hlag, absC_immediate_margin hmp]
  exact hstep

/-! ## 12. The refill obligation

`rotate` hands the recycled `last` tape to the spare slot, so `SpareSynced` is
*lost* at every boundary event and must be re-established before the next one.
That is the timing hypothesis every consume lemma above carries.  It is
discharged by `LocalMirror`'s background rebuild, one mark per tick, from a
sacrificial donor (`LocalMirror.read_costs_value` explains why a donor is
needed). -/

/-- **The timing budget.**  Between two boundary events the machine must run at
least `val distance` rebuild ticks. -/
def RefillBudget (x : ChainL) (ticks : ℕ) : Prop :=
  LocalCounter.val (x.tape .distance) ≤ ticks

/-- **The refill.**  Installing a completed `LocalMirror` rebuild in the spare
slot re-establishes `Refilled`, hence `SpareSynced`. -/
theorem refill_of_rebuild {x : ChainL} {r : LocalMirror.Rebuild} {v : ℕ}
    (hinv : LocalMirror.RebuildInv r v) (hp : r.pending = v)
    (hv : v = LocalCounter.val (x.tape .distance)) :
    Refilled { x with spare := (LocalMirror.rebuildRun v r).spare } := by
  have h := (LocalMirror.rebuild_done hinv hp).1
  show LocalCounter.SegCtr (LocalMirror.rebuildRun v r).spare
    (LocalCounter.val (x.tape .distance))
  rwa [← hv]

/-- …and one rebuild tick is one action on each of two tapes, so it fits inside
the same budget `c₂`. -/
theorem acts_rebuildStep (r : LocalMirror.Rebuild) :
    Acts CtrAct c₂ r.don (LocalMirror.rebuildStep r).don ∧
    Acts CtrAct c₂ r.spare (LocalMirror.rebuildStep r).spare :=
  ⟨(Acts.one (CtrAct.pop _)).mono (by simp [c₂]),
    (Acts.one (CtrAct.push _)).mono (by simp [c₂])⟩

#print axioms absChain
#print axioms absChain_tag
#print axioms absChain_tag_inj
#print axioms absChain_watch_inj
#print axioms absChain_copy_inj
#print axioms absC_canonical
#print axioms absChain_spare_irrelevant
#print axioms absPlace_moveLeftV
#print axioms absVer_moveRight
#print axioms absCtr_pop4
#print axioms slot_rotate
#print axioms absCtr_spare_take
#print axioms consume_ok_eq
#print axioms consume_break_eq
#print axioms absCons_consumeL
#print axioms consumeL_slots
#print axioms absMach_consumeL
#print axioms absChain_idle
#print axioms absChain_brokenIdle
#print axioms absChain_copyBit
#print axioms absChain_copyEnd
#print axioms absChain_backStep
#print axioms absChain_backDone
#print axioms absChain_watchIdle
#print axioms absChain_watchTake
#print axioms absChain_matchedCopy
#print axioms absChain_matchedBack
#print axioms absChain_queued
#print axioms absChain_immediate
#print axioms absChain_break
#print axioms local_stepCopyBit
#print axioms local_stepCopyEnd
#print axioms local_stepBack
#print axioms local_stepBackDone
#print axioms local_consumeL
#print axioms local_stepWatchTake
#print axioms local_bumpCredits
#print axioms local_stepImmediate
#print axioms local_stepBreak
#print axioms refilled_stepBackDone
#print axioms refill_of_rebuild

end PalPeg.LocalChain
