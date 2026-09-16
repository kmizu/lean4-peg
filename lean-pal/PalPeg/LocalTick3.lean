import PalPeg.LocalTick1
import PalPeg.LocalTick2
import PalPeg.LocalReplayParked
import PalPeg.GalilTickFun3
import PalPeg.LocalChain

/-!
# 局所化計画, piece 9: the *local* phase-mode ticks (`TickL3`)

`LocalTick1` realized the scan ticks, `LocalTick2` the restart-family commits.
This file realizes the seven **phase modes** of `GalilScaffoldTop.Tick`
(`shift`, `copy`, `home`, `fpp`, `markEnd`, `choose`, `rewind`; the fifteen
constructors `shift_one … rewind_pair`) against `galilFrameS`.

## Cost per tick (`c₃ = 66`)

| constructor | local steps | what moves |
|---|---|---|
| `shift_one` | 2 | C right, L right twice; `remaining`/`radius` pop, `length` pop ×2, `cycle` push ×2 (with mirrors) |
| `shift_done`, `home_start` | 1 | finite control only |
| `copy_one` | 1 | SOURCE write+move, `fppWork` pop, fpp walker `moveLeftV` |
| `copy_done`, `home_step` | 1 | one SOURCE action |
| `fpp_slice` | `q + 1 ≤ 65` | `q` pointwise `stepL` on the fpp buffer, then pc/done |
| `fpp_done` | `q + 2 ≤ 66` | `q` steps, then `markNew` = two MARKS actions |
| `markEnd_*`, `choose_step` | 1 | one MARKS move |
| `choose_select` | 2 | `length`/`radius` `resetSeg`, then `length` push |
| `rewind_done` | 1 | `resetL` on the fpp double buffer |
| `rewind_one` / `rewind_pair` | 1 | MARKS left, L (and C) `moveLeftV`, `length` (and `radius`) push |

Every counter update goes through one generic bank tick (`bankTick`, one `Op`
per logical counter, mirrors included), whose abstraction (`abs'_bankTick`) and
invariant preservation (`inv_bankTick`) are proved once.

## Hypotheses kept in the constructors

* `hr : replaying = false` — phase modes never replay, so `abs'' = abs'`.
* sign bits (`pol = true`) and positivity of popped tapes (`ShiftCounters`,
  `hpol`/`hv`);
* `Ahead` for the three right moves of a shift unit (input already delivered);
* `ProperView x.fppWalker` for the walker's `Place.left`;
* `fpp_slice`/`fpp_done`: the pointwise step family `g` **computes** the
  `Run` of the marked FPP code over `q` ticks (`hprog`), and `q ≤ 64`;
* `choose_select`: the head-copy jobs have already brought L and C onto R
  (`hleft`/`hcenter`), as in `LocalTick2`;
* `rewind_done`: the idle half of the fpp buffer is erased (`hclean`).
* Frame guards (`remainingPos`, `atLeft`, `atEnd`, `markSet`, `atFirst`) and
  the "cell to the left" facts are stated on `abs' x`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.LocalTick3

open PalPeg.Program (STape)
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldTop
open PalPeg.GalilScaffoldController (Control)
open PalPeg.LocalState
open PalPeg.LocalCounter (Seg)
open PalPeg.LocalInputView (InputView)
open PalPeg.LocalMirror (Mirrored Shaped)
open PalPeg.LocalArrival (absHead' abs' absState' Ahead)
open PalPeg.LocalTick2 (StepLocalN)
open PalPeg.LocalTick1 (Inv CountersShaped stepLocalN_one stepLocalN_trans stepLocalN_le)
open PalPeg.LocalReplayParked (abs'' absState'' abs''_eq_abs')

attribute [local ext] GalilVM

variable {P : ℕ}

/-! ## 1. One tape action per counter -/

/-- The single action a local tick performs on one counter tape. -/
inductive Op
  | keep | push | pop | reset
  deriving DecidableEq

def Op.apply : Op → STape Seg → STape Seg
  | .keep, t => t
  | .push, t => LocalCounter.push t
  | .pop, t => LocalCounter.pop t
  | .reset, t => LocalCounter.resetSeg t

def Op.abs : Op → GalilScaffoldCounter.Counter → GalilScaffoldCounter.Counter
  | .keep, c => c
  | .push, c => GalilScaffoldCounter.inc c
  | .pop, c => GalilScaffoldCounter.dec c
  | .reset, _ => GalilScaffoldCounter.reset

def Op.val : Op → ℕ → ℕ
  | .keep, v => v
  | .push, v => v + 1
  | .pop, v => v - 1
  | .reset, _ => 0

theorem tapeLocal_op (o : Op) (t : STape Seg) : TapeLocal t (o.apply t) := by
  cases o
  · exact tapeLocal_refl _
  · exact tapeLocal_push _
  · exact tapeLocal_pop _
  · exact tapeLocal_resetSeg _

/-- Sign and positivity side conditions of an op. -/
def Op.Ok (o : Op) (t : STape Seg) (b : Bool) : Prop :=
  (o = .push → b = true) ∧ (o = .pop → b = true ∧ 0 < LocalCounter.val t)

theorem absCtr_op {o : Op} {t : STape Seg} {b : Bool} (h : o.Ok t b) :
    LocalCounter.absCtr (o.apply t) b = o.abs (LocalCounter.absCtr t b) := by
  cases o
  · rfl
  · rw [h.1 rfl]
    exact PalPeg.LocalTick1.absCtr_push_pol t rfl
  · obtain ⟨hb, hv⟩ := h.2 rfl
    rw [hb]
    exact PalPeg.LocalTick1.absCtr_pop_pol hv rfl
  · exact LocalCounter.absCtr_reset _ _

theorem segCtr_op {o : Op} {t : STape Seg} {v : ℕ} (hs : LocalCounter.SegCtr t v)
    (hp : o = .pop → 0 < LocalCounter.val t) :
    LocalCounter.SegCtr (o.apply t) (o.val v) := by
  cases o
  · exact hs
  · exact LocalCounter.segCtr_push hs
  · have hv : LocalCounter.val t = v := LocalCounter.val_eq_of_segCtr hs
    have hpos := hp rfl
    have hs' : LocalCounter.SegCtr t (v - 1 + 1) := by
      rw [show v - 1 + 1 = v by omega]; exact hs
    exact LocalCounter.segCtr_pop hs'
  · exact LocalCounter.segCtr_reset t

theorem val_op {o : Op} {t : STape Seg} {v : ℕ} (hs : LocalCounter.SegCtr t v)
    (hp : o = .pop → 0 < LocalCounter.val t) :
    LocalCounter.val (o.apply t) = o.val v :=
  LocalCounter.val_eq_of_segCtr (segCtr_op hs hp)

/-- The op on a whole mirror bank. -/
def mirOp {k : ℕ} (o : Op) (m : Mirrored k) : Mirrored k := ⟨o.apply m.src, fun i => o.apply (m.mir i)⟩

theorem mirLocal_op {k : ℕ} (o : Op) (m : Mirrored k) : MirLocal m (mirOp o m) :=
  ⟨tapeLocal_op _ _, fun _ => tapeLocal_op _ _⟩

theorem shaped_op {k : ℕ} {o : Op} {m : Mirrored k} {v : ℕ} (hs : Shaped m v)
    (hp : o = .pop → 0 < v) : Shaped (mirOp o m) (o.val v) := by
  have hv : LocalCounter.val m.src = v := LocalCounter.val_eq_of_segCtr hs.1
  refine ⟨segCtr_op hs.1 (by rw [hv]; exact hp), fun i => ?_⟩
  have hvi : LocalCounter.val (m.mir i) = v := LocalCounter.val_eq_of_segCtr (hs.2 i)
  exact segCtr_op (hs.2 i) (by rw [hvi]; exact hp)

/-! ## 2. A bank tick: one op per logical counter -/

/-- The physical bank after applying `f c` on the tape of each counter `c`. -/
noncomputable def bankStep (f : Ctr → Op) (x : GalilVML P) : Fin P → STape Seg := by
  classical
  exact fun j => if h : ∃ c, x.roles c = j then (f (Classical.choose h)).apply (x.phys j)
    else x.phys j

theorem bankStep_role {x : GalilVML P} (hinj : RolesInjective x) (f : Ctr → Op) (c : Ctr) :
    bankStep f x (x.roles c) = (f c).apply (x.phys (x.roles c)) := by
  have h : ∃ d, x.roles d = x.roles c := ⟨c, rfl⟩
  have hc : Classical.choose h = c := hinj (Classical.choose_spec h)
  simp only [bankStep, dif_pos h, hc]

theorem tapeLocal_bankStep (f : Ctr → Op) (x : GalilVML P) (j : Fin P) :
    TapeLocal (x.phys j) (bankStep f x j) := by
  unfold bankStep
  split
  · exact tapeLocal_op _ _
  · exact tapeLocal_refl _

/-- One bank tick: every counter tape and every mirror bank takes its op. -/
noncomputable def bankTick (f : Ctr → Op) (x : GalilVML P) : GalilVML P :=
  { x with phys := bankStep f x,
           radiusMir := mirOp (f .radius) x.radiusMir,
           lowerMir := mirOp (f .lower) x.lowerMir,
           lengthMir := mirOp (f .length) x.lengthMir }

/-- The side conditions of a bank tick. -/
def BankOk (f : Ctr → Op) (x : GalilVML P) : Prop :=
  ∀ c, (f c).Ok (x.phys (x.roles c)) (x.pol c)

theorem absCtrs_bankTick {x : GalilVML P} (hinj : RolesInjective x) {f : Ctr → Op}
    (hok : BankOk f x) (c : Ctr) :
    absCtrs (bankTick f x) c = (f c).abs (absCtrs x c) := by
  show LocalCounter.absCtr (bankStep f x (x.roles c)) (x.pol c) = _
  rw [bankStep_role hinj]
  exact absCtr_op (hok c)

/-- A bank tick plus arbitrary *view* moves, each one of the four view actions,
and arbitrary finite-control and fpp-buffer updates, is one local step. -/
theorem stepLocal_bank (f : Ctr → Op) (x y : GalilVML P)
    (hp : y.phys = bankStep f x)
    (h1 : y.radiusMir = mirOp (f .radius) x.radiusMir)
    (h2 : y.lowerMir = mirOp (f .lower) x.lowerMir)
    (h3 : y.lengthMir = mirOp (f .length) x.lengthMir)
    (hl : ViewLocal x.left y.left) (hc : ViewLocal x.center y.center)
    (hr : ViewLocal x.right y.right) (hw : ViewLocal x.walkerView y.walkerView)
    (hfw : ViewLocal x.fppWalker y.fppWalker)
    (hdp : BufLocal x.dpBuf y.dpBuf) (hfb : BufLocal x.fppBuf y.fppBuf) :
    StepLocal x y := by
  refine ⟨fun j => ?_, ?_, ?_, ?_, hl, hc, hr, hw, hfw, hdp, hfb⟩
  · rw [hp]; exact tapeLocal_bankStep f x j
  · rw [h1]; exact mirLocal_op _ _
  · rw [h2]; exact mirLocal_op _ _
  · rw [h3]; exact mirLocal_op _ _

theorem inv_bankTick {x : GalilVML P} (hinv : Inv x) {f : Ctr → Op}
    (hpop : ∀ c, f c = .pop → 0 < LocalCounter.val (x.phys (x.roles c))) :
    Inv (bankTick f x) := by
  have hinj := hinv.roles
  obtain ⟨vr, hvr⟩ := hinv.radiusShaped
  obtain ⟨vw, hvw⟩ := hinv.lowerShaped
  obtain ⟨vl, hvl⟩ := hinv.lengthShaped
  have hsrc : ∀ {k : ℕ} {m : Mirrored k} {v : ℕ} {c : Ctr}, Shaped m v →
      m.src = x.phys (x.roles c) → (f c = .pop → 0 < v) := by
    intro k m v c hs he hp
    have := hpop c hp
    rw [← he, LocalCounter.val_eq_of_segCtr hs.1] at this
    exact this
  refine ⟨hinj, ⟨?_, ?_, ?_⟩, hinv.views,
    ⟨_, shaped_op hvr (hsrc hvr hinv.attached.1)⟩,
    ⟨_, shaped_op hvw (hsrc hvw hinv.attached.2.1)⟩,
    ⟨_, shaped_op hvl (hsrc hvl hinv.attached.2.2)⟩, ?_⟩
  · show (f .radius).apply x.radiusMir.src = bankStep f x (x.roles .radius)
    rw [bankStep_role hinj, hinv.attached.1]
  · show (f .lower).apply x.lowerMir.src = bankStep f x (x.roles .lower)
    rw [bankStep_role hinj, hinv.attached.2.1]
  · show (f .length).apply x.lengthMir.src = bankStep f x (x.roles .length)
    rw [bankStep_role hinj, hinv.attached.2.2]
  · intro c
    obtain ⟨v, hv⟩ := hinv.shaped c
    exact ⟨_, show LocalCounter.SegCtr (bankStep f x (x.roles c)) _ by
      rw [bankStep_role hinj]; exact segCtr_op hv (hpop c)⟩

/-- `Inv` only reads the bank, the mirrors and the views. -/
theorem inv_congr {x y : GalilVML P} (hinv : Inv x) (hr : y.roles = x.roles)
    (hp : y.phys = x.phys) (h1 : y.radiusMir = x.radiusMir) (h2 : y.lowerMir = x.lowerMir)
    (h3 : y.lengthMir = x.lengthMir) (hv : ViewsWF y) : Inv y := by
  obtain ⟨i1, i2, _, i4, i5, i6, i7⟩ := hinv
  refine ⟨?_, ?_, hv, ?_, ?_, ?_, ?_⟩
  · intro a b h; rw [hr] at h; exact i1 h
  · unfold MirrorsAttached; rw [hr, hp, h1, h2, h3]; exact i2
  · rw [h1]; exact i4
  · rw [h2]; exact i5
  · rw [h3]; exact i6
  · intro c; show ∃ v, LocalCounter.SegCtr (y.phys (y.roles c)) v; rw [hr, hp]; exact i7 c


/-- The abstract image of a bank tick. -/
def bankAbs (f : Ctr → Op) (s : GalilVM) : GalilVM :=
  { s with cycle := (f .cycle).abs s.cycle, remaining := (f .remaining).abs s.remaining,
           radius := (f .radius).abs s.radius, length := (f .length).abs s.length,
           replay := (f .replay).abs s.replay, lower := (f .lower).abs s.lower,
           fpp := { s.fpp with work := (f .fppWork).abs s.fpp.work },
           search := { s.search with span := (f .span).abs s.search.span,
                                     work := (f .work).abs s.search.work,
                                     debt := (f .debt).abs s.search.debt } }

theorem abs'_bankTick {x : GalilVML P} (hinj : RolesInjective x) {f : Ctr → Op}
    (hok : BankOk f x) : abs' (bankTick f x) = bankAbs f (abs' x) := by
  have h := absCtrs_bankTick hinj hok
  ext
  · rfl
  · rfl
  · rfl
  · rfl
  · exact h .cycle
  · exact h .remaining
  · exact h .radius
  · exact h .length
  · exact h .replay
  · exact congrArg (fun w => ({(abs' x).fpp with work := w} : FppControl.State)) (h .fppWork)
  · show (⟨x.searchMode, x.searchFinalStage, absCtrs (bankTick f x) .span,
        absCtrs (bankTick f x) .work, absCtrs (bankTick f x) .debt, x.searchQuarter⟩ :
          GalilScaffoldSearchFinish.State) = _
    rw [h .span, h .work, h .debt]
    rfl
  · rfl
  · exact h .lower
  · rfl
  · rfl


theorem ok_keep (t : STape Seg) (b : Bool) : Op.Ok .keep t b :=
  ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

theorem ok_push (t : STape Seg) {b : Bool} (hb : b = true) : Op.Ok .push t b :=
  ⟨fun _ => hb, fun h => (nomatch h)⟩

theorem ok_pop {t : STape Seg} {b : Bool} (hb : b = true) (hv : 0 < LocalCounter.val t) :
    Op.Ok .pop t b :=
  ⟨fun h => (nomatch h), fun _ => ⟨hb, hv⟩⟩

theorem ok_reset (t : STape Seg) (b : Bool) : Op.Ok .reset t b :=
  ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

/-- The bank tape of `c` after a bank tick. -/
theorem bankTick_phys {x : GalilVML P} (hinj : RolesInjective x) (f : Ctr → Op) (c : Ctr) :
    (bankTick f x).phys ((bankTick f x).roles c) = (f c).apply (x.phys (x.roles c)) :=
  bankStep_role hinj f c

/-! ## 3. Locality of a tick that moves no counter -/

theorem stepLocal_noBank (x y : GalilVML P) (hp : y.phys = x.phys)
    (h1 : y.radiusMir = x.radiusMir) (h2 : y.lowerMir = x.lowerMir)
    (h3 : y.lengthMir = x.lengthMir)
    (hl : ViewLocal x.left y.left) (hc : ViewLocal x.center y.center)
    (hr : ViewLocal x.right y.right) (hw : ViewLocal x.walkerView y.walkerView)
    (hfw : ViewLocal x.fppWalker y.fppWalker)
    (hdp : BufLocal x.dpBuf y.dpBuf) (hfb : BufLocal x.fppBuf y.fppBuf) :
    StepLocal x y := by
  refine ⟨fun j => ?_, ?_, ?_, ?_, hl, hc, hr, hw, hfw, hdp, hfb⟩
  · rw [hp]; exact tapeLocal_refl _
  · rw [h1]; exact ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩
  · rw [h2]; exact ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩
  · rw [h3]; exact ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩

/-! ## 4. One pointwise action on one fpp tape -/

/-- Act with `g` on tape `i` only. -/
def atTape (i : Fin 9) (g : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) :
    Fin 9 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape :=
  fun j t => if j = i then g t else t

/-- The fpp buffer after one action on tape `i`. -/
def bufAt (i : Fin 9) (g : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape)
    (b : LocalBuffers.Buffered 9) : LocalBuffers.Buffered 9 :=
  LocalBuffers.stepL (fun ts j => atTape i g j (ts j)) b

theorem abs_bufAt (i : Fin 9) (g : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape)
    (b : LocalBuffers.Buffered 9) :
    LocalBuffers.abs (bufAt i g b)
      = Function.update (LocalBuffers.abs b) i (g (LocalBuffers.abs b i)) := by
  rw [bufAt, LocalBuffers.abs_stepL]
  funext j
  by_cases h : j = i
  · subst h; simp [atTape]
  · simp [atTape, h]

theorem bufLocal_bufAt (i : Fin 9) (g : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape)
    (b : LocalBuffers.Buffered 9) : BufLocal b (bufAt i g b) :=
  bufLocal_stepL (atTape i g) b

/-- `FppControl.tape` read through the buffer abstraction. -/
theorem tape_bufAt (x : GalilVML P) (i : Fin 9) (g : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) :
    (⟨⟨x.fppPc, LocalBuffers.abs (bufAt i g x.fppBuf)⟩, x.fppDone⟩ : GalilScaffoldControl.Machine 9)
      = FppControl.tape (abs' x).fpp i g := by
  rw [abs_bufAt]; rfl

/-- Every fpp-side update is invisible outside the fpp projection. -/
theorem abs'_fppSet (x : GalilVML P) (b : LocalBuffers.Buffered 9) (pc : ℕ) (d : Bool)
    (m : FppControl.Mode) (fs : Bool) (w : InputView) :
    abs' { x with
      fppBuf := b, fppPc := pc, fppDone := d, fppMode := m, fppFinalStage := fs,
      fppWalker := w }
      = fppLens.set (abs' x) { (abs' x).fpp with
          mode := m, program := ⟨⟨pc, LocalBuffers.abs b⟩, d⟩, finalStage := fs,
          walker := absPlace w } :=
  rfl

/-! ## 5. `shift_one`: two local steps -/

/-- First step: `remaining--`, `radius--`, `length--`, `cycle++`, C and L one
place right, the chain's `shiftOne`. -/
def shiftOps1 : Ctr → Op
  | .remaining => .pop
  | .radius => .pop
  | .length => .pop
  | .cycle => .push
  | _ => .keep

/-- Second step: the second `length--`, the second `cycle++`, L's second move. -/
def shiftOps2 : Ctr → Op
  | .length => .pop
  | .cycle => .push
  | _ => .keep

noncomputable def shiftMid (w : GalilScaffoldChainWatch.State) (x : GalilVML P) : GalilVML P :=
  { bankTick shiftOps1 x with
      center := LocalInputView.moveRight x.center,
      left := LocalInputView.moveRight x.left,
      chain := .watch (chainShiftOne w) }

noncomputable def shiftVm (w : GalilScaffoldChainWatch.State) (x : GalilVML P) : GalilVML P :=
  { bankTick shiftOps2 (shiftMid w x) with
      left := LocalInputView.moveRight (LocalInputView.moveRight x.left) }

/-- The counter side conditions of a local shift unit. -/
structure ShiftCounters (x : GalilVML P) : Prop where
  remPol : x.pol .remaining = true
  radPol : x.pol .radius = true
  lenPol : x.pol .length = true
  cycPol : x.pol .cycle = true
  remPos : 0 < LocalCounter.val (x.phys (x.roles .remaining))
  radPos : 0 < LocalCounter.val (x.phys (x.roles .radius))
  lenTwo : 2 ≤ LocalCounter.val (x.phys (x.roles .length))

theorem shiftOps1_ok {x : GalilVML P} (h : ShiftCounters x) : BankOk shiftOps1 x := by
  intro c
  cases c
  · exact ok_push _ h.cycPol
  · exact ok_pop h.remPol h.remPos
  · exact ok_pop h.radPol h.radPos
  · exact ok_pop h.lenPol (by have := h.lenTwo; omega)
  all_goals exact ok_keep _ _

theorem val_pop_pos {t : STape Seg} (h : 2 ≤ LocalCounter.val t) :
    0 < LocalCounter.val (LocalCounter.pop t) := by
  have hv : LocalCounter.val t = (LocalCounter.val t - 2 + 1) + 1 := by omega
  rw [LocalCounter.val_pop hv]; omega

theorem shiftOps2_ok {x : GalilVML P} (hinj : RolesInjective x) (h : ShiftCounters x)
    (w : GalilScaffoldChainWatch.State) : BankOk shiftOps2 (shiftMid w x) := by
  intro c
  cases c
  · exact ok_push _ h.cycPol
  · exact ok_keep _ _
  · exact ok_keep _ _
  · refine ok_pop h.lenPol ?_
    show 0 < LocalCounter.val ((bankTick shiftOps1 x).phys ((bankTick shiftOps1 x).roles .length))
    rw [bankTick_phys hinj]
    exact val_pop_pos h.lenTwo
  all_goals exact ok_keep _ _

theorem stepLocalN_shiftVm (w : GalilScaffoldChainWatch.State) (x : GalilVML P) :
    StepLocalN 2 x (shiftVm w x) :=
  stepLocalN_trans 1 1
    (stepLocalN_one (stepLocal_bank shiftOps1 x (shiftMid w x) rfl rfl rfl rfl
      (viewLocal_moveRight x.left) (viewLocal_moveRight x.center) (viewLocal_refl _)
      (viewLocal_refl _) (viewLocal_refl _) (bufLocal_refl _) (bufLocal_refl _)))
    (stepLocalN_one (stepLocal_bank shiftOps2 (shiftMid w x) (shiftVm w x) rfl rfl rfl rfl
      (viewLocal_moveRight (LocalInputView.moveRight x.left)) (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _)
      (viewLocal_refl _) (bufLocal_refl _) (bufLocal_refl _)))

theorem inv_shiftVm {x : GalilVML P} (hinv : Inv x) (h : ShiftCounters x)
    (w : GalilScaffoldChainWatch.State) : Inv (shiftVm w x) := by
  have hinj := hinv.roles
  have i1 : Inv (bankTick shiftOps1 x) := inv_bankTick hinv (fun c hc => by
    cases c
    · exact (nomatch hc)
    · exact h.remPos
    · exact h.radPos
    · have := h.lenTwo; omega
    all_goals exact (nomatch hc))
  have i2 : Inv (shiftMid w x) := inv_congr i1 rfl rfl rfl rfl rfl
    ⟨PalPeg.LocalTick1.WF_moveRight hinv.views.1, PalPeg.LocalTick1.WF_moveRight hinv.views.2.1,
      hinv.views.2.2.1, hinv.views.2.2.2.1, hinv.views.2.2.2.2⟩
  have i3 : Inv (bankTick shiftOps2 (shiftMid w x)) := inv_bankTick i2 (fun c hc => by
    cases c
    · exact (nomatch hc)
    · exact (nomatch hc)
    · exact (nomatch hc)
    · show 0 < LocalCounter.val ((bankTick shiftOps1 x).phys
            ((bankTick shiftOps1 x).roles .length))
      rw [bankTick_phys hinj]
      exact val_pop_pos h.lenTwo
    all_goals exact (nomatch hc))
  exact inv_congr i3 rfl rfl rfl rfl rfl
    ⟨PalPeg.LocalTick1.WF_moveRight i2.views.1, i2.views.2.1,
      i2.views.2.2.1, i2.views.2.2.2.1, i2.views.2.2.2.2⟩

/-- The abstract image of the local shift unit. -/
theorem abs'_shiftVm {x : GalilVML P} (hinv : Inv x) (h : ShiftCounters x)
    (w : GalilScaffoldChainWatch.State)
    (haC : Ahead x.center x.pending) (haL : Ahead x.left x.pending)
    (haL' : Ahead (LocalInputView.moveRight x.left) x.pending)
    (hcC : GalilScaffoldChainVerifier.canRight (abs' x).center)
    (hcL : GalilScaffoldChainVerifier.canRight (abs' x).left)
    (hcL' : GalilScaffoldChainVerifier.canRight
      (GalilScaffoldChainVerifier.right (abs' x).left)) :
    abs' (shiftVm w x)
      = shiftLens.set (abs' x)
          ⟨shiftTick ⟨(abs' x).center, (abs' x).left, (abs' x).remaining, (abs' x).radius,
              (abs' x).length⟩,
            .watch (chainShiftOne w),
            GalilScaffoldCounter.inc (GalilScaffoldCounter.inc (abs' x).cycle)⟩ := by
  have hinj := hinv.roles
  have hinj1 : RolesInjective (shiftMid w x) := hinj
  have hC : absHead' (LocalInputView.moveRight x.center) x.pending
      = GalilScaffoldChainVerifier.right (abs' x).center :=
    PalPeg.LocalArrival.moveRight_ok hinv.views.2.1 haC hcC
  have hL : absHead' (LocalInputView.moveRight x.left) x.pending
      = GalilScaffoldChainVerifier.right (abs' x).left :=
    PalPeg.LocalArrival.moveRight_ok hinv.views.1 haL hcL
  have hL2 : absHead' (LocalInputView.moveRight (LocalInputView.moveRight x.left)) x.pending
      = GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right (abs' x).left) := by
    rw [PalPeg.LocalArrival.moveRight_ok (PalPeg.LocalTick1.WF_moveRight hinv.views.1) haL'
      (by rw [hL]; exact hcL'), hL]
  rw [show abs' (shiftVm w x)
      = { abs' (bankTick shiftOps2 (shiftMid w x)) with
          left := absHead' (LocalInputView.moveRight (LocalInputView.moveRight x.left))
            x.pending } from rfl,
    abs'_bankTick hinj1 (shiftOps2_ok hinj h w),
    show abs' (shiftMid w x)
      = { abs' (bankTick shiftOps1 x) with
          center := absHead' (LocalInputView.moveRight x.center) x.pending,
          left := absHead' (LocalInputView.moveRight x.left) x.pending,
          chain := .watch (chainShiftOne w) } from rfl,
    abs'_bankTick hinj (shiftOps1_ok h), hC, hL, hL2]
  rfl


/-! ## 6. `copy`/`home`: one action on SOURCE (and the walker, the work counter) -/

def workOps : Ctr → Op
  | .fppWork => .pop
  | _ => .keep

/-- `copy_one`: SOURCE writes the walker's symbol and moves right, `work--`,
the walker one place left. -/
noncomputable def copyVm (a : Fin 3) (x : GalilVML P) : GalilVML P :=
  { bankTick workOps x with
      fppBuf := bufAt 7 (fun t => GalilScaffoldTape.moveRight
        (GalilScaffoldTape.write t (GalilFppPreparation.symbol a))) x.fppBuf,
      fppWalker := LocalInputView.moveLeftV x.fppWalker }

theorem workOps_ok {x : GalilVML P} (hp : x.pol .fppWork = true)
    (hv : 0 < LocalCounter.val (x.phys (x.roles .fppWork))) : BankOk workOps x := by
  intro c
  cases c
  all_goals first | exact ok_pop hp hv | exact ok_keep _ _

theorem abs'_copyVm {x : GalilVML P} (hinj : RolesInjective x) (a : Fin 3)
    (hp : x.pol .fppWork = true) (hv : 0 < LocalCounter.val (x.phys (x.roles .fppWork)))
    (hprop : PalPeg.LocalChain.ProperView x.fppWalker) :
    abs' (copyVm a x)
      = fppLens.set (abs' x) { (abs' x).fpp with
          program := FppControl.tape (abs' x).fpp 7 (fun t => GalilScaffoldTape.moveRight
            (GalilScaffoldTape.write t (GalilFppPreparation.symbol a))),
          work := GalilScaffoldCounter.dec (abs' x).fpp.work,
          walker := GalilScaffoldPlace.left (abs' x).fpp.walker } := by
  rw [show abs' (copyVm a x)
      = { abs' (bankTick workOps x) with
          fpp := { (abs' (bankTick workOps x)).fpp with
            program := ⟨⟨x.fppPc, LocalBuffers.abs (bufAt 7 (fun t => GalilScaffoldTape.moveRight
              (GalilScaffoldTape.write t (GalilFppPreparation.symbol a))) x.fppBuf)⟩, x.fppDone⟩,
            walker := absPlace (LocalInputView.moveLeftV x.fppWalker) } } from rfl,
    abs'_bankTick hinj (workOps_ok hp hv), PalPeg.LocalChain.absPlace_moveLeftV hprop, abs_bufAt]
  rfl

/-- `copy_done`: SOURCE writes `END`, the fpp mode turns to `home`. -/
def copyDoneVm (c : Control) (x : GalilVML P) : GalilVML P :=
  { x with
      fppBuf := bufAt 7 (fun t => GalilScaffoldTape.write t 5) x.fppBuf,
      fppMode := .home,
      fppFinalStage := (GalilScaffoldPlace.read (absPlace x.fppWalker)).isNone,
      ctl := c }

theorem abs'_copyDoneVm (c : Control) (x : GalilVML P) :
    abs' (copyDoneVm c x)
      = fppLens.set (abs' x) { (abs' x).fpp with
          program := FppControl.tape (abs' x).fpp 7 (fun t => GalilScaffoldTape.write t 5),
          mode := .home,
          finalStage := (GalilScaffoldPlace.read (abs' x).fpp.walker).isNone } := by
  rw [show abs' (copyDoneVm c x)
      = fppLens.set (abs' x) { (abs' x).fpp with
          program := ⟨⟨x.fppPc, LocalBuffers.abs
            (bufAt 7 (fun t => GalilScaffoldTape.write t 5) x.fppBuf)⟩, x.fppDone⟩,
          mode := .home,
          finalStage := (GalilScaffoldPlace.read (abs' x).fpp.walker).isNone } from rfl,
    abs_bufAt]
  rfl

/-- `home_start`: `fpp.start()` is a pc load, pure finite control. -/
def homeStartVm (c : Control) (x : GalilVML P) : GalilVML P :=
  { x with fppPc := 320, fppDone := false, fppMode := .run, ctl := c }

theorem abs'_homeStartVm (c : Control) (x : GalilVML P) :
    abs' (homeStartVm c x)
      = fppLens.set (abs' x) { (abs' x).fpp with
          program := GalilScaffoldControl.start 320 (abs' x).fpp.program, mode := .run } :=
  rfl

/-- `home_step`: SOURCE one cell left. -/
def homeStepVm (x : GalilVML P) : GalilVML P :=
  { x with fppBuf := bufAt 7 GalilScaffoldTape.moveLeft x.fppBuf }

theorem abs'_homeStepVm (x : GalilVML P) :
    abs' (homeStepVm x)
      = fppLens.set (abs' x) { (abs' x).fpp with
          program := FppControl.tape (abs' x).fpp 7 GalilScaffoldTape.moveLeft } := by
  rw [show abs' (homeStepVm x)
      = fppLens.set (abs' x) { (abs' x).fpp with
          program := ⟨⟨x.fppPc, LocalBuffers.abs
            (bufAt 7 GalilScaffoldTape.moveLeft x.fppBuf)⟩, x.fppDone⟩ } from rfl,
    abs_bufAt]
  rfl

/-! ## 7. `fpp`: a quantum of `q` pointwise program steps -/

/-- `n` pointwise program steps on the fpp buffer, the `k`-th by `g k`. -/
def fppRunBuf (g : ℕ → Fin 9 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) :
    ℕ → LocalBuffers.Buffered 9 → LocalBuffers.Buffered 9
  | 0, b => b
  | n + 1, b => fppRunBuf g n (LocalBuffers.stepL (fun ts i => g n i (ts i)) b)

theorem stepLocalN_fppRun (g : ℕ → Fin 9 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) :
    ∀ (n : ℕ) (x : GalilVML P), StepLocalN n x { x with fppBuf := fppRunBuf g n x.fppBuf } := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      exact ⟨{ x with fppBuf := LocalBuffers.stepL (fun ts i => g n i (ts i)) x.fppBuf },
        stepLocal_noBank _ _ rfl rfl rfl rfl (viewLocal_refl _) (viewLocal_refl _)
          (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _) (bufLocal_refl _)
          (bufLocal_stepL (g n) _),
        ih _⟩

/-- `fpp_slice`: the quantum ran, the program is not halted. -/
def sliceVm (g : ℕ → Fin 9 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) (n pc : ℕ)
    (x : GalilVML P) : GalilVML P :=
  { x with fppBuf := fppRunBuf g n x.fppBuf, fppPc := pc, fppDone := false }

theorem abs'_sliceVm (g : ℕ → Fin 9 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape)
    (n pc : ℕ) (x : GalilVML P) :
    abs' (sliceVm g n pc x)
      = fppLens.set (abs' x) { (abs' x).fpp with
          program := ⟨⟨pc, LocalBuffers.abs (fppRunBuf g n x.fppBuf)⟩, false⟩ } :=
  rfl

theorem stepLocalN_sliceVm (g : ℕ → Fin 9 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape)
    (n pc : ℕ) (x : GalilVML P) : StepLocalN (n + 1) x (sliceVm g n pc x) :=
  stepLocalN_trans n 1 (stepLocalN_fppRun g n x)
    (stepLocalN_one (stepLocal_noBank _ _ rfl rfl rfl rfl (viewLocal_refl _) (viewLocal_refl _)
      (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _) (bufLocal_refl _)
      (bufLocal_refl _)))

/-- `fpp_done`: the quantum reached the halt; then
`marks.move(1)` and `marks.write(FIRST); marks.move(1)` — two more tape actions. -/
def doneVm (first : Fin 9) (g : ℕ → Fin 9 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape)
    (n pc : ℕ) (c : Control) (x : GalilVML P) : GalilVML P :=
  { x with
      fppBuf := bufAt 8 (fun t => GalilScaffoldTape.moveRight (GalilScaffoldTape.write t first))
        (bufAt 8 GalilScaffoldTape.moveRight (fppRunBuf g n x.fppBuf)),
      fppPc := pc, fppDone := true, ctl := c }

theorem abs'_doneVm (first : Fin 9)
    (g : ℕ → Fin 9 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape)
    (n pc : ℕ) (c : Control) (x : GalilVML P) :
    abs' (doneVm first g n pc c x)
      = fppLens.set (abs' x) { (abs' x).fpp with
          program := markNew ⟨⟨pc, LocalBuffers.abs (fppRunBuf g n x.fppBuf)⟩, true⟩ first } := by
  rw [show abs' (doneVm first g n pc c x)
      = fppLens.set (abs' x) { (abs' x).fpp with
          program := ⟨⟨pc, LocalBuffers.abs (bufAt 8
            (fun t => GalilScaffoldTape.moveRight (GalilScaffoldTape.write t first))
            (bufAt 8 GalilScaffoldTape.moveRight (fppRunBuf g n x.fppBuf)))⟩, true⟩ } from rfl,
    abs_bufAt, abs_bufAt, Function.update_self, Function.update_idem]
  rfl

theorem stepLocalN_doneVm (first : Fin 9)
    (g : ℕ → Fin 9 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape)
    (n pc : ℕ) (c : Control) (x : GalilVML P) :
    StepLocalN (n + 2) x (doneVm first g n pc c x) :=
  stepLocalN_trans n 2 (stepLocalN_fppRun g n x)
    (stepLocalN_trans 1 1
      (stepLocalN_one (stepLocal_noBank _
        { x with fppBuf := bufAt 8 GalilScaffoldTape.moveRight (fppRunBuf g n x.fppBuf) }
        rfl rfl rfl rfl (viewLocal_refl _) (viewLocal_refl _)
        (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _) (bufLocal_refl _)
        (bufLocal_bufAt _ _ _)))
      (stepLocalN_one (stepLocal_noBank _ _ rfl rfl rfl rfl (viewLocal_refl _) (viewLocal_refl _)
        (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _) (bufLocal_refl _)
        (bufLocal_bufAt _ _ _))))

/-! ## 8. `markEnd`/`choose`/`rewind`: one action on MARKS -/

/-- MARKS one cell in direction `f`, with a new controller record. -/
def marksVm (f : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) (c : Control)
    (x : GalilVML P) : GalilVML P :=
  { x with fppBuf := bufAt 8 f x.fppBuf, ctl := c }

theorem abs'_marksVm (f : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) (c : Control)
    (x : GalilVML P) :
    abs' (marksVm f c x) = fppLens.set (abs' x) (markStep (abs' x).fpp f) := by
  rw [show abs' (marksVm f c x)
      = fppLens.set (abs' x) { (abs' x).fpp with
          program := ⟨⟨x.fppPc, LocalBuffers.abs (bufAt 8 f x.fppBuf)⟩, x.fppDone⟩ } from rfl,
    abs_bufAt]
  rfl

theorem abs'_marksVm_rewind (f : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) (c : Control)
    (x : GalilVML P) :
    abs' (marksVm f c x)
      = rewindLens.set (abs' x) { rewindLens.get (abs' x) with fpp := markStep (abs' x).fpp f } := by
  rw [abs'_marksVm]; rfl

theorem stepLocal_marksVm (f : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) (c : Control)
    (x : GalilVML P) : StepLocal x (marksVm f c x) :=
  stepLocal_noBank _ _ rfl rfl rfl rfl (viewLocal_refl _) (viewLocal_refl _)
    (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _) (bufLocal_refl _)
    (bufLocal_bufAt _ _ _)

/-- `choose_select`, first step: `length := reset`, `radius := reset`. -/
def chooseOps1 : Ctr → Op
  | .length => .reset
  | .radius => .reset
  | _ => .keep

/-- …second step: `length++`, so `length = 1`. -/
def chooseOps2 : Ctr → Op
  | .length => .push
  | _ => .keep

noncomputable def chooseVm (c : Control) (x : GalilVML P) : GalilVML P :=
  { bankTick chooseOps2 (bankTick chooseOps1 x) with ctl := c }

theorem chooseOps1_ok (x : GalilVML P) : BankOk chooseOps1 x := by
  intro c
  cases c
  all_goals first | exact ok_reset _ _ | exact ok_keep _ _

theorem chooseOps2_ok {x : GalilVML P} (hp : x.pol .length = true) :
    BankOk chooseOps2 (bankTick chooseOps1 x) := by
  intro c
  cases c
  all_goals first | exact ok_push _ hp | exact ok_keep _ _

theorem abs'_chooseVm {x : GalilVML P} (hinj : RolesInjective x) (c : Control)
    (hp : x.pol .length = true)
    (hleft : absHead' x.left x.pending = absHead' x.right x.pending)
    (hcenter : absHead' x.center x.pending = absHead' x.right x.pending) :
    abs' (chooseVm c x)
      = rewindLens.set (abs' x) { rewindLens.get (abs' x) with
          left := (abs' x).right, center := (abs' x).right,
          length := GalilScaffoldCounter.ofNat 1, radius := GalilScaffoldCounter.reset } := by
  have hinj1 : RolesInjective (bankTick chooseOps1 x) := hinj
  rw [show abs' (chooseVm c x) = abs' (bankTick chooseOps2 (bankTick chooseOps1 x)) from rfl,
    abs'_bankTick hinj1 (chooseOps2_ok hp), abs'_bankTick hinj (chooseOps1_ok x)]
  ext
  · exact hleft
  · exact hcenter
  all_goals rfl

theorem stepLocalN_chooseVm (c : Control) (x : GalilVML P) : StepLocalN 2 x (chooseVm c x) :=
  stepLocalN_trans 1 1
    (stepLocalN_one (stepLocal_bank chooseOps1 x (bankTick chooseOps1 x) rfl rfl rfl rfl
      (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _)
      (viewLocal_refl _) (bufLocal_refl _) (bufLocal_refl _)))
    (stepLocalN_one (stepLocal_bank chooseOps2 (bankTick chooseOps1 x) (chooseVm c x)
      rfl rfl rfl rfl
      (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _)
      (viewLocal_refl _) (bufLocal_refl _) (bufLocal_refl _)))

/-- `rewind_done`: `fpp.reset()` is one `resetL` on the double buffer. -/
def rewindDoneVm (c : Control) (x : GalilVML P) : GalilVML P :=
  { x with fppBuf := LocalBuffers.resetL x.fppBuf, fppPc := 320, fppDone := true, ctl := c }

theorem abs'_rewindDoneVm {x : GalilVML P} (c : Control)
    (hclean : ∀ i, LocalBuffers.Cleared (LocalBuffers.idle x.fppBuf i)) :
    abs' (rewindDoneVm c x)
      = rewindLens.set (abs' x) { rewindLens.get (abs' x) with
          fpp := { (abs' x).fpp with
            program := GalilScaffoldControl.reset 320 (abs' x).fpp.program } } := by
  rw [show abs' (rewindDoneVm c x)
      = fppLens.set (abs' x) { (abs' x).fpp with
          program := ⟨⟨320, LocalBuffers.abs (LocalBuffers.resetL x.fppBuf)⟩, true⟩ } from rfl,
    LocalBuffers.abs_resetL_of_clean hclean]
  rfl

theorem stepLocal_rewindDoneVm (c : Control) (x : GalilVML P) :
    StepLocal x (rewindDoneVm c x) :=
  stepLocal_noBank _ _ rfl rfl rfl rfl (viewLocal_refl _) (viewLocal_refl _)
    (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _) (bufLocal_refl _)
    (bufLocal_resetL _)

/-- `rewind_one`: MARKS left, L left, `length++`. -/
def rewindOps1 : Ctr → Op
  | .length => .push
  | _ => .keep

/-- `rewind_pair`: also C left, `radius++`. -/
def rewindOps2 : Ctr → Op
  | .length => .push
  | .radius => .push
  | _ => .keep

noncomputable def rewindOneVm (c : Control) (x : GalilVML P) : GalilVML P :=
  { bankTick rewindOps1 x with
      fppBuf := bufAt 8 GalilScaffoldTape.moveLeft x.fppBuf,
      left := LocalInputView.moveLeftV x.left,
      ctl := c }

noncomputable def rewindPairVm (c : Control) (x : GalilVML P) : GalilVML P :=
  { bankTick rewindOps2 x with
      fppBuf := bufAt 8 GalilScaffoldTape.moveLeft x.fppBuf,
      left := LocalInputView.moveLeftV x.left,
      center := LocalInputView.moveLeftV x.center,
      ctl := c }

theorem rewindOps1_ok {x : GalilVML P} (hp : x.pol .length = true) : BankOk rewindOps1 x := by
  intro c
  cases c
  all_goals first | exact ok_push _ hp | exact ok_keep _ _

theorem rewindOps2_ok {x : GalilVML P} (hp : x.pol .length = true)
    (hr : x.pol .radius = true) : BankOk rewindOps2 x := by
  intro c
  cases c
  all_goals first | exact ok_push _ hp | exact ok_push _ hr | exact ok_keep _ _

theorem abs'_rewindOneVm {x : GalilVML P} (hinj : RolesInjective x) (c : Control)
    (hp : x.pol .length = true) :
    abs' (rewindOneVm c x)
      = rewindLens.set (abs' x) { rewindLens.get (abs' x) with
          fpp := markStep (abs' x).fpp GalilScaffoldTape.moveLeft,
          left := GalilScaffoldInputHead.left (abs' x).left,
          length := GalilScaffoldCounter.inc (abs' x).length } := by
  rw [show abs' (rewindOneVm c x)
      = { abs' (bankTick rewindOps1 x) with
          left := absHead' (LocalInputView.moveLeftV x.left) x.pending,
          fpp := { (abs' (bankTick rewindOps1 x)).fpp with
            program := ⟨⟨x.fppPc, LocalBuffers.abs
              (bufAt 8 GalilScaffoldTape.moveLeft x.fppBuf)⟩, x.fppDone⟩ } } from rfl,
    abs'_bankTick hinj (rewindOps1_ok hp), PalPeg.LocalTick1.absHead'_moveLeft, abs_bufAt]
  rfl

theorem abs'_rewindPairVm {x : GalilVML P} (hinj : RolesInjective x) (c : Control)
    (hp : x.pol .length = true) (hr : x.pol .radius = true) :
    abs' (rewindPairVm c x)
      = rewindLens.set (abs' x) { rewindLens.get (abs' x) with
          fpp := markStep (abs' x).fpp GalilScaffoldTape.moveLeft,
          left := GalilScaffoldInputHead.left (abs' x).left,
          length := GalilScaffoldCounter.inc (abs' x).length,
          center := GalilScaffoldInputHead.left (abs' x).center,
          radius := GalilScaffoldCounter.inc (abs' x).radius } := by
  rw [show abs' (rewindPairVm c x)
      = { abs' (bankTick rewindOps2 x) with
          left := absHead' (LocalInputView.moveLeftV x.left) x.pending,
          center := absHead' (LocalInputView.moveLeftV x.center) x.pending,
          fpp := { (abs' (bankTick rewindOps2 x)).fpp with
            program := ⟨⟨x.fppPc, LocalBuffers.abs
              (bufAt 8 GalilScaffoldTape.moveLeft x.fppBuf)⟩, x.fppDone⟩ } } from rfl,
    abs'_bankTick hinj (rewindOps2_ok hp hr), PalPeg.LocalTick1.absHead'_moveLeft,
    PalPeg.LocalTick1.absHead'_moveLeft, abs_bufAt]
  rfl


/-! ## 9. The local phase ticks -/

open PalPeg.GalilTickFun3 (marksOf frameS_shiftOne frameS_copyOne frameS_copyEnd frameS_fppStart
  frameS_homeStep frameS_fppSlice frameS_fppDone frameS_markForward frameS_markBack frameS_choose
  frameS_fppReset frameS_rewindOne frameS_rewindPair)

/-- **The per-tick local budget of a phase tick**: the fpp quantum (`q ≤ 64`
pointwise program steps) plus the two MARKS actions of `markNew`. -/
def c₃ : ℕ := 66

/-- **The third slice of the local step relation**: the seven phase modes. -/
inductive TickL3 {P : ℕ} (S : Shared) (q : ℕ) (first : Fin 9) :
    GalilVML P → GalilVML P → Prop
  | shift_one (x : GalilVML P) (w : GalilScaffoldChainWatch.State)
      (hm : x.ctl.mode = .shift) (hr : x.ctl.replaying = false)
      (hw : x.chain = .watch w) (hctr : ShiftCounters x)
      (haC : Ahead x.center x.pending) (haL : Ahead x.left x.pending)
      (haL' : Ahead (LocalInputView.moveRight x.left) x.pending)
      (hcC : GalilScaffoldChainVerifier.canRight (abs' x).center)
      (hcL : GalilScaffoldChainVerifier.canRight (abs' x).left)
      (hcL' : GalilScaffoldChainVerifier.canRight
        (GalilScaffoldChainVerifier.right (abs' x).left)) :
      TickL3 S q first x (shiftVm w x)
  | shift_done (x : GalilVML P) (o : Bool)
      (hm : x.ctl.mode = .shift) (hr : x.ctl.replaying = false)
      (hp : ¬ (galilFrameS S q first).remainingPos (abs' x))
      (ho : refresh (galilFrameS S q first) (abs' x) x.ctl.output o) :
      TickL3 S q first x { x with ctl := { x.ctl with mode := .scan, output := o } }
  | copy_one (x : GalilVML P) (a : Fin 3)
      (hm : x.ctl.mode = .copy) (hr : x.ctl.replaying = false)
      (ha : GalilScaffoldPlace.read (absPlace x.fppWalker) = some a)
      (hprop : PalPeg.LocalChain.ProperView x.fppWalker)
      (hpol : x.pol .fppWork = true)
      (hv : 0 < LocalCounter.val (x.phys (x.roles .fppWork))) :
      TickL3 S q first x (copyVm a x)
  | copy_done (x : GalilVML P)
      (hm : x.ctl.mode = .copy) (hr : x.ctl.replaying = false)
      (hp : ¬ (galilFrameS S q first).remainingPos (abs' x)) :
      TickL3 S q first x (copyDoneVm { x.ctl with mode := .home } x)
  | home_start (x : GalilVML P)
      (hm : x.ctl.mode = .home) (hr : x.ctl.replaying = false)
      (hl : (galilFrameS S q first).atLeft (abs' x)) :
      TickL3 S q first x (homeStartVm { x.ctl with mode := .fpp } x)
  | home_step (x : GalilVML P)
      (hm : x.ctl.mode = .home) (hr : x.ctl.replaying = false)
      (hl : ¬ (galilFrameS S q first).atLeft (abs' x))
      (hne : ((abs' x).fpp.program.config.tapes 7).left ≠ []) :
      TickL3 S q first x (homeStepVm x)
  | fpp_slice (x : GalilVML P)
      (g : ℕ → Fin 9 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) (pc : ℕ)
      (hm : x.ctl.mode = .fpp) (hr : x.ctl.replaying = false) (hq : q ≤ 64)
      (hrun : x.fppMode = .run)
      (hprog : GalilScaffoldControl.Run GalilFppMarkedCode.code (abs' x).fpp.program
        (List.replicate q true) ⟨⟨pc, LocalBuffers.abs (fppRunBuf g q x.fppBuf)⟩, false⟩) :
      TickL3 S q first x (sliceVm g q pc x)
  | fpp_done (x : GalilVML P)
      (g : ℕ → Fin 9 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) (pc : ℕ)
      (hm : x.ctl.mode = .fpp) (hr : x.ctl.replaying = false) (hq : q ≤ 64)
      (hrun : x.fppMode = .run)
      (hprog : GalilScaffoldControl.Run GalilFppMarkedCode.code (abs' x).fpp.program
        (List.replicate q true) ⟨⟨pc, LocalBuffers.abs (fppRunBuf g q x.fppBuf)⟩, true⟩) :
      TickL3 S q first x (doneVm first g q pc { x.ctl with mode := .markEnd } x)
  | markEnd_found (x : GalilVML P)
      (hm : x.ctl.mode = .markEnd) (hr : x.ctl.replaying = false)
      (he : (galilFrameS S q first).atEnd (abs' x))
      (hne : (marksOf (abs' x)).left ≠ []) :
      TickL3 S q first x
        (marksVm GalilScaffoldTape.moveLeft { x.ctl with mode := .choose, odd := false } x)
  | markEnd_step (x : GalilVML P)
      (hm : x.ctl.mode = .markEnd) (hr : x.ctl.replaying = false)
      (he : ¬ (galilFrameS S q first).atEnd (abs' x)) :
      TickL3 S q first x (marksVm GalilScaffoldTape.moveRight x.ctl x)
  | choose_select (x : GalilVML P)
      (hm : x.ctl.mode = .choose) (hr : x.ctl.replaying = false)
      (ho : x.ctl.odd = true) (hs : (galilFrameS S q first).markSet (abs' x))
      (hpol : x.pol .length = true)
      (hleft : absHead' x.left x.pending = absHead' x.right x.pending)
      (hcenter : absHead' x.center x.pending = absHead' x.right x.pending) :
      TickL3 S q first x (chooseVm { x.ctl with mode := .rewind, pair := false } x)
  | choose_step (x : GalilVML P)
      (hm : x.ctl.mode = .choose) (hr : x.ctl.replaying = false)
      (hs : x.ctl.odd = false ∨ ¬ (galilFrameS S q first).markSet (abs' x))
      (hne : (marksOf (abs' x)).left ≠ []) :
      TickL3 S q first x
        (marksVm GalilScaffoldTape.moveLeft { x.ctl with odd := !x.ctl.odd } x)
  | rewind_done (x : GalilVML P)
      (hm : x.ctl.mode = .rewind) (hr : x.ctl.replaying = false)
      (hf : (galilFrameS S q first).atFirst (abs' x))
      (hclean : ∀ i, LocalBuffers.Cleared (LocalBuffers.idle x.fppBuf i)) :
      TickL3 S q first x (rewindDoneVm { x.ctl with mode := .replayStart } x)
  | rewind_one (x : GalilVML P)
      (hm : x.ctl.mode = .rewind) (hr : x.ctl.replaying = false)
      (hf : ¬ (galilFrameS S q first).atFirst (abs' x)) (hp : x.ctl.pair = false)
      (hne : (marksOf (abs' x)).left ≠ []) (hpol : x.pol .length = true) :
      TickL3 S q first x (rewindOneVm { x.ctl with pair := true } x)
  | rewind_pair (x : GalilVML P)
      (hm : x.ctl.mode = .rewind) (hr : x.ctl.replaying = false)
      (hf : ¬ (galilFrameS S q first).atFirst (abs' x)) (hp : x.ctl.pair = true)
      (hne : (marksOf (abs' x)).left ≠ []) (hpol : x.pol .length = true)
      (hrad : x.pol .radius = true) :
      TickL3 S q first x (rewindPairVm { x.ctl with pair := false } x)

/-! ### Every phase tick keeps `replaying = false`, so `abs'' = abs'` on both ends -/

theorem tickL3_replaying {S : Shared} {q : ℕ} {first : Fin 9} {x y : GalilVML P}
    (h : TickL3 S q first x y) : x.ctl.replaying = false ∧ y.ctl.replaying = false := by
  cases h <;> exact ⟨‹_›, ‹_›⟩

theorem absState''_eq {x : GalilVML P} (hr : x.ctl.replaying = false) :
    absState'' x = ⟨x.ctl, abs' x⟩ := by
  show (⟨x.ctl, abs'' x⟩ : State GalilVM) = _
  rw [abs''_eq_abs' hr]

/-! ### Locality: every local phase tick costs at most `c₃ = 66` steps -/

theorem tickL3_local {S : Shared} {q : ℕ} {first : Fin 9} {x y : GalilVML P}
    (h : TickL3 S q first x y) : StepLocalN c₃ x y := by
  cases h with
  | shift_one w => exact stepLocalN_le (by decide) (stepLocalN_shiftVm w x)
  | shift_done o =>
      exact stepLocalN_le (n := 1) (by decide) (stepLocalN_one (stepLocal_refl _))
  | copy_one a =>
      exact stepLocalN_le (n := 1) (by decide) (stepLocalN_one
        (stepLocal_bank workOps x (copyVm a x) rfl rfl rfl rfl (viewLocal_refl _)
          (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _) (viewLocal_moveLeft _)
          (bufLocal_refl _) (bufLocal_bufAt _ _ _)))
  | copy_done =>
      exact stepLocalN_le (n := 1) (by decide) (stepLocalN_one
        (stepLocal_noBank _ _ rfl rfl rfl rfl (viewLocal_refl _) (viewLocal_refl _)
          (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _) (bufLocal_refl _)
          (bufLocal_bufAt _ _ _)))
  | home_start =>
      exact stepLocalN_le (n := 1) (by decide) (stepLocalN_one (stepLocal_refl _))
  | home_step =>
      exact stepLocalN_le (n := 1) (by decide) (stepLocalN_one
        (stepLocal_noBank _ _ rfl rfl rfl rfl (viewLocal_refl _) (viewLocal_refl _)
          (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _) (bufLocal_refl _)
          (bufLocal_bufAt _ _ _)))
  | fpp_slice g pc hm hr hq =>
      exact stepLocalN_le (by unfold c₃; omega) (stepLocalN_sliceVm g q pc x)
  | fpp_done g pc hm hr hq =>
      exact stepLocalN_le (by unfold c₃; omega) (stepLocalN_doneVm first g q pc _ x)
  | markEnd_found =>
      exact stepLocalN_le (n := 1) (by decide) (stepLocalN_one (stepLocal_marksVm _ _ _))
  | markEnd_step =>
      exact stepLocalN_le (n := 1) (by decide) (stepLocalN_one (stepLocal_marksVm _ _ _))
  | choose_select => exact stepLocalN_le (by decide) (stepLocalN_chooseVm _ x)
  | choose_step =>
      exact stepLocalN_le (n := 1) (by decide) (stepLocalN_one (stepLocal_marksVm _ _ _))
  | rewind_done =>
      exact stepLocalN_le (n := 1) (by decide) (stepLocalN_one (stepLocal_rewindDoneVm _ _))
  | rewind_one =>
      exact stepLocalN_le (n := 1) (by decide) (stepLocalN_one
        (stepLocal_bank rewindOps1 x _ rfl rfl rfl rfl (viewLocal_moveLeft _)
          (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _)
          (bufLocal_refl _) (bufLocal_bufAt _ _ _)))
  | rewind_pair =>
      exact stepLocalN_le (n := 1) (by decide) (stepLocalN_one
        (stepLocal_bank rewindOps2 x _ rfl rfl rfl rfl (viewLocal_moveLeft _)
          (viewLocal_moveLeft _) (viewLocal_refl _) (viewLocal_refl _) (viewLocal_refl _)
          (bufLocal_refl _) (bufLocal_bufAt _ _ _)))

/-! ### The invariant is preserved -/

theorem tickL3_inv {S : Shared} {q : ℕ} {first : Fin 9} {x y : GalilVML P}
    (hinv : Inv x) (h : TickL3 S q first x y) : Inv y := by
  have hv := hinv.views
  cases h with
  | shift_one w hm hr hw hctr => exact inv_shiftVm hinv hctr w
  | shift_done => exact inv_congr hinv rfl rfl rfl rfl rfl hv
  | copy_one a hm hr ha hprop hpol hpos =>
      have i1 : Inv (bankTick workOps x) := inv_bankTick hinv (fun c hc => by
        cases c
        all_goals first | exact hpos | exact (nomatch hc))
      exact inv_congr i1 rfl rfl rfl rfl rfl
        ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, PalPeg.LocalTick1.WF_moveLeftV hv.2.2.2.2⟩
  | copy_done => exact inv_congr hinv rfl rfl rfl rfl rfl hv
  | home_start => exact inv_congr hinv rfl rfl rfl rfl rfl hv
  | home_step => exact inv_congr hinv rfl rfl rfl rfl rfl hv
  | fpp_slice => exact inv_congr hinv rfl rfl rfl rfl rfl hv
  | fpp_done => exact inv_congr hinv rfl rfl rfl rfl rfl hv
  | markEnd_found => exact inv_congr hinv rfl rfl rfl rfl rfl hv
  | markEnd_step => exact inv_congr hinv rfl rfl rfl rfl rfl hv
  | choose_select =>
      have i1 : Inv (bankTick chooseOps1 x) :=
        inv_bankTick hinv (fun c hc => by cases c <;> exact (nomatch hc))
      have i2 : Inv (bankTick chooseOps2 (bankTick chooseOps1 x)) :=
        inv_bankTick i1 (fun c hc => by cases c <;> exact (nomatch hc))
      exact inv_congr i2 rfl rfl rfl rfl rfl i2.views
  | choose_step => exact inv_congr hinv rfl rfl rfl rfl rfl hv
  | rewind_done => exact inv_congr hinv rfl rfl rfl rfl rfl hv
  | rewind_one =>
      have i1 : Inv (bankTick rewindOps1 x) :=
        inv_bankTick hinv (fun c hc => by cases c <;> exact (nomatch hc))
      exact inv_congr i1 rfl rfl rfl rfl rfl
        ⟨PalPeg.LocalTick1.WF_moveLeftV hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2⟩
  | rewind_pair =>
      have i1 : Inv (bankTick rewindOps2 x) :=
        inv_bankTick hinv (fun c hc => by cases c <;> exact (nomatch hc))
      exact inv_congr i1 rfl rfl rfl rfl rfl
        ⟨PalPeg.LocalTick1.WF_moveLeftV hv.1, PalPeg.LocalTick1.WF_moveLeftV hv.2.1,
          hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2⟩


/-! ### The abstraction: a local phase tick is a scaffold `Tick` -/

theorem shiftCounters_remaining {x : GalilVML P} (h : ShiftCounters x) :
    GalilScaffoldCounter.positive (abs' x).remaining = true := by
  show GalilScaffoldCounter.positive
    (LocalCounter.absCtr (x.phys (x.roles .remaining)) (x.pol .remaining)) = true
  rw [h.remPol]
  have hp := h.remPos
  exact PalPeg.LocalChain.positive_absCtr (n := LocalCounter.val (x.phys (x.roles .remaining)) - 1)
    (by omega)

theorem tickL3_abs {S : Shared} {q : ℕ} {first : Fin 9} (delay : ℕ) {x y : GalilVML P}
    (hinv : Inv x) (h : TickL3 S q first x y) :
    Tick (galilFrameS S q first) delay (absState'' x) (absState'' y) := by
  have hinj := hinv.roles
  obtain ⟨hrx, hry⟩ := tickL3_replaying h
  rw [absState''_eq hrx, absState''_eq hry]
  cases h with
  | shift_one w hm hr hw hctr haC haL haL' hcC hcL hcL' =>
      rw [abs'_shiftVm hinv hctr w haC haL haL' hcC hcL hcL']
      exact Tick.shift_one x.ctl (abs' x) _ hm (Or.inl (shiftCounters_remaining hctr))
        (frameS_shiftOne S q first ⟨hcC, hcL, hcL', w, hw, rfl⟩)
  | shift_done o hm hr hp ho =>
      exact Tick.shift_done x.ctl (abs' x) o hm hp ho
  | copy_one a hm hr ha hprop hpol hpos =>
      rw [abs'_copyVm hinj a hpol hpos hprop]
      have hcr : (galilFrameS S q first).remainingPos (abs' x) := by
        refine Or.inr ?_
        rintro (h0 | h0)
        · have h1 : GalilScaffoldPlace.read (absPlace x.fppWalker) = none := h0
          rw [ha] at h1
          cases h1
        · have h1 : GalilScaffoldCounter.zero
              (LocalCounter.absCtr (x.phys (x.roles .fppWork)) (x.pol .fppWork)) = true := h0
          rw [LocalCounter.zero_iff] at h1
          have := of_decide_eq_true h1
          omega
      exact Tick.copy_one x.ctl (abs' x) _ hm hcr (frameS_copyOne S q first ⟨a, ha, rfl⟩)
  | copy_done hm hr hp =>
      rw [abs'_copyDoneVm]
      exact Tick.copy_done x.ctl (abs' x) _ hm hp (frameS_copyEnd S q first rfl)
  | home_start hm hr hl =>
      rw [abs'_homeStartVm]
      exact Tick.home_start x.ctl (abs' x) _ hm hl (frameS_fppStart S q first rfl)
  | home_step hm hr hl hne =>
      rw [abs'_homeStepVm]
      exact Tick.home_step x.ctl (abs' x) _ hm hl (frameS_homeStep S q first ⟨hne, rfl⟩)
  | fpp_slice g pc hm hr hq hrun hprog =>
      rw [abs'_sliceVm]
      exact Tick.fpp_slice x.ctl (abs' x) _ hm (frameS_fppSlice S q first ⟨hrun, hprog, rfl, rfl⟩)
  | fpp_done g pc hm hr hq hrun hprog =>
      rw [abs'_doneVm]
      exact Tick.fpp_done x.ctl (abs' x) _ hm
        (frameS_fppDone S q first ⟨hrun, _, hprog, rfl, rfl⟩)
  | markEnd_found hm hr he hne =>
      rw [abs'_marksVm_rewind]
      exact Tick.markEnd_found x.ctl (abs' x) _ hm he (frameS_markBack S q first ⟨hne, rfl⟩)
  | markEnd_step hm hr he =>
      rw [abs'_marksVm]
      exact Tick.markEnd_step x.ctl (abs' x) _ hm he (frameS_markForward S q first rfl)
  | choose_select hm hr ho hs hpol hleft hcenter =>
      rw [abs'_chooseVm hinj _ hpol hleft hcenter]
      exact Tick.choose_select x.ctl (abs' x) _ hm ho hs (frameS_choose S q first rfl)
  | choose_step hm hr hs hne =>
      rw [abs'_marksVm_rewind]
      exact Tick.choose_step x.ctl (abs' x) _ hm hs (frameS_markBack S q first ⟨hne, rfl⟩)
  | rewind_done hm hr hf hclean =>
      rw [abs'_rewindDoneVm _ hclean]
      exact Tick.rewind_done x.ctl (abs' x) _ hm hf (frameS_fppReset S q first rfl)
  | rewind_one hm hr hf hp hne hpol =>
      rw [abs'_rewindOneVm hinj _ hpol]
      exact Tick.rewind_one x.ctl (abs' x) _ hm hf hp (frameS_rewindOne S q first ⟨hne, rfl⟩)
  | rewind_pair hm hr hf hp hne hpol hrad =>
      rw [abs'_rewindPairVm hinj _ hpol hrad]
      exact Tick.rewind_pair x.ctl (abs' x) _ hm hf hp
        (frameS_rewindPair S q first ⟨hne, rfl⟩)

#print axioms absCtr_op
#print axioms inv_bankTick
#print axioms abs'_bankTick
#print axioms abs'_shiftVm
#print axioms abs'_copyVm
#print axioms abs'_doneVm
#print axioms abs'_chooseVm
#print axioms abs'_rewindDoneVm
#print axioms abs'_rewindPairVm
#print axioms tickL3_local
#print axioms tickL3_inv
#print axioms tickL3_abs

end PalPeg.LocalTick3
