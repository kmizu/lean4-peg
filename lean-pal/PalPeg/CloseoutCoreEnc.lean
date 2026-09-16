import PalPeg.CloseoutCoreStep
import PalPeg.LocalChain

/-!
# Closeout, step 2: the symbol layout and the radius-`1` window budget

`CloseoutCoreStep` names two residuals for the concrete core `Mirrored1 P`:
the encoding `encC` into `QL … × (Fin (tL P tChain) → STape Γc)` (gap 1), and
the window-locality of each mode step (gap 3).  This file does the part of both
that is unconditional, and names the rest with its exact type.  It builds no
`LocalStep` and proves no new dynamics, so

**無条件 PAL ∈ PEG は未完.**

## What is established

* **§1 (the window budget).**  `Kc := 1`, and `WinRealizes T T'` is the semantic
  reading of "one radius-`Kc` window rewrite plus a displacement `|d| ≤ Kc`":
  the head moves by `d`, the `2 * Kc + 1` cells centred on the old head are
  overwritten by a window, and nothing else changes.  `winRealizes_sweep`
  connects it to `Local.sweep`, i.e. to what `LocalStep.apply` actually does on
  a tape whose head is at least `Kc` cells from the left edge, and
  `winRealizes_applyAction` shows that **one `STape.applyAction` is a radius-1
  window rewrite** — the elementary fact behind `K = 1`.
* **§2 (the alphabet recoding).**  `segSym : Seg → Γc` is injective and
  blank-preserving, `mapTape` transports a `STape Seg` into a `STape Γc`,
  `pos_mapTape`/`rd_mapTape` say the transport commutes with the absolute view,
  and `mapTape_applyAction` that it commutes with one micro-action.  Hence
  `winRealizes_of_tapeLocal`: **every `LocalState.TapeLocal` change is a
  radius-1 window rewrite** on the recoded tape, at any head position `≥ 1`.
  `winRealizes_of_mirLocal` lifts this to a whole mirror bank.
* **§3 (the layout).**  `dpSTape` puts a `GalilScaffoldTape.Tape` on `Γc`,
  `viewTapes` lays an `InputView` on the `tView = 4` tapes of
  `CloseoutCoreStep`, `bufTapes` a `Buffered n`, `QChain`/`tChain` are the finite
  summary and the tape count of one `LocalChain.ChainL`, and `encTapes` /
  `encCOf` assemble the whole family — parameterized by a local representation
  of the still abstract `chain : ChainVM` field, which is `NAMED_chainRep`.

## What is *not* established (the NAMED residuals of §4)

`encCOf` is a layout, not a refinement: nothing here says the layout is
injective, that heads stay `≥ Kc` from the left edge, that `viewTapes` tracks
`RTQueue` in two stacks, or that any `stepLocal_*` of `LocalTick1/2/3` — let
alone the `fpp` quantum of one `GalilDpCode` instruction — is realized by a
single `LocalStep`.  Those are §4, stated with their exact types.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace PalPeg.CloseoutCoreEnc

open PalPeg PalPeg.Program
open PalPeg.Local (Window idx idx_val pos rd sweep pos_sweep rd_sweep
  rd_applyAction pos_applyAction LocalStep)
open PalPeg.LocalCounter (Seg)
open PalPeg.LocalInputView (InputView)
open PalPeg.LocalMirror (Mirrored)
open PalPeg.LocalState (GalilVML Ctr TapeLocal MirLocal ViewLocal BufLocal StepLocal)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)
open PalPeg.CloseoutCoreStep (Γc blankc tView nViews tMir tBuf tL QL qOfL)

/-! ## 1. The radius-`1` window budget -/

/-- The window radius of the core. -/
abbrev Kc : ℕ := 1

/-- **One radius-`Kc` window rewrite, semantically.**  The head moves by `d`
with `|d| ≤ Kc`, the `2 * Kc + 1` cells centred on the old head are overwritten
by `w`, and no other cell changes.  This is exactly the pair
`pos_sweep` / `rd_sweep`, i.e. the effect of one tape component of
`LocalStep.apply`. -/
def WinRealizes (T T' : STape Γc) : Prop :=
  ∃ (w : Window Γc Kc) (d : ℤ), |d| ≤ (Kc : ℤ) ∧
    (pos T' : ℤ) = (pos T : ℤ) + d ∧
    ∀ p : ℕ, rd blankc T' p =
      if pos T - Kc ≤ p ∧ p ≤ pos T + Kc then w (idx Kc (p - (pos T - Kc)))
      else rd blankc T p

/-- What one tape component of `LocalStep.apply` does, when the head is at least
`Kc` cells from the left edge, is a `WinRealizes`. -/
theorem winRealizes_sweep (T : STape Γc) (w : Window Γc Kc) (d : ℤ)
    (hK : Kc ≤ pos T) (hd : |d| ≤ (Kc : ℤ)) :
    WinRealizes T (sweep blankc Kc T w d) :=
  ⟨w, d, hd, pos_sweep blankc Kc T w d hK hd, fun p => rd_sweep blankc Kc T w d hK p⟩

/-- **One micro-action is a radius-1 window rewrite.**  The head must be at
least one cell from the left edge, which is where `.left` would be clamped. -/
theorem winRealizes_applyAction (T : STape Γc) (s : Γc) (m : PegSeparation.RealTimeTM.Move)
    (h1 : 1 ≤ pos T) : WinRealizes T (T.applyAction blankc (s, m)) := by
  classical
  refine ⟨fun i => if (i : ℕ) = 1 then s else rd blankc T (pos T - 1 + (i : ℕ)),
    (match m with | .right => (1 : ℤ) | .left => (-1 : ℤ) | .stay => (0 : ℤ)), ?_, ?_, ?_⟩
  · cases m <;> simp [Kc]
  · rw [pos_applyAction blankc s T m]
    cases m <;> simp <;> omega
  · intro p
    rw [rd_applyAction blankc s T m p]
    by_cases hmem : pos T - Kc ≤ p ∧ p ≤ pos T + Kc
    · rw [if_pos hmem]
      have hle : p - (pos T - Kc) ≤ 2 * Kc := by
        simp only [Kc] at hmem ⊢
        omega
      simp only [idx_val hle]
      by_cases hp : p = pos T
      · rw [if_pos hp]
        simp only [Kc]
        rw [if_pos (by omega)]
      · rw [if_neg hp]
        simp only [Kc] at hmem ⊢
        rw [if_neg (by omega)]
        congr 1
        omega
    · rw [if_neg hmem, if_neg (by simp only [Kc] at hmem ⊢; omega)]

theorem winRealizes_refl (T : STape Γc) : WinRealizes T T := by
  refine ⟨fun i => rd blankc T (pos T - Kc + (i : ℕ)), 0, by simp, by simp, ?_⟩
  intro p
  by_cases hmem : pos T - Kc ≤ p ∧ p ≤ pos T + Kc
  · rw [if_pos hmem]
    have hle : p - (pos T - Kc) ≤ 2 * Kc := by
      simp only [Kc] at hmem ⊢
      omega
    simp only [idx_val hle]
    congr 1
    simp only [Kc] at hmem ⊢
    omega
  · rw [if_neg hmem]

/-! ## 2. Recoding the counter alphabet into `Γc` -/

/-- The counter alphabet `Seg = Fin 3` inside `Γc`, blank-preserving. -/
def segSym (s : Seg) : Γc :=
  if s = LocalCounter.blank then blankc
  else if s = LocalCounter.sep then PalPeg.GalilVMEncode.sDp 1
  else PalPeg.GalilVMEncode.mark

theorem segSym_blank : segSym LocalCounter.blank = blankc := rfl

theorem segSym_inj : Function.Injective segSym := by decide

/-- Transport a tape along a symbol recoding. -/
def mapTape {Γ Γ' : Type} (f : Γ → Γ') (T : STape Γ) : STape Γ' :=
  ⟨T.left.map f, f T.focus, T.right.map f⟩

theorem getD_map {Γ Γ' : Type} (f : Γ → Γ') (l : List Γ) (b : Γ) (p : ℕ) :
    (l.map f).getD p (f b) = f (l.getD p b) := by
  induction l generalizing p with
  | nil => simp
  | cons a t ih =>
      cases p with
      | zero => simp
      | succ n => simpa using ih n

@[simp] theorem pos_mapTape {Γ Γ' : Type} (f : Γ → Γ') (T : STape Γ) :
    pos (mapTape f T) = pos T := by simp [pos, mapTape]

theorem rd_mapTape {Γ Γ' : Type} (f : Γ → Γ') (b : Γ) (T : STape Γ) (p : ℕ) :
    rd (f b) (mapTape f T) p = f (rd b T p) := by
  have h : PalPeg.Local.toList (mapTape f T) = (PalPeg.Local.toList T).map f := by
    simp [PalPeg.Local.toList, mapTape]
  rw [rd, rd, h, getD_map]

/-- Recoding commutes with one micro-action. -/
theorem mapTape_applyAction {Γ Γ' : Type} (f : Γ → Γ') (b : Γ) (T : STape Γ)
    (s : Γ) (m : PegSeparation.RealTimeTM.Move) :
    mapTape f (T.applyAction b (s, m)) = (mapTape f T).applyAction (f b) (f s, m) := by
  obtain ⟨L, x, R⟩ := T
  cases m <;> cases L <;> cases R <;> simp [mapTape, STape.applyAction]

/-- **Every `TapeLocal` change is a radius-1 window rewrite** on the recoded
tape, provided the head is not at the left edge. -/
theorem winRealizes_of_tapeLocal {t t' : STape Seg} (h : TapeLocal t t')
    (h1 : 1 ≤ pos t) : WinRealizes (mapTape segSym t) (mapTape segSym t') := by
  have hpos : (1 : ℕ) ≤ pos (mapTape segSym t) := by rwa [pos_mapTape]
  rcases h with rfl | ⟨⟨s, m⟩, rfl⟩
  · exact winRealizes_refl _
  · rw [mapTape_applyAction segSym LocalCounter.blank t s m, segSym_blank]
    exact winRealizes_applyAction _ _ m hpos

/-- The same, for a whole mirror bank. -/
theorem winRealizes_of_mirLocal {k : ℕ} {m m' : Mirrored k} (h : MirLocal m m')
    (hsrc : 1 ≤ pos m.src) (hmir : ∀ i, 1 ≤ pos (m.mir i)) :
    WinRealizes (mapTape segSym m.src) (mapTape segSym m'.src) ∧
      ∀ i, WinRealizes (mapTape segSym (m.mir i)) (mapTape segSym (m'.mir i)) :=
  ⟨winRealizes_of_tapeLocal h.1 hsrc, fun i => winRealizes_of_tapeLocal (h.2 i) (hmir i)⟩

/-! ## 3. The layout -/

/-- A `ProgLang` tape on `Γc`. -/
def dpSTape (t : GalilScaffoldTape.Tape) : STape Γc :=
  ⟨t.left.map PalPeg.GalilVMEncode.sDp, PalPeg.GalilVMEncode.sDp t.focus,
    t.right.map PalPeg.GalilVMEncode.sDp⟩

/-- The eleven period tokens inside `Γc`, blank-preserving and injective. -/
def tokSym : GalilScaffoldChainPeriod.Token → Γc
  | .blank => blankc
  | .left => PalPeg.GalilVMEncode.sBit false
  | .plain a => PalPeg.GalilVMEncode.sDp ⟨a.val, by omega⟩
  | .first a => PalPeg.GalilVMEncode.sDp ⟨3 + a.val, by omega⟩
  | .last a => PalPeg.GalilVMEncode.sDp ⟨6 + a.val, by omega⟩

theorem tokSym_inj : Function.Injective tokSym := by decide

/-- A cell of a cursor as a symbol. -/
def cellSym (o : Option (Fin 2)) : Γc := PalPeg.GalilVMEncode.sOpt o

/-- A list of cells as a right-extending tape with the head at the left end. -/
def listTape (l : List (Option (Fin 2))) : STape Γc :=
  match l with
  | [] => STape.blankTape blankc
  | a :: rest => ⟨[], cellSym a, rest.map cellSym⟩

/-- **The `tView = 4` tapes of one cursor**: `back` carrying `focus` at the
head, `near`, and the two stacks of the real-time queue `far` (its front list
and its rear list; the rotation state is *not* laid out here, see
`NAMED_queueLayout`). -/
def viewTapes (v : InputView) : ℕ → STape Γc
  | 0 => ⟨v.back.map cellSym, cellSym v.focus, []⟩
  | 1 => listTape v.near
  | 2 => listTape (v.far.front.map (fun a => some a))
  | _ => listTape (v.far.rear.map (fun a => some a))

/-- The `2 * n + 1` tapes of a double buffer: both banks, plus the unary `job`
counter. -/
def bufTapes {n : ℕ} (x : LocalBuffers.Buffered n) : ℕ → STape Γc := fun i =>
  if h : i < n then dpSTape (x.A ⟨i, h⟩)
  else if h2 : i - n < n then dpSTape (x.B ⟨i - n, h2⟩)
  else PalPeg.GalilVMEncode.natTape (x.job.getD 0)

/-- **The finite summary of one local chain**: its tag, the consume phase, the
two consume bits and the six sign bits. -/
abbrev QChain : Type :=
  LocalChain.TagL × Fin 5 × Bool × Bool × (LocalChain.CtrL → Bool)

instance : Fintype QChain := inferInstance
instance : DecidableEq QChain := inferInstance

def qChainOf (c : LocalChain.ChainL) : QChain :=
  (c.tag, c.phase, c.forward, c.broken, c.pol)

/-- **The tape count of one local chain**: the verifier view and the copy walker
(`tView` each), the arrivals `vpending`, the period and answer tapes, the six
counter tapes and the spare. -/
def tChain : ℕ := 2 * tView + 1 + 1 + 1 + (Fintype.card LocalChain.CtrL + 1)

theorem tChain_eq : tChain = 18 := by
  have h : Fintype.card LocalChain.CtrL = 6 := by decide
  simp [tChain, tView, h]

/-- The tapes of one local chain. -/
noncomputable def chainTapes (c : LocalChain.ChainL) : ℕ → STape Γc := fun i =>
  if i < tView then viewTapes c.verifier i
  else if i < 2 * tView then viewTapes c.walkerV (i - tView)
  else if i = 2 * tView then listTape (c.vpending.map (fun a => some a))
  else if i = 2 * tView + 1 then
    ⟨c.period.left.map tokSym, tokSym c.period.focus, c.period.right.map tokSym⟩
  else if i = 2 * tView + 2 then dpSTape c.answer
  else if h : i - (2 * tView + 3) < Fintype.card LocalChain.CtrL then
    mapTape segSym (c.tape ((Fintype.equivFin LocalChain.CtrL).symm ⟨_, h⟩))
  else mapTape segSym c.spare

/-- **The whole tape family of the core**, as a total function of the index:
the `nViews = 6` cursors (`left`, `center`, `right`, `walkerView`, `fppWalker`
and the parked mirror `Mirrored1.mirL`), the `P` counter tapes of the bank, the
three mirror banks, the two double buffers, and the chain. -/
noncomputable def encTapes {P : ℕ} (rep : ChainVM → LocalChain.ChainL)
    (m : Mirrored1 P) : ℕ → STape Γc := fun i =>
  if i < tView then viewTapes m.vm.left i
  else if i < 2 * tView then viewTapes m.vm.center (i - tView)
  else if i < 3 * tView then viewTapes m.vm.right (i - 2 * tView)
  else if i < 4 * tView then viewTapes m.vm.walkerView (i - 3 * tView)
  else if i < 5 * tView then viewTapes m.vm.fppWalker (i - 4 * tView)
  else if i < 6 * tView then viewTapes m.mirL (i - 5 * tView)
  else if h : i - nViews * tView < P then mapTape segSym (m.vm.phys ⟨_, h⟩)
  else
    let j := i - nViews * tView - P
    if j = 0 then mapTape segSym m.vm.radiusMir.src
    else if j = 1 then mapTape segSym (m.vm.radiusMir.mir 0)
    else if j = 2 then mapTape segSym (m.vm.radiusMir.mir 1)
    else if j = 3 then mapTape segSym m.vm.lowerMir.src
    else if j = 4 then mapTape segSym (m.vm.lowerMir.mir 0)
    else if j = 5 then mapTape segSym m.vm.lengthMir.src
    else if j = 6 then mapTape segSym (m.vm.lengthMir.mir 0)
    else if j < tMir + (2 * 12 + 1) then bufTapes m.vm.dpBuf (j - tMir)
    else if j < tMir + tBuf then bufTapes m.vm.fppBuf (j - tMir - (2 * 12 + 1))
    else chainTapes (rep m.vm.chain) (j - tMir - tBuf)

/-- **The encoding `encC` of `CloseoutCoreStep`**, for the finite control `QL`
of that file with `QChain` as the chain summary.  It is a layout: no injectivity
or step-faithfulness is claimed here (see §4). -/
noncomputable def encCOf {P : ℕ} (delay Lp Lf : ℕ) (rep : ChainVM → LocalChain.ChainL)
    (m : Mirrored1 P) :
    QL delay Lp Lf P QChain × (Fin (tL P tChain) → STape Γc) :=
  (qOfL delay Lp Lf (fun c => qChainOf (rep c)) m, fun i => encTapes rep m i.val)

/-! ## 4. The NAMED residuals -/

/-- **A local representation of the abstract chain.**  `GalilVML.chain` is a
`ChainVM`; `LocalChain.ChainL` is its `K`-local realization and `absChain` the
abstraction map, but no section of `absChain` is constructed anywhere. -/
def NAMED_chainRep : Type :=
  { rep : ChainVM → LocalChain.ChainL // ∀ c, LocalChain.absChain (rep c) = c }

/-- **The queue layout.**  `tView = 4` budgets two tapes for `InputView.far`,
but `RTQueue.Queue` also carries a `RotationState`; `viewTapes` drops it.  The
residual is that the two stacks suffice, i.e. that the rotation state is finite
control plus the two laid-out lists. -/
def NAMED_queueLayout : Prop :=
  ∀ v v' : InputView, ViewLocal v v' → ∀ i : ℕ, WinRealizes (viewTapes v i) (viewTapes v' i)

/-- **The left-edge margin.**  `winRealizes_applyAction` and `pos_sweep` both
need the head at least `Kc` cells from the left edge, and the initial
configuration has every head at the edge. -/
def NAMED_margin {P : ℕ} (rep : ChainVM → LocalChain.ChainL)
    (Reach : Mirrored1 P → Prop) : Prop :=
  ∀ m : Mirrored1 P, Reach m → ∀ i : Fin (tL P tChain), Kc ≤ pos (encTapes rep m i.val)

/-- **The layout is a refinement.**  Injectivity of the encoding on reachable
states; without it the finite control cannot recover the state it must dispatch
on. -/
def NAMED_encInjective {P : ℕ} (delay Lp Lf : ℕ) (rep : ChainVM → LocalChain.ChainL)
    (Reach : Mirrored1 P → Prop) : Prop :=
  ∀ m m' : Mirrored1 P, Reach m → Reach m' →
    encCOf delay Lp Lf rep m = encCOf delay Lp Lf rep m' → m = m'

/-- **Gap (3) itself: a `StepLocal` pair is one `LocalStep`.**  §1 and §2 give
the per-component window rewrite for the counter and mirror tapes; what is
missing is that the *same* `next` function — a function of the finite control,
the input symbol and the windows only — produces all of them at once, for each
of the mode steps of `LocalTick1/2/3`. -/
def NAMED_stepWindow {P : ℕ} (delay Lp Lf : ℕ) (rep : ChainVM → LocalChain.ChainL)
    (f : Mirrored1 P → Mirrored1 P) : Prop :=
  ∃ L0 : LocalStep (Fin 2) (QL delay Lp Lf P QChain) Γc (tL P tChain) Kc,
    CloseoutCoreStep.RealizedTick (encCOf delay Lp Lf rep) L0 f

/-- **The arrival half.** -/
def NAMED_feedWindow {P : ℕ} (delay Lp Lf : ℕ)
    (rep : ChainVM → LocalChain.ChainL) : Prop :=
  ∃ L0 : LocalStep (Fin 2) (QL delay Lp Lf P QChain) Γc (tL P tChain) Kc,
    CloseoutCoreStep.RealizedFeed (P := P) (encCOf delay Lp Lf rep) L0

/-- **The fpp quantum.**  One `.fpp` tick is to be a single `GalilDpCode`
instruction executed in a fixed window; this is the `.fpp` component of
`CloseoutCoreStep.realizes_seven_of_agree`. -/
def NAMED_fppQuantum {P : ℕ} (raw : List (Fin 2))
    (stOf : ℕ → PalPeg.GalilScaffoldTop.State
      PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (Pw : PalPeg.GalilScaffoldChainInputSupply.Shared) (qq : ℕ) (first : Fin 9) : Prop :=
  ∃ g : Mirrored1 P → Mirrored1 P,
    CloseoutCoreStep.AgreeOn raw stOf (PalPeg.LocalWF.ffpp (P := P) Pw qq first) g
      PalPeg.GalilScaffoldController.Mode.fpp

end PalPeg.CloseoutCoreEnc

#print axioms PalPeg.CloseoutCoreEnc.winRealizes_sweep
#print axioms PalPeg.CloseoutCoreEnc.winRealizes_applyAction
#print axioms PalPeg.CloseoutCoreEnc.winRealizes_refl
#print axioms PalPeg.CloseoutCoreEnc.segSym_inj
#print axioms PalPeg.CloseoutCoreEnc.rd_mapTape
#print axioms PalPeg.CloseoutCoreEnc.mapTape_applyAction
#print axioms PalPeg.CloseoutCoreEnc.winRealizes_of_tapeLocal
#print axioms PalPeg.CloseoutCoreEnc.winRealizes_of_mirLocal
#print axioms PalPeg.CloseoutCoreEnc.tokSym_inj
#print axioms PalPeg.CloseoutCoreEnc.tChain_eq
