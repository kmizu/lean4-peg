import PalPeg.CloseoutCoreEnc
import PalPeg.GhostSection

/-!
# Closeout, step 2b: closing (and refuting) the NAMED residuals of `CloseoutCoreEnc`

`CloseoutCoreEnc` lays the core `Mirrored1 P` out on `Γc` and names six
residuals.  This file settles three of them and sharpens the rest.  It builds no
`LocalStep`, so

**無条件 PAL ∈ PEG は未完.**

## What is established

* **§1–§3 (`NAMED_chainRep`, restricted — closed).**  `ctrOf` sections
  `LocalCounter.absCtr` on *canonical* counters, `viewOfPH` sections
  `LocalInputView.absHead`, `viewOfPlace` sections `LocalState.absPlace`, and
  `repChain` assembles them into a section of `LocalChain.absChain`:
  `absChain_repChain` proves `absChain (repChain c) = c` for every `c : ChainVM`
  whose embedded counters are `Canonical`.
* **§4 (`NAMED_chainRep`, unrestricted — refuted).**  `isEmpty_NAMED_chainRep`:
  the residual *as stated* is uninhabited.  `absC` is always canonical
  (`absC_canonical`), while `ChainVM` can carry `⟨[()], [()]⟩`; no section of
  `absChain` on all of `ChainVM` exists.  The repaired statement is
  `NAMED_chainRep'`, which `chainRep'` inhabits.
* **§5 (`NAMED_queueLayout` — refuted).**  `not_NAMED_queueLayout`: one
  `moveRight` that dequeues `RTQueue` shifts the *entire* front list one cell
  left, and `listTape` anchors the head at cell `0`, so the cell at distance `2`
  changes outside every radius-`1` window.  A queue tape must move its *head*,
  not its content; `NAMED_queueLayout'` states that repaired obligation.
* **§6 (`NAMED_margin` — refuted as stated).**  `listTape` and
  `STape.blankTape` both have `pos = 0`, so `NAMED_margin` forces `Reach` to be
  empty (`isEmpty_of_NAMED_margin`).  The repair is a left sentinel:
  `listTape1` has `pos = 1` (`pos_listTape1`), `viewTapes1` rebuilds the cursor
  block on it, and `margin_viewTapes1` proves the margin for that block
  unconditionally.
* **§7 (partial progress on `NAMED_stepWindow`).**  `encTapes_phys` identifies
  the counter-bank block of the layout, and `winRealizes_stepLocal_phys` shows
  every `StepLocal` change there *is* a radius-`1` window rewrite, given the
  margin.  What is still missing is that one `next` produces all blocks at once.

## What is *not* established

`NAMED_stepWindow`, `NAMED_feedWindow`, `NAMED_fppQuantum`, `NAMED_encInjective`
remain open, restated here with their exact types (§8).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc2

open PalPeg PalPeg.Program
open PalPeg.Local (pos rd LocalStep)
open PalPeg.LocalCounter (Seg)
open PalPeg.LocalInputView (InputView)
open PalPeg.LocalState (GalilVML TapeLocal MirLocal ViewLocal StepLocal)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.GalilScaffoldInputHead (Head PlaceHead)
open PalPeg.GalilScaffoldPlace (Place)
open PalPeg.GalilScaffoldCounter (Counter Canonical ofNat)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)
open PalPeg.CloseoutCoreStep (Γc blankc tView nViews tMir tBuf tL QL qOfL)
open PalPeg.CloseoutCoreEnc (Kc WinRealizes segSym mapTape listTape cellSym viewTapes
  encTapes winRealizes_of_tapeLocal)

/-! ## 1. A section of the counter abstraction

`LocalCounter.absCtr` lands in the canonical counters only, so it can only be
sectioned there — but on those it can be, explicitly. -/

-- The section of the counter abstraction lives in `PalPeg.GhostSection`.
export PalPeg.GhostSection (ctrTapeSeg val_ctrTapeSeg segCtr_ctrTapeSeg list_unit_eq ctrOf
  absCtr_ctrOf)

/-! ## 2. Sections of the cursor abstractions -/

/-- The queue of a freshly built cursor is empty, so its `farList` is. -/
@[simp] theorem farList_empty_queue (back : List (Option (Fin 2))) (f : Option (Fin 2))
    (near : List (Option (Fin 2))) (g : Bool) :
    LocalInputView.farList ⟨back, f, near, RTQueue.empty, g⟩ = [] := rfl

/-- The cursor representing an abstract head, with the whole unvisited suffix
parked in `near` and the queue empty. -/
def viewOfPH (p : PlaceHead) : InputView :=
  ⟨p.head.left, p.head.focus, p.head.right, RTQueue.empty, p.gap⟩

/-- **A section of `absHead`.** -/
theorem absHead_viewOfPH (p : PlaceHead) :
    LocalInputView.absHead (viewOfPH p) p.head.incoming = p := by
  rcases p with ⟨⟨f, l, r, q⟩, g⟩
  show (⟨⟨f, l, r ++ [], q⟩, g⟩ : PlaceHead) = ⟨⟨f, l, r, q⟩, g⟩
  rw [List.append_nil]

-- The section of `absPlace` lives in `PalPeg.GhostSection`.
export PalPeg.GhostSection (viewOfPlace placeLetters_map absPlace_viewOfPlace)

/-! ## 3. A section of `absChain` on the canonical chains -/

open PalPeg.LocalChain (ChainL CtrL TagL absChain absC absVer absCons absMach absWatch)

/-- A blank period tape. -/
def period0 : GalilScaffoldChainPeriod.Tape := ⟨[], .blank, []⟩

/-- A blank `ProgLang` tape. -/
def dp0 : GalilScaffoldTape.Tape := ⟨[], 0, []⟩

/-- A chain skeleton: every field at a default, to be overwritten per tag. -/
def chain0 : ChainL where
  tag := .idle
  verifier := viewOfPH ⟨⟨none, [], [], []⟩, false⟩
  vpending := []
  walkerV := viewOfPlace ⟨[], false⟩
  period := period0
  answer := dp0
  tape := fun _ => ctrTapeSeg 0
  pol := fun _ => true
  spare := ctrTapeSeg 0
  phase := 0
  forward := true
  broken := false

/-- Install a counter into a role. -/
def withCtr (x : ChainL) (k : CtrL) (c : Counter) : ChainL :=
  { x with tape := Function.update x.tape k (ctrOf c).1,
           pol := Function.update x.pol k (ctrOf c).2 }

theorem absC_withCtr_self {x : ChainL} {k : CtrL} {c : Counter} (hc : Canonical c) :
    absC (withCtr x k c) k = c := by
  show LocalCounter.absCtr (Function.update x.tape k (ctrOf c).1 k)
      (Function.update x.pol k (ctrOf c).2 k) = c
  rw [Function.update_self, Function.update_self]
  exact absCtr_ctrOf hc

theorem absC_withCtr_other {x : ChainL} {k k' : CtrL} {c : Counter} (h : k' ≠ k) :
    absC (withCtr x k c) k' = absC x k' := by
  show LocalCounter.absCtr (Function.update x.tape k (ctrOf c).1 k')
      (Function.update x.pol k (ctrOf c).2 k') = _
  rw [Function.update_of_ne h, Function.update_of_ne h]
  rfl

/-- The consume-side skeleton of a watch state. -/
def repCons (cs : GalilScaffoldChainConsume.State) (x : ChainL) : ChainL :=
  withCtr (withCtr (withCtr
    { x with period := cs.period, phase := cs.phase, forward := cs.forward,
             broken := cs.broken } .distance cs.distance) .boundary cs.boundary) .last cs.last

/-- The local realization of a watch state. -/
def repWatch (w : GalilScaffoldChainWatch.State) (tg : TagL) : ChainL :=
  withCtr (withCtr
    (repCons w.machine.control
      { chain0 with tag := tg, verifier := viewOfPH w.machine.verifier,
                    vpending := w.machine.verifier.head.incoming })
    .lag w.lag) .margin w.margin

/-- **The local realization of a `ChainVM`.** -/
def repChain : ChainVM → ChainL
  | .idle => { chain0 with tag := .idle }
  | .copy answer h walker period lag margin verifier =>
      withCtr (withCtr (withCtr
        { chain0 with tag := .copy, answer := answer, walkerV := viewOfPlace walker,
                      period := period, verifier := viewOfPH verifier,
                      vpending := verifier.head.incoming } .h h) .lag lag) .margin margin
  | .back period h lag margin verifier =>
      withCtr (withCtr (withCtr
        { chain0 with tag := .back, period := period, verifier := viewOfPH verifier,
                      vpending := verifier.head.incoming } .h h) .lag lag) .margin margin
  | .watch w => repWatch w .watch
  | .broken w => repWatch w .broken

/-- The counters a `ChainVM` carries must all be canonical for it to be in the
image of `absChain`. -/
def CanonChain : ChainVM → Prop
  | .idle => True
  | .copy _ h _ _ lag margin _ => Canonical h ∧ Canonical lag ∧ Canonical margin
  | .back _ h lag margin _ => Canonical h ∧ Canonical lag ∧ Canonical margin
  | .watch w | .broken w =>
      Canonical w.lag ∧ Canonical w.margin ∧ Canonical w.machine.control.distance ∧
        Canonical w.machine.control.boundary ∧ Canonical w.machine.control.last

theorem absWatch_repWatch {w : GalilScaffoldChainWatch.State} {tg : TagL}
    (hc : Canonical w.lag ∧ Canonical w.margin ∧ Canonical w.machine.control.distance ∧
      Canonical w.machine.control.boundary ∧ Canonical w.machine.control.last) :
    absWatch (repWatch w tg) = w := by
  obtain ⟨hlag, hmar, hdist, hbnd, hlast⟩ := hc
  rcases w with ⟨⟨ver, cs⟩, lag, margin⟩
  rcases cs with ⟨per, dist, bnd, lst, ph, fw, br⟩
  have hL : absC (repWatch ⟨⟨ver, ⟨per, dist, bnd, lst, ph, fw, br⟩⟩, lag, margin⟩ tg) .lag
      = lag := by
    unfold repWatch repCons
    rw [absC_withCtr_other (by decide), absC_withCtr_self hlag]
  have hM : absC (repWatch ⟨⟨ver, ⟨per, dist, bnd, lst, ph, fw, br⟩⟩, lag, margin⟩ tg) .margin
      = margin := by
    unfold repWatch repCons
    exact absC_withCtr_self hmar
  have hD : absC (repWatch ⟨⟨ver, ⟨per, dist, bnd, lst, ph, fw, br⟩⟩, lag, margin⟩ tg) .distance
      = dist := by
    unfold repWatch repCons
    rw [absC_withCtr_other (by decide), absC_withCtr_other (by decide),
      absC_withCtr_other (by decide), absC_withCtr_other (by decide),
      absC_withCtr_self hdist]
  have hB : absC (repWatch ⟨⟨ver, ⟨per, dist, bnd, lst, ph, fw, br⟩⟩, lag, margin⟩ tg) .boundary
      = bnd := by
    unfold repWatch repCons
    rw [absC_withCtr_other (by decide), absC_withCtr_other (by decide),
      absC_withCtr_other (by decide), absC_withCtr_self hbnd]
  have hT : absC (repWatch ⟨⟨ver, ⟨per, dist, bnd, lst, ph, fw, br⟩⟩, lag, margin⟩ tg) .last
      = lst := by
    unfold repWatch repCons
    rw [absC_withCtr_other (by decide), absC_withCtr_other (by decide),
      absC_withCtr_self hlast]
  have hV : absVer (repWatch ⟨⟨ver, ⟨per, dist, bnd, lst, ph, fw, br⟩⟩, lag, margin⟩ tg)
      = ver := absHead_viewOfPH ver
  show (⟨⟨absVer _, ⟨_, absC _ .distance, absC _ .boundary, absC _ .last, _, _, _⟩⟩,
    absC _ .lag, absC _ .margin⟩ : GalilScaffoldChainWatch.State) = _
  rw [hL, hM, hD, hB, hT, hV]
  rfl

/-- **A section of `absChain` on the canonical chains.** -/
theorem absChain_repChain {c : ChainVM} (hc : CanonChain c) : absChain (repChain c) = c := by
  cases c with
  | idle => rfl
  | copy answer h walker period lag margin verifier =>
      obtain ⟨hh, hlag, hmar⟩ := hc
      have hH : absC (repChain (.copy answer h walker period lag margin verifier)) .h = h := by
        unfold repChain
        rw [absC_withCtr_other (by decide), absC_withCtr_other (by decide),
          absC_withCtr_self hh]
      have hL : absC (repChain (.copy answer h walker period lag margin verifier)) .lag
          = lag := by
        unfold repChain
        rw [absC_withCtr_other (by decide), absC_withCtr_self hlag]
      have hM : absC (repChain (.copy answer h walker period lag margin verifier)) .margin
          = margin := by
        unfold repChain
        exact absC_withCtr_self hmar
      have hW : LocalState.absPlace
          (repChain (.copy answer h walker period lag margin verifier)).walkerV = walker := by
        unfold repChain
        exact absPlace_viewOfPlace walker
      have hV : absVer (repChain (.copy answer h walker period lag margin verifier))
          = verifier := by
        unfold repChain
        exact absHead_viewOfPH verifier
      show ChainVM.copy _ (absC _ .h) (LocalState.absPlace _) _ (absC _ .lag) (absC _ .margin)
        (absVer _) = _
      rw [hH, hL, hM, hW, hV]
      rfl
  | back period h lag margin verifier =>
      obtain ⟨hh, hlag, hmar⟩ := hc
      have hH : absC (repChain (.back period h lag margin verifier)) .h = h := by
        unfold repChain
        rw [absC_withCtr_other (by decide), absC_withCtr_other (by decide),
          absC_withCtr_self hh]
      have hL : absC (repChain (.back period h lag margin verifier)) .lag = lag := by
        unfold repChain
        rw [absC_withCtr_other (by decide), absC_withCtr_self hlag]
      have hM : absC (repChain (.back period h lag margin verifier)) .margin
          = margin := by
        unfold repChain
        exact absC_withCtr_self hmar
      have hV : absVer (repChain (.back period h lag margin verifier))
          = verifier := by
        unfold repChain
        exact absHead_viewOfPH verifier
      show ChainVM.back _ (absC _ .h) (absC _ .lag) (absC _ .margin) (absVer _) = _
      rw [hH, hL, hM, hV]
      rfl
  | watch w => exact congrArg ChainVM.watch (absWatch_repWatch hc)
  | broken w => exact congrArg ChainVM.broken (absWatch_repWatch hc)

/-! ## 4. `NAMED_chainRep` as stated is uninhabited

`absC` is canonical by construction, so a chain carrying a non-canonical counter
— and `ChainVM` places no constraint — is outside the image of `absChain`. -/

/-- A `ChainVM` no local chain abstracts to. -/
def badChain : ChainVM :=
  .back period0 ⟨[()], [()]⟩ GalilScaffoldCounter.reset GalilScaffoldCounter.reset
    ⟨⟨none, [], [], []⟩, false⟩

theorem not_canonical_bad : ¬ Canonical (⟨[()], [()]⟩ : Counter) := by
  rintro (h | h) <;> simp at h

theorem no_preimage_badChain (x : ChainL) : absChain x ≠ badChain := by
  intro h
  cases htag : x.tag with
  | idle => rw [absChain, htag] at h; simp [badChain] at h
  | copy => rw [absChain, htag] at h; simp [badChain] at h
  | watch => rw [absChain, htag] at h; simp [badChain] at h
  | broken => rw [absChain, htag] at h; simp [badChain] at h
  | back =>
      rw [absChain, htag] at h
      have hh : absC x CtrL.h = (⟨[()], [()]⟩ : Counter) := by
        injection h with _ hh _ _ _
      exact not_canonical_bad (hh ▸ LocalChain.absC_canonical x CtrL.h)

/-- **`NAMED_chainRep` is refuted.** -/
theorem isEmpty_NAMED_chainRep : IsEmpty PalPeg.CloseoutCoreEnc.NAMED_chainRep :=
  ⟨fun r => no_preimage_badChain (r.1 badChain) (r.2 badChain)⟩

/-- **The repaired residual**: a section of `absChain` over the canonical
chains, which is what the layout actually needs. -/
def NAMED_chainRep' : Type :=
  { rep : ChainVM → ChainL // ∀ c, CanonChain c → absChain (rep c) = c }

/-- …and it is inhabited. -/
def chainRep' : NAMED_chainRep' := ⟨repChain, fun _ hc => absChain_repChain hc⟩

/-! ## 5. `NAMED_queueLayout` is refuted

`listTape` anchors the head at cell `0`, so a dequeue — which drops the first
element of `far.front` — shifts every remaining cell one place left.  With three
elements in the front list, the cell at distance `2` changes, and no radius-`1`
window reaches it. -/

/-- A cursor whose real-time queue holds three letters in its front list, poised
on the letter step of a right move. -/
def vBad : InputView :=
  ⟨[], none, [], ⟨3, [0, 0, 0], .idle, 0, []⟩, true⟩

theorem viewTapes_vBad_two : viewTapes vBad 2 = listTape [some 0, some 0, some 0] := rfl

theorem viewTapes_moveRight_vBad_two :
    viewTapes (LocalInputView.moveRight vBad) 2 = listTape [some 0, some 0] := rfl

theorem rd_listTape_two_of_three :
    rd blankc (listTape [some (0 : Fin 2), some 0, some 0]) 2 = cellSym (some 0) := rfl

theorem rd_listTape_two_of_two :
    rd blankc (listTape [some (0 : Fin 2), some 0]) 2 = blankc := rfl

theorem cellSym_ne_blank : cellSym (some (0 : Fin 2)) ≠ blankc := by decide

theorem pos_viewTapes_vBad_two : pos (viewTapes vBad 2) = 0 := rfl

/-- **`NAMED_queueLayout` is refuted.** -/
theorem not_NAMED_queueLayout : ¬ PalPeg.CloseoutCoreEnc.NAMED_queueLayout := by
  intro h
  obtain ⟨w, d, hd, hpos, hcell⟩ :=
    h vBad (LocalInputView.moveRight vBad) (LocalState.viewLocal_moveRight vBad) 2
  have h2 := hcell 2
  rw [viewTapes_vBad_two, viewTapes_moveRight_vBad_two] at h2
  rw [if_neg (by
    rw [show pos (listTape [some (0 : Fin 2), some 0, some 0]) = 0 from rfl]
    decide)] at h2
  rw [rd_listTape_two_of_two, rd_listTape_two_of_three] at h2
  exact cellSym_ne_blank h2.symm

/-- **The repaired residual.**  A queue layout must not re-anchor the head: the
obligation is the existence of *some* layout `lay` of a cursor on its tapes
under which every `ViewLocal` step is a radius-`Kc` window rewrite. -/
def NAMED_queueLayout' : Prop :=
  ∃ lay : InputView → ℕ → STape Γc,
    ∀ v v' : InputView, LocalInputView.WF v → ViewLocal v v' →
      ∀ i : ℕ, WinRealizes (lay v i) (lay v' i)

/-! ## 6. `NAMED_margin` is refuted as stated, and repaired by a sentinel -/

@[simp] theorem pos_listTape (l : List (Option (Fin 2))) : pos (listTape l) = 0 := by
  cases l <;> rfl

theorem pos_viewTapes_one (v : InputView) : pos (viewTapes v 1) = 0 := pos_listTape _

theorem encTapes_one {P : ℕ} (rep : ChainVM → ChainL) (m : Mirrored1 P) :
    encTapes rep m 1 = viewTapes m.vm.left 1 := by
  rw [encTapes]
  exact if_pos (by decide)

/-- **`NAMED_margin` forces `Reach` to be empty**: tape `1` of the layout is a
`listTape`, whose head is at the left edge. -/
theorem isEmpty_of_NAMED_margin {P : ℕ} (rep : ChainVM → ChainL)
    (Reach : Mirrored1 P → Prop) (h : PalPeg.CloseoutCoreEnc.NAMED_margin rep Reach)
    (m : Mirrored1 P) : ¬ Reach m := by
  intro hm
  have h1 : (1 : ℕ) < tL P PalPeg.CloseoutCoreEnc.tChain := by
    have ht : PalPeg.CloseoutCoreEnc.tChain = 18 := PalPeg.CloseoutCoreEnc.tChain_eq
    unfold tL nViews tView tMir tBuf
    omega
  have hkey := h m hm ⟨1, h1⟩
  rw [show ((⟨1, h1⟩ : Fin (tL P PalPeg.CloseoutCoreEnc.tChain)) : ℕ) = 1 from rfl,
    encTapes_one rep m, pos_viewTapes_one] at hkey
  exact absurd hkey (by decide)

/-- The repair: a left sentinel cell, so the head sits at position `1`. -/
def listTape1 (l : List (Option (Fin 2))) : STape Γc :=
  match l with
  | [] => ⟨[blankc], blankc, []⟩
  | a :: rest => ⟨[blankc], cellSym a, rest.map cellSym⟩

@[simp] theorem pos_listTape1 (l : List (Option (Fin 2))) : pos (listTape1 l) = 1 := by
  cases l <;> rfl

/-- The cursor block rebuilt over the sentinel layout. -/
def viewTapes1 (v : InputView) : ℕ → STape Γc
  | 0 => ⟨v.back.map cellSym ++ [blankc], cellSym v.focus, []⟩
  | 1 => listTape1 v.near
  | 2 => listTape1 (v.far.front.map (fun a => some a))
  | _ => listTape1 (v.far.rear.map (fun a => some a))

/-- **The margin holds unconditionally for the repaired cursor block.** -/
theorem margin_viewTapes1 (v : InputView) (i : ℕ) : Kc ≤ pos (viewTapes1 v i) := by
  match i with
  | 0 =>
      show Kc ≤ (v.back.map cellSym ++ [blankc]).length
      simp [Kc]
  | 1 => rw [show viewTapes1 v 1 = listTape1 v.near from rfl, pos_listTape1]
  | 2 =>
      rw [show viewTapes1 v 2 = listTape1 (v.far.front.map (fun a => some a)) from rfl,
        pos_listTape1]
  | (n + 3) =>
      rw [show viewTapes1 v (n + 3) = listTape1 (v.far.rear.map (fun a => some a)) from rfl,
        pos_listTape1]

/-! ## 7. Partial progress on `NAMED_stepWindow`: the counter-bank block -/

theorem encTapes_phys {P : ℕ} (rep : ChainVM → ChainL) (m : Mirrored1 P)
    (j : ℕ) (hj : j < P) :
    encTapes rep m (nViews * tView + j) = mapTape segSym (m.vm.phys ⟨j, hj⟩) := by
  have h24 : nViews * tView = 24 := by decide
  have h4 : tView = 4 := rfl
  rw [encTapes]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]
  rw [dif_pos (show nViews * tView + j - nViews * tView < P by omega)]
  exact congrArg (fun k => mapTape segSym (m.vm.phys k))
    (Fin.ext (show nViews * tView + j - nViews * tView = j by omega))

/-- **Every `StepLocal` change on the counter bank is a radius-1 window
rewrite**, given the margin. -/
theorem winRealizes_stepLocal_phys {P : ℕ} (rep : ChainVM → ChainL)
    {m m' : Mirrored1 P} (h : StepLocal m.vm m'.vm) (j : ℕ) (hj : j < P)
    (hmargin : Kc ≤ pos (m.vm.phys ⟨j, hj⟩)) :
    WinRealizes (encTapes rep m (nViews * tView + j))
      (encTapes rep m' (nViews * tView + j)) := by
  rw [encTapes_phys rep m j hj, encTapes_phys rep m' j hj]
  exact winRealizes_of_tapeLocal (h.1 ⟨j, hj⟩) hmargin

/-! ## 8. The residuals that remain open

Restated with their exact types; nothing below is proved here. -/

/-- **Gap (3): a tick is one `LocalStep`.** -/
def NAMED_stepWindow {P : ℕ} (delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (f : Mirrored1 P → Mirrored1 P) : Prop :=
  ∃ L0 : LocalStep (Fin 2) (QL delay Lp Lf P PalPeg.CloseoutCoreEnc.QChain) Γc
      (tL P PalPeg.CloseoutCoreEnc.tChain) Kc,
    CloseoutCoreStep.RealizedTick (PalPeg.CloseoutCoreEnc.encCOf delay Lp Lf rep) L0 f

/-- **The arrival half.** -/
def NAMED_feedWindow {P : ℕ} (delay Lp Lf : ℕ) (rep : ChainVM → ChainL) : Prop :=
  ∃ L0 : LocalStep (Fin 2) (QL delay Lp Lf P PalPeg.CloseoutCoreEnc.QChain) Γc
      (tL P PalPeg.CloseoutCoreEnc.tChain) Kc,
    CloseoutCoreStep.RealizedFeed (P := P) (PalPeg.CloseoutCoreEnc.encCOf delay Lp Lf rep) L0

/-- **The fpp quantum.** -/
def NAMED_fppQuantum {P : ℕ} (Good : Mirrored1 P → Prop) (raw : List (Fin 2))
    (stOf : ℕ → PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (Pw : PalPeg.GalilScaffoldChainInputSupply.Shared) (qq : ℕ) (first : Fin 9) : Prop :=
  ∃ g : Mirrored1 P → Mirrored1 P,
    CloseoutCoreStep.AgreeOn Good raw stOf (PalPeg.LocalWF.ffpp (P := P) Pw qq first) g
      PalPeg.GalilScaffoldController.Mode.fpp

/-- **Injectivity of the layout on reachable states.** -/
def NAMED_encInjective {P : ℕ} (delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (Reach : Mirrored1 P → Prop) : Prop :=
  ∀ m m' : Mirrored1 P, Reach m → Reach m' →
    PalPeg.CloseoutCoreEnc.encCOf delay Lp Lf rep m
      = PalPeg.CloseoutCoreEnc.encCOf delay Lp Lf rep m' → m = m'

/-- **The margin, over a repaired layout.**  `NAMED_margin` of
`CloseoutCoreEnc` is refuted above; the obligation that survives is the margin
for a sentinel-shifted layout, of which `margin_viewTapes1` is the cursor part. -/
def NAMED_margin' {P : ℕ} (lay : Mirrored1 P → ℕ → STape Γc)
    (Reach : Mirrored1 P → Prop) : Prop :=
  ∀ m : Mirrored1 P, Reach m → ∀ i : ℕ, Kc ≤ pos (lay m i)

end PalPeg.CloseoutCoreEnc2

#print axioms PalPeg.CloseoutCoreEnc2.absCtr_ctrOf
#print axioms PalPeg.CloseoutCoreEnc2.absHead_viewOfPH
#print axioms PalPeg.CloseoutCoreEnc2.absPlace_viewOfPlace
#print axioms PalPeg.CloseoutCoreEnc2.absChain_repChain
#print axioms PalPeg.CloseoutCoreEnc2.isEmpty_NAMED_chainRep
#print axioms PalPeg.CloseoutCoreEnc2.chainRep'
#print axioms PalPeg.CloseoutCoreEnc2.not_NAMED_queueLayout
#print axioms PalPeg.CloseoutCoreEnc2.isEmpty_of_NAMED_margin
#print axioms PalPeg.CloseoutCoreEnc2.margin_viewTapes1
#print axioms PalPeg.CloseoutCoreEnc2.encTapes_phys
#print axioms PalPeg.CloseoutCoreEnc2.winRealizes_stepLocal_phys
