import PalPeg.CloseoutCoreEnc23

/-!
# Closeout, step 2x: a concrete chain representation and the shift contract

`CloseoutCoreEnc23` reads the chain block through an uninterpreted
`rep : ChainVM → ChainL` and states the chain residue of a `shiftPick` step as
the contract `ChainShiftBounded rep`.  This file instantiates `rep` by the
concrete watch-chain encoding `chainRepD` (verifier view, pending arrivals,
period tape, the six counters `lag/margin/h/distance/boundary/last` as
`LocalCounter` unary tapes with a control-held sign bit, the `spare` mirror
of `distance`) and proves the *debris-parametrised* shift contract
`chainShiftBoundedD`.  Nothing here is about the whole machine, so

**無条件 PAL ∈ PEG は未完.**

## What is established (unconditional)

* **§1** `ctrTapeD n r`: the counter tape of absolute value `n` with debris
  `r` on the right.  `ctrTapeD_pop`/`ctrTapeD_push`: `n+1 → n` is the
  `2`-composite `popActsS`, `n → n+1` is the `≤ 2`-composite `pushActsS r`
  (one action when `r = []`).  `ctrN`/`ctrPol` encode a `Counter` (any, not
  only canonical); `ctrTapeD_dec`: one `dec` is a `≤ 2`-composite with debris
  `decDebris`.
* **§2** `chainRepD c d`: the concrete `ChainL` of a `ChainVM` with counter
  debris `d : CtrL → List Seg`.  `absChain_chainRepD_watch`: it is faithful
  on `.watch w` whenever the five counters of `w` are `Canonical` (the `h`
  slot is `reset`).
* **§3** `chainShiftOne` changes exactly `margin`, `distance`, `boundary`,
  `last` (each one `dec`) and leaves `lag`, the verifier, the period tape
  and the consume bits alone (`watchCtr_shift`).  **`chainShiftBoundedD`**:
  for every `w` and debris `d` there is debris `d'` and, at every address
  `j`, a list of `≤ 2` micro-actions turning `chainTapes (chainRepD (.watch w) d) j`
  into `chainTapes (chainRepD (.watch (chainShiftOne w)) d') j`.
  `restC_of_chainRepD` restates it in the shape of `CloseoutCoreEnc23.restC_of_rep`
  on `encTapes`, with the two sides read through the two debris families.

## What is *not* established, and why

1. **`ChainShiftBounded chainRepD` as literally stated in `CloseoutCoreEnc23`
   is not provable for any faithful `rep`.**  It quantifies `c : ChainVM`
   *independently* of `w`, so it asks the tapes of `rep (.watch (chainShiftOne w))`
   to be a `≤ 4`-composite of the tapes of `rep c` for `c` with arbitrarily
   different counters; `≤ 4` actions change `≤ 4` cells.  The instance actually
   used by `restC_of_rep` is `c := m.vm.chain` with `m.vm.chain = .watch w`,
   which is what `chainShiftBoundedD` provides.
2. **Even at `c := .watch w`, no debris-free `rep : ChainVM → ChainL` can
   satisfy the contract.**  The unary value sits on `left` (`LocalCounter.val`
   reads `markRun t.left`); popping a mark moves the head left and leaves a
   blank on `right`, and no micro-action ever deletes a cell (`|left|+|right|`
   never decreases).  A state-functional tape would need `right` to grow
   without bound as the value shrinks.  Hence the counter tapes carry a debris
   parameter, exactly like the cursor queues of `CloseoutCoreEnc20`–`23`
   (`dTape`/`dbg`); `chainShiftBoundedD` is the chain analogue of `qLay_step`.
   Hooking it into `shiftVm_tapeActKQ_run` requires threading `d` through
   `Lay` (a third component), which is a change to `CloseoutCoreEnc23` and is
   not done here.
3. No counter is changed by an unbounded amount: all four changes are `dec`
   (`±1` on the tape, a free sign flip in the control).  No copy, no rename.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc24

open PalPeg PalPeg.Program
open PalPeg.CloseoutCoreStep (Γc blankc nViews tView tMir tBuf)
open PalPeg.CloseoutCoreEnc (encTapes chainTapes mapTape segSym)
open PalPeg.CloseoutCoreEnc12 (Act actList actList_cons)
open PalPeg.CloseoutCoreEnc14 (embActs embAct mapTape_actList)
open PalPeg.CloseoutCoreEnc23 (ChainShiftBounded encTapes_chainIdx shiftVm_chain)
open PalPeg.LocalInputView (InputView emptyView)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalChain (ChainL CtrL absChain)
open PalPeg.LocalCounter (Seg mark sep)
open PalPeg.GalilScaffoldCounter (Counter dec Canonical)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM chainShiftOne)
open PalPeg.GalilScaffoldInputHead (PlaceHead)
open PalPeg.LocalTick3 (shiftVm)

variable {P : ℕ}

/-! ## 1. One counter tape with debris -/

/-- The counter tape of absolute value `n`, head on the blank frontier, debris
`r` to the right. -/
def ctrTapeD (n : ℕ) (r : List Seg) : STape Seg :=
  ⟨List.replicate n mark ++ [sep], PalPeg.LocalCounter.blank, r⟩

/-- Pop one mark: step left (blanking the frontier), then blank the mark. -/
def popActsS : List (Act Seg) :=
  [some (PalPeg.LocalCounter.blank, .left), some (PalPeg.LocalCounter.blank, .stay)]

/-- Push one mark: write it and step right; if debris was there, blank it. -/
def pushActsS : List Seg → List (Act Seg)
  | [] => [some (mark, .right)]
  | _ :: _ => [some (mark, .right), some (PalPeg.LocalCounter.blank, .stay)]

theorem popActsS_length : popActsS.length ≤ 2 := by simp [popActsS]

theorem pushActsS_length (r : List Seg) : (pushActsS r).length ≤ 2 := by
  cases r <;> simp [pushActsS]

theorem ctrTapeD_pop (n : ℕ) (r : List Seg) :
    ctrTapeD n (PalPeg.LocalCounter.blank :: r)
      = actList PalPeg.LocalCounter.blank (ctrTapeD (n + 1) r) popActsS := by
  simp [ctrTapeD, popActsS, actList, PalPeg.CloseoutCoreEnc12.actOnG, STape.applyAction,
    List.replicate_succ]

theorem ctrTapeD_push (n : ℕ) (r : List Seg) :
    ctrTapeD (n + 1) r.tail
      = actList PalPeg.LocalCounter.blank (ctrTapeD n r) (pushActsS r) := by
  cases r with
  | nil =>
      simp [ctrTapeD, pushActsS, actList, PalPeg.CloseoutCoreEnc12.actOnG, STape.applyAction,
        List.replicate_succ]
  | cons x r =>
      simp [ctrTapeD, pushActsS, actList, PalPeg.CloseoutCoreEnc12.actOnG, STape.applyAction,
        List.replicate_succ]

/-- The absolute value of a (not necessarily canonical) counter. -/
def ctrN (c : Counter) : ℕ := c.pos.length + c.neg.length

/-- Its sign bit: `true` unless a negative unit is present. -/
def ctrPol (c : Counter) : Bool := c.neg.isEmpty

/-- The debris after one `dec`. -/
def decDebris (c : Counter) (r : List Seg) : List Seg :=
  match c.pos with
  | [] => r.tail
  | _ :: _ => PalPeg.LocalCounter.blank :: r

/-- The actions of one `dec`. -/
def decActs (c : Counter) (r : List Seg) : List (Act Seg) :=
  match c.pos with
  | [] => pushActsS r
  | _ :: _ => popActsS

theorem decActs_length (c : Counter) (r : List Seg) : (decActs c r).length ≤ 2 := by
  unfold decActs
  cases c.pos with
  | nil => exact pushActsS_length r
  | cons _ _ => exact popActsS_length

/-- **One `dec` is a `≤ 2`-composite on the counter tape.** -/
theorem ctrTapeD_dec (c : Counter) (r : List Seg) :
    ctrTapeD (ctrN (dec c)) (decDebris c r)
      = actList PalPeg.LocalCounter.blank (ctrTapeD (ctrN c) r) (decActs c r) := by
  obtain ⟨p, ng⟩ := c
  cases p with
  | nil =>
      show ctrTapeD (ctrN ⟨[], () :: ng⟩) r.tail = actList _ (ctrTapeD (ctrN ⟨[], ng⟩) r) (pushActsS r)
      have h1 : ctrN ⟨[], () :: ng⟩ = ctrN ⟨[], ng⟩ + 1 := by simp [ctrN]
      rw [h1]
      exact ctrTapeD_push _ r
  | cons a ps =>
      show ctrTapeD (ctrN ⟨ps, ng⟩) (PalPeg.LocalCounter.blank :: r)
        = actList _ (ctrTapeD (ctrN ⟨a :: ps, ng⟩) r) popActsS
      have h1 : ctrN ⟨a :: ps, ng⟩ = ctrN ⟨ps, ng⟩ + 1 := by simp [ctrN]; omega
      rw [h1]
      exact ctrTapeD_pop _ r

/-! ## 2. The concrete chain representation -/

/-- The verifier view of a `PlaceHead`: everything stored explicitly, an empty
far queue; the pending arrivals go to `vpending`. -/
def viewOfHead (p : PlaceHead) : InputView :=
  ⟨p.head.left, p.head.focus, p.head.right, RTQueue.empty, p.gap⟩

theorem absHead_viewOfHead (p : PlaceHead) :
    PalPeg.LocalInputView.absHead (viewOfHead p) p.head.incoming = p := by
  obtain ⟨⟨f, l, r, q⟩, g⟩ := p
  simp [PalPeg.LocalInputView.absHead, viewOfHead, PalPeg.LocalInputView.absRight,
    PalPeg.LocalInputView.farList, RTQueue.toList_empty]

/-- The blank DP answer tape. -/
def answer0 : GalilScaffoldTape.Tape := ⟨[], 0, []⟩

/-- The blank period tape. -/
def period0 : GalilScaffoldChainPeriod.Tape := ⟨[], .blank, []⟩

/-- The six counters of a watch state (`h` is unused in `watch`: `reset`). -/
def watchCtr (w : PalPeg.GalilScaffoldChainWatch.State) : CtrL → Counter
  | .lag => w.lag
  | .margin => w.margin
  | .h => GalilScaffoldCounter.reset
  | .distance => w.machine.control.distance
  | .boundary => w.machine.control.boundary
  | .last => w.machine.control.last

/-- A `ChainL` from its finite control, cursors, tapes and counters, with
counter debris `d`. -/
def mkChain (tag : LocalChain.TagL) (ver : InputView) (pending : List (Fin 2))
    (walker : InputView) (period : GalilScaffoldChainPeriod.Tape)
    (answer : GalilScaffoldTape.Tape) (ctr : CtrL → Counter) (phase : Fin 5)
    (forward broken : Bool) (d : CtrL → List Seg) : ChainL where
  tag := tag
  verifier := ver
  vpending := pending
  walkerV := walker
  period := period
  answer := answer
  tape := fun k => ctrTapeD (ctrN (ctr k)) (d k)
  pol := fun k => ctrPol (ctr k)
  spare := ctrTapeD (ctrN (ctr .distance)) (d .distance)
  phase := phase
  forward := forward
  broken := broken

/-- The watch representation. -/
def watchRep (w : PalPeg.GalilScaffoldChainWatch.State) (d : CtrL → List Seg) : ChainL :=
  mkChain .watch (viewOfHead w.machine.verifier) w.machine.verifier.head.incoming emptyView
    w.machine.control.period answer0 (watchCtr w) w.machine.control.phase
    w.machine.control.forward w.machine.control.broken d

/-- **The concrete chain representation, with counter debris `d`.**  Faithful
on `.watch` (§2); the `copy`/`back`/`broken` walker is not reconstructed from
the abstract `Place` (that direction is not needed for the shift contract). -/
def chainRepD (c : ChainVM) (d : CtrL → List Seg) : ChainL :=
  match c with
  | .idle =>
      mkChain .idle emptyView [] emptyView period0 answer0 (fun _ => GalilScaffoldCounter.reset)
        0 false false d
  | .copy answer h _ period lag margin verifier =>
      mkChain .copy (viewOfHead verifier) verifier.head.incoming emptyView period answer
        (fun k => match k with
          | .h => h | .lag => lag | .margin => margin | _ => GalilScaffoldCounter.reset)
        0 false false d
  | .back period h lag margin verifier =>
      mkChain .back (viewOfHead verifier) verifier.head.incoming emptyView period answer0
        (fun k => match k with
          | .h => h | .lag => lag | .margin => margin | _ => GalilScaffoldCounter.reset)
        0 false false d
  | .watch w => watchRep w d
  | .broken w => { watchRep w d with tag := .broken }

theorem chainRepD_watch (w : PalPeg.GalilScaffoldChainWatch.State) (d : CtrL → List Seg) :
    chainRepD (.watch w) d = watchRep w d := rfl

theorem val_ctrTapeD (n : ℕ) (r : List Seg) : PalPeg.LocalCounter.val (ctrTapeD n r) = n := by
  simp [PalPeg.LocalCounter.val, ctrTapeD, PalPeg.LocalCounter.markRun_replicate_sep]

/-- A canonical counter is recovered from `(ctrN, ctrPol)`. -/
theorem absCtr_ctrTapeD (c : Counter) (hc : Canonical c) (r : List Seg) :
    PalPeg.LocalCounter.absCtr (ctrTapeD (ctrN c) r) (ctrPol c) = c := by
  obtain ⟨p, ng⟩ := c
  have hp : p = List.replicate p.length () :=
    List.eq_replicate_of_mem (fun b _ => Subsingleton.elim b ())
  have hn : ng = List.replicate ng.length () :=
    List.eq_replicate_of_mem (fun b _ => Subsingleton.elim b ())
  rcases hc with h | h
  · subst h
    simp [PalPeg.LocalCounter.absCtr, ctrPol, val_ctrTapeD, ctrN, PalPeg.LocalCounter.negOfNat]
    cases ng with
    | nil => simp [GalilScaffoldCounter.ofNat]
    | cons x t => simp; exact (List.eq_replicate_of_mem (l := x :: t) (fun b _ => Subsingleton.elim b ())).symm
  · subst h
    simp [PalPeg.LocalCounter.absCtr, ctrPol, val_ctrTapeD, ctrN, GalilScaffoldCounter.ofNat]
    exact (List.eq_replicate_of_mem (fun b _ => Subsingleton.elim b ())).symm

/-- **Faithfulness on `.watch`**, under canonical counters. -/
theorem absChain_chainRepD_watch (w : PalPeg.GalilScaffoldChainWatch.State)
    (d : CtrL → List Seg) (hlag : Canonical w.lag) (hmar : Canonical w.margin)
    (hdis : Canonical w.machine.control.distance) (hbd : Canonical w.machine.control.boundary)
    (hlast : Canonical w.machine.control.last) :
    absChain (chainRepD (.watch w) d) = .watch w := by
  obtain ⟨⟨v, ⟨per, dis, bd, la, ph, fw, br⟩⟩, lag, mar⟩ := w
  simp only [chainRepD_watch, absChain, watchRep, mkChain, LocalChain.absWatch,
    LocalChain.absMach, LocalChain.absVer, LocalChain.absCons, LocalChain.absC]
  rw [absHead_viewOfHead]
  simp only [watchCtr] at *
  rw [absCtr_ctrTapeD _ hlag, absCtr_ctrTapeD _ hmar, absCtr_ctrTapeD _ hdis,
    absCtr_ctrTapeD _ hbd, absCtr_ctrTapeD _ hlast]

/-! ## 3. The shift contract -/

/-- Which counters `chainShiftOne` decrements. -/
def shifted : CtrL → Bool
  | .lag => false
  | .margin => true
  | .h => false
  | .distance => true
  | .boundary => true
  | .last => true

theorem watchCtr_shift (w : PalPeg.GalilScaffoldChainWatch.State) (k : CtrL) :
    watchCtr (chainShiftOne w) k = if shifted k then dec (watchCtr w k) else watchCtr w k := by
  cases k <;> rfl

/-- The debris after a shift. -/
def shiftDebris (w : PalPeg.GalilScaffoldChainWatch.State) (d : CtrL → List Seg) :
    CtrL → List Seg :=
  fun k => if shifted k then decDebris (watchCtr w k) (d k) else d k

/-- The actions of a shift on counter `k`. -/
def shiftCtrActs (w : PalPeg.GalilScaffoldChainWatch.State) (d : CtrL → List Seg) (k : CtrL) :
    List (Act Seg) :=
  if shifted k then decActs (watchCtr w k) (d k) else []

theorem shiftCtrActs_length (w : PalPeg.GalilScaffoldChainWatch.State) (d : CtrL → List Seg)
    (k : CtrL) : (shiftCtrActs w d k).length ≤ 2 := by
  unfold shiftCtrActs
  split
  · exact decActs_length _ _
  · simp

theorem tape_shift (w : PalPeg.GalilScaffoldChainWatch.State) (d : CtrL → List Seg) (k : CtrL) :
    (watchRep (chainShiftOne w) (shiftDebris w d)).tape k
      = actList PalPeg.LocalCounter.blank ((watchRep w d).tape k) (shiftCtrActs w d k) := by
  show ctrTapeD (ctrN (watchCtr (chainShiftOne w) k)) (shiftDebris w d k)
    = actList _ (ctrTapeD (ctrN (watchCtr w k)) (d k)) (shiftCtrActs w d k)
  rw [watchCtr_shift]
  unfold shiftDebris shiftCtrActs
  by_cases h : shifted k = true
  · rw [if_pos h, if_pos h, if_pos h]
    exact ctrTapeD_dec _ _
  · rw [if_neg h, if_neg h, if_neg h]
    rfl

theorem spare_shift (w : PalPeg.GalilScaffoldChainWatch.State) (d : CtrL → List Seg) :
    (watchRep (chainShiftOne w) (shiftDebris w d)).spare
      = actList PalPeg.LocalCounter.blank ((watchRep w d).spare) (shiftCtrActs w d .distance) :=
  tape_shift w d .distance

/-- The chain block: the counter addresses. -/
theorem chainTapes_ctr (c : ChainL) (n : ℕ) (h : n < Fintype.card CtrL) :
    chainTapes c (n + 11) = mapTape segSym (c.tape ((Fintype.equivFin CtrL).symm ⟨n, h⟩)) := by
  have htv : tView = 4 := rfl
  unfold chainTapes
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]
  have h' : n + 11 - (2 * tView + 3) = n := by omega
  rw [dif_pos (by rw [h']; exact h)]
  exact congrArg (fun i => mapTape segSym (c.tape ((Fintype.equivFin CtrL).symm i))) (Fin.ext h')

/-- The chain block: the spare address. -/
theorem chainTapes_spare (c : ChainL) (n : ℕ) (h : Fintype.card CtrL ≤ n) :
    chainTapes c (n + 11) = mapTape segSym c.spare := by
  have htv : tView = 4 := rfl
  unfold chainTapes
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]
  have h' : n + 11 - (2 * tView + 3) = n := by omega
  rw [dif_neg (by rw [h']; omega)]

/-- The chain block: the addresses below the counters read only the fields
that `chainShiftOne` leaves alone. -/
theorem chainTapes_low (c c' : ChainL) (j : ℕ) (hj : j < 11)
    (hv : c'.verifier = c.verifier) (hw : c'.walkerV = c.walkerV)
    (hp : c'.vpending = c.vpending) (hper : c'.period = c.period)
    (ha : c'.answer = c.answer) : chainTapes c' j = chainTapes c j := by
  have htv : tView = 4 := rfl
  unfold chainTapes
  rw [hv, hw, hp, hper, ha]
  split_ifs <;> first | rfl | omega

/-- The actions of a shift at chain address `j`. -/
noncomputable def shiftChainActs (w : PalPeg.GalilScaffoldChainWatch.State) (d : CtrL → List Seg)
    (j : ℕ) : List (Act Γc) :=
  if hj : j < 11 then []
  else if h : j - 11 < Fintype.card CtrL then
    embActs (shiftCtrActs w d ((Fintype.equivFin CtrL).symm ⟨j - 11, h⟩))
  else embActs (shiftCtrActs w d .distance)

theorem shiftChainActs_length (w : PalPeg.GalilScaffoldChainWatch.State) (d : CtrL → List Seg)
    (j : ℕ) : (shiftChainActs w d j).length ≤ 2 := by
  unfold shiftChainActs
  split
  · simp
  · split
    · rw [PalPeg.CloseoutCoreEnc14.embActs_length]; exact shiftCtrActs_length _ _ _
    · rw [PalPeg.CloseoutCoreEnc14.embActs_length]; exact shiftCtrActs_length _ _ _

/-- **One shift on the concrete chain block is a `≤ 2`-composite at every
address.** -/
theorem chainTapes_shift (w : PalPeg.GalilScaffoldChainWatch.State) (d : CtrL → List Seg)
    (j : ℕ) :
    chainTapes (chainRepD (.watch (chainShiftOne w)) (shiftDebris w d)) j
      = actList blankc (chainTapes (chainRepD (.watch w) d) j) (shiftChainActs w d j) := by
  rw [chainRepD_watch, chainRepD_watch]
  unfold shiftChainActs
  by_cases hj : j < 11
  · rw [dif_pos hj, PalPeg.CloseoutCoreEnc12.actList_nil]
    exact chainTapes_low _ _ j hj rfl rfl rfl rfl rfl
  · rw [dif_neg hj]
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 11 := ⟨j - 11, by omega⟩
    have hn : n + 11 - 11 = n := by omega
    by_cases h : n < Fintype.card CtrL
    · rw [dif_pos (by rw [hn]; exact h)]
      rw [chainTapes_ctr _ n h, chainTapes_ctr _ n h, tape_shift, mapTape_actList]
      exact congrArg (fun i => actList blankc
        (mapTape segSym ((watchRep w d).tape ((Fintype.equivFin CtrL).symm ⟨n, h⟩)))
        (embActs (shiftCtrActs w d ((Fintype.equivFin CtrL).symm i)))) (Fin.ext hn.symm)
    · rw [dif_neg (by rw [hn]; exact h)]
      rw [chainTapes_spare _ n (by omega), chainTapes_spare _ n (by omega), spare_shift,
        mapTape_actList]

/-- **The shift contract for `chainRepD`, debris-parametrised**: the honest
form of `CloseoutCoreEnc23.ChainShiftBounded` at `c := .watch w`. -/
theorem chainShiftBoundedD (w : PalPeg.GalilScaffoldChainWatch.State) (d : CtrL → List Seg) :
    ∃ (d' : CtrL → List Seg) (rc : ℕ → List (Act Γc)), (∀ j, (rc j).length ≤ 4) ∧
      ∀ j, chainTapes (chainRepD (.watch (chainShiftOne w)) d') j
        = actList blankc (chainTapes (chainRepD (.watch w) d) j) (rc j) :=
  ⟨shiftDebris w d, shiftChainActs w d,
    fun j => le_trans (shiftChainActs_length w d j) (by norm_num),
    fun j => chainTapes_shift w d j⟩

/-- **`restC` for `chainRepD`**, in the shape of `CloseoutCoreEnc23.restC_of_rep`:
when the chain is `.watch w`, the chain block of `encTapes` after the step, read
through the shifted debris, is a `≤ 2`-composite of the chain block before,
read through `d`. -/
theorem restC_of_chainRepD (w : PalPeg.GalilScaffoldChainWatch.State) (m : Mirrored1 P)
    (hw : m.vm.chain = .watch w) (d : CtrL → List Seg) :
    ∃ restC : ℕ → List (Act Γc), (∀ i, (restC i).length ≤ 2) ∧
      ∀ i, nViews * tView + P + (tMir + tBuf) ≤ i →
        encTapes (fun c => chainRepD c (shiftDebris w d)) ⟨shiftVm w m.vm, m.mirL⟩ i
          = actList blankc (encTapes (fun c => chainRepD c d) m i)
              (restC (i - nViews * tView - P - tMir - tBuf)) := by
  refine ⟨shiftChainActs w d, shiftChainActs_length w d, ?_⟩
  intro i hi
  rw [encTapes_chainIdx _ _ i hi, encTapes_chainIdx _ m i hi]
  show chainTapes (chainRepD (shiftVm w m.vm).chain _) _ = _
  rw [shiftVm_chain, hw]
  exact chainTapes_shift w d _

end PalPeg.CloseoutCoreEnc24

#print axioms PalPeg.CloseoutCoreEnc24.ctrTapeD_dec
#print axioms PalPeg.CloseoutCoreEnc24.absChain_chainRepD_watch
#print axioms PalPeg.CloseoutCoreEnc24.chainTapes_shift
#print axioms PalPeg.CloseoutCoreEnc24.chainShiftBoundedD
#print axioms PalPeg.CloseoutCoreEnc24.restC_of_chainRepD
