import PalPeg.CloseoutCoreEnc12

/-!
# Closeout, step 2m: counters are micro-actions, and the radius-`cFor` re-export

`CloseoutCoreEnc12` closes the *generic* half of the composite repair
(`ActRule`/`compStep`/`teq_sweep_actList`, the sentinel alphabet `Γs`, the
budget table `microCount ≤ cFor = 64`) and lists three obstructions.  This file
attacks the third one — `chooseSelect`, `shiftPick`, `NAMED_shiftRem`,
`NAMED_workZero`, `NAMED_walkerRead` — and re-exports the `Kc = 1` layer of
`CloseoutCoreEnc8`–`10` at radius `K`.  Nothing here is about the whole machine,
so

**無条件 PAL ∈ PEG は未完.**

## What is established (unconditional)

* **§1 (a counter operation *is* one micro-action).**  The premise this file was
  written to check — "a unary counter's reset is a bounded rewrite" — is not
  merely plausible, it is already true *on the nose* in `LocalCounter`:
  `push`/`pop`/`resetSeg` are each literally one `STape.applyAction`
  (`mark,.right` / `blank,.left` / `sep,.right`).  So `opActs` turns every
  `LocalTick3.Op` into a list of at most **one** `CloseoutCoreEnc12.Act Seg`
  with `op_apply_eq_actList : o.apply t = actList blank t (opActs o)`, and
  `bankStep_actList` lifts this to every slot of the bank, whether or not the
  slot carries a role.  **No role switch is needed**: `LocalTick2.setRole` and
  `resetSlots` are a *different* mechanism (whole-slot recycling), and the
  branches at issue do not use it.
* **§2 (the two branches meet their tabled budget, slot by slot).**
  `chooseVm_phys_actList` and `shiftVm_phys_actList`: `LocalTick3.chooseVm` and
  `LocalTick3.shiftVm` are each two `bankTick`s, hence **at most two**
  micro-actions on every slot tape — `CloseoutCoreEnc12.microCount .chooseSelect
  = 2` is therefore a theorem about the counter bank, and the `2` of
  `microCount .shiftPick = 4` that the bank is responsible for is too.
* **§3 (the sign of a counter is a radius-1 window read).**  `rd_pred_cell`: on
  a tape with a non-empty left part the cell one step left of the head is
  `T.left.headD`.  Under `LocalCounter.SegCtr t v` that cell is `sep` when
  `v = 0` and `mark` when `v > 0` (`segCtr_rd_pred`), so `val t = 0` is decided
  by the radius-1 window (`segCtr_zero_iff`, `segCtr_pos_iff`).  This is the
  *slot-level* form of "`shiftRem`/`workZero` are focus reads".
* **§4 (the three residuals, from one carrier shape).**  `signSym` encodes
  `zero`/`positive`/`negative` in three of the nine `ProgLang` symbols;
  `CounterPark` is `CloseoutCoreEnc9.FocusCarrier` at `signSym ∘ val`, and
  `shiftRem_of_park`, `workZero_of_park` **derive** `NAMED_shiftRem` and
  `NAMED_workZero` from it.  `FlagPark` does the same for one bit, and
  `walkerRead_of_park` derives `NAMED_walkerRead`.  Three unstructured window
  residuals thus become three instances of the single residual shape that
  `CloseoutCoreEnc9` already uses for MARKS and SOURCE.
* **§5 (the radius-`K` re-export).**  `WinOnK`/`TapeActK` are `CloseoutCoreEnc8.WinOn`
  and `CloseoutCoreEnc10.TapeAct` with `Kc` replaced by a parameter `K` and the
  single action replaced by a list; `winOnK_of_tapeActK` is the bridge, via
  `CloseoutCoreEnc12.teq_sweep_actList`.  `shrinkWin`/`shrinkWin_readWin` then
  give `tapeActK_of_tapeAct`: **every `Kc = 1` residual already proved is a
  radius-`K` composite residual**, so the re-run of `CloseoutCoreEnc8`–`10` at
  `K := cFor` costs nothing on the branches that are done (e.g. `homeStart`).
  `wlen_actList` and `widthStepK_of_tapeActK` iterate the width argument
  (`CloseoutCoreEnc10.wlen_actOn`) along the list.

## What is *not* established, one line each

1. **The slot alphabet is not the core alphabet.**  §1–§3 live on `STape Seg`
   (`Seg = Fin 3`) while `padTapesN` lays tapes out over `Γc`; the missing fact
   is the embedding `Seg → Γc` used by `CloseoutCoreEnc.encTapes` on the bank
   slots together with the index of slot `j` in `Fin (tL P tChain)`, without
   which §1's action lists cannot be transported into a `TapeActK`, and §3's
   `sep`/`mark` cell cannot be named as the `signSym` of §4.
2. **`CounterPark`/`FlagPark` are carriers, not theorems.**  Exhibiting one is
   exactly missing fact 1 plus "the head is parked on the frontier", i.e. the
   layout invariant `SegCtr` for the laid-out slot at the layout's index; this
   file only shows what such a carrier buys.
3. **The margin at radius `K`.**  `winOnK_of_tapeActK` and `tapeActK_of_tapeAct`
   take `∀ m i, K ≤ pos (padTapesN n rep m i)` as a hypothesis:
   `CloseoutCoreEnc3.margin_encTapes1` gives only `Kc = 1`, and the left pad at
   radius `cFor` (the `Γs` sentinel layout of `CloseoutCoreEnc12` §4 widened to
   `cFor` cells) is not built.
4. **`shiftPick`'s other two micro-actions.**  §2 covers the bank half; the `L`
   cursor moves twice through `LocalInputView.moveRight`, whose cost in
   micro-actions depends on the queue layout `CloseoutCoreEnc7.queueTapes6` /
   `viewTapes8`, which is the same repair `NAMED_walkerRead` needs.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc13

open PalPeg PalPeg.Program
open PalPeg.Local (Window idx idx_val pos rd toList sweep readWin readWin_eq LocalStep)
open PalPeg.CloseoutCoreStep (Γc blankc tL QL)
open PalPeg.CloseoutCoreEnc (Kc QChain tChain)
open PalPeg.CloseoutCoreEnc12 (Act MoveC actOnG actList actList_cons TEqG teq_sweep_actList
  winAfter dAfter dAfter_le)
open PalPeg.LocalCounter (Seg)
open PalPeg.LocalState (GalilVML Ctr)

/-! ## 1. A counter operation is one micro-action -/

open PalPeg.LocalTick3 (Op bankStep bankTick)

/-- The micro-action list of one bank operation: `keep` is empty, and each of
`push`/`pop`/`reset` is a **single** `STape.applyAction`. -/
def opActs : Op → List (Act Seg)
  | .keep => []
  | .push => [some (PalPeg.LocalCounter.mark, .right)]
  | .pop => [some (PalPeg.LocalCounter.blank, .left)]
  | .reset => [some (PalPeg.LocalCounter.sep, .right)]

theorem opActs_length (o : Op) : (opActs o).length ≤ 1 := by
  cases o <;> simp [opActs]

/-- **A bank operation is a composite of at most one micro-action.** -/
theorem op_apply_eq_actList (o : Op) (t : STape Seg) :
    o.apply t = actList PalPeg.LocalCounter.blank t (opActs o) := by
  cases o <;> rfl

theorem actList_append {Γ : Type} (blank : Γ) (T : STape Γ) (as bs : List (Act Γ)) :
    actList blank T (as ++ bs) = actList blank (actList blank T as) bs := by
  induction as generalizing T with
  | nil => rfl
  | cons a as ih => rw [List.cons_append, actList_cons, actList_cons, ih]

variable {P : ℕ}

/-- **Every slot of a bank tick is a composite of at most one micro-action**,
whether or not the slot currently carries a role. -/
theorem bankStep_actList (f : Ctr → Op) (x : GalilVML P) (j : Fin P) :
    ∃ as : List (Act Seg), as.length ≤ 1 ∧
      bankStep f x j = actList PalPeg.LocalCounter.blank (x.phys j) as := by
  classical
  by_cases h : ∃ c, x.roles c = j
  · refine ⟨opActs (f (Classical.choose h)), opActs_length _, ?_⟩
    have : bankStep f x j = (f (Classical.choose h)).apply (x.phys j) := by
      simp only [bankStep, dif_pos h]
    rw [this, op_apply_eq_actList]
  · refine ⟨[], by simp, ?_⟩
    have : bankStep f x j = x.phys j := by simp only [bankStep, dif_neg h]
    rw [this]; rfl

theorem bankTick_phys (f : Ctr → Op) (x : GalilVML P) : (bankTick f x).phys = bankStep f x := rfl

/-- Two bank ticks: at most two micro-actions per slot. -/
theorem bankStep_two (f g : Ctr → Op) (x : GalilVML P) (j : Fin P) :
    ∃ as : List (Act Seg), as.length ≤ 2 ∧
      bankStep g (bankTick f x) j = actList PalPeg.LocalCounter.blank (x.phys j) as := by
  obtain ⟨as, has, h1⟩ := bankStep_actList f x j
  obtain ⟨bs, hbs, h2⟩ := bankStep_actList g (bankTick f x) j
  refine ⟨as ++ bs, ?_, ?_⟩
  · simp only [List.length_append]; omega
  · rw [h2, bankTick_phys, h1, actList_append]

/-! ## 2. The two branches meet their tabled budget on the bank -/

open PalPeg.GalilScaffoldController (Control)

/-- **`chooseSelect`'s two counter resets cost two micro-actions per slot.** -/
theorem chooseVm_phys_actList (c : Control) (x : GalilVML P) (j : Fin P) :
    ∃ as : List (Act Seg), as.length ≤ 2 ∧
      (PalPeg.LocalTick3.chooseVm c x).phys j
        = actList PalPeg.LocalCounter.blank (x.phys j) as :=
  bankStep_two _ _ x j

/-- **`shiftPick`'s bank half costs two micro-actions per slot.** -/
theorem shiftVm_phys_actList (w : PalPeg.GalilScaffoldChainWatch.State) (x : GalilVML P)
    (j : Fin P) :
    ∃ as : List (Act Seg), as.length ≤ 2 ∧
      (PalPeg.LocalTick3.shiftVm w x).phys j
        = actList PalPeg.LocalCounter.blank (x.phys j) as := by
  obtain ⟨as, has, h1⟩ := bankStep_actList PalPeg.LocalTick3.shiftOps1 x j
  obtain ⟨bs, hbs, h2⟩ := bankStep_actList PalPeg.LocalTick3.shiftOps2
    (PalPeg.LocalTick3.shiftMid w x) j
  refine ⟨as ++ bs, by simp only [List.length_append]; omega, ?_⟩
  have h3 : (PalPeg.LocalTick3.shiftVm w x).phys j
      = bankStep PalPeg.LocalTick3.shiftOps2 (PalPeg.LocalTick3.shiftMid w x) j := rfl
  have h4 : (PalPeg.LocalTick3.shiftMid w x).phys j = bankStep PalPeg.LocalTick3.shiftOps1 x j :=
    rfl
  rw [h3, h2, h4, h1, actList_append]

/-! ## 3. The sign of a counter is a radius-1 window read -/

variable {Γ : Type}

/-- **The cell one step left of the head** is the top of the left part. -/
theorem rd_pred_cell (blank : Γ) (T : STape Γ) (h : T.left ≠ []) :
    rd blank T (pos T - 1) = T.left.headD blank := by
  obtain ⟨L, f, R⟩ := T
  cases L with
  | nil => exact absurd rfl h
  | cons a L =>
      show (((a :: L).reverse ++ f :: R).getD ((a :: L).length - 1) blank) = a
      have hlen : (a :: L).length - 1 = L.reverse.length := by simp
      have hrev : (a :: L).reverse ++ f :: R = L.reverse ++ a :: f :: R := by
        simp [List.reverse_cons]
      rw [hlen, hrev]
      simp [List.getD_eq_getElem?_getD]

/-- Under the shape invariant the cell left of the head displays the sign. -/
theorem segCtr_rd_pred {t : STape Seg} {v : ℕ} (h : PalPeg.LocalCounter.SegCtr t v) :
    rd PalPeg.LocalCounter.blank t (pos t - 1)
      = if v = 0 then PalPeg.LocalCounter.sep else PalPeg.LocalCounter.mark := by
  obtain ⟨g, hg⟩ := h
  have hne : t.left ≠ [] := by
    rw [hg]; cases v <;> simp [List.replicate_succ]
  rw [rd_pred_cell _ _ hne, hg]
  cases v with
  | zero => simp
  | succ v => simp [List.replicate_succ]

/-- **The zero test is a radius-1 window read.** -/
theorem segCtr_zero_iff {t : STape Seg} {v : ℕ} (h : PalPeg.LocalCounter.SegCtr t v) :
    rd PalPeg.LocalCounter.blank t (pos t - 1) = PalPeg.LocalCounter.sep ↔ v = 0 := by
  rw [segCtr_rd_pred h]
  cases v with
  | zero => simp
  | succ v => simp [PalPeg.LocalCounter.sep_ne_mark.symm]

/-- **The sign test is a radius-1 window read.** -/
theorem segCtr_pos_iff {t : STape Seg} {v : ℕ} (h : PalPeg.LocalCounter.SegCtr t v) :
    rd PalPeg.LocalCounter.blank t (pos t - 1) = PalPeg.LocalCounter.mark ↔ 0 < v := by
  rw [segCtr_rd_pred h]
  cases v with
  | zero => simp [PalPeg.LocalCounter.sep_ne_mark]
  | succ v => simp

/-! ## 4. The three residuals, from one carrier shape -/

open PalPeg.GalilScaffoldChainInputSupply (ChainVM)
open PalPeg.GalilScaffoldController (Mode)
open PalPeg.LocalChain (ChainL)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalSysConcrete (Starved)
open PalPeg.CloseoutCoreEnc8 (encPadN padTapesN rwOf NAMED_branchRead margin_encPadN)
open PalPeg.CloseoutCoreEnc9 (FocusCarrier branchRead_ofFocus NAMED_shiftRem NAMED_workZero
  NAMED_walkerRead)
open PalPeg.GalilScaffoldCounter (Counter zero positive)

variable {n delay Lp Lf : ℕ} {rep : ChainVM → ChainL}

/-- The three-way sign of a unary counter, as a `ProgLang` symbol. -/
def signSym (c : Counter) : Fin 9 := if zero c then 0 else if positive c then 1 else 2

theorem signSym_eq_zero_iff (c : Counter) : signSym c = 0 ↔ zero c = true := by
  unfold signSym
  by_cases hz : zero c = true
  · simp [hz]
  · by_cases hp : positive c = true <;> simp [hz, hp]

theorem signSym_eq_one_iff (c : Counter) : signSym c = 1 ↔ positive c = true := by
  unfold signSym
  by_cases hz : zero c = true
  · have hp : positive c = false := by
      rcases c with ⟨ps, ns⟩
      simp only [zero, Bool.and_eq_true, List.isEmpty_iff] at hz
      simp [positive, hz.1]
    simp [hz, hp]
  · by_cases hp : positive c = true <;> simp [hz, hp]

/-- A bit, as a `ProgLang` symbol. -/
def boolSym (b : Bool) : Fin 9 := if b then 1 else 0

theorem boolSym_eq_one_iff (b : Bool) : boolSym b = 1 ↔ b = true := by
  cases b <;> simp [boolSym]

/-- **The parking carrier for a counter**: some laid-out tape has, under its
head, the symbol displaying the sign of `val`.  This is exactly
`CloseoutCoreEnc9.FocusCarrier` at `signSym ∘ val`. -/
def CounterPark (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (val : Mirrored1 P → Counter) (md : Mode) : Type :=
  FocusCarrier (P := P) n delay Lp Lf rep (fun m => signSym (val m)) md

/-- **The parking carrier for a bit.** -/
def FlagPark (n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (b : Mirrored1 P → Bool) (md : Mode) : Type :=
  FocusCarrier (P := P) n delay Lp Lf rep (fun m => boolSym (b m)) md

/-- **`NAMED_shiftRem`, from the parking carrier of `remaining`.** -/
noncomputable def shiftRem_of_park {md : Mode}
    (A : CounterPark (P := P) n delay Lp Lf rep
      (fun m => (PalPeg.LocalArrival.abs' m.vm).remaining) md) :
    NAMED_shiftRem (P := P) n delay Lp Lf rep md := by
  classical
  exact branchRead_ofFocus A.idx _ (fun a => decide (a = 1)) A.spec
    (fun m _ _ => by
      simp only [decide_eq_true_eq]
      exact (signSym_eq_one_iff _).trans Iff.rfl)

/-- **`NAMED_workZero`, from the parking carrier of the fpp work counter.** -/
noncomputable def workZero_of_park {md : Mode}
    (A : CounterPark (P := P) n delay Lp Lf rep
      (fun m => (PalPeg.LocalArrival.abs' m.vm).fpp.work) md) :
    NAMED_workZero (P := P) n delay Lp Lf rep md := by
  classical
  exact branchRead_ofFocus A.idx _ (fun a => decide (a = 0)) A.spec
    (fun m _ _ => by
      simp only [decide_eq_true_eq]
      exact (signSym_eq_zero_iff _).trans Iff.rfl)

/-- **`NAMED_walkerRead`, from the parking carrier of the walker's emptiness
bit.** -/
noncomputable def walkerRead_of_park {md : Mode}
    (A : FlagPark (P := P) n delay Lp Lf rep
      (fun m => (PalPeg.GalilScaffoldPlace.read
        (PalPeg.LocalArrival.abs' m.vm).fpp.walker).isNone) md) :
    NAMED_walkerRead (P := P) n delay Lp Lf rep md := by
  classical
  exact branchRead_ofFocus A.idx _ (fun a => decide (a = 1)) A.spec
    (fun m _ _ => by
      simp only [decide_eq_true_eq]
      rw [boolSym_eq_one_iff]
      simp [Option.isNone_iff_eq_none])

/-! ## 5. The radius-`K` re-export of `CloseoutCoreEnc8`–`10` -/

open PalPeg.CloseoutCoreEnc4 (TEq)
open PalPeg.CloseoutCoreEnc5 (wlen)
open PalPeg.CloseoutCoreEnc10 (actOn winAct dOfAct wlen_actOn TapeAct)

/-- The windows a state presents at radius `K`. -/
def rwOfK (K : ℕ) {Q : Type} {t : ℕ} (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (m : Mirrored1 P) : Fin t → Window Γc K :=
  fun j => readWin blankc K ((enc m).2 j)

/-- `CloseoutCoreEnc8.WinOn` at radius `K`. -/
structure WinOnK (K : ℕ) (Q : Type) (t : ℕ) (enc : Mirrored1 P → Q × (Fin t → STape Γc))
    (f : Mirrored1 P → Mirrored1 P) (md : Mode) (sc : Mirrored1 P → Prop) where
  nx : Q → (Fin t → Window Γc K) → Q × (Fin t → Window Γc K × ℤ)
  disp : ∀ (q : Q) (ws : Fin t → Window Γc K) (j : Fin t), |((nx q ws).2 j).2| ≤ (K : ℤ)
  ctl : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm → sc m →
    (enc (f m)).1 = (nx (enc m).1 (rwOfK K enc m)).1
  tape : ∀ (m : Mirrored1 P) (j : Fin t), m.vm.ctl.mode = md → ¬ Starved m.vm → sc m →
    TEqG blankc ((enc (f m)).2 j)
      (sweep blankc K ((enc m).2 j) ((nx (enc m).1 (rwOfK K enc m)).2 j).1
        ((nx (enc m).1 (rwOfK K enc m)).2 j).2)

/-- `CloseoutCoreEnc10.TapeAct` at radius `K`, with a *list* of micro-actions. -/
structure TapeActK (K n delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (f : Mirrored1 P → Mirrored1 P) (md : Mode) (sc : Mirrored1 P → Prop) where
  nq : QL delay Lp Lf P QChain → (Fin (tL P tChain) → Window Γc K) →
    QL delay Lp Lf P QChain
  acts : QL delay Lp Lf P QChain → (Fin (tL P tChain) → Window Γc K) → ℕ → List (Act Γc)
  len_le : ∀ q ws i, (acts q ws i).length ≤ K
  ctl : ∀ m : Mirrored1 P, m.vm.ctl.mode = md → ¬ Starved m.vm → sc m →
    (encPadN n delay Lp Lf rep (f m)).1
      = nq (encPadN n delay Lp Lf rep m).1 (rwOfK K (encPadN n delay Lp Lf rep) m)
  tape : ∀ (m : Mirrored1 P) (i : ℕ), m.vm.ctl.mode = md → ¬ Starved m.vm → sc m →
    padTapesN n rep (f m) i
      = actList blankc (padTapesN n rep m i)
        (acts (encPadN n delay Lp Lf rep m).1 (rwOfK K (encPadN n delay Lp Lf rep) m) i)

/-- **The window residual, from the composite tape residual.** -/
noncomputable def winOnK_of_tapeActK {K : ℕ} {f : Mirrored1 P → Mirrored1 P} {md : Mode}
    {sc : Mirrored1 P → Prop} (A : TapeActK (P := P) K n delay Lp Lf rep f md sc)
    (hmar : ∀ (m : Mirrored1 P) (i : ℕ), K ≤ pos (padTapesN n rep m i)) :
    WinOnK (P := P) K (QL delay Lp Lf P QChain) (tL P tChain)
      (encPadN n delay Lp Lf rep) f md sc where
  nx := fun q ws => (A.nq q ws, fun j =>
    (winAfter K (ws j) (A.acts q ws j.val), dAfter K (ws j) (A.acts q ws j.val)))
  disp := fun q ws j => dAfter_le K (ws j) (A.acts q ws j.val) (A.len_le q ws j.val)
  ctl := fun m hmd hs hsc => A.ctl m hmd hs hsc
  tape := fun m j hmd hs hsc => by
    have hT : (encPadN n delay Lp Lf rep (f m)).2 j = padTapesN n rep (f m) j.val := rfl
    have hT0 : (encPadN n delay Lp Lf rep m).2 j = padTapesN n rep m j.val := rfl
    rw [hT, A.tape m j.val hmd hs hsc, hT0]
    exact teq_sweep_actList blankc K (padTapesN n rep m j.val) _
      (A.len_le _ _ _) (hmar m j.val)

/-- Restricting a radius-`K` window to radius `Kc = 1`. -/
def shrinkWin (K : ℕ) (w : Window Γc K) : Window Γc Kc :=
  fun i => w (idx K (K - 1 + (i : ℕ)))

theorem shrinkWin_readWin (K : ℕ) (hK : 1 ≤ K) (T : STape Γc) (hpos : K ≤ pos T) :
    shrinkWin K (readWin blankc K T) = readWin blankc Kc T := by
  funext i
  have hi : (i : ℕ) ≤ 2 := by
    have := i.isLt
    simp only [Kc] at this
    omega
  have h1 : K - 1 + (i : ℕ) ≤ 2 * K := by omega
  have h2 : (i : ℕ) ≤ 2 * Kc := by simp only [Kc]; omega
  show readWin blankc K T (idx K (K - 1 + (i : ℕ))) = readWin blankc Kc T i
  rw [readWin_eq, readWin_eq, idx_val h1]
  have h3 : pos T - K + (K - 1 + (i : ℕ)) = pos T - Kc + (i : ℕ) := by
    simp only [Kc]; omega
  rw [h3]

/-- **Every `Kc = 1` tape residual is a radius-`K` composite residual.** -/
noncomputable def tapeActK_of_tapeAct {K : ℕ} {f : Mirrored1 P → Mirrored1 P} {md : Mode}
    {sc : Mirrored1 P → Prop} (A : TapeAct (P := P) n delay Lp Lf rep f md sc)
    (hK : 1 ≤ K) (hmar : ∀ (m : Mirrored1 P) (i : ℕ), K ≤ pos (padTapesN n rep m i)) :
    TapeActK (P := P) K n delay Lp Lf rep f md sc where
  nq := fun q ws => A.nq q (fun j => shrinkWin K (ws j))
  acts := fun q ws i => [A.act q (fun j => shrinkWin K (ws j)) i]
  len_le := fun q ws i => by simpa using hK
  ctl := fun m hmd hs hsc => by
    have hws : (fun j => shrinkWin K (rwOfK K (encPadN n delay Lp Lf rep) m j))
        = rwOf (encPadN n delay Lp Lf rep) m := by
      funext j
      exact shrinkWin_readWin K hK _ (hmar m j.val)
    rw [show (fun j => shrinkWin K (rwOfK K (encPadN n delay Lp Lf rep) m j))
      = rwOf (encPadN n delay Lp Lf rep) m from hws]
    exact A.ctl m hmd hs hsc
  tape := fun m i hmd hs hsc => by
    have hws : (fun j => shrinkWin K (rwOfK K (encPadN n delay Lp Lf rep) m j))
        = rwOf (encPadN n delay Lp Lf rep) m := by
      funext j
      exact shrinkWin_readWin K hK _ (hmar m j.val)
    rw [show (fun j => shrinkWin K (rwOfK K (encPadN n delay Lp Lf rep) m j))
      = rwOf (encPadN n delay Lp Lf rep) m from hws]
    rw [A.tape m i hmd hs hsc]
    cases A.act (encPadN n delay Lp Lf rep m).1 (rwOf (encPadN n delay Lp Lf rep) m) i <;> rfl

/-! ### The width argument, iterated along the list -/

theorem pos_actOnG_le (blank : Γ) (T : STape Γ) (a : Act Γ) :
    pos (actOnG blank T a) ≤ pos T + 1 := by
  cases a with
  | none => simp [actOnG]
  | some sm =>
      obtain ⟨s, mv⟩ := sm
      show pos (T.applyAction blank (s, mv)) ≤ pos T + 1
      rw [PalPeg.Local.pos_applyAction]
      cases mv <;> simp <;> omega

theorem actOnG_eq_actOn (T : STape Γc) (a : Act Γc) : actOnG blankc T a = actOn T a := by
  cases a <;> rfl

/-- **A composite conserves the stored width**, if the whole composite stays
strictly inside the reservoir. -/
theorem wlen_actList (T : STape Γc) (as : List (Act Γc)) (h : pos T + as.length < wlen T) :
    wlen (actList blankc T as) = wlen T := by
  induction as generalizing T with
  | nil => rfl
  | cons a as ih =>
      simp only [List.length_cons] at h
      have h1 : wlen (actOnG blankc T a) = wlen T := by
        rw [actOnG_eq_actOn]
        exact wlen_actOn T a (by omega)
      have h2 : pos (actOnG blankc T a) ≤ pos T + 1 := pos_actOnG_le blankc T a
      rw [actList_cons, ih (actOnG blankc T a) (by omega), h1]

open PalPeg.CloseoutCoreEnc8 (padRN wlen_padRN pos_padRN wlen_padTapesN)
open PalPeg.CloseoutCoreEnc9 (NAMED_widthStep)

/-- **The width residual, from the composite tape residual**, provided the
reservoir is one cell wider than the radius. -/
theorem widthStepK_of_tapeActK {K : ℕ} {f : Mirrored1 P → Mirrored1 P} {md : Mode}
    {sc : Mirrored1 P → Prop} (A : TapeActK (P := P) K n delay Lp Lf rep f md sc)
    (hn : K + 1 ≤ n) : NAMED_widthStep (P := P) rep f md sc := by
  intro m i hmd hs hsc
  have hroom : pos (padTapesN n rep m i) + (K + 1) ≤ wlen (padTapesN n rep m i) :=
    PalPeg.CloseoutCoreEnc8.room_padRN blankc n (K + 1) _ hn
  have hlen := A.len_le (encPadN n delay Lp Lf rep m).1
    (rwOfK K (encPadN n delay Lp Lf rep) m) i
  have h0 : wlen (padTapesN n rep (f m) i) = wlen (padTapesN n rep m i) := by
    rw [A.tape m i hmd hs hsc]
    exact wlen_actList _ _ (by omega)
  rw [wlen_padTapesN, wlen_padTapesN] at h0
  omega

#print axioms PalPeg.CloseoutCoreEnc13.op_apply_eq_actList
#print axioms PalPeg.CloseoutCoreEnc13.bankStep_actList
#print axioms PalPeg.CloseoutCoreEnc13.chooseVm_phys_actList
#print axioms PalPeg.CloseoutCoreEnc13.shiftVm_phys_actList
#print axioms PalPeg.CloseoutCoreEnc13.segCtr_zero_iff
#print axioms PalPeg.CloseoutCoreEnc13.segCtr_pos_iff
#print axioms PalPeg.CloseoutCoreEnc13.shiftRem_of_park
#print axioms PalPeg.CloseoutCoreEnc13.workZero_of_park
#print axioms PalPeg.CloseoutCoreEnc13.walkerRead_of_park
#print axioms PalPeg.CloseoutCoreEnc13.winOnK_of_tapeActK
#print axioms PalPeg.CloseoutCoreEnc13.tapeActK_of_tapeAct
#print axioms PalPeg.CloseoutCoreEnc13.wlen_actList
#print axioms PalPeg.CloseoutCoreEnc13.widthStepK_of_tapeActK

end PalPeg.CloseoutCoreEnc13
