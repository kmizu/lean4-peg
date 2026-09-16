import PalPeg.CloseoutCoreEnc2

/-!
# Closeout, step 2c: the sentinel layout, stack tapes, and the residual bundle

`CloseoutCoreEnc2` refutes `NAMED_queueLayout` and `NAMED_margin` as stated and
repairs them.  This file closes the margin residual **unconditionally** for a
sentinel-shifted layout, supplies the geometric content behind the repaired
queue obligation (a stack laid out with its head on the top cell moves its
*head*, not its content, and every push/pop is a radius-`1` window rewrite),
collects the injectivity building blocks, and packages everything that is still
open into one bundle from which a `CloseoutCoreAudit.CoreLocal` term for the
concrete core is actually constructed.

No `LocalStep` is built, so

**無条件 PAL ∈ PEG は未完.**

## What is established

* **§1 (`NAMED_margin'` — closed).**  `shift1` prepends one blank cell at the
  left edge.  `pos_shift1` puts every head at distance `≥ Kc` from the edge,
  `toList_shift1`/`rd_shift1_*` say the transport is a pure re-indexing, and
  `winRealizes_shift1` transports `WinRealizes` across it in **both** the
  `pos T = 0` and the `pos T ≥ 1` case.  Hence `encTapes1`, the sentinel
  version of `CloseoutCoreEnc.encTapes`, satisfies
  `margin_encTapes1 : ∀ m i, Kc ≤ pos (encTapes1 rep m i)` with no reachability
  hypothesis at all, and `NAMED_margin'` holds for *every* `Reach`
  (`named_margin'_encTapes1`).
* **§2 (stack tapes).**  `winRealizes_of_agree` is the reusable criterion
  ("head moves by `≤ Kc`, cells outside the old window unchanged").  `stackTape` lays a list out with the head on its top
  cell and a sentinel below.  `winRealizes_push`/`winRealizes_pop` show a push
  and a pop are single radius-`1` window rewrites: the content stays put and the
  head moves.  This is exactly the geometry `not_NAMED_queueLayout` shows
  `listTape` lacks.  `queueTapes5` lays a Hood–Melville queue on the five stacks
  its rotation state actually uses.
* **§3 (injectivity blocks, and one refutation).**  `cellSym_inj`,
  `mapTape_inj`, `shift1_inj` and `stackTape_inj` are injective;
  `not_injective_listTape1` refutes the corresponding statement for the
  sentinel cursor layout of `CloseoutCoreEnc2`, because `cellSym none = blankc`
  makes the empty list and `[none]` indistinguishable.  The stack layout of §2
  does not have this defect: `pos_stackTape` exposes the length.
* **§4 (the bundle).**  `CoreResidual` collects exactly what is still open, and
  `coreLocal_ofResidual` builds
  `CloseoutCoreAudit.CoreLocal (sysC M repC) x0 Q Γc t Kc` from it, via
  `CloseoutCoreStep.coreLocal_of`.

## What is *not* established

`NAMED_stepWindow`, `NAMED_feedWindow`, `NAMED_fppQuantum`, `NAMED_encInjective`
and the queue layout remain open; §5 restates them with their exact types.  The
`tView = 4` budget of `CloseoutCoreStep` is moreover **too small** for the five
stacks of §2, which `NAMED_queueBudget` records.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc3

open PalPeg PalPeg.Program
open PalPeg.Local (Window idx idx_val pos rd toList LocalStep)
open PalPeg.LocalCounter (Seg)
open PalPeg.LocalInputView (InputView)
open PalPeg.LocalState (GalilVML ViewLocal)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.GalilScaffoldChainInputSupply (ChainVM)
open PalPeg.GalilScaffoldController (Control)
open PalPeg.LocalChain (ChainL)
open PalPeg.LocalSysConcrete (Steps sysC tickC feedC)
open PalPeg.LocalTrackingLatch (LX)
open PalPeg.CloseoutCoreAudit (CoreLocal)
open PalPeg.CloseoutCoreStep (Γc blankc tView nViews tMir tBuf tL QL qOfL
  RealizedTick RealizedFeed coreLocal_of)
open PalPeg.CloseoutCoreEnc (Kc WinRealizes segSym mapTape cellSym encTapes
  QChain tChain qChainOf winRealizes_refl)

/-! ## 1. The sentinel shift closes the margin -/

/-- Prepend one blank cell at the left edge of a tape. -/
def shift1 {Γ : Type} (b : Γ) (T : STape Γ) : STape Γ :=
  ⟨T.left ++ [b], T.focus, T.right⟩

@[simp] theorem pos_shift1 {Γ : Type} (b : Γ) (T : STape Γ) :
    pos (shift1 b T) = pos T + 1 := by
  simp [pos, shift1]

theorem toList_shift1 {Γ : Type} (b : Γ) (T : STape Γ) :
    toList (shift1 b T) = b :: toList T := by
  simp [toList, shift1]

@[simp] theorem rd_shift1_zero {Γ : Type} (b : Γ) (T : STape Γ) :
    rd b (shift1 b T) 0 = b := by
  rw [rd, toList_shift1]; rfl

@[simp] theorem rd_shift1_succ {Γ : Type} (b : Γ) (T : STape Γ) (p : ℕ) :
    rd b (shift1 b T) (p + 1) = rd b T p := by
  rw [rd, rd, toList_shift1]; rfl

/-- The head of a shifted tape is always at least `Kc` cells from the edge. -/
theorem margin_shift1 {Γ : Type} (b : Γ) (T : STape Γ) : Kc ≤ pos (shift1 b T) := by
  rw [pos_shift1]
  exact Nat.succ_le_succ (Nat.zero_le _)

/-- **`WinRealizes` transports across the sentinel shift.** -/
theorem winRealizes_shift1 {T T' : STape Γc} (h : WinRealizes T T') :
    WinRealizes (shift1 blankc T) (shift1 blankc T') := by
  classical
  obtain ⟨w, d, hd, hpos, hcell⟩ := h
  refine ⟨(fun i => if pos T = 0 then (if (i : ℕ) = 0 then blankc else w (idx Kc ((i : ℕ) - 1)))
      else w i), d, hd, ?_, ?_⟩
  · rw [pos_shift1, pos_shift1]
    push_cast
    omega
  · intro p
    cases p with
    | zero =>
        rw [rd_shift1_zero]
        simp only [pos_shift1, Kc]
        by_cases hmem : pos T + 1 - 1 ≤ 0 ∧ 0 ≤ pos T + 1 + 1
        · rw [if_pos hmem]
          have hp0 : pos T = 0 := by omega
          rw [hp0]
          simp [idx]
        · rw [if_neg hmem, rd_shift1_zero]
    | succ q =>
        rw [rd_shift1_succ, hcell q, rd_shift1_succ]
        simp only [pos_shift1, Kc]
        by_cases hmem : pos T + 1 - 1 ≤ q + 1 ∧ q + 1 ≤ pos T + 1 + 1
        · rw [if_pos hmem]
          have hq : pos T - 1 ≤ q ∧ q ≤ pos T + 1 := by omega
          rw [if_pos hq]
          by_cases hp0 : pos T = 0
          · have hq2 : q = 0 ∨ q = 1 := by omega
            rw [hp0]
            rcases hq2 with rfl | rfl <;> simp [idx]
          · have h1 : 1 ≤ pos T := Nat.one_le_iff_ne_zero.mpr hp0
            rw [if_neg hp0]
            congr 1
            apply Fin.ext
            rw [idx_val (by omega), idx_val (by omega)]
            omega
        · rw [if_neg hmem, if_neg (by omega)]

/-- **The sentinel layout of the core.** -/
noncomputable def encTapes1 {P : ℕ} (rep : ChainVM → ChainL) (m : Mirrored1 P) :
    ℕ → STape Γc := fun i => shift1 blankc (encTapes rep m i)

/-- **The margin holds for the sentinel layout, unconditionally.** -/
theorem margin_encTapes1 {P : ℕ} (rep : ChainVM → ChainL) (m : Mirrored1 P) (i : ℕ) :
    Kc ≤ pos (encTapes1 rep m i) := margin_shift1 _ _

/-- …so the repaired margin residual of `CloseoutCoreEnc2` is discharged for it,
for every notion of reachability. -/
theorem named_margin'_encTapes1 {P : ℕ} (rep : ChainVM → ChainL)
    (Reach : Mirrored1 P → Prop) :
    PalPeg.CloseoutCoreEnc2.NAMED_margin' (P := P) (encTapes1 rep) Reach :=
  fun m _ i => margin_encTapes1 rep m i

/-- And window-locality is unaffected by the shift, tape by tape. -/
theorem winRealizes_encTapes1 {P : ℕ} (rep : ChainVM → ChainL) {m m' : Mirrored1 P}
    {i : ℕ} (h : WinRealizes (encTapes rep m i) (encTapes rep m' i)) :
    WinRealizes (encTapes1 rep m i) (encTapes1 rep m' i) := winRealizes_shift1 h

/-! ## 2. Stack tapes: the head moves, the content does not -/

/-- **A sufficient criterion for `WinRealizes`**: the head moves by at most
`Kc`, and the two tapes agree at every cell outside the radius-`Kc` window of
the *old* head.  (The window itself is then read off `T'`.) -/
theorem winRealizes_of_agree {T T' : STape Γc} (d : ℤ) (hd : |d| ≤ (Kc : ℤ))
    (hpos : (pos T' : ℤ) = (pos T : ℤ) + d)
    (hagree : ∀ p : ℕ, ¬ (pos T - Kc ≤ p ∧ p ≤ pos T + Kc) →
      rd blankc T' p = rd blankc T p) :
    WinRealizes T T' := by
  classical
  refine ⟨(fun i => rd blankc T' (pos T - Kc + (i : ℕ))), d, hd, hpos, ?_⟩
  intro p
  by_cases hmem : pos T - Kc ≤ p ∧ p ≤ pos T + Kc
  · rw [if_pos hmem]
    have hle : p - (pos T - Kc) ≤ 2 * Kc := by
      simp only [Kc] at hmem ⊢; omega
    simp only [idx_val hle]
    congr 1
    simp only [Kc] at hmem ⊢
    omega
  · rw [if_neg hmem]
    exact hagree p hmem

/-- A list as a stack tape: the top cell under the head, the rest to the left,
one sentinel blank below the bottom. -/
def stackTape (l : List (Option (Fin 2))) : STape Γc :=
  match l with
  | [] => ⟨[], blankc, []⟩
  | a :: rest => ⟨(rest.map cellSym) ++ [blankc], cellSym a, []⟩

/-- **The head of a stack tape sits on the top cell**, at depth `l.length`. -/
@[simp] theorem pos_stackTape (l : List (Option (Fin 2))) : pos (stackTape l) = l.length := by
  cases l with
  | nil => rfl
  | cons a t => simp [pos, stackTape]

/-- The absolute contents of a stack tape: the sentinel, then the list bottom-up. -/
theorem toList_stackTape (l : List (Option (Fin 2))) :
    toList (stackTape l) = blankc :: (l.map cellSym).reverse := by
  cases l with
  | nil => rfl
  | cons a t => simp [toList, stackTape]

/-- **Pushing changes exactly one cell**, the one just above the old head. -/
theorem getD_append_singleton {α : Type} (X : List α) (y b : α) {q : ℕ}
    (h : q ≠ X.length) : (X ++ [y]).getD q b = X.getD q b := by
  rcases Nat.lt_or_ge q X.length with hlt | hge
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
  · have hq : X.length < q := by omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem rd_stackTape_cons (a : Option (Fin 2)) (l : List (Option (Fin 2))) {p : ℕ}
    (hp : p ≠ l.length + 1) :
    rd blankc (stackTape (a :: l)) p = rd blankc (stackTape l) p := by
  rw [rd, rd, toList_stackTape, toList_stackTape]
  have hrev : ((a :: l).map cellSym).reverse = (l.map cellSym).reverse ++ [cellSym a] := by
    simp
  rw [hrev]
  cases p with
  | zero => rfl
  | succ q =>
      rw [List.getD_cons_succ, List.getD_cons_succ]
      exact getD_append_singleton _ _ _ (by simp; omega)

/-- **A push is one radius-`1` window rewrite**: the head moves right by one and
the cell it lands on is written; nothing else changes. -/
theorem winRealizes_push (a : Option (Fin 2)) (l : List (Option (Fin 2))) :
    WinRealizes (stackTape l) (stackTape (a :: l)) := by
  refine winRealizes_of_agree (1 : ℤ) (by simp [Kc]) (by simp) ?_
  intro p hp
  refine rd_stackTape_cons a l ?_
  simp only [Kc, pos_stackTape] at hp
  omega

/-- **A pop is one radius-`1` window rewrite.** -/
theorem winRealizes_pop (a : Option (Fin 2)) (l : List (Option (Fin 2))) :
    WinRealizes (stackTape (a :: l)) (stackTape l) := by
  refine winRealizes_of_agree (-1 : ℤ) (by simp [Kc]) (by simp) ?_
  intro p hp
  refine (rd_stackTape_cons a l ?_).symm
  simp only [Kc, pos_stackTape, List.length_cons] at hp
  omega


/-- The five stacks a Hood–Melville rotation actually touches. -/
def queueTapes5 (q : RTQueue.Queue (Fin 2)) : ℕ → STape Γc
  | 0 => stackTape (q.front.map some)
  | 1 => stackTape (q.rear.map some)
  | 2 => match q.state with
      | .reversing _ f _ _ _ => stackTape (f.map some)
      | _ => stackTape []
  | 3 => match q.state with
      | .reversing _ _ f' _ _ => stackTape (f'.map some)
      | .appending _ f' _ => stackTape (f'.map some)
      | _ => stackTape []
  | _ => match q.state with
      | .reversing _ _ _ _ r' => stackTape (r'.map some)
      | .appending _ _ r' => stackTape (r'.map some)
      | .done f => stackTape (f.map some)
      | .idle => stackTape []

/-! ## 3. Injectivity building blocks -/

theorem cellSym_inj : Function.Injective cellSym := by decide

theorem mapTape_inj {Γ Γ' : Type} {f : Γ → Γ'} (hf : Function.Injective f) :
    Function.Injective (mapTape f) := by
  rintro ⟨L, x, R⟩ ⟨L', x', R'⟩ h
  have h1 : L.map f = L'.map f := congrArg STape.left h
  have h2 : f x = f x' := congrArg STape.focus h
  have h3 : R.map f = R'.map f := congrArg STape.right h
  have e1 : L = L' := List.map_injective_iff.mpr hf h1
  have e3 : R = R' := List.map_injective_iff.mpr hf h3
  rw [e1, hf h2, e3]

theorem shift1_inj {Γ : Type} (b : Γ) : Function.Injective (shift1 b) := by
  rintro ⟨L, x, R⟩ ⟨L', x', R'⟩ h
  have h1 : L ++ [b] = L' ++ [b] := congrArg STape.left h
  have h2 : x = x' := congrArg STape.focus h
  have h3 : R = R' := congrArg STape.right h
  rw [List.append_cancel_right h1, h2, h3]

theorem stackTape_inj : Function.Injective stackTape := by
  intro l l' h
  cases l with
  | nil =>
      cases l' with
      | nil => rfl
      | cons b t =>
          exact absurd (congrArg pos h) (by
            rw [pos_stackTape, pos_stackTape]; simp)
  | cons a t =>
      cases l' with
      | nil =>
          exact absurd (congrArg pos h) (by
            rw [pos_stackTape, pos_stackTape]; simp)
      | cons b t' =>
          have hf : cellSym a = cellSym b := congrArg STape.focus h
          have hl : (t.map cellSym) ++ [blankc] = (t'.map cellSym) ++ [blankc] :=
            congrArg STape.left h
          have ht : t.map cellSym = t'.map cellSym := List.append_cancel_right hl
          rw [cellSym_inj hf, List.map_injective_iff.mpr cellSym_inj ht]

/-- **`listTape1` is *not* injective.**  `cellSym none = blankc`, so the empty
cursor list and the one-cell list `[none]` have the same sentinel layout: the
"no cell" and the "unknown cell" readings are confused.  Any injectivity proof
for the layout must therefore recover the *lengths* from elsewhere — which is
what the stack layout of §2 does, since `pos_stackTape` exposes the length. -/
theorem cellSym_none : cellSym none = blankc := by decide

theorem not_injective_listTape1 : ¬ Function.Injective PalPeg.CloseoutCoreEnc2.listTape1 := by
  intro h
  have hEq : PalPeg.CloseoutCoreEnc2.listTape1 [] = PalPeg.CloseoutCoreEnc2.listTape1 [none] := by
    show (⟨[blankc], blankc, []⟩ : STape Γc) = ⟨[blankc], cellSym none, []⟩
    rw [cellSym_none]
  exact absurd (h hEq) (by simp)

/-! ## 4. The residual bundle, and the `CoreLocal` term it yields -/

variable {P : ℕ} {Q : Type} {t : ℕ}

/-- **Everything that is still open, in one record.** -/
structure CoreResidual (M : Steps P) (repC : Control → Bool) (x0 : LX (Mirrored1 P))
    (Q : Type) (t : ℕ) where
  L0 : LocalStep (Fin 2) Q Γc t Kc
  q0 : Q
  repQ : Q → Bool
  outQ : Q → Bool
  encC : Mirrored1 P → Q × (Fin t → STape Γc)
  htick : RealizedTick encC L0 (tickC M)
  hfeed : RealizedFeed encC L0
  hrep : ∀ m : Mirrored1 P, repC m.vm.ctl = repQ (encC m).1
  hout : ∀ m : Mirrored1 P, m.vm.ctl.output = outQ (encC m).1
  hinit : encC x0.core = (q0, fun _ => STape.blankTape blankc)

/-- **The `CoreLocal` term for the concrete core**, built from the bundle. -/
def coreLocal_ofResidual {M : Steps P} {repC : Control → Bool} {x0 : LX (Mirrored1 P)}
    (R : CoreResidual M repC x0 Q t) : CoreLocal (sysC M repC) x0 Q Γc t Kc :=
  coreLocal_of M repC x0 R.L0 R.q0 R.repQ R.outQ R.encC R.htick R.hfeed R.hrep R.hout R.hinit

theorem coreLocal_ofResidual_L0 {M : Steps P} {repC : Control → Bool}
    {x0 : LX (Mirrored1 P)} (R : CoreResidual M repC x0 Q t) :
    (coreLocal_ofResidual R).L0 = R.L0 := rfl

/-! ## 5. The residuals that remain open -/

/-- **Gap (3): one `LocalSysConcrete.tickC` is one `LocalStep`** — the layout
being the sentinel one of §1. -/
def NAMED_stepWindow (delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (f : Mirrored1 P → Mirrored1 P) : Prop :=
  ∃ L0 : LocalStep (Fin 2) (QL delay Lp Lf P QChain) Γc (tL P tChain) Kc,
    RealizedTick (P := P)
      (fun m => (qOfL delay Lp Lf (fun c => qChainOf (rep c)) m,
        fun i => encTapes1 rep m i.val)) L0 f

/-- **The arrival half.** -/
def NAMED_feedWindow (delay Lp Lf : ℕ) (rep : ChainVM → ChainL) : Prop :=
  ∃ L0 : LocalStep (Fin 2) (QL delay Lp Lf P QChain) Γc (tL P tChain) Kc,
    RealizedFeed (P := P)
      (fun m => (qOfL delay Lp Lf (fun c => qChainOf (rep c)) m,
        fun i => encTapes1 rep m i.val)) L0

/-- **The fpp quantum.** -/
def NAMED_fppQuantum (raw : List (Fin 2))
    (stOf : ℕ → PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (Pw : PalPeg.GalilScaffoldChainInputSupply.Shared) (qq : ℕ) (first : Fin 9) : Prop :=
  ∃ g : Mirrored1 P → Mirrored1 P,
    PalPeg.CloseoutCoreStep.AgreeOn raw stOf (PalPeg.LocalWF.ffpp (P := P) Pw qq first) g
      PalPeg.GalilScaffoldController.Mode.fpp

/-- **Injectivity of the sentinel layout on reachable states.** -/
def NAMED_encInjective (delay Lp Lf : ℕ) (rep : ChainVM → ChainL)
    (Reach : Mirrored1 P → Prop) : Prop :=
  ∀ m m' : Mirrored1 P, Reach m → Reach m' →
    ((qOfL delay Lp Lf (fun c => qChainOf (rep c)) m,
        fun i : Fin (tL P tChain) => encTapes1 rep m i.val) =
      (qOfL delay Lp Lf (fun c => qChainOf (rep c)) m',
        fun i : Fin (tL P tChain) => encTapes1 rep m' i.val)) → m = m'

/-- **The repaired queue layout, on the five stacks.** -/
def NAMED_queueLayout5 : Prop :=
  ∀ v v' : InputView, PalPeg.LocalInputView.WF v → ViewLocal v v' →
    ∀ i : ℕ, WinRealizes (queueTapes5 v.far i) (queueTapes5 v'.far i)

/-- **The budget mismatch.** -/
def NAMED_queueBudget : Prop := 7 ≤ tView

theorem tView_lt_seven : tView < 7 := by decide

end PalPeg.CloseoutCoreEnc3

#print axioms PalPeg.CloseoutCoreEnc3.pos_shift1
#print axioms PalPeg.CloseoutCoreEnc3.toList_shift1
#print axioms PalPeg.CloseoutCoreEnc3.winRealizes_shift1
#print axioms PalPeg.CloseoutCoreEnc3.margin_encTapes1
#print axioms PalPeg.CloseoutCoreEnc3.named_margin'_encTapes1
#print axioms PalPeg.CloseoutCoreEnc3.winRealizes_of_agree
#print axioms PalPeg.CloseoutCoreEnc3.rd_stackTape_cons
#print axioms PalPeg.CloseoutCoreEnc3.pos_stackTape
#print axioms PalPeg.CloseoutCoreEnc3.cellSym_none
#print axioms PalPeg.CloseoutCoreEnc3.winRealizes_push
#print axioms PalPeg.CloseoutCoreEnc3.winRealizes_pop
#print axioms PalPeg.CloseoutCoreEnc3.stackTape_inj
#print axioms PalPeg.CloseoutCoreEnc3.not_injective_listTape1
#print axioms PalPeg.CloseoutCoreEnc3.mapTape_inj
#print axioms PalPeg.CloseoutCoreEnc3.shift1_inj
#print axioms PalPeg.CloseoutCoreEnc3.coreLocal_ofResidual
#print axioms PalPeg.CloseoutCoreEnc3.tView_lt_seven
