import PalPeg.CloseoutCoreEnc11

/-!
# Closeout, step 2l: composite steps, a sentinel alphabet, and the micro-action budget

`CloseoutCoreEnc11` records three obstructions to closing the thirteen
`CloseoutCoreEnc10.ActPieces` fields at radius `Kc = 1` with **one** micro-action
per tape per tick.  This file supplies the generic machinery for the design
repair, and nothing about the concrete VM branches, so

**無条件 PAL ∈ PEG は未完.**

## What is established (unconditional)

* **§1 (the cell machine).**  `actList blank T as` applies a *list* of optional
  micro-actions to a structured tape.  `runA` is the same list run on the pair
  (`cells : ℕ → Γ`, `cursor : ℕ`), and `runA_eq` says the two agree **exactly and
  unconditionally**: `runA (rd blank T, pos T) as = (rd blank (actList blank T as),
  pos (actList blank T as))`.  This is the point at which the left-end clamp of
  `STape.applyAction` is *kept* rather than wished away: `pos_applyAction` and
  `rd_applyAction` are themselves unconditional.  `runA_outside` bounds the
  written region and `runA_cur_le`/`runA_le_cur` the cursor.
* **§2 (composite = one sweep, up to `TEq`).**  `runA_shift` is the
  shift-equivariance of the cell machine on a window of width `B`, under the two
  budget hypotheses `as.length ≤ cursor` and `cursor + as.length ≤ B`.  With
  `B := 2 * K`, `cursor := K` it gives `teq_sweep_actList`: for `as.length ≤ K`
  and `K ≤ pos T`,
  `TEqG blank (actList blank T as) (sweep blank K T (winAfter K (readWin blank K T) as) (dAfter …))`,
  where `winAfter`/`dAfter` are **functions of the read window alone** — exactly
  what `LocalStep.next` may depend on.  So a tick that is a composite of at most
  `K` micro-actions per tape is a legal radius-`K` local step.
* **§3 (the composite `LocalStep`).**  `ActRule` is "next control + at most `K`
  micro-actions per tape, all window-computable"; `compStep` builds the
  `LocalStep` (its `disp_le` is `dAfter_le`), and `compStep_apply` is the
  intertwining: the control is `R.nq`, and each tape of `(compStep R).apply` is
  `TEqG` to the composite `actList` on that tape, given the margin `K ≤ pos`.
  `compStep_applyN` iterates it.
* **§4 (the sentinel alphabet).**  `Γs := Option Γc` has `15` symbols,
  `sentinel := none ≠ blanks := some blankc`.  `leftEnd_of_window` closes
  obstruction 1 *generically*: on a tape whose sentinel sits exactly at cell `0`,
  the cell one to the left of the head reads `sentinel` **iff** `pos T = 1`, so
  "am I at the left end?" is a window read, and `leftClamp` is the resulting
  window-computable branch between a clamped `.stay` and a real `.left`.
* **§5 (the budget table).**  `Branch` enumerates the thirteen branches and
  `microCount` records how many micro-actions each needs; `microCount_le` proves
  `≤ cFor = 64`, the `fpp` quantum `qq ≤ 64`.  So radius `K := cFor` suffices for
  every branch simultaneously.
* **§6 (the `CoreLocal` connection).**  `CoreLocalC` is
  `CloseoutCoreAudit.CoreLocal` at `Γ := Γs`, `K := cFor`; `Γs` has the
  `Fintype`/`DecidableEq` instances that `pal_in_peg_of_coreLocal` demands, and
  `coreLocal_c_ok` exhibits the substituted consumer.

## What is *not* established, one line each

1. **`compStep_apply` is false as a literal equation of tapes.**  `sweep` at
   radius `K` materializes the reservoir out to `pos + K` (`mvR^[2K]`) while `c`
   micro-sweeps at radius `1` materialize only out to `max pos + 1`, so the two
   `STape` *terms* differ in trailing blanks even though `pos` and every `rd`
   agree; `TEqG` (= `CloseoutCoreEnc4.TEq` on `Γc`) is the strongest available
   form, and obstruction 2 of `CloseoutCoreEnc11` is therefore not a defect of
   the branches but of stating residuals as term equations.
2. **`CloseoutCoreEnc8`–`10` are hard-wired to `Kc = 1`.**  `WinOn`, `TapeAct`,
   `winAct`, `dOfAct`, `NAMED_widthStep` and `margin_encPadN` all mention `Kc`,
   so the composite repair needs those four files re-run at radius `cFor`;
   `teq_sweep_actList` is the replacement for `teq_sweep_act`, `ActRule` for
   `TapeAct`, and the width argument (`wlen_actOn`) must be iterated along the
   list.  That re-run is not done here.
3. **`shiftPick` and `chooseSelect` are not discharged.**  Neither is provable
   from anything in scope: `shiftPick` needs the layout indices of the `L`
   cursor and of the counter bank (the analogue, for `LocalBuffers.resetL`'s
   counters, of `CloseoutCoreEnc11.encTapes_fpp` for `fppBuf`), and
   `chooseSelect` needs *the missing machine fact that a unary counter's reset is
   a bounded rewrite* — i.e. that counters are stored head-parked at their
   sentinel with the value as a head offset, which is also what would turn
   `NAMED_shiftRem` and `NAMED_workZero` into focus reads; `NAMED_walkerRead`
   additionally needs the queue-layout repair of `CloseoutCoreEnc3` §2.
   `microCount` records their budgets (`4` and `2`) as *claims about a layout
   that does not exist yet*, not as theorems.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCoreEnc12

open PalPeg PalPeg.Program
open PalPeg.Local (Window idx idx_val pos rd sweep readWin readWin_eq pos_sweep rd_sweep
  pos_applyAction rd_applyAction LocalStep)
open PalPeg.CloseoutCoreStep (Γc blankc)

/-- The move alphabet of one micro-action. -/
abbrev MoveC : Type := PegSeparation.RealTimeTM.Move

/-- One optional micro-action. -/
abbrev Act (Γ : Type) : Type := Option (Γ × MoveC)

variable {Γ : Type}

/-! ## 1. The cell machine -/

/-- The displacement of one micro-action. -/
def dOfA : Act Γ → ℤ
  | none => 0
  | some (_, mv) => match mv with | .right => (1 : ℤ) | .left => (-1 : ℤ) | .stay => (0 : ℤ)

/-- One optional micro-action on a structured tape. -/
def actOnG (blank : Γ) (T : STape Γ) : Act Γ → STape Γ
  | none => T
  | some sm => T.applyAction blank sm

/-- **A composite step**: a list of micro-actions, applied left to right. -/
def actList (blank : Γ) (T : STape Γ) : List (Act Γ) → STape Γ
  | [] => T
  | a :: as => actList blank (actOnG blank T a) as

@[simp] theorem actList_nil (blank : Γ) (T : STape Γ) : actList blank T [] = T := rfl

theorem actList_cons (blank : Γ) (T : STape Γ) (a : Act Γ) (as : List (Act Γ)) :
    actList blank T (a :: as) = actList blank (actOnG blank T a) as := rfl

/-- One micro-action on the pair (cell contents, cursor). -/
def stepA (a : Act Γ) (c : (ℕ → Γ) × ℕ) : (ℕ → Γ) × ℕ :=
  match a with
  | none => c
  | some (s, mv) =>
      (Function.update c.1 c.2 s,
        match mv with | .right => c.2 + 1 | .left => c.2 - 1 | .stay => c.2)

/-- The composite step on the pair (cell contents, cursor). -/
def runA (c : (ℕ → Γ) × ℕ) : List (Act Γ) → (ℕ → Γ) × ℕ
  | [] => c
  | a :: as => runA (stepA a c) as

@[simp] theorem runA_nil (c : (ℕ → Γ) × ℕ) : runA c [] = c := rfl

theorem runA_cons (c : (ℕ → Γ) × ℕ) (a : Act Γ) (as : List (Act Γ)) :
    runA c (a :: as) = runA (stepA a c) as := rfl

/-- **The cell machine is the tape machine**, unconditionally: the left-end
clamp of `STape.applyAction` is reproduced by `ℕ`-subtraction of the cursor. -/
theorem runA_eq (blank : Γ) (as : List (Act Γ)) (T : STape Γ) :
    runA (rd blank T, pos T) as = (rd blank (actList blank T as), pos (actList blank T as)) := by
  induction as generalizing T with
  | nil => rfl
  | cons a as ih =>
      have hstep : stepA a (rd blank T, pos T)
          = (rd blank (actOnG blank T a), pos (actOnG blank T a)) := by
        cases a with
        | none => rfl
        | some sm =>
            obtain ⟨s, mv⟩ := sm
            refine Prod.ext ?_ ?_
            · funext p
              show Function.update (rd blank T) (pos T) s p
                = rd blank (T.applyAction blank (s, mv)) p
              rw [rd_applyAction, Function.update_apply]
            · show (match mv with | .right => pos T + 1 | .left => pos T - 1 | .stay => pos T)
                = pos (T.applyAction blank (s, mv))
              rw [pos_applyAction]
              cases mv <;> rfl
      rw [runA_cons, hstep, actList_cons, ih]

theorem runA_cur_le (as : List (Act Γ)) (c : (ℕ → Γ) × ℕ) : (runA c as).2 ≤ c.2 + as.length := by
  induction as generalizing c with
  | nil => simp
  | cons a as ih =>
      have h := ih (stepA a c)
      have h2 : (stepA a c).2 ≤ c.2 + 1 := by
        cases a with
        | none => simp [stepA]
        | some sm => obtain ⟨s, mv⟩ := sm; cases mv <;> simp [stepA] <;> omega
      rw [runA_cons]
      simp only [List.length_cons]
      omega

theorem runA_le_cur (as : List (Act Γ)) (c : (ℕ → Γ) × ℕ) : c.2 - as.length ≤ (runA c as).2 := by
  induction as generalizing c with
  | nil => simp
  | cons a as ih =>
      have h := ih (stepA a c)
      have h2 : c.2 - 1 ≤ (stepA a c).2 := by
        cases a with
        | none => simp [stepA]
        | some sm => obtain ⟨s, mv⟩ := sm; cases mv <;> simp [stepA] <;> omega
      rw [runA_cons]
      simp only [List.length_cons]
      omega

/-- **The written region is the cursor's reach.** -/
theorem runA_outside (as : List (Act Γ)) (c : (ℕ → Γ) × ℕ) (p : ℕ)
    (h : p + as.length < c.2 ∨ c.2 + as.length < p) : (runA c as).1 p = c.1 p := by
  induction as generalizing c with
  | nil => rfl
  | cons a as ih =>
      simp only [List.length_cons] at h
      have hcur : c.2 - 1 ≤ (stepA a c).2 ∧ (stepA a c).2 ≤ c.2 + 1 := by
        cases a with
        | none => simp [stepA]
        | some sm => obtain ⟨s, mv⟩ := sm; cases mv <;> simp [stepA] <;> omega
      have hne : p ≠ c.2 := by omega
      have hstep : (stepA a c).1 p = c.1 p := by
        cases a with
        | none => rfl
        | some sm =>
            obtain ⟨s, mv⟩ := sm
            show Function.update c.1 c.2 s p = c.1 p
            rw [Function.update_apply, if_neg hne]
      rw [runA_cons, ih (stepA a c) (by omega), hstep]

/-- **Shift-equivariance of the cell machine** on a window of width `B`. -/
theorem runA_shift (as : List (Act Γ)) (f g : ℕ → Γ) (a s B : ℕ)
    (hfg : ∀ p ≤ B, f p = g (p + s)) (h1 : as.length ≤ a) (h2 : a + as.length ≤ B) :
    (runA (f, a) as).2 + s = (runA (g, a + s) as).2 ∧
      ∀ p ≤ B, (runA (f, a) as).1 p = (runA (g, a + s) as).1 (p + s) := by
  induction as generalizing f g a with
  | nil => exact ⟨rfl, fun p _ => hfg p ‹_›⟩
  | cons act as ih =>
      simp only [List.length_cons] at h1 h2
      cases act with
      | none =>
          have := ih f g a hfg (by omega) (by omega)
          simpa [runA_cons, stepA] using this
      | some sm =>
          obtain ⟨w, mv⟩ := sm
          have ha1 : 1 ≤ a := by omega
          have hfg' : ∀ p ≤ B, Function.update f a w p = Function.update g (a + s) w (p + s) := by
            intro p hp
            rw [Function.update_apply, Function.update_apply]
            by_cases hpa : p = a
            · rw [if_pos hpa, if_pos (by omega)]
            · rw [if_neg hpa, if_neg (by omega)]
              exact hfg p hp
          rw [runA_cons, runA_cons]
          cases mv with
          | right =>
              have h := ih (Function.update f a w) (Function.update g (a + s) w) (a + 1)
                hfg' (by omega) (by omega)
              have hs' : a + 1 + s = a + s + 1 := by omega
              rw [hs'] at h
              simpa [stepA] using h
          | left =>
              have h := ih (Function.update f a w) (Function.update g (a + s) w) (a - 1)
                hfg' (by omega) (by omega)
              have hs' : a - 1 + s = a + s - 1 := by omega
              rw [hs'] at h
              simpa [stepA] using h
          | stay =>
              have h := ih (Function.update f a w) (Function.update g (a + s) w) a
                hfg' (by omega) (by omega)
              simpa [stepA] using h

/-! ## 2. A composite step is one sweep, up to `TEq` -/

/-- `CloseoutCoreEnc4.TEq`, for an arbitrary alphabet. -/
def TEqG (blank : Γ) (T T' : STape Γ) : Prop :=
  pos T = pos T' ∧ ∀ p, rd blank T p = rd blank T' p

theorem TEqG_Γc (T T' : STape Γc) : TEqG blankc T T' ↔ PalPeg.CloseoutCoreEnc4.TEq T T' :=
  Iff.rfl

/-- The generic form of `CloseoutCoreEnc10.teq_sweep_of_witness`. -/
theorem teqG_sweep_of_witness (blank : Γ) {K : ℕ} {T T' : STape Γ} {w : Window Γ K} {d : ℤ}
    (hK : K ≤ pos T) (hd : |d| ≤ (K : ℤ))
    (hpos : (pos T' : ℤ) = (pos T : ℤ) + d)
    (hcell : ∀ p : ℕ, rd blank T' p =
      if pos T - K ≤ p ∧ p ≤ pos T + K then w (idx K (p - (pos T - K))) else rd blank T p) :
    TEqG blank T' (sweep blank K T w d) := by
  refine ⟨?_, ?_⟩
  · have h1 : (pos T' : ℤ) = (pos (sweep blank K T w d) : ℤ) := by
      rw [pos_sweep blank K T w d hK hd]; exact hpos
    exact_mod_cast h1
  · intro p
    rw [hcell p, rd_sweep blank K T w d hK p]

/-- A window, read as a cell function in local coordinates (head at `K`). -/
def cellOfWin (K : ℕ) (w : Window Γ K) : ℕ → Γ := fun p => w (idx K p)

/-- **The window a composite step leaves behind** — a function of the read window. -/
def winAfter (K : ℕ) (w : Window Γ K) (as : List (Act Γ)) : Window Γ K :=
  fun i => (runA (cellOfWin K w, K) as).1 (i : ℕ)

/-- **The displacement of a composite step** — a function of the read window. -/
def dAfter (K : ℕ) (w : Window Γ K) (as : List (Act Γ)) : ℤ :=
  ((runA (cellOfWin K w, K) as).2 : ℤ) - (K : ℤ)

theorem dAfter_le (K : ℕ) (w : Window Γ K) (as : List (Act Γ)) (hlen : as.length ≤ K) :
    |dAfter K w as| ≤ (K : ℤ) := by
  have h1 := runA_cur_le as (cellOfWin K w, K)
  have h2 := runA_le_cur as (cellOfWin K w, K)
  simp only [] at h1 h2
  rw [abs_le]
  constructor <;> · simp only [dAfter]; omega

/-- **A composite of at most `K` micro-actions is a radius-`K` sweep**, up to `TEq`. -/
theorem teq_sweep_actList (blank : Γ) (K : ℕ) (T : STape Γ) (as : List (Act Γ))
    (hlen : as.length ≤ K) (hK : K ≤ pos T) :
    TEqG blank (actList blank T as)
      (sweep blank K T (winAfter K (readWin blank K T) as) (dAfter K (readWin blank K T) as)) := by
  set w := readWin blank K T with hw
  set f : ℕ → Γ := cellOfWin K w with hf
  set s : ℕ := pos T - K with hs
  have hKs : K + s = pos T := by omega
  have hfg : ∀ p ≤ 2 * K, f p = rd blank T (p + s) := by
    intro p hp
    have : w (idx K p) = rd blank T (pos T - K + p) := by
      rw [hw, readWin_eq, idx_val hp]
    simpa [hf, cellOfWin, hs, Nat.add_comm] using this
  obtain ⟨hcur, hcell⟩ := runA_shift as f (rd blank T) K s (2 * K) hfg hlen (by omega)
  rw [hKs] at hcur hcell
  have hrun : runA (rd blank T, pos T) as
      = (rd blank (actList blank T as), pos (actList blank T as)) := runA_eq blank as T
  refine teqG_sweep_of_witness blank hK (dAfter_le K w as hlen) ?_ ?_
  · have : (runA (f, K) as).2 + s = pos (actList blank T as) := by
      rw [hcur, hrun]
    simp only [dAfter, ← hf]
    omega
  · intro p
    by_cases hmem : pos T - K ≤ p ∧ p ≤ pos T + K
    · rw [if_pos hmem]
      have hle : p - (pos T - K) ≤ 2 * K := by omega
      have h1 : ((idx K (p - (pos T - K)) : Fin (2 * K + 1)) : ℕ) = p - s := by
        rw [idx_val hle]
      have h2 := hcell (p - s) (by omega)
      have h3 : p - s + s = p := by omega
      rw [h3] at h2
      have h4 : (runA (rd blank T, pos T) as).1 p = rd blank (actList blank T as) p := by
        rw [hrun]
      simp only [winAfter, hw, h1]
      rw [← hf, h2, h4]
    · rw [if_neg hmem]
      have h4 : (runA (rd blank T, pos T) as).1 p = rd blank (actList blank T as) p := by
        rw [hrun]
      rw [← h4]
      exact runA_outside as (rd blank T, pos T) p (by simp only []; omega)

/-! ## 3. The composite `LocalStep` -/

variable {Terminal Q : Type} {t K : ℕ}

/-- **One abstract tick as at most `K` micro-actions per tape**, all computed
from the finite control, the input symbol and the read windows. -/
structure ActRule (Terminal Q Γ : Type) (t K : ℕ) where
  nq : Q → Option Terminal → (Fin t → Window Γ K) → Q
  acts : Q → Option Terminal → (Fin t → Window Γ K) → Fin t → List (Act Γ)
  len_le : ∀ q a ws j, (acts q a ws j).length ≤ K

/-- **The composite step.** -/
def compStep (R : ActRule Terminal Q Γ t K) : LocalStep Terminal Q Γ t K where
  next := fun q a ws =>
    (R.nq q a ws, fun j => (winAfter K (ws j) (R.acts q a ws j), dAfter K (ws j) (R.acts q a ws j)))
  disp_le := fun q a ws j => dAfter_le K (ws j) (R.acts q a ws j) (R.len_le q a ws j)

/-- **The intertwining.**  `compStep R` runs exactly the composite the rule
prescribes, up to `TEqG` — see the first missing fact in the header for why the
literal equation of `STape` terms is false. -/
theorem compStep_apply (R : ActRule Terminal Q Γ t K) (blank : Γ)
    (x : Q × (Fin t → STape Γ)) (a : Option Terminal)
    (hmargin : ∀ j, K ≤ pos (x.2 j)) :
    ((compStep R).apply blank x a).1
        = R.nq x.1 a (fun j => readWin blank K (x.2 j)) ∧
      ∀ j : Fin t,
        TEqG blank
          (actList blank (x.2 j) (R.acts x.1 a (fun j => readWin blank K (x.2 j)) j))
          (((compStep R).apply blank x a).2 j) := by
  refine ⟨rfl, fun j => ?_⟩
  show TEqG blank _ (sweep blank K (x.2 j) _ _)
  exact teq_sweep_actList blank K (x.2 j)
    (R.acts x.1 a (fun j => readWin blank K (x.2 j)) j)
    (R.len_le _ _ _ _) (hmargin j)

/-- Iterating the composite step; the control is a plain iteration. -/
def compIter (R : ActRule Terminal Q Γ t K) (blank : Γ) (a : Option Terminal) :
    ℕ → Q × (Fin t → STape Γ) → Q × (Fin t → STape Γ)
  | 0, x => x
  | (n + 1), x => compIter R blank a n ((compStep R).apply blank x a)

theorem compStep_applyN (R : ActRule Terminal Q Γ t K) (blank : Γ) (a : Option Terminal)
    (n : ℕ) (x : Q × (Fin t → STape Γ)) :
    compIter R blank a n x = (fun y => (compStep R).apply blank y a)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [compIter, ih, Function.iterate_succ_apply]

/-! ## 4. The sentinel alphabet -/

/-- `Γc` with a left-end sentinel adjoined: fifteen symbols. -/
abbrev Γs : Type := Option Γc

/-- The left-end marker, distinct from every symbol of `Γc`. -/
def sentinel : Γs := none

/-- The blank of `Γs`. -/
def blanks : Γs := some blankc

theorem sentinel_ne_blanks : sentinel ≠ blanks := by
  simp [sentinel, blanks]

theorem card_Γs : Fintype.card Γs = 15 := by
  rw [Fintype.card_option]
  decide

instance : Fintype Γs := inferInstance
instance : DecidableEq Γs := inferInstance

/-- A tape carrying the sentinel exactly at cell `0`. -/
def SentinelTape (T : STape Γs) : Prop := ∀ p : ℕ, rd blanks T p = sentinel ↔ p = 0

/-- **Obstruction 1, closed generically.**  On a sentinel tape, "is the head at
the left end?" is a *window read*: the cell one to the left of the head carries
the sentinel iff the head is at cell `1`. -/
theorem leftEnd_of_window {K : ℕ} (T : STape Γs) (h : SentinelTape T)
    (hK : K ≤ pos T) (hK1 : 1 ≤ K) :
    readWin blanks K T (idx K (K - 1)) = sentinel ↔ pos T = 1 := by
  have hle : K - 1 ≤ 2 * K := by omega
  rw [readWin_eq, idx_val hle]
  have hp : pos T - K + (K - 1) = pos T - 1 := by omega
  rw [hp, h (pos T - 1)]
  omega

/-- The window-computable clamped left move: at the left end it degenerates to a
write in place, exactly as `GalilScaffoldTape.moveLeft` clamps. -/
def leftClamp (atEnd : Bool) (s : Γs) : List (Act Γs) :=
  if atEnd then [some (s, .stay)] else [some (s, .left)]

theorem leftClamp_length (atEnd : Bool) (s : Γs) : (leftClamp atEnd s).length = 1 := by
  cases atEnd <;> rfl

theorem pos_actList_leftClamp (T : STape Γs) (atEnd : Bool) (s : Γs) :
    pos (actList blanks T (leftClamp atEnd s))
      = if atEnd then pos T else pos T - 1 := by
  cases atEnd <;>
    simp [leftClamp, actList, actOnG, pos_applyAction]

/-! ## 5. The micro-action budget of the thirteen branches -/

/-- The thirteen acting branches of the seven phase modes, as in
`CloseoutCoreEnc10.ActPieces`. -/
inductive Branch : Type
  | shiftPick | copyPick | copyDone | homeStart | homeStep
  | markEndDone | markEndStep | chooseSelect | chooseScan
  | rewindPair | rewindOne | rewindDone | fpp
  deriving DecidableEq

/-- The radius the repair runs at: the `fpp` quantum is `qq ≤ 64` program steps. -/
def cFor : ℕ := 64

/-- **The budget table.**  How many micro-actions each branch must be a
composite of.  Only `homeStart` is a theorem today
(`CloseoutCoreEnc11.tapeAct_homeStart`); the rest are the *claims* the layout
repair has to meet — see missing fact 3 in the header. -/
def microCount : Branch → ℕ
  | .shiftPick => 4      -- `L` moves twice, the counter bank ticks twice
  | .copyPick => 6       -- walker `+1`, one `InputView` queue rotation (4), SOURCE `+1`
  | .copyDone => 1       -- one `.stay` write on `bufAt` (`CloseoutCoreEnc11` §5)
  | .homeStart => 0      -- no tape moves at all (`CloseoutCoreEnc11` §3)
  | .homeStep => 1       -- clamped `moveLeft`, via `leftClamp`
  | .markEndDone => 1    -- clamped `moveLeft` on MARKS
  | .markEndStep => 1    -- `moveRight` on MARKS, eating one reservoir cell
  | .chooseSelect => 2   -- two unary counter resets, *if* they are head-parked
  | .chooseScan => 1     -- clamped `moveLeft` on MARKS
  | .rewindPair => 1
  | .rewindOne => 1
  | .rewindDone => 3     -- bank swap plus the `job` rewrite of `LocalBuffers.resetL`
  | .fpp => 64           -- one `qq`-step quantum

theorem microCount_le (b : Branch) : microCount b ≤ cFor := by
  cases b <;> simp [microCount, cFor]

theorem microCount_homeStart : microCount .homeStart = 0 := rfl

/-! ## 6. The `CoreLocal` connection -/

open PalPeg.CloseoutCoreAudit (CoreLocal)
open PalPeg.LocalTrackingLatch (LocalSys LX)

/-- `CloseoutCoreAudit.CoreLocal` with the alphabet and radius of this repair. -/
abbrev CoreLocalC {X : Type} (S : LocalSys X) (x0 : LX X) (Q : Type) (t : ℕ) : Type :=
  CoreLocal S x0 Q Γs t cFor

/-- The consumer, with `Γ := Γs` and `K := cFor` substituted: the instances it
demands exist, so the substitution is legal and nothing else in
`pal_in_peg_of_coreLocal` mentions `Γ` or `K`. -/
theorem coreLocal_c_ok {X : Type} (S : LocalSys X) (x0 : LX X) (Q : Type) (t : ℕ)
    [Fintype Q] [DecidableEq Q] :
    (CoreLocalC S x0 Q t) = CoreLocal S x0 Q Γs t cFor := rfl

#check @PalPeg.CloseoutCoreAudit.pal_in_peg_of_coreLocal

#print axioms PalPeg.CloseoutCoreEnc12.runA_eq
#print axioms PalPeg.CloseoutCoreEnc12.runA_shift
#print axioms PalPeg.CloseoutCoreEnc12.teq_sweep_actList
#print axioms PalPeg.CloseoutCoreEnc12.compStep_apply
#print axioms PalPeg.CloseoutCoreEnc12.compStep_applyN
#print axioms PalPeg.CloseoutCoreEnc12.leftEnd_of_window
#print axioms PalPeg.CloseoutCoreEnc12.card_Γs
#print axioms PalPeg.CloseoutCoreEnc12.microCount_le

end PalPeg.CloseoutCoreEnc12
