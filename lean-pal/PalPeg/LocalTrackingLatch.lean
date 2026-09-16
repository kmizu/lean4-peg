import PalPeg.LocalTracking
import PalPeg.LocalStepRealize
import PalPeg.GalilLatchTracking
import PalPeg.GalilArriveChain
import PalPeg.GalilThrottledRunGen
import PalPeg.GalilEmptyWord
import PalPeg.LocalReplayParked

/-!
# The local tracking skeleton, restated for latched, throttled semantics

`LocalTracking.tracking_of_oracles` used `nLocal = 2·2048`, read the answer off
the *current* controller state and did not throttle. Here:

1. `nLocalL := GalilLedgerThrottled.ticksPerSymbol = 2^18` local steps per letter.
2. The local state `LX X` carries a **latch** `ans : Bool` (reset on arrival, set
   at a local tick whose post-state passes the local report test `repL`, to the
   local output `outL`) and a `started` bit (set on arrival; it is what makes
   `accept' := ans ∨ q = initQ` inert on nonempty words, no mode argument needed).
3. Local ticks **stutter** exactly when the local core is `Starved` (the right
   view has no `far`/`near` material for the next abstract tick).
4. Micro-step `s` of the realized machine feeds letter `j` iff `s = j·τ`; that
   micro-step does the arrival only. So the local run abstracts, index by index,
   to an `AbstractRun'` (`abstractRun_of_oracles`) with arrival counter
   `arrL w s = min |w| ⌈s/τ⌉`. No index matching with `stTG` is required: the
   ledger has to be discharged for the run `stAbs` the local run abstracts to.
5. **Deadline slot.** Letter `j` (0-based) arrives at `j·τ`, one slot earlier
   than the Lindley recursion `GalilLindley.S` assumes. `run_on_time_shift`
   proves the shifted recursion finishes checkpoint `m` by `m·τ` (not
   `(m+1)·τ`), so the deadline is `T w := |w|·τ`, exactly the number of
   micro-steps the structured machine has (`reported_of_shift`).

`tracking_latch_of_oracles` : `M.SAccepts w ↔ LatchTrue … (stAbs w) (|w|·τ)`.
`pal_in_peg_of_local_latch` : composes with `GalilArriveChain.pal_in_peg_of_latch'`.

**Unconditional PAL ∈ PEG is not finished**: the oracles below are open.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PalPeg.LocalTrackingLatch

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.Local (LocalStep)

/-! ## 1. Constants -/

/-- Local steps per letter. -/
def nLocalL : ℕ := GalilLedgerThrottled.ticksPerSymbol

theorem nLocalL_eq : nLocalL = 262144 := by
  unfold nLocalL GalilLedgerThrottled.ticksPerSymbol; norm_num

theorem nLocalL_pos : 0 < nLocalL := by rw [nLocalL_eq]; norm_num

/-! ## 2. Latched local state -/

/-- Local state: the core `X` (e.g. `GalilVML Np`), the latch, the started bit. -/
structure LX (X : Type) where
  core : X
  ans : Bool
  started : Bool

/-- The core local dynamics the latch layer is built on. -/
structure LocalSys (X : Type) where
  /-- one local tick of the core (may stutter) -/
  tickL : X → X
  /-- arrival of a letter on the core -/
  feedC : Fin 2 → X → X
  /-- the local report test: right head at `2·arrived−1`, not replaying,
  refresh just happened -/
  repL : X → Bool
  /-- the local output bit -/
  outL : X → Bool
  /-- the local starvation test: the next abstract tick needs an unarrived letter -/
  Starved : X → Prop

variable {X : Type}

/-- A non-arrival local step: tick the core, then latch. -/
def latchStep (S : LocalSys X) (x : LX X) : LX X :=
  ⟨S.tickL x.core, x.ans || (S.repL (S.tickL x.core) && S.outL (S.tickL x.core)), x.started⟩

/-- An arrival local step: feed the core, reset the latch, mark started. -/
def arriveL (S : LocalSys X) (a : Fin 2) (x : LX X) : LX X := ⟨S.feedC a x.core, false, true⟩

/-- One local step, as seen by `LocalStep.apply`. -/
def stepL (S : LocalSys X) : Option (Fin 2) → LX X → LX X
  | none, x => latchStep S x
  | some a, x => arriveL S a x

/-- Abstraction of a latched local state: the latch is invisible. -/
def absL (absS : X → State GalilVM) (x : LX X) : State GalilVM := absS x.core

@[simp] theorem latchStep_abs (S : LocalSys X) (absS : X → State GalilVM) (x : LX X) :
    absL absS (latchStep S x) = absS (S.tickL x.core) := rfl

@[simp] theorem arriveL_abs (S : LocalSys X) (absS : X → State GalilVM) (a : Fin 2) (x : LX X) :
    absL absS (arriveL S a x) = absS (S.feedC a x.core) := rfl

/-- One letter's block: arrival, then `τ − 1` latch steps. -/
def blockL (S : LocalSys X) (x : LX X) (a : Fin 2) : LX X :=
  (stepL S none)^[nLocalL - 1] (stepL S (some a) x)

/-! ## 3. The micro-indexed local run -/

/-- The input slot of micro-step `s`: letter `j` at `s = j·τ`. -/
def inp (w : List (Fin 2)) (s : ℕ) : Option (Fin 2) :=
  if s % nLocalL = 0 then w[s / nLocalL]? else none

/-- The local state after `s` micro-steps. -/
def micro (S : LocalSys X) (w : List (Fin 2)) (x0 : LX X) : ℕ → LX X
  | 0 => x0
  | s+1 => stepL S (inp w s) (micro S w x0 s)

/-- The abstract run the local run abstracts to. -/
def stAbs (S : LocalSys X) (absS : X → State GalilVM) (w : List (Fin 2)) (x0 : LX X)
    (s : ℕ) : State GalilVM :=
  absL absS (micro S w x0 s)

/-- Letters arrived after `s` micro-steps. -/
def arrL (w : List (Fin 2)) (s : ℕ) : ℕ := min w.length ((s + nLocalL - 1) / nLocalL)

theorem inp_at (w : List (Fin 2)) (j : ℕ) (hj : j < w.length) :
    inp w (j * nLocalL) = some w[j] := by
  unfold inp
  rw [nLocalL_eq]
  have h1 : j * 262144 % 262144 = 0 := by omega
  have h2 : j * 262144 / 262144 = j := by omega
  rw [if_pos h1, h2, List.getElem?_eq_getElem hj]

theorem inp_mid (w : List (Fin 2)) (j i : ℕ) (hi : i + 1 < nLocalL) :
    inp w (j * nLocalL + 1 + i) = none := by
  unfold inp
  rw [nLocalL_eq] at hi ⊢
  have h1 : ¬ (j * 262144 + 1 + i) % 262144 = 0 := by omega
  rw [if_neg h1]

theorem inp_late (w : List (Fin 2)) (s : ℕ) (hs : (w.length - 1) * nLocalL < s) :
    inp w s = none := by
  unfold inp
  rw [nLocalL_eq] at hs ⊢
  split_ifs with h
  · rw [List.getElem?_eq_none_iff]; omega
  · rfl

theorem inp_some (w : List (Fin 2)) (s : ℕ) (a : Fin 2) (h : inp w s = some a) :
    s % nLocalL = 0 ∧ s / nLocalL < w.length ∧ w[s / nLocalL]? = some a := by
  unfold inp at h
  split_ifs at h with h1
  · refine ⟨h1, ?_, h⟩
    by_contra hc
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at h
    cases h

theorem micro_mid (S : LocalSys X) (w : List (Fin 2)) (x0 : LX X) (j : ℕ) :
    ∀ i, i ≤ nLocalL - 1 →
      micro S w x0 (j * nLocalL + 1 + i) = (stepL S none)^[i] (micro S w x0 (j * nLocalL + 1)) := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
      intro hi
      have hlt : i + 1 < nLocalL := by have := nLocalL_pos; omega
      show stepL S (inp w (j * nLocalL + 1 + i)) (micro S w x0 (j * nLocalL + 1 + i)) = _
      rw [inp_mid w j i hlt, ih (by omega), Function.iterate_succ_apply']

theorem micro_block (S : LocalSys X) (w : List (Fin 2)) (x0 : LX X) (j : ℕ) (hj : j < w.length) :
    micro S w x0 ((j+1) * nLocalL) = blockL S (micro S w x0 (j * nLocalL)) w[j] := by
  have he : (j+1) * nLocalL = j * nLocalL + 1 + (nLocalL - 1) := by
    have := nLocalL_pos; rw [Nat.succ_mul]; omega
  rw [he, micro_mid S w x0 j (nLocalL - 1) le_rfl]
  show (stepL S none)^[nLocalL - 1]
      (stepL S (inp w (j * nLocalL)) (micro S w x0 (j * nLocalL))) = _
  rw [inp_at w j hj, blockL]

theorem micro_take (S : LocalSys X) (w : List (Fin 2)) (x0 : LX X) :
    ∀ j, j ≤ w.length → micro S w x0 (j * nLocalL) = (w.take j).foldl (blockL S) x0 := by
  intro j
  induction j with
  | zero => intro _; simp [micro]
  | succ j ih =>
      intro hj
      rw [micro_block S w x0 j (by omega), ih (by omega), List.take_add_one,
        List.getElem?_eq_getElem (by omega), Option.toList_some, List.foldl_append,
        List.foldl_cons, List.foldl_nil]

theorem micro_end (S : LocalSys X) (w : List (Fin 2)) (x0 : LX X) :
    micro S w x0 (w.length * nLocalL) = w.foldl (blockL S) x0 := by
  rw [micro_take S w x0 w.length le_rfl, List.take_length]

/-! ## 4. The started bit makes `accept'` inert on nonempty words -/

theorem started_iter (S : LocalSys X) :
    ∀ (m : ℕ) (x : LX X), ((stepL S none)^[m] x).started = x.started := by
  intro m
  induction m with
  | zero => intro x; rfl
  | succ m ih => intro x; rw [Function.iterate_succ_apply', ← ih x]; rfl

theorem started_block (S : LocalSys X) (x : LX X) (a : Fin 2) : (blockL S x a).started = true := by
  rw [blockL, started_iter]
  simp only [stepL, arriveL]

theorem started_foldl (S : LocalSys X) :
    ∀ (w : List (Fin 2)) (x : LX X), 0 < w.length → (w.foldl (blockL S) x).started = true := by
  intro w
  induction w with
  | nil => intro _ h; simp at h
  | cons a rest ih =>
      intro x _
      rw [List.foldl_cons]
      rcases rest with _ | ⟨b, rest'⟩
      · rw [List.foldl_nil]; exact started_block S x a
      · exact ih (blockL S x a) (by simp)

/-! ## 5. The encoding fold -/

section Enc

variable {t K : ℕ} {Q' Γ' : Type}

theorem applyN_encL (L : LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (S : LocalSys X)
    (enc : LX X → Q' × (Fin t → STape Γ'))
    (hsim : ∀ (x : LX X) (a : Option (Fin 2)), L.apply blank (enc x) a = enc (stepL S a x))
    (x : LX X) (a : Fin 2) :
    L.applyN blank nLocalL (enc x) a = enc (blockL S x a) := by
  have hsc : Function.Semiconj enc (stepL S none) (fun y => L.apply blank y none) :=
    fun y => (hsim y none).symm
  unfold LocalStep.applyN blockL
  rw [hsim x (some a), (hsc.iterate_right (nLocalL - 1)) (stepL S (some a) x)]

theorem foldl_encL (L : LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (S : LocalSys X)
    (enc : LX X → Q' × (Fin t → STape Γ'))
    (hsim : ∀ (x : LX X) (a : Option (Fin 2)), L.apply blank (enc x) a = enc (stepL S a x)) :
    ∀ (w : List (Fin 2)) (x : LX X),
      w.foldl (L.applyN blank nLocalL) (enc x) = enc (w.foldl (blockL S) x) := by
  intro w
  induction w with
  | nil => intro x; rfl
  | cons a rest ih =>
      intro x
      rw [List.foldl_cons, applyN_encL L blank S enc hsim x a, ih, List.foldl_cons]

end Enc

/-! ## 6. The latch along the run -/

/-- After the last arrival the latch is exactly "some later local step passed
the report test with output `true`". -/
theorem latch_ans (S : LocalSys X) (w : List (Fin 2)) (x0 : LX X) (hw : 0 < w.length) :
    ∀ d, (micro S w x0 ((w.length - 1) * nLocalL + 1 + d)).ans = true ↔
      ∃ s, (w.length - 1) * nLocalL + 1 < s ∧ s ≤ (w.length - 1) * nLocalL + 1 + d ∧
        S.repL (micro S w x0 s).core = true ∧ S.outL (micro S w x0 s).core = true := by
  intro d
  induction d with
  | zero =>
      have h : micro S w x0 ((w.length - 1) * nLocalL + 1 + 0)
          = stepL S (inp w ((w.length - 1) * nLocalL)) (micro S w x0 ((w.length - 1) * nLocalL)) :=
        rfl
      rw [h, inp_at w (w.length - 1) (by omega)]
      constructor
      · intro hc; exact absurd hc (by simp [stepL, arriveL])
      · rintro ⟨s, h1, h2, -⟩; omega
  | succ d ih =>
      have hlate := inp_late w ((w.length - 1) * nLocalL + 1 + d) (by omega)
      have h : micro S w x0 ((w.length - 1) * nLocalL + 1 + (d+1))
          = latchStep S (micro S w x0 ((w.length - 1) * nLocalL + 1 + d)) := by
        show stepL S (inp w ((w.length - 1) * nLocalL + 1 + d)) _ = _
        rw [hlate]; rfl
      have hcore : ∀ y : LX X, (latchStep S y).core = S.tickL y.core := fun _ => rfl
      rw [h]
      simp only [latchStep, Bool.or_eq_true, Bool.and_eq_true]
      rw [ih]
      constructor
      · rintro (⟨s, h1, h2, h3⟩ | ⟨h3, h4⟩)
        · exact ⟨s, h1, by omega, h3⟩
        · refine ⟨(w.length - 1) * nLocalL + 1 + (d+1), by omega, le_rfl, ?_⟩
          rw [h]; exact ⟨h3, h4⟩
      · rintro ⟨s, h1, h2, h3⟩
        by_cases hs : s ≤ (w.length - 1) * nLocalL + 1 + d
        · exact Or.inl ⟨s, h1, hs, h3⟩
        · have hse : s = (w.length - 1) * nLocalL + 1 + (d+1) := by omega
          rw [hse, h] at h3
          exact Or.inr h3

/-! ## 7. The abstract run with arrivals -/

theorem inv_micro (S : LocalSys X) (w : List (Fin 2)) (x0 : LX X) (Inv : X → Prop)
    (h0 : Inv x0.core) (ht : ∀ x, Inv x → Inv (S.tickL x))
    (hf : ∀ a x, Inv x → Inv (S.feedC a x)) :
    ∀ s, Inv (micro S w x0 s).core := by
  intro s
  induction s with
  | zero => exact h0
  | succ s ih =>
      show Inv (stepL S (inp w s) (micro S w x0 s)).core
      cases inp w s with
      | none => exact ht _ ih
      | some a => exact hf a _ ih

theorem arrL_none (w : List (Fin 2)) (s : ℕ) (h : inp w s = none) : arrL w (s+1) = arrL w s := by
  unfold inp at h
  unfold arrL
  rw [nLocalL_eq] at h ⊢
  split_ifs at h with h1
  · have := List.getElem?_eq_none_iff.mp h
    omega
  · omega

theorem arrL_some (w : List (Fin 2)) (s : ℕ) (a : Fin 2) (h : inp w s = some a) :
    arrL w (s+1) = arrL w s + 1 ∧ w[arrL w s]? = some a := by
  obtain ⟨h1, h2, h3⟩ := inp_some w s a h
  have he : arrL w s = s / nLocalL := by
    unfold arrL; rw [nLocalL_eq] at h1 h2 ⊢; omega
  refine ⟨?_, by rw [he]; exact h3⟩
  unfold arrL; rw [nLocalL_eq] at h1 h2 ⊢; unfold arrL at he; rw [nLocalL_eq] at he; omega

/-- Stutter correctness gives the `Tick ∨ stutter` disjunct of a local tick. -/
theorem tick_or_stutter (S : LocalSys X) (absS : X → State GalilVM) (Inv : X → Prop)
    (Pw : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (stutter_of_starved : ∀ x, Inv x → S.Starved x → absS (S.tickL x) = absS x)
    (tick_of_not_starved : ∀ x, Inv x → ¬ S.Starved x →
      Tick (galilFrameS Pw q first) delay (absS x) (absS (S.tickL x)))
    (x : X) (hx : Inv x) :
    Tick (galilFrameS Pw q first) delay (absS x) (absS (S.tickL x)) ∨
      absS (S.tickL x) = absS x := by
  by_cases h : S.Starved x
  · exact Or.inr (stutter_of_starved x hx h)
  · exact Or.inl (tick_of_not_starved x hx h)

/-- **The local run abstracts to an `AbstractRun'`.** -/
theorem abstractRun_of_oracles (S : LocalSys X) (absS : X → State GalilVM) (Inv : X → Prop)
    (Pw : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (w : List (Fin 2)) (x0 : LX X)
    (x0_inv : Inv x0.core)
    (x0_ctl : (absS x0.core).ctl = GalilScaffoldController.initial delay)
    (inv_tick : ∀ x, Inv x → Inv (S.tickL x))
    (inv_feed : ∀ a x, Inv x → Inv (S.feedC a x))
    (stutter_of_starved : ∀ x, Inv x → S.Starved x → absS (S.tickL x) = absS x)
    (tick_of_not_starved : ∀ x, Inv x → ¬ S.Starved x →
      Tick (galilFrameS Pw q first) delay (absS x) (absS (S.tickL x)))
    (feed_abs : ∀ a x, Inv x → absS (S.feedC a x) = arriveState' a (absS x)) :
    AbstractRun' Pw q first delay w (stAbs S absS w x0) (arrL w) := by
  refine ⟨x0_ctl, by unfold arrL; rw [nLocalL_eq]; omega, fun s => ?_⟩
  have hinv := inv_micro S w x0 Inv x0_inv inv_tick inv_feed s
  have hm : micro S w x0 (s+1) = stepL S (inp w s) (micro S w x0 s) := rfl
  cases hi : inp w s with
  | none =>
      refine Or.inl ⟨arrL_none w s hi, ?_⟩
      show Tick _ _ (absL absS (micro S w x0 s)) (absL absS (micro S w x0 (s+1))) ∨
        absL absS (micro S w x0 (s+1)) = absL absS (micro S w x0 s)
      rw [hm, hi]
      exact tick_or_stutter S absS Inv Pw q first delay stutter_of_starved tick_of_not_starved _ hinv
  | some a =>
      obtain ⟨h1, h2⟩ := arrL_some w s a hi
      refine Or.inr ⟨h1, a, h2, ?_⟩
      show absL absS (micro S w x0 (s+1)) = arriveState' a (absL absS (micro S w x0 s))
      rw [hm, hi]
      exact feed_abs a _ hinv

/-- **Stutter correctness, run form.** At a non-arrival micro-step the abstract
run ticks iff the local core is not starved. -/
theorem run_progress (S : LocalSys X) (absS : X → State GalilVM) (Inv : X → Prop)
    (Pw : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (w : List (Fin 2)) (x0 : LX X)
    (x0_inv : Inv x0.core)
    (inv_tick : ∀ x, Inv x → Inv (S.tickL x))
    (inv_feed : ∀ a x, Inv x → Inv (S.feedC a x))
    (tick_of_not_starved : ∀ x, Inv x → ¬ S.Starved x →
      Tick (galilFrameS Pw q first) delay (absS x) (absS (S.tickL x)))
    (s : ℕ) (hi : inp w s = none) (hns : ¬ S.Starved (micro S w x0 s).core) :
    Tick (galilFrameS Pw q first) delay (stAbs S absS w x0 s) (stAbs S absS w x0 (s+1)) := by
  have hinv := inv_micro S w x0 Inv x0_inv inv_tick inv_feed s
  show Tick _ _ (absL absS (micro S w x0 s)) (absL absS (stepL S (inp w s) (micro S w x0 s)))
  rw [hi]
  exact tick_of_not_starved _ hinv hns

/-! ## 8. The deadline slot -/

/-- **Shifted Lindley.** With letter `m+1` available at `m·τ` (one slot earlier
than `GalilLindley.S` assumes), a zero backlog finishes checkpoint `m` by `m·τ`. -/
theorem run_on_time_shift (d : ℕ → ℕ) (c τ : ℕ) (hτ : 2*c ≤ τ) (T : ℕ → ℕ) (h0 : T 0 = 0)
    (hstep : ∀ m, T (m+1) ≤ max (T m) (m*τ) + d (m+1)) (m : ℕ)
    (hz : PalPeg.Predictability.backlog d c m = 0) : T m ≤ m*τ := by
  let T' : ℕ → ℕ := fun k => if k = 0 then 0 else T k + τ
  have h0' : T' 0 = 0 := rfl
  have hstep' : ∀ k, T' (k+1) ≤ max (T' k) ((k+1)*τ) + d (k+1) := by
    intro k
    have hs := hstep k
    show T (k+1) + τ ≤ _
    rcases k with _ | k
    · simp only [T', if_pos rfl, zero_mul, zero_add, one_mul, h0] at hs ⊢
      rw [max_eq_right (Nat.zero_le _)]
      rw [max_eq_left (Nat.zero_le _)] at hs
      omega
    · simp only [T', if_neg (Nat.succ_ne_zero k)]
      have e : (k+1+1)*τ = (k+1)*τ + τ := Nat.succ_mul _ _
      rw [e]
      rcases le_total (T (k+1)) ((k+1)*τ) with h | h
      · rw [max_eq_right h] at hs; rw [max_eq_right (by omega)]; omega
      · rw [max_eq_left h] at hs; rw [max_eq_left (by omega)]; omega
  have := PalPeg.Lindley.run_on_time d c τ hτ T' h0' hstep' m hz
  rcases m with _ | m
  · simp [h0]
  · simp only [T', if_neg (Nat.succ_ne_zero m), Nat.succ_mul] at this
    rw [Nat.succ_mul]; omega

/-- **Deadline slot, packaged.** Checkpoint times `Tc` of a run `st` obeying the
shifted O-step, with zero backlog at `|w|` and a refreshed report point at
checkpoint `|w|`, give `Reported` by `|w|·τ` — the machine's last micro-step. -/
theorem reported_of_shift (P : Shared) (q : ℕ) (first : Fin 9) (w : List (Fin 2))
    (st : ℕ → State GalilVM) (Tc d : ℕ → ℕ) (c : ℕ) (hτ : 2*c ≤ nLocalL) (h0 : Tc 0 = 0)
    (hstep : ∀ m, Tc (m+1) ≤ max (Tc m) (m*nLocalL) + d (m+1))
    (hz : PalPeg.Predictability.backlog d c w.length = 0)
    (hrep : ReportPoint w (st (Tc w.length)) ∧ Refreshed P q first (st (Tc w.length))) :
    Reported P q first w st (w.length * nLocalL) :=
  ⟨Tc w.length, run_on_time_shift d c nLocalL hτ Tc h0 hstep w.length hz, hrep.1, hrep.2⟩

/-! ## 9. The tracking theorem -/

/-- **Latched tracking from the oracles.**

Oracles:
* *tick simulation incl. latch* — `enc_step` (the encoding intertwines
  `LocalStep.apply` with `stepL`, i.e. `latchStep` / `arriveL`), `enc_init`,
  `enc_ans` (the finite control exposes the latch), `enc_started`, `x0_ans`,
  `x0_started`, `outL_abs` (local output = abstract `output`), and the report
  test: `rep_sound` (a passing test after the last arrival is a refreshed report
  point for `w`) and `rep_complete` (every refreshed report point for `w` is
  preceded, strictly after the arrival state of the last letter, by a passing
  test);
* *stutter correctness* — `stutter_of_starved`, `tick_of_not_starved` (used in
  `abstractRun_of_oracles`; not needed for the equivalence itself);
* *arrival encoding* — `feed_abs` (`arriveState'`), with the invariant;
* *deadline slot* — not an oracle of the equivalence: `T w = |w|·τ` is forced by
  the micro-step count; the ledger side is `reported_of_shift`. -/
theorem tracking_latch_of_oracles
    {t K : ℕ} {Q' Γ' : Type} [Fintype Q'] [DecidableEq Q'] [Fintype Γ'] [DecidableEq Γ']
    (S : LocalSys X) (absS : X → State GalilVM) (x0 : LX X)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9)
    (H_letter : ∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w)
    (H_first : ∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM)
    (L : LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q') (ansQ startQ : Q' → Bool)
    (enc : LX X → Q' × (Fin t → STape Γ')) (htape : 0 < t)
    -- tick simulation incl. latch
    (enc_step : ∀ (x : LX X) (a : Option (Fin 2)), L.apply blank (enc x) a = enc (stepL S a x))
    (enc_init : enc x0 = (initQ, fun _ => STape.blankTape blank))
    (enc_ans : ∀ x : LX X, ansQ (enc x).1 = x.ans)
    (enc_started : ∀ x : LX X, startQ (enc x).1 = x.started)
    (x0_started : x0.started = false)
    (outL_abs : ∀ x : X, S.outL x = (absS x).ctl.output)
    (rep_sound : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length → (w.length - 1) * nLocalL < s →
      S.repL (micro S w x0 s).core = true →
      ReportPoint w (stAbs S absS w x0 s) ∧ Refreshed (Pof w) (qof w) (firstOf w) (stAbs S absS w x0 s))
    (rep_complete : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length →
      ReportPoint w (stAbs S absS w x0 s) → Refreshed (Pof w) (qof w) (firstOf w) (stAbs S absS w x0 s) →
      ∃ s', s' ≤ s ∧ (w.length - 1) * nLocalL + 1 < s' ∧ S.repL (micro S w x0 s').core = true)
    (w : List (Fin 2)) (hw : 0 < w.length) :
    (L.realize blank initQ (GalilEmptyWord.accept' initQ ansQ) nLocalL htape nLocalL_pos).SAccepts w ↔
      LatchTrue (Pof w) (qof w) (firstOf w) w (stAbs S absS w x0) (w.length * nLocalL) := by
  have hfold := foldl_encL L blank S enc enc_step w x0
  rw [enc_init] at hfold
  have hne : (w.foldl (L.applyN blank nLocalL) (initQ, fun _ => STape.blankTape blank)).1 ≠ initQ := by
    intro hc
    have h1 : startQ (enc (w.foldl (blockL S) x0)).1 = true := by
      rw [enc_started]; exact started_foldl S w x0 hw
    rw [← hfold, hc] at h1
    have h2 : startQ (enc x0).1 = false := by rw [enc_started, x0_started]
    rw [enc_init] at h2
    rw [h1] at h2; cases h2
  rw [GalilEmptyWord.realize_accept'_pos L blank initQ ansQ nLocalL htape nLocalL_pos w hw hne,
    hfold, enc_ans, ← micro_end]
  have hE : w.length * nLocalL = (w.length - 1) * nLocalL + 1 + (nLocalL - 1) := by
    have := nLocalL_pos
    have e : w.length = (w.length - 1) + 1 := by omega
    conv_lhs => rw [e]
    rw [Nat.succ_mul]; omega
  rw [hE, latch_ans S w x0 hw, ← hE]
  constructor
  · rintro ⟨s, h1, h2, h3, h4⟩
    obtain ⟨hrp, hfr⟩ := rep_sound w s hw (by omega) h3
    refine ⟨s, h2, hrp, hfr, ?_⟩
    rw [outL_abs] at h4; exact h4
  · rintro ⟨s, h1, hrp, hfr, ho⟩
    obtain ⟨s', h1', h2', h3'⟩ := rep_complete w s hw hrp hfr
    obtain ⟨hrp', hfr'⟩ := rep_sound w s' hw (by omega) h3'
    refine ⟨s', h2', by omega, h3', ?_⟩
    rw [outL_abs]
    show (stAbs S absS w x0 s').ctl.output = true
    rw [report_output_eq w (Pof w) (H_letter w) (H_first w) (qof w) (firstOf w) _ _
      hrp' hfr' hrp hfr]
    exact ho

/-- The empty word, with `accept' := ans ∨ q = initQ`. -/
theorem empty_accepted {t K : ℕ} {Q' Γ' : Type} [Fintype Q'] [DecidableEq Q'] [Fintype Γ']
    [DecidableEq Γ'] (L : LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q')
    (ansQ : Q' → Bool) (htape : 0 < t) :
    (L.realize blank initQ (GalilEmptyWord.accept' initQ ansQ) nLocalL htape nLocalL_pos).SAccepts [] :=
  GalilEmptyWord.realize_accept'_nil L blank initQ ansQ nLocalL htape nLocalL_pos

/-- **`PAL ∈ PEG` from the latched local layer** plus the ledger for the run the
local run abstracts to, at the shifted deadline `|w|·τ`. -/
theorem pal_in_peg_of_local_latch
    {t K : ℕ} {Q' Γ' : Type} [Fintype Q'] [DecidableEq Q'] [Fintype Γ'] [DecidableEq Γ']
    (S : LocalSys X) (absS : X → State GalilVM) (Inv : List (Fin 2) → X → Prop) (x0 : LX X)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9)
    (delay : ℕ)
    (H_letter : ∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w)
    (H_first : ∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM)
    (L : LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q') (ansQ startQ : Q' → Bool)
    (enc : LX X → Q' × (Fin t → STape Γ')) (htape : 0 < t)
    (enc_step : ∀ (x : LX X) (a : Option (Fin 2)), L.apply blank (enc x) a = enc (stepL S a x))
    (enc_init : enc x0 = (initQ, fun _ => STape.blankTape blank))
    (enc_ans : ∀ x : LX X, ansQ (enc x).1 = x.ans)
    (enc_started : ∀ x : LX X, startQ (enc x).1 = x.started)
    (x0_started : x0.started = false)
    (outL_abs : ∀ x : X, S.outL x = (absS x).ctl.output)
    (rep_sound : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length → (w.length - 1) * nLocalL < s →
      S.repL (micro S w x0 s).core = true →
      ReportPoint w (stAbs S absS w x0 s) ∧ Refreshed (Pof w) (qof w) (firstOf w) (stAbs S absS w x0 s))
    (rep_complete : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length →
      ReportPoint w (stAbs S absS w x0 s) → Refreshed (Pof w) (qof w) (firstOf w) (stAbs S absS w x0 s) →
      ∃ s', s' ≤ s ∧ (w.length - 1) * nLocalL + 1 < s' ∧ S.repL (micro S w x0 s').core = true)
    (x0_inv : ∀ w, Inv w x0.core)
    (x0_ctl : (absS x0.core).ctl = GalilScaffoldController.initial delay)
    (inv_tick : ∀ w x, Inv w x → Inv w (S.tickL x))
    (inv_feed : ∀ w a x, Inv w x → Inv w (S.feedC a x))
    (stutter_of_starved : ∀ w x, Inv w x → S.Starved x → absS (S.tickL x) = absS x)
    (tick_of_not_starved : ∀ w x, Inv w x → ¬ S.Starved x →
      Tick (galilFrameS (Pof w) (qof w) (firstOf w)) delay (absS x) (absS (S.tickL x)))
    (feed_abs : ∀ w a x, Inv w x → absS (S.feedC a x) = arriveState' a (absS x))
    (H_ledger : LedgerObligation Pof qof firstOf (fun w => stAbs S absS w x0)
      (fun w => w.length * nLocalL)) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_of_latch' (Nat.mul_pos nLocalL_pos (PalPeg.Local.cnt_pos K))
    (L.realize blank initQ (GalilEmptyWord.accept' initQ ansQ) nLocalL htape nLocalL_pos)
    Pof qof firstOf delay H_letter H_first (fun w => stAbs S absS w x0) (fun w => arrL w)
    (fun w => w.length * nLocalL)
    (fun w _ => abstractRun_of_oracles S absS (Inv w) (Pof w) (qof w) (firstOf w) delay w x0
      (x0_inv w) x0_ctl (inv_tick w) (inv_feed w) (stutter_of_starved w) (tick_of_not_starved w)
      (feed_abs w))
    (fun w hw => tracking_latch_of_oracles S absS x0 Pof qof firstOf H_letter H_first
      L blank initQ ansQ startQ enc htape enc_step enc_init enc_ans enc_started x0_started outL_abs
      rep_sound rep_complete w hw)
    H_ledger (empty_accepted L blank initQ ansQ htape)

#print axioms nLocalL_eq
#print axioms inp_at
#print axioms inp_mid
#print axioms inp_late
#print axioms micro_block
#print axioms micro_end
#print axioms started_foldl
#print axioms foldl_encL
#print axioms latch_ans
#print axioms arrL_none
#print axioms arrL_some
#print axioms abstractRun_of_oracles
#print axioms run_progress
#print axioms run_on_time_shift
#print axioms reported_of_shift
#print axioms tracking_latch_of_oracles
#print axioms empty_accepted
#print axioms pal_in_peg_of_local_latch

end PalPeg.LocalTrackingLatch
