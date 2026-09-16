import PalPeg.GalilRealizeOfTracking
import PalPeg.GalilStructuredSkeleton
import PalPeg.LocalTracking
import PalPeg.GalilEmptyWord
import PalPeg.GalilOracleLocal

/-!
# Latched answers: tracking without "report point at every local period"

The scaffold *lags*: fallback / shift / replay phases do not move the scan, so
"at local time `|w| · nLocal` the abstract state is a report point" is false in
general, and `GalilRealizeOfTracking.Tracking` (a report point that *is* the
machine's final answer) is too strong for a realization.

Replacement semantics — **a latched answer**. The machine keeps a latch bit:

* reset on every arrival;
* set at a `refresh` whose right head sits on the newest letter and which is not
  replaying (i.e. at a refreshed `ReportPoint`), to the refreshed `output`.

The machine's accept flag after reading `w` is the latch. Abstractly: the run
`st : ℕ → State GalilVM` together with an arrival schedule, and the latch is
`LatchTrue w st T` — *some* refreshed report point up to abstract tick `T`
carries `output = true`.

* `latch_sound`    : `LatchTrue → w ∈ PAL`            (from `output_iff_pal`)
* `latch_complete` : `w ∈ PAL → Reported → LatchTrue` (from `output_iff_pal`)
* `report_output_eq`: all refreshed report points agree on `output`.

The remaining *scaffold* obligation is `LedgerObligation`: on palindromes the
scaffold does reach a refreshed report point by the deadline `T w`.
Non-palindromes need nothing (the latch is then never `true`).
-/

set_option autoImplicit false

namespace PalPeg.GalilLatchTracking

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton

/-! ## 1. Abstract runs with arrivals -/

/-- One abstract tick index step: a scaffold `Tick` of the merged scan frame, a
stutter, or the arrival of the next letter of `raw` (which advances the
arrival counter by one). Outside arrivals the counter is unchanged. -/
def RunStep (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (raw : List (Fin 2))
    (st : ℕ → State GalilVM) (arr : ℕ → ℕ) (k : ℕ) : Prop :=
  (arr (k+1) = arr k ∧
    (Tick (galilFrameS P q first) delay (st k) (st (k+1)) ∨ st (k+1) = st k)) ∨
  (arr (k+1) = arr k + 1 ∧
    ∃ a : Fin 2, raw[arr k]? = some a ∧ st (k+1) = LocalTracking.arriveState a (st k))

/-- An abstract run with arrivals: starts in the initial controller with no
letters arrived, and every step is a `RunStep`. -/
def AbstractRun (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (raw : List (Fin 2))
    (st : ℕ → State GalilVM) (arr : ℕ → ℕ) : Prop :=
  (st 0).ctl = GalilScaffoldController.initial delay ∧ arr 0 = 0 ∧
    ∀ k, RunStep P q first delay raw st arr k

/-- Some refreshed report point for `raw` occurs by abstract tick `T`. -/
def Reported (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (st : ℕ → State GalilVM) (T : ℕ) : Prop :=
  ∃ t ≤ T, ReportPoint raw (st t) ∧ Refreshed P q first (st t)

/-- The latch: some refreshed report point by tick `T` answers `true`. -/
def LatchTrue (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (st : ℕ → State GalilVM) (T : ℕ) : Prop :=
  ∃ t ≤ T, ReportPoint raw (st t) ∧ Refreshed P q first (st t) ∧ (st t).ctl.output = true

/-! ## 2. Soundness / completeness of the latch -/

/-- Refreshed report points are unique in output value. -/
theorem report_output_eq (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (x y : State GalilVM)
    (hx : ReportPoint raw x) (hxf : Refreshed P q first x)
    (hy : ReportPoint raw y) (hyf : Refreshed P q first y) :
    x.ctl.output = y.ctl.output := by
  have h1 := output_iff_pal raw P hP hP' q first x hx hxf
  have h2 := output_iff_pal raw P hP hP' q first y hy hyf
  cases hxo : x.ctl.output <;> cases hyo : y.ctl.output <;> simp_all

theorem latch_sound (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (st : ℕ → State GalilVM) (T : ℕ) :
    LatchTrue P q first raw st T → raw ∈ PAL := by
  rintro ⟨t, _, hrp, hfr, ho⟩
  exact (output_iff_pal raw P hP hP' q first (st t) hrp hfr).mp ho

theorem latch_complete (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (st : ℕ → State GalilVM) (T : ℕ) :
    raw ∈ PAL → Reported P q first raw st T → LatchTrue P q first raw st T := by
  rintro hpal ⟨t, ht, hrp, hfr⟩
  exact ⟨t, ht, hrp, hfr, (output_iff_pal raw P hP hP' q first (st t) hrp hfr).mpr hpal⟩

/-- Given the ledger instance for `raw`, the latch is exactly membership. -/
theorem latch_iff_pal (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (st : ℕ → State GalilVM) (T : ℕ) (hled : raw ∈ PAL → Reported P q first raw st T) :
    LatchTrue P q first raw st T ↔ raw ∈ PAL :=
  ⟨latch_sound raw P hP hP' q first st T,
   fun h => latch_complete raw P hP hP' q first st T h (hled h)⟩

/-! ## 3. The ledger obligation -/

/-- **The ledger obligation.** For every nonempty palindrome `w`, the chosen
abstract run `stOf w` reaches a refreshed report point for `w` no later than
the deadline `T w`. (Nothing is required of non-palindromes.) -/
def LedgerObligation (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (stOf : List (Fin 2) → ℕ → State GalilVM)
    (T : List (Fin 2) → ℕ) : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → w ∈ PAL →
    Reported (Pof w) (qof w) (firstOf w) w (stOf w) (T w)

/-- **Relation to `GalilLedgerObligations2.pal_in_peg_of_galil_buffered`.**
There the ledger's centre obligation is `hcentre : w ∈ PAL → C w |w| = |w|`
("on a palindrome the centre counter has caught up with the input"). That is a
statement about a counter, not about a run; it yields `LedgerObligation` once
one has the *catch-up ⇒ report* bridge `hbridge` (a caught-up centre at the
deadline means the scaffold has produced a refreshed report point by `T w`).
The shapes relate exactly through this composition. -/
theorem ledgerObligation_of_hcentre (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (stOf : List (Fin 2) → ℕ → State GalilVM)
    (T : List (Fin 2) → ℕ) (C : List (Fin 2) → ℕ → ℕ)
    (hcentre : ∀ w : List (Fin 2), w ∈ PAL → C w w.length = w.length)
    (hbridge : ∀ w : List (Fin 2), 0 < w.length → C w w.length = w.length →
      Reported (Pof w) (qof w) (firstOf w) w (stOf w) (T w)) :
    LedgerObligation Pof qof firstOf stOf T :=
  fun w hw hpal => hbridge w hw (hcentre w hpal)

/-! ## 4. `PAL ∈ PEG` from a latched realization plus the ledger -/

/-- **`PAL ∈ PEG` from latches.** Obligations:
* `H_run`     : each nonempty `w` has an abstract run with arrivals `stOf w`/`arrOf w`;
* `H_realize` : the machine's accept flag is the latch at the deadline `T w`
  (locally: latch bit reset on arrival, set at a non-replaying refresh with the
  right head on the newest letter);
* `H_ledger`  : `LedgerObligation`;
* `H_empty`   : the empty word. -/
theorem pal_in_peg_of_latch {Q Γ : Type} [Fintype Q] [DecidableEq Q]
    [Fintype Γ] [DecidableEq Γ] {t B : ℕ} (hB : 0 < B)
    (M : StructuredMachine (Fin 2) Q Γ t B)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (delay : ℕ)
    (H_letter : ∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w)
    (H_first : ∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM)
    (stOf : List (Fin 2) → ℕ → State GalilVM) (arrOf : List (Fin 2) → ℕ → ℕ)
    (T : List (Fin 2) → ℕ)
    (_H_run : ∀ w : List (Fin 2), 0 < w.length →
      AbstractRun (Pof w) (qof w) (firstOf w) delay w (stOf w) (arrOf w))
    (H_realize : ∀ w : List (Fin 2), 0 < w.length →
      (M.SAccepts w ↔ LatchTrue (Pof w) (qof w) (firstOf w) w (stOf w) (T w)))
    (H_ledger : LedgerObligation Pof qof firstOf stOf T)
    (H_empty : M.SAccepts []) :
    RecognizedByTotalPEG PAL := by
  refine pal_in_peg_of_structured hB M ?_
  intro w
  rcases w with _ | ⟨a, w⟩
  · simp only [H_empty, true_iff]
    rw [mem_PAL_iff_isPal]
    simp [PalPeg.IsPal]
  · have hlen : 0 < (a :: w).length := by simp
    exact (H_realize _ hlen).trans
      (latch_iff_pal (a :: w) _ (H_letter _) (H_first _) _ _ _ _ (H_ledger _ hlen))

#print axioms RunStep
#print axioms AbstractRun
#print axioms Reported
#print axioms LatchTrue
#print axioms report_output_eq
#print axioms latch_sound
#print axioms latch_complete
#print axioms latch_iff_pal
#print axioms LedgerObligation
#print axioms ledgerObligation_of_hcentre
#print axioms pal_in_peg_of_latch

end PalPeg.GalilLatchTracking
