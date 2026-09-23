import PalPeg.ScaFlagsReaders
import PalPeg.ScaWindowPlumbing

/-!
# The flag workers' promise from the flags jobs

`ScaWindowPlumbing.FlagsContract` asks, for the real controller, that job `r` of the stage born
at `b = 2^j` (half `S = 2^(j-1)`) released at `R = b + (r+1)S` be captured at some `c` with
`R ≤ c < R + S`: not done at `R … c-1`, done at `c`, with the job's bits. This file derives it
from one fact about the flags head VM per job.

## What the controller hands the flag worker

* At the stage's birth (the tick producing `b`), `resetFlags` puts `begin := end = b`, `h := 0`.
* Between releases every tick is an arrival (`tick_idle`); at the release of job `r` (the tick
  producing `b + (r+1)S`) the worker has `begin = b`, `end = b + (r+1)S` and `hKey = S` (the
  arrivals since the previous release or the birth). `start true; mark true` therefore starts
  `DualFlagVM(y, rS, (r+1)S)` on `y = W[b, b + (r+1)S)` (`releaseVM_eq`): `Upper = (r+1)S`,
  `Lower = rS`, and the job's bits are the palindrome bits of the prefixes of `y` of lengths
  `rS, …, rS + S - 1` (`jobBits_eq`).
* From the release on, one service quantum (32768 VM steps) runs per tick. If the VM halts after
  `N` steps, the worker executes the halt row as its step `N + 1`, i.e. in the tick
  `R + N / 32768`. So the capture tick is `R + N / 32768`, and the contract's `c < R + S` is
  exactly `N < 32768 · S`.

## The hypothesis

`JobHalts y S r`: `DualFlagVM(y, rS, (r+1)S)` from the coroutine's first yield runs `N < 32768·S`
steps (`iterFlags N … = some v`) to a halted VM whose flags, reversed, are the palindrome bits
(`segBits`). `iterFlags N … = some v` already says that no earlier state halted or got stuck.
The main theorems take `JobHalts` for every word of length `(r+1)·2^i`, `r < 4`.

## Results

* `flagsContract`: `FlagsContract mOps flagsOps m0 flagsInit W` for every `W` (any matcher).
* `flags_never_fault`: the flag workers never fault on any input (`flagsOps.faulted … = false`).
-/

set_option autoImplicit false

namespace PalPeg.ScaFlagsLife

open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWindowWorker PalPeg.ScaWorkerCoroutine
  PalPeg.ScaHeadVM PalPeg.ScaFlagsLink PalPeg.ScaWindowInstance PalPeg.ScaWindowPal
  PalPeg.ScaWindowSchedule PalPeg.ScaWindowPlumbing

/-! ## The per-job promise -/

/-- The palindrome bits of the prefixes of `y` of lengths `rS, …, rS + S - 1`. -/
def segBits (y : List (Fin 2)) (S r : ℕ) : List Bool :=
  (List.range S).map fun i => (y.take (r * S + i)).reverse == y.take (r * S + i)

/-- `DualFlagVM(y, rS, (r+1)S)` at the coroutine's first yield. -/
def jobStart (y : List (Fin 2)) (S r : ℕ) : HVM :=
  flagsInitialVM y ((r * S : ℕ) : ℤ) (((r + 1) * S : ℕ) : ℤ) ctl0

/-- **The per-job promise**: the flags job on `y` halts within `32768·S` steps, leaving the bits of
the job on its flag list (append order, i.e. reversed onto the worker's stack). -/
def JobHalts (y : List (Fin 2)) (S r : ℕ) : Prop :=
  ∃ N v, N < 32768 * S ∧ iterFlags N (jobStart y S r) = some v ∧ v.flagsDone ∧
    v.flags.reverse = segBits y S r

/-- The segment of job `r` of the stage born at `b` with half `S`. -/
def seg (W : List (Fin 2)) (b S r : ℕ) : List (Fin 2) := (W.drop b).take ((r + 1) * S)

theorem jobBits_eq (W : List (Fin 2)) (b S r : ℕ) :
    jobBits W b S r = segBits (seg W b S r) S r := by
  unfold jobBits segBits seg
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [List.take_take, Nat.min_eq_left (by rw [Nat.add_mul, Nat.one_mul]; omega)]

/-! ## Runs of the VM that halt -/

theorem stepFlags_done {u : HVM} (hu : u.flagsDone) : stepFlags u = none := by
  obtain ⟨val, hval⟩ := hu
  unfold stepFlags
  rw [hval]

theorem iterFlags_done {u : HVM} (hu : u.flagsDone) (m : ℕ) : iterFlags (m + 1) u = none := by
  simp only [iterFlags, stepFlags_done hu, Option.bind_none]

/-- Along a run that halts at step `N`, every state is at step `m ≤ N`, and only the last one
has halted. -/
theorem halt_unique {v0 V u : HVM} {N m : ℕ} (hN : iterFlags N v0 = some V) (hV : V.flagsDone)
    (hm : iterFlags m v0 = some u) : m ≤ N ∧ (u.flagsDone → m = N) := by
  refine ⟨?_, fun hu => ?_⟩
  · by_contra hlt
    have h := iterFlags_add N (m - N - 1 + 1) v0
    rw [show N + (m - N - 1 + 1) = m by omega, hN, Option.bind_some, iterFlags_done hV] at h
    rw [hm] at h
    cases h
  · by_contra hne
    have hlt : m < N := by
      have := (show m ≤ N by
        by_contra hlt
        have h := iterFlags_add N (m - N - 1 + 1) v0
        rw [show N + (m - N - 1 + 1) = m by omega, hN, Option.bind_some, iterFlags_done hV] at h
        rw [hm] at h
        cases h)
      omega
    have h := iterFlags_add m (N - m - 1 + 1) v0
    rw [show m + (N - m - 1 + 1) = N by omega, hm, Option.bind_some, iterFlags_done hu] at h
    rw [hN] at h
    cases h

/-- A state on a run that halts is never stuck before halting. -/
theorem runsFor_of_halt {v0 V v : HVM} {N m : ℕ} (hN : iterFlags N v0 = some V)
    (hV : V.flagsDone) (hm : iterFlags m v0 = some v) (k : ℕ) : RunsFor k v := by
  intro i _ u hu hnd
  have hmi : iterFlags (m + i) v0 = some u := by
    rw [iterFlags_add, hm, Option.bind_some, hu]
  obtain ⟨hle, hlast⟩ := halt_unique hN hV hmi
  have hlt : m + i < N := by
    rcases Nat.lt_or_ge (m + i) N with h | h
    · exact h
    · exact absurd (by have := hlast; exact (show u.flagsDone by
        have heq : m + i = N := by omega
        rw [heq, hN] at hmi
        cases hmi
        exact hV)) hnd
  have h := iterFlags_add (m + i) (N - (m + i) - 1 + 1) v0
  rw [show m + i + (N - (m + i) - 1 + 1) = N by omega, hmi, Option.bind_some, hN] at h
  cases hs : stepFlags u with
  | none => simp [iterFlags, hs] at h
  | some _ => rfl

/-! ## The flag worker's text, `begin` and `hKey` through a tick -/

theorem step_counters (w : Worker) (act : Bool) (s : WorkerState) :
    ScaWorkerRegs.counters (step w act s) = ScaWorkerRegs.counters s ∧
      (step w act s).text = s.text := by
  refine ⟨?_, (step_text_end w act s).1⟩
  cases act
  · rw [step_inactive]
  · rw [step_eq]
    exact (ScaWorkerRegs.effect_counters w.spec (w.fields s.pc) true s).1

theorem service_frame (s : WorkerState) :
    ScaWorkerRegs.counters (service flagsW s) = ScaWorkerRegs.counters s ∧
      (service flagsW s).text = s.text := by
  unfold service
  generalize List.range flagsW.spec.quantum = l
  induction l generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons x l ih =>
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (step flagsW (decide (s.mode = .run)) s)
    obtain ⟨h3, h4⟩ := step_counters flagsW (decide (s.mode = .run)) s
    exact ⟨h1.trans h3, h2.trans h4⟩

theorem start_counters (en : Bool) (s : WorkerState) :
    ScaWorkerRegs.counters (start flagsW en s) = ScaWorkerRegs.counters s := by
  obtain ⟨t, hframeT, hframeBody⟩ := ScaWorkerRegs.startBody_frame (spec := fspec) en s
  have hc : ScaWorkerRegs.counters (startBody flagsW en s) = ScaWorkerRegs.counters s := by
    simp only [ScaWorkerRegs.frame, Prod.mk.injEq] at hframeT hframeBody
    rw [flagsW_eq, hframeBody.2.1, ← hframeT.2.1]
    cases en
    · rfl
    · rw [ScaWorkerRegs.initializeValues_true]
      exact (ScaWorkerRegs.initFold_frame (spec := fspec) _ t).1
  rw [start_eq]
  cases en
  · exact hc
  · exact hc

theorem counters_eq {s t : WorkerState} (h : ScaWorkerRegs.counters s = ScaWorkerRegs.counters t) :
    s.begin = t.begin ∧ s.end = t.end ∧ s.h = t.h := by
  simp only [ScaWorkerRegs.counters, Prod.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.2⟩

/-- A tick without birth: the letter is appended, `begin` stays, `hKey` counts the arrival or is
cleared by a release. -/
theorem flagTick_frame (a : Fin 2) (rel : Bool) (s : WorkerState) :
    (flagTick a false rel s).text = s.text ++ [a] ∧ (flagTick a false rel s).begin = s.begin ∧
      (flagTick a false rel s).h = (if rel then 0 else s.h + 1) := by
  rw [flagTick_eq, resetFlags_false]
  obtain ⟨hsc, hst⟩ := service_frame (mark flagsW rel (start flagsW rel (arrive flagsW a s)))
  obtain ⟨hsb, -, hsh⟩ := counters_eq hsc
  obtain ⟨hstb, -, hsth⟩ := counters_eq (start_counters rel (arrive flagsW a s))
  have hso := start_outer (arrive flagsW a s)
  simp only [outer, Prod.mk.injEq] at hso
  have hat : (arrive flagsW a s).text = s.text ++ [a] := (arrive_proj flagsW a s).2.2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [hst]
    cases rel
    · rw [mark_false, start_false, hat]
    · rw [mark_true]
      show (start flagsW true (arrive flagsW a s)).text = _
      rw [hso.2.1, hat]
  · rw [hsb]
    cases rel
    · rw [mark_false, hstb, arrive_begin]
    · rw [mark_true]
      show (start flagsW true (arrive flagsW a s)).begin = _
      rw [hstb, arrive_begin]
  · rw [hsh]
    cases rel
    · rw [mark_false, hsth, arrive_h]; rfl
    · rw [mark_true]; rfl

/-! ## What a controller tick hands flag worker `i` -/

section Controller

variable {Wm Wf : Type} (mOps : WorkerOps Wm) (fOps : WorkerOps Wf)

/-- Flag worker `i` through a controller tick (any worker ops): arrive, `resetFlags` with the
birth bit of the tick, `start`/`mark` with the release bit of its advanced stage, service. -/
theorem tick_flags_ops (s : PalState Wm Wf) (a : Fin 2) (i : Fin 2) :
    (tick mOps fOps s a).flags i =
      fOps.service (fOps.mark (ScaWindowPal.advance (s.stages i) (birthOf s && s.slot == i) s.power).1.release
        (fOps.start (ScaWindowPal.advance (s.stages i) (birthOf s && s.slot == i) s.power).1.release
          (fOps.resetFlags (birthOf s && s.slot == i) (fOps.arrive a (s.flags i))))) := by
  have hb : (s.powerReady && (if s.powerReady then s.nextBirth.pred else s.nextBirth) == 0) =
      birthOf s := by unfold birthOf; cases s.powerReady <;> simp
  fin_cases i
  · rw [← hb]; rfl
  · rw [← hb]; rfl

/-- Flag worker `i` of the real flag workers through a controller tick. -/
theorem tick_flags (s : PalState Wm WorkerState) (a : Fin 2) (i : Fin 2) :
    (tick mOps flagsOps s a).flags i =
      flagTick a (birthOf s && s.slot == i)
        (ScaWindowPal.advance (s.stages i) (birthOf s && s.slot == i) s.power).1.release (s.flags i) := by
  rw [tick_flags_ops]
  rfl

end Controller

/-- A birth is not a release. -/
theorem release_birth (st : StageState) (src : ℕ) : (ScaWindowPal.advance st true src).1.release = false := by
  simp [ScaWindowPal.advance]

/-- A stage not yet born releases nothing. -/
theorem release_dormant {st : StageState} (h : st.alive = false) (src : ℕ) :
    (ScaWindowPal.advance st false src).1.release = false := by
  simp [ScaWindowPal.advance, h]

/-- A stage not yet born stays unborn without a birth. -/
theorem alive_dormant {st : StageState} (h : st.alive = false) (src : ℕ) :
    (ScaWindowPal.advance st false src).1.alive = false := by
  simp [ScaWindowPal.advance, h]

/-- **The release bit of a live stage**: it releases at the ticks onto `(r+1)S`, `r < 4`. -/
theorem release_live {st : StageState} {S d : ℕ} (hS : 1 ≤ S) (h : StageAt st S d)
    (hlive : (d + 1) / S ≤ 5) (src : ℕ) :
    (ScaWindowPal.advance st false src).1.release = decide ((d + 1) % S = 0 ∧ (d + 1) / S ≤ 4) := by
  by_cases hb : (d + 1) % S = 0
  · rw [advance_on hS h hb src]
    obtain ⟨q, m, hm, rfl⟩ : ∃ q m, m < S ∧ d = q * S + m :=
      ⟨d / S, d % S, Nat.mod_lt _ (by omega), by rw [Nat.div_add_mod' d S]⟩
    have hmS : m = S - 1 := by
      rcases Nat.lt_or_ge (m + 1) S with hm1 | hm1
      · rw [(divmod_off (q := q) hm1).2] at hb; omega
      · omega
    subst hmS
    have hq0 : (q * S + (S - 1)) / S = q := (divmod_at (q := q) (show S - 1 < S by omega)).1
    have hd1 : q * S + (S - 1) + 1 = (q + 1) * S := by rw [Nat.add_mul, Nat.one_mul]; omega
    have hq1 : (q + 1) * S / S = q + 1 := Nat.mul_div_cancel _ (by omega)
    rw [hd1, hq1] at hlive ⊢
    have hiv0 : st.interval.val = q := by rw [h.2.2.2, hq0]
    have hiv : (incInterval st.interval).val = q + 1 := by simp [incInterval, hiv0]; omega
    show relOf (incInterval st.interval) = _
    simp only [relOf, hiv]
    rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 by omega) with h0 | h0 | h0 | h0 | h0 <;>
      simp [h0, Nat.mul_mod_left]
  · rw [advance_off hS h hb src]
    simp [hb]

/-! ## The flag worker through the life of one stage -/

/-- `DualFlagVM` of job `r` of the stage born at `b` with half `S`. -/
def jobVM (W : List (Fin 2)) (b S r : ℕ) : HVM := jobStart (seg W b S r) S r

/-- The jobs of the stage born at `b` with half `S` (those released inside `W`) halt after
`N r < 32768·S` steps with their bits. -/
def StageJobs (W : List (Fin 2)) (N : ℕ → ℕ) (b S : ℕ) : Prop :=
  ∀ r, r < 4 → b + (r + 1) * S ≤ W.length →
    N r < 32768 * S ∧ ∃ V, iterFlags (N r) (jobVM W b S r) = some V ∧ V.flagsDone ∧
      V.flags.reverse = jobBits W b S r

/-- The flag worker `e` ticks after the release of job `r`: running the job's VM (after
`32768·(e+1)` steps) until the tick `N r / 32768`, done with the job's bits from then on. -/
def JobPhase (W : List (Fin 2)) (N : ℕ → ℕ) (b S r e : ℕ) (s : WorkerState) : Prop :=
  s.h = (e : ℤ) ∧
  (e < N r / 32768 → s.mode = .run ∧
    ∃ v, iterFlags (32768 * (e + 1)) (jobVM W b S r) = some v ∧ Link b ((r + 1) * S) s v) ∧
  (N r / 32768 ≤ e → s.mode = .done ∧ s.flags = jobBits W b S r)

/-- **The flag worker of the stage born at `b` with half `S`, `d` ticks after the birth.** -/
def WorkerAt (W : List (Fin 2)) (N : ℕ → ℕ) (b S d : ℕ) (s : WorkerState) : Prop :=
  Base s ∧ s.fault = false ∧ s.text = W.take (b + d) ∧ s.begin = b ∧
  (d < S → s.mode = .idle ∧ s.h = (d : ℤ)) ∧
  (S ≤ d → ∃ r, r < 4 ∧ (r + 1) * S ≤ d ∧ (d < (r + 2) * S ∨ r = 3) ∧
    JobPhase W N b S r (d - (r + 1) * S) s)

/-- A flag worker between stages (or before its first): not running, not faulted. -/
def Ready (W : List (Fin 2)) (n : ℕ) (s : WorkerState) : Prop :=
  Base s ∧ s.fault = false ∧ s.mode ≠ .run ∧ s.text = W.take n

theorem take_succ_getElem (W : List (Fin 2)) {n : ℕ} (hn : n < W.length) :
    W.take n ++ [W[n]] = W.take (n + 1) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hn, Option.toList_some]

theorem end_of_text {W : List (Fin 2)} {n : ℕ} {s : WorkerState} (hb : Base s)
    (ht : s.text = W.take n) (hn : n ≤ W.length) : s.end = n := by
  rw [hb.endEq, ht, List.length_take, Nat.min_eq_left hn]

/-- An idle tick of a waiting worker. -/
theorem ready_idle {W : List (Fin 2)} {n : ℕ} {s : WorkerState} (h : Ready W n s)
    (hn : n < W.length) : Ready W (n + 1) (flagTick W[n] false false s) := by
  obtain ⟨hb, hf, hm, ht⟩ := h
  obtain ⟨heq, hb', hf', hm', -⟩ := tick_idle hb hm W[n]
  refine ⟨hb', by rw [hf', hf], by rw [hm']; exact hm, ?_⟩
  rw [heq, (arrive_proj flagsW W[n] s).2.2.1, ht, take_succ_getElem W hn]

/-- **A birth**: a waiting worker is reset onto the new stage. -/
theorem workerAt_birth {W : List (Fin 2)} {N : ℕ → ℕ} {n S : ℕ} {s : WorkerState}
    (h : Ready W n s) (hn : n < W.length) (hS : 1 ≤ S) :
    WorkerAt W N (n + 1) S 0 (flagTick W[n] true false s) := by
  obtain ⟨hb, hf, -, ht⟩ := h
  obtain ⟨heq, hb', hf', hm', -, hbeg, hh⟩ := tick_birth hb W[n]
  have hend := end_of_text hb ht hn.le
  refine ⟨hb', by rw [hf', hf], ?_, by rw [hbeg, hend], fun _ => ⟨hm', by rw [hh]; rfl⟩,
    fun h0 => absurd h0 (by omega)⟩
  rw [heq, resetFlags_true]
  show (arrive flagsW W[n] s).text = _
  rw [(arrive_proj flagsW W[n] s).2.2.1, ht, take_succ_getElem W hn]

/-- A job within its budget is done `S - 1` ticks after its release. -/
theorem jobPhase_done {W : List (Fin 2)} {N : ℕ → ℕ} {b S r e : ℕ} {s : WorkerState}
    (h : JobPhase W N b S r e s) (hN : N r < 32768 * S) (he : S - 1 ≤ e) : s.mode = .done :=
  (h.2.2 (by omega)).1

theorem releaseVM_eq {W : List (Fin 2)} {b S r : ℕ} {t : WorkerState}
    (ht : t.text = W.take (b + (r + 1) * S)) (hbeg : t.begin = b) (hend : t.end = b + (r + 1) * S)
    (hh : t.h = (S : ℤ)) : releaseVM t = jobVM W b S r := by
  unfold releaseVM jobVM jobStart seg
  have hL : t.end - t.begin = (r + 1) * S := by rw [hend, hbeg]; omega
  rw [hL, ht, hbeg, hh]
  have hw : flagWord (W.take (b + (r + 1) * S)) b ((r + 1) * S) = (W.drop b).take ((r + 1) * S) := by
    unfold flagWord
    rw [List.drop_take, show b + (r + 1) * S - b = (r + 1) * S by omega, List.take_take,
      Nat.min_self]
  rw [hw]
  congr 1
  push_cast
  ring

theorem mul_lt_of {a c S : ℕ} (h : a * S < c * S) : a < c := Nat.lt_of_mul_lt_mul_right h

theorem mul_le_of {a c S : ℕ} (hS : 1 ≤ S) (h : a * S ≤ c * S) : a ≤ c :=
  Nat.le_of_mul_le_mul_right h (by omega)

/-- The release tick of job `r`: the worker was waiting with `hKey = S - 1`. -/
theorem workerAt_release {W : List (Fin 2)} {N : ℕ → ℕ} {b S d r : ℕ} {s : WorkerState}
    (hS : 1 ≤ S) (hjobs : StageJobs W N b S) (hn : b + d < W.length)
    (hdr : d + 1 = (r + 1) * S) (hr : r < 4)
    (hbase : Base s) (hfault : s.fault = false) (htext : s.text = W.take (b + d))
    (hbeg : s.begin = b) (hmode : s.mode ≠ .run) (hh : s.h = ((S - 1 : ℕ) : ℤ)) :
    WorkerAt W N b S (d + 1) (flagTick W[b + d] false true s) := by
  have hend : s.end = b + d := end_of_text hbase htext hn.le
  obtain ⟨htext', hbeg', hh'⟩ := flagTick_frame W[b + d] true s
  have htA : (arrive flagsW W[b + d] s).text = W.take (b + (r + 1) * S) := by
    rw [(arrive_proj flagsW W[b + d] s).2.2.1, htext, take_succ_getElem W hn, ← hdr]; rfl
  have hbA : (arrive flagsW W[b + d] s).begin = b := by rw [arrive_begin, hbeg]
  have heA : (arrive flagsW W[b + d] s).end = b + (r + 1) * S := by rw [arrive_end, hend]; omega
  have hhA : (arrive flagsW W[b + d] s).h = (S : ℤ) := by
    rw [arrive_h, hh, Nat.cast_sub hS]
    push_cast
    ring
  have hvm : releaseVM (arrive flagsW W[b + d] s) = jobVM W b S r := releaseVM_eq htA hbA heA hhA
  obtain ⟨hNr, V, hV, hVd, hVbits⟩ := hjobs r hr (by omega)
  have hrun : RunsFor quantum (releaseVM (arrive flagsW W[b + d] s)) := by
    rw [hvm]
    exact runsFor_of_halt (m := 0) hV hVd rfl quantum
  obtain ⟨n', v', hn', hiter, hlink, hfault', hdone, hdone', hflags⟩ :=
    tick_release ScaFlagsReaders.readerFacts hbase W[b + d] hrun
  rw [hvm] at hiter
  rw [quantum_eq] at hn' hdone
  have hLb : s.end + 1 - s.begin = (r + 1) * S := by rw [hbeg, hend]; omega
  rw [hLb, hbeg] at hlink
  obtain ⟨hle, hlast⟩ := halt_unique hV hVd hiter
  have hSr : S ≤ (r + 1) * S := Nat.le_mul_of_pos_left S (Nat.succ_pos r)
  refine ⟨hlink.base, ?_, by rw [htext', htext, take_succ_getElem W hn]; rfl,
    by rw [hbeg', hbeg], fun h1 => absurd h1 (by omega),
    fun _ => ⟨r, hr, by omega, Or.inl (by rw [show (r + 2) * S = (r + 1) * S + S by ring]; omega), ?_⟩⟩
  · rw [hfault', hfault]
    simp [hmode]
  · have he0 : d + 1 - (r + 1) * S = 0 := by omega
    rw [he0]
    refine ⟨by rw [hh']; rfl, fun hlt => ?_, fun hge => ?_⟩
    · -- still running after the release tick
      have hnd : modeDone (flagTick W[b + d] false true s) = false := by
        cases hmd : modeDone (flagTick W[b + d] false true s)
        · rfl
        · have hnl := hdone.mp hmd
          have := hlast (hdone' hmd)
          omega
      have hn1024 : n' = 32768 := by
        by_contra hne
        have := hdone.mpr (by omega)
        rw [hnd] at this
        cases this
      refine ⟨?_, v', by rw [← hn1024]; simpa using hiter, hlink⟩
      rcases hlink.mode with hm | ⟨hm, -⟩
      · exact hm
      · simp [modeDone, hm] at hnd
    · -- done in the release tick
      have hNlt : N r < 32768 := by omega
      have hn'lt : n' < 32768 := by omega
      have hmd := hdone.mpr hn'lt
      have hnN := hlast (hdone' hmd)
      subst hnN
      rw [hiter] at hV
      cases hV
      refine ⟨by simpa [modeDone] using hmd, ?_⟩
      rw [hflags, hVbits]

/-- A tick inside the window of job `r` (no release): the running job advances one quantum. -/
theorem workerAt_window {W : List (Fin 2)} {N : ℕ → ℕ} {b S d r : ℕ} {s : WorkerState}
    (hjobs : StageJobs W N b S) (hn : b + d < W.length) (hr : r < 4) (hr1 : (r + 1) * S ≤ d)
    (hr2 : d + 1 < (r + 2) * S ∨ r = 3)
    (hbase : Base s) (hfault : s.fault = false) (htext : s.text = W.take (b + d))
    (hbeg : s.begin = b) (hph : JobPhase W N b S r (d - (r + 1) * S) s) :
    WorkerAt W N b S (d + 1) (flagTick W[b + d] false false s) := by
  obtain ⟨htext', hbeg', hh'⟩ := flagTick_frame W[b + d] false s
  have htext1 : (flagTick W[b + d] false false s).text = W.take (b + (d + 1)) := by
    rw [htext', htext, take_succ_getElem W hn]; rfl
  have he : d + 1 - (r + 1) * S = d - (r + 1) * S + 1 := by omega
  have hSr : S ≤ (r + 1) * S := Nat.le_mul_of_pos_left S (Nat.succ_pos r)
  obtain ⟨hNr, V, hV, hVd, hVbits⟩ := hjobs r hr (by omega)
  have hwin : ∀ t : WorkerState, Base t → t.fault = false → t.begin = b →
      t.text = W.take (b + (d + 1)) → JobPhase W N b S r (d - (r + 1) * S + 1) t →
      WorkerAt W N b S (d + 1) t := fun t hb hf hbg ht hp =>
    ⟨hb, hf, ht, hbg, fun h1 => absurd h1 (by omega),
      fun _ => ⟨r, hr, by omega, hr2, by rw [he]; exact hp⟩⟩
  obtain ⟨hhe, hrun, hdn⟩ := hph
  have hhnew : (flagTick W[b + d] false false s).h = ((d - (r + 1) * S + 1 : ℕ) : ℤ) := by
    rw [hh', hhe]; push_cast; rfl
  by_cases hrunning : d - (r + 1) * S < N r / 32768
  · obtain ⟨hmr, v, hv, hlink⟩ := hrun hrunning
    obtain ⟨n', v'', hn', hiter, hlink', hfault', hmode', hdone', hflags'⟩ :=
      tick_running ScaFlagsReaders.readerFacts hlink W[b + d] (runsFor_of_halt hV hVd hv quantum)
    rw [quantum_eq] at hn' hmode' hdone'
    have hcomb : iterFlags (32768 * (d - (r + 1) * S + 1) + n') (jobVM W b S r) = some v'' := by
      rw [iterFlags_add, hv, Option.bind_some, hiter]
    obtain ⟨hle, hlast⟩ := halt_unique hV hVd hcomb
    refine hwin _ hlink'.base (by rw [hfault', hfault]) (by rw [hbeg', hbeg]) htext1
      ⟨hhnew, fun hlt => ?_, fun hge => ?_⟩
    · have hn1024 : n' = 32768 := by
        by_contra hne
        have := hlast (hdone' (by omega))
        omega
      refine ⟨?_, v'', ?_, hlink'⟩
      · rcases hlink'.mode with hm | ⟨hm, -⟩
        · exact hm
        · have := hmode'.mp hm
          rw [hmr] at this
          simp only [reduceCtorEq, false_or] at this
          omega
      · rw [hn1024] at hcomb
        rw [show 32768 * (d - (r + 1) * S + 1 + 1) = 32768 * (d - (r + 1) * S + 1) + 32768 by ring]
        exact hcomb
    · have hn'lt : n' < 32768 := by
        by_contra hge'
        omega
      have hnN := hlast (hdone' hn'lt)
      rw [← hnN, hcomb] at hV
      cases hV
      refine ⟨hmode'.mpr (Or.inr hn'lt), ?_⟩
      rw [hflags', hVbits]
  · have hdn' := hdn (by omega)
    obtain ⟨heq, hb', hf', hm', hfl'⟩ := tick_idle hbase (by rw [hdn'.1]; decide) W[b + d]
    exact hwin _ hb' (by rw [hf', hfault]) (by rw [hbeg', hbeg]) htext1
      ⟨hhnew, fun hlt => absurd hlt (by omega), fun _ => ⟨by rw [hm', hdn'.1], by rw [hfl', hdn'.2]⟩⟩

/-- **One tick of a live stage's flag worker**, with the release bit of the schedule. -/
theorem workerAt_step {W : List (Fin 2)} {N : ℕ → ℕ} {b S d : ℕ} {s : WorkerState}
    (hS : 1 ≤ S) (hjobs : StageJobs W N b S) (hd : d + 1 < 6 * S) (hn : b + d < W.length)
    (h : WorkerAt W N b S d s) :
    WorkerAt W N b S (d + 1)
      (flagTick W[b + d] false (decide ((d + 1) % S = 0 ∧ (d + 1) / S ≤ 4)) s) := by
  obtain ⟨hbase, hfault, htext, hbeg, hyoung, hold⟩ := h
  by_cases hrelT : (d + 1) % S = 0 ∧ (d + 1) / S ≤ 4
  · rw [decide_eq_true hrelT]
    set q := (d + 1) / S with hqdef
    have hdq : d + 1 = q * S := by
      have := Nat.div_add_mod (d + 1) S
      rw [hrelT.1, Nat.add_zero, Nat.mul_comm] at this
      exact this.symm
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · rw [h0, Nat.zero_mul] at hdq; omega
      · exact h0
    have hq4 : q ≤ 4 := hrelT.2
    have hdr : d + 1 = (q - 1 + 1) * S := by rw [show q - 1 + 1 = q by omega]; exact hdq
    by_cases hdS : d < S
    · obtain ⟨hm, hhd⟩ := hyoung hdS
      have hq1' : q = 1 := by
        by_contra hne
        have : 2 * S ≤ q * S := Nat.mul_le_mul_right S (by omega)
        omega
      refine workerAt_release hS hjobs hn hdr (by omega) hbase hfault htext hbeg
        (by rw [hm]; decide) ?_
      rw [hhd]
      congr 1
      rw [hq1', Nat.one_mul] at hdq
      omega
    · obtain ⟨r', hr'4, hr'1, hr'2, hph⟩ := hold (by omega)
      have hr'q : r' + 1 < q := mul_lt_of (show (r' + 1) * S < q * S by omega)
      have hr'2' : d < (r' + 2) * S := by
        rcases hr'2 with h2 | h3
        · exact h2
        · omega
      have hqr : q ≤ r' + 2 := mul_le_of hS (by omega)
      have hqr' : q = r' + 2 := by omega
      have he : d - (r' + 1) * S = S - 1 := by
        have : (r' + 2) * S = (r' + 1) * S + S := by ring
        rw [hqr'] at hdq
        omega
      have hjob := (hjobs r' hr'4 (by omega)).1
      refine workerAt_release hS hjobs hn hdr (by omega) hbase hfault htext hbeg
        (by rw [jobPhase_done hph hjob (by omega)]; decide) ?_
      rw [hph.1, he]
  · rw [decide_eq_false hrelT]
    by_cases hd1 : d + 1 < S
    · obtain ⟨hm, hhd⟩ := hyoung (by omega)
      obtain ⟨heq, hb', hf', hm', -⟩ := tick_idle hbase (by rw [hm]; decide) W[b + d]
      obtain ⟨htext', hbeg', hh'⟩ := flagTick_frame W[b + d] false s
      refine ⟨hb', by rw [hf', hfault], by rw [htext', htext, take_succ_getElem W hn]; rfl,
        by rw [hbeg', hbeg], fun _ => ⟨by rw [hm', hm], ?_⟩, fun h1 => absurd h1 (by omega)⟩
      rw [hh', hhd]
      simp
    · have hdS : S ≤ d := by
        by_contra hlt
        have hdS1 : d + 1 = S := by omega
        exact hrelT ⟨by rw [hdS1, Nat.mod_self], by rw [hdS1, Nat.div_self (by omega)]; omega⟩
      obtain ⟨r, hr4, hr1, hr2, hph⟩ := hold hdS
      have hr2' : d + 1 < (r + 2) * S ∨ r = 3 := by
        by_cases hr3 : r = 3
        · exact Or.inr hr3
        · left
          rcases hr2 with h2 | h3
          · by_contra hge
            have hlast : d + 1 = (r + 2) * S := by omega
            apply hrelT
            refine ⟨by rw [hlast, Nat.mul_mod_left], ?_⟩
            rw [hlast, Nat.mul_div_cancel _ (by omega)]
            omega
          · exact absurd h3 hr3
      exact workerAt_window hjobs hn hr4 hr1 hr2' hbase hfault htext hbeg hph

/-- At the end of a stage's life every job is done: the worker is waiting. -/
theorem ready_of_end {W : List (Fin 2)} {N : ℕ → ℕ} {b S : ℕ} {s : WorkerState}
    (hS : 1 ≤ S) (hjobs : StageJobs W N b S) (hn : b + (6 * S - 1) ≤ W.length)
    (h : WorkerAt W N b S (6 * S - 1) s) : Ready W (b + (6 * S - 1)) s := by
  obtain ⟨hbase, hfault, htext, -, -, hold⟩ := h
  obtain ⟨r, hr4, hr1, hr2, hph⟩ := hold (by omega)
  have hr3 : r = 3 := by
    rcases hr2 with h2 | h3
    · by_contra hne
      have : (r + 2) * S ≤ 4 * S := Nat.mul_le_mul_right S (by omega)
      omega
    · exact h3
  subst hr3
  have hjob := (hjobs 3 (by omega) (by omega)).1
  exact ⟨hbase, hfault, by rw [jobPhase_done hph hjob (by omega)]; decide, htext⟩

/-! ## Both flag workers along the run -/

theorem getElem_eq_of_eq {W : List (Fin 2)} {i j : ℕ} (hij : i = j) (hi : i < W.length)
    (hj : j < W.length) : W[i] = W[j] := by
  subst hij; rfl

theorem seg_length {W : List (Fin 2)} {b S r : ℕ} (h : b + (r + 1) * S ≤ W.length) :
    (seg W b S r).length = (r + 1) * S := by
  unfold seg
  rw [List.length_take, List.length_drop]
  omega

/-- The job step counts for every stage, from the per-job promise. -/
theorem exists_jobSteps
    (hjob : ∀ (y : List (Fin 2)) (i r : ℕ), r < 4 → y.length = (r + 1) * 2 ^ i →
      JobHalts y (2 ^ i) r)
    (W : List (Fin 2)) :
    ∃ N : ℕ → ℕ → ℕ, ∀ j, 1 ≤ j → StageJobs W (N j) (2 ^ j) (2 ^ (j - 1)) := by
  have hex : ∀ j r : ℕ, ∃ Nr : ℕ, 1 ≤ j → r < 4 → 2 ^ j + (r + 1) * 2 ^ (j - 1) ≤ W.length →
      Nr < 32768 * 2 ^ (j - 1) ∧ ∃ V, iterFlags Nr (jobVM W (2 ^ j) (2 ^ (j - 1)) r) = some V ∧
        V.flagsDone ∧ V.flags.reverse = jobBits W (2 ^ j) (2 ^ (j - 1)) r := by
    intro j r
    by_cases hc : 1 ≤ j ∧ r < 4 ∧ 2 ^ j + (r + 1) * 2 ^ (j - 1) ≤ W.length
    · obtain ⟨Nr, V, h1, h2, h3, h4⟩ :=
        hjob (seg W (2 ^ j) (2 ^ (j - 1)) r) (j - 1) r hc.2.1 (seg_length hc.2.2)
      exact ⟨Nr, fun _ _ _ => ⟨h1, V, h2, h3, by rw [jobBits_eq]; exact h4⟩⟩
    · exact ⟨0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc⟩
  choose N hN using hex
  exact ⟨N, fun j hj r hr hlen => hN j r hj hr hlen⟩

section Global

variable {Wm : Type} {mOps : WorkerOps Wm} {m0 : Wm}

/-- The flag workers after `n` letters, `2^k ≤ n < 2^(k+1)`: the young stage's worker (slot
`idx (k-1)`), the old stage's worker (slot `idx k`), and the slots not used yet waiting, their
stages unborn. -/
def FInv (W : List (Fin 2)) (N : ℕ → ℕ → ℕ) (k n : ℕ) (s : PalState Wm WorkerState) : Prop :=
  (1 ≤ k → WorkerAt W (N k) (2 ^ k) (2 ^ (k - 1)) (n - 2 ^ k) (s.flags (idx (k - 1)))) ∧
  (2 ≤ k → WorkerAt W (N (k - 1)) (2 ^ (k - 1)) (2 ^ (k - 2)) (n - 2 ^ (k - 1))
    (s.flags (idx k))) ∧
  (k = 0 → ∀ i, Ready W n (s.flags i) ∧ (s.stages i).alive = false) ∧
  (k = 1 → Ready W n (s.flags (idx 1)) ∧ (s.stages (idx 1)).alive = false)

theorem alive_after (s : PalState Wm WorkerState) (a : Fin 2) (i : Fin 2)
    (h : (s.stages i).alive = false) (hnb : (birthOf s && s.slot == i) = false) :
    ((tick mOps flagsOps s a).stages i).alive = false := by
  have hs := (tick_sched mOps flagsOps a s).1 i
  simp only [sched, Prod.mk.injEq] at hs
  rw [hs.2.2.1, hnb]
  exact alive_dormant h s.power

theorem finv_step {W : List (Fin 2)} {N : ℕ → ℕ → ℕ}
    (hjobs : ∀ j, 1 ≤ j → StageJobs W (N j) (2 ^ j) (2 ^ (j - 1)))
    {k n : ℕ} (hk : 2 ^ k ≤ n) (hkn : n < 2 ^ (k + 1)) (hnW : n < W.length)
    (hI : Inv k n (run mOps flagsOps m0 flagsInit (W.take n)))
    (h : FInv W N k n (run mOps flagsOps m0 flagsInit (W.take n))) :
    (n + 1 < 2 ^ (k + 1) → FInv W N k (n + 1) (run mOps flagsOps m0 flagsInit (W.take (n + 1)))) ∧
      (n + 1 = 2 ^ (k + 1) →
        FInv W N (k + 1) (n + 1) (run mOps flagsOps m0 flagsInit (W.take (n + 1)))) := by
  set s := run mOps flagsOps m0 flagsInit (W.take n) with hs
  obtain ⟨_, hready, hpow, hnb, hslot, hnew, hold⟩ := hI
  have hbirth : birthOf s = decide (n + 1 = 2 ^ (k + 1)) := by
    simp only [birthOf, hready, hnb, Bool.true_and, Nat.pred_eq_sub_one]
    by_cases he : n + 1 = 2 ^ (k + 1)
    · simp [he]; omega
    · simp [he]; omega
  have hs' := run_take_succ mOps flagsOps m0 flagsInit W hnW
  have hflag : ∀ i, (run mOps flagsOps m0 flagsInit (W.take (n + 1))).flags i =
      flagTick W[n] (birthOf s && s.slot == i)
        (ScaWindowPal.advance (s.stages i) (birthOf s && s.slot == i) s.power).1.release
        (s.flags i) := by
    intro i; rw [hs', tick_flags]
  have halive : ∀ i, (s.stages i).alive = false → (birthOf s && s.slot == i) = false →
      ((run mOps flagsOps m0 flagsInit (W.take (n + 1))).stages i).alive = false := by
    intro i hi hnbi; rw [hs']; exact alive_after s W[n] i hi hnbi
  have h2k : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  -- the young stage (born at `2^k`, slot `idx (k-1)`)
  have young : 1 ≤ k →
      WorkerAt W (N k) (2 ^ k) (2 ^ (k - 1)) (n + 1 - 2 ^ k)
        ((run mOps flagsOps m0 flagsInit (W.take (n + 1))).flags (idx (k - 1))) := by
    intro hk1
    have hS : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    have hne : (birthOf s && s.slot == idx (k - 1)) = false := by
      rw [hslot]
      have := idx_succ_ne (k - 1); rw [show k - 1 + 1 = k by omega] at this
      simp [this.symm]
    have hst := hnew hk1
    have hrel := release_live (src := s.power) Nat.one_le_two_pow hst
      (Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by omega)))
    have hstep := workerAt_step (d := n - 2 ^ k) Nat.one_le_two_pow (hjobs k hk1) (by omega)
      (by omega) (h.1 hk1)
    rw [getElem_eq_of_eq (show 2 ^ k + (n - 2 ^ k) = n by omega) _ hnW] at hstep
    rw [hflag, hne, hrel, show n + 1 - 2 ^ k = n - 2 ^ k + 1 by omega]
    exact hstep
  -- the old stage (born at `2^(k-1)`, slot `idx k`), no birth
  have old : 2 ≤ k → n + 1 < 2 ^ (k + 1) →
      WorkerAt W (N (k - 1)) (2 ^ (k - 1)) (2 ^ (k - 2)) (n + 1 - 2 ^ (k - 1))
        ((run mOps flagsOps m0 flagsInit (W.take (n + 1))).flags (idx k)) := by
    intro hk2 hlt
    have hS : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    have hS1 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by rw [← pow_succ']; congr 1; omega
    have hnb0 : (birthOf s && s.slot == idx k) = false := by
      rw [hbirth]; simp; omega
    have hst := hold hk2
    have hrel := release_live (src := s.power) Nat.one_le_two_pow hst
      (Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by omega)))
    have hjk := hjobs (k - 1) (by omega)
    rw [show k - 1 - 1 = k - 2 by omega] at hjk
    have hstep := workerAt_step (d := n - 2 ^ (k - 1)) Nat.one_le_two_pow hjk (by omega)
      (by omega) (h.2.1 hk2)
    rw [getElem_eq_of_eq (show 2 ^ (k - 1) + (n - 2 ^ (k - 1)) = n by omega) _ hnW] at hstep
    rw [hflag, hnb0, hrel, show n + 1 - 2 ^ (k - 1) = n - 2 ^ (k - 1) + 1 by omega]
    exact hstep
  -- a waiting slot without birth
  have wait : ∀ i, Ready W n (s.flags i) → (s.stages i).alive = false →
      (birthOf s && s.slot == i) = false →
      Ready W (n + 1) ((run mOps flagsOps m0 flagsInit (W.take (n + 1))).flags i) ∧
        ((run mOps flagsOps m0 flagsInit (W.take (n + 1))).stages i).alive = false := by
    intro i hr ha hnbi
    refine ⟨?_, halive i ha hnbi⟩
    rw [hflag, hnbi, release_dormant ha]
    exact ready_idle hr hnW
  refine ⟨fun hlt => ?_, fun heq => ?_⟩
  · -- no birth: `1 ≤ k`
    have hnb0 : birthOf s = false := by rw [hbirth]; simp; omega
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have : k = 0 := by omega
      subst this
      simp at hk hkn
      omega
    refine ⟨fun _ => young hk1, fun hk2 => old hk2 hlt, fun h0 => absurd h0 (by omega),
      fun h1 => ?_⟩
    obtain ⟨hr, ha⟩ := h.2.2.2 h1
    exact wait _ hr ha (by rw [hnb0, Bool.false_and])
  · -- a birth into slot `idx k`
    have hnbk : (birthOf s && s.slot == idx k) = true := by rw [hbirth, hslot]; simp [heq]
    have hprev : Ready W n (s.flags (idx k)) := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · rcases Nat.lt_or_ge k 1 with hk1 | hk1
        · exact ((h.2.2.1 (by omega)) (idx k)).1
        · have hk1' : k = 1 := by omega
          have := (h.2.2.2 hk1').1
          rw [← hk1'] at this
          exact this
      · have hS1 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by rw [← pow_succ']; congr 1; omega
        have hS : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
        have hjk := hjobs (k - 1) (by omega)
        rw [show k - 1 - 1 = k - 2 by omega] at hjk
        have hw := h.2.1 hk2
        rw [show n - 2 ^ (k - 1) = 6 * 2 ^ (k - 2) - 1 by omega] at hw
        have := ready_of_end Nat.one_le_two_pow hjk (by omega) hw
        rwa [show 2 ^ (k - 1) + (6 * 2 ^ (k - 2) - 1) = n by omega] at this
    have newborn : WorkerAt W (N (k + 1)) (2 ^ (k + 1)) (2 ^ (k + 1 - 1)) (n + 1 - 2 ^ (k + 1))
        ((run mOps flagsOps m0 flagsInit (W.take (n + 1))).flags (idx (k + 1 - 1))) := by
      rw [show k + 1 - 1 = k by omega, show n + 1 - 2 ^ (k + 1) = 0 by omega, hflag, hnbk,
        release_birth, ← heq]
      exact workerAt_birth hprev hnW Nat.one_le_two_pow
    refine ⟨fun _ => newborn, fun hk2 => ?_, fun h0 => absurd h0 (by omega), fun h1 => ?_⟩
    · have hk1 : 1 ≤ k := by omega
      have e3 : idx (k + 1) = idx (k - 1) := by
        rw [show k + 1 = k - 1 + 2 by omega, idx_add_two]
      rw [show k + 1 - 1 = k by omega, show k + 1 - 2 = k - 1 by omega, e3]
      exact young hk1
    · have hk0 : k = 0 := by omega
      subst hk0
      obtain ⟨hr, ha⟩ := (h.2.2.1 rfl) (idx 1)
      exact wait _ hr ha (by rw [hslot]; simp only [Bool.and_eq_false_iff]; right; decide)

theorem finv_one (W : List (Fin 2)) (N : ℕ → ℕ → ℕ) (hW : 1 ≤ W.length) :
    FInv W N 0 1 (run mOps flagsOps m0 flagsInit (W.take 1)) := by
  have hs' := run_take_succ mOps flagsOps m0 flagsInit W (n := 0) (by omega)
  refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ i => ?_,
    fun h => absurd h (by omega)⟩
  have h0 : run mOps flagsOps m0 flagsInit (W.take 0) = initial m0 flagsInit := by simp [run]
  have hb : (birthOf (initial m0 flagsInit) && (initial m0 flagsInit).slot == i) = false := by
    simp [birthOf, initial]
  have hr : Ready W 0 flagsInit := ⟨base_initial, rfl, by decide, by simp [flagsInit, WorkerState.initial]⟩
  refine ⟨?_, ?_⟩
  · rw [hs', h0, tick_flags, hb, release_dormant (by rfl)]
    exact ready_idle hr (by omega)
  · rw [hs', h0]
    exact alive_after (initial m0 flagsInit) W[0] i rfl hb

theorem finv_run (W : List (Fin 2)) (N : ℕ → ℕ → ℕ)
    (hjobs : ∀ j, 1 ≤ j → StageJobs W (N j) (2 ^ j) (2 ^ (j - 1))) :
    ∀ n, 1 ≤ n → n ≤ W.length →
      FInv W N (Nat.log 2 n) n (run mOps flagsOps m0 flagsInit (W.take n)) := by
  intro n hn1
  induction n with
  | zero => omega
  | succ n ih =>
    intro hnW
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; exact finv_one W N hnW
    · have h := ih hpos (by omega)
      have hI := inv_run mOps flagsOps m0 flagsInit (W.take n) (by simp; omega)
      simp only [List.length_take, Nat.min_eq_left (show n ≤ W.length by omega)] at hI
      set k := Nat.log 2 n
      have hk : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by omega)
      have hkn : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
      have hstep := finv_step hjobs hk hkn (by omega) hI h
      rcases Nat.lt_or_ge (n + 1) (2 ^ (k + 1)) with hlt | hge
      · rw [show Nat.log 2 (n + 1) = k from Nat.log_eq_of_pow_le_of_lt_pow (by omega) hlt]
        exact hstep.1 hlt
      · have heq : n + 1 = 2 ^ (k + 1) := by omega
        rw [show Nat.log 2 (n + 1) = k + 1 by rw [heq, Nat.log_pow (by norm_num)]]
        exact hstep.2 heq

/-- The worker of the stage born at `2^j` during its life, from the run invariant. -/
theorem workerAt_run (W : List (Fin 2)) (N : ℕ → ℕ → ℕ)
    (hjobs : ∀ j, 1 ≤ j → StageJobs W (N j) (2 ^ j) (2 ^ (j - 1))) {j n : ℕ} (hj : 1 ≤ j)
    (hjn : 2 ^ j ≤ n) (hn4 : n < 2 ^ (j + 2)) (hnW : n ≤ W.length) :
    WorkerAt W (N j) (2 ^ j) (2 ^ (j - 1)) (n - 2 ^ j)
      ((run mOps flagsOps m0 flagsInit (W.take n)).flags (idx (j - 1))) := by
  have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow hjn
  have h := finv_run (mOps := mOps) (m0 := m0) W N hjobs n hn1 hnW
  rcases Nat.lt_or_ge n (2 ^ (j + 1)) with hlt | hge
  · rw [show Nat.log 2 n = j from Nat.log_eq_of_pow_le_of_lt_pow hjn hlt] at h
    exact h.1 hj
  · rw [show Nat.log 2 n = j + 1 from Nat.log_eq_of_pow_le_of_lt_pow hge hn4] at h
    have hw := h.2.1 (by omega)
    rw [show j + 1 - 1 = j by omega, show j + 1 - 2 = j - 1 by omega,
      show idx (j + 1) = idx (j - 1) by rw [show j + 1 = j - 1 + 2 by omega, idx_add_two]] at hw
    exact hw

end Global

/-! ## The flag workers' promise, and no fault -/

section Final

variable {Wm : Type} (mOps : WorkerOps Wm) (m0 : Wm)

/-- **The flag workers' promise** (`ScaWindowPlumbing.FlagsContract`) for the real flag workers
on any word, from the per-job promise. -/
theorem flagsContract
    (hjob : ∀ (y : List (Fin 2)) (i r : ℕ), r < 4 → y.length = (r + 1) * 2 ^ i →
      JobHalts y (2 ^ i) r)
    (W : List (Fin 2)) : FlagsContract mOps flagsOps m0 flagsInit W := by
  obtain ⟨N, hjobs⟩ := exists_jobSteps hjob W
  refine ⟨fun j r => 2 ^ j + (r + 1) * 2 ^ (j - 1) + N j r / 32768, fun j r hj hr hR => ?_⟩
  dsimp only
  obtain ⟨hNlt, V, hV, hVd, hVbits⟩ := hjobs j hj r hr hR
  have hSr : 2 ^ (j - 1) ≤ (r + 1) * 2 ^ (j - 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos r)
  have hS : 2 ^ j = 2 * 2 ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
  have h4 : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
  have hSpos : 1 ≤ 2 ^ (j - 1) := Nat.one_le_two_pow
  have hr2 : (r + 2) * 2 ^ (j - 1) = (r + 1) * 2 ^ (j - 1) + 2 ^ (j - 1) := by ring
  have hr5 : (r + 2) * 2 ^ (j - 1) ≤ 5 * 2 ^ (j - 1) := Nat.mul_le_mul_right _ (by omega)
  -- the worker between the release and the capture
  have hat : ∀ n, 2 ^ j + (r + 1) * 2 ^ (j - 1) ≤ n →
      n ≤ 2 ^ j + (r + 1) * 2 ^ (j - 1) + N j r / 32768 → n ≤ W.length →
      JobPhase W (N j) (2 ^ j) (2 ^ (j - 1)) r (n - (2 ^ j + (r + 1) * 2 ^ (j - 1)))
        ((run mOps flagsOps m0 flagsInit (W.take n)).flags (idx (j - 1))) := by
    intro n hRn hnc hnW
    have hw := workerAt_run W N hjobs (mOps := mOps) (m0 := m0) hj (by omega) (by omega) hnW
    obtain ⟨-, -, -, -, -, hold⟩ := hw
    obtain ⟨r', hr'4, hr'1, hr'2, hph⟩ := hold (by omega)
    have hlt : (r' + 1) * 2 ^ (j - 1) < (r + 2) * 2 ^ (j - 1) := by omega
    have h1 : r' + 1 < r + 2 := mul_lt_of hlt
    have h2 : r ≤ r' := by
      rcases hr'2 with h3 | h3
      · have := mul_lt_of (show (r + 1) * 2 ^ (j - 1) < (r' + 2) * 2 ^ (j - 1) by omega)
        omega
      · omega
    have hrr : r' = r := by omega
    subst hrr
    have he : n - 2 ^ j - (r' + 1) * 2 ^ (j - 1) = n - (2 ^ j + (r' + 1) * 2 ^ (j - 1)) := by
      omega
    rw [he] at hph
    exact hph
  refine ⟨by omega, by omega, fun n hRn hnc hnW => ?_, fun hcW => ?_⟩
  · have hph := hat n hRn hnc hnW
    show modeDone _ = true ↔ _
    by_cases hrun : n - (2 ^ j + (r + 1) * 2 ^ (j - 1)) < N j r / 32768
    · rw [modeDone, (hph.2.1 hrun).1]
      simp
      omega
    · rw [modeDone, (hph.2.2 (by omega)).1]
      simp
      omega
  · have hph := hat _ (by omega) le_rfl hcW
    show ((run mOps flagsOps m0 flagsInit (W.take _)).flags (idx (j - 1))).flags = _
    exact (hph.2.2 (by omega)).2

/-- **The flag workers never fault**, on any input. -/
theorem flags_never_fault
    (hjob : ∀ (y : List (Fin 2)) (i r : ℕ), r < 4 → y.length = (r + 1) * 2 ^ i →
      JobHalts y (2 ^ i) r)
    (u : List (Fin 2)) (i : Fin 2) :
    flagsOps.faulted ((run mOps flagsOps m0 flagsInit u).flags i) = false := by
  obtain ⟨N, hjobs⟩ := exists_jobSteps hjob u
  show ((run mOps flagsOps m0 flagsInit u).flags i).fault = false
  rcases Nat.eq_zero_or_pos u.length with h0 | hpos
  · rw [List.length_eq_zero_iff.mp h0]
    rfl
  · have h := finv_run (mOps := mOps) (m0 := m0) u N hjobs u.length hpos le_rfl
    rw [List.take_length] at h
    set k := Nat.log 2 u.length
    rcases Nat.lt_or_ge k 1 with hk1 | hk1
    · exact (((h.2.2.1 (by omega)) i).1).2.1
    · rcases fin2_cover k hk1 i with hi | hi
      · rw [hi]
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · have hk1' : k = 1 := by omega
          have := (h.2.2.2 hk1').1
          rw [← hk1'] at this
          exact this.2.1
        · exact (h.2.1 hk2).2.1
      · rw [hi]
        exact (h.1 hk1).2.1

end Final

end PalPeg.ScaFlagsLife
