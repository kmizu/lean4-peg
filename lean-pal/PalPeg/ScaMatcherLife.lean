import PalPeg.ScaWorkerLink
import PalPeg.ScaWindowSchedule
import PalPeg.Stages

/-!
# The lives of the real matchers in the controller run

A stage slot's matcher is (re)started exactly at its stage's births. Between two births it runs
one service quantum (`2048` head-VM steps) per letter. This file follows the real matchers of the
controller run (`ScaWindowPal.run` with `ScaWindowInstance.matcherOps` and `matcherInit`) through
`ScaWorkerLink` and states everything about them through the head VM.

## One life

A life born on the pattern `x` (the text read so far, reversed) and then fed the letters `T`:

* `lifeIn x T` — the head VM (with its ghost orientation) at the start of the last tick's
  service quantum: `matchInitial x startCtl` with `startOrient` at the birth tick (`T = []`),
  else the previous quantum's result with the last letter appended;
* `lifeOut x T` — the same after the quantum (`2048` `stepMatch` steps, orientation moved along by
  `orientAt`); `lifeVM x T` is its head VM (`lifeVM_nil`, `lifeVM_append`);
* `LifeSafe x T` — every quantum of the life up to `T` runs `2048` steps and meets the side
  conditions `StepSide` at every step (`QuantumSafe`), with `W = x.length`.

## The schedule of births

`Born b i`: slot `i` starts its matcher at the tick that reads letter number `b`, i.e. `b = 2^j`,
`j ≥ 1`, `i = idx (j - 1)` (`birth_iff`, from `ScaWindowSchedule.inv_run`). `LastBorn i n b`:
`b` is the last such tick up to `n`; `NeverBorn i n`: there is none.

## Results

* `slotInv_run`: for every word `u` and slot `i`, the real matcher has read `u`, has not faulted,
  and is either idle (never born, `output = false`) or last born at `b` and linked
  (`ScaWorkerLink.Link b ρ`) to `lifeVM (u.take b).reverse (u.drop b)`, with
  `output = (the last quantum appended to outputs)`. Its only hypothesis is `hlivesSafe`:
  `LifeSafe x T` for patterns of length `2^j` (`j ≥ 1`) and `|T| < 3·|x|` (a slot is reborn at
  `4b`).
* `matcher_faulted_run` (no matcher ever faults), `answering_matcher` (from four letters on, the
  answering slot `idx (log₂ n)` was last born at `stageOf n`, and its output is whether the last
  quantum appended a `match` value), and the forms `…_of_all` with `∀ x T, LifeSafe x T`.
-/

set_option autoImplicit false

namespace PalPeg.ScaMatcherLife

open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWindowWorker PalPeg.ScaWorkerCoroutine
  PalPeg.ScaHeadVM PalPeg.ScaHeadGen PalPeg.ScaWorkerLink PalPeg.ScaWindowPal
  PalPeg.ScaWindowSchedule

/-! ## One life of a matcher, on the head VM -/

/-- A head VM with its ghost orientation. -/
abbrev Ghosted := HVM × (String → Bool)

/-- One service quantum: `2048` steps, the orientation carried along. -/
def quantum (p : Ghosted) : Option Ghosted :=
  (iterStep 2048 p.1).map fun v' => (v', orientAt 2048 p.1 p.2)

/-- A letter arrives. -/
def feed (a : Fin 2) (p : Ghosted) : Ghosted := (p.1.append a, p.2)

/-- The head VM a matcher is born into on the pattern `x`. -/
def birthState (x : List (Fin 2)) : Ghosted := (matchInitial x startCtl, startOrient)

/-- The head VM after the last quantum of the life born on `x` and fed `T`. -/
def lifeOut (x T : List (Fin 2)) : Option Ghosted :=
  T.foldl (fun o a => o.bind fun p => quantum (feed a p)) (quantum (birthState x))

/-- The head VM at the start of the last quantum of that life. -/
def lifeIn (x T : List (Fin 2)) : Option Ghosted :=
  match T.reverse with
  | [] => some (birthState x)
  | a :: R => (lifeOut x R.reverse).map (feed a)

/-- The head VM of `lifeOut`. -/
def lifeVM (x T : List (Fin 2)) : Option HVM := (lifeOut x T).map Prod.fst

theorem lifeOut_nil (x : List (Fin 2)) : lifeOut x [] = quantum (birthState x) := rfl

theorem lifeOut_append (x T : List (Fin 2)) (a : Fin 2) :
    lifeOut x (T ++ [a]) = (lifeOut x T).bind fun p => quantum (feed a p) := by
  unfold lifeOut
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem lifeIn_nil (x : List (Fin 2)) : lifeIn x [] = some (birthState x) := rfl

theorem lifeIn_append (x T : List (Fin 2)) (a : Fin 2) :
    lifeIn x (T ++ [a]) = (lifeOut x T).map (feed a) := by
  unfold lifeIn
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
  simp only [List.reverse_reverse]

theorem quantum_def (p : Ghosted) :
    quantum p = (iterStep 2048 p.1).map fun v' => (v', orientAt 2048 p.1 p.2) := rfl

theorem map_fst_quantum (p : Ghosted) : (quantum p).map Prod.fst = iterStep 2048 p.1 := by
  rw [quantum_def]
  generalize iterStep 2048 p.1 = o
  cases o with
  | none => rfl
  | some v => rfl

/-- The quantum after `lifeIn` gives `lifeOut`. -/
theorem lifeOut_eq_bind (x T : List (Fin 2)) : lifeOut x T = (lifeIn x T).bind quantum := by
  induction T using List.reverseRecOn with
  | nil => rw [lifeOut_nil, lifeIn_nil, Option.bind_some]
  | append_singleton T a _ =>
    rw [lifeOut_append, lifeIn_append]
    cases lifeOut x T with
    | none => rfl
    | some p => rw [Option.bind_some, Option.map_some, Option.bind_some]

/-- The birth tick: `arrive`, `start`, `service`. -/
theorem lifeVM_nil (x : List (Fin 2)) : lifeVM x [] = iterStep 2048 (matchInitial x startCtl) := by
  unfold lifeVM
  rw [lifeOut_nil, map_fst_quantum]
  rfl

/-- A later tick: `arrive a`, `service`. -/
theorem lifeVM_append (x T : List (Fin 2)) (a : Fin 2) :
    lifeVM x (T ++ [a]) = (lifeVM x T).bind fun v => iterStep 2048 (v.append a) := by
  unfold lifeVM
  rw [lifeOut_append]
  cases lifeOut x T with
  | none => rfl
  | some p =>
    rw [Option.bind_some, Option.map_some, Option.bind_some, map_fst_quantum]
    rfl

/-! ## Safe lives -/

/-- One quantum from `v` with orientations `ρ` runs its `2048` steps and meets the side conditions
at every step (the hypotheses of `ScaWorkerLink.service_link`). -/
def QuantumSafe (W : ℕ) (ρ : String → Bool) (v : HVM) : Prop :=
  (iterStep 2048 v).isSome ∧ SideRun W ρ 2048 v

/-- Every quantum of the life born on `x` and fed `T` (up to and including `T`'s last letter) is
safe, with `W = x.length`. -/
def LifeSafe (x T : List (Fin 2)) : Prop :=
  ∀ T', T' <+: T → ∀ p, lifeIn x T' = some p → QuantumSafe x.length p.2 p.1

theorem quantum_of_safe {W : ℕ} {p : Ghosted} (h : QuantumSafe W p.2 p.1) :
    ∃ v', iterStep 2048 p.1 = some v' ∧ quantum p = some (v', orientAt 2048 p.1 p.2) := by
  obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp h.1
  refine ⟨v', hv', ?_⟩
  unfold quantum
  rw [hv']
  rfl

/-! ## The schedule of births -/

/-- Slot `i` starts its matcher at the tick that reads letter number `b`. -/
def Born (b : ℕ) (i : Fin 2) : Prop := ∃ j, 1 ≤ j ∧ b = 2 ^ j ∧ idx (j - 1) = i

/-- `b` is the last tick up to `n` at which slot `i` starts its matcher. -/
def LastBorn (i : Fin 2) (n b : ℕ) : Prop :=
  b ≤ n ∧ Born b i ∧ ∀ b', b' ≤ n → Born b' i → b' ≤ b

/-- Slot `i` has not started its matcher in the first `n` ticks. -/
def NeverBorn (i : Fin 2) (n : ℕ) : Prop := ∀ b, b ≤ n → ¬ Born b i

theorem born_two_le {b : ℕ} {i : Fin 2} (h : Born b i) : 2 ≤ b := by
  obtain ⟨j, hj, rfl, -⟩ := h
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj

/-- A slot is reborn four times later. -/
theorem born_four_mul {b : ℕ} {i : Fin 2} (h : Born b i) : Born (4 * b) i := by
  obtain ⟨j, hj, rfl, hidx⟩ := h
  refine ⟨j + 2, by omega, by ring, ?_⟩
  rw [show j + 2 - 1 = (j - 1) + 2 by omega, idx_add_two]
  exact hidx

theorem pow_eq_pow_of_bounds {j k n : ℕ} (hk : 2 ^ k ≤ n) (hn : n < 2 ^ (k + 1))
    (hj : n + 1 = 2 ^ j) : j = k + 1 := by
  have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have h1 : k < j := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp (by omega)
  have h2 : j ≤ k + 1 := (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp (by omega)
  omega

section Schedule

variable {Wm Wf : Type} (mOps : WorkerOps Wm) (fOps : WorkerOps Wf) (m0 : Wm) (f0 : Wf)

/-- **The births of the controller run.** The tick reading letter number `|u| + 1` starts the
matcher of slot `i` exactly when `Born (|u| + 1) i`. -/
theorem birth_iff (u : List (Fin 2)) (i : Fin 2) :
    (birthOf (run mOps fOps m0 f0 u) && (run mOps fOps m0 f0 u).slot == i) = true ↔
      Born (u.length + 1) i := by
  rcases Nat.eq_zero_or_pos u.length with h0 | hpos
  · rw [List.length_eq_zero_iff.mp h0]
    constructor
    · intro h
      have h' : birthOf (initial m0 f0 : PalState Wm Wf) = true := by
        simp only [Bool.and_eq_true] at h
        exact h.1
      simp [birthOf, initial] at h'
    · intro h
      have := born_two_le h
      simp at this
  · obtain ⟨-, hready, -, hnb, hslot, -, -⟩ := inv_run mOps fOps m0 f0 u hpos
    set n := u.length with hndef
    set k := Nat.log 2 n with hkdef
    have hk : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by omega)
    have hn : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    rw [birthOf, hready, hnb, hslot]
    simp only [Bool.true_and, Bool.and_eq_true, beq_iff_eq, Nat.pred_eq_sub_one]
    constructor
    · rintro ⟨hb, hi⟩
      refine ⟨k + 1, by omega, by omega, ?_⟩
      rw [show k + 1 - 1 = k by omega]
      exact hi
    · rintro ⟨j, hj1, hjeq, hidx⟩
      have hjk := pow_eq_pow_of_bounds hk hn hjeq
      subst hjk
      refine ⟨by omega, ?_⟩
      rw [show k + 1 - 1 = k by omega] at hidx
      exact hidx

end Schedule

/-- **From four letters on, the answering slot was last born at `stageOf n`.** -/
theorem lastBorn_answering {n : ℕ} (hn : 4 ≤ n) :
    LastBorn (idx (Nat.log 2 n)) n (PalPeg.stageOf n) := by
  set K := Nat.log 2 n with hKdef
  have hK : 2 ^ K ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hnK : n < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hK2 : 2 ≤ K := by
    have := Nat.log_mono_right (b := 2) hn
    rwa [show Nat.log 2 4 = 2 by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.log_pow (by norm_num)]]
      at this
  have hstage : PalPeg.stageOf n = 2 ^ (K - 1) := rfl
  rw [hstage]
  refine ⟨le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hK,
    ⟨K - 1, by omega, rfl, ?_⟩, ?_⟩
  · rw [show K - 1 - 1 = K - 2 by omega, ← idx_add_two, show K - 2 + 2 = K by omega]
  · rintro b' hb' ⟨j, hj1, rfl, hidx⟩
    have hjK : j ≤ K := by
      by_contra hlt
      have : 2 ^ (K + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hjne : j ≠ K := by
      intro hjK'
      subst hjK'
      have := congrArg Fin.val hidx
      simp only [idx] at this
      omega
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem lastBorn_unique {i : Fin 2} {n b b' : ℕ} (h : LastBorn i n b) (h' : LastBorn i n b') :
    b = b' :=
  le_antisymm (h'.2.2 b h.1 h.2.1) (h.2.2 b' h'.1 h'.2.1)

theorem not_neverBorn_of_lastBorn {i : Fin 2} {n b : ℕ} (h : LastBorn i n b) :
    ¬ NeverBorn i n :=
  fun hnever => hnever b h.1 h.2.1

/-! ## The matchers in one controller tick -/

theorem stageRound_stages_other {Wm Wf : Type} (mOps : WorkerOps Wm) (fOps : WorkerOps Wf)
    (a i : Fin 2) (s : PalState Wm Wf) (j : Fin 2) (hj : j ≠ i) :
    (stageRound mOps fOps a i s).stages j = s.stages j := by
  unfold stageRound
  exact Function.update_of_ne hj _ _

theorem advance_birth (st : StageState) (nb : Bool) (src : ℕ) : (advance st nb src).1.birth = nb :=
  rfl

theorem two_rounds_matchers {Wf : Type} (fOps : WorkerOps Wf) (s1 : PalState WorkerState Wf)
    (a i : Fin 2) :
    (stageRound ScaWindowInstance.matcherOps fOps a 1
        (stageRound ScaWindowInstance.matcherOps fOps a 0 s1)).matchers i =
      matcherTick (s1.stages i).birth a (s1.matchers i) := by
  fin_cases i
  · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl,
      stageRound_other fOps a 1 _ 0 (by decide), stageRound_self]
  · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, stageRound_self,
      stageRound_stages_other _ _ a 0 s1 1 (by decide), stageRound_other fOps a 0 s1 1 (by decide)]

/-- **The matchers in a controller tick**: each slot's matcher arrives, starts iff its stage is
born this tick, and is serviced. -/
theorem tick_matchers {Wf : Type} (fOps : WorkerOps Wf)
    (s : PalState WorkerState Wf) (a i : Fin 2) :
    (tick ScaWindowInstance.matcherOps fOps s a).matchers i =
      matcherTick (birthOf s && s.slot == i) a (s.matchers i) := by
  unfold tick
  simp only []
  rw [two_rounds_matchers]
  congr 1
  fin_cases i <;> cases hp : s.powerReady <;> simp [advance_birth, birthOf, hp]

/-! ## The matcher reads every letter -/

theorem step_true_text (w : Worker) (s : WorkerState) :
    (step w true s).text = (effect w.spec (w.fields s.pc) true s).text := rfl

theorem mstep_text (s : WorkerState) : (mstep s).text = s.text := by
  unfold mstep
  cases decide (s.mode = .run)
  · rw [step_false, ScaWorkerCoroutine.ofSpec_spec, effect_false]
  · rw [step_true_text, ScaWorkerCoroutine.ofSpec_spec]
    exact (effect_data spec _ s).1

theorem iterate_mstep_text (n : ℕ) (s : WorkerState) : (mstep^[n] s).text = s.text := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, mstep_text]

/-- A tick appends its letter to the matcher's text, whatever else it does. -/
theorem matcherTick_text (birth : Bool) (a : Fin 2) (m : WorkerState) :
    (matcherTick birth a m).text = m.text ++ [a] := by
  rw [matcherTick_eq, service_eq, iterate_mstep_text]
  cases birth
  · rw [start_false, matcher_eq]
    exact (arrive_fields _ isFlags_eq a m).2.2.2.2.2.1
  · rw [matcher_eq, (start_fields _).2.2.2.2.1]
    exact (arrive_fields _ isFlags_eq a m).2.2.2.2.2.1

/-! ## The invariant of a slot's matcher -/

/-- The matcher `m`, last started at tick `b`, after the word `u`: linked to the life born on
`(u.take b).reverse` and fed `u.drop b`, running, and its `output` says whether the last quantum
appended to `outputs`. -/
def LiveSince (u : List (Fin 2)) (b : ℕ) (m : WorkerState) : Prop :=
  ∃ p0 p, lifeIn (u.take b).reverse (u.drop b) = some p0 ∧
    lifeOut (u.take b).reverse (u.drop b) = some p ∧ Link b p.2 m p.1 ∧ m.mode = .run ∧
    m.output = decide (p0.1.outputs.length < p.1.outputs.length)

/-- What the controller run keeps for the matcher `m` of slot `i` after the word `u`. -/
def SlotInv (u : List (Fin 2)) (i : Fin 2) (m : WorkerState) : Prop :=
  m.text = u ∧ m.fault = false ∧
    ((NeverBorn i u.length ∧ m.mode ≠ .run ∧ Ready m ∧ m.output = false) ∨
      ∃ b, LastBorn i u.length b ∧ LiveSince u b m)

/-- The safety of the lives the controller actually runs: patterns of length `2^j` (`j ≥ 1`),
fed fewer than `3·|x|` letters (the slot is reborn at `4·|x|`). -/
def ScheduledLivesSafe : Prop :=
  ∀ x T : List (Fin 2), (∃ j, 1 ≤ j ∧ x.length = 2 ^ j) → T.length < 3 * x.length → LifeSafe x T

theorem slotInv_initial (i : Fin 2) : SlotInv [] i ScaWindowInstance.matcherInit := by
  refine ⟨rfl, rfl, Or.inl ⟨?_, ?_, ready_initial, rfl⟩⟩
  · intro b hb hborn
    have := born_two_le hborn
    simp at hb
    omega
  · intro h
    cases h

theorem ready_of_slotInv {u : List (Fin 2)} {i : Fin 2} {m : WorkerState}
    (hinv : SlotInv u i m) : Ready m := by
  rcases hinv.2.2 with ⟨-, -, hready, -⟩ | ⟨b, -, p0, p, -, -, hlink, -⟩
  · exact hready
  · exact ready_of_link hlink

theorem take_drop_succ {u : List (Fin 2)} (a : Fin 2) :
    (u ++ [a]).take (u.length + 1) = u ++ [a] ∧ (u ++ [a]).drop (u.length + 1) = [] := by
  constructor
  · apply List.take_of_length_le
    simp
  · apply List.drop_of_length_le
    simp

/-- **A birth tick.** -/
theorem slotInv_birth (hlivesSafe : ScheduledLivesSafe) {u : List (Fin 2)} {i : Fin 2}
    {m : WorkerState} (hinv : SlotInv u i m) (a : Fin 2) (hborn : Born (u.length + 1) i) :
    SlotInv (u ++ [a]) i (matcherTick true a m) := by
  have htext : m.text = u := hinv.1
  have hready := ready_of_slotInv hinv
  set x : List (Fin 2) := (u ++ [a]).reverse with hxdef
  have hxlen : x.length = u.length + 1 := by simp [hxdef]
  obtain ⟨j, hj1, hjeq, -⟩ := id hborn
  have hsafe : LifeSafe x [] :=
    hlivesSafe x [] ⟨j, hj1, by rw [hxlen, hjeq]⟩ (by simp [hxlen])
  have hq : QuantumSafe x.length startOrient (matchInitial x startCtl) :=
    hsafe [] (List.prefix_refl _) (birthState x) rfl
  obtain ⟨v', hv', hquant⟩ := quantum_of_safe (p := birthState x) hq
  have hbirthVM : birthVM m a = matchInitial x startCtl := by
    unfold birthVM
    rw [htext]
  obtain ⟨hlink, hfault, hmode, hout⟩ := tick_birth readerFacts hready a (v' := v')
    (by rw [hbirthVM]; exact hv')
    (by
      rw [hbirthVM, htext, ← hxlen]
      exact hq.2)
  rw [hbirthVM, htext] at hlink
  obtain ⟨htake, hdrop⟩ := take_drop_succ (u := u) a
  refine ⟨by rw [matcherTick_text, htext], by rw [hfault]; exact hinv.2.1, Or.inr ?_⟩
  refine ⟨u.length + 1, ⟨by simp, hborn, fun b' hb' _ => by simpa using hb'⟩, ?_⟩
  unfold LiveSince
  rw [htake, hdrop, ← hxdef]
  refine ⟨birthState x, (v', orientAt 2048 (matchInitial x startCtl) startOrient), rfl, hquant,
    hlink, hmode, ?_⟩
  rw [hout]
  rfl

/-- **A tick without birth, idle matcher.** -/
theorem slotInv_idle {u : List (Fin 2)} {i : Fin 2} {m : WorkerState} (hinv : SlotInv u i m)
    (a : Fin 2) (hnoBirth : ¬ Born (u.length + 1) i) (hnever : NeverBorn i u.length)
    (hidle : m.mode ≠ .run) (hready : Ready m) :
    SlotInv (u ++ [a]) i (matcherTick false a m) := by
  obtain ⟨-, hreadyA, hfaultA, houtA, hmodeA⟩ := tick_idle hready hidle a
  refine ⟨by rw [matcherTick_text, hinv.1], by rw [hfaultA]; exact hinv.2.1,
    Or.inl ⟨?_, by rw [hmodeA]; exact hidle, hreadyA, houtA⟩⟩
  intro b hb hbornB
  rw [List.length_append, List.length_singleton] at hb
  rcases Nat.lt_or_ge b (u.length + 1) with hlt | hge
  · exact hnever b (by omega) hbornB
  · exact hnoBirth (by rw [show u.length + 1 = b by omega]; exact hbornB)

/-- A live slot is not reborn before `4b`: its life has fewer than `3b` letters. -/
theorem life_short {i : Fin 2} {n b : ℕ} (hlast : LastBorn i n b)
    (hnoBirth : ¬ Born (n + 1) i) : n + 1 < 4 * b := by
  have h4 := born_four_mul hlast.2.1
  have h2 := born_two_le hlast.2.1
  by_contra hge
  rcases Nat.lt_or_ge (4 * b) (n + 1) with hlt | hge'
  · have := hlast.2.2 (4 * b) (by omega) h4
    omega
  · exact hnoBirth (by rw [show n + 1 = 4 * b by omega]; exact h4)

/-- **A tick without birth, live matcher.** -/
theorem slotInv_live (hlivesSafe : ScheduledLivesSafe) {u : List (Fin 2)} {i : Fin 2}
    {m : WorkerState} (hinv : SlotInv u i m) (a : Fin 2) (hnoBirth : ¬ Born (u.length + 1) i)
    {b : ℕ} (hlast : LastBorn i u.length b) (hlive : LiveSince u b m) :
    SlotInv (u ++ [a]) i (matcherTick false a m) := by
  obtain ⟨p0, p, hin, hout, hlink, hrun, -⟩ := hlive
  have hbu : b ≤ u.length := hlast.1
  obtain ⟨j, hj1, hjeq, -⟩ := id hlast.2.1
  set x : List (Fin 2) := (u.take b).reverse with hxdef
  set T : List (Fin 2) := u.drop b with hTdef
  have hxlen : x.length = b := by simp [hxdef]; omega
  have hTlen : (T ++ [a]).length < 3 * x.length := by
    have := life_short hlast hnoBirth
    simp [hTdef, hxlen]
    omega
  have hsafe : LifeSafe x (T ++ [a]) :=
    hlivesSafe x (T ++ [a]) ⟨j, hj1, by rw [hxlen, hjeq]⟩ hTlen
  have hinA : lifeIn x (T ++ [a]) = some (feed a p) := by
    rw [lifeIn_append, hout]
    rfl
  have hq : QuantumSafe x.length p.2 (p.1.append a) :=
    hsafe (T ++ [a]) (List.prefix_refl _) (feed a p) hinA
  obtain ⟨v', hv', hquant⟩ := quantum_of_safe (p := feed a p) hq
  obtain ⟨hlinkA, hfaultA, hmodeA, houtA, -⟩ := tick_run readerFacts hlink hrun a hv'
    (by rw [← hxlen]; exact hq.2)
  have htake : (u ++ [a]).take b = u.take b := List.take_append_of_le_length hbu
  have hdrop : (u ++ [a]).drop b = T ++ [a] := List.drop_append_of_le_length hbu
  refine ⟨by rw [matcherTick_text, hinv.1], by rw [hfaultA]; exact hinv.2.1, Or.inr ⟨b, ?_, ?_⟩⟩
  · refine ⟨by simp; omega, hlast.2.1, fun b' hb' hbornB => ?_⟩
    rw [List.length_append, List.length_singleton] at hb'
    rcases Nat.lt_or_ge b' (u.length + 1) with hlt | hge
    · exact hlast.2.2 b' (by omega) hbornB
    · exact absurd (by rw [show u.length + 1 = b' by omega]; exact hbornB) hnoBirth
  · unfold LiveSince
    rw [htake, hdrop, ← hxdef]
    have houtA' : lifeOut x (T ++ [a]) = some (v', orientAt 2048 (p.1.append a) p.2) := by
      rw [lifeOut_append, hout, Option.bind_some]
      exact hquant
    refine ⟨feed a p, (v', orientAt 2048 (p.1.append a) p.2), hinA, houtA', hlinkA, hmodeA, ?_⟩
    rw [houtA]
    rfl

/-- **One controller tick** keeps the invariant of every slot's matcher. -/
theorem slotInv_tick (hlivesSafe : ScheduledLivesSafe) {u : List (Fin 2)} {i : Fin 2}
    {m : WorkerState} (hinv : SlotInv u i m) (a : Fin 2) (birth : Bool)
    (hbirth : birth = true ↔ Born (u.length + 1) i) :
    SlotInv (u ++ [a]) i (matcherTick birth a m) := by
  cases birth
  · have hnoBirth : ¬ Born (u.length + 1) i := fun h => by simpa using hbirth.mpr h
    rcases hinv.2.2 with ⟨hnever, hidle, hready, -⟩ | ⟨b, hlast, hlive⟩
    · exact slotInv_idle hinv a hnoBirth hnever hidle hready
    · exact slotInv_live hlivesSafe hinv a hnoBirth hlast hlive
  · exact slotInv_birth hlivesSafe hinv a (hbirth.mp rfl)

/-! ## The controller run -/

/-- **The lives of the real matchers.** After any word `u`, the matcher of slot `i` in the real
controller run has read `u`, has not faulted, and is either idle and never started (`output =
false`) or was last started at the birth tick `b` and is linked to the life born on
`(u.take b).reverse` and fed `u.drop b`, its `output` saying whether the last quantum appended to
`outputs`. -/
theorem slotInv_run (hlivesSafe : ScheduledLivesSafe) {Wf : Type} (fOps : WorkerOps Wf)
    (f0 : Wf) (u : List (Fin 2)) (i : Fin 2) :
    SlotInv u i
      ((run ScaWindowInstance.matcherOps fOps ScaWindowInstance.matcherInit f0 u).matchers i) := by
  induction u using List.reverseRecOn with
  | nil => exact slotInv_initial i
  | append_singleton u a ih =>
    rw [run_append, tick_matchers]
    exact slotInv_tick hlivesSafe ih a _
      (birth_iff ScaWindowInstance.matcherOps fOps ScaWindowInstance.matcherInit f0 u i)

/-- **No matcher ever faults** (the matcher half of `hworkers`). -/
theorem matcher_faulted_run (hlivesSafe : ScheduledLivesSafe) {Wf : Type} (fOps : WorkerOps Wf)
    (f0 : Wf) (u : List (Fin 2)) (i : Fin 2) :
    ScaWindowInstance.matcherOps.faulted
      ((run ScaWindowInstance.matcherOps fOps ScaWindowInstance.matcherInit f0 u).matchers i) =
        false := by
  rw [matcherOps_faulted]
  exact (slotInv_run hlivesSafe fOps f0 u i).2.1

/-- **The answering matcher.** From four letters on, the matcher of the answering slot
`idx (log₂ |w|)` was last started at `stageOf |w|` on the pattern `(w.take (stageOf |w|)).reverse`
and has been fed `w.drop (stageOf |w|)`; its output is whether the last quantum appended to
`outputs`. -/
theorem answering_matcher (hlivesSafe : ScheduledLivesSafe) {Wf : Type} (fOps : WorkerOps Wf)
    (f0 : Wf) (w : List (Fin 2)) (hw : 4 ≤ w.length) :
    ∃ p0 p,
      lifeIn (w.take (PalPeg.stageOf w.length)).reverse (w.drop (PalPeg.stageOf w.length)) =
        some p0 ∧
      lifeOut (w.take (PalPeg.stageOf w.length)).reverse (w.drop (PalPeg.stageOf w.length)) =
        some p ∧
      Link (PalPeg.stageOf w.length) p.2
        ((run ScaWindowInstance.matcherOps fOps ScaWindowInstance.matcherInit f0 w).matchers
          (idx (Nat.log 2 w.length))) p.1 ∧
      ScaWindowInstance.matcherOps.output
          ((run ScaWindowInstance.matcherOps fOps ScaWindowInstance.matcherInit f0 w).matchers
            (idx (Nat.log 2 w.length))) =
        decide (p0.1.outputs.length < p.1.outputs.length) := by
  have hinv := slotInv_run hlivesSafe fOps f0 w (idx (Nat.log 2 w.length))
  have hlastA := lastBorn_answering hw
  rw [matcherOps_output]
  rcases hinv.2.2 with ⟨hnever, -, -, -⟩ | ⟨b, hlast, hlive⟩
  · exact absurd hnever (not_neverBorn_of_lastBorn hlastA)
  · rw [lastBorn_unique hlast hlastA] at hlive
    obtain ⟨p0, p, hin, hout, hlink, -, houtput⟩ := hlive
    exact ⟨p0, p, hin, hout, hlink, houtput⟩

/-! ## Reading a life back -/

/-- The head VM before the last quantum: the fresh matcher at the birth tick. -/
theorem lifeIn_fst_nil (x : List (Fin 2)) :
    (lifeIn x []).map Prod.fst = some (matchInitial x startCtl) := rfl

/-- The head VM before the last quantum: the previous life with the last letter appended. -/
theorem lifeIn_fst_append (x T : List (Fin 2)) (a : Fin 2) :
    (lifeIn x (T ++ [a])).map Prod.fst = (lifeVM x T).map (·.append a) := by
  rw [lifeIn_append]
  unfold lifeVM
  cases lifeOut x T <;> rfl

theorem lifeVM_of_lifeOut {x T : List (Fin 2)} {p : Ghosted} (h : lifeOut x T = some p) :
    lifeVM x T = some p.1 := by
  unfold lifeVM
  rw [h]
  rfl

/-- The last quantum of a life: `2048` steps from `lifeIn` to `lifeOut`. -/
theorem quantum_of_life {x T : List (Fin 2)} {p0 p : Ghosted} (hin : lifeIn x T = some p0)
    (hout : lifeOut x T = some p) :
    iterStep 2048 p0.1 = some p.1 ∧ p.2 = orientAt 2048 p0.1 p0.2 := by
  rw [lifeOut_eq_bind, hin, Option.bind_some, quantum_def] at hout
  obtain ⟨v', hv', hp⟩ := Option.map_eq_some_iff.mp hout
  subst hp
  exact ⟨hv', rfl⟩

theorem stepMatch_outputs {v v' : HVM} (h : stepMatch v = some v') :
    v.outputs <+: v'.outputs := by
  obtain ⟨c, e, hctl, -⟩ := ScaHeadRun.stepMatch_ctl h
  obtain ⟨-, hv'⟩ := stepMatch_some hctl h
  rw [hv']
  exact List.prefix_append _ _

/-- The head VM only appends to `outputs`. -/
theorem iterStep_outputs (n : ℕ) :
    ∀ {v v' : HVM}, iterStep n v = some v' → v.outputs <+: v'.outputs := by
  induction n with
  | zero =>
    intro v v' h
    simp only [iterStep, Option.some.injEq] at h
    subst h
    exact List.prefix_refl _
  | succ n ih =>
    intro v v' h
    cases hstep : stepMatch v with
    | none =>
      rw [iterStep, hstep] at h
      cases h
    | some v1 =>
      rw [iterStep_succ_of hstep] at h
      exact (stepMatch_outputs hstep).trans (ih h)

/-- **The answering matcher's output, on the head VM**: with `x = (w.take S).reverse`,
`T = w.drop S`, `S = stageOf |w|`, the output is whether the last quantum (from `lifeIn x T`, i.e.
the fresh matcher if `T = []`, else `lifeVM x T.dropLast` with the last letter appended, to
`lifeVM x T`) appended a value to `outputs`. -/
theorem answering_output (hlivesSafe : ScheduledLivesSafe) {Wf : Type} (fOps : WorkerOps Wf)
    (f0 : Wf) (w : List (Fin 2)) (hw : 4 ≤ w.length) :
    ∃ v0 v, (lifeIn (w.take (PalPeg.stageOf w.length)).reverse
          (w.drop (PalPeg.stageOf w.length))).map Prod.fst = some v0 ∧
      lifeVM (w.take (PalPeg.stageOf w.length)).reverse (w.drop (PalPeg.stageOf w.length)) =
        some v ∧
      iterStep 2048 v0 = some v ∧ v0.outputs <+: v.outputs ∧
      ScaWindowInstance.matcherOps.output
          ((run ScaWindowInstance.matcherOps fOps ScaWindowInstance.matcherInit f0 w).matchers
            (idx (Nat.log 2 w.length))) =
        decide (v0.outputs.length < v.outputs.length) := by
  obtain ⟨p0, p, hin, hout, -, houtput⟩ := answering_matcher hlivesSafe fOps f0 w hw
  have hq := (quantum_of_life hin hout).1
  refine ⟨p0.1, p.1, by rw [hin]; rfl, lifeVM_of_lifeOut hout, hq, iterStep_outputs 2048 hq,
    houtput⟩

/-! ## With every life safe -/

theorem scheduledLivesSafe_of_all (hall : ∀ x T : List (Fin 2), LifeSafe x T) :
    ScheduledLivesSafe :=
  fun x T _ _ => hall x T

/-! ## Axiom audit -/

/-- info: 'PalPeg.ScaMatcherLife.slotInv_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slotInv_run

/-- info: 'PalPeg.ScaMatcherLife.matcher_faulted_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms matcher_faulted_run

/-- info: 'PalPeg.ScaMatcherLife.answering_matcher' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms answering_matcher

/-- info: 'PalPeg.ScaMatcherLife.answering_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms answering_output

end PalPeg.ScaMatcherLife
