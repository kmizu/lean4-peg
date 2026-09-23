import PalPeg.ScaMatcherLife

/-!
# Matcher lives with any start orientation

`ScaMatcherLife` starts every life's ghost orientation at `startOrient` (only `Origin` reversed).
The orientation is a ghost: `Link` only reads it on the readers live at the current row, and at
the start row only `Origin` and `Tail` are live. So a life may start from any `ρ₀` with
`ρ₀ "Origin" = true` and `ρ₀ "Tail" = false` (e.g. with the decomposition heads already reversed
from birth).

* `revAgree_congr`, `link_congr`: `Link W ρ s v` only depends on `ρ` on `readersAt s.pc`.
* `start_link'`, `tick_birth'`: `start` / a birth tick, linked with orientation `ρ₀`.
* `lifeIn'`, `lifeOut'` (from `(matchInitial x startCtl, ρ₀)`), `LifeSafe'`; their head VMs do not
  depend on `ρ₀`: `lifeOut'_fst : (lifeOut' ρ₀ x T).map Prod.fst = lifeVM x T`, `lifeIn'_fst`.
* `ScheduledLivesSafe' ρ₀` for a start orientation chosen per pattern
  (`ρ₀ : List (Fin 2) → String → Bool`, `StartOrients ρ₀`), and the results of `ScaMatcherLife`
  from it: `slotInv'_run`, `matcher_faulted_run'`, `answering_matcher'`, `answering_output'`
  (the last one states the output on `lifeIn`/`lifeVM`, independent of `ρ₀`).
* `scheduledLivesSafe'_of_fixed`: a single `ρ₀` for all patterns.
-/

set_option autoImplicit false

namespace PalPeg.ScaMatcherLife

open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWindowWorker PalPeg.ScaWorkerCoroutine
  PalPeg.ScaHeadVM PalPeg.ScaHeadGen PalPeg.ScaWorkerLink PalPeg.ScaWindowPal
  PalPeg.ScaWindowSchedule

/-! ## The orientation of a link only matters on the live readers -/

theorem revAgree_congr {L : List String} {s : WorkerState} {ρ ρ' : String → Bool}
    (h : RevAgree spec L s ρ) (hagree : ∀ x ∈ L, ρ x = ρ' x) : RevAgree spec L s ρ' := by
  intro x hx i hc
  rw [h x hx i hc]
  exact hagree x hx

theorem link_congr {W : ℕ} {ρ ρ' : String → Bool} {s : WorkerState} {v : HVM}
    (hlink : Link W ρ s v) (hagree : ∀ x ∈ readersAt s.pc, ρ x = ρ' x) : Link W ρ' s v :=
  { hlink with orient := revAgree_congr hlink.orient hagree }

/-- A start orientation: `Origin` reversed, `Tail` forward (the heads live at the start row). -/
def StartOrient (ρ₀ : String → Bool) : Prop := ρ₀ "Origin" = true ∧ ρ₀ "Tail" = false

theorem startOrient_startOrient : StartOrient startOrient := ⟨by decide, by decide⟩

theorem start_pc (s : WorkerState) :
    (start ScaWindowInstance.matcher true s).pc = spec.program.start := by
  rw [matcher_eq]
  exact (start_fields s).1

/-- **`start` with any start orientation.** -/
theorem start_link' {ρ₀ : String → Bool} (hρ₀ : StartOrient ρ₀) {s : WorkerState}
    (hready : Ready s) :
    Link s.text.length ρ₀ (start ScaWindowInstance.matcher true s)
        (matchInitial s.text.reverse startCtl) ∧
      (start ScaWindowInstance.matcher true s).fault = s.fault ∧
      (start ScaWindowInstance.matcher true s).output = s.output ∧
      (start ScaWindowInstance.matcher true s).mode = .run := by
  obtain ⟨hlink, hfault, hout, hmode⟩ := start_link readerFacts hready
  refine ⟨link_congr hlink fun x hx => ?_, hfault, hout, hmode⟩
  rw [start_pc] at hx
  rcases readerFacts.startLive x hx with rfl | rfl
  · rw [hρ₀.1]; rfl
  · rw [hρ₀.2]; rfl

/-- **A birth tick with any start orientation.** -/
theorem tick_birth' {ρ₀ : String → Bool} (hρ₀ : StartOrient ρ₀) {m : WorkerState} {v' : HVM}
    (hready : Ready m) (a : Fin 2) (hvm : iterStep spec.quantum (birthVM m a) = some v')
    (hside : ∀ i, i < spec.quantum → ∀ u, iterStep i (birthVM m a) = some u →
      StepSide (m.text.length + 1) (orientAt i (birthVM m a) ρ₀) u) :
    Link (m.text.length + 1) (orientAt spec.quantum (birthVM m a) ρ₀)
        (matcherTick true a m) v' ∧
      (matcherTick true a m).fault = m.fault ∧ (matcherTick true a m).mode = .run ∧
      (matcherTick true a m).output = decide (0 < v'.outputs.length) := by
  obtain ⟨hreadyA, hfaultA, houtA, -, htextA⟩ := ready_arrive hready a
  obtain ⟨hlinkS, hfaultS, houtS, hmodeS⟩ := start_link' hρ₀ hreadyA
  rw [htextA, List.length_append, List.length_singleton] at hlinkS
  obtain ⟨hlinkV, hfaultV, hmodeV, houtV, -⟩ := service_link readerFacts hlinkS hmodeS hvm hside
  rw [matcherTick_eq]
  refine ⟨hlinkV, ?_, hmodeV, ?_⟩
  · rw [hfaultV, hfaultS, hfaultA]
  · rw [houtV, houtS, houtA, Bool.false_or]
    rfl

/-! ## Lives from a start orientation -/

/-- The head VM a matcher is born into on the pattern `x`, with start orientation `ρ₀`. -/
def birthState' (ρ₀ : String → Bool) (x : List (Fin 2)) : Ghosted :=
  (matchInitial x startCtl, ρ₀)

/-- `lifeOut`, from the start orientation `ρ₀`. -/
def lifeOut' (ρ₀ : String → Bool) (x T : List (Fin 2)) : Option Ghosted :=
  T.foldl (fun o a => o.bind fun p => quantum (feed a p)) (quantum (birthState' ρ₀ x))

/-- `lifeIn`, from the start orientation `ρ₀`. -/
def lifeIn' (ρ₀ : String → Bool) (x T : List (Fin 2)) : Option Ghosted :=
  match T.reverse with
  | [] => some (birthState' ρ₀ x)
  | a :: R => (lifeOut' ρ₀ x R.reverse).map (feed a)

theorem lifeOut'_nil (ρ₀ : String → Bool) (x : List (Fin 2)) :
    lifeOut' ρ₀ x [] = quantum (birthState' ρ₀ x) := rfl

theorem lifeOut'_append (ρ₀ : String → Bool) (x T : List (Fin 2)) (a : Fin 2) :
    lifeOut' ρ₀ x (T ++ [a]) = (lifeOut' ρ₀ x T).bind fun p => quantum (feed a p) := by
  unfold lifeOut'
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem lifeIn'_nil (ρ₀ : String → Bool) (x : List (Fin 2)) :
    lifeIn' ρ₀ x [] = some (birthState' ρ₀ x) := rfl

theorem lifeIn'_append (ρ₀ : String → Bool) (x T : List (Fin 2)) (a : Fin 2) :
    lifeIn' ρ₀ x (T ++ [a]) = (lifeOut' ρ₀ x T).map (feed a) := by
  unfold lifeIn'
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
  simp only [List.reverse_reverse]

theorem lifeOut'_eq_bind (ρ₀ : String → Bool) (x T : List (Fin 2)) :
    lifeOut' ρ₀ x T = (lifeIn' ρ₀ x T).bind quantum := by
  induction T using List.reverseRecOn with
  | nil => rw [lifeOut'_nil, lifeIn'_nil, Option.bind_some]
  | append_singleton T a _ =>
    rw [lifeOut'_append, lifeIn'_append]
    cases lifeOut' ρ₀ x T with
    | none => rfl
    | some p => rw [Option.bind_some, Option.map_some, Option.bind_some]

/-- **The head VMs of a life do not depend on the start orientation.** -/
theorem lifeOut'_fst (ρ₀ : String → Bool) (x T : List (Fin 2)) :
    (lifeOut' ρ₀ x T).map Prod.fst = lifeVM x T := by
  induction T using List.reverseRecOn with
  | nil =>
    rw [lifeOut'_nil, map_fst_quantum, lifeVM_nil]
    rfl
  | append_singleton T a ih =>
    rw [lifeOut'_append, lifeVM_append, ← ih]
    cases lifeOut' ρ₀ x T with
    | none => rfl
    | some p =>
      rw [Option.bind_some, map_fst_quantum, Option.map_some, Option.bind_some]
      rfl

theorem lifeIn'_fst (ρ₀ : String → Bool) (x T : List (Fin 2)) :
    (lifeIn' ρ₀ x T).map Prod.fst = (lifeIn x T).map Prod.fst := by
  induction T using List.reverseRecOn with
  | nil => rfl
  | append_singleton T a _ =>
    rw [lifeIn_fst_append, lifeIn'_append, ← lifeOut'_fst ρ₀ x T]
    cases lifeOut' ρ₀ x T <;> rfl

/-- `LifeSafe`, from the start orientation `ρ₀`. -/
def LifeSafe' (ρ₀ : String → Bool) (x T : List (Fin 2)) : Prop :=
  ∀ T', T' <+: T → ∀ p, lifeIn' ρ₀ x T' = some p → QuantumSafe x.length p.2 p.1

/-- A start orientation for every pattern. -/
def StartOrients (ρ₀ : List (Fin 2) → String → Bool) : Prop := ∀ x, StartOrient (ρ₀ x)

/-- The scheduled lives are safe, each from the start orientation `ρ₀ x` of its pattern. -/
def ScheduledLivesSafe' (ρ₀ : List (Fin 2) → String → Bool) : Prop :=
  ∀ x T : List (Fin 2), (∃ j, 1 ≤ j ∧ x.length = 2 ^ j) → T.length < 3 * x.length →
    LifeSafe' (ρ₀ x) x T

/-! ## The invariant of a slot's matcher -/

/-- `LiveSince`, for lives from `ρ₀`. -/
def LiveSince' (ρ₀ : List (Fin 2) → String → Bool) (u : List (Fin 2)) (b : ℕ)
    (m : WorkerState) : Prop :=
  ∃ p0 p, lifeIn' (ρ₀ (u.take b).reverse) (u.take b).reverse (u.drop b) = some p0 ∧
    lifeOut' (ρ₀ (u.take b).reverse) (u.take b).reverse (u.drop b) = some p ∧
    Link b p.2 m p.1 ∧ m.mode = .run ∧
    m.output = decide (p0.1.outputs.length < p.1.outputs.length)

/-- `SlotInv`, for lives from `ρ₀`. -/
def SlotInv' (ρ₀ : List (Fin 2) → String → Bool) (u : List (Fin 2)) (i : Fin 2)
    (m : WorkerState) : Prop :=
  m.text = u ∧ m.fault = false ∧
    ((NeverBorn i u.length ∧ m.mode ≠ .run ∧ Ready m ∧ m.output = false) ∨
      ∃ b, LastBorn i u.length b ∧ LiveSince' ρ₀ u b m)

theorem slotInv'_initial (ρ₀ : List (Fin 2) → String → Bool) (i : Fin 2) :
    SlotInv' ρ₀ [] i ScaWindowInstance.matcherInit := by
  obtain ⟨htext, hfault, hidle⟩ := slotInv_initial i
  refine ⟨htext, hfault, ?_⟩
  rcases hidle with hidle | ⟨b, hlast, -⟩
  · exact Or.inl hidle
  · exact absurd hlast.1 (by have := born_two_le hlast.2.1; simp; omega)

theorem ready_of_slotInv' {ρ₀ : List (Fin 2) → String → Bool} {u : List (Fin 2)} {i : Fin 2}
    {m : WorkerState} (hinv : SlotInv' ρ₀ u i m) : Ready m := by
  rcases hinv.2.2 with ⟨-, -, hready, -⟩ | ⟨b, -, p0, p, -, -, hlink, -⟩
  · exact hready
  · exact ready_of_link hlink

/-- **A birth tick.** -/
theorem slotInv'_birth {ρ₀ : List (Fin 2) → String → Bool} (hρ₀ : StartOrients ρ₀)
    (hlivesSafe : ScheduledLivesSafe' ρ₀) {u : List (Fin 2)} {i : Fin 2} {m : WorkerState}
    (hinv : SlotInv' ρ₀ u i m) (a : Fin 2) (hborn : Born (u.length + 1) i) :
    SlotInv' ρ₀ (u ++ [a]) i (matcherTick true a m) := by
  have htext : m.text = u := hinv.1
  have hready := ready_of_slotInv' hinv
  set x : List (Fin 2) := (u ++ [a]).reverse with hxdef
  have hxlen : x.length = u.length + 1 := by simp [hxdef]
  obtain ⟨j, hj1, hjeq, -⟩ := id hborn
  have hsafe : LifeSafe' (ρ₀ x) x [] :=
    hlivesSafe x [] ⟨j, hj1, by rw [hxlen, hjeq]⟩ (by simp [hxlen])
  have hq : QuantumSafe x.length (ρ₀ x) (matchInitial x startCtl) :=
    hsafe [] (List.prefix_refl _) (birthState' (ρ₀ x) x) rfl
  obtain ⟨v', hv', hquant⟩ := quantum_of_safe (p := birthState' (ρ₀ x) x) hq
  have hbirthVM : birthVM m a = matchInitial x startCtl := by
    unfold birthVM
    rw [htext]
  obtain ⟨hlink, hfault, hmode, hout⟩ := tick_birth' (hρ₀ x) hready a (v' := v')
    (by rw [hbirthVM]; exact hv')
    (by
      rw [hbirthVM, htext, ← hxlen]
      exact hq.2)
  rw [hbirthVM, htext] at hlink
  obtain ⟨htake, hdrop⟩ := take_drop_succ (u := u) a
  refine ⟨by rw [matcherTick_text, htext], by rw [hfault]; exact hinv.2.1, Or.inr ?_⟩
  refine ⟨u.length + 1, ⟨by simp, hborn, fun b' hb' _ => by simpa using hb'⟩, ?_⟩
  unfold LiveSince'
  rw [htake, hdrop, ← hxdef]
  refine ⟨birthState' (ρ₀ x) x, (v', orientAt 512 (matchInitial x startCtl) (ρ₀ x)), rfl,
    hquant, hlink, hmode, ?_⟩
  rw [hout]
  rfl

/-- **A tick without birth, idle matcher.** -/
theorem slotInv'_idle {ρ₀ : List (Fin 2) → String → Bool} {u : List (Fin 2)} {i : Fin 2}
    {m : WorkerState} (hinv : SlotInv' ρ₀ u i m) (a : Fin 2)
    (hnoBirth : ¬ Born (u.length + 1) i) (hnever : NeverBorn i u.length)
    (hidle : m.mode ≠ .run) (hready : Ready m) :
    SlotInv' ρ₀ (u ++ [a]) i (matcherTick false a m) := by
  obtain ⟨-, hreadyA, hfaultA, houtA, hmodeA⟩ := tick_idle hready hidle a
  refine ⟨by rw [matcherTick_text, hinv.1], by rw [hfaultA]; exact hinv.2.1,
    Or.inl ⟨?_, by rw [hmodeA]; exact hidle, hreadyA, houtA⟩⟩
  intro b hb hbornB
  rw [List.length_append, List.length_singleton] at hb
  rcases Nat.lt_or_ge b (u.length + 1) with hlt | hge
  · exact hnever b (by omega) hbornB
  · exact hnoBirth (by rw [show u.length + 1 = b by omega]; exact hbornB)

/-- **A tick without birth, live matcher.** -/
theorem slotInv'_live {ρ₀ : List (Fin 2) → String → Bool} (hlivesSafe : ScheduledLivesSafe' ρ₀)
    {u : List (Fin 2)} {i : Fin 2} {m : WorkerState} (hinv : SlotInv' ρ₀ u i m) (a : Fin 2)
    (hnoBirth : ¬ Born (u.length + 1) i) {b : ℕ} (hlast : LastBorn i u.length b)
    (hlive : LiveSince' ρ₀ u b m) :
    SlotInv' ρ₀ (u ++ [a]) i (matcherTick false a m) := by
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
  have hsafe : LifeSafe' (ρ₀ x) x (T ++ [a]) :=
    hlivesSafe x (T ++ [a]) ⟨j, hj1, by rw [hxlen, hjeq]⟩ hTlen
  have hinA : lifeIn' (ρ₀ x) x (T ++ [a]) = some (feed a p) := by
    rw [lifeIn'_append, hout]
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
  · unfold LiveSince'
    rw [htake, hdrop, ← hxdef]
    have houtA' : lifeOut' (ρ₀ x) x (T ++ [a]) =
        some (v', orientAt 512 (p.1.append a) p.2) := by
      rw [lifeOut'_append, hout, Option.bind_some]
      exact hquant
    refine ⟨feed a p, (v', orientAt 512 (p.1.append a) p.2), hinA, houtA', hlinkA, hmodeA, ?_⟩
    rw [houtA]
    rfl

/-- **One controller tick.** -/
theorem slotInv'_tick {ρ₀ : List (Fin 2) → String → Bool} (hρ₀ : StartOrients ρ₀)
    (hlivesSafe : ScheduledLivesSafe' ρ₀) {u : List (Fin 2)} {i : Fin 2} {m : WorkerState}
    (hinv : SlotInv' ρ₀ u i m) (a : Fin 2) (birth : Bool)
    (hbirth : birth = true ↔ Born (u.length + 1) i) :
    SlotInv' ρ₀ (u ++ [a]) i (matcherTick birth a m) := by
  cases birth
  · have hnoBirth : ¬ Born (u.length + 1) i := fun h => by simpa using hbirth.mpr h
    rcases hinv.2.2 with ⟨hnever, hidle, hready, -⟩ | ⟨b, hlast, hlive⟩
    · exact slotInv'_idle hinv a hnoBirth hnever hidle hready
    · exact slotInv'_live hlivesSafe hinv a hnoBirth hlast hlive
  · exact slotInv'_birth hρ₀ hlivesSafe hinv a (hbirth.mp rfl)

/-! ## The controller run -/

/-- **The lives of the real matchers**, from start orientations `ρ₀`. -/
theorem slotInv'_run {ρ₀ : List (Fin 2) → String → Bool} (hρ₀ : StartOrients ρ₀)
    (hlivesSafe : ScheduledLivesSafe' ρ₀) {Wf : Type} (fOps : WorkerOps Wf) (f0 : Wf)
    (u : List (Fin 2)) (i : Fin 2) :
    SlotInv' ρ₀ u i
      ((run ScaWindowInstance.matcherOps fOps ScaWindowInstance.matcherInit f0 u).matchers i) := by
  induction u using List.reverseRecOn with
  | nil => exact slotInv'_initial ρ₀ i
  | append_singleton u a ih =>
    rw [run_append, tick_matchers]
    exact slotInv'_tick hρ₀ hlivesSafe ih a _
      (birth_iff ScaWindowInstance.matcherOps fOps ScaWindowInstance.matcherInit f0 u i)

/-- **No matcher ever faults.** -/
theorem matcher_faulted_run' {ρ₀ : List (Fin 2) → String → Bool} (hρ₀ : StartOrients ρ₀)
    (hlivesSafe : ScheduledLivesSafe' ρ₀) {Wf : Type} (fOps : WorkerOps Wf) (f0 : Wf)
    (u : List (Fin 2)) (i : Fin 2) :
    ScaWindowInstance.matcherOps.faulted
      ((run ScaWindowInstance.matcherOps fOps ScaWindowInstance.matcherInit f0 u).matchers i) =
        false := by
  rw [matcherOps_faulted]
  exact (slotInv'_run hρ₀ hlivesSafe fOps f0 u i).2.1

/-- **The answering matcher**, on the lives from `ρ₀`. -/
theorem answering_matcher' {ρ₀ : List (Fin 2) → String → Bool} (hρ₀ : StartOrients ρ₀)
    (hlivesSafe : ScheduledLivesSafe' ρ₀) {Wf : Type} (fOps : WorkerOps Wf) (f0 : Wf)
    (w : List (Fin 2)) (hw : 4 ≤ w.length) :
    ∃ p0 p,
      lifeIn' (ρ₀ (w.take (PalPeg.stageOf w.length)).reverse)
          (w.take (PalPeg.stageOf w.length)).reverse (w.drop (PalPeg.stageOf w.length)) =
        some p0 ∧
      lifeOut' (ρ₀ (w.take (PalPeg.stageOf w.length)).reverse)
          (w.take (PalPeg.stageOf w.length)).reverse (w.drop (PalPeg.stageOf w.length)) =
        some p ∧
      Link (PalPeg.stageOf w.length) p.2
        ((run ScaWindowInstance.matcherOps fOps ScaWindowInstance.matcherInit f0 w).matchers
          (idx (Nat.log 2 w.length))) p.1 ∧
      ScaWindowInstance.matcherOps.output
          ((run ScaWindowInstance.matcherOps fOps ScaWindowInstance.matcherInit f0 w).matchers
            (idx (Nat.log 2 w.length))) =
        decide (p0.1.outputs.length < p.1.outputs.length) := by
  have hinv := slotInv'_run hρ₀ hlivesSafe fOps f0 w (idx (Nat.log 2 w.length))
  have hlastA := lastBorn_answering hw
  rw [matcherOps_output]
  rcases hinv.2.2 with ⟨hnever, -, -, -⟩ | ⟨b, hlast, hlive⟩
  · exact absurd hnever (not_neverBorn_of_lastBorn hlastA)
  · rw [lastBorn_unique hlast hlastA] at hlive
    obtain ⟨p0, p, hin, hout, hlink, -, houtput⟩ := hlive
    exact ⟨p0, p, hin, hout, hlink, houtput⟩

/-- The last quantum of a life from `ρ₀`. -/
theorem quantum_of_life' {ρ₀ : String → Bool} {x T : List (Fin 2)} {p0 p : Ghosted}
    (hin : lifeIn' ρ₀ x T = some p0) (hout : lifeOut' ρ₀ x T = some p) :
    iterStep 512 p0.1 = some p.1 ∧ p.2 = orientAt 512 p0.1 p0.2 := by
  rw [lifeOut'_eq_bind, hin, Option.bind_some, quantum_def] at hout
  obtain ⟨v', hv', hp⟩ := Option.map_eq_some_iff.mp hout
  subst hp
  exact ⟨hv', rfl⟩

/-- **The answering matcher's output, on the head VM** (independent of `ρ₀`): the same statement
as `answering_output`. -/
theorem answering_output' {ρ₀ : List (Fin 2) → String → Bool} (hρ₀ : StartOrients ρ₀)
    (hlivesSafe : ScheduledLivesSafe' ρ₀) {Wf : Type} (fOps : WorkerOps Wf) (f0 : Wf)
    (w : List (Fin 2)) (hw : 4 ≤ w.length) :
    ∃ v0 v, (lifeIn (w.take (PalPeg.stageOf w.length)).reverse
          (w.drop (PalPeg.stageOf w.length))).map Prod.fst = some v0 ∧
      lifeVM (w.take (PalPeg.stageOf w.length)).reverse (w.drop (PalPeg.stageOf w.length)) =
        some v ∧
      iterStep 512 v0 = some v ∧ v0.outputs <+: v.outputs ∧
      ScaWindowInstance.matcherOps.output
          ((run ScaWindowInstance.matcherOps fOps ScaWindowInstance.matcherInit f0 w).matchers
            (idx (Nat.log 2 w.length))) =
        decide (v0.outputs.length < v.outputs.length) := by
  obtain ⟨p0, p, hin, hout, -, houtput⟩ := answering_matcher' hρ₀ hlivesSafe fOps f0 w hw
  have hq := (quantum_of_life' hin hout).1
  refine ⟨p0.1, p.1, ?_, ?_, hq, iterStep_outputs 512 hq, houtput⟩
  · rw [← lifeIn'_fst (ρ₀ (w.take (PalPeg.stageOf w.length)).reverse), hin]
    rfl
  · rw [← lifeOut'_fst (ρ₀ (w.take (PalPeg.stageOf w.length)).reverse), hout]
    rfl

/-! ## One start orientation for every pattern -/

theorem startOrients_const {ρ₀ : String → Bool} (hρ₀ : StartOrient ρ₀) :
    StartOrients fun _ => ρ₀ := fun _ => hρ₀

/-- A single start orientation `ρ₀` whose lives are all safe. -/
theorem scheduledLivesSafe'_of_fixed {ρ₀ : String → Bool}
    (hall : ∀ x T : List (Fin 2), LifeSafe' ρ₀ x T) : ScheduledLivesSafe' fun _ => ρ₀ :=
  fun x T _ _ => hall x T

/-! ## Axiom audit -/

/-- info: 'PalPeg.ScaMatcherLife.slotInv'_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slotInv'_run

/-- info: 'PalPeg.ScaMatcherLife.matcher_faulted_run'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms matcher_faulted_run'

/-- info: 'PalPeg.ScaMatcherLife.answering_matcher'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms answering_matcher'

/-- info: 'PalPeg.ScaMatcherLife.answering_output'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms answering_output'

/-- info: 'PalPeg.ScaMatcherLife.start_link'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms start_link'

/-- info: 'PalPeg.ScaMatcherLife.lifeOut'_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifeOut'_fst

end PalPeg.ScaMatcherLife
