import PalPeg.HistoryRecover

set_option autoImplicit false
namespace PalPeg.HistoryReady
open PegSeparation.RealTimeTM PalPeg.Program
variable {k : ℕ}

abbrev Control := Fin 3 ⊕ (Fin 3 → Fin 3)

/-- Copy completion is detected by finite control. The following tick
starts destination rewind and simultaneous recycling of both sources. -/
def machine (blank : Fin k) :
    StructuredMachine Unit Control (Fin k) 3 1 where
  tapeCount_pos := by decide
  blank := blank
  initial := .inl 0
  accepting := fun q => match q with
    | .inl _ => false
    | .inr r => decide (∀ i, r i = 2)
  micro := fun q a σ => match q with
    | .inl p => if p = 2 then (.inr (fun _ => 0), fun j => (σ j, .stay)) else
        let d := (HistoryConcat.machine blank).micro p a σ
        (.inl d.1, d.2)
    | .inr p =>
        let d := (HistoryRecover.machine blank).micro p a σ
        (.inr d.1, d.2)

def run (blank : Fin k) (n : ℕ) (x : SConfig Control (Fin k) 3) :=
  (List.replicate n ()).foldl (machine blank).sRound x

def copy (x : SConfig (Fin 3) (Fin k) 3) : SConfig Control (Fin k) 3 :=
  ⟨.inl x.state, x.tape⟩

def back (x : SConfig (Fin 3 → Fin 3) (Fin k) 3) : SConfig Control (Fin k) 3 :=
  ⟨.inr x.state, x.tape⟩

theorem run_add (blank : Fin k) (n m : ℕ) (x : SConfig Control (Fin k) 3) :
    run blank (n + m) x = run blank m (run blank n x) := by
  simp only [run, List.replicate_add, List.foldl_append]

theorem copy_round (blank : Fin k) (x : SConfig (Fin 3) (Fin k) 3) (h : x.state ≠ 2) :
    (machine blank).sRound (copy x) () = copy ((HistoryConcat.machine blank).sRound x ()) := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, copy, h, ↓reduceIte]
  rfl

theorem switch_round (blank : Fin k) (T : Fin 3 → STape (Fin k)) :
    (machine blank).sRound (copy ⟨2, T⟩) () = back ⟨fun _ => 0, T⟩ := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, copy, back, ↓reduceIte]
  rfl

theorem back_round (blank : Fin k) (x : SConfig (Fin 3 → Fin 3) (Fin k) 3) :
    (machine blank).sRound (back x) () = back ((HistoryRecover.machine blank).sRound x ()) := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, back]
  rfl

theorem back_run (blank : Fin k) (n : ℕ) (x : SConfig (Fin 3 → Fin 3) (Fin k) 3) :
    run blank n (back x) = back (HistoryRecover.run blank n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change run blank n ((machine blank).sRound (back x) ()) = _
    rw [back_round, ih]
    rfl

theorem copy_run (blank : Fin k) (n : ℕ) (x : SConfig (Fin 3) (Fin k) 3)
    (h : ∀ i, i < n → (HistoryConcat.run blank i x).state ≠ 2) :
    run blank n (copy x) = copy (HistoryConcat.run blank n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change run blank n ((machine blank).sRound (copy x) ()) = _
    rw [copy_round blank x (h 0 (by omega)), ih]
    · rfl
    · intro i hi
      exact h (i + 1) (by omega)

/-- If copying is known to be finished by n ticks, its first completion
occurs at some t≤n and the machine itself enters rewind one tick later.
The copy's absorbing done state identifies the handoff tape exactly. -/
theorem handoff (blank : Fin k) (n : ℕ) (x : SConfig (Fin 3) (Fin k) 3)
    (h : (HistoryConcat.run blank n x).state = 2) :
    ∃ t, t ≤ n ∧ run blank (t + 1) (copy x) =
      back ⟨fun _ => 0, (HistoryConcat.run blank n x).tape⟩ := by
  have hex : ∃ t, (HistoryConcat.run blank t x).state = 2 := ⟨n, h⟩
  let t := Nat.find hex
  have ht : (HistoryConcat.run blank t x).state = 2 := Nat.find_spec hex
  have hn : t ≤ n := Nat.find_min' hex h
  have hp : ∀ i, i < t → (HistoryConcat.run blank i x).state ≠ 2 := by
    intro i hi
    exact Nat.find_min hex hi
  have he : HistoryConcat.run blank n x = HistoryConcat.run blank t x := by
    rw [show n = t + (n - t) by omega, HistoryConcat.run_add]
    exact HistoryConcat.stable_done blank _ ht _
  refine ⟨t, hn, ?_⟩
  rw [run_add, copy_run blank t x hp, he]
  have hx : HistoryConcat.run blank t x = ⟨2, (HistoryConcat.run blank t x).tape⟩ := by
    rw [← ht]
  rw [hx]
  exact switch_round blank _

theorem done_round (blank : Fin k) (T : Fin 3 → STape (Fin k)) :
    (machine blank).sRound ⟨.inr (fun _ => 2), T⟩ () = ⟨.inr (fun _ => 2), T⟩ := by
  change (machine blank).sRound (back ⟨fun _ => 2, T⟩) () = _
  rw [back_round, HistoryRecover.done_round]
  rfl

theorem done_run (blank : Fin k) (n : ℕ) (T : Fin 3 → STape (Fin k)) :
    run blank n ⟨.inr (fun _ => 2), T⟩ = ⟨.inr (fun _ => 2), T⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change run blank n ((machine blank).sRound ⟨.inr (fun _ => 2), T⟩ ()) = _
    rw [done_round, ih]

/-- The linear budget prepares the merged source and simultaneously returns
both old source buffers to reusable blank frontiers. -/
theorem ready (blank : Fin k) (u v : List (Fin k)) (hu : blank ∉ u) (hv : blank ∉ v)
    (T : Fin 3 → STape (Fin k))
    (h0 : T 0 = HistoryConcat.source blank u [blank])
    (h1 : T 1 = HistoryConcat.source blank v [blank])
    (h2 : T 2 = ⟨[blank], blank, []⟩) :
    let y := run blank (2 * (u.length + v.length) + 5) (copy ⟨0, T⟩)
    y.state = .inr (fun _ => 2) ∧
      STape.BlankEq blank (y.tape 2) (HistoryConcat.source blank (u ++ v) [blank]) ∧
      STape.BlankEq blank (y.tape 0) ⟨[blank], blank, []⟩ ∧
      STape.BlankEq blank (y.tape 1) ⟨[blank], blank, []⟩ := by
  have hc := HistoryConcat.concat blank u v hu hv [blank] [blank] [blank] T h0 h1 h2
  let x := HistoryConcat.run blank (u.length + v.length + 2) ⟨0, T⟩
  have hx : x.state = 2 := hc.1
  obtain ⟨t, ht, hh⟩ := handoff blank (u.length + v.length + 2) ⟨0, T⟩ hx
  change run blank (t + 1) (copy ⟨0, T⟩) = back ⟨fun _ => 0, x.tape⟩ at hh
  have hR := HistoryRecover.recovered blank u v hu hv x.tape hc.2.2.1 hc.2.2.2 hc.2.1
  let r := HistoryRecover.run blank (u.length + v.length + 2) ⟨fun _ => 0, x.tape⟩
  have hs : r.state = fun _ => 2 := funext hR.1
  have hr : run blank ((t + 1) + (u.length + v.length + 2)) (copy ⟨0, T⟩) = back r := by
    rw [run_add, hh, back_run]
  let d := (t + 1) + (u.length + v.length + 2)
  have hd : d ≤ 2 * (u.length + v.length) + 5 := by dsimp only [d]; omega
  have he : back r = ⟨.inr (fun _ => 2), r.tape⟩ := by
    change (⟨.inr r.state, r.tape⟩ : SConfig Control (Fin k) 3) = _
    rw [hs]
  have hall : run blank (2 * (u.length + v.length) + 5) (copy ⟨0, T⟩) = back r := by
    rw [show 2 * (u.length + v.length) + 5 = d + (2 * (u.length + v.length) + 5 - d) by omega,
      run_add, hr, he, done_run]
  simp only [hall]
  exact ⟨congrArg Sum.inr hs, hR.2.2.2, hR.2.1, hR.2.2.1⟩

theorem ready_padded (blank : Fin k) (u v : List (Fin k)) (hu : blank ∉ u) (hv : blank ∉ v)
    (T : Fin 3 → STape (Fin k))
    (h0 : STape.BlankEq blank (T 0) (HistoryConcat.source blank u [blank]))
    (h1 : STape.BlankEq blank (T 1) (HistoryConcat.source blank v [blank]))
    (h2 : STape.BlankEq blank (T 2) ⟨[blank], blank, []⟩) :
    let y := run blank (2 * (u.length + v.length) + 5) (copy ⟨0, T⟩)
    y.state = .inr (fun _ => 2) ∧
      STape.BlankEq blank (y.tape 2) (HistoryConcat.source blank (u ++ v) [blank]) ∧
      STape.BlankEq blank (y.tape 0) ⟨[blank], blank, []⟩ ∧
      STape.BlankEq blank (y.tape 1) ⟨[blank], blank, []⟩ := by
  let A : Fin 3 → STape (Fin k) := Fin.cases (HistoryConcat.source blank u [blank])
    (Fin.cases (HistoryConcat.source blank v [blank]) (fun _ => ⟨[blank], blank, []⟩))
  have ha : ∀ i, STape.BlankEq blank (T i) (A i) := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hc := ready blank u v hu hv A rfl rfl rfl
  have hr := (machine blank).runFrom_blankEq (List.replicate (2 * (u.length + v.length) + 5) ())
    (show ConfigBlankEq (machine blank).blank (copy ⟨0, T⟩) (copy ⟨0, A⟩) from ⟨rfl, ha⟩)
  exact ⟨hr.1.trans hc.1, (hr.2 2).trans hc.2.1,
    (hr.2 0).trans hc.2.2.1, (hr.2 1).trans hc.2.2.2⟩

/-- info: 'PalPeg.HistoryReady.ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ready

end PalPeg.HistoryReady
