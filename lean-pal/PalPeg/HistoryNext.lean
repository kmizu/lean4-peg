import PalPeg.HistoryFreeze
import PalPeg.HistoryReady

set_option autoImplicit false
namespace PalPeg.HistoryNext
open PegSeparation.RealTimeTM PalPeg.Program
variable {k : ℕ}

abbrev Control := Fin 3 ⊕ HistoryReady.Control

/-- Freeze completion starts copying automatically. Copy completion already
starts recovery automatically inside HistoryReady. No runtime word length
or externally supplied transition command is used in either handoff. -/
def machine (blank : Fin k) : StructuredMachine Unit Control (Fin k) 3 1 where
  tapeCount_pos := by decide
  blank := blank
  initial := .inl 0
  accepting := fun q => match q with
    | .inl _ => false
    | .inr p => (HistoryReady.machine blank).accepting p
  micro := fun q a σ => match q with
    | .inl p => if p = 2 then (.inr (.inl 0), fun j => (σ j, .stay)) else
        let d := (HistoryFreeze.worker blank).micro p a σ
        (.inl d.1, d.2)
    | .inr p =>
        let d := (HistoryReady.machine blank).micro p a σ
        (.inr d.1, d.2)

def run (blank : Fin k) (n : ℕ) (x : SConfig Control (Fin k) 3) :=
  (List.replicate n ()).foldl (machine blank).sRound x

def frozen (x : SConfig (Fin 3) (Fin k) 3) : SConfig Control (Fin k) 3 :=
  ⟨.inl x.state, x.tape⟩

def merging (x : SConfig HistoryReady.Control (Fin k) 3) : SConfig Control (Fin k) 3 :=
  ⟨.inr x.state, x.tape⟩

theorem run_add (blank : Fin k) (n m : ℕ) (x : SConfig Control (Fin k) 3) :
    run blank (n + m) x = run blank m (run blank n x) := by
  simp only [run, List.replicate_add, List.foldl_append]

theorem freeze_round (blank : Fin k) (x : SConfig (Fin 3) (Fin k) 3) (h : x.state ≠ 2) :
    (machine blank).sRound (frozen x) () = frozen ((HistoryFreeze.worker blank).sRound x ()) := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, frozen, h, ↓reduceIte]
  rfl

theorem switch_round (blank : Fin k) (T : Fin 3 → STape (Fin k)) :
    (machine blank).sRound (frozen ⟨2, T⟩) () = merging (HistoryReady.copy ⟨0, T⟩) := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, frozen, merging, HistoryReady.copy, ↓reduceIte]
  rfl

theorem merge_round (blank : Fin k) (x : SConfig HistoryReady.Control (Fin k) 3) :
    (machine blank).sRound (merging x) () = merging ((HistoryReady.machine blank).sRound x ()) := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, merging]
  rfl

theorem merge_run (blank : Fin k) (n : ℕ) (x : SConfig HistoryReady.Control (Fin k) 3) :
    run blank n (merging x) = merging (HistoryReady.run blank n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change run blank n ((machine blank).sRound (merging x) ()) = _
    rw [merge_round, ih]
    rfl

theorem freeze_run (blank : Fin k) (n : ℕ) (x : SConfig (Fin 3) (Fin k) 3)
    (h : ∀ i, i < n → (HistoryFreeze.run blank i x).state ≠ 2) :
    run blank n (frozen x) = frozen (HistoryFreeze.run blank n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change run blank n ((machine blank).sRound (frozen x) ()) = _
    rw [freeze_round blank x (h 0 (by omega)), ih]
    · rfl
    · intro i hi
      exact h (i + 1) (by omega)

theorem handoff (blank : Fin k) (n : ℕ) (x : SConfig (Fin 3) (Fin k) 3)
    (h : (HistoryFreeze.run blank n x).state = 2) :
    ∃ t, t ≤ n ∧ run blank (t + 1) (frozen x) =
      merging (HistoryReady.copy ⟨0, (HistoryFreeze.run blank n x).tape⟩) := by
  have hex : ∃ t, (HistoryFreeze.run blank t x).state = 2 := ⟨n, h⟩
  let t := Nat.find hex
  have ht : (HistoryFreeze.run blank t x).state = 2 := Nat.find_spec hex
  have hn : t ≤ n := Nat.find_min' hex h
  have hp : ∀ i, i < t → (HistoryFreeze.run blank i x).state ≠ 2 := by
    intro i hi
    exact Nat.find_min hex hi
  have he : HistoryFreeze.run blank n x = HistoryFreeze.run blank t x := by
    rw [show n = t + (n - t) by omega, HistoryFreeze.run_add]
    have hx : HistoryFreeze.run blank t x = ⟨2, (HistoryFreeze.run blank t x).tape⟩ := by
      rw [← ht]
    rw [hx, HistoryFreeze.done_run]
  refine ⟨t, hn, ?_⟩
  rw [run_add, freeze_run blank t x hp, he]
  have hx : HistoryFreeze.run blank t x = ⟨2, (HistoryFreeze.run blank t x).tape⟩ := by rw [← ht]
  rw [hx]
  exact switch_round blank _

theorem done_run (blank : Fin k) (n : ℕ) (T : Fin 3 → STape (Fin k)) :
    run blank n ⟨.inr (.inr (fun _ => 2)), T⟩ = ⟨.inr (.inr (fun _ => 2)), T⟩ := by
  change run blank n (merging ⟨.inr (fun _ => 2), T⟩) = _
  rw [merge_run, HistoryReady.done_run]
  rfl

/-- One complete freeze/merge/recycle pass, with no externally initiated
intermediate phase. All three output buffers meet their next-use contract. -/
theorem ready (blank : Fin k) (u v : List (Fin k)) (hu : blank ∉ u) (hv : blank ∉ v)
    (T : Fin 3 → STape (Fin k))
    (h0 : T 0 = HistoryConcat.source blank u [blank])
    (h1 : T 1 = ⟨v.reverse ++ [blank], blank, []⟩)
    (h2 : T 2 = ⟨[blank], blank, []⟩) :
    let y := run blank (2 * (u.length + v.length) + v.length + 8) (frozen ⟨0, T⟩)
    y.state = .inr (.inr (fun _ => 2)) ∧
      STape.BlankEq blank (y.tape 2) (HistoryConcat.source blank (u ++ v) [blank]) ∧
      STape.BlankEq blank (y.tape 0) ⟨[blank], blank, []⟩ ∧
      STape.BlankEq blank (y.tape 1) ⟨[blank], blank, []⟩ := by
  have hf := HistoryFreeze.frozen blank v hv (v.length + 2) (by omega) T h1
  let x := HistoryFreeze.run blank (v.length + 2) ⟨0, T⟩
  have hx : x.state = 2 := hf.1
  obtain ⟨t, ht, hh⟩ := handoff blank (v.length + 2) ⟨0, T⟩ hx
  have hA : STape.BlankEq blank (x.tape 0) (HistoryConcat.source blank u [blank]) := by
    rw [hf.2.2.1, h0]
    exact STape.BlankEq.refl _ _
  have hD : STape.BlankEq blank (x.tape 2) ⟨[blank], blank, []⟩ := by
    rw [hf.2.2.2, h2]
    exact STape.BlankEq.refl _ _
  have hc := HistoryReady.ready_padded blank u v hu hv x.tape hA hf.2.1 hD
  let r := HistoryReady.run blank (2 * (u.length + v.length) + 5) (HistoryReady.copy ⟨0, x.tape⟩)
  have hs : r.state = .inr (fun _ => 2) := hc.1
  have hr : run blank ((t + 1) + (2 * (u.length + v.length) + 5)) (frozen ⟨0, T⟩) = merging r := by
    rw [run_add, hh, merge_run]
  let d := (t + 1) + (2 * (u.length + v.length) + 5)
  let D := 2 * (u.length + v.length) + v.length + 8
  have hd : d ≤ D := by dsimp only [d, D]; omega
  have he : merging r = ⟨.inr (.inr (fun _ => 2)), r.tape⟩ := by
    change (⟨.inr r.state, r.tape⟩ : SConfig Control (Fin k) 3) = _
    rw [hs]
  have hall : run blank D (frozen ⟨0, T⟩) = merging r := by
    rw [show D = d + (D - d) by omega, run_add, hr, he, done_run]
  dsimp only [D] at hall
  simp only [hall]
  exact ⟨congrArg Sum.inr hs, hc.2⟩

/-- info: 'PalPeg.HistoryNext.ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ready

end PalPeg.HistoryNext
