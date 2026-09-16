import PalPeg.HistoryRewind
import PalPeg.ProgramArrivalLog

set_option autoImplicit false
namespace PalPeg.HistoryFreeze
open PegSeparation.RealTimeTM PalPeg.Program
variable {k : ℕ} {Terminal : Type}

/-- Logical tape 1 is the frozen previous log. Tape 0 holds the older
readable prefix; tape 2 is the next copy destination. Both remain untouched. -/
def worker (blank : Fin k) : StructuredMachine Unit (Fin 3) (Fin k) 3 1 where
  tapeCount_pos := by decide
  blank := blank
  initial := 0
  accepting := fun q => decide (q = 2)
  micro := fun q a σ =>
    let d := (HistoryRewind.machine blank).micro q a (fun _ => σ 1)
    (d.1, fun j => if j = 1 then d.2 0 else (σ j, .stay))

def slice (x : SConfig (Fin 3) (Fin k) 3) : SConfig (Fin 3) (Fin k) 1 :=
  HistoryRewind.config x.state (x.tape 1)

def run (blank : Fin k) (n : ℕ) (x : SConfig (Fin 3) (Fin k) 3) :=
  (List.replicate n ()).foldl (worker blank).sRound x

theorem round_slice (blank : Fin k) (x : SConfig (Fin 3) (Fin k) 3) :
    slice ((worker blank).sRound x ()) = (HistoryRewind.machine blank).sRound (slice x) () := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, worker, slice, HistoryRewind.config, ↓reduceIte]
  congr 1
  funext j
  have : j = 0 := Subsingleton.elim _ _
  rw [this]
  rfl

theorem round_other (blank : Fin k) (x : SConfig (Fin 3) (Fin k) 3)
    (i : Fin 3) (hi : i ≠ 1) : ((worker blank).sRound x ()).tape i = x.tape i := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, worker, hi, ↓reduceIte]
  rfl

theorem run_slice (blank : Fin k) (n : ℕ) (x : SConfig (Fin 3) (Fin k) 3) :
    slice (run blank n x) = HistoryRewind.run blank n (slice x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change slice (run blank n ((worker blank).sRound x ())) = _
    rw [ih, round_slice]
    rfl

theorem run_other (blank : Fin k) (n : ℕ) (x : SConfig (Fin 3) (Fin k) 3)
    (i : Fin 3) (hi : i ≠ 1) : (run blank n x).tape i = x.tape i := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change (run blank n ((worker blank).sRound x ())).tape i = _
    rw [ih, round_other blank x i hi]

theorem frozen (blank : Fin k) (v : List (Fin k)) (hv : blank ∉ v)
    (n : ℕ) (hn : v.length + 2 ≤ n) (T : Fin 3 → STape (Fin k))
    (hT : T 1 = ⟨v.reverse ++ [blank], blank, []⟩) :
    let y := run blank n ⟨0, T⟩
    y.state = 2 ∧ STape.BlankEq blank (y.tape 1) (HistoryConcat.source blank v [blank]) ∧
      y.tape 0 = T 0 ∧ y.tape 2 = T 2 := by
  have hr := run_slice blank n ⟨0, T⟩
  simp only [slice, hT] at hr
  have he : n = (v.length + 2) + (n - (v.length + 2)) := by omega
  have hb : HistoryRewind.run blank n (HistoryRewind.config 0 ⟨v.reverse ++ [blank], blank, []⟩) =
      HistoryRewind.config 2 (HistoryConcat.source blank (v ++ [blank]) [blank]) := by
    rw [he, HistoryRewind.run, List.replicate_add, List.foldl_append]
    change HistoryRewind.run blank (n - (v.length + 2))
      (HistoryRewind.run blank (v.length + 2)
        (HistoryRewind.config 0 ⟨v.reverse ++ [blank], blank, []⟩)) = _
    rw [HistoryRewind.rewind blank v hv, HistoryRewind.done_run]
  rw [hb] at hr
  have hs := congrArg SConfig.state hr
  have ht := congrArg (fun x => x.tape 0) hr
  simp only [HistoryRewind.config] at hs ht
  refine ⟨hs, ?_, run_other blank n ⟨0, T⟩ 0 (by decide),
    run_other blank n ⟨0, T⟩ 2 (by decide)⟩
  rw [ht]
  exact HistoryRewind.source_padding blank v [blank]

theorem done_round (blank : Fin k) (T : Fin 3 → STape (Fin k)) :
    (worker blank).sRound ⟨2, T⟩ () = ⟨2, T⟩ := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, worker, HistoryRewind.machine,
    show (2 : Fin 3) ≠ 0 by decide, ↓reduceIte]
  congr 1
  funext j
  by_cases h : j = 1 <;> simp only [h, ↓reduceIte] <;> rfl

theorem done_run (blank : Fin k) (n : ℕ) (T : Fin 3 → STape (Fin k)) :
    run blank n ⟨2, T⟩ = ⟨2, T⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change run blank n ((worker blank).sRound ⟨2, T⟩ ()) = _
    rw [done_round, ih]

theorem run_add (blank : Fin k) (n m : ℕ) (x : SConfig (Fin 3) (Fin k) 3) :
    run blank (n + m) x = run blank m (run blank n x) := by
  simp only [run, List.replicate_add, List.foldl_append]

/-- New arrivals go exclusively to the fourth logical tape while the old
log is rewound. This is a fixed C+1 microsteps per actual arrival. -/
def machine (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ) :=
  ArrivalLog.machine (worker blank) enc C

theorem frozen_input (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (w : List Terminal) (v : List (Fin k)) (hv : blank ∉ v)
    (T : Fin 4 → STape (Fin k))
    (h1 : T 1 = ⟨v.reverse ++ [blank], blank, []⟩)
    (h3 : T 3 = ⟨[blank], blank, []⟩) (budget : v.length + 2 ≤ w.length * C) :
    let y := w.foldl (machine blank enc C).sRound ⟨(0, 0), T⟩
    y.state = (2, 0) ∧ STape.BlankEq blank (y.tape 1) (HistoryConcat.source blank v [blank]) ∧
      y.tape 0 = T 0 ∧ y.tape 2 = T 2 ∧
      y.tape 3 = ⟨(w.map enc).reverse ++ [blank], blank, []⟩ := by
  have hh := ArrivalLog.rounds (worker blank) enc C w 0 T [blank] h3
  let A : Fin 3 → STape (Fin k) := fun j => T (ArrivalLog.addr j)
  have hf := frozen blank v hv (w.length * C) budget A h1
  let y := w.foldl (machine blank enc C).sRound ⟨(0, 0), T⟩
  have hp : ArrivalLog.view y = run blank (w.length * C) ⟨0, A⟩ := hh.2.1
  have hs := congrArg SConfig.state hp
  have ht (i : Fin 3) := congrArg (fun x => x.tape i) hp
  have hA : y.tape 0 = (run blank (w.length * C) ⟨0, A⟩).tape 0 := ht 0
  have hB : y.tape 1 = (run blank (w.length * C) ⟨0, A⟩).tape 1 := ht 1
  have hD : y.tape 2 = (run blank (w.length * C) ⟨0, A⟩).tape 2 := ht 2
  refine ⟨Prod.ext (hs.trans hf.1) hh.1, ?_, hA.trans hf.2.2.1,
    hD.trans hf.2.2.2, hh.2.2⟩
  change STape.BlankEq blank (y.tape 1) _
  rw [hB]
  exact hf.2.1

theorem frozen_padded (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (w : List Terminal) (u v : List (Fin k)) (hv : blank ∉ v)
    (T : Fin 4 → STape (Fin k))
    (h0 : STape.BlankEq blank (T 0) (HistoryConcat.source blank u [blank]))
    (h1 : STape.BlankEq blank (T 1) ⟨v.reverse ++ [blank], blank, []⟩)
    (h2 : STape.BlankEq blank (T 2) ⟨[blank], blank, []⟩)
    (h3 : STape.BlankEq blank (T 3) ⟨[blank], blank, []⟩)
    (budget : v.length + 2 ≤ w.length * C) :
    let y := w.foldl (machine blank enc C).sRound ⟨(0, 0), T⟩
    y.state = (2, 0) ∧
      STape.BlankEq blank (y.tape 0) (HistoryConcat.source blank u [blank]) ∧
      STape.BlankEq blank (y.tape 1) (HistoryConcat.source blank v [blank]) ∧
      STape.BlankEq blank (y.tape 2) ⟨[blank], blank, []⟩ ∧
      STape.BlankEq blank (y.tape 3) ⟨(w.map enc).reverse ++ [blank], blank, []⟩ := by
  let A : Fin 4 → STape (Fin k) := Fin.cases (HistoryConcat.source blank u [blank])
    (Fin.cases ⟨v.reverse ++ [blank], blank, []⟩
      (Fin.cases ⟨[blank], blank, []⟩ (fun _ => ⟨[blank], blank, []⟩)))
  have ha : ∀ i, STape.BlankEq blank (T i) (A i) := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hc := frozen_input blank enc C w v hv A rfl rfl budget
  have hr := (machine blank enc C).runFrom_blankEq w
    (show ConfigBlankEq (machine blank enc C).blank ⟨(0, 0), T⟩ ⟨(0, 0), A⟩ from ⟨rfl, ha⟩)
  refine ⟨hr.1.trans hc.1, ?_, (hr.2 1).trans hc.2.1, ?_, ?_⟩
  · apply (hr.2 0).trans
    rw [hc.2.2.1]
    exact STape.BlankEq.refl _ _
  · apply (hr.2 2).trans
    rw [hc.2.2.2.1]
    exact STape.BlankEq.refl _ _
  · apply (hr.2 3).trans
    rw [hc.2.2.2.2]
    exact STape.BlankEq.refl _ _

/-- info: 'PalPeg.HistoryFreeze.frozen_padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frozen_padded

end PalPeg.HistoryFreeze
