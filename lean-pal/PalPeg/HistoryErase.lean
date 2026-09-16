import PalPeg.HistoryRewind

set_option autoImplicit false
namespace PalPeg.HistoryErase
open PegSeparation.RealTimeTM PalPeg.Program
variable {k : ℕ}

/-- Erase an exhausted source while scanning back to its reserved blank
sentinel. The result can be reused as an append-only destination. -/
def machine (blank : Fin k) : StructuredMachine Unit (Fin 3) (Fin k) 1 1 where
  tapeCount_pos := by decide
  blank := blank
  initial := 0
  accepting := fun q => decide (q = 2)
  micro := fun q _ σ =>
    if q = 0 then (1, fun _ => (blank, .left))
    else if q = 2 then (2, fun j => (σ j, .stay))
    else if σ 0 = blank then (2, fun _ => (blank, .right))
    else (1, fun _ => (blank, .left))

abbrev config := @HistoryRewind.config

def run (blank : Fin k) (n : ℕ) (x : SConfig (Fin 3) (Fin k) 1) :=
  (List.replicate n ()).foldl (machine blank).sRound x

theorem run_add (blank : Fin k) (n m : ℕ) (x : SConfig (Fin 3) (Fin k) 1) :
    run blank (n + m) x = run blank m (run blank n x) := by
  simp only [run, List.replicate_add, List.foldl_append]

theorem scan_round (blank a b : Fin k) (l r : List (Fin k)) (ha : a ≠ blank) :
    (machine blank).sRound (config 1 ⟨b :: l, a, r⟩) () =
      config 1 ⟨l, b, blank :: r⟩ := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, config, HistoryRewind.config, ha,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, ↓reduceIte]
  rfl

theorem scan (blank : Fin k) (l : List (Fin k)) (a : Fin k) (r : List (Fin k))
    (hl : blank ∉ l) (ha : a ≠ blank) :
    run blank (l.length + 1) (config 1 ⟨l ++ [blank], a, r⟩) =
      config 1 ⟨[], blank, List.replicate (l.length + 1) blank ++ r⟩ := by
  induction l generalizing a r with
  | nil => exact scan_round blank a blank [] r ha
  | cons b l ih =>
    have hb : b ≠ blank := by intro h; subst b; exact hl (by simp)
    have hl' : blank ∉ l := fun h => hl (by simp [h])
    change run blank (l.length + 1)
      ((machine blank).sRound (config 1 ⟨b :: (l ++ [blank]), a, r⟩) ()) = _
    rw [scan_round blank a b (l ++ [blank]) r ha]
    simpa only [List.length_cons, List.replicate_succ', List.append_assoc,
      List.singleton_append, List.cons_append, List.nil_append] using ih b (blank :: r) hl' hb

theorem boundary (blank : Fin k) (n : ℕ) :
    (machine blank).sRound (config 1 ⟨[], blank, List.replicate (n + 1) blank⟩) () =
      config 2 ⟨[blank], blank, List.replicate n blank⟩ := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, config, HistoryRewind.config,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, ↓reduceIte,
    List.replicate_succ]
  rfl

theorem erase (blank : Fin k) (l : List (Fin k)) (hl : blank ∉ l) :
    run blank (l.length + 2) (config 0 ⟨l ++ [blank], blank, []⟩) =
      config 2 ⟨[blank], blank, List.replicate l.length blank⟩ := by
  have hfirst : (machine blank).sRound (config 0 ⟨l ++ [blank], blank, []⟩) () =
      config 1 ⟨(l ++ [blank]).tail, (l ++ [blank]).headD blank, [blank]⟩ := by
    simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
      Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
      StructuredMachine.sMicroStep, machine, config, HistoryRewind.config, ↓reduceIte]
    cases l <;> rfl
  have hs : run blank l.length
      (config 1 ⟨(l ++ [blank]).tail, (l ++ [blank]).headD blank, [blank]⟩) =
      config 1 ⟨[], blank, List.replicate (l.length + 1) blank⟩ := by
    cases l with
    | nil => rfl
    | cons a l =>
      have ha : a ≠ blank := by intro h; subst a; exact hl (by simp)
      have hl' : blank ∉ l := fun h => hl (by simp [h])
      simpa only [List.cons_append, List.length_cons, List.tail_cons, List.headD_cons,
        List.replicate_succ'] using scan blank l a [blank] hl' ha
  change run blank (l.length + 1)
    ((machine blank).sRound (config 0 ⟨l ++ [blank], blank, []⟩) ()) = _
  rw [hfirst, run_add, hs]
  exact boundary blank l.length

theorem done_round (blank : Fin k) (T : STape (Fin k)) :
    (machine blank).sRound (config 2 T) () = config 2 T := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, config, HistoryRewind.config,
    show (2 : Fin 3) ≠ 0 by decide, ↓reduceIte]
  rfl

theorem done_run (blank : Fin k) (n : ℕ) (T : STape (Fin k)) :
    run blank n (config 2 T) = config 2 T := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change run blank n ((machine blank).sRound (config 2 T) ()) = _
    rw [done_round, ih]

theorem reusable (blank : Fin k) (l : List (Fin k)) (hl : blank ∉ l)
    (n : ℕ) (hn : l.length + 2 ≤ n) :
    let y := run blank n (config 0 ⟨l ++ [blank], blank, []⟩)
    y.state = 2 ∧ STape.BlankEq blank (y.tape 0) ⟨[blank], blank, []⟩ := by
  have hr : n = (l.length + 2) + (n - (l.length + 2)) := by omega
  rw [hr, run_add, erase blank l hl, done_run]
  exact ⟨rfl, (STape.BlankEq.padRight blank ⟨[blank], blank, []⟩ l.length).symm⟩

/-- info: 'PalPeg.HistoryErase.reusable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reusable

end PalPeg.HistoryErase
