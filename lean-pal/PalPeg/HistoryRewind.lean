import PalPeg.HistoryConcat
import PalPeg.ProgramBlankEq

set_option autoImplicit false
namespace PalPeg.HistoryRewind
open PegSeparation.RealTimeTM PalPeg.Program
variable {k : ℕ}

/-- Enter from a blank frontier, scan back to a reserved blank sentinel,
then step onto the first symbol. No length is stored in the control.
The sentinel is required: a left move at the physical boundary is clamped. -/
def machine (blank : Fin k) : StructuredMachine Unit (Fin 3) (Fin k) 1 1 where
  tapeCount_pos := by decide
  blank := blank
  initial := 0
  accepting := fun q => decide (q = 2)
  micro := fun q _ σ =>
    if q = 0 then (1, fun j => (σ j, .left))
    else if q = 2 then (2, fun j => (σ j, .stay))
    else if σ 0 = blank then (2, fun j => (σ j, .right))
    else (1, fun j => (σ j, .left))

def config (q : Fin 3) (T : STape (Fin k)) : SConfig (Fin 3) (Fin k) 1 :=
  ⟨q, fun _ => T⟩

def run (blank : Fin k) (n : ℕ) (x : SConfig (Fin 3) (Fin k) 1) :=
  (List.replicate n ()).foldl (machine blank).sRound x

theorem scan_round (blank a b : Fin k) (l r : List (Fin k)) (ha : a ≠ blank) :
    (machine blank).sRound (config 1 ⟨b :: l, a, r⟩) () =
      config 1 ⟨l, b, a :: r⟩ := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, config, ha,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, ↓reduceIte]
  rfl

theorem scan (blank : Fin k) (l : List (Fin k)) (a : Fin k) (r : List (Fin k))
    (hl : blank ∉ l) (ha : a ≠ blank) :
    run blank (l.length + 1) (config 1 ⟨l ++ [blank], a, r⟩) =
      config 1 ⟨[], blank, l.reverse ++ a :: r⟩ := by
  induction l generalizing a r with
  | nil => exact scan_round blank a blank [] r ha
  | cons b l ih =>
    have hb : b ≠ blank := by intro h; subst b; exact hl (by simp)
    have hl' : blank ∉ l := fun h => hl (by simp [h])
    change run blank (l.length + 1) ((machine blank).sRound (config 1 ⟨b :: (l ++ [blank]), a, r⟩) ()) = _
    rw [scan_round blank a b (l ++ [blank]) r ha]
    simpa only [List.tail_cons, List.headD_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append] using ih b (a :: r) hl' hb

theorem boundary (blank : Fin k) (r : List (Fin k)) :
    (machine blank).sRound (config 1 ⟨[], blank, r⟩) () =
      config 2 (HistoryConcat.source blank r [blank]) := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, config,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, ↓reduceIte]
  cases r <;> rfl

/-- A freshly built frontier becomes a forward-readable source. The extra
right blank is an explicit terminator, including for the empty history. -/
theorem rewind (blank : Fin k) (w : List (Fin k)) (hw : blank ∉ w) :
    run blank (w.length + 2) (config 0 ⟨w.reverse ++ [blank], blank, []⟩) =
      config 2 (HistoryConcat.source blank (w ++ [blank]) [blank]) := by
  have hfirst : (machine blank).sRound (config 0 ⟨w.reverse ++ [blank], blank, []⟩) () =
      config 1 ⟨(w.reverse ++ [blank]).tail, (w.reverse ++ [blank]).headD blank, [blank]⟩ := by
    simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
      Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
      StructuredMachine.sMicroStep, machine, config, ↓reduceIte]
    cases w.reverse <;> rfl
  have hs : run blank w.length
      (config 1 ⟨(w.reverse ++ [blank]).tail, (w.reverse ++ [blank]).headD blank, [blank]⟩) =
      config 1 ⟨[], blank, w ++ [blank]⟩ := by
    have hrev : blank ∉ w.reverse := by simpa using hw
    have hlen : w.length = w.reverse.length := by simp
    rw [hlen]
    generalize he : w.reverse = v at *
    have he' : w = v.reverse := by rw [← he, List.reverse_reverse]
    rw [he']
    cases v with
    | nil => rfl
    | cons a l =>
      have ha : a ≠ blank := by intro h; subst a; exact hrev (by simp)
      have hl : blank ∉ l := fun h => hrev (by simp [h])
      simpa only [List.cons_append, List.length_cons, List.tail_cons, List.headD_cons,
        List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using
        scan blank l a [blank] hl ha
  change run blank (w.length + 1) ((machine blank).sRound (config 0 ⟨w.reverse ++ [blank], blank, []⟩) ()) = _
  rw [hfirst]
  have hr (n m : ℕ) (x : SConfig (Fin 3) (Fin k) 1) :
      run blank (n + m) x = run blank m (run blank n x) := by
    simp only [run, List.replicate_add, List.foldl_append]
  rw [hr, hs]
  exact boundary blank (w ++ [blank])

theorem done_round (blank : Fin k) (T : STape (Fin k)) :
    (machine blank).sRound (config 2 T) () = config 2 T := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, config,
    show (2 : Fin 3) ≠ 0 by decide, ↓reduceIte]
  rfl

theorem done_run (blank : Fin k) (n : ℕ) (T : STape (Fin k)) :
    run blank n (config 2 T) = config 2 T := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change run blank n ((machine blank).sRound (config 2 T) ()) = _
    rw [done_round, ih]

theorem source_padding (blank : Fin k) (w junk : List (Fin k)) :
    STape.BlankEq blank (HistoryConcat.source blank (w ++ [blank]) junk)
      (HistoryConcat.source blank w junk) := by
  cases w with
  | nil => exact STape.BlankEq.refl _ _
  | cons a w =>
    exact (STape.BlankEq.padRight blank (HistoryConcat.source blank (a :: w) junk) 1).symm

theorem rewind_source (blank : Fin k) (w : List (Fin k)) (hw : blank ∉ w) :
    STape.BlankEq blank
      ((run blank (w.length + 2) (config 0 ⟨w.reverse ++ [blank], blank, []⟩)).tape 0)
      (HistoryConcat.source blank w [blank]) := by
  rw [rewind blank w hw]
  exact source_padding blank w [blank]

/-- info: 'PalPeg.HistoryRewind.rewind_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rewind_source

end PalPeg.HistoryRewind
