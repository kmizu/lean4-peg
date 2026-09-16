import PalPeg.HistoryErase

set_option autoImplicit false
namespace PalPeg.HistoryRecover
open PegSeparation.RealTimeTM PalPeg.Program
variable {k : ℕ}

def lane (blank : Fin k) (i : Fin 3) : StructuredMachine Unit (Fin 3) (Fin k) 1 1 :=
  if i = 2 then HistoryRewind.machine blank else HistoryErase.machine blank

/-- Rewind the merged destination and erase both exhausted sources in
parallel. All three heads operate independently in the same fixed tick. -/
def machine (blank : Fin k) : StructuredMachine Unit (Fin 3 → Fin 3) (Fin k) 3 1 where
  tapeCount_pos := by decide
  blank := blank
  initial := fun _ => 0
  accepting := fun q => decide (∀ i, q i = 2)
  micro := fun q a σ =>
    let d := fun i => (lane blank i).micro (q i) a (fun _ => σ i)
    (fun i => (d i).1, fun i => (d i).2 0)

def slice (i : Fin 3) (x : SConfig (Fin 3 → Fin 3) (Fin k) 3) :
    SConfig (Fin 3) (Fin k) 1 := HistoryRewind.config (x.state i) (x.tape i)

def run (blank : Fin k) (n : ℕ) (x : SConfig (Fin 3 → Fin 3) (Fin k) 3) :=
  (List.replicate n ()).foldl (machine blank).sRound x

theorem round_slice (blank : Fin k) (i : Fin 3)
    (x : SConfig (Fin 3 → Fin 3) (Fin k) 3) :
    slice i ((machine blank).sRound x ()) = (lane blank i).sRound (slice i x) () := by
  have hb : (lane blank i).blank = blank := by unfold lane; split <;> rfl
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, slice, HistoryRewind.config, hb]
  congr 1
  funext j
  have : j = 0 := Subsingleton.elim _ _
  rw [this]

theorem run_slice (blank : Fin k) (i : Fin 3) (n : ℕ)
    (x : SConfig (Fin 3 → Fin 3) (Fin k) 3) :
    slice i (run blank n x) = (List.replicate n ()).foldl (lane blank i).sRound (slice i x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change slice i (run blank n ((machine blank).sRound x ())) = _
    rw [ih, round_slice]
    rfl

theorem erase_lane (blank : Fin k) (i : Fin 3) (hi : i ≠ 2)
    (l : List (Fin k)) (hl : blank ∉ l) (n : ℕ) (hn : l.length + 2 ≤ n)
    (T : Fin 3 → STape (Fin k)) (hT : T i = ⟨l ++ [blank], blank, []⟩) :
    let y := run blank n ⟨fun _ => 0, T⟩
    y.state i = 2 ∧ STape.BlankEq blank (y.tape i) ⟨[blank], blank, []⟩ := by
  have hr := run_slice blank i n ⟨fun _ => 0, T⟩
  simp only [lane, hi, ↓reduceIte, slice, hT] at hr
  have hh := HistoryErase.reusable blank l hl n hn
  have hs := congrArg SConfig.state hr
  have ht := congrArg (fun x => x.tape 0) hr
  simp only [HistoryRewind.config] at ht
  refine ⟨hs.trans hh.1, ?_⟩
  change STape.BlankEq blank ((run blank n ⟨fun _ => 0, T⟩).tape i) _
  rw [ht]
  exact hh.2

theorem rewind_lane (blank : Fin k) (w : List (Fin k)) (hw : blank ∉ w)
    (n : ℕ) (hn : w.length + 2 ≤ n) (T : Fin 3 → STape (Fin k))
    (hT : T 2 = ⟨w.reverse ++ [blank], blank, []⟩) :
    let y := run blank n ⟨fun _ => 0, T⟩
    y.state 2 = 2 ∧ STape.BlankEq blank (y.tape 2) (HistoryConcat.source blank w [blank]) := by
  have hr := run_slice blank 2 n ⟨fun _ => 0, T⟩
  simp only [lane, ↓reduceIte, slice, hT] at hr
  have hb : HistoryRewind.run blank n (HistoryRewind.config 0 ⟨w.reverse ++ [blank], blank, []⟩) =
      HistoryRewind.config 2 (HistoryConcat.source blank (w ++ [blank]) [blank]) := by
    have he : n = (w.length + 2) + (n - (w.length + 2)) := by omega
    rw [he]
    rw [HistoryRewind.run, List.replicate_add, List.foldl_append]
    change HistoryRewind.run blank (n - (w.length + 2))
      (HistoryRewind.run blank (w.length + 2)
        (HistoryRewind.config 0 ⟨w.reverse ++ [blank], blank, []⟩)) = _
    rw [HistoryRewind.rewind blank w hw, HistoryRewind.done_run]
  change _ = HistoryRewind.run blank n _ at hr
  rw [hb] at hr
  have hs := congrArg SConfig.state hr
  have ht := congrArg (fun x => x.tape 0) hr
  simp only [HistoryRewind.config] at ht
  refine ⟨hs, ?_⟩
  change STape.BlankEq blank ((run blank n ⟨fun _ => 0, T⟩).tape 2) _
  rw [ht]
  exact HistoryRewind.source_padding blank w [blank]

/-- This is precisely the three-frontier shape left by concatenation when
each source and destination reserves one blank sentinel. -/
theorem recovered (blank : Fin k) (u v : List (Fin k)) (hu : blank ∉ u) (hv : blank ∉ v)
    (T : Fin 3 → STape (Fin k))
    (h0 : T 0 = ⟨u.reverse ++ [blank], blank, []⟩)
    (h1 : T 1 = ⟨v.reverse ++ [blank], blank, []⟩)
    (h2 : T 2 = ⟨(u ++ v).reverse ++ [blank], blank, []⟩) :
    let y := run blank (u.length + v.length + 2) ⟨fun _ => 0, T⟩
    (∀ i, y.state i = 2) ∧ STape.BlankEq blank (y.tape 0) ⟨[blank], blank, []⟩ ∧
      STape.BlankEq blank (y.tape 1) ⟨[blank], blank, []⟩ ∧
      STape.BlankEq blank (y.tape 2) (HistoryConcat.source blank (u ++ v) [blank]) := by
  have hA := erase_lane blank 0 (by decide) u.reverse (by simpa using hu)
    (u.length + v.length + 2) (by simp) T h0
  have hB := erase_lane blank 1 (by decide) v.reverse (by simpa using hv)
    (u.length + v.length + 2) (by simp) T h1
  have hC := rewind_lane blank (u ++ v) (by simpa using And.intro hu hv)
    (u.length + v.length + 2) (by simp) T h2
  refine ⟨?_, hA.2, hB.2, hC.2⟩
  intro i
  fin_cases i
  · exact hA.1
  · exact hB.1
  · exact hC.1

theorem done_round (blank : Fin k) (T : Fin 3 → STape (Fin k)) :
    (machine blank).sRound ⟨fun _ => 2, T⟩ () = ⟨fun _ => 2, T⟩ := by
  have hl (i : Fin 3) : (lane blank i).micro 2 (some ()) (fun _ => (T i).focus) =
      (2, fun _ => ((T i).focus, Move.stay)) := by
    unfold lane
    split <;> simp only [HistoryRewind.machine, HistoryErase.machine,
      show (2 : Fin 3) ≠ 0 by decide, ↓reduceIte]
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, hl]
  rfl

/-- info: 'PalPeg.HistoryRecover.recovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms recovered

end PalPeg.HistoryRecover
