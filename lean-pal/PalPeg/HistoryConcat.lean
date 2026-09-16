import PalPeg.ProgramMachine

set_option autoImplicit false
namespace PalPeg.HistoryConcat
open PegSeparation.RealTimeTM PalPeg.Program
variable {k : ℕ}

def source (blank : Fin k) (w junk : List (Fin k)) : STape (Fin k) :=
  ⟨junk, w.headD blank, w.tail⟩

/-- Two finite history segments are copied into one frontier tape. Blank
terminates each source segment; input symbols must therefore be nonblank.
Neither segment length nor contents are part of the finite controller. -/
def machine (blank : Fin k) : StructuredMachine Unit (Fin 3) (Fin k) 3 1 where
  tapeCount_pos := by decide
  blank := blank
  initial := 0
  accepting := fun q => decide (q = 2)
  micro := fun q _ σ =>
    if q = 2 then (q, fun j => (σ j, .stay))
    else if σ q = blank then ((if q = 0 then 1 else 2), fun j => (σ j, .stay))
    else (q, fun j => if j = q then (σ j, .right)
      else if j = 2 then (σ q, .right) else (σ j, .stay))

def run (blank : Fin k) (n : ℕ) (x : SConfig (Fin 3) (Fin k) 3) :=
  (List.replicate n ()).foldl (machine blank).sRound x

theorem run_add (blank : Fin k) (n m : ℕ) (x : SConfig (Fin 3) (Fin k) 3) :
    run blank (n + m) x = run blank m (run blank n x) := by
  simp only [run, List.replicate_add, List.foldl_append]

def copied (blank : Fin k) (p : Fin 3) (T : Fin 3 → STape (Fin k)) : Fin 3 → STape (Fin k) :=
  fun j => (T j).applyAction blank
    (if j = p then ((T j).focus, .right)
      else if j = 2 then ((T p).focus, .right) else ((T j).focus, .stay))

theorem copy_round (blank : Fin k) (p : Fin 3) (hp : p ≠ 2)
    (T : Fin 3 → STape (Fin k)) (ha : (T p).focus ≠ blank) :
    (machine blank).sRound ⟨p, T⟩ () = ⟨p, copied blank p T⟩ := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs, Nat.sub_self,
    List.replicate_zero, List.foldl_cons, List.foldl_nil, StructuredMachine.sMicroStep,
    machine, hp, ha, ↓reduceIte]
  rfl

theorem boundary_round (blank : Fin k) (p : Fin 3) (hp : p ≠ 2)
    (T : Fin 3 → STape (Fin k)) (ha : (T p).focus = blank) :
    (machine blank).sRound ⟨p, T⟩ () = ⟨(if p = 0 then 1 else 2), T⟩ := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs, Nat.sub_self,
    List.replicate_zero, List.foldl_cons, List.foldl_nil, StructuredMachine.sMicroStep,
    machine, hp, ha, ↓reduceIte]
  rfl

theorem copy_word (blank : Fin k) (p : Fin 3) (hp : p ≠ 2) (w : List (Fin k))
    (hw : blank ∉ w) (junk out : List (Fin k)) (T : Fin 3 → STape (Fin k))
    (hs : T p = source blank w junk) (hd : T 2 = ⟨out, blank, []⟩) :
    let y := run blank w.length ⟨p, T⟩
    y.state = p ∧ y.tape p = source blank [] (w.reverse ++ junk) ∧
    y.tape 2 = ⟨w.reverse ++ out, blank, []⟩ ∧
    ∀ j, j ≠ p → j ≠ 2 → y.tape j = T j := by
  induction w generalizing junk out T with
  | nil => exact ⟨rfl, hs, hd, fun _ _ _ => rfl⟩
  | cons a w ih =>
    have ha : a ≠ blank := by intro h; subst a; exact hw (by simp)
    have hw' : blank ∉ w := fun h => hw (by simp [h])
    have hfocus : (T p).focus = a := by rw [hs]; rfl
    have hs' : copied blank p T p = source blank w (a :: junk) := by
      simp only [copied, ↓reduceIte, hs, source]
      cases w <;> rfl
    have hd' : copied blank p T 2 = ⟨a :: out, blank, []⟩ := by
      simp only [copied, Ne.symm hp, ↓reduceIte, hfocus, hd, STape.applyAction]
    have hr : run blank (a :: w).length ⟨p, T⟩ = run blank w.length ⟨p, copied blank p T⟩ := by
      change run blank w.length ((machine blank).sRound ⟨p, T⟩ ()) = _
      rw [copy_round blank p hp T (by rw [hfocus]; exact ha)]
    simp only [hr]
    have hh := ih hw' (a :: junk) (a :: out) (copied blank p T) hs' hd'
    refine ⟨hh.1, ?_, ?_, ?_⟩
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hh.2.1
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hh.2.2.1
    · intro j hj h2
      rw [hh.2.2.2 j hj h2]
      simp only [copied, hj, h2, ↓reduceIte]
      rfl

theorem segment (blank : Fin k) (p : Fin 3) (hp : p ≠ 2) (w : List (Fin k))
    (hw : blank ∉ w) (junk out : List (Fin k)) (T : Fin 3 → STape (Fin k))
    (hs : T p = source blank w junk) (hd : T 2 = ⟨out, blank, []⟩) :
    let y := run blank (w.length + 1) ⟨p, T⟩
    y.state = (if p = 0 then 1 else 2) ∧ y.tape p = source blank [] (w.reverse ++ junk) ∧
    y.tape 2 = ⟨w.reverse ++ out, blank, []⟩ ∧
    ∀ j, j ≠ p → j ≠ 2 → y.tape j = T j := by
  have hh := copy_word blank p hp w hw junk out T hs hd
  let y := run blank w.length ⟨p, T⟩
  have hy : y.state = p := hh.1
  have he : y = ⟨p, y.tape⟩ := by rw [← hy]
  have hr : run blank (w.length + 1) ⟨p, T⟩ = ⟨(if p = 0 then 1 else 2), y.tape⟩ := by
    rw [run_add]
    change (machine blank).sRound y () = _
    rw [he, boundary_round blank p hp y.tape (by rw [hh.2.1]; rfl)]
  rw [hr]
  exact ⟨rfl, hh.2⟩

/-- All copied symbols are read from physical source heads. Empty segments
are allowed, and exactly two additional rounds detect their ends. -/
theorem concat (blank : Fin k) (u v : List (Fin k)) (hu : blank ∉ u) (hv : blank ∉ v)
    (left right out : List (Fin k)) (T : Fin 3 → STape (Fin k))
    (h0 : T 0 = source blank u left) (h1 : T 1 = source blank v right)
    (h2 : T 2 = ⟨out, blank, []⟩) :
    let y := run blank (u.length + v.length + 2) ⟨0, T⟩
    y.state = 2 ∧ y.tape 2 = ⟨(u ++ v).reverse ++ out, blank, []⟩ ∧
    y.tape 0 = source blank [] (u.reverse ++ left) ∧
    y.tape 1 = source blank [] (v.reverse ++ right) := by
  have hh0 := segment blank 0 (by decide) u hu left out T h0 h2
  let y := run blank (u.length + 1) ⟨0, T⟩
  have hy : y.state = 1 := hh0.1
  have he : y = ⟨1, y.tape⟩ := by rw [← hy]
  have hy1 : y.tape 1 = source blank v right :=
    (hh0.2.2.2 1 (by decide) (by decide)).trans h1
  have hh1 := segment blank 1 (by decide) v hv right (u.reverse ++ out) y.tape hy1 hh0.2.2.1
  have hr : run blank (u.length + v.length + 2) ⟨0, T⟩ =
      run blank (v.length + 1) ⟨1, y.tape⟩ := by
    rw [show u.length + v.length + 2 = (u.length + 1) + (v.length + 1) by omega, run_add]
    change run blank (v.length + 1) y = _
    rw [he]
  rw [hr]
  refine ⟨hh1.1, ?_, ?_, hh1.2.1⟩
  · simpa only [List.reverse_append, List.append_assoc] using hh1.2.2.1
  · exact (hh1.2.2.2 0 (by decide) (by decide)).trans hh0.2.1

theorem concat_prefix (blank : Fin k) (w : List (Fin k)) (h₀ h : ℕ)
    (h0h : h₀ ≤ h) (hw : h ≤ w.length) (hb : blank ∉ w)
    (left right out : List (Fin k)) (T : Fin 3 → STape (Fin k))
    (h0 : T 0 = source blank (w.take h₀) left)
    (h1 : T 1 = source blank ((w.drop h₀).take (h - h₀)) right)
    (h2 : T 2 = ⟨out, blank, []⟩) :
    let y := run blank (h + 2) ⟨0, T⟩
    y.state = 2 ∧ y.tape 2 = ⟨(w.take h).reverse ++ out, blank, []⟩ := by
  have hu : blank ∉ w.take h₀ := fun hm => hb (List.mem_of_mem_take hm)
  have hv : blank ∉ (w.drop h₀).take (h - h₀) := fun hm =>
    hb (List.mem_of_mem_drop (List.mem_of_mem_take hm))
  have hs : w.take h₀ ++ (w.drop h₀).take (h - h₀) = w.take h := by
    rw [← List.take_add, Nat.add_sub_of_le h0h]
  have hl : (w.take h₀).length + ((w.drop h₀).take (h - h₀)).length = h := by
    simp only [List.length_take, List.length_drop]
    omega
  have hh := concat blank (w.take h₀) ((w.drop h₀).take (h - h₀)) hu hv left right out T h0 h1 h2
  rw [hl, hs] at hh
  exact ⟨hh.1, hh.2.1⟩

theorem done_round (blank : Fin k) (T : Fin 3 → STape (Fin k)) :
    (machine blank).sRound ⟨2, T⟩ () = ⟨2, T⟩ := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs, Nat.sub_self,
    List.replicate_zero, List.foldl_cons, List.foldl_nil, StructuredMachine.sMicroStep,
    machine, ↓reduceIte]
  rfl

theorem run_done (blank : Fin k) (n : ℕ) (T : Fin 3 → STape (Fin k)) :
    run blank n ⟨2, T⟩ = ⟨2, T⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change run blank n ((machine blank).sRound ⟨2, T⟩ ()) = _
    rw [done_round, ih]

/-- A fixed-budget caller can continue ticking after completion without
changing the reconstructed prefix or either source tape. -/
theorem stable_done (blank : Fin k) (x : SConfig (Fin 3) (Fin k) 3)
    (hx : x.state = 2) (n : ℕ) : run blank n x = x := by
  have he : x = ⟨2, x.tape⟩ := by rw [← hx]
  rw [he, run_done]

/-- info: 'PalPeg.HistoryConcat.concat_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms concat_prefix

/-- info: 'PalPeg.HistoryConcat.concat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms concat

/-- info: 'PalPeg.HistoryConcat.copy_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copy_word

end PalPeg.HistoryConcat
