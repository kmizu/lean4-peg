import PalPeg.ClockHistoryPeriods

set_option autoImplicit false
namespace PalPeg.ClockHistoryInvariant
open PegSeparation.RealTimeTM PalPeg.Program
variable {k : ℕ} {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]

def atWord (blank : Fin k) (enc : Terminal → Fin k) (w : List Terminal) :=
  w.foldl (ClockHistory.machine blank enc).sRound (ClockHistoryStartup.seed blank enc)

theorem at_append (blank : Fin k) (enc : Terminal → Fin k) (u v : List Terminal) :
    atWord blank enc (u ++ v) = v.foldl (ClockHistory.machine blank enc).sRound (atWord blank enc u) := by
  simp only [atWord, List.foldl_append]

theorem at_clock (blank : Fin k) (enc : Terminal → Fin k) (w : List Terminal) :
    ClockHistory.clock (atWord blank enc w) = SlotClockBirth.atTime w.length := by
  rw [atWord, ClockHistory.clock_rounds blank enc w _ rfl, ClockHistoryStartup.seed_clock]
  rfl

theorem at_phase (blank : Fin k) (enc : Terminal → Fin k) (w : List Terminal) :
    (atWord blank enc w).state.2 = 0 := by
  have h (v : List Terminal) (x : SConfig (ClockHistory.Core × Fin 33) (SlotClock.Symbol × Fin k) 12)
      (hx : x.state.2 = 0) : (v.foldl (ClockHistory.machine blank enc).sRound x).state.2 = 0 := by
    induction v generalizing x with
    | nil => exact hx
    | cons a v ih =>
      have hp := ClockHistory.round_phase blank enc x hx a
      simp only [List.foldl_cons]
      generalize hz : (ClockHistory.machine blank enc).sRound x a = z at hp ⊢
      exact ih z hp
  exact h w _ rfl

theorem at_actual (blank : Fin k) (enc : Terminal → Fin k) (w : List Terminal) (hw : w ≠ []) :
    atWord blank enc w = WarmStart.view ((ClockHistoryStartup.machine blank enc).srun w) := by
  cases w with
  | nil => contradiction
  | cons a w => exact (ClockHistoryStartup.from_blank blank enc a w).symm

theorem encoded_nonblank (blank : Fin k) (enc : Terminal → Fin k) (henc : ∀ a, enc a ≠ blank)
    (w : List Terminal) : blank ∉ w.map enc := by
  intro h
  obtain ⟨a, _, ha⟩ := List.mem_map.mp h
  exact henc a ha

/-- At every dyadic boundary, starting at 32, the actual clock-driven
history has the reusable layout and contains exactly the entire read word.
No oracle start schedule or source-tape assumption remains in this invariant. -/
theorem dyadic (blank : Fin k) (enc : Terminal → Fin k) (henc : ∀ a, enc a ≠ blank)
    (g : ℕ) (w : List Terminal) (hw : w.length = 2 ^ (g + 5)) :
    let y := ClockHistory.history (atWord blank enc w)
    ∃ u v, HistoryRotation.Layout blank y.state.1 u v y.tape ∧ u ++ v = w.map enc := by
  induction g generalizing w with
  | zero =>
    have h32 : w.length = 32 := hw
    have hnon : w ≠ [] := by intro h; subst w; simp at h32
    rw [at_actual blank enc w hnon]
    refine ⟨[], w.map enc, ?_, rfl⟩
    rw [ClockHistoryStartup.startup_role blank enc w h32]
    exact ClockHistoryStartup.startup_layout blank enc w h32
  | succ g ih =>
    let N := 2 ^ (g + 5)
    have hN : 0 < N := pow_pos (by decide) _
    have hlen : w.length = 2 * N := by
      rw [hw, show g + 1 + 5 = (g + 5) + 1 by omega, pow_succ]
      omega
    have hleft : (w.take N).length = N := by rw [List.length_take]; omega
    have hright : (w.drop N).length = N := by rw [List.length_drop]; omega
    obtain ⟨u, v, hLayout, huv⟩ := ih (w.take N) hleft
    have hsize : u.length + v.length = N := by
      have := congrArg List.length huv
      simp only [List.length_append, List.length_map, hleft] at this
      exact this
    have hfree : blank ∉ (w.take N).map enc := encoded_nonblank blank enc henc _
    have hu : blank ∉ u := by
      intro h
      apply hfree
      rw [← huv]
      exact List.mem_append_left _ h
    have hv : blank ∉ v := by
      intro h
      apply hfree
      rw [← huv]
      exact List.mem_append_right _ h
    have hrun : atWord blank enc w =
        (w.drop N).foldl (ClockHistory.machine blank enc).sRound (atWord blank enc (w.take N)) := by
      have he := congrArg (atWord blank enc) (List.take_append_drop N w)
      rw [at_append] at he
      exact he.symm
    cases hr : w.drop N with
    | nil => rw [hr] at hright; simp at hright; omega
    | cons a rest =>
      have hrest : (a :: rest).length = N := by rw [← hr]; exact hright
      have hc : ClockHistory.clock (atWord blank enc (w.take N)) = SlotClockBirth.atTime (2 ^ (g + 5)) := by
        rw [at_clock, hleft]
      have hb := ClockHistoryPeriods.block_layout blank enc (g + 5) (by omega) a rest u v hu hv
        (atWord blank enc (w.take N)) (at_phase blank enc _) hc hLayout hsize
        (by rw [hrest]; exact Nat.div_le_self _ _) (by rw [hrest])
      refine ⟨u ++ v, (w.drop N).map enc, ?_, ?_⟩
      · rw [hrun, hr]
        exact hb.2.2
      · rw [huv, ← List.map_append, List.take_append_drop]

theorem actual_dyadic (blank : Fin k) (enc : Terminal → Fin k) (henc : ∀ a, enc a ≠ blank)
    (g : ℕ) (w : List Terminal) (hw : w.length = 2 ^ (g + 5)) :
    let y := ClockHistory.history (WarmStart.view ((ClockHistoryStartup.machine blank enc).srun w))
    ∃ u v, HistoryRotation.Layout blank y.state.1 u v y.tape ∧ u ++ v = w.map enc := by
  have hnon : w ≠ [] := by
    intro h
    subst w
    have := pow_pos (by decide : 0 < (2 : ℕ)) (g + 5)
    simp only [List.length_nil] at hw
    omega
  rw [← at_actual blank enc w hnon]
  exact dyadic blank enc henc g w hw

/-- The requested snapshot is physically readable by the eighth-length
deadline and remains so until the next cycle. Both snapshot and later
arrivals are identified with slices of the actual raw input. -/
theorem actual_window (blank : Fin k) (enc : Terminal → Fin k) (henc : ∀ a, enc a ≠ blank)
    (g : ℕ) (w : List Terminal)
    (hl : 2 ^ (g + 5) + 2 ^ (g + 5) / 8 ≤ w.length)
    (hh : w.length ≤ 2 * 2 ^ (g + 5)) :
    let y := ClockHistory.history (WarmStart.view ((ClockHistoryStartup.machine blank enc).srun w))
    y.state.2 = (.inr (.inr (fun _ => 2)), 0) ∧
      HistoryRotation.Layout blank y.state.1 ((w.take (2 ^ (g + 5))).map enc)
        ((w.drop (2 ^ (g + 5))).map enc) y.tape := by
  let N := 2 ^ (g + 5)
  have hN : 32 ≤ N := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 5 ≤ g + 5)
  have hleft : (w.take N).length = N := by rw [List.length_take]; omega
  have hright : (w.drop N).length = w.length - N := List.length_drop
  obtain ⟨u, v, hLayout, huv⟩ := dyadic blank enc henc g (w.take N) hleft
  have hsize : u.length + v.length = N := by
    have := congrArg List.length huv
    simpa only [List.length_append, List.length_map, hleft] using this
  have hfree : blank ∉ u ++ v := by
    rw [huv]
    exact encoded_nonblank blank enc henc _
  have hu : blank ∉ u := fun h => hfree (List.mem_append_left _ h)
  have hv : blank ∉ v := fun h => hfree (List.mem_append_right _ h)
  have hrun : atWord blank enc w =
      (w.drop N).foldl (ClockHistory.machine blank enc).sRound (atWord blank enc (w.take N)) := by
    have he := congrArg (atWord blank enc) (List.take_append_drop N w)
    rw [at_append] at he
    exact he.symm
  have hnon : w ≠ [] := by intro h; subst w; simp only [List.length_nil] at hl; omega
  rw [← at_actual blank enc w hnon]
  cases hr : w.drop N with
  | nil => rw [hr] at hright; simp only [List.length_nil] at hright; omega
  | cons a rest =>
    have hrest : (a :: rest).length = w.length - N := by rw [← hr]; exact hright
    have hc : ClockHistory.clock (atWord blank enc (w.take N)) = SlotClockBirth.atTime (2 ^ (g + 5)) := by
      rw [at_clock, hleft]
    have hb := ClockHistoryPeriods.block_layout blank enc (g + 5) (by omega) a rest u v hu hv
      (atWord blank enc (w.take N)) (at_phase blank enc _) hc hLayout hsize
      (by rw [hrest]; omega) (by rw [hrest]; omega)
    rw [hrun, hr]
    rw [huv] at hb
    exact hb.2

/-- info: 'PalPeg.ClockHistoryInvariant.actual_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms actual_window

/-- info: 'PalPeg.ClockHistoryInvariant.actual_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms actual_dyadic

end PalPeg.ClockHistoryInvariant
