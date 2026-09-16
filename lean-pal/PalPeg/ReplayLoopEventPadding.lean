import PalPeg.ReplayLoopEventCut

set_option autoImplicit false
namespace PalPeg.ReplayLoopEventPadding
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ReplayLoop PalPeg.ReplayLoopEvents
variable {Terminal Q : Type} [Fintype Q] [DecidableEq Q] {k t B : ℕ}
local instance : DecidableEq (Control Q B) := inferInstance

theorem step_blankEq (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal)
    {x y : SConfig (Control Q B) (Fin k) (4 + t)} (h : ConfigBlankEq M.blank x y)
    (e : Event Terminal) :
    ConfigBlankEq M.blank (step M hB enc decode x e) (step M hB enc decode y e) := by
  cases e with
  | tick => exact (worker M hB decode).microStep_blankEq h none
  | arrival a =>
    cases x with
    | mk q T =>
      cases y with
      | mk r U =>
        obtain ⟨hq, ht⟩ := h
        change q = r at hq
        subst r
        refine ⟨rfl, ?_⟩
        intro j
        change STape.BlankEq M.blank
          ((T j).applyAction M.blank (if j = buf (q.2.1 3) then (enc a, .right) else ((T j).focus, .stay)))
          ((U j).applyAction M.blank (if j = buf (q.2.1 3) then (enc a, .right) else ((U j).focus, .stay)))
        rw [(ht j).focus]
        exact (ht j).applyAction _

/-- Right-blank padding is preserved under arbitrary arrival/tick streams,
including arbitrarily many phase changes and physical role rotations. -/
theorem run_blankEq (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (es : List (Event Terminal))
    {x y : SConfig (Control Q B) (Fin k) (4 + t)} (h : ConfigBlankEq M.blank x y) :
    ConfigBlankEq M.blank (run M hB enc decode es x) (run M hB enc decode es y) := by
  induction es generalizing x y with
  | nil => exact h
  | cons e es ih => exact ih (step_blankEq M hB enc decode h e)

/-- Any exact event-stream result transfers to a recycled physical
configuration without normalizing or replacing any of its tapes. -/
theorem transfer (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (es : List (Event Terminal))
    {x y z : SConfig (Control Q B) (Fin k) (4 + t)} (h : ConfigBlankEq M.blank x y)
    (hr : run M hB enc decode es y = z) :
    ConfigBlankEq M.blank (run M hB enc decode es x) z := by
  rw [← hr]
  exact run_blankEq M hB enc decode es h

/-- Exact phase lemmas can be composed through observationally padded
intermediate states, without resetting the machine between event segments. -/
theorem compose (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (as bs : List (Event Terminal))
    {x y z : SConfig (Control Q B) (Fin k) (4 + t)}
    (ha : ConfigBlankEq M.blank (run M hB enc decode as x) y)
    (hb : ConfigBlankEq M.blank (run M hB enc decode bs y) z) :
    ConfigBlankEq M.blank (run M hB enc decode (as ++ bs) x) z := by
  rw [ReplayLoopEventCut.run_append]
  have hh := run_blankEq M hB enc decode bs ha
  exact ⟨hh.1.trans hb.1, fun j => (hh.2 j).trans (hb.2 j)⟩

/-- Arbitrarily many verified phase segments compose on the same physical
tapes. This does not assume a fresh canonical tape at any phase boundary. -/
theorem segments (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal)
    (chunks : List (List (Event Terminal)))
    (states : ℕ → SConfig (Control Q B) (Fin k) (4 + t))
    (hs : ∀ i es, chunks[i]? = some es →
      ConfigBlankEq M.blank (run M hB enc decode es (states i)) (states (i + 1))) :
    ConfigBlankEq M.blank (run M hB enc decode chunks.flatten (states 0)) (states chunks.length) := by
  induction chunks generalizing states with
  | nil => exact ⟨rfl, fun _ => STape.BlankEq.refl _ _⟩
  | cons es chunks ih =>
    have hfirst := hs 0 es rfl
    have hrest := ih (fun i => states (i + 1)) (by
      intro i e he
      exact hs (i + 1) e he)
    exact compose M hB enc decode es chunks.flatten hfirst hrest

/-- info: 'PalPeg.ReplayLoopEventPadding.segments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms segments

/-- info: 'PalPeg.ReplayLoopEventPadding.run_blankEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_blankEq

end PalPeg.ReplayLoopEventPadding
