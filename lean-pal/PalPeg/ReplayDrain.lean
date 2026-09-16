import PalPeg.ReplayPaddedHandoff
import PalPeg.ReplayContraction

set_option autoImplicit false
namespace PalPeg.ReplayDrain
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ReplayLoop PalPeg.ReplayLoopEvents
open PalPeg.ReplayPaddedHandoff
variable {Terminal Q : Type} [Fintype Q] [DecidableEq Q] {k t B : ℕ}
local instance : DecidableEq (Control Q B) := inferInstance

/-- Iterate every cycle whose worst-case budget fits. The resulting
suffix may still execute a partial cycle: this is not a zero-lag claim.
The word equation tracks all completed and still-pending input exactly. -/
theorem drain (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal)
    (hdec : ∀ a, decode (enc a) = a) (henc : ∀ a, enc a ≠ M.blank)
    (roles : Fin 4 ≃ Fin 4) (es : List (Event Terminal))
    (old : List (Fin k)) (ho : M.blank ∉ old) (batch pending : List Terminal)
    (x : SConfig Q (Fin k) t) (actual : SConfig (Control Q B) (Fin k) (4 + t))
    (hactual : ConfigBlankEq M.blank actual (boundary M.blank enc roles old batch pending x)) :
    ∃ pre post done roles' old' batch' pending',
      es = pre ++ post ∧ M.blank ∉ old' ∧
      batch ++ pending ++ arrivals pre = done ++ batch' ++ pending' ∧
      work post < max old'.length batch'.length + batch'.length * B + 4 ∧
      ConfigBlankEq M.blank (run M hB enc decode es actual)
        (run M hB enc decode post
          (boundary M.blank enc roles' old' batch' pending' (done.foldl M.sRound x))) := by
  generalize hn : work es = n
  induction n using Nat.strong_induction_on generalizing roles es old batch pending x actual with
  | h n ih =>
    by_cases hb : max old.length batch.length + batch.length * B + 4 ≤ work es
    · obtain ⟨seg, rest, he, _, hpos, hr⟩ := boundary_cycle M hB enc decode hdec henc
        roles es old ho batch pending x hb actual hactual
      have hwork : work rest < n := by
        rw [he, ReplayLoopEventCut.work_append] at hn
        omega
      have hnew : M.blank ∉ batch.map enc := by
        intro h
        obtain ⟨a, _, ha⟩ := List.mem_map.mp h
        exact henc a ha
      let next := boundary (B := B) M.blank enc (rotate.trans roles) (batch.map enc)
        (pending ++ arrivals seg) [] (batch.foldl M.sRound x)
      obtain ⟨pre, post, done, roles', old', batch', pending', he', ho', hc, ht, hh⟩ :=
        ih (work rest) hwork (rotate.trans roles) rest (batch.map enc) hnew
          (pending ++ arrivals seg) [] (batch.foldl M.sRound x) next
          ⟨rfl, fun j => STape.BlankEq.refl _ _⟩ rfl
      refine ⟨seg ++ pre, post, batch ++ done, roles', old', batch', pending', ?_, ho', ?_, ht, ?_⟩
      · rw [he, he', List.append_assoc]
      · have hc' := congrArg (fun w => batch ++ w) hc
        simpa [arrivals, List.filterMap_append, List.append_assoc] using hc'
      · simp only [List.foldl_append]
        exact ⟨hr.1.trans hh.1, fun j => (hr.2 j).trans (hh.2 j)⟩
    · refine ⟨[], es, [], roles, old, batch, pending, by simp, ho, by simp [arrivals],
        by omega, ?_⟩
      exact ReplayLoopEventPadding.run_blankEq M hB enc decode es hactual

/-- On the actual fixed-speed input trace, each concrete boundary cycle
has the contraction bound; no separate cycle-time assumption is needed. -/
theorem trace_cycle (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal)
    (hdec : ∀ a, decode (enc a) = a) (henc : ∀ a, enc a ≠ M.blank)
    (input : List Terminal) (before es : List (Event Terminal))
    (htrace : events (ReplayContraction.speed B) input = before ++ es)
    (roles : Fin 4 ≃ Fin 4) (old : List (Fin k)) (ho : M.blank ∉ old)
    (batch pending : List Terminal) (x : SConfig Q (Fin k) t)
    (hbudget : max old.length batch.length + batch.length * B + 4 ≤ work es)
    (actual : SConfig (Control Q B) (Fin k) (4 + t))
    (hactual : ConfigBlankEq M.blank actual (boundary M.blank enc roles old batch pending x)) :
    ∃ seg post, es = seg ++ post ∧
      work seg ≤ max old.length batch.length + batch.length * B + 4 ∧
      2 ≤ work seg ∧
      (pending ++ arrivals seg).length ≤ pending.length + max old.length batch.length / 8 + 2 ∧
      ConfigBlankEq M.blank (run M hB enc decode es actual)
        (run M hB enc decode post
          (boundary M.blank enc (rotate.trans roles) (batch.map enc)
            (pending ++ arrivals seg) [] (batch.foldl M.sRound x))) := by
  obtain ⟨seg, post, he, hw, hpos, hr⟩ := boundary_cycle M hB enc decode hdec henc
    roles es old ho batch pending x hbudget actual hactual
  have ht : events (ReplayContraction.speed B) input = before ++ seg ++ post := by
    rw [htrace, he, List.append_assoc]
  have hf := ReplayContraction.segment_shrink B input before seg post ht old.length batch.length hw
  refine ⟨seg, post, he, hw, hpos, ?_, hr⟩
  rw [List.length_append]
  omega

/-- info: 'PalPeg.ReplayDrain.trace_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_cycle

/-- info: 'PalPeg.ReplayDrain.drain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms drain

end PalPeg.ReplayDrain
