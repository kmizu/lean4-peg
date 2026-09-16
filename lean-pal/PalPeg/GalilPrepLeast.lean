import PalPeg.GalilScaffoldTopWatchSegE
import PalPeg.GalilMinimalPeriod

/-!
# The prepared semiperiod is the DP's least candidate

`prep_watch_start` (`PalPeg/GalilScaffoldTopWatchSegE.lean`) produces a
semiperiod `h` with `Candidate w lower h`, but its existential hides the
fact that `h` is the cursor on OUTPUT, hence the *least* candidate.  This
file re-runs the same chain (`found_copy_walk` → `found_start_back` →
`found_to_watchStart` → `prep_watch_start`) carrying one extra conjunct,
`(denote y.config).pos 11 = h`, all the way out, and concludes with
`result_least` that no candidate lies below `h`.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## The two small facts about `Result` -/

/-- A `Result` that has any candidate at all cannot be the failure branch. -/
theorem result_pc_of_candidate {w : List (Fin 3)} {lower h : ℕ} {y : GalilFppWide.Config 12}
    (hres : GalilDpCorrect.Result w lower 0 y) (hc : GalilDpCorrect.Candidate w lower h) :
    y.pc = 346 := by
  rcases hres with ⟨k, _, _, _, hpc, _, _⟩ | ⟨_, hnone⟩
  · exact hpc
  · exact absurd hc (hnone h (Nat.zero_le _))

/-- If the OUTPUT cursor of a successful `Result` is `h`, then `h` is the least
candidate: nothing below it is a candidate. -/
theorem no_candidate_below_of_least {w : List (Fin 3)} {lower h : ℕ} {y : GalilFppWide.Config 12}
    (hres : GalilDpCorrect.Result w lower 0 y) (hpc : y.pc = 346) (hpos : y.pos 11 = h) :
    ∀ g, g < h → ¬ GalilDpCorrect.Candidate w lower g := by
  obtain ⟨k, _, hk, hmin⟩ := result_least hres hpc
  have hkh : k = h := by rw [← hk, hpos]
  subst hkh
  exact hmin

#print axioms result_pc_of_candidate
#print axioms no_candidate_below_of_least

/-! ## The chain, re-run with the OUTPUT cursor exposed -/

/-- `GalilScaffoldChainAnswer.found_copy_walk` with the OUTPUT cursor exposed:
the length `h` of the copy walk is exactly `(denote y.config).pos 11`. -/
theorem found_copy_walk_least {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {as : List Bool}
    {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run)
    (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config)) :
    ∃ h u q xs, GalilDpCorrect.Candidate w lower h ∧
      GalilScaffoldChainAnswer.CopyWalk (y.config.tapes 11) GalilScaffoldCounter.reset p h u
        (GalilScaffoldCounter.ofNat h) q xs ∧
      u.focus = 4 ∧ GalilScaffoldCounter.positive (GalilScaffoldCounter.ofNat h) = true ∧
      xs = ((GalilScaffoldPlace.stream p).drop 1).take h ∧
      GalilScaffoldPlace.stream q = (GalilScaffoldPlace.stream p).drop h ∧
      (GalilScaffoldProgram.denote y.config).pos 11 = h := by
  obtain ⟨h, hc, _, hout, hpos, _, _⟩ := GalilScaffoldChainAnswer.found_output hr hs ht hv
  have hh : 0 < h := by have := hc.1; omega
  obtain ⟨u, ha, hf, hpositive⟩ :=
    GalilScaffoldChainAnswer.answer_copy_done h hh (y.config.tapes 11) hout hpos
  have hlen : h < (GalilScaffoldPlace.stream p).length := by
    have hb := hc.2.1
    rw [hw, List.length_take] at hb
    omega
  obtain ⟨q, xs, hcopy, hxs, hq⟩ := GalilScaffoldChainAnswer.copy_walk ha p hlen
  exact ⟨h, u, q, xs, hc, hcopy, hf, hpositive, hxs, hq, hpos⟩

#print axioms found_copy_walk_least

/-- `GalilScaffoldChainPeriod.found_start_back` with the OUTPUT cursor exposed. -/
theorem found_start_back_least
    {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ}
    (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run)
    (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config)) :
    ∃ h center u q ys b,
      GalilDpCorrect.Candidate w lower h ∧
      GalilScaffoldPlace.read p = some center ∧
      GalilScaffoldChainPeriod.Copy (y.config.tapes 11) GalilScaffoldCounter.reset p
        (GalilScaffoldChainPeriod.start center) h u
        (GalilScaffoldCounter.ofNat h) q
        (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start center) (ys ++ [b])) ∧
      u.focus = 4 ∧ GalilScaffoldCounter.positive (GalilScaffoldCounter.ofNat h) = true ∧
      (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start center) (ys ++ [b])).focus
        = .plain b ∧
      GalilScaffoldChainPeriod.Back (GalilScaffoldChainPeriod.write
        (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start center) (ys ++ [b]))
        (.last b)) (h+1)
        (GalilScaffoldChainPeriod.moveRight ⟨[], .first center,
          ys.map GalilScaffoldChainPeriod.Token.plain ++ [.last b]⟩) ∧
      ys ++ [b] = ((GalilScaffoldPlace.stream p).drop 1).take h ∧
      GalilScaffoldPlace.stream q = (GalilScaffoldPlace.stream p).drop h ∧
      (GalilScaffoldProgram.denote y.config).pos 11 = h := by
  obtain ⟨h,u,q,xs,hc,hcopy,hu,hpositive,hxs,hq,hcur⟩ :=
    found_copy_walk_least p hw hr hs ht hv
  have hh : 0 < h := by have := hc.1; omega
  have hne : GalilScaffoldPlace.stream p ≠ [] := by
    intro he
    have hb := hc.2.1
    rw [hw, he] at hb
    simp at hb
  cases he : GalilScaffoldPlace.read p with
  | none => exact False.elim (hne ((GalilScaffoldPlace.read_none p).mp he))
  | some center =>
    obtain ⟨ys,b,hparts,hperiod,hplain,hback⟩ :=
      GalilScaffoldChainPeriod.copy_then_back hcopy hh center
    rw [hparts] at hperiod hplain hback hxs
    exact ⟨h,center,u,q,ys,b,hc,rfl,hperiod,hu,hpositive,hplain,hback,hxs,hq,hcur⟩

#print axioms found_start_back_least

theorem found_to_watchStart_least {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (ver : GalilScaffoldInputHead.PlaceHead) (r0 : ℕ) (sm dm : Bool) :
    ∃ (h : ℕ) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate w lower h ∧ GalilScaffoldPlace.read p = some c ∧ ys.length + 1 = h ∧
      (GalilScaffoldProgram.denote y.config).pc = 346 ∧
      (GalilScaffoldProgram.denote y.config).pos 11 = h ∧
      ∀ (bs cs : List Bool), bs.length = h → cs.length = h+1 →
        ∃ x1 : ChainVM,
          (if sm then ChainMatched (chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) x1
            else x1 = chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) ∧
          ChainTicks (bs ++ dm :: cs) x1
            (.watch (watchStart ver c ys b (GalilScaffoldChainCredits.run
              (GalilScaffoldChainCredits.start (ofNat (r0+1)))
              (GalilScaffoldChainCredits.prepEvents sm dm bs cs)))) := by
  obtain ⟨h, c, u, q, ys, b, hcand, hread, hcopy, hu, hpos, hfocus, hback, hys, _, hcur⟩ :=
    found_start_back_least p hw hr hs ht hv
  have hlen : ys.length + 1 = h := by
    have hwl : w.length ≤ (GalilScaffoldPlace.stream p).length := by
      rw [hw, List.length_take]; omega
    have h4 := hcand.2.1
    have := congrArg List.length hys
    simp only [List.length_append, List.length_singleton, List.length_take, List.length_drop] at this
    omega
  refine ⟨h, c, ys, b, hcand, hread, hlen, result_pc_of_candidate hv hcand, hcur, ?_⟩
  intro bs cs hbs hcs
  -- the start tick
  let k0 : ℕ := if sm then r0+2 else r0+1
  let cr0 := GalilScaffoldChainCredits.step (GalilScaffoldChainCredits.start (ofNat (r0+1))) (false, sm)
  have hcr0 : cr0 = creditsOf (if sm then inc (ofNat (r0+1)) else ofNat (r0+1)) (ofNat k0) := by
    show GalilScaffoldChainCredits.step (creditsOf (ofNat (r0+1)) (ofNat (r0+1))) (false, sm) = _
    rw [step_idle]
    cases sm <;> simp [k0, inc_ofNat]
  have hk0 : 1 ≤ k0 := by cases sm <;> simp [k0]
  let x1 : ChainVM := .copy (y.config.tapes 11) reset p (GalilScaffoldChainPeriod.start c) cr0.lag cr0.margin ver
  refine ⟨x1, ?_, ?_⟩
  · cases sm
    · show x1 = chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))
      simp only [x1, hcr0, creditsOf, k0]
      rfl
    · show ChainMatched (chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) x1
      simp only [x1, hcr0, creditsOf, k0]
      rw [show r0+2 = r0+1+1 from rfl, ← inc_ofNat]
      exact .copy _ _ _ _ _ _ _
  · -- the copy ticks
    have h1 := copy_ticks h bs hbs cr0.lag cr0.margin ver hcopy
    rw [creditsOf_eta] at h1
    -- the end tick (credit `dm`)
    let cr1 := GalilScaffoldChainCredits.run cr0 (bs.map (fun b => (true, b)))
    let cr2 := GalilScaffoldChainCredits.step cr1 (false, dm)
    have hend : ChainTick dm (.copy u (ofNat h) q (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start c) (ys ++ [b])) cr1.lag cr1.margin ver)
        (.back (GalilScaffoldChainPeriod.write (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start c) (ys ++ [b])) (.last b))
          (ofNat h) cr2.lag cr2.margin ver) := by
      refine ⟨_, .copyEnd u (ofNat h) q _ cr1.lag cr1.margin ver b hu hpos hfocus, ?_⟩
      have : cr2 = creditsOf (if dm then inc cr1.margin else cr1.margin) (if dm then inc cr1.lag else cr1.lag) := by
        show GalilScaffoldChainCredits.step (creditsOf cr1.margin cr1.lag) (false, dm) = _
        exact step_idle cr1.margin cr1.lag dm
      rw [this]
      cases dm
      · rfl
      · exact .back _ _ _ _ _
    -- the lag is unary throughout
    obtain ⟨k1, hk1, hk1'⟩ := run_lag_ofNat (bs.map (fun b => (true, b))) cr0.margin k0
    have hcr1lag : cr1.lag = ofNat k1 := by
      have : cr0 = creditsOf cr0.margin (ofNat k0) := by rw [hcr0]; rfl
      show (GalilScaffoldChainCredits.run cr0 _).lag = _
      rw [this]; exact hk1
    let k2 : ℕ := if dm then k1+1 else k1
    have hcr2lag : cr2.lag = ofNat k2 := by
      have : cr2 = creditsOf (if dm then inc cr1.margin else cr1.margin) (if dm then inc cr1.lag else cr1.lag) :=
        step_idle cr1.margin cr1.lag dm
      rw [this]
      cases dm <;> simp [creditsOf, k2, hcr1lag, inc_ofNat]
    have hk2 : 1 ≤ k2 := by cases dm <;> simp [k2] <;> omega
    have hcr2' : cr2 = creditsOf cr2.margin (ofNat (k2 - 1 + 1)) := by
      rw [show k2 - 1 + 1 = k2 by omega, ← hcr2lag]; rfl
    have hcr2lag' : cr2.lag = ofNat (k2 - 1 + 1) := by rw [hcr2lag, show k2 - 1 + 1 = k2 by omega]
    have h3 := back_ticks (h+1) cs hcs (ofNat h) cr2.margin (k2 - 1) ver hback
    rw [← hcr2', ← hcr2lag'] at h3
    -- assemble
    have hfinal : GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start (ofNat (r0+1)))
        (GalilScaffoldChainCredits.prepEvents sm dm bs cs) =
        GalilScaffoldChainCredits.run cr2 (cs.map (fun b => (false, b))) := by
      simp only [GalilScaffoldChainCredits.prepEvents, GalilScaffoldChainCredits.run,
        GalilScaffoldChainCredits.run_append]
      rfl
    rw [hfinal]
    exact chainTicks_trans h1 (.cons (y := .back (GalilScaffoldChainPeriod.write
      (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start c) (ys ++ [b])) (.last b))
      (ofNat h) cr2.lag cr2.margin ver) hend h3)

#print axioms found_to_watchStart_least

/-! ## The strengthened preparation period -/

/-- `prep_watch_start` with the DP link exposed: the semiperiod `h` the chain
prepares is exactly the OUTPUT cursor of the successful DP result. -/
theorem prep_watch_start_least (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (ver : PlaceHead) (r0 : ℕ) (dm : Bool) :
    ∃ (h : ℕ) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate w lower h ∧ GalilScaffoldPlace.read p = some c ∧ ys.length + 1 = h ∧
      (GalilScaffoldProgram.denote y.config).pc = 346 ∧
      (GalilScaffoldProgram.denote y.config).pos 11 = h ∧
      ∀ (bs cs : List Bool), bs.length = h → cs.length = h+1 →
        ∀ (ch : ChainVM), ChainMatched (chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) ch →
        ∀ {c0 c1 : Control} {v0 v1 : GalilVM},
          WatchSegE P q first delay (bs ++ dm :: cs) c0 v0 c1 v1 → v0.chain = ch →
          v1.chain = .watch (watchStart ver c ys b (GalilScaffoldChainCredits.run
            (GalilScaffoldChainCredits.start (ofNat (r0+1)))
            (GalilScaffoldChainCredits.prepEvents true dm bs cs))) := by
  obtain ⟨h, c, ys, b, hcand, hread, hlen, hpc, hcur, hrest⟩ :=
    found_to_watchStart_least p hw hr hs ht hv ver r0 true dm
  refine ⟨h, c, ys, b, hcand, hread, hlen, hpc, hcur, ?_⟩
  intro bs cs hbs hcs ch hch c0 c1 v0 v1 hseg hv0
  obtain ⟨x1, hx1, hticks⟩ := hrest bs cs hbs hcs
  simp only [ite_true] at hx1
  have hx : ch = x1 := chainMatched_unique hch hx1
  subst hx
  obtain ⟨hch', _⟩ := watchSegE_events P q first delay hseg (by rw [hv0]; intro h0; rw [h0] at hch; cases hch)
  rw [hv0] at hch'
  exact chainTicks_unique hch' hticks

#print axioms prep_watch_start_least

/-- The full statement: the prepared semiperiod `h` is the OUTPUT cursor of the
DP result, hence the least candidate — no candidate lies below it. -/
theorem prep_least_no_candidate (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (ver : PlaceHead) (r0 : ℕ) (dm : Bool) :
    ∃ (h : ℕ) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate w lower h ∧ GalilScaffoldPlace.read p = some c ∧ ys.length + 1 = h ∧
      (GalilScaffoldProgram.denote y.config).pc = 346 ∧
      (GalilScaffoldProgram.denote y.config).pos 11 = h ∧
      (∀ g, g < h → ¬ GalilDpCorrect.Candidate w lower g) ∧
      ∀ (bs cs : List Bool), bs.length = h → cs.length = h+1 →
        ∀ (ch : ChainVM), ChainMatched (chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) ch →
        ∀ {c0 c1 : Control} {v0 v1 : GalilVM},
          WatchSegE P q first delay (bs ++ dm :: cs) c0 v0 c1 v1 → v0.chain = ch →
          v1.chain = .watch (watchStart ver c ys b (GalilScaffoldChainCredits.run
            (GalilScaffoldChainCredits.start (ofNat (r0+1)))
            (GalilScaffoldChainCredits.prepEvents true dm bs cs))) := by
  obtain ⟨h, c, ys, b, hcand, hread, hlen, hpc, hcur, hrest⟩ :=
    prep_watch_start_least P q first delay p hw hr hs ht hv ver r0 dm
  exact ⟨h, c, ys, b, hcand, hread, hlen, hpc, hcur,
    no_candidate_below_of_least hv hpc hcur, hrest⟩

#print axioms prep_least_no_candidate

end PalPeg.GalilScaffoldChainInputSupply
