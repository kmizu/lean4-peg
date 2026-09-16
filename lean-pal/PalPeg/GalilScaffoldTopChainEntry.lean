import PalPeg.GalilScaffoldTopChainCredits

/-!
# The chain entry with credits: `watchStart`

Composing the start tick (credit `sm`), the copy walk (`bs`), the copy end
(credit `dm`) and the back walk (`cs`) gives the watch state
`watchStart ver c ys b (run (start radius) (prepEvents sm dm bs cs))` of the
lower layer, for a found search with positive unary radius. This is the
chain-side content of `found_supplied_restart`: the chain enters watch with
exactly the credits the scan events supplied.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter

theorem start_eq (radius : Counter) : GalilScaffoldChainCredits.start radius = creditsOf radius radius := rfl

theorem creditsOf_eta (s : GalilScaffoldChainCredits.State) : creditsOf s.margin s.lag = s := rfl

/-- The lag of a credit run is unary: it only increments. -/
theorem run_lag_ofNat (es : List (Bool × Bool)) : ∀ (margin : Counter) (k : ℕ),
    ∃ k', (GalilScaffoldChainCredits.run (creditsOf margin (ofNat k)) es).lag = ofNat k' ∧ k ≤ k' := by
  induction es with
  | nil => intro margin k; exact ⟨k, rfl, le_refl _⟩
  | cons e es ih =>
    intro margin k
    obtain ⟨e1, e2⟩ := e
    have hstep : GalilScaffoldChainCredits.step (creditsOf margin (ofNat k)) (e1, e2) =
        creditsOf (if e2 then inc (if e1 then GalilScaffoldChainCredits.decFour margin else margin)
          else (if e1 then GalilScaffoldChainCredits.decFour margin else margin))
          (if e2 then ofNat (k+1) else ofNat k) := by
      cases e1 <;> cases e2 <;> simp [GalilScaffoldChainCredits.step, creditsOf, inc_ofNat]
    show ∃ k', (GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.step (creditsOf margin (ofNat k)) (e1, e2)) es).lag = ofNat k' ∧ k ≤ k'
    rw [hstep]
    cases e2
    · obtain ⟨k', h1, h2⟩ := ih _ k
      exact ⟨k', by simpa using h1, h2⟩
    · obtain ⟨k', h1, h2⟩ := ih _ (k+1)
      exact ⟨k', by simpa using h1, by omega⟩

/-- The chain from `chain.start()` (credited `sm` in the same tick) through
copy, end and back to `watchStart`. -/
theorem found_to_watchStart {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (ver : GalilScaffoldInputHead.PlaceHead) (r0 : ℕ) (sm dm : Bool) :
    ∃ (h : ℕ) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate w lower h ∧ GalilScaffoldPlace.read p = some c ∧ ys.length + 1 = h ∧
      ∀ (bs cs : List Bool), bs.length = h → cs.length = h+1 →
        ∃ x1 : ChainVM,
          (if sm then ChainMatched (chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) x1
            else x1 = chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) ∧
          ChainTicks (bs ++ dm :: cs) x1
            (.watch (watchStart ver c ys b (GalilScaffoldChainCredits.run
              (GalilScaffoldChainCredits.start (ofNat (r0+1)))
              (GalilScaffoldChainCredits.prepEvents sm dm bs cs)))) := by
  obtain ⟨h, c, u, q, ys, b, hcand, hread, hcopy, hu, hpos, hfocus, hback, hys, _⟩ :=
    GalilScaffoldChainPeriod.found_start_back p hw hr hs ht hv
  have hlen : ys.length + 1 = h := by
    have hwl : w.length ≤ (GalilScaffoldPlace.stream p).length := by
      rw [hw, List.length_take]; omega
    have h4 := hcand.2.1
    have := congrArg List.length hys
    simp only [List.length_append, List.length_singleton, List.length_take, List.length_drop] at this
    omega
  refine ⟨h, c, ys, b, hcand, hread, hlen, ?_⟩
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

#print axioms found_to_watchStart

end PalPeg.GalilScaffoldChainInputSupply
