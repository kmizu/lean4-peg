import PalPeg.GalilScaffoldChainVerifyRun

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainCatch
open GalilScaffoldChainVerifier GalilScaffoldCounter

theorem broken_preserved (s : State) (hb : s.control.broken = true) :
    (consume s).control.broken = true := by
  cases ht : GalilScaffoldChainConsume.symbol s.control.period.focus with
  | none => simp [consume, GalilScaffoldChainConsume.consume, ht]
  | some a =>
    by_cases ha : GalilScaffoldInputHead.read (right s.verifier) = some a
    all_goals simp [consume, GalilScaffoldChainConsume.consume, ht, ha, hb]

theorem run_unbroken {s n t} (hr : GalilScaffoldChainVerifyRun.Run s n t)
    (ht : t.control.broken = false) : s.control.broken = false := by
  induction hr with
  | stop s => exact ht
  | next s hp hr ih =>
    have hc := ih ht
    cases hb : s.control.broken
    · rfl
    · have he := broken_preserved s hb
      rw [hc] at he
      contradiction

/-- Enabled watch catch-up, excluding outer matched/shift/fallback events.
Each step has positive lag and a successful consume; only then lag.dec. -/
inductive Catch : State → Counter → ℕ → State → Counter → Prop
  | stop (s lag) : Catch s lag 0 s lag
  | next (s lag) {n t tail} (hl : positive lag = true)
      (hp : canRight s.verifier) (hb : s.control.broken = false)
      (hc : (consume s).control.broken = false)
      (hr : Catch (consume s) (dec lag) n t tail) : Catch s lag (n+1) t tail

theorem catch_run {s n t} (hr : GalilScaffoldChainVerifyRun.Run s n t)
    (ht : t.control.broken = false) (k : ℕ) :
    Catch s (ofNat (n+k)) n t (ofNat k) := by
  induction hr with
  | stop s => simpa using Catch.stop s (ofNat k)
  | @next s n t hp hr ih =>
    have hc := run_unbroken hr ht
    have hs := run_unbroken (GalilScaffoldChainVerifyRun.Run.next s hp hr) ht
    apply Catch.next s (ofNat (n+1+k)) _ hp hs hc
    · simpa [show n+1+k = (n+k)+1 by omega, dec_ofNat_succ] using ih ht
    · apply (positive_iff _ (ofNat_canonical _)).mpr
      rw [ofNat_value]
      omega

/-- Enough lag to cover two bounces yields the same phase4 verifier state
and an exact residual lag, not a separately chosen control execution. -/
theorem four_boundaries (center b : Fin 3) (xs : List (Fin 3))
    (p q : GalilScaffoldInputHead.PlaceHead)
    (hr : GalilScaffoldChainVerifyRun.Reads p
      (GalilScaffoldChainSweep.bounce center b xs ++ GalilScaffoldChainSweep.bounce center b xs) q)
    (k : ℕ) :
    ∃ t, Catch ⟨p,GalilScaffoldChainConsume.ready center xs b⟩
      (ofNat (4*(xs.length+1)+k)) (4*(xs.length+1)) t (ofNat k) ∧
      t.verifier = q ∧ t.control.phase = 4 ∧
      value t.control.boundary = 4*(xs.length+1) ∧
      value t.control.last = 3*(xs.length+1) ∧ t.control.broken = false := by
  obtain ⟨t,hRun,hq,hperiod,hd,hboundary,hlast,hphase,hforward,hbroken⟩ :=
    GalilScaffoldChainVerifyRun.four_boundaries center b xs p q hr
  exact ⟨t,catch_run hRun hbroken k,hq,hphase,hboundary,hlast,hbroken⟩

/-- Fresh watch/only=false branch of Scala canShift. In this projection
unbroken means that the uninterrupted watch execution has not left watch. -/
def freshShiftGuard (s : State) (lag margin : Counter) : Bool :=
  !s.control.broken && zero lag && decide (s.control.phase = 4) && !negative margin

theorem caught_shift_guard (center b : Fin 3) (xs : List (Fin 3))
    (p q : GalilScaffoldInputHead.PlaceHead)
    (hr : GalilScaffoldChainVerifyRun.Reads p
      (GalilScaffoldChainSweep.bounce center b xs ++ GalilScaffoldChainSweep.bounce center b xs) q)
    (margin : Counter) (hm : Canonical margin) (hv : 0 ≤ value margin) :
    ∃ t, Catch ⟨p,GalilScaffoldChainConsume.ready center xs b⟩
      (ofNat (4*(xs.length+1))) (4*(xs.length+1)) t (ofNat 0) ∧
      t.verifier = q ∧ freshShiftGuard t (ofNat 0) margin = true ∧
      value t.control.last = 3*(xs.length+1) := by
  obtain ⟨t,hc,hq,hphase,hboundary,hlast,hbroken⟩ := four_boundaries center b xs p q hr 0
  have hn : negative margin = false := by
    cases he : negative margin
    · rfl
    · have hv' := (negative_iff _ hm).mp he
      omega
  refine ⟨t,by simpa using hc,hq,?_,hlast⟩
  simp [freshShiftGuard,hphase,hbroken,hn,ofNat,zero]

theorem canonical_nat (c : Counter) (hc : Canonical c) (n : ℕ) (hv : value c = n) :
    c = ofNat n := by
  have hn : c.neg = [] := by
    rcases hc with hp | hn
    · have hv' := hv
      simp only [value, hp, List.length_nil, Nat.cast_zero, zero_sub] at hv'
      have hl : c.neg.length = 0 := by omega
      exact List.length_eq_zero_iff.mp hl
    · exact hn
  have hl : c.pos.length = n := by simp only [value, hn, List.length_nil, Nat.cast_zero, sub_zero] at hv; omega
  have hp : c.pos = List.replicate n () := by
    apply List.ext_getElem
    · simpa using hl
    · intro i hi hj
      exact Subsingleton.elim _ _
  cases c
  simp_all [ofNat]

theorem prepared_margin (radius : Counter) (sm dm : Bool) (bs cs : List Bool) :
    let final := GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
      (GalilScaffoldChainCredits.prepEvents sm dm bs cs)
    value final.margin = value final.lag - 4*(bs.length : ℤ) := by
  have hv := GalilScaffoldChainCredits.prep_value radius sm dm bs cs
  dsimp only at *
  omega

/-- The margin premise of the fresh shift guard is obtained from the
same preparation ledger, not supplied independently. Balanced lag=4h
is still an explicit boundary condition. -/
theorem prepared_shift_guard (center b : Fin 3) (xs : List (Fin 3))
    (p q : GalilScaffoldInputHead.PlaceHead)
    (hr : GalilScaffoldChainVerifyRun.Reads p
      (GalilScaffoldChainSweep.bounce center b xs ++ GalilScaffoldChainSweep.bounce center b xs) q)
    (radius : Counter) (hc : Canonical radius) (sm dm : Bool) (bs cs : List Bool)
    (hb : bs.length = xs.length+1)
    (final : GalilScaffoldChainCredits.State)
    (he : final = GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
      (GalilScaffoldChainCredits.prepEvents sm dm bs cs))
    (hl : value final.lag = 4*(xs.length+1)) :
    ∃ t, Catch ⟨p,GalilScaffoldChainConsume.ready center xs b⟩ final.lag
      (4*(xs.length+1)) t (ofNat 0) ∧
      t.verifier = q ∧ freshShiftGuard t (ofNat 0) final.margin = true ∧
      value final.margin = 0 := by
  have hk := GalilScaffoldChainCredits.run_canonical
    (GalilScaffoldChainCredits.start radius) (GalilScaffoldChainCredits.prepEvents sm dm bs cs) hc hc
  rw [← he] at hk
  have hm := prepared_margin radius sm dm bs cs
  dsimp only at hm
  rw [← he, hb, hl] at hm
  have hm0 : value final.margin = 0 := by omega
  have hlag : final.lag = ofNat (4*(xs.length+1)) :=
    canonical_nat final.lag hk.2 _ (by simpa using hl)
  obtain ⟨t,hcatch,hq,hguard,_⟩ := caught_shift_guard center b xs p q hr final.margin hk.1 (by omega)
  rw [← hlag] at hcatch
  exact ⟨t,hcatch,hq,hguard,hm0⟩

theorem phase4_consume (s : GalilScaffoldChainConsume.State)
    (seen : Option (Fin 3)) (hp : s.phase = 4) :
    (GalilScaffoldChainConsume.consume s seen).phase = 4 := by
  cases ht : GalilScaffoldChainConsume.symbol s.period.focus with
  | none => simp [GalilScaffoldChainConsume.consume, ht, hp]
  | some a =>
    by_cases ha : seen = some a
    all_goals simp [GalilScaffoldChainConsume.consume, ht, ha, hp, GalilScaffoldChainConsume.advancePhase]

theorem phase4_run (s : GalilScaffoldChainConsume.State) (xs : List (Fin 3))
    (hp : s.phase = 4) : (GalilScaffoldChainSweep.run s xs).phase = 4 := by
  induction xs generalizing s with
  | nil => exact hp
  | cons a xs ih => exact ih _ (phase4_consume s (some a) hp)

/-- General nonnegative-margin preparation: consume all lag, including a
successful suffix beyond the fourth boundary. No lag=4h restriction. -/
theorem prepared_shift_after (center b : Fin 3) (xs suffix : List (Fin 3))
    (p q : GalilScaffoldInputHead.PlaceHead)
    (hr : GalilScaffoldChainVerifyRun.Reads p
      ((GalilScaffoldChainSweep.bounce center b xs ++ GalilScaffoldChainSweep.bounce center b xs) ++ suffix) q)
    (radius : Counter) (hc : Canonical radius) (sm dm : Bool) (bs cs : List Bool)
    (hb : bs.length = xs.length+1) (final : GalilScaffoldChainCredits.State)
    (he : final = GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
      (GalilScaffoldChainCredits.prepEvents sm dm bs cs))
    (hl : value final.lag = 4*(xs.length+1) + suffix.length)
    (hsuccess : (GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready center xs b)
      ((GalilScaffoldChainSweep.bounce center b xs ++ GalilScaffoldChainSweep.bounce center b xs) ++ suffix)).broken = false) :
    ∃ t, Catch ⟨p,GalilScaffoldChainConsume.ready center xs b⟩ final.lag
      (4*(xs.length+1)+suffix.length) t (ofNat 0) ∧ t.verifier = q ∧
      freshShiftGuard t (ofNat 0) final.margin = true ∧ value final.margin = suffix.length := by
  have hk := GalilScaffoldChainCredits.run_canonical
    (GalilScaffoldChainCredits.start radius) (GalilScaffoldChainCredits.prepEvents sm dm bs cs) hc hc
  rw [← he] at hk
  have hm := prepared_margin radius sm dm bs cs
  dsimp only at hm
  rw [← he, hb, hl] at hm
  have hmval : value final.margin = suffix.length := by omega
  have hlag : final.lag = ofNat (4*(xs.length+1)+suffix.length) :=
    canonical_nat final.lag hk.2 _ (by simpa using hl)
  have hruns := GalilScaffoldChainVerifyRun.realize hr (GalilScaffoldChainConsume.ready center xs b)
  have hlength : ((GalilScaffoldChainSweep.bounce center b xs ++
      GalilScaffoldChainSweep.bounce center b xs) ++ suffix).length = 4*(xs.length+1)+suffix.length := by
    simp [GalilScaffoldChainSweep.bounce]; omega
  rw [hlength] at hruns
  have hcatch := catch_run hruns hsuccess 0
  simp only [Nat.add_zero] at hcatch
  rw [← hlag] at hcatch
  have hfour := GalilScaffoldChainSweep.four_boundaries center b xs
  have hphase := phase4_run _ suffix hfour.2.2.2.2.1
  rw [← GalilScaffoldChainSweep.run_append] at hphase
  have hn : negative final.margin = false := by
    cases hn : negative final.margin
    · rfl
    · have hv := (negative_iff _ hk.1).mp hn
      omega
  refine ⟨_,hcatch,rfl,?_,hmval⟩
  simp only [List.append_assoc] at hsuccess hphase
  simp [freshShiftGuard,hsuccess,hphase,ofNat,zero,hn]

#print axioms prepared_shift_after
#print axioms prepared_shift_guard
#print axioms canonical_nat
#print axioms caught_shift_guard
#print axioms four_boundaries
#print axioms catch_run
end PalPeg.GalilScaffoldChainCatch
