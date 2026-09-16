import PalPeg.GalilScaffoldChainLag

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainWatchTrace
open GalilScaffoldChainWatch GalilScaffoldCounter

structure Trace (s : GalilScaffoldChainVerifier.State) (xs : List (Fin 3))
    (t : GalilScaffoldChainVerifier.State) : Prop where
  reads : GalilScaffoldChainVerifyRun.Reads s.verifier xs t.verifier
  control : t.control = GalilScaffoldChainSweep.run s.control xs
  distance : value t.control.distance = value s.control.distance + (xs.length : ℤ)
  broken : t.control.broken = s.control.broken

theorem empty (s : GalilScaffoldChainVerifier.State) : Trace s [] s :=
  ⟨.stop _,rfl,by simp,rfl⟩

theorem one {s : State} (hg : Good s) :
    ∃ a, Trace s.machine [a] (GalilScaffoldChainVerifier.consume s.machine) := by
  obtain ⟨hp,a,ht,ha⟩ := hg
  have hv := GalilScaffoldChainVerifier.consume_agrees s.machine a ht ha
  refine ⟨a,⟨GalilScaffoldChainVerifyRun.Reads.next _ a hp ha (.stop _),?_,?_,hv.2⟩⟩
  · simp [GalilScaffoldChainVerifier.consume,ha,GalilScaffoldChainSweep.run]
  · simpa using hv.1

theorem append {s m t xs ys} (h1 : Trace s xs m) (h2 : Trace m ys t) :
    Trace s (xs ++ ys) t := by
  refine ⟨GalilScaffoldChainVerifyRun.reads_append h1.reads h2.reads,?_,?_,h2.broken.trans h1.broken⟩
  · rw [GalilScaffoldChainSweep.run_append,← h1.control,← h2.control]
  · rw [h2.distance,h1.distance,List.length_append,Nat.cast_add]
    omega

theorem internal_trace {s t : State} (hr : Internal s t) :
    ∃ xs, Trace s.machine xs t.machine ∧ xs.length ≤ 1 := by
  cases hr with
  | idle => exact ⟨[],empty _,by simp⟩
  | take hp hg =>
    obtain ⟨a,ha⟩ := one hg
    exact ⟨[a],ha,by simp⟩

theorem outer_trace {s t : State} {b : Bool} (hr : Outer s b t) :
    ∃ xs, Trace s.machine xs t.machine ∧ xs.length ≤ 1 := by
  cases hr with
  | idle => exact ⟨[],empty _,by simp⟩
  | queued hz => exact ⟨[],empty _,by simp⟩
  | immediate hz hg =>
    obtain ⟨a,ha⟩ := one hg
    exact ⟨[a],ha,by simp⟩

theorem tick_trace {s t : State} {b : Bool} (hr : Tick s b t) :
    ∃ xs, Trace s.machine xs t.machine ∧ xs.length ≤ 2 := by
  cases hr with
  | step hi ho =>
    obtain ⟨xs,hx,hlx⟩ := internal_trace hi
    obtain ⟨ys,hy,hly⟩ := outer_trace ho
    exact ⟨xs ++ ys,append hx hy,by simp; omega⟩

/-- Flatten the same watch execution, preserving internal-before-outer
order and the actual verifier, into its successful consume word. -/
theorem run_trace {s t : State} {bs : List Bool} (hr : Run s bs t) :
    ∃ xs, Trace s.machine xs t.machine ∧ xs.length ≤ 2*bs.length := by
  induction hr with
  | stop s => exact ⟨[],empty _,by simp⟩
  | next ht hr ih =>
    obtain ⟨xs,hx,hlx⟩ := tick_trace ht
    obtain ⟨ys,hy,hly⟩ := ih
    exact ⟨xs ++ ys,append hx hy,by simp; omega⟩

theorem four_prefix {s t : GalilScaffoldChainVerifier.State}
    (center b : Fin 3) (xs suffix : List (Fin 3))
    (hs : s.control = GalilScaffoldChainConsume.ready center xs b)
    (ht : Trace s ((GalilScaffoldChainSweep.bounce center b xs ++
      GalilScaffoldChainSweep.bounce center b xs) ++ suffix) t) :
    t.control.phase = 4 ∧ 4*(xs.length+1) ≤ value t.control.distance ∧
      t.control.broken = false := by
  have hf := GalilScaffoldChainSweep.four_boundaries center b xs
  have hp := GalilScaffoldChainCatch.phase4_run _ suffix hf.2.2.2.2.1
  have hd := ht.distance
  have hb := ht.broken
  rw [hs] at hd hb
  have hl : ((GalilScaffoldChainSweep.bounce center b xs ++
      GalilScaffoldChainSweep.bounce center b xs) ++ suffix).length =
      4*(xs.length+1)+suffix.length := by simp [GalilScaffoldChainSweep.bounce]; omega
  rw [hl] at hd
  have hz : value (GalilScaffoldChainConsume.ready center xs b).distance = 0 := rfl
  rw [hz,zero_add] at hd
  change t.control.broken = false at hb
  refine ⟨?_,by omega,hb⟩
  rw [ht.control,hs,GalilScaffoldChainSweep.run_append]
  exact hp

/-- Consume-word phase and distance facts are now about the very same
interleaved watch run used for the lag/margin shift proof. -/
theorem shift_from_trace {s t : State} {bs : List Bool} (hr : Run s bs t)
    (hc : CanonicalState s) (center b : Fin 3) (xs suffix : List (Fin 3))
    (hs : s.machine.control = GalilScaffoldChainConsume.ready center xs b)
    (hb : balance s = 4*((xs.length+1 : ℕ) : ℤ)) (hz : zero t.lag = true)
    (ht : Trace s.machine ((GalilScaffoldChainSweep.bounce center b xs ++
      GalilScaffoldChainSweep.bounce center b xs) ++ suffix) t.machine) :
    GalilScaffoldChainCatch.freshShiftGuard t.machine t.lag t.margin = true := by
  obtain ⟨hp,hd,hn⟩ := four_prefix center b xs suffix hs ht
  exact shift_ready hr hc (xs.length+1) hb hz (by simpa using hd) hp hn

#print axioms shift_from_trace
#print axioms run_trace
#print axioms append
end PalPeg.GalilScaffoldChainWatchTrace
