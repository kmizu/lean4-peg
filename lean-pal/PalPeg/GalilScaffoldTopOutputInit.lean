import PalPeg.GalilScaffoldTopFallbackRestartAll

/-!
# The initial tick and the restart tick are sound

The `init` tick outputs `true` with the right head on the first place: the
one-letter prefix is a palindrome. The `restart` tick keeps the controller
and the heads, so soundness is carried across it.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- Soundness transfers to a state with the same right head and output. -/
theorem outputRel_transfer (raw : List (Fin 2)) {c c' : Control} {s t : GalilVM}
    (hr : t.right = s.right) (ho : c'.output = c.output) (h : OutputRel raw c s) : OutputRel raw c' t := by
  intro hout k hk hk2 hrk
  rw [ho] at hout; rw [hr] at hrk
  exact h hout k hk hk2 hrk

theorem soundScanNR_vm (raw : List (Fin 2)) (c : Control) {s t : GalilVM} (hr : t.right = s.right)
    (h : SoundScanNR raw ⟨c, s⟩) : SoundScanNR raw ⟨c, t⟩ :=
  fun hm hrep => outputRel_transfer raw hr rfl (h hm hrep)

/-- With the right head on the first place, any output is sound: the
one-letter prefix is a palindrome. -/
theorem outputRel_position_one (a : Fin 2) (rest : List (Fin 2)) (c : Control) (t : GalilVM)
    (h1 : position t.right = 1) : OutputRel (a :: rest) c t := by
  intro _ k hk _ hrk
  have hk1 : k = 1 := by omega
  subst hk1
  simp

/-- The `init` tick as a sound run of one tick into a restarted state. -/
theorem init_stepsAll (onLetter leftFirst guard : GalilVM → Prop) (bs bf rs : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control) (hm : c.mode = .init) (s0 : GalilVM)
    (a : Fin 2) (rest : List (Fin 2)) (h0 : s0.right = initialHead (a :: rest))
    (hrad : s0.radius = reset) (hlen : s0.length = reset) :
    ∃ t : GalilVM,
      StepsAll (galilFrameS (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first) delay
        (SoundScanNR (a :: rest)) 1 ⟨c, s0⟩ ⟨{c with mode := .scan, output := true}, t⟩ ∧
      Restarted (a :: rest) t 0 reset ∧ position t.center = 1 ∧
      t.left = t.center ∧ t.right = t.center ∧ t.remaining = s0.remaining ∧ t.replay = s0.replay := by
  obtain ⟨t, ht, hR, hpos, hL, hRt, hrem, hrep⟩ :=
    init_restarted onLetter leftFirst guard bs bf rs centre place entry q first delay c hm s0 a rest h0 hrad hlen
  refine ⟨t, .succ (fun hsc => by rw [hm] at hsc; cases hsc) ht (.zero _ (fun _ _ => ?_)), hR, hpos, hL, hRt, hrem, hrep⟩
  exact outputRel_position_one a rest _ t (by rw [hRt, hpos])

/-- A sound run extended by a tick that keeps the controller and the right
head (the `restart` tick). -/
theorem stepsAll_keep_tick (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {k : ℕ}
    {x : State GalilVM} {c : Control} {s t : GalilVM}
    (h : StepsAll (galilFrameS P q first) delay (SoundScanNR raw) k x ⟨c, s⟩)
    (ht : Tick (galilFrameS P q first) delay ⟨c, s⟩ ⟨c, t⟩) (hr : t.right = s.right) :
    StepsAll (galilFrameS P q first) delay (SoundScanNR raw) (k+1) x ⟨c, t⟩ :=
  stepsAll_trans h (.succ (stepsAll_last h) ht (.zero _ (soundScanNR_vm raw c hr (stepsAll_last h))))

#print axioms init_stepsAll
#print axioms stepsAll_keep_tick

end PalPeg.GalilScaffoldChainInputSupply
