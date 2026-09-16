import PalPeg.GalilScaffoldTopShiftCycle

/-!
# The scan → fallback → scan cycle on the merged frame

`beginFallback`: `fpp.reset(); walker.copyFrom(right); remaining := length+1;
source.write(LEFT); source.move(1); search/chain idle; mode := Copy` — on the
unified VM this is `FppControl.beginFallback` applied to the FPP state with
the right place `p` and the current `length`. The entry tick from scan mode
followed by `fallback_to_scan` gives the whole cycle back to scan mode with
L = R = C on the selected centre and `replay = chosenRadius`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

/-- `beginFallback` on the VM, with `p` the decoded right place. -/
def beginFallbackVM (p : GalilScaffoldPlace.Place) (s t : GalilVM) : Prop :=
  t = {s with fpp := FppControl.beginFallback s.fpp.program p s.length, chain := .idle, search := {s.search with mode := .idle}}

theorem scan_fallback_cycle (onLetter leftFirst guard : GalilVM → Prop) (bs bf rs : GalilVM → GalilVM → Prop) (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (hq : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8) (delay : ℕ)
    (c : Control) (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (s s1 s2 : GalilVM) (hi : ShiftIdle s)
    (hav : (galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first).available s)
    (hcmp : (galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first).compare s s1)
    (hmt : ¬ (galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first).matched s1)
    (hg : ¬ guard s1) (hb : bf s1 s2) (p : GalilScaffoldPlace.Place) (hs2 : beginFallbackVM p s1 s2)
    (hrem : s1.remaining = s.remaining)
    (hcan : GalilScaffoldCounter.Canonical s1.length) (ℓ : ℕ) (hv : GalilScaffoldCounter.value s1.length = ℓ)
    (hne : (GalilScaffoldPlace.stream p) ≠ [])
    (heven : ((GalilScaffoldPlace.stream p).take (ℓ+1)).length % 2 = 0) :
    let win := (GalilScaffoldPlace.stream p).take (ℓ+1)
    let r := chosenRadius win
    ∃ (n : ℕ) (o : Bool) (t : GalilVM),
      Steps (galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first) delay (1 + (n+1)) ⟨c, s⟩
        ⟨{c with mode := .scan, clock := delay, output := o, replaying := decide (0 < r), odd := oddAt false (win.length - (2*r+1)), pair := pairAt (2*r)}, t⟩ ∧
      t.left = GalilScaffoldInputHead.left^[r] s2.right ∧ t.right = GalilScaffoldInputHead.left^[r] s2.right ∧
      t.center = GalilScaffoldInputHead.left^[r] s2.right ∧
      t.replay = GalilScaffoldCounter.ofNat r ∧ t.radius = GalilScaffoldCounter.reset ∧
      t.length = GalilScaffoldCounter.ofNat 1 ∧ t.chain = .idle ∧
      t.fpp.program = GalilScaffoldControl.reset 320 t.fpp.program ∧ ShiftIdle t ∧
      (0 < r → o = c.output) := by
  intro win r
  have ht1 : Tick (galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first) delay ⟨c, s⟩
      ⟨{c with clock := delay, mode := .copy}, s2⟩ :=
    .scan_fallback c s s1 s2 hm (Or.inr hav) hc hcmp hmt (Or.inr hg) hr hb
  have hm2 : ({c with clock := delay, mode := .copy} : Control).mode = .copy := rfl
  have hi2 : ShiftIdle s2 := by
    rw [shiftIdle_iff] at hi ⊢
    rw [hs2]
    show GalilScaffoldCounter.positive s1.remaining = false
    rw [hrem]; exact hi
  have hs2' : s2.fpp = FppControl.beginFallback s1.fpp.program p s1.length := by
    rw [hs2]
  obtain ⟨n, o, t, hst, hl, hR, hC, hrep, hrad, hlen, hw, hprog, hi', ho⟩ :=
    fallback_to_scan onLetter leftFirst guard bs bf rs centre place entry q hq first h7 h8 delay _ hm2 s2 hi2
      s1.fpp.program p s1.length hcan ℓ hv hs2' hne heven
  refine ⟨n, o, t, ?_, hl, hR, hC, hrep, hrad, hlen, hw, hprog, hi', ?_⟩
  · exact steps_trans (.succ ht1 (.zero _)) hst
  · intro hr0
    exact ho hr0

#print axioms scan_fallback_cycle

end PalPeg.GalilScaffoldChainInputSupply
