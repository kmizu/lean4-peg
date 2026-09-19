import PalPeg.GalilTickFun
import PalPeg.GalilRoundsLeftmost
import PalPeg.GalilLiveCentreCycle2
import PalPeg.GalilScaffoldTopFallbackRestartAll

/-!
# `ChainReady` from the branch invariants, and the centre's progress per cycle

Two independent pieces of the real-time ledger.

**(L5) `ChainReady` from `BlockInv`.**  `GalilTickFun.ChainReady` is the
chain-side enabling condition of the scaffold tick.  `chainReady_of_blockInv`
isolates exactly which facts beyond `GalilBranchInvariants.BlockInv` each
constructor still needs:

* `.idle` — nothing;
* `.copy` — the copy invariant `∃ n, CopyInv t h p v n` (`BlockInv` only
  carries its `OnPrefix` component);
* `.back` — only `canRight ver`: the `WatchReady` demanded at `isFirst` is
  `canRight ver ∧ OnBlock (watchControl v).period`, and the block half is
  `onBlock_moveRight` applied to `BlockInv`'s `OnBlock v` (legal because
  `isFirst_isLast`);
* `.watch` — `positive lag = true → Good w` and `∀ m, Internal w m →
  canRight m.machine.verifier` (`BlockInv` supplies `WatchBlock w`);
* `.broken` — unreachable, so it is ruled out by hypothesis.

**(L10) Centre progress per main-loop cycle.**  `found_cycle_center_progress`:
in the conclusion state of `cycle_found_minv` / `life_restarted` the centre has
moved right by at least one half period `h`, and `h` is positive.  The centre
advances by exactly `(m+1)*h` where `m` is the number of re-shift rounds:
`h` from the first shift (the origin's `Entry` puts the new centre at
`org.center + h`), then `m*h` from `rounds_origin`, and neither the final scan
segment nor `afterCompare` touches the centre.

`fallback_cycle_center_progress`: after `cycle_fallback_stepsAll` the restarted
centre is `position sF.right + 1 - r` with `r = chosenRadius …`, and it is
strictly to the right of the old centre, because the old centre is dead at the
next place while the new one is live there and the old one was leftmost.
-/

set_option autoImplicit false
namespace PalPeg.GalilChainReadyProgress

open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilBranchInvariants PalPeg.GalilTickFun
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## (L5) `ChainReady` from the branch invariants -/

/-- The `back` case of `ChainReady`, isolated: `OnBlock` plus the verifier's
right guard give `WatchReady` at the state `backDone` enters. -/
theorem watchReady_backDone {v : GalilScaffoldChainPeriod.Tape} (hb : OnBlock v)
    (hf : GalilScaffoldChainPeriod.isFirst v.focus = true)
    (ver : PlaceHead) (hc : canRight ver) (lag margin : Counter) :
    WatchReady ⟨⟨ver, watchControl v⟩, lag, margin⟩ :=
  ⟨hc, onBlock_moveRight hb (isFirst_isLast hf)⟩

/-- **`ChainReady` from `BlockInv`.**  Exactly the extra facts listed in the
module docstring, one per constructor. -/
theorem chainReady_of_blockInv (c : ChainVM) (hb : BlockInv c)
    (hcopy : ∀ (t : GalilScaffoldTape.Tape) (hh : Counter) (p : GalilScaffoldPlace.Place)
      (v : GalilScaffoldChainPeriod.Tape) (lag margin : Counter) (ver : PlaceHead),
      c = .copy t hh p v lag margin ver → ∃ n : ℕ, CopyInv t hh p v n)
    (hback : ∀ (v : GalilScaffoldChainPeriod.Tape) (hh lag margin : Counter) (ver : PlaceHead),
      c = .back v hh lag margin ver → canRight ver)
    (hgood : ∀ w : GalilScaffoldChainWatch.State, c = .watch w →
      positive w.lag = true → GalilScaffoldChainWatch.Good w)
    (hcan : ∀ w : GalilScaffoldChainWatch.State, c = .watch w →
      ∀ m, GalilScaffoldChainWatch.Internal w m → canRight m.machine.verifier) :
    ChainReady c := by
  cases c with
  | idle => exact trivial
  | copy t hh p v lag margin ver => exact hcopy t hh p v lag margin ver rfl
  | back v hh lag margin ver =>
    intro hf _
    exact watchReady_backDone hb hf ver (hback v hh lag margin ver rfl) lag margin
  | watch w => exact ⟨PalPeg.GalilBranchInvariants.readyWatch_of_good (hgood w rfl), hb, hcan w rfl⟩
  | broken w => exact trivial

#print axioms watchReady_backDone
#print axioms chainReady_of_blockInv

/-! ## (L10) Centre progress across one main-loop cycle -/

/-- The re-shift rounds advance the centre by exactly `m` half periods. -/
theorem rounds_center (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay h : ℕ)
    {m : ℕ} {c c' : Control} {s s' : GalilVM} (hr : Rounds P q first delay h m c s c' s')
    (w0 : GalilScaffoldChainWatch.State) (hp : s.periodOnly = true) (hs : s.chain = .watch w0)
    (hz : zero w0.lag = true) (org : ReadOrigin raw) (hint : org.interior.length+1 = h)
    (he : Entry raw org (toOnly s w0)) :
    position s'.center = position s.center + m*h := by
  obtain ⟨_, w', _, _, _, hcr⟩ := rounds_lift P q first delay h hr w0 hp hs hz
  obtain ⟨org', he', _, hinterior, _, _, _, hcenter', _⟩ := rounds_origin hcr org hint he
  have hint' : org'.interior.length+1 = h := by rw [hinterior]; exact hint
  have h1 : position s.center = org.center + h := by
    have h0 := he.centerPos; rw [hint] at h0; exact h0
  have h2 : position s'.center = org'.center + h := by
    have h0 := he'.centerPos; rw [hint'] at h0; exact h0
  rw [h1, h2, hcenter']; ring

/-- **The centre moves right by at least one half period across a found
cycle.**  The hypotheses are the centre-relevant fragment of
`cycle_found_minv` / `life_restarted`: the first shift (`hs2'`, `hchain`), the
read origin it establishes (`org`, `hint`, `he`, `hoc`), the re-shift rounds
and the final scan segment. -/
theorem found_cycle_center_progress (raw : List (Fin 2)) (P : Shared) (qq : ℕ) (first : Fin 9)
    (delay : ℕ) {sF : GalilVM} (h : ℕ)
    {c1 : Control} {s1 : GalilVM}
    (w : GalilScaffoldChainWatch.State) (hz : zero w.lag = true)
    (vs : ScanVM) (vq' : SearchVM)
    (s2' : GalilVM) (hs2' : beginShiftVM h w (afterMismatch s1 vs vq') s2')
    {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle)
    (org : ReadOrigin raw) (hint : org.interior.length+1 = h)
    (he : Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v))
    (hoc : org.center = position sF.center)
    {m : ℕ} {o : Bool} {c' : Control} {s' : GalilVM}
    (hrounds : Rounds P qq first delay h m {c1 with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    {n : ℕ} {c3 : Control} {s3 : GalilVM} (hseg3 : ScanSeg P qq first delay n c' s' c3 s3)
    (vs3 : ScanVM) (vq3 : SearchVM) :
    0 < h ∧
      position sF.center + h ≤ position (afterCompare s3 vs3 vq3).center ∧
      position (afterCompare s3 vs3 vq3).center = position sF.center + (m+1)*h := by
  have hh : 0 < h := by omega
  have hp2 : (shiftLens.set s2' ⟨t', .watch v, cycle⟩).periodOnly = true := by
    show s2'.periodOnly = true; rw [hs2'.2]
  have hz2 : zero v.lag = true := by rw [chain_shift_lag hchain]; exact hz
  -- the centre right after the first shift
  have hstart : position (shiftLens.set s2' ⟨t', .watch v, cycle⟩).center
      = position sF.center + h := by
    have h0 := he.centerPos; rw [hint, hoc] at h0; exact h0
  -- the rounds
  have hrnd := rounds_center raw P qq first delay h hrounds v hp2 rfl hz2 org hint he
  -- the final segment and the matched comparison keep the centre
  have hseg : s3.center = s'.center := scanSeg_center P qq first delay hseg3
  have hfin : position (afterCompare s3 vs3 vq3).center = position sF.center + (m+1)*h := by
    rw [afterCompare_center, hseg, hrnd, hstart]; ring
  refine ⟨hh, ?_, hfin⟩
  rw [hfin]
  have : 0 ≤ m*h := Nat.zero_le _
  have e : (m+1)*h = m*h + h := by ring
  omega

#print axioms rounds_center
#print axioms found_cycle_center_progress

/-! ### The fallback cycle -/

/-- The fallback's chosen radius really names a live centre at the next place. -/
theorem live_of_chosen {raw : List (Fin 2)} {n r : ℕ} (hrn : 2*r < n+1)
    (hpal : PalAt (encoded raw) (n+1-r) r) : Live raw (n+1) (n+1-r) := by
  have hr : r ≤ n+1-r := hpal.1
  refine ⟨by omega, by omega, ?_⟩
  have e : n+1-(n+1-r) = r := by omega
  rw [e]; exact hpal

/-- **The arithmetic of `leftmost_fallback`, isolated.**  If the old leftmost
live centre dies at the next place and the fallback's centre is live there,
the centre has strictly advanced. -/
theorem leftmost_fallback_progress {raw : List (Fin 2)} {n C r : ℕ}
    (hL : Leftmost raw n C) (hdead : ¬ Live raw (n+1) C)
    (hlive : Live raw (n+1) (n+1-r)) : C + 1 ≤ n+1-r := by
  by_cases hcn : n+1-r ≤ n
  · have hCc := hL.2 _ (live_pred hlive hcn)
    have hne : n+1-r ≠ C := fun e => hdead (e ▸ hlive)
    omega
  · have := hL.1.1
    omega

/-- **The centre moves right by at least one place across a fallback cycle.**
`hpos`, `hpal` are the conclusions `fallback_restarted_soundNR` /
`fallback_restarted` deliver about the restarted state `t` with
`r = chosenRadius …`; `hinv`, `hav`, `hmis` are the mismatching comparison at
`sF` and `hL` says its centre was the leftmost live one. -/
theorem fallback_cycle_center_progress {raw : List (Fin 2)} {sF t : GalilVM} {cen Rad r : ℕ}
    (hinv : ScanInvariant raw cen Rad sF.left sF.right) (hav : canRight sF.right)
    (hmis : read (left sF.left) ≠ read (right sF.right))
    (hL : Leftmost raw (position sF.right) cen)
    (hpos : position t.center = position (right sF.right) - r)
    (hpal : PalAt (encoded raw) (position (right sF.right) - r) r)
    (hrn : 2*r < position (right sF.right)) :
    position t.center = position sF.right + 1 - r ∧ cen + 1 ≤ position t.center := by
  have hrpos : position (right sF.right) = position sF.right + 1 :=
    right_position sF.right hav
      (represented_position sF.right.head raw hinv.rightRep hinv.rightPresent).1
  rw [hrpos] at hpos hpal hrn
  refine ⟨hpos, ?_⟩
  rw [hpos]
  exact leftmost_fallback_progress hL (not_live_of_mismatch hinv hav hmis)
    (live_of_chosen hrn hpal)

#print axioms live_of_chosen
#print axioms leftmost_fallback_progress
#print axioms fallback_cycle_center_progress

end PalPeg.GalilChainReadyProgress
