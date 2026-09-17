import PalPeg.CloseoutPackRun31

/-!
# `PeriodShape`: while `periodOnly`, the chain is never copying or backing

`CloseoutPackRun31.chainRound_tick`'s last named branch pair is `H_shiftDone`
and `H_birth`, and `H_birth` has two halves:

```
H_birth w c s t := (c.replaying = true ∨ ∀ w0, s.chain ≠ .watch w0) →
  t.periodOnly = true → ∀ wch, t.chain = .watch wch → ∃ C R used, RoundScan …
```

The second half — the source chain is not a watch, yet the target's is — can
only arise from `ChainStep.backDone` (`chainAt_false_watch` /
`chainAt_true_watch`), i.e. from a `.back` chain.  But a `.back` chain is
unreachable while `periodOnly = true`:

* `beginShiftVM` is the **only** writer of `periodOnly := true`
  (`CloseoutPeriodOnlyRegression.shift_sets_periodOnly`) and it requires
  `shiftGuardVM`, hence a `.watch` chain;
* the only route to `.copy` is a birth (`chainStart`), and `afterBirth` sets
  `periodOnly := false` (`GalilScaffoldTopSearch:78`);
* the only route to `.back` is `copyEnd` from a `.copy`.

So "`periodOnly = true` → the chain is `idle`, `watch` or `broken`" is a tick
invariant.  `WatchLike` states it, `periodShape_tick` proves it, and
`h_birth_not_watch_vacuous` is the half of `H_birth` it kills.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPeriodShape

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton
open PalPeg.CloseoutPackRun31

/-- **The chain shapes compatible with `periodOnly`.**  `copy` and `back` are
the two phases a chain only reaches after a birth, which clears the flag. -/
def WatchLike : ChainVM → Prop
  | .idle => True
  | .copy _ _ _ _ _ _ _ => False
  | .back _ _ _ _ _ => False
  | .watch _ => True
  | .broken _ => True

theorem watchLike_idle : WatchLike ChainVM.idle := trivial

theorem watchLike_watch (w : GalilScaffoldChainWatch.State) :
    WatchLike (ChainVM.watch w) := trivial

/-- A `WatchLike` chain is not `back`, which is what the birth branch needs. -/
theorem not_back_of_watchLike {z : ChainVM} (h : WatchLike z)
    {v : GalilScaffoldChainPeriod.Tape} {hh lag margin : Counter} {ver : PlaceHead}
    (hz : z = .back v hh lag margin ver) : False := by
  rw [hz] at h; exact h

theorem watchLike_chainStep {x y : ChainVM} (h : ChainStep x y) (hx : WatchLike x) :
    WatchLike y := by
  cases h <;> first | exact hx | exact hx.elim | trivial

theorem watchLike_chainMatched {x y : ChainVM} (h : ChainMatched x y) (hx : WatchLike x) :
    WatchLike y := by
  cases h <;> first | exact hx | exact hx.elim | trivial

theorem watchLike_chainTick {a : Bool} {x z : ChainVM} (h : ChainTick a x z)
    (hx : WatchLike x) : WatchLike z := by
  obtain ⟨y, hstep, hrest⟩ := h
  have hy : WatchLike y := watchLike_chainStep hstep hx
  cases a with
  | false => rw [if_neg (by simp)] at hrest; exact hrest ▸ hy
  | true =>
    rw [if_pos rfl] at hrest
    exact watchLike_chainMatched hrest hy

/-- **`WatchLike` along `chainAt`, when no chain is born.** -/
theorem watchLike_chainAt {a found : Bool} {ans : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter} {x z : ChainVM}
    (h : chainAt a found ans cc walker ver radius x z) (hx : WatchLike x)
    (hnb : chainBorn found x = false) : WatchLike z := by
  rcases h with ⟨-, ht⟩ | ⟨-, -, rfl⟩ | ⟨hi, hf, -⟩
  · exact watchLike_chainTick ht hx
  · trivial
  · unfold chainBorn at hnb
    rw [hi, hf] at hnb
    simp [ChainVM.isIdle] at hnb

/-- **(NAMED) the invariant.** -/
def PeriodShape (s : GalilVM) : Prop := s.periodOnly = true → WatchLike s.chain

theorem periodShape_of_idle {s : GalilVM} (h : s.chain = ChainVM.idle) : PeriodShape s :=
  fun _ => by rw [h]; trivial

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- The phase ticks (`copy`, `home`, `fpp`, `markEnd`, `choose`, `rewind`) act
through a lens that excludes `chain` and `periodOnly`, so `PeriodShape` passes
through them by `rfl`. -/
theorem phase_case {s t : GalilVM} (hs : PeriodShape s) (hpo : t.periodOnly = true)
    (hc : t.chain = s.chain) (hp : t.periodOnly = s.periodOnly) : WatchLike t.chain := by
  rw [hc]; exact hs (by rw [← hp]; exact hpo)

/-- **`PeriodShape` along one `galilFrameS` tick.** -/
theorem periodShape_tick {w : List (Fin 2)} {delay : ℕ} {c c' : Control} {s t : GalilVM}
    (hs : PeriodShape s)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay ⟨c, s⟩ ⟨c', t⟩) :
    PeriodShape t := by
  intro hpo
  cases h
  case init =>
    rename_i hm hi
    have hch : t.chain = ChainVM.idle := hi.2.2.2.2.2.2.2.2.2.1
    rw [hch]; trivial
  case restart =>
    rename_i hb
    obtain ⟨w0, -, -, -, -, ht⟩ : restartVM entry s t := hb
    rw [ht]; trivial
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hchain, -⟩ : replayStartVM entry s t := hi
    rw [hchain]; trivial
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, -, hch, -, hp, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    by_cases hborn : chainBorn (decide ((searchLens.get t).search.mode
        = GalilScaffoldSearchFinish.Mode.found)) s.chain = true
    · rw [hborn, if_pos rfl] at hp; rw [hp] at hpo; cases hpo
    · have hb0 : chainBorn (decide ((searchLens.get t).search.mode
          = GalilScaffoldSearchFinish.Mode.found)) s.chain = false := by
        cases hx : chainBorn (decide ((searchLens.get t).search.mode
          = GalilScaffoldSearchFinish.Mode.found)) s.chain with
        | false => rfl
        | true => exact absurd hx hborn
      rw [hb0, if_neg (by decide)] at hp
      exact watchLike_chainAt hch (hs (hp ▸ hpo)) hb0
  case scan_count =>
    rename_i hm hcl hav hb
    obtain ⟨-, -, hch, -, hp, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    by_cases hborn : chainBorn (decide ((searchLens.get t).search.mode
        = GalilScaffoldSearchFinish.Mode.found)) s.chain = true
    · rw [hborn, if_pos rfl] at hp; rw [hp] at hpo; cases hpo
    · have hb0 : chainBorn (decide ((searchLens.get t).search.mode
          = GalilScaffoldSearchFinish.Mode.found)) s.chain = false := by
        cases hx : chainBorn (decide ((searchLens.get t).search.mode
          = GalilScaffoldSearchFinish.Mode.found)) s.chain with
        | false => rfl
        | true => exact absurd hx hborn
      rw [hb0, if_neg (by decide)] at hp
      exact watchLike_chainAt hch (hs (hp ▸ hpo)) hb0
  case scan_match =>
    rename_i s' o hm hav hc hcmp hmt hpl ho
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have htc : t.chain = s'.chain := by rw [hpl']; cases c.replaying <;> rfl
    have htp : t.periodOnly = s'.periodOnly := by rw [hpl']; cases c.replaying <;> rfl
    have hcf : compareFound (PofC centre place entry w) q first s s' := hcmp
    obtain ⟨vs, vq, a, hvl, hvr, hiff, -, hch, hteq⟩ := hcf
    have hsc : s'.chain = vs.chain := by
      rw [hteq]; cases a <;> (rw [afterBirth_chain]; rfl)
    have key : s'.periodOnly = true →
        chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain = false
          ∧ s.periodOnly = true := by
      intro hp
      rw [hteq] at hp
      cases a <;> rw [afterBirth_periodOnly] at hp <;>
        · cases hb : chainBorn (decide (vq.search.mode
              = GalilScaffoldSearchFinish.Mode.found)) s.chain with
          | true => rw [hb, if_pos rfl] at hp; cases hp
          | false => rw [hb, if_neg (by decide)] at hp; exact ⟨rfl, hp⟩
    obtain ⟨hb0, hsp⟩ := key (by rw [← htp]; exact hpo)
    rw [htc, hsc]
    exact watchLike_chainAt hch (hs hsp) hb0
  case scan_shift =>
    rename_i s' hm hav hc hcmp hmt hr hg hb
    obtain ⟨wch, -, ht⟩ : beginShiftVM' s' t := hb
    rw [ht]; trivial
  case scan_fallback =>
    rename_i s' hm hav hc hcmp hmt hg hr hb
    obtain ⟨pl, ht⟩ : beginFallbackVM' s' t := hb
    rw [ht]; trivial
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨-, -, -, wch, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    have htc : t.chain = ChainVM.watch (chainShiftOne wch) := by rw [ht]; rfl
    rw [htc]; trivial
  case shift_done =>
    rename_i o hm hp ho
    exact hs hpo
  case copy_one =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    exact phase_case hs hpo (by rw [hset]; rfl) (by rw [hset]; rfl)
  case copy_done =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    exact phase_case hs hpo (by rw [hset]; rfl) (by rw [hset]; rfl)
  case home_start =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    exact phase_case hs hpo (by rw [hset]; rfl) (by rw [hset]; rfl)
  case home_step =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    exact phase_case hs hpo (by rw [hset]; rfl) (by rw [hset]; rfl)
  case fpp_slice =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    exact phase_case hs hpo (by rw [hset]; rfl) (by rw [hset]; rfl)
  case fpp_done =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    exact phase_case hs hpo (by rw [hset]; rfl) (by rw [hset]; rfl)
  case markEnd_step =>
    rename_i hm he hi
    obtain ⟨-, hset⟩ := hi
    exact phase_case hs hpo (by rw [hset]; rfl) (by rw [hset]; rfl)
  case markEnd_found =>
    rename_i hm he hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact phase_case hs hpo (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
  case choose_step =>
    rename_i hm hst hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact phase_case hs hpo (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
  case choose_select =>
    rename_i hm hodd hst hi
    obtain ⟨heq, hset⟩ := hi
    exact phase_case hs hpo (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
  case rewind_done =>
    rename_i hm hfi hi
    obtain ⟨heq, hset⟩ := hi
    exact phase_case hs hpo (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
  case rewind_one =>
    rename_i hm hfi hpr hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact phase_case hs hpo (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
  case rewind_pair =>
    rename_i hm hfi hpr hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact phase_case hs hpo (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)

/-- **`PeriodShape` along a run.** -/
theorem periodShape_steps {w : List (Fin 2)} {delay n : ℕ} {x y : State GalilVM}
    (hx : PeriodShape x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) delay n x y) :
    PeriodShape y.vm := by
  induction h with
  | zero x => exact hx
  | @succ n x z y ht _ ih =>
    obtain ⟨c, s⟩ := x
    obtain ⟨c', t⟩ := z
    exact ih (periodShape_tick centre place entry q first hx ht)

/-! At the boot state the chain is idle, so `periodShape_of_idle` applies
wherever `boot` is in scope. -/

end

#print axioms watchLike_chainStep
#print axioms watchLike_chainAt
#print axioms periodShape_of_idle
#print axioms periodShape_tick
#print axioms periodShape_steps

end PalPeg.CloseoutPeriodShape
