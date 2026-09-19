import PalPeg.CloseoutRoundUnique

/-!
# A watching chain with `periodOnly` is never replaying

`CloseoutBirthFree.H_birthR` and `CloseoutRoundUnique.H_readsBirth` are both
premised on

```
c.replaying = true → t.periodOnly = true → ∀ wch, t.chain = .watch wch → …
```

and that combination is unreachable:

* `replaying` is only ever *raised* at the fallback exit and at `replayStart`,
  and both of those set `chain := .idle` (`beginFallbackVM`,
  `replayStartVM`);
* from an idle chain the only way back to a watch is a birth (`chainStart`,
  giving `.copy`), and `afterBirth` sets `periodOnly := false`;
* the only writer of `periodOnly := true` is `beginShiftVM`
  (`CloseoutPeriodOnlyRegression.shift_sets_periodOnly`), and the `scan_shift`
  tick that fires it carries `c.replaying = false`.

So "`periodOnly = true` and the chain is a watch ⇒ not replaying" is a tick
invariant.  `NoReplayWatch` states it and `noReplayWatch_tick` proves it over
all 23 shapes.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutNoReplayWatch

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton
open PalPeg.CloseoutPackRun31 PalPeg.CloseoutPeriodShape PalPeg.CloseoutBirthFree

/-- **(NAMED) the invariant.** -/
def NoReplayWatch (c : Control) (s : GalilVM) : Prop :=
  s.periodOnly = true → ∀ w : GalilScaffoldChainWatch.State,
    s.chain = ChainVM.watch w → c.replaying = false

theorem noReplayWatch_of_idle {c : Control} {s : GalilVM} (h : s.chain = ChainVM.idle) :
    NoReplayWatch c s := fun _ w hw => by rw [h] at hw; cases hw

/-- The phase ticks keep `chain`, `periodOnly` and `replaying`. -/
theorem phase_replay {c : Control} {s t : GalilVM}
    {wch : GalilScaffoldChainWatch.State}
    (hn : NoReplayWatch c s) (hpo : t.periodOnly = true) (hw : t.chain = ChainVM.watch wch)
    (hc : t.chain = s.chain) (hp : t.periodOnly = s.periodOnly) : c.replaying = false :=
  hn (by rw [← hp]; exact hpo) wch (by rw [← hc]; exact hw)

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`NoReplayWatch` along one `galilFrameS` tick.** -/
theorem noReplayWatch_tick {w : List (Fin 2)} {delay : ℕ} {c c' : Control} {s t : GalilVM}
    (hn : NoReplayWatch c s) (hps : PeriodShape s)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay ⟨c, s⟩ ⟨c', t⟩) :
    NoReplayWatch c' t := by
  intro hpo wch hw
  cases h
  case init =>
    rename_i hm hi
    have hch : t.chain = ChainVM.idle := hi.2.2.2.2.2.2.2.2.2.1
    rw [hch] at hw; cases hw
  case restart =>
    rename_i hb
    obtain ⟨w0, -, -, -, -, ht⟩ : restartVM entry s t := hb
    rw [ht] at hw; cases hw
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hchain, -⟩ : replayStartVM entry s t := hi
    rw [hchain] at hw; cases hw
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, -, hch, -, hp, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    have hb0 : chainBorn (decide ((searchLens.get t).search.mode
        = GalilScaffoldSearchFinish.Mode.found)) s.chain = false := by
      cases hbq : chainBorn (decide ((searchLens.get t).search.mode
          = GalilScaffoldSearchFinish.Mode.found)) s.chain with
      | true => rw [hbq, if_pos rfl] at hp; rw [hp] at hpo; cases hpo
      | false => rfl
    rw [hb0, if_neg (by decide)] at hp
    have hsp : s.periodOnly = true := by rw [← hp]; exact hpo
    rcases chainAt_false_watch hch hw with ⟨w0, hw0, hint⟩ | hnot
    · exact hn hsp w0 hw0
    · exact absurd (hps hsp) (chainAt_false_back hch hw hnot)
  case scan_count =>
    rename_i hm hcl hav hb
    obtain ⟨-, -, hch, -, hp, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    have hb0 : chainBorn (decide ((searchLens.get t).search.mode
        = GalilScaffoldSearchFinish.Mode.found)) s.chain = false := by
      cases hbq : chainBorn (decide ((searchLens.get t).search.mode
          = GalilScaffoldSearchFinish.Mode.found)) s.chain with
      | true => rw [hbq, if_pos rfl] at hp; rw [hp] at hpo; cases hpo
      | false => rfl
    rw [hb0, if_neg (by decide)] at hp
    have hsp : s.periodOnly = true := by rw [← hp]; exact hpo
    rcases chainAt_false_watch hch hw with ⟨w0, hw0, hint⟩ | hnot
    · exact hn hsp w0 hw0
    · exact absurd (hps hsp) (chainAt_false_back hch hw hnot)
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
        · cases hbq : chainBorn (decide (vq.search.mode
              = GalilScaffoldSearchFinish.Mode.found)) s.chain with
          | true => rw [hbq, if_pos rfl] at hp; cases hp
          | false => rw [hbq, if_neg (by decide)] at hp; exact ⟨rfl, hp⟩
    obtain ⟨hb0, hsp⟩ := key (by rw [← htp]; exact hpo)
    have hvw : vs.chain = ChainVM.watch wch := by rw [← hsc, ← htc]; exact hw
    have hcr : c.replaying = false := by
      cases a with
      | false =>
        rcases chainAt_false_watch hch hvw with ⟨w0, hw0, hint⟩ | hnot
        · exact hn hsp w0 hw0
        · exact absurd (hps hsp) (chainAt_false_back hch hvw hnot)
      | true =>
        rcases chainAt_true_watch hch hvw with ⟨w0, w1, hw0, hint, hout⟩ | hnot
        · exact hn hsp w0 hw0
        · exact absurd (hps hsp) (chainAt_true_back hch hvw hnot)
    show (c.replaying && _) = false
    rw [hcr]; rfl
  case scan_shift =>
    -- the `scan_shift` tick carries `c.replaying = false` outright
    show c.replaying = false
    assumption
  case scan_fallback =>
    rename_i s' hm hav hcl hcmp hmt hg hr hb
    obtain ⟨pl, ht, -⟩ : beginFallbackVM' s' t := hb
    rw [ht] at hw; cases hw
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨-, -, -, wch0, hw0, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    have htp : t.periodOnly = s.periodOnly := by rw [ht]; rfl
    exact hn (by rw [← htp]; exact hpo) wch0 hw0
  case shift_done =>
    rename_i o hm hp ho
    exact hn hpo wch hw
  case copy_one =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset]; rfl) (by rw [hset]; rfl)
  case copy_done =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset]; rfl) (by rw [hset]; rfl)
  case home_start =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset]; rfl) (by rw [hset]; rfl)
  case home_step =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset]; rfl) (by rw [hset]; rfl)
  case fpp_slice =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset]; rfl) (by rw [hset]; rfl)
  case fpp_done =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset]; rfl) (by rw [hset]; rfl)
  case markEnd_step =>
    rename_i hm he hi
    obtain ⟨-, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset]; rfl) (by rw [hset]; rfl)
  case markEnd_found =>
    rename_i hm he hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
  case choose_step =>
    rename_i hm hst hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
  case choose_select =>
    rename_i hm hodd hst hi
    obtain ⟨heq, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
  case rewind_done =>
    rename_i hm hfi hi
    obtain ⟨heq, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
  case rewind_one =>
    rename_i hm hfi hpr hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
  case rewind_pair =>
    rename_i hm hfi hpr hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)

/-- **The *source* is not replaying either.**  Same case analysis as
`noReplayWatch_tick`, concluding about `c` rather than `c'`; this is the form
`H_birthR` and `H_readsBirth` need. -/
theorem replay_false_of_tick {w : List (Fin 2)} {delay : ℕ} {c c' : Control} {s t : GalilVM}
    {wch : GalilScaffoldChainWatch.State}
    (hn : NoReplayWatch c s) (hps : PeriodShape s)
    (hpo : t.periodOnly = true) (hw : t.chain = ChainVM.watch wch)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay ⟨c, s⟩ ⟨c', t⟩) :
    c.replaying = false := by
  cases h
  case init =>
    rename_i hm hi
    have hch : t.chain = ChainVM.idle := hi.2.2.2.2.2.2.2.2.2.1
    rw [hch] at hw; cases hw
  case restart =>
    rename_i hb
    obtain ⟨w0, -, -, -, -, ht⟩ : restartVM entry s t := hb
    rw [ht] at hw; cases hw
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hchain, -⟩ : replayStartVM entry s t := hi
    rw [hchain] at hw; cases hw
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, -, hch, -, hp, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    have hb0 : chainBorn (decide ((searchLens.get t).search.mode
        = GalilScaffoldSearchFinish.Mode.found)) s.chain = false := by
      cases hbq : chainBorn (decide ((searchLens.get t).search.mode
          = GalilScaffoldSearchFinish.Mode.found)) s.chain with
      | true => rw [hbq, if_pos rfl] at hp; rw [hp] at hpo; cases hpo
      | false => rfl
    rw [hb0, if_neg (by decide)] at hp
    have hsp : s.periodOnly = true := by rw [← hp]; exact hpo
    rcases chainAt_false_watch hch hw with ⟨w0, hw0, hint⟩ | hnot
    · exact hn hsp w0 hw0
    · exact absurd (hps hsp) (chainAt_false_back hch hw hnot)
  case scan_count =>
    rename_i hm hcl hav hb
    obtain ⟨-, -, hch, -, hp, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    have hb0 : chainBorn (decide ((searchLens.get t).search.mode
        = GalilScaffoldSearchFinish.Mode.found)) s.chain = false := by
      cases hbq : chainBorn (decide ((searchLens.get t).search.mode
          = GalilScaffoldSearchFinish.Mode.found)) s.chain with
      | true => rw [hbq, if_pos rfl] at hp; rw [hp] at hpo; cases hpo
      | false => rfl
    rw [hb0, if_neg (by decide)] at hp
    have hsp : s.periodOnly = true := by rw [← hp]; exact hpo
    rcases chainAt_false_watch hch hw with ⟨w0, hw0, hint⟩ | hnot
    · exact hn hsp w0 hw0
    · exact absurd (hps hsp) (chainAt_false_back hch hw hnot)
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
        · cases hbq : chainBorn (decide (vq.search.mode
              = GalilScaffoldSearchFinish.Mode.found)) s.chain with
          | true => rw [hbq, if_pos rfl] at hp; cases hp
          | false => rw [hbq, if_neg (by decide)] at hp; exact ⟨rfl, hp⟩
    obtain ⟨hb0, hsp⟩ := key (by rw [← htp]; exact hpo)
    have hvw : vs.chain = ChainVM.watch wch := by rw [← hsc, ← htc]; exact hw
    have hcr : c.replaying = false := by
      cases a with
      | false =>
        rcases chainAt_false_watch hch hvw with ⟨w0, hw0, hint⟩ | hnot
        · exact hn hsp w0 hw0
        · exact absurd (hps hsp) (chainAt_false_back hch hvw hnot)
      | true =>
        rcases chainAt_true_watch hch hvw with ⟨w0, w1, hw0, hint, hout⟩ | hnot
        · exact hn hsp w0 hw0
        · exact absurd (hps hsp) (chainAt_true_back hch hvw hnot)
    exact hcr
  case scan_shift =>
    -- the `scan_shift` tick carries `c.replaying = false` outright
    show c.replaying = false
    assumption
  case scan_fallback =>
    rename_i s' hm hav hcl hcmp hmt hg hr hb
    obtain ⟨pl, ht, -⟩ : beginFallbackVM' s' t := hb
    rw [ht] at hw; cases hw
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨-, -, -, wch0, hw0, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    have htp : t.periodOnly = s.periodOnly := by rw [ht]; rfl
    exact hn (by rw [← htp]; exact hpo) wch0 hw0
  case shift_done =>
    rename_i o hm hp ho
    exact hn hpo wch hw
  case copy_one =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset]; rfl) (by rw [hset]; rfl)
  case copy_done =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset]; rfl) (by rw [hset]; rfl)
  case home_start =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset]; rfl) (by rw [hset]; rfl)
  case home_step =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset]; rfl) (by rw [hset]; rfl)
  case fpp_slice =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset]; rfl) (by rw [hset]; rfl)
  case fpp_done =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset]; rfl) (by rw [hset]; rfl)
  case markEnd_step =>
    rename_i hm he hi
    obtain ⟨-, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset]; rfl) (by rw [hset]; rfl)
  case markEnd_found =>
    rename_i hm he hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
  case choose_step =>
    rename_i hm hst hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
  case choose_select =>
    rename_i hm hodd hst hi
    obtain ⟨heq, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
  case rewind_done =>
    rename_i hm hfi hi
    obtain ⟨heq, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
  case rewind_one =>
    rename_i hm hfi hpr hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
  case rewind_pair =>
    rename_i hm hfi hpr hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact phase_replay hn hpo hw (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)

/-- **`H_birthR` is vacuous.**  A replaying source cannot have a watching chain
with `periodOnly` at the target. -/
theorem h_birthR_vacuous {w : List (Fin 2)} {delay : ℕ} {c c' : Control} {s t : GalilVM}
    (hn : NoReplayWatch c s) (hps : PeriodShape s)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay ⟨c, s⟩ ⟨c', t⟩) :
    PalPeg.CloseoutBirthFree.H_birthR w c s t := by
  intro hrep hpo wch hchain
  exact absurd (replay_false_of_tick centre place entry q first hn hps hpo hchain h)
    (by rw [hrep]; decide)

/-- **`H_readsBirth` is vacuous**, for the same reason. -/
theorem h_readsBirth_vacuous {w : List (Fin 2)} {delay : ℕ} {c c' : Control} {s t : GalilVM}
    (hn : NoReplayWatch c s) (hps : PeriodShape s)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay ⟨c, s⟩ ⟨c', t⟩) :
    PalPeg.CloseoutRoundUnique.H_readsBirth w c t := by
  intro hrep hpo wch hchain C R used hI
  exact absurd (replay_false_of_tick centre place entry q first hn hps hpo hchain h)
    (by rw [hrep]; decide)

/-! ## The two tick theorems with the birth halves gone -/

/-- **`ChainRound` along a tick: only `H_shiftDone` left.** -/
theorem chainRound_tick_S {w : List (Fin 2)} {delay : ℕ} {c c' : Control} {s t : GalilVM}
    (hCR : ChainRound w c s)
    (hRR : PalPeg.CloseoutRoundReads.ReadsRound w c s)
    (hps : PeriodShape s)
    (hn : NoReplayWatch c s)
    (hinv : PalPeg.CloseoutPackRun41.ChainPositionInvariantWithShiftPhase w c s)
    (hS : H_shiftDone centre place entry q first w c s)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay ⟨c, s⟩ ⟨c', t⟩) :
    ChainRound w c' t :=
  PalPeg.CloseoutBirthFree.chainRound_tick_BF centre place entry q first hCR hRR hps hinv hS
    (h_birthR_vacuous centre place entry q first hn hps h) h

/-- **`ReadsRound` along a tick: only `H_readsShift` left.** -/
theorem readsRound_tick_S {w : List (Fin 2)} {delay : ℕ} {c c' : Control} {s t : GalilVM}
    (hCR : ChainRound w c s)
    (hRR : PalPeg.CloseoutRoundReads.ReadsRound w c s)
    (hps : PeriodShape s)
    (hn : NoReplayWatch c s)
    (hinv : PalPeg.CloseoutPackRun41.ChainPositionInvariantWithShiftPhase w c s)
    (hSh : PalPeg.CloseoutRoundUnique.H_readsShift w c s)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay ⟨c, s⟩ ⟨c', t⟩) :
    PalPeg.CloseoutRoundReads.ReadsRound w c' t :=
  PalPeg.CloseoutRoundUnique.readsRound_tick centre place entry q first hCR hRR hps hSh
    (h_readsBirth_vacuous centre place entry q first hn hps h)
    (PalPeg.CloseoutRoundReads.blockInv_of_chainPosInv2 hinv) h

end

#print axioms noReplayWatch_of_idle
#print axioms phase_replay
#print axioms noReplayWatch_tick
#print axioms replay_false_of_tick
#print axioms h_birthR_vacuous
#print axioms h_readsBirth_vacuous
#print axioms chainRound_tick_S
#print axioms readsRound_tick_S

end PalPeg.CloseoutNoReplayWatch
