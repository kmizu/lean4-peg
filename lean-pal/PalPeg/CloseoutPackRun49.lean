import PalPeg.CloseoutPackRun48
import PalPeg.CloseoutPackRun23

/-!
# `CloseoutPackRun49`: `LPackM3` — the left pack carries the centre ledger and `LagCan`

`CloseoutPackRun48` leaves `H_matchP2` / `H_shiftEntry2` standing on one
residue pack `MatchRes2`, and `CloseoutPackRun47` leaves `BgStartP2` standing
on `CentreLedger`.  Both are *state* predicates, so they belong in the
inductive left pack rather than in a per-landing leaf.  This file adds them to
`CloseoutPackRun23.LPackM2`:

* `centreLedger` — `CentreLedger s` in `scan`.  Preserved by the background
  ticks and by `restart` (heads, centre and radius all kept), and by
  `scan_match` (right head and radius both advance by one).  Blocked at the
  three landings that *enter* `scan` from elsewhere: `init`, `shift_done`
  and `replayStart` — one named leaf each.
* `lagCan` — `CloseoutPackRun48.LagCan s.chain`, unguarded.  Preserved by
  every branch: the chain is either untouched, reset to `idle`, started as a
  `copy` chain, stepped (`lagCan_step`), credited (`lagCan_matched`) or moved
  by one `immediate` consume (`lagCan_immediate`).  The single leaf it needs
  is `backLag`, the `back`-phase lag shape that `lagCan_step` consumes.

## Honest status

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun49

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilFinalAssembly
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack3
open PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.CloseoutPackRun23
open PalPeg.CloseoutPackRun47 (CentreLedger)
open PalPeg.CloseoutPackRun41 PalPeg.CloseoutPackRun48

/-! ## 1. Two small chain facts -/

/-- `value reset = 0`. -/
theorem value_reset : value reset = 0 := by
  simp [value, reset]

/-- One `immediate` consume keeps the lag counter, hence `LagCan`. -/
theorem lagCan_immediate {v : GalilScaffoldChainWatch.State}
    (hL : LagCan (ChainVM.watch v)) :
    LagCan (ChainVM.watch (GalilScaffoldChainWatch.immediate v)) := by
  obtain ⟨hc, hn⟩ := hL v rfl
  intro wch hw
  cases hw
  exact ⟨hc, hn⟩

/-- One shift unit keeps the lag counter, hence `LagCan`. -/
theorem lagCan_shiftOne {v : GalilScaffoldChainWatch.State}
    (hL : LagCan (ChainVM.watch v)) :
    LagCan (ChainVM.watch (chainShiftOne v)) := by
  obtain ⟨hc, hn⟩ := hL v rfl
  intro wch hw
  cases hw
  exact ⟨hc, hn⟩

/-- A freshly started chain is a `copy` chain, so `LagCan` is vacuous. -/
theorem lagCan_chainStart (ans : GalilScaffoldTape.Tape) (c : Fin 3)
    (wk : GalilScaffoldPlace.Place) (ver : PlaceHead) (rad : Counter) :
    LagCan (chainStart ans c wk ver rad) := by
  intro wch hw
  unfold chainStart at hw
  exact ChainVM.noConfusion hw

#print axioms lagCan_immediate


/-- `LagCan` through a scan background tick. -/
theorem bgLagCan (P : Shared) (q : ℕ) (first : Fin 9) {s s' : GalilVM}
    (hb : (galilFrameS P q first).background s s') (hL : LagCan s.chain)
    (hback : ∀ (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter) (ver : PlaceHead),
      s.chain = .back v h lag margin ver → Canonical lag ∧ 0 ≤ value lag) :
    LagCan s'.chain := by
  by_cases hi : s.chain = ChainVM.idle
  · rcases backgroundS_idle P q first hb hi with ⟨-, hz⟩ | ⟨-, hz⟩
    · rw [hz]; exact lagCan_idle
    · rw [hz]; exact lagCan_chainStart _ _ _ _ _
  · obtain ⟨y, hst, hy⟩ := backgroundS_chainTick P q first hb hi
    simp only [Bool.false_eq_true, ↓reduceIte] at hy
    rw [hy]
    exact lagCan_step hL hback hst

/-! ## 2. The pack -/


/-- **(KEY DEFINITION) `LPackM2` plus the centre ledger and `LagCan`.** -/
structure LPackM3 (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  packM2 : LPackM2 w c s
  centreLedger : c.mode = Mode.scan → CentreLedger s
  lagCan : LagCan s.chain

section Tick
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the four new leaves.**  One per branch that cannot carry the new
fields: the three `scan` *entries* for the ledger, and the `back` phase for
`LagCan`. -/
structure LTickLeaves3 (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  backLag : ∀ (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter) (ver : PlaceHead),
    s.chain = .back v h lag margin ver → Canonical lag ∧ 0 ≤ value lag
  initLedger : c.mode = Mode.init → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).init s t → CentreLedger t
  shiftDoneLedger : c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s → CentreLedger s
  replayLedger : c.mode = Mode.replayStart → canRight s.center ∧ Sane s.center


/-- **(KEY) `LPackM3` survives one tick.** -/
theorem lpackM3_tick {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (hP : LPackM3 w c s) (hL : LTickLeavesN centre place entry q first w c s)
    (hA : AuxPack c s) (hL2 : LTickLeaves2 centre place entry q first w c s)
    (hL3 : LTickLeaves3 centre place entry q first w c s)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩ ⟨c', t⟩) :
    LPackM3 w c' t := by
  have hM2 : LPackM2 w c' t :=
    lpackM2_tick centre place entry q first hP.packM2 hL hA hL2 h
  cases h
  case init =>
    rename_i hm hi
    have hch : t.chain = ChainVM.idle := hi.2.2.2.2.2.2.2.2.2.1
    exact ⟨hM2, fun _ => hL3.initLedger hm _ hi, by rw [hch]; exact lagCan_idle⟩
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨hl, hr, -, hC, -, hrad, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    obtain ⟨hc1, hc2, hc3⟩ := hP.centreLedger hm
    refine ⟨hM2, fun _ => ⟨by rw [hC]; exact hc1, by rw [hC]; exact hc2, ?_⟩, ?_⟩
    · rw [hC, hrad, hr]; exact hc3
    · exact bgLagCan (PofC centre place entry w) q first hb hP.lagCan hL3.backLag
  case scan_count =>
    rename_i hm hcl hav hb
    obtain ⟨hl, hr, -, hC, -, hrad, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    obtain ⟨hc1, hc2, hc3⟩ := hP.centreLedger hm
    refine ⟨hM2, fun _ => ⟨by rw [hC]; exact hc1, by rw [hC]; exact hc2, ?_⟩, ?_⟩
    · rw [hC, hrad, hr]; exact hc3
    · exact bgLagCan (PofC centre place entry w) q first hb hP.lagCan hL3.backLag
  case restart =>
    rename_i hm hb
    obtain ⟨wch, -, -, -, -, ht⟩ : restartVM entry s t := hb
    obtain ⟨hc1, hc2, hc3⟩ := hP.centreLedger hm
    refine ⟨hM2, fun _ => ⟨?_, ?_, ?_⟩, ?_⟩
    · show canRight t.center; rw [ht]; exact hc1
    · show Sane t.center; rw [ht]; exact hc2
    · show (position t.center : ℤ) + value t.radius = position t.right
      rw [ht]; exact hc3
    · rw [ht]; exact lagCan_idle
  case scan_match =>
    rename_i s' o hmt hm hcl hcmp hav hpl ho
    have hpl' : t = (if c.replaying then {s' with replay := dec s'.replay} else s') := hpl
    have hts : t.left = s'.left ∧ t.right = s'.right ∧ t.chain = s'.chain ∧
        t.center = s'.center ∧ t.radius = s'.radius := by
      rw [hpl']; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨vs, vq, a, hvl, hvr, hiff, -, hch, hteq⟩ :
      compareFound (PofC centre place entry w) q first s s' := hcmp
    have ha : a = true := by
      cases a with
      | true => rfl
      | false =>
        rw [if_neg (by simp)] at hteq
        subst hteq
        refine absurd (hiff.2 ?_) (by simp)
        have h0 : GalilScaffoldInputHead.read
              (afterBirth (chainBorn (decide (vq.search.mode
                = GalilScaffoldSearchFinish.Mode.found)) s.chain)
                (afterMismatch s vs vq)).left
            = GalilScaffoldInputHead.read
              (afterBirth (chainBorn (decide (vq.search.mode
                = GalilScaffoldSearchFinish.Mode.found)) s.chain)
                (afterMismatch s vs vq)).right := hmt
        rw [afterBirth_left, afterBirth_right] at h0
        exact h0
    subst ha
    rw [if_pos rfl] at hteq
    subst hteq
    obtain ⟨htl, htr, htc, htcen, htrad⟩ := hts
    rw [afterBirth_left] at htl
    rw [afterBirth_right] at htr
    rw [afterBirth_chain] at htc
    rw [afterBirth_center] at htcen
    rw [afterBirth_radius] at htrad
    have hsr : (afterCompare s vs vq).right = vs.right := rfl
    have hsc : (afterCompare s vs vq).chain = vs.chain := rfl
    have hscen : (afterCompare s vs vq).center = s.center := rfl
    have hsrad : (afterCompare s vs vq).radius = inc s.radius := rfl
    rw [hsr, hvr] at htr
    rw [hsc] at htc
    rw [hscen] at htcen
    rw [hsrad] at htrad
    obtain ⟨hc1, hc2, hc3⟩ := hP.centreLedger hm
    have hcan := hL.scanCanR hm
    obtain ⟨r0, hi⟩ : ∃ r, ScanInvariant w (position s.center) r s.left s.right := by
      cases hrep : c.replaying with
      | false => exact hP.packM2.packM.scanGeom hm hrep
      | true => exact hP.packM2.scanGeomR hm hrep
    have hlv : 0 < s.right.head.left.length :=
      (present_iff_left hi.rightRep).1 hi.rightPresent
    have hposR : position (right s.right) = position s.right + 1 :=
      right_position s.right hcan hlv
    refine ⟨hM2, fun _ => ⟨by rw [htcen]; exact hc1, by rw [htcen]; exact hc2, ?_⟩, ?_⟩
    · show (position t.center : ℤ) + value t.radius = position t.right
      rw [htcen, htrad, htr, inc_value, hposR]
      push_cast
      omega
    · rw [htc]
      rcases hch with ⟨hne, y, hst, hmy⟩ | ⟨-, -, hz⟩ | ⟨-, -, hz⟩
      · rw [if_pos rfl] at hmy
        exact lagCan_matched (lagCan_step hP.lagCan hL3.backLag hst) hmy
      · rw [hz]; exact lagCan_idle
      · rw [if_pos rfl] at hz
        exact lagCan_matched (lagCan_chainStart _ _ _ _ _) hz
  case scan_shift =>
    rename_i s' hmt hg hm hcl hr hcmp hav hb
    obtain ⟨vs, vq, a, hvl, hvr, hiff, -, hch, hteq⟩ :
      compareFound (PofC centre place entry w) q first s s' := hcmp
    have ha : a = false := by
      cases a with
      | false => rfl
      | true =>
        rw [if_pos rfl] at hteq
        subst hteq
        refine absurd ?_ hmt
        show GalilScaffoldInputHead.read (afterBirth _ (afterCompare s vs vq)).left
          = GalilScaffoldInputHead.read (afterBirth _ (afterCompare s vs vq)).right
        rw [afterBirth_left, afterBirth_right]
        exact hiff.1 rfl
    subst ha
    rw [if_neg (by simp)] at hteq
    subst hteq
    have hsc : (afterMismatch s vs vq).chain = vs.chain := rfl
    obtain ⟨wch, hcw0, hteq2⟩ :
      beginShiftVM' (afterBirth (chainBorn (decide (vq.search.mode
        = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)) t := hb
    have hcw : (afterMismatch s vs vq).chain = ChainVM.watch wch := by
      have h0 : (afterBirth (chainBorn (decide (vq.search.mode
          = GalilScaffoldSearchFinish.Mode.found)) s.chain)
          (afterMismatch s vs vq)).chain = ChainVM.watch wch := hcw0
      rw [afterBirth_chain] at h0
      exact h0
    have hcw' : vs.chain = ChainVM.watch wch := hcw
    have hneidle : s.chain ≠ ChainVM.idle := by
      intro hidle
      rw [hidle] at hch
      exact chainAt_idle_not_watch hch wch hcw'
    rw [afterBirth_of_ne_idle hneidle] at hteq2
    have hLv : LagCan (ChainVM.watch wch) := by
      rcases hch with ⟨hne, y, hst, hmy⟩ | ⟨-, -, hz⟩ | ⟨-, -, hz⟩
      · simp only [Bool.false_eq_true, ↓reduceIte] at hmy
        rw [← hcw', hmy]
        exact lagCan_step hP.lagCan hL3.backLag hst
      · rw [hz] at hcw'; exact absurd hcw' (by simp)
      · simp only [Bool.false_eq_true, ↓reduceIte] at hz
        rw [hz] at hcw'
        unfold chainStart at hcw'
        exact absurd hcw' (by simp)
    refine ⟨hM2, ?_, ?_⟩
    · vac hm
    · have htc : t.chain = ChainVM.watch (GalilScaffoldChainWatch.immediate wch) := by
        rw [hteq2]
      rw [htc]; exact lagCan_immediate hLv
  case scan_fallback =>
    rename_i s' hmt hm hcl hg hr hcmp hav hb
    obtain ⟨pl, ht⟩ : beginFallbackVM' s' t := hb
    refine ⟨hM2, ?_, ?_⟩
    · vac hm
    · have htc : t.chain = ChainVM.idle := by rw [ht]
      rw [htc]; exact lagCan_idle
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨-, -, -, wch, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    have hsw : s.chain = ChainVM.watch wch := hw
    have htc : t.chain = ChainVM.watch (chainShiftOne wch) := by rw [ht]; rfl
    refine ⟨hM2, ?_, by rw [htc]; exact lagCan_shiftOne (by rw [← hsw]; exact hP.lagCan)⟩
    vac hm
  case shift_done =>
    rename_i o hm hp ho
    exact ⟨hM2, fun _ => hL3.shiftDoneLedger hm hp, hP.lagCan⟩
  case copy_one =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    have htc : t.chain = s.chain := by rw [hset]; rfl
    refine ⟨hM2, ?_, by rw [htc]; exact hP.lagCan⟩
    vac hm
  case copy_done =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    have htc : t.chain = s.chain := by rw [hset]; rfl
    refine ⟨hM2, ?_, by rw [htc]; exact hP.lagCan⟩
    vac hm
  case home_start =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    have htc : t.chain = s.chain := by rw [hset]; rfl
    refine ⟨hM2, ?_, by rw [htc]; exact hP.lagCan⟩
    vac hm
  case home_step =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    have htc : t.chain = s.chain := by rw [hset]; rfl
    refine ⟨hM2, ?_, by rw [htc]; exact hP.lagCan⟩
    vac hm
  case fpp_slice =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    have htc : t.chain = s.chain := by rw [hset]; rfl
    refine ⟨hM2, ?_, by rw [htc]; exact hP.lagCan⟩
    vac hm
  case fpp_done =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    have htc : t.chain = s.chain := by rw [hset]; rfl
    refine ⟨hM2, ?_, by rw [htc]; exact hP.lagCan⟩
    vac hm
  case markEnd_step =>
    rename_i hm he hi
    obtain ⟨-, hset⟩ := hi
    have htc : t.chain = s.chain := by rw [hset]; rfl
    refine ⟨hM2, ?_, by rw [htc]; exact hP.lagCan⟩
    vac hm
  case markEnd_found =>
    rename_i hm he hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    have htc : t.chain = s.chain := by rw [hset, heq]; rfl
    refine ⟨hM2, ?_, by rw [htc]; exact hP.lagCan⟩
    vac hm
  case choose_step =>
    rename_i hm hs hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    have htc : t.chain = s.chain := by rw [hset, heq]; rfl
    refine ⟨hM2, ?_, by rw [htc]; exact hP.lagCan⟩
    vac hm
  case choose_select =>
    rename_i hm hodd hs hi
    obtain ⟨heq, hset⟩ := hi
    have htc : t.chain = s.chain := by rw [hset, heq]; rfl
    refine ⟨hM2, ?_, by rw [htc]; exact hP.lagCan⟩
    vac hm
  case rewind_done =>
    rename_i hm hfi hi
    obtain ⟨heq, hset⟩ := hi
    have htc : t.chain = s.chain := by rw [hset, heq]; rfl
    refine ⟨hM2, ?_, by rw [htc]; exact hP.lagCan⟩
    vac hm
  case rewind_one =>
    rename_i hm hfi hpr hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    have htc : t.chain = s.chain := by rw [hset, heq]; rfl
    refine ⟨hM2, ?_, by rw [htc]; exact hP.lagCan⟩
    vac hm
  case rewind_pair =>
    rename_i hm hfi hpr hi
    have heq := hi.1.2
    have hset := hi.2
    have htc : t.chain = s.chain := by rw [hset, heq]; rfl
    refine ⟨hM2, ?_, by rw [htc]; exact hP.lagCan⟩
    vac hm
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, hr, -, hc, hrad, -, -, -, -, hchain, -⟩ := hi
    obtain ⟨hcc, hcs⟩ := hL3.replayLedger hm
    refine ⟨hM2, fun _ => ⟨by rw [hc]; exact hcc, by rw [hc]; exact hcs, ?_⟩, ?_⟩
    · show (position t.center : ℤ) + value t.radius = position t.right
      rw [hc, hr, hrad, value_reset]; omega
    · rw [hchain]; exact lagCan_idle

/-- `lpackM3_tick` in state form. -/
theorem lpackM3_tick' {w : List (Fin 2)} {x y : State GalilVM}
    (hP : LPackM3 w x.ctl x.vm) (hL : LTickLeavesN centre place entry q first w x.ctl x.vm)
    (hA : AuxPack x.ctl x.vm) (hL2 : LTickLeaves2 centre place entry q first w x.ctl x.vm)
    (hL3 : LTickLeaves3 centre place entry q first w x.ctl x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y) :
    LPackM3 w y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpackM3_tick centre place entry q first hP hL hA hL2 hL3 h

/-- **Entry.**  At the boot state the mode is `init` and the chain is idle. -/
theorem lpackM3_boot (w : List (Fin 2)) : LPackM3 w (boot w).ctl (boot w).vm := by
  refine ⟨lpackM2_boot w, ?_, ?_⟩
  · intro hx; exact Mode.noConfusion hx
  · show LagCan ChainVM.idle
    exact lagCan_idle

/-- **The tick induction.** -/
theorem lpackM3_steps {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc)
    (hLv : ∀ i, i ≤ Tc w.length →
      LTickLeavesN centre place entry q first w (st i).ctl (st i).vm ∧
      AuxPack (st i).ctl (st i).vm ∧
      LTickLeaves2 centre place entry q first w (st i).ctl (st i).vm ∧
      LTickLeaves3 centre place entry q first w (st i).ctl (st i).vm) :
    ∀ i, i ≤ Tc w.length → LPackM3 w (st i).ctl (st i).vm := by
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact lpackM3_boot w
  | succ n ih =>
    intro hi
    obtain ⟨h1, h2, h3, h4⟩ := hLv n (by omega)
    exact lpackM3_tick' centre place entry q first (ih (by omega)) h1 h2 h3 h4
      (hP.trace.tick n (by omega))

/-! ## 4. Projections -/

theorem centreLedger_of_lpackM3 {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : LPackM3 w c s) (hm : c.mode = Mode.scan) : CentreLedger s :=
  h.centreLedger hm

theorem lagCan_of_lpackM3 {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : LPackM3 w c s) : LagCan s.chain :=
  h.lagCan

/-! ## 5. `MatchRes2` from the pack -/

/-- **(NAMED residue of `MatchRes2` after `LPackM3`.)**  Everything the landing
pack still needs: the verifier's `lrep` pair now and one step on, the payload
under `replaying`, and the supply of the *moved* right head. -/
structure MatchRest (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  repV : ∀ wch : GalilScaffoldChainWatch.State, s.chain = .watch wch →
    GalilScaffoldInputTrace.Represents wch.machine.verifier.head w ∧
      wch.machine.verifier.head.focus ≠ none
  repVmid : ∀ (y : ChainVM) (wch : GalilScaffoldChainWatch.State),
    ChainStep s.chain y → y = .watch wch →
      GalilScaffoldInputTrace.Represents wch.machine.verifier.head w ∧
        wch.machine.verifier.head.focus ≠ none
  replayPay : c.replaying = true → s.chain ≠ ChainVM.idle → PosPayload2 w s
  canRNext : canRight (right s.right)

/-- **`MatchRes2` from `LPackM3` plus `MatchRest`.**  Closed here: `repR`,
`saneR`, `canR`, `repNext` (scan geometry plus `scanCanR`), `radNext` (the
centre ledger pins the radius exactly), `startLedger` (the centre ledger),
`lagCan` and `backLag` (the pack and its `back` leaf). -/
theorem matchRes2_of_lpackM3 {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hP : LPackM3 w c s) (hL : LTickLeavesN centre place entry q first w c s)
    (hL3 : LTickLeaves3 centre place entry q first w c s)
    (hm : c.mode = Mode.scan) (hR : MatchRest w c s) :
    MatchRes2 w c s := by
  have hcan := hL.scanCanR hm
  obtain ⟨r0, hi⟩ : ∃ r, ScanInvariant w (position s.center) r s.left s.right := by
    cases hrep : c.replaying with
    | false => exact hP.packM2.packM.scanGeom hm hrep
    | true => exact hP.packM2.scanGeomR hm hrep
  have hlv : 0 < s.right.head.left.length :=
    (present_iff_left hi.rightRep).1 hi.rightPresent
  have hposR : position (right s.right) = position s.right + 1 :=
    right_position s.right hcan hlv
  obtain ⟨hc1, hc2, hc3⟩ := hP.centreLedger hm
  refine ⟨⟨hi.rightRep, hi.rightPresent⟩, hR.repV, hR.repVmid, hP.lagCan, hL3.backLag,
    hR.replayPay, Or.inr hlv, hcan,
    ⟨right_word _ w hi.rightRep hcan, right_present _ w hi.rightRep hi.rightPresent hcan⟩,
    hR.canRNext, ?_, fun _ => ⟨hc1, hc2, hc3⟩⟩
  intro rad hsc
  have hrp := hsc.rightPos
  rw [hposR] at hrp
  omega

end Tick

#print axioms lpackM3_tick
#print axioms lpackM3_boot
#print axioms lpackM3_steps
#print axioms centreLedger_of_lpackM3
#print axioms lagCan_of_lpackM3
#print axioms matchRes2_of_lpackM3

end PalPeg.CloseoutPackRun49
