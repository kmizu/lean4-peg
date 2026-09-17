import PalPeg.CloseoutPackRun34
import PalPeg.CloseoutFrontExtra
import PalPeg.CloseoutPackRun30

/-!
# `ShiftLocalS` along a run, from `ChainPosInv`

`CloseoutPackRun32` found `WatchShiftG` false at unguarded comparison targets
(a watch born at `ChainStep.backDone` has `distance = reset`), and
`CloseoutPackRun34` built the guarded replacements — `WatchShiftS`,
`ShiftLocalS`, `ChainPosInv`, `watchShiftS_of_chainPosInv`, `chainPosInv_tick`
(20 of 23 tick shapes closed) — but never wired them to a run.

This file does the wiring: `ChainPosInv` travels along a run by
`chainPosInv_tick`, and at each state it yields `ShiftLocalS` through
`watchShiftS_of_chainPosInv` and `shiftLocalS_of_watchShiftS`, with the idle
branch free (`shiftLocalS_of_chainIdle`).

The residue is exactly `CloseoutPackRun34`'s four named branch hypotheses
(`H_fourOther`, `H_bgP`, `H_matchP`, `H_shiftDoneP`) plus the entry
`ChainPosInv`, in place of the **false** `∀ y, WatchShiftG … y`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutShiftS

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilChainCoupling
open PalPeg.CloseoutLPack5 PalPeg.CloseoutPackRun6 PalPeg.CloseoutPackRun10
open PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack4
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun32
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun34 PalPeg.CloseoutFrontExtra
open PalPeg.CloseoutLPack PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun30
open PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6 PalPeg.CloseoutPackRun12
open PalPeg.GalilTrailSane PalPeg.GalilChainCoupling PalPeg.GalilBranchInvariants
open PalPeg.CloseoutPackRun11 PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun8
open PalPeg.GalilTrailChain PalPeg.GalilFinalAssembly PalPeg.GalilThrottledRun
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3 PalPeg.CloseoutRadPack4
open PalPeg.GalilTrailRad

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`ShiftLocalS` from `ChainPosInv`.**  The idle branch is free; the watching
branch goes through the guarded `WatchShiftS`. -/
theorem shiftLocalS_of_chainPosInv {w : List (Fin 2)}
    (hfour : H_fourOther centre place entry q first w) {x : State GalilVM}
    (h : ChainPosInv w x.ctl x.vm) : ShiftLocalS centre place entry q first w x := by
  by_cases hi : x.vm.chain = ChainVM.idle
  · exact shiftLocalS_of_chainIdle centre place entry q first hi
  · exact shiftLocalS_of_watchShiftS centre place entry q first hi
      (watchShiftS_of_chainPosInv centre place entry q first hfour h)

/-- **`ChainPosInv` along a run.** -/
theorem chainPosInv_steps {w : List (Fin 2)}
    (hbg : H_bgP centre place entry q first w) (hmatch : H_matchP centre place entry q first w)
    (hsd : H_shiftDoneP centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (hx : ChainPosInv w x.ctl x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) :
    ChainPosInv w y.ctl y.vm := by
  induction h with
  | zero x => exact hx
  | @succ n x z y ht _ ih =>
    exact ih (chainPosInv_tick centre place entry q first hbg hmatch hsd hx ht)

/-- **`ShiftLocalS` at every state of a run.**  This is what replaces the false
`∀ y, WatchShiftG … y` on the main path. -/
theorem shiftLocalS_of_run {w : List (Fin 2)}
    (hfour : H_fourOther centre place entry q first w)
    (hbg : H_bgP centre place entry q first w) (hmatch : H_matchP centre place entry q first w)
    (hsd : H_shiftDoneP centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (hx : ChainPosInv w x.ctl x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) :
    ShiftLocalS centre place entry q first w y :=
  shiftLocalS_of_chainPosInv centre place entry q first hfour
    (chainPosInv_steps centre place entry q first hbg hmatch hsd hx h)

#print axioms shiftLocalS_of_chainPosInv
#print axioms chainPosInv_steps
#print axioms shiftLocalS_of_run

/-! ## The two `.shift` readers, re-cut to the guard

`IPackMG.shift`'s four fields are projected at exactly four places
(`CloseoutPackRun30:535, 538, 540, 562`), inside two readers:
`halfBound_of_ipackMG` (:523) and `shiftVerSane_ptMG` (:558).
`CloseoutPackRun34.halfBound_of_shiftLocalS` (:165) already re-cuts the first.
This is the second. -/

/-- **The Run30:558 reader re-cut to the guard.** -/
theorem saneVer_of_shiftLocalS {w : List (Fin 2)} {x : State GalilVM}
    (hsh : ShiftLocalS centre place entry q first w x) (hs : ScanNR x) {s'' t'' : GalilVM}
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare x.vm s'')
    (hmt : ¬ (galilFrameS (PofC centre place entry w) q first).matched s'')
    (hg : shiftGuardVM s'') (hb : beginShiftVM' s'' t'') :
    SaneVer t''.chain :=
  saneVer_beginShift hb (hsh.ver hs s'' t'' hcmp hmt hg hb)

/-- **Both readers along a run, from `ChainPosInv` alone.**  This is the pair
`shiftEntry_ptMG` / `shiftVerSane_ptMG` needs, with the false
`∀ y, WatchShiftG … y` replaced by the four guarded branch hypotheses. -/
theorem shiftReaders_of_run {w : List (Fin 2)}
    (hfour : H_fourOther centre place entry q first w)
    (hbg : H_bgP centre place entry q first w) (hmatch : H_matchP centre place entry q first w)
    (hsd : H_shiftDoneP centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (hx : ChainPosInv w x.ctl x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y)
    (hp : PalPeg.CloseoutPackRun10.LPackM w y.ctl y.vm) (hs : ScanNR y)
    {s'' t'' : GalilVM}
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare y.vm s'')
    (hmt : ¬ (galilFrameS (PofC centre place entry w) q first).matched s'')
    (hg : shiftGuardVM s'') (hb : beginShiftVM' s'' t'') :
    (∃ rad : ℕ,
      ScanInvariant w (position y.vm.center) rad y.vm.left y.vm.right ∧
      GalilScaffoldChainVerifier.canRight y.vm.right ∧
      ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
        2 * periodLength wch ≤ rad) ∧ SaneVer t''.chain := by
  have hsh := shiftLocalS_of_run centre place entry q first hfour hbg hmatch hsd hx h
  exact ⟨halfBound_of_shiftLocalS centre place entry q first hp hsh hs hcmp hmt hg hb,
    saneVer_of_shiftLocalS centre place entry q first hsh hs hcmp hmt hg hb⟩

#print axioms saneVer_of_shiftLocalS
#print axioms shiftReaders_of_run

/-! ## `SaneVer` along the trace, guarded

`CloseoutPackRun26.saneTickG` (:444) calls its entry hypothesis at exactly one
branch — `scan_shift` (:481) — which owns `hmt` and `hg`.  So the guard can be
added to the hypothesis for free.  `CloseoutPackRun30.verSane_ptG` (:591) is the
trace-level reader; both are re-cut here. -/

theorem saneTickS (onLetter leftFirst : GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (delay : ℕ) {c c' : Control} {s t : GalilVM}
    (hx : SaneVer s.chain) (hC : GalilFrontMono.Sane s.center)
    (hen : c.mode = Mode.scan → c.replaying = false → ∀ s'' t'' : GalilVM,
      (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s'' →
      ¬ (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).matched s'' →
      shiftGuardVM s'' → beginShiftVM' s'' t'' → SaneVer t''.chain)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : SaneVer t.chain := by
  cases h
  case init =>
    rename_i hm hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s t := hi
    exact saneVer_congr hch saneVer_idle
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, -, hch, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact chainAt_sane hch hx hC
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, -, hch, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact chainAt_sane hch hx hC
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    exact saneVer_idle
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨a, found, ans, cc, wk, hch, -⟩ :=
      compare_chainAt onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have htc : t.chain = s'.chain := by rw [hpl']; cases c.replaying <;> rfl
    exact saneVer_congr htc (chainAt_sane hch hx hC)
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    exact hen hm hr s' t hcmp hmt hg hb
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨pl, ht⟩ : beginFallbackVM' s' t := hb
    subst ht
    exact saneVer_idle
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨-, -, -, w, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    have hws : s.chain = .watch w := hw
    exact fun r hr => hx r (by rw [hws]; exact hr)
  case shift_done =>
    rename_i o hm hp ho
    exact hx
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : replayStartVM entry s t := hi
    exact saneVer_congr hch saneVer_idle
  all_goals
    (rename_i hi
     have hch : t.chain = s.chain := (congrArg GalilVM.chain hi.2).trans rfl
     exact saneVer_congr hch hx)



theorem verSane_ptS {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm)
    (hsv : ∀ i, i ≤ Tc w.length → ScanNR (st i) → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      ¬ (galilFrameS (PofC centre place entry w) q first).matched s'' →
      shiftGuardVM s'' → beginShiftVM' s'' t'' → SaneVer t''.chain) :
    ∀ i, i ≤ Tc w.length → ∀ p, verOf (st i).vm.chain = some p →
      GalilFrontMono.Sane p := by
  have hsane := sanePack_pt centre place entry q first hw hP hll
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact saneVer_idle
  | succ i ih =>
    intro hi
    have hlt : i < Tc w.length := by omega
    have hle : i ≤ Tc w.length := by omega
    exact saneTickS (onLetterVM w) leftFirstVM centre place entry q first 2048
      (ih hle) (hsane i hle).saneC
      (fun hm hr s'' t'' hcmp hmt hg hb => hsv i hle ⟨hm, hr⟩ s'' t'' hcmp hmt hg hb)
      (hP.trace.tick i hlt)


#print axioms saneTickS
#print axioms verSane_ptS

/-! ## `ShiftOrd` along the trace, guarded

`CloseoutPackRun34.shiftOrd_tickS` (:197) is the guarded tick; this is the
trace-level reader (`CloseoutPackRun30.shiftOrd_ptG` :567) over it. -/

theorem shiftOrd_ptS {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm)
    (hen : ∀ i, i ≤ Tc w.length → ScanNR (st i) → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      ¬ (galilFrameS (PofC centre place entry w) q first).matched s'' →
      shiftGuardVM s'' → beginShiftVM' s'' t'' → ShiftBud t'') :
    ∀ i, i ≤ Tc w.length → ShiftOrd (st i).ctl (st i).vm := by
  have hsane := sanePack_pt centre place entry q first hw hP hll
  have hL := radLedger_pt centre place entry q first hw hP hll
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact shiftOrd_boot w
  | succ i ih =>
    intro hi
    have hlt : i < Tc w.length := by omega
    have hle : i ≤ Tc w.length := by omega
    exact shiftOrd_tickS (onLetterVM w) leftFirstVM centre place entry q first 2048
      (ih hle) (hL i hle).canonRem (hsane i hle).saneC
      (copyIdle_trace centre place entry q first hP i hle)
      (fun hm hr s'' t'' hcmp hmt hg hb => hen i hle ⟨hm, hr⟩ s'' t'' hcmp hmt hg hb)
      (hP.trace.tick i hlt)


#print axioms shiftOrd_ptS

/-! ## `RadPack` without `hws`

`CloseoutPackRun30.radPack_ptMG` (:612) reads `IPackMG.shift` through the two
readers, which is where the false `∀ y, WatchShiftG … y` enters.  Here the same
`RadPack` comes from `ChainPosInv` travelling along the trace, with
`CloseoutPackRun34`'s four guarded branch hypotheses in its place. -/

theorem radPack_ptS {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hfour : H_fourOther centre place entry q first w)
    (hbg : H_bgP centre place entry q first w) (hmatch : H_matchP centre place entry q first w)
    (hsd : H_shiftDoneP centre place entry q first w)
    (hpos0 : ChainPosInv w (st 0).ctl (st 0).vm)
    (hreach : ∀ i, i ≤ Tc w.length →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 i (st 0) (st i))
    (hLP : ∀ i, i ≤ Tc w.length → PalPeg.CloseoutPackRun10.LPackM w (st i).ctl (st i).vm)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm) :
    ∀ i, i ≤ Tc w.length → RadPack (st i).ctl (st i).vm := by
  have hsh : ∀ i, i ≤ Tc w.length → ShiftLocalS centre place entry q first w (st i) := fun i hi =>
    shiftLocalS_of_run centre place entry q first hfour hbg hmatch hsd hpos0 (hreach i hi)
  have hen : ∀ i, i ≤ Tc w.length → ScanNR (st i) → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      ¬ (galilFrameS (PofC centre place entry w) q first).matched s'' →
      shiftGuardVM s'' → beginShiftVM' s'' t'' → ShiftBud t'' := by
    intro i hi hs s'' t'' hcmp hmt hg hb
    obtain ⟨rad, hscan, hcan, hh⟩ :=
      halfBound_of_shiftLocalS centre place entry q first (hLP i hi) (hsh i hi) hs hcmp hmt hg hb
    exact shiftBud_of_scanInv (onLetterVM w) leftFirstVM centre place entry q first
      hscan hcan hcmp hb hh
  have hsv : ∀ i, i ≤ Tc w.length → ScanNR (st i) → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      ¬ (galilFrameS (PofC centre place entry w) q first).matched s'' →
      shiftGuardVM s'' → beginShiftVM' s'' t'' → SaneVer t''.chain := fun i hi hs s'' t'' =>
    saneVer_of_shiftLocalS centre place entry q first (hsh i hi) hs
  have hL := radLedger_pt centre place entry q first hw hP hll
  have hS := shiftOrd_ptS centre place entry q first hw hP hll hen
  have hV := verSane_ptS centre place entry q first hw hP hll hsv
  exact fun i hi => radPack_of_parts (hL i hi) (hS i hi) (hll i hi) (hV i hi)

#print axioms radPack_ptS

end

end PalPeg.CloseoutShiftS
