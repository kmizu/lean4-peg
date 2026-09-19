import PalPeg.WindowRun
import PalPeg.CloseoutPackRun2
import PalPeg.CloseoutReplayCanRight

/-!
# `ChainWindowRun` の `Tick` ごとの transport

`WindowRun.lean` の VM 遷移ごとの補題を、`galilFrameS (PofC centre place entry raw) q first` の
`Tick` 24 構成子に配線する。chain に触る構成子は scan の 5 つ（`scan_wait`／`scan_count` の
`backgroundS`、`scan_match`／`scan_shift`／`scan_fallback` の `compareFound`）と shift の 2 つ
（`shift_one`／`shift_done`）、chain を idle にするのは `init`／`scan_fallback`／`replayStart`／
`restart`。残り（copy/home/fpp/markEnd/choose/rewind）は `fppLens`／`rewindLens` 越しで chain に
触らず、そこでは chain が idle（`AuxPack.coupled.idleOut`）。

周辺事実（run 層が各点で供給するもの）は仮説に取る: `AuxPack`、`CentreRep`、右ヘッドの
`Represents`／存在、比較点の `canRight`、誕生点の `RadiusRep`、`Decodes`。

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.WindowTick

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilReplayGeneral2 PalPeg.GalilBranchInvariants PalPeg.ShiftPalAlongTrace
open PalPeg.WindowInv PalPeg.WindowRun PalPeg.GalilRunSkeleton
open PalPeg.GalilInvPlus2 (CentreRep)
open PalPeg.CloseoutPackRun2 (AuxPack)
open PalPeg.GalilChainCoupling (CopyPack Coupled)
open PalPeg.GalilFrontMono (FrontPack)

/-! ## 1. 周辺の小補題 -/

/-- **中心の記号**（`Decodes` ＋ `CentreRep`）。 -/
theorem centreSymbol_of_decodes {P : Shared} (hP : Decodes P) {raw : List (Fin 2)} {s : GalilVM}
    (hcen : CentreRep raw s) : (encoded raw)[position s.center]? = some (P.centre s) := by
  obtain ⟨hrep, hpres⟩ := hcen
  have hrep' := hrep
  obtain ⟨xs, rs, q, hhead, -⟩ := hrep'
  rcases xs with _ | ⟨a, ls⟩
  · exfalso
    rw [hhead] at hpres
    exact hpres rfl
  · have hcs : s.center = represent ⟨a :: ls, s.center.gap⟩ (rs.map some) q := by
      show s.center = ⟨layout (a :: ls) (rs.map some) q, s.center.gap⟩
      rw [← hhead]
    have hd := (hP.1 s a ls rs q s.center.gap hcs).1
    rw [← represented_read s.center raw hrep hpres, hcs, read_represent]
    exact hd

#print axioms centreSymbol_of_decodes

/-- `fppLens` 越しの遷移は chain・中心・右ヘッド・`remaining` を変えない。 -/
theorem fppLens_rel_fields {R : FppControl.State → FppControl.State → Prop} {s s' : GalilVM}
    (h : fppLens.rel R s s') :
    s'.chain = s.chain ∧ s'.center = s.center ∧ s'.right = s.right ∧ s'.remaining = s.remaining := by
  obtain ⟨-, hs⟩ := h
  rw [hs]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `rewindLens` 越しの遷移は chain を変えない。 -/
theorem rewindLens_rel_chain {R : RewindVM → RewindVM → Prop} {s s' : GalilVM}
    (h : rewindLens.rel R s s') : s'.chain = s.chain := by
  obtain ⟨-, hs⟩ := h
  rw [hs]
  rfl

/-- 比較の着地の左右ヘッド（`afterBirth` と `afterCompare`／`afterMismatch` を通す）。 -/
theorem compare_target_heads {s s' : GalilVM}
    {vs : ScanVM} {vq : SearchVM} {a : Bool} {born : Bool}
    (hs' : s' = afterBirth born (if a then afterCompare s vs vq else afterMismatch s vs vq)) :
    s'.left = vs.left ∧ s'.right = vs.right ∧ s'.chain = vs.chain ∧ s'.center = s.center ∧
      s'.remaining = s.remaining := by
  subst hs'
  cases born <;> cases a <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `Good w`（予測 ＝ 次の読み）を guard の最後の連言と窓から。 -/
theorem good_of_guard {raw : List (Fin 2)} {cen₀ R : ℕ} {cc : Fin 3}
    {w : GalilScaffoldChainWatch.State} {r' : PlaceHead}
    (hinv : WindowInv raw cen₀ R cc (ChainVM.watch w)) (hz : zero w.lag = true)
    (hrep' : GalilScaffoldInputTrace.Represents r'.head raw) (hpres' : r'.head.focus ≠ none)
    (hpos' : position r' = R + 1)
    (hsym : GalilScaffoldChainConsume.symbol w.machine.control.period.focus = read r') :
    GalilScaffoldChainWatch.Good w := by
  obtain ⟨b, xs, hlag, hblk, hcore⟩ := hinv
  have hposNil : w.lag.pos = [] := by
    have hz' : (w.lag.pos.isEmpty && w.lag.neg.isEmpty) = true := hz
    cases hp : w.lag.pos with
    | nil => rfl
    | cons _ _ => simp [hp] at hz'
  have hver : position w.machine.verifier = R := by
    have hl := hlag.2
    rw [hposNil, List.length_nil, Nat.add_zero] at hl
    exact hl
  have hread' : read r' = (encoded raw)[R + 1]? := by
    rw [represented_read r' raw hrep' hpres', hpos']
  have hne : read r' ≠ none := fun hnone => hpres' (Option.map_eq_none_iff.1 hnone)
  have hlt : R + 1 < (encoded raw).length := by
    rcases Nat.lt_or_ge (R + 1) (encoded raw).length with hlt | hge
    · exact hlt
    · exact absurd (hread'.trans (List.getElem?_eq_none_iff.2 hge)) hne
  have hcan : GalilScaffoldChainVerifier.canRight w.machine.verifier :=
    canRight_of_bound _ raw hcore.2.1 hcore.2.2.1 (by omega)
  have hreadVer : read (GalilScaffoldChainVerifier.right w.machine.verifier)
      = (encoded raw)[R + 1]? := by
    rw [represented_read _ raw (right_word _ raw hcore.2.1 hcan)
        (right_present _ raw hcore.2.1 hcore.2.2.1 hcan),
      right_position _ hcan (represented_position _ raw hcore.2.1 hcore.2.2.1).1, hver]
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
  exact ⟨hcan, a, hsym.trans ha, by rw [hreadVer, ← hread', ha]⟩

#print axioms good_of_guard

/-! ## 1b. scan／shift の各構成子の中身 -/

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **background**（`scan_wait`／`scan_count`）: `chainAt false` は chain 1 歩か誕生。 -/
theorem chainWindowRun_background_case {raw : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (hm : c.mode = Mode.scan) (hmode : c'.mode = c.mode)
    (hb : backgroundS (PofC centre place entry raw) q first s t)
    (hx : ChainWindowRun raw c s) (hcen : CentreRep raw s)
    (hrad : ∃ R', RadiusRep s.radius R' ∧ position s.right = position s.center + R')
    (hcs : (encoded raw)[position s.center]? = some ((PofC centre place entry raw).centre s)) :
    ChainWindowRun raw c' t := by
  obtain ⟨-, hr, -, hchainAt, ht⟩ := hb
  have hcenter : t.center = s.center := by
    rw [ht]; unfold afterBirth; split <;> rfl
  have hrem : t.remaining = s.remaining := by
    rw [ht]; unfold afterBirth; split <;> rfl
  rcases hchainAt with ⟨-, y, hstep, hy⟩ | ⟨-, -, hidle'⟩ | ⟨-, -, hstart⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hy
    rw [← hy] at hstep
    exact chainWindowRun_chainStep hm hmode hcenter hr hrem hstep hx
  · exact chainWindowRun_of_idle hidle'
  · simp only [Bool.false_eq_true, ↓reduceIte] at hstart
    obtain ⟨R', hrad', hR⟩ := hrad
    exact chainWindowRun_birth _ _ hcen hrad' hR hcs hcenter hr hstart

#print axioms chainWindowRun_background_case

/-- **一致比較**（`scan_match`）: `compareFound` の一致枝と `matchedPlace`。 -/
theorem chainWindowRun_match_case {raw : List (Fin 2)} {c c' : Control} {s s' t : GalilVM}
    (hm : c.mode = Mode.scan) (hmode : c'.mode = c.mode)
    (hcmp : (galilFrameS (PofC centre place entry raw) q first).compare s s')
    (hmt : (galilFrameS (PofC centre place entry raw) q first).matched s')
    (hpl : (galilFrameS (PofC centre place entry raw) q first).matchedPlace c.replaying s' t)
    (hx : ChainWindowRun raw c s) (hcen : CentreRep raw s)
    (hrightRep : GalilScaffoldInputTrace.Represents s.right.head raw)
    (hrightPres : s.right.head.focus ≠ none) (hcan : canRight s.right)
    (hrad : ∃ R', RadiusRep s.radius R' ∧ position s.right = position s.center + R')
    (hcs : (encoded raw)[position s.center]? = some ((PofC centre place entry raw).centre s)) :
    ChainWindowRun raw c' t := by
  have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
  obtain ⟨vs, vq, a, hvl, hvr, hmatch, -, hchainAt, hs'⟩ := hcmp'
  obtain ⟨hl', hr', hch', hcen', hrem'⟩ := compare_target_heads hs'
  have ha : a = true := by
    apply hmatch.2
    show read vs.left = read vs.right
    have hmt' : read s'.left = read s'.right := hmt
    rwa [hl', hr'] at hmt'
  subst ha
  have hpl' : t = (if c.replaying then {s' with replay := dec s'.replay} else s') := hpl
  have htc : t.chain = s'.chain := by rw [hpl']; split <;> rfl
  have htcenter : t.center = s'.center := by rw [hpl']; split <;> rfl
  have htright : t.right = s'.right := by rw [hpl']; split <;> rfl
  have htrem : t.remaining = s'.remaining := by rw [hpl']; split <;> rfl
  have hl0 : 0 < s.right.head.left.length := (represented_position _ raw hrightRep hrightPres).1
  have hright : position t.right = position s.right + 1 := by
    rw [htright, hr', hvr, right_position _ hcan hl0]
  rcases hchainAt with ⟨-, htick⟩ | ⟨-, -, hidle'⟩ | ⟨-, -, hm'⟩
  · rw [← hch', ← htc] at htick
    exact chainWindowRun_matched hm hmode (htcenter.trans hcen') hright (htrem.trans hrem') htick hx
  · exact chainWindowRun_of_idle (by rw [htc, hch', hidle'])
  · simp only [↓reduceIte] at hm'
    obtain ⟨R', hrad', hR⟩ := hrad
    rw [← hch', ← htc] at hm'
    exact chainWindowRun_birth_matched _ _ hcen hrad' hR hcs (htcenter.trans hcen') hright hm'

#print axioms chainWindowRun_match_case

/-- **shift 入口**（`scan_shift`）: 不一致比較 → guard → `beginShiftVM'`。 -/
theorem chainWindowRun_shift_case {raw : List (Fin 2)} {c c' : Control} {s s' t : GalilVM}
    (hm : c.mode = Mode.scan) (hmode : c'.mode = Mode.shift)
    (hcmp : (galilFrameS (PofC centre place entry raw) q first).compare s s')
    (hmt : ¬ (galilFrameS (PofC centre place entry raw) q first).matched s')
    (hg : (galilFrameS (PofC centre place entry raw) q first).shiftGuard s')
    (hb : (galilFrameS (PofC centre place entry raw) q first).beginShift s' t)
    (hx : ChainWindowRun raw c s)
    (hrightRep : GalilScaffoldInputTrace.Represents s.right.head raw)
    (hrightPres : s.right.head.focus ≠ none) (hcan : canRight s.right) :
    ChainWindowRun raw c' t := by
  have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
  obtain ⟨vs, vq, a, hvl, hvr, hmatch, -, hchainAt, hs'⟩ := hcmp'
  obtain ⟨hl', hr', hch', hcen', hrem'⟩ := compare_target_heads hs'
  have hg' : shiftGuardVM s' := hg
  obtain ⟨w, hw, hz, hphase, -, -, hsym⟩ := hg'
  have hb' : beginShiftVM' s' t := hb
  obtain ⟨w', hw', ht⟩ := hb'
  have hww : w' = w := by rw [hw] at hw'; exact (ChainVM.watch.inj hw').symm
  subst hww
  have htchain : t.chain = ChainVM.watch (GalilScaffoldChainWatch.immediate w') := by rw [ht]
  have htcenter : t.center = s.center := by rw [ht]; exact hcen'
  have htright : t.right = s'.right := by rw [ht]
  have htrem : t.remaining = ofNat (periodLength w') := by rw [ht]
  have hl0 : 0 < s.right.head.left.length := (represented_position _ raw hrightRep hrightPres).1
  have hright' : position s'.right = position s.right + 1 := by
    rw [hr', hvr, right_position _ hcan hl0]
  have hright : position t.right = position s.right + 1 := by rw [htright, hright']
  -- the comparison mismatched, so the chain effect is a plain `ChainStep`
  have ha : a = false := by
    cases a with
    | false => rfl
    | true =>
      exfalso
      apply hmt
      have hm := hmatch.1 rfl
      show read s'.left = read s'.right
      rw [hl', hr']
      exact hm
  subst ha
  have hstep : ChainStep s.chain (ChainVM.watch w') := by
    rcases hchainAt with ⟨-, y, hstep, hy⟩ | ⟨-, -, hidle'⟩ | ⟨-, -, hstart⟩
    · simp only [Bool.false_eq_true, ↓reduceIte] at hy
      rw [← hy, ← hch', hw] at hstep
      exact hstep
    · exfalso
      rw [hidle'] at hch'
      rw [hch'] at hw
      cases hw
    · exfalso
      simp only [Bool.false_eq_true, ↓reduceIte] at hstart
      rw [hstart] at hch'
      rw [hch'] at hw
      cases hw
  -- `Good w'` from the guard's prediction match at the new right head
  have hx' := hx
  obtain ⟨cen₀, cc, -, hinv, -, -, -⟩ := hx'
  have hinvW : WindowInv raw cen₀ (position s.right) cc (ChainVM.watch w') :=
    windowInv_step hinv hstep
  have hrep' : GalilScaffoldInputTrace.Represents s'.right.head raw := by
    rw [hr', hvr]; exact right_word _ raw hrightRep hcan
  have hpres' : s'.right.head.focus ≠ none := by
    rw [hr', hvr]; exact right_present _ raw hrightRep hrightPres hcan
  have hgood : GalilScaffoldChainWatch.Good w' :=
    good_of_guard hinvW hz hrep' hpres' hright' hsym
  exact chainWindowRun_shift hm hmode hstep hphase hz hgood htcenter hright htrem htchain hx

#print axioms chainWindowRun_shift_case

/-- **shift の 1 歩**（`shift_one`）: `shiftLens` 越しの `shiftTick`＋`chainShiftOne`。 -/
theorem chainWindowRun_shiftOne_case {raw : List (Fin 2)} {c : Control} {s t : GalilVM}
    (hm : c.mode = Mode.shift)
    (hp : (galilFrameS (PofC centre place entry raw) q first).remainingPos s)
    (hso : (galilFrameS (PofC centre place entry raw) q first).shiftOne s t)
    (hx : ChainWindowRun raw c s) (hcen : CentreRep raw s) (hci : CopyIdle s) :
    ChainWindowRun raw c t := by
  have hso' : shiftLens.rel (shiftFrame (fun _ => True) (fun _ => True)).shiftOne s t := hso
  obtain ⟨⟨hcanC, -, -, w, hw, hget⟩, hset⟩ := hso'
  have htcenter : t.center = right s.center :=
    congrArg (fun v : ShiftVM => v.shift.center) hget
  have htrem : t.remaining = dec s.remaining :=
    congrArg (fun v : ShiftVM => v.shift.remaining) hget
  have htchain : t.chain = ChainVM.watch (chainShiftOne w) :=
    congrArg (fun v : ShiftVM => v.chain) hget
  have htright : t.right = s.right := by rw [hset]; rfl
  have hpos : positive s.remaining = true := by
    rcases hp with hp | hp
    · exact hp
    · exact absurd hp hci
  have hl0 : 0 < s.center.head.left.length := (represented_position _ raw hcen.1 hcen.2).1
  have hcanC' : canRight s.center := hcanC
  have hcenter : position t.center = position s.center + 1 := by
    rw [htcenter, right_position s.center hcanC' hl0]
  exact chainWindowRun_shiftOne hm hm hw htchain hcenter htright htrem hpos hx

#print axioms chainWindowRun_shiftOne_case

end

/-! ## 2. `Tick` ごとの組み立て -/

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`ChainWindowRun` は `galilFrameS` の 1 tick で保たれる**（周辺事実は仮説）。 -/
theorem chainWindowRun_tick {raw : List (Fin 2)} {x y : State GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (h : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hx : ChainWindowRun raw x.ctl x.vm)
    (haux : AuxPack x.ctl x.vm)
    (hcen : x.ctl.mode = Mode.scan ∨ x.ctl.mode = Mode.shift → CentreRep raw x.vm)
    (hrightRep : x.ctl.mode = Mode.scan → GalilScaffoldInputTrace.Represents x.vm.right.head raw)
    (hrightPres : x.ctl.mode = Mode.scan → x.vm.right.head.focus ≠ none)
    (hfront : FrontPack x.ctl x.vm)
    (hrad : x.ctl.mode = Mode.scan →
      ∃ R', RadiusRep x.vm.radius R' ∧ position x.vm.right = position x.vm.center + R') :
    ChainWindowRun raw y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  have hidle : c.mode ≠ Mode.scan → c.mode ≠ Mode.shift → c.mode ≠ Mode.init →
      s.chain = ChainVM.idle := haux.coupled.idleOut
  cases h with
  | init c s t hm hi =>
    have hi' : initVM entry s t := hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hChain, -, -, -, -, -⟩ := hi'
    exact chainWindowRun_of_idle hChain
  | scan_wait c s t hm hav hb =>
    exact chainWindowRun_background_case centre place entry q first hm rfl hb hx
      (hcen (Or.inl hm)) (hrad hm) (centreSymbol_of_decodes hP (hcen (Or.inl hm)))
  | scan_count c s t hm hav hc hb =>
    exact chainWindowRun_background_case centre place entry q first hm rfl hb hx
      (hcen (Or.inl hm)) (hrad hm) (centreSymbol_of_decodes hP (hcen (Or.inl hm)))
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    have hcan : canRight s.right := by
      rcases hav with hrp | hav
      · exact PalPeg.CloseoutReplayCanRight.canRight_of_frontPack hfront hrp
      · exact hav
    exact chainWindowRun_match_case centre place entry q first hm rfl hcmp hmt hpl hx
      (hcen (Or.inl hm)) (hrightRep hm) (hrightPres hm) hcan (hrad hm)
      (centreSymbol_of_decodes hP (hcen (Or.inl hm)))
  | scan_shift c s s' t hm hav hc hcmp hmt hr hg hb =>
    have hcan : canRight s.right := by
      rcases hav with hrp | hav
      · exact PalPeg.CloseoutReplayCanRight.canRight_of_frontPack hfront hrp
      · exact hav
    exact chainWindowRun_shift_case centre place entry q first hm rfl hcmp hmt hg hb hx
      (hrightRep hm) (hrightPres hm) hcan
  | scan_fallback c s s' t hm hav hc hcmp hmt hg hr hb =>
    have hb' : beginFallbackVM' s' t := hb
    obtain ⟨p, ht, -⟩ := hb'
    unfold beginFallbackVM at ht
    exact chainWindowRun_of_idle (congrArg GalilVM.chain ht)
  | shift_one c s t hm hp hso =>
    exact chainWindowRun_shiftOne_case centre place entry q first hm hp hso hx (hcen (Or.inr hm))
      (haux.copyP (by rw [hm]; decide))
  | shift_done c s o hm hp ho =>
    have hnp : positive s.remaining = false := by
      have : ¬ (positive s.remaining = true) := fun hpos => hp (Or.inl hpos)
      simpa using this
    exact chainWindowRun_shiftDone hm rfl hnp hx
  | copy_one c s t hm hp hc =>
    apply chainWindowRun_of_idle
    rw [(fppLens_rel_fields hc).1]
    exact hidle (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)
  | copy_done c s t hm hp hc =>
    apply chainWindowRun_of_idle
    rw [(fppLens_rel_fields hc).1]
    exact hidle (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)
  | home_start c s t hm hl hc =>
    apply chainWindowRun_of_idle
    rw [(fppLens_rel_fields hc).1]
    exact hidle (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)
  | home_step c s t hm hl hc =>
    apply chainWindowRun_of_idle
    rw [(fppLens_rel_fields hc).1]
    exact hidle (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)
  | fpp_slice c s t hm hc =>
    apply chainWindowRun_of_idle
    rw [(fppLens_rel_fields hc).1]
    exact hidle (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)
  | fpp_done c s t hm hc =>
    apply chainWindowRun_of_idle
    rw [(fppLens_rel_fields hc).1]
    exact hidle (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)
  | markEnd_found c s t hm he hc =>
    apply chainWindowRun_of_idle
    rw [rewindLens_rel_chain hc]
    exact hidle (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)
  | markEnd_step c s t hm he hc =>
    apply chainWindowRun_of_idle
    rw [(fppLens_rel_fields hc).1]
    exact hidle (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)
  | choose_select c s t hm ho hs hc =>
    apply chainWindowRun_of_idle
    rw [rewindLens_rel_chain hc]
    exact hidle (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)
  | choose_step c s t hm hs hc =>
    apply chainWindowRun_of_idle
    rw [rewindLens_rel_chain hc]
    exact hidle (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)
  | rewind_done c s t hm hf hc =>
    apply chainWindowRun_of_idle
    rw [rewindLens_rel_chain hc]
    exact hidle (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)
  | rewind_one c s t hm hf hp hc =>
    apply chainWindowRun_of_idle
    rw [rewindLens_rel_chain hc]
    exact hidle (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)
  | rewind_pair c s t hm hf hp hc =>
    apply chainWindowRun_of_idle
    rw [rewindLens_rel_chain hc]
    exact hidle (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)
  | replayStart c s t o hm hrs ho ho' =>
    have hrs' : replayStartVM entry s t := hrs
    obtain ⟨-, -, -, -, -, -, -, -, -, hChain, -, -, -, -, -⟩ := hrs'
    exact chainWindowRun_of_idle hChain
  | restart c s t hm hrs =>
    have hrs' : restartVM entry s t := hrs
    obtain ⟨w, -, -, -, -, ht⟩ := hrs'
    exact chainWindowRun_of_idle (congrArg GalilVM.chain ht)

#print axioms chainWindowRun_tick

end

end PalPeg.WindowTick
