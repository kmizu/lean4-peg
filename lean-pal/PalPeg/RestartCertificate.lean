import PalPeg.RestartBoundary
import PalPeg.CanonicalChainMinimal

/-!
# The left period certificate along packed runs

A chain is born from a DP candidate, which certifies period `2h` on the four semiperiods to the
left of the birth centre (`candidate_periodOn`).  While the centre is fixed the certificate rides
on the chain's semantic datum (`SemWith`); at a shift entry the whole scan span is periodic
(`periodOn_span_of_next`), which certifies the landing centre.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.RestartCertificate

open PalPeg GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply GalilBranchInvariants
open PalPeg.CanonicalSearchProgram PalPeg.GalilShiftH
open GalilScaffoldTop GalilScaffoldController GalilRunSkeleton GalilInvPlus3
open PalPeg.WindowInv PalPeg.WindowRun PalPeg.WindowPack PalPeg.ShiftPalAlongTrace
open PalPeg.CloseoutPackRun26 PalPeg.CanonicalChainMinimal PalPeg.RestartBoundary
open PalPeg.RestartStageRun

/-- Period `2H` on the four semiperiods to the left of `C`. -/
def LeftPeriod (raw : List (Fin 2)) (C H : ℕ) : Prop :=
  PeriodOn (encoded raw) (2 * H) (C - 4 * H) C

/-- The certificate at a machine state: on the scan centre in scan mode, on the landing centre
in shift mode. -/
def CertAt (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  (c.mode = Mode.scan → SemWith (LeftPeriod raw (position s.center)) s.chain) ∧
  (c.mode = Mode.shift → ∃ w rem, s.chain = .watch w ∧ s.remaining = ofNat rem ∧
    LeftPeriod raw (position s.center + rem) (periodLength w))

theorem certAt_of_idle {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (hmode : c.mode ≠ Mode.shift) (hidle : s.chain = .idle) : CertAt raw c s :=
  ⟨fun _ => by rw [hidle]; trivial, fun h => absurd h hmode⟩

theorem leftCertificate_of_certAt {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (hcert : CertAt raw c s) (hm : c.mode = Mode.scan) : LeftCertificate raw s := by
  intro w hw
  have hsem := hcert.1 hm
  rw [hw] at hsem
  obtain ⟨-, H, -, hcells, hperiod⟩ := hsem
  have hH : H = periodLength w := by
    have h1 : cellsOf (.watch w) = periodLength w + 1 := rfl
    omega
  rw [← hH]
  exact hperiod

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- The birth hook in the form `semWith_chainAt` consumes. -/
def BirthCertificate (raw : List (Fin 2)) (s : GalilVM) : Prop :=
  ∀ a vq, s.chain = .idle → searchEffect (PofC centre place entry raw) a s vq →
    vq.search.mode = .found → ∃ H,
      CopyInv (vq.dp.config.tapes 11) reset ((PofC centre place entry raw).place s)
        (GalilScaffoldChainPeriod.start ((PofC centre place entry raw).centre s)) H ∧
      LeftPeriod raw (position s.center) H

theorem birthCertificate_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hr : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y)
    (hm : y.ctl.mode = .scan) : BirthCertificate centre place entry raw y.vm := by
  intro a vq hidle he hf
  obtain ⟨lower, span, h, -, -, hcand, -, hcopy⟩ :=
    PalPeg.CanonicalSearchHistory.birthMinimal_packed centre place entry q first hP hI hr hm
      hidle he hf
  have hp := PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hr
  have hcen := (hp.win hP).centreRep (Or.inl hm)
  obtain ⟨a0, ls, rs, suffix, hdec, hraw⟩ :=
    represents_decompose y.vm.center raw hcen.1 hcen.2
  obtain ⟨-, hplace⟩ := hP.1 y.vm a0 ls rs suffix y.vm.center.gap hdec
  refine ⟨h, hcopy, ?_⟩
  have hper := candidate_periodOn a0 ls rs suffix y.vm.center.gap span lower h
    (by rw [← hplace]; exact hcand)
  unfold LeftPeriod
  rw [hraw, hdec]
  exact hper

/-- The certificate of the landing centre at a shift entry. -/
theorem leftPeriod_shiftEntry {raw : List (Fin 2)} {c : Control} {s s' : GalilVM}
    {w : GalilScaffoldChainWatch.State}
    (hm : c.mode = .scan) (hr : c.replaying = false)
    (hpack : PalPeg.CloseoutPackRun10.LPackM raw c s)
    (hwin : WindowRunPack raw c s)
    (hav : (galilFrameS (PofC centre place entry raw) q first).available s)
    (hcmp : (galilFrameS (PofC centre place entry raw) q first).compare s s')
    (hmt : ¬ (galilFrameS (PofC centre place entry raw) q first).matched s')
    (hg : shiftGuardVM s') (hw : s'.chain = .watch w) :
    LeftPeriod raw (position s.center + periodLength w) (periodLength w) := by
  have hcan : canRight s.right := hav
  obtain ⟨k, hscan⟩ := hpack.scanGeom hm hr
  have hsNR : ScanNR ⟨c,s⟩ := ⟨hm,hr⟩
  have hledger := freshLedger_of_windowRunPack centre place entry q first hpack hwin hcan
    hsNR hcmp hmt hg w hw k hscan
  obtain ⟨-, hleft, hh0, -, hcaught⟩ := hledger
  have hsp := shiftPal_of_windowRunPack centre place entry q first hpack hwin hcan hsNR
  obtain ⟨-, -, hpal1⟩ := hsp s' hcmp hmt w hw hg k hscan
  have hfourZ := four_of_guard centre place entry q first hwin.coupled hsNR hcmp hmt hg hw
  obtain ⟨R, hRR, hposR⟩ := hwin.radiusScan hm
  have hpos : position s.right = position s.center + k := hscan.rightPos
  have hkR : k = R := by omega
  have hfour : 4 * periodLength w ≤ k := by
    have hv : value s.radius = (R : ℤ) := hRR.2
    rw [hv] at hfourZ
    omega
  have hright := periodOn_right_succ hscan.palindrome (by omega) hleft hcaught
  have hall := periodOn_span_of_next hh0 (by omega) hscan.palindrome hpal1 hright
  exact hall.mono (by omega) (by omega)

/-- One tick keeps the certificate.  `hbirth` and the packs come from the packed run. -/
theorem certAt_tick {raw : List (Fin 2)} {x y : State GalilVM}
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hcert : CertAt raw x.ctl x.vm)
    (hpack : PalPeg.CloseoutPackRun10.LPackM raw x.ctl x.vm)
    (hwinX : WindowRunPack raw x.ctl x.vm)
    (hbirth : x.ctl.mode = .scan → BirthCertificate centre place entry raw x.vm)
    (hcopy : x.ctl.mode = .shift → CopyIdle x.vm) :
    CertAt raw y.ctl y.vm := by
  cases ht with
  | init c s t hm hi =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_⟩ := hi
    exact certAt_of_idle (by simp) hch
  | scan_wait c s t hm hav hb =>
    obtain ⟨-, -, hch, hcenter, -⟩ :=
      backgroundS_fields (PofC centre place entry raw) q first hb
    refine ⟨fun _ => ?_, fun h => by simp [hm] at h⟩
    rw [hcenter]
    exact semWith_chainAt (hcert.1 hm) (fun hi hf => hbirth hm false _ hi
      (backgroundS_fields (PofC centre place entry raw) q first hb).2.2.2.2.2.2.2.2.2.2.2
      (by simpa using hf)) hch
  | scan_count c s t hm hav hc hb =>
    obtain ⟨-, -, hch, hcenter, -⟩ :=
      backgroundS_fields (PofC centre place entry raw) q first hb
    refine ⟨fun _ => ?_, fun h => by simp [hm] at h⟩
    rw [hcenter]
    exact semWith_chainAt (hcert.1 hm) (fun hi hf => hbirth hm false _ hi
      (backgroundS_fields (PofC centre place entry raw) q first hb).2.2.2.2.2.2.2.2.2.2.2
      (by simpa using hf)) hch
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
    obtain ⟨vs, vq, a, -, -, -, heffect, hch, heq⟩ := hcmp'
    obtain ⟨-, -, hchain', hcenter', -⟩ := PalPeg.WindowTick.compare_target_heads heq
    have hchain : t.chain = s'.chain := by rw [hpl]; split <;> rfl
    have hcenter : t.center = s'.center := by rw [hpl]; split <;> rfl
    refine ⟨fun _ => ?_, fun h => by simp [hm] at h⟩
    rw [hchain, hchain', hcenter, hcenter']
    exact semWith_chainAt (hcert.1 hm) (fun hi hf => hbirth hm a vq hi heffect
      (by simpa using hf)) hch
  | scan_shift c s s' t hm hav hc hcmp hmt hr hg hb =>
    have ha : (galilFrameS (PofC centre place entry raw) q first).available s := by
      rcases hav with hrep | ha
      · rw [hr] at hrep; cases hrep
      · exact ha
    obtain ⟨w, hw, hteq⟩ := hb
    have hperiod := leftPeriod_shiftEntry centre place entry q first hm hr hpack hwinX ha hcmp
      hmt hg hw
    have hscenter : s'.center = s.center := by
      have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
      obtain ⟨vs, vq, a, -, -, -, -, -, heq⟩ := hcmp'
      exact (PalPeg.WindowTick.compare_target_heads heq).2.2.2.1
    have hblockW : OnBlock w.machine.control.period := by
      have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
      obtain ⟨w₀, hw₀, hint⟩ := source_watch_of_guard hcmp' hmt hg
      have hb0 : BlockInv s.chain := hwinX.coupled.block
      rw [hw₀] at hb0
      exact blockInv_step (.watchStep w₀ w (hint w hw)) hb0
    have hperiodI : periodLength (GalilScaffoldChainWatch.immediate w) = periodLength w :=
      PalPeg.GalilChainCoupling.periodLength_consume
        w.machine w.lag w.margin w.lag (inc w.margin) hblockW
    refine ⟨fun h => by simp at h, fun _ =>
      ⟨GalilScaffoldChainWatch.immediate w, periodLength w, by rw [hteq], by rw [hteq], ?_⟩⟩
    have htcenter : t.center = s.center := by rw [hteq, hscenter]
    rw [htcenter, hperiodI]
    exact hperiod
  | scan_fallback c s s' t hm hav hc hcmp hmt hg hr hb =>
    obtain ⟨p, hteq, -⟩ := hb
    exact certAt_of_idle (by simp) (by rw [hteq])
  | shift_one c s t hm hp hso =>
    obtain ⟨w0, rem, hw0, hrem0, hperiod⟩ := hcert.2 hm
    have hpos : positive s.remaining = true := by
      rcases hp with hp | hp
      · exact hp
      · exact absurd hp (hcopy hm)
    obtain ⟨⟨hcanC, -, -, w, hw, hget⟩, hset⟩ := hso
    change s.chain = .watch w at hw
    have hwe : w0 = w := by rw [hw] at hw0; cases hw0; rfl
    subst hwe
    have hchain : t.chain = .watch (chainShiftOne w0) := by rw [hset, hget]; rfl
    have hrem : t.remaining = dec s.remaining := by rw [hset, hget]; rfl
    have htc : t.center = right s.center := by rw [hset, hget]; rfl
    have hcen := hwinX.centreRep (Or.inr hm)
    have hl0 : 0 < s.center.head.left.length :=
      (represented_position _ raw hcen.1 hcen.2).1
    have hcenter : position t.center = position s.center + 1 := by
      rw [htc, right_position s.center hcanC hl0]
    refine ⟨fun h => by simp [hm] at h, fun _ => ?_⟩
    cases rem with
    | zero => rw [hrem0] at hpos; exact absurd hpos (by decide)
    | succ rem =>
      refine ⟨chainShiftOne w0, rem, hchain, by rw [hrem, hrem0, dec_ofNat_succ], ?_⟩
      have hdest : position t.center + rem = position s.center + (rem + 1) := by omega
      rw [hdest]
      exact hperiod
  | shift_done c s o hm hp ho =>
    obtain ⟨w, rem, hw, hrem, hperiod⟩ := hcert.2 hm
    have hz : positive s.remaining = false := Bool.eq_false_iff.mpr (fun h => hp (Or.inl h))
    have hrem0 : rem = 0 := by
      cases rem with
      | zero => rfl
      | succ rem =>
        rw [hrem] at hz
        simp [positive, ofNat, List.replicate_succ] at hz
    subst hrem0
    refine ⟨fun _ => ?_, fun h => by simp at h⟩
    have hblock : BlockInv s.chain := hwinX.coupled.block
    rw [hw] at hblock ⊢
    exact ⟨trivial, periodLength w, hblock, rfl, by simpa using hperiod⟩
  | replayStart c s t o hm hr ho ho' =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_,_,_⟩ := hr
    exact certAt_of_idle (by simp) hch
  | restart c s t hm hr =>
    obtain ⟨_,_,_,_,_,rfl⟩ := hr
    exact certAt_of_idle (by simp [hm]) rfl
  | copy_one _ _ _ hm _ hi | copy_done _ _ _ hm _ hi
  | home_start _ _ _ hm _ hi | home_step _ _ _ hm _ hi
  | fpp_slice _ _ _ hm hi | fpp_done _ _ _ hm hi
  | markEnd_found _ _ _ hm _ hi | markEnd_step _ _ _ hm _ hi
  | choose_select _ _ _ hm _ _ hi | choose_step _ _ _ hm _ hi
  | rewind_done _ _ _ hm _ hi | rewind_one _ _ _ hm _ _ hi
  | rewind_pair _ _ _ hm _ _ hi =>
    have hidle := hwinX.coupled.idleOut (by rw [hm]; decide) (by rw [hm]; decide)
      (by rw [hm]; decide)
    have hchain := (congrArg GalilVM.chain hi.2).trans hidle
    exact certAt_of_idle (by intro hshift; simp [hm] at hshift) hchain

end PalPeg.RestartCertificate
