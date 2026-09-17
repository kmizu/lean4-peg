import PalPeg.CloseoutPackRun38

/-!
# `CloseoutPackRun40`: the strengthened post-shift half `Other'` (bound `5h`)
and `H_fourOther` discharged for `Coupled'`

`CloseoutPackRun38.other_guard_lower` shows that `GalilChainCoupling.Other`
(`2h ≤ R + C`) cannot give the `4h ≤ distance` that
`CloseoutPackRun34.watchShiftS_of_chainPosInv` names as `H_fourOther`.  This
file strengthens the post-shift half of `WatchOK` to the bound the machine
actually maintains and re-runs the coupling on it.

* §1 `Other'`: `periodOnly = true`, `1 ≤ h`, and `5h ≤ R + C (+ Rem in shift
  mode)`.  The bound is sharp with respect to what the shift exit
  (`scan_shift`) can deliver: the exit happens at a guard with
  `distance = R₀` (lag `0`), lands at `R = R₀ + 1`, `C = 0`, `Rem = h`, so it
  can establish `k·h ≤ R₀ + 1 + h`; a *fresh* guard carries only `4h ≤ R₀`
  (`four_of_freshC`, phase `4`), hence `k = 5` is the largest constant
  provable, and `Other'` at a guard (`C ≤ 1`) yields `distance ≥ 5h − 1`
  (matching the machine reading "real guards have `R ≥ 5h − 1`").
* §2 `Coupled'`: `Coupled` with `Other'`; `coupled'_toCoupled`.
* §3 `compare'_inv`, `coupled'_tick`: the mirror of
  `GalilChainCoupling.coupled_tick`.  Every branch closes: the shift exit
  from a fresh guard uses `4h ≤ R₀` (and `1 ≤ h` from `FreshC`), from an
  `Other'` guard uses `5h ≤ R₀ + C`, `C ≤ 1`; `shift_one` keeps `R + C + Rem`
  (`−1 + 2 − 1`); `shift_done` drops `Rem ≤ 0`; `scan_match` keeps `R + C`
  (`+1`, `cycleAfter` `−1`).  No hypothesis is left open.
* §4 `four_of_other'`: `4h ≤ distance` at a guarded unmatched target in the
  `Other'` half — the content of `H_fourOther`, now a theorem.
* §5 `ChainPosInv'` (= `ChainPosInv` over `Coupled'`),
  `watchShiftS_of_chainPosInv'` (no `H_fourOther`), `chainPosInv'_tick`
  (same three payload hypotheses as `chainPosInv_tick`).

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun40

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilChainCoupling
open PalPeg.CloseoutLPack5 PalPeg.CloseoutPackRun6 PalPeg.CloseoutPackRun10
open PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack4
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun32
open PalPeg.CloseoutPackRun34 PalPeg.CloseoutPackRun38 PalPeg.GalilBranchInvariants

/-! ## 1. The strengthened post-shift bound -/

/-- **`Other'`**: the post-shift round bound with the constant `5`
(`radius + countdown (+ shift budget)` covers five semiperiods) and a
positive semiperiod. -/
def Other' (po : Bool) (m : Mode) (R C Rem : ℤ) (h : ℕ) : Prop :=
  po = true ∧ 1 ≤ h ∧ (m = Mode.shift → 5 * (h : ℤ) ≤ R + C + Rem) ∧
    (m ≠ Mode.shift → 5 * (h : ℤ) ≤ R + C)

theorem other_of_other' {po : Bool} {m : Mode} {R C Rem : ℤ} {h : ℕ}
    (hO : Other' po m R C Rem h) : Other po m R C Rem h := by
  obtain ⟨hpo, -, hs, hns⟩ := hO
  have h0 : (0 : ℤ) ≤ h := by positivity
  exact ⟨hpo, fun hm => by have := hs hm; linarith, fun hm => by have := hns hm; linarith⟩

/-- A fresh watch control has a positive semiperiod. -/
theorem one_le_of_freshC {k : GalilScaffoldChainConsume.State} (hf : FreshC k) :
    1 ≤ k.period.left.length + k.period.right.length := by
  cases hfw : k.forward with
  | true => have := (hf.1 hfw).1; omega
  | false => have := (hf.2 hfw).1; omega

/-! ## 2. The coupling over `Other'` -/

/-- **`Coupled'`**: `GalilChainCoupling.Coupled` with the post-shift half
strengthened to `Other'`. -/
structure Coupled' (c : Control) (s : GalilVM) : Prop where
  idleOut : c.mode ≠ Mode.scan → c.mode ≠ Mode.shift → c.mode ≠ Mode.init → s.chain = .idle
  block : BlockInv s.chain
  sum : SumRel s.chain (value s.radius)
  watch : WatchOK s.chain (c.mode ≠ Mode.shift)
    (Other' s.periodOnly c.mode (value s.radius) (value s.cycle) (value s.remaining))

theorem coupled'_toCoupled {c : Control} {s : GalilVM} (h : Coupled' c s) : Coupled c s :=
  ⟨h.idleOut, h.block, h.sum, watchOK_mono (fun _ => other_of_other') h.watch⟩

theorem coupled'_of_idle {c : Control} {s : GalilVM} (h : s.chain = .idle) : Coupled' c s :=
  ⟨fun _ _ _ => h, by rw [h]; trivial, by rw [h]; trivial, fun w hw => by rw [h] at hw; cases hw⟩

/-! ## 3. One tick -/

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- `GalilChainCoupling.compare_inv` over `Coupled'`. -/
theorem compare'_inv {c : Control} {s s' : GalilVM} (hC : Coupled' c s) (hm : c.mode = Mode.scan)
    (hcmp : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s') :
    BlockInv s'.chain ∧ s'.periodOnly = s.periodOnly ∧ s'.remaining = s.remaining ∧
    ((galilFrameS (sharedC onLetter leftFirst centre place entry) q first).matched s' →
      s'.radius = inc s.radius ∧ s'.cycle = cycleAfter s ∧
      SumRel s'.chain (value s.radius + 1) ∧
      WatchOK s'.chain (c.mode ≠ Mode.shift)
        (Other' s.periodOnly c.mode (value s.radius) (value s.cycle) (value s.remaining))) ∧
    (¬ (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).matched s' →
      s'.radius = inc s.radius ∧ s'.cycle = s.cycle ∧
      SumRel s'.chain (value s.radius) ∧
      WatchOK s'.chain (c.mode ≠ Mode.shift)
        (Other' s.periodOnly c.mode (value s.radius) (value s.cycle) (value s.remaining))) := by
  obtain ⟨vs, vq, a, -, -, hiff, -, hch, hteq⟩ :
    compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
  have hF : c.mode ≠ Mode.shift := by rw [hm]; decide
  cases a with
  | true =>
    rw [if_pos rfl] at hteq
    subst hteq
    obtain ⟨hb, hs, hw⟩ := chainAt_true_inv hch hF hC.block hC.sum hC.watch
    exact ⟨hb, rfl, rfl, fun _ => ⟨rfl, rfl, hs, hw⟩, fun hn => absurd (hiff.1 rfl) hn⟩
  | false =>
    rw [if_neg (by simp)] at hteq
    subst hteq
    obtain ⟨hb, hs, hw⟩ := chainAt_false_inv hch hF hC.block hC.sum hC.watch
    exact ⟨hb, rfl, rfl, fun hmt => absurd (hiff.2 hmt) (by simp), fun _ => ⟨rfl, rfl, hs, hw⟩⟩

/-- **`coupled'_tick`**: the mirror of `GalilChainCoupling.coupled_tick` with
the strengthened half.  The shift exit (`scan_shift`) is the content. -/
theorem coupled'_tick {c c' : Control} {s t : GalilVM} (hC : Coupled' c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : Coupled' c' t := by
  cases h
  case init =>
    rename_i hm hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s t := hi
    exact coupled'_of_idle hch
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, -, hch, -, hpo, hrad, -, hcyc, hrem, -, -, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    have hF : c.mode ≠ Mode.shift := by rw [hm]; decide
    obtain ⟨hb', hs', hw'⟩ := chainAt_false_inv hch hF hC.block hC.sum hC.watch
    refine ⟨fun h1 => absurd hm h1, hb', by rw [hrad]; exact hs', ?_⟩
    rw [hpo, hrad, hcyc, hrem]; exact hw'
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, -, hch, -, hpo, hrad, -, hcyc, hrem, -, -, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    have hF : c.mode ≠ Mode.shift := by rw [hm]; decide
    obtain ⟨hb', hs', hw'⟩ := chainAt_false_inv hch hF hC.block hC.sum hC.watch
    refine ⟨fun h1 => absurd hm h1, hb', by rw [hrad]; exact hs', ?_⟩
    rw [hpo, hrad, hcyc, hrem]; exact hw'
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    exact coupled'_of_idle rfl
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨hb, hpo, hrem, hmat, -⟩ :=
      compare'_inv onLetter leftFirst centre place entry q first hC hm hcmp
    obtain ⟨hrad, hcyc, hs, hw⟩ := hmat hmt
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have htc : t.chain = s'.chain := by rw [hpl']; cases c.replaying <;> rfl
    have htr : t.radius = s'.radius := by rw [hpl']; cases c.replaying <;> rfl
    have hty : t.cycle = s'.cycle := by rw [hpl']; cases c.replaying <;> rfl
    have htp : t.periodOnly = s'.periodOnly := by rw [hpl']; cases c.replaying <;> rfl
    have htm : t.remaining = s'.remaining := by rw [hpl']; cases c.replaying <;> rfl
    refine ⟨fun h1 => absurd hm h1, by rw [htc]; exact hb, ?_, ?_⟩
    · rw [htc, htr, hrad, inc_value]; exact hs
    · rw [htc, htr, hty, htp, htm, hpo, hrem, hrad, hcyc]
      refine watchOK_mono ?_ hw
      rintro h ⟨hp, hh, -, hns⟩
      refine ⟨hp, hh, fun h1 => absurd (hm.symm.trans h1) (by decide), fun h1 => ?_⟩
      have h2 := hns h1
      unfold cycleAfter
      rw [hp, if_pos rfl, inc_value, dec_value]
      linarith
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨hbl, hpo, hrem, -, hmis⟩ :=
      compare'_inv onLetter leftFirst centre place entry q first hC hm hcmp
    obtain ⟨hrad, hcyc, hs, hw⟩ := hmis hmt
    obtain ⟨w, hs0, ht⟩ : beginShiftVM' s' t := hb
    obtain ⟨w1, hw1, hz, hph, hbr, hif, -⟩ := hg
    rw [hw1] at hs0
    cases hs0
    rw [hw1] at hbl hs hw
    rw [hpo, hcyc] at hif
    -- the exit budget: `4h ≤ R₀ + 1` and `1 ≤ h`, from either half
    have hd : value w.machine.control.distance + value w.lag = value s.radius := hs hbr
    rw [value_zero_of_zero hz] at hd
    have hpl0 : periodLength w = w.machine.control.period.left.length +
        w.machine.control.period.right.length := rfl
    have hbud : 4 * (periodLength w : ℤ) ≤ value s.radius + 1 ∧ 1 ≤ periodLength w := by
      rcases hw w rfl hbr with ⟨-, hf⟩ | ⟨hpo', hh, -, hns⟩
      · have h4 := four_of_freshC hph hf
        have h1 := one_le_of_freshC hf
        rw [← hpl0] at h4 h1
        exact ⟨by linarith, h1⟩
      · rw [hpo', if_pos rfl] at hif
        have h1 := value_le_one_of_single hif
        have h2 := hns (by rw [hm]; decide)
        exact ⟨by linarith, hh⟩
    subst ht
    have hbw : OnBlock w.machine.control.period := hbl
    refine ⟨fun _ h2 => absurd rfl h2, onBlock_verifier_consume _ hbw, fun hnb => ?_,
      fun w' hw' hnb => ?_⟩
    · obtain ⟨hnb0, hd', -⟩ := consume_fresh w.machine.control _ hbw hnb
      have h0 := hs hnb0
      show value (GalilScaffoldChainVerifier.consume w.machine).control.distance +
        value w.lag = value s'.radius
      have hd'' : value (GalilScaffoldChainVerifier.consume w.machine).control.distance =
          value w.machine.control.distance + 1 := hd'
      rw [hrad, inc_value]; omega
    · cases hw'
      right
      have hpl := periodLength_consume w.machine w.lag w.margin w.lag (inc w.margin) hbw
      refine ⟨rfl, ?_, fun _ => ?_, fun h2 => absurd rfl h2⟩
      · show 1 ≤ periodLength ⟨GalilScaffoldChainVerifier.consume w.machine, w.lag,
          inc w.margin⟩
        rw [hpl]; exact hbud.2
      · show 5 * ((periodLength ⟨GalilScaffoldChainVerifier.consume w.machine, w.lag,
          inc w.margin⟩ : ℕ) : ℤ) ≤ value s'.radius + value reset +
            value (ofNat (periodLength w))
        rw [hpl, ofNat_value, hrad, inc_value]
        have : value reset = 0 := rfl
        have := hbud.1
        linarith
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨p, ht⟩ : beginFallbackVM' s' t := hb
    subst ht
    exact coupled'_of_idle rfl
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨-, -, -, w, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    have hws : s.chain = .watch w := hw
    have hbw : OnBlock w.machine.control.period := by
      have := hC.block; rw [hws] at this; exact this
    have hsw := hC.sum; rw [hws] at hsw
    have hww := hC.watch; rw [hws] at hww
    refine ⟨fun _ h2 => absurd hm h2, hbw, fun hnb => ?_, fun w' hw' hnb => ?_⟩
    · have h0 := hsw hnb
      show value (dec w.machine.control.distance) + value w.lag = value (dec s.radius)
      rw [dec_value, dec_value]; omega
    · cases hw'
      rcases hww w rfl hnb with ⟨hF, -⟩ | ⟨hpo, hh, hsh, -⟩
      · exact absurd hm hF
      · right
        refine ⟨hpo, hh, fun _ => ?_, fun h2 => absurd hm h2⟩
        have h2 := hsh hm
        show 5 * ((periodLength w : ℕ) : ℤ) ≤ value (dec s.radius) +
          value (inc (inc s.cycle)) + value (dec s.remaining)
        rw [dec_value, dec_value, inc_value, inc_value]; linarith
  case shift_done =>
    rename_i o hm hp ho
    have hpos : positive s.remaining = false := by
      cases h1 : positive s.remaining
      · rfl
      · exact absurd (Or.inl h1) hp
    have hr0 := value_nonpos_of_not_positive hpos
    refine ⟨fun h1 => absurd rfl h1, hC.block, hC.sum, ?_⟩
    intro w hw hnb
    rcases hC.watch w hw hnb with ⟨hF, -⟩ | ⟨hpo, hh, hsh, -⟩
    · exact absurd hm hF
    · right
      refine ⟨hpo, hh, fun h1 => absurd h1 (by simp), fun _ => ?_⟩
      have h2 := hsh hm
      linarith
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : replayStartVM entry s t := hi
    exact coupled'_of_idle hch
  all_goals
    first
    | (rename_i hm _ _ hi
       exact coupled'_of_idle ((congrArg GalilVM.chain hi.2).trans
        (hC.idleOut (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))))
    | (rename_i hm _ hi
       exact coupled'_of_idle ((congrArg GalilVM.chain hi.2).trans
        (hC.idleOut (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))))
    | (rename_i hm hi
       exact coupled'_of_idle ((congrArg GalilVM.chain hi.2).trans
        (hC.idleOut (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))))

theorem coupled'_steps {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hC : Coupled' x.ctl x.vm) : Coupled' y.ctl y.vm := by
  induction h with
  | zero => exact hC
  | succ ht _ ih => exact ih (coupled'_tick onLetter leftFirst centre place entry q first delay hC ht)

end Tick

/-! ## 4. `H_fourOther` for `Other'` -/

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`four_of_other'`**: at a guarded unmatched target in the `Other'` half,
`4h ≤ distance` (`5h ≤ R + C`, `C ≤ 1`, `distance = R`, `1 ≤ h`). -/
theorem four_of_other' {w : List (Fin 2)} {x : State GalilVM} {s'' : GalilVM}
    {wch : GalilScaffoldChainWatch.State} (hx : Coupled' x.ctl x.vm) (hs : ScanNR x)
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare x.vm s'')
    (hmt : ¬ (galilFrameS (PofC centre place entry w) q first).matched s'')
    (hg : shiftGuardVM s'') (hch : s''.chain = .watch wch)
    (hO : Other' x.vm.periodOnly x.ctl.mode (value x.vm.radius) (value x.vm.cycle)
      (value x.vm.remaining) (periodLength wch)) :
    4 * (periodLength wch : ℤ) ≤ value wch.machine.control.distance := by
  obtain ⟨-, hpo, -, -, hmis⟩ :=
    compare'_inv (onLetterVM w) leftFirstVM centre place entry q first hx hs.1 hcmp
  obtain ⟨-, hcyc, hsum, -⟩ := hmis hmt
  obtain ⟨hpo', hh, -, hns⟩ := hO
  have h3 : (1 : ℤ) ≤ periodLength wch := by exact_mod_cast hh
  have h2 := hns (by rw [hs.1]; decide)
  obtain ⟨w1, hw1, hz, -, hbr, hif, -⟩ := hg
  rw [hw1] at hch
  injection hch with hwe
  subst hwe
  rw [hw1] at hsum
  have hd := hsum hbr
  rw [value_zero_of_zero hz] at hd
  rw [hpo, hcyc] at hif
  rw [hpo', if_pos rfl] at hif
  have h1 := value_le_one_of_single hif
  linarith

/-! ## 5. `ChainPosInv'` -/

/-- **`ChainPosInv'`**: `CloseoutPackRun34.ChainPosInv` over `Coupled'`. -/
structure ChainPosInv' (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  coupled : Coupled' c s
  payload : ScanNR ⟨c, s⟩ → s.chain ≠ ChainVM.idle → PosPayload w s

theorem chainPosInv'_toChainPosInv {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : ChainPosInv' w c s) : ChainPosInv w c s :=
  ⟨coupled'_toCoupled h.coupled, h.payload⟩

/-- **`WatchShiftS` from `ChainPosInv'`** — `H_fourOther` is no longer needed. -/
theorem watchShiftS_of_chainPosInv' {w : List (Fin 2)} {x : State GalilVM}
    (h : ChainPosInv' w x.ctl x.vm) : WatchShiftS centre place entry q first w x := by
  intro hs hni s'' hcmp hmt hg wch hch
  have hs' : ScanNR ⟨x.ctl, x.vm⟩ := hs
  have P := h.payload hs' hni
  obtain ⟨a, ht⟩ := compareFound_chainTick q first hcmp hni
  have hver := P.verNext a s''.chain wch ht hch
  obtain ⟨-, -, -, -, hmis⟩ :=
    compare'_inv (onLetterVM w) leftFirstVM centre place entry q first h.coupled hs.1 hcmp
  obtain ⟨-, -, hsum, hwk⟩ := hmis hmt
  have hg' := hg
  obtain ⟨w1, hw1, hz, hph, hbr, -, -⟩ := hg'
  have hch' := hch
  rw [hw1] at hch'
  injection hch' with hwe
  rw [hwe] at hw1 hz hph hbr
  rw [hw1] at hsum hwk
  have hd : value wch.machine.control.distance + value wch.lag = value x.vm.radius := hsum hbr
  rw [value_zero_of_zero hz] at hd
  refine ⟨P.canR, ?_, ?_, hver⟩
  · rcases hwk wch rfl hbr with ⟨-, hf⟩ | hO
    · exact four_of_freshC hph hf
    · exact four_of_other' centre place entry q first h.coupled hs hcmp hmt hg hch hO
  · intro rad hsc
    have := P.radLe rad hsc
    omega

/-- **One tick of `ChainPosInv'`**: `Coupled'` by `coupled'_tick`, the payload
by `chainPosInv_tick` through `chainPosInv'_toChainPosInv`. -/
theorem chainPosInv'_tick {w : List (Fin 2)}
    (hbg : H_bgP centre place entry q first w) (hmatch : H_matchP centre place entry q first w)
    (hsd : H_shiftDoneP centre place entry q first w)
    {x y : State GalilVM} (hx : ChainPosInv' w x.ctl x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y) :
    ChainPosInv' w y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact ⟨coupled'_tick (onLetterVM w) leftFirstVM centre place entry q first 2048 hx.coupled h,
    (chainPosInv_tick centre place entry q first hbg hmatch hsd
      (chainPosInv'_toChainPosInv hx) h).payload⟩

end

#print axioms other_of_other'
#print axioms coupled'_toCoupled
#print axioms compare'_inv
#print axioms coupled'_tick
#print axioms coupled'_steps
#print axioms four_of_other'
#print axioms watchShiftS_of_chainPosInv'
#print axioms chainPosInv'_tick

end PalPeg.CloseoutPackRun40
