import PalPeg.CloseoutPackRun34

/-!
# `CloseoutPackRun38`: the three `PosPayload` landings of `ChainPosInv` and
the `Other`-half guard bound

`CloseoutPackRun34.chainPosInv_tick` names `H_bgP` (`scan_wait`/`scan_count`),
`H_matchP` (`scan_match`) and `H_shiftDoneP` (`shift_done`), and
`watchShiftS_of_chainPosInv` names `H_fourOther`.  This file discharges each
of the first three **modulo one named residual** and pins the fourth down to
the bound `Other` actually carries.

The residuals are exactly what `PosPayload` (Run34:313) does not carry at its
source, so that it is *not* inductive on its own:

* the verifier of a live watch is not known `Sane` (needed for `take`,
  `immediate`: `position (right v) = position v + 1` is false at an insane
  head, `GalilFrontMono.right_sane`);
* nothing is said about a `copy`/`back` chain (the `backDone` landing
  `ChainStep.backDone` creates a watch whose verifier/lag come from the
  `back` phase);
* `verNext` is a one-tick lookahead: to preserve it one needs two ticks;
* the payload is guarded by `ScanNR`, so it is empty at a `shift`-mode source
  (`shift_done`) and at a `replaying = true` source (`scan_match` with
  `replaying && b = false` through `b = false`);
* the moved right head's `canRight`, its `Sane`, and the radius ledger at the
  moved heads need the input representation (`ScanInvariant`), which the
  payload only consumes.

§1 `SrcPos` + `step_pos`/`matched_pos`: the chain-side position bookkeeping
through one `ChainStep` and one `ChainMatched`.
§2 `posPayload_background`: `H_bgP` from `H_bgRes` (closes `canR`, `radLe`,
`pos` — the `idle`/`take`/`backDone` shapes — leaving `SrcPos`, the chain-start
head facts and `verNext`).
§3 `posPayload_match`: `H_matchP` from `H_matchRes` (closes `pos` through
`ChainTick true` — `idle`/`take` then `queued`/`immediate`, the chain start
being a `copy`).
§4 `posPayload_shiftDone`: `H_shiftDoneP` from `H_shiftDoneRes`, which *is*
the payload at the shift-mode state: `ChainPosInv.payload` is vacuous there
(`chainPosInv_payload_vacuous_shift`).
§5 `other_guard_lower`: at a guarded unmatched target in the `Other` half,
`2h − 1 ≤ distance` — this is all `Other` gives (`2h ≤ R + C`, `C ≤ 1`,
`distance = R`), so `H_fourOther` is **not** a consequence of `WatchOK`.

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun38

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilChainCoupling
open PalPeg.CloseoutLPack5 PalPeg.CloseoutPackRun6 PalPeg.CloseoutPackRun10
open PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack4
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun32
open PalPeg.CloseoutPackRun34

/-! ## 1. Chain-side position bookkeeping -/

/-- The chain-side facts `PosPayload` lacks at its source: the live watch's
verifier is `Sane`, and a `back`-phase chain already sits `lag` cells behind
the right head with a sane verifier. -/
structure SrcPos (s : GalilVM) : Prop where
  saneVer : ∀ wch : GalilScaffoldChainWatch.State, s.chain = .watch wch →
    Sane wch.machine.verifier
  backPos : ∀ (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter) (ver : PlaceHead),
    s.chain = .back v h lag margin ver →
      Sane ver ∧ (position ver : ℤ) + value lag = position s.right

/-- One `ChainStep` keeps `position verifier + lag` (`take`: verifier `+1`,
lag `−1`; `backDone`: from the `back` payload). -/
theorem step_pos {x y : ChainVM} {R : ℕ}
    (hw : ∀ wch : GalilScaffoldChainWatch.State, x = .watch wch →
      Sane wch.machine.verifier ∧ (position wch.machine.verifier : ℤ) + value wch.lag = R)
    (hb : ∀ (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter) (ver : PlaceHead),
      x = .back v h lag margin ver → Sane ver ∧ (position ver : ℤ) + value lag = R)
    (hst : ChainStep x y) :
    ∀ wch : GalilScaffoldChainWatch.State, y = .watch wch →
      Sane wch.machine.verifier ∧ (position wch.machine.verifier : ℤ) + value wch.lag = R := by
  intro wch hy
  subst hy
  cases hst with
  | backDone v h lag margin ver hf => exact hb v h lag margin ver rfl
  | watchStep w w' hi =>
    obtain ⟨hsw, hpw⟩ := hw w rfl
    cases hi with
    | idle hz => exact ⟨hsw, hpw⟩
    | take hp hg =>
      have hr := right_sane hg.1 hsw
      refine ⟨hr.2, ?_⟩
      show (position (right w.machine.verifier) : ℤ) + value (dec w.lag) = R
      rw [hr.1, dec_value]
      push_cast
      omega

/-- One `ChainMatched` into a watch raises `position verifier + lag` by one
(`queued`: lag `+1`; `immediate`: verifier `+1`). -/
theorem matched_pos {y z : ChainVM} {R : ℕ}
    (hw : ∀ wch : GalilScaffoldChainWatch.State, y = .watch wch →
      Sane wch.machine.verifier ∧ (position wch.machine.verifier : ℤ) + value wch.lag = R)
    (hm : ChainMatched y z) :
    ∀ wch : GalilScaffoldChainWatch.State, z = .watch wch →
      Sane wch.machine.verifier ∧ (position wch.machine.verifier : ℤ) + value wch.lag = R + 1 := by
  intro wch hz
  subst hz
  cases hm with
  | watch w w' ho =>
    obtain ⟨hsw, hpw⟩ := hw w rfl
    cases ho with
    | queued hz =>
      refine ⟨hsw, ?_⟩
      show (position w.machine.verifier : ℤ) + value (inc w.lag) = R + 1
      rw [inc_value]
      omega
    | immediate hz hg =>
      have hr := right_sane hg.1 hsw
      refine ⟨hr.2, ?_⟩
      show (position (right w.machine.verifier) : ℤ) + value w.lag = R + 1
      rw [hr.1]
      push_cast
      omega

#print axioms step_pos
#print axioms matched_pos

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-! ## 2. `scan_wait` / `scan_count` -/

/-- **(NAMED residual of `H_bgP`.)**  What a `backgroundS` landing needs beyond
`ChainPosInv` at its source: `SrcPos`, the head facts at a chain start
(`s.chain = idle`, the source payload being empty), and the one-tick lookahead
`verNext` at the target. -/
structure BgRes (w : List (Fin 2)) (s t : GalilVM) : Prop where
  src : SrcPos s
  start : s.chain = ChainVM.idle →
    GalilScaffoldChainVerifier.canRight s.right ∧
      ∀ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right →
        value s.radius ≤ (rad : ℤ)
  verNext : ∀ (a : Bool) (z : ChainVM) (wch : GalilScaffoldChainWatch.State),
    ChainTick a t.chain z → z = .watch wch →
      GalilScaffoldChainVerifier.canRight wch.machine.verifier ∧
        Sane wch.machine.verifier

def H_bgRes (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s t : GalilVM), c.mode = Mode.scan → ChainPosInv w c s →
    (galilFrameS (PofC centre place entry w) q first).background s t →
    ScanNR ⟨c, t⟩ → t.chain ≠ ChainVM.idle → BgRes w s t

/-- **`H_bgP` modulo `H_bgRes`.** -/
theorem posPayload_background {w : List (Fin 2)} (hres : H_bgRes centre place entry q first w) :
    H_bgP centre place entry q first w := by
  intro c s t hm hx hb hs hni
  have R := hres c s t hm hx hb hs hni
  obtain ⟨hl, hr, -, hcen, -, hrad, -, -, -, -, -, -⟩ :=
    backgroundS_fields (PofC centre place entry w) q first hb
  by_cases hsi : s.chain = ChainVM.idle
  · obtain ⟨hcr, hrl⟩ := R.start hsi
    rcases backgroundS_idle (PofC centre place entry w) q first hb hsi with ⟨-, hti⟩ | ⟨-, hts⟩
    · exact absurd hti hni
    · refine ⟨by rw [hr]; exact hcr, ?_, ?_, R.verNext⟩
      · intro rad hsc
        rw [hcen, hl, hr] at hsc
        rw [hrad]
        exact hrl rad hsc
      · intro wch hw
        rw [hts] at hw
        exact absurd hw (by simp [chainStart])
  · have P := hx.payload ⟨hm, hs.2⟩ hsi
    obtain ⟨y, hst, hy⟩ := backgroundS_chainTick (PofC centre place entry w) q first hb hsi
    simp only [Bool.false_eq_true, ↓reduceIte] at hy
    refine ⟨by rw [hr]; exact P.canR, ?_, ?_, R.verNext⟩
    · intro rad hsc
      rw [hcen, hl, hr] at hsc
      rw [hrad]
      exact P.radLe rad hsc
    · intro wch hw
      rw [hy] at hw
      have := step_pos (R := position s.right)
        (fun w' hw' => ⟨R.src.saneVer w' hw', P.pos w' hw'⟩)
        (fun v h lag margin ver hb' => R.src.backPos v h lag margin ver hb') hst wch hw
      rw [hr]
      exact this.2

/-! ## 3. `scan_match` -/

/-- **(NAMED residual of `H_matchP`.)**  Beyond `ChainPosInv` at the source:
`SrcPos`; the source payload when the source is replaying (`ChainPosInv.payload`
is guarded by `ScanNR`, and the landing's `replaying && b = false` may come from
`b`); `Sane` of the source right head; `canRight` of the moved right head; the
radius ledger at the moved heads; and `verNext` at the target. -/
structure MatchRes (w : List (Fin 2)) (c : Control) (s t : GalilVM) : Prop where
  src : SrcPos s
  replayPay : c.replaying = true → s.chain ≠ ChainVM.idle → PosPayload w s
  saneR : Sane s.right
  canRNext : GalilScaffoldChainVerifier.canRight (right s.right)
  radNext : ∀ rad : ℕ,
    ScanInvariant w (position s.center) rad (GalilScaffoldInputHead.left s.left) (right s.right) →
      value s.radius + 1 ≤ (rad : ℤ)
  verNext : ∀ (a : Bool) (z : ChainVM) (wch : GalilScaffoldChainWatch.State),
    ChainTick a t.chain z → z = .watch wch →
      GalilScaffoldChainVerifier.canRight wch.machine.verifier ∧
        Sane wch.machine.verifier

def H_matchRes (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s s' t : GalilVM) (o b : Bool), c.mode = Mode.scan → ChainPosInv w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    (galilFrameS (PofC centre place entry w) q first).matched s' →
    (galilFrameS (PofC centre place entry w) q first).matchedPlace c.replaying s' t →
    ScanNR ⟨{c with clock := 2048, output := o, replaying := c.replaying && b}, t⟩ →
    t.chain ≠ ChainVM.idle → MatchRes w c s t

/-- **`H_matchP` modulo `H_matchRes`.** -/
theorem posPayload_match {w : List (Fin 2)} (hres : H_matchRes centre place entry q first w) :
    H_matchP centre place entry q first w := by
  intro c s s' t o b hm hx hcmp hmt hpl hs hni
  have R := hres c s s' t o b hm hx hcmp hmt hpl hs hni
  have hpl' : t = (if c.replaying then {s' with replay := dec s'.replay} else s') := hpl
  have hts : t.left = s'.left ∧ t.right = s'.right ∧ t.chain = s'.chain ∧
      t.center = s'.center ∧ t.radius = s'.radius := by
    rw [hpl']
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨vs, vq, a, hvl, hvr, hiff, -, hch, hteq⟩ :
    compareFound (PofC centre place entry w) q first s s' := hcmp
  have ha : a = true := by
    cases a with
    | true => rfl
    | false =>
      rw [if_neg (by simp)] at hteq
      subst hteq
      refine absurd (hiff.2 ?_) (by simp)
      have h0 : GalilScaffoldInputHead.read (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)).left
        = GalilScaffoldInputHead.read (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)).right := hmt
      rw [afterBirth_left, afterBirth_right] at h0
      exact h0
  subst ha
  rw [if_pos rfl] at hteq
  subst hteq
  obtain ⟨htl, htr, htc, htcen, htrad⟩ := hts
  have hsl : (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).left = vs.left := afterBirth_left _ _
  have hsr : (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).right = vs.right := afterBirth_right _ _
  have hsc : (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).chain = vs.chain := afterBirth_chain _ _
  have hscen : (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).center = s.center := afterBirth_center _ _
  have hsrad : (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).radius = inc s.radius :=
    afterBirth_radius _ _
  rw [hsl, hvl] at htl
  rw [hsr, hvr] at htr
  rw [hsc] at htc
  rw [hscen] at htcen
  rw [hsrad] at htrad
  -- the source payload, replaying or not
  have hP : s.chain ≠ ChainVM.idle → PosPayload w s := by
    intro hne
    cases hrep : c.replaying with
    | false => exact hx.payload ⟨hm, hrep⟩ hne
    | true => exact R.replayPay hrep hne
  refine ⟨by rw [htr]; exact R.canRNext, ?_, ?_, R.verNext⟩
  · intro rad hsc'
    rw [htcen, htl, htr] at hsc'
    rw [htrad, inc_value]
    exact R.radNext rad hsc'
  · intro wch hw
    rw [htc] at hw
    rw [htr]
    rcases hch with ⟨hne, ht⟩ | ⟨-, -, hz⟩ | ⟨-, -, hz⟩
    · have P := hP hne
      obtain ⟨y, hst, hmy⟩ := ht
      rw [if_pos rfl] at hmy
      have hy := step_pos (R := position s.right)
        (fun w' hw' => ⟨R.src.saneVer w' hw', P.pos w' hw'⟩)
        (fun v h lag margin ver hb' => R.src.backPos v h lag margin ver hb') hst
      have hz := matched_pos hy hmy wch hw
      rw [(right_sane P.canR R.saneR).1]
      push_cast
      omega
    · rw [hz] at hw
      cases hw
    · generalize hvc : vs.chain = z at hz hw
      unfold chainStart at hz
      cases hz
      cases hw

/-! ## 4. `shift_done` -/

/-- `ChainPosInv.payload` says nothing at a `shift`-mode state. -/
theorem chainPosInv_payload_vacuous_shift {c : Control} {s : GalilVM}
    (hm : c.mode = Mode.shift) : ¬ ScanNR ⟨c, s⟩ := by
  intro hs
  have := hs.1
  rw [hm] at this
  cases this

/-- **(NAMED residual of `H_shiftDoneP`.)**  The positional payload at the
shift-mode state itself.  Since `ChainPosInv.payload` is empty in `shift`
mode, this is the whole obligation: a shift-mode payload must be carried
through `shift_one` (`shiftTick` leaves the right head alone and moves
centre/left, `chainShiftOne` leaves the verifier and lag alone, so `pos` and
`canR` are step-invariant there; only `radLe` needs the centre move). -/
def H_shiftDoneRes (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s : GalilVM) (o : Bool), c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
    ChainPosInv w c s →
    ScanNR ⟨{c with mode := Mode.scan, output := o}, s⟩ → s.chain ≠ ChainVM.idle →
    PosPayload w s

/-- **`H_shiftDoneP` modulo `H_shiftDoneRes`** (which is `H_shiftDoneP` itself:
nothing in `ChainPosInv` reaches across `shift` mode). -/
theorem posPayload_shiftDone {w : List (Fin 2)}
    (hres : H_shiftDoneRes centre place entry q first w) :
    H_shiftDoneP centre place entry q first w := hres

/-! ## 5. The `Other` half at a guarded target -/

/-- **What `Other` gives at a guarded unmatched target**: `2h − 1 ≤ distance`
(`distance = R` from `SumRel` at lag `0`; `2h ≤ R + C` from `Other` in a
non-shift mode; `C ≤ 1` from the guard's `singlePositive cycle`).  This is
sharp for the *state* predicates: `R = 2h − 1`, `C = 1` satisfy `Other` and
the guard, so `H_fourOther` is not a consequence of `WatchOK`. -/
theorem other_guard_lower {w : List (Fin 2)} {x : State GalilVM} {s'' : GalilVM}
    {wch : GalilScaffoldChainWatch.State} (hx : Coupled x.ctl x.vm) (hs : ScanNR x)
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare x.vm s'')
    (hmt : ¬ (galilFrameS (PofC centre place entry w) q first).matched s'')
    (hg : shiftGuardVM s'') (hch : s''.chain = .watch wch)
    (hO : Other x.vm.periodOnly x.ctl.mode (value x.vm.radius) (value x.vm.cycle)
      (value x.vm.remaining) (periodLength wch)) :
    2 * (periodLength wch : ℤ) - 1 ≤ value wch.machine.control.distance := by
  have hne : x.vm.chain ≠ ChainVM.idle := by
    intro hidle
    obtain ⟨vs0, vq0, a0, -, -, -, -, hch0, hteq0⟩ :
      compareFound (PofC centre place entry w) q first x.vm s'' := hcmp
    rw [hidle] at hch0
    rw [hteq0, afterBirth_chain] at hch
    exact chainAt_idle_not_watch hch0 wch (by cases a0 <;> exact hch)
  obtain ⟨-, hpo, -, -, hmis⟩ :=
    compare_inv (onLetterVM w) leftFirstVM centre place entry q first hx hs.1 hcmp
  have hpo := hpo hne
  obtain ⟨-, hcyc, hsum, -⟩ := hmis hmt
  have hcyc := hcyc hne
  obtain ⟨w1, hw1, hz, -, hbr, hif, -⟩ := hg
  rw [hw1] at hch
  injection hch with hwe
  subst hwe
  rw [hw1] at hsum
  have hd := hsum hbr
  rw [value_zero_of_zero hz] at hd
  rw [hpo, hcyc] at hif
  obtain ⟨hpo', -, hns⟩ := hO
  rw [hpo', if_pos rfl] at hif
  have h1 := value_le_one_of_single hif
  have h2 := hns (by rw [hs.1]; decide)
  linarith

end

#print axioms posPayload_background
#print axioms posPayload_match
#print axioms chainPosInv_payload_vacuous_shift
#print axioms posPayload_shiftDone
#print axioms other_guard_lower

end PalPeg.CloseoutPackRun38
