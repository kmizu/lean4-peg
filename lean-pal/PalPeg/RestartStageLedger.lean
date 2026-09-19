import PalPeg.GalilChainCoupling
import PalPeg.GalilLastRadius

/-!
# The mark ledger of a watching chain, and the stage bound at a broken restart

`restartVM` installs `lower := last` of the broken chain, and the search stage that follows
needs `StageEntry Rad last` (`3 * Rad ≤ 5 * last`).  The chain side of that bound is a ledger of
the consume control: `distance` runs at most one semiperiod ahead of `boundary`, `boundary` is at
most one semiperiod ahead of `last`, and `boundary` is a multiple of the semiperiod once the unit
shifts still to run (`shiftDebt`) are discounted.
-/

set_option autoImplicit false

namespace PalPeg.RestartStageLedger

open GalilScaffoldCounter GalilBranchInvariants PalPeg.GalilChainCoupling

/-- The mark ledger of a consume control with semiperiod `h`.  `shiftDebt` is the number of
unit shifts of the current shift round still to run (`0` outside shift mode). -/
structure MarkLedger (h : ℕ) (shiftDebt : ℤ) (k : GalilScaffoldChainConsume.State) : Prop where
  size : k.period.left.length + k.period.right.length = h
  forward : k.forward = true → 1 ≤ k.period.left.length ∧
    value k.distance = value k.boundary + (k.period.left.length : ℤ) - 1
  backward : k.forward = false → k.period.left.length + 1 ≤ h ∧
    value k.distance = value k.boundary + (h : ℤ) - 1 - (k.period.left.length : ℤ)
  marks : (value k.boundary = value k.last ∧ value k.boundary ≤ 0) ∨
    value k.boundary = value k.last + (h : ℤ)
  aligned : ∃ n : ℤ, value k.boundary - shiftDebt = n * (h : ℤ)
  canonical : Canonical k.distance ∧ Canonical k.boundary ∧ Canonical k.last

/-- A successful consume keeps the mark ledger. -/
theorem MarkLedger.consume {h : ℕ} {shiftDebt : ℤ} {k : GalilScaffoldChainConsume.State}
    (hledger : MarkLedger h shiftDebt k) (seen : Option (Fin 3)) (hblock : OnBlock k.period)
    (hunbroken : (GalilScaffoldChainConsume.consume k seen).broken = false) :
    MarkLedger h shiftDebt (GalilScaffoldChainConsume.consume k seen) := by
  obtain ⟨hsize, hforward, hbackward, hmarks, ⟨n, hn⟩, hcd, hcb, hcl⟩ := hledger
  cases hf : k.period.focus with
  | blank =>
    rw [GalilShiftH.consume_of_none k seen (by rw [hf]; rfl)] at hunbroken; cases hunbroken
  | left =>
    rw [GalilShiftH.consume_of_none k seen (by rw [hf]; rfl)] at hunbroken; cases hunbroken
  | plain a =>
    by_cases hs : seen = some a
    · subst hs
      have hl := onBlock_left_ne hblock (by rw [hf]; rfl)
      have hr := onBlock_right_ne hblock (by rw [hf]; rfl)
      rw [GalilScaffoldChainConsume.plain k a hf]
      rcases k with ⟨⟨ls, f, rs⟩, d, bd, lst, ph, fw, br⟩
      simp only at hsize hforward hbackward hmarks hn hcd hcb hcl hl hr ⊢
      cases fw with
      | true =>
        obtain ⟨r0, rs', rfl⟩ := List.exists_cons_of_ne_nil hr
        obtain ⟨h1, h2⟩ := hforward rfl
        refine ⟨?_, fun _ => ?_, fun hc => absurd hc (by simp), hmarks, ⟨n, hn⟩,
          inc_canonical _ hcd, hcb, hcl⟩
        · simp only [GalilScaffoldChainPeriod.moveRight, ↓reduceIte, List.length_cons] at hsize ⊢
          omega
        · simp only [GalilScaffoldChainPeriod.moveRight, ↓reduceIte, List.length_cons, inc_value]
          push_cast
          exact ⟨trivial, by linarith⟩
      | false =>
        obtain ⟨l0, ls', rfl⟩ := List.exists_cons_of_ne_nil hl
        obtain ⟨h1, h2⟩ := hbackward rfl
        refine ⟨?_, fun hc => absurd hc (by simp), fun _ => ?_, hmarks, ⟨n, hn⟩,
          inc_canonical _ hcd, hcb, hcl⟩
        · simp only [GalilScaffoldChainPeriod.moveLeft, Bool.false_eq_true, ↓reduceIte,
            List.length_cons] at hsize ⊢
          omega
        · simp only [GalilScaffoldChainPeriod.moveLeft, Bool.false_eq_true, ↓reduceIte,
            List.length_cons, inc_value] at h1 h2 ⊢
          push_cast at h2 ⊢
          exact ⟨by first | trivial | omega, by linarith⟩
    · rw [GalilScaffoldChainConsume.mismatch k a seen (by rw [hf]; rfl) hs] at hunbroken
      cases hunbroken
  | first c =>
    by_cases hs : seen = some c
    · subst hs
      have hl := onBlock_first hblock hf
      have hr := onBlock_right_ne hblock (by rw [hf]; rfl)
      rw [GalilScaffoldChainConsume.first k c hf]
      rcases k with ⟨⟨ls, f, rs⟩, d, bd, lst, ph, fw, br⟩
      simp only at hsize hforward hbackward hmarks hn hcd hcb hcl hl hr ⊢
      subst hl
      obtain ⟨r0, rs', rfl⟩ := List.exists_cons_of_ne_nil hr
      cases fw with
      | true => exact absurd (hforward rfl).1 (by simp)
      | false =>
        obtain ⟨-, h2⟩ := hbackward rfl
        simp only [List.length_nil, Nat.cast_zero, sub_zero] at h2
        refine ⟨?_, fun _ => ?_, fun hc => absurd hc (by simp), Or.inr ?_, ⟨n + 1, ?_⟩,
          inc_canonical _ hcd, inc_canonical _ hcd, hcb⟩
        · simp only [GalilScaffoldChainPeriod.moveRight, List.length_cons, List.length_nil]
            at hsize ⊢
          omega
        · simp only [GalilScaffoldChainPeriod.moveRight, List.length_cons, List.length_nil,
            inc_value]
          push_cast
          exact ⟨trivial, by linarith⟩
        · rw [inc_value]; linarith
        · rw [inc_value]; linarith
    · rw [GalilScaffoldChainConsume.mismatch k c seen (by rw [hf]; rfl) hs] at hunbroken
      cases hunbroken
  | last b =>
    by_cases hs : seen = some b
    · subst hs
      have hl := onBlock_left_ne hblock (by rw [hf]; rfl)
      have hr := onBlock_last hblock hf
      rw [GalilScaffoldChainConsume.last k b hf]
      rcases k with ⟨⟨ls, f, rs⟩, d, bd, lst, ph, fw, br⟩
      simp only at hsize hforward hbackward hmarks hn hcd hcb hcl hl hr ⊢
      subst hr
      obtain ⟨l0, ls', rfl⟩ := List.exists_cons_of_ne_nil hl
      cases fw with
      | false =>
        have := (hbackward rfl).1
        simp only [List.length_cons, List.length_nil] at hsize this
        omega
      | true =>
        obtain ⟨-, h2⟩ := hforward rfl
        simp only [List.length_cons, List.length_nil, Nat.add_zero] at hsize h2
        refine ⟨?_, fun hc => absurd hc (by simp), fun _ => ?_, Or.inr ?_, ⟨n + 1, ?_⟩,
          inc_canonical _ hcd, inc_canonical _ hcd, hcb⟩
        · simp only [GalilScaffoldChainPeriod.moveLeft, List.length_cons, List.length_nil]
          omega
        · simp only [GalilScaffoldChainPeriod.moveLeft, inc_value]
          have hh : (h : ℤ) = (ls'.length : ℤ) + 1 := by exact_mod_cast hsize.symm
          exact ⟨by first | trivial | omega, by linarith⟩
        · rw [inc_value]
          have hh : (h : ℤ) = (ls'.length : ℤ) + 1 := by exact_mod_cast hsize.symm
          push_cast at h2
          linarith
        · rw [inc_value]
          have hh : (h : ℤ) = (ls'.length : ℤ) + 1 := by exact_mod_cast hsize.symm
          push_cast at h2
          linarith
    · rw [GalilScaffoldChainConsume.mismatch k b seen (by rw [hf]; rfl) hs] at hunbroken
      cases hunbroken

/-- A unit shift lowers the three sweep counters together with the shift debt. -/
theorem MarkLedger.shiftOne {h : ℕ} {shiftDebt : ℤ} {k : GalilScaffoldChainConsume.State}
    (hledger : MarkLedger h shiftDebt k) :
    MarkLedger h (shiftDebt - 1)
      { k with distance := dec k.distance, boundary := dec k.boundary, last := dec k.last } := by
  obtain ⟨hsize, hforward, hbackward, hmarks, ⟨n, hn⟩, hcd, hcb, hcl⟩ := hledger
  refine ⟨hsize, fun hfw => ?_, fun hfw => ?_, ?_, ⟨n, ?_⟩,
    dec_canonical _ hcd, dec_canonical _ hcb, dec_canonical _ hcl⟩
  · obtain ⟨h1, h2⟩ := hforward hfw
    exact ⟨h1, by simp only [dec_value]; linarith⟩
  · obtain ⟨h1, h2⟩ := hbackward hfw
    exact ⟨h1, by simp only [dec_value]; linarith⟩
  · simp only [dec_value]
    rcases hmarks with hm | hm
    · exact Or.inl ⟨by linarith [hm.1], by linarith [hm.2]⟩
    · exact Or.inr (by linarith)
  · simp only [dec_value]; linarith

/-- Entering a shift round of `h` unit shifts keeps the alignment. -/
theorem MarkLedger.beginShift {h : ℕ} {k : GalilScaffoldChainConsume.State}
    (hledger : MarkLedger h 0 k) : MarkLedger h (h : ℤ) k := by
  obtain ⟨hsize, hforward, hbackward, hmarks, ⟨n, hn⟩, hcanonical⟩ := hledger
  exact ⟨hsize, hforward, hbackward, hmarks, ⟨n - 1, by linear_combination hn⟩, hcanonical⟩

/-! ## The watching chain -/

open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply

/-- A canonical counter with a nonempty positive stack stays nonnegative after `dec`. -/
theorem canonical_dec_nonneg {x : Counter} (hcanonical : Canonical x)
    (hpositive : positive x = true) : Canonical (dec x) ∧ 0 ≤ value (dec x) := by
  refine ⟨dec_canonical _ hcanonical, ?_⟩
  have := (positive_iff x hcanonical).mp hpositive
  rw [dec_value]; omega

/-- The ledger of a watching chain: the mark ledger of its control, the credit balance
`distance + lag − margin = 4h`, and a canonical nonnegative lag. -/
structure WatchLedger (shiftDebt : ℤ) (w : GalilScaffoldChainWatch.State) : Prop where
  marks : MarkLedger (periodLength w) shiftDebt w.machine.control
  balance : GalilScaffoldChainWatch.balance w = 4 * (periodLength w : ℤ)
  lag : Canonical w.lag ∧ 0 ≤ value w.lag

theorem WatchLedger.consumed {shiftDebt : ℤ} {w : GalilScaffoldChainWatch.State}
    (hledger : WatchLedger shiftDebt w) (hblock : OnBlock w.machine.control.period)
    (lag' margin' : Counter)
    (hbalance : GalilScaffoldChainWatch.balance
      ⟨GalilScaffoldChainVerifier.consume w.machine, lag', margin'⟩
        = GalilScaffoldChainWatch.balance w)
    (hlag : Canonical lag' ∧ 0 ≤ value lag')
    (hunbroken : (GalilScaffoldChainVerifier.consume w.machine).control.broken = false) :
    WatchLedger shiftDebt ⟨GalilScaffoldChainVerifier.consume w.machine, lag', margin'⟩ := by
  have hlength := periodLength_consume w.machine w.lag w.margin lag' margin' hblock
  refine ⟨?_, ?_, hlag⟩
  · rw [hlength]
    exact hledger.marks.consume _ hblock hunbroken
  · rw [hlength, hbalance]
    exact hledger.balance

theorem WatchLedger.internal {shiftDebt : ℤ} {w w' : GalilScaffoldChainWatch.State}
    (hledger : WatchLedger shiftDebt w) (hinternal : GalilScaffoldChainWatch.Internal w w')
    (hblock : OnBlock w.machine.control.period)
    (hunbroken : w'.machine.control.broken = false) : WatchLedger shiftDebt w' := by
  cases hinternal with
  | idle => exact hledger
  | take hp hg =>
    exact hledger.consumed hblock _ _
      (GalilScaffoldChainWatch.internal_balance (.take w hp hg))
      (canonical_dec_nonneg hledger.lag.1 hp) hunbroken

theorem WatchLedger.outer {shiftDebt : ℤ} {w w' : GalilScaffoldChainWatch.State}
    (hledger : WatchLedger shiftDebt w) (houter : GalilScaffoldChainWatch.Outer w true w')
    (hblock : OnBlock w.machine.control.period)
    (hunbroken : w'.machine.control.broken = false) : WatchLedger shiftDebt w' := by
  cases houter with
  | queued hz =>
    refine ⟨hledger.marks,
      (GalilScaffoldChainWatch.outer_balance (.queued w hz)).trans hledger.balance,
      inc_canonical _ hledger.lag.1, ?_⟩
    show 0 ≤ value (inc w.lag)
    rw [inc_value]
    have := hledger.lag.2
    omega
  | immediate hz hg =>
    exact hledger.consumed hblock _ _
      (GalilScaffoldChainWatch.outer_balance (.immediate w hz hg)) hledger.lag hunbroken

theorem WatchLedger.shiftOne {shiftDebt : ℤ} {w : GalilScaffoldChainWatch.State}
    (hledger : WatchLedger shiftDebt w) : WatchLedger (shiftDebt - 1) (chainShiftOne w) := by
  refine ⟨hledger.marks.shiftOne, ?_, hledger.lag⟩
  have hbalance := hledger.balance
  simp only [GalilScaffoldChainWatch.balance] at hbalance
  show value (dec w.machine.control.distance) + value w.lag - value (dec w.margin)
    = 4 * (periodLength w : ℤ)
  simp only [dec_value]
  linarith

/-- The watch installed at the end of `back`. -/
theorem watchLedger_born {v : GalilScaffoldChainPeriod.Tape} {lag margin : Counter}
    {ver : GalilScaffoldInputHead.PlaceHead} (hblock : OnBlock v)
    (hfirst : GalilScaffoldChainPeriod.isFirst v.focus = true)
    (hbalance : value lag - value margin = 4 * ((GalilShiftH.cells v : ℤ) - 1))
    (hlag : Canonical lag ∧ 0 ≤ value lag) :
    WatchLedger 0 ⟨⟨ver, watchControl v⟩, lag, margin⟩ := by
  have hleft : v.left = [] := by
    cases hv : v.focus with
    | first c => exact onBlock_first hblock hv
    | _ => rw [hv] at hfirst; simp [GalilScaffoldChainPeriod.isFirst] at hfirst
  have hright : v.right ≠ [] := onBlock_right_ne hblock (by
    cases hv : v.focus with
    | first c => rfl
    | _ => rw [hv] at hfirst; simp [GalilScaffoldChainPeriod.isFirst] at hfirst)
  rcases v with ⟨ls, f, rs⟩
  simp only at hleft hright
  subst hleft
  obtain ⟨r0, rs', rfl⟩ := List.exists_cons_of_ne_nil hright
  have hreset : value reset = 0 := rfl
  refine ⟨⟨rfl, fun _ => ⟨by simp [watchControl, GalilScaffoldChainPeriod.moveRight], ?_⟩,
    fun hc => absurd hc (by simp [watchControl]), Or.inl ⟨rfl, le_of_eq hreset⟩, ⟨0, ?_⟩,
    Or.inl rfl, Or.inl rfl, Or.inl rfl⟩, ?_, hlag⟩
  · simp [watchControl, GalilScaffoldChainPeriod.moveRight, hreset]
  · simp [watchControl, hreset]
  · simp only [GalilScaffoldChainWatch.balance, watchControl, periodLength,
      GalilScaffoldChainPeriod.moveRight, GalilShiftH.cells, List.length_cons, List.length_nil,
      hreset] at hbalance ⊢
    push_cast at hbalance ⊢
    linarith

/-- `negative = false` means the negative stack is empty. -/
theorem value_nonneg_of_not_negative {x : Counter} (hnegative : negative x = false) :
    0 ≤ value x := by
  rcases x with ⟨pos, neg⟩
  simp only [negative, Bool.not_eq_false', List.isEmpty_iff] at hnegative
  simp [value, hnegative]

/-- **The stage bound at a lag-zero break.**  The failing consume leaves `distance` and `last`
untouched and raises `margin` by one, so a nonnegative margin after the break gives
`4h − 1 ≤ distance`.  Off the boundary case `distance = 4h − 1` the aligned marks give
`3h ≤ last` and `distance + 1 ≤ last + 2h`. -/
theorem WatchLedger.stageEntry_of_break {w w' : GalilScaffoldChainWatch.State}
    (hledger : WatchLedger 0 w) (hbreak : BreakStep w w')
    (hmargin : negative w'.margin = false)
    (hinterior : value w.machine.control.distance ≠ 4 * (periodLength w : ℤ) - 1)
    {Rad : ℕ} (hRad : (Rad : ℤ) = value w.machine.control.distance + 1) :
    PalPeg.GalilScaffoldChainInputSupply.StageEntry Rad w'.machine.control.last ∧
      Canonical w'.machine.control.last ∧ w'.lag = w.lag := by
  obtain ⟨hzero, -, a, hsymbol, hread, rfl⟩ := hbreak
  have hcontrol : (GalilScaffoldChainVerifier.consume w.machine).control
      = {w.machine.control with broken := true} :=
    GalilScaffoldChainConsume.mismatch w.machine.control a _ hsymbol hread
  have hlast : (GalilScaffoldChainVerifier.consume w.machine).control.last
      = w.machine.control.last := by rw [hcontrol]
  have hmarginValue := value_nonneg_of_not_negative hmargin
  have hbalance := hledger.balance
  simp only [GalilScaffoldChainWatch.balance] at hbalance
  have hlagZero := value_zero_of_zero hzero
  change 0 ≤ value (inc w.margin) at hmarginValue
  rw [inc_value] at hmarginValue
  obtain ⟨hsize, hforward, hbackward, hmarks, ⟨n, hn⟩, -, -, hcanonicalLast⟩ := hledger.marks
  have hh0 : (0 : ℤ) ≤ (periodLength w : ℤ) := by positivity
  have hleft : (w.machine.control.period.left.length : ℤ) ≤ (periodLength w : ℤ) := by
    have : w.machine.control.period.left.length ≤ periodLength w := by omega
    exact_mod_cast this
  have hboundaryLow : value w.machine.control.distance - (periodLength w : ℤ) + 1
      ≤ value w.machine.control.boundary := by
    cases hfw : w.machine.control.forward with
    | true => obtain ⟨-, h2⟩ := hforward hfw; linarith
    | false =>
      obtain ⟨-, h2⟩ := hbackward hfw
      have : (0 : ℤ) ≤ (w.machine.control.period.left.length : ℤ) := by positivity
      linarith
  have hboundaryHigh : value w.machine.control.distance + 1
      ≤ value w.machine.control.boundary + (periodLength w : ℤ) := by
    cases hfw : w.machine.control.forward with
    | true => obtain ⟨-, h2⟩ := hforward hfw; linarith
    | false =>
      obtain ⟨h1, h2⟩ := hbackward hfw
      have : (0 : ℤ) ≤ (w.machine.control.period.left.length : ℤ) := by positivity
      linarith
  have hfour : 4 * (periodLength w : ℤ) ≤ value w.machine.control.distance := by
    have h1 : 4 * (periodLength w : ℤ) - 1 ≤ value w.machine.control.distance := by linarith
    omega
  have haligned : 4 * (periodLength w : ℤ) ≤ value w.machine.control.boundary := by
    rw [sub_zero] at hn
    by_contra hnot
    have hlt := not_le.mp hnot
    have hn3 : n ≤ 3 := by
      by_contra hnot4
      have h4 := not_le.mp hnot4
      have : 4 * (periodLength w : ℤ) ≤ n * (periodLength w : ℤ) :=
        mul_le_mul_of_nonneg_right (by omega) hh0
      linarith
    have : n * (periodLength w : ℤ) ≤ 3 * (periodLength w : ℤ) :=
      mul_le_mul_of_nonneg_right hn3 hh0
    linarith
  refine ⟨?_, by rw [hlast]; exact hcanonicalLast, rfl⟩
  rw [hlast]
  apply PalPeg.GalilLastRadius.stageEntry_of_gap Rad (periodLength w)
  · rcases hmarks with hm | hm
    · linarith [hm.1]
    · linarith
  · rcases hmarks with hm | hm
    · linarith [hm.1]
    · linarith

/-- Once four semiperiods are consumed, `last` trails `distance` by at least one and at most two
semiperiods.  (The inputs of `LowerExcludedAtBreak.lowerExcluded_of_break`.) -/
theorem WatchLedger.last_bounds {shiftDebt : ℤ} {w : GalilScaffoldChainWatch.State}
    (hledger : WatchLedger shiftDebt w)
    (hfour : 4 * (periodLength w : ℤ) ≤ value w.machine.control.distance) :
    value w.machine.control.last + (periodLength w : ℤ) ≤ value w.machine.control.distance ∧
      value w.machine.control.distance + 1 ≤ 4 * (value w.machine.control.last + 1) := by
  obtain ⟨hsize, hforward, hbackward, hmarks, -, -⟩ := hledger.marks
  have hleft : (w.machine.control.period.left.length : ℤ) ≤ (periodLength w : ℤ) := by
    have : w.machine.control.period.left.length ≤ periodLength w := by omega
    exact_mod_cast this
  have hleft0 : (0 : ℤ) ≤ (w.machine.control.period.left.length : ℤ) := by positivity
  have hbounds : value w.machine.control.boundary ≤ value w.machine.control.distance ∧
      value w.machine.control.distance + 1
        ≤ value w.machine.control.boundary + (periodLength w : ℤ) ∧
      (1 : ℤ) ≤ (periodLength w : ℤ) := by
    cases hfw : w.machine.control.forward with
    | true =>
      obtain ⟨h1, h2⟩ := hforward hfw
      have h1' : (1 : ℤ) ≤ (w.machine.control.period.left.length : ℤ) := by exact_mod_cast h1
      exact ⟨by linarith, by linarith, by linarith⟩
    | false =>
      obtain ⟨h1, h2⟩ := hbackward hfw
      have h1' : (w.machine.control.period.left.length : ℤ) + 1 ≤ (periodLength w : ℤ) := by
        exact_mod_cast h1
      exact ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨hb1, hb2, hh1⟩ := hbounds
  rcases hmarks with hm | hm
  · exfalso
    linarith [hm.2]
  · exact ⟨by linarith, by linarith⟩

/-! ## The chain -/

/-- The ledger of a live chain.  Copy and back phases carry the credit balance against the cells
copied so far; an unbroken watch carries `WatchLedger`. -/
def ChainLedger (shiftDebt : ℤ) : ChainVM → Prop
  | .copy _ _ _ v lag margin _ =>
      value lag - value margin = 4 * ((GalilShiftH.cells v : ℤ) - 1) ∧
        Canonical lag ∧ 0 ≤ value lag
  | .back v _ lag margin _ =>
      value lag - value margin = 4 * ((GalilShiftH.cells v : ℤ) - 1) ∧
        Canonical lag ∧ 0 ≤ value lag
  | .watch w => w.machine.control.broken = false → WatchLedger shiftDebt w
  | _ => True

theorem chainLedger_step {x y : ChainVM} (hstep : ChainStep x y) (hblock : BlockInv x)
    (hledger : ChainLedger 0 x) : ChainLedger 0 y := by
  cases hstep with
  | idle => exact hledger
  | brokenIdle => trivial
  | watchBreak => trivial
  | copyBit t h p v lag margin ver a one legal present =>
    obtain ⟨hbalance, hlag⟩ := hledger
    refine ⟨?_, hlag⟩
    rw [GalilShiftH.cells_put v a hblock.1]
    simp only [GalilScaffoldChainCredits.decFour, dec_value]
    push_cast
    linarith
  | copyEnd => exact hledger
  | backStep v h lag margin ver hf =>
    obtain ⟨hbalance, hlag⟩ := hledger
    exact ⟨by rw [GalilShiftH.cells_moveLeft]; exact hbalance, hlag⟩
  | backDone v h lag margin ver hf =>
    obtain ⟨hbalance, hlag⟩ := hledger
    exact fun _ => watchLedger_born hblock hf hbalance hlag
  | watchStep w w' hinternal =>
    intro hunbroken
    have hbw : OnBlock w.machine.control.period := hblock
    have hunbroken0 : w.machine.control.broken = false := by
      cases hinternal with
      | idle => exact hunbroken
      | take hp hg => exact (consume_fresh w.machine.control _ hbw hunbroken).1
    exact (hledger hunbroken0).internal hinternal hbw hunbroken

theorem chainLedger_matched {y z : ChainVM} (hmatched : ChainMatched y z) (hblock : BlockInv y)
    (hledger : ChainLedger 0 y) : ChainLedger 0 z := by
  cases hmatched with
  | idle => trivial
  | copy =>
    obtain ⟨hbalance, hcanonical, hnonneg⟩ := hledger
    refine ⟨?_, inc_canonical _ hcanonical, ?_⟩
    · simp only [inc_value]; linarith
    · rw [inc_value]; omega
  | back =>
    obtain ⟨hbalance, hcanonical, hnonneg⟩ := hledger
    refine ⟨?_, inc_canonical _ hcanonical, ?_⟩
    · simp only [inc_value]; linarith
    · rw [inc_value]; omega
  | breaks => trivial
  | brokenMatched => trivial
  | watch w w' houter =>
    intro hunbroken
    have hbw : OnBlock w.machine.control.period := hblock
    have hunbroken0 : w.machine.control.broken = false := by
      cases houter with
      | queued hz => exact hunbroken
      | immediate hz hg => exact (consume_fresh w.machine.control _ hbw hunbroken).1
    exact (hledger hunbroken0).outer houter hbw hunbroken

theorem chainLedger_chainStart (answer : GalilScaffoldTape.Tape) (c : Fin 3)
    (walker : GalilScaffoldPlace.Place) (ver : GalilScaffoldInputHead.PlaceHead)
    {radius : Counter} (hradius : Canonical radius ∧ 0 ≤ value radius) :
    ChainLedger 0 (chainStart answer c walker ver radius) := by
  refine ⟨?_, hradius⟩
  rw [GalilShiftH.cells_start]
  simp

/-- One chain tick of a comparison or of the background, including a birth. -/
theorem chainLedger_chainAt {matchedBit found : Bool} {answer : GalilScaffoldTape.Tape}
    {c : Fin 3} {walker : GalilScaffoldPlace.Place} {ver : GalilScaffoldInputHead.PlaceHead}
    {radius : Counter} {x z : ChainVM}
    (hchainAt : chainAt matchedBit found answer c walker ver radius x z)
    (hradius : Canonical radius ∧ 0 ≤ value radius)
    (hblock : BlockInv x) (hledger : ChainLedger 0 x) : ChainLedger 0 z := by
  rcases hchainAt with ⟨-, y, hstep, hzy⟩ | ⟨-, -, rfl⟩ | ⟨-, -, hz⟩
  · have hy := chainLedger_step hstep hblock hledger
    cases matchedBit with
    | true =>
      rw [if_pos rfl] at hzy
      exact chainLedger_matched hzy (blockInv_step hstep hblock) hy
    | false =>
      rw [if_neg (by simp)] at hzy
      subst hzy
      exact hy
  · trivial
  · have hstart := chainLedger_chainStart answer c walker ver hradius
    cases matchedBit with
    | true =>
      rw [if_pos rfl] at hz
      exact chainLedger_matched hz (blockInv_chainStart answer c walker ver radius) hstart
    | false =>
      rw [if_neg (by simp)] at hz
      subst hz
      exact hstart

end PalPeg.RestartStageLedger
