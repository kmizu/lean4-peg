import PalPeg.RestartStageRun
import PalPeg.CanonicalChainMinimal

/-!
# The clock of a chain before it has caught up

A chain is born within two semiperiods of the centre and then copies its period, walks back and
catches up with the scan.  Each scan tick is one chain step, a match comes once in `2048` ticks,
so the radius cannot reach four semiperiods before the chain has caught up.  This file is the
chain-level half: the remaining work of a chain and its semiperiod, as functions of the chain
state, and how one chain step and one matched event change them.
-/

set_option autoImplicit false

namespace PalPeg.ChainClock

open PalPeg GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply GalilBranchInvariants
open GalilScaffoldTop PalPeg.GalilChainCoupling PalPeg.GalilShiftH

/-- The unary answer still to be copied: the run of `8`s from the focus leftwards. -/
def remainingBits (t : GalilScaffoldTape.Tape) : ℕ :=
  ((t.focus :: t.left).takeWhile (fun x => decide (x = 8))).length

theorem remainingBits_of_left {t : GalilScaffoldTape.Tape} (hleft : t.focus = 4) :
    remainingBits t = 0 := by
  unfold remainingBits
  rw [hleft]
  simp [List.takeWhile]

theorem remainingBits_moveLeft {t : GalilScaffoldTape.Tape} (hone : t.focus = 8)
    (hlegal : t.left ≠ []) :
    remainingBits (GalilScaffoldTape.moveLeft t) + 1 = remainingBits t := by
  obtain ⟨a, ls, hls⟩ := List.exists_cons_of_ne_nil hlegal
  unfold remainingBits GalilScaffoldTape.moveLeft
  rw [hls, hone]
  simp [List.takeWhile]

/-- The semiperiod of a chain: the cells of its period tape, plus what is still to be copied. -/
def chainPeriod : ChainVM → ℤ
  | .copy t _ _ v _ _ _ => (cells v : ℤ) + (remainingBits t : ℤ) - 1
  | x => (cellsOf x : ℤ) - 1

/-- The chain steps left before the chain has caught up with the scan. -/
def chainWork : ChainVM → ℤ
  | .copy t _ _ v lag _ _ =>
      (remainingBits t : ℤ) + 1 + ((cells v : ℤ) + (remainingBits t : ℤ) - 1) + 1 + value lag
  | .back v _ lag _ _ => (v.left.length : ℤ) + 1 + value lag
  | .watch w => value w.lag
  | _ => 0

/-- One chain step does one unit of the remaining work and keeps the semiperiod. -/
theorem chainWork_step {x y : ChainVM} (hstep : ChainStep x y) (hblock : BlockInv x)
    (hlag : ∀ w, x = .watch w → Canonical w.lag) (hwork : 0 < chainWork x) :
    chainWork y ≤ chainWork x - 1 ∧ (0 < chainWork y → chainPeriod y = chainPeriod x) := by
  cases hstep with
  | idle => simp [chainWork] at hwork
  | brokenIdle => simp [chainWork] at hwork
  | copyBit t h p v lag margin ver a one legal present =>
    have hbits := remainingBits_moveLeft one legal
    have hcells := cells_put v a hblock.1
    simp only [chainWork, chainPeriod]
    rw [hcells]
    push_cast
    constructor
    · omega
    · intro _; omega
  | copyEnd t h p v lag margin ver b hleft hp hv =>
    have hbits := remainingBits_of_left hleft
    have hright : v.right = [] := hblock.1
    have hcells : cells (GalilScaffoldChainPeriod.write v (.last b)) = cells v := cells_write _ _
    have hleftLength : (GalilScaffoldChainPeriod.write v (.last b)).left.length = v.left.length :=
      rfl
    simp only [chainWork, chainPeriod, cellsOf]
    rw [hbits, hcells, hleftLength]
    unfold cells
    rw [hright]
    simp only [List.length_nil]
    push_cast
    constructor
    · omega
    · intro _; omega
  | backStep v h lag margin ver hf =>
    have hne := onBlock_left_ne hblock hf
    obtain ⟨l0, ls, hls⟩ := List.exists_cons_of_ne_nil hne
    have hcells := cells_moveLeft v
    have hleftLength : (GalilScaffoldChainPeriod.moveLeft v).left.length + 1 = v.left.length := by
      rcases v with ⟨left, f, right⟩
      simp only at hls
      subst hls
      simp [GalilScaffoldChainPeriod.moveLeft]
    simp only [chainWork, chainPeriod, cellsOf]
    rw [hcells]
    constructor
    · omega
    · intro _; trivial
  | backDone v h lag margin ver hf =>
    have hleft : v.left = [] := by
      cases hv : v.focus with
      | first c => exact onBlock_first hblock hv
      | _ => rw [hv] at hf; simp [GalilScaffoldChainPeriod.isFirst] at hf
    have hright : v.right ≠ [] := onBlock_right_ne hblock (by
      cases hv : v.focus with
      | first c => rfl
      | _ => rw [hv] at hf; simp [GalilScaffoldChainPeriod.isFirst] at hf)
    have hcells : cells (watchControl v).period = cells v := cells_moveRight v hright
    simp only [chainWork, chainPeriod, cellsOf]
    rw [hleft, hcells]
    simp only [List.length_nil]
    push_cast
    constructor
    · omega
    · intro _; trivial
  | watchStep w w' hinternal =>
    have hbw : OnBlock w.machine.control.period := hblock
    cases hinternal with
    | idle hz =>
      exfalso
      have hcanonical := hlag w rfl
      have hvalue : ¬ 0 < value w.lag := fun hpos =>
        absurd ((positive_iff _ hcanonical).mpr hpos) (by rw [hz]; simp)
      exact hvalue hwork
    | take hp hg =>
      have hcells : cells (GalilScaffoldChainVerifier.consume w.machine).control.period
          = cells w.machine.control.period := cells_verifier_consume w.machine hbw
      simp only [chainWork, chainPeriod, cellsOf, GalilScaffoldChainWatch.caught, dec_value]
      rw [hcells]
      constructor
      · omega
      · intro _; trivial
  | watchBreak w hb =>
    simp only [chainWork]
    have : (0 : ℤ) < value w.lag := hwork
    constructor
    · omega
    · intro h; exact absurd h (lt_irrefl _)

/-- A matched event queues one more unit of work at most and keeps the semiperiod. -/
theorem chainWork_matched {y z : ChainVM} (hmatched : ChainMatched y z) :
    chainWork z ≤ chainWork y + 1 ∧ (0 < chainWork z → chainPeriod z = chainPeriod y) := by
  cases hmatched with
  | idle => simp [chainWork]
  | copy t h p v lag margin ver =>
    simp only [chainWork, chainPeriod, inc_value]
    exact ⟨by omega, fun _ => trivial⟩
  | back v h lag margin ver =>
    simp only [chainWork, chainPeriod, inc_value]
    exact ⟨by omega, fun _ => rfl⟩
  | watch w w' houter =>
    cases houter with
    | queued hz =>
      simp only [chainWork, chainPeriod, cellsOf, GalilScaffoldChainWatch.queued, inc_value]
      exact ⟨by omega, fun _ => trivial⟩
    | immediate hz hg =>
      have hzero : value w.lag = 0 := value_zero_of_zero hz
      simp only [chainWork, GalilScaffoldChainWatch.immediate]
      rw [hzero]
      exact ⟨by omega, fun h => absurd h (lt_irrefl _)⟩
  | breaks w w' hb =>
    simp only [chainWork]
    have hzero : value w.lag = 0 := value_zero_of_zero hb.1
    rw [hzero]
    exact ⟨by omega, fun h => absurd h (lt_irrefl _)⟩
  | brokenMatched w => simp [chainWork]

/-- A chain with no work left has none after a step either. -/
theorem chainWork_step_done {x y : ChainVM} (hstep : ChainStep x y)
    (hlag : ∀ w, x = .watch w → Canonical w.lag ∧ 0 ≤ value w.lag)
    (hpre : ∀ t h p v lag margin ver, x = .copy t h p v lag margin ver → 0 ≤ value lag)
    (hback : ∀ v h lag margin ver, x = .back v h lag margin ver → 0 ≤ value lag)
    (hdone : chainWork x ≤ 0) : chainWork y ≤ 0 := by
  cases hstep with
  | idle => simp [chainWork]
  | brokenIdle => simp [chainWork]
  | copyBit t h p v lag margin ver a one legal present =>
    exfalso
    have := hpre _ _ _ _ _ _ _ rfl
    simp only [chainWork] at hdone
    have hcells : 1 ≤ cells v := by unfold cells; omega
    omega
  | copyEnd t h p v lag margin ver b hleft hp hv =>
    exfalso
    have := hpre _ _ _ _ _ _ _ rfl
    simp only [chainWork] at hdone
    have hcells : 1 ≤ cells v := by unfold cells; omega
    omega
  | backStep v h lag margin ver hf =>
    exfalso
    have := hback _ _ _ _ _ rfl
    simp only [chainWork] at hdone
    omega
  | backDone v h lag margin ver hf =>
    exfalso
    have := hback _ _ _ _ _ rfl
    simp only [chainWork] at hdone
    omega
  | watchStep w w' hinternal =>
    obtain ⟨hcanonical, hnonneg⟩ := hlag w rfl
    cases hinternal with
    | idle hz => exact hdone
    | take hp hg =>
      exfalso
      have hpos := (positive_iff _ hcanonical).mp hp
      simp only [chainWork] at hdone
      omega
  | watchBreak w hb =>
    simp [chainWork]

/-- The unary answer ahead of the focus is the number of bits still to copy. -/
theorem remainingBits_of_answerAhead {t : GalilScaffoldTape.Tape} {n : ℕ}
    (hahead : AnswerAhead t n) : remainingBits t = n := by
  obtain ⟨ls, hlist⟩ := hahead
  unfold remainingBits
  rw [hlist]
  clear hlist
  induction n with
  | zero => simp [List.takeWhile]
  | succ n ih => simpa [List.replicate_succ, List.takeWhile] using ih

/-- A newborn chain: the whole answer is still to be copied, and the lag is the radius. -/
theorem chainWork_chainStart (answer : GalilScaffoldTape.Tape) (c : Fin 3)
    (walker : GalilScaffoldPlace.Place) (ver : PlaceHead) (radius : Counter) :
    chainWork (chainStart answer c walker ver radius)
        = 2 * (remainingBits answer : ℤ) + 2 + value radius ∧
      chainPeriod (chainStart answer c walker ver radius) = (remainingBits answer : ℤ) := by
  simp only [chainStart, chainWork, chainPeriod, cells_start]
  push_cast
  constructor <;> ring

/-- The semiperiod the payload of a live chain speaks about is `chainPeriod`. -/
theorem period_of_semWith {Cert : ℕ → Prop} {x : ChainVM}
    (hsem : PalPeg.CanonicalChainMinimal.SemWith Cert x) (hne : x ≠ .idle) :
    ∃ H : ℕ, (H : ℤ) = chainPeriod x ∧ Cert H := by
  cases x with
  | idle => exact absurd rfl hne
  | copy t h p v lag margin ver =>
    obtain ⟨H, n, hcopy, hcells, hcert⟩ := hsem
    refine ⟨H, ?_, hcert⟩
    have hbits := remainingBits_of_answerAhead hcopy.1
    simp only [chainPeriod]
    rw [hbits]
    have : (cells v : ℤ) + (n : ℤ) = (H : ℤ) + 1 := by exact_mod_cast hcells
    omega
  | back v h lag margin ver =>
    obtain ⟨-, H, -, hcells, hcert⟩ := hsem
    refine ⟨H, ?_, hcert⟩
    simp only [chainPeriod]
    have : (cellsOf (.back v h lag margin ver) : ℤ) = (H : ℤ) + 1 := by exact_mod_cast hcells
    omega
  | watch w =>
    obtain ⟨-, H, -, hcells, hcert⟩ := hsem
    refine ⟨H, ?_, hcert⟩
    simp only [chainPeriod]
    have : (cellsOf (.watch w) : ℤ) = (H : ℤ) + 1 := by exact_mod_cast hcells
    omega
  | broken w =>
    obtain ⟨-, H, -, hcells, hcert⟩ := hsem
    refine ⟨H, ?_, hcert⟩
    simp only [chainPeriod]
    have : (cellsOf (.broken w) : ℤ) = (H : ℤ) + 1 := by exact_mod_cast hcells
    omega

/-- A chain with no work left has none after a matched event either. -/
theorem chainWork_matched_done {y z : ChainVM} (hmatched : ChainMatched y z)
    (hlag : ∀ w, y = .watch w → Canonical w.lag ∧ 0 ≤ value w.lag)
    (hpre : ∀ t h p v lag margin ver, y = .copy t h p v lag margin ver → 0 ≤ value lag)
    (hback : ∀ v h lag margin ver, y = .back v h lag margin ver → 0 ≤ value lag)
    (hdone : chainWork y ≤ 0) : chainWork z ≤ 0 := by
  cases hmatched with
  | idle => simp [chainWork]
  | copy t h p v lag margin ver =>
    exfalso
    have := hpre _ _ _ _ _ _ _ rfl
    simp only [chainWork] at hdone
    have hcells : 1 ≤ cells v := by unfold cells; omega
    omega
  | back v h lag margin ver =>
    exfalso
    have := hback _ _ _ _ _ rfl
    simp only [chainWork] at hdone
    omega
  | watch w w' houter =>
    obtain ⟨hcanonical, hnonneg⟩ := hlag w rfl
    simp only [chainWork] at hdone
    have hzeroValue : value w.lag = 0 := by omega
    cases houter with
    | queued hz =>
      exfalso
      have := (zero_iff _ hcanonical).mpr hzeroValue
      rw [hz] at this
      cases this
    | immediate hz hg =>
      simp only [chainWork, GalilScaffoldChainWatch.immediate]
      omega
  | breaks w w' hb => simp [chainWork]
  | brokenMatched w => simp [chainWork]

/-- The lag facts of a chain state, from its ledger. -/
theorem lagFacts_of_ledger {x : ChainVM} (hledger : PalPeg.RestartStageLedger.ChainLedger 0 x)
    (hunbroken : ∀ w, x = .watch w → w.machine.control.broken = false) :
    (∀ w, x = .watch w → Canonical w.lag ∧ 0 ≤ value w.lag) ∧
    (∀ t h p v lag margin ver, x = .copy t h p v lag margin ver → 0 ≤ value lag) ∧
    (∀ v h lag margin ver, x = .back v h lag margin ver → 0 ≤ value lag) := by
  refine ⟨fun w hw => ?_, fun t h p v lag margin ver hx => ?_, fun v h lag margin ver hx => ?_⟩
  · subst hw
    exact (hledger (hunbroken _ rfl)).lag
  · subst hx
    exact hledger.2.2.2
  · subst hx
    exact hledger.2.2.2

/-- **One chain tick keeps the clock inequality.**  `E` is the time since the last match,
`R` the radius; a tick without a match costs one unit of time and does one unit of work, a match
resets the time and raises the radius by one, and a birth starts within two semiperiods. -/
theorem clock_chainAt {a found : Bool} {answer : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter} {x z : ChainVM}
    {E E' R R' : ℤ}
    (hchainAt : chainAt a found answer cc walker ver radius x z)
    (hblock : BlockInv x) (hledger : PalPeg.RestartStageLedger.ChainLedger 0 x)
    (hunbroken : ∀ w, x = .watch w → w.machine.control.broken = false)
    (hradiusValue : value radius = R)
    (hsource : 0 < chainWork x → chainWork x + E ≤ 2047 * (4 * chainPeriod x - R))
    (hbirth : x = .idle → found = true →
      1 ≤ remainingBits answer ∧ R ≤ 2 * (remainingBits answer : ℤ))
    (htime : if a then E' + 2047 ≤ E else E' ≤ E + 1)
    (htimeBounds : 0 ≤ E' ∧ E' ≤ 2047 ∧ E ≤ 2047)
    (hradius : R' = R + if a then 1 else 0) :
    0 < chainWork z → chainWork z + E' ≤ 2047 * (4 * chainPeriod z - R') := by
  intro hworkZ
  rcases hchainAt with ⟨-, y, hstep, hzy⟩ | ⟨-, -, hz⟩ | ⟨hidle, hfound, hz⟩
  · obtain ⟨hlagX, hpreX, hbackX⟩ := lagFacts_of_ledger hledger hunbroken
    have hledgerY := PalPeg.RestartStageLedger.chainLedger_step hstep hblock hledger
    have hunbrokenY : ∀ w, y = .watch w → w.machine.control.broken = false := by
      intro w hw
      subst hw
      exact PalPeg.RestartStageRun.unbroken_of_step hstep hunbroken
    obtain ⟨hlagY, hpreY, hbackY⟩ := lagFacts_of_ledger hledgerY hunbrokenY
    by_cases hworkX : 0 < chainWork x
    · obtain ⟨hstepWork, hstepPeriod⟩ :=
        chainWork_step hstep hblock (fun w hw => (hlagX w hw).1) hworkX
      have hclock := hsource hworkX
      cases a with
      | false =>
        rw [if_neg (by simp)] at hzy
        subst hzy
        simp only [Bool.false_eq_true, if_false] at htime hradius
        rw [hstepPeriod hworkZ, hradius]
        omega
      | true =>
        rw [if_pos rfl] at hzy
        obtain ⟨hmatchedWork, hmatchedPeriod⟩ := chainWork_matched hzy
        have hworkY : 0 < chainWork y := by
          by_contra hdone
          have := chainWork_matched_done hzy hlagY hpreY hbackY (by omega)
          omega
        simp only [if_true] at htime hradius
        rw [hmatchedPeriod hworkZ, hstepPeriod hworkY, hradius]
        omega
    · have hdoneY := chainWork_step_done hstep hlagX hpreX hbackX (by omega)
      exfalso
      cases a with
      | false =>
        rw [if_neg (by simp)] at hzy
        subst hzy
        omega
      | true =>
        rw [if_pos rfl] at hzy
        have := chainWork_matched_done hzy hlagY hpreY hbackY hdoneY
        omega
  · rw [hz] at hworkZ
    simp [chainWork] at hworkZ
  · obtain ⟨hbits, hradiusBound⟩ := hbirth hidle hfound
    obtain ⟨hstartWork, hstartPeriod⟩ := chainWork_chainStart answer cc walker ver radius
    rw [hradiusValue] at hstartWork
    have hbitsZ : (1 : ℤ) ≤ (remainingBits answer : ℤ) := by exact_mod_cast hbits
    cases a with
    | false =>
      rw [if_neg (by simp)] at hz
      rw [hz] at hworkZ ⊢
      simp only [Bool.false_eq_true, if_false] at htime hradius
      rw [hstartWork, hstartPeriod, hradius]
      omega
    | true =>
      rw [if_pos rfl] at hz
      obtain ⟨hmatchedWork, hmatchedPeriod⟩ := chainWork_matched hz
      simp only [if_true] at htime hradius
      rw [hmatchedPeriod hworkZ, hstartPeriod, hradius]
      rw [hstartWork] at hmatchedWork
      omega

end PalPeg.ChainClock


