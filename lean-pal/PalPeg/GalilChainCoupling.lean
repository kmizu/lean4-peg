import PalPeg.GalilLengthFloor
import PalPeg.GalilShiftH
import PalPeg.GalilBootVM
import PalPeg.GalilInvPlus


/-!
# Chain–scan coupling: `hbudget` and `hcopy` of `GalilLengthFloor`

* `Coupled c s` (tick-local, `coupled_tick` over every `Tick` of
  `galilFrameS (sharedC …)`): outside scan/shift/init the chain is idle; the
  period block invariant `BlockInv`; the radius ledger `SumRel` (`lag = radius`
  in copy/back, `distance + lag = radius` on an unbroken watch); and on an
  unbroken watch either the fresh phase ledger `FreshC`
  (`phase·h + pos − 1 ≤ distance` forward, `phase·h + h − 1 − pos ≤ distance`
  backward; not in shift mode) or, after a shift (`periodOnly`), the round
  bound `2h ≤ radius + cycle (+ remaining in shift mode)`.
* `guard_budget`: at a guarded shift entry `h ≤ radius + 1` (fresh: phase `4`
  gives `4h ≤ distance = radius`; after a shift: `singlePositive cycle` gives
  `cycle ≤ 1`).  The periodOnly case is therefore tick-local too: `cycle` is
  reset by `beginShiftVM`, `+2` per shift unit, `−1` per matched comparison.
  The margin guard is not used.
* `hbudget_of_invLP`: unconditional (an `InvL` state is chain-idle).
* `CopyPack` (`mode ≠ copy → CopyIdle`) is preserved by every tick
  (`copyPack_tick`) and holds at boot (`copyPack_boot`), but is not a
  consequence of `InvLP` (which does not constrain `fpp`): `hfloor_final`
  keeps `hcopy`, `hfloor_of_reach` takes it from any run out of a copy-pack
  state.
-/

set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace PalPeg.GalilChainCoupling
open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainInputSupply GalilBranchInvariants

/-! ## 1. Positions on a period block -/

theorem mem_of_append_cons {α : Type} {A B C : List α} {f x : α} (hA : A ≠ [])
    (h : A ++ f :: B = x :: C) : f ∈ C := by
  obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil hA
  simp only [List.cons_append, List.cons.injEq] at h
  rw [← h.2]; simp

theorem onBlock_first {v : GalilScaffoldChainPeriod.Tape} (h : OnBlock v) {c : Fin 3}
    (hf : v.focus = .first c) : v.left = [] := by
  obtain ⟨c0, b0, ys, he⟩ := h
  by_contra hne
  have hA : v.left.reverse ≠ [] := by simpa using hne
  have hm := mem_of_append_cons hA he
  rw [hf] at hm
  simp at hm

theorem onBlock_left_ne {v : GalilScaffoldChainPeriod.Tape} (h : OnBlock v)
    (hf : GalilScaffoldChainPeriod.isFirst v.focus = false) : v.left ≠ [] := by
  obtain ⟨c0, b0, ys, he⟩ := h
  intro hl
  rw [hl] at he
  simp only [List.reverse_nil, List.nil_append, blockTokens, List.cons.injEq] at he
  rw [he.1] at hf
  simp [GalilScaffoldChainPeriod.isFirst] at hf

theorem onBlock_last {v : GalilScaffoldChainPeriod.Tape} (h : OnBlock v) {b : Fin 3}
    (hf : v.focus = .last b) : v.right = [] := by
  obtain ⟨c0, b0, ys, he⟩ := h
  by_contra hne
  have h2 := congrArg List.reverse he
  simp only [blockTokens, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.reverse_reverse] at h2
  rw [List.append_assoc, List.singleton_append] at h2
  have hA : v.right.reverse ≠ [] := by simpa using hne
  have hm := mem_of_append_cons hA h2
  rw [hf] at hm
  simp at hm

/-! ## 2. The fresh-watch phase ledger -/

/-- Head position `p = |left|`, block size `h = |left| + |right|`; the phase
ledger of an unshifted watch. -/
def FreshC (k : GalilScaffoldChainConsume.State) : Prop :=
  (k.forward = true → 1 ≤ k.period.left.length ∧
    (k.phase.val : ℤ) * ((k.period.left.length + k.period.right.length : ℕ) : ℤ) +
      (k.period.left.length : ℤ) - 1 ≤ value k.distance) ∧
  (k.forward = false → k.period.left.length + 1 ≤ k.period.left.length + k.period.right.length ∧
    (k.phase.val : ℤ) * ((k.period.left.length + k.period.right.length : ℕ) : ℤ) +
      ((k.period.left.length + k.period.right.length : ℕ) : ℤ) - 1 -
        (k.period.left.length : ℤ) ≤ value k.distance)

theorem advancePhase_le (p : Fin 5) :
    ((GalilScaffoldChainConsume.advancePhase p).val : ℤ) ≤ p.val + 1 := by
  unfold GalilScaffoldChainConsume.advancePhase; simp only; omega

theorem consume_fresh (k : GalilScaffoldChainConsume.State) (seen : Option (Fin 3))
    (hb : OnBlock k.period)
    (hnb : (GalilScaffoldChainConsume.consume k seen).broken = false) :
    k.broken = false ∧
    value (GalilScaffoldChainConsume.consume k seen).distance = value k.distance + 1 ∧
    (FreshC k → FreshC (GalilScaffoldChainConsume.consume k seen)) := by
  cases hf : k.period.focus with
  | blank =>
    rw [GalilShiftH.consume_of_none k seen (by rw [hf]; rfl)] at hnb; cases hnb
  | left =>
    rw [GalilShiftH.consume_of_none k seen (by rw [hf]; rfl)] at hnb; cases hnb
  | plain a =>
    by_cases hs : seen = some a
    · subst hs
      have hl := onBlock_left_ne hb (by rw [hf]; rfl)
      have hr := onBlock_right_ne hb (by rw [hf]; rfl)
      rw [GalilScaffoldChainConsume.plain k a hf] at hnb ⊢
      refine ⟨hnb, inc_value _, ?_⟩
      rintro ⟨hF1, hF2⟩
      rcases k with ⟨⟨ls, f, rs⟩, d, bd, lst, ph, fw, br⟩
      simp only at hF1 hF2 hl hr ⊢
      cases fw with
      | true =>
        obtain ⟨r0, rs', rfl⟩ := List.exists_cons_of_ne_nil hr
        obtain ⟨t1, t2⟩ := hF1 rfl
        refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
        simp only [GalilScaffoldChainPeriod.moveRight, ↓reduceIte, List.length_cons, inc_value] at t2 ⊢
        push_cast at t2 ⊢
        first | exact ⟨trivial, by linarith⟩ | exact ⟨by omega, by linarith⟩ | linarith
      | false =>
        obtain ⟨l0, ls', rfl⟩ := List.exists_cons_of_ne_nil hl
        obtain ⟨t1, t2⟩ := hF2 rfl
        refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
        simp only [GalilScaffoldChainPeriod.moveLeft, Bool.false_eq_true, ↓reduceIte,
          List.length_cons, inc_value] at t1 t2 ⊢
        push_cast at t1 t2 ⊢
        first | exact ⟨trivial, by linarith⟩ | exact ⟨by omega, by linarith⟩ | linarith
    · rw [GalilScaffoldChainConsume.mismatch k a seen (by rw [hf]; rfl) hs] at hnb; cases hnb
  | first c =>
    by_cases hs : seen = some c
    · subst hs
      have hl := onBlock_first hb hf
      have hr := onBlock_right_ne hb (by rw [hf]; rfl)
      have hap := advancePhase_le k.phase
      rw [GalilScaffoldChainConsume.first k c hf] at hnb ⊢
      refine ⟨hnb, inc_value _, ?_⟩
      rintro ⟨hF1, hF2⟩
      rcases k with ⟨⟨ls, f, rs⟩, d, bd, lst, ph, fw, br⟩
      simp only at hF1 hF2 hl hr hap ⊢
      subst hl
      obtain ⟨r0, rs', rfl⟩ := List.exists_cons_of_ne_nil hr
      cases fw with
      | true => exact absurd (hF1 rfl).1 (by simp)
      | false =>
        have := (hF2 rfl).2
        refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
        simp only [GalilScaffoldChainPeriod.moveRight, List.length_cons, List.length_nil,
          inc_value] at this ⊢
        push_cast at this ⊢
        have h0 : (0 : ℤ) ≤ (rs'.length : ℤ) + 1 := by positivity
        have hm := mul_le_mul_of_nonneg_right hap h0
        first | exact ⟨trivial, by nlinarith⟩ | exact ⟨le_refl _, by nlinarith⟩ | nlinarith
    · rw [GalilScaffoldChainConsume.mismatch k c seen (by rw [hf]; rfl) hs] at hnb; cases hnb
  | last b =>
    by_cases hs : seen = some b
    · subst hs
      have hl := onBlock_left_ne hb (by rw [hf]; rfl)
      have hr := onBlock_last hb hf
      have hap := advancePhase_le k.phase
      rw [GalilScaffoldChainConsume.last k b hf] at hnb ⊢
      refine ⟨hnb, inc_value _, ?_⟩
      rintro ⟨hF1, hF2⟩
      rcases k with ⟨⟨ls, f, rs⟩, d, bd, lst, ph, fw, br⟩
      simp only at hF1 hF2 hl hr hap ⊢
      subst hr
      obtain ⟨l0, ls', rfl⟩ := List.exists_cons_of_ne_nil hl
      cases fw with
      | false => exact absurd (hF2 rfl).1 (by simp)
      | true =>
        have := (hF1 rfl).2
        refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
        simp only [GalilScaffoldChainPeriod.moveLeft, List.length_cons, List.length_nil,
          inc_value] at this ⊢
        push_cast at this ⊢
        have h0 : (0 : ℤ) ≤ (ls'.length : ℤ) + 1 := by positivity
        have hm := mul_le_mul_of_nonneg_right hap h0
        first | exact ⟨trivial, by nlinarith⟩ | exact ⟨by omega, by nlinarith⟩ | nlinarith
    · rw [GalilScaffoldChainConsume.mismatch k b seen (by rw [hf]; rfl) hs] at hnb; cases hnb

#print axioms consume_fresh

/-! ## 3. Chain-level ledgers -/

/-- The radius ledger: the chain's `distance + lag` (its `lag` before the
watch) is the VM radius it was started from, plus the matched comparisons. -/
def SumRel : ChainVM → ℤ → Prop
  | .copy _ _ _ _ lag _ _, R => value lag = R
  | .back _ _ lag _ _, R => value lag = R
  | .watch w, R => w.machine.control.broken = false →
      value w.machine.control.distance + value w.lag = R
  | _, _ => True

/-- An unbroken watch is either fresh (phase ledger, under the side condition
`F`) or satisfies the round bound `O` at its semiperiod. -/
def WatchOK (x : ChainVM) (F : Prop) (O : ℕ → Prop) : Prop :=
  ∀ w, x = .watch w → w.machine.control.broken = false →
    (F ∧ FreshC w.machine.control) ∨ O (periodLength w)

theorem watchOK_mono {x : ChainVM} {F : Prop} {O O' : ℕ → Prop} (hO : ∀ h, O h → O' h)
    (hw : WatchOK x F O) : WatchOK x F O' := by
  intro w hx hb
  rcases hw w hx hb with h | h
  · exact Or.inl h
  · exact Or.inr (hO _ h)

theorem periodLength_consume (m : GalilScaffoldChainVerifier.State) (lag margin lag' margin' : Counter)
    (hb : OnBlock m.control.period) :
    periodLength ⟨GalilScaffoldChainVerifier.consume m, lag', margin'⟩ =
      periodLength ⟨m, lag, margin⟩ := by
  have h1 := GalilShiftH.cells_verifier_consume m hb
  have h2 := GalilShiftH.periodLength_succ_eq_cells ⟨GalilScaffoldChainVerifier.consume m, lag', margin'⟩
  have h3 := GalilShiftH.periodLength_succ_eq_cells ⟨m, lag, margin⟩
  simp only at h2 h3
  omega

theorem freshC_watchControl (v : GalilScaffoldChainPeriod.Tape) (hb : OnBlock v)
    (hf : GalilScaffoldChainPeriod.isFirst v.focus = true) : FreshC (watchControl v) := by
  have hl : v.left = [] := by
    cases hv : v.focus with
    | first c => exact onBlock_first hb hv
    | _ => rw [hv] at hf; simp [GalilScaffoldChainPeriod.isFirst] at hf
  rcases v with ⟨ls, f, rs⟩
  simp only at hl
  subst hl
  refine ⟨fun _ => ?_, fun h => absurd h (by simp [watchControl])⟩
  cases rs <;> simp [watchControl, GalilScaffoldChainPeriod.moveRight, value, reset]

theorem step_inv {x y : ChainVM} (h : ChainStep x y) {F : Prop} (hF : F) {O : ℕ → Prop} {R : ℤ}
    (hb : BlockInv x) (hs : SumRel x R) (hw : WatchOK x F O) :
    SumRel y R ∧ WatchOK y F O := by
  cases h with
  | idle => exact ⟨hs, hw⟩
  | brokenIdle => exact ⟨trivial, fun w hw => by cases hw⟩
  | copyBit => exact ⟨hs, fun w hw => by cases hw⟩
  | copyEnd => exact ⟨hs, fun w hw => by cases hw⟩
  | backStep => exact ⟨hs, fun w hw => by cases hw⟩
  | backDone v h lag margin ver hf =>
    refine ⟨fun _ => ?_, fun w hw' _ => ?_⟩
    · show value reset + value lag = R
      have : value reset = 0 := rfl
      have hs' : value lag = R := hs
      omega
    · cases hw'
      exact Or.inl ⟨hF, freshC_watchControl v hb hf⟩
  | watchStep w w' hi =>
    cases hi with
    | idle => exact ⟨hs, hw⟩
    | take hp hg =>
      have hbw : OnBlock w.machine.control.period := hb
      refine ⟨fun hnb => ?_, fun w'' hw'' hnb => ?_⟩
      · obtain ⟨hnb0, hd, -⟩ := consume_fresh w.machine.control _ hbw hnb
        have h0 := hs hnb0
        show value (GalilScaffoldChainVerifier.consume w.machine).control.distance +
          value (dec w.lag) = R
        rw [dec_value]
        have hd' : value (GalilScaffoldChainVerifier.consume w.machine).control.distance =
            value w.machine.control.distance + 1 := hd
        omega
      · cases hw''
        obtain ⟨hnb0, -, hfr⟩ := consume_fresh w.machine.control _ hbw hnb
        rcases hw w rfl hnb0 with ⟨hF', hfr0⟩ | ho
        · exact Or.inl ⟨hF', hfr hfr0⟩
        · right
          show O (periodLength ⟨GalilScaffoldChainVerifier.consume w.machine, dec w.lag, w.margin⟩)
          rw [periodLength_consume w.machine w.lag w.margin _ _ hbw]
          exact ho

theorem matched_inv {y z : ChainVM} (h : ChainMatched y z) {F : Prop} {O : ℕ → Prop} {R : ℤ}
    (hb : BlockInv y) (hs : SumRel y R) (hw : WatchOK y F O) :
    SumRel z (R + 1) ∧ WatchOK z F O := by
  cases h with
  | idle => exact ⟨trivial, fun w hw => by cases hw⟩
  | copy =>
    refine ⟨?_, fun w hw => by cases hw⟩
    show value (inc _) = R + 1
    rw [inc_value]; exact congrArg (· + 1) hs
  | back =>
    refine ⟨?_, fun w hw => by cases hw⟩
    show value (inc _) = R + 1
    rw [inc_value]; exact congrArg (· + 1) hs
  | breaks => exact ⟨trivial, fun w hw => by cases hw⟩
  | watch w w' ho =>
    cases ho with
    | queued hz =>
      refine ⟨fun hnb => ?_, fun w'' hw'' hnb => ?_⟩
      · have h0 := hs hnb
        show value w.machine.control.distance + value (inc w.lag) = R + 1
        rw [inc_value]; omega
      · cases hw''
        exact hw w rfl hnb
    | immediate hz hg =>
      have hbw : OnBlock w.machine.control.period := hb
      refine ⟨fun hnb => ?_, fun w'' hw'' hnb => ?_⟩
      · obtain ⟨hnb0, hd, -⟩ := consume_fresh w.machine.control _ hbw hnb
        have h0 := hs hnb0
        show value (GalilScaffoldChainVerifier.consume w.machine).control.distance +
          value w.lag = R + 1
        have hd' : value (GalilScaffoldChainVerifier.consume w.machine).control.distance =
            value w.machine.control.distance + 1 := hd
        omega
      · cases hw''
        obtain ⟨hnb0, -, hfr⟩ := consume_fresh w.machine.control _ hbw hnb
        rcases hw w rfl hnb0 with ⟨hF', hfr0⟩ | ho
        · exact Or.inl ⟨hF', hfr hfr0⟩
        · right
          show O (periodLength ⟨GalilScaffoldChainVerifier.consume w.machine, w.lag, inc w.margin⟩)
          rw [periodLength_consume w.machine w.lag w.margin _ _ hbw]
          exact ho

theorem chainAt_false_inv {found : Bool} {ans : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter} {x z : ChainVM}
    (h : chainAt false found ans cc walker ver radius x z) {F : Prop} (hF : F) {O : ℕ → Prop}
    (hb : BlockInv x) (hs : SumRel x (value radius)) (hw : WatchOK x F O) :
    BlockInv z ∧ SumRel z (value radius) ∧ WatchOK z F O := by
  rcases h with ⟨-, y, hstep, hzy⟩ | ⟨-, -, rfl⟩ | ⟨-, -, hz⟩
  · rw [if_neg (by simp)] at hzy
    subst hzy
    exact ⟨blockInv_step hstep hb, step_inv hstep hF hb hs hw⟩
  · exact ⟨trivial, trivial, fun w hw => by cases hw⟩
  · rw [if_neg (by simp)] at hz
    subst hz
    exact ⟨blockInv_chainStart _ _ _ _ _, rfl, fun w hw => by cases hw⟩

theorem chainAt_true_inv {found : Bool} {ans : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter} {x z : ChainVM}
    (h : chainAt true found ans cc walker ver radius x z) {F : Prop} (hF : F) {O : ℕ → Prop}
    (hb : BlockInv x) (hs : SumRel x (value radius)) (hw : WatchOK x F O) :
    BlockInv z ∧ SumRel z (value radius + 1) ∧ WatchOK z F O := by
  rcases h with ⟨-, y, hstep, hzy⟩ | ⟨-, -, rfl⟩ | ⟨-, -, hz⟩
  · rw [if_pos rfl] at hzy
    have hb' := blockInv_step hstep hb
    obtain ⟨hs', hw'⟩ := step_inv hstep hF hb hs hw
    exact ⟨blockInv_matched hzy hb', matched_inv hzy hb' hs' hw'⟩
  · exact ⟨trivial, trivial, fun w hw => by cases hw⟩
  · rw [if_pos rfl] at hz
    have hb0 := blockInv_chainStart ans cc walker ver radius
    unfold chainStart at hz hb0
    exact ⟨blockInv_matched hz hb0, matched_inv hz hb0 rfl (fun w hw => by cases hw)⟩

#print axioms step_inv
#print axioms matched_inv
#print axioms chainAt_false_inv
#print axioms chainAt_true_inv

/-! ## 4. The state-level coupling -/

/-- The round bound after a shift (`periodOnly`): the continuation countdown
plus the radius (plus the shift budget still to run, in `shift` mode) covers
two semiperiods. -/
def Other (po : Bool) (m : Mode) (R C Rem : ℤ) (h : ℕ) : Prop :=
  po = true ∧ (m = Mode.shift → 2 * (h : ℤ) ≤ R + C + Rem) ∧
    (m ≠ Mode.shift → 2 * (h : ℤ) ≤ R + C)

/-- **The chain–scan coupling.** -/
structure Coupled (c : Control) (s : GalilVM) : Prop where
  idleOut : c.mode ≠ Mode.scan → c.mode ≠ Mode.shift → c.mode ≠ Mode.init → s.chain = .idle
  block : BlockInv s.chain
  sum : SumRel s.chain (value s.radius)
  watch : WatchOK s.chain (c.mode ≠ Mode.shift)
    (Other s.periodOnly c.mode (value s.radius) (value s.cycle) (value s.remaining))

theorem coupled_of_idle {c : Control} {s : GalilVM} (h : s.chain = .idle) : Coupled c s :=
  ⟨fun _ _ _ => h, by rw [h]; trivial, by rw [h]; trivial, fun w hw => by rw [h] at hw; cases hw⟩

theorem value_le_one_of_single {x : Counter} (h : singlePositive x = true) : value x ≤ 1 := by
  rcases x with ⟨pos, neg⟩
  cases pos with
  | nil => simp [singlePositive, positive] at h
  | cons a t =>
    cases t with
    | nil => simp [value]
    | cons b u => simp [singlePositive] at h

theorem value_zero_of_zero {x : Counter} (h : zero x = true) : value x = 0 := by
  rcases x with ⟨pos, neg⟩
  simp only [zero, Bool.and_eq_true, List.isEmpty_iff] at h
  simp [value, h.1, h.2]

theorem value_nonpos_of_not_positive {x : Counter} (h : positive x = false) : value x ≤ 0 := by
  rcases x with ⟨pos, neg⟩
  simp only [positive, Bool.not_eq_false', List.isEmpty_iff] at h
  simp [value, h]

/-- **The guard budget.**  At a guarded shift entry of a coupled watch: `h ≤ R+1`
(fresh: `4h ≤ R` from phase `4`; after a shift: `2h ≤ R + 1` from the
countdown at its last cell). -/
theorem guard_budget {w : GalilScaffoldChainWatch.State} {R C Rem : ℤ} {F : Prop}
    {po : Bool} {m : Mode} (hm : m ≠ Mode.shift) {cyc : Counter} (hC : value cyc = C)
    (hs : SumRel (.watch w) R) (hw : WatchOK (.watch w) F (Other po m R C Rem))
    (hz : zero w.lag = true) (hph : w.machine.control.phase = 4)
    (hbr : w.machine.control.broken = false)
    (hif : if po then singlePositive cyc = true else negative w.margin = false) :
    (periodLength w : ℤ) ≤ R + 1 := by
  have hd : value w.machine.control.distance + value w.lag = R := hs hbr
  rw [value_zero_of_zero hz] at hd
  have hh0 : (0 : ℤ) ≤ periodLength w := by positivity
  rcases hw w rfl hbr with ⟨-, hf1, hf2⟩ | ⟨hpo, -, hns⟩
  · have hpv : (w.machine.control.phase.val : ℤ) = 4 := by rw [hph]; rfl
    have hpl : periodLength w = w.machine.control.period.left.length +
        w.machine.control.period.right.length := rfl
    cases hfw : w.machine.control.forward with
    | true =>
      obtain ⟨-, h2⟩ := hf1 hfw
      rw [hpv, ← hpl] at h2
      linarith
    | false =>
      obtain ⟨h1, h2⟩ := hf2 hfw
      rw [hpv, ← hpl] at h2
      rw [← hpl] at h1
      have : (w.machine.control.period.left.length : ℤ) + 1 ≤ (periodLength w : ℤ) := by
        exact_mod_cast h1
      linarith
  · rw [hpo, if_pos rfl] at hif
    have h1 := value_le_one_of_single hif
    have h2 := hns hm
    linarith

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- What a comparison from a coupled scan state delivers. -/
theorem compare_inv {c : Control} {s s' : GalilVM} (hC : Coupled c s) (hm : c.mode = Mode.scan)
    (hcmp : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s') :
    BlockInv s'.chain ∧
    (s.chain ≠ ChainVM.idle → s'.periodOnly = s.periodOnly) ∧ s'.remaining = s.remaining ∧
    ((galilFrameS (sharedC onLetter leftFirst centre place entry) q first).matched s' →
      s'.radius = inc s.radius ∧ (s.chain ≠ ChainVM.idle → s'.cycle = cycleAfter s) ∧
      SumRel s'.chain (value s.radius + 1) ∧
      WatchOK s'.chain (c.mode ≠ Mode.shift)
        (Other s.periodOnly c.mode (value s.radius) (value s.cycle) (value s.remaining))) ∧
    (¬ (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).matched s' →
      s'.radius = inc s.radius ∧ (s.chain ≠ ChainVM.idle → s'.cycle = s.cycle) ∧
      SumRel s'.chain (value s.radius) ∧
      WatchOK s'.chain (c.mode ≠ Mode.shift)
        (Other s.periodOnly c.mode (value s.radius) (value s.cycle) (value s.remaining))) := by
  obtain ⟨vs, vq, a, -, -, hiff, -, hch, hteq⟩ :
    compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
  have hF : c.mode ≠ Mode.shift := by rw [hm]; decide
  cases a with
  | true =>
    rw [if_pos rfl] at hteq
    subst hteq
    obtain ⟨hb, hs, hw⟩ := chainAt_true_inv hch hF hC.block hC.sum hC.watch
    simp only [afterBirth_chain, afterBirth_radius, afterBirth_remaining, afterBirth_left,
      afterBirth_right, afterBirth_center, afterBirth_replay, afterBirth_searchGet]
    refine ⟨hb, fun hne => ?_, rfl, fun _ => ⟨rfl, fun hne => ?_, hs, hw⟩,
      fun hn => absurd ?_ hn⟩
    · rw [afterBirth_of_ne_idle hne]; rfl
    · rw [afterBirth_of_ne_idle hne]; rfl
    show GalilScaffoldInputHead.read (afterBirth _ (afterCompare s vs vq)).left
      = GalilScaffoldInputHead.read (afterBirth _ (afterCompare s vs vq)).right
    rw [afterBirth_left, afterBirth_right]
    exact hiff.1 rfl
  | false =>
    rw [if_neg (by simp)] at hteq
    subst hteq
    obtain ⟨hb, hs, hw⟩ := chainAt_false_inv hch hF hC.block hC.sum hC.watch
    simp only [afterBirth_chain, afterBirth_radius, afterBirth_remaining, afterBirth_left,
      afterBirth_right, afterBirth_center, afterBirth_replay, afterBirth_searchGet]
    refine ⟨hb, fun hne => ?_, rfl, fun hmt => absurd (hiff.2 ?_) (by simp),
      fun _ => ⟨rfl, fun hne => ?_, hs, hw⟩⟩
    · rw [afterBirth_of_ne_idle hne]; rfl
    swap
    · rw [afterBirth_of_ne_idle hne]; rfl
    show GalilScaffoldInputHead.read (afterMismatch s vs vq).left
      = GalilScaffoldInputHead.read (afterMismatch s vs vq).right
    have h0 : GalilScaffoldInputHead.read (afterBirth _ (afterMismatch s vs vq)).left
      = GalilScaffoldInputHead.read (afterBirth _ (afterMismatch s vs vq)).right := hmt
    rw [afterBirth_left, afterBirth_right] at h0
    exact h0

/-- **`budget_of_coupled`.**  The `BudgetAt` of `GalilLengthFloor` at every
coupled state. -/
theorem budget_of_coupled {c : Control} {s : GalilVM} (hC : Coupled c s) :
    GalilLengthFloor.BudgetAt onLetter leftFirst centre place entry q first c s := by
  intro hm _ s' w hcmp hmt hg hw
  have hne : s.chain ≠ ChainVM.idle := by
    intro hidle
    obtain ⟨vs, vq, a, -, -, -, -, hch, hteq⟩ :
      compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
    obtain ⟨w1, hw1, -⟩ := hg
    rw [hidle] at hch
    rw [hteq, afterBirth_chain] at hw1
    exact chainAt_idle_not_watch hch w1 (by rw [← hw1]; cases a <;> rfl)
  obtain ⟨-, hpo, -, -, hmis⟩ := compare_inv onLetter leftFirst centre place entry q first hC hm hcmp
  obtain ⟨hrad, hcyc, hs, hwk⟩ := hmis hmt
  have hpo := hpo hne
  have hcyc := hcyc hne
  obtain ⟨w1, hw1, hz, hph, hbr, hif, -⟩ := hg
  rw [hw1] at hw
  cases hw
  rw [hw1] at hs hwk
  rw [hpo, hcyc] at hif
  have := guard_budget (by rw [hm]; decide) rfl hs hwk hz hph hbr hif
  rw [hrad, inc_value]
  exact this

theorem coupled_tick {c c' : Control} {s t : GalilVM} (hC : Coupled c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : Coupled c' t := by
  cases h
  case init =>
    rename_i hm hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s t := hi
    exact coupled_of_idle hch
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, -, hch, -, hpo, hrad, -, hcyc, hrem, -, -, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    have hF : c.mode ≠ Mode.shift := by rw [hm]; decide
    obtain ⟨hb', hs', hw'⟩ := chainAt_false_inv hch hF hC.block hC.sum hC.watch
    refine ⟨fun h1 => absurd hm h1, hb', by rw [hrad]; exact hs', ?_⟩
    rw [hpo, hrad, hcyc, hrem]
    cases hbb : chainBorn (decide ((searchLens.get t).search.mode
        = GalilScaffoldSearchFinish.Mode.found)) s.chain with
    | false => simpa using hw'
    | true =>
      intro w hx hbk
      exact absurd hx (chainBorn_true_not_watch hbb hch w)
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, -, hch, -, hpo, hrad, -, hcyc, hrem, -, -, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    have hF : c.mode ≠ Mode.shift := by rw [hm]; decide
    obtain ⟨hb', hs', hw'⟩ := chainAt_false_inv hch hF hC.block hC.sum hC.watch
    refine ⟨fun h1 => absurd hm h1, hb', by rw [hrad]; exact hs', ?_⟩
    rw [hpo, hrad, hcyc, hrem]
    cases hbb : chainBorn (decide ((searchLens.get t).search.mode
        = GalilScaffoldSearchFinish.Mode.found)) s.chain with
    | false => simpa using hw'
    | true =>
      intro w hx hbk
      exact absurd hx (chainBorn_true_not_watch hbb hch w)
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    exact coupled_of_idle rfl
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨hb, hpo, hrem, hmat, -⟩ :=
      compare_inv onLetter leftFirst centre place entry q first hC hm hcmp
    obtain ⟨hrad, hcyc, hs, hw⟩ := hmat hmt
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have htc : t.chain = s'.chain := by rw [hpl']; cases c.replaying <;> rfl
    have htr : t.radius = s'.radius := by rw [hpl']; cases c.replaying <;> rfl
    have hty : t.cycle = s'.cycle := by rw [hpl']; cases c.replaying <;> rfl
    have htp : t.periodOnly = s'.periodOnly := by rw [hpl']; cases c.replaying <;> rfl
    have htm : t.remaining = s'.remaining := by rw [hpl']; cases c.replaying <;> rfl
    by_cases hne : s.chain = ChainVM.idle
    · refine ⟨fun h1 => absurd hm h1, by rw [htc]; exact hb, ?_, ?_⟩
      · rw [htc, htr, hrad, inc_value]; exact hs
      · intro w0 hx _
        obtain ⟨vs, vq, a, -, -, -, -, hch, hteq⟩ :
          compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
        rw [hne] at hch
        rw [htc, hteq, afterBirth_chain] at hx
        exact absurd (by cases a <;> exact hx) (chainAt_idle_not_watch hch w0)
    have hpo := hpo hne
    have hcyc := hcyc hne
    refine ⟨fun h1 => absurd hm h1, by rw [htc]; exact hb, ?_, ?_⟩
    · rw [htc, htr, hrad, inc_value]; exact hs
    · rw [htc, htr, hty, htp, htm, hpo, hrem, hrad, hcyc]
      refine watchOK_mono ?_ hw
      rintro h ⟨hp, -, hns⟩
      refine ⟨hp, fun h1 => absurd (hm.symm.trans h1) (by decide), fun h1 => ?_⟩
      have h2 := hns h1
      unfold cycleAfter
      rw [hp, if_pos rfl, inc_value, dec_value]
      linarith
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨hbl, hpo, hrem, -, hmis⟩ :=
      compare_inv onLetter leftFirst centre place entry q first hC hm hcmp
    obtain ⟨hrad, hcyc, hs, hw⟩ := hmis hmt
    obtain ⟨w, hs0, ht⟩ : beginShiftVM' s' t := hb
    obtain ⟨w1, hw1, hz, hph, hbr, hif, -⟩ := hg
    have hne : s.chain ≠ ChainVM.idle := by
      intro hidle
      obtain ⟨vs0, vq0, a0, -, -, -, -, hch0, hteq0⟩ :
        compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
      rw [hidle] at hch0
      have hw1' := hw1
      rw [hteq0, afterBirth_chain] at hw1'
      exact chainAt_idle_not_watch hch0 w1 (by cases a0 <;> exact hw1')
    have hpo := hpo hne
    have hcyc := hcyc hne
    rw [hw1] at hs0
    cases hs0
    rw [hw1] at hbl hs hw
    rw [hpo, hcyc] at hif
    have hbud := guard_budget (by rw [hm]; decide) rfl hs hw hz hph hbr hif
    subst ht
    have hbw : OnBlock w.machine.control.period := hbl
    refine ⟨fun _ h2 => absurd rfl h2, onBlock_verifier_consume _ hbw, fun hnb => ?_,
      fun w' hw' hnb => ?_⟩
    · obtain ⟨hnb0, hd, -⟩ := consume_fresh w.machine.control _ hbw hnb
      have h0 := hs hnb0
      show value (GalilScaffoldChainVerifier.consume w.machine).control.distance +
        value w.lag = value s'.radius
      have hd' : value (GalilScaffoldChainVerifier.consume w.machine).control.distance =
          value w.machine.control.distance + 1 := hd
      rw [hrad, inc_value]; omega
    · cases hw'
      right
      have hpl := periodLength_consume w.machine w.lag w.margin w.lag (inc w.margin) hbw
      refine ⟨rfl, fun _ => ?_, fun h2 => absurd rfl h2⟩
      show 2 * ((periodLength ⟨GalilScaffoldChainVerifier.consume w.machine, w.lag,
        inc w.margin⟩ : ℕ) : ℤ) ≤ value s'.radius + value reset +
          value (ofNat (periodLength w))
      rw [hpl, ofNat_value, hrad, inc_value]
      have : value reset = 0 := rfl
      linarith
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨p, ht⟩ : beginFallbackVM' s' t := hb
    subst ht
    exact coupled_of_idle rfl
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
      rcases hww w rfl hnb with ⟨hF, -⟩ | ⟨hpo, hsh, -⟩
      · exact absurd hm hF
      · right
        refine ⟨hpo, fun _ => ?_, fun h2 => absurd hm h2⟩
        have h2 := hsh hm
        show 2 * ((periodLength w : ℕ) : ℤ) ≤ value (dec s.radius) +
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
    rcases hC.watch w hw hnb with ⟨hF, -⟩ | ⟨hpo, hsh, -⟩
    · exact absurd hm hF
    · right
      refine ⟨hpo, fun h1 => absurd h1 (by simp), fun _ => ?_⟩
      have h2 := hsh hm
      linarith
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : replayStartVM entry s t := hi
    exact coupled_of_idle hch
  all_goals
    first
    | (rename_i hm _ _ hi
       exact coupled_of_idle ((congrArg GalilVM.chain hi.2).trans
        (hC.idleOut (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))))
    | (rename_i hm _ hi
       exact coupled_of_idle ((congrArg GalilVM.chain hi.2).trans
        (hC.idleOut (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))))
    | (rename_i hm hi
       exact coupled_of_idle ((congrArg GalilVM.chain hi.2).trans
        (hC.idleOut (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))))

#print axioms guard_budget
#print axioms compare_inv
#print axioms budget_of_coupled
#print axioms coupled_tick

theorem coupled_steps {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hC : Coupled x.ctl x.vm) : Coupled y.ctl y.vm := by
  induction h with
  | zero => exact hC
  | succ ht _ ih => exact ih (coupled_tick onLetter leftFirst centre place entry q first delay hC ht)

/-! ## 5. The FPP copy walker is idle outside `copy` -/

/-- Outside `copy` mode the FPP copy walker is idle. -/
def CopyPack (c : Control) (s : GalilVM) : Prop := c.mode ≠ Mode.copy → CopyIdle s

theorem copyPack_tick {c c' : Control} {s t : GalilVM} (hP : CopyPack c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : CopyPack c' t := by
  cases h
  case init =>
    rename_i hm hi
    obtain ⟨-, -, -, -, -, -, -, -, hfpp, -⟩ : initVM entry s t := hi
    intro _; rw [copyIdle_iff, hfpp, ← copyIdle_iff]; exact hP (by rw [hm]; decide)
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hfpp, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    intro _; rw [copyIdle_iff, hfpp, ← copyIdle_iff]; exact hP (by rw [hm]; decide)
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hfpp, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    intro _; rw [copyIdle_iff, hfpp, ← copyIdle_iff]; exact hP (by rw [hm]; decide)
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    intro _; exact hP (by rw [hm]; decide)
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨hf, -⟩ :=
      GalilLengthFloor.compare_counters onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have htf : t.fpp = s'.fpp := by rw [hpl']; cases c.replaying <;> rfl
    intro _; rw [copyIdle_iff, htf, hf, ← copyIdle_iff]; exact hP (by rw [hm]; decide)
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨hf, -⟩ :=
      GalilLengthFloor.compare_counters onLetter leftFirst centre place entry q first hcmp
    obtain ⟨w, hw, ht⟩ : beginShiftVM' s' t := hb
    subst ht
    intro _
    rw [copyIdle_iff]
    show GalilScaffoldPlace.read s'.fpp.walker = none ∨ GalilScaffoldCounter.zero s'.fpp.work = true
    rw [hf, ← copyIdle_iff]; exact hP (by rw [hm]; decide)
  case scan_fallback =>
    intro hx; exact absurd rfl hx
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨-, -, -, w, -, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    intro _; exact hP (by rw [hm]; decide)
  case shift_done =>
    rename_i o hm hp ho
    intro _; exact hP (by rw [hm]; decide)
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, -, -, -, -, -, -, -, hfpp, -⟩ : replayStartVM entry s t := hi
    intro _; rw [copyIdle_iff, hfpp, ← copyIdle_iff]; exact hP (by rw [hm]; decide)
  case copy_one =>
    rename_i hm hp hi
    intro hx; exact absurd hm hx
  case copy_done =>
    rename_i hm hp hi
    have hv : t.fpp = {s.fpp with program := FppControl.tape s.fpp 7 (fun t => GalilScaffoldTape.write t 5), mode := .home, finalStage := (GalilScaffoldPlace.read s.fpp.walker).isNone} := hi.1
    have he : GalilScaffoldPlace.read s.fpp.walker = none ∨ zero s.fpp.work = true :=
      Classical.byContradiction (fun hn => hp (Or.inr hn))
    intro _; rw [copyIdle_iff, hv]; exact he
  case home_step =>
    rename_i hm hl hi
    obtain ⟨-, hv⟩ : (s.fpp.program.config.tapes 7).left ≠ [] ∧
        t.fpp = {s.fpp with program := FppControl.tape s.fpp 7 GalilScaffoldTape.moveLeft} := hi.1
    intro _; rw [copyIdle_iff, hv]
    exact (copyIdle_iff s).1 (hP (by rw [hm]; decide))
  case home_start =>
    rename_i hm hl hi
    have hv : t.fpp = {s.fpp with program := GalilScaffoldControl.start 320 s.fpp.program, mode := .run} := hi.1
    intro _; rw [copyIdle_iff, hv]
    exact (copyIdle_iff s).1 (hP (by rw [hm]; decide))
  case fpp_slice =>
    rename_i hm hi
    obtain ⟨-, -, -, hv⟩ : s.fpp.mode = .run ∧
        GalilScaffoldControl.Run GalilFppMarkedCode.code s.fpp.program (List.replicate q true) t.fpp.program ∧
        t.fpp.program.done = false ∧ t.fpp = {s.fpp with program := t.fpp.program} := hi.1
    intro _; rw [copyIdle_iff, hv]
    exact (copyIdle_iff s).1 (hP (by rw [hm]; decide))
  case fpp_done =>
    rename_i hm hi
    obtain ⟨-, p, -, -, hv⟩ : s.fpp.mode = .run ∧ ∃ p : GalilScaffoldControl.Machine 9,
        GalilScaffoldControl.Run GalilFppMarkedCode.code s.fpp.program (List.replicate q true) p ∧
        p.done = true ∧ t.fpp = {s.fpp with program := markNew p first} := hi.1
    intro _; rw [copyIdle_iff, hv]
    exact (copyIdle_iff s).1 (hP (by rw [hm]; decide))
  case markEnd_step =>
    rename_i hm he hi
    have hv : t.fpp = markStep s.fpp GalilScaffoldTape.moveRight := hi.1
    intro _; rw [copyIdle_iff, hv]
    exact (copyIdle_iff s).1 (hP (by rw [hm]; decide))
  all_goals
    first
    | (rename_i hm _ _ hi
       obtain ⟨-, hv⟩ := hi.1
       have ht := hi.2
       rw [hv] at ht
       subst ht
       intro _; exact hP (by rw [hm]; decide))
    | (rename_i hm _ hi
       obtain ⟨-, hv⟩ := hi.1
       have ht := hi.2
       rw [hv] at ht
       subst ht
       intro _; exact hP (by rw [hm]; decide))
    | (rename_i hm _ hi
       have ht := hi.2
       rw [hi.1] at ht
       subst ht
       intro _; exact hP (by rw [hm]; decide))
    | (rename_i hm _ _ hi
       have ht := hi.2
       rw [hi.1] at ht
       subst ht
       intro _; exact hP (by rw [hm]; decide))

#print axioms coupled_steps
#print axioms copyPack_tick

theorem copyPack_steps {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hP : CopyPack x.ctl x.vm) : CopyPack y.ctl y.vm := by
  induction h with
  | zero => exact hP
  | succ ht _ ih => exact ih (copyPack_tick onLetter leftFirst centre place entry q first delay hP ht)

end Tick

/-- The boot state carries the copy pack. -/
theorem copyPack_boot (delay : ℕ) (w : List (Fin 2)) :
    CopyPack (GalilScaffoldController.initial delay) (GalilBootVM.initVM0 w) :=
  fun _ => (copyIdle_iff _).2 (Or.inr rfl)

/-! ## 6. Discharging `hbudget` and `hfloor` -/

open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilGlueBLeaves
  PalPeg.GalilRunSkeleton

/-- An `InvL` state is chain-idle in scan mode, hence coupled. -/
theorem coupled_of_invL {raw : List (Fin 2)} {c : Control} {r : GalilVM} (h : InvL raw c r) :
    Coupled c r := by
  rcases h.1 with hI | ⟨k, hI⟩
  · obtain ⟨Rad, last, hR⟩ := hI.rest
    exact coupled_of_idle hR.1
  · exact coupled_of_idle hI.chainIdle

/-- **`hbudget_of_invLP`.**  The `hbudget` hypothesis of
`GalilLengthFloor.hfloor_of_invLP`, unconditionally. -/
theorem hbudget_of_invLP (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIP : InvL raw c r ∧ EntryCounters raw r) :
    ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c, r⟩ z →
      GalilLengthFloor.BudgetAt (onLetterVM raw) leftFirstVM centre place entry q first z.ctl z.vm :=
  fun _ _ hz => budget_of_coupled (onLetterVM raw) leftFirstVM centre place entry q first
    (coupled_steps (onLetterVM raw) leftFirstVM centre place entry q first 2048 hz
      (coupled_of_invL hIP.1))

/-- `CopyIdle` at a scan state reached from any copy-pack state (e.g. the boot
state, `copyPack_boot`). -/
theorem copyIdle_of_reach (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {raw : List (Fin 2)} {c : Control} {r : GalilVM} (hm : c.mode = Mode.scan)
    {n : ℕ} {x : State GalilVM} (hx : CopyPack x.ctl x.vm)
    (hrun : Steps (galilFrameS (PofC centre place entry raw) q first) 2048 n x ⟨c, r⟩) :
    CopyIdle r :=
  copyPack_steps (onLetterVM raw) leftFirstVM centre place entry q first 2048 hrun hx
    (by rw [hm]; decide)

/-- **`hfloor_final`.**  The `hfloor` of `centreLive_of_invLP_run` from `InvLP`
and `CopyIdle` at the entry; `hbudget` is discharged. -/
theorem hfloor_final (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIP : InvL raw c r ∧ EntryCounters raw r) (hcopy : CopyIdle r) :
    ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c, r⟩ z →
      z.ctl.mode = Mode.scan → 0 ≤ value z.vm.length :=
  GalilLengthFloor.hfloor_of_invLP centre place entry q first hIP hcopy
    (hbudget_of_invLP centre place entry q first hIP)

/-- `hfloor_final` with `CopyIdle` obtained from a run out of a copy-pack state. -/
theorem hfloor_of_reach (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIP : InvL raw c r ∧ EntryCounters raw r)
    {n : ℕ} {x : State GalilVM} (hx : CopyPack x.ctl x.vm)
    (hrun : Steps (galilFrameS (PofC centre place entry raw) q first) 2048 n x ⟨c, r⟩) :
    ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c, r⟩ z →
      z.ctl.mode = Mode.scan → 0 ≤ value z.vm.length :=
  hfloor_final centre place entry q first hIP
    (copyIdle_of_reach centre place entry q first (invS_mode hIP.1.1).1 hx hrun)

#print axioms copyPack_steps
#print axioms copyPack_boot
#print axioms coupled_of_invL
#print axioms hbudget_of_invLP
#print axioms copyIdle_of_reach
#print axioms hfloor_final
#print axioms hfloor_of_reach

end PalPeg.GalilChainCoupling
