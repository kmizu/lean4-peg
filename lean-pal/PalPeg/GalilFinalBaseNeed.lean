import PalPeg.GalilFinalAssembly
import PalPeg.GalilTruncTick

/-!
# `O_base` discharged, `needLe` reduced to a per-state consumption bound

`GalilFinalAssembly.H_base` quantifies over **every** `PreTrace`.  `PreTrace`
does not pin down *which* time with a report point of the prefix `1` is chosen
as `Tc 1`, so `H_base` is not derivable from `PreTrace` alone.  We therefore
strengthen the trace record:

* `PreTraceB` — `PreTrace` plus `Tc 1 = 1`.
* `checkpoints_cost_upto1` — `GalilTraceCost.checkpoints_cost_upto` re-derived
  with the extra conjunct `1 ≤ M → Tc 1 = k0`, under `position r.right = 1`.
  The point: every costed run from right head `1` to right head `2·1-1 = 1` has
  no pieces (`costedRun_zero`), hence zero ticks, so the first checkpoint is the
  landing of the boot prefix itself.
* `preTraceB_exists` — booted at `initVM0` through `inv_init_pos` (`k0 = 1`).
* `base_of_preTraceB` — `Tc 1 ≤ 2050`.

`needLe` is reduced to the plain per-state bound `H_usedLeB`
(`usedVM` of every state up to checkpoint `m+1` is `≤ m+1`), with the
`pmax` bookkeeping proved (`needLe_of_usedLe`), and a further optional split
(`usedLe_of_mono`): monotone `usedVM` along the trace plus the bound at the
checkpoints.

`pal_in_peg_final'` is `pal_in_peg_final` with the trace hypotheses quantified
over `PreTraceB` (weaker than over `PreTrace`, see `*_B_of`), without `H_base`,
and with `H_usedLeB` in place of `H_needLe`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PalPeg.GalilFinalBaseNeed

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilTickArrive PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.GalilThrottledRun PalPeg.GalilThrottledRunGen PalPeg.GalilLedgerQ64
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleLocal PalPeg.GalilOracleDischarge
open PalPeg.GalilFinalAssembly

/-! ## Costed runs that do not advance the right head are empty -/

theorem costedRun_zero {r0 r1 : GalilVM} {k : ℕ} {L : List Piece} (h : CostedRun r0 r1 k L)
    (hle : position r1.right ≤ position r0.right) : k = 0 := by
  cases L with
  | nil => have := h.ticks; simpa using this.symm
  | cons p L =>
    have := h.places p List.mem_cons_self
    omega

/-! ## The checkpoint construction with `Tc 1 = k0` -/

theorem checkpoints_cost_upto1 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC P q first raw)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 x0 ⟨c, r⟩)
    (hI : InvL raw c r) (hpos : position r.right = 1) :
    ∀ M, M ≤ raw.length →
    ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) (e : ℕ),
      st 0 = x0 ∧ Tc 0 = 0 ∧ Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st e ∧
      (∀ m, m < M → Tc m ≤ Tc (m+1)) ∧ Tc M ≤ e ∧
      (∀ m, 1 ≤ m → m ≤ M →
        PalPeg.GalilReportPrefix.ReportPointAt raw m (st (Tc m)) ∧
        Refreshed P q first (st (Tc m))) ∧
      (∀ m, 1 ≤ m → m < M →
        Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw raw (m+1) - Cw raw m) + beta' 2048) ∧
      (M < raw.length → ∃ (c' : Control) (r' : GalilVM),
        st e = ⟨c', r'⟩ ∧ InvL raw c' r' ∧ position r'.right ≤ 2 * (M+1) - 1 ∧
        (1 ≤ M → ∃ L : List Piece, CostedRun (st (Tc M)).vm r' (e - Tc M) L)) ∧
      (M = 0 → e = k0 ∧ st e = ⟨c, r⟩) ∧
      (1 ≤ M → Tc 1 = k0) := by
  intro M
  induction M with
  | zero =>
    intro _
    obtain ⟨g, hg0, hgn, htr⟩ := stepsAll_fn hpre
    refine ⟨g, fun _ => 0, k0, hg0, rfl, htr, fun m hm => absurd hm (Nat.not_lt_zero _),
      Nat.zero_le _, fun m h1 h2 => absurd h1 (by omega), fun m h1 h2 => absurd h2 (by omega),
      fun _ => ⟨c, r, hgn, hI, by omega, fun h => absurd h (by omega)⟩,
      fun _ => ⟨rfl, hgn⟩, fun h => absurd h (by omega)⟩
  | succ M ih =>
    intro hM
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, hres, hzero, hone⟩ :=
      ih (by omega)
    obtain ⟨c', r', hste, hI', hp', hpend⟩ := hres (by omega)
    obtain ⟨y, k, L2, hrun, hcr, hrp, hfr, hcont⟩ :=
      reachC_from_invL P q first raw hor (m := M+1) (by omega) hM hI' hp'
    -- the first target is reached in zero ticks
    have hk0 : M = 0 → k = 0 ∧ e = k0 := by
      intro hM0
      subst hM0
      obtain ⟨he, hse⟩ := hzero rfl
      have hrr : r' = r := by
        have := hste.symm.trans hse
        exact (State.mk.injEq _ _ _ _ ▸ this).2
      subst hrr
      have hyp := hrp.atPlace
      exact ⟨costedRun_zero hcr (by rw [hyp, hpos]), he⟩
    obtain ⟨g1, hg10, hg1k, htr1⟩ := stepsAll_fn hrun
    have hj1 : st e = g1 0 := by rw [hste, hg10]
    set st1 := concat st g1 e with hst1
    have htr1' : Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st1 (e + k) :=
      trace_concat htr htr1 hj1
    have hst1y : st1 (e + k) = y := by rw [hst1, concat_end st g1 hj1, hg1k]
    obtain ⟨st2, e2, htr2, hagree, hle2, hres2⟩ :
        ∃ (st2 : ℕ → State GalilVM) (e2 : ℕ),
          Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st2 e2 ∧
          (∀ i, i ≤ e + k → st2 i = st1 i) ∧ e + k ≤ e2 ∧
          (M + 1 < raw.length → ∃ (c'' : Control) (r'' : GalilVM),
            st2 e2 = ⟨c'', r''⟩ ∧ InvL raw c'' r'' ∧ position r''.right ≤ 2 * (M+1+1) - 1 ∧
            ∃ L : List Piece, CostedRun y.vm r'' (e2 - (e + k)) L) := by
      by_cases hlt : M + 1 < raw.length
      · obtain ⟨c'', r'', k', L', hrun2, hcr2, hI2, hp2⟩ := hcont hlt
        obtain ⟨g2, hg20, hg2k, htr2⟩ := stepsAll_fn hrun2
        have hj2 : st1 (e + k) = g2 0 := by rw [hst1y, hg20]
        refine ⟨concat st1 g2 (e + k), e + k + k', trace_concat htr1' htr2 hj2,
          fun i hi => concat_le st1 g2 hi, by omega, fun _ => ⟨c'', r'', ?_, hI2, hp2, L', ?_⟩⟩
        · rw [concat_end st1 g2 hj2, hg2k]
        · rw [show e + k + k' - (e + k) = k' by omega]; exact hcr2
      · exact ⟨st1, e + k, htr1', fun _ _ => rfl, le_rfl, fun h => absurd h hlt⟩
    have hTcle : ∀ m, m ≤ M → Tc m ≤ e := fun m hm =>
      le_trans (mono_of_step Tc M hmono m M hm le_rfl) hTcM
    have hst2old : ∀ m, m ≤ M → st2 (Tc m) = st (Tc m) := by
      intro m hm
      rw [hagree _ (by have := hTcle m hm; omega), hst1, concat_le st g1 (hTcle m hm)]
    have hst2y : st2 (e + k) = y := by rw [hagree _ le_rfl, hst1y]
    refine ⟨st2, fun m => if m ≤ M then Tc m else e + k, e2, ?_, ?_, htr2, ?_, ?_, ?_, ?_, ?_,
      fun h => absurd h (by omega), ?_⟩
    · rw [hagree 0 (by omega), hst1, concat_le st g1 (Nat.zero_le _), hst0]
    · simp [hTc0]
    · intro m hm
      by_cases hm' : m + 1 ≤ M
      · simp only [hm', show m ≤ M by omega, if_true]; exact hmono m (by omega)
      · have hmM : m = M := by omega
        subst hmM
        simp only [le_refl, if_true, hm', if_false]
        exact le_trans hTcM (Nat.le_add_right _ _)
    · simp only [show ¬ M + 1 ≤ M by omega, if_false]; exact hle2
    · intro m h1 h2
      by_cases hm' : m ≤ M
      · simp only [hm', if_true]
        rw [hst2old m hm']
        exact hchk m h1 hm'
      · have hmM : m = M + 1 := by omega
        subst hmM
        simp only [hm', if_false]
        rw [hst2y]
        exact ⟨hrp, hfr⟩
    · intro m h1 h2
      by_cases hm' : m + 1 ≤ M
      · simp only [hm', show m ≤ M by omega, if_true]
        exact hcost m h1 (by omega)
      · have hmM : m = M := by omega
        subst hmM
        simp only [le_refl, if_true, hm', if_false]
        obtain ⟨L1, hcr1⟩ := hpend h1
        have hall := costedRun_trans hcr1 hcr
        have hTm := hTcle m le_rfl
        obtain ⟨hrp0, hfr0⟩ := hchk m h1 le_rfl
        have hc' : CostedRun (st (Tc m)).vm y.vm (e + k - Tc m) (L1 ++ L2) := by
          rw [show e + k - Tc m = e - Tc m + k by omega]; exact hall
        exact interval_cost_of_costedRun h1 hrp0 hfr0 hrp hfr hc'
    · intro hlt
      obtain ⟨c'', r'', h1, h2, h3, L, h4⟩ := hres2 hlt
      refine ⟨c'', r'', h1, h2, h3, fun _ => ⟨L, ?_⟩⟩
      simp only [show ¬ M + 1 ≤ M by omega, if_false]
      rw [hst2y]
      exact h4
    · intro _
      by_cases hM0 : M = 0
      · subst hM0
        obtain ⟨hk, he⟩ := hk0 rfl
        simp only [show ¬ (1 ≤ 0) by omega, if_false]
        omega
      · simp only [show 1 ≤ M by omega, if_true]
        exact hone (by omega)

/-! ## The strengthened pre-loaded trace -/

/-- `PreTrace` plus: the first checkpoint is the boot landing. -/
structure PreTraceB (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) :
    Prop where
  pre : PreTrace centre place entry q first w st Tc
  tc1 : Tc 1 = 1

/-- **Adapter oracle → strengthened pre-loaded trace.** -/
theorem preTraceB_exists (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (w : List (Fin 2)) (hw : 0 < w.length)
    (hor : CycleOracleMC (PofC centre place entry w) q first w) :
    ∃ st Tc, PreTraceB centre place entry q first w st Tc := by
  rcases w with _ | ⟨a, rest⟩
  · simp at hw
  · obtain ⟨c1, t, hst, hI, hpos⟩ :=
      inv_init_pos (onLetterVM (a :: rest)) leftFirstVM centre place entry q first
        (GalilBootVM.initVM0 (a :: rest)) a rest
        (GalilBootVM.initVM0_right _) (GalilBootVM.initVM0_radius _)
        (GalilBootVM.initVM0_length _) (GalilBootVM.initVM0_replay _)
        (GalilBootVM.initVM0_shiftIdle _)
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, -, -, hone⟩ :=
      checkpoints_cost_upto1 (PofC centre place entry (a :: rest)) q first (a :: rest) hor hst
        (invL_of_run hst (invS_of_inv hI)) hpos (a :: rest).length le_rfl
    refine ⟨st, Tc, ⟨⟨hst0, hTc0, trace_le htr hTcM, mono_of_step Tc _ hmono, ?_, hcost⟩,
      hone (by simp)⟩⟩
    intro m h1 h2
    exact ledgerAt_of_prefix (hchk m h1 h2).1 (hchk m h1 h2).2

/-- **`O_base` discharged** on the strengthened trace. -/
theorem base_of_preTraceB {centre : GalilVM → Fin 3} {place : GalilVM → GalilScaffoldPlace.Place}
    {entry q : ℕ} {first : Fin 9} {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (h : PreTraceB centre place entry q first w st Tc) : Tc 1 ≤ 2050 := by
  rw [h.tc1]; omega

/-! ## `needLe` from a per-state bound -/

/-- The `pmax` bookkeeping: `needLe` is exactly a bound on the states up to the
checkpoint. -/
theorem needLe_of_usedLe (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (h : ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → usedVM w (st i).vm ≤ m+1) :
    ∀ m, m < w.length → ∀ k, k < Tc (m+1) → need w st k ≤ m+1 := by
  intro m hm k hk
  exact pmax_le _ _ (k+1) (fun i hi => h m hm i (by omega))

theorem mono_chain (f : ℕ → ℕ) (E : ℕ) (h : ∀ i, i < E → f i ≤ f (i+1)) :
    ∀ i j, i ≤ j → j ≤ E → f i ≤ f j := by
  intro i j hij hj
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact le_rfl
  | succ j ih =>
    by_cases hi : i ≤ j
    · exact le_trans (ih hi (by omega)) (h j (by omega))
    · have : i = j+1 := by omega
      subst this; exact le_rfl

/-- Optional split: monotone consumption along the trace plus the bound at the
checkpoints gives the per-state bound. -/
theorem usedLe_of_mono (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (hTc : ∀ m, m ≤ w.length → Tc m ≤ Tc w.length)
    (hmono : ∀ i, i < Tc w.length → usedVM w (st i).vm ≤ usedVM w (st (i+1)).vm)
    (hchk : ∀ m, 1 ≤ m → m ≤ w.length → usedVM w (st (Tc m)).vm ≤ m) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → usedVM w (st i).vm ≤ m+1 := by
  intro m hm i hi
  have h1 := mono_chain (fun i => usedVM w (st i).vm) (Tc w.length) hmono i (Tc (m+1)) hi
    (hTc (m+1) (by omega))
  have h2 := hchk (m+1) (by omega) (by omega)
  exact le_trans h1 h2

/-! ## The hypotheses on the strengthened trace -/

section Hyps
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

def H_truncTickB : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTraceB centre place entry q first w st Tc →
    TruncTick w st (Tc w.length) (galilFrameS (PofC centre place entry w) q first) 2048

def H_sufB : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTraceB centre place entry q first w st Tc →
    ∀ k, k ≤ Tc w.length → SufVM w (st k).vm

/-- The per-state consumption bound replacing `H_needLe`. -/
def H_usedLeB : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTraceB centre place entry q first w st Tc →
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → usedVM w (st i).vm ≤ m+1

def H_realizeB : Prop :=
  ∃ (Q' Γ' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (_ : Fintype Γ') (_ : DecidableEq Γ')
    (t K : ℕ) (L : PalPeg.Local.LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q')
    (outQ : Q' → Bool) (n : ℕ) (htape : 0 < t) (hn : 0 < n),
    ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTraceB centre place entry q first w st Tc →
      ((L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn).SAccepts w ↔
        LatchTrue (PofC centre place entry w) q first w (stTG τF w st (Tc w.length))
          ((w.length + 1) * τF))

theorem truncTickB_of (h : H_truncTick centre place entry q first) :
    H_truncTickB centre place entry q first :=
  fun w hw st Tc hB => h w hw st Tc hB.pre

theorem sufB_of (h : H_suf centre place entry q first) : H_sufB centre place entry q first :=
  fun w hw st Tc hB => h w hw st Tc hB.pre

theorem realizeB_of (h : H_realize centre place entry q first) :
    H_realizeB centre place entry q first := by
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hr⟩ := h
  exact ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn,
    fun w hw st Tc hB => hr w hw st Tc hB.pre⟩

end Hyps

/-! ## The final theorem, `H_base` discharged -/

theorem pal_in_peg_final' (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9)
    (hA : H_oracle centre place entry q first)
    (hB_trunc : H_truncTickB centre place entry q first)
    (hB_suf : H_sufB centre place entry q first)
    (hB_used : H_usedLeB centre place entry q first)
    (hC : H_realizeB centre place entry q first) :
    RecognizedByTotalPEG PAL := by
  classical
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := hC
  have key : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceB centre place entry q first w st Tc := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨st, Tc, h⟩ := preTraceB_exists centre place entry q first w hw (hA w hw)
      exact ⟨st, Tc, fun _ => h⟩
    · exact ⟨fun _ => boot w, fun _ => 0, fun h => absurd h hw⟩
  choose stP TcP hP using key
  let M := L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn
  have hpre : ∀ w : List (Fin 2), 0 < w.length → Preload w (stP w) (TcP w) :=
    fun w hw => preload_of_preTrace (hP w hw).pre
      (needLe_of_usedLe w (stP w) (TcP w) (hB_used w hw _ _ (hP w hw)))
  refine pal_in_peg_of_latch' (Nat.mul_pos hn (PalPeg.Local.cnt_pos K)) M
    (PofC centre place entry) (fun _ => q) (fun _ => first) 2048
    (fun w => PofC_onLetter centre place entry w) (fun w => PofC_leftFirst centre place entry w)
    (fun w => stTG τF w (stP w) (TcP w w.length))
    (fun w => arrTG τF w (stP w) (TcP w w.length))
    (fun w => (w.length + 1) * τF) ?_ ?_ ?_ ?_
  · intro w hw
    have h := (hP w hw).pre
    exact abstractRun_throttled_2p18 w (stP w) (TcP w w.length) (PofC centre place entry w) q
      first 2048 (by rw [h.start]; rfl) (needS_boot w (stP w) h.start)
      (hB_suf w hw _ _ (hP w hw)) (hB_trunc w hw _ _ (hP w hw))
  · intro w hw
    exact hreal w hw _ _ (hP w hw)
  · exact ledger_throttled_2p18 (PofC centre place entry) (fun _ => q) (fun _ => first) stP TcP
      hpre (fun w hw => (hP w hw).pre.report w.length (by omega) le_rfl)
      (fun w hw => base_of_preTraceB (hP w hw))
      (fun w hw => (hP w hw).pre.cost)
  · exact GalilEmptyWord.realize_accept'_nil L blank initQ outQ n htape hn

#print axioms costedRun_zero
#print axioms checkpoints_cost_upto1
#print axioms preTraceB_exists
#print axioms base_of_preTraceB
#print axioms needLe_of_usedLe
#print axioms mono_chain
#print axioms usedLe_of_mono
#print axioms truncTickB_of
#print axioms sufB_of
#print axioms realizeB_of
#print axioms pal_in_peg_final'

/-! ## The lookahead-need target of `GalilTruncTick` -/

/-- The pointwise `needL` bound that `GalilTruncTick.needLe_of_pointwise` consumes. -/
def H_needLB (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTraceB centre place entry q first w st Tc →
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → PalPeg.GalilTruncTick.needL w st i ≤ m+1

/-- `needL` splits into consumption and lookahead. -/
theorem needL_le_of (w : List (Fin 2)) (st : ℕ → State GalilVM) (i b : ℕ)
    (hu : usedVM w (st i).vm ≤ b) (hl : PalPeg.GalilTruncTick.look w (st i) ≤ b) :
    PalPeg.GalilTruncTick.needL w st i ≤ b :=
  max_le hu hl

/-- With consumption one below the target, the lookahead is free (`look_le_succ`). -/
theorem needL_le_of_used (w : List (Fin 2)) (st : ℕ → State GalilVM) (i m : ℕ)
    (hu : usedVM w (st i).vm ≤ m) : PalPeg.GalilTruncTick.needL w st i ≤ m+1 :=
  needL_le_of w st i (m+1) (by omega)
    (le_trans (PalPeg.GalilTruncTick.look_le_succ w (st i)) (by omega))

/-- The `PreloadL` record from a strengthened trace and the pointwise bound. -/
theorem preloadL_of_preTraceB {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (h : PreTraceB centre place entry q first w st Tc)
    (h0 : PalPeg.GalilTruncTick.needL w st 0 = 0)
    (hn : ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → PalPeg.GalilTruncTick.needL w st i ≤ m+1) :
    PalPeg.GalilTruncTick.PreloadL w st Tc :=
  ⟨h.pre.tc0, fun m hm => h.pre.mono m (m+1) (by omega) hm, h0,
    PalPeg.GalilTruncTick.needLe_of_pointwise w st Tc hn⟩

/-- **Base interval of the `dwT` ledger** (`O_cost` at `m = 0` of `ledger_throttledL`):
with `Tc 1 = 1`, `dwT Tc 1 = 3 ≤ beta' 2048`. -/
theorem dwT_one_of_preTraceB {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (h : PreTraceB centre place entry q first w st Tc) :
    dwT Tc (0+1) ≤ alpha' 2048 * (Cw w (0+1) - Cw w 0) + beta' 2048 := by
  have e : dwT Tc (0+1) = 3 := by simp [dwT, h.tc1, h.pre.tc0]
  rw [e, beta'_2048]; omega

#print axioms needL_le_of
#print axioms needL_le_of_used
#print axioms preloadL_of_preTraceB
#print axioms dwT_one_of_preTraceB

end PalPeg.GalilFinalBaseNeed
