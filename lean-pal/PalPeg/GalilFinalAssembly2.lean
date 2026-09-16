import PalPeg.GalilFinalAssembly
import PalPeg.GalilTruncTick
import PalPeg.GalilThrottledRunGen
import PalPeg.GalilLedgerThrottled

/-!
# Final assembly, with `TruncTick` / `SufVM` discharged

`GalilTruncTick` proves `TruncTick` and `SufVM` away for the lookahead-throttled
schedule (need `needT`), but at the fixed spacing `GalilLedgerAssembly.τ = 2^17`.
Here

1. the lookahead-throttled run is restated generic in `τ` on top of
   `GalilThrottledRunGen.cfgG` with `nd := needT`, and instantiated at
   `ticksPerSymbol = 2^18` (`abstractRun_throttledL_2p18`, `ledger_throttledL_2p18`);
2. `pal_in_peg_final2_gen` replaces (B) of `GalilFinalAssembly.pal_in_peg_final` by
   `H_centrePlace` (truncation-invariance of `centre`/`place`), `H_needL` (the
   pointwise premise of `needLe_of_pointwise`) and `H_base`;
3. concrete `centreC`/`placeC` (read off the centre head's focus, left stack and gap)
   satisfy `H_centrePlace` and `Decodes`, giving `pal_in_peg_final2` with (B) reduced
   to `H_needL` and `H_base`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PalPeg.GalilFinalAssembly2

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilTickArrive PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.GalilThrottledRun PalPeg.GalilThrottledRunGen PalPeg.GalilLedgerQ64
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilTruncTick PalPeg.GalilFinalAssembly

/-! ## 1. The lookahead-throttled run, generic in `τ` -/

section Run
variable (τ : ℕ) (raw : List (Fin 2)) (st : ℕ → State GalilVM) (e : ℕ)

abbrev cfgLG (t : ℕ) : Cfg := cfgG τ raw.length e (needT raw st) t

def stLG (t : ℕ) : State GalilVM :=
  truncS (raw.length - (cfgLG τ raw st e t).j) (st (cfgLG τ raw st e t).k)

def arrLG (t : ℕ) : ℕ := (cfgLG τ raw st e t).j

/-- **`AbstractRun'` for the τ-spaced lookahead-throttled run** (no `TruncTick`,
no `SufVM` hypothesis). -/
theorem abstractRun_throttledLG (hτ : 2 ≤ τ) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hP : ∀ j, SharedTrunc raw j P) (hS : SharedSuf raw P)
    (hctl : (st 0).ctl = GalilScaffoldController.initial delay)
    (h0 : needL raw st 0 = 0) (hsuf0 : SufVM raw (st 0).vm)
    (htick : ∀ k, k < e → Tick (galilFrameS P q first) delay (st k) (st (k+1))) :
    AbstractRun' P q first delay raw (stLG τ raw st e) (arrLG τ raw st e) := by
  have hsuf := sufVM_trace raw st e hS q first delay htick hsuf0
  refine ⟨hctl, rfl, fun t => ?_⟩
  have hused := cfgG_used τ raw.length e (needT raw st) (needL raw st) h0
    (fun k i hi => needL_le_needT raw st hi) t
  obtain ⟨-, hke, -, -⟩ := cfgG_inv τ hτ raw.length e (needT raw st) t
  rcases cfgG_succ_cases τ raw.length e (needT raw st) t with
    ⟨h1, _, h3⟩ | ⟨_, h2, h3, h4⟩ | ⟨_, _, h3⟩
  · refine Or.inr ⟨by simp only [arrLG, cfgLG, h3], raw[(cfgLG τ raw st e t).j], ?_, ?_⟩
    · exact List.getElem?_eq_getElem h1
    · simp only [stLG, cfgLG, h3]
      exact (arrive_trunc raw _ h1 _ (hsuf _ hke)
        (le_trans (needS_le_needL raw st _) (hused _ le_rfl))).symm
  · refine Or.inl ⟨by simp only [arrLG, cfgLG, h4], Or.inl ?_⟩
    simp only [stLG, cfgLG, h4]
    have hA : needL raw st (cfgLG τ raw st e t).k ≤ (cfgLG τ raw st e t).j := hused _ le_rfl
    have hB : needL raw st ((cfgLG τ raw st e t).k + 1) ≤ (cfgLG τ raw st e t).j :=
      le_trans (needL_le_needT raw st le_rfl) h3
    exact tick_trunc raw _ (hP _) q first delay (htick _ h2)
      (le_trans (needS_le_needL raw st _) hA) (le_trans (needS_le_needL raw st _) hB)
      (le_trans (le_max_right _ _) hA)
  · refine Or.inl ⟨by simp only [arrLG, cfgLG, h3], Or.inr ?_⟩
    simp only [stLG, cfgLG, h3]

open Classical in
noncomputable def TcLG (Tc : ℕ → ℕ) (m : ℕ) : ℕ :=
  if h : ∃ t, Tc m ≤ (cfgLG τ raw st e t).k then Nat.find h else 0

theorem TcLG_spec (Tc : ℕ → ℕ) (m : ℕ) (h : ∃ t, Tc m ≤ (cfgLG τ raw st e t).k) :
    Tc m ≤ (cfgLG τ raw st e (TcLG τ raw st e Tc m)).k ∧
      ∀ t, Tc m ≤ (cfgLG τ raw st e t).k → TcLG τ raw st e Tc m ≤ t := by
  unfold TcLG
  rw [dif_pos h]
  exact ⟨Nat.find_spec h, fun t ht => Nat.find_min' h ht⟩

theorem TcLG_exact (Tc : ℕ → ℕ) (m : ℕ) (h : ∃ t, Tc m ≤ (cfgLG τ raw st e t).k) :
    (cfgLG τ raw st e (TcLG τ raw st e Tc m)).k = Tc m := by
  obtain ⟨h1, h2⟩ := TcLG_spec τ raw st e Tc m h
  refine le_antisymm ?_ h1
  rcases hT : TcLG τ raw st e Tc m with _ | t'
  · simp [cfgLG, cfgG]
  · have hlt : ¬ Tc m ≤ (cfgLG τ raw st e t').k := fun hc => by
      have := h2 t' hc; omega
    have := (cfgG_mono τ raw.length e (needT raw st) t').2.1
    simp only [cfgLG] at hlt this ⊢
    omega

theorem TcLG_exists (hτ : 2 ≤ τ) {Tc : ℕ → ℕ} (hp : PreloadL raw st Tc) :
    ∀ m, m ≤ raw.length →
      ∃ t, Tc m ≤ (cfgG τ raw.length (Tc raw.length) (needT raw st) t).k := by
  intro m
  induction m with
  | zero => intro _; exact ⟨0, by rw [hp.tc0]; exact Nat.zero_le _⟩
  | succ m ih =>
    intro hm
    obtain ⟨hK, -⟩ := TcLG_spec τ raw st (Tc raw.length) Tc m (ih (by omega))
    exact ⟨_, ostepG τ hτ raw.length _ (needT raw st) Tc m hm (hp.mono m hm)
      (GalilCheckpoints.mono_of_step Tc raw.length hp.mono (m+1) raw.length hm le_rfl)
      (hp.needLe m hm) _ hK⟩

theorem TcLG_zero (hτ : 2 ≤ τ) {Tc : ℕ → ℕ} (hp : PreloadL raw st Tc) :
    TcLG τ raw st (Tc raw.length) Tc 0 = 0 := by
  have h := TcLG_exists τ raw st hτ hp 0 (Nat.zero_le _)
  have := (TcLG_spec τ raw st _ Tc 0 h).2 0 (by rw [hp.tc0]; exact Nat.zero_le _)
  omega

theorem O_step_throttledLG (hτ : 2 ≤ τ) {Tc : ℕ → ℕ} (hp : PreloadL raw st Tc) (m : ℕ)
    (hm : m < raw.length) :
    TcLG τ raw st (Tc raw.length) Tc (m+1) ≤
      max (TcLG τ raw st (Tc raw.length) Tc m) ((m+1) * τ) + dwT Tc (m+1) := by
  obtain ⟨hK, -⟩ := TcLG_spec τ raw st (Tc raw.length) Tc m (TcLG_exists τ raw st hτ hp m hm.le)
  have ho := ostepG τ hτ raw.length _ (needT raw st) Tc m hm (hp.mono m hm)
    (GalilCheckpoints.mono_of_step Tc raw.length hp.mono (m+1) raw.length hm le_rfl)
    (hp.needLe m hm) _ hK
  have := (TcLG_spec τ raw st (Tc raw.length) Tc (m+1)
    (TcLG_exists τ raw st hτ hp (m+1) hm)).2 _ ho
  simpa [dwT] using this

theorem stLG_at_end (hτ : 2 ≤ τ) {Tc : ℕ → ℕ} (hp : PreloadL raw st Tc) (hn : 0 < raw.length)
    {P : Shared} {q : ℕ} {first : Fin 9}
    (hrep : GalilLedgerAssembly.ReportPointAt P q first raw raw.length (st (Tc raw.length))) :
    stLG τ raw st (Tc raw.length) (TcLG τ raw st (Tc raw.length) Tc raw.length) =
      st (Tc raw.length) := by
  have hex := TcLG_exists τ raw st hτ hp raw.length le_rfl
  have hk := TcLG_exact τ raw st (Tc raw.length) Tc raw.length hex
  have hused := cfgG_used τ raw.length (Tc raw.length) (needT raw st) (needL raw st) hp.need0
    (fun k i hi => needL_le_needT raw st hi) (TcLG τ raw st (Tc raw.length) Tc raw.length)
    (Tc raw.length) (by simp only [cfgLG] at hk; omega)
  have hu := used_of_report raw hn hrep
  have hS := needS_le_needL raw st (Tc raw.length)
  obtain ⟨i1, -, -, -⟩ := cfgG_inv τ hτ raw.length (Tc raw.length) (needT raw st)
    (TcLG τ raw st (Tc raw.length) Tc raw.length)
  have hjn : (cfgLG τ raw st (Tc raw.length)
      (TcLG τ raw st (Tc raw.length) Tc raw.length)).j = raw.length := by
    simp only [cfgLG, needS] at hused i1 hS ⊢
    omega
  unfold stLG
  rw [hjn, hk, Nat.sub_self, truncS_zero]

end Run

/-- Ledger obligation for the τ-spaced lookahead-throttled runs. -/
theorem ledger_throttledLG (τ : ℕ) (hτ2 : 2 ≤ τ) (α β : ℕ) (hτ : 2 * (α + β) ≤ τ)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (stOf : List (Fin 2) → ℕ → State GalilVM)
    (TcOf : List (Fin 2) → ℕ → ℕ)
    (hpre : ∀ w : List (Fin 2), 0 < w.length → PreloadL w (stOf w) (TcOf w))
    (hrep : ∀ w : List (Fin 2), 0 < w.length →
      GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w w.length
        (stOf w (TcOf w w.length)))
    (O_cost : ∀ w : List (Fin 2), 0 < w.length → ∀ m, m < w.length →
      dwT (TcOf w) (m+1) ≤ α * (Cw w (m+1) - Cw w m) + β) :
    LedgerObligation Pof qof firstOf
      (fun w => stLG τ w (stOf w) (TcOf w w.length))
      (fun w => (w.length + 1) * τ) := by
  intro w hw hpal
  have hp := hpre w hw
  have hz := GalilLedgerThrottled.backlog_zero_trunc' α β τ hτ w hw hpal (dwT (TcOf w))
    (O_cost w hw)
  have ht := GalilLedgerThrottled.on_time_trunc' α β τ hτ w (dwT (TcOf w))
    (TcLG τ w (stOf w) (TcOf w w.length) (TcOf w)) (TcLG_zero τ w (stOf w) hτ2 hp)
    (O_step_throttledLG τ w (stOf w) hτ2 hp) hz
  obtain ⟨hrp, hfr⟩ := GalilLedgerAssembly.reportPoint_of_at_length hw (hrep w hw)
  refine ⟨TcLG τ w (stOf w) (TcOf w w.length) (TcOf w) w.length, ht, ?_, ?_⟩
  · show ReportPoint w (stLG τ w (stOf w) (TcOf w w.length) _)
    rw [stLG_at_end τ w (stOf w) hτ2 hp hw (hrep w hw)]; exact hrp
  · show Refreshed _ _ _ (stLG τ w (stOf w) (TcOf w w.length) _)
    rw [stLG_at_end τ w (stOf w) hτ2 hp hw (hrep w hw)]; exact hfr

/-- **`AbstractRun'` for the lookahead-throttled run with arrivals `2^18` apart.** -/
theorem abstractRun_throttledL_2p18 (raw : List (Fin 2)) (st : ℕ → State GalilVM) (e : ℕ)
    (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hP : ∀ j, SharedTrunc raw j P) (hS : SharedSuf raw P)
    (hctl : (st 0).ctl = GalilScaffoldController.initial delay)
    (h0 : needL raw st 0 = 0) (hsuf0 : SufVM raw (st 0).vm)
    (htick : ∀ k, k < e → Tick (galilFrameS P q first) delay (st k) (st (k+1))) :
    AbstractRun' P q first delay raw (stLG GalilLedgerThrottled.ticksPerSymbol raw st e)
      (arrLG GalilLedgerThrottled.ticksPerSymbol raw st e) :=
  abstractRun_throttledLG _ raw st e two_le_ticksPerSymbol P q first delay hP hS hctl h0 hsuf0 htick

/-- **Ledger obligation, lookahead need, run spacing = deadline slope = `2^18`.** -/
theorem ledger_throttledL_2p18 (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (stOf : List (Fin 2) → ℕ → State GalilVM)
    (TcOf : List (Fin 2) → ℕ → ℕ)
    (hpre : ∀ w : List (Fin 2), 0 < w.length → PreloadL w (stOf w) (TcOf w))
    (hrep : ∀ w : List (Fin 2), 0 < w.length →
      GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w w.length
        (stOf w (TcOf w w.length)))
    (O_base : ∀ w : List (Fin 2), 0 < w.length → TcOf w 1 ≤ 2050)
    (O_cost : ∀ w : List (Fin 2), 0 < w.length → ∀ m, 1 ≤ m → m < w.length →
      TcOf w (m+1) - TcOf w m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048) :
    LedgerObligation Pof qof firstOf
      (fun w => stLG GalilLedgerThrottled.ticksPerSymbol w (stOf w) (TcOf w w.length))
      (fun w => (w.length + 1) * GalilLedgerThrottled.ticksPerSymbol) := by
  have hτ : 2 * (2 * alpha' 2048 + (2 * beta' 2048 + 1)) ≤ GalilLedgerThrottled.ticksPerSymbol := by
    have := GalilLedgerThrottled.two_c2_le_τ'
    unfold GalilLedgerThrottled.c2 at this
    exact this.trans_eq' (by ring)
  exact ledger_throttledLG _ two_le_ticksPerSymbol _ _ hτ Pof qof firstOf stOf TcOf hpre hrep
    (fun w hw m hm => GalilLedgerThrottled.dwT_cost w (TcOf w) (hpre w hw).tc0 (O_base w hw)
      (O_cost w hw) m hm)

/-! ## 2. Boot-state facts -/

theorem sufVM_boot (w : List (Fin 2)) : SufVM w (boot w).vm := by
  have h : SufPH w (initialHead w) := ⟨0, by simp [initialHead]⟩
  exact ⟨h, h, h, fun p hp => by cases hp⟩

theorem needL_boot (w : List (Fin 2)) (st : ℕ → State GalilVM) (h : st 0 = boot w) :
    needL w st 0 = 0 := by
  have h1 := needS_boot w st h
  have h2 : look w (st 0) = 0 := by
    unfold look
    rw [if_neg]
    rw [h]; simp [boot, GalilScaffoldController.initial]
  simp [needL, h1, h2]

/-! ## 3. The hypotheses -/

section Hyps
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- (B') `centre`/`place` do not look at the incoming FIFOs. -/
def H_centrePlace : Prop :=
  ∀ (w : List (Fin 2)) (j : ℕ) (s : GalilVM),
    centre (truncVM (w.length - j) s) = centre s ∧ place (truncVM (w.length - j) s) = place s

/-- (B') Pointwise lookahead need bound (premise of `needLe_of_pointwise`). -/
def H_needL : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → needL w st i ≤ m+1

/-- (C) Realization, now over the `2^18`-spaced lookahead-throttled run. -/
def H_realizeL : Prop :=
  ∃ (Q' Γ' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (_ : Fintype Γ') (_ : DecidableEq Γ')
    (t K : ℕ) (L : PalPeg.Local.LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q')
    (outQ : Q' → Bool) (n : ℕ) (htape : 0 < t) (hn : 0 < n),
    ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
      ((L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn).SAccepts w ↔
        LatchTrue (PofC centre place entry w) q first w (stLG τF w st (Tc w.length))
          ((w.length + 1) * τF))

end Hyps

/-! ## 4. The final theorem, generic `centre`/`place` -/

theorem pal_in_peg_final2_gen (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9)
    (hA : H_oracle centre place entry q first)
    (hCP : H_centrePlace centre place)
    (hB_need : H_needL centre place entry q first)
    (hB_base : H_base centre place entry q first)
    (hC : H_realizeL centre place entry q first) :
    RecognizedByTotalPEG PAL := by
  classical
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := hC
  have key : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTrace centre place entry q first w st Tc := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨st, Tc, h⟩ := preTrace_exists centre place entry q first w hw (hA w hw)
      exact ⟨st, Tc, fun _ => h⟩
    · exact ⟨fun _ => boot w, fun _ => 0, fun h => absurd h hw⟩
  choose stP TcP hP using key
  let M := L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn
  have hpre : ∀ w : List (Fin 2), 0 < w.length → PreloadL w (stP w) (TcP w) := by
    intro w hw
    have h := hP w hw
    exact ⟨h.tc0, fun m hm => h.mono m (m+1) (by omega) hm, needL_boot w (stP w) h.start,
      needLe_of_pointwise w (stP w) (TcP w) (hB_need w hw _ _ h)⟩
  refine pal_in_peg_of_latch' (Nat.mul_pos hn (PalPeg.Local.cnt_pos K)) M
    (PofC centre place entry) (fun _ => q) (fun _ => first) 2048
    (fun w => PofC_onLetter centre place entry w) (fun w => PofC_leftFirst centre place entry w)
    (fun w => stLG τF w (stP w) (TcP w w.length))
    (fun w => arrLG τF w (stP w) (TcP w w.length))
    (fun w => (w.length + 1) * τF) ?_ ?_ ?_ ?_
  · intro w hw
    have h := hP w hw
    exact abstractRun_throttledL_2p18 w (stP w) (TcP w w.length) (PofC centre place entry w) q
      first 2048
      (fun j => sharedC_trunc_vm w j centre place entry (fun s => (hCP w j s).1)
        (fun s => (hCP w j s).2))
      (sharedC_suf w _ _ centre place entry)
      (by rw [h.start]; rfl) (needL_boot w (stP w) h.start)
      (by rw [h.start]; exact sufVM_boot w) h.trace.tick
  · intro w hw
    exact hreal w hw _ _ (hP w hw)
  · exact ledger_throttledL_2p18 (PofC centre place entry) (fun _ => q) (fun _ => first) stP TcP
      hpre (fun w hw => (hP w hw).report w.length (by omega) le_rfl)
      (fun w hw => hB_base w hw _ _ (hP w hw))
      (fun w hw => (hP w hw).cost)
  · exact GalilEmptyWord.realize_accept'_nil L blank initQ outQ n htape hn

/-! ## 5. Concrete `centre`/`place` -/

/-- The letters of a place head: the focus followed by the left stack (the `none`
sentinel dropped). -/
def lettersOf (h : GalilScaffoldInputHead.Head) : List (Fin 2) :=
  match h.focus with
  | none => []
  | some a => a :: h.left.filterMap id

/-- The concrete place: read off the centre head (focus, left stack, gap). -/
def placeC (s : GalilVM) : GalilScaffoldPlace.Place := ⟨lettersOf s.center.head, s.center.gap⟩

/-- The concrete centre symbol: the read of the centre head (`0` on the sentinel). -/
def centreC (s : GalilVM) : Fin 3 := (GalilScaffoldInputHead.read s.center).getD 0

theorem centrePlaceC : H_centrePlace centreC placeC := fun _ _ _ => ⟨rfl, rfl⟩

theorem decodesC (entry : ℕ) (w : List (Fin 2)) : Decodes (PofC centreC placeC entry w) := by
  refine ⟨fun u a ls rs q gap hu => ?_, fun u v h => ?_⟩
  · have hr := GalilScaffoldInputHead.read_represent ⟨a :: ls, gap⟩ (rs.map some) q
    have hc : GalilScaffoldInputHead.read u.center = GalilScaffoldPlace.read ⟨a :: ls, gap⟩ := by
      rw [hu, hr]
    refine ⟨?_, ?_⟩
    · show _ = some ((GalilScaffoldInputHead.read u.center).getD 0)
      rw [hc]; rfl
    · show placeC u = _
      simp [placeC, hu, lettersOf, GalilScaffoldInputHead.represent, GalilScaffoldInputHead.layout,
        List.filterMap_append, List.filterMap_map]
  · show placeC u = placeC v
    simp [placeC, h]

/-- **`PAL ∈ PEG` with concrete `centre`/`place`**: (B) is down to `H_needL` and `H_base`. -/
theorem pal_in_peg_final2 (entry q : ℕ) (first : Fin 9)
    (hA : H_oracle centreC placeC entry q first)
    (hB_need : H_needL centreC placeC entry q first)
    (hB_base : H_base centreC placeC entry q first)
    (hC : H_realizeL centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final2_gen centreC placeC entry q first hA centrePlaceC hB_need hB_base hC

#print axioms abstractRun_throttledLG
#print axioms ledger_throttledLG
#print axioms abstractRun_throttledL_2p18
#print axioms ledger_throttledL_2p18
#print axioms decodesC
#print axioms pal_in_peg_final2_gen
#print axioms pal_in_peg_final2

end PalPeg.GalilFinalAssembly2
