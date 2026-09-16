import PalPeg.GalilCheckpoints
import PalPeg.GalilIntervalCost
import PalPeg.GalilOracleM

/-!
# (O-cost) along the pre-loaded checkpoint trace

`GalilCheckpoints.checkpoints_upto` concatenates the runs handed out by
`CycleOracleM` into one trace with checkpoint times `Tc`.  Here the oracle is
strengthened with cost data and the tick count between two consecutive
checkpoints is bounded by `interval_cost_report`.

* `Piece` — the cost record of one place-tagged part of a run: shifts, at most
  one fallback (with its replay), a wait `≤ 2048` and a flag `cmp` for the one
  comparison tick.  A piece without a comparison has no wait.
* `CostedRun r0 r1 k L` — a run `r0 ⇝ r1` of `k` ticks decomposed into the
  pieces `L`, with the **grouping facts** as fields:
  - `places`: every piece's place lies in `(right r0, right r1]`;
  - `sep`: comparison pieces have strictly increasing places, and so have
    fallback pieces (in run order);
  - `centre`: the centre advance is the sum of the pieces' advances;
  - `right_mono`: the right head does not go back over the whole run.
* `CycleOracleMC` — `CycleOracleM` whose every exit (cycle, report segment,
  resume continuation) carries a `CostedRun`.
* `costedRun_trans` — costed runs concatenate (this is where `places` + `sep`
  give global separation across cycles).
* `interval_cost_of_costedRun` — a costed run between the report points `m`
  and `m+1` (right heads `2m-1`, `2m+1`) has all places in `{2m, 2m+1}`;
  grouping the pieces by place gives two `PlaceEvent`s with
  `AtMostOneFallback`, and `interval_cost_report` applies.
* `checkpoints_cost` — the checkpoint trace with the cost bound for every
  `1 ≤ m < |raw|`.
-/

set_option autoImplicit false

namespace PalPeg.GalilTraceCost

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge
open PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints
open PalPeg.GalilIntervalCost PalPeg.GalilLedgerQ64 PalPeg.GalilLedgerAssembly

/-! ## Pieces -/

/-- The cost record of one place-tagged part of a run. -/
structure Piece where
  place : ℕ
  shifts : List ShiftEv
  fallbacks : List (FallbackEv 2048)
  wait : ℕ
  cmp : Bool
  wait_le : wait ≤ 2048
  wait_cmp : cmp = false → wait = 0
  fb_le : fallbacks.length ≤ 1

namespace Piece

def ev (p : Piece) : PlaceEvent 2048 := ⟨p.shifts, p.fallbacks, p.wait, p.wait_le⟩
def cmpN (p : Piece) : ℕ := if p.cmp then 1 else 0
def ticks (p : Piece) : ℕ := p.ev.slot + p.wait + p.cmpN
def adv (p : Piece) : ℕ := p.ev.adv

end Piece

/-- Separation of two pieces in run order. -/
def Sep (a b : Piece) : Prop :=
  (a.cmp = true → b.cmp = true → a.place < b.place) ∧
  (0 < a.fallbacks.length → 0 < b.fallbacks.length → a.place < b.place)

/-- A run `r0 ⇝ r1` of `k` ticks decomposed into place-tagged pieces. -/
structure CostedRun (r0 r1 : GalilVM) (k : ℕ) (L : List Piece) : Prop where
  ticks : (L.map Piece.ticks).sum = k
  centre : position r1.center = position r0.center + (L.map Piece.adv).sum
  right_mono : position r0.right ≤ position r1.right
  places : ∀ p ∈ L, position r0.right < p.place ∧ p.place ≤ position r1.right
  sep : L.Pairwise Sep

theorem costedRun_trans {a b c : GalilVM} {k1 k2 : ℕ} {L1 L2 : List Piece}
    (h1 : CostedRun a b k1 L1) (h2 : CostedRun b c k2 L2) :
    CostedRun a c (k1 + k2) (L1 ++ L2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.map_append, List.sum_append, h1.ticks, h2.ticks]
  · rw [h2.centre, h1.centre, List.map_append, List.sum_append]; omega
  · exact le_trans h1.right_mono h2.right_mono
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · have := h1.places p hp; have := h2.right_mono; omega
    · have := h2.places p hp; have := h1.right_mono; omega
  · refine List.pairwise_append.2 ⟨h1.sep, h2.sep, fun x hx y hy => ?_⟩
    have := (h1.places x hx).2
    have := (h2.places y hy).1
    exact ⟨fun _ _ => by omega, fun _ _ => by omega⟩

theorem costedRun_nil (r : GalilVM) : CostedRun r r 0 [] :=
  ⟨rfl, by simp, le_rfl, fun _ h => absurd h (List.not_mem_nil), List.Pairwise.nil⟩

/-! ## The costed oracle -/

/-- `ReachAt` with cost data on the report segment and on the resume continuation. -/
def ReachAtC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) : Prop :=
  ∃ (y : State GalilVM) (k : ℕ) (L : List Piece),
    StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ y ∧
    CostedRun r y.vm k L ∧
    PalPeg.GalilReportPrefix.ReportPointAt raw m y ∧ Refreshed P q first y ∧
    (m < raw.length → ∃ (c' : Control) (r' : GalilVM) (k' : ℕ) (L' : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k' y ⟨c', r'⟩ ∧
      CostedRun y.vm r' k' L' ∧
      InvL raw c' r' ∧ position r'.right ≤ 2 * (m+1) - 1)

/-- `CycleOutM` with cost data. -/
def CycleOutMC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) : Prop :=
  ReachAtC P q first raw m c r ∨
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧
      InvL raw cT sT ∧ position r.center < position sT.center ∧
      position sT.right ≤ 2 * m - 1

/-- **The costed per-target cycle oracle.** -/
def CycleOracleMC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) : Prop :=
  ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ raw.length → InvL raw c r →
    position r.right ≤ 2 * m - 1 → CycleOutMC P q first raw m c r

theorem reachAt_of_C {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM} (h : ReachAtC P q first raw m c r) : ReachAt P q first raw m c r := by
  obtain ⟨y, k, _, hst, _, hrp, hfr, hcont⟩ := h
  refine ⟨y, k, hst, hrp, hfr, fun hlt => ?_⟩
  obtain ⟨c', r', k', _, hst', _, hI, hp⟩ := hcont hlt
  exact ⟨c', r', k', hst', hI, hp⟩

/-- Forgetting the cost data. -/
theorem cycleOracleM_of_C {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    (h : CycleOracleMC P q first raw) : CycleOracleM P q first raw := by
  intro m c r h1 h2 hI hp
  rcases h m c r h1 h2 hI hp with hr | ⟨cT, sT, k, _, hst, _, hIT, hlt, hpT⟩
  · exact Or.inl (reachAt_of_C hr)
  · exact Or.inr ⟨cT, sT, k, hst, hIT, hlt, hpT⟩

theorem reachC_fuel (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC P q first raw) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), 2 * raw.length - position r.center ≤ n →
      InvL raw c r → position r.right ≤ 2 * m - 1 → ReachAtC P q first raw m c r := by
  intro n
  induction n with
  | zero =>
    intro c r hn hI hp
    rcases hor m c r hm1 hmle hI hp with hdone | ⟨cT, sT, k, L, _, _, hIT, hlt, _⟩
    · exact hdone
    · exact absurd (invS_center_le hIT.1) (by have := invS_center_le hI.1; omega)
  | succ n ih =>
    intro c r hn hI hp
    rcases hor m c r hm1 hmle hI hp with hdone | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hpT⟩
    · exact hdone
    · obtain ⟨y, k', L', hst', hcr', hrp, hfr, hcont⟩ :=
        ih cT sT (by have := invS_center_le hIT.1; omega) hIT hpT
      exact ⟨y, k + k', L ++ L', stepsAll_trans hst hst', costedRun_trans hcr hcr', hrp, hfr, hcont⟩

theorem reachC_from_invL (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC P q first raw) {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c : Control} {r : GalilVM} (hI : InvL raw c r) (hp : position r.right ≤ 2 * m - 1) :
    ReachAtC P q first raw m c r :=
  reachC_fuel P q first raw hor m hm1 hmle _ c r le_rfl hI hp

/-! ## Grouping pieces by place -/

/-- The place event collecting a list of pieces (intended: all at one place). -/
def group (L : List Piece) : PlaceEvent 2048 :=
  ⟨(L.map Piece.shifts).flatten, (L.map Piece.fallbacks).flatten,
    min (L.map Piece.wait).sum 2048, min_le_right _ _⟩

theorem sum_flatten_map {α β : Type} (f : α → List β) (g : β → ℕ) :
    ∀ L : List α, (((L.map f).flatten).map g).sum = (L.map fun a => ((f a).map g).sum).sum := by
  intro L
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.flatten_cons, List.map_append, List.sum_append, List.sum_cons, ih]

theorem sum_map_add3 {α : Type} (f g h : α → ℕ) :
    ∀ L : List α, (L.map fun a => f a + g a + h a).sum =
      (L.map f).sum + (L.map g).sum + (L.map h).sum := by
  intro L
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem group_slot (L : List Piece) : (group L).slot = (L.map fun p => p.ev.slot).sum := by
  have e1 := sum_flatten_map Piece.shifts ShiftEv.ticks L
  have e2 := sum_flatten_map Piece.fallbacks FallbackEv.fb L
  have e3 := sum_flatten_map Piece.fallbacks FallbackEv.replay L
  have e4 := sum_map_add3 (fun p : Piece => (p.shifts.map ShiftEv.ticks).sum)
    (fun p : Piece => (p.fallbacks.map FallbackEv.fb).sum)
    (fun p : Piece => (p.fallbacks.map FallbackEv.replay).sum) L
  simp only [group, PlaceEvent.slot, PlaceEvent.shiftTicks, PlaceEvent.fbTicks,
    PlaceEvent.replayTicks, Piece.ev]
  rw [e1, e2, e3, ← e4]

theorem group_adv (L : List Piece) : (group L).adv = (L.map Piece.adv).sum := by
  have e1 := sum_flatten_map Piece.shifts ShiftEv.adv L
  have e2 := sum_flatten_map Piece.fallbacks FallbackEv.adv L
  have e4 : ∀ L : List Piece, (L.map fun p => (p.shifts.map ShiftEv.adv).sum +
      (p.fallbacks.map FallbackEv.adv).sum).sum =
      (L.map fun p => (p.shifts.map ShiftEv.adv).sum).sum +
      (L.map fun p => (p.fallbacks.map FallbackEv.adv).sum).sum := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  simp only [group, PlaceEvent.adv, PlaceEvent.shiftAdv, PlaceEvent.fbAdv]
  rw [e1, e2, ← e4]
  rfl

theorem group_fallbacks_length (L : List Piece) :
    (group L).fallbacks.length = (L.map fun p => p.fallbacks.length).sum := by
  simp only [group, List.length_flatten, List.map_map]
  rfl

theorem sum_zero_of_all {α : Type} (f : α → ℕ) :
    ∀ L : List α, (∀ x ∈ L, f x = 0) → (L.map f).sum = 0 := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons b L ihb =>
    intro h
    simp only [List.map_cons, List.sum_cons]
    rw [h b List.mem_cons_self, ihb (fun x hx => h x (List.mem_cons_of_mem b hx))]

/-- In a list where no two elements both satisfy `g`, a function vanishing off
`g` and bounded by `B` sums to at most `B`. -/
theorem sum_le_of_unique {α : Type} (g : α → Prop) (f : α → ℕ) (B : ℕ) :
    ∀ L : List α, L.Pairwise (fun a b => g a → g b → False) →
      (∀ x ∈ L, ¬ g x → f x = 0) → (∀ x ∈ L, f x ≤ B) → (L.map f).sum ≤ B := by
  intro L
  induction L with
  | nil => intro _ _ _; simp
  | cons a L ih =>
    intro hp h0 hB
    obtain ⟨ha, hL⟩ := List.pairwise_cons.1 hp
    have ih' := ih hL (fun x hx => h0 x (List.mem_cons_of_mem a hx))
      (fun x hx => hB x (List.mem_cons_of_mem a hx))
    simp only [List.map_cons, List.sum_cons]
    by_cases hga : g a
    · have hz : (L.map f).sum = 0 :=
        sum_zero_of_all f L (fun x hx => h0 x (List.mem_cons_of_mem a hx) (fun hgx => ha x hx hga hgx))
      have := hB a List.mem_cons_self
      omega
    · rw [h0 a List.mem_cons_self hga]; omega

/-- **Per-place cost.** Pieces all at one place `n`, separated in run order, cost
at most the ticks of their group event, which has at most one fallback. -/
theorem group_cost (n : ℕ) (L : List Piece) (hn : ∀ p ∈ L, p.place = n) (hsep : L.Pairwise Sep) :
    (L.map Piece.ticks).sum ≤ (group L).ticks ∧ (group L).AtMostOneFallback ∧
      (group L).adv = (L.map Piece.adv).sum := by
  have hcmp : L.Pairwise (fun a b => a.cmp = true → b.cmp = true → False) :=
    List.Pairwise.imp_of_mem (fun ha hb h h1 h2 => by
      have := h.1 h1 h2; rw [hn _ ha, hn _ hb] at this; omega) hsep
  have hfb : L.Pairwise (fun a b => 0 < a.fallbacks.length → 0 < b.fallbacks.length → False) :=
    List.Pairwise.imp_of_mem (fun ha hb h h1 h2 => by
      have := h.2 h1 h2; rw [hn _ ha, hn _ hb] at this; omega) hsep
  have hW : (L.map Piece.wait).sum ≤ 2048 :=
    sum_le_of_unique (fun a : Piece => a.cmp = true) Piece.wait 2048 L hcmp
      (fun x _ hx => x.wait_cmp (by simpa using hx)) (fun x _ => x.wait_le)
  have hC : (L.map Piece.cmpN).sum ≤ 1 :=
    sum_le_of_unique (fun a : Piece => a.cmp = true) Piece.cmpN 1 L hcmp
      (fun x _ hx => by simp [Piece.cmpN, hx]) (fun x _ => by unfold Piece.cmpN; split <;> omega)
  have hF : (L.map fun p => p.fallbacks.length).sum ≤ 1 :=
    sum_le_of_unique (fun a : Piece => 0 < a.fallbacks.length) (fun p => p.fallbacks.length) 1 L hfb
      (fun x _ hx => by omega) (fun x _ => x.fb_le)
  refine ⟨?_, ?_, group_adv L⟩
  · have e := sum_map_add3 (fun p : Piece => p.ev.slot) Piece.wait Piece.cmpN L
    have e' : (L.map Piece.ticks).sum = (L.map fun p => p.ev.slot + p.wait + p.cmpN).sum := rfl
    have hw : (group L).wait = (L.map Piece.wait).sum := by
      show min (L.map Piece.wait).sum 2048 = _
      omega
    unfold PlaceEvent.ticks
    rw [e', e, group_slot, hw]
    omega
  · unfold PlaceEvent.AtMostOneFallback
    rw [group_fallbacks_length]
    exact hF

/-- Splitting a sum over a list whose tags take two distinct values. -/
theorem sum_split (a b : ℕ) (hab : a ≠ b) (f : Piece → ℕ) :
    ∀ L : List Piece, (∀ p ∈ L, p.place = a ∨ p.place = b) →
      (L.map f).sum = ((L.filter fun p => decide (p.place = a)).map f).sum +
        ((L.filter fun p => decide (p.place = b)).map f).sum := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons x L ih =>
    intro h
    have ih' := ih (fun p hp => h p (List.mem_cons_of_mem x hp))
    rcases h x List.mem_cons_self with hx | hx
    · have hxb : ¬ x.place = b := by omega
      simp only [List.filter_cons, hx, decide_true, if_true, List.map_cons, List.sum_cons,
        show decide (a = b) = false from decide_eq_false hab, Bool.false_eq_true, if_false]
      omega
    · have hxa : ¬ x.place = a := by omega
      simp only [List.filter_cons, hx, decide_true, if_true, List.map_cons, List.sum_cons,
        show decide (b = a) = false from decide_eq_false (Ne.symm hab), Bool.false_eq_true,
        if_false]
      omega

/-! ## One interval -/

/-- **Interval cost from a costed run.** A costed run between the refreshed
report points `m` and `m+1` costs at most `alpha' 2048 · (Cw (m+1) − Cw m) + beta' 2048`. -/
theorem interval_cost_of_costedRun {P : Shared} {q : ℕ} {first : Fin 9} {w : List (Fin 2)} {m : ℕ}
    {y0 y1 : State GalilVM} (hm : 1 ≤ m)
    (r0 : PalPeg.GalilReportPrefix.ReportPointAt w m y0) (f0 : Refreshed P q first y0)
    (r1 : PalPeg.GalilReportPrefix.ReportPointAt w (m+1) y1) (f1 : Refreshed P q first y1)
    {D : ℕ} {L : List Piece} (hc : CostedRun y0.vm y1.vm D L) :
    D ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048 := by
  have p0 := r0.atPlace
  have p1 := r1.atPlace
  have hpl : ∀ p ∈ L, p.place = 2*m ∨ p.place = 2*m+1 := by
    intro p hp
    have := hc.places p hp
    omega
  have hab : 2*m ≠ 2*m+1 := by omega
  set La := L.filter fun p => decide (p.place = 2*m)
  set Lb := L.filter fun p => decide (p.place = 2*m+1)
  have hna : ∀ p ∈ La, p.place = 2*m := fun p hp => by
    simpa using (List.mem_filter.1 hp).2
  have hnb : ∀ p ∈ Lb, p.place = 2*m+1 := fun p hp => by
    simpa using (List.mem_filter.1 hp).2
  obtain ⟨ta, oa, aa⟩ := group_cost (2*m) La hna (hc.sep.sublist (List.filter_sublist))
  obtain ⟨tb, ob, ab⟩ := group_cost (2*m+1) Lb hnb (hc.sep.sublist (List.filter_sublist))
  have hT : (L.map Piece.ticks).sum = (La.map Piece.ticks).sum + (Lb.map Piece.ticks).sum :=
    sum_split (2*m) (2*m+1) hab Piece.ticks L hpl
  have hA : (L.map Piece.adv).sum = (La.map Piece.adv).sum + (Lb.map Piece.adv).sum :=
    sum_split (2*m) (2*m+1) hab Piece.adv L hpl
  have hD : D ≤ (group La).ticks + (group Lb).ticks := by
    rw [← hc.ticks, hT]; omega
  have hcen : position y1.vm.center = position y0.vm.center + (group La).adv + (group Lb).adv := by
    rw [hc.centre, hA, aa, ab]; omega
  have := interval_cost_report hm (ledgerAt_of_prefix r0 f0) (ledgerAt_of_prefix r1 f1)
    (group La) (group Lb) oa ob hcen _ rfl
  omega

/-! ## The checkpoint trace with costs -/

theorem checkpoints_cost_upto (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC P q first raw)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 x0 ⟨c, r⟩)
    (hI : InvL raw c r) (hpos : position r.right ≤ 1) :
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
        (1 ≤ M → ∃ L : List Piece, CostedRun (st (Tc M)).vm r' (e - Tc M) L)) := by
  intro M
  induction M with
  | zero =>
    intro _
    obtain ⟨g, hg0, hgn, htr⟩ := stepsAll_fn hpre
    refine ⟨g, fun _ => 0, k0, hg0, rfl, htr, fun m hm => absurd hm (Nat.not_lt_zero _),
      Nat.zero_le _, fun m h1 h2 => absurd h1 (by omega), fun m h1 h2 => absurd h2 (by omega),
      fun _ => ⟨c, r, hgn, hI, by omega, fun h => absurd h (by omega)⟩⟩
  | succ M ih =>
    intro hM
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, hres⟩ := ih (by omega)
    obtain ⟨c', r', hste, hI', hp', hpend⟩ := hres (by omega)
    obtain ⟨y, k, L2, hrun, hcr, hrp, hfr, hcont⟩ :=
      reachC_from_invL P q first raw hor (m := M+1) (by omega) hM hI' hp'
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
    refine ⟨st2, fun m => if m ≤ M then Tc m else e + k, e2, ?_, ?_, htr2, ?_, ?_, ?_, ?_, ?_⟩
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

/-- **`checkpoints_cost`.** From a sound prefix run into an `InvL` state with the
right head at most on the first letter cell, the costed oracle yields one
trace with checkpoint times `Tc` (as in `checkpoints_from_invL`) and, for every
`1 ≤ m < |raw|`, the (O-cost) bound on the ticks between the checkpoints. -/
theorem checkpoints_cost (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC P q first raw)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 x0 ⟨c, r⟩)
    (hI : InvL raw c r) (hpos : position r.right ≤ 1) :
    ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      st 0 = x0 ∧ Tc 0 = 0 ∧
      Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st (Tc raw.length) ∧
      (∀ m m', m ≤ m' → m' ≤ raw.length → Tc m ≤ Tc m') ∧
      (∀ m, 1 ≤ m → m ≤ raw.length →
        PalPeg.GalilLedgerAssembly.ReportPointAt P q first raw m (st (Tc m))) ∧
      (∀ m, 1 ≤ m → m < raw.length →
        Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw raw (m+1) - Cw raw m) + beta' 2048) := by
  obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, -⟩ :=
    checkpoints_cost_upto P q first raw hor hpre hI hpos raw.length le_rfl
  exact ⟨st, Tc, hst0, hTc0, trace_le htr hTcM, mono_of_step Tc raw.length hmono,
    fun m h1 h2 => ledgerAt_of_prefix (hchk m h1 h2).1 (hchk m h1 h2).2, hcost⟩

#print axioms costedRun_trans
#print axioms costedRun_nil
#print axioms reachAt_of_C
#print axioms cycleOracleM_of_C
#print axioms reachC_fuel
#print axioms reachC_from_invL
#print axioms sum_flatten_map
#print axioms sum_map_add3
#print axioms group_slot
#print axioms group_adv
#print axioms group_fallbacks_length
#print axioms sum_zero_of_all
#print axioms sum_le_of_unique
#print axioms group_cost
#print axioms sum_split
#print axioms interval_cost_of_costedRun
#print axioms checkpoints_cost_upto
#print axioms checkpoints_cost

end PalPeg.GalilTraceCost
