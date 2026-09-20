import PalPeg.GalilScaffoldTopStagePrefix
import PalPeg.AnswerAheadDecode
import PalPeg.CanonicalChainReady
import PalPeg.GalilMinimalPeriod

/-! # DP result and copy validity from the executed search program

The result is extracted from a finite execution which has actually halted.
It does not assume that a future event list has room for every later stage.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PalPeg.CanonicalSearchProgram
open PalPeg GalilScaffoldChainInputSupply GalilScaffoldCounter
open GalilScaffoldSearchRun GalilBranchInvariants2
open GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- A DP candidate only inspects its first `4*h+1` symbols, so it transfers
between two prefixes of the same stream once both prefixes are long enough. -/
theorem candidate_rewindow {xs : List (Fin 3)} {n m lower h : ℕ}
    (hc : GalilDpCorrect.Candidate (xs.take n) lower h)
    (hm : 4*h+1 ≤ (xs.take m).length) :
    GalilDpCorrect.Candidate (xs.take m) lower h := by
  have hn : 4*h+1 ≤ n := le_trans hc.2.1 (List.length_take_le _ _)
  have hm' : 4*h+1 ≤ m := le_trans hm (List.length_take_le _ _)
  refine ⟨hc.1,hm,?_,?_⟩
  · have hn2 : 2*h+1 ≤ n := by omega
    have hm2 : 2*h+1 ≤ m := by omega
    simpa [List.take_take,Nat.min_eq_left hn2,Nat.min_eq_left hm2] using hc.2.2.1
  · simpa [List.take_take,Nat.min_eq_left hn,Nat.min_eq_left hm'] using hc.2.2.2

/-- A too-short fallback move exposes the corresponding semiperiod as a DP
candidate on every stage window covering the current scan radius. -/
theorem candidate_of_span_period (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {C k span g : ℕ}
    (hC : C = (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length)
    (hkC : k < C) (hpal : Manacher.PalAt
      (encoded ((a :: ls).reverse ++ rs ++ q)) C k)
    (hg0 : 0 < g) (hfour : 4*g ≤ k)
    (hper : HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C k) (2*g))
    (hspan : 4*g ≤ span) :
    GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) 0 g := by
  have hp := palAt_pair_of_period hpal hfour hper
  have hlen1 : 2*g+1 ≤ (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length := by
    rw [← hC]
    omega
  have hlen2 : 2*(2*g)+1 ≤ (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length := by
    rw [← hC]
    omega
  have hpal1 : IsPal
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*g+1)) := by
    apply (stream_prefix_palindrome a ls rs q gap g hlen1).2
    simpa [hC] using hp.1
  have hpal2 : IsPal
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (4*g+1)) := by
    have hp2 : Manacher.PalAt (encoded ((a :: ls).reverse ++ rs ++ q))
        ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length - 2*g) (2*g) := by
      rw [← hC]
      exact hp.2
    have hh := (stream_prefix_palindrome a ls rs q gap (2*g) hlen2).2 hp2
    simpa [show 2*(2*g)+1 = 4*g+1 by omega] using hh
  refine ⟨by omega,?_,?_,?_⟩
  · simp only [List.length_take]
    omega
  · rw [List.take_take,Nat.min_eq_left (by omega)]
    exact hpal1
  · rw [List.take_take,Nat.min_eq_left (by omega)]
    exact hpal2

/-- The fallback-facing meaning of a least candidate: whenever a future
palindrome is long enough to expose a smaller semiperiod, that semiperiod is
not a period of the palindrome. -/
def MoveMinimal (raw : List (Fin 2)) (C h : ℕ) : Prop :=
  ∀ k, k < C → Manacher.PalAt (encoded raw) C k →
    ∀ g, 0 < g → g < h → 4*g ≤ k →
      ¬ HasPeriod (Span raw C k) (2*g)

/-- What the DP itself excludes when it runs above a lower bound: the semiperiods strictly
between `lower` and the least candidate `h`.  (Those up to `lower` are the history of the lower
bound, `LowerExcludedFrom`.) -/
def MoveAbove (raw : List (Fin 2)) (C lower h : ℕ) : Prop :=
  ∀ k, k < C → Manacher.PalAt (encoded raw) C k →
    ∀ g, lower < g → g < h → 4*g ≤ k →
      ¬ HasPeriod (Span raw C k) (2*g)

theorem MoveAbove.toMoveMinimal {raw : List (Fin 2)} {C h : ℕ} (hmove : MoveAbove raw C 0 h) :
    MoveMinimal raw C h :=
  fun k hkC hpal g hg0 hgh hfour => hmove k hkC hpal g hg0 hgh hfour

theorem moveAbove_of_candidate (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {C lower span h : ℕ}
    (hC : C = position (represent ⟨a :: ls,gap⟩ (rs.map some) q))
    (hcand : GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower h)
    (hmin : ∀ g, g < h → ¬ GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower g) :
    MoveAbove ((a :: ls).reverse ++ rs ++ q) C lower h := by
  have hstream : C = (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length := by
    rw [hC,position_represent]
  intro k hkC hpal g hlower hgh hfour hper
  apply hmin g hgh
  have hzero := candidate_of_span_period a ls rs q gap (span := span) hstream hkC hpal
    (by omega) hfour hper (by
      have hlen := hcand.2.1
      simp only [List.length_take] at hlen
      omega)
  exact ⟨hlower, hzero.2⟩

/-- The reusable semantic meaning of a least found candidate at one centre. -/
def FutureMinimal (raw : List (Fin 2)) (C h : ℕ) : Prop :=
  ∀ k, k < C → Manacher.PalAt (encoded raw) C k → 4*h ≤ k →
    HasPeriod (GalilScaffoldChainInputSupply.Span raw C k) (2*h) →
    ∀ p, 0 < p → p < 2*h →
      ¬ HasPeriod (GalilScaffoldChainInputSupply.Span raw C k) p

/-- The history a positive search lower bound stands for: no semiperiod `δ ≤ lower` is a period
of a span of the centre that is large enough to hold a candidate above `lower`. -/
def LowerExcluded (raw : List (Fin 2)) (C lower : ℕ) : Prop :=
  ∀ k, k < C → Manacher.PalAt (encoded raw) C k → 4*(lower+1) ≤ k →
    ∀ δ, 0 < δ → δ ≤ lower →
      ¬ HasPeriod (GalilScaffoldChainInputSupply.Span raw C k) (2*δ)

/-- The same exclusion on every span of radius at least `base`: what a break inside the span
gives, whatever the size of the span. -/
def LowerExcludedFrom (raw : List (Fin 2)) (C lower base : ℕ) : Prop :=
  ∀ k, base ≤ k → k < C → Manacher.PalAt (encoded raw) C k →
    ∀ δ, 0 < δ → δ ≤ lower →
      ¬ HasPeriod (GalilScaffoldChainInputSupply.Span raw C k) (2*δ)

theorem lowerExcludedFrom_zero (raw : List (Fin 2)) (C base : ℕ) :
    LowerExcludedFrom raw C 0 base := by
  intro k _ _ _ δ hδ0 hδ
  omega

theorem LowerExcludedFrom.toLowerExcluded {raw : List (Fin 2)} {C lower base : ℕ}
    (hexcluded : LowerExcludedFrom raw C lower base) (hbase : base ≤ 4*(lower+1)) :
    LowerExcluded raw C lower :=
  fun k hkC hpal hk => hexcluded k (by omega) hkC hpal

theorem lowerExcluded_zero (raw : List (Fin 2)) (C : ℕ) : LowerExcluded raw C 0 := by
  intro k _ _ _ δ hδ0 hδ
  omega

/-- A least DP candidate on the centre's place stream yields the future
minimal-period certificate needed when its chain has caught up. -/
theorem futureMinimal_of_candidate (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {C lower span h : ℕ}
    (hC : C = position (represent ⟨a :: ls,gap⟩ (rs.map some) q))
    (hcand : GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower h)
    (hmin : ∀ g, g < h → ¬ GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower g)
    (hexcluded : LowerExcluded ((a :: ls).reverse ++ rs ++ q) C lower) :
    FutureMinimal ((a :: ls).reverse ++ rs ++ q) C h := by
  intro k hkC hpal h4 hper p hp hp2
  apply GalilScaffoldChainInputSupply.no_short_period_of_minimal
    a ls rs q gap hC hkC hpal (by have := hcand.1; omega) (by omega) hper
  · intro g _hg0 hgh hcg
    apply hmin g hgh
    apply candidate_rewindow hcg
    have hlen := hcand.2.1
    omega
  · intro δ hδ0 hδ
    exact hexcluded k hkC hpal (by have := hcand.1; omega) δ hδ0 hδ
  · exact hp
  · exact hp2

private theorem run_unique {n : ℕ} {code : List (GalilFppWide.Instruction n)}
    (hf : GalilTickDet.ReadFun code) {x y z : GalilScaffoldControl.Machine n} {bs : List Bool}
    (h₁ : GalilScaffoldControl.Run code x bs y)
    (h₂ : GalilScaffoldControl.Run code x bs z) : y = z := by
  induction h₁ generalizing z with
  | nil => cases h₂; rfl
  | cons x y z b bs ht hr ih =>
    cases h₂ with
    | cons _ y' _ _ _ ht' hr' =>
      have he := GalilTickDet.progTick_unique hf ht ht'
      subst y'
      exact ih hr'

/-- Once the actual program has halted, arbitrary remaining clock slots cannot
change its answer, so the existing costed reference run identifies its result. -/
theorem result_of_run {w : List (Fin 3)} {lower : ℕ}
    {bs : List Bool} {v : GalilScaffoldControl.Machine 12}
    (hr : GalilScaffoldControl.Run GalilDpCode.code
      ⟨GalilScaffoldPreload.initial w lower,false⟩ bs v)
    (hd : v.done = true) : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote v.config) := by
  obtain ⟨t,hresult,hall⟩ := GalilScaffoldDpCost.scheduled_correct w lower
  let padding := List.replicate (3186*w.length+1683) true
  have hp : GalilScaffoldControl.Run GalilDpCode.code
      ⟨GalilScaffoldPreload.initial w lower,false⟩ (bs ++ padding) v :=
    GalilScaffoldControl.run_append hr (GalilScaffoldControl.done_run GalilDpCode.code v hd padding)
  have href := hall (bs ++ padding) (by simp [padding])
  have he := run_unique GalilTickFair.readFun_code hp href
  simpa only [he] using hresult

private theorem calls_run {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (h : SafeCalls s x bs t y) :
    ∃ es, GalilScaffoldControl.Run GalilDpCode.code x es y := by
  induction h with
  | nil => exact ⟨[],.nil _⟩
  | cons s x y z b bs t ht _ _ ih =>
    obtain ⟨es,hes⟩ := ih
    exact ⟨(b && decide (s.mode = .run)) :: es,.cons _ _ _ _ _ ht hes⟩

private theorem quanta_run {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (h : SafeQuanta s x bs t y) :
    ∃ es, GalilScaffoldControl.Run GalilDpCode.code x es y := by
  induction h with
  | nil => exact ⟨[],.nil _⟩
  | cons s u t x y z a as hm hc hr ih =>
    obtain ⟨es,he⟩ := calls_run hc
    obtain ⟨fs,hf⟩ := ih
    exact ⟨es ++ fs,GalilScaffoldControl.run_append he hf⟩

theorem calls_mode_done {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (hr : SafeCalls s x bs t y) (hi : s.mode = .run ↔ x.done = false) :
    t.mode = .run ↔ y.done = false := by
  induction hr with
  | nil => exact hi
  | cons s x y z b bs t ht _ hr ih =>
    have hg : decide (s.mode = .run) = !x.done := by cases hd : x.done <;> simp_all
    have ht' := ht
    rw [hg] at ht'
    exact ih (run_call b hi ht').2

theorem quanta_mode_done {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (hr : SafeQuanta s x bs t y) (hi : s.mode = .run ↔ x.done = false) :
    t.mode = .run ↔ y.done = false := by
  induction hr with
  | nil => exact hi
  | cons s u t x y z a as hm hc hr ih =>
    have hu := calls_mode_done hc hi
    apply ih
    cases a <;> exact hu

/-- Any halted state reached from a real preload has the proved DP result. -/
theorem result_of_reached_terminal {w : List (Fin 3)} {lower : ℕ}
    {s0 : GalilScaffoldSearchFinish.State} {bs : List Bool} {v : SearchVM}
    (hs : s0.mode = .run) (hr : DpReached w lower s0 bs v.search v.dp)
    (hf : v.search.mode ≠ .run) :
    GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote v.dp.config) := by
  have hlink := quanta_mode_done hr (by simp [hs])
  have hd : v.dp.done = true := by cases hd : v.dp.done <;> simp_all
  obtain ⟨es,he⟩ := quanta_run hr
  exact result_of_run he hd

/-- A found state reached from a real preload has the proved DP result. -/
theorem result_of_reached {w : List (Fin 3)} {lower : ℕ}
    {s0 : GalilScaffoldSearchFinish.State} {bs : List Bool} {v : SearchVM}
    (hs : s0.mode = .run) (hr : DpReached w lower s0 bs v.search v.dp)
    (hf : v.search.mode = .found) :
    GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote v.dp.config) :=
  result_of_reached_terminal hs hr (by simp [hf])

/-- The copy datum is a consequence of the DP execution, not a new oracle. -/
theorem copy_of_reached {p : GalilScaffoldPlace.Place} {lower span : ℕ}
    {s0 : GalilScaffoldSearchFinish.State} {bs : List Bool} {v : SearchVM}
    (hs : s0.mode = .run)
    (hr : DpReached ((GalilScaffoldPlace.stream p).take (span+1)) lower s0 bs v.search v.dp)
    (hf : v.search.mode = .found) (cc : Fin 3) :
    ∃ n, GalilBranchInvariants.CopyInv (v.dp.config.tapes 11) reset p
      (GalilScaffoldChainPeriod.start cc) n := by
  have hresult := result_of_reached hs hr hf
  obtain ⟨h,hcand,_,hden,hhead,hfocus,_⟩ :=
    GalilScaffoldChainAnswer.found_output hr hs hf hresult
  exact ⟨h,AnswerAheadDecode.copyInv_of_found (by have := hcand.1; omega)
    hden hhead hfocus hcand⟩

/-- The preparation certificate stores the remaining real preparation ticks. -/
def PrepFuture (w : List (Fin 3)) (lower : ℕ) (s : GalilScaffoldPrepareControl.State) : Prop :=
  ∃ n t, GalilScaffoldPrepareControl.Run s (List.replicate n true) t ∧
    t.mode = .run ∧ t.program.config = GalilScaffoldPreload.initial w lower ∧ t.program.done = false

theorem prep_run_rebase {s t : GalilScaffoldPrepareControl.State} {bs : List Bool}
    (h : GalilScaffoldPrepareControl.Run s bs t) (d : Counter) :
    GalilScaffoldPrepareControl.Run {s with debt := d} bs {t with debt := d} := by
  induction h with
  | nil => exact .nil _
  | cons s u t b bs hs hr ih =>
    exact .cons _ _ _ _ _ (GalilScaffoldPreparePaced.tick_rebase hs d) ih

theorem prepFuture_advance {w : List (Fin 3)} {lower : ℕ}
    {s : GalilScaffoldPrepareControl.State} (h : PrepFuture w lower s) (a : Bool) :
    PrepFuture w lower (GalilScaffoldPreparePaced.afterAdvance a s) := by
  obtain ⟨n,t,hr,hm,hc,hd⟩ := h
  cases a with
  | false => exact ⟨n,t,hr,hm,hc,hd⟩
  | true => exact ⟨n,{t with debt := dec s.debt},prep_run_rebase hr _,hm,hc,hd⟩

/-- Dispatch creates the semantic preload certificate for this actual centre. -/
theorem prepFuture_dispatch (p : GalilScaffoldPlace.Place) (lower span : ℕ)
    (s : GalilScaffoldPrepareControl.State) (hs : s.span = ofNat span) (a : Bool) :
    PrepFuture ((GalilScaffoldPlace.stream p).take (span+1)) lower
      (GalilScaffoldPreparePaced.afterAdvance a
        (GalilScaffoldPrepareControl.prepare s (ofNat lower) p)) := by
  obtain ⟨t,hr,hm,hc,hd,_,_⟩ := GalilScaffoldPrepareControl.prepare_complete s lower span p hs
  cases hr with
  | intro s0 _ hRun =>
    exact prepFuture_advance
      ⟨2*lower + 2*(List.take (span+1) (GalilScaffoldPlace.stream p)).length + 6,
        t,hRun,hm,hc,hd⟩ a

/-- Each actual prep tick removes the head of that certificate. -/
theorem prepFuture_step {w : List (Fin 3)} {lower : ℕ}
    {s u : GalilScaffoldPrepareControl.State}
    (h : PrepFuture w lower s) (hm : s.mode ≠ .run)
    (ht : GalilScaffoldPrepareControl.Tick true s u) (a : Bool) :
    PrepFuture w lower (GalilScaffoldPreparePaced.afterAdvance a u) := by
  obtain ⟨n,t,hr,hmode,hc,hd⟩ := h
  cases n with
  | zero => cases hr; exact (hm hmode).elim
  | succ n =>
    simp only [List.replicate_succ] at hr
    cases hr with
    | cons _ z _ _ _ hz htail =>
      have he := GalilScaffoldChainInputSupply.Prep.tick_unique ht hz
      subst z
      exact prepFuture_advance ⟨n,t,htail,hmode,hc,hd⟩ a

/-- A certificate whose source has reached `run` is already at its target. -/
theorem prepFuture_run {w : List (Fin 3)} {lower : ℕ}
    {s : GalilScaffoldPrepareControl.State} (h : PrepFuture w lower s) (hm : s.mode = .run) :
    s.program.config = GalilScaffoldPreload.initial w lower ∧ s.program.done = false := by
  obtain ⟨n,t,hr,hmode,hc,hd⟩ := h
  cases n with
  | zero => cases hr; exact ⟨hc,hd⟩
  | succ n =>
    simp only [List.replicate_succ] at hr
    cases hr with
    | cons _ z _ _ _ hz _ => cases hz <;> simp_all

/-- Preparation together with the exact final-stage bound for its centre. -/
def PrepFutureAt (p : GalilScaffoldPlace.Place) (lower : ℕ)
    (s : GalilScaffoldPrepareControl.State) : Prop :=
  ∃ span n t, s.span = ofNat span ∧
    GalilScaffoldPrepareControl.Run s (List.replicate n true) t ∧
    t.mode = .run ∧ t.program.config = GalilScaffoldPreload.initial
      ((GalilScaffoldPlace.stream p).take (span+1)) lower ∧ t.program.done = false ∧
    (t.finalStage = true ↔ (GalilScaffoldPlace.stream p).length ≤ span+1)

private theorem prepFutureAt_advance {p : GalilScaffoldPlace.Place} {lower : ℕ}
    {s : GalilScaffoldPrepareControl.State} (h : PrepFutureAt p lower s) (a : Bool) :
    PrepFutureAt p lower (GalilScaffoldPreparePaced.afterAdvance a s) := by
  obtain ⟨span,n,t,hspan,hr,hm,hc,hd,hfinal⟩ := h
  cases a with
  | false => exact ⟨span,n,t,hspan,hr,hm,hc,hd,hfinal⟩
  | true => exact ⟨span,n,{t with debt := dec s.debt},hspan,
      prep_run_rebase hr _,hm,hc,hd,hfinal⟩

private theorem prepFutureAt_dispatch (p : GalilScaffoldPlace.Place) (lower span : ℕ)
    (s : GalilScaffoldPrepareControl.State) (hs : s.span = ofNat span) (a : Bool) :
    PrepFutureAt p lower (GalilScaffoldPreparePaced.afterAdvance a
      (GalilScaffoldPrepareControl.prepare s (ofNat lower) p)) := by
  obtain ⟨t,hr,hm,hc,hd,_,hfinal⟩ :=
    GalilScaffoldPrepareControl.prepare_complete s lower span p hs
  cases hr with
  | intro _ _ hrun =>
      exact prepFutureAt_advance
        ⟨span,2*lower+2*((GalilScaffoldPlace.stream p).take (span+1)).length+6,
          t,(by simpa [GalilScaffoldPrepareControl.prepare] using hs),
          hrun,hm,hc,hd,hfinal⟩ a

private theorem prepFutureAt_step {p : GalilScaffoldPlace.Place} {lower : ℕ}
    {s u : GalilScaffoldPrepareControl.State}
    (h : PrepFutureAt p lower s) (hm : s.mode ≠ .run)
    (ht : GalilScaffoldPrepareControl.Tick true s u) (a : Bool) :
    PrepFutureAt p lower (GalilScaffoldPreparePaced.afterAdvance a u) := by
  obtain ⟨span,n,t,hspan,hr,hmode,hc,hd,hfinal⟩ := h
  cases n with
  | zero => cases hr; exact (hm hmode).elim
  | succ n =>
      simp only [List.replicate_succ] at hr
      cases hr with
      | cons _ z _ _ _ hz htail =>
          have he := GalilScaffoldChainInputSupply.Prep.tick_unique ht hz
          subst z
          have huspan : u.span = s.span := by cases ht <;> rfl
          exact prepFutureAt_advance
            ⟨span,n,t,huspan.trans hspan,htail,hmode,hc,hd,hfinal⟩ a

private theorem prepFutureAt_run {p : GalilScaffoldPlace.Place} {lower : ℕ}
    {s : GalilScaffoldPrepareControl.State} (h : PrepFutureAt p lower s)
    (hm : s.mode = .run) :
    ∃ span, s.span = ofNat span ∧
      s.program.config = GalilScaffoldPreload.initial
        ((GalilScaffoldPlace.stream p).take (span+1)) lower ∧
      s.program.done = false ∧
      (s.finalStage = true ↔ (GalilScaffoldPlace.stream p).length ≤ span+1) := by
  obtain ⟨span,n,t,hspan,hr,hmode,hc,hd,hfinal⟩ := h
  cases n with
  | zero => cases hr; exact ⟨span,hspan,hc,hd,hfinal⟩
  | succ n =>
      simp only [List.replicate_succ] at hr
      cases hr with
      | cons _ z _ _ _ hz _ => cases hz <;> simp_all

/-- Preparation modes, separated from scheduling and DP execution. -/
def Preparing (m : GalilScaffoldSearchFinish.Mode) : Prop :=
  m = .lower ∨ m = .lowerHome ∨ m = .copy ∨ m = .home

/-- The semantic certificate follows each new preparation, including later stages. -/
structure ProgramInv (p : GalilScaffoldPlace.Place) (lower : ℕ) (v : SearchVM) : Prop where
  lower_eq : v.lower = ofNat lower
  span_nat : ∃ m, v.search.span = ofNat m
  prep : Preparing v.search.mode → PrepFutureAt p lower v.toPrep
  running : v.search.mode = .run → ∃ m s0 bs, s0.mode = .run ∧
    (s0.finalStage = true ↔ (GalilScaffoldPlace.stream p).length ≤ m+1) ∧
    DpReached ((GalilScaffoldPlace.stream p).take (m+1)) lower s0 bs v.search v.dp
  found : v.search.mode = .found → ∃ m s0 bs, s0.mode = .run ∧
    (s0.finalStage = true ↔ (GalilScaffoldPlace.stream p).length ≤ m+1) ∧
    DpReached ((GalilScaffoldPlace.stream p).take (m+1)) lower s0 bs v.search v.dp
  missed : v.search.mode = .missed → ∃ m s0 bs, s0.mode = .run ∧
    (s0.finalStage = true ↔ (GalilScaffoldPlace.stream p).length ≤ m+1) ∧
    DpReached ((GalilScaffoldPlace.stream p).take (m+1)) lower s0 bs v.search v.dp

private theorem programInv_quiet {p : GalilScaffoldPlace.Place} {lower : ℕ} {v : SearchVM}
    (hl : v.lower = ofNat lower) (hspan : ∃ m, v.search.span = ofNat m)
    (hp : ¬ Preparing v.search.mode) (hr : v.search.mode ≠ .run) (hf : v.search.mode ≠ .found) (hmiss : v.search.mode ≠ .missed) :
    ProgramInv p lower v :=
  ⟨hl,hspan,fun h => (hp h).elim,fun h => (hr h).elim,fun h => (hf h).elim,
    fun h => (hmiss h).elim⟩

private theorem programInv_quiet_target {p : GalilScaffoldPlace.Place} {lower : ℕ}
    (v : SearchVM) (hl : v.lower = ofNat lower) (hspan : ∃ m, v.search.span = ofNat m)
    (hp : ¬ Preparing v.search.mode) (hr : v.search.mode ≠ .run)
    (hf : v.search.mode ≠ .found) (hmiss : v.search.mode ≠ .missed) : ProgramInv p lower v :=
  ⟨hl,hspan,fun h => (hp h).elim,fun h => (hr h).elim,fun h => (hf h).elim,
    fun h => (hmiss h).elim⟩

/-- Arbitrary old tapes are harmless: dispatch resets them before any DP step. -/
theorem programInv_begin (p : GalilScaffoldPlace.Place) (v : SearchVM) (lower : ℕ) (rad : Counter) :
    ProgramInv p lower ({ v with search := GalilScaffoldSearchFinish.begin (ofNat lower) rad, lower := ofNat lower }) := by
  apply programInv_quiet rfl
  · exact ⟨0,rfl⟩
  all_goals simp [Preparing,GalilScaffoldSearchFinish.begin]

private theorem programInv_dispatch {p : GalilScaffoldPlace.Place} {lower : ℕ} {v : SearchVM}
    (hi : ProgramInv p lower v) (a : Bool) :
    ProgramInv p lower (SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
      (GalilScaffoldPrepareControl.prepare v.toPrep v.lower p)) v.search.quarter v.lower) := by
  obtain ⟨m,hm⟩ := hi.span_nat
  refine ⟨hi.lower_eq,⟨m,?_⟩,?_,?_,?_,?_⟩
  · cases a <;> exact hm
  · intro _
    rw [toPrep_ofPrep,hi.lower_eq]
    exact prepFutureAt_dispatch p lower m v.toPrep hm a
  all_goals intro h; cases a <;> cases h

private theorem programInv_prep {p : GalilScaffoldPlace.Place} {lower : ℕ} {v : SearchVM}
    (hi : ProgramInv p lower v) (hm : Preparing v.search.mode)
    {u : GalilScaffoldPrepareControl.State}
    (ht : GalilScaffoldPrepareControl.Tick true v.toPrep u) (a : Bool) :
    ProgramInv p lower (SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a u)
      v.search.quarter v.lower) := by
  have hfuture := hi.prep hm
  have hn : v.toPrep.mode ≠ .run := by rcases hm with h|h|h|h <;> simp [SearchVM.toPrep,h]
  have hf := prepFutureAt_step hfuture hn ht a
  let v' := SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a u) v.search.quarter v.lower
  have he : v'.toPrep = GalilScaffoldPreparePaced.afterAdvance a u := rfl
  have hspan : u.span = v.search.span := by
    cases ht <;> rfl
  refine ⟨hi.lower_eq,?_,fun _ => hf,?_,?_,?_⟩
  · obtain ⟨n,hn⟩ := hi.span_nat
    refine ⟨n,?_⟩
    cases a <;> exact hspan.trans hn
  · intro hr
    have hs : (GalilScaffoldPreparePaced.afterAdvance a u).mode = .run := hr
    obtain ⟨m,hmspan,hc,hd,hfinal⟩ := prepFutureAt_run hf hs
    refine ⟨m,v'.search,[],hr,hfinal,?_⟩
    have hdp : v'.dp = ⟨GalilScaffoldPreload.initial
        ((GalilScaffoldPlace.stream p).take (m+1)) lower,false⟩ := by
      dsimp [v', SearchVM.ofPrep]
      cases hp : (GalilScaffoldPreparePaced.afterAdvance a u).program
      simp_all [hp]
    rw [hdp]
    exact dpReached_start _ _ _
  · intro hfound
    dsimp [v', SearchVM.ofPrep] at hfound
    have hfound' : (GalilScaffoldPreparePaced.afterAdvance a u).mode = .found := by
      simpa [GalilScaffoldStagePrepare.runState] using hfound
    cases a <;> simp [GalilScaffoldPreparePaced.afterAdvance] at hfound'
    rcases hm with h | h | h | h
    all_goals
      have hsource : v.toPrep.mode = v.search.mode := rfl
      cases ht <;> simp_all [hsource, v', SearchVM.ofPrep,
        SearchVM.toPrep, GalilScaffoldStagePrepare.runState,
        GalilScaffoldPreparePaced.afterAdvance, hfound']
  · intro hmissed
    dsimp [v', SearchVM.ofPrep] at hmissed
    cases a <;> cases ht <;> simp_all [v', SearchVM.ofPrep, SearchVM.toPrep,
      GalilScaffoldStagePrepare.runState, GalilScaffoldPreparePaced.afterAdvance]

private theorem programInv_quantum {p : GalilScaffoldPlace.Place} {lower : ℕ} {v v' : SearchVM}
    (hi : ProgramInv p lower v) (hm : v.search.mode = .run) {a : Bool}
    (hq : SafeQuanta v.search v.dp [a] v'.search v'.dp)
    (hl : v'.lower = v.lower) : ProgramInv p lower v' := by
  obtain ⟨m,s0,bs,hs,hfinal,hr⟩ := hi.running hm
  have hreached := dpReached_step hr hq
  have hexit := safe_quanta_exit hq (by simp [ExitMode,hm])
  refine ⟨hl.trans hi.lower_eq,?_,?_,fun _ => ⟨m,s0,bs++[a],hs,hfinal,hreached⟩,
    fun _ => ⟨m,s0,bs++[a],hs,hfinal,hreached⟩,
    fun _ => ⟨m,s0,bs++[a],hs,hfinal,hreached⟩⟩
  · by_cases hd : v'.search.mode = .double
    · have hz := safe_quanta_double_reset hq (by simp [DoubleReset,hm]) hd
      exact ⟨0,hz.1⟩
    · obtain ⟨n,hn⟩ := hi.span_nat
      have hf := (safe_quanta_frame hq).2
      have hn' : stageSpan v.search = ofNat n := by simpa [stageSpan,hm] using hn
      simpa [stageSpan,hm,hd,hn] using (show ∃ n, stageSpan v'.search = ofNat n from ⟨n,hf.trans hn'⟩)
  · intro hp
    rcases hp with hp|hp|hp|hp <;> simp_all [ExitMode]

/-- Semantic program validity is independent of timing and of stage count. -/
theorem programInv_step {p : GalilScaffoldPlace.Place} {lower : ℕ} {v v' : SearchVM} {a : Bool}
    (hi : ProgramInv p lower v) (ht : searchStep p a v v') : ProgramInv p lower v' := by
  cases hm : v.search.mode with
  | idle | found | missed => simp only [searchStep,hm] at ht; subst v'; exact hi
  | lower | lowerHome | copy | home =>
    simp only [searchStep,hm] at ht
    obtain ⟨u,hu,rfl⟩ := ht
    exact programInv_prep hi (by simp [Preparing,hm]) hu a
  | run =>
    simp only [searchStep,hm] at ht
    obtain ⟨hq,hl,_⟩ := ht
    exact programInv_quantum hi hm hq hl
  | grow =>
    simp only [searchStep,hm] at ht
    split at ht
    · subst v'
      apply programInv_quiet_target
      · simpa [SearchVM.ofPrep] using hi.lower_eq
      · obtain ⟨n,hn⟩ := hi.span_nat
        refine ⟨n+8,?_⟩
        cases a <;> simp [SearchVM.ofPrep,SearchVM.toPrep,GalilScaffoldStagePrepare.runState,
          GalilScaffoldPreparePaced.afterAdvance,GalilScaffoldStagePrepare.growStep,hn,
          GalilScaffoldStagePrepare.add_ofNat]
      all_goals cases a <;> simp [Preparing,SearchVM.ofPrep,SearchVM.toPrep,
        GalilScaffoldStagePrepare.runState,GalilScaffoldPreparePaced.afterAdvance,
        GalilScaffoldStagePrepare.growStep,hm]
    · subst v'; exact programInv_dispatch hi a
  | double =>
    simp only [searchStep,hm] at ht
    split at ht
    · subst v'
      apply programInv_quiet_target
      · simpa [SearchVM.ofPrep] using hi.lower_eq
      · obtain ⟨n,hn⟩ := hi.span_nat
        refine ⟨n+2,?_⟩
        cases a <;> simp [advance,GalilScaffoldDouble.step,hn,inc_ofNat]
      all_goals cases a <;> simp [Preparing,advance,GalilScaffoldDouble.step,hm]
    · subst v'; exact programInv_dispatch hi a
  | wait =>
    simp only [searchStep,hm] at ht
    subst v'
    apply programInv_quiet_target
    · simpa [SearchVM.ofPrep] using hi.lower_eq
    · obtain ⟨n,hn⟩ := hi.span_nat
      by_cases hz : zero v.search.debt = true
      · exact ⟨0,by cases a <;> simp [stageSpan,advance,GalilScaffoldDouble.waitStep,GalilScaffoldDouble.enter,hm,hz]
          <;> exact reset_eq_ofNat⟩
      · exact ⟨n,by cases a <;> simp [advance,GalilScaffoldDouble.waitStep,hm,hz,hn]⟩
    all_goals cases a <;> simp [Preparing,advance,GalilScaffoldDouble.waitStep,
      GalilScaffoldDouble.enter,hm] <;> split <;> simp_all

/-- All stages share the same certificate and hence the same verified result decoder. -/
theorem programInv_found_copy {p : GalilScaffoldPlace.Place} {lower : ℕ} {v : SearchVM}
    (hi : ProgramInv p lower v) (hf : v.search.mode = .found) (cc : Fin 3) :
    ∃ n, GalilBranchInvariants.CopyInv (v.dp.config.tapes 11) reset p
      (GalilScaffoldChainPeriod.start cc) n := by
  obtain ⟨m,s0,bs,hs,_,hr⟩ := hi.found hf
  exact copy_of_reached hs hr hf cc

/-- The semantic DP result at `found`, with the exact searched span exposed. -/
theorem programInv_found_result {p : GalilScaffoldPlace.Place} {lower : ℕ} {v : SearchVM}
    (hi : ProgramInv p lower v) (hf : v.search.mode = .found) :
    ∃ span, GalilDpCorrect.Result ((GalilScaffoldPlace.stream p).take (span+1)) lower 0
        (GalilScaffoldProgram.denote v.dp.config) := by
  obtain ⟨span,s0,bs,hs,_,hr⟩ := hi.found hf
  exact ⟨span,result_of_reached hs hr hf⟩

/-- The semantic DP result at a completed failed search. -/
theorem programInv_missed_result {p : GalilScaffoldPlace.Place} {lower : ℕ} {v : SearchVM}
    (hi : ProgramInv p lower v) (hm : v.search.mode = .missed) :
    ∃ span, (GalilScaffoldPlace.stream p).length ≤ span+1 ∧
      GalilDpCorrect.Result ((GalilScaffoldPlace.stream p).take (span+1)) lower 0
        (GalilScaffoldProgram.denote v.dp.config) ∧
      (GalilScaffoldProgram.denote v.dp.config).pc = 347 := by
  obtain ⟨span,s0,bs,hs,hfinal,hr⟩ := hi.missed hm
  have hres := result_of_reached_terminal hs hr (by simp [hm])
  have hlink := (safe_quanta_terminal_link hr (Or.inl hs)).resolve_left (by simp [hm])
  have hterm := (hlink.2.mp hm).2
  have hframe := (safe_quanta_frame hr).1
  rw [hframe] at hterm
  have hpc : (GalilScaffoldProgram.denote v.dp.config).pc = 347 := by
    rcases hres with hfound | hfailed
    · obtain ⟨_,_,_,_,h346,_,_⟩ := hfound
      exact absurd h346 ((hlink.2.mp hm).1)
    · exact hfailed.1
  exact ⟨span,hfinal.mp hterm,hres,hpc⟩

/-- The complete datum installed at a chain birth: the least candidate and
the copy invariant come from the same executed DP run. -/
theorem programInv_found_birth {p : GalilScaffoldPlace.Place} {lower : ℕ} {v : SearchVM}
    (hi : ProgramInv p lower v) (hf : v.search.mode = .found) (cc : Fin 3) :
    ∃ span h,
      GalilDpCorrect.Result ((GalilScaffoldPlace.stream p).take (span+1)) lower 0
        (GalilScaffoldProgram.denote v.dp.config) ∧
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream p).take (span+1)) lower h ∧
      (∀ g, g < h →
        ¬ GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream p).take (span+1)) lower g) ∧
      GalilBranchInvariants.CopyInv (v.dp.config.tapes 11) reset p
        (GalilScaffoldChainPeriod.start cc) h := by
  obtain ⟨span,s0,bs,hs,_,hr⟩ := hi.found hf
  have hres := result_of_reached hs hr hf
  obtain ⟨h,hcand,hmin,hden,hhead,hfocus,_⟩ :=
    GalilScaffoldChainAnswer.found_output hr hs hf hres
  exact ⟨span,h,hres,hcand,hmin,
    AnswerAheadDecode.copyInv_of_found (by have := hcand.1; omega)
      hden hhead hfocus hcand⟩

#print axioms copy_of_reached
end PalPeg.CanonicalSearchProgram
