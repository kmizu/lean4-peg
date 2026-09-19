import PalPeg.GalilTickDet
import PalPeg.LocalRealizesPhase
import PalPeg.LocalRealizesScan

/-!
# `Fair`: the Scala priorities and pins that make the abstract `Tick` functional

`GalilTickDet` shows `Tick (galilFrameS (sharedC …) q first) delay` is **not**
functional, with four genuine sources:

* **(a)** `Tick.restart` overlaps the scan constructors — at a broken chain the
  background can stutter (`scan_restart_not_det`).  Scala restarts *in the
  transition prelude*, before the mode step.
* **(b)** the search quantum, functional modulo `ReadFun GalilDpCode.code` and
  determinism of `GalilScaffoldPrepareControl.Tick`.  **Both are closed here**
  (`readFun_code` by `decide` through the decidable surrogate `ReadFunB`, and
  `prepTick_true_unique` by case analysis: the enabled preparation ticks are
  pairwise disjoint), so (b) leaves *no* residual hypothesis.
* **(e)** `beginFallbackVM'` leaves the copy place free. Scala copies the right
  head (`walker.copyFrom(right)`), as the final `Canonical` policy now records.
  The historical `Fair` pin to the search cursor is retained only for old lemmas.
* **(e)** `initVM`/`replayStartVM` constrain 13 of the 15 `GalilVM` fields;
  the witnesses actually built by `GalilScaffoldTopScanRun.init_tick` (used by
  `GalilScaffoldTopInitRestart.init_restarted`) and by
  `GalilScaffoldTopReplay.replayStart_tick` (used by
  `GalilScaffoldTopFallbackAll.fallback_replayStart_All`) carry
  `periodOnly := s.periodOnly` and `walker := s.walker`, so that is the pin.

`Fair` is exactly those three refinements, and `tick_fair_unique` proves the
refined tick relation is functional — **with no reachability pack at all**:
every remaining branch overlap is settled by the constructor guards.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace PalPeg.GalilTickFair

open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilTickDet (ReadFun chainAt_unique safeQuanta_unique)

/-! ## 0. Record extensionality -/

theorem searchVM_ext {a b : SearchVM} (h1 : a.search = b.search) (h2 : a.dp = b.dp)
    (h3 : a.lower = b.lower) (h4 : a.walker = b.walker) : a = b := by
  cases a; cases b; simp_all

theorem scanVM_ext {a b : ScanVM} (h1 : a.left = b.left) (h2 : a.right = b.right)
    (h3 : a.chain = b.chain) : a = b := by
  cases a; cases b; simp_all

theorem galilVM_ext {a b : GalilVM}
    (hl : a.left = b.left) (hc : a.center = b.center) (hr : a.right = b.right)
    (hch : a.chain = b.chain) (hcy : a.cycle = b.cycle) (hrm : a.remaining = b.remaining)
    (hrad : a.radius = b.radius) (hlen : a.length = b.length) (hrep : a.replay = b.replay)
    (hfpp : a.fpp = b.fpp) (hse : a.search = b.search) (hdp : a.dp = b.dp)
    (hlo : a.lower = b.lower) (hpo : a.periodOnly = b.periodOnly) (hw : a.walker = b.walker) :
    a = b := by
  cases a; cases b; simp_all

theorem state_ext {a b : State GalilVM} (hc : a.ctl = b.ctl) (hv : a.vm = b.vm) : a = b := by
  cases a; cases b; simp_all

/-! ## 1. Residual (b), closed

`ReadFun` quantifies over all dispatch tables, so it is not itself decidable;
`ReadFunB` is the equivalent check over the tables that actually occur in the
code, and that one `decide`s. -/

/-- One dispatch table is single-valued. -/
def readOk (cs : List (Fin 9 × ℕ)) : Bool :=
  cs.all (fun a => cs.all (fun b => (a.1 != b.1) || (a.2 == b.2)))

/-- The decidable surrogate of `ReadFun`. -/
def ReadFunB {n : ℕ} (code : List (GalilFppWide.Instruction n)) : Bool :=
  code.all (fun i => match i with | .read _ cs => readOk cs | _ => true)

theorem readFun_of_b {n : ℕ} {code : List (GalilFppWide.Instruction n)}
    (h : ReadFunB code = true) : ReadFun code := by
  intro t cs hmem f p₁ p₂ h1 h2
  have hok : readOk cs = true := (List.all_eq_true.1 h) _ hmem
  have h3 := (List.all_eq_true.1 hok) _ h1
  have h4 := (List.all_eq_true.1 h3) _ h2
  simpa using h4

/-- **The DP code's `read` dispatch tables are single-valued.** -/
theorem readFun_code : ReadFun GalilDpCode.code := readFun_of_b (by decide)

/-- **The enabled preparation ticks are a function.**  `Tick.idle` only fires
disabled, and the eight enabled constructors are pairwise separated by
`mode`, `positive work`, the tape focus and `read walker`. -/
theorem prepTick_true_unique {x y₁ y₂ : GalilScaffoldPrepareControl.State}
    (h1 : GalilScaffoldPrepareControl.Tick true x y₁)
    (h2 : GalilScaffoldPrepareControl.Tick true x y₂) : y₁ = y₂ := by
  cases h1 <;> cases h2 <;> simp_all

#print axioms readFun_code
#print axioms prepTick_true_unique

/-! ## 2. The search co-process is a function -/

theorem searchStep_unique {center : GalilScaffoldPlace.Place} {a : Bool} {v v₁ v₂ : SearchVM}
    (h1 : searchStep center a v v₁) (h2 : searchStep center a v v₂) : v₁ = v₂ := by
  unfold searchStep at h1 h2
  cases hm : v.search.mode <;> simp only [hm] at h1 h2
  case idle => rw [h1, h2]
  case found => rw [h1, h2]
  case missed => rw [h1, h2]
  case wait => rw [h1, h2]
  case grow =>
    by_cases hw : GalilScaffoldCounter.positive v.search.work = true
    · rw [if_pos hw] at h1 h2; rw [h1, h2]
    · rw [if_neg hw] at h1 h2; rw [h1, h2]
  case double =>
    by_cases hw : GalilScaffoldCounter.positive v.search.work = true
    · rw [if_pos hw] at h1 h2; rw [h1, h2]
    · rw [if_neg hw] at h1 h2; rw [h1, h2]
  case run =>
    obtain ⟨hq₁, hl₁, hw₁⟩ := h1
    obtain ⟨hq₂, hl₂, hw₂⟩ := h2
    obtain ⟨hs, hd⟩ := safeQuanta_unique readFun_code hq₁ hq₂
    exact searchVM_ext hs hd (hl₁.trans hl₂.symm) (hw₁.trans hw₂.symm)
  all_goals
    (obtain ⟨z₁, ht₁, he₁⟩ := h1
     obtain ⟨z₂, ht₂, he₂⟩ := h2
     rw [he₁, he₂, prepTick_true_unique ht₁ ht₂])

theorem searchEffect_unique {P : Shared} {a : Bool} {s : GalilVM} {v₁ v₂ : SearchVM}
    (h1 : searchEffect P a s v₁) (h2 : searchEffect P a s v₂) : v₁ = v₂ := by
  rcases h1 with ⟨hi, hs₁⟩ | ⟨hn, he₁⟩ <;> rcases h2 with ⟨hi', hs₂⟩ | ⟨hn', he₂⟩
  · exact searchStep_unique hs₁ hs₂
  · exact absurd hi hn'
  · exact absurd hi' hn
  · rw [he₁, he₂]

/-! ## 3. The two relational blocks of the scan mode are functions -/

theorem backgroundS_unique {P : Shared} {q : ℕ} {first : Fin 9} {s t₁ t₂ : GalilVM}
    (h1 : (galilFrameS P q first).background s t₁)
    (h2 : (galilFrameS P q first).background s t₂) : t₁ = t₂ := by
  obtain ⟨hl₁, hr₁, hq₁, hc₁, he₁⟩ := h1
  obtain ⟨hl₂, hr₂, hq₂, hc₂, he₂⟩ := h2
  have hv : searchLens.get t₁ = searchLens.get t₂ := searchEffect_unique hq₁ hq₂
  rw [hv] at hc₁
  have hch : t₁.chain = t₂.chain := chainAt_unique hc₁ hc₂
  have hscan : scanLens.get t₁ = scanLens.get t₂ :=
    scanVM_ext (hl₁.trans hl₂.symm) (hr₁.trans hr₂.symm) hch
  rw [he₁, he₂, hv, hscan]

theorem matched_set (P : Shared) (q : ℕ) (first : Fin 9) (s : GalilVM) (vs : ScanVM) :
    (galilFrame P q first).matched (scanLens.set s vs) ↔
      GalilScaffoldInputHead.read vs.left = GalilScaffoldInputHead.read vs.right := Iff.rfl

theorem compareFound_unique {P : Shared} {q : ℕ} {first : Fin 9} {s t₁ t₂ : GalilVM}
    (h1 : (galilFrameS P q first).compare s t₁)
    (h2 : (galilFrameS P q first).compare s t₂) : t₁ = t₂ := by
  obtain ⟨vs₁, vq₁, a₁, hl₁, hr₁, ha₁, hq₁, hc₁, he₁⟩ := h1
  obtain ⟨vs₂, vq₂, a₂, hl₂, hr₂, ha₂, hq₂, hc₂, he₂⟩ := h2
  -- the comparison event is read off `s` alone
  have hm₁ := ha₁.trans ((matched_set P q first s vs₁).trans (by rw [hl₁, hr₁]))
  have hm₂ := ha₂.trans ((matched_set P q first s vs₂).trans (by rw [hl₂, hr₂]))
  have haa : a₁ = a₂ := by
    cases a₁ <;> cases a₂
    · rfl
    · exact absurd (hm₁.2 (hm₂.1 rfl)) (by simp)
    · exact absurd (hm₂.2 (hm₁.1 rfl)) (by simp)
    · rfl
  subst haa
  have hvq : vq₁ = vq₂ := searchEffect_unique hq₁ hq₂
  subst hvq
  have hch : vs₁.chain = vs₂.chain := chainAt_unique hc₁ hc₂
  have hvs : vs₁ = vs₂ := scanVM_ext (hl₁.trans hl₂.symm) (hr₁.trans hr₂.symm) hch
  subst hvs
  rw [he₁, he₂]

/-! ## 4. `Fair` -/

/-- **Legacy deterministic refinement of `Tick`.**  Its fallback pin selects
the search cursor, which is not Scala's `walker.copyFrom(right)`.  The final
canonical run uses `rightPlace` instead.  Source (b) needs no refinement.

* `restartFirst` — `transition`'s prelude restarts a broken chain *before* the
  mode step, so no scan constructor may fire while `restartGuardVM` holds.
* `fallbackPlace` — the legacy policy selects the search cursor; retained
  for old conditional lemmas, not a claim about the Scala fallback origin.
* `keepsSearchCursor` — `stepInit` and `stepReplayStart` touch neither
  `periodOnly` nor `walker`, as the witnesses of `init_tick` /
  `replayStart_tick` (hence of `init_restarted` /
  `fallback_replayStart_All`) do. -/
structure Fair (entry delay : ℕ) (x y : State GalilVM) : Prop where
  restartFirst : x.ctl.mode = Mode.scan → restartGuardVM x.vm →
    y.ctl = {x.ctl with clock := delay} ∧ restartVM entry x.vm y.vm
  fallbackPlace : x.ctl.mode = Mode.scan → y.ctl.mode = Mode.copy →
    y.vm.fpp.walker = y.vm.walker
  keepsSearchCursor : x.ctl.mode = Mode.init ∨ x.ctl.mode = Mode.replayStart →
    y.vm.periodOnly = x.vm.periodOnly ∧ y.vm.walker = x.vm.walker

/-- The restart is enabled only at a broken chain with the guard. -/
theorem restartGuard_of_restartVM {entry : ℕ} {s t : GalilVM} (h : restartVM entry s t) :
    restartGuardVM s := by
  obtain ⟨w, hw, hm, hl, hz, -⟩ := h
  exact ⟨w, hw, hm, hl, hz⟩

/-- Decode the copy origin of Scala `beginFallback`: `walker.copyFrom(right)`.
The search cursor is a distinct logical field in the abstract VM. -/
def rightPlace (s : GalilVM) : GalilScaffoldPlace.Place :=
  ⟨PalPeg.GalilFinalAssembly2.lettersOf s.right.head, s.right.gap⟩

/-- **The canonical schedule of the oracle's own runs.**  `Fair` with `restartFirst` replaced by
"no restart at all": the constructed runs keep a broken chain broken until the next fallback
(`ShapedRun`), which is a legitimate execution of the machine.  The fallback origin is the right head, as in Scala `beginFallback`; `Fair` retains
its historical search-cursor pin for the older lemmas.  The init/replay cursor
clause is shared. -/
structure Canonical (entry delay : ℕ) (x y : State GalilVM) : Prop where
  noRestart : x.ctl.mode = Mode.scan → ¬ restartVM entry x.vm y.vm
  fallbackPlace : x.ctl.mode = Mode.scan → y.ctl.mode = Mode.copy →
    y.vm.fpp.walker = rightPlace y.vm
  keepsSearchCursor : x.ctl.mode = Mode.init ∨ x.ctl.mode = Mode.replayStart →
    y.vm.periodOnly = x.vm.periodOnly ∧ y.vm.walker = x.vm.walker

theorem canonical_of_scan_nonCopy {entry delay : ℕ} {x y : State GalilVM}
    (hm : x.ctl.mode = Mode.scan) (hy : y.ctl.mode ≠ Mode.copy)
    (hnr : ¬ restartVM entry x.vm y.vm) : Canonical entry delay x y :=
  ⟨fun _ => hnr, fun _ h => absurd h hy,
    fun h => by rcases h with h | h <;> exact absurd (hm.symm.trans h) (by decide)⟩

theorem canonical_of_scan_copy {entry delay : ℕ} {x y : State GalilVM}
    (hm : x.ctl.mode = Mode.scan) (hnr : ¬ restartVM entry x.vm y.vm)
    (hw : y.vm.fpp.walker = rightPlace y.vm) : Canonical entry delay x y :=
  ⟨fun _ => hnr, fun _ _ => hw,
    fun h => by rcases h with h | h <;> exact absurd (hm.symm.trans h) (by decide)⟩

theorem canonical_of_offScan {entry delay : ℕ} {x y : State GalilVM}
    (hm : x.ctl.mode ≠ Mode.scan) (hi : x.ctl.mode ≠ Mode.init)
    (hr : x.ctl.mode ≠ Mode.replayStart) : Canonical entry delay x y :=
  ⟨fun h => absurd h hm, fun h => absurd h hm,
    fun h => by rcases h with h | h; exact absurd h hi; exact absurd h hr⟩



/-- The fallback entry leaves the search's walker where it was. -/
theorem beginFallback_walker {s t : GalilVM} (h : beginFallbackVM' s t) : t.walker = s.walker := by
  obtain ⟨p, he, -⟩ := h
  rw [(beginFallbackVM_iff p s t).1 he]
  rfl

theorem beginFallback_rightPlace {s t : GalilVM} (h : beginFallbackVM' s t) :
    rightPlace t = rightPlace s := by
  obtain ⟨p, he, _⟩ := h
  rw [(beginFallbackVM_iff p s t).1 he]
  rfl

/-- The actual fallback copy origin satisfies the canonical pin. -/
theorem fallbackAt_rightPlace (s : GalilVM)
    (hBound : (GalilScaffoldPlace.stream (rightPlace s)).length ≤ position s.right) :
    beginFallbackVM' s (beginFallbackAt (rightPlace s) s) ∧
      (beginFallbackAt (rightPlace s) s).fpp.walker = rightPlace (beginFallbackAt (rightPlace s) s) :=
  ⟨⟨rightPlace s, rfl, hBound⟩, rfl⟩

/-- Decoding a represented right head returns its logical place. -/
theorem rightPlace_of_represent {s : GalilVM} (p : GalilScaffoldPlace.Place)
    (rs : List (Option (Fin 2))) (queue : List (Fin 2))
    (h : s.right = GalilScaffoldInputHead.represent p rs queue) : rightPlace s = p := by
  rcases p with ⟨letters, gap⟩
  cases letters <;>
    simp [rightPlace, h, PalPeg.GalilFinalAssembly2.lettersOf,
      GalilScaffoldInputHead.represent, GalilScaffoldInputHead.layout,
      List.filterMap_append, List.filterMap_map]

/-- The ordinary input-representation invariant supplies the fallback's window
bound; no assumption about the old search cursor is needed. -/
theorem rightPlace_length {s : GalilVM} {raw : List (Fin 2)}
    (hRep : GalilScaffoldInputTrace.Represents s.right.head raw) :
    (GalilScaffoldPlace.stream (rightPlace s)).length = position s.right := by
  obtain ⟨letters, rs, queue, hHead, _⟩ := right_place s.right hRep
  rw [rightPlace_of_represent (s := s) _ _ _ hHead]
  cases letters with
  | nil =>
    conv_rhs => rw [hHead]
    simp [GalilScaffoldPlace.stream, position,
      GalilScaffoldInputHead.represent, GalilScaffoldInputHead.layout]
  | cons a letters =>
    conv_rhs => rw [hHead]
    exact (position_represent a letters s.right.gap (rs.map some) queue).symm

theorem fallbackAt_rightPlace_of_represented {s : GalilVM} {raw : List (Fin 2)}
    (hRep : GalilScaffoldInputTrace.Represents s.right.head raw) :
    beginFallbackVM' s (beginFallbackAt (rightPlace s) s) ∧
      (beginFallbackAt (rightPlace s) s).fpp.walker = rightPlace (beginFallbackAt (rightPlace s) s) :=
  fallbackAt_rightPlace s (rightPlace_length hRep).le

/-- The right-head pin and the old search-cursor pin are different even on a
legal bounded fallback entry.  This is a policy mismatch, not a refutation of
PAL recognition or a claim that this source is boot-reachable. -/
theorem fallback_right_not_searchPin :
    ∃ s t : GalilVM, beginFallbackVM' s t ∧
      t.fpp.walker = rightPlace t ∧ t.fpp.walker ≠ t.walker := by
  let s : GalilVM := {PalPeg.GalilBootVM.initVM0 [] with
    right := GalilScaffoldInputHead.represent ⟨[0], false⟩ [] [],
    walker := ⟨[], false⟩}
  have hRep : GalilScaffoldInputTrace.Represents s.right.head [0] :=
    ⟨[0], [], [], rfl, rfl⟩
  obtain ⟨hEntry, hPin⟩ := fallbackAt_rightPlace_of_represented hRep
  refine ⟨s, beginFallbackAt (rightPlace s) s, hEntry, hPin, ?_⟩
  intro hEqual
  have hLetters := congrArg GalilScaffoldPlace.Place.letters hEqual
  change ([0] : List (Fin 2)) = [] at hLetters
  cases hLetters

#print axioms fallback_right_not_searchPin

theorem matchedPlace_unique {P : Shared} {q : ℕ} {first : Fin 9} {b : Bool} {s t₁ t₂ : GalilVM}
    (h1 : (galilFrameS P q first).matchedPlace b s t₁)
    (h2 : (galilFrameS P q first).matchedPlace b s t₂) : t₁ = t₂ := by
  have e1 : t₁ = (if b then {s with replay := GalilScaffoldCounter.dec s.replay} else s) := h1
  have e2 : t₂ = (if b then {s with replay := GalilScaffoldCounter.dec s.replay} else s) := h2
  rw [e1, e2]

/-! ## 5. The scan-mode constructors, packaged

Four top-level shapes; the three comparison exits share the compared state, so
`compareFound_unique` pins it once for all of them. -/

variable {onLetter leftFirst : GalilVM → Prop} {centre : GalilVM → Fin 3}
  {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9} {delay : ℕ}

/-- `scan_wait` and the enabled constructors cannot both fire. -/
theorem wait_enabled_absurd {P : Shared} {c : Control} {s : GalilVM}
    (hr : c.replaying = false) (hav : ¬ (galilFrameS P q first).available s)
    (hen : c.replaying = true ∨ (galilFrameS P q first).available s) : False := by
  rcases hen with h | h
  · exact absurd (hr.symm.trans h) (by simp)
  · exact hav h

theorem tick_scan_cases {P : Shared} {c : Control} {s : GalilVM} {y : State GalilVM}
    (hm : c.mode = Mode.scan) (h : Tick (galilFrameS P q first) delay ⟨c, s⟩ y) :
    (∃ s', c.replaying = false ∧ ¬ (galilFrameS P q first).available s ∧
        (galilFrameS P q first).background s s' ∧ y = ⟨c, s'⟩) ∨
    (∃ s', (c.replaying = true ∨ (galilFrameS P q first).available s) ∧ 1 < c.clock ∧
        (galilFrameS P q first).background s s' ∧ y = ⟨{c with clock := c.clock - 1}, s'⟩) ∨
    (∃ s', (c.replaying = true ∨ (galilFrameS P q first).available s) ∧ c.clock = 1 ∧
        (galilFrameS P q first).compare s s' ∧
        ((∃ (s'' : GalilVM) (o : Bool), (galilFrameS P q first).matched s' ∧
            (galilFrameS P q first).matchedPlace c.replaying s' s'' ∧
            refresh (galilFrameS P q first) s'' c.output o ∧
            y = ⟨{c with clock := delay, output := o, replaying := c.replaying && !(galilFrameS P q first).replayExhausted s''}, s''⟩) ∨
         (∃ s'' : GalilVM, ¬ (galilFrameS P q first).matched s' ∧ c.replaying = false ∧
            (galilFrameS P q first).shiftGuard s' ∧ (galilFrameS P q first).beginShift s' s'' ∧
            y = ⟨{c with clock := delay, mode := Mode.shift}, s''⟩) ∨
         (∃ s'' : GalilVM, ¬ (galilFrameS P q first).matched s' ∧ c.replaying = false ∧
            ¬ (galilFrameS P q first).shiftGuard s' ∧ (galilFrameS P q first).beginFallback s' s'' ∧
            y = ⟨{c with clock := delay, mode := Mode.copy}, s''⟩))) ∨
    (∃ s', (galilFrameS P q first).restart s s' ∧ y = ⟨{c with clock := delay}, s'⟩) := by
  cases h with
  | scan_wait _ _ s' _ hg hb => exact Or.inl ⟨s', hg.1, hg.2, hb, rfl⟩
  | scan_count _ _ s' _ hg hc hb => exact Or.inr (Or.inl ⟨s', hg, hc, hb, rfl⟩)
  | scan_match _ _ s' s'' o _ hg hc hcmp hmt hpl ho =>
      exact Or.inr (Or.inr (Or.inl ⟨s', hg, hc, hcmp, Or.inl ⟨s'', o, hmt, hpl, ho, rfl⟩⟩))
  | scan_shift _ _ s' s'' _ hg hc hcmp hmt hr hsg hb =>
      exact Or.inr (Or.inr (Or.inl ⟨s', hg, hc, hcmp, Or.inr (Or.inl ⟨s'', hmt, hr, hsg, hb, rfl⟩)⟩))
  | scan_fallback _ _ s' s'' _ hg hc hcmp hmt hsg hr hb =>
      refine Or.inr (Or.inr (Or.inl ⟨s', hg, hc, hcmp, Or.inr (Or.inr ⟨s'', hmt, hr, ?_, hb, rfl⟩)⟩))
      rcases hsg with h0 | h0
      · exact absurd (hr.symm.trans h0) (by simp)
      · exact h0
  | restart _ _ s' _ hb => exact Or.inr (Or.inr (Or.inr ⟨s', hb, rfl⟩))
  | init _ _ _ hm' _ => exact absurd (hm.symm.trans hm') (by decide)
  | shift_one _ _ _ hm' _ _ => exact absurd (hm.symm.trans hm') (by decide)
  | shift_done _ _ _ hm' _ _ => exact absurd (hm.symm.trans hm') (by decide)
  | copy_one _ _ _ hm' _ _ => exact absurd (hm.symm.trans hm') (by decide)
  | copy_done _ _ _ hm' _ _ => exact absurd (hm.symm.trans hm') (by decide)
  | home_start _ _ _ hm' _ _ => exact absurd (hm.symm.trans hm') (by decide)
  | home_step _ _ _ hm' _ _ => exact absurd (hm.symm.trans hm') (by decide)
  | fpp_slice _ _ _ hm' _ => exact absurd (hm.symm.trans hm') (by decide)
  | fpp_done _ _ _ hm' _ => exact absurd (hm.symm.trans hm') (by decide)
  | markEnd_found _ _ _ hm' _ _ => exact absurd (hm.symm.trans hm') (by decide)
  | markEnd_step _ _ _ hm' _ _ => exact absurd (hm.symm.trans hm') (by decide)
  | choose_select _ _ _ hm' _ _ _ => exact absurd (hm.symm.trans hm') (by decide)
  | choose_step _ _ _ hm' _ _ => exact absurd (hm.symm.trans hm') (by decide)
  | rewind_done _ _ _ hm' _ _ => exact absurd (hm.symm.trans hm') (by decide)
  | rewind_one _ _ _ hm' _ _ _ => exact absurd (hm.symm.trans hm') (by decide)
  | rewind_pair _ _ _ hm' _ _ _ => exact absurd (hm.symm.trans hm') (by decide)
  | replayStart _ _ _ _ hm' _ _ _ => exact absurd (hm.symm.trans hm') (by decide)

theorem tick_init_cases {P : Shared} {c : Control} {s : GalilVM} {y : State GalilVM}
    (hm : c.mode = Mode.init) (h : Tick (galilFrameS P q first) delay ⟨c, s⟩ y) :
    ∃ t : GalilVM, (galilFrameS P q first).init s t ∧
      y = ⟨{c with mode := Mode.scan, output := true}, t⟩ := by
  cases h <;> first | (exact ⟨_, ‹_›, rfl⟩) | (exfalso; simp_all)


/-- An `init` tick is canonical: `initVM` keeps the search cursor. -/
theorem canonical_of_init {c : Control} {s : GalilVM} {y : State GalilVM}
    (hm : c.mode = Mode.init)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay ⟨c, s⟩ y) :
    Canonical entry delay ⟨c, s⟩ y := by
  obtain ⟨t, hi, hy⟩ := tick_init_cases hm h
  have e : initVM entry s t := hi
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hp, hwk⟩ := e
  refine ⟨fun h0 => absurd (hm.symm.trans h0) (by decide),
    fun h0 => absurd (hm.symm.trans h0) (by decide), fun _ => ?_⟩
  rw [hy]; exact ⟨hp, hwk⟩

theorem tick_replayStart_cases {P : Shared} {c : Control} {s : GalilVM} {y : State GalilVM}
    (hm : c.mode = Mode.replayStart) (h : Tick (galilFrameS P q first) delay ⟨c, s⟩ y) :
    ∃ (t : GalilVM) (o : Bool), (galilFrameS P q first).replayStart s t ∧
      ((galilFrameS P q first).replayPos t = true → o = c.output) ∧
      ((galilFrameS P q first).replayPos t = false → refresh (galilFrameS P q first) t c.output o) ∧
      y = ⟨{c with mode := Mode.scan, clock := delay, output := o, replaying := (galilFrameS P q first).replayPos t}, t⟩ := by
  cases h <;> first | (exact ⟨_, _, ‹_›, ‹_›, ‹_›, rfl⟩) | (exfalso; simp_all)


/-! ## 6. `Tick` refined by `Fair` is a function -/

/-- Scan determinism with restart excluded at each actual successor. -/
theorem tick_scan_noRestart_unique
    (select : GalilVM → GalilScaffoldPlace.Place)
    (hSelect : ∀ {s t}, beginFallbackVM' s t → select t = select s) {c : Control} {s : GalilVM} {y₁ y₂ : State GalilVM}
    (hm : c.mode = Mode.scan)
    (h1 : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay ⟨c, s⟩ y₁)
    (hnr1 : ¬ restartVM entry s y₁.vm)
    (hp1 : y₁.ctl.mode = Mode.copy → y₁.vm.fpp.walker = select y₁.vm)
    (h2 : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay ⟨c, s⟩ y₂)
    (hnr2 : ¬ restartVM entry s y₂.vm)
    (hp2 : y₂.ctl.mode = Mode.copy → y₂.vm.fpp.walker = select y₂.vm) : y₁ = y₂ := by
  rcases tick_scan_cases hm h1 with
      ⟨a1, ar1, aav1, abg1, ay1⟩ | ⟨b1, ben1, bck1, bbg1, by1⟩ |
      ⟨u1, cen1, cck1, ccmp1, hin1⟩ | ⟨f1, frs1, fy1⟩ <;>
    rcases tick_scan_cases hm h2 with
      ⟨a2, ar2, aav2, abg2, ay2⟩ | ⟨b2, ben2, bck2, bbg2, by2⟩ |
      ⟨u2, cen2, cck2, ccmp2, hin2⟩ | ⟨f2, frs2, fy2⟩
  -- restart is impossible below the guard
  all_goals try exact (hnr1 (by rw [fy1]; exact frs1)).elim
  all_goals try exact (hnr2 (by rw [fy2]; exact frs2)).elim
  -- wait against the enabled constructors
  all_goals try exact (wait_enabled_absurd ar1 aav1 ben2).elim
  all_goals try exact (wait_enabled_absurd ar1 aav1 cen2).elim
  all_goals try exact (wait_enabled_absurd ar2 aav2 ben1).elim
  all_goals try exact (wait_enabled_absurd ar2 aav2 cen1).elim
  -- counting against comparing
  all_goals try exact absurd bck1 (by omega)
  all_goals try exact absurd bck2 (by omega)
  -- the two background branches
  all_goals try exact (by rw [ay1, ay2, backgroundS_unique abg1 abg2])
  all_goals try exact (by rw [by1, by2, backgroundS_unique bbg1 bbg2])
  -- the three comparison exits, on the state pinned by `compareFound_unique`
  have hu : u1 = u2 := compareFound_unique ccmp1 ccmp2
  subst hu
  rcases hin1 with ⟨t1, o1, cmt1, cpl1, cho1, cy1⟩ | ⟨t1, dmt1, dr1, dsg1, dbs1, dy1⟩ |
      ⟨t1, emt1, er1, esg1, ebf1, ey1⟩ <;>
    rcases hin2 with ⟨t2, o2, cmt2, cpl2, cho2, cy2⟩ | ⟨t2, dmt2, dr2, dsg2, dbs2, dy2⟩ |
      ⟨t2, emt2, er2, esg2, ebf2, ey2⟩
  -- matched against mismatched
  all_goals try exact absurd cmt1 dmt2
  all_goals try exact absurd cmt1 emt2
  all_goals try exact absurd cmt2 dmt1
  all_goals try exact absurd cmt2 emt1
  -- shift against fallback
  all_goals try exact absurd dsg1 esg2
  all_goals try exact absurd dsg2 esg1
  -- match / match
  · have ht : t1 = t2 := matchedPlace_unique cpl1 cpl2
    subst ht
    rw [cy1, cy2, LocalRealizesPhase.refresh_unique cho1 cho2]
  -- shift / shift
  · have hbs1 : beginShiftVM' u1 t1 := dbs1
    have hbs2 : beginShiftVM' u1 t2 := dbs2
    rw [dy1, dy2, beginShiftVM'_unique hbs1 hbs2]
  -- fallback / fallback: both copy places use the same preserved selector
  · have hbf1 : beginFallbackVM' u1 t1 := ebf1
    have hbf2 : beginFallbackVM' u1 t2 := ebf2
    have hw1 : t1.fpp.walker = select t1 := by
      have h0 := hp1 (by rw [ey1])
      rw [ey1] at h0; exact h0
    have hw2 : t2.fpp.walker = select t2 := by
      have h0 := hp2 (by rw [ey2])
      rw [ey2] at h0; exact h0
    have hv1 : select t1 = select u1 := hSelect hbf1
    have hv2 : select t2 = select u1 := hSelect hbf2
    rw [ey1, ey2, beginFallbackVM'_unique_of_walker hbf1 hbf2
      ((hw1.trans hv1).trans (hw2.trans hv2).symm)]

/-- **The `scan` mode, refined.**  The restart guard decides the branch; below
it the five scan constructors are pairwise separated by their own guards and
each is functional. -/
theorem tick_fair_scan_unique {c : Control} {s : GalilVM} {y₁ y₂ : State GalilVM}
    (hm : c.mode = Mode.scan)
    (h1 : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay ⟨c, s⟩ y₁)
    (hf1 : Fair entry delay ⟨c, s⟩ y₁)
    (h2 : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay ⟨c, s⟩ y₂)
    (hf2 : Fair entry delay ⟨c, s⟩ y₂) : y₁ = y₂ := by
  by_cases hg : restartGuardVM s
  · obtain ⟨hc1, hr1⟩ := hf1.restartFirst hm hg
    obtain ⟨hc2, hr2⟩ := hf2.restartFirst hm hg
    exact state_ext (hc1.trans hc2.symm) (restartVM_unique entry hr1 hr2)
  · have hnr : ∀ t : GalilVM,
        ¬ (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).restart s t := by
      intro t ht
      exact hg (restartGuard_of_restartVM (entry := entry) ht)
    exact tick_scan_noRestart_unique (fun s => s.walker) beginFallback_walker hm h1 (hnr _) (hf1.fallbackPlace hm)
      h2 (hnr _) (hf2.fallbackPlace hm)

/-- **The `init` mode, refined**: `initVM` pins 13 of the 15 `GalilVM` fields
and `Fair` pins the remaining two. -/
theorem tick_fair_init_unique {c : Control} {s : GalilVM} {y₁ y₂ : State GalilVM}
    (hm : c.mode = Mode.init)
    (h1 : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay ⟨c, s⟩ y₁)
    (hf1 : Fair entry delay ⟨c, s⟩ y₁)
    (h2 : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay ⟨c, s⟩ y₂)
    (hf2 : Fair entry delay ⟨c, s⟩ y₂) : y₁ = y₂ := by
  obtain ⟨t1, hi1, hy1⟩ := tick_init_cases hm h1
  obtain ⟨t2, hi2, hy2⟩ := tick_init_cases hm h2
  have e1 : initVM entry s t1 := hi1
  have e2 : initVM entry s t2 := hi2
  obtain ⟨r1, l1, cc1, len1, rad1, rem1, rep1, cyc1, fpp1, ch1, se1, lo1, dp1, hp1, hwk1⟩ := e1
  obtain ⟨r2, l2, cc2, len2, rad2, rem2, rep2, cyc2, fpp2, ch2, se2, lo2, dp2, hp2, hwk2⟩ := e2
  rw [hy1, hy2, galilVM_ext (l1.trans l2.symm) (cc1.trans cc2.symm) (r1.trans r2.symm)
    (ch1.trans ch2.symm) (cyc1.trans cyc2.symm) (rem1.trans rem2.symm) (rad1.trans rad2.symm)
    (len1.trans len2.symm) (rep1.trans rep2.symm) (fpp1.trans fpp2.symm) (se1.trans se2.symm)
    (dp1.trans dp2.symm) (lo1.trans lo2.symm) (hp1.trans hp2.symm) (hwk1.trans hwk2.symm)]

/-- **The `replayStart` mode, refined**, the same way; the output bit then
follows from `refresh_unique`. -/
theorem tick_fair_replayStart_unique {c : Control} {s : GalilVM} {y₁ y₂ : State GalilVM}
    (hm : c.mode = Mode.replayStart)
    (h1 : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay ⟨c, s⟩ y₁)
    (hf1 : Fair entry delay ⟨c, s⟩ y₁)
    (h2 : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay ⟨c, s⟩ y₂)
    (hf2 : Fair entry delay ⟨c, s⟩ y₂) : y₁ = y₂ := by
  obtain ⟨t1, o1, hi1, hpos1, hneg1, hy1⟩ := tick_replayStart_cases hm h1
  obtain ⟨t2, o2, hi2, hpos2, hneg2, hy2⟩ := tick_replayStart_cases hm h2
  have e1 : replayStartVM entry s t1 := hi1
  have e2 : replayStartVM entry s t2 := hi2
  obtain ⟨rep1, r1, l1, cc1, rad1, len1, rem1, cyc1, fpp1, ch1, se1, lo1, dp1, hp1, hwk1⟩ := e1
  obtain ⟨rep2, r2, l2, cc2, rad2, len2, rem2, cyc2, fpp2, ch2, se2, lo2, dp2, hp2, hwk2⟩ := e2
  have ht : t1 = t2 :=
    galilVM_ext (l1.trans l2.symm) (cc1.trans cc2.symm) (r1.trans r2.symm)
      (ch1.trans ch2.symm) (cyc1.trans cyc2.symm) (rem1.trans rem2.symm) (rad1.trans rad2.symm)
      (len1.trans len2.symm) (rep1.trans rep2.symm) (fpp1.trans fpp2.symm) (se1.trans se2.symm)
      (dp1.trans dp2.symm) (lo1.trans lo2.symm) (hp1.trans hp2.symm) (hwk1.trans hwk2.symm)
  subst ht
  have ho : o1 = o2 := by
    by_cases hp : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).replayPos t1 = true
    · rw [hpos1 hp, hpos2 hp]
    · have hp' : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).replayPos t1 = false :=
        Bool.eq_false_iff.mpr hp
      exact LocalRealizesPhase.refresh_unique (hneg1 hp') (hneg2 hp')
  rw [hy1, hy2, ho]

/-- **The main theorem.**  `Tick (galilFrameS (sharedC …) q first) delay`
refined by `Fair entry delay` is functional — for *every* state, with no
reachability hypothesis. -/
theorem tick_fair_unique {x y₁ y₂ : State GalilVM}
    (h1 : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay x y₁)
    (hf1 : Fair entry delay x y₁)
    (h2 : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay x y₂)
    (hf2 : Fair entry delay x y₂) : y₁ = y₂ := by
  obtain ⟨c, s⟩ := x
  cases hm : c.mode with
  | init => exact tick_fair_init_unique hm h1 hf1 h2 hf2
  | scan => exact tick_fair_scan_unique hm h1 hf1 h2 hf2
  | shift => exact LocalRealizesPhase.tick_shift_unique hm h1 h2
  | copy => exact LocalRealizesPhase.tick_copy_unique hm h1 h2
  | home => exact LocalRealizesPhase.tick_home_unique hm h1 h2
  | fpp => exact LocalRealizesPhase.tick_fpp_unique hm h1 h2
  | markEnd => exact LocalRealizesPhase.tick_markEnd_unique hm h1 h2
  | choose => exact LocalRealizesScan.tick_det_choose _ q first delay hm h1 h2
  | rewind => exact LocalRealizesScan.tick_det_rewind _ q first delay hm h1 h2
  | replayStart => exact tick_fair_replayStart_unique hm h1 hf1 h2 hf2

/-- Away from scan, the two scheduling refinements agree. -/
theorem Canonical.toFair_offScan {x y : State GalilVM}
    (h : Canonical entry delay x y) (hm : x.ctl.mode ≠ Mode.scan) :
    Fair entry delay x y :=
  ⟨fun hs => (hm hs).elim, fun hs _ => (hm hs).elim, h.keepsSearchCursor⟩

/-- The oracle's canonical tick is functional, without a reachability hypothesis. -/
theorem tick_canonical_unique {x y₁ y₂ : State GalilVM}
    (h1 : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay x y₁)
    (hc1 : Canonical entry delay x y₁)
    (h2 : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay x y₂)
    (hc2 : Canonical entry delay x y₂) : y₁ = y₂ := by
  by_cases hm : x.ctl.mode = Mode.scan
  · exact tick_scan_noRestart_unique rightPlace beginFallback_rightPlace hm h1 (hc1.noRestart hm) (hc1.fallbackPlace hm)
      h2 (hc2.noRestart hm) (hc2.fallbackPlace hm)
  · exact tick_fair_unique h1 (hc1.toFair_offScan hm) h2 (hc2.toFair_offScan hm)

#print axioms tick_canonical_unique

/-! ## 7. `Fair` is not vacuous

Each of the three clauses is met by the witness the construction actually
builds, so `tick_fair_unique` is not vacuously true. -/

/-- The prelude restart is a `Fair` tick, so the `scan` mode is still inhabited
under the guard. -/
theorem fair_restart {c : Control} {s : GalilVM} (hm : c.mode = Mode.scan)
    (hg : restartGuardVM s) :
    ∃ y, Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay ⟨c, s⟩ y ∧
      Fair entry delay ⟨c, s⟩ y := by
  obtain ⟨t, ht⟩ := restartVM_exists entry s hg
  refine ⟨⟨{c with clock := delay}, t⟩, .restart c s t hm ht, ⟨?_, ?_, ?_⟩⟩
  · intro _ _; exact ⟨rfl, ht⟩
  · intro _ h0; exact absurd (hm.symm.trans h0) (by decide)
  · intro h0; rcases h0 with h0 | h0 <;> exact absurd (hm.symm.trans h0) (by decide)

/-- The fallback place clause is met by the entry that copies from the search's
own walker. -/
theorem fallbackAt_walker_self (s : GalilVM)
    (hplaceBound : (GalilScaffoldPlace.stream s.walker).length ≤ position s.right) :
    beginFallbackVM' s (beginFallbackAt s.walker s) ∧
      (beginFallbackAt s.walker s).fpp.walker = (beginFallbackAt s.walker s).walker :=
  ⟨⟨s.walker, rfl, hplaceBound⟩, rfl⟩

/-- The `init` clause is met by the witness of
`GalilScaffoldTopScanRun.init_tick` (hence of `init_restarted`). -/
theorem initVM_keeps_cursor (entry : ℕ) (s : GalilVM) :
    ∃ t, initVM entry s t ∧ t.periodOnly = s.periodOnly ∧ t.walker = s.walker :=
  ⟨⟨GalilScaffoldChainVerifier.right s.right, GalilScaffoldChainVerifier.right s.right,
      GalilScaffoldChainVerifier.right s.right, .idle, s.cycle, s.remaining, s.radius,
      GalilScaffoldCounter.inc s.length, s.replay, s.fpp,
      GalilScaffoldSearchFinish.begin GalilScaffoldCounter.reset s.radius,
      GalilScaffoldControl.reset entry s.dp, GalilScaffoldCounter.reset, s.periodOnly, s.walker⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

/-- The `replayStart` clause is met by the witness of
`GalilScaffoldTopReplay.replayStart_tick` (hence of
`fallback_replayStart_All`). -/
theorem replayStartVM_keeps_cursor (entry : ℕ) (s : GalilVM) :
    ∃ t, replayStartVM entry s t ∧ t.periodOnly = s.periodOnly ∧ t.walker = s.walker :=
  ⟨⟨s.center, s.center, s.center, .idle, s.cycle, s.remaining, GalilScaffoldCounter.reset,
      GalilScaffoldCounter.ofNat 1, s.radius, s.fpp,
      GalilScaffoldSearchFinish.begin GalilScaffoldCounter.reset GalilScaffoldCounter.reset,
      GalilScaffoldControl.reset entry s.dp, GalilScaffoldCounter.reset, s.periodOnly, s.walker⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

/-- **`Fair` の第 3 場は `Tick` からタダ。**

`initVM`（`GalilScaffoldTopReplay:20`）と `replayStartVM`（`:33`）の定義そのものの
15 連言の最後 2 つが `t.periodOnly = s.periodOnly ∧ t.walker = s.walker`。
だから `keepsSearchCursor` は供給する必要がない。

**CLAUDE.md §2 の「(e) …`initVM`/`replayStartVM`（`periodOnly`, `walker` 自由）が
非関数的」は古い記述だった**（2026-09-19, n173 で訂正）。`Fair` の実質は 2 場:
`restartFirst`（`fair_restart`）と `fallbackPlace`（`fallbackAt_walker_self`）。 -/
theorem keepsSearchCursor_of_tick {c : Control} {s : GalilVM} {y : State GalilVM}
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay ⟨c, s⟩ y)
    (hm : c.mode = Mode.init ∨ c.mode = Mode.replayStart) :
    y.vm.periodOnly = s.periodOnly ∧ y.vm.walker = s.walker := by
  rcases hm with hm | hm
  · obtain ⟨t, hi, hy⟩ := tick_init_cases hm h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hpo, hw⟩ : initVM entry s t := hi
    rw [hy]; exact ⟨hpo, hw⟩
  · obtain ⟨t, o, hi, -, -, hy⟩ := tick_replayStart_cases hm h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hpo, hw⟩ : replayStartVM entry s t := hi
    rw [hy]; exact ⟨hpo, hw⟩

#print axioms keepsSearchCursor_of_tick
#print axioms fair_restart
#print axioms initVM_keeps_cursor
#print axioms replayStartVM_keeps_cursor

#print axioms tick_scan_cases
#print axioms compareFound_unique
#print axioms tick_fair_scan_unique
#print axioms tick_fair_init_unique
#print axioms tick_fair_replayStart_unique
#print axioms tick_fair_unique

end PalPeg.GalilTickFair
