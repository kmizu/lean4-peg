import PalPeg.CloseoutPackRun25

/-!
# `CloseoutPackRun28`: `WalkerInOrigin` along `Fair` runs

`CloseoutPackRun25` named `WalkerInOrigin` at the `copy` states of a run: the
search's own cursor `walker` never crosses the origin
(`|stream s.walker| ≤ position s.right`).  Here it is proved as a global
invariant `WalkerInv` of the search co-process along `Fair` runs.

The invariant has three shapes:
* `Boot`: in `init` mode the walker is empty (`emptyPlace` at boot);
* `Bounded`: `|stream walker| ≤ position R` (all other modes);
* `Fresh`: right after `replayStart` (which moves `R` *left* to `C` while
  `Fair.keepsSearchCursor` keeps the stale walker), the search has just been
  reset to `grow` with `work = inc reset`, chain idle, and the clock leaves
  room for the one `growStep` and the `prepare` that reloads the walker from
  `place s` *before* the next comparison (`hdelay : 2 ≤ delay`).

Branches: `init`/`replayStart` keep the cursor (`Fair`); `prepare` (from
`grow`/`double` with `work` exhausted) loads `walker := place s`, bounded by
`hplace`; preparation ticks move it left (`left_stream`); `run`/`wait`/idle
modes keep it; scan comparisons move `R` right (`position_le_right`, which
needs `canRight R`: `available` for non-replaying ticks, `hcan` for the
replaying `scan_match`); every other tick keeps `walker` and `R`.

## Honest status

Standard axioms only; unconditional `PAL ∈ PEG` remains open.  Named
hypothesis: `hplace : ∀ s, |stream (place s)| ≤ position s.right` (the
centre place fits before `R`; `place` is a parameter of `sharedC`).  Side
conditions: `hdelay : 2 ≤ delay` (the closeout fixes `delay = 2048`) and
`hcan` (a replaying `scan_match` fires only with `canRight R`; the model's
`right` on a dead-end gap head lowers `position` by one).
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun28

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldCounter
open PalPeg.CloseoutPackRun25 (WalkerInOrigin FairSteps)
open PalPeg.GalilTickFair (Fair)

/-! ## 1. The invariant -/

/-- The search cursor is before `R`. -/
def Bounded (s : GalilVM) : Prop :=
  (GalilScaffoldPlace.stream s.walker).length ≤ position s.right

/-- Right after `replayStart`: the search is reset to `grow`, the chain idle,
and the walker will be reloaded by `prepare` before the next comparison. -/
def Fresh (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.scan ∧ s.chain = .idle ∧ s.search.mode = .grow ∧
    ((s.search.work = inc reset ∧ 2 ≤ c.clock) ∨ positive s.search.work = false)

/-- The global invariant. -/
def WalkerInv (c : Control) (s : GalilVM) : Prop :=
  (c.mode = Mode.init ∧ GalilScaffoldPlace.stream s.walker = []) ∨
  (c.mode ≠ Mode.init ∧ Bounded s) ∨ Fresh c s

theorem walkerInOrigin_of_inv {c : Control} {s : GalilVM} (h : WalkerInv c s)
    (hm : c.mode = Mode.copy) : WalkerInOrigin s := by
  rcases h with ⟨h1, -⟩ | ⟨-, hb⟩ | ⟨h1, -⟩
  · rw [hm] at h1; cases h1
  · exact hb
  · rw [hm] at h1; cases h1

/-! ## 2. Heads and places -/

theorem position_le_right (p : PlaceHead) (hc : GalilScaffoldChainVerifier.canRight p) :
    position p ≤ position (GalilScaffoldChainVerifier.right p) := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g with
  | false =>
    simp only [position, GalilScaffoldChainVerifier.right, Bool.false_eq_true, if_false,
      Bool.not_false, if_true]
    omega
  | true =>
    cases rs with
    | cons a rs =>
      simp [position, GalilScaffoldChainVerifier.right, GalilScaffoldChainVerifier.headRight,
        GalilScaffoldInputTrace.moveRight]
      omega
    | nil =>
      cases q with
      | cons a q =>
        simp [position, GalilScaffoldChainVerifier.right, GalilScaffoldChainVerifier.headRight,
          GalilScaffoldInputTrace.moveRight]
        omega
      | nil =>
        exfalso
        simp [GalilScaffoldChainVerifier.canRight] at hc

theorem stream_left_length (p : GalilScaffoldPlace.Place) :
    (GalilScaffoldPlace.stream (GalilScaffoldPlace.left p)).length ≤
      (GalilScaffoldPlace.stream p).length := by
  rw [GalilScaffoldPlace.left_stream, List.length_tail]
  omega

/-! ## 3. The search step and the walker -/

theorem prepTick_walker {b : Bool} {x y : GalilScaffoldPrepareControl.State}
    (ht : GalilScaffoldPrepareControl.Tick b x y) :
    y.walker = x.walker ∨ y.walker = GalilScaffoldPlace.left x.walker := by
  cases ht <;> simp

theorem afterAdvance_walker (b : Bool) (s : GalilScaffoldPrepareControl.State) :
    (GalilScaffoldPreparePaced.afterAdvance b s).walker = s.walker := by
  unfold GalilScaffoldPreparePaced.afterAdvance
  split <;> rfl

theorem afterAdvance_mode (b : Bool) (s : GalilScaffoldPrepareControl.State) :
    (GalilScaffoldPreparePaced.afterAdvance b s).mode = s.mode := by
  unfold GalilScaffoldPreparePaced.afterAdvance
  split <;> rfl

theorem afterAdvance_work (b : Bool) (s : GalilScaffoldPrepareControl.State) :
    (GalilScaffoldPreparePaced.afterAdvance b s).work = s.work := by
  unfold GalilScaffoldPreparePaced.afterAdvance
  split <;> rfl

/-- One search step keeps the walker, moves it left, or loads `center`. -/
theorem searchStep_walker {center : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (h : searchStep center a v v') :
    v'.walker = v.walker ∨ v'.walker = GalilScaffoldPlace.left v.walker ∨ v'.walker = center := by
  unfold searchStep at h
  cases hm : v.search.mode <;> rw [hm] at h
  case idle => exact Or.inl (by rw [show v' = v from h])
  case found => exact Or.inl (by rw [show v' = v from h])
  case missed => exact Or.inl (by rw [show v' = v from h])
  case grow =>
    have h' : (if positive v.search.work = true then
        v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
          (GalilScaffoldStagePrepare.growStep v.toPrep)) v.search.quarter v.lower
      else
        v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
          (GalilScaffoldPrepareControl.prepare v.toPrep v.lower center)) v.search.quarter v.lower) := h
    split at h'
    · left; rw [h']; exact afterAdvance_walker a _
    · right; right; rw [h']; exact afterAdvance_walker a _
  case lower | lowerHome | copy | home =>
    obtain ⟨y, ht, hv⟩ : ∃ y, GalilScaffoldPrepareControl.Tick true v.toPrep y ∧
        v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a y) v.search.quarter v.lower := h
    have e : (SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a y) v.search.quarter v.lower).walker
        = y.walker := afterAdvance_walker a y
    rw [hv, e]
    rcases prepTick_walker ht with hw | hw
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
  case run =>
    have h' : GalilScaffoldSearchRun.SafeQuanta v.search v.dp [a] v'.search v'.dp ∧
        v'.lower = v.lower ∧ v'.walker = v.walker := h
    exact Or.inl h'.2.2
  case wait =>
    have h' : v' = {v with search := GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.waitStep true v.search)} := h
    exact Or.inl (by rw [h'])
  case double =>
    have h' : (if positive v.search.work = true then
        v' = {v with search := GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)}
      else
        v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
          (GalilScaffoldPrepareControl.prepare v.toPrep v.lower center)) v.search.quarter v.lower) := h
    split at h'
    · exact Or.inl (by rw [h'])
    · right; right; rw [h']; exact afterAdvance_walker a _

/-- From `grow`: a positive `work` is one `growStep` (walker kept), an
exhausted one is `prepare` (walker loaded). -/
theorem searchStep_grow {center : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (h : searchStep center a v v') (hm : v.search.mode = .grow) :
    (positive v.search.work = true ∧ v'.search.mode = .grow ∧
      v'.search.work = dec v.search.work ∧ v'.walker = v.walker) ∨
    (positive v.search.work = false ∧ v'.walker = center) := by
  unfold searchStep at h
  rw [hm] at h
  have h' : (if positive v.search.work = true then
      v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
        (GalilScaffoldStagePrepare.growStep v.toPrep)) v.search.quarter v.lower
    else
      v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
        (GalilScaffoldPrepareControl.prepare v.toPrep v.lower center)) v.search.quarter v.lower) := h
  split at h'
  · rename_i hp
    left
    refine ⟨hp, ?_, ?_, ?_⟩
    · rw [h']
      show (GalilScaffoldPreparePaced.afterAdvance a (GalilScaffoldStagePrepare.growStep v.toPrep)).mode = _
      rw [afterAdvance_mode]
      exact hm
    · rw [h']
      show (GalilScaffoldPreparePaced.afterAdvance a (GalilScaffoldStagePrepare.growStep v.toPrep)).work = _
      rw [afterAdvance_work]
      rfl
    · rw [h']; exact afterAdvance_walker a _
  · rename_i hp
    right
    refine ⟨by simpa using hp, ?_⟩
    rw [h']; exact afterAdvance_walker a _

theorem searchEffect_walker (P : Shared) {a : Bool} {s : GalilVM} {vq : SearchVM}
    (h : searchEffect P a s vq) :
    vq.walker = s.walker ∨ vq.walker = GalilScaffoldPlace.left s.walker ∨ vq.walker = P.place s := by
  rcases h with ⟨-, hs⟩ | ⟨-, he⟩
  · exact searchStep_walker hs
  · exact Or.inl (by rw [he]; rfl)

theorem searchEffect_fresh (P : Shared) {a : Bool} {s : GalilVM} {vq : SearchVM}
    (h : searchEffect P a s vq) (hidle : s.chain = .idle) (hgrow : s.search.mode = .grow) :
    (positive s.search.work = true ∧ vq.search.mode = .grow ∧
      vq.search.work = dec s.search.work ∧ vq.walker = s.walker) ∨
    (positive s.search.work = false ∧ vq.walker = P.place s) := by
  rcases h with ⟨-, hs⟩ | ⟨hne, -⟩
  · exact searchStep_grow hs hgrow
  · exact absurd hidle hne

/-! ## 4. Bounded steps -/

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

theorem bounded_step (hplace : ∀ u, (GalilScaffoldPlace.stream (place u)).length ≤ position u.right)
    {s t : GalilVM}
    (hw : t.walker = s.walker ∨ t.walker = GalilScaffoldPlace.left s.walker ∨ t.walker = place s)
    (hr : position s.right ≤ position t.right) (hb : Bounded s) : Bounded t := by
  unfold Bounded at *
  rcases hw with hw | hw | hw <;> rw [hw]
  · omega
  · have := stream_left_length s.walker; omega
  · have := hplace s; omega

theorem walkerInv_keep {c c' : Control} {s t : GalilVM}
    (hw : t.walker = s.walker) (hr : t.right = s.right)
    (hm : c.mode ≠ Mode.init) (hs : c.mode ≠ Mode.scan) (hm' : c'.mode ≠ Mode.init)
    (hI : WalkerInv c s) : WalkerInv c' t := by
  rcases hI with ⟨h1, -⟩ | ⟨-, hb⟩ | ⟨h1, -⟩
  · exact absurd h1 hm
  · refine Or.inr (Or.inl ⟨hm', ?_⟩)
    unfold Bounded at *
    rw [hw, hr]; exact hb
  · exact absurd h1 hs

theorem walkerInv_pull {σ' : Type} (L : Lens GalilVM σ') {c c' : Control} {s t : GalilVM}
    (h2 : t = L.set s (L.get t))
    (hw : (L.set s (L.get t)).walker = s.walker)
    (hr : (L.set s (L.get t)).right = s.right)
    (hm : c.mode ≠ Mode.init) (hs : c.mode ≠ Mode.scan) (hm' : c'.mode ≠ Mode.init)
    (hI : WalkerInv c s) : WalkerInv c' t :=
  walkerInv_keep ((congrArg GalilVM.walker h2).trans hw) ((congrArg GalilVM.right h2).trans hr)
    hm hs hm' hI

theorem positive_dec_inc_reset : positive (dec (inc reset)) = false := rfl

theorem begin_reset_work : (GalilScaffoldSearchFinish.begin reset reset).work = inc reset := rfl

theorem begin_reset_mode : (GalilScaffoldSearchFinish.begin reset reset).mode = .grow := rfl

/-- A scan-sourced tick whose search effect is `searchEffect` and whose `R`
does not move left. -/
theorem walkerInv_scan
    (hplace : ∀ u, (GalilScaffoldPlace.stream (place u)).length ≤ position u.right)
    {c c' : Control} {s t : GalilVM} {a : Bool}
    (hm : c.mode = Mode.scan) (hm' : c'.mode = Mode.scan)
    (hse : searchEffect (sharedC onLetter leftFirst centre place entry) a s (searchLens.get t))
    (hr : position s.right ≤ position t.right)
    (hch : s.chain = .idle → t.search.mode = .grow → t.chain = .idle ∨ c.clock < 2)
    (hI : WalkerInv c s) : WalkerInv c' t := by
  have hP : (sharedC onLetter leftFirst centre place entry).place s = place s := rfl
  rcases hI with ⟨h1, -⟩ | ⟨-, hb⟩ | hfr
  · rw [hm] at h1; cases h1
  · refine Or.inr (Or.inl ⟨by rw [hm']; simp, ?_⟩)
    have hw := searchEffect_walker _ hse
    rw [hP] at hw
    exact bounded_step place hplace hw hr hb
  · obtain ⟨-, hidle, hgrow, hwork⟩ := hfr
    rcases searchEffect_fresh _ hse hidle hgrow with ⟨hp, hg, hk, hw⟩ | ⟨hp, hw⟩
    · have hg' : t.search.mode = .grow := hg
      have hk' : t.search.work = dec s.search.work := hk
      rcases hwork with ⟨hw1, hclk⟩ | hw2
      · rcases hch hidle hg' with hti | hclk'
        · refine Or.inr (Or.inr ⟨hm', hti, hg', Or.inr ?_⟩)
          rw [hk', hw1]
          exact positive_dec_inc_reset
        · omega
      · rw [hw2] at hp; cases hp
    · refine Or.inr (Or.inl ⟨by rw [hm']; simp, ?_⟩)
      unfold Bounded
      have hw' : t.walker = place s := hw
      rw [hw']
      have := hplace s
      omega

/-- The compared state: `R` moved right, the search stepped. -/
theorem compareFound_fields {s s' : GalilVM}
    (hcmp : compareFound (sharedC onLetter leftFirst centre place entry) q first s s') :
    s'.right = GalilScaffoldChainVerifier.right s.right ∧
    ∃ a : Bool, searchEffect (sharedC onLetter leftFirst centre place entry) a s (searchLens.get s') := by
  obtain ⟨vs, vq, a, -, hvr, -, hse, -, hteq⟩ := hcmp
  refine ⟨?_, a, ?_⟩
  · rw [hteq, afterBirth_right]; cases a <;> exact hvr
  · have hq : searchLens.get s' = vq := by rw [hteq, afterBirth_searchGet]; cases a <;> rfl
    rw [hq]; exact hse

/-- **The invariant along one `Fair` tick.** -/
theorem walkerInv_tick
    (hplace : ∀ u, (GalilScaffoldPlace.stream (place u)).length ≤ position u.right)
    (hdelay : 2 ≤ delay) {c c' : Control} {s t : GalilVM}
    (hcan : c.replaying = true → GalilScaffoldChainVerifier.canRight s.right)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩)
    (hI : WalkerInv c s) : WalkerInv c' t := by
  cases h
  case init =>
    rename_i hm hi
    have hi' : initVM entry s t := hi
    have hw : t.walker = s.walker :=
      (PalPeg.GalilTickDet.initVM_keepsSearchCursor hi').2
    rcases hI with ⟨-, h0⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · refine Or.inr (Or.inl ⟨by simp, ?_⟩)
      unfold Bounded
      rw [hw, h0]
      simp
    · exact absurd hm h1
    · rw [hm] at h1; cases h1
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, hr, hch, -, -, -, -, -, -, -, -, hse⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    refine walkerInv_scan onLetter leftFirst centre place entry hplace hm hm hse (by rw [hr])
      ?_ hI
    intro hidle hg
    left
    rcases hch with ⟨hne, -⟩ | ⟨-, -, hz⟩ | ⟨-, hfd, -⟩
    · exact absurd hidle hne
    · exact hz
    · have : (searchLens.get t).search.mode = .grow := hg
      rw [this] at hfd; cases hfd
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, hr, hch, -, -, -, -, -, -, -, -, hse⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    refine walkerInv_scan onLetter leftFirst centre place entry hplace hm hm hse (by rw [hr])
      ?_ hI
    intro hidle hg
    left
    rcases hch with ⟨hne, -⟩ | ⟨-, -, hz⟩ | ⟨-, hfd, -⟩
    · exact absurd hidle hne
    · exact hz
    · have : (searchLens.get t).search.mode = .grow := hg
      rw [this] at hfd; cases hfd
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨hs'r, a, hse⟩ := compareFound_fields onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have htw : searchLens.get t = searchLens.get s' := by rw [hpl']; split <;> rfl
    have htr : t.right = s'.right := by rw [hpl']; split <;> rfl
    have htc : t.chain = s'.chain := by rw [hpl']; split <;> rfl
    have hcr : GalilScaffoldChainVerifier.canRight s.right := by
      rcases hav with hrep | hav
      · exact hcan hrep
      · exact hav
    rw [← htw] at hse
    refine walkerInv_scan onLetter leftFirst centre place entry hplace hm hm hse ?_ ?_ hI
    · rw [htr, hs'r]; exact position_le_right s.right hcr
    · intro _ _; right; omega
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨hs'r, a, hse⟩ := compareFound_fields onLetter leftFirst centre place entry q first hcmp
    obtain ⟨w, -, ht⟩ : beginShiftVM' s' t := hb
    have htw : searchLens.get t = searchLens.get s' := by rw [ht]; rfl
    have htr : t.right = s'.right := by rw [ht]
    have hcr : GalilScaffoldChainVerifier.canRight s.right := by
      rcases hav with hrep | hav
      · rw [hr] at hrep; cases hrep
      · exact hav
    rw [← htw] at hse
    rcases hI with ⟨h1, -⟩ | ⟨-, hb'⟩ | ⟨-, hidle, hgrow, hwork⟩
    · rw [hm] at h1; cases h1
    · refine Or.inr (Or.inl ⟨by simp, ?_⟩)
      have hw := searchEffect_walker _ hse
      have hP : (sharedC onLetter leftFirst centre place entry).place s = place s := rfl
      rw [hP] at hw
      exact bounded_step place hplace hw (by rw [htr, hs'r]; exact position_le_right s.right hcr) hb'
    · rcases searchEffect_fresh _ hse hidle hgrow with ⟨hp, -, -, -⟩ | ⟨-, hw⟩
      · rcases hwork with ⟨-, hclk⟩ | hw2
        · omega
        · rw [hw2] at hp; cases hp
      · refine Or.inr (Or.inl ⟨by simp, ?_⟩)
        unfold Bounded
        have hw' : t.walker = place s := hw
        rw [hw', htr, hs'r]
        have := hplace s
        have := position_le_right s.right hcr
        omega
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨hs'r, a, hse⟩ := compareFound_fields onLetter leftFirst centre place entry q first hcmp
    obtain ⟨pl, ht, -⟩ : beginFallbackVM' s' t := hb
    unfold GalilScaffoldChainInputSupply.beginFallbackVM at ht
    have htw : t.walker = s'.walker := by rw [ht]
    have htr : t.right = s'.right := by rw [ht]
    have hcr : GalilScaffoldChainVerifier.canRight s.right := by
      rcases hav with hrep | hav
      · rw [hr] at hrep; cases hrep
      · exact hav
    have hpos : position s.right ≤ position t.right := by
      rw [htr, hs'r]; exact position_le_right s.right hcr
    rcases hI with ⟨h1, -⟩ | ⟨-, hb'⟩ | ⟨-, hidle, hgrow, hwork⟩
    · rw [hm] at h1; cases h1
    · refine Or.inr (Or.inl ⟨by simp, ?_⟩)
      have hw := searchEffect_walker _ hse
      have hP : (sharedC onLetter leftFirst centre place entry).place s = place s := rfl
      rw [hP] at hw
      have hw' : t.walker = s.walker ∨ t.walker = GalilScaffoldPlace.left s.walker ∨
          t.walker = place s := by rw [htw]; exact hw
      exact bounded_step place hplace hw' hpos hb'
    · rcases searchEffect_fresh _ hse hidle hgrow with ⟨hp, -, -, -⟩ | ⟨-, hw⟩
      · rcases hwork with ⟨-, hclk⟩ | hw2
        · omega
        · rw [hw2] at hp; cases hp
      · refine Or.inr (Or.inl ⟨by simp, ?_⟩)
        unfold Bounded
        have hw' : s'.walker = place s := hw
        rw [htw, hw']
        have := hplace s
        omega
  case shift_one =>
    rename_i hm hp hi
    exact walkerInv_pull shiftLens hi.2 rfl rfl (by rw [hm]; simp) (by rw [hm]; simp)
      (by rw [hm]; simp) hI
  case shift_done =>
    rename_i hm hp ho
    exact walkerInv_keep rfl rfl (by rw [hm]; simp) (by rw [hm]; simp) (by simp) hI
  case copy_one =>
    rename_i hm hp hi
    exact walkerInv_pull fppLens hi.2 rfl rfl (by rw [hm]; simp) (by rw [hm]; simp)
      (by rw [hm]; simp) hI
  case copy_done =>
    rename_i hm hp hi
    exact walkerInv_pull fppLens hi.2 rfl rfl (by rw [hm]; simp) (by rw [hm]; simp) (by simp) hI
  case home_start =>
    rename_i hm hl hi
    exact walkerInv_pull fppLens hi.2 rfl rfl (by rw [hm]; simp) (by rw [hm]; simp) (by simp) hI
  case home_step =>
    rename_i hm hl hi
    exact walkerInv_pull fppLens hi.2 rfl rfl (by rw [hm]; simp) (by rw [hm]; simp)
      (by rw [hm]; simp) hI
  case fpp_slice =>
    rename_i hm hi
    exact walkerInv_pull fppLens hi.2 rfl rfl (by rw [hm]; simp) (by rw [hm]; simp)
      (by rw [hm]; simp) hI
  case fpp_done =>
    rename_i hm hi
    exact walkerInv_pull fppLens hi.2 rfl rfl (by rw [hm]; simp) (by rw [hm]; simp) (by simp) hI
  case markEnd_found =>
    rename_i hm he hi
    exact walkerInv_pull rewindLens hi.2 rfl (by rw [hi.1.2]; rfl) (by rw [hm]; simp)
      (by rw [hm]; simp) (by simp) hI
  case markEnd_step =>
    rename_i hm he hi
    exact walkerInv_pull fppLens hi.2 rfl rfl (by rw [hm]; simp) (by rw [hm]; simp)
      (by rw [hm]; simp) hI
  case choose_select =>
    rename_i hm hodd hs hi
    exact walkerInv_pull rewindLens hi.2 rfl (by rw [hi.1]; rfl) (by rw [hm]; simp)
      (by rw [hm]; simp) (by simp) hI
  case choose_step =>
    rename_i hm hs hi
    exact walkerInv_pull rewindLens hi.2 rfl (by rw [hi.1.2]; rfl) (by rw [hm]; simp)
      (by rw [hm]; simp) (by rw [hm]; simp) hI
  case rewind_done =>
    rename_i hm hfi hi
    exact walkerInv_pull rewindLens hi.2 rfl (by rw [hi.1]; rfl) (by rw [hm]; simp)
      (by rw [hm]; simp) (by simp) hI
  case rewind_one =>
    rename_i hm hpr hfi hi
    exact walkerInv_pull rewindLens hi.2 rfl (by rw [hi.1.2]; rfl) (by rw [hm]; simp)
      (by rw [hm]; simp) (by rw [hm]; simp) hI
  case rewind_pair =>
    rename_i hm hpr hfi hi
    exact walkerInv_pull rewindLens hi.2 rfl (by rw [hi.1.2]; rfl) (by rw [hm]; simp)
      (by rw [hm]; simp) (by rw [hm]; simp) hI
  case replayStart =>
    rename_i o hm ho ho' hi
    have hi' : replayStartVM entry s t := hi
    refine Or.inr (Or.inr ⟨by simp, hi'.2.2.2.2.2.2.2.2.2.1, ?_, Or.inl ⟨?_, ?_⟩⟩)
    · rw [hi'.2.2.2.2.2.2.2.2.2.2.1]; exact begin_reset_mode
    · rw [hi'.2.2.2.2.2.2.2.2.2.2.1]; exact begin_reset_work
    · show 2 ≤ delay; exact hdelay
  case restart =>
    rename_i hm hb
    obtain ⟨w, hbr, -, -, -, ht⟩ : restartVM entry s t := hb
    rcases hI with ⟨h1, -⟩ | ⟨-, hb'⟩ | ⟨-, hidle, -, -⟩
    · rw [hm] at h1; cases h1
    · refine Or.inr (Or.inl ⟨by rw [hm]; simp, ?_⟩)
      unfold Bounded at *
      rw [ht]; exact hb'
    · rw [hidle] at hbr; cases hbr

#print axioms walkerInv_tick

/-! ## 5. `Fair` runs -/

/-- **`Fair` はもう要らない**（2026-09-19）。`walkerInv_tick` が `Fair` を読んでいた
唯一の箇所は `keepsSearchCursor` で、`M-initCursor` の修正でそれが定理
（`GalilTickDet.initVM_keepsSearchCursor`）になったため。 -/
theorem walkerInv_of_run
    (hplace : ∀ u, (GalilScaffoldPlace.stream (place u)).length ≤ position u.right)
    (hdelay : 2 ≤ delay) {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first)
      delay n x y)
    (hcan : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first)
        delay m x z → z.ctl.replaying = true → GalilScaffoldChainVerifier.canRight z.vm.right)
    (hx : WalkerInv x.ctl x.vm) : WalkerInv y.ctl y.vm := by
  induction h with
  | zero x => exact hx
  | @succ n x w y ht hr ih =>
    exact ih (fun m z hz => hcan (m+1) z (.succ ht hz))
      (walkerInv_tick onLetter leftFirst centre place entry q first delay hplace hdelay
        (hcan 0 x (.zero x)) ht hx)

/-- **`WalkerInOrigin` at every `copy` state of a run** — the `hwalk`
hypothesis of `CloseoutPackRun25.wpack_of_fair`.
**2026-09-19: `Fair` を外した**（`M-initCursor` の修正で不要になった）。 -/
theorem walkerInOrigin_of_run
    (hplace : ∀ u, (GalilScaffoldPlace.stream (place u)).length ≤ position u.right)
    (hdelay : 2 ≤ delay) {x : State GalilVM}
    (hcan : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first)
        delay m x z → z.ctl.replaying = true → GalilScaffoldChainVerifier.canRight z.vm.right)
    (hx : WalkerInv x.ctl x.vm) (m : ℕ) (z : State GalilVM)
    (hz : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first)
      delay m x z) (hm : z.ctl.mode = Mode.copy) : WalkerInOrigin z.vm :=
  walkerInOrigin_of_inv
    (walkerInv_of_run onLetter leftFirst centre place entry q first delay hplace hdelay hz hcan hx) hm

#print axioms walkerInOrigin_of_run

/-- The boot shape: `init` mode with an empty walker. -/
theorem walkerInv_boot {c : Control} {s : GalilVM} (hc : c.mode = Mode.init)
    (hw : s.walker = ⟨[], false⟩) : WalkerInv c s :=
  Or.inl ⟨hc, by rw [hw]; rfl⟩

end Tick

end PalPeg.CloseoutPackRun28
