import PalPeg.GalilRunEntries
import PalPeg.GalilSearchResult

/-!
# The wait between two stages

`PalPeg/GalilRunEntries.lean` discharges `RunEntries` for the calibrated first
stage only under `Terminal v3.search.mode`: when the quantum exits in `.wait`
or `.double` the events after it can start a *second* stage inside the same
event list.  This file closes the `.wait` half of that gap at the `SearchRun`
level.

The scheduler's wait is `GalilScaffoldDouble.waitStep`: while `debt ≠ 0` the
tick is inert except for the outer `advance` (one debt unit per `true` event);
the first tick at which `debt = 0` fires `GalilScaffoldDouble.enter`, which is
exactly the entry shape of `search_later_stage'`
(`mode = .double`, `work = span`, `span = reset`, `quarter = 0`).
-/

set_option autoImplicit false
namespace PalPeg.GalilSearchWait

open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilSearchReadyInv
open GalilScaffoldCounter
open PalPeg.GalilBranchInvariants2
open GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead

/-! ## One wait tick -/

/-- The state after one wait tick. -/
def waitNext (a : Bool) (v : SearchVM) : SearchVM :=
  {v with search := GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.waitStep true v.search)}

theorem wait_searchStep (center : GalilScaffoldPlace.Place) (a : Bool) (v : SearchVM)
    (hm : v.search.mode = .wait) : searchStep center a v (waitNext a v) := by
  unfold searchStep
  rw [hm]
  rfl

theorem wait_searchStep_eq {center : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hm : v.search.mode = .wait) (h : searchStep center a v v') : v' = waitNext a v := by
  unfold searchStep at h
  rw [hm] at h
  exact h

/-- While the debt is nonzero the wait tick only pays the outer advance. -/
theorem waitNext_nonzero (a : Bool) (v : SearchVM) (hm : v.search.mode = .wait)
    (hz : zero v.search.debt = false) :
    waitNext a v = {v with search := GalilScaffoldSearchRun.advance a v.search} := by
  simp [waitNext, GalilScaffoldDouble.waitStep, hm, hz]

theorem waitNext_mode (a : Bool) (v : SearchVM) (hm : v.search.mode = .wait)
    (hz : zero v.search.debt = false) : (waitNext a v).search.mode = .wait := by
  rw [waitNext_nonzero a v hm hz]
  cases a <;> simpa [GalilScaffoldSearchRun.advance] using hm

theorem waitNext_debt (a : Bool) (v : SearchVM) (hm : v.search.mode = .wait)
    (hz : zero v.search.debt = false) :
    value (waitNext a v).search.debt =
      value v.search.debt - (if a = true then 1 else 0) := by
  rw [waitNext_nonzero a v hm hz]
  cases a <;> simp [GalilScaffoldSearchRun.advance, dec_value]

theorem waitNext_canonical (a : Bool) (v : SearchVM) (hm : v.search.mode = .wait)
    (hz : zero v.search.debt = false) (hc : Canonical v.search.debt) :
    Canonical (waitNext a v).search.debt := by
  rw [waitNext_nonzero a v hm hz]
  cases a
  · exact hc
  · exact dec_canonical _ hc

theorem waitNext_rest (a : Bool) (v : SearchVM) (hm : v.search.mode = .wait)
    (hz : zero v.search.debt = false) :
    (waitNext a v).search.span = v.search.span ∧
      (waitNext a v).search.quarter = v.search.quarter ∧
      (waitNext a v).search.work = v.search.work ∧
      (waitNext a v).search.finalStage = v.search.finalStage ∧
      (waitNext a v).lower = v.lower ∧ (waitNext a v).dp = v.dp ∧
      (waitNext a v).walker = v.walker := by
  rw [waitNext_nonzero a v hm hz]
  cases a <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The burn: retiring the debt -/

/-- The event list of a wait is *minimal*: the last `true` of `ws` is the tick
at which the debt reaches zero, i.e. every proper prefix pays strictly less. -/
def BurnEvents (ws : List Bool) : Prop :=
  ∀ p : List Bool, p <+: ws → p ≠ ws → p.count true < ws.count true

theorem burnEvents_tail {a : Bool} {as : List Bool} (h : BurnEvents (a :: as)) :
    BurnEvents as := by
  intro p hp hne
  obtain ⟨t, ht⟩ := hp
  have hp' : a :: p <+: a :: as := ⟨t, by simp [ht]⟩
  have hne' : a :: p ≠ a :: as := by
    intro he; exact hne (by simpa using he)
  have := h (a :: p) hp' hne'
  simp only [List.count_cons] at this
  omega

theorem burnEvents_pos {a : Bool} {as : List Bool} (h : BurnEvents (a :: as)) :
    0 < (a :: as).count true := by
  have := h [] ⟨a :: as, by simp⟩ (by simp)
  simpa using this

/-- Along a proper prefix of a burn the search never leaves `.wait`. -/
theorem wait_prefix_mode (center : GalilScaffoldPlace.Place) :
    ∀ (ps : List Bool) (v u : SearchVM), SearchRun center ps v u →
      v.search.mode = .wait → Canonical v.search.debt →
      ((ps.count true : ℤ) < value v.search.debt) →
      u.search.mode = .wait ∧ Canonical u.search.debt ∧
        value u.search.debt = value v.search.debt - ps.count true ∧
        u.search.span = v.search.span ∧ u.search.work = v.search.work ∧
        u.search.quarter = v.search.quarter ∧
        u.search.finalStage = v.search.finalStage ∧
        u.lower = v.lower ∧ u.dp = v.dp ∧ u.walker = v.walker := by
  intro ps
  induction ps with
  | nil =>
    intro v u h hm hc _
    cases h
    exact ⟨hm, hc, by simp, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons a as ih =>
    intro v u h hm hc hlt
    cases h with
    | cons hstep hrest =>
      rename_i v1
      have hcnt : (0 : ℤ) ≤ ((a :: as).count true : ℤ) := by positivity
      have hz : zero v.search.debt = false := by
        by_contra hcon
        have hcon' : zero v.search.debt = true := by
          cases hzz : zero v.search.debt
          · exact absurd hzz hcon
          · rfl
        have := (zero_iff v.search.debt hc).mp hcon'
        omega
      have hv1 : v1 = waitNext a v := wait_searchStep_eq hm hstep
      subst hv1
      have hm1 := waitNext_mode a v hm hz
      have hc1 := waitNext_canonical a v hm hz hc
      have hd1 := waitNext_debt a v hm hz
      obtain ⟨hsp, hqu, hwk, hfs, hlo, hdp, hwa⟩ := waitNext_rest a v hm hz
      have hlt1 : ((as.count true : ℤ)) < value (waitNext a v).search.debt := by
        rw [hd1]
        cases a <;> simp only [List.count_cons] at hlt <;> simp at hlt ⊢ <;> omega
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := ih _ _ hrest hm1 hc1 hlt1
      refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h3, hd1]
        cases a <;> simp [List.count_cons] <;> omega
      · rw [h4, hsp]
      · rw [h5, hwk]
      · rw [h6, hqu]
      · rw [h7, hfs]
      · rw [h8, hlo]
      · rw [h9, hdp]
      · rw [h10, hwa]

/-- **The burn.**  A minimal event list whose `true`s are exactly the debt
drives the wait to a zero-debt `.wait` state, leaving everything else alone. -/
theorem searchRun_burn (center : GalilScaffoldPlace.Place) :
    ∀ (ws : List Bool) (v : SearchVM), v.search.mode = .wait → Canonical v.search.debt →
      value v.search.debt = ws.count true → BurnEvents ws →
      ∃ v', SearchRun center ws v v' ∧ v'.search.mode = .wait ∧
        zero v'.search.debt = true ∧ Canonical v'.search.debt ∧
        v'.search.span = v.search.span ∧ v'.search.work = v.search.work ∧
        v'.search.quarter = v.search.quarter ∧
        v'.search.finalStage = v.search.finalStage ∧
        v'.lower = v.lower ∧ v'.dp = v.dp ∧ v'.walker = v.walker := by
  intro ws
  induction ws with
  | nil =>
    intro v hm hc hd _
    simp only [List.count_nil, Nat.cast_zero] at hd
    exact ⟨v, .nil _, hm, (zero_iff v.search.debt hc).mpr hd, hc, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons a as ih =>
    intro v hm hc hd hb
    have hpos := burnEvents_pos hb
    have hz : zero v.search.debt = false := by
      by_contra hcon
      have hcon' : zero v.search.debt = true := by
        cases hzz : zero v.search.debt
        · exact absurd hzz hcon
        · rfl
      have := (zero_iff v.search.debt hc).mp hcon'
      omega
    have hm1 := waitNext_mode a v hm hz
    have hc1 := waitNext_canonical a v hm hz hc
    have hd1 := waitNext_debt a v hm hz
    obtain ⟨hsp, hqu, hwk, hfs, hlo, hdp, hwa⟩ := waitNext_rest a v hm hz
    have hd1' : value (waitNext a v).search.debt = (as.count true : ℤ) := by
      rw [hd1, hd]
      cases a <;> simp [List.count_cons]
    obtain ⟨v', hrun, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
      ih _ hm1 hc1 hd1' (burnEvents_tail hb)
    refine ⟨v', .cons (wait_searchStep center a v hm) hrun, h1, h2, h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h4, hsp]
    · rw [h5, hwk]
    · rw [h6, hqu]
    · rw [h7, hfs]
    · rw [h8, hlo]
    · rw [h9, hdp]
    · rw [h10, hwa]

#print axioms wait_prefix_mode
#print axioms searchRun_burn

/-! ## The boundary tick -/

theorem reset_eq_ofNat : reset = ofNat 0 := rfl

/-- **The lift.**  A state in `.wait` with canonical debt, followed by a
minimal burn `ws` and one more clocked tick, reaches a state satisfying
*exactly* the entry hypotheses `hm0/hq0/hw0/hs0/hcanon/hd` of
`search_later_stage'` (`PalPeg/GalilSearchResult.lean`), with the doubled
window `work = ofNat n` read off the span the wait was entered with, and the
clock of the later stage the one the match clock hands on. -/
theorem searchRun_waiting (center : GalilScaffoldPlace.Place)
    (ws : List Bool) (available eligible : Bool) (clock : ℕ)
    (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    (v3 : SearchVM) (hm : v3.search.mode = .wait) (hc : Canonical v3.search.debt)
    (hdebt : value v3.search.debt = ws.count true) (hb : BurnEvents ws)
    (n : ℕ) (hspan : v3.search.span = ofNat n) :
    ∃ v4 : SearchVM,
      SearchRun center (ws ++ [available && decide (clock = 1) && eligible]) v3 v4 ∧
      v4.search.mode = .double ∧ v4.search.quarter = 0 ∧
      v4.search.work = ofNat n ∧ v4.search.span = ofNat 0 ∧
      Canonical v4.search.debt ∧
      (0 ≤ value v4.search.debt ∨
        (-1 ≤ value v4.search.debt ∧
          (GalilScaffoldMatchClock.run 2048 clock [available]).1 = 2048)) ∧
      (1 ≤ (GalilScaffoldMatchClock.run 2048 clock [available]).1 ∧
        (GalilScaffoldMatchClock.run 2048 clock [available]).1 ≤ 2048) ∧
      v4.lower = v3.lower ∧ v4.dp = v3.dp ∧ v4.walker = v3.walker := by
  obtain ⟨vm, hrun, hmm, hmz, hmc, hmsp, _, _, _, hmlo, hmdp, hmwa⟩ :=
    searchRun_burn center ws v3 hm hc hdebt hb
  set aB : Bool := available && decide (clock = 1) && eligible with haB
  have hstep : searchStep center aB vm (waitNext aB vm) := wait_searchStep center aB vm hmm
  have hwn : waitNext aB vm =
      {vm with search := GalilScaffoldSearchRun.advance aB (GalilScaffoldDouble.enter vm.search)} := by
    rw [waitNext, GalilScaffoldDouble.wait_enter vm.search hmm hmz]
  have hbd := GalilScaffoldDouble.enter_boundary vm.search available eligible clock hmc hmz hclock
  simp only [] at hbd
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hbd
  refine ⟨waitNext aB vm, searchRun_append hrun (.cons hstep (.nil _)), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [hwn]; exact hb1
  · rw [hwn]; exact hb4
  · rw [hwn]; rw [hb2, hmsp, hspan]
  · rw [hwn]; rw [hb3, reset_eq_ofNat]
  · rw [hwn]; exact hb5
  · rw [hwn]; exact hb6
  · exact hb7
  · rw [hwn]; exact hmlo
  · rw [hwn]; exact hmdp
  · rw [hwn]; exact hmwa

#print axioms searchRun_waiting

/-! ## The later stage: `RunEntries` from a `.double` entry

`runEntries_of_stage` (`PalPeg/GalilRunEntries.lean`) classifies the modes of a
stage that starts in `.grow`.  A stage entered through the wait starts in
`.double`; the classification is the same with the doubling ticks in place of
the grow ticks, because the `.double` dispatch with `positive work = false` has
the same body as the `.grow` one.
-/

/-- A prefix of the doubling ticks stays in `double`, with the remaining work. -/
theorem searchRun_double_prefix (center : GalilScaffoldPlace.Place) (as : List Bool) :
    ∀ {v v' : SearchVM} (n : ℕ), SearchRun center as v v' → v.search.mode = .double →
      v.search.work = ofNat n → as.length ≤ n →
      v'.search.mode = .double ∧ v'.search.work = ofNat (n - as.length) := by
  induction as with
  | nil => intro v v' n h hm hw _; cases h; exact ⟨hm, by simpa using hw⟩
  | cons a as ih =>
    intro v v'' n h hm hw hlen
    cases h with
    | cons hstep hrest =>
      rename_i v'
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hlen; omega⟩
      have hpos : positive v.search.work = true := by rw [hw, positive_ofNat]; simp
      have hv' : v' = {v with search :=
          GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)} := by
        unfold searchStep at hstep
        rw [hm] at hstep
        simp only [hpos, if_true] at hstep
        exact hstep
      have hm' : v'.search.mode = .double := by
        rw [hv']
        show (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)).mode = _
        cases a <;> simpa [GalilScaffoldSearchRun.advance, GalilScaffoldDouble.step] using hm
      have hw' : v'.search.work = ofNat m := by
        rw [hv']
        show (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)).work = _
        cases a <;>
          simp [GalilScaffoldSearchRun.advance, GalilScaffoldDouble.step, hw, dec_ofNat_succ]
      have := ih m hrest hm' hw' (by simp at hlen; omega)
      simpa [Nat.succ_sub_succ] using this

/-- The `.double` counterpart of `stage_mode_at`. -/
theorem stage_mode_at_double (center : GalilScaffoldPlace.Place) (k : ℕ)
    {as bs usedQ : List Bool} {v0 v1 v2 v3 : SearchVM}
    (h1 : SearchRun center as v0 v1) (h2 : SearchRun center bs v1 v2)
    (hm0 : v0.search.mode = .double) (hw0 : v0.search.work = ofNat as.length)
    (hp : GalilScaffoldPreparePaced.PacedPrepared (ofNat k) center v1.toPrep bs v2.toPrep)
    (hm1 : v1.search.mode = .double) (hw1 : positive v1.search.work = false)
    (hl1 : v1.lower = ofNat k)
    (hq : GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp usedQ v3.search v3.dp) :
    ∀ (j : ℕ) (v : SearchVM), SearchRun center ((as ++ bs ++ usedQ).take j) v0 v →
      (j < as.length + bs.length → v.search.mode ≠ .run) ∧
      (as.length + bs.length ≤ j → j < as.length + bs.length + usedQ.length →
        v.search.mode = .run) := by
  intro j v hv
  obtain ⟨a', bs', hbs⟩ : ∃ a' bs', bs = a' :: bs' := by
    cases hb0 : bs with
    | nil => rw [hb0] at hp; cases hp
    | cons a' bs' => exact ⟨a', bs', rfl⟩
  by_cases hj1 : j ≤ as.length
  · have hes1' : (as ++ bs ++ usedQ).take j = as.take j := by
      rw [List.append_assoc, List.take_append_of_le_length hj1]
    rw [hes1'] at hv
    obtain ⟨hg, _⟩ := searchRun_double_prefix center (as.take j) as.length hv hm0 hw0
      (by rw [List.length_take]; omega)
    refine ⟨fun _ => by rw [hg]; decide, fun hge _ => ?_⟩
    exfalso
    rw [hbs] at hge
    simp only [List.length_cons] at hge
    omega
  · by_cases hj2 : j < as.length + bs.length
    · have hj1' := Nat.lt_of_not_le hj1
      have hes1' : (as ++ bs ++ usedQ).take j = as ++ bs.take (j - as.length) := by
        rw [List.take_append_of_le_length (by rw [List.length_append]; omega),
          List.take_append, List.take_of_length_le (by omega)]
      rw [hes1'] at hv
      obtain ⟨vm1, hv1, hv'⟩ := searchRun_split _ as hv
      rw [searchRun_unique hv1 h1] at hv'
      obtain ⟨i, hi⟩ : ∃ i, j - as.length = i + 1 := ⟨j - as.length - 1, by omega⟩
      rw [hi, hbs, List.take_succ_cons] at hv'
      cases hv' with
      | cons hstep hrest =>
        rename_i v1'
        have hv1' : v1' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a'
            (GalilScaffoldPrepareControl.prepare v1.toPrep v1.lower center)) v1.search.quarter
            v1.lower := by
          unfold searchStep at hstep
          rw [hm1] at hstep
          simp only [hw1, Bool.false_eq_true, if_false] at hstep
          exact hstep
        have hx1 : v1'.toPrep = GalilScaffoldPreparePaced.afterAdvance a'
            (GalilScaffoldPrepareControl.prepare v1.toPrep (ofNat k) center) := by
          rw [hv1', toPrep_ofPrep, hl1]
        rw [hbs] at hp
        cases hp with
        | intro _ _ _ hrun =>
          have hsplitb : bs' = bs'.take i ++ bs'.drop i := (List.take_append_drop i bs').symm
          rw [hsplitb] at hrun
          obtain ⟨y, hy1, hy2⟩ := pacedPrepared_split _ _ hrun
          have hpref : SearchRun center
              (((List.replicate (bs'.take i).length true).zip (bs'.take i)).map Prod.snd) v1' v := by
            rw [map_snd_zip_replicate]; exact hrest
          obtain ⟨hvy, _, _⟩ := searchRun_paced center (all_enabled_zip _) hy1 hpref hx1
          have hi2 : i < bs'.length := by
            rw [hbs] at hj2
            simp only [List.length_cons] at hj2
            omega
          have hdne : bs'.drop i ≠ [] := by
            intro h0
            have hlen0 := congrArg List.length h0
            rw [List.length_drop] at hlen0
            simp only [List.length_nil] at hlen0
            omega
          obtain ⟨e, es', hd⟩ : ∃ e es', bs'.drop i = e :: es' := by
            cases hd0 : bs'.drop i with
            | nil => exact absurd hd0 hdne
            | cons e es' => exact ⟨e, es', rfl⟩
          rw [hd] at hy2
          simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons] at hy2
          have hpm := pacedRun_cons_prepMode rfl hy2
          rw [← hvy, toPrep_mode] at hpm
          refine ⟨fun _ => ?_, fun hge _ => absurd hge (by omega)⟩
          rcases hpm with hpm | hpm | hpm | hpm <;> rw [hpm] <;> decide
    · -- the run quanta
      have hj2' : as.length + bs.length ≤ j := Nat.le_of_not_lt hj2
      have hes1' : (as ++ bs ++ usedQ).take j =
          as ++ bs ++ usedQ.take (j - (as.length + bs.length)) := by
        rw [List.take_append, List.take_of_length_le (by rw [List.length_append]; omega),
          List.length_append]
      rw [hes1', List.append_assoc] at hv
      obtain ⟨vm1, hv1, hvA⟩ := searchRun_split _ as hv
      rw [searchRun_unique hv1 h1] at hvA
      obtain ⟨vm2, hv2, hvB⟩ := searchRun_split _ bs hvA
      rw [searchRun_unique hv2 h2] at hvB
      refine ⟨fun hlt => absurd hj2' (by omega), fun _ hlt => ?_⟩
      obtain ⟨i, hi⟩ : ∃ i, j - (as.length + bs.length) = i := ⟨_, rfl⟩
      rw [hi] at hvB
      have hdne : usedQ.drop i ≠ [] := by
        intro h0
        have hlen0 := congrArg List.length h0
        rw [List.length_drop] at hlen0
        simp only [List.length_nil] at hlen0
        omega
      have hq' : GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp
          (usedQ.take i ++ usedQ.drop i) v3.search v3.dp := by
        rw [List.take_append_drop]; exact hq
      obtain ⟨m, y', hqm, hmm⟩ := safeQuanta_prefix_run _ _ hdne hq'
      have hvC : SearchRun center (usedQ.take i ++ []) v2 v := by
        rw [List.append_nil]; exact hvB
      obtain ⟨vq, _, hsq, _, _, _, hnil⟩ := searchRun_quanta center hqm hvC rfl rfl
      cases hnil
      rw [hsq]
      exact hmm

/-- The `.double` counterpart of `runEntries_of_stage`. -/
theorem runEntries_of_stage_double (center : GalilScaffoldPlace.Place) (k : ℕ)
    {as bs usedQ rest es : List Bool} {v0 v1 v2 v3 : SearchVM}
    (hes : es = as ++ bs ++ usedQ ++ rest)
    (h1 : SearchRun center as v0 v1) (h2 : SearchRun center bs v1 v2)
    (h3 : SearchRun center usedQ v2 v3)
    (hm0 : v0.search.mode = .double) (hw0 : v0.search.work = ofNat as.length)
    (hp : GalilScaffoldPreparePaced.PacedPrepared (ofNat k) center v1.toPrep bs v2.toPrep)
    (hm1 : v1.search.mode = .double) (hw1 : positive v1.search.work = false)
    (hl1 : v1.lower = ofNat k)
    (hq : GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp usedQ v3.search v3.dp)
    (hm3 : v3.search.mode ≠ .run)
    (hterm : Terminal v3.search.mode)
    (hentry : DpSafeRem v2 (usedQ ++ rest)) :
    RunEntries center es v0 := by
  classical
  have hclass := stage_mode_at_double center k h1 h2 hm0 hw0 hp hm1 hw1 hl1 hq
  have hstage : as ++ bs ++ usedQ = es.take (as.length + bs.length + usedQ.length) := by
    have e1 : as.length + bs.length + usedQ.length = (as ++ bs ++ usedQ).length := by
      simp only [List.length_append]
    rw [hes, e1, List.take_left]
  intro cs ds b u u' heq hru hstep hnr hrr
  have hsplit2 : es = (cs ++ [b]) ++ ds := by rw [heq]; simp
  have hlb : cs.length + 1 = (cs ++ [b]).length := by simp
  have hcs : cs = es.take cs.length := by rw [heq, List.take_left]
  have hcsb : cs ++ [b] = es.take (cs.length + 1) := by rw [hsplit2, hlb, List.take_left]
  have hdrop : es.drop (cs.length + 1) = ds := by rw [hsplit2, hlb, List.drop_left]
  have hu' : SearchRun center (cs ++ [b]) v0 u' := searchRun_append hru (.cons hstep (.nil _))
  by_cases hjT : cs.length + 1 ≤ as.length + bs.length + usedQ.length
  · -- inside the classified region
    have hpref1 : cs = (as ++ bs ++ usedQ).take cs.length := by
      rw [hstage, List.take_take, Nat.min_eq_left (by omega)]
      exact hcs
    have hpref2 : cs ++ [b] = (as ++ bs ++ usedQ).take (cs.length + 1) := by
      rw [hstage, List.take_take, Nat.min_eq_left (by omega)]
      exact hcsb
    have hA := hclass cs.length u (by rw [← hpref1]; exact hru)
    have hB := hclass (cs.length + 1) u' (by rw [← hpref2]; exact hu')
    have hge : as.length + bs.length ≤ cs.length + 1 := by
      by_contra hcon
      exact hB.1 (by omega) hrr
    have hlt : cs.length < as.length + bs.length := by
      by_contra hcon
      exact hnr (hA.2 (by omega) (by omega))
    have heqj : cs.length + 1 = as.length + bs.length := by omega
    have hab : cs ++ [b] = as ++ bs := by
      rw [hpref2, heqj, show as.length + bs.length = (as ++ bs).length by simp, List.take_left]
    have hrun_ab : SearchRun center (as ++ bs) v0 v2 := searchRun_append h1 h2
    have hv2 : u' = v2 := by
      rw [hab] at hu'
      exact searchRun_unique hu' hrun_ab
    have hds : ds = usedQ ++ rest := by
      have hd2 : es.drop (as.length + bs.length) = usedQ ++ rest := by
        have e1 : as ++ bs ++ usedQ ++ rest = (as ++ bs) ++ (usedQ ++ rest) := by
          simp [List.append_assoc]
        have e2 : as.length + bs.length = (as ++ bs).length := by simp
        rw [hes, e1, e2, List.drop_left]
      rw [← hdrop, heqj, hd2]
    rw [hv2, hds]
    exact hentry
  · -- after the quantum: the inert tail
    exfalso
    have hcs' : cs = (as ++ bs ++ usedQ) ++ rest.take (cs.length - (as ++ bs ++ usedQ).length) := by
      have h0 : es.take cs.length =
          (as ++ bs ++ usedQ) ++ rest.take (cs.length - (as ++ bs ++ usedQ).length) := by
        rw [hes, List.take_append,
          List.take_of_length_le (by simp only [List.length_append]; omega)]
      rw [← h0]
      exact hcs
    rw [hcs'] at hru
    obtain ⟨vm, hvm1, hvm2⟩ := searchRun_split _ (as ++ bs ++ usedQ) hru
    have hvm : vm = v3 := searchRun_unique hvm1 (searchRun_append (searchRun_append h1 h2) h3)
    rw [hvm] at hvm2
    have hu : u = v3 := searchRun_terminal hvm2 hterm
    rw [hu] at hstep
    have hu2 : u' = v3 := searchStep_terminal hstep hterm
    rw [hu2] at hrr
    exact hm3 hrr

#print axioms searchRun_double_prefix
#print axioms stage_mode_at_double
#print axioms runEntries_of_stage_double

/-! ## `RunEntries` for a stage entered through the wait -/

/-- **The later-stage counterpart of `runEntries_of_calibrated`.**  For a
`SearchRun` starting at the `.double` entry produced by `searchRun_waiting`,
whose event list is the clocked stream of exactly the calibrated later-stage
length, the stage decomposes as `as ++ bs ++ usedQ ++ rest`, the entry datum
`DpSafeRem v2 (usedQ ++ rest)` holds at the handover, and — provided the
quantum exits in an inert mode — `RunEntries` holds for the whole of `es`. -/
theorem runEntries_of_later_stage (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool)
    (cen : PlaceHead) (hcen : cen = represent ⟨a :: ls, gap⟩ (rs.map some) qq)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls, gap⟩ = some c)
    (k n clock : ℕ)
    {v0 v' : SearchVM} {es : List Bool} (hrun : SearchRun ⟨a :: ls, gap⟩ es v0 v')
    (hm0 : v0.search.mode = .double) (hq0 : v0.search.quarter = 0)
    (hw0 : v0.search.work = ofNat n) (hs0 : v0.search.span = ofNat 0)
    (hcanon : Canonical v0.search.debt)
    (hd : 0 ≤ value v0.search.debt ∨ (-1 ≤ value v0.search.debt ∧ clock = 2048))
    (hlow : v0.lower = ofNat k)
    (hmod : n % 4 = 0) (hn : 8 ≤ n) (hl : 4*k ≤ n)
    {av : List Bool}
    (hes : es = GalilScaffoldAdvanceClock.advances 2048 clock (av.map (fun b => (b, true))))
    (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    (hlen : es.length = n
      + (2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (2*n+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (2*n)) :
    ∃ (as bs usedQ rest : List Bool) (v1 v2 v3 : SearchVM),
      es = as ++ bs ++ usedQ ++ rest ∧
      SearchRun ⟨a :: ls, gap⟩ as v0 v1 ∧ SearchRun ⟨a :: ls, gap⟩ bs v1 v2 ∧
      SearchRun ⟨a :: ls, gap⟩ usedQ v2 v3 ∧ SearchRun ⟨a :: ls, gap⟩ rest v3 v' ∧
      v2.search.mode = .run ∧ v3.search.mode ≠ .run ∧
      DpSafeRem v2 (usedQ ++ rest) ∧
      (Terminal v3.search.mode → RunEntries ⟨a :: ls, gap⟩ es v0) := by
  obtain ⟨as, bs, usedQ, rest, v1, v2, v3, hsplit, hasl, hbsl, hcsl, h1, h2, h3, hrest,
      hm2, hquanta, hm3, _, hdp2, hcanon2, hcount, hbudget⟩ :=
    search_later_stage' a ls rs qq gap cen hcen c hc k n clock hrun hm0 hq0 hw0 hs0 hcanon hd
      hlow hmod hn hl hes hclock hlen
  have hentry : DpSafeRem v2 (usedQ ++ rest) :=
    dpSafeRem_entry v2 _ k (usedQ ++ rest) hdp2 hm2 hbudget hcanon2 hcount
  refine ⟨as, bs, usedQ, rest, v1, v2, v3, hsplit, h1, h2, h3, hrest, hm2, hm3, hentry,
    fun hterm => ?_⟩
  obtain ⟨a'', bs'', hbs⟩ : ∃ a'' bs'', bs = a'' :: bs'' := by
    cases hb0 : bs with
    | nil => rw [hb0] at hbsl; simp only [List.length_nil] at hbsl; omega
    | cons a'' bs'' => exact ⟨a'', bs'', rfl⟩
  have hw0' : v0.search.work = ofNat as.length := by rw [hw0, hasl]
  obtain ⟨hdr1, hdp1, hl1', hwk1, hm1, hw1⟩ :=
    searchRun_doubling ⟨a :: ls, gap⟩ as h1 hm0 hw0'
  have hspan1 : v1.search.span = ofNat (2*n) := by
    have h := GalilScaffoldDouble.span_of_run hdr1 0 hs0
    rw [h, hasl, Nat.zero_add]
  obtain ⟨p, hp, _, _, _, _, _⟩ :=
    GalilScaffoldPrepareControl.prepare_complete v1.toPrep k (2*n) ⟨a :: ls, gap⟩ hspan1
  have hprep : GalilScaffoldPreparePaced.PacedPrepared (ofNat k) ⟨a :: ls, gap⟩ v1.toPrep
      (a'' :: bs'') {p with debt := GalilScaffoldPreparePaced.spend (a'' :: bs'') v1.toPrep.debt} :=
    GalilScaffoldPreparePaced.prepared_interleave hp (a'' :: bs'') (by rw [← hbs]; exact hbsl)
  have hl1 : v1.lower = ofNat k := by rw [hl1', hlow]
  have hw1' : positive v1.search.work = false := by rw [hw1]; rfl
  have hv2 : v2.toPrep =
      {p with debt := GalilScaffoldPreparePaced.spend (a'' :: bs'') v1.toPrep.debt} :=
    (searchRun_prepared_double _ hprep (hbs ▸ h2) rfl hm1 hw1' hl1).1
  have hpfull : GalilScaffoldPreparePaced.PacedPrepared (ofNat k) ⟨a :: ls, gap⟩ v1.toPrep
      bs v2.toPrep := by rw [hv2, hbs]; exact hprep
  exact runEntries_of_stage_double _ k hsplit h1 h2 h3 hm0 hw0' hpfull hm1 hw1' hl1
    hquanta hm3 hterm hentry

#print axioms runEntries_of_later_stage

/-! ## Two stages

`searchRun_waiting` hands the later stage exactly the entry hypotheses
`runEntries_of_later_stage` consumes, so the two compose: from the `.wait`
exit `v3` of the first stage, the burn and the boundary tick reach the entry
`v4` of the second stage and `RunEntries` holds for the second stage's own
event list.

**The obstacle to a single `RunEntries` over `stage1 ++ wait ++ stage2`.**
`DpSafeRem u' ds` carries `((bs ++ ds).count true : ℤ) ≤ value s0.debt` with
`ds` the tail of the *whole* event list, and the first stage's entry debt is
exhausted exactly at the end of its wait (the burn retires the last unit), so
`RunEntries center (stage1 ++ wait ++ stage2) v0` is false as soon as the
boundary tick or the second stage contains a single `true` event; `RunEntries`
is a per-stage statement and a multi-stage version needs `DpSafeRem` re-indexed
by the current stage's remainder rather than by the whole tail.  The same
obstacle blocks the `k`-stage induction.
-/

/-- **Two stages.**  The wait after the first stage's quantum reaches the entry
of the second stage, and `RunEntries` holds for the second stage. -/
theorem runEntries_two_stages (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool)
    (cen : PlaceHead) (hcen : cen = represent ⟨a :: ls, gap⟩ (rs.map some) qq)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls, gap⟩ = some c)
    (k n : ℕ) (ws : List Bool) (available eligible : Bool) (clock0 : ℕ)
    (hclock0 : 1 ≤ clock0 ∧ clock0 ≤ 2048)
    {v3 v' : SearchVM} {es2 : List Bool}
    (hrun : SearchRun ⟨a :: ls, gap⟩
      ((ws ++ [available && decide (clock0 = 1) && eligible]) ++ es2) v3 v')
    (hm : v3.search.mode = .wait) (hc3 : Canonical v3.search.debt)
    (hdebt : value v3.search.debt = ws.count true) (hb : BurnEvents ws)
    (hspan : v3.search.span = ofNat n) (hlow : v3.lower = ofNat k)
    (hmod : n % 4 = 0) (hn : 8 ≤ n) (hl : 4*k ≤ n)
    {av : List Bool}
    (hes2 : es2 = GalilScaffoldAdvanceClock.advances 2048
      (GalilScaffoldMatchClock.run 2048 clock0 [available]).1 (av.map (fun b => (b, true))))
    (hlen2 : es2.length = n
      + (2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (2*n+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (2*n)) :
    ∃ v4 : SearchVM,
      SearchRun ⟨a :: ls, gap⟩ (ws ++ [available && decide (clock0 = 1) && eligible]) v3 v4 ∧
      SearchRun ⟨a :: ls, gap⟩ es2 v4 v' ∧
      v4.search.mode = .double ∧ v4.search.quarter = 0 ∧
      v4.search.work = ofNat n ∧ v4.search.span = ofNat 0 ∧
      ∃ (as bs usedQ rest : List Bool) (v5 v6 v7 : SearchVM),
        es2 = as ++ bs ++ usedQ ++ rest ∧
        SearchRun ⟨a :: ls, gap⟩ as v4 v5 ∧ SearchRun ⟨a :: ls, gap⟩ bs v5 v6 ∧
        SearchRun ⟨a :: ls, gap⟩ usedQ v6 v7 ∧ SearchRun ⟨a :: ls, gap⟩ rest v7 v' ∧
        v6.search.mode = .run ∧ v7.search.mode ≠ .run ∧
        DpSafeRem v6 (usedQ ++ rest) ∧
        (Terminal v7.search.mode → RunEntries ⟨a :: ls, gap⟩ es2 v4) := by
  obtain ⟨v4, hw, hm4, hq4, hwk4, hsp4, hcan4, hd4, hcl4, hlo4, hdp4, hwa4⟩ :=
    searchRun_waiting ⟨a :: ls, gap⟩ ws available eligible clock0 hclock0 v3 hm hc3 hdebt hb
      n hspan
  obtain ⟨u, hu1, hu2⟩ := searchRun_split _ _ hrun
  have hueq : u = v4 := searchRun_unique hu1 hw
  rw [hueq] at hu2
  obtain ⟨as, bs, usedQ, rest, v5, v6, v7, hsplit, h1, h2, h3, hrest, hm6, hm7, hentry, hE⟩ :=
    runEntries_of_later_stage a ls rs qq gap cen hcen c hc k n
      (GalilScaffoldMatchClock.run 2048 clock0 [available]).1 hu2 hm4 hq4 hwk4 hsp4 hcan4 hd4
      (by rw [hlo4, hlow]) hmod hn hl hes2 hcl4 hlen2
  exact ⟨v4, hw, hu2, hm4, hq4, hwk4, hsp4, as, bs, usedQ, rest, v5, v6, v7, hsplit, h1, h2, h3,
    hrest, hm6, hm7, hentry, hE⟩

#print axioms runEntries_two_stages

#print axioms wait_searchStep
#print axioms waitNext_debt

end PalPeg.GalilSearchWait
