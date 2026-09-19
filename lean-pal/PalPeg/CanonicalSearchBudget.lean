import PalPeg.CanonicalSearchHistory
import PalPeg.CloseoutReadyStage

/-! # Search safety paid for by the actual controller clock

`credit = 2048 * debt + clock` loses at most one per search event.  Grow
adds 4096 credits; every fourth double tick adds 2048.  Preparation and the
DP spend this credit.  No quantification over arbitrarily truncated future
stage lists is needed.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PalPeg.CanonicalSearchBudget
open PalPeg GalilScaffoldChainInputSupply GalilScaffoldCounter
open GalilScaffoldSearchRun GalilBranchInvariants2 CanonicalSearchProgram

abbrev SearchMode := GalilScaffoldSearchFinish.Mode

def credit (clock : ℕ) (v : SearchVM) : ℤ := 2048 * value v.search.debt + clock

def ClockEvent (a : Bool) (clock clock' : ℕ) : Prop :=
  1 ≤ clock ∧ clock ≤ 2048 ∧ 1 ≤ clock' ∧ clock' ≤ 2048 ∧
    (if a then (2048 : ℤ) else 0) + clock - clock' ≤ 1

def dpBudget (span : ℕ) : ℕ := 50*(span+1)+27

private theorem canonical_eq_ofNat (c : Counter) (hc : Canonical c)
    (hn : 0 ≤ value c) : c = ofNat (value c).toNat := by
  have unit_replicate (xs : List Unit) : xs = List.replicate xs.length () := by
    induction xs with
    | nil => rfl
    | cons u xs ih =>
      cases u
      rw [List.length_cons, List.replicate_succ]
      exact congrArg (List.cons ()) ih
  rcases c with ⟨ps,ns⟩
  simp only [Canonical] at hc
  rcases hc with hp | hn0
  · subst ps
    have hlen : ns.length = 0 := by simp [value] at hn ⊢; omega
    have : ns = [] := List.eq_nil_of_length_eq_zero hlen
    subst ns
    rfl
  · subst ns
    simp only [value, List.length_nil, Nat.cast_zero, sub_zero, Int.toNat_natCast, ofNat]
    congr
    exact unit_replicate ps

private theorem credit_advance (s : GalilScaffoldSearchFinish.State) (a : Bool)
    (clock clock' : ℕ) (hc : ClockEvent a clock clock') :
    2048*value (advance a s).debt + clock' ≥ 2048*value s.debt + clock - 1 := by
  rcases hc with ⟨_,_,_,_,hh⟩
  cases a <;> simp only [advance,Bool.false_eq_true,reduceIte,dec_value] at * <;> omega

private theorem positive_credit_nonneg {clock : ℕ} {v : SearchVM}
    (hc : clock ≤ 2048) (hp : 0 < credit clock v) : 0 ≤ value v.search.debt := by
  unfold credit at hp
  omega

/-- The preparation certificate with its exact remaining enabled ticks. -/
def PrepCredit (p : GalilScaffoldPlace.Place) (lower clock : ℕ) (v : SearchVM) : Prop :=
  ∃ span n t, v.search.span = ofNat span ∧
    GalilScaffoldPrepareControl.Run v.toPrep (List.replicate n true) t ∧
    t.mode = .run ∧ t.program.config = GalilScaffoldPreload.initial
      ((GalilScaffoldPlace.stream p).take (span+1)) lower ∧ t.program.done = false ∧
    (dpBudget span+n : ℕ) ≤ credit clock v

/-- In a running stage, each elapsed quantum is paid exactly once. -/
def RunCredit (p : GalilScaffoldPlace.Place) (lower clock : ℕ) (v : SearchVM) : Prop :=
  ∃ span s0 bs, v.search.span = ofNat span ∧ s0.mode = .run ∧ Canonical s0.debt ∧
    DpReached ((GalilScaffoldPlace.stream p).take (span+1)) lower s0 bs v.search v.dp ∧
    (dpBudget span : ℤ) ≤ credit clock v + bs.length

/-- Quantitative fields live only in the mode which consumes them. -/
structure BudgetInv (p : GalilScaffoldPlace.Place) (lower clock : ℕ) (v : SearchVM) : Prop where
  clock_pos : 1 ≤ clock
  clock_le : clock ≤ 2048
  lower_eq : v.lower = ofNat lower
  debt_canonical : Canonical v.search.debt
  prep_inv : PrepInv v.toPrep
  span_nat : ∃ span, v.search.span = ofNat span
  work_nat : v.search.mode = .grow ∨ v.search.mode = .double → ∃ work, v.search.work = ofNat work
  stage_size : v.search.mode ≠ .grow → v.search.mode ≠ .double →
    8*max lower 1 ≤ (value v.search.span).toNat ∧ (value v.search.span).toNat % 8 = 0
  grow_size : v.search.mode = .grow →
    value v.search.span + 8*value v.search.work = 8*max lower 1
  grow : v.search.mode = .grow →
    64*value v.search.span + 2*lower + 128 ≤ credit clock v + 3583*value v.search.work
  doubling : v.search.mode = .double →
    64*value v.search.span + 2*lower + 128 ≤
      credit clock v + 383*value v.search.work + 512*v.search.quarter.val
  double_size : v.search.mode = .double →
    16*max lower 1 ≤ (value v.search.span + 2*value v.search.work).toNat ∧
    (value v.search.span + 2*value v.search.work).toNat % 8 = 0 ∧
    (value v.search.span).toNat % 8 = 2*v.search.quarter.val
  prep : Preparing v.search.mode → PrepCredit p lower clock v
  running : v.search.mode = .run → RunCredit p lower clock v

private theorem guarded_append {x y z : GalilScaffoldControl.Machine 12} {as bs : List Bool}
    (ha : GalilScaffoldDpCost.GuardedRun GalilDpCode.code x as y)
    (hb : GalilScaffoldDpCost.GuardedRun GalilDpCode.code y bs z) :
    GalilScaffoldDpCost.GuardedRun GalilDpCode.code x (as++bs) z := by
  induction ha with
  | nil => exact hb
  | cons x y z b bs ht hr ih => exact .cons _ _ _ _ _ ht (ih hb)

private theorem guarded_unique {x y z : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (ha : GalilScaffoldDpCost.GuardedRun GalilDpCode.code x bs y)
    (hb : GalilScaffoldDpCost.GuardedRun GalilDpCode.code x bs z) : y=z := by
  induction ha generalizing z with
  | nil => cases hb; rfl
  | cons x y z b bs ht hr ih =>
    cases hb with
    | cons _ y' _ _ _ ht' hr' =>
      have he := GalilTickDet.progTick_unique GalilTickFair.readFun_code ht ht'
      subst y'; exact ih hr'

private theorem calls_guarded {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (hr : SafeCalls s x bs t y) (hi : s.mode=.run ↔ x.done=false) :
    GalilScaffoldDpCost.GuardedRun GalilDpCode.code x bs y := by
  induction hr with
  | nil => exact .nil _
  | cons s x y z b bs t ht _ hr ih =>
    have hg : decide (s.mode=.run) = !x.done := by cases hd : x.done <;> simp_all
    have ht' := ht
    rw [hg] at ht'
    exact .cons _ _ _ _ _ ht' (ih (run_call b hi ht').2)

private theorem quanta_guarded {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (hr : SafeQuanta s x bs t y) (hi : s.mode=.run ↔ x.done=false) :
    GalilScaffoldDpCost.GuardedRun GalilDpCode.code x (List.replicate (64*bs.length) true) y := by
  induction hr with
  | nil => exact .nil _
  | cons s u t x y z a as hm hc hr ih =>
    have h1 := calls_guarded hc hi
    have hmode := calls_mode_done hc hi
    have h2 := ih (by cases a <;> exact hmode)
    simpa [Nat.mul_add,List.replicate_add,Nat.add_comm] using guarded_append h1 h2

/-- A still-running actual DP has consumed fewer than its certified budget. -/
theorem running_length_lt {p : GalilScaffoldPlace.Place} {lower span : ℕ}
    {s0 : GalilScaffoldSearchFinish.State} {bs : List Bool} {v : SearchVM}
    (hs : s0.mode=.run)
    (hr : DpReached ((GalilScaffoldPlace.stream p).take (span+1)) lower s0 bs v.search v.dp)
    (hm : v.search.mode=.run) : bs.length < dpBudget span := by
  by_contra hbad
  have hh : dpBudget span ≤ bs.length := by omega
  have hi : s0.mode=.run ↔ (⟨GalilScaffoldPreload.initial
      ((GalilScaffoldPlace.stream p).take (span+1)) lower,false⟩ :
        GalilScaffoldControl.Machine 12).done=false := by simp [hs]
  have hactual := quanta_guarded hr hi
  obtain ⟨out,_,hfull⟩ := GalilScaffoldDpCost.scheduled_correct
    ((GalilScaffoldPlace.stream p).take (span+1)) lower
  have hlen : ((GalilScaffoldPlace.stream p).take (span+1)).length ≤ span+1 := List.length_take_le _ _
  have href := GalilScaffoldDpCost.guard_run (hfull (List.replicate (64*bs.length) true) (by
    simp only [List.count_replicate_self]
    unfold dpBudget at hh
    omega))
  have he := guarded_unique hactual href
  have hd := (quanta_mode_done hr hi).mp hm
  rw [he] at hd
  cases hd

private theorem quanta_debt {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (hr : SafeQuanta s x bs t y) : value t.debt = value s.debt - bs.count true := by
  induction hr with
  | nil => simp
  | cons s u t x y z a as hm hc hr ih =>
    have he : u.debt = s.debt := PalPeg.CloseoutPreload13.safe_calls_debt hc
    cases a <;> simp [advance,he,dec_value] at ih ⊢ <;> omega

/-- Clock credit supplies the actual one-step safety precondition. -/
theorem ready_of_budget {p : GalilScaffoldPlace.Place} {lower clock : ℕ} {v : SearchVM}
    (hi : BudgetInv p lower clock v) : SearchReady v := by
  refine ⟨hi.prep_inv,?_⟩
  intro hm
  obtain ⟨span,s0,bs,hspan,hs,hcan,hr,hcredit⟩ := hi.running hm
  have hshort := running_length_lt hs hr hm
  have hnonneg : 0 ≤ value v.search.debt :=
    positive_credit_nonneg hi.clock_le (by omega)
  have hdebt := quanta_debt hr
  let padding := List.replicate (3186*(span+1)+1683) false
  refine ⟨_,lower,s0,bs,padding,?_,hs,hcan,?_,hr⟩
  · have hlen : ((GalilScaffoldPlace.stream p).take (span+1)).length ≤ span+1 := List.length_take_le _ _
    simp [padding, dpBudget]
    omega
  · simp only [List.count_append,padding,List.count_replicate,List.length_replicate]
    norm_num
    omega

/-- The initial grow phase has enough credit even at the largest allowed restart radius. -/
theorem initial_credit (lower rad : ℕ) (hstage : 3*rad ≤ 5*lower) :
    (2*lower+128 : ℕ) ≤ (2048 : ℤ) - 2048*rad + 3583*max lower 1 := by
  have hm : lower ≤ max lower 1 := le_max_left _ _
  omega

/-- The grow potential pays for eight new span cells per work unit. -/
theorem grow_credit {span work lower : ℕ} {D D' : ℤ} (hw : 0 < work)
    (hD : (64*span+2*lower+128 : ℕ) ≤ D+3583*work)
    (hstep : D+4095 ≤ D') :
    (64*(span+8)+2*lower+128 : ℕ) ≤ D'+3583*(work-1) := by
  omega

/-- The double potential pays for two new span cells per tick, including quarter wrap. -/
theorem double_credit {span work lower quarter : ℕ} {D D' : ℤ}
    (hw : 0 < work) (hq : quarter < 4)
    (hD : (64*span+2*lower+128 : ℕ) ≤ D+383*work+512*quarter)
    (hstep : D+(if quarter=3 then 2048 else 0)-1 ≤ D') :
    (64*(span+2)+2*lower+128 : ℕ) ≤
      D'+383*(work-1)+512*((quarter+1)%4) := by
  by_cases he : quarter=3
  · simp only [he,if_true] at *; omega
  · simp only [if_neg he] at hstep
    have hh : (quarter+1)%4 = quarter+1 := Nat.mod_eq_of_lt (by omega)
    simp [hh] at *
    omega

/-- At the end of doubling, the quarter is zero; no reserved credit is lost. -/
theorem double_end_quarter {span work quarter : ℕ}
    (hw : work=0) (hq : quarter<4) (hmod : (span+2*work)%8=0)
    (hqmod : span%8=2*quarter) : quarter=0 := by subst work; simp at hmod; omega

/-- The dispatch credit pays for both the entire preparation and the DP's worst case. -/
theorem dispatch_budget (lower span len : ℕ) (hlen : len ≤ span+1) :
    dpBudget span + (2*lower+2*len+6) + 1 ≤ 64*span+2*lower+128 := by
  unfold dpBudget
  omega

/-- A later stage starts with zero or one negative debt unit, compensated by its clock. -/
theorem double_entry_credit (lower span : ℕ) {D : ℤ}
    (hsize : 8*max lower 1 ≤ span) (hD : 0 ≤ D) :
    (2*lower+128 : ℕ) ≤ D+383*span := by
  have hm : lower ≤ max lower 1 := le_max_left _ _
  have h1 : 1 ≤ max lower 1 := le_max_right _ _
  omega

private theorem advance_canonical (a : Bool) (s : GalilScaffoldSearchFinish.State)
    (hc : Canonical s.debt) : Canonical (advance a s).debt := by
  cases a
  · exact hc
  · exact dec_canonical _ hc

private theorem prep_advance_canonical (a : Bool) (s : GalilScaffoldPrepareControl.State)
    (hc : Canonical s.debt) : Canonical (GalilScaffoldPreparePaced.afterAdvance a s).debt := by
  cases a
  · exact hc
  · exact dec_canonical _ hc

private theorem prep_credit_advance (a : Bool) (clock clock' : ℕ)
    (s : GalilScaffoldPrepareControl.State) (quarter : Fin 4) (lower : Counter)
    (hc : ClockEvent a clock clock') :
    2048*value s.debt+clock-1 ≤ credit clock'
      (SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a s) quarter lower) := by
  have h := credit_advance (GalilScaffoldStagePrepare.runState s quarter) a clock clock' hc
  cases a <;> exact h

private def budgetBegin (lower radius : Counter) : GalilScaffoldSearchFinish.State :=
  GalilScaffoldSearchFinish.begin lower radius

private def budgetBeginVM (v : SearchVM) (lower radius : Counter) : SearchVM :=
  { v with search := budgetBegin lower radius, lower := lower }

/-- Fresh restart, with the actual full clock. -/
theorem budget_begin (p : GalilScaffoldPlace.Place) (v : SearchVM) (lower rad : ℕ)
    (hstage : 3*rad ≤ 5*lower) :
    BudgetInv p lower 2048 (budgetBeginVM v (ofNat lower) (ofNat rad)) := by
  have hw : (GalilScaffoldSearchFinish.begin (ofNat lower) (ofNat rad)).work = ofNat (max lower 1) := by
    cases lower <;> simp [GalilScaffoldSearchFinish.begin,zero,ofNat,inc]
  have hc : Canonical (GalilScaffoldSearchFinish.initialDebt (ofNat rad)) :=
    initialDebt_canonical _ (ofNat_canonical _)
  refine ⟨by omega,le_rfl,rfl,hc,?_,⟨0,rfl⟩,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [budgetBeginVM,budgetBegin,PrepInv,SearchVM.toPrep,GalilScaffoldSearchFinish.begin]
  · intro _; exact ⟨max lower 1,hw⟩
  · intro hn; exact (hn rfl).elim
  · intro _
    cases lower <;> simp [budgetBeginVM,budgetBegin,GalilScaffoldSearchFinish.begin,
      zero,ofNat,inc,reset,value]
  · intro _
    have h := initial_credit lower rad hstage
    cases lower <;> simp [budgetBeginVM,budgetBegin,credit,hw,GalilScaffoldSearchFinish.begin,
      GalilScaffoldSearchFinish.initialDebt,zero,ofNat,inc,value,reset] at h ⊢ <;> omega
  all_goals intro h; simp [budgetBeginVM,budgetBegin,Preparing,GalilScaffoldSearchFinish.begin] at h

private theorem prep_inv_searchStep {p : GalilScaffoldPlace.Place} {v v' : SearchVM} {a : Bool}
    (hi : PrepInv v.toPrep) (ht : searchStep p a v v') : PrepInv v'.toPrep := by
  cases hm : v.search.mode with
  | idle | found | missed => simp only [searchStep,hm] at ht; subst v'; exact hi
  | lower | lowerHome | copy | home =>
    simp only [searchStep,hm] at ht
    obtain ⟨u,hu,rfl⟩ := ht
    exact GalilSearchReadyInv.prepInv_afterAdvance a (prepInv_tick hu hi)
  | run =>
    simp only [searchStep,hm] at ht
    obtain ⟨hq,_,_⟩ := ht
    have he := safe_quanta_exit hq (by simp [ExitMode,hm])
    rcases he with h|h|h|h|h <;> simp [PrepInv,SearchVM.toPrep,h]
  | grow | double =>
    simp only [searchStep,hm] at ht
    split at ht
    · subst v'; cases a <;>
        simp [PrepInv,SearchVM.toPrep,SearchVM.ofPrep,GalilScaffoldStagePrepare.runState,
          GalilScaffoldPreparePaced.afterAdvance,GalilScaffoldStagePrepare.growStep,
          GalilScaffoldDouble.step,advance,hm]
    · subst v'
      exact GalilSearchReadyInv.prepInv_afterAdvance a (prepInv_prepare _ _ _)
  | wait =>
    simp only [searchStep,hm] at ht
    subst v'
    cases a <;> simp [PrepInv,SearchVM.toPrep,GalilScaffoldDouble.waitStep,
      GalilScaffoldDouble.enter,advance,hm] <;> split <;> simp_all

/-- Dispatch spends one clock credit and installs the complete prep/DP budget. -/
private theorem budget_dispatch {p : GalilScaffoldPlace.Place} {lower clock clock' : ℕ}
    {v : SearchVM} {a : Bool} (hi : BudgetInv p lower clock v)
    (hc : ClockEvent a clock clock') (m : ℕ) (hspan : v.search.span=ofNat m)
    (hsize : 8*max lower 1 ≤ m ∧ m%8=0)
    (hfund : (64*m+2*lower+128 : ℕ) ≤ credit clock v) :
    BudgetInv p lower clock' (SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
      (GalilScaffoldPrepareControl.prepare v.toPrep v.lower p)) v.search.quarter v.lower) := by
  let t := SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
    (GalilScaffoldPrepareControl.prepare v.toPrep v.lower p)) v.search.quarter v.lower
  have hspan' : t.search.span=ofNat m := by cases a <;> exact hspan
  have hmode : t.search.mode=.lower := by cases a <;> rfl
  have hdebt : Canonical t.search.debt := prep_advance_canonical a _ hi.debt_canonical
  refine ⟨hc.2.2.1,hc.2.2.2.1,hi.lower_eq,hdebt,?_,⟨m,hspan'⟩,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact GalilSearchReadyInv.prepInv_afterAdvance a (prepInv_prepare _ _ _)
  · intro h
    have hh : t.search.mode = .grow ∨ t.search.mode = .double := by simpa [t] using h
    rcases hh with hh | hh <;> simp [hmode] at hh
  · intro _ _
    change 8*max lower 1 ≤ (value t.search.span).toNat ∧ (value t.search.span).toNat % 8 = 0
    simpa [hspan',ofNat_value] using hsize
  · intro h
    have hh : t.search.mode = .grow := by simpa [t] using h
    simp [hmode] at hh
  · intro h
    have hh : t.search.mode = .grow := by simpa [t] using h
    simp [hmode] at hh
  · intro h
    have hh : t.search.mode = .double := by simpa [t] using h
    simp [hmode] at hh
  · intro h
    have hh : t.search.mode = .double := by simpa [t] using h
    simp [hmode] at hh
  · intro _
    obtain ⟨u,hu,hum,hup,hud,_,_⟩ := GalilScaffoldPrepareControl.prepare_complete v.toPrep lower m p hspan
    cases hu with
    | intro _ _ hrun =>
      have href := prep_run_rebase hrun (if a then dec v.search.debt else v.search.debt)
      refine ⟨m,2*lower + 2*((GalilScaffoldPlace.stream p).take (m+1)).length + 6,
        {u with debt := if a then dec v.search.debt else v.search.debt},hspan',?_,hum,hup,hud,?_⟩
      · simpa only [t,toPrep_ofPrep,hi.lower_eq] using (by cases a <;> exact href)
      · have hlen : ((GalilScaffoldPlace.stream p).take (m+1)).length ≤ m+1 := List.length_take_le _ _
        have hbud := dispatch_budget lower m _ hlen
        have hstep := prep_credit_advance a clock clock'
          (GalilScaffoldPrepareControl.prepare v.toPrep v.lower p) v.search.quarter v.lower hc
        change credit clock v-1 ≤ credit clock' t at hstep
        change (dpBudget m : ℤ) +
          (2*lower + 2*((GalilScaffoldPlace.stream p).take (m+1)).length + 6 : ℕ) ≤ credit clock' t
        omega
  · intro h
    have hh : t.search.mode = .run := by simpa [t] using h
    simp [hmode] at hh

/-- Preparation ticks consume their exact certificate one cell at a time. -/
private theorem budget_prep {p : GalilScaffoldPlace.Place} {lower clock clock' : ℕ}
    {v : SearchVM} {u : GalilScaffoldPrepareControl.State} {a : Bool}
    (hi : BudgetInv p lower clock v) (hm : Preparing v.search.mode)
    (ht : GalilScaffoldPrepareControl.Tick true v.toPrep u) (hc : ClockEvent a clock clock') :
    BudgetInv p lower clock' (SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a u)
      v.search.quarter v.lower) := by
  let t := SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a u) v.search.quarter v.lower
  obtain ⟨span,n,target,hspan,href,htm,htc,htd,hfund⟩ := hi.prep hm
  have hnotrun : v.toPrep.mode ≠ .run := by rcases hm with h|h|h|h <;> simp [SearchVM.toPrep,h]
  have hn : 0<n := by cases n with
    | zero => cases href; exact (hnotrun htm).elim
    | succ n => omega
  obtain ⟨r,rfl⟩ : ∃ r,n=r+1 := ⟨n-1,by omega⟩
  simp only [List.replicate_succ] at href
  cases href with
  | cons _ z _ _ _ hz htail =>
    have he := Prep.tick_unique ht hz
    subst z
    have hd : u.debt=v.search.debt := GalilScaffoldPrepareControl.tick_debt ht
    have hs : u.span=v.search.span :=
      GalilScaffoldPrepareControl.run_span (.cons _ _ _ true [] ht (.nil _))
    have htspan : t.search.span=ofNat span := by cases a <;> exact hs.trans hspan
    have hcanon : Canonical t.search.debt := prep_advance_canonical a u (hd ▸ hi.debt_canonical)
    have hstep := prep_credit_advance a clock clock' u v.search.quarter v.lower hc
    rw [hd] at hstep
    change credit clock v - 1 ≤ credit clock' t at hstep
    have hpaid : (dpBudget span+r : ℕ) ≤ credit clock' t := by
      omega
    have hfut : PrepFuture ((GalilScaffoldPlace.stream p).take (span+1)) lower t.toPrep :=
      prepFuture_advance ⟨r,target,htail,htm,htc,htd⟩ a
    have hmodes : Preparing t.search.mode ∨ t.search.mode=.run := by
      cases ht <;> cases a <;> simp_all [t,Preparing,SearchVM.ofPrep,
        GalilScaffoldStagePrepare.runState,GalilScaffoldPreparePaced.afterAdvance]
    refine ⟨hc.2.2.1,hc.2.2.2.1,hi.lower_eq,hcanon,
      GalilSearchReadyInv.prepInv_afterAdvance a (prepInv_tick ht hi.prep_inv),⟨span,htspan⟩,
      ?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro h
      change t.search.mode = .grow ∨ t.search.mode = .double at h
      rcases hmodes with hp | hr
      · rcases hp with hp | hp | hp | hp <;> simp [hp] at h
      · simp [hr] at h
    · intro _ _
      have hng : v.search.mode ≠ .grow := by rcases hm with h|h|h|h <;> simp [h]
      have hnd : v.search.mode ≠ .double := by rcases hm with h|h|h|h <;> simp [h]
      have hsz := hi.stage_size hng hnd
      rw [hspan] at hsz
      change 8*max lower 1 ≤ (value t.search.span).toNat ∧ (value t.search.span).toNat % 8 = 0
      simpa [htspan,ofNat_value] using hsz
    · intro h
      change t.search.mode = .grow at h
      rcases hmodes with hp | hr
      · rcases hp with hp | hp | hp | hp <;> simp [hp] at h
      · simp [hr] at h
    · intro h
      change t.search.mode = .grow at h
      rcases hmodes with hp | hr
      · rcases hp with hp | hp | hp | hp <;> simp [hp] at h
      · simp [hr] at h
    · intro h
      change t.search.mode = .double at h
      rcases hmodes with hp | hr
      · rcases hp with hp | hp | hp | hp <;> simp [hp] at h
      · simp [hr] at h
    · intro h
      change t.search.mode = .double at h
      rcases hmodes with hp | hr
      · rcases hp with hp | hp | hp | hp <;> simp [hp] at h
      · simp [hr] at h
    · intro _
      refine ⟨span,r,{target with debt := if a then dec u.debt else u.debt},htspan,?_,htm,htc,htd,hpaid⟩
      cases a <;> exact prep_run_rebase htail _
    · intro hrun
      have hinit := prepFuture_run hfut hrun
      have hdp : t.dp=⟨GalilScaffoldPreload.initial
          ((GalilScaffoldPlace.stream p).take (span+1)) lower,false⟩ := by
        cases htconf : t.dp with
        | mk cfg done => simp_all [SearchVM.toPrep]
      refine ⟨span,t.search,[],htspan,hrun,hcanon,?_,?_⟩
      · rw [hdp]; exact dpReached_start _ _ _
      · simp only [List.length_nil,Nat.cast_zero,add_zero]
        have hle : (dpBudget span : ℤ) ≤ dpBudget span + r := by omega
        exact hle.trans hpaid

private theorem budget_grow {p : GalilScaffoldPlace.Place} {lower clock clock' : ℕ}
    {v : SearchVM} {a : Bool} (hi : BudgetInv p lower clock v)
    (hm : v.search.mode=.grow) (hp : positive v.search.work=true) (hc : ClockEvent a clock clock') :
    BudgetInv p lower clock' (SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
      (GalilScaffoldStagePrepare.growStep v.toPrep)) v.search.quarter v.lower) := by
  let t := SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
    (GalilScaffoldStagePrepare.growStep v.toPrep)) v.search.quarter v.lower
  obtain ⟨span,hs⟩ := hi.span_nat
  obtain ⟨work,hw⟩ := hi.work_nat (Or.inl hm)
  have hwork : 0<work := by simpa [hw,positive_ofNat] using hp
  have hmode : t.search.mode=.grow := by cases a <;> exact hm
  have htspan : t.search.span=ofNat (span+8) := by
    cases a <;> simp [t,SearchVM.ofPrep,SearchVM.toPrep,GalilScaffoldStagePrepare.runState,
      GalilScaffoldPreparePaced.afterAdvance,GalilScaffoldStagePrepare.growStep,hs,
      GalilScaffoldStagePrepare.add_ofNat]
  have htwork : t.search.work=ofNat (work-1) := by
    obtain ⟨r,rfl⟩ : ∃ r,work=r+1 := ⟨work-1,by omega⟩
    cases a <;> simp [t,SearchVM.ofPrep,SearchVM.toPrep,GalilScaffoldStagePrepare.runState,
      GalilScaffoldPreparePaced.afterAdvance,GalilScaffoldStagePrepare.growStep,hw,dec_ofNat_succ]
  have hcanon : Canonical t.search.debt :=
    prep_advance_canonical a _ (GalilScaffoldGrow.add_canonical 2 _ hi.debt_canonical)
  have hstep : credit clock v+4095 ≤ credit clock' t := by
    have hh := prep_credit_advance a clock clock' (GalilScaffoldStagePrepare.growStep v.toPrep)
      v.search.quarter v.lower hc
    change 2048 * value v.search.debt + clock + 4095 ≤ 2048 * value t.search.debt + clock'
    have hhv : 2048 * (value v.search.debt + 2) + clock ≤ credit clock' t + 1 := by
      simpa [t,GalilScaffoldStagePrepare.growStep,SearchVM.toPrep,
        GalilScaffoldGrow.add_value] using hh
    unfold credit at hhv
    omega
  refine ⟨hc.2.2.1,hc.2.2.2.1,hi.lower_eq,hcanon,?_,⟨span+8,htspan⟩,
    fun _ => ⟨work-1,htwork⟩,?_,?_,?_,?_,?_,?_,?_⟩
  · change PrepInv t.toPrep
    simp [PrepInv,SearchVM.toPrep,hmode]
  · intro h; exact (h hmode).elim
  · intro _
    change value t.search.span + 8*value t.search.work = 8*max lower 1
    have hh := hi.grow_size hm
    simp only [hs,hw,htspan,htwork,ofNat_value] at hh ⊢
    omega
  · intro _
    change 64*value t.search.span + 2*lower + 128 ≤ credit clock' t + 3583*value t.search.work
    have hh := hi.grow hm
    simp only [hs,hw,ofNat_value] at hh
    have hn := grow_credit hwork hh hstep
    rw [htspan,htwork]
    simp only [ofNat_value]
    rw [Nat.cast_sub (by omega : 1 ≤ work)]
    norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ofNat_value] at hn ⊢
    exact hn
  · intro h
    change t.search.mode = .double at h
    simp [hmode] at h
  · intro h
    change t.search.mode = .double at h
    simp [hmode] at h
  · intro h
    change Preparing t.search.mode at h
    simp [hmode,Preparing] at h
  · intro h
    change t.search.mode = .run at h
    simp [hmode] at h

private theorem budget_double {p : GalilScaffoldPlace.Place} {lower clock clock' : ℕ}
    {v : SearchVM} {a : Bool} (hi : BudgetInv p lower clock v)
    (hm : v.search.mode=.double) (hp : positive v.search.work=true) (hc : ClockEvent a clock clock') :
    BudgetInv p lower clock' {v with search := advance a (GalilScaffoldDouble.step v.search)} := by
  let t : SearchVM := {v with search := advance a (GalilScaffoldDouble.step v.search)}
  obtain ⟨span,hs⟩ := hi.span_nat
  obtain ⟨work,hw⟩ := hi.work_nat (Or.inr hm)
  have hwork : 0<work := by simpa [hw,positive_ofNat] using hp
  have hmode : t.search.mode=.double := by cases a <;> exact hm
  have htspan : t.search.span=ofNat (span+2) := by cases a <;> simp [t,advance,GalilScaffoldDouble.step,hs,inc_ofNat]
  have htwork : t.search.work=ofNat (work-1) := by
    obtain ⟨r,rfl⟩ : ∃ r,work=r+1 := ⟨work-1,by omega⟩
    cases a <;> simp [t,advance,GalilScaffoldDouble.step,hw,dec_ofNat_succ]
  have htq : t.search.quarter.val=(v.search.quarter.val+1)%4 := by cases a <;> rfl
  have hcanon : Canonical t.search.debt := by
    apply advance_canonical
    change Canonical (if v.search.quarter.val=3 then inc v.search.debt else v.search.debt)
    split
    · exact inc_canonical _ hi.debt_canonical
    · exact hi.debt_canonical
  have hstep : credit clock v+(if v.search.quarter.val=3 then 2048 else 0)-1 ≤ credit clock' t := by
    have hh := credit_advance (GalilScaffoldDouble.step v.search) a clock clock' hc
    unfold credit
    by_cases hq : v.search.quarter.val=3
    · have hhv := hh
      simp [t,GalilScaffoldDouble.step,hq,inc_value] at hhv ⊢
      omega
    · simpa [credit,t,GalilScaffoldDouble.step,hq] using hh
  refine ⟨hc.2.2.1,hc.2.2.2.1,hi.lower_eq,hcanon,?_,⟨span+2,htspan⟩,
    fun _ => ⟨work-1,htwork⟩,?_,?_,?_,?_,?_,?_,?_⟩
  · change PrepInv t.toPrep
    simp [PrepInv,SearchVM.toPrep,hmode]
  · intro _ h
    change t.search.mode ≠ .double at h
    exact (h hmode).elim
  · intro h
    change t.search.mode = .grow at h
    simp [hmode] at h
  · intro h
    change t.search.mode = .grow at h
    simp [hmode] at h
  · intro _
    change 64*value t.search.span + 2*lower + 128 ≤
      credit clock' t + 383*value t.search.work + 512*t.search.quarter.val
    have hh := hi.doubling hm
    simp only [hs,hw,ofNat_value] at hh
    have hn := double_credit hwork v.search.quarter.isLt hh hstep
    rw [htspan,htwork]
    simp only [ofNat_value]
    rw [Nat.cast_sub (by omega : 1 ≤ work)]
    simpa [htq] using hn
  · intro _
    change 16*max lower 1 ≤ (value t.search.span + 2*value t.search.work).toNat ∧
      (value t.search.span + 2*value t.search.work).toNat % 8 = 0 ∧
      (value t.search.span).toNat % 8 = 2*t.search.quarter.val
    have hh := hi.double_size hm
    simp only [hs,hw,htspan,htwork,htq,ofNat_value] at hh ⊢
    norm_cast at hh ⊢
    have hq := v.search.quarter.isLt
    omega
  · intro h
    change Preparing t.search.mode at h
    simp [hmode,Preparing] at h
  · intro h
    change t.search.mode = .run at h
    simp [hmode] at h

private theorem calls_debt_eq {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {bs : List Bool} (hr : SafeCalls s x bs t y) :
    t.debt=s.debt := by
  induction hr with
  | nil => rfl
  | cons s x y z b bs t ht hsafe hr ih => exact ih.trans (finish_debt s _ _ _)

private theorem quanta_canonical {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (hr : SafeQuanta s x bs t y) (hc : Canonical s.debt) : Canonical t.debt := by
  induction hr with
  | nil => exact hc
  | cons s u t x y z a as hm hq hr ih =>
    apply ih
    apply advance_canonical
    rw [calls_debt_eq hq]; exact hc

private theorem calls_double_zero {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (hr : SafeCalls s x bs t y) (hi : s.mode=.double → zero s.debt=true) :
    t.mode=.double → zero t.debt=true := by
  induction hr with
  | nil => exact hi
  | cons s x y z b bs t ht hsafe hr ih =>
    apply ih
    by_cases hm : s.mode=.run
    · cases b <;> cases hd : y.done <;> by_cases hp : y.config.pc=346 <;>
        cases hf : s.finalStage <;> cases hz : zero s.debt <;>
        simp_all [GalilScaffoldSearchFinish.finish]
    · simpa [GalilScaffoldSearchFinish.finish,hm] using hi

/-- A quantum either spends its reserved DP credit or enters a funded double. -/
private theorem budget_run {p : GalilScaffoldPlace.Place} {lower clock clock' : ℕ}
    {v v' : SearchVM} {a : Bool} (hi : BudgetInv p lower clock v)
    (hm : v.search.mode=.run) (hc : ClockEvent a clock clock')
    (hq : SafeQuanta v.search v.dp [a] v'.search v'.dp) (hl : v'.lower=v.lower) :
    BudgetInv p lower clock' v' := by
  obtain ⟨span,s0,bs,hspan,hs,hcan,hr,hfund⟩ := hi.running hm
  have hsize : 8*max lower 1 ≤ span ∧ span%8=0 := by
    simpa [hspan,ofNat_value] using hi.stage_size (by simp [hm]) (by simp [hm])
  have hdebtcanon := quanta_canonical hq hi.debt_canonical
  have hframe := (safe_quanta_frame hq).2
  have hmodes := safe_quanta_exit hq (Or.inl hm)
  have hstep : credit clock v-1 ≤ credit clock' v' := by
    have he := quanta_debt hq
    have hh := hc.2.2.2.2
    unfold credit
    cases a <;> simp at he hh <;> omega
  have hspan' : v'.search.mode≠.double → v'.search.span=ofNat span := by
    intro hn
    simpa [stageSpan,hm,hn,hspan] using hframe
  have hdouble : v'.search.mode=.double →
      v'.search.span=reset ∧ v'.search.quarter=0 ∧ v'.search.work=ofNat span ∧ 0≤credit clock' v' := by
    intro hd
    obtain ⟨hz,hq0⟩ := double_reset_of_quanta hq hm hd
    have hw := double_work_of_quanta hq hm hd
    refine ⟨hz,hq0,hw.trans hspan,?_⟩
    obtain ⟨u,z,hcalls,he⟩ := PalPeg.CloseoutPreload34.safeQuanta_single hq
    have hu : u.mode=.double := by rw [he] at hd; cases a <;> exact hd
    have hzero := calls_double_zero hcalls (by simp [hm]) hu
    have hval := (zero_iff u.debt (by rw [calls_debt_eq hcalls]; exact hi.debt_canonical)).mp hzero
    have hclockMin := hc.1
    have hclockMax := hc.2.2.2.1
    have hclock := hc.2.2.2.2
    have hvd : value v'.search.debt = if a then -1 else 0 := by
      rw [congrArg (fun s => s.debt) he]
      cases a <;> simp [advance,dec_value,hval]
    unfold credit
    rw [hvd]
    cases a <;> simp at hclock ⊢ <;> omega
  refine ⟨hc.2.2.1,hc.2.2.2.1,hl.trans hi.lower_eq,hdebtcanon,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rcases hmodes with h|h|h|h|h <;> simp [PrepInv,SearchVM.toPrep,h]
  · by_cases hd : v'.search.mode=.double
    · exact ⟨0,(hdouble hd).1⟩
    · exact ⟨span,hspan' hd⟩
  · intro h
    rcases h with h|h
    · rcases hmodes with he|he|he|he|he <;> simp_all
    · exact ⟨span,(hdouble h).2.2.1⟩
  · intro _ hn; simpa [hspan' hn,ofNat_value] using hsize
  · intro h; rcases hmodes with he|he|he|he|he <;> simp_all
  · intro h; rcases hmodes with he|he|he|he|he <;> simp_all
  · intro hd
    obtain ⟨hz,hq0,hw,hpos⟩ := hdouble hd
    have hh := double_entry_credit lower span hsize.1 hpos
    rw [hz,hq0,hw]
    simp only [ofNat_value]
    simpa [reset,value] using hh
  · intro hd
    obtain ⟨hz,hq0,hw,_⟩ := hdouble hd
    have hw' : v'.search.work = ofNat span := hw
    rw [hz,hq0,hw']
    rw [reset_eq_ofNat, ofNat_value, ofNat_value]
    norm_num
    omega
  · intro h; rcases hmodes with he|he|he|he|he <;> simp_all [Preparing]
  · intro hrun
    refine ⟨span,s0,bs++[a],hspan' (by simp [hrun]),hs,hcan,dpReached_step hr hq,?_⟩
    simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
    omega

private theorem budget_wait {p : GalilScaffoldPlace.Place} {lower clock clock' : ℕ}
    {v : SearchVM} {a : Bool} (hi : BudgetInv p lower clock v)
    (hm : v.search.mode=.wait) (hc : ClockEvent a clock clock') :
    BudgetInv p lower clock'
      {v with search := advance a (GalilScaffoldDouble.waitStep true v.search)} := by
  let t : SearchVM := {v with search := advance a (GalilScaffoldDouble.waitStep true v.search)}
  obtain ⟨span,hspan⟩ := hi.span_nat
  have hsize := hi.stage_size (by simp [hm]) (by simp [hm])
  by_cases hz : zero v.search.debt=true
  · have hval := (zero_iff v.search.debt hi.debt_canonical).mp hz
    have hmode : t.search.mode=.double := by
      cases a <;> simp [t,GalilScaffoldDouble.waitStep,hm,hz,GalilScaffoldDouble.enter,advance]
    have htspan : t.search.span=reset := by
      cases a <;> simp [t,GalilScaffoldDouble.waitStep,hm,hz,GalilScaffoldDouble.enter,advance]
    have htwork : t.search.work=ofNat span := by
      cases a <;> simp [t,GalilScaffoldDouble.waitStep,hm,hz,GalilScaffoldDouble.enter,advance,hspan]
    have htq : t.search.quarter=0 := by
      cases a <;> simp [t,GalilScaffoldDouble.waitStep,hm,hz,GalilScaffoldDouble.enter,advance]
    have hcanon : Canonical t.search.debt := by
      apply advance_canonical
      simpa [GalilScaffoldDouble.waitStep,hm,hz,GalilScaffoldDouble.enter] using hi.debt_canonical
    have hcredit : 0 ≤ credit clock' t := by
      have hmin := hc.1
      have hmax := hc.2.2.2.1
      have hevent := hc.2.2.2.2
      unfold credit
      cases a <;>
        simp [t,GalilScaffoldDouble.waitStep,hm,hz,GalilScaffoldDouble.enter,
          advance,dec_value,hval] at hevent ⊢ <;> omega
    refine ⟨hc.2.2.1,hc.2.2.2.1,hi.lower_eq,hcanon,?_,⟨0,htspan⟩,
      (fun _ => ⟨span,htwork⟩),?_,?_,?_,?_,?_,?_,?_⟩
    · change PrepInv t.toPrep
      simp [PrepInv,SearchVM.toPrep,hmode]
    · intro _ h; change t.search.mode ≠ .double at h; exact (h hmode).elim
    · intro h; change t.search.mode = .grow at h; simp [hmode] at h
    · intro h; change t.search.mode = .grow at h; simp [hmode] at h
    · intro _
      change 64*value t.search.span + 2*lower + 128 ≤
        credit clock' t + 383*value t.search.work + 512*t.search.quarter.val
      rw [htspan,htwork,htq]
      simp only [reset_eq_ofNat,ofNat_value]
      have hmxl : lower ≤ max lower 1 := le_max_left _ _
      simp [hspan,ofNat_value] at hsize
      norm_num
      omega
    · intro _
      change 16*max lower 1 ≤ (value t.search.span+2*value t.search.work).toNat ∧
        (value t.search.span+2*value t.search.work).toNat%8=0 ∧
        (value t.search.span).toNat%8=2*t.search.quarter.val
      rw [htspan,htwork,htq]
      simp only [reset_eq_ofNat,ofNat_value]
      norm_num
      simp [hspan,ofNat_value] at hsize
      omega
    · intro h; change Preparing t.search.mode at h; simp [hmode,Preparing] at h
    · intro h; change t.search.mode=.run at h; simp [hmode] at h
  · have hmode : t.search.mode=.wait := by
      cases a <;> simp [t,GalilScaffoldDouble.waitStep,hm,hz,advance]
    have hcanon : Canonical t.search.debt := by
      apply advance_canonical
      simpa [GalilScaffoldDouble.waitStep,hm,hz] using hi.debt_canonical
    refine ⟨hc.2.2.1,hc.2.2.2.1,hi.lower_eq,hcanon,?_,⟨span,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · change PrepInv t.toPrep
      simp [PrepInv,SearchVM.toPrep,hmode]
    · cases a <;> simpa [t,GalilScaffoldDouble.waitStep,hm,hz,advance] using hspan
    · intro h
      change t.search.mode=.grow ∨ t.search.mode=.double at h
      rcases h with h|h <;> simp [hmode] at h
    · intro _ _
      change 8*max lower 1 ≤ (value t.search.span).toNat ∧ _
      cases a <;> simpa [t,GalilScaffoldDouble.waitStep,hm,hz,advance] using hsize
    · intro h; change t.search.mode=.grow at h; simp [hmode] at h
    · intro h; change t.search.mode=.grow at h; simp [hmode] at h
    · intro h; change t.search.mode=.double at h; simp [hmode] at h
    · intro h; change t.search.mode=.double at h; simp [hmode] at h
    · intro h; change Preparing t.search.mode at h; simp [Preparing,hmode] at h
    · intro h; change t.search.mode=.run at h; simp [hmode] at h

private theorem budget_terminal {p : GalilScaffoldPlace.Place} {lower clock clock' : ℕ}
    {v : SearchVM} {a : Bool} (hi : BudgetInv p lower clock v)
    (hm : v.search.mode=.idle ∨ v.search.mode=.found ∨ v.search.mode=.missed)
    (hc : ClockEvent a clock clock') : BudgetInv p lower clock' v := by
  refine ⟨hc.2.2.1,hc.2.2.2.1,hi.lower_eq,hi.debt_canonical,hi.prep_inv,
    hi.span_nat,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro h; rcases hm with hm|hm|hm <;> simp [hm] at h
  · exact hi.stage_size
  · intro h; rcases hm with hm|hm|hm <;> simp [hm] at h
  · intro h; rcases hm with hm|hm|hm <;> simp [hm] at h
  · intro h; rcases hm with hm|hm|hm <;> simp [hm] at h
  · intro h; rcases hm with hm|hm|hm <;> simp [hm] at h
  · intro h; rcases hm with hm|hm|hm <;> simp [hm,Preparing] at h
  · intro h; rcases hm with hm|hm|hm <;> simp [hm] at h

/-- The actual clock event preserves the quantitative search certificate. -/
theorem budget_step {p : GalilScaffoldPlace.Place} {lower clock clock' : ℕ}
    {v v' : SearchVM} {a : Bool} (hi : BudgetInv p lower clock v)
    (hc : ClockEvent a clock clock') (ht : searchStep p a v v') :
    BudgetInv p lower clock' v' := by
  cases hm : v.search.mode with
  | idle | found | missed =>
      simp only [searchStep,hm] at ht
      subst v'
      exact budget_terminal hi (by simp [hm]) hc
  | lower | lowerHome | copy | home =>
      simp only [searchStep,hm] at ht
      obtain ⟨u,hu,rfl⟩ := ht
      exact budget_prep hi (by simp [Preparing,hm]) hu hc
  | run =>
      simp only [searchStep,hm] at ht
      exact budget_run hi hm hc ht.1 ht.2.1
  | wait =>
      simp only [searchStep,hm] at ht
      subst v'
      exact budget_wait hi hm hc
  | grow =>
      simp only [searchStep,hm] at ht
      by_cases hp : positive v.search.work=true
      · simp only [hp,if_true] at ht
        subst v'
        exact budget_grow hi hm hp hc
      · simp only [hp,Bool.false_eq_true,if_false] at ht
        subst v'
        obtain ⟨span,hspan⟩ := hi.span_nat
        obtain ⟨work,hwork⟩ := hi.work_nat (Or.inl hm)
        have hw0 : work=0 := by
          simp [hwork,positive_ofNat] at hp
          omega
        have hsz := hi.grow_size hm
        have hfund := hi.grow hm
        simp [hspan,hwork,hw0,ofNat_value] at hsz hfund
        apply budget_dispatch hi hc span hspan
        · constructor <;> omega
        · omega
  | double =>
      simp only [searchStep,hm] at ht
      by_cases hp : positive v.search.work=true
      · simp only [hp,if_true] at ht
        subst v'
        exact budget_double hi hm hp hc
      · simp only [hp,Bool.false_eq_true,if_false] at ht
        subst v'
        obtain ⟨span,hspan⟩ := hi.span_nat
        obtain ⟨work,hwork⟩ := hi.work_nat (Or.inr hm)
        have hw0 : work=0 := by
          simp [hwork,positive_ofNat] at hp
          omega
        have hds := hi.double_size hm
        simp only [hspan,hwork,ofNat_value] at hds
        norm_cast at hds
        have hq0 : v.search.quarter.val=0 := by
          apply double_end_quarter hw0 v.search.quarter.isLt
          · exact hds.2.1
          · exact hds.2.2
        have hfund := hi.doubling hm
        simp [hspan,hwork,hw0,hq0,ofNat_value] at hfund hds
        apply budget_dispatch hi hc span hspan
        · constructor <;> omega
        · omega

/-- Before a dispatch the place has not entered the preparation certificate yet. -/
private theorem budget_rebase_dispatch {p p' : GalilScaffoldPlace.Place}
    {lower clock : ℕ} {v : SearchVM} (hi : BudgetInv p lower clock v)
    (hm : v.search.mode=.grow ∨ v.search.mode=.double) : BudgetInv p' lower clock v := by
  refine ⟨hi.clock_pos,hi.clock_le,hi.lower_eq,hi.debt_canonical,hi.prep_inv,
    hi.span_nat,hi.work_nat,hi.stage_size,hi.grow_size,hi.grow,hi.doubling,
    hi.double_size,?_,?_⟩
  · intro h
    rcases hm with hm|hm <;> rcases h with h|h|h|h <;> simp_all
  · intro h
    rcases hm with hm|hm <;> simp_all

def BudgetSome (lower clock : ℕ) (v : SearchVM) : Prop :=
  ∃ p, BudgetInv p lower clock v

/-- One actual search event may choose a new place only at a dispatch boundary. -/
theorem budgetSome_step {lower clock clock' : ℕ} {v v' : SearchVM} {a : Bool}
    (hi : BudgetSome lower clock v) (hc : ClockEvent a clock clock')
    (p : GalilScaffoldPlace.Place) (ht : searchStep p a v v') :
    BudgetSome lower clock' v' := by
  obtain ⟨p₀,hi⟩ := hi
  cases hm : v.search.mode with
  | grow => exact ⟨p,budget_step (budget_rebase_dispatch hi (Or.inl hm)) hc ht⟩
  | double => exact ⟨p,budget_step (budget_rebase_dispatch hi (Or.inr hm)) hc ht⟩
  | idle | found | missed | lower | lowerHome | copy | home | run | wait =>
      have ht' : searchStep p₀ a v v' := by
        simp only [searchStep,hm] at ht ⊢
        exact ht
      exact ⟨p₀,budget_step hi hc ht'⟩

/-- The concrete budget calibration at every fresh restart, at the place the caller names,
together with the shape of the restarted search. -/
theorem budgetInv_restarted (p : GalilScaffoldPlace.Place)
    {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ}
    {last : Counter} (hR : Restarted raw r Rad last) (hSE : StageEntry Rad last) :
    ∃ lower, BudgetInv p lower 2048 (searchLens.get r) ∧
      (searchLens.get r).search = GalilScaffoldSearchFinish.begin (ofNat lower) r.radius := by
  obtain ⟨_,_,_,_,⟨hRadCan,hRad⟩,_,hSearch,hLower,hLastCan,hLastNonneg⟩ := hR
  let lower := (value last).toNat
  have hLast : last = ofNat lower := canonical_eq_ofNat last hLastCan hLastNonneg
  have hRadCounter : r.radius = ofNat Rad := by
    rw [canonical_eq_ofNat r.radius hRadCan (by rw [hRad]; omega)]
    simp [hRad]
  have hStage : 3 * Rad ≤ 5 * lower := hSE lower (by
    simp only [lower, Int.toNat_of_nonneg hLastNonneg])
  have hb := budget_begin p (searchLens.get r) lower Rad hStage
  have hs : (searchLens.get r).search =
      GalilScaffoldSearchFinish.begin (ofNat lower) (ofNat Rad) := by
    simpa [searchLens,hLast,hRadCounter] using hSearch
  have hl : (searchLens.get r).lower = ofNat lower := by
    simpa [searchLens,hLast] using hLower
  have he : budgetBeginVM (searchLens.get r) (ofNat lower) (ofNat Rad) = searchLens.get r := by
    rcases hv : searchLens.get r with ⟨s,d,l,w⟩
    simp only [hv] at hs hl ⊢
    subst s; subst l
    rfl
  rw [he] at hb
  exact ⟨lower,hb,by rw [hs,hRadCounter]⟩

/-- The same calibration with the place forgotten. -/
theorem budgetSome_restarted (p : GalilScaffoldPlace.Place)
    {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ}
    {last : Counter} (hR : Restarted raw r Rad last) (hSE : StageEntry Rad last) :
    ∃ lower, BudgetSome lower 2048 (searchLens.get r) := by
  obtain ⟨lower,hb,-⟩ := budgetInv_restarted p hR hSE
  exact ⟨lower,p,hb⟩

theorem ready_restarted (p : GalilScaffoldPlace.Place)
    {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ}
    {last : Counter} (hR : Restarted raw r Rad last) (hSE : StageEntry Rad last) :
    SearchReady (searchLens.get r) := by
  obtain ⟨_,_,h⟩ := budgetSome_restarted p hR hSE
  exact ready_of_budget h

end PalPeg.CanonicalSearchBudget
