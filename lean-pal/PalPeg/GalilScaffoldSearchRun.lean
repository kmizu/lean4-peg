import PalPeg.GalilScaffoldDpCost
import PalPeg.GalilScaffoldSearchFinish
import PalPeg.GalilScaffoldTimingCost
import PalPeg.GalilDpSuffix

set_option autoImplicit false
namespace PalPeg.GalilScaffoldSearchRun
open GalilScaffoldControl GalilScaffoldSearchFinish

theorem finish_run_iff (s : State) (enabled done : Bool) (pc : ℕ) :
    (finish s enabled done pc).mode = .run ↔
      s.mode = .run ∧ (enabled = false ∨ done = false) := by
  cases enabled <;> cases done <;>
    by_cases hp : pc = 346 <;> cases hf : s.finalStage <;>
    cases hz : GalilScaffoldCounter.zero s.debt <;> simp [finish,hp,hf,hz]

/-- One run-mode instruction call, followed by the actual finish dispatch.
The independent Scala debt assertion remains an explicit separate obligation. -/
theorem run_call {s : State} {x y : Machine 12} (b : Bool)
    (hinv : s.mode = .run ↔ x.done = false)
    (ht : Tick GalilDpCode.code (b && !x.done) x y) :
    let enabled := b && decide (s.mode = .run)
    Tick GalilDpCode.code enabled x y ∧
      ((finish s enabled y.done y.config.pc).mode = .run ↔ y.done = false) := by
  have hg : decide (s.mode = .run) = !x.done := by
    cases hd : x.done <;> simp_all
  dsimp
  rw [hg]
  refine ⟨ht,?_⟩
  rw [finish_run_iff,hinv]
  cases hd : x.done <;> cases b <;> simp only [hd,Bool.not_false,Bool.not_true,
    Bool.false_and,Bool.true_and] at ht ⊢
  all_goals cases ht <;> simp_all

inductive Calls : State → Machine 12 → List Bool → State → Machine 12 → Prop
  | nil (s : State) (x : Machine 12) : Calls s x [] s x
  | cons (s : State) (x y z : Machine 12) (b : Bool) (bs : List Bool) (t : State)
      (ht : Tick GalilDpCode.code (b && decide (s.mode = .run)) x y)
      (hr : Calls (finish s (b && decide (s.mode = .run)) y.done y.config.pc) y bs t z) :
      Calls s x (b :: bs) t z

theorem realize_calls {x y : Machine 12} {bs : List Bool}
    (hr : GalilScaffoldDpCost.GuardedRun GalilDpCode.code x bs y)
    (s : State) (hinv : s.mode = .run ↔ x.done = false) :
    ∃ t, Calls s x bs t y ∧ (t.mode = .run ↔ y.done = false) := by
  induction hr generalizing s with
  | nil => exact ⟨s,.nil _ _,hinv⟩
  | cons x y z b bs ht hr ih =>
    obtain ⟨hcall,hnext⟩ := run_call b hinv ht
    obtain ⟨t,htail,hend⟩ := ih _ hnext
    exact ⟨t,.cons s x y z b bs t hcall htail,hend⟩

/-- Once run mode has exited, residual calls in the current quantum are inert. -/
theorem calls_stopped {s t : State} {x y : Machine 12} {bs : List Bool}
    (hr : Calls s x bs t y) (hs : s.mode ≠ .run) : t = s ∧ y = x := by
  induction hr with
  | nil => exact ⟨rfl,rfl⟩
  | cons s x y z b bs t ht hr ih =>
    have hy : y = x := by
      simp only [hs,decide_false,Bool.and_false] at ht
      cases ht
      rfl
    subst y
    have hf : finish s (b && decide (s.mode = .run)) x.done x.config.pc = s := by
      simp [hs,finish]
    have hn : (finish s (b && decide (s.mode = .run)) x.done x.config.pc).mode ≠ .run := by
      rw [hf]; exact hs
    obtain ⟨hts,hzx⟩ := ih hn
    exact ⟨hts.trans hf,hzx⟩

/-- The bounded DP run reaches both done and a non-run Search mode.
This is the run-call phase; other outer-tick dispatches and debt are separate. -/
theorem quantum64_exits (w : List (Fin 3)) (lower : ℕ) (s : State) (hs : s.mode = .run) :
    ∃ t v, Calls s ⟨GalilScaffoldPreload.initial w lower,false⟩
      (List.replicate (64*(50*w.length+27)) true) t ⟨v,true⟩ ∧
      t.mode ≠ .run ∧ GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote v) := by
  obtain ⟨v,hv,hr⟩ := GalilScaffoldDpCost.quantum64_correct w lower
  obtain ⟨t,ht,hm⟩ := realize_calls hr s (by simp [hs])
  refine ⟨t,v,ht,?_,hv⟩
  simpa using hm

theorem finish_debt (s : State) (enabled done : Bool) (pc : ℕ) :
    (finish s enabled done pc).debt = s.debt := by
  unfold finish
  split <;> first | rfl | (split <;> first | rfl | (split <;> first | rfl | (split <;> rfl)))

/-- Calls with Scala's guarded nonnegative-debt assertion included. -/
inductive SafeCalls : State → Machine 12 → List Bool → State → Machine 12 → Prop
  | nil (s : State) (x : Machine 12) : SafeCalls s x [] s x
  | cons (s : State) (x y z : Machine 12) (b : Bool) (bs : List Bool) (t : State)
      (ht : Tick GalilDpCode.code (b && decide (s.mode = .run)) x y)
      (hsafe : b && decide (s.mode = .run) && y.done = true →
        GalilScaffoldCounter.negative s.debt ≠ true)
      (hr : SafeCalls (finish s (b && decide (s.mode = .run)) y.done y.config.pc) y bs t z) :
      SafeCalls s x (b :: bs) t z

theorem calls_safe {s t : State} {x y : Machine 12} {bs : List Bool}
    (hr : Calls s x bs t y) (hs : GalilScaffoldCounter.negative s.debt ≠ true) :
    SafeCalls s x bs t y ∧ t.debt = s.debt := by
  induction hr with
  | nil => exact ⟨.nil _ _,rfl⟩
  | cons s x y z b bs t ht hr ih =>
    have hn : GalilScaffoldCounter.negative
        (finish s (b && decide (s.mode = .run)) y.done y.config.pc).debt ≠ true := by
      rw [finish_debt]; exact hs
    obtain ⟨hsafe,hdebt⟩ := ih hn
    exact ⟨.cons s x y z b bs t ht (fun _ => hs) hsafe,hdebt.trans (finish_debt _ _ _ _)⟩

theorem quantum64_safe (w : List (Fin 3)) (lower : ℕ) (s : State)
    (hs : s.mode = .run) (hc : GalilScaffoldCounter.Canonical s.debt)
    (hn : 0 ≤ GalilScaffoldCounter.value s.debt) :
    ∃ t v, SafeCalls s ⟨GalilScaffoldPreload.initial w lower,false⟩
      (List.replicate (64*(50*w.length+27)) true) t ⟨v,true⟩ ∧
      t.mode ≠ .run ∧ GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote v) ∧
      t.debt = s.debt := by
  obtain ⟨t,v,hr,ht,hv⟩ := quantum64_exits w lower s hs
  obtain ⟨hsafe,hdebt⟩ := calls_safe hr (debt_guard s hc hn)
  exact ⟨t,v,hsafe,ht,hv,hdebt⟩

theorem calls_debt {s t : State} {x y : Machine 12} {bs : List Bool}
    (hr : Calls s x bs t y) : t.debt = s.debt := by
  induction hr with
  | nil => rfl
  | cons s x y z b bs t ht hr ih => exact ih.trans (finish_debt _ _ _ _)

def advance (a : Bool) (s : State) : State :=
  if a then {s with debt := GalilScaffoldCounter.dec s.debt} else s

/-- An outer tick entered in run mode performs 64 calls, then one outer advance.
No non-run dispatch is silently treated as an inert run tick. -/
inductive RunQuanta : State → Machine 12 → List Bool → State → Machine 12 → Prop
  | nil (s : State) (x : Machine 12) : RunQuanta s x [] s x
  | cons (s u t : State) (x y z : Machine 12) (a : Bool) (as : List Bool)
      (hm : s.mode = .run)
      (hq : Calls s x (List.replicate 64 true) u y)
      (hr : RunQuanta (advance a u) y as t z) : RunQuanta s x (a :: as) t z

inductive SafeQuanta : State → Machine 12 → List Bool → State → Machine 12 → Prop
  | nil (s : State) (x : Machine 12) : SafeQuanta s x [] s x
  | cons (s u t : State) (x y z : Machine 12) (a : Bool) (as : List Bool)
      (hm : s.mode = .run)
      (hq : SafeCalls s x (List.replicate 64 true) u y)
      (hr : SafeQuanta (advance a u) y as t z) : SafeQuanta s x (a :: as) t z

theorem quanta_safe {s t : State} {x y : Machine 12} {as : List Bool}
    (hr : RunQuanta s x as t y)
    (hc : GalilScaffoldCounter.Canonical s.debt)
    (hb : (as.count true : ℤ) ≤ GalilScaffoldCounter.value s.debt) :
    SafeQuanta s x as t y ∧ GalilScaffoldCounter.Canonical t.debt ∧
      GalilScaffoldCounter.value t.debt = GalilScaffoldCounter.value s.debt-as.count true := by
  induction hr with
  | nil => exact ⟨.nil _ _,hc,by simp⟩
  | cons s u t x y z a as hm hq hr ih =>
    have hn : 0 ≤ GalilScaffoldCounter.value s.debt := by omega
    obtain ⟨hqSafe,hd⟩ := calls_safe hq (debt_guard s hc hn)
    have huc : GalilScaffoldCounter.Canonical u.debt := hd ▸ hc
    have hac : GalilScaffoldCounter.Canonical (advance a u).debt := by
      cases a
      · exact huc
      · exact GalilScaffoldCounter.dec_canonical _ huc
    have hav : GalilScaffoldCounter.value (advance a u).debt =
        GalilScaffoldCounter.value s.debt-(if a then 1 else 0) := by
      cases a <;> simp [advance,GalilScaffoldCounter.dec_value,hd]
    have hab : (as.count true : ℤ) ≤ GalilScaffoldCounter.value (advance a u).debt := by
      cases a <;> simp_all <;> omega
    obtain ⟨ht,hct,hvt⟩ := ih hac hab
    refine ⟨.cons s u t x y z a as hm hqSafe ht,hct,?_⟩
    cases a <;> simp_all <;> omega

theorem guarded_split {x z : Machine 12} (as bs : List Bool)
    (hr : GalilScaffoldDpCost.GuardedRun GalilDpCode.code x (as++bs) z) :
    ∃ y, GalilScaffoldDpCost.GuardedRun GalilDpCode.code x as y ∧
      GalilScaffoldDpCost.GuardedRun GalilDpCode.code y bs z := by
  induction as generalizing x with
  | nil => exact ⟨x,.nil _,hr⟩
  | cons a as ih =>
    cases hr with
    | cons x y z a bs ht hr =>
      obtain ⟨u,hu,hz⟩ := ih hr
      exact ⟨u,.cons x y u a as ht hu,hz⟩

theorem guarded_stopped {x y : Machine 12} {bs : List Bool}
    (hr : GalilScaffoldDpCost.GuardedRun GalilDpCode.code x bs y)
    (hd : x.done = true) : y = x := by
  induction hr with
  | nil => rfl
  | cons x y z b bs ht hr ih =>
    have he : y = x := by
      simp only [hd,Bool.not_true,Bool.and_false] at ht
      cases ht
      rfl
    subst y
    exact ih hd

/-- Consume only the prefix of outer events needed to leave run mode. -/
theorem realize_quanta (as : List Bool) {x y : Machine 12}
    (hr : GalilScaffoldDpCost.GuardedRun GalilDpCode.code x
      (List.replicate (64*as.length) true) y) (hy : y.done = true)
    (s : State) (hi : s.mode = .run ↔ x.done = false) :
    ∃ used rest t, as = used++rest ∧ RunQuanta s x used t y ∧ t.mode ≠ .run := by
  induction as generalizing x s with
  | nil =>
    cases hr
    exact ⟨[],[],s,rfl,.nil _ _,by simp_all⟩
  | cons a as ih =>
    by_cases hm : s.mode = .run
    · have hsplit : GalilScaffoldDpCost.GuardedRun GalilDpCode.code x
          ((List.replicate 64 true)++List.replicate (64*as.length) true) y := by
        simpa [List.replicate_add,Nat.mul_add,Nat.add_comm] using hr
      obtain ⟨v,hfirst,hrest⟩ := guarded_split _ _ hsplit
      obtain ⟨u,hcalls,hu⟩ := realize_calls hfirst s hi
      have hai : (advance a u).mode = .run ↔ v.done = false := by
        cases a <;> simpa [advance] using hu
      obtain ⟨used,rest,t,he,ht,hmend⟩ := ih hrest (advance a u) hai
      exact ⟨a::used,rest,t,by simp [he],.cons s u t x v y a used hm hcalls ht,hmend⟩
    · have hd : x.done = true := by cases h : x.done <;> simp_all
      have he := guarded_stopped hr hd
      subst y
      exact ⟨[],a::as,s,rfl,.nil _ _,hm⟩

theorem dp_quanta_safe (w : List (Fin 3)) (lower : ℕ) (as : List Bool)
    (ha : 3186*w.length+1683 ≤ 64*as.length) (s : State) (hs : s.mode = .run)
    (hc : GalilScaffoldCounter.Canonical s.debt)
    (hb : (as.count true : ℤ) ≤ GalilScaffoldCounter.value s.debt) :
    ∃ used rest t v, as = used++rest ∧
      SafeQuanta s ⟨GalilScaffoldPreload.initial w lower,false⟩ used t ⟨v,true⟩ ∧
      t.mode ≠ .run ∧ GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote v) ∧
      GalilScaffoldCounter.value t.debt = GalilScaffoldCounter.value s.debt-used.count true ∧
      GalilScaffoldCounter.Canonical t.debt ∧ 0 ≤ GalilScaffoldCounter.value t.debt := by
  obtain ⟨v,hv,hscheduled⟩ := GalilScaffoldDpCost.scheduled_correct w lower
  have hr := GalilScaffoldDpCost.guard_run
    (hscheduled (List.replicate (64*as.length) true) (by simpa using ha))
  obtain ⟨used,rest,t,he,ht,hm⟩ := realize_quanta as hr rfl s (by simp [hs])
  have hbudget : (used.count true : ℤ) ≤ GalilScaffoldCounter.value s.debt := by
    rw [he,List.count_append] at hb
    omega
  obtain ⟨htsafe,hct,hdebt⟩ := quanta_safe ht hc hbudget
  exact ⟨used,rest,t,v,he,htsafe,hm,hv,hdebt,hct,by omega⟩

theorem calibrated_quanta_safe (w : List (Fin 3)) (lower span : ℕ) (as : List Bool)
    (hw : w.length ≤ span+1) (ha : as.length = GalilScaffoldTimingCost.runBudget span)
    (s : State) (hs : s.mode = .run) (hc : GalilScaffoldCounter.Canonical s.debt)
    (hb : (as.count true : ℤ) ≤ GalilScaffoldCounter.value s.debt) :
    ∃ used rest t v, as = used++rest ∧
      SafeQuanta s ⟨GalilScaffoldPreload.initial w lower,false⟩ used t ⟨v,true⟩ ∧
      t.mode ≠ .run ∧ GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote v) ∧
      GalilScaffoldCounter.value t.debt = GalilScaffoldCounter.value s.debt-used.count true ∧
      GalilScaffoldCounter.Canonical t.debt ∧ 0 ≤ GalilScaffoldCounter.value t.debt := by
  apply dp_quanta_safe w lower as ?_ s hs hc hb
  have h := GalilScaffoldTimingCost.runBudget_sufficient span
  rw [ha]
  omega

/-- On double entry the old span has moved into work. -/
def stageSpan (s : State) : GalilScaffoldCounter.Counter :=
  if s.mode = .double then s.work else s.span

theorem finish_frame (s : State) (b done : Bool) (pc : ℕ) :
    let t := finish s (b && decide (s.mode = .run)) done pc
    t.finalStage = s.finalStage ∧ stageSpan t = stageSpan s := by
  by_cases hm : s.mode = .run
  · cases b <;> cases done <;> by_cases hp : pc = 346 <;>
      cases hf : s.finalStage <;> cases hz : GalilScaffoldCounter.zero s.debt <;>
      simp [finish,stageSpan,hm,hp,hf,hz]
  · simp [finish,hm]

theorem safe_calls_frame {s t : State} {x y : Machine 12} {bs : List Bool}
    (hr : SafeCalls s x bs t y) :
    t.finalStage = s.finalStage ∧ stageSpan t = stageSpan s := by
  induction hr with
  | nil => exact ⟨rfl,rfl⟩
  | cons s x y z b bs t ht hsafe hr ih =>
    have h := finish_frame s b y.done y.config.pc
    exact ⟨ih.1.trans h.1,ih.2.trans h.2⟩

theorem safe_quanta_frame {s t : State} {x y : Machine 12} {as : List Bool}
    (hr : SafeQuanta s x as t y) :
    t.finalStage = s.finalStage ∧ stageSpan t = stageSpan s := by
  induction hr with
  | nil => exact ⟨rfl,rfl⟩
  | cons s u t x y z a as hm hq hr ih =>
    have h := safe_calls_frame hq
    have hf : (advance a u).finalStage = u.finalStage := by cases a <;> rfl
    have hs : stageSpan (advance a u) = stageSpan u := by cases a <;> rfl
    exact ⟨ih.1.trans (hf.trans h.1),ih.2.trans (hs.trans h.2)⟩

theorem double_work_of_quanta {s t : State} {x y : Machine 12} {as : List Bool}
    (hr : SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode = .double) :
    t.work = s.span := by
  simpa [stageSpan,hs,ht] using (safe_quanta_frame hr).2

def DoubleReset (s : State) : Prop :=
  s.mode = .double → s.span = GalilScaffoldCounter.reset ∧ s.quarter = 0

theorem finish_double_reset (s : State) (b done : Bool) (pc : ℕ) (hs : DoubleReset s) :
    DoubleReset (finish s (b && decide (s.mode = .run)) done pc) := by
  by_cases hm : s.mode = .run
  · cases b <;> cases done <;> by_cases hp : pc = 346 <;>
      cases hf : s.finalStage <;> cases hz : GalilScaffoldCounter.zero s.debt <;>
      simp [DoubleReset,finish,hm,hp,hf,hz]
  · simpa [finish,hm] using hs

theorem safe_calls_double_reset {s t : State} {x y : Machine 12} {bs : List Bool}
    (hr : SafeCalls s x bs t y) (hs : DoubleReset s) : DoubleReset t := by
  induction hr with
  | nil => exact hs
  | cons s x y z b bs t ht hsafe hr ih => exact ih (finish_double_reset s b y.done y.config.pc hs)

theorem safe_quanta_double_reset {s t : State} {x y : Machine 12} {as : List Bool}
    (hr : SafeQuanta s x as t y) (hs : DoubleReset s) : DoubleReset t := by
  induction hr with
  | nil => exact hs
  | cons s u t x y z a as hm hq hr ih =>
    have h := safe_calls_double_reset hq hs
    apply ih
    cases a <;> exact h

theorem double_reset_of_quanta {s t : State} {x y : Machine 12} {as : List Bool}
    (hr : SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode = .double) :
    t.span = GalilScaffoldCounter.reset ∧ t.quarter = 0 := by
  exact safe_quanta_double_reset hr (by simp [DoubleReset,hs]) ht

def ExitMode (s : State) : Prop :=
  s.mode = .found ∨ s.mode = .missed ∨ s.mode = .wait ∨ s.mode = .double

theorem finish_exit (s : State) (b done : Bool) (pc : ℕ)
    (hs : s.mode = .run ∨ ExitMode s) :
    (finish s (b && decide (s.mode = .run)) done pc).mode = .run ∨
      ExitMode (finish s (b && decide (s.mode = .run)) done pc) := by
  by_cases hm : s.mode = .run
  · cases b <;> cases done <;> by_cases hp : pc = 346 <;>
      cases hf : s.finalStage <;> cases hz : GalilScaffoldCounter.zero s.debt <;>
      simp [finish,ExitMode,hm,hp,hf,hz]
  · simpa [finish,hm] using hs

theorem safe_calls_exit {s t : State} {x y : Machine 12} {bs : List Bool}
    (hr : SafeCalls s x bs t y) (hs : s.mode = .run ∨ ExitMode s) :
    t.mode = .run ∨ ExitMode t := by
  induction hr with
  | nil => exact hs
  | cons s x y z b bs t ht hsafe hr ih => exact ih (finish_exit s b y.done y.config.pc hs)

theorem safe_quanta_exit {s t : State} {x y : Machine 12} {as : List Bool}
    (hr : SafeQuanta s x as t y) (hs : s.mode = .run ∨ ExitMode s) :
    t.mode = .run ∨ ExitMode t := by
  induction hr with
  | nil => exact hs
  | cons s u t x y z a as hm hq hr ih =>
    have h := safe_calls_exit hq hs
    apply ih
    cases a <;> exact h

theorem quanta_exit_mode {s t : State} {x y : Machine 12} {as : List Bool}
    (hr : SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode ≠ .run) : ExitMode t :=
  (safe_quanta_exit hr (Or.inl hs)).resolve_left ht

def TerminalLink (s : State) (x : Machine 12) : Prop :=
  s.mode = .run ∨ ((s.mode = .found ↔ x.config.pc = 346) ∧
    (s.mode = .missed ↔ x.config.pc ≠ 346 ∧ s.finalStage = true))

theorem call_terminal_link {s : State} {x y : Machine 12} (b : Bool)
    (hl : TerminalLink s x)
    (ht : Tick GalilDpCode.code (b && decide (s.mode = .run)) x y) :
    TerminalLink (finish s (b && decide (s.mode = .run)) y.done y.config.pc) y := by
  by_cases hm : s.mode = .run
  · cases b <;> cases hd : y.done <;> by_cases hp : y.config.pc = 346 <;>
      cases hf : s.finalStage <;> cases hz : GalilScaffoldCounter.zero s.debt <;>
      simp [TerminalLink,finish,hm,hd,hp,hf,hz]
  · have he : y = x := by
      simp only [hm,decide_false,Bool.and_false] at ht
      cases ht
      rfl
    subst y
    simpa [finish,hm] using hl

theorem safe_calls_terminal_link {s t : State} {x y : Machine 12} {bs : List Bool}
    (hr : SafeCalls s x bs t y) (hl : TerminalLink s x) : TerminalLink t y := by
  induction hr with
  | nil => exact hl
  | cons s x y z b bs t ht hsafe hr ih => exact ih (call_terminal_link b hl ht)

theorem safe_quanta_terminal_link {s t : State} {x y : Machine 12} {as : List Bool}
    (hr : SafeQuanta s x as t y) (hl : TerminalLink s x) : TerminalLink t y := by
  induction hr with
  | nil => exact hl
  | cons s u t x y z a as hm hq hr ih =>
    have h := safe_calls_terminal_link hq hl
    apply ih
    cases a <;> exact h

theorem quanta_found_result {s t : State} {x y : Machine 12} {as : List Bool}
    {w : List (Fin 3)} {lower : ℕ}
    (hr : SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode ≠ .run)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config)) :
    t.mode = .found ↔ ∃ k, 0 ≤ k ∧ GalilDpCorrect.Candidate w lower k := by
  have hl := (safe_quanta_terminal_link hr (Or.inl hs)).resolve_left ht
  have h := GalilScaffoldSearchFinish.result_found hv t
  rw [GalilScaffoldSearchFinish.found_iff] at h
  exact hl.1.trans h

theorem quanta_missed_result {s t : State} {x y : Machine 12} {as : List Bool}
    {w : List (Fin 3)} {lower : ℕ}
    (hr : SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode ≠ .run)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config)) :
    t.mode = .missed ↔ (¬ ∃ k, 0 ≤ k ∧ GalilDpCorrect.Candidate w lower k) ∧ s.finalStage = true := by
  have hl := (safe_quanta_terminal_link hr (Or.inl hs)).resolve_left ht
  have hpc := hl.1.symm.trans (quanta_found_result hr hs ht hv)
  simpa only [ne_eq,hpc,(safe_quanta_frame hr).1] using hl.2

theorem quanta_suffix_result {s t : State} {x y : Machine 12} {as : List Bool}
    {w : List (Fin 3)} {lower : ℕ}
    (hr : SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode ≠ .run)
    (hv : GalilDpCorrect.Result w.reverse lower 0 (GalilScaffoldProgram.denote y.config)) :
    GalilDpSuffix.Result w lower (GalilScaffoldProgram.denote y.config) ∧
      (t.mode = .found ↔ ∃ k, GalilDpSuffix.Candidate w lower k) ∧
      (t.mode = .missed ↔ (¬ ∃ k, GalilDpSuffix.Candidate w lower k) ∧ s.finalStage = true) := by
  refine ⟨GalilDpSuffix.result_of_reverse hv,?_,?_⟩
  · simpa [GalilDpSuffix.candidate_iff] using quanta_found_result hr hs ht hv
  · simpa [GalilDpSuffix.candidate_iff] using quanta_missed_result hr hs ht hv

theorem quanta_window_result {s t : State} {x y : Machine 12} {as : List Bool}
    {w : List (Fin 3)} {span lower : ℕ}
    (hr : SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode ≠ .run)
    (hv : GalilDpCorrect.Result (w.reverse.take (span+1)) lower 0 (GalilScaffoldProgram.denote y.config)) :
    let v := w.drop (w.length-(span+1))
    GalilDpSuffix.Result v lower (GalilScaffoldProgram.denote y.config) ∧
      (t.mode = .found ↔ ∃ k, GalilDpSuffix.Candidate v lower k) ∧
      (t.mode = .missed ↔ (¬ ∃ k, GalilDpSuffix.Candidate v lower k) ∧ s.finalStage = true) := by
  apply quanta_suffix_result hr hs ht
  simpa only [List.take_reverse] using hv

#print axioms quanta_window_result
#print axioms quanta_missed_result
#print axioms quanta_found_result
#print axioms quanta_exit_mode
#print axioms double_reset_of_quanta
#print axioms double_work_of_quanta
#print axioms safe_quanta_frame
#print axioms calibrated_quanta_safe
#print axioms dp_quanta_safe
#print axioms realize_quanta
#print axioms quanta_safe
#print axioms quantum64_safe
#print axioms quantum64_exits
#print axioms calls_stopped
#print axioms realize_calls
#print axioms run_call
end PalPeg.GalilScaffoldSearchRun
