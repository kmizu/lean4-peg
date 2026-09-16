import PalPeg.TextFeedRefine

/-! Amortized work including a suspended scan's physical progress. -/
set_option autoImplicit false

namespace PalPeg.TextFeedRefine

def workScale (rate : ℕ) : ℕ := 8 * rate + 22

def workScore {k : ℕ} (rate : ℕ) (M : TextFeed.Machine' k) : Phase → ℕ
  | .scan N => workScale rate * Phi rate M.st + N
  | _ => workScale rate * Phi rate M.st

/-- Retiring a scan pays for every physical action and the retirement call.
The progress component can therefore be discarded without losing work. -/
theorem retirement_work {k : ℕ} {e : TextFeedControl.Env k}
    {v Text : List (Fin k)} {rate p₁ rem n : ℕ} {M : TextFeed.Machine' k}
    (hk : 0 < rate) (hp : 0 < p₁) (hmb : e.mark ≠ e.blank)
    (hend : e.endSym ∉ v) (hn : n ≤ Text.length)
    (hrd : M.st.q ≠ v.length → M.st.pos + M.st.q < M.m)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem n M) :
    workScore rate M (.scan (cost e rate M)) + 1 ≤
      workScore rate (TextFeed.scanOne' e.blank e.endSym e.mark v rate p₁ rem Text M) .fill := by
  have hc := TextFeed.scanOne'_cost hk hmb hend hn hrd hf
  have hl := phi_step_lt (v := v) (T := Text) (r := rem) hk hp M.st
  simp only [TextFeed.scanOne', TextFeed.stepCost'] at hc
  simp only [workScore, TextFeed.scanOne'_st, cost, workScale]
  have hd : Phi rate (scanStep v rate p₁ rem Text M.st) - Phi rate M.st ≥ 1 := by omega
  have he : Phi rate (scanStep v rate p₁ rem Text M.st) =
      Phi rate M.st + (Phi rate (scanStep v rate p₁ rem Text M.st) - Phi rate M.st) := by omega
  nlinarith

/-- Every worker call preserves accumulated work, including supply/wait calls. -/
theorem advance_work_mono {k : ℕ} {e : TextFeedControl.Env k}
    {v Text : List (Fin k)} {rate p₁ rem n : ℕ} {M : TextFeed.Machine' k} {ph : Phase}
    (hk : 0 < rate) (hp : 0 < p₁) (hmb : e.mark ≠ e.blank)
    (hend : e.endSym ∉ v) (hn : n ≤ Text.length)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem n M)
    (hw : pending e v rate M ph) :
    workScore rate M ph ≤
      workScore rate (advance e v Text rate p₁ rem n M ph).1
        (advance e v Text rate p₁ rem n M ph).2 := by
  classical
  cases ph with
  | loop => exact Nat.le_refl _
  | fill =>
    simp only [advance]
    split_ifs <;> simp [workScore, TextFeed.fillIf'_st]
  | gate =>
    simp only [advance]
    split_ifs <;> simp [workScore]
  | scan N =>
    obtain ⟨hle, hrd⟩ := hw
    simp only [advance]
    split_ifs with hlt
    · simp [workScore]
    · have he : N = cost e rate M := by omega
      subst N
      exact Nat.le_trans (Nat.le_succ _) (retirement_work hk hp hmb hend hn hrd hf)

/-- Once in a scan, every call is productive, even its final retirement. -/
theorem scan_advance_work {k : ℕ} {e : TextFeedControl.Env k}
    {v Text : List (Fin k)} {rate p₁ rem n N : ℕ} {M : TextFeed.Machine' k}
    (hk : 0 < rate) (hp : 0 < p₁) (hmb : e.mark ≠ e.blank)
    (hend : e.endSym ∉ v) (hn : n ≤ Text.length)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem n M)
    (hw : pending e v rate M (.scan N)) :
    workScore rate M (.scan N) + 1 ≤
      workScore rate (advance e v Text rate p₁ rem n M (.scan N)).1
        (advance e v Text rate p₁ rem n M (.scan N)).2 := by
  classical
  obtain ⟨hle, hrd⟩ := hw
  simp only [advance]
  split_ifs with hlt
  · simp [workScore, Nat.add_assoc]
  · have he : N = cost e rate M := by omega
    subst N
    exact retirement_work hk hp hmb hend hn hrd hf

section Service
open TextFeedControl TextFeedCycleModel GSTapes GSProg

variable {k : ℕ} {e : Env k} {v Text : List (Fin k)} {rate p₁ rem n : ℕ}

/-- The ghost state needed for service estimates, independent of tape encoding. -/
def WorkInv (e : Env k) (v Text : List (Fin k)) (rate p₁ rem n : ℕ)
    (z : TextFeed.Machine' k × Phase) : Prop :=
  TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem n z.1 ∧
    pending e v rate z.1 z.2

theorem advance_workInv (hk : 0 < rate) (hmb : e.mark ≠ e.blank)
    (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hn : n ≤ Text.length)
    {M : TextFeed.Machine' k} {ph : Phase}
    (h : WorkInv e v Text rate p₁ rem n (M, ph)) :
    WorkInv e v Text rate p₁ rem n (advance e v Text rate p₁ rem n M ph) := by
  classical
  obtain ⟨hf, hw⟩ := h
  have hEnter (hg : GateEnabled e (TS M.ts)) :
      WorkInv e v Text rate p₁ rem n (M, .scan 1) :=
    ⟨hf, cost_pos hk hmb hstart hf, scan_ready hend hblank hn hf hg⟩
  cases ph with
  | loop => exact ⟨hf, trivial⟩
  | fill =>
    simp only [advance]
    split_ifs with ht
    · exact ⟨TextFeed.fillIf'_feedInv hmb hn hf, trivial⟩
    · exact hEnter (Or.inr ht)
  | gate =>
    simp only [advance]
    split_ifs with hg
    · exact hEnter hg
    · exact ⟨hf, trivial⟩
  | scan N =>
    obtain ⟨hle, hrd⟩ := hw
    simp only [advance]
    split_ifs with hlt
    · exact ⟨hf, by change N + 1 ≤ cost e rate M ∧ _; exact ⟨by omega, hrd⟩⟩
    · exact ⟨TextFeed.scanOne'_feedInv hk hmb hv hend hn hrd hf, trivial⟩

theorem modelRun_succ (N : ℕ) (M : TextFeed.Machine' k) (ph : Phase) :
    modelRun e v Text rate p₁ rem n (N + 1) M ph =
      modelRun e v Text rate p₁ rem n N (advance e v Text rate p₁ rem n M ph).1
        (advance e v Text rate p₁ rem n M ph).2 := by
  simp only [modelRun, Function.iterate_succ_apply]

theorem modelRun_add (A B : ℕ) (M : TextFeed.Machine' k) (ph : Phase) :
    modelRun e v Text rate p₁ rem n (A + B) M ph =
      modelRun e v Text rate p₁ rem n B (modelRun e v Text rate p₁ rem n A M ph).1
        (modelRun e v Text rate p₁ rem n A M ph).2 := by
  rw [Nat.add_comm A B]
  simp only [modelRun, Function.iterate_add_apply, Prod.mk.eta]

theorem modelRun_workInv (hk : 0 < rate) (hmb : e.mark ≠ e.blank)
    (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hn : n ≤ Text.length) (N : ℕ)
    {M : TextFeed.Machine' k} {ph : Phase}
    (h : WorkInv e v Text rate p₁ rem n (M, ph)) :
    WorkInv e v Text rate p₁ rem n (modelRun e v Text rate p₁ rem n N M ph) := by
  induction N generalizing M ph with
  | zero => exact h
  | succ N ih =>
    rw [modelRun_succ]
    exact ih (advance_workInv hk hmb hv hend hstart hblank hn h)

theorem modelRun_work_mono (hk : 0 < rate) (hp : 0 < p₁) (hmb : e.mark ≠ e.blank)
    (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hn : n ≤ Text.length) (N : ℕ)
    {M : TextFeed.Machine' k} {ph : Phase}
    (h : WorkInv e v Text rate p₁ rem n (M, ph)) :
    workScore rate M ph ≤ workScore rate (modelRun e v Text rate p₁ rem n N M ph).1
      (modelRun e v Text rate p₁ rem n N M ph).2 := by
  induction N generalizing M ph with
  | zero => exact Nat.le_refl _
  | succ N ih =>
    rw [modelRun_succ]
    exact (advance_work_mono hk hp hmb hend hn h.1 h.2).trans
      (ih (advance_workInv hk hmb hv hend hstart hblank hn h))

/-- Supply needs at most two calls to start a scan when work is enabled. -/
theorem fill_productive (hmb : e.mark ≠ e.blank) (hend : e.endSym ∉ v)
    (hblank : e.blank ∉ Text) (hn : n ≤ Text.length) {M : TextFeed.Machine' k}
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem n M)
    (he : Enabled v n M.st) :
    ∃ j, 1 ≤ j ∧ j ≤ 2 ∧ workScore rate M .fill + 1 ≤
      workScore rate (modelRun e v Text rate p₁ rem n j M .fill).1
        (modelRun e v Text rate p₁ rem n j M .fill).2 := by
  classical
  by_cases ht : (TS M.ts tT).focus = e.blank
  · have hg := (filled_enabled hmb hend hblank hn hf).mpr he
    refine ⟨2, by omega, by omega, ?_⟩
    simp only [show 2 = 0 + 1 + 1 from rfl, modelRun_succ, advance, if_pos ht, if_pos hg]
    simp [modelRun, workScore, TextFeed.fillIf'_st]
  · refine ⟨1, by omega, by omega, ?_⟩
    simp only [modelRun, Function.iterate_one, advance, if_neg ht]
    exact Nat.le_refl _

/-- Even a gate interrupted by an arrival reaches productive work in three
calls. This bound does not assume gate-enabled iff numeric-enabled. -/
theorem enabled_productive (hk : 0 < rate) (hp : 0 < p₁) (hmb : e.mark ≠ e.blank)
    (hend : e.endSym ∉ v) (hblank : e.blank ∉ Text) (hn : n ≤ Text.length)
    {M : TextFeed.Machine' k} {ph : Phase}
    (h : WorkInv e v Text rate p₁ rem n (M, ph)) (he : Enabled v n M.st) :
    ∃ j, 1 ≤ j ∧ j ≤ 3 ∧ workScore rate M ph + 1 ≤
      workScore rate (modelRun e v Text rate p₁ rem n j M ph).1
        (modelRun e v Text rate p₁ rem n j M ph).2 := by
  classical
  cases ph with
  | fill =>
    obtain ⟨j, hj, hj2, hs⟩ := fill_productive hmb hend hblank hn h.1 he
    exact ⟨j, hj, by omega, hs⟩
  | loop =>
    obtain ⟨j, hj, hj2, hs⟩ := fill_productive hmb hend hblank hn h.1 he
    refine ⟨j + 1, by omega, by omega, ?_⟩
    simpa only [modelRun_succ, advance, workScore] using hs
  | gate =>
    by_cases hg : GateEnabled e (TS M.ts)
    · refine ⟨1, by omega, by omega, ?_⟩
      simp only [modelRun, Function.iterate_one, advance, if_pos hg]
      exact Nat.le_refl _
    · obtain ⟨j, hj, hj2, hs⟩ := fill_productive hmb hend hblank hn h.1 he
      refine ⟨j + 1, by omega, by omega, ?_⟩
      simpa only [modelRun_succ, advance, if_neg hg, workScore] using hs
  | scan N =>
    refine ⟨1, by omega, by omega, ?_⟩
    simpa only [modelRun, Function.iterate_one, Prod.mk.eta] using
      scan_advance_work hk hp hmb hend hn h.1 h.2

theorem enabled_three_work (hk : 0 < rate) (hp : 0 < p₁) (hmb : e.mark ≠ e.blank)
    (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hn : n ≤ Text.length)
    {M : TextFeed.Machine' k} {ph : Phase}
    (h : WorkInv e v Text rate p₁ rem n (M, ph)) (he : Enabled v n M.st) :
    workScore rate M ph + 1 ≤ workScore rate (modelRun e v Text rate p₁ rem n 3 M ph).1
      (modelRun e v Text rate p₁ rem n 3 M ph).2 := by
  obtain ⟨j, _, hj3, hs⟩ := enabled_productive hk hp hmb hend hblank hn h he
  have hi := modelRun_workInv hk hmb hv hend hstart hblank hn j h
  have hm := modelRun_work_mono hk hp hmb hv hend hstart hblank hn (3 - j) hi
  have heq : 3 = j + (3 - j) := by omega
  rw [heq, modelRun_add]
  exact hs.trans hm

/-- Credit relative to the latest possible matching prefix. -/
def workCredit (v : List (Fin k)) (rate : ℕ) (z : TextFeed.Machine' k × Phase) : ℕ :=
  workScore rate z.1 z.2 + workScale rate * (rate * v.length)

theorem disabled_credit {M : TextFeed.Machine' k} {ph : Phase}
    (h : WorkInv e v Text rate p₁ rem n (M, ph)) (he : ¬ Enabled v n M.st) :
    workScale rate * ((rate + 1) * n) ≤ workCredit v rate (M, ph) := by
  have hq := h.1.qle
  have hn : n ≤ M.st.pos + M.st.q := by
    unfold Enabled at he
    omega
  have hphi : (rate + 1) * n ≤ Phi rate M.st + rate * v.length := by
    have ha := Nat.mul_le_mul_left (rate + 1) hn
    have hb := Nat.mul_le_mul_left rate hq
    simp only [Phi]
    nlinarith
  have hs := Nat.mul_le_mul_left (workScale rate) hphi
  cases ph <;> simp only [workCredit, workScore, Nat.mul_add] at * <;> omega

/-- In any fixed arrival window, every three calls either earn a unit of
credit or have already reached that window's input frontier. -/
theorem work_service_blocks (hk : 0 < rate) (hp : 0 < p₁) (hmb : e.mark ≠ e.blank)
    (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hn : n ≤ Text.length) (B : ℕ)
    {M : TextFeed.Machine' k} {ph : Phase}
    (h : WorkInv e v Text rate p₁ rem n (M, ph)) :
    min (workScale rate * ((rate + 1) * n)) (workCredit v rate (M, ph) + B) ≤
      workCredit v rate (modelRun e v Text rate p₁ rem n (3 * B) M ph) := by
  induction B generalizing M ph with
  | zero =>
    simpa only [Nat.mul_zero, modelRun, Function.iterate_zero_apply, Nat.add_zero] using
      (Nat.min_le_right (workScale rate * ((rate + 1) * n)) (workCredit v rate (M, ph)))
  | succ B ih =>
    by_cases he : Enabled v n M.st
    · have hs := enabled_three_work hk hp hmb hv hend hstart hblank hn h he
      have hi := modelRun_workInv hk hmb hv hend hstart hblank hn 3 h
      have hb := ih (M := (modelRun e v Text rate p₁ rem n 3 M ph).1)
        (ph := (modelRun e v Text rate p₁ rem n 3 M ph).2) hi
      have heq : 3 * (B + 1) = 3 + 3 * B := by omega
      rw [heq, modelRun_add]
      change min _ _ ≤ workCredit v rate
        (modelRun e v Text rate p₁ rem n (3 * B)
          (modelRun e v Text rate p₁ rem n 3 M ph).1
          (modelRun e v Text rate p₁ rem n 3 M ph).2)
      apply le_trans _ hb
      apply min_le_min (Nat.le_refl _)
      change workScore rate M ph + workScale rate * (rate * v.length) + (B + 1) ≤
        workScore rate (modelRun e v Text rate p₁ rem n 3 M ph).1
          (modelRun e v Text rate p₁ rem n 3 M ph).2 + workScale rate * (rate * v.length) + B
      omega
    · have hd := disabled_credit h he
      have hm := modelRun_work_mono hk hp hmb hv hend hstart hblank hn (3 * (B + 1)) h
      exact (Nat.min_le_left _ _).trans (hd.trans (by
        simp only [workCredit]
        omega))

/-- A worker window of any length supplies floor(N/3) units, up to its
input frontier. The bound is independent of the current scan cost. -/
theorem work_service (hk : 0 < rate) (hp : 0 < p₁) (hmb : e.mark ≠ e.blank)
    (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hn : n ≤ Text.length) (N : ℕ)
    {M : TextFeed.Machine' k} {ph : Phase}
    (h : WorkInv e v Text rate p₁ rem n (M, ph)) :
    min (workScale rate * ((rate + 1) * n)) (workCredit v rate (M, ph) + N / 3) ≤
      workCredit v rate (modelRun e v Text rate p₁ rem n N M ph) := by
  have hb := work_service_blocks hk hp hmb hv hend hstart hblank hn (N / 3) h
  have hi := modelRun_workInv hk hmb hv hend hstart hblank hn (3 * (N / 3)) h
  have hm := modelRun_work_mono hk hp hmb hv hend hstart hblank hn (N % 3) hi
  have heq : N = 3 * (N / 3) + N % 3 := by omega
  conv_rhs => rw [heq, modelRun_add]
  apply hb.trans
  simp only [workCredit]
  exact Nat.add_le_add_right hm _

/-- Number of worker calls per arrival sufficient to maintain the frontier.
It depends only on the fixed GS rate, not on the pattern or text lengths. -/
def workRate (rate : ℕ) : ℕ := 3 * (workScale rate * (rate + 1))

@[simp] theorem workCredit_arrive (v : List (Fin k)) (rate : ℕ) (M : TextFeed.Machine' k)
    (ph : Phase) (a : Fin k) :
    workCredit v rate (TextFeed.arrive' e.blank e.mark a M, ph) = workCredit v rate (M, ph) := by
  cases ph <;> rfl

theorem arrive_workInv (hmb : e.mark ≠ e.blank) (hn : n < Text.length)
    {M : TextFeed.Machine' k} {ph : Phase} {a : Fin k} (ha : Text[n]? = some a)
    (h : WorkInv e v Text rate p₁ rem n (M, ph)) :
    WorkInv e v Text rate p₁ rem (n + 1) (TextFeed.arrive' e.blank e.mark a M, ph) := by
  exact ⟨TextFeed.arrive'_feedInv hmb hn ha h.1, (pending_arrive e v rate M ph a).symm ▸ h.2⟩

/-- The frontier credit invariant survives an actual arrival and its
fixed-size worker window, even when the arrival interrupts a scan. -/
theorem frame_work_credit (hk : 0 < rate) (hp : 0 < p₁) (hmb : e.mark ≠ e.blank)
    (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hn : n < Text.length) {R : ℕ} (hR : workRate rate ≤ R)
    {M : TextFeed.Machine' k} {ph : Phase} {a : Fin k} (ha : Text[n]? = some a)
    (h : WorkInv e v Text rate p₁ rem n (M, ph))
    (hc : workScale rate * ((rate + 1) * n) ≤ workCredit v rate (M, ph)) :
    let z := modelRun e v Text rate p₁ rem (n + 1) R (TextFeed.arrive' e.blank e.mark a M) ph
    WorkInv e v Text rate p₁ rem (n + 1) z ∧
      workScale rate * ((rate + 1) * (n + 1)) ≤ workCredit v rate z := by
  have haI := arrive_workInv hmb hn ha h
  have hn' : n + 1 ≤ Text.length := by omega
  refine ⟨modelRun_workInv hk hmb hv hend hstart hblank hn' R haI, ?_⟩
  have hs := work_service hk hp hmb hv hend hstart hblank hn' R haI
  apply le_trans _ hs
  apply le_min (Nat.le_refl _)
  rw [workCredit_arrive]
  have hr : workScale rate * (rate + 1) ≤ R / 3 := by
    unfold workRate at hR
    omega
  have heq : workScale rate * ((rate + 1) * (n + 1)) =
      workScale rate * ((rate + 1) * n) + workScale rate * (rate + 1) := by ring
  omega

/-- Proof-only complete input stream execution; the implemented machine
obtains the same updates from its input register and finite controller. -/
noncomputable def onlineWork (e : Env k) (v Text : List (Fin k)) (R rate p₁ rem : ℕ)
    (M₀ : TextFeed.Machine' k) (ph₀ : Phase) : ℕ → TextFeed.Machine' k × Phase
  | 0 => (M₀, ph₀)
  | n + 1 =>
    let z := onlineWork e v Text R rate p₁ rem M₀ ph₀ n
    modelRun e v Text rate p₁ rem (n + 1) R
      (TextFeed.arrive' e.blank e.mark (Text[n]?.getD e.blank) z.1) z.2

/-- Uniform service throughout an arbitrary finite input, with no bound
on the number of arrivals or the duration of any single GS scan. -/
theorem onlineWork_credit (hk : 0 < rate) (hp : 0 < p₁) (hmb : e.mark ≠ e.blank)
    (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) {R : ℕ} (hR : workRate rate ≤ R)
    {M₀ : TextFeed.Machine' k} {ph₀ : Phase}
    (h₀ : WorkInv e v Text rate p₁ rem 0 (M₀, ph₀)) (n : ℕ) (hn : n ≤ Text.length) :
    let z := onlineWork e v Text R rate p₁ rem M₀ ph₀ n
    WorkInv e v Text rate p₁ rem n z ∧
      workScale rate * ((rate + 1) * n) ≤ workCredit v rate z := by
  induction n with
  | zero => exact ⟨h₀, by simp⟩
  | succ n ih =>
    obtain ⟨hi, hc⟩ := ih (by omega)
    have hn' : n < Text.length := by omega
    have ha : Text[n]? = some (Text[n]?.getD e.blank) := by
      simp only [List.getElem?_eq_getElem hn', Option.getD_some]
    exact frame_work_credit hk hp hmb hv hend hstart hblank hn' hR ha hi hc

/-- info: 'PalPeg.TextFeedRefine.work_service' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms work_service

/-- info: 'PalPeg.TextFeedRefine.onlineWork_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms onlineWork_credit

end Service
end PalPeg.TextFeedRefine
