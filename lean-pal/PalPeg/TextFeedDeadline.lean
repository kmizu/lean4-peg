import PalPeg.TextFeedWork

/-! Deadline consequences of the finite feeder's uniform service estimate. -/
set_option autoImplicit false

namespace PalPeg.TextFeedRefine
open TextFeedControl

variable {k : ℕ} {e : Env k} {v Text : List (Fin k)} {rate p₁ rem n : ℕ}

def Hit (v : List (Fin k)) (i : ℕ) (M : TextFeed.Machine' k) : Prop :=
  M.st.pos = i ∧ M.st.q = v.length

/-- At an occurrence deadline, frontier credit rules out an unreported
snapshot at or before the occurrence. A suspended scan is strictly short
of its successor's potential, because retirement itself costs one call. -/
theorem credit_forces_hit (hk : 0 < rate) (hp : 0 < p₁) (hmb : e.mark ≠ e.blank)
    (hend : e.endSym ∉ v) (hn : n ≤ Text.length) (hK : KSimple v rate p₁ rem)
    {M : TextFeed.Machine' k} {ph : Phase} {i : ℕ}
    (h : WorkInv e v Text rate p₁ rem n (M, ph)) (hi : ScanInv v Text M.st)
    (hocc : OccAt v Text i) (hpos : M.st.pos ≤ i) (hd : i + v.length = n)
    (hc : workScale rate * ((rate + 1) * n) ≤ workCredit v rate (M, ph)) :
    Hit v i M := by
  have hC : 0 < workScale rate := by unfold workScale; omega
  by_contra hno
  have hnq : M.st.q = v.length → M.st.pos ≠ i := by
    intro hq he
    exact hno ⟨he, hq⟩
  have hq := hi.2
  have hbound (st : ScanState) (hp' : st.pos ≤ i) (hq' : st.q ≤ v.length) :
      Phi rate st + rate * v.length ≤ (rate + 1) * n := by
    have hh := Nat.mul_le_mul_left (rate + 1) hp'
    rw [← hd]
    simp only [Phi]
    nlinarith
  have hplain : workCredit v rate (M, .fill) < workScale rate * ((rate + 1) * n) := by
    have hlt : Phi rate M.st + rate * v.length < (rate + 1) * n := by
      have hh := hbound M.st hpos hq
      by_contra hnlt
      have he : Phi rate M.st + rate * v.length = (rate + 1) * n := by omega
      have hposEq : M.st.pos = i := by
        by_contra hne
        have hle : M.st.pos + 1 ≤ i := by omega
        have hm := Nat.mul_le_mul_left (rate + 1) hle
        rw [← hd] at he
        simp only [Phi] at he
        nlinarith
      have hqEq : M.st.q = v.length := by
        simp only [Phi] at he
        rw [← hd, hposEq] at he
        nlinarith
      exact hno ⟨hposEq, hqEq⟩
    have hm := Nat.mul_lt_mul_of_pos_left hlt hC
    simpa only [workCredit, workScore, Nat.mul_add] using hm
  cases ph with
  | loop => exact (Nat.not_lt_of_ge hc) hplain
  | fill => exact (Nat.not_lt_of_ge hc) hplain
  | gate => exact (Nat.not_lt_of_ge hc) hplain
  | scan N =>
    have hnext := scanStep_pos_le_of_occ hK hk hi hocc hpos hnq
    have hnextq := scanStep_q_le (T := Text) (k := rate) (p₁ := p₁) (r := rem) hq
    have hb := Nat.mul_le_mul_left (workScale rate) (hbound _ hnext hnextq)
    have hr := retirement_work hk hp hmb hend hn h.2.2 h.1
    have hN : N ≤ cost e rate M := h.2.1
    simp only [workCredit, workScore, TextFeed.scanOne'_st, Nat.mul_add] at hc hr hb
    omega

theorem advance_scanInv (hK : KSimple v rate p₁ rem)
    {M : TextFeed.Machine' k} {ph : Phase} (h : ScanInv v Text M.st) :
    ScanInv v Text (advance e v Text rate p₁ rem n M ph).1.st := by
  classical
  cases ph with
  | loop => exact h
  | fill => simp only [advance]; split_ifs <;> simpa only [TextFeed.fillIf'_st] using h
  | gate => simp only [advance]; split_ifs <;> exact h
  | scan N =>
    simp only [advance]; split_ifs
    · exact h
    · exact scanStep_inv hK h

theorem advance_no_skip (hK : KSimple v rate p₁ rem) (hk : 0 < rate)
    {M : TextFeed.Machine' k} {ph : Phase} {i : ℕ}
    (h : ScanInv v Text M.st) (hocc : OccAt v Text i) (hpos : M.st.pos ≤ i)
    (hno : ¬ Hit v i M) :
    (advance e v Text rate p₁ rem n M ph).1.st.pos ≤ i := by
  classical
  have hs := scanStep_pos_le_of_occ hK hk h hocc hpos
    (fun hq he => hno ⟨he, hq⟩)
  cases ph with
  | loop => exact hpos
  | fill => simp only [advance]; split_ifs <;> simpa only [TextFeed.fillIf'_st] using hpos
  | gate => simp only [advance]; split_ifs <;> exact hpos
  | scan N => simp only [advance]; split_ifs <;> assumption

theorem modelRun_scanInv (hK : KSimple v rate p₁ rem) (N : ℕ)
    {M : TextFeed.Machine' k} {ph : Phase} (h : ScanInv v Text M.st) :
    ScanInv v Text (modelRun e v Text rate p₁ rem n N M ph).1.st := by
  induction N generalizing M ph with
  | zero => exact h
  | succ N ih =>
    rw [modelRun_succ]
    exact ih (advance_scanInv hK h)

/-- Without a report at any prefix, a worker window cannot skip an occurrence. -/
theorem modelRun_no_skip (hK : KSimple v rate p₁ rem) (hk : 0 < rate) (N : ℕ)
    {M : TextFeed.Machine' k} {ph : Phase} {i : ℕ}
    (h : ScanInv v Text M.st) (hocc : OccAt v Text i) (hpos : M.st.pos ≤ i)
    (hno : ∀ j, j ≤ N → ¬ Hit v i (modelRun e v Text rate p₁ rem n j M ph).1) :
    (modelRun e v Text rate p₁ rem n N M ph).1.st.pos ≤ i := by
  induction N generalizing M ph with
  | zero => exact hpos
  | succ N ih =>
    rw [modelRun_succ]
    apply ih (advance_scanInv hK h) (advance_no_skip hK hk h hocc hpos (hno 0 (by omega)))
    intro j hj
    simpa only [modelRun_succ] using hno (j + 1) (by omega)

/-- Any window that has earned its deadline credit must contain the
occurrence's report, not merely a partially executed comparison. -/
theorem modelRun_reports_of_credit (hk : 0 < rate) (hmb : e.mark ≠ e.blank)
    (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hn : n ≤ Text.length) (hK : KSimple v rate p₁ rem)
    (N : ℕ) {M : TextFeed.Machine' k} {ph : Phase} {i : ℕ}
    (h : WorkInv e v Text rate p₁ rem n (M, ph)) (hi : ScanInv v Text M.st)
    (hocc : OccAt v Text i) (hpos : M.st.pos ≤ i) (hd : i + v.length = n)
    (hc : workScale rate * ((rate + 1) * n) ≤
      workCredit v rate (modelRun e v Text rate p₁ rem n N M ph)) :
    ∃ j, j ≤ N ∧ Hit v i (modelRun e v Text rate p₁ rem n j M ph).1 := by
  by_contra hnex
  have hno : ∀ j, j ≤ N → ¬ Hit v i (modelRun e v Text rate p₁ rem n j M ph).1 := by
    intro j hj hh
    exact hnex ⟨j, hj, hh⟩
  have hpos' := modelRun_no_skip hK hk N hi hocc hpos hno
  have hi' := modelRun_scanInv (e := e) (n := n) (ph := ph) hK N hi
  have hw' := modelRun_workInv hk hmb hv hend hstart hblank hn N h
  exact hno N (Nat.le_refl N)
    (credit_forces_hit hk hK.period_pos hmb hend hn hK hw' hi' hocc hpos' hd hc)

theorem workInv_not_hit_before {M : TextFeed.Machine' k} {ph : Phase} {i : ℕ}
    (h : WorkInv e v Text rate p₁ rem n (M, ph)) (hn : n < i + v.length) :
    ¬ Hit v i M := by
  rintro ⟨hp, hq⟩
  have hh : M.st.pos + M.st.q ≤ M.m := h.1.hd
  have hm : M.m ≤ n := h.1.mle
  omega

theorem onlineWork_scanInv (hK : KSimple v rate p₁ rem) (R : ℕ)
    {M₀ : TextFeed.Machine' k} {ph₀ : Phase} (h₀ : ScanInv v Text M₀.st) (n : ℕ) :
    ScanInv v Text (onlineWork e v Text R rate p₁ rem M₀ ph₀ n).1.st := by
  induction n with
  | zero => exact h₀
  | succ n ih =>
    exact modelRun_scanInv hK R ih

/-- No occurrence can have been passed strictly before its deadline:
the tape frontier excludes reports, and safe shifts exclude skipping. -/
theorem onlineWork_no_skip_before (hk : 0 < rate) (hmb : e.mark ≠ e.blank)
    (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hK : KSimple v rate p₁ rem)
    {R : ℕ} (hR : workRate rate ≤ R) {M₀ : TextFeed.Machine' k} {ph₀ : Phase} {i : ℕ}
    (h₀ : WorkInv e v Text rate p₁ rem 0 (M₀, ph₀)) (hs₀ : ScanInv v Text M₀.st)
    (hocc : OccAt v Text i) (hpos₀ : M₀.st.pos ≤ i)
    (n : ℕ) (hn : n ≤ Text.length) (hbefore : n < i + v.length) :
    (onlineWork e v Text R rate p₁ rem M₀ ph₀ n).1.st.pos ≤ i := by
  induction n with
  | zero => exact hpos₀
  | succ n ih =>
    have hn' : n < Text.length := by omega
    have ha : Text[n]? = some (Text[n]?.getD e.blank) := by
      simp only [List.getElem?_eq_getElem hn', Option.getD_some]
    have hi := (onlineWork_credit hk hK.period_pos hmb hv hend hstart hblank hR h₀ n (by omega)).1
    have hiA := arrive_workInv hmb hn' ha hi
    have hs := onlineWork_scanInv (e := e) (ph₀ := ph₀) hK R hs₀ n
    have hp := ih (by omega) (by omega)
    apply modelRun_no_skip (M := TextFeed.arrive' e.blank e.mark (Text[n]?.getD e.blank)
      (onlineWork e v Text R rate p₁ rem M₀ ph₀ n).1) hK hk R hs hocc hp
    intro j hj
    exact workInv_not_hit_before
      (modelRun_workInv hk hmb hv hend hstart hblank hn j hiA) hbefore

/-- A suffix occurrence is reported within its very last input round.
No bounded-word enumeration or maximum scan length is assumed. -/
theorem onlineWork_deadline (hk : 0 < rate) (hmb : e.mark ≠ e.blank)
    (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hK : KSimple v rate p₁ rem)
    {R : ℕ} (hR : workRate rate ≤ R) {M₀ : TextFeed.Machine' k} {ph₀ : Phase} {i n : ℕ}
    (h₀ : WorkInv e v Text rate p₁ rem 0 (M₀, ph₀)) (hs₀ : ScanInv v Text M₀.st)
    (hocc : OccAt v Text i) (hpos₀ : M₀.st.pos ≤ i)
    (hn : n + 1 ≤ Text.length) (hd : i + v.length = n + 1) :
    let z := onlineWork e v Text R rate p₁ rem M₀ ph₀ n
    ∃ j, j ≤ R ∧ Hit v i (modelRun e v Text rate p₁ rem (n + 1) j
      (TextFeed.arrive' e.blank e.mark (Text[n]?.getD e.blank) z.1) z.2).1 := by
  have hn' : n < Text.length := by omega
  have ha : Text[n]? = some (Text[n]?.getD e.blank) := by
    simp only [List.getElem?_eq_getElem hn', Option.getD_some]
  have hi := (onlineWork_credit hk hK.period_pos hmb hv hend hstart hblank hR h₀ n (by omega)).1
  have hiA := arrive_workInv hmb hn' ha hi
  have hs := onlineWork_scanInv (e := e) (ph₀ := ph₀) hK R hs₀ n
  have hp := onlineWork_no_skip_before hk hmb hv hend hstart hblank hK hR h₀ hs₀
    hocc hpos₀ n (by omega) (by omega)
  have hc := (onlineWork_credit hk hK.period_pos hmb hv hend hstart hblank hR h₀ (n + 1) hn).2
  exact modelRun_reports_of_credit hk hmb hv hend hstart hblank hn hK R hiA hs hocc hp hd hc

/-- Every report in a worker window denotes a real occurrence. -/
theorem modelRun_hit_sound (hK : KSimple v rate p₁ rem)
    {M : TextFeed.Machine' k} {ph : Phase} {i j : ℕ}
    (hs : ScanInv v Text M.st) (hh : Hit v i (modelRun e v Text rate p₁ rem n j M ph).1) :
    OccAt v Text i := by
  have hi := (modelRun_scanInv (e := e) (n := n) (ph := ph) hK j hs).1
  rw [hh.1, hh.2] at hi
  exact hi

/-- A newly obtained report can only be a completed GS retirement.
Thus it is observable on stable scanner tapes, not just a ghost snapshot. -/
theorem advance_first_hit_phase {M : TextFeed.Machine' k} {ph : Phase} {i : ℕ}
    (hno : ¬ Hit v i M) (hh : Hit v i (advance e v Text rate p₁ rem n M ph).1) :
    (advance e v Text rate p₁ rem n M ph).2 = .fill := by
  classical
  cases ph with
  | loop => rfl
  | fill =>
    simp only [advance] at hh ⊢
    split_ifs at hh ⊢
    · exact False.elim (hno (by simpa only [Hit, TextFeed.fillIf'_st] using hh))
    · exact False.elim (hno hh)
  | gate =>
    simp only [advance] at hh ⊢
    split_ifs at hh ⊢ <;> exact False.elim (hno hh)
  | scan N =>
    simp only [advance] at hh ⊢
    split_ifs at hh ⊢
    · exact False.elim (hno hh)
    · rfl

theorem modelRun_succ_last (N : ℕ) (M : TextFeed.Machine' k) (ph : Phase) :
    modelRun e v Text rate p₁ rem n (N + 1) M ph =
      advance e v Text rate p₁ rem n (modelRun e v Text rate p₁ rem n N M ph).1
        (modelRun e v Text rate p₁ rem n N M ph).2 := by
  simp only [modelRun, Function.iterate_succ_apply']

theorem modelRun_stable_report {M : TextFeed.Machine' k} {ph : Phase} {i N : ℕ}
    (hno : ¬ Hit v i M)
    (hex : ∃ j, j ≤ N ∧ Hit v i (modelRun e v Text rate p₁ rem n j M ph).1) :
    ∃ j, 1 ≤ j ∧ j ≤ N ∧ Hit v i (modelRun e v Text rate p₁ rem n j M ph).1 ∧
      (modelRun e v Text rate p₁ rem n j M ph).2 = .fill := by
  classical
  let j := Nat.find hex
  have hj : j ≤ N ∧ Hit v i (modelRun e v Text rate p₁ rem n j M ph).1 := Nat.find_spec hex
  have hjpos : 0 < j := by
    by_contra hzero
    have hz : j = 0 := by omega
    exact hno (by simpa only [hz, modelRun, Function.iterate_zero_apply] using hj.2)
  obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
  have hprev : ¬ Hit v i (modelRun e v Text rate p₁ rem n l M ph).1 := by
    intro hh
    exact Nat.find_min hex (show l < j by omega) ⟨by omega, hh⟩
  refine ⟨j, hjpos, hj.1, hj.2, ?_⟩
  have hh := hj.2
  rw [hl, modelRun_succ_last] at hh ⊢
  exact advance_first_hit_phase hprev hh

/-- At the deadline the report occurs at a stable post-retirement boundary
strictly inside the worker window. It cannot be inherited from before arrival. -/
theorem onlineWork_stable_deadline (hk : 0 < rate) (hmb : e.mark ≠ e.blank)
    (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hK : KSimple v rate p₁ rem)
    {R : ℕ} (hR : workRate rate ≤ R) {M₀ : TextFeed.Machine' k} {ph₀ : Phase} {i n : ℕ}
    (h₀ : WorkInv e v Text rate p₁ rem 0 (M₀, ph₀)) (hs₀ : ScanInv v Text M₀.st)
    (hocc : OccAt v Text i) (hpos₀ : M₀.st.pos ≤ i)
    (hn : n + 1 ≤ Text.length) (hd : i + v.length = n + 1) :
    let z := onlineWork e v Text R rate p₁ rem M₀ ph₀ n
    ∃ j, 1 ≤ j ∧ j ≤ R ∧
      Hit v i (modelRun e v Text rate p₁ rem (n + 1) j
        (TextFeed.arrive' e.blank e.mark (Text[n]?.getD e.blank) z.1) z.2).1 ∧
      (modelRun e v Text rate p₁ rem (n + 1) j
        (TextFeed.arrive' e.blank e.mark (Text[n]?.getD e.blank) z.1) z.2).2 = .fill := by
  have hex := onlineWork_deadline hk hmb hv hend hstart hblank hK hR h₀ hs₀ hocc hpos₀ hn hd
  have hi := (onlineWork_credit hk hK.period_pos hmb hv hend hstart hblank hR h₀ n (by omega)).1
  have hno := workInv_not_hit_before hi (show n < i + v.length by omega)
  exact modelRun_stable_report hno hex

/-- info: 'PalPeg.TextFeedRefine.onlineWork_stable_deadline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms onlineWork_stable_deadline

end PalPeg.TextFeedRefine
