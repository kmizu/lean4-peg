import MacroPeg.Properties.DecideCBV

namespace Shallot.MacroPeg.CBV.SequentialClock

abbrev Table := Nat → List (List Char) → Val

/-- A table never returns an earlier input position (larger suffix length). -/
def Descending (T : Table) : Prop := ∀ i W p, OkR p (valAt (T i W) p)

mutual
  theorem expression_descending {g : MGrammar} {x : List Char} {T : Table}
      (hT : Descending T) (E : List (List Char)) :
      ∀ e p, OkR p (evV g x .callByValueSeq T E e p)
    | .eps, p | .dbg _, p | .lam _ _, p => by simp only [evV]; exact okR_ok (Nat.le_refl _)
    | .callParam _ _, _ => by simp only [evV]; exact okR_fail _
    | .invoke _ _ _, _ => by simp only [evV]; exact okR_none _
    | .any, p => by
      have hl : (sfx x p).length ≤ p := by simp only [sfx, List.length_drop]; omega
      simp only [evV]
      split
      · rename_i c rest he; rw [he] at hl; exact okR_ok (by simp at hl; omega)
      · exact okR_fail _
    | .chr c, p => by
      have hl : (sfx x p).length ≤ p := by simp only [sfx, List.length_drop]; omega
      simp only [evV]
      split
      · rename_i d rest he; rw [he] at hl
        split
        · exact okR_ok (by simp at hl; omega)
        · exact okR_fail _
      · exact okR_fail _
    | .range lo hi, p => by
      have hl : (sfx x p).length ≤ p := by simp only [sfx, List.length_drop]; omega
      simp only [evV]
      split
      · rename_i d rest he; rw [he] at hl
        split
        · exact okR_ok (by simp at hl; omega)
        · exact okR_fail _
      · exact okR_fail _
    | .lit w, p => by
      have hl : (sfx x p).length ≤ p := by simp only [sfx, List.length_drop]; omega
      simp only [evV]
      split
      · rename_i rest he; exact okR_ok (Nat.le_trans (stripPrefix_length _ _ _ he) hl)
      · exact okR_fail _
    | .param k, p => by
      have hl : (sfx x p).length ≤ p := by simp only [sfx, List.length_drop]; omega
      simp only [evV]
      split
      · split
        · rename_i rest he; exact okR_ok (Nat.le_trans (stripPrefix_length _ _ _ he) hl)
        · exact okR_fail _
      · exact okR_fail _
    | .call i args, p => by
      cases hr : ruleAtM g.rules i with
      | none => simp only [evV, hr]; exact okR_fail _
      | some rule =>
        by_cases ha : rule.arity = args.length
        · rw [evV_call_seq hr ha]
          cases hv : evSeqArgs g x .callByValueSeq T E args p with
          | none => exact okR_none _
          | some result =>
            cases result with
            | none => exact okR_fail _
            | some Wq =>
              obtain ⟨W, q⟩ := Wq
              have hq := (arguments_metadata hT E args p W q hv).1
              intro j hj
              exact Nat.le_trans (hT i W q j hj) hq
        · simp only [evV, hr, if_neg ha]; exact okR_fail _
    | .seq a b, p => by
      have ha := expression_descending (g := g) (x := x) hT E a p
      cases hv : evV g x .callByValueSeq T E a p with
      | none => rw [evV_seq_none hv]; exact okR_none _
      | some result =>
        cases result with
        | none => rw [evV_seq_fail hv]; exact okR_fail _
        | some q =>
          rw [evV_seq_ok hv]
          intro j hj
          exact Nat.le_trans (expression_descending hT E b q j hj) (ha q hv)
    | .alt a b, p => by
      cases hv : evV g x .callByValueSeq T E a p with
      | none => rw [evV_alt_none hv]; exact okR_none _
      | some result =>
        cases result with
        | none => rw [evV_alt_fail hv]; exact expression_descending hT E b p
        | some q => rw [evV_alt_ok hv]; exact okR_ok (expression_descending hT E a p q hv)
    | .notP a, p => by
      cases hv : evV g x .callByValueSeq T E a p with
      | none => rw [evV_not_none hv]; exact okR_none _
      | some result =>
        cases result with
        | none => rw [evV_not_fail hv]; exact okR_ok (Nat.le_refl _)
        | some q => rw [evV_not_ok hv]; exact okR_fail _
    | .star a, p => by rw [evV_star]; exact evStar_le p

  theorem arguments_metadata {g : MGrammar} {x : List Char} {T : Table}
      (hT : Descending T) (E : List (List Char)) :
      ∀ args p W q, evSeqArgs g x .callByValueSeq T E args p = some (some (W, q)) →
        q ≤ p ∧ (q = p → W = List.replicate args.length [])
    | [], p, W, q, h => by cases h; exact ⟨Nat.le_refl _, fun _ => rfl⟩
    | a :: args, p, W, q, h => by
      cases ha : evV g x .callByValueSeq T E a p with
      | none => simp [evSeqArgs, ha] at h
      | some result =>
        cases result with
        | none => simp [evSeqArgs, ha] at h
        | some j =>
          have hj := expression_descending hT E a p j ha
          cases ht : evSeqArgs g x .callByValueSeq T E args j with
          | none => simp [evSeqArgs, ha, ht] at h
          | some result =>
            cases result with
            | none => simp [evSeqArgs, ha, ht] at h
            | some Wr =>
              obtain ⟨V, r⟩ := Wr
              simp only [evSeqArgs, ha, ht, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨hr, hV⟩ := arguments_metadata hT E args j V r ht
              refine ⟨Nat.le_trans hr hj, ?_⟩
              intro he
              have hjp : j = p := by omega
              subst j
              simp [pre, hV he, List.replicate_succ]
end

theorem table_descending (g : MGrammar) (x : List Char) :
    ∀ m, Descending (tblV g x .callByValueSeq m)
  | 0 => by intro i W p; simp only [tblV, valAt_nil]; exact okR_none _
  | m + 1 => by
    intro i W p
    cases hr : ruleAtM g.rules i with
    | none => simp only [tblV, hr, valAt_nil]; exact okR_none _
    | some rule =>
      by_cases hp : p ≤ x.length
      · rw [valAt_tblV_succ hr W hp]
        exact expression_descending (table_descending g x m) W rule.body p
      · simp only [tblV, hr, valAt_rangeMap, if_neg hp]; exact okR_none _

/-- A Seq expression at position p consults arbitrary environments only at
strictly smaller positions, and all-empty environments at the same position. -/
def LocalAgree (g : MGrammar) (p : Nat) (T U : Table) : Prop :=
  ∀ i rule W, ruleAtM g.rules i = some rule → rule.arity = W.length →
    ∀ q, q ≤ p → (q = p → W = List.replicate rule.arity []) →
      valAt (T i W) q = valAt (U i W) q

mutual
  theorem expression_agree {g : MGrammar} {x : List Char} {T U : Table} {bound : Nat}
      (hT : Descending T) (h : LocalAgree g bound T U) (E : List (List Char)) :
      ∀ e p, p ≤ bound → evV g x .callByValueSeq T E e p = evV g x .callByValueSeq U E e p
    | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _
    | .param _, _, _ | .dbg _, _, _ | .lam _ _, _, _ | .callParam _ _, _, _
    | .invoke _ _ _, _, _ => rfl
    | .call i args, p, hp => by
      cases hr : ruleAtM g.rules i with
      | none => simp only [evV, hr]
      | some rule =>
        by_cases ha : rule.arity = args.length
        · rw [evV_call_seq hr ha, evV_call_seq hr ha, ← arguments_agree hT h E args p hp]
          cases hv : evSeqArgs g x .callByValueSeq T E args p with
          | none => rfl
          | some result =>
            cases result with
            | none => rfl
            | some Wq =>
              obtain ⟨W, q⟩ := Wq
              obtain ⟨hq, hzero⟩ := arguments_metadata hT E args p W q hv
              have hlen := evSeq_length args p W q hv
              apply h i rule W hr (by omega) q (by omega)
              intro heq
              have hqp : q = p := by omega
              rw [ha]
              exact hzero hqp
        · simp only [evV, hr, if_neg ha]
    | .seq a b, p, hp => by
      have heq := expression_agree (g := g) (x := x) hT h E a p hp
      cases hv : evV g x .callByValueSeq T E a p with
      | none => rw [evV_seq_none hv, evV_seq_none (heq.symm.trans hv)]
      | some result =>
        cases result with
        | none => rw [evV_seq_fail hv, evV_seq_fail (heq.symm.trans hv)]
        | some q =>
          rw [evV_seq_ok hv, evV_seq_ok (heq.symm.trans hv)]
          have hq := expression_descending hT E a p q hv
          exact expression_agree hT h E b q (by omega)
    | .alt a b, p, hp => by
      have heq := expression_agree (g := g) (x := x) hT h E a p hp
      cases hv : evV g x .callByValueSeq T E a p with
      | none => rw [evV_alt_none hv, evV_alt_none (heq.symm.trans hv)]
      | some result =>
        cases result with
        | none =>
          rw [evV_alt_fail hv, evV_alt_fail (heq.symm.trans hv)]
          exact expression_agree hT h E b p hp
        | some q => rw [evV_alt_ok hv, evV_alt_ok (heq.symm.trans hv)]
    | .notP a, p, hp => by
      simp only [evV]
      rw [expression_agree hT h E a p hp]
    | .star a, p, hp => by
      rw [evV_star, evV_star]
      exact evStar_congr p (fun q hq => expression_agree hT h E a q (by omega))

  theorem arguments_agree {g : MGrammar} {x : List Char} {T U : Table} {bound : Nat}
      (hT : Descending T) (h : LocalAgree g bound T U) (E : List (List Char)) :
      ∀ args p, p ≤ bound →
        evSeqArgs g x .callByValueSeq T E args p = evSeqArgs g x .callByValueSeq U E args p
    | [], _, _ => rfl
    | a :: args, p, hp => by
      have heq := expression_agree (g := g) (x := x) hT h E a p hp
      simp only [evSeqArgs]
      rw [← heq]
      cases hv : evV g x .callByValueSeq T E a p with
      | none => rfl
      | some result =>
        cases result with
        | none => rfl
        | some q =>
          have hq := expression_descending hT E a p q hv
          simp only []
          rw [arguments_agree hT h E args q (by omega)]
end

def EmptyAgree (g : MGrammar) (p : Nat) (T U : Table) : Prop :=
  ∀ i rule, ruleAtM g.rules i = some rule →
    valAt (T i (List.replicate rule.arity [])) p = valAt (U i (List.replicate rule.arity [])) p

def RowAgree (g : MGrammar) (p : Nat) (T U : Table) : Prop :=
  ∀ i rule W, ruleAtM g.rules i = some rule → rule.arity = W.length →
    valAt (T i W) p = valAt (U i W) p

theorem RowAgree.empty {g : MGrammar} {p : Nat} {T U : Table} (h : RowAgree g p T U) :
    EmptyAgree g p T U := fun i rule hr => h i rule _ hr (by simp)

theorem local_of_rows {g : MGrammar} {p : Nat} {T U : Table}
    (lower : ∀ q, q < p → RowAgree g q T U) (same : EmptyAgree g p T U) :
    LocalAgree g p T U := by
  intro i rule W hr hlen q hq hzero
  by_cases he : q = p
  · subst q
    rw [hzero rfl]
    exact same i rule hr
  · exact lower q (by omega) i rule W hr hlen

def emptyCount (g : MGrammar) (p : Nat) (T : Table) : Nat :=
  ((List.range g.rules.length).map (fun i =>
    match ruleAtM g.rules i with
    | some rule => defined (valAt (T i (List.replicate rule.arity [])) p)
    | none => 0)).sum

theorem emptyCount_le (g : MGrammar) (p : Nat) (T : Table) :
    emptyCount g p T ≤ g.rules.length := by
  have hh := sum_le_length_mul (fun i =>
    match ruleAtM g.rules i with
    | some rule => defined (valAt (T i (List.replicate rule.arity [])) p)
    | none => 0) 1 (List.range g.rules.length) (by
      intro i hi; split
      · exact defined_le_one _
      · omega)
  simpa [emptyCount] using hh

theorem emptyCount_mono {g : MGrammar} {p : Nat} {T U : Table} (h : TLeV T U) :
    emptyCount g p T ≤ emptyCount g p U := by
  apply sum_le_sum_of_le
  intro i hi
  split
  · exact defined_le (h i _ p)
  · exact Nat.le_refl _

theorem empty_agree_of_count_eq {g : MGrammar} {p : Nat} {T U : Table} (h : TLeV T U)
    (he : emptyCount g p T = emptyCount g p U) : EmptyAgree g p T U := by
  intro i rule hr
  have hi := eq_of_sum_eq _ _ (List.range g.rules.length) (fun j _ => by
    split
    · exact defined_le (h j _ p)
    · exact Nat.le_refl _) he i (List.mem_range.mpr (ruleAtM_lt hr))
  simp only [hr] at hi
  rcases h i (List.replicate rule.arity []) p with hn | heq
  · rw [hn] at hi ⊢
    cases hv : valAt (U i (List.replicate rule.arity [])) p with
    | none => rfl
    | some result => rw [hv] at hi; simp [defined] at hi
  · exact heq

/-- At any starting clock, one of the next |rules|+1 stages leaves every
all-empty environment unchanged at this position. -/
theorem empty_fix_exists (g : MGrammar) (x : List Char) (p base : Nat) :
    ∃ m, base ≤ m ∧ m ≤ base + g.rules.length ∧
      EmptyAgree g p (tblV g x .callByValueSeq m) (tblV g x .callByValueSeq (m + 1)) := by
  refine Classical.byContradiction fun hne => ?_
  have hlt : ∀ k, k ≤ g.rules.length →
      emptyCount g p (tblV g x .callByValueSeq (base + k)) <
        emptyCount g p (tblV g x .callByValueSeq (base + k + 1)) := by
    intro k hk
    apply Nat.lt_of_le_of_ne (emptyCount_mono (tblV_step g x .callByValueSeq _))
    intro heq
    exact hne ⟨base + k, by omega, by omega,
      empty_agree_of_count_eq (tblV_step g x .callByValueSeq _) heq⟩
  have hgrow : ∀ k, k ≤ g.rules.length + 1 →
      k ≤ emptyCount g p (tblV g x .callByValueSeq (base + k)) := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
      intro hk
      have hh := hlt k (by omega)
      have hp := ih (by omega)
      simpa only [Nat.add_assoc] using (show k + 1 ≤
        emptyCount g p (tblV g x .callByValueSeq (base + k + 1)) by omega)
  have hh := hgrow (g.rules.length + 1) (Nat.le_refl _)
  have hb := emptyCount_le g p (tblV g x .callByValueSeq (base + (g.rules.length + 1)))
  omega

theorem row_step {g : MGrammar} {x : List Char} {p m : Nat} (hp : p ≤ x.length)
    (lower : ∀ q, q < p → RowAgree g q
      (tblV g x .callByValueSeq m) (tblV g x .callByValueSeq (m + 1)))
    (same : EmptyAgree g p (tblV g x .callByValueSeq m) (tblV g x .callByValueSeq (m + 1))) :
    RowAgree g p (tblV g x .callByValueSeq (m + 1)) (tblV g x .callByValueSeq (m + 2)) := by
  intro i rule W hr hlen
  rw [valAt_tblV_succ hr W hp, valAt_tblV_succ hr W hp]
  exact expression_agree (table_descending g x m) (local_of_rows lower same) W rule.body p (Nat.le_refl _)

theorem row_eventual {g : MGrammar} {x : List Char} {p base : Nat} (hp : p ≤ x.length)
    (lower : ∀ m, base ≤ m → ∀ q, q < p → RowAgree g q
      (tblV g x .callByValueSeq m) (tblV g x .callByValueSeq (m + 1))) :
    ∀ m, base + g.rules.length + 1 ≤ m → RowAgree g p
      (tblV g x .callByValueSeq m) (tblV g x .callByValueSeq (m + 1)) := by
  obtain ⟨start, hb, hs, hfix⟩ := empty_fix_exists g x p base
  have hrows : ∀ k, RowAgree g p (tblV g x .callByValueSeq (start + k + 1))
      (tblV g x .callByValueSeq (start + k + 2)) := by
    intro k
    induction k with
    | zero => exact row_step hp (lower start hb) hfix
    | succ k ih =>
      have hh := row_step hp (lower (start + k + 1) (by omega)) ih.empty
      simpa only [Nat.add_assoc] using hh
  intro m hm
  have he : start + (m - start - 1) + 1 = m := by omega
  have hh := hrows (m - start - 1)
  simpa only [show start + (m - start - 1) + 2 = m + 1 by omega, he] using hh

def positionClock (g : MGrammar) (p : Nat) : Nat := (g.rules.length + 1) * (p + 1)

/-- Every valid environment at position p stabilizes after a number of table
rounds linear in p, regardless of rule arity or captured-string lengths. -/
theorem position_stable (g : MGrammar) (x : List Char) : ∀ p, p ≤ x.length →
    ∀ m, positionClock g p ≤ m → RowAgree g p
      (tblV g x .callByValueSeq m) (tblV g x .callByValueSeq (m + 1)) := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro hp m hm
    apply row_eventual (base := (g.rules.length + 1) * p) hp ?_ m ?_
    · intro k hk q hq
      apply ih q hq (by omega) k
      have hh := Nat.mul_le_mul_left (g.rules.length + 1) (show q + 1 ≤ p by omega)
      exact Nat.le_trans hh hk
    · simpa only [positionClock, Nat.mul_succ, Nat.add_assoc] using hm

theorem expression_step_stable (g : MGrammar) (x : List Char) (m : Nat)
    (hm : positionClock g x.length ≤ m) (E : List (List Char)) (e : MExp)
    (p : Nat) (hp : p ≤ x.length) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq m) E e p =
      evV g x .callByValueSeq (tblV g x .callByValueSeq (m + 1)) E e p := by
  apply expression_agree (table_descending g x m) (bound := x.length) ?_ E e p hp
  intro i rule W hr hlen q hq hzero
  apply position_stable g x q hq m ?_ i rule W hr hlen
  have hh := Nat.mul_le_mul_left (g.rules.length + 1) (show q + 1 ≤ x.length + 1 by omega)
  exact Nat.le_trans hh hm

theorem expression_from_clock (g : MGrammar) (x : List Char) (E : List (List Char))
    (e : MExp) (p : Nat) (hp : p ≤ x.length) : ∀ k,
    evV g x .callByValueSeq (tblV g x .callByValueSeq (positionClock g x.length)) E e p =
      evV g x .callByValueSeq (tblV g x .callByValueSeq (positionClock g x.length + k)) E e p := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    exact ih.trans (expression_step_stable g x _ (by omega) E e p hp)

/-- Every finite result already appears at the explicit linear table clock. -/
theorem finite_eval_iff (g : MGrammar) (x : List Char) (E : List (List Char))
    (e : MExp) (p : Nat) (hp : p ≤ x.length) (r : Option Nat) :
    (∃ m, evV g x .callByValueSeq (tblV g x .callByValueSeq m) E e p = some r) ↔
      evV g x .callByValueSeq (tblV g x .callByValueSeq (positionClock g x.length)) E e p = some r := by
  constructor
  · rintro ⟨m, hm⟩
    by_cases hle : m ≤ positionClock g x.length
    · exact evV_lift hle hm
    · have he := expression_from_clock g x E e p hp (m - positionClock g x.length)
      rw [Nat.add_sub_cancel' (by omega)] at he
      exact he.trans hm
  · intro h; exact ⟨_, h⟩

theorem evaluator_eq_standard (g : MGrammar) (x : List Char) (e : MExp) (p : Nat)
    (hp : p ≤ x.length) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (positionClock g x.length)) [] e p =
      evV g x .callByValueSeq (tblV g x .callByValueSeq (iterBoundV g x)) [] e p := by
  cases hlin : evV g x .callByValueSeq (tblV g x .callByValueSeq (positionClock g x.length)) [] e p with
  | none =>
    cases hstd : evV g x .callByValueSeq (tblV g x .callByValueSeq (iterBoundV g x)) [] e p with
    | none => rfl
    | some r =>
      have hh := (finite_eval_iff g x [] e p hp r).mp ⟨iterBoundV g x, hstd⟩
      rw [hlin] at hh
      cases hh
  | some r =>
    exact ((tblV_stable g x .callByValueSeq hp).mp ⟨positionClock g x.length, hlin⟩).symm

def decide (g : MGrammar) (x : List Char) (e : MExp) : Option (Option (List Char)) :=
  match evV g x .callByValueSeq (tblV g x .callByValueSeq (positionClock g x.length)) [] e x.length with
  | none => none
  | some none => some none
  | some (some q) => some (some (sfx x q))

theorem decide_eq_standard (g : MGrammar) (x : List Char) (e : MExp) :
    decide g x e = decideObsV .callByValueSeq g x e := by
  unfold decide decideObsV
  rw [evaluator_eq_standard g x e x.length (Nat.le_refl _)]
  rfl

/-- The actual linear-clock decision procedure preserves all finite Seq
observations on original character strings, without a termination premise. -/
theorem decide_iff {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (x : List Char) (r : Option (List Char)) :
    decide g x e = some r ↔ SObs g .callByValueSeq e x r := by
  rw [decide_eq_standard]
  exact decideObsV_iff hg (by decide) he x r

theorem decide_none_iff {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (x : List Char) : decide g x e = none ↔ ∀ r, ¬ SObs g .callByValueSeq e x r := by
  rw [decide_eq_standard]
  exact decideObsV_none_iff hg (by decide) he x

end Shallot.MacroPeg.CBV.SequentialClock
