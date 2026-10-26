import MacroPeg.CBV.CaptureObservability
import MacroPeg.CBV.CaptureViews
import MacroPeg.CBV.SequentialClock

/-! The exact body-independent quotient of opaque captures on one remaining
input. Every replayable word keeps its identity. Unreplayable words and an
unbound parameter form one class. The converse uses full-input acceptance
contexts, so this is not merely a distinction between residual cursors.
This local interface result does not separate grammar language classes. -/
namespace Shallot.MacroPeg.CBV.LiveCaptureQuotient

open CaptureObservability (EnvAgree Unreplayable parameterRest)

def visible (x w : List Char) : Bool :=
  (List.range (x.length+1)).any (fun p => (Shallot.stripPrefix? w (sfx x p)).isSome)

def profile (x : List Char) : Option (List Char) → Option (List Char)
  | none => none
  | some w => if visible x w = true then some w else none

theorem visible_iff (x w : List Char) : visible x w = true ↔
    ∃ p, p≤x.length ∧ (Shallot.stripPrefix? w (sfx x p)).isSome = true := by
  simp only [visible, List.any_eq_true, List.mem_range, Nat.lt_succ_iff]

theorem invisible_iff (x w : List Char) : visible x w = false ↔ Unreplayable x w := by
  constructor
  · intro hv p hp
    cases hs : Shallot.stripPrefix? w (sfx x p) with
    | none => rfl
    | some rest =>
      have hh := (visible_iff x w).mpr ⟨p,hp,by simp [hs]⟩
      rw [hv] at hh
      cases hh
  · intro hd
    cases hv : visible x w with
    | false => rfl
    | true =>
      obtain ⟨p,hp,hs⟩ := (visible_iff x w).mp hv
      rw [hd p hp] at hs
      cases hs

theorem profile_some (x : List Char) (v : Option (List Char)) (w : List Char) :
    profile x v = some w ↔ v = some w ∧ visible x w = true := by
  cases v with
  | none => simp [profile]
  | some u =>
    by_cases hu : visible x u = true
    · simp only [profile, if_pos hu, Option.some.injEq]
      constructor
      · intro h; subst w; exact ⟨rfl,hu⟩
      · exact And.left
    · simp [profile,hu]
      intro h
      subst w
      simpa using hu

theorem profile_rest (x : List Char) (v : Option (List Char)) (p : Nat) (hp : p≤x.length) :
    (profile x v).bind (fun w => Shallot.stripPrefix? w (sfx x p)) =
      v.bind (fun w => Shallot.stripPrefix? w (sfx x p)) := by
  cases v with
  | none => rfl
  | some w =>
    by_cases hv : visible x w = true
    · simp [profile,hv]
    · have hd : Unreplayable x w := (invisible_iff x w).mp (by simpa using hv)
      simp [profile,hv,hd p hp]

theorem profile_empty (x : List Char) : profile x (some [])=some [] := by
  apply (profile_some x _ []).mpr
  refine ⟨rfl,(visible_iff x []).mpr ⟨0,Nat.zero_le _,?_⟩⟩
  rfl

theorem profile_dead {x w : List Char} (hd : Unreplayable x w) : profile x (some w)=none := by
  have hv := (invisible_iff x w).mpr hd
  simp [profile,hv]

def test (k : Nat) (lead trail : List Char) : MExp :=
  .seq (.lit lead) (.seq (.param k) (.lit trail))

theorem test_firstOrder (k : Nat) (lead trail : List Char) : (test k lead trail).FirstOrder := by
  trivial

private theorem literal_whole (g : MGrammar) (x : List Char) (s : Strategy)
    (T : SequentialClock.Table) (E : List (List Char)) (w : List Char) :
    evV g x s T E (.lit w) x.length = some (some 0) ↔ x=w := by
  constructor
  · intro h
    cases hs : Shallot.stripPrefix? w x with
    | none => simp [evV,sfx_self,hs] at h
    | some rest =>
      have hl : rest.length=0 := by simpa [evV,sfx_self,hs] using h
      have he := (CBVtoCBN.stripPrefix_exact w x rest).mp hs
      simpa [List.eq_nil_of_length_eq_zero hl] using he
  · rintro rfl
    have hs : Shallot.stripPrefix? x x=some [] :=
      (CBVtoCBN.stripPrefix_exact x x []).mpr (by simp)
    simp [evV,sfx_self,hs]

theorem test_accept (g : MGrammar) (x : List Char) (s : Strategy)
    (T : SequentialClock.Table) (E : List (List Char)) (k : Nat) (lead trail : List Char) :
    evV g x s T E (test k lead trail) x.length = some (some 0) ↔
      ∃ w, E[k]?=some w ∧ x=lead++w++trail := by
  cases hk : E[k]? with
  | none =>
    simp only [test, evV, hk]
    cases Shallot.stripPrefix? lead (sfx x x.length) <;> simp
  | some w =>
    have ht (p : Nat) : evV g x s T E (.seq (.param k) (.lit trail)) p =
        evV g x s T E (.lit (w++trail)) p := by
      have he : evV g x s T E (.seq (.param k) (.lit trail)) p =
          evV g x s T E (.seq (.lit w) (.lit trail)) p := by simp only [evV,hk]
      exact he.trans (CaptureViews.sequence_literals g x s T E w trail p)
    have he : evV g x s T E (test k lead trail) x.length =
        evV g x s T E (.lit (lead++(w++trail))) x.length := by
      rw [← CaptureViews.sequence_literals g x s T E lead (w++trail) x.length]
      change (match evV g x s T E (.lit lead) x.length with
        | some (some p) => evV g x s T E (.seq (.param k) (.lit trail)) p
        | result => result) = (match evV g x s T E (.lit lead) x.length with
          | some (some p) => evV g x s T E (.lit (w++trail)) p
          | result => result)
      cases evV g x s T E (.lit lead) x.length with
      | none => rfl
      | some result =>
        cases result with
        | none => rfl
        | some p => exact ht p
    rw [he,literal_whole]
    simp [List.append_assoc]

private theorem profile_transport (g : MGrammar) (x : List Char) (s : Strategy)
    (T : SequentialClock.Table) (E F : List (List Char))
    (h : ∀ k lead trail,
      evV g x s T E (test k lead trail) x.length=some (some 0) →
        evV g x s T F (test k lead trail) x.length=some (some 0))
    (k : Nat) (w : List Char) (hw : profile x E[k]?=some w) : profile x F[k]?=some w := by
  obtain ⟨hget,hvis⟩ := (profile_some x _ w).mp hw
  obtain ⟨p,hp,hmatch⟩ := (visible_iff x w).mp hvis
  cases hs : Shallot.stripPrefix? w (sfx x p) with
  | none => simp [hs] at hmatch
  | some trail =>
    obtain ⟨lead,hroot⟩ := sfx_is_suffix x p
    have hx : x=lead++w++trail := by
      rw [hroot,(CBVtoCBN.stripPrefix_exact _ _ _).mp hs,List.append_assoc]
    have hstart := (test_accept g x s T E k lead trail).mpr ⟨w,hget,hx⟩
    obtain ⟨v,hv,hxv⟩ := (test_accept g x s T F k lead trail).mp (h k lead trail hstart)
    have hword : w=v := by
      apply List.append_cancel_right
      apply List.append_cancel_left
      exact (by simpa only [List.append_assoc] using hx.symm.trans hxv)
    subst v
    exact (profile_some x _ w).mpr ⟨hv,hvis⟩

/-- Only accepting tests at the original input origin are needed for the
converse. Arbitrary input-specific literal wrappers are allowed contexts. -/
theorem profiles_of_tests (g : MGrammar) (x : List Char) (s : Strategy)
    (T : SequentialClock.Table) (E F : List (List Char))
    (h : ∀ k lead trail,
      evV g x s T E (test k lead trail) x.length=some (some 0) ↔
        evV g x s T F (test k lead trail) x.length=some (some 0)) :
    ∀ k : Nat, profile x E[k]? = profile x F[k]? := by
  intro k
  cases he : profile x E[k]? with
  | some w => exact (profile_transport g x s T E F (fun k lead trail => (h k lead trail).mp) k w he).symm
  | none =>
    cases hf : profile x F[k]? with
    | none => rfl
    | some w =>
      have hh := profile_transport g x s T F E (fun k lead trail => (h k lead trail).mpr) k w hf
      rw [he] at hh
      cases hh

theorem envAgree_iff_profiles (x : List Char) (E F : List (List Char)) :
    EnvAgree x E F ↔ ∀ k : Nat, profile x E[k]?=profile x F[k]? := by
  constructor
  · intro h
    apply profiles_of_tests ⟨[]⟩ x .callByValueSeq (tblV ⟨[]⟩ x .callByValueSeq 0) E F
    intro k lead trail
    rw [CaptureObservability.evaluator_eq (tblV_ok _ _ _ _) h _ _ (Nat.le_refl _)]
  · intro h k p hp
    unfold parameterRest
    rw [← profile_rest x E[k]? p hp, ← profile_rest x F[k]? p hp, h k]

theorem acceptance_contexts_iff {g : MGrammar} {x : List Char} {s : Strategy}
    {T : SequentialClock.Table} (hT : OkTV x.length T) (E F : List (List Char)) :
    (∀ e : MExp, e.FirstOrder →
      (evV g x s T E e x.length=some (some 0) ↔ evV g x s T F e x.length=some (some 0))) ↔
        ∀ k : Nat, profile x E[k]?=profile x F[k]? := by
  constructor
  · intro h
    exact profiles_of_tests g x s T E F (fun k lead trail => h _ (test_firstOrder k lead trail))
  · intro h e he
    rw [CaptureObservability.evaluator_eq hT ((envAgree_iff_profiles x E F).mpr h) e _ (Nat.le_refl _)]

theorem live_injective {x u v : List Char} (hu : visible x u=true)
    (h : profile x (some u)=profile x (some v)) : u=v := by
  have hs : profile x (some u)=some u := (profile_some x _ u).mpr ⟨rfl,hu⟩
  have hv := (profile_some x (some v) u).mp (h.symm.trans hs)
  exact (Option.some.inj hv.1).symm

private theorem accepts_iff_clock {g : MGrammar} {x : List Char} {s : Strategy}
    (hg : g.FirstOrder) (hs : s≠.callByName) (E : List (List Char)) (e : MExp) (he : e.FirstOrder) :
    SObs g s (MExp.subst (E.map MExp.lit) e) x (some []) ↔
      ∃ m, evV g x s (tblV g x s m) E e x.length=some (some 0) := by
  have he' := firstOrder_subst (firstOrderArgs_lits E) e he
  constructor
  · rintro ⟨out,hd,hr⟩
    cases out with
    | fail => cases hr
    | ok tree rest =>
      have hr' : rest=[] := Option.some.inj hr
      subst rest
      obtain ⟨m,hv⟩ := derivesV_ev (x := x) hg hs hd he' ⟨[],by simp⟩
      exact ⟨m, by simpa only [evV_subst E e he, obsR, List.length_nil] using hv⟩
  · rintro ⟨m,hv⟩
    have hv' : evV g x s (tblV g x s m) [] (MExp.subst (E.map MExp.lit) e) x.length =
        some (some 0) := (evV_subst E e he x.length).trans hv
    obtain ⟨out,hd,ho⟩ := evV_derives hg hs he' m (Nat.le_refl _) hv'
    cases out with
    | fail => cases ho
    | ok tree rest =>
      have hr : rest=[] := List.eq_nil_of_length_eq_zero (by simpa [obsR] using ho)
      subst rest
      exact ⟨_,by simpa only [sfx_self] using hd,rfl⟩

theorem test_observation {g : MGrammar} {x : List Char} {s : Strategy}
    (hg : g.FirstOrder) (hs : s≠.callByName) (E : List (List Char))
    (k : Nat) (lead trail : List Char) :
    SObs g s (MExp.subst (E.map MExp.lit) (test k lead trail)) x (some []) ↔
      ∃ w, E[k]?=some w ∧ x=lead++w++trail := by
  rw [accepts_iff_clock hg hs E _ (test_firstOrder k lead trail)]
  constructor
  · rintro ⟨m,hv⟩
    exact (test_accept g x s _ E k lead trail).mp hv
  · intro h
    exact ⟨0,(test_accept g x s _ E k lead trail).mpr h⟩

theorem live_distinguishing_test {g : MGrammar} {x u v : List Char} {s : Strategy}
    (hg : g.FirstOrder) (hs : s≠.callByName) (hu : visible x u=true) (hne : u≠v) :
    ∃ lead trail,
      SObs g s (MExp.subst [MExp.lit u] (test 0 lead trail)) x (some []) ∧
        ¬SObs g s (MExp.subst [MExp.lit v] (test 0 lead trail)) x (some []) := by
  obtain ⟨p,hp,hmatch⟩ := (visible_iff x u).mp hu
  cases hm : Shallot.stripPrefix? u (sfx x p) with
  | none => simp [hm] at hmatch
  | some trail =>
    obtain ⟨lead,hroot⟩ := sfx_is_suffix x p
    have hx : x=lead++u++trail := by
      rw [hroot,(CBVtoCBN.stripPrefix_exact _ _ _).mp hm,List.append_assoc]
    refine ⟨lead,trail,(test_observation hg hs [u] 0 lead trail).mpr ⟨u,rfl,hx⟩,?_⟩
    intro hbad
    obtain ⟨w,hw,hxw⟩ := (test_observation hg hs [v] 0 lead trail).mp hbad
    have hwv : w=v := by simpa using hw.symm
    subst w
    apply hne
    apply List.append_cancel_right
    apply List.append_cancel_left
    simpa only [List.append_assoc] using hx.symm.trans hxw

/-- Exact contextual equivalence for ordinary finite CBV observations:
the grammar is fixed, contexts range over all first-order expressions,
and every test asks for full consumption of the same original input. -/
theorem observations_contexts_iff {g : MGrammar} {x : List Char} {s : Strategy}
    (hg : g.FirstOrder) (hs : s≠.callByName) (E F : List (List Char)) :
    (∀ e : MExp, e.FirstOrder →
      (SObs g s (MExp.subst (E.map MExp.lit) e) x (some []) ↔
        SObs g s (MExp.subst (F.map MExp.lit) e) x (some []))) ↔
          ∀ k : Nat, profile x E[k]?=profile x F[k]? := by
  constructor
  · intro h
    apply profiles_of_tests g x s (tblV g x s 0) E F
    intro k lead trail
    rw [test_accept,test_accept,← test_observation hg hs E,← test_observation hg hs F]
    exact h _ (test_firstOrder k lead trail)
  · intro h e he
    exact CaptureObservability.observations_iff hg hs ((envAgree_iff_profiles x E F).mpr h) e he (some [])

end Shallot.MacroPeg.CBV.LiveCaptureQuotient
