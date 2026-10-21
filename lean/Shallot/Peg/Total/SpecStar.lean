import Shallot.Peg.Total.Spec

/-!
# The specification for repetition

After a consuming step the repetition continues with the empty open set. `star_run` shows, by induction on the
length, that the rest `(p a ∅)* · fl a ∅` succeeds exactly where the repetition (with the empty set) succeeds, with
the same consumption, and fails where it loops. `spec_star` puts the first step in front.
-/

namespace Shallot

variable {g G : Grammar} {a : PExp} {ta ta0 : Tr}

/-- A repetition whose body succeeds without consuming loops. -/
theorem star_lp_okE {S : Nat} {y : List Char} (hB : Beh g S a y .okE) : Beh g S (.star a) y .lp := by
  obtain ⟨t, h⟩ := hB
  intro o hd
  cases hd with
  | starNil _ _ _ h' => cases ds_det h h'
  | starCons _ _ _ _ _ _ _ h₁ hne _ => cases ds_det h h₁; exact hne rfl

/-- A repetition whose body loops loops. -/
theorem star_lp_lp {S : Nat} {y : List Char} (hB : Beh g S a y .lp) : Beh g S (.star a) y .lp := by
  intro o hd
  cases hd with
  | starNil _ _ _ h' => exact hB _ h'
  | starCons _ _ _ _ _ _ _ h₁ _ _ => exact hB _ h₁

/-- A repetition loops when its first step reaches `r` where the repetition with the empty set loops. -/
theorem star_lp_step {S : Nat} {y r : List Char} {t : PTree} (h : DS g S a y (.ok t r))
    (hL : ∀ o, ¬ DS g 0 (.star a) r o) : Beh g S (.star a) y .lp := by
  intro o hd
  cases hd with
  | starNil _ _ _ h' => cases ds_det h h'
  | starCons _ _ _ _ _ _ _ h₁ _ h₂ => cases ds_det h h₁; exact hL _ h₂

/-- The outcome of the rest of a repetition: success with the repetition's consumption, or failure where it loops. -/
def RunOut (g G : Grammar) (a : PExp) (ta0 : Tr) (y : List Char) : Prop :=
  (∃ z, (∃ t, DS g 0 (.star a) y (.ok t z)) ∧ OkD G (starRest ta0) y z) ∨
    ((∀ o, ¬ DS g 0 (.star a) y o) ∧ FlD G (starRest ta0) y)

/-- One step of `star_run`: the body's behavior at `y` and the result at the reached suffix give the result at `y`. -/
theorem star_run_step {y : List Char} (hA : Spec g G ta0 0 a y)
    (hih : ∀ r, r.length < y.length → RunOut g G a ta0 r) : RunOut g G a ta0 y := by
  obtain ⟨c, hB, hG⟩ := hA
  cases c with
  | fl =>
    exact .inl ⟨y, ⟨_, .starNil _ _ _ hB⟩,
      ⟨_, .seqOk _ _ _ _ _ _ _ (.starNil _ _ hG.2.1) (fl_ok hG).choose_spec⟩⟩
  | okE =>
    exact .inr ⟨star_lp_okE hB, .seqFail₂ _ _ _ _ _ (.starNil _ _ hG.2.1) (fl_fail hG (by simp))⟩
  | lp =>
    exact .inr ⟨star_lp_lp hB, .seqFail₂ _ _ _ _ _ (.starNil _ _ hG.2.1) (fl_fail hG (by simp))⟩
  | okC r =>
    obtain ⟨hne, t, h⟩ := hB
    obtain ⟨tp, hp⟩ := hG.2.1
    rcases hih r (ds_lt h hne) with ⟨z, ⟨t₂, h₂⟩, ⟨tq, hq⟩⟩ | ⟨hL, hq⟩
    · cases hq with
      | seqOk _ _ _ w _ _ _ hs hf =>
        exact .inl ⟨z, ⟨_, .starCons _ _ _ _ _ _ _ h hne h₂⟩,
          ⟨_, .seqOk _ _ _ _ _ _ _ (.starCons _ _ _ _ _ _ hp hs) hf⟩⟩
    · cases hq with
      | seqFail₁ _ _ _ hs => cases hs
      | seqFail₂ _ _ _ w _ hs hf =>
        exact .inr ⟨star_lp_step h hL, .seqFail₂ _ _ _ _ _ (.starCons _ _ _ _ _ _ hp hs) hf⟩

/-- **The rest of a repetition**, at every position shorter than a bound where the body's specification holds. -/
theorem star_run {N : Nat} (hA : ∀ y, y.length < N → Spec g G ta0 0 a y) :
    ∀ M y, y.length < M → y.length < N → RunOut g G a ta0 y := by
  intro M
  induction M with
  | zero => intro y hy; omega
  | succ M ih =>
    intro y hy hN
    exact star_run_step (hA y hN) (fun r hr => ih r (by omega) (by omega))

/-- **Repetition.** -/
theorem spec_star {S : Nat} {x : List Char} (ha : Spec g G ta S a x)
    (ha0 : ∀ y, y.length < x.length → Spec g G ta0 0 a y) : Spec g G (starT ta ta0) S (.star a) x := by
  obtain ⟨c, hB, hG⟩ := ha
  cases c with
  | fl =>
    obtain ⟨tF, hF⟩ := fl_ok hG
    exact ⟨.okE, ⟨_, .starNil _ _ _ hB⟩, ⟨_, hF⟩, .seqFail₁ _ _ _ hG.2.1, .notOk _ _ _ _ (.altL _ _ _ _ _ hF)⟩
  | okE =>
    have hF := fl_fail hG (by simp)
    have hP : FlD G (.seq ta.p (starRest ta0)) x := .seqFail₁ _ _ _ hG.2.1
    exact ⟨.lp, star_lp_okE hB, hF, hP, x, _, .notFail _ _ (.altFail _ _ _ hF hP)⟩
  | lp =>
    have hF := fl_fail hG (by simp)
    have hP : FlD G (.seq ta.p (starRest ta0)) x := .seqFail₁ _ _ _ hG.2.1
    exact ⟨.lp, star_lp_lp hB, hF, hP, x, _, .notFail _ _ (.altFail _ _ _ hF hP)⟩
  | okC r =>
    have hF := fl_fail hG (by simp)
    obtain ⟨hne, t, h⟩ := hB
    obtain ⟨tp, hp⟩ := hG.2.1
    have hlt := ds_lt h hne
    rcases star_run ha0 (r.length + 1) r (by omega) hlt with ⟨z, ⟨t₂, h₂⟩, ⟨tq, hq⟩⟩ | ⟨hL, hq⟩
    · have hz : z ≠ x := by
        intro hz; subst hz
        obtain ⟨p, hp'⟩ := ds_suffix h₂
        have := suffix_le hp'; omega
      have hP : Derives G (.seq ta.p (starRest ta0)) x (.ok _ z) := .seqOk _ _ _ _ _ _ _ hp hq
      exact ⟨.okC z, ⟨hz, _, .starCons _ _ _ _ _ _ _ h hne h₂⟩, hF, ⟨_, hP⟩,
        .notOk _ _ _ _ (.altR _ _ _ _ _ hF hP)⟩
    · have hP : FlD G (.seq ta.p (starRest ta0)) x := .seqFail₂ _ _ _ _ _ hp hq
      exact ⟨.lp, star_lp_step h hL, hF, hP, x, _, .notFail _ _ (.altFail _ _ _ hF hP)⟩

end Shallot
