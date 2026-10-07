import Cfg.Greibach.PelHomSteps

/-!
# Completeness of the simulation

Whatever `g` derives on the image `img q u`, the simulating grammar reproduces from `q` on the source `u`
(`complete`): if `e` fails, every call `(e, q, q')` fails; if `e` succeeds with rest `img q₁ u₁`, the call
for `q₁` succeeds with rest `u₁` and every other call fails.
-/

namespace Shallot.Cfg

open Shallot (Grammar Derives PExp PTree Outcome ruleAt beqChar leChar stripPrefix?)

/-- Building a hit from its two halves. -/
theorem Hits.mk' {G : Grammar} {Q : List St} {F : St → PExp} {u : List Char} {q₁ : St} {u₁ : List Char}
    (hq : q₁ ∈ Q) (hok : ∃ t, Derives G (F q₁) u (.ok t u₁))
    (hfail : ∀ q' ∈ Q, q' ≠ q₁ → Derives G (F q') u .fail) : Hits G Q F u q₁ u₁ :=
  ⟨hq, fun q' hq' => ⟨fun he => he ▸ hok, hfail q' hq'⟩⟩

/-- The members of a hitting family other than the hit fail. -/
theorem Hits.fail {G : Grammar} {Q : List St} {F : St → PExp} {u : List Char} {q₁ : St} {u₁ : List Char}
    (h : Hits G Q F u q₁ u₁) {q' : St} (hq' : q' ∈ Q) (hne : q' ≠ q₁) : Derives G (F q') u .fail :=
  (h.2 q' hq').2 hne

namespace PhSim

variable (M : PhSim)

/-- What the simulation must reproduce of an outcome of `e` from state `q` on source `u`. -/
def CSpec (e : PExp) (q : St) (u : List Char) : Outcome → Prop
  | .fail => Misses M.grammar M.stList (M.NF e q) u
  | .ok _ r => ∃ q₁ u₁, r = M.img q₁ u₁ ∧ Hits M.grammar M.stList (M.NF e q) u q₁ u₁

/-- `guardEq` succeeds on equal states. -/
theorem guardEq_ok {G : Grammar} (q : St) (u : List Char) : Derives G (guardEq q q) u (.ok (.leaf []) u) := by
  simp only [guardEq, if_true]; exact .eps u

/-- `guardEq` fails on different states. -/
theorem guardEq_fail {G : Grammar} {q q' : St} (h : q ≠ q') (u : List Char) : Derives G (guardEq q q') u .fail := by
  simp only [guardEq, if_neg h]; exact phFail_fail u

/-- One image letter, as a `CSpec` for an atom whose body is `step1 P`. -/
theorem atom_spec (hne : ∀ a, M.h a ≠ []) (hS : ∀ a, a ∉ M.S → M.h a = M.h₀) {e : PExp} {P : Char → Bool}
    (hbody : ∀ q q', M.body (e, q, q') = M.step1 P q q') {q : St} {u : List Char} (hq : q ∈ M.stList)
    (he : e ∈ M.elist) :
    (M.img q u = [] → M.CSpec e q u .fail) ∧
    (∀ d r, M.img q u = d :: r → P d = false → M.CSpec e q u .fail) ∧
    (∀ d r t, M.img q u = d :: r → P d = true → M.CSpec e q u (.ok t r)) := by
  have hfun : (fun q' => M.body (e, q, q')) = M.step1 P q := funext (hbody q)
  rcases M.step1_spec hne hS (G := M.grammar) P hq with ⟨himg, hmiss⟩ | ⟨d, q₁, u₁, himg, _, hhit, hmiss⟩
  · refine ⟨fun _ => M.misses_N he hq (hfun ▸ hmiss), fun d r h => ?_, fun d r t h => ?_⟩
    · rw [himg] at h; cases h
    · rw [himg] at h; cases h
  · refine ⟨fun h => ?_, fun d' r h hP => ?_, fun d' r t h hP => ?_⟩
    · rw [himg] at h; cases h
    · rw [himg] at h; injection h with h1 _; subst h1
      exact M.misses_N he hq (hfun ▸ hmiss hP)
    · rw [himg] at h; injection h with h1 h2; subst h1; subst h2
      exact ⟨q₁, u₁, rfl, M.hits_N he hq (hfun ▸ hhit hP)⟩

/-- **Completeness.** -/
theorem complete (hne : ∀ a, M.h a ≠ []) (hS : ∀ a, a ∉ M.S → M.h a = M.h₀) {e : PExp} {x : List Char}
    {o : Outcome} (hd : Derives M.g e x o) :
    ∀ q u, q ∈ M.stList → x = M.img q u → e ∈ M.elist → M.CSpec e q u o := by
  induction hd with
  | eps input =>
    intro q u hq hx he
    exact ⟨q, u, hx, M.hits_N he hq (guardEq_hits hq)⟩
  | anyOk c rest =>
    intro q u hq hx he
    exact (M.atom_spec hne hS (P := fun _ => true) (fun _ _ => rfl) hq he).2.2 c rest _ hx.symm rfl
  | anyFail =>
    intro q u hq hx he
    exact (M.atom_spec hne hS (P := fun _ => true) (fun _ _ => rfl) hq he).1 hx.symm
  | chrOk c d rest hcd =>
    intro q u hq hx he
    exact (M.atom_spec hne hS (P := beqChar c) (fun _ _ => rfl) hq he).2.2 d rest _ hx.symm hcd
  | chrFail c d rest hcd =>
    intro q u hq hx he
    exact (M.atom_spec hne hS (P := beqChar c) (fun _ _ => rfl) hq he).2.1 d rest hx.symm hcd
  | chrEmpty c =>
    intro q u hq hx he
    exact (M.atom_spec hne hS (P := beqChar c) (fun _ _ => rfl) hq he).1 hx.symm
  | rangeOk lo hi d rest hc =>
    intro q u hq hx he
    exact (M.atom_spec hne hS (P := fun d => leChar lo d && leChar d hi) (fun _ _ => rfl) hq he).2.2
      d rest _ hx.symm hc
  | rangeFail lo hi d rest hc =>
    intro q u hq hx he
    exact (M.atom_spec hne hS (P := fun d => leChar lo d && leChar d hi) (fun _ _ => rfl) hq he).2.1
      d rest hx.symm hc
  | rangeEmpty lo hi =>
    intro q u hq hx he
    exact (M.atom_spec hne hS (P := fun d => leChar lo d && leChar d hi) (fun _ _ => rfl) hq he).1 hx.symm
  | litOk s input rest hs =>
    intro q u hq hx he
    subst hx
    obtain ⟨q₁, u₁, hr, hh⟩ := (M.litT_spec hne hS (G := M.grammar) s q u hq).1 rest hs
    exact ⟨q₁, u₁, hr, M.hits_N he hq hh⟩
  | litFail s input hs =>
    intro q u hq hx he
    subst hx
    exact M.misses_N he hq ((M.litT_spec hne hS (G := M.grammar) s q u hq).2 hs)
  | ntOk i r input rest t hr _ ih =>
    intro q u hq hx he
    have hfun : (fun q' => M.body (.nt i, q, q')) = M.NF r q := by
      funext q'; simp only [body, hr]; rfl
    obtain ⟨q₁, u₁, hr', hh⟩ := ih q u hq hx (M.elist_rule hr)
    exact ⟨q₁, u₁, hr', M.hits_N he hq (hfun ▸ hh)⟩
  | ntFail i r input hr _ ih =>
    intro q u hq hx he
    have hfun : (fun q' => M.body (.nt i, q, q')) = M.NF r q := by
      funext q'; simp only [body, hr]; rfl
    exact M.misses_N he hq (hfun ▸ ih q u hq hx (M.elist_rule hr))
  | ntMissing i input hr =>
    intro q u hq _ he
    exact M.misses_N he hq (fun q' _ => by simp only [body, hr]; exact phFail_fail u)
  | seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ _ _ ih₁ ih₂ =>
    intro q u hq hx he
    obtain ⟨q₁, u₁, hr₁, h₁⟩ := ih₁ q u hq hx (M.elist_seq he).1
    obtain ⟨q₂, u₂, hr₂, h₂⟩ := ih₂ q₁ u₁ h₁.1 hr₁ (M.elist_seq he).2
    exact ⟨q₂, u₂, hr₂, M.hits_N he hq (chainSeq_hits (B := fun y => M.NF e₂ y) h₁ h₂)⟩
  | seqFail₁ e₁ e₂ input _ ih₁ =>
    intro q u hq hx he
    exact M.misses_N he hq (chainSeq_misses₁ (B := fun y => M.NF e₂ y) (ih₁ q u hq hx (M.elist_seq he).1))
  | seqFail₂ e₁ e₂ input rest₁ t₁ _ _ ih₁ ih₂ =>
    intro q u hq hx he
    obtain ⟨q₁, u₁, hr₁, h₁⟩ := ih₁ q u hq hx (M.elist_seq he).1
    exact M.misses_N he hq
      (chainSeq_misses₂ (B := fun y => M.NF e₂ y) h₁ (ih₂ q₁ u₁ h₁.1 hr₁ (M.elist_seq he).2))
  | altL e₁ e₂ input rest t _ ih =>
    intro q u hq hx he
    obtain ⟨q₁, u₁, hr₁, h₁⟩ := ih q u hq hx (M.elist_alt he).1
    refine ⟨q₁, u₁, hr₁, M.hits_N he hq (Hits.mk' h₁.1 ?_ (fun q' hq' hne' => ?_))⟩
    · obtain ⟨t', ht'⟩ := h₁.ok
      exact ⟨_, .altL _ _ _ _ _ ht'⟩
    · exact .altFail _ _ _ (h₁.fail hq' hne') (.seqFail₁ _ _ _ (M.FL_fail h₁))
  | altR e₁ e₂ input rest t _ _ ih₁ ih₂ =>
    intro q u hq hx he
    have m₁ := ih₁ q u hq hx (M.elist_alt he).1
    obtain ⟨q₂, u₂, hr₂, h₂⟩ := ih₂ q u hq hx (M.elist_alt he).2
    refine ⟨q₂, u₂, hr₂, M.hits_N he hq (Hits.mk' h₂.1 ?_ (fun q' hq' hne' => ?_))⟩
    · obtain ⟨t', ht'⟩ := h₂.ok
      exact ⟨_, .altR _ _ _ _ _ (m₁ q₂ h₂.1) (.seqOk _ _ _ _ _ _ _ (M.FL_ok m₁) ht')⟩
    · exact .altFail _ _ _ (m₁ q' hq') (.seqFail₂ _ _ _ _ _ (M.FL_ok m₁) (h₂.fail hq' hne'))
  | altFail e₁ e₂ input _ _ ih₁ ih₂ =>
    intro q u hq hx he
    have m₁ := ih₁ q u hq hx (M.elist_alt he).1
    have m₂ := ih₂ q u hq hx (M.elist_alt he).2
    exact M.misses_N he hq (fun q' hq' => .altFail _ _ _ (m₁ q' hq') (.seqFail₂ _ _ _ _ _ (M.FL_ok m₁) (m₂ q' hq')))
  | starNil e input _ ih =>
    intro q u hq hx he
    have m := ih q u hq hx (M.elist_star he)
    have mc := chainSeq_misses₁ (B := fun y => M.NF (.star e) y) m
    refine ⟨q, u, hx, M.hits_N he hq (Hits.mk' hq ?_ (fun q' hq' hne' => ?_))⟩
    · exact ⟨_, .altR _ _ _ _ _ (mc q hq) (.seqOk _ _ _ _ _ _ _ (M.FL_ok m) (guardEq_ok q u))⟩
    · exact .altFail _ _ _ (mc q' hq') (.seqFail₂ _ _ _ _ _ (M.FL_ok m) (guardEq_fail (fun h => hne' h.symm) u))
  | starCons e input rest rest' t ts _ _ ih₁ ih₂ =>
    intro q u hq hx he
    obtain ⟨q₁, u₁, hr₁, h₁⟩ := ih₁ q u hq hx (M.elist_star he)
    obtain ⟨q₂, u₂, hr₂, h₂⟩ := ih₂ q₁ u₁ h₁.1 hr₁ he
    have hc := chainSeq_hits (B := fun y => M.NF (.star e) y) h₁ h₂
    refine ⟨q₂, u₂, hr₂, M.hits_N he hq (Hits.mk' h₂.1 ?_ (fun q' hq' hne' => ?_))⟩
    · obtain ⟨t', ht'⟩ := hc.ok
      exact ⟨_, .altL _ _ _ _ _ ht'⟩
    · exact .altFail _ _ _ (hc.fail hq' hne') (.seqFail₁ _ _ _ (M.FL_fail h₁))
  | notOk e input rest t _ ih =>
    intro q u hq hx he
    obtain ⟨_, _, _, h₁⟩ := ih q u hq hx (M.elist_notP he)
    exact M.misses_N he hq (fun q' _ => .seqFail₁ _ _ _ (M.FL_fail h₁))
  | notFail e input _ ih =>
    intro q u hq hx he
    have m := ih q u hq hx (M.elist_notP he)
    refine ⟨q, u, hx, M.hits_N he hq (Hits.mk' hq ?_ (fun q' _ hne' => ?_))⟩
    · exact ⟨_, .seqOk _ _ _ _ _ _ _ (M.FL_ok m) (guardEq_ok q u)⟩
    · exact .seqFail₂ _ _ _ _ _ (M.FL_ok m) (guardEq_fail (fun h => hne' h.symm) u)

end PhSim

end Shallot.Cfg
