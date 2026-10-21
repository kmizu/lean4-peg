import Shallot.Peg.Total.SpecSeq
import Shallot.Peg.Total.SpecStar
import Shallot.Peg.Undecidable.FordCor
import Cfg.OpenProblems

/-!
# Every PEG language is the language of a complete PEG

The specification (`Spec.lean`) holds for every expression, position and open set (`spec_all`), by induction on
the length of the input, then on the number of rules not yet open (`free`), then on the expression. From it:

* the transformed grammar `newG g` accepts exactly what `g` accepts (`newG_accepts`): from the empty open set,
  checked derivations are derivations (`derives_ds`, `ds_derives`);
* every nonterminal of `newG g` terminates on every input (`newG_allNtTotal`), in particular the start rule
  (`newG_complete`).

So every PEG language — the grammar may loop on some inputs, which are then not accepted — is the language of a
complete PEG (`isPEL_iff_isTotalPEL`), even of one all of whose nonterminals terminate everywhere
(`isPEL_allNtTotal`). The construction is Birman's run-time circularity check as Ford (POPL 2004, §5) describes it.
-/

namespace Shallot

/-- Rules beyond the end of the list are missing. -/
theorem ruleAt_none_of_ge {l : List PExp} {i : Nat} (h : ¬ i < l.length) : ruleAt l i = none := by
  rw [ruleAt_eq]; simp; omega

/-- **The specification holds everywhere**, for every open set `S < 2 ^ n`. -/
theorem spec_all (g : Grammar) :
    ∀ M (x : List Char), x.length < M → ∀ F S, free g.rules.length S < F → S < 2 ^ g.rules.length →
      ∀ e, Spec g (newG g) (tr g.rules.length e S) S e x := by
  intro M
  induction M with
  | zero => intro x hx; omega
  | succ M ihM =>
    intro x hx F
    have h0 : ∀ e y, y.length < x.length → Spec g (newG g) (tr g.rules.length e 0) 0 e y := fun e y hy =>
      ihM y (by omega) (free g.rules.length 0 + 1) 0 (by omega) (Nat.two_pow_pos _) e
    induction F with
    | zero => intro S hF; omega
    | succ F ihF =>
      intro S hF hS e
      induction e with
      | eps => exact spec_eps _ _ _ _
      | any => exact spec_any _ _ _ _
      | chr c => exact spec_chr _ _ _ _ _
      | range lo hi => exact spec_range _ _ _ _ _ _
      | lit s => exact spec_lit _ _ _ _ _
      | nt A =>
        show Spec g (newG g) (ntT g.rules.length A S) S (.nt A) x
        unfold ntT
        by_cases hA : A < g.rules.length
        · rw [if_pos hA]
          obtain ⟨e, he⟩ := ruleAt_lt_length hA
          cases hm : S.testBit A with
          | true => exact spec_nt_open _ _ x he hm
          | false =>
            exact spec_nt_call he hm (newG_rule_idx (k := 0) (by omega) hA hS he)
              (newG_rule_idx (k := 1) (by omega) hA hS he) (newG_rule_idx (k := 2) (by omega) hA hS he)
              (ihF (ins S A) (by have := free_ins_lt hA hm; omega) (ins_lt hS hA) e)
        · rw [if_neg hA]
          exact spec_nt_missing _ _ x (ruleAt_none_of_ge hA)
      | seq a b iha ihb => exact spec_seq iha ihb (fun r hr => h0 b r hr)
      | alt a b iha ihb => exact spec_alt iha ihb
      | notP a iha => exact spec_not iha
      | star a iha => exact spec_star iha (fun y hy => h0 a y hy)

/-- The specification of the start call. -/
theorem spec_start (g : Grammar) (w : List Char) :
    Spec g (newG g) (tr g.rules.length (.nt g.start) 0) 0 (.nt g.start) w :=
  spec_all g (w.length + 1) w (by omega) (free g.rules.length 0 + 1) 0 (by omega) (Nat.two_pow_pos _) _

/-- Under the specification, `r` has an outcome. -/
theorem r_total {G : Grammar} {T : Tr} {x : List Char} {c : Cl} (h : Good G T x c) : ∃ o, Derives G T.r x o := by
  cases c with
  | okE => obtain ⟨t, hr⟩ := r_okE h; exact ⟨_, hr⟩
  | okC r => obtain ⟨t, hr⟩ := r_okC h; exact ⟨_, hr⟩
  | fl => exact ⟨_, r_fl h⟩
  | lp => exact ⟨_, r_lp h⟩

/-- Under the specification, each of the three parts has an outcome. -/
theorem comp_total {G : Grammar} {T : Tr} {x : List Char} {c : Cl} (h : Good G T x c) :
    ∀ k, ∃ o, Derives G (comp k T) x o := by
  have hz : ∃ o, Derives G T.z x o := by
    cases c with
    | okE => obtain ⟨⟨t, d⟩, -, -⟩ := h; exact ⟨_, d⟩
    | okC r => exact ⟨_, h.1⟩
    | fl => exact ⟨_, h.1⟩
    | lp => exact ⟨_, h.1⟩
  have hp : ∃ o, Derives G T.p x o := by
    cases c with
    | okE => exact ⟨_, h.2.1⟩
    | okC r => obtain ⟨-, ⟨t, d⟩, -⟩ := h; exact ⟨_, d⟩
    | fl => exact ⟨_, h.2.1⟩
    | lp => exact ⟨_, h.2.1⟩
  have hl : ∃ o, Derives G T.l x o := by
    cases c with
    | okE => exact ⟨_, h.2.2⟩
    | okC r => exact ⟨_, h.2.2⟩
    | fl => exact ⟨_, h.2.2⟩
    | lp => obtain ⟨-, -, r, t, d⟩ := h; exact ⟨_, d⟩
  intro k
  match k with
  | 0 => exact hz
  | 1 => exact hp
  | _ + 2 => exact hl

/-- A nonterminal whose rule has an outcome has one. -/
theorem nt_total {G : Grammar} {i : Nat} {e : PExp} {x : List Char} (hr : ruleAt G.rules i = some e)
    (h : ∃ o, Derives G e x o) : ∃ o, Derives G (.nt i) x o := by
  obtain ⟨o, d⟩ := h
  cases o with
  | ok t r => exact ⟨_, .ntOk _ _ _ _ _ hr d⟩
  | fail => exact ⟨_, .ntFail _ _ _ hr d⟩

/-- **Every nonterminal of the transformed grammar terminates on every input.** -/
theorem newG_allNtTotal (g : Grammar) (i : Nat) (w : List Char) : ∃ o, Derives (newG g) (.nt i) w o := by
  rcases Nat.lt_trichotomy i (bound g) with hi | hi | hi
  · obtain ⟨hA, hS⟩ := decode_lt hi
    obtain ⟨e, he⟩ := ruleAt_lt_length hA
    obtain ⟨c, -, hG⟩ := spec_all g (w.length + 1) w (by omega) (free g.rules.length (ins ((i / 3) / g.rules.length)
      ((i / 3) % g.rules.length)) + 1) _ (by omega) (ins_lt hS hA) e
    refine nt_total (newG_rule_lt hi) ?_
    simp only [ruleOf, body_eq he]
    exact comp_total hG _
  · subst hi
    obtain ⟨c, -, hG⟩ := spec_start g w
    exact nt_total (newG_rule_start g) (r_total hG)
  · exact ⟨_, .ntMissing _ _ (newG_rule_gt hi)⟩

/-- **The transformed grammar is complete.** -/
theorem newG_complete (g : Grammar) : Complete (newG g) := fun w => newG_allNtTotal g _ w

/-- **The transformed grammar accepts exactly what the original accepts** (whole input). -/
theorem newG_accepts (g : Grammar) (w : List Char) :
    (∃ t, Derives (newG g) (.nt (newG g).start) w (.ok t [])) ↔ ∃ t, Derives g (.nt g.start) w (.ok t []) := by
  obtain ⟨c, hB, hG⟩ := spec_start g w
  constructor
  · rintro ⟨t, h⟩
    cases h with
    | ntOk _ e _ _ _ hr hd =>
      have hr' := newG_rule_start g
      simp only [newG] at hr hr' ⊢
      rw [hr'] at hr; cases hr
      cases c with
      | okE =>
        obtain ⟨t', d⟩ := r_okE hG
        cases derives_det hd d
        obtain ⟨t₀, h₀⟩ := hB
        exact ⟨_, ds_derives h₀⟩
      | okC r =>
        obtain ⟨t', d⟩ := r_okC hG
        cases derives_det hd d
        obtain ⟨-, t₀, h₀⟩ := hB
        exact ⟨_, ds_derives h₀⟩
      | fl => cases derives_det hd (r_fl hG)
      | lp => cases derives_det hd (r_lp hG)
  · rintro ⟨t, h⟩
    have hD := derives_ds h
    have hR : OkD (newG g) (tr g.rules.length (.nt g.start) 0).r w [] := by
      cases c with
      | okE =>
        obtain ⟨t₀, h₀⟩ := hB
        cases ds_det hD h₀
        exact r_okE hG
      | okC r =>
        obtain ⟨-, t₀, h₀⟩ := hB
        cases ds_det hD h₀
        exact r_okC hG
      | fl => cases ds_det hD hB
      | lp => exact absurd hD (hB _)
    obtain ⟨t', d⟩ := hR
    exact ⟨_, .ntOk _ _ _ _ _ (newG_rule_start g) d⟩

/-! ## The language classes -/

/-- Languages of complete grammars. -/
def IsTotalPEL (L : Shallot.Cfg.Language) : Prop :=
  ∃ g : Grammar, Complete g ∧ ∀ w, L w ↔ ∃ t, Derives g (.nt g.start) w (.ok t [])

/-- **Every PEG language has a grammar all of whose nonterminals terminate on every input.** -/
theorem isPEL_allNtTotal {L : Shallot.Cfg.Language} (h : Shallot.Cfg.IsPEL L) :
    ∃ g : Grammar, (∀ (i : Nat) (w : List Char), ∃ o, Derives g (.nt i) w o) ∧
      ∀ w, L w ↔ ∃ t, Derives g (.nt g.start) w (.ok t []) := by
  obtain ⟨g, hg⟩ := h
  exact ⟨newG g, newG_allNtTotal g, fun w => (hg w).trans (newG_accepts g w).symm⟩

/-- **The PEG languages are the languages of complete PEGs.** -/
theorem isPEL_iff_isTotalPEL (L : Shallot.Cfg.Language) : Shallot.Cfg.IsPEL L ↔ IsTotalPEL L := by
  constructor
  · intro h
    obtain ⟨g, hall, hg⟩ := isPEL_allNtTotal h
    exact ⟨g, fun w => hall _ w, hg⟩
  · rintro ⟨g, -, hg⟩
    exact ⟨g, hg⟩

end Shallot
