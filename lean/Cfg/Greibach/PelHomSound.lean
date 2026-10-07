import Cfg.Greibach.PelHomComplete

/-!
# Soundness of the simulation: it terminates only where `g` does

If a call `(e, q, q')` of the simulating grammar has an outcome, then `e` has an outcome on the image
`img q u` (`sound`). By strong induction on the interpreter's fuel: every body first runs the calls that
evaluating `e` needs, at smaller fuel; which later calls run is read off from completeness.
-/

namespace Shallot.Cfg

open Shallot (Grammar Derives PExp PTree Outcome ruleAt beqChar leChar stripPrefix? pegRun pegRun_sound
  pegRun_complete derives_det starNeverFails)

section Run

variable {G : Grammar}

/-- Running a sequence runs its first part, and its second part after a success. -/
theorem run_seq {n : Nat} {A B : PExp} {u : List Char} {o : Outcome} (h : pegRun G n (.seq A B) u = some o) :
    ∃ m, m < n ∧ ∃ oA, pegRun G m A u = some oA ∧ ∀ t r, oA = .ok t r → ∃ oB, pegRun G m B r = some oB := by
  cases n with
  | zero => simp [pegRun] at h
  | succ n =>
    simp only [pegRun] at h
    refine ⟨n, Nat.lt_succ_self n, ?_⟩
    split at h
    · next t₁ r₁ hA =>
      refine ⟨_, hA, fun t r he => ?_⟩
      cases he
      split at h
      · next hB => exact ⟨_, hB⟩
      · next hB => exact ⟨_, hB⟩
      · cases h
    · next hA => exact ⟨_, hA, fun _ _ he => by cases he⟩
    · cases h

/-- Running a choice runs its first branch, and its second branch after a failure. -/
theorem run_alt {n : Nat} {A B : PExp} {u : List Char} {o : Outcome} (h : pegRun G n (.alt A B) u = some o) :
    ∃ m, m < n ∧ ∃ oA, pegRun G m A u = some oA ∧ (oA = .fail → ∃ oB, pegRun G m B u = some oB) := by
  cases n with
  | zero => simp [pegRun] at h
  | succ n =>
    simp only [pegRun] at h
    refine ⟨n, Nat.lt_succ_self n, ?_⟩
    split at h
    · next hA => exact ⟨_, hA, fun he => by cases he⟩
    · next hA =>
      refine ⟨_, hA, fun _ => ?_⟩
      split at h
      · next hB => exact ⟨_, hB⟩
      · next hB => exact ⟨_, hB⟩
      · cases h
    · cases h

/-- Running a not-predicate runs its operand. -/
theorem run_not {n : Nat} {A : PExp} {u : List Char} {o : Outcome} (h : pegRun G n (.notP A) u = some o) :
    ∃ m, m < n ∧ ∃ oA, pegRun G m A u = some oA := by
  cases n with
  | zero => simp [pegRun] at h
  | succ n =>
    simp only [pegRun] at h
    refine ⟨n, Nat.lt_succ_self n, ?_⟩
    split at h
    · next hA => exact ⟨_, hA⟩
    · next hA => exact ⟨_, hA⟩
    · cases h

/-- Running a call runs its rule. -/
theorem run_nt {n i : Nat} {r : PExp} {u : List Char} {o : Outcome} (h : pegRun G n (.nt i) u = some o)
    (hr : ruleAt G.rules i = some r) : ∃ m, m < n ∧ ∃ o', pegRun G m r u = some o' := by
  cases n with
  | zero => simp [pegRun] at h
  | succ n =>
    simp only [pegRun, hr] at h
    refine ⟨n, Nat.lt_succ_self n, ?_⟩
    split at h
    · next hA => exact ⟨_, hA⟩
    · next hA => exact ⟨_, hA⟩
    · cases h

/-- A run agrees with every derivation. -/
theorem run_eq {n : Nat} {A : PExp} {u : List Char} {o o' : Outcome} (h : pegRun G n A u = some o)
    (hd : Derives G A u o') : o = o' :=
  derives_det (pegRun_sound h) hd

/-- Running an ordered choice over a list runs its first member. -/
theorem run_chain_first {α : Type} {F : α → PExp} {y : α} {l : List α} {n : Nat} {u : List Char}
    {o : Outcome} (h : pegRun G n (chain (y :: l) F) u = some o) : ∃ m, m < n ∧ ∃ o', pegRun G m (F y) u = some o' := by
  obtain ⟨m, hm, oA, hA, _⟩ := run_alt h
  exact ⟨m, hm, oA, hA⟩

/-- Running an ordered choice over a list runs the member `y₁` when every member before it fails. -/
theorem run_chain_at {α : Type} {F : α → PExp} {u : List Char} {y₁ : α} :
    ∀ {l : List α} {n : Nat} {o : Outcome}, pegRun G n (chain l F) u = some o → y₁ ∈ l →
      (∀ y ∈ l, y ≠ y₁ → Derives G (F y) u .fail) → ∃ m, m < n ∧ ∃ o', pegRun G m (F y₁) u = some o'
  | [], _, _, _, hm, _ => absurd hm List.not_mem_nil
  | y :: l, n, o, h, hm, hf => by
    obtain ⟨m, hmn, oA, hA, hB⟩ := run_alt h
    rcases Classical.em (y = y₁) with rfl | hy
    · exact ⟨m, hmn, oA, hA⟩
    · have hl : y₁ ∈ l := by
        rcases List.mem_cons.mp hm with h | h
        · exact absurd h.symm hy
        · exact h
      have hfail : oA = .fail := run_eq hA (hf y List.mem_cons_self hy)
      obtain ⟨oB, hB'⟩ := hB hfail
      obtain ⟨m', hm', o', h'⟩ := run_chain_at hB' hl (fun z hz hne => hf z (List.mem_cons_of_mem y hz) hne)
      exact ⟨m', by omega, o', h'⟩

end Run

/-- `any`, letters, classes and literals always have an outcome. -/
theorem atom_total {G : Grammar} (y : List Char) :
    (∃ o, Derives G .any y o) ∧ (∀ c, ∃ o, Derives G (.chr c) y o) ∧
      (∀ lo hi, ∃ o, Derives G (.range lo hi) y o) ∧ (∀ s, ∃ o, Derives G (.lit s) y o) := by
  refine ⟨?_, fun c => ?_, fun lo hi => ?_, fun s => ?_⟩
  · cases y with
    | nil => exact ⟨_, .anyFail⟩
    | cons d r => exact ⟨_, .anyOk d r⟩
  · cases y with
    | nil => exact ⟨_, .chrEmpty c⟩
    | cons d r =>
      cases hb : beqChar c d
      · exact ⟨_, .chrFail c d r hb⟩
      · exact ⟨_, .chrOk c d r hb⟩
  · cases y with
    | nil => exact ⟨_, .rangeEmpty lo hi⟩
    | cons d r =>
      cases hb : (leChar lo d && leChar d hi)
      · exact ⟨_, .rangeFail lo hi d r hb⟩
      · exact ⟨_, .rangeOk lo hi d r hb⟩
  · cases hs : stripPrefix? s y with
    | none => exact ⟨_, .litFail s y hs⟩
    | some r => exact ⟨_, .litOk s y r hs⟩

namespace PhSim

variable (M : PhSim)

/-- The fuel statement of soundness. -/
def SoundAt (n : Nat) : Prop :=
  ∀ e q q' u o, e ∈ M.elist → q ∈ M.stList → q' ∈ M.stList → pegRun M.grammar n (M.N (e, q, q')) u = some o →
    ∃ o', Derives M.g e (M.img q u) o'

/-- An outcome of `e` from `q` as a success or a failure, read off by completeness. -/
theorem outcome_cases (hne : ∀ a, M.h a ≠ []) (hS : ∀ a, a ∉ M.S → M.h a = M.h₀) {e : PExp} {q : St}
    {u : List Char} {o : Outcome} (hq : q ∈ M.stList) (he : e ∈ M.elist) (hd : Derives M.g e (M.img q u) o) :
    (o = .fail ∧ Misses M.grammar M.stList (M.NF e q) u) ∨
      ∃ t q₁ u₁, o = .ok t (M.img q₁ u₁) ∧ Hits M.grammar M.stList (M.NF e q) u q₁ u₁ := by
  have hc := M.complete hne hS hd q u hq rfl he
  cases o with
  | fail => exact Or.inl ⟨rfl, hc⟩
  | ok t r =>
    obtain ⟨q₁, u₁, hr, hh⟩ := hc
    exact Or.inr ⟨t, q₁, u₁, hr ▸ rfl, hh⟩

/-- Soundness for a sequence. -/
theorem sound_seq (hne : ∀ a, M.h a ≠ []) (hS : ∀ a, a ∉ M.S → M.h a = M.h₀) {n : Nat}
    (ih : ∀ m, m ≤ n → M.SoundAt m) {e₁ e₂ : PExp} {q q' : St} {u : List Char} {o : Outcome}
    (he : PExp.seq e₁ e₂ ∈ M.elist) (hq : q ∈ M.stList) (hq' : q' ∈ M.stList)
    (h : pegRun M.grammar n (M.body (.seq e₁ e₂, q, q')) u = some o) :
    ∃ o', Derives M.g (.seq e₁ e₂) (M.img q u) o' := by
  have he₁ := (M.elist_seq he).1
  have he₂ := (M.elist_seq he).2
  have h' : pegRun M.grammar n (chain M.stList (fun y => .seq (M.N (e₁, q, y)) (M.N (e₂, y, q')))) u = some o := h
  obtain ⟨m₁, hm₁, _, h₁⟩ := run_chain_first h'
  obtain ⟨m₂, hm₂, _, h₂, _⟩ := run_seq h₁
  obtain ⟨o₁, hd₁⟩ := ih m₂ (by omega) e₁ q none u _ he₁ hq M.none_mem_stList h₂
  rcases M.outcome_cases hne hS hq he₁ hd₁ with ⟨rfl, _⟩ | ⟨t, q₁, u₁, rfl, H⟩
  · exact ⟨_, .seqFail₁ _ _ _ hd₁⟩
  · obtain ⟨m₃, hm₃, _, h₃⟩ := run_chain_at (y₁ := q₁) h' H.1
      (fun y hy hne' => .seqFail₁ _ _ _ (H.fail hy hne'))
    obtain ⟨m₄, hm₄, oA, h₄, hB⟩ := run_seq h₃
    obtain ⟨t', ht'⟩ := H.ok
    obtain ⟨oB, h₅⟩ := hB _ _ (run_eq h₄ ht')
    obtain ⟨o₂, hd₂⟩ := ih m₄ (by omega) e₂ q₁ q' u₁ _ he₂ H.1 hq' h₅
    cases o₂ with
    | fail => exact ⟨_, .seqFail₂ _ _ _ _ _ hd₁ hd₂⟩
    | ok t₂ r₂ => exact ⟨_, .seqOk _ _ _ _ _ _ _ hd₁ hd₂⟩

/-- Soundness for a choice. -/
theorem sound_alt (hne : ∀ a, M.h a ≠ []) (hS : ∀ a, a ∉ M.S → M.h a = M.h₀) {n : Nat}
    (ih : ∀ m, m ≤ n → M.SoundAt m) {e₁ e₂ : PExp} {q q' : St} {u : List Char} {o : Outcome}
    (he : PExp.alt e₁ e₂ ∈ M.elist) (hq : q ∈ M.stList) (hq' : q' ∈ M.stList)
    (h : pegRun M.grammar n (M.body (.alt e₁ e₂, q, q')) u = some o) :
    ∃ o', Derives M.g (.alt e₁ e₂) (M.img q u) o' := by
  have he₁ := (M.elist_alt he).1
  have he₂ := (M.elist_alt he).2
  have h' : pegRun M.grammar n (.alt (M.N (e₁, q, q')) (.seq (M.FL e₁ q) (M.N (e₂, q, q')))) u = some o := h
  obtain ⟨m₁, hm₁, oA, h₁, hB⟩ := run_alt h'
  obtain ⟨o₁, hd₁⟩ := ih m₁ (by omega) e₁ q q' u _ he₁ hq hq' h₁
  rcases M.outcome_cases hne hS hq he₁ hd₁ with ⟨rfl, H⟩ | ⟨t, q₁, u₁, rfl, _⟩
  · obtain ⟨oB, h₂⟩ := hB (run_eq h₁ (H q' hq'))
    obtain ⟨m₃, hm₃, oF, h₃, hC⟩ := run_seq h₂
    obtain ⟨oC, h₄⟩ := hC _ _ (run_eq h₃ (M.FL_ok H))
    obtain ⟨o₂, hd₂⟩ := ih m₃ (by omega) e₂ q q' u _ he₂ hq hq' h₄
    cases o₂ with
    | fail => exact ⟨_, .altFail _ _ _ hd₁ hd₂⟩
    | ok t₂ r₂ => exact ⟨_, .altR _ _ _ _ _ hd₁ hd₂⟩
  · exact ⟨_, .altL _ _ _ _ _ hd₁⟩

/-- Soundness for a repetition. -/
theorem sound_star (hne : ∀ a, M.h a ≠ []) (hS : ∀ a, a ∉ M.S → M.h a = M.h₀) {n : Nat}
    (ih : ∀ m, m ≤ n → M.SoundAt m) {e : PExp} {q q' : St} {u : List Char} {o : Outcome}
    (he : PExp.star e ∈ M.elist) (hq : q ∈ M.stList) (hq' : q' ∈ M.stList)
    (h : pegRun M.grammar n (M.body (.star e, q, q')) u = some o) :
    ∃ o', Derives M.g (.star e) (M.img q u) o' := by
  have he₁ := M.elist_star he
  have h' : pegRun M.grammar n (.alt (chain M.stList (fun y => .seq (M.N (e, q, y)) (M.N (.star e, y, q'))))
      (.seq (M.FL e q) (guardEq q q'))) u = some o := h
  obtain ⟨m₁, hm₁, _, h₁, _⟩ := run_alt h'
  obtain ⟨m₂, hm₂, _, h₂⟩ := run_chain_first h₁
  obtain ⟨m₃, hm₃, _, h₃, _⟩ := run_seq h₂
  obtain ⟨o₁, hd₁⟩ := ih m₃ (by omega) e q none u _ he₁ hq M.none_mem_stList h₃
  rcases M.outcome_cases hne hS hq he₁ hd₁ with ⟨rfl, _⟩ | ⟨t, q₁, u₁, rfl, H⟩
  · exact ⟨_, .starNil _ _ hd₁⟩
  · obtain ⟨m₄, hm₄, _, h₄⟩ := run_chain_at (y₁ := q₁) h₁ H.1
      (fun y hy hne' => .seqFail₁ _ _ _ (H.fail hy hne'))
    obtain ⟨m₅, hm₅, oA, h₅, hB⟩ := run_seq h₄
    obtain ⟨t', ht'⟩ := H.ok
    obtain ⟨oB, h₆⟩ := hB _ _ (run_eq h₅ ht')
    obtain ⟨o₂, hd₂⟩ := ih m₅ (by omega) (.star e) q₁ q' u₁ _ he H.1 hq' h₆
    cases o₂ with
    | fail => exact absurd rfl (starNeverFails hd₂)
    | ok t₂ r₂ => exact ⟨_, .starCons _ _ _ _ _ _ hd₁ hd₂⟩

/-- Soundness for a not-predicate. -/
theorem sound_notP {n : Nat} (ih : ∀ m, m ≤ n → M.SoundAt m) {e : PExp} {q q' : St} {u : List Char}
    {o : Outcome} (he : PExp.notP e ∈ M.elist) (hq : q ∈ M.stList)
    (h : pegRun M.grammar n (M.body (.notP e, q, q')) u = some o) :
    ∃ o', Derives M.g (.notP e) (M.img q u) o' := by
  have he₁ := M.elist_notP he
  have h' : pegRun M.grammar n (.seq (.notP (chain M.stList (M.NF e q))) (guardEq q q')) u = some o := h
  obtain ⟨m₁, hm₁, _, h₁, _⟩ := run_seq h'
  obtain ⟨m₂, hm₂, _, h₂⟩ := run_not h₁
  obtain ⟨m₃, hm₃, _, h₃⟩ := run_chain_first h₂
  obtain ⟨o₁, hd₁⟩ := ih m₃ (by omega) e q none u _ he₁ hq M.none_mem_stList h₃
  cases o₁ with
  | fail => exact ⟨_, .notFail _ _ hd₁⟩
  | ok t r => exact ⟨_, .notOk _ _ _ _ hd₁⟩

/-- Soundness for a call of `g`. -/
theorem sound_nt {n : Nat} (ih : ∀ m, m ≤ n → M.SoundAt m) {i : Nat} {q q' : St} {u : List Char}
    {o : Outcome} (hq : q ∈ M.stList) (hq' : q' ∈ M.stList)
    (h : pegRun M.grammar n (M.body (.nt i, q, q')) u = some o) :
    ∃ o', Derives M.g (.nt i) (M.img q u) o' := by
  cases hr : ruleAt M.g.rules i with
  | none => exact ⟨_, .ntMissing _ _ hr⟩
  | some r =>
    have h' : pegRun M.grammar n (M.N (r, q, q')) u = some o := by
      simp only [body, hr] at h; exact h
    obtain ⟨o₁, hd₁⟩ := ih n (Nat.le_refl n) r q q' u o (M.elist_rule hr) hq hq' h'
    cases o₁ with
    | fail => exact ⟨_, .ntFail _ _ _ hr hd₁⟩
    | ok t r' => exact ⟨_, .ntOk _ _ _ _ _ hr hd₁⟩

/-- **Soundness**: a call with an outcome means an outcome of `g` on the image. -/
theorem sound (hne : ∀ a, M.h a ≠ []) (hS : ∀ a, a ∉ M.S → M.h a = M.h₀) (n : Nat) : M.SoundAt n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro e q q' u o he hq hq' h
    obtain ⟨m, hm, _, hb⟩ := run_nt h (M.ruleAt_code ((M.mem_items).mpr ⟨he, hq, hq'⟩))
    have ih' : ∀ k, k ≤ m → M.SoundAt k := fun k hk => ih k (by omega)
    cases e with
    | eps => exact ⟨_, .eps _⟩
    | any => exact (atom_total _).1
    | chr c => exact (atom_total _).2.1 c
    | range lo hi => exact (atom_total _).2.2.1 lo hi
    | lit s => exact (atom_total _).2.2.2 s
    | nt i => exact M.sound_nt ih' hq hq' hb
    | seq e₁ e₂ => exact M.sound_seq hne hS ih' he hq hq' hb
    | alt e₁ e₂ => exact M.sound_alt hne hS ih' he hq hq' hb
    | star e => exact M.sound_star hne hS ih' he hq hq' hb
    | notP e => exact M.sound_notP ih' he hq hb

end PhSim

end Shallot.Cfg
