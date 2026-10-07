import Shallot.Peg.Undecidable.FordIff
import Shallot.Peg.GrammarExtend

/-!
# Equivalence and completeness, from emptiness (Ford §3.4–3.5)

- **Equivalence**: a grammar has the language of the trivial grammar for the empty language (`emptyG`) iff its
  language is empty (`equiv_emptyG_iff`).
- **Completeness**: a grammar is complete when its start rule succeeds or fails on every input (`Complete`). Ford
  adds the rule `A' ← &e_S A'` as the new start (`loopG`): where `e_S` succeeds, `A'` loops; where it fails, `A'`
  fails. So `loopG g` is complete iff the language of `g` is empty (`loopG_complete_iff`) — **provided `g` itself is
  complete**, which Ford's argument uses without saying. Ford's grammar is complete (`fordG_complete`), so the
  argument applies to it.
-/

namespace Shallot

/-! ## Equivalence -/

/-- The trivial grammar for the empty language. -/
def emptyG : Grammar where
  rules := [.notP .eps]
  start := 0

theorem emptyG_not (w : List Char) : ¬ Accepts emptyG w := by
  rintro ⟨t, r, h⟩
  cases h with
  | ntOk _ e _ _ _ hr hd =>
    cases hr
    cases hd with
    | notFail _ _ h => cases h

/-- **A grammar has the empty grammar's language iff its language is empty.** -/
theorem equiv_emptyG_iff (g : Grammar) : (∀ w, Accepts g w ↔ Accepts emptyG w) ↔ ¬ ∃ w, Accepts g w := by
  constructor
  · rintro h ⟨w, hw⟩
    exact emptyG_not w ((h w).1 hw)
  · intro h w
    exact ⟨fun hw => absurd ⟨w, hw⟩ h, fun hw => absurd hw (emptyG_not w)⟩

/-! ## Completeness -/

/-- A grammar is complete when its start rule has a derivation on every input. -/
def Complete (g : Grammar) : Prop := ∀ w, ∃ o, Derives g (.nt g.start) w o

/-- The loop rule `A' ← &e_S A'`. -/
def loopRule (g : Grammar) : PExp := .seq (PExp.andP (.nt g.start)) (.nt g.rules.length)

/-- Ford's grammar `G'`: the rules of `g` and the loop rule as the new start. -/
def loopG (g : Grammar) : Grammar where
  rules := g.rules ++ [loopRule g]
  start := g.rules.length

theorem loopG_rule (g : Grammar) : ruleAt (loopG g).rules g.rules.length = some (loopRule g) := by
  have : ∀ (l : List PExp) (x : PExp), ruleAt (l ++ [x]) l.length = some x := by
    intro l x
    induction l with
    | nil => rfl
    | cons y l ih => simpa [ruleAt] using ih
  exact this g.rules (loopRule g)

section Loop

variable {g : Grammar} (hself : g.SelfContained) (hs : g.start < g.rules.length)
include hself hs

/-- Derivations of the start rule carry over to `loopG g`. -/
theorem loopG_start {w : List Char} {o : Outcome} (h : Derives g (.nt g.start) w o) :
    Derives (loopG g) (.nt g.start) w o :=
  derives_append_preserved [loopRule g] g.rules.length (e := .nt g.start) hs hself h

omit hself hs in
/-- Where the start rule succeeds, the loop rule has no derivation. -/
theorem loopG_no {x : List Char} {tS : PTree} {rS : List Char} (hx : Derives (loopG g) (.nt g.start) x (.ok tS rS)) :
    ∀ {e u o}, Derives (loopG g) e u o → (e = .nt g.rules.length ∨ e = loopRule g) → u = x → False := by
  intro e u o h
  induction h with
  | ntOk i e' _ _ _ hr _ ih =>
    intro he hu
    rcases he with he | he
    · cases he
      rw [loopG_rule] at hr; cases hr
      exact ih (.inr rfl) hu
    · cases he
  | ntFail i e' _ hr _ ih =>
    intro he hu
    rcases he with he | he
    · cases he
      rw [loopG_rule] at hr; cases hr
      exact ih (.inr rfl) hu
    · cases he
  | ntMissing i _ hr =>
    intro he _
    rcases he with he | he
    · cases he; rw [loopG_rule] at hr; cases hr
    · cases he
  | seqOk e₁ e₂ _ _ _ _ _ h₁ _ _ ih₂ =>
    intro he hu
    rcases he with he | he
    · cases he
    · cases he
      obtain ⟨_, rfl⟩ := andP_ok h₁
      exact ih₂ (.inl rfl) hu
  | seqFail₁ e₁ e₂ _ h₁ _ =>
    intro he hu
    rcases he with he | he
    · cases he
    · cases he; subst hu
      exact absurd (derives_det h₁ (andP_of hx)) (by simp)
  | seqFail₂ e₁ e₂ _ _ _ h₁ _ _ ih₂ =>
    intro he hu
    rcases he with he | he
    · cases he
    · cases he
      obtain ⟨_, rfl⟩ := andP_ok h₁
      exact ih₂ (.inl rfl) hu
  | _ => intro he _; rcases he with he | he <;> cases he

omit hself hs in
/-- Where the start rule fails, the loop rule fails. -/
theorem loopG_fail {x : List Char} (hx : Derives (loopG g) (.nt g.start) x .fail) :
    Derives (loopG g) (.nt (loopG g).start) x .fail :=
  .ntFail _ _ _ (loopG_rule g) (.seqFail₁ _ _ _ (.notOk _ _ _ _ (.notFail _ _ hx)))

/-- **Ford's grammar `G'` is complete iff the language of a complete `g` is empty.** -/
theorem loopG_complete_iff (hc : Complete g) : Complete (loopG g) ↔ ¬ ∃ w, Accepts g w := by
  constructor
  · rintro hc' ⟨x, t, r, hx⟩
    obtain ⟨o, ho⟩ := hc' x
    exact loopG_no (loopG_start hself hs hx) ho (.inl rfl) rfl
  · intro he x
    obtain ⟨o, ho⟩ := hc x
    cases o with
    | ok t r => exact absurd ⟨x, t, r, ho⟩ he
    | fail => exact ⟨_, loopG_fail (loopG_start hself hs ho)⟩

end Loop

/-! ## Ford's grammar is complete and self-contained -/

/-- An expression has a derivation on every input. -/
def Total (g : Grammar) (e : PExp) : Prop := ∀ u, ∃ o, Derives g e u o

theorem total_any (g : Grammar) : Total g .any := fun u => by
  cases u with
  | nil => exact ⟨_, .anyFail⟩
  | cons c u => exact ⟨_, .anyOk c u⟩

theorem total_notP {g : Grammar} {e : PExp} (h : Total g e) : Total g (.notP e) := fun u => by
  obtain ⟨o, ho⟩ := h u
  cases o with
  | ok t r => exact ⟨_, .notOk _ _ _ _ ho⟩
  | fail => exact ⟨_, .notFail _ _ ho⟩

theorem total_seq {g : Grammar} {e₁ e₂ : PExp} (h₁ : Total g e₁) (h₂ : Total g e₂) : Total g (.seq e₁ e₂) := fun u => by
  obtain ⟨o, ho⟩ := h₁ u
  cases o with
  | fail => exact ⟨_, .seqFail₁ _ _ _ ho⟩
  | ok t r =>
    obtain ⟨o', ho'⟩ := h₂ r
    cases o' with
    | fail => exact ⟨_, .seqFail₂ _ _ _ _ _ ho ho'⟩
    | ok t' r' => exact ⟨_, .seqOk _ _ _ _ _ _ _ ho ho'⟩

theorem total_andP {g : Grammar} {e : PExp} (h : Total g e) : Total g (PExp.andP e) := total_notP (total_notP h)

/-- **Ford's grammar is complete.** -/
theorem fordG_complete {C : PCP} (hC : C.NonemptyPairs) : Complete (fordG C) := by
  have hA : Total (fordG C) (.nt 1) := fun u => by
    obtain ⟨t, r, h⟩ := side_total (fordG_rule1 (C := C)) (top_ne hC) u; exact ⟨_, h⟩
  have hB : Total (fordG C) (.nt 2) := fun u => by
    obtain ⟨t, r, h⟩ := side_total (fordG_rule2 (C := C)) (bot_ne hC) u; exact ⟨_, h⟩
  have hn := total_notP (total_any (fordG C))
  have hD : Total (fordG C) fordD :=
    total_seq (total_andP (total_any _)) (total_seq (total_andP (total_seq hA hn)) (total_seq hB hn))
  intro w
  obtain ⟨o, ho⟩ := hD w
  cases o with
  | ok t r => exact ⟨_, .ntOk _ _ _ _ _ rfl ho⟩
  | fail => exact ⟨_, .ntFail _ _ _ rfl ho⟩

theorem sideAlts_bounded (f : Nat → List Bool) {self m : Nat} (h : self < m) :
    ∀ is : List Nat, (sideAlts f self is).NtBounded m
  | [] => trivial
  | _ :: is => ⟨⟨trivial, h, trivial⟩, sideAlts_bounded f h is⟩

theorem fordG_selfContained (C : PCP) : (fordG C).SelfContained := by
  intro r hr
  simp only [fordG, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simp [fordG, fordD, PExp.andP, PExp.NtBounded]
  · exact sideAlts_bounded _ (by simp [fordG]) _
  · exact sideAlts_bounded _ (by simp [fordG]) _

/-! ## The reductions, on instances -/

/-- **Equivalence, from Ford's grammar**: `fordG C` has the empty language's language iff `C` has no solution. -/
theorem ford_equiv_iff {C : PCP} (hC : C.NonemptyPairs) :
    (∀ w, Accepts (fordG C) w ↔ Accepts emptyG w) ↔ ¬ PCPSol C := by
  rw [equiv_emptyG_iff, ford_iff hC]

/-- **Completeness, from Ford's grammar**: `loopG (fordG C)` is complete iff `C` has no solution. -/
theorem ford_complete_iff {C : PCP} (hC : C.NonemptyPairs) : Complete (loopG (fordG C)) ↔ ¬ PCPSol C := by
  rw [loopG_complete_iff (fordG_selfContained C) (by simp [fordG]) (fordG_complete hC), ford_iff hC]

end Shallot
