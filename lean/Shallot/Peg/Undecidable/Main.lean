import Shallot.Peg.Undecidable.MachCards
import Shallot.Peg.Undecidable.MachPrint
import Complexity.Undec.K1
import Complexity.Comp.Reduce

/-!
# The emptiness, equivalence and completeness of PEGs are undecidable (Ford §3.4–3.5)

The problems, on the bits of grammars (`encG`):
- `PegEmpty`: the grammar's language is empty;
- `PegEquiv`: two grammars have the same language;
- `PegComplete`: the grammar is complete (its start rule succeeds or fails on every input).

No Turing machine decides any of them. Each reduces from `K1` (a one-tape table accepting its own code), which is
undecidable (`k1_undecidable`), through Ford's grammar of the table (`k1_grammar`), computed by a stack program
(`kP_computes`):
- **emptiness** (`peg_empty_undecidable`) by `ford_iff`;
- **equivalence** (`peg_equiv_undecidable`), comparing with the grammar of the empty language as Ford does;
- **completeness** (`peg_complete_undecidable`) by Ford's loop grammar `A' ← &e_S A'`.
-/

namespace Shallot

open Complexity
open Complexity.Univ
open Complexity.Undec

/-- **The emptiness problem**: bits of a grammar whose language is empty. -/
def PegEmpty : Lang := fun bits => ∃ g, bits = encG g ∧ ¬ ∃ w, Accepts g w

/-- **The equivalence problem**: bits of two grammars with the same language. -/
def PegEquiv : Lang := fun bits => ∃ g h, bits = encG g ++ encG h ∧ ∀ w, Accepts g w ↔ Accepts h w

/-- **The completeness problem**: bits of a complete grammar. -/
def PegComplete : Lang := fun bits => ∃ g, bits = encG g ∧ Complete g

/-! ## The stack programs of the reductions -/

/-- The grammar of an input from its cards. -/
def kP : NProg UK := .seq cardsP printP

/-- The loop grammar of an input from its cards. -/
def kLP : NProg UK := .seq cardsP printLP

/-- The empty grammar followed by the grammar of an input. -/
def kEP : NProg UK := .seq kP (nloadP 0 ((encG emptyG).map bitElem).reverse)

theorem k1Grammar_good {w : List Bool} {nq na : Nat} {rest : List Nat} (h : GoodCode w nq na rest) :
    k1Grammar w = fordG (toPCP (tablePCPN (table1 nq na rest) w)) := by
  unfold k1Grammar; rw [h.1]; simp [h.2]

theorem k1Grammar_bad {w : List Bool} (h : ∀ nq na rest, ¬ GoodCode w nq na rest) : k1Grammar w = emptyG := by
  unfold k1Grammar
  split
  next nq na rest heq =>
    have : ¬ rest.length % 3 = 0 := fun hm => h nq na rest ⟨heq, hm⟩
    simp [this]
  next => rfl

/-- **The stack program computes the grammar of an input.** -/
theorem kP_computes : NComputes kP (fun w => encG (k1Grammar w)) := by
  intro w
  by_cases hg : ∃ nq na rest, GoodCode w nq na rest
  · obtain ⟨nq, na, rest, h⟩ := hg
    obtain ⟨c₁, x₁⟩ := cardsP_good h
    obtain ⟨c₂, x₂⟩ := printP_good (tablePCPN (table1 nq na rest) w)
    dsimp only
    rw [k1Grammar_good h]
    exact ⟨_, x₁.seq x₂⟩
  · have h : ∀ nq na rest, ¬ GoodCode w nq na rest := fun nq na rest hc => hg ⟨nq, na, rest, hc⟩
    obtain ⟨c₁, x₁⟩ := cardsP_bad h
    obtain ⟨c₂, x₂⟩ := printP_bad
    dsimp only
    rw [k1Grammar_bad h]
    exact ⟨_, x₁.seq x₂⟩

/-- **The stack program computes the loop grammar of an input.** -/
theorem kLP_computes : NComputes kLP (fun w => encG (loopG (k1Grammar w))) := by
  intro w
  by_cases hg : ∃ nq na rest, GoodCode w nq na rest
  · obtain ⟨nq, na, rest, h⟩ := hg
    obtain ⟨c₁, x₁⟩ := cardsP_good h
    obtain ⟨c₂, x₂⟩ := printLP_good (tablePCPN (table1 nq na rest) w)
    dsimp only
    rw [k1Grammar_good h]
    exact ⟨_, x₁.seq x₂⟩
  · have h : ∀ nq na rest, ¬ GoodCode w nq na rest := fun nq na rest hc => hg ⟨nq, na, rest, hc⟩
    obtain ⟨c₁, x₁⟩ := cardsP_bad h
    obtain ⟨c₂, x₂⟩ := printLP_bad
    dsimp only
    rw [k1Grammar_bad h]
    exact ⟨_, x₁.seq x₂⟩

theorem nInit_prepend (b x : List Bool) :
    (nInit UK x).set 0 ((nInit UK x) 0 ++ (b.map bitElem).reverse) = nInit UK (b ++ x) := by
  funext i
  by_cases hi : i = 0
  · subst hi; simp [Lists.set, nInit]
  · have : i.val ≠ 0 := fun e => hi (Fin.ext e)
    simp [Lists.set, nInit, hi, this]

/-- **The stack program computes the empty grammar followed by the grammar of an input.** -/
theorem kEP_computes : NComputes kEP (fun w => encG emptyG ++ encG (k1Grammar w)) := by
  intro w
  obtain ⟨c, x⟩ := kP_computes w
  have x₂ := nruns_load (0 : Fin UK) ((encG emptyG).map bitElem).reverse (nInit UK (encG (k1Grammar w)))
  rw [nInit_prepend] at x₂
  exact ⟨_, x.seq x₂⟩

/-! ## The grammars of inputs -/

theorem emptyG_complete : Complete emptyG := fun w => ⟨_, .ntFail _ _ _ rfl (.notOk _ _ _ _ (.eps w))⟩

theorem emptyG_selfContained : emptyG.SelfContained := by
  intro r hr; simp [emptyG] at hr; subst hr; trivial

/-- The grammar of an input is self-contained and complete, with its start among its rules. -/
theorem k1Grammar_ok (w : List Bool) :
    (k1Grammar w).SelfContained ∧ (k1Grammar w).start < (k1Grammar w).rules.length ∧ Complete (k1Grammar w) := by
  by_cases hg : ∃ nq na rest, GoodCode w nq na rest
  · obtain ⟨nq, na, rest, h⟩ := hg
    rw [k1Grammar_good h]
    have hb := srCards_nonempty (tmSRS (table1 nq na rest)) (tmStart (table1 nq na rest) w)
      (tmAcc (table1 nq na rest)) (tmSyms (table1 nq na rest)) (tmSRS_nonempty _)
    exact ⟨fordG_selfContained _, by simp [fordG],
      fordG_complete (toPCP_nonempty (mpcpToPCP_nonempty _ _ _ hb))⟩
  · rw [k1Grammar_bad (fun nq na rest hc => hg ⟨nq, na, rest, hc⟩)]
    exact ⟨emptyG_selfContained, by simp [emptyG], emptyG_complete⟩

/-! ## The undecidability -/

theorem not_pegEmpty_iff (g : Grammar) : ¬ PegEmpty (encG g) ↔ ∃ w, Accepts g w := by
  unfold PegEmpty
  constructor
  · intro h
    exact Classical.byContradiction fun hn => h ⟨g, rfl, hn⟩
  · rintro he ⟨g', hg, hn⟩
    rw [encG_inj hg] at he
    exact hn he

/-- **The emptiness of PEGs is undecidable.** -/
theorem peg_empty_undecidable : ¬ TMDecidable PegEmpty := by
  intro h
  apply k1_undecidable
  exact tmDecidable_of_nreduce (tmDecidable_compl h) kP_computes
    (fun w => by rw [k1_grammar w, not_pegEmpty_iff])

theorem pegEquiv_empty_iff (g : Grammar) : PegEquiv (encG emptyG ++ encG g) ↔ ¬ ∃ w, Accepts g w := by
  unfold PegEquiv
  constructor
  · rintro ⟨g₁, h₁, e, he⟩
    obtain ⟨rfl, rfl⟩ := encG_pair_inj e
    have := (equiv_emptyG_iff g).1 (fun w => (he w).symm)
    exact this
  · intro hn
    exact ⟨emptyG, g, rfl, fun w => ((equiv_emptyG_iff g).2 hn w).symm⟩

/-- **The equivalence of PEGs is undecidable.** -/
theorem peg_equiv_undecidable : ¬ TMDecidable PegEquiv := by
  intro h
  apply k1_undecidable
  exact tmDecidable_of_nreduce (tmDecidable_compl h) kEP_computes
    (fun w => by
      rw [k1_grammar w, pegEquiv_empty_iff]
      exact ⟨fun h₁ h₂ => h₂ h₁, fun h₁ => Classical.byContradiction fun hn => h₁ hn⟩)

theorem pegComplete_iff (g : Grammar) : PegComplete (encG g) ↔ Complete g := by
  unfold PegComplete
  exact ⟨fun ⟨g', hg, hc⟩ => by rw [encG_inj hg]; exact hc, fun hc => ⟨g, rfl, hc⟩⟩

/-- **The completeness of PEGs is undecidable.** -/
theorem peg_complete_undecidable : ¬ TMDecidable PegComplete := by
  intro h
  apply k1_undecidable
  exact tmDecidable_of_nreduce (tmDecidable_compl h) kLP_computes (fun w => by
    obtain ⟨hs, hst, hc⟩ := k1Grammar_ok w
    rw [k1_grammar w, pegComplete_iff, loopG_complete_iff hs hst hc]
    exact ⟨fun h₁ h₂ => h₂ h₁, fun h₁ => Classical.byContradiction fun hn => h₁ hn⟩)

end Shallot
