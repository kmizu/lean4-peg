import Cfg.Greibach.GNFBase

/-!
# Greibach normal form, stage 3: removing unit right sides

`unitG g` gives each nonterminal `A` (below the number of rules) the non-unit right sides of every `B`
reachable from `A` through unit right sides `A → B` (`UnitReach`, decided classically). It generates the
same language from every nonterminal (`gen_unitG_iff`), is `UnitFree`, and keeps `EpsFree` and
`RefsInRange`.
-/

namespace Shallot.Cfg

/-- `A` reaches `B` through unit right sides. -/
inductive UnitReach (g : CFGrammar) : Nat → Nat → Prop
  | refl (A : Nat) : UnitReach g A A
  | step {A B C : Nat} {alts : List Rhs} (halts : altsAt g.rules A = some alts) (hmem : [.nt B] ∈ alts)
      (h : UnitReach g B C) : UnitReach g A C

/-- The alternatives of a nonterminal, empty if missing. -/
def altsOf (g : CFGrammar) (i : Nat) : List Rhs := (altsAt g.rules i).getD []

open Classical in
/-- The new alternatives of `A`: the non-unit sides of every `B` that `A` reaches. -/
noncomputable def unitAlts (g : CFGrammar) (A : Nat) : List Rhs :=
  (List.range g.rules.length).flatMap fun B =>
    if UnitReach g A B then (altsOf g B).filter (fun r => !isUnitRhs r) else []

/-- The grammar without unit right sides. -/
noncomputable def unitG (g : CFGrammar) : CFGrammar :=
  ⟨(List.range g.rules.length).map (unitAlts g), g.start⟩

/-- Removing unit sides keeps the number of nonterminals. -/
theorem unitG_length (g : CFGrammar) : (unitG g).rules.length = g.rules.length := by
  simp only [unitG, List.length_map, List.length_range]

/-- The alternatives of `unitG g`. -/
theorem altsAt_unitG (g : CFGrammar) (i : Nat) :
    altsAt (unitG g).rules i = if i < g.rules.length then some (unitAlts g i) else none :=
  altsAt_range_map _ _ _

/-- `altsOf` on a defined index. -/
theorem altsOf_of_some {g : CFGrammar} {i : Nat} {alts : List Rhs} (h : altsAt g.rules i = some alts) :
    altsOf g i = alts := by
  simp only [altsOf, h, Option.getD_some]

/-- A member of `unitAlts`. -/
theorem mem_unitAlts {g : CFGrammar} {A : Nat} {rhs : Rhs} :
    rhs ∈ unitAlts g A ↔ ∃ B, B < g.rules.length ∧ UnitReach g A B ∧ rhs ∈ altsOf g B ∧
      isUnitRhs rhs = false := by
  simp only [unitAlts, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨B, hB, hr⟩
    split at hr
    · rename_i hreach
      have := List.mem_filter.mp hr
      refine ⟨B, hB, hreach, this.1, ?_⟩
      simpa using this.2
    · exact absurd hr List.not_mem_nil
  · rintro ⟨B, hB, hreach, hr, hu⟩
    refine ⟨B, hB, ?_⟩
    rw [if_pos hreach]
    exact List.mem_filter.mpr ⟨hr, by simp [hu]⟩

/-- A member of `altsOf` comes from a defined index. -/
theorem altsAt_of_mem_altsOf {g : CFGrammar} {B : Nat} {rhs : Rhs} (h : rhs ∈ altsOf g B) :
    ∃ alts, altsAt g.rules B = some alts ∧ rhs ∈ alts := by
  unfold altsOf at h
  cases hB : altsAt g.rules B with
  | none => rw [hB] at h; exact absurd h List.not_mem_nil
  | some a => rw [hB] at h; exact ⟨a, rfl, h⟩

/-- Reachability transports words up a unit chain. -/
theorem gen_of_unitReach {g : CFGrammar} {A B : Nat} (h : UnitReach g A B) {w : List Char}
    (hw : Gen g B w) : Gen g A w := by
  induction h with
  | refl => exact hw
  | step halts hmem _ ih => exact gen_of_rule halts hmem ((semRhs_single_nt _ _ _).mpr (ih hw))

/-- **Removing unit sides keeps the language** of every nonterminal. -/
theorem gen_unitG_iff (g : CFGrammar) (i : Nat) (w : List Char) : Gen (unitG g) i w ↔ Gen g i w := by
  constructor
  · intro h
    refine gen_sound (g := unitG g) (Gen g) (fun A alts rhs w halts hmem hr => ?_) h
    rw [altsAt_unitG] at halts
    split at halts
    · cases halts
      obtain ⟨B, _, hreach, hrB, _⟩ := mem_unitAlts.mp hmem
      obtain ⟨a, ha, hra⟩ := altsAt_of_mem_altsOf hrB
      exact gen_of_unitReach hreach (gen_of_rule ha hra hr)
    · cases halts
  · intro h
    refine gen_sound (g := g) (Gen (unitG g)) (fun A alts rhs w halts hmem hr => ?_) h
    have hA := altsAt_some_lt halts
    have halts' : altsAt (unitG g).rules A = some (unitAlts g A) := by rw [altsAt_unitG, if_pos hA]
    cases hu : isUnitRhs rhs with
    | false =>
        refine gen_of_rule halts' (mem_unitAlts.mpr ⟨A, hA, .refl A, ?_, hu⟩) hr
        rw [altsOf_of_some halts]; exact hmem
    | true =>
        match rhs, hu with
        | [.nt B], _ =>
          have hB := (semRhs_single_nt _ _ _).mp hr
          obtain ⟨altsB, rB, haltsB, hmemB, hrB⟩ := gen_cases hB
          rw [altsAt_unitG] at haltsB
          split at haltsB
          · cases haltsB
            obtain ⟨C, hC, hreach, hrC, hu'⟩ := mem_unitAlts.mp hmemB
            exact gen_of_rule halts' (mem_unitAlts.mpr ⟨C, hC, .step halts hmem hreach, hrC, hu'⟩) hrB
          · cases haltsB

/-- `unitG g` has no unit side. -/
theorem unitG_unitFree (g : CFGrammar) : UnitFree (unitG g) := by
  intro alts halts rhs hrhs
  simp only [unitG, List.mem_map] at halts
  obtain ⟨A, _, rfl⟩ := halts
  obtain ⟨_, _, _, _, hu⟩ := mem_unitAlts.mp hrhs
  exact hu

/-- Every side of `unitG g` is a side of `g`. -/
theorem mem_rules_of_mem_unitG {g : CFGrammar} {alts : List Rhs} (halts : alts ∈ (unitG g).rules)
    {rhs : Rhs} (hrhs : rhs ∈ alts) : ∃ a ∈ g.rules, rhs ∈ a := by
  simp only [unitG, List.mem_map] at halts
  obtain ⟨A, _, rfl⟩ := halts
  obtain ⟨B, _, _, hrB, _⟩ := mem_unitAlts.mp hrhs
  obtain ⟨a, ha, hra⟩ := altsAt_of_mem_altsOf hrB
  exact ⟨a, altsAt_some_mem ha, hra⟩

/-- Removing unit sides keeps `EpsFree`. -/
theorem unitG_epsFree {g : CFGrammar} (hg : EpsFree g) : EpsFree (unitG g) := by
  intro alts halts rhs hrhs
  obtain ⟨a, ha, hra⟩ := mem_rules_of_mem_unitG halts hrhs
  exact hg a ha rhs hra

/-- Removing unit sides keeps `RefsInRange`. -/
theorem unitG_refs {g : CFGrammar} (hg : RefsInRange g) : RefsInRange (unitG g) := by
  intro alts halts rhs hrhs j hj
  obtain ⟨a, ha, hra⟩ := mem_rules_of_mem_unitG halts hrhs
  rw [unitG_length]
  exact hg a ha rhs hra j hj

end Shallot.Cfg
