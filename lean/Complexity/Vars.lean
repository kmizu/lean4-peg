import Complexity.CfgEnc

namespace Complexity

/-- Every variable occurring in the formula satisfies `P`. -/
def Formula.Within (P : Name → Prop) : Formula → Prop
  | .var x => P x
  | .tt => True
  | .ff => True
  | .not a => a.Within P
  | .and a b => a.Within P ∧ b.Within P
  | .or a b => a.Within P ∧ b.Within P

theorem Formula.Within.mono {P Q : Name → Prop} {ψ : Formula} (h : ψ.Within P) (hPQ : ∀ x, P x → Q x) :
    ψ.Within Q := by
  induction ψ with
  | var x => exact hPQ x h
  | tt => trivial
  | ff => trivial
  | not a ih => exact ih h
  | and a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | or a b iha ihb => exact ⟨iha h.1, ihb h.2⟩

theorem within_bigAnd {P : Name → Prop} : ∀ l : List Formula, (bigAnd l).Within P ↔ ∀ a ∈ l, a.Within P
  | [] => by simp [bigAnd, Formula.Within]
  | a :: as => by simp [bigAnd, Formula.Within, within_bigAnd as]

theorem within_bigOr {P : Name → Prop} : ∀ l : List Formula, (bigOr l).Within P ↔ ∀ a ∈ l, a.Within P
  | [] => by simp [bigOr, Formula.Within]
  | a :: as => by simp [bigOr, Formula.Within, within_bigOr as]

theorem within_iff {P : Name → Prop} (a b : Formula) : (Formula.iff a b).Within P ↔ a.Within P ∧ b.Within P := by
  simp only [Formula.iff, Formula.Within]
  constructor
  · intro h; exact ⟨h.1.1, h.1.2⟩
  · intro h; exact ⟨⟨h.1, h.2⟩, h.1, h.2⟩

theorem within_imp {P : Name → Prop} (a b : Formula) : (Formula.imp a b).Within P ↔ a.Within P ∧ b.Within P := by
  simp [Formula.imp, Formula.Within]

theorem eval_upd_of_within {P : Name → Prop} {ψ : Formula} (h : ψ.Within P) {x : Name} (hx : ¬ P x)
    (ρ : Name → Bool) (b : Bool) : ψ.eval (upd ρ x b) = ψ.eval ρ := by
  induction ψ with
  | var y =>
    have : y ≠ x := fun e => hx (e ▸ h)
    simp [Formula.eval, upd, this]
  | tt => simp [Formula.eval]
  | ff => simp [Formula.eval]
  | not a ih => simp [Formula.eval, ih h]
  | and a b iha ihb => simp [Formula.eval, iha h.1, ihb h.2]
  | or a b iha ihb => simp [Formula.eval, iha h.1, ihb h.2]

/-- `y` is a variable of block `b`. -/
def InBlock (b y : Name) : Prop := ∃ v, y = b ++ v

theorem pairsOf_mem {α : Type} {l : List α} : ∀ {p : α × α}, p ∈ pairsOf l → p.1 ∈ l ∧ p.2 ∈ l := by
  induction l with
  | nil => intro p h; simp [pairsOf] at h
  | cons x xs ih =>
    intro p h
    simp only [pairsOf, List.mem_append, List.mem_map] at h
    rcases h with ⟨y, hy, rfl⟩ | h
    · simp [hy]
    · have := ih h
      exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩

theorem within_exOneF {P : Name → Prop} (vs : List Name) (h : ∀ v ∈ vs, P v) : (exOneF vs).Within P := by
  simp only [exOneF, Formula.Within, within_bigOr, within_bigAnd, List.mem_map]
  refine ⟨?_, ?_⟩
  · rintro a ⟨v, hv, rfl⟩; exact h v hv
  · rintro a ⟨p, hp, rfl⟩
    have := pairsOf_mem hp
    exact ⟨h _ this.1, h _ this.2⟩

section
variable {k : Nat} (M : TM k) (S : Nat)

theorem initF_within (b : Name) (c : Cfg k) : (initF M S b c).Within (InBlock b) := by
  simp only [initF, within_bigAnd, List.mem_map]
  rintro a ⟨v, hv, rfl⟩
  split <;> exact ⟨v, rfl⟩

theorem eqF_within (b b' : Name) : (eqF M S b b').Within (fun y => InBlock b y ∨ InBlock b' y) := by
  simp only [eqF, within_bigAnd, List.mem_map]
  rintro a ⟨v, hv, rfl⟩
  exact (within_iff _ _).2 ⟨Or.inl ⟨v, rfl⟩, Or.inr ⟨v, rfl⟩⟩

theorem accF_within (b : Name) : (accF b).Within (InBlock b) := ⟨[0, 0], rfl⟩

theorem wfF_within (b : Name) : (wfF M S b).Within (InBlock b) := by
  simp only [wfF, within_bigAnd, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap]
  rintro a ((rfl | ⟨i, hi, rfl⟩) | ⟨i, hi, j, hj, rfl⟩)
  · apply within_exOneF
    simp only [List.mem_map]
    rintro _ ⟨v, hv, rfl⟩; exact ⟨v, rfl⟩
  · apply within_exOneF
    simp only [List.mem_map]
    rintro _ ⟨v, hv, rfl⟩; exact ⟨_, rfl⟩
  · apply within_exOneF
    simp only [List.mem_map]
    rintro _ ⟨v, hv, rfl⟩; exact ⟨_, rfl⟩

theorem within_combF (b : Name) (q : Nat) (r : Fin k → Nat) : (combF S b q r).Within (InBlock b) := by
  refine ⟨⟨[0, q], rfl⟩, ?_⟩
  simp only [within_bigAnd, List.mem_map]
  rintro a ⟨i, _, rfl⟩
  simp only [readF, within_bigOr, List.mem_map]
  rintro a ⟨j, _, rfl⟩
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

theorem stepF_within (b b' : Name) : (stepF M S b b').Within (fun y => InBlock b y ∨ InBlock b' y) := by
  have hb : ∀ v, (fun y => InBlock b y ∨ InBlock b' y) (b ++ v) := fun v => Or.inl ⟨v, rfl⟩
  have hb' : ∀ v, (fun y => InBlock b y ∨ InBlock b' y) (b' ++ v) := fun v => Or.inr ⟨v, rfl⟩
  have hc : ∀ (q : Nat) (r : Fin k → Nat), (combF S b q r).Within (fun y => InBlock b y ∨ InBlock b' y) :=
    fun q r => (within_combF S b q r).mono (fun y h => Or.inl h)
  simp only [stepF, within_bigAnd, List.mem_append, List.mem_flatMap, List.mem_map, stateBitsF]
  rintro a ((⟨q', _, rfl⟩ | ⟨i, _, j, _, rfl⟩) | ⟨i, _, j, _, s, _, rfl⟩)
  · refine (within_iff _ _).2 ⟨hb' _, (within_bigOr _).2 ?_⟩
    simp only [List.mem_map]
    rintro _ ⟨p, _, rfl⟩; exact hc _ _
  · refine (within_iff _ _).2 ⟨hb' _, (within_bigOr _).2 ?_⟩
    simp only [List.mem_map]
    rintro _ ⟨p, _, rfl⟩
    refine ⟨hc _ _, (within_bigOr _).2 ?_⟩
    simp only [List.mem_map]
    rintro _ ⟨j', _, rfl⟩; exact hb _
  · refine (within_iff _ _).2 ⟨hb' _, ?_⟩
    refine ⟨⟨hb _, hb _⟩, hb _, (within_bigOr _).2 ?_⟩
    simp only [List.mem_map]
    rintro _ ⟨p, _, rfl⟩; exact hc _ _

end

end Complexity
