import Complexity.TM

/-!
# Structured programs over `k` tapes, compiled to Turing machines

Writing Turing machines as transition tables is impractical, so machines are written as structured programs
(`act`, `seq`, `ite`, `loop`, `halt`) and compiled to a flat machine whose states are program points. A big-step
semantics with exact step counts and an invariant on every visited tape state (`Exec P p τ t o`) is the reasoning layer;
`run_of_exec` transfers it to the machine: the compiled machine reaches the corresponding state in exactly `t` steps, and
every intermediate configuration's tapes satisfy `P` (used for space bounds).
-/

namespace Complexity

/-- The tapes of a configuration (everything but the control state). -/
structure Tapes (k : Nat) where
  pos : Fin k → Nat
  cells : Fin k → Nat → Nat

def Tapes.read {k : Nat} (τ : Tapes k) : Fin k → Nat := fun i => τ.cells i (τ.pos i)

/-- Write the symbols `w` under the heads, then move the heads by `mv`. -/
def Tapes.apply {k : Nat} (τ : Tapes k) (w : Fin k → Nat) (mv : Fin k → Move) : Tapes k where
  pos := fun i => (mv i).apply (τ.pos i)
  cells := fun i j => if j = τ.pos i then w i else τ.cells i j

def toCfg {k : Nat} (q : Nat) (τ : Tapes k) : Cfg k := ⟨q, τ.pos, τ.cells⟩

def Cfg.tapes {k : Nat} (c : Cfg k) : Tapes k := ⟨c.pos, c.cells⟩

/-- One machine step's effect on the tapes is determined by an action of the symbols read. -/
abbrev Action (k : Nat) := (Fin k → Nat) → (Fin k → Nat) × (Fin k → Move)

inductive Prog (k : Nat) where
  | act (f : Action k)
  | seq (p q : Prog k)
  | ite (c : (Fin k → Nat) → Bool) (p q : Prog k)
  | loop (c : (Fin k → Nat) → Bool) (p : Prog k)
  | halt (accept : Bool)

inductive Outcome (k : Nat) where
  | cont (τ : Tapes k)
  | stop (accept : Bool) (τ : Tapes k)

/-- Big-step semantics with exact step counts; every visited tape state satisfies `P`. -/
inductive Exec {k : Nat} (P : Tapes k → Prop) : Prog k → Tapes k → Nat → Outcome k → Prop
  | act {f : Action k} {τ : Tapes k} : P τ → P (τ.apply (f τ.read).1 (f τ.read).2) →
      Exec P (.act f) τ 1 (.cont (τ.apply (f τ.read).1 (f τ.read).2))
  | halt {b : Bool} {τ : Tapes k} : P τ → Exec P (.halt b) τ 1 (.stop b τ)
  | seqC {p q : Prog k} {τ τ₁ : Tapes k} {t₁ t₂ : Nat} {o : Outcome k} :
      Exec P p τ t₁ (.cont τ₁) → Exec P q τ₁ t₂ o → Exec P (.seq p q) τ (t₁ + t₂) o
  | seqS {p q : Prog k} {τ τ₁ : Tapes k} {t₁ : Nat} {b : Bool} :
      Exec P p τ t₁ (.stop b τ₁) → Exec P (.seq p q) τ t₁ (.stop b τ₁)
  | iteT {c : (Fin k → Nat) → Bool} {p q : Prog k} {τ : Tapes k} {t : Nat} {o : Outcome k} :
      P τ → c τ.read = true → Exec P p τ t o → Exec P (.ite c p q) τ (t + 1) o
  | iteF {c : (Fin k → Nat) → Bool} {p q : Prog k} {τ : Tapes k} {t : Nat} {o : Outcome k} :
      P τ → c τ.read = false → Exec P q τ t o → Exec P (.ite c p q) τ (t + 1) o
  | loopF {c : (Fin k → Nat) → Bool} {p : Prog k} {τ : Tapes k} :
      P τ → c τ.read = false → Exec P (.loop c p) τ 1 (.cont τ)
  | loopC {c : (Fin k → Nat) → Bool} {p : Prog k} {τ τ₁ : Tapes k} {t₁ t₂ : Nat} {o : Outcome k} :
      P τ → c τ.read = true → Exec P p τ t₁ (.cont τ₁) → Exec P (.loop c p) τ₁ t₂ o →
      Exec P (.loop c p) τ (t₁ + 1 + t₂) o
  | loopS {c : (Fin k → Nat) → Bool} {p : Prog k} {τ τ₁ : Tapes k} {t₁ : Nat} {b : Bool} :
      P τ → c τ.read = true → Exec P p τ t₁ (.stop b τ₁) → Exec P (.loop c p) τ (t₁ + 1) (.stop b τ₁)

/-! ## Compilation -/

inductive Node (k : Nat) where
  | act (f : Action k) (next : Nat)
  | test (c : (Fin k → Nat) → Bool) (ifT ifF : Nat)

def Prog.size {k : Nat} : Prog k → Nat
  | .act _ => 1
  | .seq p q => p.size + q.size
  | .ite _ p q => 1 + p.size + q.size
  | .loop _ p => 1 + p.size
  | .halt _ => 1

/-- The nodes of `p`, numbered from `base`, continuing at `exit`. Program entry is `base`. -/
def Prog.compile {k : Nat} : Prog k → Nat → Nat → List (Node k)
  | .act f, _, exit => [.act f exit]
  | .seq p q, base, exit => p.compile base (base + p.size) ++ q.compile (base + p.size) exit
  | .ite c p q, base, exit =>
    .test c (base + 1) (base + 1 + p.size) :: (p.compile (base + 1) exit ++ q.compile (base + 1 + p.size) exit)
  | .loop c p, base, exit => .test c (base + 1) exit :: p.compile (base + 1) base
  | .halt b, _, _ => [.act (fun r => (r, fun _ => .S)) (if b then 0 else 1)]

theorem Prog.length_compile {k : Nat} : ∀ (p : Prog k) (base exit : Nat), (p.compile base exit).length = p.size
  | .act _, _, _ => rfl
  | .seq p q, base, exit => by simp [compile, size, length_compile p, length_compile q]
  | .ite c p q, base, exit => by simp [compile, size, length_compile p, length_compile q]; omega
  | .loop c p, base, exit => by simp [compile, size, length_compile p]; omega
  | .halt _, _, _ => rfl

/-- The node table `nodes` holds the block `l` at states `base, base + 1, …` (state `q` is `nodes[q - 2]`). -/
def Embeds {k : Nat} (nodes : List (Node k)) (base : Nat) (l : List (Node k)) : Prop :=
  2 ≤ base ∧ ∀ i (h : i < l.length), nodes[base - 2 + i]? = some l[i]

theorem Embeds.left {k : Nat} {nodes l₁ l₂ : List (Node k)} {base : Nat} (h : Embeds nodes base (l₁ ++ l₂)) :
    Embeds nodes base l₁ :=
  ⟨h.1, fun i hi => by have := h.2 i (by simp; omega); rwa [List.getElem_append_left hi] at this⟩

theorem Embeds.right {k : Nat} {nodes l₁ l₂ : List (Node k)} {base : Nat} (h : Embeds nodes base (l₁ ++ l₂)) :
    Embeds nodes (base + l₁.length) l₂ := by
  refine ⟨by have := h.1; omega, fun i hi => ?_⟩
  have := h.2 (l₁.length + i) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simp only [Nat.add_sub_cancel_left] at this
  rw [show base + l₁.length - 2 + i = base - 2 + (l₁.length + i) by have := h.1; omega]
  exact this

theorem Embeds.head {k : Nat} {nodes l : List (Node k)} {x : Node k} {base : Nat} (h : Embeds nodes base (x :: l)) :
    nodes[base - 2]? = some x := by
  have := h.2 0 (by simp); simpa using this

theorem Embeds.tail {k : Nat} {nodes l : List (Node k)} {x : Node k} {base : Nat} (h : Embeds nodes base (x :: l)) :
    Embeds nodes (base + 1) l :=
  have h' : Embeds nodes base ([x] ++ l) := h
  h'.right

/-- The machine of a node table: state `q ≥ 2` runs node `q - 2`; other states halt; a missing node rejects. -/
def nodeDelta {k : Nat} (nodes : List (Node k)) (q : Nat) (r : Fin k → Nat) : Nat × (Fin k → Nat) × (Fin k → Move) :=
  match nodes[q - 2]? with
  | some (.act f next) => (next, (f r).1, (f r).2)
  | some (.test c a b) => (if c r then a else b, r, fun _ => .S)
  | none => (1, r, fun _ => .S)

/-- The tape effect of a test step is nothing. -/
theorem Tapes.apply_read_stay {k : Nat} (τ : Tapes k) : τ.apply τ.read (fun _ => .S) = τ := by
  cases τ with
  | mk pos cells =>
    simp only [Tapes.apply, Move.apply, Tapes.read, Tapes.mk.injEq, true_and]
    funext i j
    split
    · rename_i h; rw [h]
    · rfl

section Sim

variable {k : Nat} (M : TM k) (nodes : List (Node k)) (hδ : ∀ q r, 2 ≤ q → M.delta q r = nodeDelta nodes q r)

include hδ

theorem step_node {q : Nat} (hq : 2 ≤ q) (τ : Tapes k) :
    M.step (toCfg q τ) = toCfg (nodeDelta nodes q τ.read).1
      (τ.apply (nodeDelta nodes q τ.read).2.1 (nodeDelta nodes q τ.read).2.2) := by
  have hnh : ¬ (toCfg q τ).halted := by simp [Cfg.halted, toCfg]; omega
  simp only [TM.step, hnh, if_false]
  have hs : (toCfg q τ).state = q := rfl
  have hr : (toCfg q τ).read = τ.read := rfl
  rw [hs, hr, hδ q _ hq]
  rfl

theorem step_act {q next : Nat} {f : Action k} (hq : 2 ≤ q) (hn : nodes[q - 2]? = some (.act f next)) (τ : Tapes k) :
    M.step (toCfg q τ) = toCfg next (τ.apply (f τ.read).1 (f τ.read).2) := by
  rw [step_node M nodes hδ hq]; simp [nodeDelta, hn]

theorem step_test {q a b : Nat} {c : (Fin k → Nat) → Bool} (hq : 2 ≤ q) (hn : nodes[q - 2]? = some (.test c a b))
    (τ : Tapes k) : M.step (toCfg q τ) = toCfg (if c τ.read then a else b) τ := by
  rw [step_node M nodes hδ hq]; simp only [nodeDelta, hn]; rw [Tapes.apply_read_stay]

/-- The state a program outcome corresponds to. -/
def outState (exit : Nat) : Outcome k → Nat
  | .cont _ => exit
  | .stop b _ => if b then 0 else 1

def Outcome.tapes : Outcome k → Tapes k
  | .cont τ => τ
  | .stop _ τ => τ

omit hδ in
theorem halted_of_stop (b : Bool) (τ : Tapes k) : (toCfg (if b then 0 else 1) τ).halted := by
  cases b <;> simp [Cfg.halted, toCfg]

/-- **Simulation.** A big-step execution of `p`, compiled at `base` with continuation `exit`, is run by the machine in
exactly `t` steps; every configuration on the way has tapes satisfying `P`. -/
theorem run_of_exec {P : Tapes k → Prop} {p : Prog k} {τ : Tapes k} {t : Nat} {o : Outcome k}
    (h : Exec P p τ t o) :
    ∀ base exit, Embeds nodes base (p.compile base exit) →
      M.run (toCfg base τ) t = toCfg (outState exit o) o.tapes ∧ ∀ u, u ≤ t → P (M.run (toCfg base τ) u).tapes := by
  induction h with
  | @act f τ hP hP' =>
    intro base exit hE
    have hs := step_act M nodes hδ hE.1 (hE.head) τ
    refine ⟨hs, fun u hu => ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu with rfl | rfl
    · exact hP
    · show P (M.step (toCfg base τ)).tapes
      rw [hs]; exact hP'
  | @halt b τ hP =>
    intro base exit hE
    have hs := step_act M nodes hδ hE.1 (hE.head) τ
    rw [Tapes.apply_read_stay] at hs
    refine ⟨hs, fun u hu => ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu with rfl | rfl
    · exact hP
    · show P (M.step (toCfg base τ)).tapes
      rw [hs]; exact hP
  | @seqC p q τ τ₁ t₁ t₂ o _ _ ih₁ ih₂ =>
    intro base exit hE
    have hE₁ := (hE : Embeds nodes base (p.compile base (base + p.size) ++ q.compile (base + p.size) exit)).left
    have hE₂ := (hE : Embeds nodes base (p.compile base (base + p.size) ++ q.compile (base + p.size) exit)).right
    rw [Prog.length_compile] at hE₂
    obtain ⟨h₁, hP₁⟩ := ih₁ base (base + p.size) hE₁
    obtain ⟨h₂, hP₂⟩ := ih₂ (base + p.size) exit hE₂
    refine ⟨by rw [TM.run_add, h₁]; exact h₂, fun u hu => ?_⟩
    by_cases hu₁ : u ≤ t₁
    · exact hP₁ u hu₁
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le hu₁)
      rw [TM.run_add, h₁]
      exact hP₂ v (by omega)
  | @seqS p q τ τ₁ t₁ b _ ih₁ =>
    intro base exit hE
    have hE₁ := (hE : Embeds nodes base (p.compile base (base + p.size) ++ q.compile (base + p.size) exit)).left
    exact ih₁ base (base + p.size) hE₁
  | @iteT c p q τ t o hP hc _ ih =>
    intro base exit hE
    have hs := step_test M nodes hδ hE.1 hE.head τ
    rw [hc, if_pos rfl] at hs
    have hE' := hE.tail.left
    obtain ⟨h₁, hP₁⟩ := ih (base + 1) exit hE'
    refine ⟨by rw [Nat.add_comm, TM.run_add]; exact (show M.run (M.step (toCfg base τ)) t = _ by rw [hs]; exact h₁),
      fun u hu => ?_⟩
    cases u with
    | zero => exact hP
    | succ u =>
      rw [Nat.add_comm, TM.run_add]
      show P (M.run (M.step (toCfg base τ)) u).tapes
      rw [hs]; exact hP₁ u (by omega)
  | @iteF c p q τ t o hP hc _ ih =>
    intro base exit hE
    have hs := step_test M nodes hδ hE.1 hE.head τ
    rw [hc] at hs
    simp only [Bool.false_eq_true, if_false] at hs
    have hE' := hE.tail.right
    rw [Prog.length_compile] at hE'
    obtain ⟨h₁, hP₁⟩ := ih (base + 1 + p.size) exit hE'
    refine ⟨by rw [Nat.add_comm, TM.run_add]; exact (show M.run (M.step (toCfg base τ)) t = _ by rw [hs]; exact h₁),
      fun u hu => ?_⟩
    cases u with
    | zero => exact hP
    | succ u =>
      rw [Nat.add_comm, TM.run_add]
      show P (M.run (M.step (toCfg base τ)) u).tapes
      rw [hs]; exact hP₁ u (by omega)
  | @loopF c p τ hP hc =>
    intro base exit hE
    have hs := step_test M nodes hδ hE.1 hE.head τ
    rw [hc] at hs
    simp only [Bool.false_eq_true, if_false] at hs
    refine ⟨hs, fun u hu => ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu with rfl | rfl
    · exact hP
    · show P (M.step (toCfg base τ)).tapes
      rw [hs]; exact hP
  | @loopC c p τ τ₁ t₁ t₂ o hP hc _ _ ih₁ ih₂ =>
    intro base exit hE
    have hs := step_test M nodes hδ hE.1 hE.head τ
    rw [hc, if_pos rfl] at hs
    obtain ⟨h₁, hP₁⟩ := ih₁ (base + 1) base hE.tail
    obtain ⟨h₂, hP₂⟩ := ih₂ base exit hE
    have hrun : M.run (toCfg base τ) (1 + t₁) = toCfg base τ₁ := by
      rw [TM.run_add]; exact (show M.run (M.step (toCfg base τ)) t₁ = _ by rw [hs]; exact h₁)
    refine ⟨by rw [show t₁ + 1 + t₂ = (1 + t₁) + t₂ by omega, TM.run_add, hrun]; exact h₂, fun u hu => ?_⟩
    by_cases hu₁ : u ≤ 1 + t₁
    · cases u with
      | zero => exact hP
      | succ u =>
        rw [Nat.add_comm, TM.run_add]
        show P (M.run (M.step (toCfg base τ)) u).tapes
        rw [hs]; exact hP₁ u (by omega)
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le hu₁)
      rw [TM.run_add, hrun]
      exact hP₂ v (by omega)
  | @loopS c p τ τ₁ t₁ b hP hc _ ih₁ =>
    intro base exit hE
    have hs := step_test M nodes hδ hE.1 hE.head τ
    rw [hc, if_pos rfl] at hs
    obtain ⟨h₁, hP₁⟩ := ih₁ (base + 1) base hE.tail
    refine ⟨by rw [Nat.add_comm, TM.run_add]; exact (show M.run (M.step (toCfg base τ)) t₁ = _ by rw [hs]; exact h₁),
      fun u hu => ?_⟩
    cases u with
    | zero => exact hP
    | succ u =>
      rw [Nat.add_comm, TM.run_add]
      show P (M.run (M.step (toCfg base τ)) u).tapes
      rw [hs]; exact hP₁ u (by omega)

end Sim

/-! ## The machine of a program -/

/-- Every action writes symbols below `na` when it reads symbols below `na`. -/
def Prog.SymOK {k : Nat} (na : Nat) : Prog k → Prop
  | .act f => ∀ r, (∀ i, r i < na) → ∀ i, (f r).1 i < na
  | .seq p q => p.SymOK na ∧ q.SymOK na
  | .ite _ p q => p.SymOK na ∧ q.SymOK na
  | .loop _ p => p.SymOK na
  | .halt _ => True

def Node.targetsBelow {k : Nat} (B : Nat) : Node k → Prop
  | .act _ next => next < B
  | .test _ a b => a < B ∧ b < B

def Node.symOK {k : Nat} (na : Nat) : Node k → Prop
  | .act f _ => ∀ r, (∀ i, r i < na) → ∀ i, (f r).1 i < na
  | .test _ _ _ => True

theorem Prog.size_pos {k : Nat} : ∀ p : Prog k, 1 ≤ p.size
  | .act _ => Nat.le_refl _
  | .seq p q => by have := size_pos p; simp [size]; omega
  | .ite _ p q => by simp [size]; omega
  | .loop _ p => by simp [size]
  | .halt _ => Nat.le_refl _

theorem Prog.compile_targets {k : Nat} : ∀ (p : Prog k) (base exit B : Nat), 2 ≤ B → base + p.size ≤ B → exit < B →
    ∀ n ∈ p.compile base exit, n.targetsBelow B
  | .act f, base, exit, B, _, _, hx, n, hn => by
    simp [compile] at hn; subst hn; exact hx
  | .seq p q, base, exit, B, h2, hb, hx, n, hn => by
    simp only [compile, List.mem_append] at hn
    simp only [size] at hb
    rcases hn with hn | hn
    · exact compile_targets p base (base + p.size) B h2 (by omega) (by have := size_pos q; omega) n hn
    · exact compile_targets q (base + p.size) exit B h2 (by omega) hx n hn
  | .ite c p q, base, exit, B, h2, hb, hx, n, hn => by
    simp only [compile, List.mem_cons, List.mem_append] at hn
    simp only [size] at hb
    rcases hn with rfl | hn | hn
    · have := size_pos q; exact ⟨by omega, by omega⟩
    · exact compile_targets p (base + 1) exit B h2 (by omega) hx n hn
    · exact compile_targets q (base + 1 + p.size) exit B h2 (by omega) hx n hn
  | .loop c p, base, exit, B, h2, hb, hx, n, hn => by
    simp only [compile, List.mem_cons] at hn
    simp only [size] at hb
    rcases hn with rfl | hn
    · have := size_pos p; exact ⟨by omega, hx⟩
    · exact compile_targets p (base + 1) base B h2 (by omega) (by omega) n hn
  | .halt b, base, exit, B, h2, hb, _, n, hn => by
    simp [compile] at hn; subst hn
    simp only [Node.targetsBelow, size] at hb ⊢
    split <;> omega

theorem Prog.compile_symOK {k : Nat} (na : Nat) : ∀ (p : Prog k) (base exit : Nat), p.SymOK na →
    ∀ n ∈ p.compile base exit, n.symOK na
  | .act f, _, _, h, n, hn => by simp [compile] at hn; subst hn; exact h
  | .seq p q, base, exit, h, n, hn => by
    simp only [compile, List.mem_append] at hn
    rcases hn with hn | hn
    · exact compile_symOK na p _ _ h.1 n hn
    · exact compile_symOK na q _ _ h.2 n hn
  | .ite c p q, base, exit, h, n, hn => by
    simp only [compile, List.mem_cons, List.mem_append] at hn
    rcases hn with rfl | hn | hn
    · trivial
    · exact compile_symOK na p _ _ h.1 n hn
    · exact compile_symOK na q _ _ h.2 n hn
  | .loop c p, base, exit, h, n, hn => by
    simp only [compile, List.mem_cons] at hn
    rcases hn with rfl | hn
    · trivial
    · exact compile_symOK na p _ _ h n hn
  | .halt b, _, _, _, n, hn => by
    simp [compile] at hn; subst hn
    intro r hr i; exact hr i

/-- The machine of a program: states `0`/`1` halt, the program starts at state `2`. -/
def Prog.machine {k : Nat} (p : Prog k) (na : Nat) (hna : 3 ≤ na) (hsym : p.SymOK na) : TM k where
  nq := p.size + 2
  na := na
  delta := nodeDelta (p.compile 2 1)
  three_le_nq := by have := p.size_pos; omega
  three_le_na := hna
  delta_state := by
    intro q r _ _
    unfold nodeDelta
    split
    · rename_i f next h
      have := p.compile_targets 2 1 (p.size + 2) (by omega) (by omega) (by omega) _ (List.mem_of_getElem? h)
      exact this
    · rename_i c a b h
      have := p.compile_targets 2 1 (p.size + 2) (by omega) (by omega) (by omega) _ (List.mem_of_getElem? h)
      simp only [Node.targetsBelow] at this
      split <;> omega
    · omega
  delta_sym := by
    intro q r _ hr i
    unfold nodeDelta
    split
    · rename_i f next h
      exact p.compile_symOK na 2 1 hsym _ (List.mem_of_getElem? h) r hr i
    · exact hr i
    · exact hr i

theorem Prog.machine_delta {k : Nat} (p : Prog k) (na : Nat) (hna : 3 ≤ na) (hsym : p.SymOK na) :
    ∀ q r, 2 ≤ q → (p.machine na hna hsym).delta q r = nodeDelta (p.compile 2 1) q r := fun _ _ _ => rfl

theorem Prog.embeds_top {k : Nat} (p : Prog k) : Embeds (p.compile 2 1) 2 (p.compile 2 1) :=
  ⟨Nat.le_refl _, fun i hi => by simp [List.getElem?_eq_getElem hi]⟩

/-! ## Transfer to `Decides`, `SpaceBounded`, and polynomial time -/

def TFits {k : Nat} (s : Nat) (τ : Tapes k) : Prop := ∀ i, τ.pos i < s ∧ ∀ j, s ≤ j → τ.cells i j = 0

def initTapes (k : Nat) (w : List Bool) : Tapes k := (initCfg k w).tapes

theorem initCfg_eq (k : Nat) (w : List Bool) : initCfg k w = toCfg 2 (initTapes k w) := rfl

/-- The program's run on `w` from the initial tapes, as a machine run. -/
theorem Prog.machine_run {k : Nat} (p : Prog k) (na : Nat) (hna : 3 ≤ na) (hsym : p.SymOK na)
    {P : Tapes k → Prop} {w : List Bool} {t : Nat} {b : Bool} {τ : Tapes k}
    (h : Exec P p (initTapes k w) t (.stop b τ)) :
    (p.machine na hna hsym).run (initCfg k w) t = toCfg (if b then 0 else 1) τ ∧
      ∀ u, P ((p.machine na hna hsym).run (initCfg k w) u).tapes := by
  have hsim := run_of_exec (p.machine na hna hsym) (p.compile 2 1) (p.machine_delta na hna hsym) h 2 1 p.embeds_top
  rw [← initCfg_eq] at hsim
  obtain ⟨hrun, hP⟩ := hsim
  refine ⟨hrun, fun u => ?_⟩
  by_cases hu : u ≤ t
  · exact hP u hu
  · have hh : ((p.machine na hna hsym).run (initCfg k w) t).halted := by
      rw [hrun]; exact halted_of_stop b τ
    rw [TM.run_stays _ _ (Nat.le_of_not_le hu) hh]
    exact hP t (Nat.le_refl _)

/-- **Decision transfer.** If on every input the program halts with the right answer while every tape state fits in
`s n` cells, its machine decides `L` in space `s`. -/
theorem Prog.decides_of_exec {k : Nat} (p : Prog k) (na : Nat) (hna : 3 ≤ na) (hsym : p.SymOK na) (L : Lang)
    (s : Nat → Nat)
    (h : ∀ w, ∃ t b τ, Exec (TFits (s w.length)) p (initTapes k w) t (.stop b τ) ∧ (b = true ↔ L w)) :
    (p.machine na hna hsym).Decides L ∧ (p.machine na hna hsym).SpaceBounded s := by
  constructor
  · intro w
    obtain ⟨t, b, τ, hex, hb⟩ := h w
    obtain ⟨hrun, _⟩ := p.machine_run na hna hsym hex
    refine ⟨t, by rw [hrun]; exact halted_of_stop b τ, ?_⟩
    rw [hrun, ← hb]
    cases b <;> simp [toCfg]
  · intro w u
    obtain ⟨t, b, τ, hex, _⟩ := h w
    exact (p.machine_run na hna hsym hex).2 u

/-- **Time transfer.** If on every input the program accepts within `T n` steps leaving `f w` on tape `0`, `f` is
polynomial-time computable (when `T` is polynomial). -/
theorem Prog.polytime_of_exec {k : Nat} (hk : 0 < k) (p : Prog k) (na : Nat) (hna : 3 ≤ na) (hsym : p.SymOK na)
    (f : List Bool → List Bool) (T : Nat → Nat) (hT : IsPoly T)
    (h : ∀ w, ∃ t τ, t ≤ T w.length ∧ Exec (fun _ => True) p (initTapes k w) t (.stop true τ) ∧
      OutputIs hk (toCfg 0 τ) (f w)) :
    PolyTimeComputable f := by
  refine ⟨k, hk, p.machine na hna hsym, T, hT, fun w => ?_⟩
  obtain ⟨t, τ, ht, hex, hout⟩ := h w
  obtain ⟨hrun, _⟩ := p.machine_run na hna hsym hex
  refine ⟨t, ht, by rw [hrun]; rfl, by rw [hrun]; exact hout⟩

end Complexity
