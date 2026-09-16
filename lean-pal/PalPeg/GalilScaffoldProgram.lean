import PalPeg.GalilScaffoldTape

set_option autoImplicit false
namespace PalPeg.GalilScaffoldProgram
open GalilFppWide (Instruction)
open GalilScaffoldTape

structure Config (n : ℕ) where
  pc : ℕ
  tapes : Fin n → Tape

def denote {n : ℕ} (x : Config n) : GalilFppWide.Config n :=
  ⟨x.pc, fun t => GalilScaffoldTape.denote (x.tapes t), fun t => head (x.tapes t)⟩

def changed {n : ℕ} (x : Config n) (t : Fin n) (v : Tape) (pc : ℕ) : Config n :=
  ⟨pc, Function.update x.tapes t v⟩

theorem wide_ext {n : ℕ} {x y : GalilFppWide.Config n}
    (hp : x.pc = y.pc) (ht : x.tape = y.tape) (hh : x.pos = y.pos) : x = y := by
  cases x; cases y; simp_all

theorem changed_right {n : ℕ} (x : Config n) (t : Fin n) (pc : ℕ) :
    denote (changed x t (moveRight (x.tapes t)) pc) =
      { denote x with pc := pc, pos := Function.update (denote x).pos t ((denote x).pos t+1) } := by
  apply wide_ext
  · rfl
  · funext k
    by_cases hk : k = t
    · subst k; simp [denote, changed, right_denote]
    · simp [denote, changed, hk]
  · funext k
    by_cases hk : k = t
    · subst k; simp [denote, changed, right_head]
    · simp [denote, changed, hk]

theorem changed_left {n : ℕ} (x : Config n) (t : Fin n) (pc : ℕ)
    (hp : 0 < head (x.tapes t)) :
    denote (changed x t (moveLeft (x.tapes t)) pc) =
      { denote x with pc := pc, pos := Function.update (denote x).pos t ((denote x).pos t-1) } := by
  apply wide_ext
  · rfl
  · funext k
    by_cases hk : k = t
    · subst k; simp [denote, changed, left_denote]
    · simp [denote, changed, hk]
  · funext k
    by_cases hk : k = t
    · subst k; simp [denote, changed, left_head _ hp]
    · simp [denote, changed, hk]

theorem changed_write {n : ℕ} (x : Config n) (t : Fin n) (s : Fin 9) (pc : ℕ) :
    denote (changed x t (write (x.tapes t) s) pc) =
      { denote x with
        pc := pc
        tape := Function.update (denote x).tape t
          (Function.update ((denote x).tape t) ((denote x).pos t) s) } := by
  apply wide_ext
  · rfl
  · funext k
    by_cases hk : k = t
    · subst k; simp [denote, changed, write_denote]
    · simp [denote, changed, hk]
  · funext k
    by_cases hk : k = t
    · subst k; simp [denote, changed, write_head]
    · simp [denote, changed, hk]

/-- Logical stack operations selected by a single instruction. This layer
does not yet represent the predicated circuit or its heap allocation. -/
inductive Execute {n : ℕ} : Instruction n → Config n → Config n → Prop
  | right (x : Config n) (t : Fin n) (pc : ℕ) : Execute (.move t true pc) x
      (changed x t (moveRight (x.tapes t)) pc)
  | left (x : Config n) (t : Fin n) (pc : ℕ) (h : (x.tapes t).left ≠ []) : Execute (.move t false pc) x
      (changed x t (moveLeft (x.tapes t)) pc)
  | write (x : Config n) (t : Fin n) (s : Fin 9) (pc : ℕ) : Execute (.write t s pc) x
      (changed x t (GalilScaffoldTape.write (x.tapes t) s) pc)
  | read (x : Config n) (t : Fin n) (cs : List (Fin 9 × ℕ)) (pc : ℕ)
      (h : ((x.tapes t).focus, pc) ∈ cs) : Execute (.read t cs) x { x with pc := pc }

theorem realize_step {n : ℕ} {i : Instruction n} {x y : GalilFppWide.Config n}
    (he : GalilFppWide.Execute i x y) (u : Config n) (hu : denote u = x) :
    ∃ v, Execute i u v ∧ denote v = y := by
  cases he with
  | right x t pc =>
    subst x
    exact ⟨_, .right u t pc, changed_right u t pc⟩
  | left x t pc hp =>
    subst x
    have hh : 0 < head (u.tapes t) := hp
    exact ⟨_, .left u t pc ((left_legal _).mpr hh), changed_left u t pc hh⟩
  | write x t s pc =>
    subst x
    exact ⟨_, .write u t s pc, changed_write u t s pc⟩
  | read x t cs pc hm =>
    subst x
    have hf : ((u.tapes t).focus, pc) ∈ cs := by
      simpa [denote, focus_eq] using hm
    exact ⟨_, .read u t cs pc hf, rfl⟩

inductive Completed {n : ℕ} (code : List (Instruction n)) : Config n → List ℕ → Config n → Prop
  | halt (x : Config n) (hi : code[x.pc]? = some .halt) : Completed code x [x.pc] x
  | step (x y z : Config n) (i : Instruction n) (qs : List ℕ)
      (hi : code[x.pc]? = some i) (he : Execute i x y) (hr : Completed code y qs z) :
      Completed code x (x.pc :: qs) z

/-- Every complete finite-tape execution has a logical-stack execution
with the same instruction trace and the same final tape interpretation. -/
theorem realize_completed {n : ℕ} {code : List (Instruction n)}
    {x y : GalilFppWide.Config n} {qs : List ℕ}
    (hr : GalilFppWide.Completed code x qs y) (u : Config n) (hu : denote u = x) :
    ∃ v, Completed code u qs v ∧ denote v = y := by
  induction hr generalizing u with
  | halt x hi =>
    have hp : u.pc = x.pc := congrArg GalilFppWide.Config.pc hu
    exact ⟨u, by simpa only [← hp] using Completed.halt u (by rw [hp]; exact hi), hu⟩
  | step x y z i qs hi he hr ih =>
    obtain ⟨v, hv, hve⟩ := realize_step he u hu
    obtain ⟨w, hw, hwe⟩ := ih v hve
    have hp : u.pc = x.pc := congrArg GalilFppWide.Config.pc hu
    exact ⟨w, by simpa only [← hp] using
      Completed.step u v w i qs (by rw [hp]; exact hi) hv hw, hwe⟩

theorem execute_sound {n : ℕ} {i : Instruction n} {x y : Config n}
    (he : Execute i x y) : GalilFppWide.Execute i (denote x) (denote y) := by
  cases he with
  | right x t pc => rw [changed_right]; exact .right _ _ _
  | left x t pc hp =>
    have hh := (left_legal _).mp hp
    rw [changed_left x t pc hh]
    exact .left _ _ _ hh
  | write x t s pc => rw [changed_write]; exact .write _ _ _ _
  | read x t cs pc hm =>
    exact .read _ _ _ _ (by simpa [denote, focus_eq] using hm)

theorem completed_sound {n : ℕ} {code : List (Instruction n)}
    {x y : Config n} {qs : List ℕ} (hr : Completed code x qs y) :
    GalilFppWide.Completed code (denote x) qs (denote y) := by
  induction hr with
  | halt x hi => exact .halt _ hi
  | step x y z i qs hi he hr ih => exact .step _ _ _ _ _ hi (execute_sound he) ih

#print axioms realize_step
#print axioms realize_completed
#print axioms completed_sound
end PalPeg.GalilScaffoldProgram
