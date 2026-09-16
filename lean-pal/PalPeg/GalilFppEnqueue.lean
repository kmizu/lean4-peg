import PalPeg.GalilFppMaterialize

set_option autoImplicit false
namespace PalPeg.GalilFppEnqueue
open GalilFppInstruction GalilFppCode GalilFppMaterialize

def pushed (b : Fin 2) (k : ℕ) (x : Config) : Config :=
  { x with
    pc := k
    pos := Function.update x.pos 5 (x.pos 5 + 1)
    tape := Function.update x.tape 5
      (Function.update (x.tape 5) (x.pos 5 + 1) (bitSymbol b)) }

def entry (j : Fin 7) : ℕ := [62,64,66,75,115,155,195][j.val]!
def target (j : Fin 7) : ℕ := [60,38,64,73,113,153,193][j.val]!
def bit (j : Fin 7) : Fin 2 := if j.val < 2 then 0 else 1

/-- All seven BACK-push sites in the exported Scala program. -/
theorem push_code (j : Fin 7) :
    code[entry j]? = some (.move 5 true (entry j - 1)) ∧
    code[entry j - 1]? = some (.write 5 (bitSymbol (bit j)) (target j)) := by
  fin_cases j <;> decide

theorem push_steps (j : Fin 7) (x : Config) (hp : x.pc = entry j) :
    Steps code x [entry j, entry j - 1] (pushed (bit j) (target j) x) := by
  let y : Config := { x with
    pc := entry j - 1
    pos := Function.update x.pos 5 (x.pos 5 + 1) }
  have he : Execute (.move 5 true (entry j - 1)) x y := .right _ _ _
  have hw : Execute (.write 5 (bitSymbol (bit j)) (target j)) y
      (pushed (bit j) (target j) x) := by
    simpa [y, pushed] using Execute.write y 5 (bitSymbol (bit j)) (target j)
  have hi : code[x.pc]? = some (.move 5 true (entry j - 1)) := by
    rw [hp]; exact (push_code j).1
  simpa only [hp] using Steps.step x y _ _ _ hi he
    (.step y _ _ _ [] (push_code j).2 hw (.nil _))

theorem pushed_queue (b : Fin 2) (k : ℕ) (x : Config) (q : List (Fin 2))
    (hq : QueueAt x q) : QueueAt (pushed b k x) (q ++ [b]) := by
  obtain ⟨bs, fs, hb, hf, he⟩ := hq
  refine ⟨b :: bs, fs, ?_, ?_, ?_⟩
  · simp only [pushed, Function.update_self]
    refine ⟨by omega, by simp, ?_⟩
    simp only [Nat.add_sub_cancel]
    apply stack_congr hb
    intro j hj
    have hn : j ≠ x.pos 5 + 1 := by omega
    simp [Function.update_of_ne hn]
  · simpa [pushed] using hf
  · simp [he, List.reverse_cons, List.append_assoc]

/-- Every actual enqueue site appends one bit and leaves C untouched. -/
theorem enqueue (j : Fin 7) (x : Config) (q : List (Fin 2))
    (hp : x.pc = entry j) (hq : QueueAt x q) :
    Steps code x [entry j, entry j - 1] (pushed (bit j) (target j) x) ∧
    QueueAt (pushed (bit j) (target j) x) (q ++ [bit j]) ∧
    (pushed (bit j) (target j) x).pos 2 = x.pos 2 ∧
    (pushed (bit j) (target j) x).tape 2 = x.tape 2 := by
  exact ⟨push_steps j x hp, pushed_queue _ _ _ _ hq, by simp [pushed], by simp [pushed]⟩

/-- Scala's failedAtLeft emits the complete unary delta block 10. -/
theorem failed_left (x : Config) (q : List (Fin 2))
    (hp : x.pc = 66) (hq : QueueAt x q) :
    ∃ y, Steps code x [66,65,64,63] y ∧ y.pc = 38 ∧
      QueueAt y (q ++ [1,0]) ∧ y.pos 2 = x.pos 2 ∧ y.tape 2 = x.tape 2 := by
  let y := pushed 1 64 x
  let z := pushed 0 38 y
  have h₁ : Steps code x [66,65] y := push_steps 2 x hp
  have h₂ : Steps code y [64,63] z := push_steps 1 y rfl
  have hq₁ : QueueAt y (q ++ [1]) := pushed_queue 1 64 x q hq
  have hq₂ : QueueAt z ((q ++ [1]) ++ [0]) := pushed_queue 0 38 y _ hq₁
  refine ⟨z, GalilFppCopy.steps_append h₁ h₂, rfl, ?_, ?_, ?_⟩
  · simpa [List.append_assoc] using hq₂
  · simp [z, y, pushed]
  · simp [z, y, pushed]

#print axioms failed_left
#print axioms enqueue
end PalPeg.GalilFppEnqueue
