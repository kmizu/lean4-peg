import PalPeg.GalilFppEnqueue

set_option autoImplicit false
namespace PalPeg.GalilFppFallbackBits
open GalilFppInstruction GalilFppCode GalilFppCopy GalilFppMaterialize GalilFppEnqueue

def offset (j : Fin 4) : ℕ := 40 * j.val

/-- The four append-distance fallback instances share this cached dispatch. -/
theorem dispatch (j : Fin 4) (b : Fin 2) (x : Config)
    (hp : x.pc = 70 + offset j) (hc : x.tape 2 (x.pos 2) = bitSymbol b) :
    Steps code x [70 + offset j,95 + offset j]
      { x with pc := 75 + offset j + 3*b.val } := by
  let y : Config := { x with pc := 95 + offset j }
  have hi : code[x.pc]? = some (.read 2 [(7,95+offset j),(8,95+offset j),(6,95+offset j)]) := by
    rw [hp]; fin_cases j <;> rfl
  have he : Execute (.read 2 [(7,95+offset j),(8,95+offset j),(6,95+offset j)]) x y :=
    .read _ _ _ _ (by rw [hc]; fin_cases b <;> simp [bitSymbol])
  have hi' : code[y.pc]? = some (.read 2 [(7,75+offset j),(8,78+offset j),(6,79+offset j)]) := by
    fin_cases j <;> rfl
  have he' : Execute (.read 2 [(7,75+offset j),(8,78+offset j),(6,79+offset j)]) y
      { x with pc := 75 + offset j + 3*b.val } := by
    apply Execute.read
    change (x.tape 2 (x.pos 2), _) ∈ _
    rw [hc]
    fin_cases b <;> simp [bitSymbol]
    omega
  simpa only [hp] using Steps.step x y _ _ _ hi he (.step y _ _ _ [] hi' he' (.nil _))

def afterOne (j : Fin 4) (x : Config) : Config :=
  { x with
    pc := 70 + offset j
    pos := Function.update (Function.update x.pos 3 (x.pos 3 - 1)) 2 (x.pos 2 - 1)
    tape := Function.update x.tape 3 (Function.update (x.tape 3) (x.pos 3) 6) }

/-- A cached one pops S and moves C left, in five actual instructions. -/
theorem one_steps (j : Fin 4) (x : Config) (hp : x.pc = 70 + offset j)
    (hc : x.tape 2 (x.pos 2) = 8) (hS : 0 < x.pos 3) (hC : 0 < x.pos 2) :
    Steps code x [70+offset j,95+offset j,78+offset j,77+offset j,76+offset j] (afterOne j x) := by
  let y : Config := { x with pc := 78 + offset j }
  let z : Config := { y with
    pc := 77 + offset j
    tape := Function.update y.tape 3 (Function.update (y.tape 3) (y.pos 3) 6) }
  let u : Config := { z with pc := 76 + offset j, pos := Function.update z.pos 3 (z.pos 3 - 1) }
  have hd : Steps code x [70+offset j,95+offset j] y := by
    have ho : 75 + offset j + 3 = 78 + offset j := by omega
    simpa [y, ho] using dispatch j 1 x hp hc
  have hi : code[y.pc]? = some (.write 3 6 (77+offset j)) := by fin_cases j <;> rfl
  have hi' : code[z.pc]? = some (.move 3 false (76+offset j)) := by fin_cases j <;> rfl
  have hi'' : code[u.pc]? = some (.move 2 false (70+offset j)) := by fin_cases j <;> rfl
  have he : Execute (.move 2 false (70+offset j)) u (afterOne j x) := by
    simpa [u, z, y, afterOne] using Execute.left u 2 (70+offset j) (by simpa [u, z, y] using hC)
  exact steps_append hd (.step y z _ _ _ hi (.write _ _ _ _)
    (.step z u _ _ _ hi' (.left _ _ _ hS) (.step u _ _ _ [] hi'' he (.nil _))))

def afterZero (j : Fin 4) (x : Config) : Config :=
  let y := pushed 1 (73 + offset j) x
  { y with
    pc := 69 + offset j
    pos := Function.update (Function.update y.pos 0 (y.pos 0 - 1)) 4 (y.pos 4 - 1)
    tape := Function.update y.tape 4 (Function.update (y.tape 4) (y.pos 4) 6) }

/-- A cached zero appends one distance bit, moves A left and pops T. -/
theorem zero_steps (j : Fin 4) (x : Config) (hp : x.pc = 70 + offset j)
    (hc : x.tape 2 (x.pos 2) = 7) (hA : 0 < x.pos 0) (hT : 0 < x.pos 4) :
    Steps code x [70+offset j,95+offset j,75+offset j,74+offset j,73+offset j,72+offset j,71+offset j]
      (afterZero j x) := by
  let y : Config := { x with pc := 75 + offset j }
  let z := pushed 1 (73 + offset j) y
  let u : Config := { z with pc := 72 + offset j, pos := Function.update z.pos 0 (z.pos 0 - 1) }
  let v : Config := { u with
    pc := 71 + offset j
    tape := Function.update u.tape 4 (Function.update (u.tape 4) (u.pos 4) 6) }
  have hd : Steps code x [70+offset j,95+offset j] y := dispatch j 0 x hp hc
  have hpush : Steps code y [75+offset j,74+offset j] z := by
    fin_cases j
    · exact push_steps 3 y rfl
    · exact push_steps 4 y rfl
    · exact push_steps 5 y rfl
    · exact push_steps 6 y rfl
  have hi : code[z.pc]? = some (.move 0 false (72+offset j)) := by fin_cases j <;> rfl
  have hi' : code[u.pc]? = some (.write 4 6 (71+offset j)) := by fin_cases j <;> rfl
  have hi'' : code[v.pc]? = some (.move 4 false (69+offset j)) := by fin_cases j <;> rfl
  have he : Execute (.move 4 false (69+offset j)) v (afterZero j x) := by
    simpa [v, u, z, y, afterZero, pushed] using
      Execute.left v 4 (69+offset j) (by simpa [v, u, z, y, pushed] using hT)
  have ht := Steps.step z u _ _ _ hi (.left _ _ _ (by simpa [z, y, pushed] using hA))
    (.step u v _ _ _ hi' (.write _ _ _ _) (.step v _ _ _ [] hi'' he (.nil _)))
  exact steps_append hd (steps_append hpush ht)

theorem zero_queue (j : Fin 4) (x : Config) (q : List (Fin 2)) (hq : QueueAt x q) :
    QueueAt (afterZero j x) (q ++ [1]) := by
  have hh := pushed_queue 1 (73+offset j) x q hq
  simpa [QueueAt, afterZero, pushed] using hh

theorem one_queue (j : Fin 4) (x : Config) (q : List (Fin 2)) (hq : QueueAt x q) :
    QueueAt (afterOne j x) q := by
  simpa [QueueAt, afterOne] using hq

/-- A unary stack with its entire unused suffix blank, suitable for both
copy restoration and arbitrarily many subsequent pushes. -/
def Unary (t : ℕ → Fin 9) (n : ℕ) : Prop :=
  t 0 = 4 ∧ (∀ k, 1 ≤ k → k ≤ n → t k = 8) ∧ (∀ k, n < k → t k = 6)

theorem unary_pop (t : ℕ → Fin 9) (n : ℕ) (hn : 0 < n) (ht : Unary t n) :
    Unary (Function.update t n 6) (n-1) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Function.update_of_ne (show 0 ≠ n by omega)] using ht.1
  · intro k hk hkn
    rw [Function.update_of_ne (show k ≠ n by omega)]
    exact ht.2.1 k hk (by omega)
  · intro k hk
    by_cases he : k = n
    · subst k; simp
    · rw [Function.update_of_ne he]
      exact ht.2.2 k (by omega)

theorem one_unary (j : Fin 4) (x : Config) (hp : 0 < x.pos 3)
    (hu : Unary (x.tape 3) (x.pos 3)) : Unary ((afterOne j x).tape 3) ((afterOne j x).pos 3) := by
  simpa [afterOne] using unary_pop (x.tape 3) (x.pos 3) hp hu

theorem zero_unary (j : Fin 4) (x : Config) (hu : Unary (x.tape 3) (x.pos 3)) :
    Unary ((afterZero j x).tape 3) ((afterZero j x).pos 3) := by
  simpa [afterZero, pushed] using hu

/-- An arbitrary run of cached delta ones consumes exactly that many S
cells and C positions. This is a real instruction trace, not a counter model. -/
theorem ones_steps (j : Fin 4) (n : ℕ) (x : Config) (q : List (Fin 2))
    (hp : x.pc = 70 + offset j) (hS : n ≤ x.pos 3) (hC : n ≤ x.pos 2)
    (hc : ∀ k, k < n → x.tape 2 (x.pos 2 - k) = 8) (hq : QueueAt x q) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 5*n ∧ y.pc = 70 + offset j ∧
      y.pos 3 = x.pos 3 - n ∧ y.pos 2 = x.pos 2 - n ∧ y.tape 2 = x.tape 2 ∧ QueueAt y q ∧
      (∀ t, t ≠ 2 → t ≠ 3 → y.pos t = x.pos t ∧ y.tape t = x.tape t) ∧
      (Unary (x.tape 3) (x.pos 3) → Unary (y.tape 3) (y.pos 3)) := by
  induction n generalizing x with
  | zero => exact ⟨x, [], .nil _, by simp, hp, by simp, by simp, rfl, hq, (fun _ _ _ => ⟨rfl, rfl⟩), id⟩
  | succ n ih =>
    have hbit : x.tape 2 (x.pos 2) = 8 := by simpa using hc 0 (by omega)
    have hs := one_steps j x hp hbit (by omega) (by omega)
    have hc' : ∀ k, k < n → (afterOne j x).tape 2 ((afterOne j x).pos 2 - k) = 8 := by
      intro k hk
      have hh := hc (k+1) (by omega)
      have he : x.pos 2 - 1 - k = x.pos 2 - (k+1) := by omega
      simpa [afterOne, he] using hh
    obtain ⟨y, qs, hr, hl, hpc, hys, hyc, hyt, hyq, hframe, hunary⟩ := ih (afterOne j x) rfl
      (by simp [afterOne]; omega) (by simp [afterOne]; omega) hc' (one_queue j x q hq)
    refine ⟨y, [70+offset j,95+offset j,78+offset j,77+offset j,76+offset j] ++ qs,
      steps_append hs hr, ?_, hpc, ?_, ?_, ?_, hyq, ?_, ?_⟩
    · simp [hl]; omega
    · simp [afterOne] at hys; omega
    · simp [afterOne] at hyc; omega
    · simpa [afterOne] using hyt
    · intro t ht₂ ht₃
      simpa [afterOne, Function.update_of_ne ht₂, Function.update_of_ne ht₃] using hframe t ht₂ ht₃
    · intro hu
      exact hunary (one_unary j x (by omega) hu)

theorem zero_effect (j : Fin 4) (x : Config) :
    (afterZero j x).pos 0 = x.pos 0 - 1 ∧
    (afterZero j x).pos 4 = x.pos 4 - 1 ∧
    (afterZero j x).pos 3 = x.pos 3 ∧
    (afterZero j x).pos 2 = x.pos 2 ∧
    (afterZero j x).tape 2 = x.tape 2 ∧
    (afterZero j x).tape 4 (x.pos 4) = 6 := by
  simp [afterZero, pushed]

#print axioms ones_steps
#print axioms one_steps
#print axioms zero_steps
end PalPeg.GalilFppFallbackBits
