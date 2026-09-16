import PalPeg.GalilFppDeltaTape

set_option autoImplicit false
namespace PalPeg.GalilFppForward
open GalilFppInstruction GalilFppCode GalilFppCopy GalilFppMaterialize GalilFppEnqueue

/-- Forward and backward traversal now use the same full-suffix invariant. -/
abbrev FullUnary := GalilFppFallbackBits.Unary

theorem full_push (t : ℕ → Fin 9) (n : ℕ) (hu : FullUnary t n) :
    FullUnary (Function.update t (n+1) 8) (n+1) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Function.update_of_ne (show 0 ≠ n+1 by omega)] using hu.1
  · intro k hk hkn
    by_cases he : k = n+1
    · subst k; simp
    · rw [Function.update_of_ne he]
      exact hu.2.1 k hk (by omega)
  · intro k hk
    rw [Function.update_of_ne (show k ≠ n+1 by omega)]
    exact hu.2.2 k (by omega)

def advanceOne (x : Config) : Config :=
  { x with
    pc := 39
    pos := Function.update (Function.update x.pos 3 (x.pos 3+1)) 2 (x.pos 2+1)
    tape := Function.update x.tape 3 (Function.update (x.tape 3) (x.pos 3+1) 8) }

theorem dispatch (b : Fin 2) (x : Config) (hp : x.pc = 39)
    (hc : x.tape 2 (x.pos 2) = bitSymbol b) :
    Steps code x [39,59] { x with pc := if b = 0 then 38 else 42 } := by
  let y : Config := { x with pc := 59 }
  have hi : code[x.pc]? = some (.read 2 [(7,59),(8,59),(6,59)]) := by rw [hp]; rfl
  have he : Execute (.read 2 [(7,59),(8,59),(6,59)]) x y :=
    .read _ _ _ _ (by rw [hc]; fin_cases b <;> simp [bitSymbol])
  have he' : Execute (.read 2 [(7,38),(8,42),(6,43)]) y
      { x with pc := if b = 0 then 38 else 42 } := by
    apply Execute.read
    change (x.tape 2 (x.pos 2), _) ∈ _
    rw [hc]
    fin_cases b <;> simp [bitSymbol]
  simpa only [hp] using Steps.step x y _ _ _ hi he (.step y _ _ _ [] rfl he' (.nil _))

theorem one_steps (x : Config) (hp : x.pc = 39) (hc : x.tape 2 (x.pos 2) = 8) :
    Steps code x [39,59,42,41,40] (advanceOne x) := by
  let y : Config := { x with pc := 42 }
  let z : Config := { y with pc := 41, pos := Function.update y.pos 3 (y.pos 3+1) }
  let u : Config := { z with
    pc := 40
    tape := Function.update z.tape 3 (Function.update (z.tape 3) (z.pos 3) 8) }
  have hd : Steps code x [39,59] y := dispatch 1 x hp hc
  have he : Execute (.move 2 true 39) u (advanceOne x) := by
    simpa [u, z, y, advanceOne] using Execute.right u 2 39
  exact steps_append hd (.step y z _ _ _ rfl (.right _ _ _)
    (.step z u _ _ _ rfl (.write _ _ _ _) (.step u _ _ _ [] rfl he (.nil _))))

theorem scan (n : ℕ) (x : Config) (q : List (Fin 2)) (hp : x.pc = 39)
    (hc : ∀ k, k < n → x.tape 2 (x.pos 2+k) = 8)
    (hz : x.tape 2 (x.pos 2+n) = 7) (hq : QueueAt x q)
    (hu : FullUnary (x.tape 3) (x.pos 3)) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 5*n+2 ∧ y.pc = 38 ∧
      y.pos 3 = x.pos 3+n ∧ y.pos 2 = x.pos 2+n ∧ y.tape 2 = x.tape 2 ∧
      QueueAt y q ∧ FullUnary (y.tape 3) (y.pos 3) ∧
      (∀ t, t ≠ 2 → t ≠ 3 → y.pos t = x.pos t ∧ y.tape t = x.tape t) := by
  induction n generalizing x with
  | zero =>
    have hd : Steps code x [39,59] { x with pc := 38 } := dispatch 0 x hp (by simpa [bitSymbol] using hz)
    exact ⟨_, _, hd, by simp, rfl, by simp, by simp, rfl, hq, hu, fun _ _ _ => ⟨rfl, rfl⟩⟩
  | succ n ih =>
    have hd := one_steps x hp (by simpa using hc 0 (by omega))
    have hc' : ∀ k, k < n → (advanceOne x).tape 2 ((advanceOne x).pos 2+k) = 8 := by
      intro k hk
      simpa [advanceOne, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc (k+1) (by omega)
    have hz' : (advanceOne x).tape 2 ((advanceOne x).pos 2+n) = 7 := by
      simpa [advanceOne, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz
    have hq' : QueueAt (advanceOne x) q := by simpa [QueueAt, advanceOne] using hq
    have hu' : FullUnary ((advanceOne x).tape 3) ((advanceOne x).pos 3) := by
      simpa [advanceOne] using full_push (x.tape 3) (x.pos 3) hu
    obtain ⟨y, qs, hs, hl, hpc, hyS, hyC, hyt, hyq, hyu, hframe⟩ := ih (advanceOne x) rfl hc' hz' hq' hu'
    refine ⟨y, [39,59,42,41,40] ++ qs, steps_append hd hs, ?_, hpc, ?_, ?_, ?_, hyq, hyu, ?_⟩
    · simp [hl]; omega
    · simp [advanceOne] at hyS; omega
    · simp [advanceOne] at hyC; omega
    · simpa [advanceOne] using hyt
    · intro t ht₂ ht₃
      simpa [advanceOne, Function.update_of_ne ht₂, Function.update_of_ne ht₃] using hframe t ht₂ ht₃

open GalilFppDelta GalilFppDeltaTape
variable {α : Type} [DecidableEq α]

/-- Actual matched branch, including the queued zero and forward S update.
This theorem handles a fully materialized delta block; lazy supply is separate. -/
theorem matched (w : List α) (p : ℕ) (x : Config) (q : List (Fin 2))
    (hp : x.pc = 62) (hC : x.pos 2 = position (failure w) p)
    (hS : x.pos 3 = p-failure w p) (hu : FullUnary (x.tape 3) (x.pos 3))
    (ht : Tape (x.tape 2) (failure w) (p+1)) (hq : QueueAt x q) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 5*delta (failure w) p+5 ∧ y.pc = 38 ∧
      y.pos 3 = p+1-failure w (p+1) ∧ y.pos 2 = position (failure w) (p+1) ∧
      y.tape 2 = x.tape 2 ∧ QueueAt y (q ++ [0]) ∧ FullUnary (y.tape 3) (y.pos 3) := by
  let z := pushed 0 60 x
  let u : Config := { z with pc := 39, pos := Function.update z.pos 2 (z.pos 2+1) }
  have hpush : Steps code x [62,61] z := push_steps 0 x hp
  have hmove : Steps code z [60] u := .step _ _ _ _ [] rfl (.right _ _ _) (.nil _)
  have hqz := pushed_queue 0 60 x q hq
  have hqu : QueueAt u (q ++ [0]) := by simpa [QueueAt, u] using hqz
  have huu : FullUnary (u.tape 3) (u.pos 3) := by simpa [u, z, pushed] using hu
  have hc : ∀ k, k < delta (failure w) p → u.tape 2 (u.pos 2+k) = 8 := by
    intro k hk
    simpa [u, z, pushed, hC] using ht.2 p (by omega) k hk
  have hpos := position_step (failure w) p
  have hz : u.tape 2 (u.pos 2+delta (failure w) p) = 7 := by
    have hh := ht.1 (p+1) (by omega)
    rw [hpos] at hh
    simpa [u, z, pushed, hC, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  obtain ⟨y, qs, hs, hl, hypc, hyS, hyC, hyt, hyq, hyu, _⟩ := scan (delta (failure w) p) u (q ++ [0]) rfl hc hz hqu huu
  refine ⟨y, [62,61,60] ++ qs, steps_append (steps_append hpush hmove) hs,
    ?_, hypc, ?_, ?_, ?_, hyq, hyu⟩
  · simp [hl]
  · simp [u, z, pushed, hS] at hyS
    have hf := failure_le w p
    have hg := failure_grows w p
    unfold delta at hyS
    omega
  · simp [u, z, pushed, hC] at hyC
    omega
  · simpa [u, z, pushed] using hyt

#print axioms matched
#print axioms scan
end PalPeg.GalilFppForward
