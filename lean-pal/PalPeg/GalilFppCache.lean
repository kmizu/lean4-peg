import PalPeg.GalilFppEnqueue

set_option autoImplicit false
namespace PalPeg.GalilFppCache
open GalilFppInstruction GalilFppCode GalilFppMaterialize

/-- C holds a materialized prefix, followed only by blank cells. -/
def CacheAt (x : Config) (s : ℕ → Fin 2) (n : ℕ) : Prop :=
  (∀ i, i < n → x.tape 2 i = bitSymbol (s i)) ∧
  (∀ i, n ≤ i → x.tape 2 i = 6)

theorem extend_cache (x y : Config) (s : ℕ → Fin 2) (n : ℕ)
    (hc : CacheAt x s n)
    (he : y.tape 2 = Function.update (x.tape 2) n (bitSymbol (s n))) :
    CacheAt y s (n + 1) := by
  constructor
  · intro i hi
    rw [he]
    by_cases hn : i = n
    · subst i; simp
    · rw [Function.update_of_ne hn]
      exact hc.1 i (by omega)
  · intro i hi
    rw [he, Function.update_of_ne (show i ≠ n by omega)]
    exact hc.2 i (by omega)

/-- At the blank frontier, actual deltaRead extends the cache by exactly
one reference bit and removes exactly that bit from the pending FIFO. -/
theorem read_frontier (x : Config) (s : ℕ → Fin 2) (n : ℕ) (rest : List (Fin 2))
    (hp : x.pc = 26) (hhead : x.pos 2 = n)
    (hc : CacheAt x s n) (hq : QueueAt x (s n :: rest)) :
    ∃ y qs, Steps code x qs y ∧ y.pc = destination (s n) ∧
      y.pos 2 = n ∧ CacheAt y s (n + 1) ∧ QueueAt y rest := by
  have hblank : x.tape 2 (x.pos 2) = 6 := by rw [hhead]; exact hc.2 n (by omega)
  obtain ⟨y, qs, hs, hpc, hpos, _, hqueue, hframe, _⟩ := dequeue (s n) rest x hp hblank hq
  rw [hhead] at hframe hpos
  exact ⟨y, qs, hs, hpc, hpos, extend_cache x y s n hc hframe, hqueue⟩

/-- Reads inside the cache return the reference bit without consuming FIFO. -/
theorem read_cached (x : Config) (s : ℕ → Fin 2) (n : ℕ) (q : List (Fin 2))
    (hp : x.pc = 26) (hh : x.pos 2 < n) (hc : CacheAt x s n) (hq : QueueAt x q) :
    ∃ y, Steps code x [26] y ∧ y.pc = destination (s (x.pos 2)) ∧
      y.pos 2 = x.pos 2 ∧ CacheAt y s n ∧ QueueAt y q := by
  exact ⟨{ x with pc := destination (s (x.pos 2)) },
    cached _ x hp (hc.1 _ hh), rfl, rfl, hc, hq⟩

/-- With the head in the materialized prefix or at its frontier, the two
actual paths return the same reference stream; materialization is lazy. -/
theorem read_correct (x : Config) (s : ℕ → Fin 2) (n : ℕ) (q : List (Fin 2))
    (hp : x.pc = 26) (hh : x.pos 2 ≤ n) (hc : CacheAt x s n) (hq : QueueAt x q)
    (hnext : x.pos 2 = n → ∃ rest, q = s n :: rest) :
    ∃ y qs m r, Steps code x qs y ∧ y.pc = destination (s (x.pos 2)) ∧
      y.pos 2 = x.pos 2 ∧ CacheAt y s m ∧ QueueAt y r ∧
      ((m = n ∧ r = q) ∨ (m = n + 1 ∧ q = s n :: r)) := by
  by_cases hlt : x.pos 2 < n
  · obtain ⟨y, hs, hp', hh', hc', hq'⟩ := read_cached x s n q hp hlt hc hq
    exact ⟨y, [26], n, q, hs, hp', hh', hc', hq', Or.inl ⟨rfl, rfl⟩⟩
  · have he : x.pos 2 = n := by omega
    obtain ⟨rest, hr⟩ := hnext he
    rw [hr] at hq
    obtain ⟨y, qs, hs, hp', hh', hc', hq'⟩ := read_frontier x s n rest hp he hc hq
    exact ⟨y, qs, n + 1, rest, hs, by simpa [he] using hp', hh'.trans he.symm,
      hc', hq', Or.inr ⟨rfl, hr⟩⟩

/-- Enqueuing at any actual BACK-push site preserves the complete cache. -/
theorem enqueue_preserves_cache (j : Fin 7) (x : Config) (s : ℕ → Fin 2)
    (n : ℕ) (q : List (Fin 2)) (hp : x.pc = GalilFppEnqueue.entry j)
    (hc : CacheAt x s n) (hq : QueueAt x q) :
    ∃ y, Steps code x [GalilFppEnqueue.entry j, GalilFppEnqueue.entry j - 1] y ∧
      CacheAt y s n ∧ QueueAt y (q ++ [GalilFppEnqueue.bit j]) := by
  obtain ⟨hs, hq', _, ht⟩ := GalilFppEnqueue.enqueue j x q hp hq
  refine ⟨_, hs, ?_, hq'⟩
  unfold CacheAt
  rw [ht]
  exact hc

#print axioms enqueue_preserves_cache
#print axioms read_correct
end PalPeg.GalilFppCache
