import PalPeg.GalilFppForward
import PalPeg.GalilFppReadInstances
import PalPeg.GalilFppCache

set_option autoImplicit false
namespace PalPeg.GalilFppLazyForward
open GalilFppInstruction GalilFppCode GalilFppMaterialize GalilFppCache GalilFppForward

/-- FIFO contents are the not-yet-materialized suffix of the reference stream. -/
def Aligned (s : ℕ → Fin 2) : ℕ → List (Fin 2) → Prop
  | _, [] => True
  | n, b :: rest => b = s n ∧ Aligned s (n+1) rest

def Supply (x : Config) (s : ℕ → Fin 2) (n : ℕ) (q : List (Fin 2)) : Prop :=
  CacheAt x s n ∧ QueueAt x q ∧ Aligned s n q

/-- Both actual read paths satisfy one stream contract. The total available
prefix length is unchanged even when a FIFO bit moves into the cache. -/
theorem read (x : Config) (s : ℕ → Fin 2) (n : ℕ) (q : List (Fin 2))
    (hp : x.pc = 39) (hh : x.pos 2 ≤ n) (ha : x.pos 2 < n+q.length)
    (hs : Supply x s n q) :
    ∃ y qs m r, Steps code x qs y ∧ y.pc = (if s (x.pos 2) = 0 then 38 else 42) ∧
      y.pos 2 = x.pos 2 ∧ y.pos 2 < m ∧ Supply y s m r ∧
      n ≤ m ∧ m+r.length = n+q.length ∧
      (∀ t, t ≠ 2 → t ≠ 5 → t ≠ 6 → y.pos t = x.pos t ∧ y.tape t = x.tape t) := by
  by_cases hlt : x.pos 2 < n
  · have hc := hs.1.1 (x.pos 2) hlt
    refine ⟨{ x with pc := if s (x.pos 2) = 0 then 38 else 42 }, [39,59], n, q,
      GalilFppForward.dispatch _ x hp hc, rfl, rfl, hlt, hs, le_refl _, rfl, ?_⟩
    exact fun _ _ _ _ => ⟨rfl, rfl⟩
  · have he : x.pos 2 = n := by omega
    cases q with
    | nil => simp at ha; omega
    | cons b rest =>
      have hb : b = s n := hs.2.2.1
      have hblank : x.tape 2 (x.pos 2) = 6 := hs.1.2 _ (by omega)
      obtain ⟨y, qs, hr, hpc, hpos, _, hq, ht, hframe⟩ :=
        GalilFppReadInstances.forward_blank b rest x hp hblank hs.2.1
      have hc : CacheAt y s (n+1) := by
        apply extend_cache x y s n hs.1
        simpa [he, hb] using ht
      refine ⟨y, qs, n+1, rest, hr, ?_, hpos, by omega, ⟨hc, hq, hs.2.2.2⟩,
        by omega, ?_, hframe⟩
      · simpa [he, hb] using hpc
      · simp; omega

/-- Finish the one-bit continuation after either kind of read. -/
theorem advance_tail (x : Config) (hp : x.pc = 42) :
    Steps code x [42,41,40] (advanceOne x) := by
  let y : Config := { x with pc := 41, pos := Function.update x.pos 3 (x.pos 3+1) }
  let z : Config := { y with
    pc := 40
    tape := Function.update y.tape 3 (Function.update (y.tape 3) (y.pos 3) 8) }
  have hi : code[x.pc]? = some (.move 3 true 41) := by rw [hp]; rfl
  have he : Execute (.move 2 true 39) z (advanceOne x) := by
    simpa [z, y, advanceOne] using Execute.right z 2 39
  simpa only [hp] using Steps.step x y _ _ _ hi (.right _ _ _)
    (.step y z _ _ _ rfl (.write _ _ _ _) (.step z _ _ _ [] rfl he (.nil _)))

/-- A complete forward delta block may straddle the cache/FIFO frontier.
Each one grows S, the final zero exits, and every read preserves Supply. -/
theorem scan (d : ℕ) (x : Config) (s : ℕ → Fin 2) (n : ℕ) (q : List (Fin 2))
    (hp : x.pc = 39) (hh : x.pos 2 ≤ n) (ha : x.pos 2+d < n+q.length)
    (hs : Supply x s n q) (hu : FullUnary (x.tape 3) (x.pos 3))
    (ho : ∀ k, k < d → s (x.pos 2+k) = 1) (hz : s (x.pos 2+d) = 0) :
    ∃ y qs m r, Steps code x qs y ∧ y.pc = 38 ∧ y.pos 2 = x.pos 2+d ∧
      y.pos 3 = x.pos 3+d ∧ FullUnary (y.tape 3) (y.pos 3) ∧
      Supply y s m r ∧ n ≤ m ∧ m+r.length = n+q.length ∧ y.pos 2 < m ∧
      (∀ t, t ≠ 2 → t ≠ 3 → t ≠ 5 → t ≠ 6 →
        y.pos t = x.pos t ∧ y.tape t = x.tape t) := by
  induction d generalizing x n q with
  | zero =>
    obtain ⟨y, qs, m, r, hr, hpc, hpos, hlt, hsup, hmn, hav, hframe⟩ :=
      read x s n q hp hh (by simpa using ha) hs
    obtain ⟨hSp, hSt⟩ := hframe 3 (by decide) (by decide) (by decide)
    refine ⟨y, qs, m, r, hr, ?_, by simpa using hpos, by simpa using hSp, ?_, hsup, hmn, hav,
      hlt, fun t h2 _ h5 h6 => hframe t h2 h5 h6⟩
    · have hzero : s (x.pos 2) = 0 := by simpa using hz
      simpa [hzero] using hpc
    · simpa [hSp, hSt] using hu
  | succ d ih =>
    have hbit : s (x.pos 2) = 1 := by simpa using ho 0 (by omega)
    obtain ⟨z, qs, m, r, hr, hpc, hpos, hlt, hsup, hmn, hav, hframe⟩ :=
      read x s n q hp hh (by omega) hs
    have hpc' : z.pc = 42 := by simpa [hbit] using hpc
    have ht := advance_tail z hpc'
    let u := advanceOne z
    obtain ⟨hSp, hSt⟩ := hframe 3 (by decide) (by decide) (by decide)
    have huZ : FullUnary (z.tape 3) (z.pos 3) := by simpa [hSp, hSt] using hu
    have huU : FullUnary (u.tape 3) (u.pos 3) := by
      simpa [u, advanceOne] using full_push (z.tape 3) (z.pos 3) huZ
    have hsU : Supply u s m r := by simpa [Supply, CacheAt, QueueAt, u, advanceOne] using hsup
    have hC : u.pos 2 = x.pos 2+1 := by simp [u, advanceOne, hpos]
    have hS : u.pos 3 = x.pos 3+1 := by simp [u, advanceOne, hSp]
    have hoU : ∀ k, k < d → s (u.pos 2+k) = 1 := by
      intro k hk
      simpa [hC, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ho (k+1) (by omega)
    have hzU : s (u.pos 2+d) = 0 := by
      simpa [hC, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz
    obtain ⟨y, rs, l, v, hrun, hyPC, hyC, hyS, hyU, hySup, hml, htotal, hylt, hyframe⟩ :=
      ih u m r rfl (by simp [u, advanceOne]; omega) (by omega) hsU huU hoU hzU
    refine ⟨y, qs ++ [42,41,40] ++ rs,
      l, v, GalilFppCopy.steps_append (GalilFppCopy.steps_append hr ht) hrun,
      hyPC, ?_, ?_, hyU, hySup, by omega, by omega, hylt, ?_⟩
    · omega
    · omega
    · intro t h2 h3 h5 h6
      obtain ⟨hyp, hyt⟩ := hyframe t h2 h3 h5 h6
      obtain ⟨hzp, hzt⟩ := hframe t h2 h5 h6
      simpa [u, advanceOne, h2, h3, hzp, hzt] using And.intro hyp hyt

#print axioms scan
#print axioms read
end PalPeg.GalilFppLazyForward
