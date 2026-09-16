import PalPeg.GalilFppFrontier

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PalPeg.GalilFppWriteOnce
open GalilFppInstruction GalilFppCode

/-- The six deltaRead refill regions, entered only by a blank-C test. -/
def needsBlank (q : ℕ) : Bool :=
  [10,43,79,119,159,199].any (fun b => decide (b ≤ q ∧ q < b + 16))

def guard (q : ℕ) : Instruction → Bool
  | .move t _ n => if t = 2 then !needsBlank n else !needsBlank n || needsBlank q
  | .write t _ n => if t = 2 then needsBlank q && !needsBlank n else !needsBlank n || needsBlank q
  | .read t cs => if t = 2 then cs.all (fun p => !needsBlank p.2 || p.1 == 6)
      else (cs.map Prod.snd).all (fun n => !needsBlank n || needsBlank q)
  | i => (successors i).all (fun n => !needsBlank n || needsBlank q)

theorem code_guard : (code.zipIdx).all (fun p => guard p.2 p.1) = true := by decide

theorem lookup_guard {q : ℕ} {i : Instruction} (hi : code[q]? = some i) : guard q i = true := by
  obtain ⟨hq, he⟩ := List.getElem?_eq_some_iff.mp hi
  have hh := List.forall_mem_zipIdx'.mp (List.all_eq_true.mp code_guard) q hq
  simpa only [he] using hh

def Invariant (x : Config) : Prop := needsBlank x.pc = true → x.tape 2 (x.pos 2) = 6

theorem step_invariant {i : Instruction} {x y : Config} (hi : code[x.pc]? = some i)
    (he : Execute i x y) (hx : Invariant x) : Invariant y := by
  have hg := lookup_guard hi
  intro hy
  cases he with
  | right x t k =>
    change needsBlank k = true at hy
    by_cases ht : t = 2
    · simp [guard, ht, hy] at hg
    · have hp : needsBlank x.pc = true := by simpa [guard, ht, hy] using hg
      simpa [Function.update_of_ne (Ne.symm ht)] using hx hp
  | left x t k hp =>
    change needsBlank k = true at hy
    by_cases ht : t = 2
    · simp [guard, ht, hy] at hg
    · have hpc : needsBlank x.pc = true := by simpa [guard, ht, hy] using hg
      simpa [Function.update_of_ne (Ne.symm ht)] using hx hpc
  | write x t s k =>
    change needsBlank k = true at hy
    by_cases ht : t = 2
    · simp [guard, ht, hy] at hg
    · have hp : needsBlank x.pc = true := by simpa [guard, ht, hy] using hg
      simpa [Function.update_of_ne (Ne.symm ht)] using hx hp
  | read x t cs k hm =>
    change needsBlank k = true at hy
    by_cases ht : t = 2
    · subst t
      simp only [guard] at hg
      have hh := List.all_eq_true.mp hg _ hm
      simpa [hy] using hh
    · simp only [guard, ht, ↓reduceIte] at hg
      have hh := List.all_eq_true.mp hg k (List.mem_map.mpr ⟨_, hm, rfl⟩)
      exact hx (by simpa [hy] using hh)
  | emit x k =>
    change needsBlank k = true at hy
    exact hx (by simpa [guard, successors, hy] using hg)

theorem steps_invariant {x y : Config} {qs : List ℕ} (hs : Steps code x qs y)
    (hx : Invariant x) : Invariant y := by
  induction hs with
  | nil => exact hx
  | step x y z i qs hi he hs ih => exact ih (step_invariant hi he hx)

/-- Every actual C write operates on a blank cell. -/
theorem write_blank {x : Config} {s : Fin 9} {k : ℕ}
    (hi : code[x.pc]? = some (.write 2 s k)) (hx : Invariant x) :
    x.tape 2 (x.pos 2) = 6 := by
  have hg := lookup_guard hi
  have hp : needsBlank x.pc = true := by
    simp only [guard, ↓reduceIte, Bool.and_eq_true] at hg
    exact hg.1
  exact hx hp

/-- No already materialized C cell changes in any single instruction. -/
theorem step_preserves {i : Instruction} {x y : Config} (hi : code[x.pc]? = some i)
    (he : Execute i x y) (hx : Invariant x) (j : ℕ) (hj : x.tape 2 j ≠ 6) :
    y.tape 2 j = x.tape 2 j := by
  cases he with
  | write x t s k =>
    by_cases ht : t = 2
    · subst t
      have hb := write_blank hi hx
      have hn : j ≠ x.pos 2 := by intro hh; subst j; exact hj hb
      simp [Function.update_of_ne hn]
    · simp [Function.update_of_ne (Ne.symm ht)]
  | _ => rfl

/-- Once materialized, every C cell is immutable over arbitrary finite runs. -/
theorem steps_preserve {x y : Config} {qs : List ℕ} (hs : Steps code x qs y)
    (hx : Invariant x) (j : ℕ) (hj : x.tape 2 j ≠ 6) : y.tape 2 j = x.tape 2 j := by
  induction hs with
  | nil => rfl
  | step x y z i qs hi he hs ih =>
    have ht := step_preserves hi he hx j hj
    exact (ih (step_invariant hi he hx) (by simpa [ht] using hj)).trans ht

theorem initial_invariant (x : Config) (hp : x.pc = start) : Invariant x := by
  intro h
  simp [hp, start, needsBlank] at h

/-- Combining both control invariants locates every C write exactly at
the materialization frontier, rather than assuming that location. -/
theorem write_at_frontier {x : Config} {s : Fin 9} {k n : ℕ}
    (hi : code[x.pc]? = some (.write 2 s k)) (hx : Invariant x)
    (hb : GalilFppFrontier.Bounded x n) : x.pos 2 = n := by
  have hh := write_blank hi hx
  have hnot : ¬x.pos 2 < n := fun h => hb.1.1 _ h hh
  have := hb.2.1
  omega

/-- From the actual start and initial C, every reachable C-write PC
writes precisely the first blank cell of a contiguous cache. -/
theorem reachable_write_frontier {x y : Config} {qs : List ℕ} {s : Fin 9} {k : ℕ}
    (hs : Steps code x qs y) (hpc : x.pc = start)
    (ht : x.tape 2 = GalilFppFrontier.initialC) (hp : x.pos 2 = 0)
    (hi : code[y.pc]? = some (.write 2 s k)) :
    ∃ n, 3 ≤ n ∧ GalilFppFrontier.Shape (y.tape 2) n ∧ y.pos 2 = n := by
  obtain ⟨n, hn, hb⟩ := GalilFppFrontier.steps_bounded hs 3
    (GalilFppFrontier.initial_bounded x ht hp)
  have hwrite := steps_invariant hs (initial_invariant x hpc)
  exact ⟨n, hn, hb.1, write_at_frontier hi hwrite hb⟩

/-- Any materialized cell at a reachable state survives every subsequent
successful execution prefix, without a cache assumption on that suffix. -/
theorem reachable_cell_immutable {x y z : Config} {as bs : List ℕ}
    (ha : Steps code x as y) (hb : Steps code y bs z) (hp : x.pc = start)
    (j : ℕ) (hj : y.tape 2 j ≠ 6) : z.tape 2 j = y.tape 2 j := by
  exact steps_preserve hb (steps_invariant ha (initial_invariant x hp)) j hj

#print axioms reachable_write_frontier
#print axioms reachable_cell_immutable
#print axioms steps_preserve
#print axioms write_at_frontier
end PalPeg.GalilFppWriteOnce
