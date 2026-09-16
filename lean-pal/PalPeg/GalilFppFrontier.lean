import PalPeg.GalilFppCode

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PalPeg.GalilFppFrontier
open GalilFppInstruction GalilFppCode

/-- PCs at which C may be blank. The complement is the backwards closure
of the two right moves, stopping at C tests, writes, and left moves. -/
def blankSafe (q : ℕ) : Bool := !([ 37,38,40,41,42,60,61,62,63,64,65,66,67,68,69,71,72,73,74,75,97,98,99,100,101,102,103,104,105,106,107,108,109,111,112,113,114,115,137,138,139,140,141,142,143,144,145,146,147,148,149,151,152,153,154,155,177,178,179,180,181,182,183,184,185,186,187,188,189,191,192,193,194,195,217,218,219,220,221,222,223,224,225,226,227 ] : List ℕ).contains q

def guard (q : ℕ) : Instruction → Bool
  | .move t true n => if t = 2 then !blankSafe q && blankSafe n else !blankSafe q || blankSafe n
  | .move t false n => if t = 2 then true else !blankSafe q || blankSafe n
  | .write t s n => if t = 2 then s != 6 else !blankSafe q || blankSafe n
  | .read t cs => if t = 2 then !blankSafe q || cs.all (fun p => p.1 != 6 || blankSafe p.2)
      else !blankSafe q || (cs.map Prod.snd).all blankSafe
  | i => !blankSafe q || (successors i).all blankSafe

/-- The certificate checks all 228 actual instructions, not sample runs. -/
theorem code_guard : (code.zipIdx).all (fun p => guard p.2 p.1) = true := by decide

theorem lookup_guard {q : ℕ} {i : Instruction} (hi : code[q]? = some i) : guard q i = true := by
  obtain ⟨hq, he⟩ := List.getElem?_eq_some_iff.mp hi
  have hh := List.forall_mem_zipIdx'.mp (List.all_eq_true.mp code_guard) q hq
  simpa only [he] using hh

def Shape (t : ℕ → Fin 9) (n : ℕ) : Prop :=
  (∀ j, j < n → t j ≠ 6) ∧ (∀ j, n ≤ j → t j = 6)

def Bounded (x : Config) (n : ℕ) : Prop :=
  Shape (x.tape 2) n ∧ x.pos 2 ≤ n ∧
    (x.tape 2 (x.pos 2) = 6 → blankSafe x.pc = true)

theorem write_shape (t : ℕ → Fin 9) (n p : ℕ) (s : Fin 9)
    (hs : Shape t n) (hp : p ≤ n) (hb : s ≠ 6) :
    Shape (Function.update t p s) (if p = n then n + 1 else n) := by
  constructor
  · intro j hj
    by_cases he : j = p
    · subst j; simpa using hb
    · rw [Function.update_of_ne he]
      apply hs.1
      split at hj <;> omega
  · intro j hj
    have he : j ≠ p := by split at hj <;> omega
    rw [Function.update_of_ne he]
    apply hs.2
    split at hj <;> omega

theorem step_bounded {i : Instruction} {x y : Config} (hi : code[x.pc]? = some i)
    (he : Execute i x y) (n : ℕ) (hx : Bounded x n) :
    ∃ m, n ≤ m ∧ m ≤ n + 1 ∧ Bounded y m := by
  have hg := lookup_guard hi
  obtain ⟨hshape, hpos, hsafe⟩ := hx
  cases he with
  | right x t k =>
    by_cases ht : t = 2
    · subst t
      have hh : blankSafe x.pc = false ∧ blankSafe k = true := by
        simpa [guard, Bool.and_eq_true] using hg
      have hn : x.pos 2 < n := by
        by_contra h
        have hp : x.pos 2 = n := by omega
        have hb := hsafe (hshape.2 _ (by omega))
        simp [hh.1] at hb
      refine ⟨n, by omega, by omega, hshape, ?_, ?_⟩
      · simpa using (show x.pos 2 + 1 ≤ n by omega)
      · intro _; exact hh.2
    · refine ⟨n, by omega, by omega, hshape, ?_, ?_⟩
      · simpa [Function.update_of_ne (Ne.symm ht)] using hpos
      · intro hb
        have hb' : x.tape 2 (x.pos 2) = 6 := by simpa [Function.update_of_ne (Ne.symm ht)] using hb
        simpa [guard, ht, hsafe hb'] using hg
  | left x t k hp =>
    by_cases ht : t = 2
    · subst t
      refine ⟨n, by omega, by omega, hshape, ?_, ?_⟩
      · simpa using (show x.pos 2 - 1 ≤ n by omega)
      · intro hb
        have hb' : x.tape 2 (x.pos 2 - 1) = 6 := by simpa using hb
        exact False.elim (hshape.1 _ (by omega) hb')
    · refine ⟨n, by omega, by omega, hshape, ?_, ?_⟩
      · simpa [Function.update_of_ne (Ne.symm ht)] using hpos
      · intro hb
        have hb' : x.tape 2 (x.pos 2) = 6 := by simpa [Function.update_of_ne (Ne.symm ht)] using hb
        simpa [guard, ht, hsafe hb'] using hg
  | write x t s k =>
    by_cases ht : t = 2
    · subst t
      have hb : s ≠ 6 := by simpa [guard] using hg
      refine ⟨if x.pos 2 = n then n + 1 else n, ?_, ?_, ?_, ?_, ?_⟩
      · split <;> omega
      · split <;> omega
      · simpa using write_shape (x.tape 2) n (x.pos 2) s hshape hpos hb
      · split <;> simp_all
      · intro hf; simp at hf; exact False.elim (hb hf)
    · refine ⟨n, by omega, by omega, ?_, hpos, ?_⟩
      · simpa [Function.update_of_ne (Ne.symm ht)] using hshape
      · intro hb
        have hb' : x.tape 2 (x.pos 2) = 6 := by simpa [Function.update_of_ne (Ne.symm ht)] using hb
        simpa [guard, ht, hsafe hb'] using hg
  | read x t cs k hm =>
    refine ⟨n, by omega, by omega, hshape, hpos, ?_⟩
    intro hb
    change x.tape 2 (x.pos 2) = 6 at hb
    by_cases ht : t = 2
    · subst t
      simp only [guard, hsafe hb, Bool.not_true, Bool.false_or] at hg
      have hh := List.all_eq_true.mp hg _ hm
      simpa [hb] using hh
    · simp only [guard, ht, ↓reduceIte, hsafe hb, Bool.not_true, Bool.false_or] at hg
      exact List.all_eq_true.mp hg k (List.mem_map.mpr ⟨_, hm, rfl⟩)
  | emit x k =>
    refine ⟨n, by omega, by omega, hshape, hpos, ?_⟩
    intro hb
    simpa [guard, successors, hsafe hb] using hg

/-- Every finite successful execution prefix keeps C's head within the
materialized prefix or its first blank cell. Eventual termination is not assumed. -/
theorem steps_bounded {x y : Config} {qs : List ℕ} (hs : Steps code x qs y)
    (n : ℕ) (hx : Bounded x n) : ∃ m, n ≤ m ∧ Bounded y m := by
  induction hs generalizing n with
  | nil => exact ⟨n, le_refl _, hx⟩
  | step x y z i qs hi he hs ih =>
    obtain ⟨m, hm, _, hb⟩ := step_bounded hi he n hx
    obtain ⟨k, hk, hb'⟩ := ih m hb
    exact ⟨k, le_trans hm hk, hb'⟩

/-- FppFinite initializes C with 010 and blanks elsewhere. -/
def initialC (i : ℕ) : Fin 9 := if i = 1 then 8 else if i < 3 then 7 else 6

theorem initial_bounded (x : Config) (ht : x.tape 2 = initialC) (hp : x.pos 2 = 0) :
    Bounded x 3 := by
  refine ⟨⟨?_, ?_⟩, by omega, ?_⟩
  · intro i hi
    rw [ht]
    simp [initialC, hi]
    split <;> decide
  · intro i hi
    rw [ht]
    simp [initialC, show i ≠ 1 by omega, show ¬i < 3 by omega]
  · intro hb
    simp [ht, hp, initialC] at hb

/-- The C-head bound from Scala's actual initial C contents, for every
successful prefix; no caller-supplied bound on the final head is needed. -/
theorem from_initial {x y : Config} {qs : List ℕ} (hs : Steps code x qs y)
    (ht : x.tape 2 = initialC) (hp : x.pos 2 = 0) :
    ∃ m, 3 ≤ m ∧ Shape (y.tape 2) m ∧ y.pos 2 ≤ m ∧
      (y.tape 2 (y.pos 2) = 6 → blankSafe y.pc = true) := by
  exact steps_bounded hs 3 (initial_bounded x ht hp)

#print axioms from_initial
#print axioms steps_bounded
end PalPeg.GalilFppFrontier
