import PalPeg.GalilScaffoldHeapTape

set_option autoImplicit false
namespace PalPeg.GalilScaffoldHeapProgram
open GalilScaffoldHeap
namespace HT
export GalilScaffoldHeapTape (Tape Represents right left right_represents left_represents
  right_frame left_frame write write_represents)
end HT
namespace LP
export GalilScaffoldProgram (Config changed)
end LP

structure Config (n slots : ℕ) where
  heap : Heap slots (Fin 9)
  pc : ℕ
  tapes : Fin n → HT.Tape slots

def Represents {n slots : ℕ} (x : Config n slots) (u : LP.Config n) : Prop :=
  x.pc = u.pc ∧ ∀ k, HT.Represents x.heap (x.tapes k) (u.tapes k)

def moved {n slots : ℕ} (x : Config n slots) (k : Fin n) (a : Address slots)
    (rightward : Bool) (pc : ℕ) : Config n slots :=
  let result := if rightward then HT.right x.heap (x.tapes k) a else HT.left x.heap (x.tapes k) a
  ⟨result.1,pc,Function.update x.tapes k result.2⟩

theorem moved_right {n slots : ℕ} {x : Config n slots} {u : LP.Config n}
    (hr : Represents x u) (k : Fin n) (a : Address slots) (hf : x.heap a = none) (pc : ℕ) :
    Represents (moved x k a true pc)
      (LP.changed u k (GalilScaffoldTape.moveRight (u.tapes k)) pc) := by
  refine ⟨rfl,?_⟩
  intro j
  by_cases he : j = k
  · subst j
    simpa [moved,LP.changed] using HT.right_represents (hr.2 k) a hf
  · obtain ⟨hl,hv,ht⟩ := hr.2 j
    have hl' := HT.right_frame (x.tapes k) a hf hl
    have ht' := HT.right_frame (x.tapes k) a hf ht
    simpa [moved,LP.changed,he,HT.Represents] using And.intro hl' (And.intro hv ht')

theorem moved_left {n slots : ℕ} {x : Config n slots} {u : LP.Config n}
    (hr : Represents x u) (k : Fin n) (a : Address slots) (hf : x.heap a = none) (pc : ℕ)
    (legal : (u.tapes k).left ≠ []) :
    (x.tapes k).left ≠ none ∧ Represents (moved x k a false pc)
      (LP.changed u k (GalilScaffoldTape.moveLeft (u.tapes k)) pc) := by
  obtain ⟨hg,hm⟩ := HT.left_represents (hr.2 k) a hf legal
  refine ⟨hg,rfl,?_⟩
  intro j
  by_cases he : j = k
  · subst j; simpa [moved,LP.changed] using hm
  · obtain ⟨hl,hv,ht⟩ := hr.2 j
    have hl' := HT.left_frame (x.tapes k) a hf hl
    have ht' := HT.left_frame (x.tapes k) a hf ht
    simpa [moved,LP.changed,he,HT.Represents] using And.intro hl' (And.intro hv ht')

def written {n slots : ℕ} (x : Config n slots) (k : Fin n) (v : Fin 9) (pc : ℕ) :
    Config n slots := ⟨x.heap,pc,Function.update x.tapes k (HT.write (x.tapes k) v)⟩

theorem written_represents {n slots : ℕ} {x : Config n slots} {u : LP.Config n}
    (hr : Represents x u) (k : Fin n) (v : Fin 9) (pc : ℕ) :
    Represents (written x k v pc) (LP.changed u k (GalilScaffoldTape.write (u.tapes k) v) pc) := by
  refine ⟨rfl,?_⟩
  intro j
  by_cases he : j = k
  · subst j; simpa [written,LP.changed] using HT.write_represents (hr.2 k) v
  · simpa [written,LP.changed,he] using hr.2 j

inductive Execute {n slots : ℕ} : GalilFppWide.Instruction n → Config n slots → Config n slots → Prop
  | right (x : Config n slots) (k : Fin n) (pc : ℕ) (a : Address slots) (hf : x.heap a = none) :
      Execute (.move k true pc) x (moved x k a true pc)
  | left (x : Config n slots) (k : Fin n) (pc : ℕ) (a : Address slots) (hf : x.heap a = none)
      (hl : (x.tapes k).left ≠ none) : Execute (.move k false pc) x (moved x k a false pc)
  | write (x : Config n slots) (k : Fin n) (v : Fin 9) (pc : ℕ) :
      Execute (.write k v pc) x (written x k v pc)
  | read (x : Config n slots) (k : Fin n) (cs : List (Fin 9 × ℕ)) (pc : ℕ)
      (hm : ((x.tapes k).focus,pc) ∈ cs) : Execute (.read k cs) x {x with pc := pc}

theorem realize_step {n slots : ℕ} {i : GalilFppWide.Instruction n} {u v : LP.Config n}
    (he : GalilScaffoldProgram.Execute i u v) (x : Config n slots) (hr : Represents x u)
    (a : Address slots) (hf : x.heap a = none) :
    ∃ y, Execute i x y ∧ Represents y v := by
  cases he with
  | right u k pc => exact ⟨_,.right x k pc a hf,moved_right hr k a hf pc⟩
  | left u k pc legal =>
    obtain ⟨hg,hm⟩ := moved_left hr k a hf pc legal
    exact ⟨_,.left x k pc a hf hg,hm⟩
  | write u k s pc => exact ⟨_,.write x k s pc,written_represents hr k s pc⟩
  | read u k cs pc hm =>
    have hh : ((x.tapes k).focus,pc) ∈ cs := by rw [(hr.2 k).2.1]; exact hm
    exact ⟨_,.read x k cs pc hh,⟨rfl,hr.2⟩⟩

/-- A finite node frontier; this is a semantic allocation resource, not yet
the fixed Scala circuit's concrete allocation schedule. -/
def FiniteHeap {slots : ℕ} (h : Heap slots (Fin 9)) : Prop :=
  ∃ bound, ∀ a, bound ≤ a.1 → h a = none

theorem put_finite {slots : ℕ} {h : Heap slots (Fin 9)} (hh : FiniteHeap h)
    (a : Address slots) (c : Cell slots (Fin 9)) : FiniteHeap (put h a c) := by
  obtain ⟨b,hb⟩ := hh
  refine ⟨max b (a.1+1),?_⟩
  intro d hd
  have hn : d ≠ a := by intro he; subst d; omega
  have hm : b ≤ d.1 := by omega
  simpa [put,hn] using hb d hm

theorem execute_finite {n slots : ℕ} {i : GalilFppWide.Instruction n}
    {x y : Config n slots} (he : Execute i x y) (hh : FiniteHeap x.heap) : FiniteHeap y.heap := by
  cases he with
  | right x k pc a hf => exact put_finite hh a _
  | left x k pc a hf hl => exact put_finite hh a _
  | write => exact hh
  | read => exact hh

inductive Completed {n slots : ℕ} (code : List (GalilFppWide.Instruction n)) :
    Config n slots → List ℕ → Config n slots → Prop
  | halt (x : Config n slots) (hi : code[x.pc]? = some .halt) : Completed code x [x.pc] x
  | step (x y z : Config n slots) (i : GalilFppWide.Instruction n) (qs : List ℕ)
      (hi : code[x.pc]? = some i) (he : Execute i x y) (hr : Completed code y qs z) :
      Completed code x (x.pc :: qs) z

theorem realize_completed {n slots : ℕ} {code : List (GalilFppWide.Instruction n)}
    {u v : LP.Config n} {qs : List ℕ} (hc : GalilScaffoldProgram.Completed code u qs v)
    (hs : 0 < slots) (x : Config n slots) (hr : Represents x u) (hh : FiniteHeap x.heap) :
    ∃ y, Completed code x qs y ∧ Represents y v ∧ FiniteHeap y.heap := by
  induction hc generalizing x with
  | halt u hi =>
    have hi' : code[x.pc]? = some .halt := by rw [hr.1]; exact hi
    exact ⟨x,by simpa only [hr.1] using Completed.halt x hi',hr,hh⟩
  | step u v w i qs hi he hc ih =>
    obtain ⟨b,hb⟩ := hh
    let a : Address slots := (b,⟨0,hs⟩)
    obtain ⟨y,hy,hry⟩ := realize_step he x hr a (hb a (Nat.le_refl b))
    have hfy := execute_finite hy ⟨b,hb⟩
    obtain ⟨z,hz,hrz,hfz⟩ := ih y hry hfy
    have hi' : code[x.pc]? = some i := by rw [hr.1]; exact hi
    refine ⟨z,?_,hrz,hfz⟩
    simpa only [hr.1] using Completed.step x y z i qs hi' hy hz

#print axioms realize_completed
#print axioms realize_step
#print axioms moved_right
#print axioms moved_left
#print axioms written_represents
end PalPeg.GalilScaffoldHeapProgram
