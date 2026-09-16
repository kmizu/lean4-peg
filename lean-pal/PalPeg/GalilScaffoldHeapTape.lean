import PalPeg.GalilScaffoldHeap

set_option autoImplicit false
namespace PalPeg.GalilScaffoldHeapTape
open GalilScaffoldHeap

structure Tape (slots : ℕ) where
  left : Root slots
  focus : Fin 9
  right : Root slots

def Represents {slots : ℕ} (h : Heap slots (Fin 9)) (t : Tape slots)
    (u : GalilScaffoldTape.Tape) : Prop :=
  Models h t.left u.left ∧ t.focus = u.focus ∧ Models h t.right u.right

def top {slots : ℕ} (h : Heap slots (Fin 9)) (r : Root slots) : Cell slots (Fin 9) :=
  (r.bind h).getD ⟨none,6⟩

theorem top_models {slots : ℕ} {h : Heap slots (Fin 9)} {r : Root slots}
    {xs : List (Fin 9)} (hr : Models h r xs) :
    Models h (top h r).below xs.tail ∧ (top h r).payload = xs.headD 6 := by
  cases hr with
  | empty => exact ⟨.empty,rfl⟩
  | cons a c xs hc ht => simpa [top,hc] using And.intro ht (Eq.refl c.payload)

def right {slots : ℕ} (h : Heap slots (Fin 9)) (t : Tape slots) (a : Address slots) :
    Heap slots (Fin 9) × Tape slots :=
  (put h a ⟨t.left,t.focus⟩, ⟨some a,(top h t.right).payload,(top h t.right).below⟩)

def left {slots : ℕ} (h : Heap slots (Fin 9)) (t : Tape slots) (a : Address slots) :
    Heap slots (Fin 9) × Tape slots :=
  (put h a ⟨t.right,t.focus⟩, ⟨(top h t.left).below,(top h t.left).payload,some a⟩)

theorem right_represents {slots : ℕ} {h : Heap slots (Fin 9)}
    {t : Tape slots} {u : GalilScaffoldTape.Tape} (hr : Represents h t u)
    (a : Address slots) (hf : h a = none) :
    Represents (right h t a).1 (right h t a).2 (GalilScaffoldTape.moveRight u) := by
  obtain ⟨hl,hv,hr⟩ := hr
  obtain ⟨hp,hd⟩ := top_models hr
  have pushed := push hl a hf t.focus
  have popped := fresh_preserves hp a hf (⟨t.left,t.focus⟩ : Cell slots (Fin 9))
  rcases u with ⟨ls,v,rs⟩
  cases rs <;> simpa [Represents,right,GalilScaffoldTape.moveRight,hv] using
    And.intro pushed (And.intro hd popped)

theorem left_represents {slots : ℕ} {h : Heap slots (Fin 9)}
    {t : Tape slots} {u : GalilScaffoldTape.Tape} (hr : Represents h t u)
    (a : Address slots) (hf : h a = none) (legal : u.left ≠ []) :
    t.left ≠ none ∧
    Represents (left h t a).1 (left h t a).2 (GalilScaffoldTape.moveLeft u) := by
  obtain ⟨hl,hv,hr⟩ := hr
  have nonempty : t.left ≠ none := by intro he; exact legal ((empty_iff hl).mp he)
  refine ⟨nonempty,?_⟩
  obtain ⟨hp,hd⟩ := top_models hl
  have pushed := push hr a hf t.focus
  have popped := fresh_preserves hp a hf (⟨t.right,t.focus⟩ : Cell slots (Fin 9))
  rcases u with ⟨ls,v,rs⟩
  cases ls with
  | nil => exact False.elim (legal rfl)
  | cons b ls =>
    simpa [Represents,left,GalilScaffoldTape.moveLeft,hv] using
      And.intro popped (And.intro hd pushed)

theorem right_frame {slots : ℕ} {h : Heap slots (Fin 9)}
    (t : Tape slots) (a : Address slots) (hf : h a = none)
    {r : Root slots} {xs : List (Fin 9)} (hr : Models h r xs) :
    Models (right h t a).1 r xs := fresh_preserves hr a hf _

theorem left_frame {slots : ℕ} {h : Heap slots (Fin 9)}
    (t : Tape slots) (a : Address slots) (hf : h a = none)
    {r : Root slots} {xs : List (Fin 9)} (hr : Models h r xs) :
    Models (left h t a).1 r xs := fresh_preserves hr a hf _

def reset {slots : ℕ} : Tape slots := ⟨none,6,none⟩
def write {slots : ℕ} (t : Tape slots) (v : Fin 9) : Tape slots := {t with focus := v}

theorem reset_represents {slots : ℕ} (h : Heap slots (Fin 9)) :
    Represents h reset GalilScaffoldTape.reset := ⟨.empty,rfl,.empty⟩

theorem write_represents {slots : ℕ} {h : Heap slots (Fin 9)}
    {t : Tape slots} {u : GalilScaffoldTape.Tape} (hr : Represents h t u) (v : Fin 9) :
    Represents h (write t v) (GalilScaffoldTape.write u v) := ⟨hr.1,rfl,hr.2.2⟩

#print axioms right_represents
#print axioms left_represents
#print axioms right_frame
end PalPeg.GalilScaffoldHeapTape
