import PalPeg.GalilScaffoldInputTrace

set_option autoImplicit false
namespace PalPeg.GalilScaffoldHeap

/-- A scaffold node and one of its finitely many pool slots. -/
abbrev Address (slots : ℕ) := ℕ × Fin slots
abbrev Root (slots : ℕ) := Option (Address slots)

/-- `below` combines the Scala below pointer and its saved tag. Payload can
contain both the value pointer and data. Circuit field decoding is separate. -/
structure Cell (slots : ℕ) (α : Type) where
  below : Root slots
  payload : α

abbrev Heap (slots : ℕ) (α : Type) := Address slots → Option (Cell slots α)

inductive Models {slots : ℕ} {α : Type} (h : Heap slots α) : Root slots → List α → Prop
  | empty : Models h none []
  | cons (a : Address slots) (c : Cell slots α) (xs : List α)
      (hc : h a = some c) (ht : Models h c.below xs) :
      Models h (some a) (c.payload :: xs)

def put {slots : ℕ} {α : Type} (h : Heap slots α) (a : Address slots) (c : Cell slots α) :
    Heap slots α := Function.update h a (some c)

/-- Fresh allocation preserves every existing root, including aliases. -/
theorem fresh_preserves {slots : ℕ} {α : Type} {h : Heap slots α}
    {r : Root slots} {xs : List α} (hr : Models h r xs)
    (a : Address slots) (fresh : h a = none) (c : Cell slots α) :
    Models (put h a c) r xs := by
  induction hr with
  | empty => exact .empty
  | cons b d ys hd ht ih =>
    have hn : b ≠ a := by intro he; subst b; rw [fresh] at hd; contradiction
    exact .cons b d ys (by simpa [put, hn] using hd) ih

theorem push {slots : ℕ} {α : Type} {h : Heap slots α} {r : Root slots} {xs : List α}
    (hr : Models h r xs) (a : Address slots) (fresh : h a = none) (v : α) :
    Models (put h a ⟨r,v⟩) (some a) (v :: xs) := by
  exact .cons a ⟨r,v⟩ xs (by simp [put]) (fresh_preserves hr a fresh _)

theorem pop {slots : ℕ} {α : Type} {h : Heap slots α} {r : Root slots}
    {v : α} {xs : List α} (hr : Models h r (v :: xs)) :
    ∃ a c, r = some a ∧ h a = some c ∧ c.payload = v ∧ Models h c.below xs := by
  cases hr with
  | cons a c xs hc ht => exact ⟨a,c,rfl,hc,rfl,ht⟩

theorem empty_iff {slots : ℕ} {α : Type} {h : Heap slots α} {r : Root slots}
    {xs : List α} (hr : Models h r xs) : r = none ↔ xs = [] := by
  cases hr <;> simp

/-- Copying a root requires no heap traversal; later fresh pushes leave the
copied root's contents unchanged. -/
theorem push_with_alias {slots : ℕ} {α : Type} {h : Heap slots α}
    {r other : Root slots} {xs ys : List α}
    (hr : Models h r xs) (ha : Models h other ys)
    (a : Address slots) (fresh : h a = none) (v : α) :
    Models (put h a ⟨r,v⟩) (some a) (v :: xs) ∧
    Models (put h a ⟨r,v⟩) other ys :=
  ⟨push hr a fresh v, fresh_preserves ha a fresh _⟩

structure Allocator (slots : ℕ) (α : Type) where
  heap : Heap slots α
  node : ℕ
  used : Finset (Fin slots)

def Bounded {slots : ℕ} {α : Type} (s : Allocator slots α) : Prop :=
  ∀ a c, s.heap a = some c → a.1 < s.node ∨ (a.1 = s.node ∧ a.2 ∈ s.used)

theorem unused_fresh {slots : ℕ} {α : Type} {s : Allocator slots α}
    (hb : Bounded s) (tag : Fin slots) (hu : tag ∉ s.used) :
    s.heap (s.node,tag) = none := by
  cases he : s.heap (s.node,tag) with
  | none => rfl
  | some c =>
    have hh := hb (s.node,tag) c he
    simp only at hh
    rcases hh with hh | ⟨_,hh⟩
    · omega
    · exact False.elim (hu hh)

/-- Reserve a slot even if its predicated write is disabled. Actual Scala
layout/slot assignment must supply the unused-slot condition. -/
def allocate {slots : ℕ} {α : Type} (s : Allocator slots α)
    (tag : Fin slots) (c : Cell slots α) (enabled : Bool) : Allocator slots α :=
  ⟨if enabled then put s.heap (s.node,tag) c else s.heap,
    s.node,insert tag s.used⟩

theorem allocate_bounded {slots : ℕ} {α : Type} {s : Allocator slots α}
    (hb : Bounded s) (tag : Fin slots) (c : Cell slots α) (enabled : Bool) :
    Bounded (allocate s tag c enabled) := by
  intro a d hd
  cases enabled with
  | false =>
    have hh := hb a d hd
    rcases hh with hh | ⟨hn,ht⟩
    · exact Or.inl hh
    · exact Or.inr ⟨hn,Finset.mem_insert_of_mem ht⟩
  | true =>
    by_cases he : a = (s.node,tag)
    · subst a; exact Or.inr ⟨rfl,Finset.mem_insert_self _ _⟩
    · have old : s.heap a = some d := by simpa [allocate, put, he] using hd
      rcases hb a d old with hh | ⟨hn,ht⟩
      · exact Or.inl hh
      · exact Or.inr ⟨hn,Finset.mem_insert_of_mem ht⟩

def nextNode {slots : ℕ} {α : Type} (s : Allocator slots α) : Allocator slots α :=
  ⟨s.heap,s.node+1,∅⟩

theorem nextNode_bounded {slots : ℕ} {α : Type} {s : Allocator slots α}
    (hb : Bounded s) : Bounded (nextNode s) := by
  intro a c hc
  have hh := hb a c hc
  left
  change a.1 < s.node+1
  rcases hh with hh | ⟨hh,_⟩ <;> omega

theorem allocated_push {slots : ℕ} {α : Type} {s : Allocator slots α}
    (hb : Bounded s) (tag : Fin slots) (hu : tag ∉ s.used)
    {r other : Root slots} {xs ys : List α}
    (hr : Models s.heap r xs) (ho : Models s.heap other ys) (v : α) :
    Models (allocate s tag ⟨r,v⟩ true).heap (some (s.node,tag)) (v :: xs) ∧
    Models (allocate s tag ⟨r,v⟩ true).heap other ys :=
  push_with_alias hr ho (s.node,tag) (unused_fresh hb tag hu) v

def initial {slots : ℕ} {α : Type} : Allocator slots α := ⟨fun _ => none,0,∅⟩

theorem initial_bounded {slots : ℕ} {α : Type} : Bounded (initial : Allocator slots α) := by
  intro a c hc
  contradiction

theorem disabled_preserves {slots : ℕ} {α : Type} {s : Allocator slots α}
    (tag : Fin slots) (c : Cell slots α) {r : Root slots} {xs : List α}
    (hr : Models s.heap r xs) : Models (allocate s tag c false).heap r xs := hr

#print axioms allocated_push
#print axioms allocate_bounded
#print axioms nextNode_bounded
#print axioms fresh_preserves
#print axioms push_with_alias
#print axioms pop
end PalPeg.GalilScaffoldHeap
