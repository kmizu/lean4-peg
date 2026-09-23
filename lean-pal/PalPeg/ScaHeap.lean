import Mathlib

/-!
# Persistent stacks on a scaffold heap

A transcription of Scala's `ScaffoldCircuitStructs` (`StackPool` / `Stack`). The heap gains one
node per input character and never changes an old node. A node has finitely many cell slots,
named by a tag; a cell has a `below` pointer and a finite `data` field. A pointer is a node address
and a tag. A stack is just its root pointer: `push` writes a cell in the new node whose `below` is
the old root, `pop` follows `below`, and `copyFrom` copies the root, as in Scala.
-/
set_option autoImplicit false
namespace PalPeg.ScaHeap

variable {Tag D : Type}

/-- A pointer to a cell: the node's address and the slot's tag. -/
abbrev Ptr (Tag : Type) := ℕ × Tag

/-- A stack cell. -/
structure Cell (Tag D : Type) where
  below : Option (Ptr Tag)
  data : D

/-- A node: finitely many slots, each possibly holding a cell. -/
abbrev Node (Tag D : Type) := Tag → Option (Cell Tag D)

/-- The heap, oldest node first; the address of a node is its index. -/
abbrev Heap (Tag D : Type) := List (Node Tag D)

def cellAt (h : Heap Tag D) (p : Ptr Tag) : Option (Cell Tag D) :=
  (h[p.1]?).bind (fun node => node p.2)

/-- **`p` represents the stack `xs`** (top first). -/
inductive Rep (h : Heap Tag D) : Option (Ptr Tag) → List D → Prop
  | nil : Rep h none []
  | cons {p : Ptr Tag} {c : Cell Tag D} {xs : List D} (hc : cellAt h p = some c)
      (hrest : Rep h c.below xs) : Rep h (some p) (c.data :: xs)

theorem cellAt_append (h : Heap Tag D) (n : Node Tag D) (p : Ptr Tag) (hp : p.1 < h.length) :
    cellAt (h ++ [n]) p = cellAt h p := by
  unfold cellAt
  rw [List.getElem?_append_left hp]

/-- **Adding a node keeps every old stack**: the heap is persistent. -/
theorem Rep.append {h : Heap Tag D} {p : Option (Ptr Tag)} {xs : List D} (hr : Rep h p xs)
    (n : Node Tag D) : Rep (h ++ [n]) p xs := by
  induction hr with
  | nil => exact .nil
  | @cons p c xs hc _ ih =>
    have hp : p.1 < h.length := by
      unfold cellAt at hc
      cases hh : h[p.1]? with
      | none => rw [hh] at hc; cases hc
      | some _ => exact (List.getElem?_eq_some_iff.mp hh).1
    exact .cons (by rw [cellAt_append h n p hp]; exact hc) ih

/-- The new node's cell in slot `t`. -/
theorem cellAt_new (h : Heap Tag D) (n : Node Tag D) (t : Tag) :
    cellAt (h ++ [n]) (h.length, t) = n t := by
  unfold cellAt
  simp

/-- **`push`**: a cell in the new node, below the old root. -/
theorem Rep.push {h : Heap Tag D} {p : Option (Ptr Tag)} {xs : List D} (hr : Rep h p xs)
    (n : Node Tag D) (t : Tag) (x : D) (hn : n t = some ⟨p, x⟩) :
    Rep (h ++ [n]) (some (h.length, t)) (x :: xs) :=
  .cons (c := ⟨p, x⟩) (by rw [cellAt_new, hn]) (hr.append n)

/-- **`pop`**: the root's cell carries the top and points below. -/
theorem Rep.pop {h : Heap Tag D} {p : Ptr Tag} {x : D} {xs : List D} (hr : Rep h (some p) (x :: xs)) :
    ∃ c, cellAt h p = some c ∧ c.data = x ∧ Rep h c.below xs := by
  cases hr with
  | cons hc hrest => exact ⟨_, hc, rfl, hrest⟩

/-- An empty root is the empty stack, and only it. -/
theorem Rep.none_iff {h : Heap Tag D} {xs : List D} : Rep h none xs ↔ xs = [] := by
  constructor
  · intro hr; cases hr; rfl
  · rintro rfl; exact .nil

/-- A stack is determined by its root. -/
theorem Rep.unique {h : Heap Tag D} {p : Option (Ptr Tag)} {xs ys : List D} (hx : Rep h p xs)
    (hy : Rep h p ys) : xs = ys := by
  induction hx generalizing ys with
  | nil => cases hy; rfl
  | cons hc _ ih =>
    cases hy with
    | cons hc' hrest' =>
      rw [hc] at hc'
      cases hc'
      rw [ih hrest']

end PalPeg.ScaHeap
