import PalPeg.GalilScaffoldPlace

set_option autoImplicit false
namespace PalPeg.GalilScaffoldInputHead

/-- Stack contents after interpreting stored input references. Queue contents
are abstract here; no claim about physical cells or queue maintenance is made. -/
structure Head where
  focus : Option (Fin 2)
  left : List (Option (Fin 2))
  right : List (Option (Fin 2))
  incoming : List (Fin 2)

def layout (xs : List (Fin 2)) (rs : List (Option (Fin 2))) (q : List (Fin 2)) : Head :=
  match xs with
  | [] => ⟨none,[],rs,q⟩
  | a :: tail => ⟨some a,tail.map some ++ [none],rs,q⟩

def moveLeft (h : Head) : Head := match h.left with
  | [] => h
  | a :: tail => ⟨a,tail,h.focus :: h.right,h.incoming⟩

theorem left_legal (a : Fin 2) (xs : List (Fin 2))
    (rs : List (Option (Fin 2))) (q : List (Fin 2)) :
    (layout (a :: xs) rs q).left ≠ [] := by simp [layout]

theorem moveLeft_at (a : Fin 2) (xs : List (Fin 2))
    (rs : List (Option (Fin 2))) (q : List (Fin 2)) :
    moveLeft (layout (a :: xs) rs q) = layout xs (some a :: rs) q := by
  cases xs <;> rfl

structure PlaceHead where
  head : Head
  gap : Bool

def represent (p : GalilScaffoldPlace.Place)
    (rs : List (Option (Fin 2))) (q : List (Fin 2)) : PlaceHead :=
  ⟨layout p.letters rs q,p.gap⟩

def read (p : PlaceHead) : Option (Fin 3) :=
  p.head.focus.map (fun a => if p.gap then 2 else GalilScaffoldPlace.letter a)

def left (p : PlaceHead) : PlaceHead :=
  ⟨if p.gap then p.head else moveLeft p.head,!p.gap⟩

theorem read_represent (p : GalilScaffoldPlace.Place)
    (rs : List (Option (Fin 2))) (q : List (Fin 2)) :
    read (represent p rs q) = GalilScaffoldPlace.read p := by
  rcases p with ⟨xs,g⟩
  cases xs <;> rfl

/-- Every enabled left step in the search copy loop has a nonempty stack
when it needs to move InputHead. This discharges Scala's left require. -/
theorem left_represent (p : GalilScaffoldPlace.Place)
    (rs : List (Option (Fin 2))) (q : List (Fin 2))
    (hp : GalilScaffoldPlace.read p ≠ none) :
    (p.gap = false → (represent p rs q).head.left ≠ []) ∧
    ∃ rs', left (represent p rs q) = represent (GalilScaffoldPlace.left p) rs' q := by
  rcases p with ⟨xs,g⟩
  cases xs with
  | nil => simp [GalilScaffoldPlace.read] at hp
  | cons a xs =>
    constructor
    · intro _; exact left_legal a xs rs q
    · cases g
      · refine ⟨some a :: rs, ?_⟩
        simp [left, represent, GalilScaffoldPlace.left, moveLeft_at]
      · exact ⟨rs,rfl⟩

structure Cursor where
  place : PlaceHead
  work : ℕ
  tape : GalilScaffoldTape.Tape

def encode (x : GalilScaffoldPlace.Cursor)
    (rs : List (Option (Fin 2))) (q : List (Fin 2)) : Cursor :=
  ⟨represent x.place rs q,x.work,x.tape⟩

inductive Copy : Cursor → ℕ → Cursor → Bool → Prop
  | stop (x : Cursor) (h : read x.place = none ∨ x.work = 0) :
      Copy x 1 {x with tape := GalilScaffoldTape.write x.tape 5}
        (read x.place).isNone
  | next (p : PlaceHead) (k : ℕ) (t : GalilScaffoldTape.Tape) (a : Fin 3)
      (ha : read p = some a) (hl : p.gap = false → p.head.left ≠ [])
      (n : ℕ) (y : Cursor) (final : Bool)
      (hr : Copy ⟨left p,k,GalilScaffoldTape.moveRight
        (GalilScaffoldTape.write t (GalilFppPreparation.symbol a))⟩ n y final) :
      Copy ⟨p,k+1,t⟩ (n+1) y final

/-- The entire search copy trace is realized with explicit focus and stack
updates, preserving the incoming queue. Every InputHead.left guard is discharged. -/
theorem realize_copy {x y : GalilScaffoldPlace.Cursor} {n : ℕ} {final : Bool}
    (hr : GalilScaffoldPlace.Copy x n y final)
    (rs : List (Option (Fin 2))) (q : List (Fin 2)) :
    ∃ rs', Copy (encode x rs q) n (encode y rs' q) final := by
  induction hr generalizing rs with
  | stop x h =>
    refine ⟨rs, ?_⟩
    have hs : read (represent x.place rs q) = GalilScaffoldPlace.read x.place :=
      read_represent x.place rs q
    have hh : read (represent x.place rs q) = none ∨ x.work = 0 := by rwa [hs]
    simpa [encode, hs] using Copy.stop (encode x rs q) hh
  | next p k t a ha n y final hr ih =>
    have hp : GalilScaffoldPlace.read p ≠ none := by rw [ha]; simp
    obtain ⟨hl,rs1,he⟩ := left_represent p rs q hp
    obtain ⟨rs2,ht⟩ := ih rs1
    refine ⟨rs2, ?_⟩
    apply Copy.next (represent p rs q) k t a
    · rwa [read_represent]
    · exact hl
    · simpa [encode, he] using ht

#print axioms realize_copy
#print axioms moveLeft_at
#print axioms read_represent
#print axioms left_represent
end PalPeg.GalilScaffoldInputHead
