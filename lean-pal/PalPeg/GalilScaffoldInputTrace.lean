import PalPeg.GalilScaffoldInputHead

set_option autoImplicit false
namespace PalPeg.GalilScaffoldInputTrace
open GalilScaffoldInputHead

def reset : Head := ⟨none,[],[],[]⟩
def append (h : Head) (a : Fin 2) : Head := {h with incoming := h.incoming ++ [a]}
def canRight (h : Head) : Prop := h.right ≠ [] ∨ h.incoming ≠ []

/-- Logical FIFO semantics; refinement of Scala Queue.work/pop is separate. -/
def moveRight (h : Head) : Head := match h.right with
  | a :: rs => ⟨a,h.focus :: h.left,rs,h.incoming⟩
  | [] => match h.incoming with
    | [] => h
    | a :: q => ⟨some a,h.focus :: h.left,[],q⟩

/-- The complete arrived word is partitioned into the reversed left history,
the saved right stack and the incoming FIFO. No absent references occur on the right. -/
def Represents (h : Head) (word : List (Fin 2)) : Prop :=
  ∃ xs rs q, h = layout xs (rs.map some) q ∧ word = xs.reverse ++ rs ++ q

theorem reset_represents : Represents reset [] := ⟨[],[],[],rfl,rfl⟩

theorem right_saved (xs : List (Fin 2)) (a : Fin 2) (rs q : List (Fin 2)) :
    moveRight (layout xs ((a :: rs).map some) q) = layout (a :: xs) (rs.map some) q := by
  cases xs <;> rfl

theorem right_incoming (xs : List (Fin 2)) (a : Fin 2) (q : List (Fin 2)) :
    moveRight (layout xs [] (a :: q)) = layout (a :: xs) [] q := by
  cases xs <;> rfl

theorem append_layout (xs rs q : List (Fin 2)) (a : Fin 2) :
    append (layout xs (rs.map some) q) a = layout xs (rs.map some) (q ++ [a]) := by
  cases xs <;> rfl

theorem append_represents {h : Head} {word : List (Fin 2)}
    (hh : Represents h word) (a : Fin 2) : Represents (append h a) (word ++ [a]) := by
  obtain ⟨xs,rs,q,rfl,rfl⟩ := hh
  refine ⟨xs,rs,q ++ [a],append_layout xs rs q a,?_⟩
  simp [List.append_assoc]

theorem right_represents {h : Head} {word : List (Fin 2)}
    (hh : Represents h word) (hc : canRight h) : Represents (moveRight h) word := by
  obtain ⟨xs,rs,q,rfl,rfl⟩ := hh
  cases rs with
  | cons a rs =>
    refine ⟨a :: xs,rs,q,right_saved xs a rs q,?_⟩
    simp [List.reverse_cons, List.append_assoc]
  | nil =>
    cases q with
    | nil => cases xs <;> simp [canRight, layout] at hc
    | cons a q =>
      refine ⟨a :: xs,[],q,right_incoming xs a q,?_⟩
      simp [List.reverse_cons, List.append_assoc]

theorem left_represents {h : Head} {word : List (Fin 2)}
    (hh : Represents h word) (hc : h.focus ≠ none) :
    h.left ≠ [] ∧ Represents (moveLeft h) word := by
  obtain ⟨xs,rs,q,rfl,rfl⟩ := hh
  cases xs with
  | nil => simp [layout] at hc
  | cons a xs =>
    refine ⟨left_legal a xs _ q, xs,a :: rs,q,?_,?_⟩
    · exact moveLeft_at a xs _ q
    · simp [List.reverse_cons, List.append_assoc]

/-- Arbitrary online arrivals interleaved with legal head movements. -/
inductive Reach : Head → List (Fin 2) → Prop
  | initial : Reach reset []
  | arrival {h : Head} {w : List (Fin 2)} (hr : Reach h w) (a : Fin 2) :
      Reach (append h a) (w ++ [a])
  | right {h : Head} {w : List (Fin 2)} (hr : Reach h w) (hc : canRight h) :
      Reach (moveRight h) w
  | left {h : Head} {w : List (Fin 2)} (hr : Reach h w) (hc : h.focus ≠ none) :
      Reach (moveLeft h) w

theorem reachable_represents {h : Head} {word : List (Fin 2)}
    (hr : Reach h word) : Represents h word := by
  induction hr with
  | initial => exact reset_represents
  | arrival hr a ih => exact append_represents ih a
  | right hr hc ih => exact right_represents ih hc
  | left hr hc ih => exact (left_represents ih hc).2

/-- Copy can start at any logically reachable online input head, without
assuming its stack layout separately. -/
theorem reachable_copy {h : Head} {word : List (Fin 2)} (hr : Reach h word)
    (gap : Bool) (work : ℕ) (t : GalilScaffoldTape.Tape) :
    ∃ n y final, Copy ⟨⟨h,gap⟩,work,t⟩ n y final := by
  obtain ⟨xs,rs,q,he,_⟩ := reachable_represents hr
  subst h
  obtain ⟨n,y,f,hc⟩ := GalilScaffoldPlace.runs ⟨xs,gap⟩ work t
  obtain ⟨rs',ht⟩ := realize_copy hc (rs.map some) q
  exact ⟨n,encode y rs' q,f,ht⟩

#print axioms reachable_copy
#print axioms reachable_represents
end PalPeg.GalilScaffoldInputTrace
