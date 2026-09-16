import PalPeg.GalilScaffoldCounter

set_option autoImplicit false
namespace PalPeg.GalilScaffoldPlace

/-- Logical read-only projection of InputHead: current letter followed by
letters to its left. The empty list represents the absent focus sentinel.
Right stacks, incoming queues and physical reference storage are not refined here. -/
structure Place where
  letters : List (Fin 2)
  gap : Bool

def letter (a : Fin 2) : Fin 3 := ⟨a.val, by omega⟩

def read (p : Place) : Option (Fin 3) := match p.letters with
  | [] => none
  | a :: _ => some (if p.gap then 2 else letter a)

/-- Scala PlaceHead.left toggles gap; only a letter-to-gap step moves InputHead. -/
def left (p : Place) : Place :=
  if p.gap then ⟨p.letters,false⟩ else ⟨p.letters.tail,true⟩

def gaps : List (Fin 2) → List (Fin 3)
  | [] => []
  | a :: xs => 2 :: letter a :: gaps xs

def stream (p : Place) : List (Fin 3) := match p.letters with
  | [] => []
  | a :: xs => if p.gap then 2 :: letter a :: gaps xs else letter a :: gaps xs

theorem read_stream (p : Place) : read p = (stream p).head? := by
  rcases p with ⟨xs,g⟩
  cases xs <;> cases g <;> rfl

theorem left_stream (p : Place) : stream (left p) = (stream p).tail := by
  rcases p with ⟨xs,g⟩
  cases xs with
  | nil => cases g <;> rfl
  | cons a xs =>
    cases g
    · cases xs <;> rfl
    · rfl

theorem read_none (p : Place) : read p = none ↔ stream p = [] := by
  rcases p with ⟨xs,g⟩
  cases xs <;> cases g <;> simp [read, stream]

structure Cursor where
  place : Place
  work : ℕ
  tape : GalilScaffoldTape.Tape

def encode (x : Cursor) : GalilScaffoldCopy.Cursor :=
  ⟨stream x.place,x.work,x.tape⟩

/-- Search copy with the actual letter/gap read and left choices, at the
logical input-head projection. A positive-work step requires a present read. -/
inductive Copy : Cursor → ℕ → Cursor → Bool → Prop
  | stop (x : Cursor) (h : read x.place = none ∨ x.work = 0) :
      Copy x 1 {x with tape := GalilScaffoldTape.write x.tape 5}
        (read x.place).isNone
  | next (p : Place) (k : ℕ) (t : GalilScaffoldTape.Tape) (a : Fin 3)
      (ha : read p = some a) (n : ℕ) (y : Cursor) (final : Bool)
      (hr : Copy ⟨left p,k,GalilScaffoldTape.moveRight
        (GalilScaffoldTape.write t (GalilFppPreparation.symbol a))⟩ n y final) :
      Copy ⟨p,k+1,t⟩ (n+1) y final

theorem runs (p : Place) (work : ℕ) (t : GalilScaffoldTape.Tape) :
    ∃ n y final, Copy ⟨p,work,t⟩ n y final := by
  induction work generalizing p t with
  | zero => exact ⟨1,_,_,Copy.stop _ (Or.inr rfl)⟩
  | succ k ih =>
    cases he : read p with
    | none => exact ⟨1,_,_,Copy.stop _ (Or.inl he)⟩
    | some a =>
      obtain ⟨n,y,f,hr⟩ := ih (left p)
        (GalilScaffoldTape.moveRight (GalilScaffoldTape.write t (GalilFppPreparation.symbol a)))
      exact ⟨n+1,y,f,Copy.next p k t a he n y f hr⟩

theorem copy_sound {x y : Cursor} {n : ℕ} {final : Bool}
    (hr : Copy x n y final) :
    GalilScaffoldCopy.Copy (encode x) n (encode y) final := by
  induction hr with
  | stop x h =>
    have hs : (read x.place).isNone = (stream x.place).isEmpty := by
      rw [read_stream]; cases stream x.place <;> rfl
    rw [hs]
    apply GalilScaffoldCopy.Copy.stop
    rcases h with h | h
    · exact Or.inl ((read_none x.place).mp h)
    · exact Or.inr h
  | next p k t a ha n y final hr ih =>
    have hs : stream p = a :: stream (left p) := by
      rw [left_stream]
      rw [read_stream] at ha
      cases he : stream p with
      | nil => simp [he] at ha
      | cons b bs => simpa [he] using ha
    simpa [encode, hs] using
      (GalilScaffoldCopy.Copy.next a (stream (left p)) k n t (encode y) final ih)

theorem copy_counter {x y : Cursor} {n : ℕ} {final : Bool}
    (hr : Copy x n y final) :
    GalilScaffoldCounter.Copy (GalilScaffoldCounter.encode (encode x)) n
      (GalilScaffoldCounter.encode (encode y)) final :=
  GalilScaffoldCounter.realize_copy (copy_sound hr)

theorem copy_ops {x y : Cursor} {n : ℕ} {final : Bool}
    (hr : Copy x n y final) :
    GalilScaffoldLoad.Run x.tape (2*n-1) y.tape :=
  GalilScaffoldCopy.copy_ops (copy_sound hr)

#print axioms copy_counter
#print axioms copy_ops
#print axioms runs
#print axioms copy_sound
end PalPeg.GalilScaffoldPlace
