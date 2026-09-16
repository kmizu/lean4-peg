import PalPeg.GalilScaffoldCopy

set_option autoImplicit false
namespace PalPeg.GalilScaffoldCounter

/-- Logical interpretation of the positive/negative stack roots used by
ScaffoldCircuitStructs.Counter. Physical StackPool storage is not modeled here. -/
structure Counter where
  pos : List Unit
  neg : List Unit
  deriving DecidableEq

def value (c : Counter) : ℤ := (c.pos.length : ℤ) - c.neg.length
def Canonical (c : Counter) : Prop := c.pos = [] ∨ c.neg = []
def positive (c : Counter) : Bool := !c.pos.isEmpty
def negative (c : Counter) : Bool := !c.neg.isEmpty
def zero (c : Counter) : Bool := c.pos.isEmpty && c.neg.isEmpty
def reset : Counter := ⟨[],[]⟩

def inc (c : Counter) : Counter := match c.neg with
  | [] => ⟨() :: c.pos, []⟩
  | _ :: ns => ⟨c.pos, ns⟩

def dec (c : Counter) : Counter := match c.pos with
  | [] => ⟨[], () :: c.neg⟩
  | _ :: ps => ⟨ps, c.neg⟩

def ofNat (n : ℕ) : Counter := ⟨List.replicate n (), []⟩

theorem inc_value (c : Counter) : value (inc c) = value c+1 := by
  rcases c with ⟨ps, ns⟩
  cases ns <;> simp [inc, value] <;> omega

theorem dec_value (c : Counter) : value (dec c) = value c-1 := by
  rcases c with ⟨ps, ns⟩
  cases ps <;> simp [dec, value] <;> omega

theorem inc_canonical (c : Counter) (hc : Canonical c) : Canonical (inc c) := by
  rcases c with ⟨ps, ns⟩
  cases ns <;> simp_all [Canonical, inc]

theorem dec_canonical (c : Counter) (hc : Canonical c) : Canonical (dec c) := by
  rcases c with ⟨ps, ns⟩
  cases ps <;> simp_all [Canonical, dec]

theorem zero_iff (c : Counter) (hc : Canonical c) : zero c = true ↔ value c = 0 := by
  rcases c with ⟨ps, ns⟩
  cases ps <;> cases ns <;> simp_all [Canonical, zero, value] <;> omega

theorem positive_iff (c : Counter) (hc : Canonical c) : positive c = true ↔ 0 < value c := by
  rcases c with ⟨ps, ns⟩
  cases ps <;> cases ns <;> simp_all [Canonical, positive, value]

theorem negative_iff (c : Counter) (hc : Canonical c) : negative c = true ↔ value c < 0 := by
  rcases c with ⟨ps, ns⟩
  cases ps <;> cases ns <;> simp_all [Canonical, negative, value] <;> omega

theorem ofNat_value (n : ℕ) : value (ofNat n) = n := by simp [value, ofNat]

/-- Logical version of positive top with no cell below it (Chain.cycleEnd). -/
def singlePositive (c : Counter) : Bool := positive c && c.pos.tail.isEmpty

theorem singlePositive_iff (c : Counter) (hc : Canonical c) :
    singlePositive c = true ↔ value c = 1 := by
  rcases c with ⟨ps,ns⟩
  cases ps with
  | nil => simp [singlePositive,positive,value]; omega
  | cons a ps =>
    have hn : ns = [] := by simpa [Canonical] using hc
    subst ns
    cases ps <;> simp [singlePositive,positive,value] <;> omega

theorem ofNat_canonical (n : ℕ) : Canonical (ofNat n) := Or.inr rfl
theorem inc_ofNat (n : ℕ) : inc (ofNat n) = ofNat (n+1) := by
  simp [inc, ofNat, List.replicate_succ]
theorem dec_ofNat_succ (n : ℕ) : dec (ofNat (n+1)) = ofNat n := by
  simp [dec, ofNat, List.replicate_succ]

structure Cursor where
  rest : List (Fin 3)
  work : Counter
  tape : GalilScaffoldTape.Tape

def encode (x : GalilScaffoldCopy.Cursor) : Cursor := ⟨x.rest, ofNat x.work, x.tape⟩

/-- The copy loop using actual two-stack zero/positive tests and dec,
rather than testing and subtracting a natural-number field directly. -/
inductive Copy : Cursor → ℕ → Cursor → Bool → Prop
  | stop (x : Cursor) (h : x.rest = [] ∨ zero x.work = true) :
      Copy x 1 { x with tape := GalilScaffoldTape.write x.tape 5 } x.rest.isEmpty
  | next (a : Fin 3) (xs : List (Fin 3)) (c : Counter) (t : GalilScaffoldTape.Tape)
      (n : ℕ) (y : Cursor) (final : Bool) (hc : positive c = true)
      (hr : Copy ⟨xs,dec c,GalilScaffoldTape.moveRight
        (GalilScaffoldTape.write t (GalilFppPreparation.symbol a))⟩ n y final) :
      Copy ⟨a :: xs,c,t⟩ (n+1) y final

theorem realize_copy {x y : GalilScaffoldCopy.Cursor} {n : ℕ} {final : Bool}
    (hr : GalilScaffoldCopy.Copy x n y final) : Copy (encode x) n (encode y) final := by
  induction hr with
  | stop x h =>
    apply Copy.stop
    rcases h with he | he
    · exact Or.inl he
    · right; simp [encode, ofNat, zero, he]
  | next a xs k n t y final hr ih =>
    apply Copy.next
    · simp [ofNat, positive, List.replicate_succ]
    · simpa [encode, dec_ofNat_succ] using ih

theorem copy_exact (xs : List (Fin 3)) (work : ℕ) (t : GalilScaffoldTape.Tape) :
    Copy ⟨xs,ofNat work,t⟩ ((xs.take work).length+1)
      ⟨xs.drop work, ofNat (work-xs.length),
        GalilScaffoldTape.write
          (GalilScaffoldLoad.fill ((xs.take work).map GalilFppPreparation.symbol) t) 5⟩
      (xs.drop work).isEmpty := by
  exact realize_copy (GalilScaffoldCopy.copy_exact xs work t)

#print axioms copy_exact
#print axioms zero_iff
#print axioms negative_iff
#print axioms inc_value
#print axioms dec_value
#print axioms realize_copy
end PalPeg.GalilScaffoldCounter
