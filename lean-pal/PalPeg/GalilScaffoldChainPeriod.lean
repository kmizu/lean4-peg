import PalPeg.GalilScaffoldChainAnswer

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainPeriod

/-- The eleven Scala period symbols, independently of the nine DP symbols. -/
inductive Token where
  | blank | left | plain (a : Fin 3) | first (a : Fin 3) | last (a : Fin 3)
  deriving DecidableEq

def isFirst : Token → Bool
  | .first _ => true
  | _ => false

/-- Decoded two-stack period tape; physical StackPool refinement is separate. -/
structure Tape where
  left : List Token
  focus : Token
  right : List Token
  deriving DecidableEq

def moveRight (t : Tape) : Tape := match t.right with
  | [] => ⟨t.focus :: t.left, .blank, []⟩
  | a :: rs => ⟨t.focus :: t.left, a, rs⟩

def moveLeft (t : Tape) : Tape := match t.left with
  | [] => t
  | a :: ls => ⟨ls, a, t.focus :: t.right⟩

def write (t : Tape) (a : Token) : Tape := {t with focus := a}
def start (a : Fin 3) : Tape := ⟨[], .first a, []⟩
def put (t : Tape) (a : Fin 3) : Tape := write (moveRight t) (.plain a)
def fill : Tape → List (Fin 3) → Tape
  | t, [] => t
  | t, a :: xs => fill (put t a) xs

/-- Each back tick tests FIRST before moving. The final tick moves right
from FIRST and enters watch, rather than leaving the head on FIRST. -/
inductive Back : Tape → ℕ → Tape → Prop
  | done (t) (hf : isFirst t.focus = true) : Back t 1 (moveRight t)
  | next (t) (hf : isFirst t.focus = false) (hl : t.left ≠ [])
      {n u} (hr : Back (moveLeft t) n u) : Back t (n+1) u

theorem back_exact (ls : List Token) (c : Fin 3) (a : Token) (rs : List Token)
    (ha : isFirst a = false) (hs : ∀ x ∈ ls, isFirst x = false) :
    Back ⟨ls ++ [.first c], a, rs⟩ (ls.length+2)
      (moveRight ⟨[], .first c, ls.reverse ++ a :: rs⟩) := by
  induction ls generalizing a rs with
  | nil =>
    apply Back.next _ ha (by simp)
    exact Back.done _ rfl
  | cons b ls ih =>
    apply Back.next _ ha (by simp)
    have hb := hs b (by simp)
    have ht : ∀ x ∈ ls, isFirst x = false := fun x hx => hs x (by simp [hx])
    simpa [moveLeft, List.reverse_cons, List.append_assoc] using ih b (a :: rs) hb ht

/-- Copy retains every previous focus on the left stack, in reverse order. -/
theorem fill_stack (xs : List (Fin 3)) (ls : List Token) (a : Token) :
    let t := fill ⟨ls, a, []⟩ xs
    t.right = [] ∧ t.focus :: t.left = (xs.map Token.plain).reverse ++ a :: ls := by
  induction xs generalizing ls a with
  | nil => simp [fill]
  | cons b xs ih =>
    simpa [fill, put, write, moveRight, List.reverse_cons, List.append_assoc] using
      ih (a :: ls) (.plain b)

/-- Copy synchronizes period.moveRight/write with OUTPUT, h and walker. -/
inductive Copy : GalilScaffoldTape.Tape → GalilScaffoldCounter.Counter →
    GalilScaffoldPlace.Place → Tape → ℕ → GalilScaffoldTape.Tape →
    GalilScaffoldCounter.Counter → GalilScaffoldPlace.Place → Tape → Prop
  | stop (t c p v) : Copy t c p v 0 t c p v
  | next {t c p v n u d q z} (a : Fin 3)
      (one : t.focus = 8) (legal : t.left ≠ [])
      (present : GalilScaffoldPlace.read (GalilScaffoldPlace.left p) = some a)
      (rest : Copy (GalilScaffoldTape.moveLeft t) (GalilScaffoldCounter.inc c)
        (GalilScaffoldPlace.left p) (put v a) n u d q z) :
      Copy t c p v (n+1) u d q z

theorem copy_period {t c p n u d q xs}
    (hr : GalilScaffoldChainAnswer.CopyWalk t c p n u d q xs) (v : Tape) :
    Copy t c p v n u d q (fill v xs) := by
  induction hr generalizing v with
  | stop t c p => exact Copy.stop t c p v
  | next a one legal present rest ih =>
    exact Copy.next a one legal present (ih (put v a))

theorem fill_append (t : Tape) (xs ys : List (Fin 3)) :
    fill t (xs ++ ys) = fill (fill t xs) ys := by
  induction xs generalizing t with
  | nil => rfl
  | cons a xs ih => exact ih (put t a)

/-- After the final plain letter is marked LAST, back reaches the first
prediction position in exactly h+1 ticks, for h=ys.length+1. -/
theorem marked_back (c b : Fin 3) (ys : List (Fin 3)) :
    Back (write (fill (start c) (ys ++ [b])) (.last b)) (ys.length+2)
      (moveRight ⟨[], .first c, ys.map Token.plain ++ [.last b]⟩) := by
  have hf := fill_stack ys [] (.first c)
  dsimp only at hf
  rw [fill_append]
  simp only [fill]
  have he : write (put (fill (start c) ys) b) (.last b) =
      ⟨(ys.map Token.plain).reverse ++ [.first c], .last b, []⟩ := by
    have hr : (fill (start c) ys).right = [] := hf.1
    simp only [put, moveRight, hr, write]
    congr 1
    exact hf.2
  rw [he]
  simpa using back_exact (ys.map Token.plain).reverse c (.last b) [] rfl
    (by intro x hx; simp only [List.mem_reverse, List.mem_map] at hx
        obtain ⟨a, _, rfl⟩ := hx; rfl)

theorem copy_length {t c p n u d q xs}
    (hr : GalilScaffoldChainAnswer.CopyWalk t c p n u d q xs) : xs.length = n := by
  induction hr with
  | stop => rfl
  | next a one legal present rest ih => simp [ih]

/-- One nonempty copy trace supplies both the plain endpoint required by
the marking dispatch and the exact subsequent back trace. -/
theorem copy_then_back {t c p n u d q xs}
    (hr : GalilScaffoldChainAnswer.CopyWalk t c p n u d q xs)
    (hn : 0 < n) (center : Fin 3) :
    ∃ ys b, xs = ys ++ [b] ∧
      Copy t c p (start center) n u d q (fill (start center) xs) ∧
      (fill (start center) xs).focus = .plain b ∧
      Back (write (fill (start center) xs) (.last b)) (n+1)
        (moveRight ⟨[], .first center, ys.map Token.plain ++ [.last b]⟩) := by
  have hl := copy_length hr
  cases he : xs.reverse with
  | nil =>
    have hx : xs.length = 0 := by
      simpa only [List.length_reverse, List.length_nil] using congrArg List.length he
    omega
  | cons b bs =>
    have hx : xs = bs.reverse ++ [b] := by
      have hv := congrArg List.reverse he
      simpa using hv
    refine ⟨bs.reverse, b, hx, copy_period hr _, ?_, ?_⟩
    · rw [hx, fill_append]
      simp [fill, put, write]
    · have hcount : n+1 = bs.reverse.length+2 := by
        rw [hx] at hl
        simp only [List.length_append, List.length_singleton] at hl
        omega
      rw [hx, hcount]
      exact marked_back center b bs.reverse

/-- The found DP machine supplies Chain.start's present center and the
same copy, endpoint-marking and back tape. This does not yet model outer
matched events, mode changes, or the physical heap. -/
theorem found_start_back
    {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ}
    (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run)
    (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config)) :
    ∃ h center u q ys b,
      GalilDpCorrect.Candidate w lower h ∧
      GalilScaffoldPlace.read p = some center ∧
      Copy (y.config.tapes 11) GalilScaffoldCounter.reset p (start center) h u
        (GalilScaffoldCounter.ofNat h) q (fill (start center) (ys ++ [b])) ∧
      u.focus = 4 ∧ GalilScaffoldCounter.positive (GalilScaffoldCounter.ofNat h) = true ∧
      (fill (start center) (ys ++ [b])).focus = .plain b ∧
      Back (write (fill (start center) (ys ++ [b])) (.last b)) (h+1)
        (moveRight ⟨[], .first center, ys.map Token.plain ++ [.last b]⟩) ∧
      ys ++ [b] = ((GalilScaffoldPlace.stream p).drop 1).take h ∧
      GalilScaffoldPlace.stream q = (GalilScaffoldPlace.stream p).drop h := by
  obtain ⟨h,u,q,xs,hc,hcopy,hu,hpositive,hxs,hq⟩ :=
    GalilScaffoldChainAnswer.found_copy_walk p hw hr hs ht hv
  have hh : 0 < h := by have := hc.1; omega
  have hne : GalilScaffoldPlace.stream p ≠ [] := by
    intro he
    have hb := hc.2.1
    rw [hw, he] at hb
    simp at hb
  cases he : GalilScaffoldPlace.read p with
  | none => exact False.elim (hne ((GalilScaffoldPlace.read_none p).mp he))
  | some center =>
    obtain ⟨ys,b,hparts,hperiod,hplain,hback⟩ := copy_then_back hcopy hh center
    rw [hparts] at hperiod hplain hback hxs
    exact ⟨h,center,u,q,ys,b,hc,rfl,hperiod,hu,hpositive,hplain,hback,hxs,hq⟩

#print axioms found_start_back
#print axioms copy_then_back
#print axioms marked_back
#print axioms copy_period
#print axioms back_exact
#print axioms fill_stack
end PalPeg.GalilScaffoldChainPeriod
