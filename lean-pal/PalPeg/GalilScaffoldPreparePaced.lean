import PalPeg.GalilScaffoldPrepareControl

set_option autoImplicit false
namespace PalPeg.GalilScaffoldPreparePaced
open GalilScaffoldPrepareControl
open GalilScaffoldCounter (Counter dec value)

def afterAdvance (b : Bool) (s : State) : State :=
  if b then {s with debt := dec s.debt} else s

def spend : List Bool → Counter → Counter
  | [],c => c
  | b :: bs,c => spend bs (if b then dec c else c)

theorem spend_value (bs : List Bool) (c : Counter) : value (spend bs c) = value c-bs.count true := by
  induction bs generalizing c with
  | nil => simp [spend]
  | cons b bs ih =>
    cases b <;> simp [spend,ih,GalilScaffoldCounter.dec_value] <;> omega

theorem tick_rebase {x y : State} {b : Bool} (hr : Tick b x y) (c : Counter) :
    Tick b {x with debt := c} {y with debt := c} := by
  cases hr with
  | idle => exact .idle _
  | lowerBit x hm hp => exact .lowerBit _ hm hp
  | lowerEnd x hm hp => exact .lowerEnd _ hm hp
  | lowerLeft x hm hf hl => exact .lowerLeft _ hm hf hl
  | beginCopy x hm hf => exact .beginCopy _ hm hf
  | copyBit x a hm ha hw => exact .copyBit _ a hm ha hw
  | copyEnd x hm he => exact .copyEnd _ hm he
  | sourceLeft x hm hf hl => exact .sourceLeft _ hm hf hl
  | startRun x hm hf => exact .startRun _ hm hf

/-- Each pair is (preparation enabled, outer advance fired), in Scala order.
The caller still owes correspondence to the actual active/compare guards. -/
inductive PacedRun : State → List (Bool × Bool) → State → Prop
  | nil (x : State) : PacedRun x [] x
  | cons (x y z : State) (enabled advance : Bool) (es : List (Bool × Bool))
      (ht : Tick enabled x y) (hr : PacedRun (afterAdvance advance y) es z) :
      PacedRun x ((enabled,advance) :: es) z

theorem interleave {x y : State} {bs : List Bool} (hr : Run x bs y)
    (as : List Bool) (hlen : as.length = bs.length) (c : Counter) :
    PacedRun {x with debt := c} (bs.zip as) {y with debt := spend as c} := by
  induction hr generalizing as c with
  | nil x =>
    have he : as = [] := by simpa using hlen
    subst as
    exact .nil _
  | cons x y z b bs ht hr ih =>
    cases as with
    | nil => simp at hlen
    | cons a as =>
      have hn : as.length = bs.length := by simpa using hlen
      have hrest := ih as hn (if a then dec c else c)
      have hstep := tick_rebase ht c
      apply PacedRun.cons _ _ _ b a _ hstep
      cases a <;> simpa [afterAdvance,spend,List.zip] using hrest

theorem spend_canonical (as : List Bool) (c : Counter)
    (hc : GalilScaffoldCounter.Canonical c) :
    GalilScaffoldCounter.Canonical (spend as c) := by
  induction as generalizing c with
  | nil => exact hc
  | cons a as ih =>
    apply ih
    cases a
    · exact hc
    · exact GalilScaffoldCounter.dec_canonical _ hc

/-- The first event belongs to the prepare dispatch, not its body. -/
inductive PacedPrepared (lower : Counter) (center : GalilScaffoldPlace.Place) :
    State → List Bool → State → Prop
  | intro (s t : State) (a : Bool) (as : List Bool)
      (hr : PacedRun (afterAdvance a (prepare s lower center))
        ((List.replicate as.length true).zip as) t) :
      PacedPrepared lower center s (a :: as) t

theorem prepared_interleave {lower : Counter} {center : GalilScaffoldPlace.Place}
    {s t : State} {n : ℕ} (hr : PreparedRun lower center s n t)
    (as : List Bool) (hlen : as.length = n) :
    PacedPrepared lower center s as {t with debt := spend as s.debt} := by
  cases hr with
  | intro t n hr =>
    cases as with
    | nil => simp at hlen
    | cons a as =>
      have hn : as.length = n := by simpa using hlen
      have h := interleave hr as (by simpa using hn)
        (if a then dec s.debt else s.debt)
      apply PacedPrepared.intro
      cases a <;> simpa [afterAdvance,prepare,spend,hn] using h

theorem paced_span {x y : State} {es : List (Bool × Bool)} (hr : PacedRun x es y) :
    y.span = x.span := by
  induction hr with
  | nil => rfl
  | cons x y z enabled advance es ht hr ih =>
    have hs : y.span = x.span := by cases ht <;> rfl
    cases advance <;> simpa [afterAdvance,hs] using ih

theorem prepared_span {lower : Counter} {center : GalilScaffoldPlace.Place}
    {x y : State} {as : List Bool} (hr : PacedPrepared lower center x as y) :
    y.span = x.span := by
  cases hr with
  | intro t a as hr =>
    have h := paced_span hr
    cases a <;> simpa [afterAdvance,prepare] using h

#print axioms prepared_span
#print axioms prepared_interleave
#print axioms interleave
#print axioms spend_value
end PalPeg.GalilScaffoldPreparePaced
