import Shallot.Peg.Packrat.Fixed
import Shallot.Peg.Undecidable.FordIff

/-!
# Bounded recognition for arbitrary PEGs

At the start call, `parse` returns semantic failure, success with its
consumed length, or no derivation. The finite iteration bound distinguishes
nontermination from semantic failure without a totality assumption.

The function-valued table is a specification, not a memoized implementation:
the bound counts rounds and does not establish a machine running-time bound.
-/

namespace Shallot.Packrat

/-- Every entry that ever fills is already filled at the explicit bound. -/
theorem iter_at_bound {g : Grammar} {x : List Char} {e : PExp} {i n : Nat} {r : Res}
    (he : e ∈ dom g) (hi : i ≤ x.length) (h : iter g x n e i = some r) :
    iter g x (bound g x) e i = some r := by
  rw [bound_fixed g x n e he i hi]
  exact iter_mono h (by omega)

/-- The bounded table records exactly the derivable outcomes with trees erased. -/
theorem bounded_iff {g : Grammar} {x : List Char} {e : PExp} {i : Nat} {r : Res}
    (he : e ∈ dom g) (hi : i ≤ x.length) :
    iter g x (bound g x) e i = some r ↔
      ∃ o, Derives g e (x.drop i) o ∧ erase (x.drop i) o = r := by
  constructor
  · exact iter_sound
  · rintro ⟨o, hd, hr⟩
    obtain ⟨n, hn⟩ := iter_complete hd
    rw [hr] at hn
    exact iter_at_bound he hi hn

/-- An empty bounded entry means that no semantic outcome has a derivation. -/
theorem bounded_none_iff {g : Grammar} {x : List Char} {e : PExp} {i : Nat}
    (he : e ∈ dom g) (hi : i ≤ x.length) :
    iter g x (bound g x) e i = none ↔ ∀ o, ¬ Derives g e (x.drop i) o := by
  constructor
  · intro h o hd
    have hb := (bounded_iff he hi).mpr ⟨o, hd, rfl⟩
    rw [h] at hb
    cases hb
  · intro h
    cases hv : iter g x (bound g x) e i with
    | none => rfl
    | some r =>
      obtain ⟨o, hd, _⟩ := iter_sound hv
      exact False.elim (h o hd)

/-- Bounded parsing, distinguishing divergence, failure, and success. -/
def parse (g : Grammar) (x : List Char) : Option Res :=
  iter g x (bound g x) (.nt g.start) 0

theorem parse_iff {g : Grammar} {x : List Char} {r : Res} :
    parse g x = some r ↔ ∃ o, Derives g (.nt g.start) x o ∧ erase x o = r := by
  simpa only [parse, List.drop_zero] using bounded_iff (dom_start g) (Nat.zero_le x.length)

theorem parse_none_iff {g : Grammar} {x : List Char} :
    parse g x = none ↔ ∀ o, ¬ Derives g (.nt g.start) x o := by
  simpa only [parse, List.drop_zero] using bounded_none_iff (dom_start g) (Nat.zero_le x.length)

theorem parse_fail_iff {g : Grammar} {x : List Char} :
    parse g x = some none ↔ Derives g (.nt g.start) x .fail := by
  rw [parse_iff]
  constructor
  · rintro ⟨o, hd, he⟩
    cases o with
    | fail => exact hd
    | ok _ _ => cases he
  · intro hd; exact ⟨.fail, hd, rfl⟩

/-- Ford's acceptance convention: successful parsing may leave a suffix. -/
def accepts (g : Grammar) (x : List Char) : Bool :=
  match parse g x with
  | some (some _) => true
  | _ => false

/-- The bounded recognizer decides the original grammar's language. -/
theorem accepts_iff (g : Grammar) (x : List Char) :
    accepts g x = true ↔ Shallot.Accepts g x := by
  constructor
  · intro h
    unfold accepts at h
    cases hp : parse g x with
    | none => simp [hp] at h
    | some r =>
      cases r with
      | none => simp [hp] at h
      | some k =>
        obtain ⟨o, hd, he⟩ := parse_iff.mp hp
        cases o with
        | fail => cases he
        | ok t rest => exact ⟨t, rest, hd⟩
  · rintro ⟨t, rest, hd⟩
    have hp := parse_iff.mpr ⟨.ok t rest, hd, rfl⟩
    simp [accepts, hp, erase]

/-- Full-input recognition, as used by `Cfg.IsPEL`. -/
def fullAccepts (g : Grammar) (x : List Char) : Bool :=
  decide (parse g x = some (some x.length))

/-- Full-input recognition agrees with successful derivation leaving no suffix. -/
theorem fullAccepts_iff (g : Grammar) (x : List Char) :
    fullAccepts g x = true ↔ ∃ t, Derives g (.nt g.start) x (.ok t []) := by
  simp only [fullAccepts, decide_eq_true_eq, parse_iff]
  constructor
  · rintro ⟨o, hd, he⟩
    cases o with
    | fail => cases he
    | ok t rest =>
      simp only [erase, Option.some.injEq] at he
      obtain ⟨p, hp⟩ := derives_suffix hd t rest rfl
      have hl : rest.length = 0 := by
        have hx : x.length = p.length + rest.length := by rw [hp, List.length_append]
        omega
      have hr : rest = [] := List.length_eq_zero_iff.mp hl
      exact ⟨t, hr ▸ hd⟩
  · rintro ⟨t, hd⟩
    exact ⟨.ok t [], hd, by simp [erase]⟩

end Shallot.Packrat
