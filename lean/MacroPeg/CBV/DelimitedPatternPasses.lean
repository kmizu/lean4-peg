import MacroPeg.CBV.DelimitedWordPattern

namespace Shallot.MacroPeg.CBV.DelimitedPatternPasses
open DelimiterTemplate DelimitedWordPattern DelimitedCopyProjection

/-- All but the last pass are lookaheads at the original origin. -/
def combine (f : Nat → Option (List Char)) : List Nat → Option (List Char)
  | [] => none
  | [i] => f i
  | i::j::is => (f i).bind (fun _ => combine f (j::is))

theorem combine_some (f : Nat → Option (List Char))
    (hcoherent : ∀ i j a b, f i=some a → f j=some b → a=b) :
    ∀ is, is≠[] → ∀ rest, combine f is=some rest ↔ ∀ i∈is, f i=some rest
  | [],hn,rest => False.elim (hn rfl)
  | [i],_,rest => by simp [combine]
  | i::j::is,_,rest => by
    change ((f i).bind (fun _ => combine f (j::is))=some rest) ↔ _
    rw [Option.bind_eq_some_iff]
    constructor
    · rintro ⟨a,ha,ht⟩
      have hh := (combine_some f hcoherent (j::is) (by simp) rest).mp ht
      intro k hk
      rcases List.mem_cons.mp hk with he|hk
      · subst k
        have he := hcoherent i j a rest ha (hh j (by simp))
        simpa [he] using ha
      · exact hh k hk
    · intro h
      exact ⟨rest,h i (by simp),(combine_some f hcoherent (j::is) (by simp) rest).mpr (fun k hk => h k (by simp [hk]))⟩

/-- Projection results at the actual, differing argument endpoints. -/
def pass (d : Char) (E tails : List (List Char)) (js : List Nat) (i : Nat) : Option (List Char) :=
  run d [E[i]!] (afterParts d i js) tails[i]!

theorem coherent (d : Char) (E tails : List (List Char))
    (hfree : ∀ i, (hi : i<E.length) → Free d E[i])
    (htails : tails.length=E.length) (x : List Char)
    (hprefix : ∀ i, (hi : i<E.length) → x=E[i]++(tails[i]'(by omega)))
    (j : Nat) (js : List Nat) (i k : Nat) (hi : i<E.length) (hk : k<E.length)
    (a b : List Char) (ha : pass d E tails (j::js) i=some a) (hb : pass d E tails (j::js) k=some b) : a=b := by
  have hp (i : Nat) (hi : i<E.length) : pass d E tails (j::js) i=run d [E[i]] (viewParts d i (j::js)) x := by
    simp only [pass,getElem!_pos E i hi,getElem!_pos tails i (show i<tails.length by omega)]
    rw [after_eq_view d E[i] (hfree i hi),←hprefix i hi]
  rw [hp i hi,view_iff d E[i] (hfree i hi) i] at ha
  rw [hp k hk,view_iff d E[k] (hfree k hk) k] at hb
  exact matches_endpoint_unique d E[i] E[k] i k (j::js) x a b ha hb

/-- A finite ordered conjunction of unary passes equals the actual source
suffix transformation for arbitrary arity and arbitrary occurrence order. -/
theorem run_eq (d : Char) (E tails : List (List Char)) (hn : 0<E.length)
    (hfree : ∀ i, (hi : i<E.length) → Free d E[i])
    (htails : tails.length=E.length) (x : List Char)
    (hprefix : ∀ i, (hi : i<E.length) → x=E[i]++(tails[i]'(by omega)))
    (j : Nat) (js : List Nat) (hscope : ∀ k∈j::js, k<E.length) :
    run d E (sourceParts d (j::js)) x=combine (pass d E tails (j::js)) (List.range E.length) := by
  let f := pass d E tails (j::js)
  -- Extend to an everywhere-coherent function by dropping invalid indices.
  let safe := fun i => if i<E.length then f i else none
  have hs (i : Nat) (hi : i<E.length) : safe i=f i := by simp [safe,hi]
  have hc : ∀ i k a b, safe i=some a → safe k=some b → a=b := by
    intro i k a b ha hb
    by_cases hi : i<E.length
    · by_cases hk : k<E.length
      · rw [hs i hi] at ha
        rw [hs k hk] at hb
        exact coherent d E tails hfree htails x hprefix j js i k hi hk a b ha hb
      · simp [safe,hk] at hb
    · simp [safe,hi] at ha
  have hreplace : ∀ is, (∀ i∈is, i<E.length) → combine f is=combine safe is := by
    intro is
    induction is with
    | nil => intro _; rfl
    | cons i is ih =>
      intro h
      cases is with
      | nil => simp only [combine,hs i (h i (by simp))]
      | cons k is =>
        simp only [combine,hs i (h i (by simp)),ih (fun z hz => h z (by simp [hz]))]
  have hne : List.range E.length≠[] := by simpa using (Nat.ne_of_gt hn)
  have he (rest : List Char) : run d E (sourceParts d (j::js)) x=some rest ↔ combine f (List.range E.length)=some rest := by
    rw [source_iff_after d E tails hn hfree htails x hprefix j js hscope,
      hreplace _ (fun i hi => List.mem_range.mp hi),combine_some safe hc _ hne]
    constructor
    · intro h i hi
      have hi := List.mem_range.mp hi
      rw [hs i hi]
      simpa only [f,pass,getElem!_pos E i hi,getElem!_pos tails i (show i<tails.length by omega)] using h i hi
    · intro h i hi
      have hh := h i (List.mem_range.mpr hi)
      rw [hs i hi] at hh
      simpa only [f,pass,getElem!_pos E i hi,getElem!_pos tails i (show i<tails.length by omega)] using hh
  cases ha : run d E (sourceParts d (j::js)) x with
  | some rest => exact ((he rest).mp ha).symm
  | none => cases hb : combine f (List.range E.length) with
    | none => rfl
    | some rest => have hh := (he rest).mpr hb; rw [ha] at hh; cases hh

end Shallot.MacroPeg.CBV.DelimitedPatternPasses
