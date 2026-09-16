import PalPeg.GalilPeriodCentre
import PalPeg.GalilPeriodUnion
import PalPeg.GalilDpCorrect

/-!
# DP candidates give periods

`GalilDpCorrect.Candidate w lower h` records what the fpp DP loop checks about the
window `w`: the prefixes of length `2h+1` and `4h+1` are both palindromes.  This
file turns that combinatorial fact into

* a period of the window itself (`candidate_hasPeriod`),
* the two centred palindromes of the encoded scan word sharing their right end at
  the head position `C` (`candidate_palAt`), and
* the periodicity of the encoded word on the index span `[C-4h, C]`
  (`candidate_periodOn`).
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- A DP candidate `h` makes the first `4h+1` places of the window periodic with
period `2h`. -/
theorem candidate_hasPeriod (w : List (Fin 3)) (lower h : ℕ)
    (hc : GalilDpCorrect.Candidate w lower h) :
    HasPeriod (w.take (4*h+1)) (2*h) := by
  obtain ⟨_,hn,hm,hs⟩ := hc
  have hlen : (w.take (4*h+1)).length = 4*h+1 := by
    simp only [List.length_take]; omega
  have hx : IsPal (w.take (4*h+1)) := hs
  have hk : 2*h+1 ≤ (w.take (4*h+1)).length := by omega
  have hy : IsPal ((w.take (4*h+1)).take (2*h+1)) := by
    rw [List.take_take,Nat.min_eq_left (by omega)]
    exact hm
  have hp := hasPeriod_of_isPal_take hx hk hy
  rw [hlen,show 4*h+1-(2*h+1) = 2*h from by omega] at hp
  exact hp

#print axioms candidate_hasPeriod

/-- A DP candidate at the centre place gives the two palindromes centred `C-h`
and `C-2h` with the same right end `C` on the encoded word. -/
theorem candidate_palAt (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool) (span lower h : ℕ)
    (hc : GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower h) :
    let C := position (represent ⟨a :: ls,gap⟩ (rs.map some) q)
    Manacher.PalAt (encoded ((a :: ls).reverse ++ rs ++ q)) (C - h) h ∧
    Manacher.PalAt (encoded ((a :: ls).reverse ++ rs ++ q)) (C - 2*h) (2*h) := by
  obtain ⟨_,hn,hm,hs⟩ := hc
  have hn' : 4*h+1 ≤ min (span+1) (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length := by
    simpa only [List.length_take] using hn
  have hspan : 4*h+1 ≤ span+1 := by omega
  have hTlen : 4*h+1 ≤ (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length := by omega
  have hC : position (represent ⟨a :: ls,gap⟩ (rs.map some) q)
      = (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length :=
    position_represent a ls gap (rs.map some) q
  have hm' : IsPal ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*h+1)) := by
    rw [List.take_take,Nat.min_eq_left (by omega)] at hm
    exact hm
  have hs' : IsPal ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*(2*h)+1)) := by
    rw [List.take_take,Nat.min_eq_left (show 4*h+1 ≤ span+1 from by omega)] at hs
    rw [show 2*(2*h)+1 = 4*h+1 from by omega]
    exact hs
  have p1 := (stream_prefix_palindrome a ls rs q gap h (by omega)).1 hm'
  have p2 := (stream_prefix_palindrome a ls rs q gap (2*h) (by omega)).1 hs'
  intro _C
  show Manacher.PalAt _ (position (represent ⟨a :: ls,gap⟩ (rs.map some) q) - h) h ∧
    Manacher.PalAt _ (position (represent ⟨a :: ls,gap⟩ (rs.map some) q) - 2*h) (2*h)
  rw [hC]
  exact ⟨p1,p2⟩

#print axioms candidate_palAt

/-- The periodicity near the centre implied by a DP candidate: the encoded scan
word has period `2h` on the index span `[C-4h, C]`. -/
theorem candidate_periodOn (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool) (span lower h : ℕ)
    (hc : GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower h) :
    let C := position (represent ⟨a :: ls,gap⟩ (rs.map some) q)
    PeriodOn (encoded ((a :: ls).reverse ++ rs ++ q)) (2*h) (C - 4*h) C := by
  have hpal := candidate_palAt a ls rs q gap span lower h hc
  obtain ⟨_,hn,_,_⟩ := hc
  have hn' : 4*h+1 ≤ min (span+1) (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length := by
    simpa only [List.length_take] using hn
  have hTlen : 4*h+1 ≤ (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length := by omega
  have hC : position (represent ⟨a :: ls,gap⟩ (rs.map some) q)
      = (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length :=
    position_represent a ls gap (rs.map some) q
  rw [hC] at hpal
  obtain ⟨h1,h2⟩ :
      Manacher.PalAt (encoded ((a :: ls).reverse ++ rs ++ q))
          ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length - h) h ∧
        Manacher.PalAt (encoded ((a :: ls).reverse ++ rs ++ q))
          ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length - 2*h) (2*h) := hpal
  -- `C` is at least `4h+1`, so all the subtractions below are honest.
  have hlt : (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length
      < (encoded ((a :: ls).reverse ++ rs ++ q)).length := by
    have := h2.2.1; omega
  have h2' : Manacher.PalAt (encoded ((a :: ls).reverse ++ rs ++ q))
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length - h)
      (((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length - 2*h) + 2*h
        - ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length - h)) := by
    rw [show ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length - 2*h) + 2*h
      - ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length - h) = h from by omega]
    exact h1
  have hper := span_hasPeriod_of_two_palAt h2 h2' (by omega) (by omega)
  rw [show ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length - 2*h) - 2*h
        = (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length - 4*h from by omega,
    show 2*(2*h)+1 = (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length + 1
        - ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length - 4*h) from by omega,
    show 2*(((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length - h)
        - ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length - 2*h)) = 2*h from by omega] at hper
  have hres := (hasPeriod_slice_iff (x := encoded ((a :: ls).reverse ++ rs ++ q)) (p := 2*h)
    (a := (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length - 4*h)
    (b := (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length) hlt (by omega)).1 hper
  intro _C
  show PeriodOn (encoded ((a :: ls).reverse ++ rs ++ q)) (2*h)
    (position (represent ⟨a :: ls,gap⟩ (rs.map some) q) - 4*h)
    (position (represent ⟨a :: ls,gap⟩ (rs.map some) q))
  rw [hC]
  exact hres

#print axioms candidate_periodOn

end PalPeg.GalilScaffoldChainInputSupply
