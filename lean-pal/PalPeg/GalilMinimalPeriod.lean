import PalPeg.GalilCandidatePeriod
import PalPeg.GalilShortPeriod
import PalPeg.GalilLiveCentreShift

/-!
# Minimality of the span period from the DP search

Three pieces of word combinatorics for the restart step of Galil's real-time
matcher.

* `palAt_pair_of_period` — the converse of `candidate_palAt`: a period `2g` on the
  span of `PalAt (encoded raw) C k` (with `4g ≤ k`) produces the two DP-style
  palindromes centred `C-g` and `C-2g`.
* `result_least` — the DP `Result` at `first = 0` reaching `pc = 346` exposes its
  witness `k` as a candidate that is least among all candidates.
* `no_short_period_of_minimal` — Fine–Wilf: with period `2h` on the span, no DP
  candidate strictly between `lower` and `h`, and no period `2δ` for
  `0 < δ ≤ lower`, the span has no period below `2h` at all.

`no_candidate_of_result` as originally stated (`∀ g < h, ¬ Candidate`, for an
arbitrary candidate `h`) is **false**: `Result` only pins down the *least*
candidate, and `h` may be any larger one.  `no_candidate_of_result_false`
refutes it; `result_least` is the correct form.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldInputHead GalilScaffoldChainVerifier

/-! ## 1. A span period gives the two DP palindromes -/

/-- If the span of `PalAt (encoded raw) C k` has period `2g` and `4g ≤ k`, then the
encoded word carries the palindromes centred `C-g` (radius `g`) and `C-2g`
(radius `2g`) — exactly the two prefixes the fpp DP checks. -/
theorem palAt_pair_of_period {raw : List (Fin 2)} {C k g : ℕ}
    (hpal : PalAt (encoded raw) C k) (hg : 4*g ≤ k)
    (hper : HasPeriod (Span raw C k) (2*g)) :
    PalAt (encoded raw) (C - g) g ∧ PalAt (encoded raw) (C - 2*g) (2*g) := by
  obtain ⟨hkC, hlen, hsym⟩ := hpal
  have espan : Span raw C k = ((encoded raw).drop (C-k)).take ((C+k)+1-(C-k)) := by
    unfold Span
    rw [show (C+k)+1-(C-k) = 2*k+1 from by omega]
  have hpo : PeriodOn (encoded raw) (2*g) (C-k) (C+k) := by
    refine (hasPeriod_slice_iff (x := encoded raw) hlen (by omega)).1 ?_
    rw [← espan]
    exact hper
  refine ⟨⟨by omega, by omega, ?_⟩, ⟨by omega, by omega, ?_⟩⟩
  · intro i hi
    have hm := hsym (g+i) (by omega)
    have hstep := hpo (C-g+i) (by omega) (by omega)
    rw [show C-g+i+2*g = C+(g+i) from by omega] at hstep
    rw [show C-g-i = C-(g+i) from by omega, hm]
    exact hstep.symm
  · intro i hi
    have hm := hsym (2*g+i) (by omega)
    have s1 := hpo (C-2*g+i) (by omega) (by omega)
    have s2 := hpo (C+i) (by omega) (by omega)
    rw [show C-2*g+i+2*g = C+i from by omega] at s1
    rw [show C+i+2*g = C+(2*g+i) from by omega] at s2
    rw [show C-2*g-i = C-(2*g+i) from by omega, hm]
    exact (s1.trans s2).symm

#print axioms palAt_pair_of_period

/-! ## 2. What the DP result really says -/

/-- The DP `Result` at `first = 0`, when it reports success (`pc = 346`), exposes a
candidate `k` (the cursor on OUTPUT) that is least among all candidates. -/
theorem result_least {w : List (Fin 3)} {lower : ℕ} {y : GalilFppWide.Config 12}
    (hres : GalilDpCorrect.Result w lower 0 y) (hy : y.pc = 346) :
    ∃ k, GalilDpCorrect.Candidate w lower k ∧ y.pos 11 = k ∧
      ∀ g, g < k → ¬ GalilDpCorrect.Candidate w lower g := by
  rcases hres with ⟨k, _, hc, hmin, _, _, hpos⟩ | ⟨hpc, _⟩
  · exact ⟨k, hc, hpos, fun g hgk => hmin g (Nat.zero_le _) hgk⟩
  · rw [hy] at hpc
    exact absurd hpc (by decide)

#print axioms result_least

/-- The originally proposed form of `no_candidate_of_result` is false: `Result`
only determines the *least* candidate, so an arbitrary candidate `h` may well have
candidates below it.  Counterexample: `w = 0^9`, `lower = 0`, least candidate
`k = 1`, and `h = 2` is also a candidate. -/
theorem no_candidate_of_result_false :
    ¬ ∀ (w : List (Fin 3)) (lower h : ℕ) (y : GalilFppWide.Config 12),
        GalilDpCorrect.Result w lower 0 y → GalilDpCorrect.Candidate w lower h →
        y.pc = 346 → ∀ g, g < h → ¬ GalilDpCorrect.Candidate w lower g := by
  intro hbad
  have hc1 : GalilDpCorrect.Candidate (List.replicate 9 (0 : Fin 3)) 0 1 :=
    ⟨by omega, by decide, by decide, by decide⟩
  have hc2 : GalilDpCorrect.Candidate (List.replicate 9 (0 : Fin 3)) 0 2 :=
    ⟨by omega, by decide, by decide, by decide⟩
  have hres : GalilDpCorrect.Result (List.replicate 9 (0 : Fin 3)) 0 0
      { pc := 346, tape := fun _ => GalilDpCounters.output 1, pos := fun _ => 1 } := by
    refine Or.inl ⟨1, Nat.zero_le _, hc1, ?_, rfl, rfl, rfl⟩
    intro j _ hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact fun hc => absurd hc.1 (by omega)
  exact hbad _ 0 2 _ hres hc2 rfl 1 (by omega) hc1

#print axioms no_candidate_of_result_false

/-! ## 3. Fine–Wilf: the span period `2h` is minimal -/

/-- **Minimality of the span period.**  Suppose the span of the palindrome centred
at the head position `C` with radius `k` has period `2h` (`2h ≤ k`), the DP search
found no candidate `g` with `lower < g < h` in the window of the first `k+1`
places, and no `2δ` with `0 < δ ≤ lower` is a period of the span.  Then the span
has no period below `2h` whatsoever.

The hypothesis `k < C` says the left end of the span is a genuine place of the
stream (the machine's left head sits on the encoded word), which is what makes the
window `(stream …).take (k+1)` long enough to hold `4g+1` places. -/
theorem no_short_period_of_minimal (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {C k h lower : ℕ}
    (hC : C = position (represent ⟨a :: ls,gap⟩ (rs.map some) q)) (hkC : k < C)
    (hpal : PalAt (encoded ((a :: ls).reverse ++ rs ++ q)) C k) (hh : 0 < h) (hk : 2*h ≤ k)
    (hper : HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C k) (2*h))
    (hcand : ∀ g, lower < g → g < h →
      ¬ GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (k+1)) lower g)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower →
      ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C k) (2*δ)) :
    ∀ p, 0 < p → p < 2*h → ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C k) p := by
  intro p hp hlt hper'
  have hstream : (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length = C := by
    rw [hC, position_represent]
  have hkle : k ≤ C := hpal.1
  have hlen : C + k < (encoded ((a :: ls).reverse ++ rs ++ q)).length := hpal.2.1
  have espan : Span ((a :: ls).reverse ++ rs ++ q) C k
      = ((encoded ((a :: ls).reverse ++ rs ++ q)).drop (C-k)).take ((C+k)+1-(C-k)) := by
    unfold Span
    rw [show (C+k)+1-(C-k) = 2*k+1 from by omega]
  have hSlen : (Span ((a :: ls).reverse ++ rs ++ q) C k).length = 2*k+1 := by
    unfold Span
    rw [List.length_take, List.length_drop]
    omega
  -- `p` is even, because the encoded word alternates separators and letters.
  have hpo : PeriodOn (encoded ((a :: ls).reverse ++ rs ++ q)) p (C-k) (C+k) := by
    refine (hasPeriod_slice_iff (x := encoded ((a :: ls).reverse ++ rs ++ q))
      hlen (by omega)).1 ?_
    rw [← espan]
    exact hper'
  have heven : p % 2 = 0 := encoded_periodOn_even hpo hp (by omega) hlen
  obtain ⟨δ, rfl⟩ : ∃ δ, p = 2*δ := ⟨p/2, by omega⟩
  have hδ : 0 < δ := by omega
  have hδh : δ < h := by omega
  -- `g := gcd δ h` is a period of the span by Fine–Wilf, and `4g ≤ 2h ≤ k`.
  obtain ⟨g, hgdef⟩ : ∃ g, g = Nat.gcd δ h := ⟨_, rfl⟩
  have hgdδ : g ∣ δ := by rw [hgdef]; exact Nat.gcd_dvd_left δ h
  have hgdh : g ∣ h := by rw [hgdef]; exact Nat.gcd_dvd_right δ h
  obtain ⟨m, hm⟩ := hgdδ
  have hg : 0 < g := by
    rcases Nat.eq_zero_or_pos g with rfl | hpos
    · simp at hm; omega
    · exact hpos
  have hgδ : g ≤ δ := Nat.le_of_dvd hδ ⟨m, hm⟩
  obtain ⟨c, hc⟩ := hgdh
  have hc2 : 2 ≤ c := by
    rcases c with _ | _ | c
    · simp at hc; omega
    · simp at hc; omega
    · omega
  have h2g : 2*g ≤ h := by
    have hmul : g * 2 ≤ g * c := Nat.mul_le_mul (le_refl g) hc2
    omega
  have h4g : 4*g ≤ k := by omega
  have hgcd : Nat.gcd (2*δ) (2*h) = 2*g := by rw [Nat.gcd_mul_left, ← hgdef]
  have hfw : HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C k) (2*g) := by
    have hw := fineWilf hper' hper (by omega) (by omega) (by rw [hSlen, hgcd]; omega)
    rwa [hgcd] at hw
  by_cases hlg : g ≤ lower
  · exact hlow g hg hlg hfw
  · have hlg' : lower < g := by omega
    obtain ⟨p1, p2⟩ := palAt_pair_of_period hpal h4g hfw
    have q1 : IsPal ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*g+1)) := by
      refine (stream_prefix_palindrome a ls rs q gap g (by rw [hstream]; omega)).2 ?_
      rw [hstream]
      exact p1
    have q2 : IsPal ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (4*g+1)) := by
      rw [show 4*g+1 = 2*(2*g)+1 from by omega]
      refine (stream_prefix_palindrome a ls rs q gap (2*g) (by rw [hstream]; omega)).2 ?_
      rw [hstream]
      exact p2
    refine hcand g hlg' (by omega) ⟨hlg', ?_, ?_, ?_⟩
    · rw [List.length_take, hstream]
      omega
    · rw [List.take_take, Nat.min_eq_left (by omega)]
      exact q1
    · rw [List.take_take, Nat.min_eq_left (by omega)]
      exact q2

#print axioms no_short_period_of_minimal

end PalPeg.GalilScaffoldChainInputSupply
