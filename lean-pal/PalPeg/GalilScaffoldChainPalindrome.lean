import PalPeg.GalilScaffoldChainRestart

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainPalindrome

theorem palindrome_split {α : Type} (w : List α) (n : ℕ)
    (hlen : w.length = 2*n+1) (hp : w.reverse = w) :
    w = w.take (n+1) ++ (w.take n).reverse := by
  have hd := congrArg (fun xs : List α => xs.drop (n+1)) hp
  rw [List.drop_reverse,hlen,show 2*n+1-(n+1) = n by omega] at hd
  have he := List.take_append_drop (n+1) w
  rw [← hd] at he
  exact he.symm

theorem palindrome_prefix {α : Type} (w : List α) (n : ℕ)
    (hlen : 2*n+1 ≤ w.length) (hp : (w.take (2*n+1)).reverse = w.take (2*n+1)) :
    w.take (2*n+1) = w.take (n+1) ++ (w.take n).reverse := by
  have he := palindrome_split (w.take (2*n+1)) n (by simp [List.length_take,hlen]) hp
  simpa [List.take_take,show min (n+1) (2*n+1) = n+1 by omega,
    show min n (2*n+1) = n by omega] using he

/-- The two actual DP palindrome tests determine exactly the two-bounce
word stored/predicted by Chain, not merely a numerical period bound. -/
theorem candidate_word (w : List (Fin 3)) (lower : ℕ) (center b : Fin 3)
    (xs : List (Fin 3)) (hc : GalilDpCorrect.Candidate w lower (xs.length+1))
    (hhead : w.take (xs.length+2) = center :: (xs ++ [b])) :
    w.take (4*(xs.length+1)+1) = center ::
      (GalilScaffoldChainSweep.bounce center b xs ++ GalilScaffoldChainSweep.bounce center b xs) := by
  have hshort : w.take (xs.length+1) = center :: xs := by
    have he := congrArg (List.take (xs.length+1)) hhead
    rw [List.take_take, Nat.min_eq_left (by omega)] at he
    simpa using he
  have hp1 := palindrome_prefix w (xs.length+1) (by have := hc.2.1; omega) hc.2.2.1
  have hfirst : w.take (2*(xs.length+1)+1) = center ::
      (xs ++ [b] ++ xs.reverse ++ [center]) := by
    rw [hp1,hshort]
    have he : xs.length+1+1 = xs.length+2 := by omega
    rw [he,hhead]
    simp [List.reverse_cons,List.append_assoc]
  have hbody : w.take (2*(xs.length+1)) = center :: (xs ++ [b] ++ xs.reverse) := by
    have he := congrArg (List.take (2*(xs.length+1))) hfirst
    rw [List.take_take,Nat.min_eq_left (by omega)] at he
    have hn : 2*(xs.length+1) = (xs ++ [b] ++ xs.reverse).length+1 := by simp; omega
    conv at he => rhs; rw [hn,List.take_succ_cons,List.take_left]
    exact he
  have hn2 : 2*(2*(xs.length+1)) = 4*(xs.length+1) := by omega
  have hp2 := palindrome_prefix w (2*(xs.length+1)) (by rw [hn2]; exact hc.2.1)
    (by rw [hn2]; exact hc.2.2.2)
  rw [show 2*(2*(xs.length+1))+1 = 4*(xs.length+1)+1 by omega] at hp2
  rw [hp2,hfirst,hbody]
  simp [GalilScaffoldChainSweep.bounce,List.reverse_append,List.reverse_cons,List.append_assoc]

/-- Every prefix of the candidate's first 4h predicted characters is
accepted by the control. Online use still requires the verifier's right
history to coincide with this known word. -/
theorem candidate_prefix_safe (w : List (Fin 3)) (lower : ℕ) (center b : Fin 3)
    (xs : List (Fin 3)) (hc : GalilDpCorrect.Candidate w lower (xs.length+1))
    (hhead : w.take (xs.length+2) = center :: (xs ++ [b]))
    (n : ℕ) (hn : n ≤ 4*(xs.length+1)) :
    (GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready center xs b)
      ((w.drop 1).take n)).broken = false := by
  let word := GalilScaffoldChainSweep.bounce center b xs ++ GalilScaffoldChainSweep.bounce center b xs
  have hw := candidate_word w lower center b xs hc hhead
  have hdrop : (w.drop 1).take (4*(xs.length+1)) = word := by
    have he := congrArg (List.drop 1) hw
    simpa [List.drop_take] using he
  have htake : (w.drop 1).take n = word.take n := by
    rw [← hdrop,List.take_take,Nat.min_eq_left hn]
  rw [htake]
  apply GalilScaffoldChainPrediction.unbroken_start _ (word.drop n)
  rw [← GalilScaffoldChainSweep.run_append,List.take_append_drop]
  exact (GalilScaffoldChainSweep.four_boundaries center b xs).2.2.2.2.2.2

#print axioms candidate_prefix_safe
#print axioms candidate_word
#print axioms palindrome_prefix
end PalPeg.GalilScaffoldChainPalindrome
