import PalPeg.GalilScaffoldChainPalindrome
import PalPeg.Manacher

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainMirror

def leftReads (word : List (Fin 3)) (center n : ℕ) : List (Option (Fin 3)) :=
  (List.range n).map (fun i => word[center-(i+1)]?)

def rightReads (word : List (Fin 3)) (center n : ℕ) : List (Option (Fin 3)) :=
  (List.range n).map (fun i => word[center+(i+1)]?)

/-- Existing centered-palindrome semantics give equality of the two
read orders on the same input, up to the already known radius. -/
theorem mirror_reads (word : List (Fin 3)) (center radius n : ℕ)
    (hp : Manacher.PalAt word center radius) (hn : n ≤ radius) :
    leftReads word center n = rightReads word center n := by
  apply List.map_congr_left
  intro i hi
  have hn' := List.mem_range.mp hi
  exact hp.2.2 (i+1) (by omega)

/-- Transfer the DP's known prediction to a legal right-verifier trace
inside the established palindrome. Layout equalities are explicit and
refer to the same word/center, rather than two unrelated input streams. -/
theorem mirrored_candidate_safe (word w : List (Fin 3)) (center radius n lower : ℕ)
    (c b : Fin 3) (xs actual : List (Fin 3))
    (hp : Manacher.PalAt word center radius) (hn : n ≤ radius)
    (hsize : n ≤ 4*(xs.length+1))
    (hc : GalilDpCorrect.Candidate w lower (xs.length+1))
    (hhead : w.take (xs.length+2) = c :: (xs ++ [b]))
    (hleft : ((w.drop 1).take n).map some = leftReads word center n)
    (hright : actual.map some = rightReads word center n)
    (p q : GalilScaffoldInputHead.PlaceHead)
    (hr : GalilScaffoldChainVerifyRun.Reads p actual q) :
    ∃ t, GalilScaffoldChainVerifyRun.Run ⟨p,GalilScaffoldChainConsume.ready c xs b⟩ n t ∧
      t.verifier = q ∧ t.control.broken = false := by
  have hm := mirror_reads word center radius n hp hn
  have he : actual.map some = ((w.drop 1).take n).map some := by
    rw [hright,hleft,hm]
  have hx : actual = (w.drop 1).take n := by
    have hh := congrArg (List.map (fun a : Option (Fin 3) => a.getD 0)) he
    simpa using hh
  have hlen : actual.length = n := by
    have hl := congrArg List.length hright
    simpa [rightReads] using hl
  have hrun := GalilScaffoldChainVerifyRun.realize hr (GalilScaffoldChainConsume.ready c xs b)
  rw [hlen] at hrun
  refine ⟨_,hrun,rfl,?_⟩
  rw [hx]
  exact GalilScaffoldChainPalindrome.candidate_prefix_safe w lower c b xs hc hhead n hsize

#print axioms mirrored_candidate_safe
#print axioms mirror_reads
end PalPeg.GalilScaffoldChainMirror
