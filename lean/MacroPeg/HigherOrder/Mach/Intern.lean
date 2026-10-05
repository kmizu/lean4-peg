import MacroPeg.HigherOrder.Mach.Tok

/-!
# Registering an arrow on stacks

The arrows are on stack `tt` as pairs (`encPairs`, entry `0` at the bottom) with their number on `ntt`.
`internP` registers the pair `(a, b)` (the tops of `sa`, `sb`, kept) and pushes its number on `d` — exactly as
`intern`: the arrows are moved to the scratch stack `w` and back one pair at a time, each compared with `(a, b)`; the
first match is remembered on `fnd` (its index plus one); without a match the pair is appended.
-/

namespace Shallot.MacroPeg.Mach

open Complexity

variable {K : Nat}

/-- Move one pair back from `w` to `tt` and compare it with `(a, b)` (the tops of `sa`, `sb`); on a first match
(`fnd` still `0`) set `fnd` to the pair's index plus one; then count the index up. Scratch: `t u g` for the
comparisons, `f f2` for their results, `z` for doing nothing. -/
def internStep (tt w sa sb idx fnd t u g f f2 z : Fin K) (hw : w ≠ tt) (htt : tt ≠ t) (hsa : sa ≠ u) (hsb : sb ≠ u)
    (hif : idx ≠ fnd) : NProg K :=
  .seq (nmv w tt hw) (.seq (cmpTop tt sa t u g f htt hsa) (.seq (nmv w tt hw) (.seq (cmpTop tt sb t u g f2 htt hsb)
    -- each flag is `1` exactly on equality
    (.seq (.prim (.dec f)) (.seq (.prim (.dec f2))
      (.seq (.ite f .zero (.ite f2 .zero (.ite fnd .zero
          (.seq (.prim (.pop fnd)) (.seq (.prim (.dup idx fnd hif)) (.prim (.inc fnd)))) (nskip z)) (nskip z)) (nskip z))
        (.seq (.prim (.pop f)) (.seq (.prim (.pop f2)) (.prim (.inc idx))))))))))

/-- Register `(a, b)` and push its number on `d`. -/
def internP (tt ntt w sa sb d idx fnd t u g f f2 z : Fin K) (htw : tt ≠ w) (htt : tt ≠ t) (hsa : sa ≠ u)
    (hsb : sb ≠ u) (hif : idx ≠ fnd) (hfd : fnd ≠ d) (hsat : sa ≠ tt) (hsbt : sb ≠ tt) (hnd : ntt ≠ d) : NProg K :=
  .seq (nmvAll tt w htw) (.seq (.prim (.pushZ fnd)) (.seq (.prim (.pushZ idx))
    (.seq (.loop w .nonempty (internStep tt w sa sb idx fnd t u g f f2 z (Ne.symm htw) htt hsa hsb hif))
      (.seq (.prim (.pop idx))
        (.seq (.ite fnd .zero
            (.seq (.prim (.dup sa tt hsat)) (.seq (.prim (.dup sb tt hsbt)) (.seq (.prim (.inc ntt))
              (.prim (.dup ntt d hnd)))))
            (.prim (.dup fnd d hfd)))
          (.prim (.pop fnd)))))))

end Shallot.MacroPeg.Mach
