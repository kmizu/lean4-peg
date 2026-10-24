import Shallot.Peg.Separation.TokenInput
import Shallot.Peg.Separation.BitWord

namespace Shallot.PegSeparation

open Complexity Shallot.Packrat Shallot.Packrat.Machine Shallot.MacroPeg.KExp

/-- Load one original a/b character for each input bit. The existing token
emitter is used only with static complete token constants, not on the input. -/
def readLetter (g : Grammar) : NProg (NK g) :=
  .ite (inpR g) .zero
    (.seq (.prim (.pop (inpR g))) (readToken g 0 [false, true, false, true]))
    (.seq (.prim (.pop (inpR g))) (readToken g 0 [false, true, true, false]))

theorem readLetter_spec (g : Grammar) (S : Lists (NK g)) (b : Bool) (w : List Bool)
    (out : List Nat) (m : Nat) :
    NRuns (readLetter g) (tokenState g S (b :: w) out m)
      (tokenState g S w (out ++ [symbolCode (if b then 'b' else 'a')]) (m + 1)) 134 := by
  have hp : tokenState g S (b :: w) out m (inpR g) = (w.map bitElem).reverse ++ [bitElem b] := by
    rw [tokenState_input]; simp
  have hpop := nruns_pop (inpR g) (tokenState g S (b :: w) out m) hp
  have hstate : (tokenState g S (b :: w) out m).set (inpR g) (w.map bitElem).reverse =
      tokenState g S w out m := by
    simp only [tokenState]; lists_eq <;> simp_all [inpR, tmpR, lenR, Fin.mk.injEq]
  rw [hstate] at hpop
  cases b with
  | false =>
    have hr := readToken_spec g S 0 [false, true, false, true] w out m
    have hc : NTest.zero.eval (tokenState g S (false :: w) out m (inpR g)) = true := by
      rw [hp]; simp [bitElem]
    simpa [readLetter, bitsTokL, bitsTok, tokChar] using (hpop.seq hr).iteT (q := _) hc |>.mono (by omega)
  | true =>
    have hr := readToken_spec g S 0 [false, true, true, false] w out m
    have hc : NTest.zero.eval (tokenState g S (true :: w) out m (inpR g)) = false := by
      rw [hp]; simp [bitElem]
    simpa [readLetter, bitsTokL, bitsTok, tokChar] using (hpop.seq hr).iteF (p := _) hc |>.mono (by omega)

def letterLoop (g : Grammar) : NProg (NK g) := .loop (inpR g) .nonempty (readLetter g)

theorem letterLoop_spec (g : Grammar) (S : Lists (NK g)) (w : List Bool) (out : List Nat) (m : Nat) :
    NRuns (letterLoop g) (tokenState g S w out m)
      (tokenState g S [] (out ++ (bitWord w).map symbolCode) (m + w.length)) (135 * w.length + 1) := by
  induction w generalizing out m with
  | nil =>
    simpa only [letterLoop, bitWord, List.map_nil, List.append_nil, List.length_nil,
      Nat.add_zero, Nat.mul_zero, Nat.zero_add] using
        nruns_loop_exit (i := inpR g) (c := .nonempty) (p := readLetter g)
          (S := tokenState g S [] out m) (by rw [tokenState_input]; rfl)
  | cons b w ih =>
    have hc : NTest.nonempty.eval (tokenState g S (b :: w) out m (inpR g)) = true := by
      rw [tokenState_input]; exact eval_nonempty_ne (by simp)
    have hr := readLetter_spec g S b w out m
    have hi := ih (out ++ [symbolCode (if b then 'b' else 'a')]) (m + 1)
    have hh := loop_continue hc hr hi
    have hh' := hh.mono (T' := 135 * (b :: w).length + 1) (by simp only [List.length_cons, Nat.mul_add, Nat.mul_one]; omega)
    simpa only [letterLoop, bitWord, List.map_cons, List.singleton_append, List.append_assoc,
      List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh'

def loadLetters (g : Grammar) : NProg (NK g) :=
  .seq (.prim (.pushZ (lenR g))) (.seq (letterLoop g)
    (.seq (replaceRow (tmpR g) (inpR g) (workR g) (by packrat_regs) (by packrat_regs))
      (.prim (.pushZ (inpR g)))))

def letterLoaded (g : Grammar) (w : List Bool) : Lists (NK g) :=
  ((nInit (NK g) w).set (lenR g) [w.length]).set (inpR g) (inputRow (bitWord w))

theorem nruns_loadLetters (g : Grammar) (w : List Bool) :
    NRuns (loadLetters g) (nInit (NK g) w) (letterLoaded g w) (160 * (w.length + 1)) := by
  have hwi : workR g ≠ inpR g := by packrat_regs
  have hwt : workR g ≠ tmpR g := by packrat_regs
  have hwl : workR g ≠ lenR g := by packrat_regs
  have pz := nruns_pushZ (lenR g) (nInit (NK g) w)
  have hstart : (nInit (NK g) w).set (lenR g) (nInit (NK g) w (lenR g) ++ [0]) =
      tokenState g (nInit (NK g) w) w [] 0 := by
    simp only [tokenState]; lists_eq <;> simp_all [inpR, tmpR, lenR, nInit, Fin.mk.injEq]
  rw [hstart] at pz
  have lp := letterLoop_spec g (nInit (NK g) w) w [] 0
  simp only [List.nil_append, Nat.zero_add] at lp
  let S := tokenState g (nInit (NK g) w) [] ((bitWord w).map symbolCode) w.length
  have hw : S (workR g) = [] := by
    simp only [S, tokenState, Lists.set_ne _ _ hwl, Lists.set_ne _ _ hwt, Lists.set_ne _ _ hwi]
    simp [nInit, workR]
  have mv := nruns_replaceRow (tmpR g) (inpR g) (workR g) (by packrat_regs) (by packrat_regs)
    (by packrat_regs) S hw
  let S₁ := (S.set (inpR g) (S (tmpR g))).set (tmpR g) []
  have ez := nruns_pushZ (inpR g) S₁
  have hend : S₁.set (inpR g) (S₁ (inpR g) ++ [0]) = letterLoaded g w := by
    simp only [S₁, S, tokenState, letterLoaded, inputRow]
    lists_eq <;> simp_all [inpR, tmpR, lenR, nInit, Fin.mk.injEq]
  rw [hend] at ez
  have hlen : (S (tmpR g)).length = w.length := by dsimp only [S]; rw [tokenState_tmp]; simp [bitWord]
  have hzero : S (inpR g) = [] := by dsimp only [S]; rw [tokenState_input]; rfl
  refine (pz.seq (lp.seq (mv.seq ez))).mono ?_
  rw [hlen, hzero]
  simp only [List.length_nil]
  omega

end Shallot.PegSeparation
