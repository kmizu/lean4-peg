import Shallot.Peg.Undecidable.MachCardsEmit

/-!
# Around the writing: clearing, the bound, the end

* `clearL is` empties the stacks `is` (`reach_clearL`); `badP` leaves the flag `1` alone (`badP_reach`), `cleanP`
  keeps the cards and adds the flag `0` (`cleanP_reach`);
* `sumP` counts the numbers of the rows and adds them to `3` (`sumP_reach`);
* `goodP` runs from the rows in place to `cardsSt` (`goodP_reach`).
-/

namespace Shallot

open Complexity
open Complexity.Univ
open Complexity.Undec

namespace MC

/-! ## Clearing -/

def clearL : List (Fin UK) → NProg UK
  | [] => nskip sSC
  | i :: is => .seq (nclr i) (clearL is)

theorem reach_clearL : ∀ (is : List (Fin UK)) (S : Lists UK),
    Reach (clearL is) S (fun x => if x ∈ is then [] else S x)
  | [], S => (reach_skip _ S).cast (funext fun x => by simp)
  | i :: is, S => by
    refine ((Reach.of (nruns_clr i S)).seq (reach_clearL is _)).cast ?_
    funext x
    by_cases hx : x = i
    · subst hx; simp
    · simp [Lists.set, hx]

/-- Clear everything and leave the flag `1`. -/
def badP : NProg UK := .seq (clearL (List.finRange UK)) (.seq (.prim (.pushZ sT1)) (.prim (.inc sT1)))

theorem badP_reach (S : Lists UK) : Reach badP S badSt := by
  refine ((reach_clearL _ S).seq ((reach_prim _ _).seq (reach_prim _ _))).cast ?_
  funext x
  simp only [NPrim.apply, Lists.set, List.mem_finRange, if_true, badSt]
  by_cases hx : x.val = 1
  · have : x = sT1 := Fin.ext hx
    subst this; simp [mapTop]
  · have : x ≠ sT1 := fun e => hx (by rw [e]; rfl)
    simp [this, hx]

/-- The stacks other than the cards. -/
def others : List (Fin UK) := (List.finRange UK).filter fun x => decide (x ≠ sOUT)

/-- Clear everything but the cards and leave the flag `0`. -/
def cleanP : NProg UK := .seq (clearL others) (.prim (.pushZ sT1))

theorem cleanP_reach (S : Lists UK) (N : List Card) (h : S sOUT = encCards N) : Reach cleanP S (cardsSt N) := by
  refine ((reach_clearL _ S).seq (reach_prim _ _)).cast ?_
  funext x
  simp only [NPrim.apply, Lists.set, others, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
    cardsSt]
  by_cases h0 : x.val = 0
  · have : x = sOUT := Fin.ext h0
    subst this; simp (config := { decide := true }) [h]
  · have hx0 : x ≠ sOUT := fun e => h0 (by rw [e]; rfl)
    by_cases h1 : x.val = 1
    · have : x = sT1 := Fin.ext h1
      subst this; simp (config := { decide := true })
    · have hx1 : x ≠ sT1 := fun e => h1 (by rw [e]; rfl)
      simp [hx0, hx1, h0, h1]

/-! ## The bound -/

def sumBody : NProg UK := .seq (nmv sRS sTMP (by decide)) (.seq (.prim (.inc sLN)) (addVar sTMP sSC sB))

/-- Count the numbers on `sRS` onto `sLN` and add them to `3` onto `sB`. -/
def sumP : NProg UK :=
  .seq (.prim (.pushZ sLN)) (.seq (npushC sB 3) (.seq (.loop sRS .nonempty sumBody) (nmvAll sTMP sRS (by decide))))

theorem sumP_reach (S : Lists UK) (rest : List Nat) (hRS : S sRS = rest) (hT : S sTMP = []) (hSC : S sSC = []) :
    Reach sumP S ((S.set sLN (S sLN ++ [rest.length])).set sB (S sB ++ [3 + rest.sum])) := by
  let r := rest.length
  let F : Nat → Lists UK := fun j =>
    (((S.set sRS (rest.take (r - j))).set sTMP (rest.drop (r - j)).reverse).set sLN (S sLN ++ [j])).set sB
      (S sB ++ [3 + (rest.drop (r - j)).sum])
  have d₁ := reach_prim (.pushZ sLN) S
  have d₂ := Reach.of (nruns_pushC sB (S.set sLN (S sLN ++ [0])) 3)
  have e₀ : (S.set sLN (S sLN ++ [0])).set sB ((S.set sLN (S sLN ++ [0])) sB ++ [3]) = F 0 := by
    simp only [F, Nat.sub_zero, List.take_length, List.drop_length, List.reverse_nil, List.sum_nil, Nat.add_zero, r]
    rw [← hRS, ← hT, Lists.set_get_self, Lists.set_get_self, Lists.set_ne _ _ (by decide)]
  rw [e₀] at d₂
  have hFRS : ∀ j, F j sRS = rest.take (r - j) := fun j => by simp (config := { decide := true }) [F, Lists.set]
  have hl := reach_family (i := sRS) (c := .nonempty) (p := sumBody) F r
    (fun m hm => by
      rw [hFRS]
      exact eval_nonempty_ne (List.ne_nil_of_length_pos (by simp only [List.length_take, r]; omega)))
    (by rw [hFRS, Nat.sub_self]; rfl)
    (fun m hm => by
      obtain ⟨k, hk⟩ : ∃ k, r - m = k + 1 := ⟨r - m - 1, by omega⟩
      have hkl : k < rest.length := by omega
      have ht : rest.take (k + 1) = rest.take k ++ [rest[k]] := List.take_succ_eq_append_getElem hkl
      have hd : rest.drop k = rest[k] :: rest.drop (k + 1) := List.drop_eq_getElem_cons hkl
      have b₁ := Reach.of (nruns_mv sRS sTMP (by decide) (F m) (l := rest.take k) (v := rest[k])
        (by rw [hFRS, hk, ht]))
      have b₂ := Reach.of (nruns_inc sLN (((F m).set sTMP (F m sTMP ++ [rest[k]])).set sRS (rest.take k))
        (l := S sLN) (v := m) (by simp (config := { decide := true }) [F, Lists.set]))
      have b₃ := reach_addVar (v := sTMP) (s := sSC) (t := sB) (by decide) (by decide) (by decide)
        ((((F m).set sTMP (F m sTMP ++ [rest[k]])).set sRS (rest.take k)).set sLN (S sLN ++ [m + 1]))
        (by simp (config := { decide := true }) [F, Lists.set, hSC]) (l := S sB)
        (b := 3 + (rest.drop (k + 1)).sum) (by simp (config := { decide := true }) [F, Lists.set, hk])
      refine (b₁.seq (b₂.seq b₃)).cast ?_
      have htv : tv ((((F m).set sTMP (F m sTMP ++ [rest[k]])).set sRS (rest.take k)).set sLN (S sLN ++ [m + 1]))
          sTMP = rest[k] := by simp (config := { decide := true }) [tv, Lists.set]
      rw [htv]
      have hm1 : r - (m + 1) = k := by omega
      have hFTMP : F m sTMP = (rest.drop (k + 1)).reverse := by
        simp (config := { decide := true }) [F, Lists.set, hk]
      rw [hFTMP]
      have eF : F (m + 1) = (((S.set sRS (rest.take k)).set sTMP ((rest.drop (k + 1)).reverse ++ [rest[k]])).set sLN
          (S sLN ++ [m + 1])).set sB (S sB ++ [3 + (rest.drop (k + 1)).sum + rest[k]]) := by
        simp only [F, hm1, hd, List.reverse_cons, List.sum_cons]
        congr 3; omega
      rw [eF]
      funext y
      simp only [F, Lists.set]
      by_cases h1 : y = sB
      · subst h1; simp (config := { decide := true })
      · by_cases h2 : y = sLN
        · subst h2; simp (config := { decide := true })
        · by_cases h3 : y = sRS
          · subst h3; simp (config := { decide := true })
          · by_cases h4 : y = sTMP
            · subst h4; simp (config := { decide := true })
            · simp [h1, h2, h3, h4])
  have hFr : F r = (((S.set sRS []).set sTMP rest.reverse).set sLN (S sLN ++ [r])).set sB (S sB ++ [3 + rest.sum]) := by
    simp [F]
  rw [hFr] at hl
  have d₄ := Reach.of (nruns_mvAll sTMP sRS (by decide)
    ((((S.set sRS []).set sTMP rest.reverse).set sLN (S sLN ++ [r])).set sB (S sB ++ [3 + rest.sum])))
  refine (d₁.seq (d₂.seq (hl.seq d₄))).cast ?_
  funext y
  simp only [Lists.set]
  by_cases h1 : y = sB
  · subst h1; simp (config := { decide := true })
  · by_cases h2 : y = sLN
    · subst h2; simp (config := { decide := true }) [r]
    · by_cases h3 : y = sRS
      · subst h3; simp (config := { decide := true }) [hRS]
      · by_cases h4 : y = sTMP
        · subst h4; simp (config := { decide := true }) [hT]
        · simp [h1, h2, h3, h4]

/-! ## From the rows in place to the cards -/

def goodP : NProg UK :=
  .seq sumP (.seq (pushE sN sSC ⟨[sB, sB], 2⟩) (.seq (pushE sM sSC ⟨[sB, sB], 4⟩)
    (.seq (pushE sNA3 sSC ⟨[sNA, sNA, sNA], 0⟩) (.seq emitP cleanP))))

/-- **The good branch**: with the bits on `sXB`, their number on `sNN`, `na` on `sNA` and the rows on `sRS`, the
program ends with the cards. -/
theorem goodP_reach (S : Lists UK) (w : List Bool) (nq na : Nat) (rest : List Nat) (h3 : rest.length % 3 = 0)
    (hXB : S sXB = w.map bitElem) (hNN : Top S sNN w.length) (hNA : Top S sNA na) (hRS : S sRS = rest)
    (hTMP : S sTMP = []) (hSC : S sSC = []) (hOUT : S sOUT = []) :
    Reach goodP S (cardsSt (tablePCPN (table1 nq na rest) w)) := by
  have hb : 3 + rest.sum = bnd (table1 nq na rest) := (bnd_table1 nq na rest).symm
  obtain ⟨lNN, hNN'⟩ := hNN
  obtain ⟨lNA, hNA'⟩ := hNA
  have d₁ := sumP_reach S rest hRS hTMP hSC
  rw [hb] at d₁
  let b := bnd (table1 nq na rest)
  let S₄ := (S.set sLN (S sLN ++ [rest.length])).set sB (S sB ++ [b])
  have d₂ := pushE_pushes (t := sN) (s := sSC) (e := ⟨[sB, sB], 2⟩) (by decide) (by decide) (by decide) S₄
    (by simp (config := { decide := true }) [S₄, Lists.set, hSC])
  rw [show LinE.ev S₄ ⟨[sB, sB], 2⟩ = 2 * b + 2 by
    simp (config := { decide := true }) [S₄, LinE.ev, tv, Lists.set]; omega] at d₂
  let S₅ := S₄.set sN (S₄ sN ++ [2 * b + 2])
  have d₃ := pushE_pushes (t := sM) (s := sSC) (e := ⟨[sB, sB], 4⟩) (by decide) (by decide) (by decide) S₅
    (by simp (config := { decide := true }) [S₅, S₄, Lists.set, hSC])
  rw [show LinE.ev S₅ ⟨[sB, sB], 4⟩ = 2 * b + 4 by
    simp (config := { decide := true }) [S₅, S₄, LinE.ev, tv, Lists.set]; omega] at d₃
  let S₆ := S₅.set sM (S₅ sM ++ [2 * b + 4])
  have d₄ := pushE_pushes (t := sNA3) (s := sSC) (e := ⟨[sNA, sNA, sNA], 0⟩) (by decide) (by decide) (by decide) S₆
    (by simp (config := { decide := true }) [S₆, S₅, S₄, Lists.set, hSC])
  rw [show LinE.ev S₆ ⟨[sNA, sNA, sNA], 0⟩ = 3 * na by
    simp (config := { decide := true }) [S₆, S₅, S₄, LinE.ev, tv, Lists.set, hNA']; omega] at d₄
  let S₇ := S₆.set sNA3 (S₆ sNA3 ++ [3 * na])
  have hBE : BE S₇ (w.map bitElem) rest w.length rest.length b (2 * b + 2) (2 * b + 4) (3 * na) :=
    { xb := by simp (config := { decide := true }) [S₇, S₆, S₅, S₄, Lists.set, hXB]
      nn := ⟨lNN, by simp (config := { decide := true }) [S₇, S₆, S₅, S₄, Lists.set, hNN']⟩
      rs := by simp (config := { decide := true }) [S₇, S₆, S₅, S₄, Lists.set, hRS]
      ln := ⟨S sLN, by simp (config := { decide := true }) [S₇, S₆, S₅, S₄, Lists.set]⟩
      bb := ⟨S sB, by simp (config := { decide := true }) [S₇, S₆, S₅, S₄, Lists.set]⟩
      nN := ⟨S sN, by simp (config := { decide := true }) [S₇, S₆, S₅, S₄, Lists.set]⟩
      mm := ⟨S sM, by simp (config := { decide := true }) [S₇, S₆, S₅, S₄, Lists.set]⟩
      na := ⟨S sNA3, by simp (config := { decide := true }) [S₇, S₆, S₅, S₄, Lists.set]⟩
      sc := by simp (config := { decide := true }) [S₇, S₆, S₅, S₄, Lists.set, hSC]
      tmp := by simp (config := { decide := true }) [S₇, S₆, S₅, S₄, Lists.set, hTMP] }
  have d₅ := emitP_pushes (w := w) h3 hBE
  have hO : S₇ sOUT = [] := by simp (config := { decide := true }) [S₇, S₆, S₅, S₄, Lists.set, hOUT]
  have d₆ := cleanP_reach (S₇.set sOUT (S₇ sOUT ++ encCards (tablePCPN (table1 nq na rest) w)))
    (tablePCPN (table1 nq na rest) w) (by rw [Lists.set_same, hO, List.nil_append])
  exact d₁.seq (d₂.seq (d₃.seq (d₄.seq (d₅.seq d₆))))

end MC

end Shallot
