import Shallot.Peg.Undecidable.MachCardsFront

/-!
# The cards stage

`cardsP` reads the bits (`parseP`: the bits on `sXB`, their number on `sNN`, the unary numbers `deUnary w` on
`LL`), turns the numbers over, checks the shape `1 :: nq :: na :: rest` with `rest` in whole chunks of three (moving
the rows onto `sRS`), and then writes the cards (`goodP`); any failure ends in `badP`.

* `cardsP_good`: on a good code, `cardsP` ends in `cardsSt (tablePCPN (table1 nq na rest) w)`;
* `cardsP_bad`: on any other input, it ends in `badSt`.
-/

namespace Shallot

open Complexity
open Complexity.Univ
open Complexity.Undec

namespace MC

def c3P : NProg UK :=
  .seq (.prim (.pushZ sDC)) (.seq (npushC sK2 2) (.seq (MacroPeg.KExp.chunkLoop sMM sRS sDC sK2 (by decide) (by decide))
    (.ite sDC .zero (.seq (.prim (.pop sDC)) (.seq (.prim (.pop sK2)) goodP)) badP)))

def c2P : NProg UK := .ite sMM .nonempty (.seq (nmv sMM sNA (by decide)) c3P) badP
def c1P : NProg UK := .ite sMM .nonempty (.seq (nmv sMM sNQ (by decide)) c2P) badP

/-- Check that the first number is `1`, then go on. -/
def chkP : NProg UK :=
  .ite sMM .pos (.seq (.prim (.dec sMM)) (.ite sMM .zero (.seq (.prim (.pop sMM)) c1P) badP)) badP

end MC

open MC in
/-- **The cards stage.** -/
def cardsP : NProg UK :=
  .seq MacroPeg.KExp.parseP (.seq (nmvAll MacroPeg.KExp.LL sMM (by decide)) chkP)

namespace MC

/-- The facts the good branch needs, kept by the checks. -/
structure Pre (S : Lists UK) (w : List Bool) : Prop where
  xb : S sXB = w.map bitElem
  nn : Top S sNN w.length
  tmp : S sTMP = []
  sc : S sSC = []
  out : S sOUT = []
  rs : S sRS = []
  dc : S sDC = []
  k2 : S sK2 = []

def preStacks : List (Fin UK) := [sXB, sNN, sTMP, sSC, sOUT, sRS, sDC, sK2]

theorem Pre.set {S : Lists UK} {w : List Bool} (h : Pre S w) (X : Fin UK) (hX : X ∉ preStacks) (v : List Nat) :
    Pre (S.set X v) w := by
  have hne : ∀ Y ∈ preStacks, Y ≠ X := fun Y hY e => hX (e ▸ hY)
  exact
    { xb := by rw [Lists.set_ne _ _ (hne sXB (by decide))]; exact h.xb
      nn := h.nn.set_ne (hne _ (by decide)) v
      tmp := by rw [Lists.set_ne _ _ (hne sTMP (by decide))]; exact h.tmp
      sc := by rw [Lists.set_ne _ _ (hne sSC (by decide))]; exact h.sc
      out := by rw [Lists.set_ne _ _ (hne sOUT (by decide))]; exact h.out
      rs := by rw [Lists.set_ne _ _ (hne sRS (by decide))]; exact h.rs
      dc := by rw [Lists.set_ne _ _ (hne sDC (by decide))]; exact h.dc
      k2 := by rw [Lists.set_ne _ _ (hne sK2 (by decide))]; exact h.k2 }

/-! ## The chunks of three -/

theorem c3P_runs {S : Lists UK} {w : List Bool} {nq na : Nat} {rest : List Nat} (h : Pre S w)
    (hNA : Top S sNA na) (hMM : S sMM = rest.reverse) :
    Reach c3P S (if rest.length % 3 = 0 then cardsSt (tablePCPN (table1 nq na rest) w) else badSt) := by
  have d₁ := reach_prim (.pushZ sDC) S
  simp only [NPrim.apply, h.dc, List.nil_append] at d₁
  have d₂ := Reach.of (nruns_pushC sK2 (S.set sDC [0]) 2)
  rw [Lists.set_ne _ _ (by decide), h.k2, List.nil_append] at d₂
  have d₃ := Reach.of (MacroPeg.KExp.nruns_chunkLoop sMM sRS sDC sK2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) ((S.set sDC [0]).set sK2 [2]) (l := rest.reverse) (lc := []) (lr := []) (R := 2)
    (by simp (config := { decide := true }) [Lists.set, hMM])
    (by simp (config := { decide := true }) [Lists.set, h.rs])
    (by simp (config := { decide := true }) [Lists.set]) (by simp (config := { decide := true }) [Lists.set]))
  rw [List.reverse_reverse, List.length_reverse, List.nil_append] at d₃
  let S₃ := ((((S.set sDC [0]).set sK2 [2]).set sMM []).set sRS rest).set sDC [MacroPeg.KExp.ccR 2 rest.length]
  have hDC : S₃ sDC = [] ++ [MacroPeg.KExp.ccR 2 rest.length] := Lists.set_same _ _ _
  refine d₁.seq (d₂.seq (d₃.seq ?_))
  by_cases h3 : rest.length % 3 = 0
  · rw [if_pos h3]
    have h0 : MacroPeg.KExp.ccR 2 rest.length = 0 := (MacroPeg.KExp.ccR_zero_iff _ _).2 h3
    rw [h0] at hDC
    refine Reach.iteT (by simp [NTest.eval, h0]) ?_
    have p₁ := Reach.of (nruns_pop sDC S₃ hDC)
    have p₂ := Reach.of (nruns_pop sK2 (S₃.set sDC []) (l := []) (v := 2)
      (by simp (config := { decide := true }) [S₃, Lists.set]))
    refine p₁.seq (p₂.seq ?_)
    obtain ⟨lNN, hNN⟩ := h.nn
    obtain ⟨lNA, hNA'⟩ := hNA
    exact goodP_reach _ w nq na rest h3
      (by simp (config := { decide := true }) [S₃, Lists.set, h.xb])
      ⟨lNN, by simp (config := { decide := true }) [S₃, Lists.set, hNN]⟩
      ⟨lNA, by simp (config := { decide := true }) [S₃, Lists.set, hNA']⟩
      (by simp (config := { decide := true }) [S₃, Lists.set])
      (by simp (config := { decide := true }) [S₃, Lists.set, h.tmp])
      (by simp (config := { decide := true }) [S₃, Lists.set, h.sc])
      (by simp (config := { decide := true }) [S₃, Lists.set, h.out])
  · rw [if_neg h3]
    have h0 : MacroPeg.KExp.ccR 2 rest.length ≠ 0 := fun e => h3 ((MacroPeg.KExp.ccR_zero_iff _ _).1 e)
    refine Reach.iteF (by simp [NTest.eval, h0]) (badP_reach _)

/-! ## The first three numbers -/

/-- Where `c1P` ends on the numbers `t` after the leading `1`. -/
def c1Out (w : List Bool) : List Nat → Lists UK
  | nq :: na :: rest => if rest.length % 3 = 0 then cardsSt (tablePCPN (table1 nq na rest) w) else badSt
  | _ => badSt

/-- Where `chkP` ends on the numbers `t`. -/
def chkOut (w : List Bool) : List Nat → Lists UK
  | 1 :: t => c1Out w t
  | _ => badSt

theorem c1P_runs {S : Lists UK} {w : List Bool} (h : Pre S w) :
    ∀ (t : List Nat), S sMM = t.reverse → Reach c1P S (c1Out w t)
  | [], hMM => Reach.iteF (by rw [hMM]; rfl) (badP_reach _)
  | [nq], hMM => by
    have hMM' : S sMM = [] ++ [nq] := by rw [hMM]; rfl
    refine Reach.iteT (by rw [hMM]; rfl) ((Reach.of (nruns_mv sMM sNQ (by decide) S hMM')).seq ?_)
    exact Reach.iteF (by simp (config := { decide := true }) [Lists.set]) (badP_reach _)
  | nq :: na :: rest, hMM => by
    have hMM' : S sMM = (rest.reverse ++ [na]) ++ [nq] := by rw [hMM]; simp
    refine Reach.iteT (eval_nonempty_ne (by rw [hMM']; simp)) ((Reach.of (nruns_mv sMM sNQ (by decide) S hMM')).seq ?_)
    let S₁ := (S.set sNQ (S sNQ ++ [nq])).set sMM (rest.reverse ++ [na])
    have h₁ : Pre S₁ w := (h.set sNQ (by decide) _).set sMM (by decide) _
    have hM₁ : S₁ sMM = rest.reverse ++ [na] := Lists.set_same _ _ _
    refine Reach.iteT (eval_nonempty_ne (by simp [S₁])) ((Reach.of (nruns_mv sMM sNA (by decide) S₁ hM₁)).seq ?_)
    have h₂ := (h₁.set sNA (by decide) (S₁ sNA ++ [na])).set sMM (by decide) rest.reverse
    have hc := c3P_runs (nq := nq) (na := na) h₂ ((Top.set_same S₁ sNA _ na).set_ne (by decide) _)
      (Lists.set_same _ _ _)
    simp only [c1Out]
    exact hc

theorem chkP_runs {S : Lists UK} {w : List Bool} (h : Pre S w) :
    ∀ (t : List Nat), S sMM = t.reverse → Reach chkP S (chkOut w t)
  | [], hMM => Reach.iteF (by rw [hMM]; rfl) (badP_reach _)
  | 0 :: t, hMM => Reach.iteF (by rw [hMM, List.reverse_cons, eval_pos_snoc]; rfl) (badP_reach _)
  | (k + 1) :: t, hMM => by
    have hMM' : S sMM = t.reverse ++ [k + 1] := by rw [hMM, List.reverse_cons]
    refine Reach.iteT (by rw [hMM', eval_pos_snoc]; simp) ((Reach.of (nruns_dec sMM S hMM')).seq ?_)
    simp only [Nat.add_sub_cancel]
    have h₁ : Pre (S.set sMM (t.reverse ++ [k])) w := h.set sMM (by decide) _
    cases k with
    | zero =>
      refine Reach.iteT (by rw [Lists.set_same, eval_zero_snoc]; rfl) ?_
      have p := Reach.of (nruns_pop sMM (S.set sMM (t.reverse ++ [0])) (Lists.set_same _ _ _))
      rw [Lists.set_set_u] at p
      exact p.seq (c1P_runs (h.set sMM (by decide) _) t (Lists.set_same _ _ _))
    | succ k =>
      refine Reach.iteF (by rw [Lists.set_same, eval_zero_snoc]; simp) ?_
      simp only [chkOut]
      exact badP_reach _

/-! ## Reading -/

/-- After reading and turning the numbers over. -/
def readSt (w : List Bool) : Lists UK :=
  ((MacroPeg.KExp.S1 w).set sMM ((MacroPeg.KExp.S1 w) sMM ++ ((MacroPeg.KExp.S1 w) MacroPeg.KExp.LL).reverse)).set
    MacroPeg.KExp.LL []

theorem read_reach (w : List Bool) : Reach (.seq MacroPeg.KExp.parseP (nmvAll MacroPeg.KExp.LL sMM (by decide)))
    (nInit UK w) (readSt w) :=
  (Reach.of (MacroPeg.KExp.nruns_parse w)).seq (Reach.of (nruns_mvAll _ _ _ _))

theorem readSt_pre (w : List Bool) : Pre (readSt w) w :=
  { xb := by simp (config := { decide := true }) [readSt, MacroPeg.KExp.S1, MacroPeg.KExp.E0, Lists.set]
    nn := ⟨[], by simp (config := { decide := true }) [readSt, MacroPeg.KExp.S1, MacroPeg.KExp.E0, Lists.set]⟩
    tmp := by simp (config := { decide := true }) [readSt, MacroPeg.KExp.S1, MacroPeg.KExp.E0, Lists.set]
    sc := by simp (config := { decide := true }) [readSt, MacroPeg.KExp.S1, MacroPeg.KExp.E0, Lists.set]
    out := by simp (config := { decide := true }) [readSt, MacroPeg.KExp.S1, MacroPeg.KExp.E0, Lists.set]
    rs := by simp (config := { decide := true }) [readSt, MacroPeg.KExp.S1, MacroPeg.KExp.E0, Lists.set]
    dc := by simp (config := { decide := true }) [readSt, MacroPeg.KExp.S1, MacroPeg.KExp.E0, Lists.set]
    k2 := by simp (config := { decide := true }) [readSt, MacroPeg.KExp.S1, MacroPeg.KExp.E0, Lists.set] }

theorem readSt_mm (w : List Bool) : readSt w sMM = (deUnary w).reverse := by
  simp (config := { decide := true }) [readSt, MacroPeg.KExp.S1, MacroPeg.KExp.E0, Lists.set]

theorem cardsP_runs (w : List Bool) : Reach cardsP (nInit UK w) (chkOut w (deUnary w)) := by
  have d₁ := read_reach w
  have d₂ := chkP_runs (readSt_pre w) (deUnary w) (readSt_mm w)
  obtain ⟨_, t₁, _, x₁⟩ := d₁
  obtain ⟨_, t₂, _, x₂⟩ := d₂
  cases x₁ with
  | seqC y₁ y₂ => exact ⟨_, _, Nat.le_refl _, .seqC y₁ (.seqC y₂ x₂)⟩

end MC

open MC in
/-- **On a good code, the cards stage ends with the cards of the instance.** -/
theorem cardsP_good {w : List Bool} {nq na : Nat} {rest : List Nat} (h : GoodCode w nq na rest) :
    ∃ c, NRuns cardsP (nInit Complexity.Univ.UK w) (cardsSt (tablePCPN (table1 nq na rest) w)) c := by
  have := cardsP_runs w
  rw [h.1] at this
  simp only [chkOut, c1Out, h.2, if_true] at this
  exact this

open MC in
/-- **On any other input, the cards stage ends with the flag `1` alone.** -/
theorem cardsP_bad {w : List Bool} (h : ∀ nq na rest, ¬ GoodCode w nq na rest) :
    ∃ c, NRuns cardsP (nInit Complexity.Univ.UK w) badSt c := by
  have hr := cardsP_runs w
  suffices e : chkOut w (deUnary w) = badSt by rw [e] at hr; exact hr
  match hd : deUnary w with
  | 1 :: nq :: na :: rest =>
    have h3 : ¬ rest.length % 3 = 0 := fun h3 => h nq na rest ⟨hd, h3⟩
    simp [chkOut, c1Out, h3]
  | [] => rfl
  | [1] => rfl
  | [1, _] => rfl
  | 0 :: _ => rfl
  | (k + 2) :: _ => rfl

end Shallot
