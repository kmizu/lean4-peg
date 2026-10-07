import Shallot.Peg.Undecidable.MachCardsEnv

/-!
# The rule cards of one state and one symbol

`cellP` writes the starred cards of `rulesQA T q a` for the table of whole chunks, `q` on top of `sQ` and `a` on
top of `sA` (`cellP_pushes`): nothing for the halted states `0` and `1`; otherwise it looks the row number
`q·na + a` up among the rows (entry `3(q·na + a)` of the numbers of the rows), and writes the cards of its move
(`moveP_pushes`).
-/

namespace Shallot

open Complexity
open Complexity.Univ
open Complexity.Undec

namespace MC

/-! ## Writing one card -/

theorem pushEs_card {S : Lists UK} {bits rest : List Nat} {nw L b n m na3 : Nat} (h : BE S bits rest nw L b n m na3)
    {ls rs : List (LinE UK)} (h₁ : AllAvoid (scE sM ls rs) sSC) (h₂ : AllAvoid (scE sM ls rs) sOUT) {c : Card}
    (hc : (ls.map (LinE.ev S), rs.map (LinE.ev S)) = c) :
    Pushes sOUT (pushEs sOUT sSC (scE sM ls rs)) S (encSC m c) :=
  (pushEs_pushes (by decide) _ h₁ h₂ S h.sc).cast (by rw [scE_ev, h.mm.tv, hc])

/-! ## The cards of a move -/

/-- Left: the left end, then every symbol `c`. -/
def cardL0 : List (LinE UK) := scE sM [⟨[sB], 0⟩, ⟨[sB, sQ], 2⟩, ⟨[sA], 0⟩] [⟨[sB], 0⟩, ⟨[sB, sQP], 2⟩, ⟨[sWR], 0⟩]
def cardLc : List (LinE UK) := scE sM [⟨[sC], 0⟩, ⟨[sB, sQ], 2⟩, ⟨[sA], 0⟩] [⟨[sB, sQP], 2⟩, ⟨[sC], 0⟩, ⟨[sWR], 0⟩]
/-- Stay. -/
def cardS : List (LinE UK) := scE sM [⟨[sB, sQ], 2⟩, ⟨[sA], 0⟩] [⟨[sB, sQP], 2⟩, ⟨[sWR], 0⟩]
/-- Right. -/
def cardR : List (LinE UK) := scE sM [⟨[sB, sQ], 2⟩, ⟨[sA], 0⟩] [⟨[sWR], 0⟩, ⟨[sB, sQP], 2⟩]

def leftP : NProg UK := .seq (pushEs sOUT sSC cardL0) (forP sC sRC sSC ⟨[sB], 0⟩ (pushEs sOUT sSC cardLc))

/-- The cards of the move with code on top of `sMV`. -/
def moveP : NProg UK :=
  .ite sMV .zero leftP
    (letP sT2 (predE sT2 sSC ⟨[sMV], 0⟩) (.ite sT2 .zero (pushEs sOUT sSC cardS) (pushEs sOUT sSC cardR)))

/-- What `moveP` writes for the new state `x`, the written symbol `y` and the move code `z`. -/
def movOut (b m q a x y z : Nat) : List Nat :=
  if z = 0 then
    encSC m ([b, b + 2 + q, a], [b, b + 2 + x, y]) ++
      (List.range b).flatMap (fun c => encSC m ([c, b + 2 + q, a], [b + 2 + x, c, y]))
  else if z = 1 then encSC m ([b + 2 + q, a], [b + 2 + x, y])
  else encSC m ([b + 2 + q, a], [y, b + 2 + x])

theorem leftP_pushes {S : Lists UK} {bits rest : List Nat} {nw L b n m na3 q a x y : Nat}
    (h : BE S bits rest nw L b n m na3) (hq : Top S sQ q) (ha : Top S sA a) (hx : Top S sQP x) (hy : Top S sWR y) :
    Pushes sOUT leftP S (encSC m ([b, b + 2 + q, a], [b, b + 2 + x, y]) ++
      (List.range b).flatMap (fun c => encSC m ([c, b + 2 + q, a], [b + 2 + x, c, y]))) := by
  have d₁ := pushEs_card h (ls := [⟨[sB], 0⟩, ⟨[sB, sQ], 2⟩, ⟨[sA], 0⟩]) (rs := [⟨[sB], 0⟩, ⟨[sB, sQP], 2⟩, ⟨[sWR], 0⟩])
    (by decide) (by decide) (c := ([b, b + 2 + q, a], [b, b + 2 + x, y]))
    (by tvsimp [h.bb.getD, hq.getD, ha.getD, hx.getD, hy.getD] <;> omega)
  refine pushes_seq d₁ ?_
  let S₁ := S.set sOUT (S sOUT ++ encSC m ([b, b + 2 + q, a], [b, b + 2 + x, y]))
  have h₁ : BE S₁ bits rest nw L b n m na3 := h.set sOUT (by decide) _
  have hlim : LinE.ev S₁ ⟨[sB], 0⟩ = b := by tvsimp [S₁, h.bb.getD]
  have d₂ := forP_pushes (t := sOUT) (X := sC) (Y := sRC) (s := sSC) (lim := ⟨[sB], 0⟩)
    (body := pushEs sOUT sSC cardLc) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) S₁ h₁.sc (fun c => encSC m ([c, b + 2 + q, a], [b + 2 + x, c, y]))
    (fun j _ o => by
      have h₂ : BE (((S₁.set sOUT o).set sC (S₁ sC ++ [j])).set sRC (S₁ sRC ++ [LinE.ev S₁ ⟨[sB], 0⟩ - j]))
          bits rest nw L b n m na3 := ((h₁.set sOUT (by decide) _).set sC (by decide) _).set sRC (by decide) _
      exact pushEs_card h₂ (by decide) (by decide) (by tvsimp [S₁, h.bb.getD, hq.getD, ha.getD, hx.getD, hy.getD] <;> omega))
  rw [hlim] at d₂
  exact d₂

theorem moveP_pushes {S : Lists UK} {bits rest : List Nat} {nw L b n m na3 q a x y z : Nat}
    (h : BE S bits rest nw L b n m na3) (hq : Top S sQ q) (ha : Top S sA a) (hx : Top S sQP x) (hy : Top S sWR y)
    (hz : Top S sMV z) : Pushes sOUT moveP S (movOut b m q a x y z) := by
  obtain ⟨lz, hz'⟩ := hz
  unfold moveP movOut
  by_cases z0 : z = 0
  · rw [if_pos z0]
    exact Pushes.iteT (by rw [hz', eval_zero_snoc, z0]; rfl) (leftP_pushes h hq ha hx hy)
  · rw [if_neg z0]
    refine Pushes.iteF (by rw [hz', eval_zero_snoc]; simp [z0]) ?_
    have d₁ := predE_pushes (t := sT2) (s := sSC) (e := ⟨[sMV], 0⟩) (by decide) (by decide) (by decide) S h.sc
    have hv : LinE.ev S ⟨[sMV], 0⟩ = z := by tvsimp [hz']
    rw [hv] at d₁
    refine letP_pushes (by decide) d₁ ?_
    let S₁ := S.set sT2 (S sT2 ++ [z - 1])
    have h₁ : BE S₁ bits rest nw L b n m na3 := h.set sT2 (by decide) _
    by_cases z1 : z = 1
    · rw [if_pos z1]
      refine Pushes.iteT (by simp only [Lists.set_same, eval_zero_snoc, z1]; rfl) ?_
      exact pushEs_card h₁ (by decide) (by decide) (by tvsimp [S₁, h.bb.getD, hq.getD, ha.getD, hx.getD, hy.getD] <;> omega)
    · rw [if_neg z1]
      refine Pushes.iteF (by simp only [Lists.set_same, eval_zero_snoc]; simp; omega) ?_
      exact pushEs_card h₁ (by decide) (by decide) (by tvsimp [S₁, h.bb.getD, hq.getD, ha.getD, hx.getD, hy.getD] <;> omega)

/-! ## The row of `q` and `a` -/

/-- `3 a + q · 3na` onto `sI3`. -/
def idxP : NProg UK :=
  .seq (pushE sI3 sSC ⟨[sA, sA, sA], 0⟩) (.seq (.prim (.dup sQ sU (by decide)))
    (MacroPeg.KExp.mulAcc sU sNA3 sSC sI3 (by decide)))

theorem idxP_pushes {S : Lists UK} {bits rest : List Nat} {nw L b n m na3 q a : Nat}
    (h : BE S bits rest nw L b n m na3) (hq : Top S sQ q) (ha : Top S sA a) :
    Pushes sI3 idxP S [a + a + a + q * na3] := by
  have d₁ := pushE_pushes (t := sI3) (s := sSC) (e := ⟨[sA, sA, sA], 0⟩) (by decide) (by decide) (by decide) S h.sc
  have hv : LinE.ev S ⟨[sA, sA, sA], 0⟩ = a + a + a := by tvsimp [ha.getD]; omega
  rw [hv] at d₁
  obtain ⟨lq, hq'⟩ := hq
  have d₂ := Reach.of (nruns_dup sQ sU (by decide) (S.set sI3 (S sI3 ++ [a + a + a])) (l := lq) (v := q)
    (by rw [Lists.set_ne _ _ (by decide), hq']))
  obtain ⟨lna, hna⟩ := (h.na.set_ne (show sNA3 ≠ sI3 by decide) (S sI3 ++ [a + a + a])).set_ne
    (show sNA3 ≠ sU by decide) ((S.set sI3 (S sI3 ++ [a + a + a])) sU ++ [q])
  have d₃ := Reach.of (MacroPeg.KExp.nruns_mulAcc sU sNA3 sSC sI3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) ((S.set sI3 (S sI3 ++ [a + a + a])).set sU ((S.set sI3 (S sI3 ++ [a + a + a])) sU ++ [q]))
    (la := (S.set sI3 (S sI3 ++ [a + a + a])) sU) (x := q) (lr := S sI3) (z := a + a + a) (by rw [Lists.set_same])
    hna (by rw [Lists.set_ne _ _ (by decide), Lists.set_same]))
  refine (d₁.seq (d₂.seq d₃)).cast ?_
  rw [Lists.set_set_u, Lists.set_get_self, Lists.set_set_u]

/-- The cards of the row of `q` and `a`, if it exists. -/
def haveP : NProg UK :=
  letP sQP (peekE sRS sTMP sCC sQP sSC (by decide) (by decide) ⟨[sI3], 0⟩)
    (letP sWR (peekE sRS sTMP sCC sWR sSC (by decide) (by decide) ⟨[sI3], 1⟩)
      (letP sMV (peekE sRS sTMP sCC sMV sSC (by decide) (by decide) ⟨[sI3], 2⟩) moveP))

theorem haveP_pushes {S : Lists UK} {bits rest : List Nat} {nw L b n m na3 q a i : Nat}
    (h : BE S bits rest nw L b n m na3) (hq : Top S sQ q) (ha : Top S sA a) (hi : Top S sI3 i)
    (hlt : i + 2 < rest.length) :
    Pushes sOUT haveP S (movOut b m q a (rest.getD i 0) (rest.getD (i + 1) 0) (rest.getD (i + 2) 0)) := by
  have hiv : ∀ (S' : Lists UK), Top S' sI3 i → ∀ c, LinE.ev S' ⟨[sI3], c⟩ = i + c := fun S' h' c => by
    simp [LinE.ev, h'.tv]
  have d₁ := peekE_pushes (tab := sRS) (tmp := sTMP) (cc := sCC) (o := sQP) (s := sSC) (e := ⟨[sI3], 0⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) S h.sc h.tmp
    (by rw [hiv S hi, h.rs]; omega)
  rw [hiv S hi, h.rs] at d₁
  refine letP_pushes (by decide) d₁ ?_
  let S₁ := S.set sQP (S sQP ++ [rest.getD (i + 0) 0])
  have h₁ : BE S₁ bits rest nw L b n m na3 := h.set sQP (by decide) _
  have hi₁ : Top S₁ sI3 i := hi.set_ne (by decide) _
  have d₂ := peekE_pushes (tab := sRS) (tmp := sTMP) (cc := sCC) (o := sWR) (s := sSC) (e := ⟨[sI3], 1⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) S₁ h₁.sc h₁.tmp
    (by rw [hiv S₁ hi₁, h₁.rs]; omega)
  rw [hiv S₁ hi₁, h₁.rs] at d₂
  refine letP_pushes (by decide) d₂ ?_
  let S₂ := S₁.set sWR (S₁ sWR ++ [rest.getD (i + 1) 0])
  have h₂ : BE S₂ bits rest nw L b n m na3 := h₁.set sWR (by decide) _
  have hi₂ : Top S₂ sI3 i := hi₁.set_ne (by decide) _
  have d₃ := peekE_pushes (tab := sRS) (tmp := sTMP) (cc := sCC) (o := sMV) (s := sSC) (e := ⟨[sI3], 2⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) S₂ h₂.sc h₂.tmp
    (by rw [hiv S₂ hi₂, h₂.rs]; omega)
  rw [hiv S₂ hi₂, h₂.rs] at d₃
  refine letP_pushes (by decide) d₃ ?_
  let S₃ := S₂.set sMV (S₂ sMV ++ [rest.getD (i + 2) 0])
  have h₃ : BE S₃ bits rest nw L b n m na3 := h₂.set sMV (by decide) _
  have := moveP_pushes h₃ (q := q) (a := a) (x := rest.getD (i + 0) 0) (y := rest.getD (i + 1) 0)
    (z := rest.getD (i + 2) 0)
    (((hq.set_ne (by decide) _).set_ne (by decide) _).set_ne (by decide) _)
    (((ha.set_ne (by decide) _).set_ne (by decide) _).set_ne (by decide) _)
    (((Top.set_same S sQP _ _).set_ne (by decide) _).set_ne (by decide) _)
    ((Top.set_same S₁ sWR _ _).set_ne (by decide) _)
    (Top.set_same S₂ sMV _ _)
  rw [Nat.add_zero] at this
  exact this

/-- The row of `q` and `a`. -/
def rowP : NProg UK :=
  letP sI3 idxP (letP sF (cmpTop sI3 sLN sCT sCU sCG sF (by decide) (by decide)) (.ite sF .zero haveP (nskip sSC)))

theorem rowP_pushes {S : Lists UK} {bits rest : List Nat} {nw L b n m na3 q a na : Nat}
    (h : BE S bits rest nw L b n m na3) (hq : Top S sQ q) (ha : Top S sA a) (hL : L = rest.length)
    (h3 : rest.length % 3 = 0) (hna : na3 = 3 * na) :
    Pushes sOUT rowP S (if 3 * (q * na + a) < rest.length then
      movOut b m q a (rest.getD (3 * (q * na + a)) 0) (rest.getD (3 * (q * na + a) + 1) 0)
        (rest.getD (3 * (q * na + a) + 2) 0) else []) := by
  have hi : a + a + a + q * na3 = 3 * (q * na + a) := by
    rw [hna, Nat.mul_left_comm, Nat.mul_add]; omega
  have d₁ := idxP_pushes h hq ha
  rw [hi] at d₁
  refine letP_pushes (by decide) d₁ ?_
  let i := 3 * (q * na + a)
  let S₁ := S.set sI3 (S sI3 ++ [i])
  have h₁ : BE S₁ bits rest nw L b n m na3 := h.set sI3 (by decide) _
  obtain ⟨ll, hll⟩ := h₁.ln
  have d₂ : Pushes sF (cmpTop sI3 sLN sCT sCU sCG sF (by decide) (by decide)) S₁ [cmpRes i L] :=
    Reach.of (nruns_cmpTop sI3 sLN sCT sCU sCG sF (by decide) (by decide) (by decide) S₁ (li := S sI3) (a := i)
      (by simp only [S₁, Lists.set_same]) hll)
  refine letP_pushes (by decide) d₂ ?_
  let S₂ := S₁.set sF (S₁ sF ++ [cmpRes i L])
  have h₂ : BE S₂ bits rest nw L b n m na3 := h₁.set sF (by decide) _
  have hF : NTest.zero.eval (S₂ sF) = decide (cmpRes i L = 0) := by
    simp only [S₂, Lists.set_same, eval_zero_snoc]
  by_cases hlt : i < rest.length
  · rw [if_pos hlt]
    have hc : cmpRes i L = 0 := by simp [cmpRes, hL, hlt]
    refine Pushes.iteT (by rw [hF, hc]; rfl) ?_
    exact haveP_pushes h₂ ((hq.set_ne (by decide) _).set_ne (by decide) _)
      ((ha.set_ne (by decide) _).set_ne (by decide) _) ((Top.set_same S sI3 _ _).set_ne (by decide) _)
      (by omega)
  · rw [if_neg hlt]
    have hc : cmpRes i L ≠ 0 := by simp only [cmpRes, hL, hlt, if_false]; split <;> simp
    refine Pushes.iteF (by rw [hF]; simp [hc]) ?_
    exact pushes_skip _ _ _

/-- The rule cards of the state on top of `sQ` reading the symbol on top of `sA`. -/
def cellP : NProg UK := letP sT1 (predE sT1 sSC ⟨[sQ], 0⟩) (.ite sT1 .pos rowP (nskip sSC))

/-- The cards of `rulesQA` at the level of lists. -/
theorem cell_out {nq na : Nat} {rest : List Nat} (h3 : rest.length % 3 = 0) (m q a : Nat) :
    (rulesQA (table1 nq na rest) q a).flatMap (encSC m) =
      if q = 0 ∨ q = 1 then [] else if 3 * (q * na + a) < rest.length then
        movOut (bnd (table1 nq na rest)) m q a (rest.getD (3 * (q * na + a)) 0) (rest.getD (3 * (q * na + a) + 1) 0)
          (rest.getD (3 * (q * na + a) + 2) 0) else [] := by
  by_cases hq : q = 0 ∨ q = 1
  · simp [rulesQA, hq]
  · simp only [rulesQA, hq, if_false, idx_table1, rows_table1 h3]
    by_cases hi : 3 * (q * na + a) < rest.length
    · simp only [hi, if_true]
      generalize rest.getD (3 * (q * na + a)) 0 = x
      generalize rest.getD (3 * (q * na + a) + 1) 0 = y
      generalize rest.getD (3 * (q * na + a) + 2) 0 = z
      rcases z with _ | _ | z
      · simp [cellRules, Undec.mv, wr, Move.ofCode, movOut, lbS, stS, List.flatMap_cons, List.flatMap_map]
      · simp [cellRules, Undec.mv, wr, Move.ofCode, movOut, lbS, stS]
      · simp [cellRules, Undec.mv, wr, Move.ofCode, movOut, lbS, stS]
    · simp [hi]

/-- **The rule cards of one state and one symbol.** -/
theorem cellP_pushes {S : Lists UK} {bits rest : List Nat} {nw L m na3 q a nq na : Nat}
    (h : BE S bits rest nw L (bnd (table1 nq na rest)) (2 * bnd (table1 nq na rest) + 2) m na3)
    (hq : Top S sQ q) (ha : Top S sA a) (hL : L = rest.length) (h3 : rest.length % 3 = 0) (hna : na3 = 3 * na) :
    Pushes sOUT cellP S ((rulesQA (table1 nq na rest) q a).flatMap (encSC m)) := by
  rw [cell_out h3]
  have d₁ := predE_pushes (t := sT1) (s := sSC) (e := ⟨[sQ], 0⟩) (by decide) (by decide) (by decide) S h.sc
  have hv : LinE.ev S ⟨[sQ], 0⟩ = q := by simp [LinE.ev, hq.tv]
  rw [hv] at d₁
  refine letP_pushes (by decide) d₁ ?_
  have h₁ := h.set sT1 (by decide) (S sT1 ++ [q - 1])
  have hT : NTest.pos.eval ((S.set sT1 (S sT1 ++ [q - 1])) sT1) = decide (0 < q - 1) := by
    simp only [Lists.set_same, eval_pos_snoc]
  by_cases hq01 : q = 0 ∨ q = 1
  · rw [if_pos hq01]
    refine Pushes.iteF (by rw [hT]; simp; omega) ?_
    exact pushes_skip _ _ _
  · rw [if_neg hq01]
    refine Pushes.iteT (by rw [hT]; simp; omega) ?_
    exact rowP_pushes h₁ (hq.set_ne (by decide) _) (ha.set_ne (by decide) _) hL h3 hna

end MC

end Shallot
