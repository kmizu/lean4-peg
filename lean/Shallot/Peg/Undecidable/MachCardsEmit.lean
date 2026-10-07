import Shallot.Peg.Undecidable.MachCardsCell

/-!
# Writing all the cards

In the environment `BE` of a good code, `emitP` writes the cards of `tablePCPN (table1 nq na rest) w` onto
`sOUT` in the format of `encCards` and leaves every other stack as it was (`emitP_pushes`):
the first card (`startP`), the rule cards (`rulesP`: the loops over `q` and `a` of `cellP`, then the end rules and
the erasing rules), the separator, the copies, the closing card and the end card.
-/

namespace Shallot

open Complexity
open Complexity.Univ
open Complexity.Undec

namespace MC

/-! ## The rule cards -/

def aLoop : NProg UK := forP sA sRA sSC ⟨[sB], 0⟩ cellP
def qLoop : NProg UK := forP sQ sRQ sSC ⟨[sB], 0⟩ aLoop

/-- The end rule of the state on top of `sQ`. -/
def cardE : List (LinE UK) := scE sM [⟨[sB, sQ], 2⟩, ⟨[sB], 1⟩] [⟨[sB, sQ], 2⟩, ⟨[], 0⟩, ⟨[sB], 1⟩]
def endBody : NProg UK := letP sT1 (predE sT1 sSC ⟨[sQ], 0⟩) (.ite sT1 .pos (pushEs sOUT sSC cardE) (nskip sSC))
def endsP : NProg UK := forP sQ sRQ sSC ⟨[sB], 0⟩ endBody

/-- The erasing rules of the symbol on top of `sX`. -/
def cardEL : List (LinE UK) := scE sM [⟨[sX], 0⟩, ⟨[sB], 2⟩] [⟨[sB], 2⟩]
def cardER : List (LinE UK) := scE sM [⟨[sB], 2⟩, ⟨[sX], 0⟩] [⟨[sB], 2⟩]
def erasesP : NProg UK := forP sX sRX sSC ⟨[sB], 2⟩ (.seq (pushEs sOUT sSC cardEL) (pushEs sOUT sSC cardER))

def rulesP : NProg UK := .seq qLoop (.seq endsP erasesP)

section
variable {S : Lists UK}

theorem loopSt_BE {bits rest : List Nat} {nw L b n m na3 : Nat} (h : BE S bits rest nw L b n m na3) {X Y : Fin UK}
    (hX : X ∉ beStacks) (hY : Y ∉ beStacks) (o lx ly : List Nat) :
    BE (((S.set sOUT o).set X lx).set Y ly) bits rest nw L b n m na3 :=
  ((h.set sOUT (by decide) o).set X hX lx).set Y hY ly

theorem loopSt_top {X Y : Fin UK} (hXY : X ≠ Y) (S : Lists UK) (o l : List Nat) (j : Nat) (ly : List Nat) :
    Top (((S.set sOUT o).set X (l ++ [j])).set Y ly) X j :=
  (Top.set_same _ X l j).set_ne hXY ly

theorem loopSt_keep {Z X Y : Fin UK} {v : Nat} (h : Top S Z v) (h₁ : Z ≠ sOUT) (h₂ : Z ≠ X) (h₃ : Z ≠ Y)
    (o lx ly : List Nat) : Top (((S.set sOUT o).set X lx).set Y ly) Z v :=
  ((h.set_ne h₁ o).set_ne h₂ lx).set_ne h₃ ly

variable {bits rest : List Nat} {nw L m na3 nq na : Nat}

theorem qLoop_pushes (h : BE S bits rest nw L (bnd (table1 nq na rest)) (2 * bnd (table1 nq na rest) + 2) m na3)
    (hL : L = rest.length) (h3 : rest.length % 3 = 0) (hna : na3 = 3 * na) :
    Pushes sOUT qLoop S ((List.range (bnd (table1 nq na rest))).flatMap fun q =>
      (List.range (bnd (table1 nq na rest))).flatMap fun a => (rulesQA (table1 nq na rest) q a).flatMap (encSC m)) := by
  have hlim : ∀ S' : Lists UK, Top S' sB (bnd (table1 nq na rest)) →
      LinE.ev S' ⟨[sB], 0⟩ = bnd (table1 nq na rest) := fun S' h' => by simp [LinE.ev, h'.tv]
  exact forP_pushes' (t := sOUT) (X := sQ) (Y := sRQ) (s := sSC) (lim := ⟨[sB], 0⟩) (body := aLoop)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) S h.sc
    _ (hlim _ h.bb)
    (fun q => (List.range (bnd (table1 nq na rest))).flatMap fun a =>
      (rulesQA (table1 nq na rest) q a).flatMap (encSC m))
    (fun q _ o => by
      have hq := loopSt_BE h (X := sQ) (Y := sRQ) (by decide) (by decide) o (S sQ ++ [q])
        (S sRQ ++ [bnd (table1 nq na rest) - q])
      have tq := loopSt_top (show sQ ≠ sRQ by decide) S o (S sQ) q (S sRQ ++ [bnd (table1 nq na rest) - q])
      exact forP_pushes' (t := sOUT) (X := sA) (Y := sRA) (s := sSC) (lim := ⟨[sB], 0⟩) (body := cellP)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _ hq.sc
        _ (hlim _ hq.bb)
        (fun a => (rulesQA (table1 nq na rest) q a).flatMap (encSC m))
        (fun a _ o' => cellP_pushes (loopSt_BE hq (by decide) (by decide) o' _ _)
          (loopSt_keep tq (by decide) (by decide) (by decide) _ _ _) (loopSt_top (by decide) _ o' _ a _) hL h3 hna))

theorem endsP_pushes (h : BE S bits rest nw L (bnd (table1 nq na rest)) (2 * bnd (table1 nq na rest) + 2) m na3) :
    Pushes sOUT endsP S ((List.range (bnd (table1 nq na rest))).flatMap fun q =>
      if q = 0 ∨ q = 1 then [] else encSC m (endRule (table1 nq na rest) q)) := by
  exact forP_pushes' (t := sOUT) (X := sQ) (Y := sRQ) (s := sSC) (lim := ⟨[sB], 0⟩) (body := endBody)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) S h.sc
    _ (by simp [LinE.ev, h.bb.tv])
    (fun q => if q = 0 ∨ q = 1 then [] else encSC m (endRule (table1 nq na rest) q))
    (fun q _ o => by
      generalize hS₀ : (((S.set sOUT o).set sQ (S sQ ++ [q])).set sRQ (S sRQ ++ [bnd (table1 nq na rest) - q])) = S₀
      have hq : BE S₀ bits rest nw L (bnd (table1 nq na rest)) (2 * bnd (table1 nq na rest) + 2) m na3 := by
        rw [← hS₀]; exact loopSt_BE h (by decide) (by decide) o _ _
      have tq : Top S₀ sQ q := by rw [← hS₀]; exact loopSt_top (by decide) S o _ q _
      have d₁ := predE_pushes (t := sT1) (s := sSC) (e := ⟨[sQ], 0⟩) (by decide) (by decide) (by decide) _ hq.sc
      rw [show LinE.ev S₀ ⟨[sQ], 0⟩ = q by simp [LinE.ev, tq.tv]] at d₁
      refine letP_pushes (by decide) d₁ ?_
      have h₁ := hq.set sT1 (by decide) (S₀ sT1 ++ [q - 1])
      have tq' := tq.set_ne (show sQ ≠ sT1 by decide) (S₀ sT1 ++ [q - 1])
      have hT : NTest.pos.eval ((S₀.set sT1 (S₀ sT1 ++ [q - 1])) sT1) = decide (0 < q - 1) := by
        simp only [Lists.set_same, eval_pos_snoc]
      by_cases hq01 : q = 0 ∨ q = 1
      · rw [if_pos hq01]
        refine Pushes.iteF (by rw [hT]; simp; omega) ?_
        exact pushes_skip _ _ _
      · rw [if_neg hq01]
        refine Pushes.iteT (by rw [hT]; simp; omega) ?_
        refine pushEs_card h₁ (by decide) (by decide) ?_
        generalize S₀.set sT1 (S₀ sT1 ++ [q - 1]) = S₁ at h₁ tq'
        simp [LinE.ev, tq'.tv, h₁.bb.tv, endRule, stS, rbS]
        omega)

theorem erasesP_pushes (h : BE S bits rest nw L (bnd (table1 nq na rest)) (2 * bnd (table1 nq na rest) + 2) m na3) :
    Pushes sOUT erasesP S ((List.range (bnd (table1 nq na rest) + 2)).flatMap fun x =>
      encSC m ([x, stS (table1 nq na rest) 0], [stS (table1 nq na rest) 0]) ++
        encSC m ([stS (table1 nq na rest) 0, x], [stS (table1 nq na rest) 0])) := by
  exact forP_pushes' (t := sOUT) (X := sX) (Y := sRX) (s := sSC) (lim := ⟨[sB], 2⟩)
    (body := .seq (pushEs sOUT sSC cardEL) (pushEs sOUT sSC cardER))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) S h.sc
    _ (by simp [LinE.ev, h.bb.tv])
    (fun x => encSC m ([x, stS (table1 nq na rest) 0], [stS (table1 nq na rest) 0]) ++
        encSC m ([stS (table1 nq na rest) 0, x], [stS (table1 nq na rest) 0]))
    (fun x _ o => by
      generalize hS₀ : (((S.set sOUT o).set sX (S sX ++ [x])).set sRX
        (S sRX ++ [bnd (table1 nq na rest) + 2 - x])) = S₀
      have hx : BE S₀ bits rest nw L (bnd (table1 nq na rest)) (2 * bnd (table1 nq na rest) + 2) m na3 := by
        rw [← hS₀]; exact loopSt_BE h (by decide) (by decide) o _ _
      have tx : Top S₀ sX x := by rw [← hS₀]; exact loopSt_top (by decide) S o _ x _
      refine pushes_seq (pushEs_card hx (by decide) (by decide) ?_) ?_
      · simp [LinE.ev, tx.tv, hx.bb.tv, stS]
      · have hx' := hx.set sOUT (by decide)
          (S₀ sOUT ++ encSC m ([x, stS (table1 nq na rest) 0], [stS (table1 nq na rest) 0]))
        have tx' := tx.set_ne (show sX ≠ sOUT by decide)
          (S₀ sOUT ++ encSC m ([x, stS (table1 nq na rest) 0], [stS (table1 nq na rest) 0]))
        refine pushEs_card hx' (by decide) (by decide) ?_
        generalize S₀.set sOUT _ = S₁ at hx' tx'
        simp [LinE.ev, tx'.tv, hx'.bb.tv, stS])

theorem rulesP_pushes (h : BE S bits rest nw L (bnd (table1 nq na rest)) (2 * bnd (table1 nq na rest) + 2) m na3)
    (hL : L = rest.length) (h3 : rest.length % 3 = 0) (hna : na3 = 3 * na) :
    Pushes sOUT rulesP S ((tmSRS (table1 nq na rest)).flatMap (encSC m)) := by
  rw [tmSRS_flatMap, List.append_assoc]
  exact pushes_seq (qLoop_pushes h hL h3 hna)
    (pushes_seq (endsP_pushes (h.set sOUT (by decide) _)) (erasesP_pushes ((h.set sOUT (by decide) _).set sOUT
      (by decide) _)))

/-! ## The first card -/

def startPre : List (LinE UK) :=
  [⟨[], 2⟩, ⟨[sM], 0⟩, ⟨[sN], 0⟩, ⟨[sNN, sNN], 11⟩, ⟨[sM], 0⟩, ⟨[sN], 0⟩, ⟨[sM], 0⟩, ⟨[sB], 0⟩, ⟨[sM], 0⟩,
    ⟨[sB], 4⟩, ⟨[sM], 0⟩]
def startPost : List (LinE UK) := [⟨[sB], 1⟩, ⟨[sM], 0⟩, ⟨[sN], 1⟩, ⟨[sM], 0⟩]
def bitBody : NProg UK :=
  letP sBV (peekE sXB sTMP sCC sBV sSC (by decide) (by decide) ⟨[sJ], 0⟩) (pushEs sOUT sSC [⟨[sBV], 1⟩, ⟨[sM], 0⟩])
def bitsP : NProg UK := forP sJ sRJ sSC ⟨[sNN], 0⟩ bitBody
def startP : NProg UK := .seq (pushEs sOUT sSC startPre) (.seq bitsP (pushEs sOUT sSC startPost))

theorem bitsP_pushes {w : List Bool} {L b n m na3 : Nat} (h : BE S (w.map bitElem) rest w.length L b n m na3) :
    Pushes sOUT bitsP S (w.flatMap fun x => [bitSym x, m]) := by
  have d := forP_pushes' (t := sOUT) (X := sJ) (Y := sRJ) (s := sSC) (lim := ⟨[sNN], 0⟩) (body := bitBody)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) S h.sc
    w.length (by simp [LinE.ev, h.nn.tv]) (fun j => [(w.map bitElem).getD j 0 + 1, m])
    (fun j hj o => by
      generalize hS₀ : (((S.set sOUT o).set sJ (S sJ ++ [j])).set sRJ (S sRJ ++ [w.length - j])) = S₀
      have hx : BE S₀ (w.map bitElem) rest w.length L b n m na3 := by
        rw [← hS₀]; exact loopSt_BE h (by decide) (by decide) o _ _
      have tj : Top S₀ sJ j := by rw [← hS₀]; exact loopSt_top (by decide) S o _ j _
      have hev : LinE.ev S₀ ⟨[sJ], 0⟩ = j := by simp [LinE.ev, tj.tv]
      have d₁ := peekE_pushes (tab := sXB) (tmp := sTMP) (cc := sCC) (o := sBV) (s := sSC) (e := ⟨[sJ], 0⟩)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) S₀ hx.sc hx.tmp
        (by rw [hev, hx.xb]; simpa using hj)
      rw [hev, hx.xb] at d₁
      refine letP_pushes (by decide) d₁ ?_
      have hx' := hx.set sBV (by decide) (S₀ sBV ++ [(w.map bitElem).getD j 0])
      have tv' := Top.set_same S₀ sBV (S₀ sBV) ((w.map bitElem).getD j 0)
      generalize S₀.set sBV (S₀ sBV ++ [(w.map bitElem).getD j 0]) = S₁ at hx' tv'
      refine (pushEs_pushes (by decide) _ (by decide) (by decide) S₁ hx'.sc).cast ?_
      simp [LinE.ev, tv'.tv, hx'.mm.tv])
  refine d.cast ?_
  have := range_flatMap_getD (fun v => [v + 1, m]) 0 (w.map bitElem)
  rw [List.length_map] at this
  rw [this, List.flatMap_map]
  simp only [MacroPeg.KExp.bitElem_succ]

theorem mpRStar_append (m : Nat) (u v : Word) : mpRStar m (u ++ v) = mpRStar m u ++ mpRStar m v := by
  simp [mpRStar, List.flatMap_append]

/-- The first card, at the level of lists. -/
theorem start_eq (T : TTable) (w : List Bool) :
    encC (mpStar (2 * bnd T + 4) [2 * bnd T + 2],
        (2 * bnd T + 4) :: mpRStar (2 * bnd T + 4) ((2 * bnd T + 2) :: (tmStart T w ++ [2 * bnd T + 3]))) =
      [2, 2 * bnd T + 4, 2 * bnd T + 2, w.length + w.length + 11, 2 * bnd T + 4, 2 * bnd T + 2, 2 * bnd T + 4,
          bnd T, 2 * bnd T + 4, bnd T + 4, 2 * bnd T + 4] ++
        ((w.flatMap fun x => [bitSym x, 2 * bnd T + 4]) ++
          [bnd T + 1, 2 * bnd T + 4, 2 * bnd T + 3, 2 * bnd T + 4]) := by
  rw [tmStart_eq]
  generalize bnd T = b
  have hlen : (mpRStar (2 * b + 4) ((2 * b + 2) :: ((b :: (b + 4) :: (w.map bitSym ++ [b + 1])) ++ [2 * b + 3]))).length
      = w.length + w.length + 10 := by
    rw [mpRStar_length]; simp; omega
  have e₁ : mpRStar (2 * b + 4) ((2 * b + 2) :: ((b :: (b + 4) :: (w.map bitSym ++ [b + 1])) ++ [2 * b + 3])) =
      [2 * b + 2, 2 * b + 4, b, 2 * b + 4, b + 4, 2 * b + 4] ++
        ((w.flatMap fun x => [bitSym x, 2 * b + 4]) ++ [b + 1, 2 * b + 4, 2 * b + 3, 2 * b + 4]) := by
    simp only [List.cons_append, mpRStar_cons, mpRStar_append]
    simp [mpRStar, List.flatMap_map]
  have hs : ∀ l : List Bool, (l.map (fun _ => 2)).sum = l.length + l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega
  simp only [encC, List.length_cons, e₁, mpStar_cons, mpStar_nil, List.length_nil]
  simp [hs]

theorem startP_pushes {w : List Bool} {L b m na3 : Nat} (h : BE S (w.map bitElem) rest w.length L b (2 * b + 2) m na3) :
    Pushes sOUT startP S ([2, m, 2 * b + 2, w.length + w.length + 11, m, 2 * b + 2, m, b, m, b + 4, m] ++
      ((w.flatMap fun x => [bitSym x, m]) ++ [b + 1, m, 2 * b + 3, m])) := by
  refine pushes_seq ((pushEs_pushes (by decide) _ (by decide) (by decide) S h.sc).cast ?_)
    (pushes_seq (bitsP_pushes (h.set sOUT (by decide) _))
      ((pushEs_pushes (by decide) _ (by decide) (by decide) _ ((h.set sOUT (by decide) _).set sOUT (by decide) _).sc).cast
        ?_))
  · simp [startPre, LinE.ev, h.mm.tv, h.nN.tv, h.nn.tv, h.bb.tv]
  · have h₂ := (h.set sOUT (by decide) (S sOUT ++ [2, m, 2 * b + 2, w.length + w.length + 11, m, 2 * b + 2, m, b, m,
      b + 4, m])).set sOUT (by decide) ((S.set sOUT (S sOUT ++ [2, m, 2 * b + 2, w.length + w.length + 11, m, 2 * b + 2,
        m, b, m, b + 4, m])) sOUT ++ w.flatMap fun x => [bitSym x, m])
    generalize (S.set sOUT _).set sOUT _ = S₂ at h₂ ⊢
    simp [startPost, LinE.ev, h₂.mm.tv, h₂.bb.tv, h₂.nN.tv]

/-! ## The other cards -/

def sepP : NProg UK := pushEs sOUT sSC (scE sM [⟨[sN], 1⟩] [⟨[sN], 1⟩])
def copiesP : NProg UK := forP sC sRC sSC ⟨[sN], 0⟩ (pushEs sOUT sSC (scE sM [⟨[sC], 0⟩] [⟨[sC], 0⟩]))
def closeP : NProg UK := pushEs sOUT sSC (scE sM [⟨[sB], 2⟩, ⟨[sN], 1⟩, ⟨[sN], 0⟩] [⟨[sN], 0⟩])
def endP : NProg UK := pushEs sOUT sSC [⟨[], 2⟩, ⟨[sM], 0⟩, ⟨[sM], 1⟩, ⟨[], 1⟩, ⟨[sM], 1⟩]

section
variable {L b m na3 : Nat}

theorem sepP_pushes (h : BE S bits rest nw L b (2 * b + 2) m na3) :
    Pushes sOUT sepP S (encSC m ([2 * b + 3], [2 * b + 3])) :=
  pushEs_card h (by decide) (by decide) (by simp [LinE.ev, h.nN.tv])

theorem copiesP_pushes (h : BE S bits rest nw L b (2 * b + 2) m na3) :
    Pushes sOUT copiesP S ((List.range (2 * b + 2)).flatMap fun a => encSC m ([a], [a])) :=
  forP_pushes' (t := sOUT) (X := sC) (Y := sRC) (s := sSC) (lim := ⟨[sN], 0⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) S h.sc
    _ (by simp [LinE.ev, h.nN.tv]) (fun a => encSC m ([a], [a])) (fun j _ o => by
      have hx := loopSt_BE h (X := sC) (Y := sRC) (by decide) (by decide) o (S sC ++ [j]) (S sRC ++ [2 * b + 2 - j])
      have tj := loopSt_top (show sC ≠ sRC by decide) S o (S sC) j (S sRC ++ [2 * b + 2 - j])
      generalize (((S.set sOUT o).set sC (S sC ++ [j])).set sRC (S sRC ++ [2 * b + 2 - j])) = S₀ at hx tj ⊢
      exact pushEs_card hx (by decide) (by decide) (by simp [LinE.ev, tj.tv]))

theorem closeP_pushes (h : BE S bits rest nw L b (2 * b + 2) m na3) :
    Pushes sOUT closeP S (encSC m ([b + 2, 2 * b + 3, 2 * b + 2], [2 * b + 2])) :=
  pushEs_card h (by decide) (by decide) (by simp [LinE.ev, h.nN.tv, h.bb.tv])

theorem endP_pushes (h : BE S bits rest nw L b (2 * b + 2) (2 * b + 4) na3) :
    Pushes sOUT endP S (encC ([2 * b + 4, 2 * b + 5], [2 * b + 5])) :=
  (pushEs_pushes (by decide) _ (by decide) (by decide) S h.sc).cast (by simp [LinE.ev, h.mm.tv, encC])

end

/-- All the cards. -/
def emitP : NProg UK := .seq startP (.seq rulesP (.seq sepP (.seq copiesP (.seq closeP endP))))

/-- **All the cards of a good code.** -/
theorem emitP_pushes {w : List Bool} (h3 : rest.length % 3 = 0)
    (h : BE S (w.map bitElem) rest w.length rest.length (bnd (table1 nq na rest)) (2 * bnd (table1 nq na rest) + 2)
      (2 * bnd (table1 nq na rest) + 4) (3 * na)) :
    Pushes sOUT emitP S (encCards (tablePCPN (table1 nq na rest) w)) := by
  rw [encCards_table, start_eq]
  refine (pushes_seq (startP_pushes h) (pushes_seq (rulesP_pushes (h.set sOUT (by decide) _) rfl h3 rfl)
    (pushes_seq (sepP_pushes ((h.set sOUT (by decide) _).set sOUT (by decide) _))
      (pushes_seq (copiesP_pushes (((h.set sOUT (by decide) _).set sOUT (by decide) _).set sOUT (by decide) _))
        (pushes_seq (closeP_pushes ((((h.set sOUT (by decide) _).set sOUT (by decide) _).set sOUT (by decide) _).set
            sOUT (by decide) _))
          (endP_pushes (((((h.set sOUT (by decide) _).set sOUT (by decide) _).set sOUT (by decide) _).set
            sOUT (by decide) _).set sOUT (by decide) _))))))).cast ?_
  simp only [List.append_assoc]

end

end MC

end Shallot
