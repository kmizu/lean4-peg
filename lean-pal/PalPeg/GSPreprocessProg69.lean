import PalPeg.GSPreprocessProg68

/-! # Finite restoration of the input head using the pattern tape -/
set_option autoImplicit false
namespace PalPeg.PrepInstance
open PegSeparation.RealTimeTM PalPeg.PatternTapes PalPeg.PatternProg PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank : Fin sc}

def restoreInputProg (startSym endSym : Fin sc) : Prog (ActG 15 sc) (CondG 15 sc) :=
  .seq (tandemRight sU sIn endSym)
    (.seq (.loop (sU, startSym) (TAct.keep sU .left).act .skip)
      (ACT (.keep sU .right)))

def restoreInputActs (L : ℕ) : List (TAct 15 sc) :=
  tandemActs sU sIn L ++ (leftWalkG sU (L + 1) ++ [.keep sU .right])

theorem restoreInputActs_length (L : ℕ) :
    (restoreInputActs (sc := sc) L).length = 3 * L + 2 := by
  simp [restoreInputActs, tandemActs_length]
  omega

theorem leftWalkG_view (i : Fin 15) (n : ℕ) (S : Tapes sc)
    {W : List (Fin sc)} {p : ℕ} (h : Tape.SeqView blank (S i) W p) (hn : n ≤ p) :
    Tape.SeqView blank (runG blank (leftWalkG i n) S i) W (p - n) := by
  induction n generalizing S p with
  | zero => simpa [leftWalkG] using h
  | succ n ih =>
    have hp : 0 < p := by omega
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
    have hstep : Tape.SeqView blank (applyG blank S (.keep i .left) i) W q := by
      rw [applyG_keep_self]
      exact Tape.seq_move_left h
    simpa [leftWalkG, List.replicate_succ, runG_cons] using
      ih _ hstep (by omega)

theorem restoreInput_exec {startSym endSym leftSym : Fin sc} {x v : List (Fin sc)}
    (hstart : startSym ∉ x) (hend : endSym ∉ x) (hne : startSym ≠ endSym)
    (S : Tapes sc) (hu : Tape.SeqView blank (S sU) (startSym :: (x ++ [endSym])) 1)
    (hi : Tape.SeqView blank (S sIn) (leftSym :: v) 0) (hlen : v.length = x.length) :
    ExecG Terminal blank (restoreInputProg startSym endSym) S (restoreInputActs x.length) ∧
    Tape.SeqView blank (runG blank (restoreInputActs x.length) S sU)
      (startSym :: (x ++ [endSym])) 1 := by
  have he : endSym ∉ startSym :: x := by simp [hend, Ne.symm hne]
  have eu := tandemRight_exec (Terminal := Terminal) (show sIn ≠ sU by decide) he
    x.length 1 S (by simp [Nat.add_comm]) (by simpa using hu)
  have ht := (tandemActs_spec (show sIn ≠ sU by decide) x.length S hu hi
    (by simp; omega) (by simp; omega)).1
  have hs := Fifteen.settle_sentinel_fresh x.reverse endSym
    (by simpa using hstart) hne
  have hword : (endSym :: (x.reverse ++ [startSym])).reverse =
      startSym :: (x ++ [endSym]) := by simp
  rw [hword] at hs
  have el := leftWalkLoop_exec (Terminal := Terminal) hs.1 hs.2 (x.length + 1)
    (runG blank (tandemActs sU sIn x.length) S) (by simpa [Nat.add_comm] using ht)
  have hl := leftWalkG_view sU (x.length + 1)
    (runG blank (tandemActs sU sIn x.length) S) ht (by omega)
  have hz : Tape.SeqView blank
      (runG blank (leftWalkG sU (x.length + 1))
        (runG blank (tandemActs sU sIn x.length) S) sU)
      (startSym :: (x ++ [endSym])) 0 := by simpa [Nat.add_comm] using hl
  constructor
  · exact execG_seq eu (execG_seq el (execG_act _ _))
  · simp only [restoreInputActs, runG_append, runG_cons, runG_nil, applyG_keep_self]
    exact Tape.seq_move_right hz (by simp)

theorem leftWalkG_other {i j : Fin 15} (hji : j ≠ i) (n : ℕ) (S : Tapes sc) :
    runG blank (leftWalkG i n) S j = S j := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    simp only [leftWalkG, List.replicate_succ, runG_cons] at *
    rw [ih, applyG_ne blank _ (TAct.keep i .left) hji]

theorem restoreInput_input {startSym endSym leftSym : Fin sc} {x v : List (Fin sc)}
    (S : Tapes sc) (hu : Tape.SeqView blank (S sU) (startSym :: (x ++ [endSym])) 1)
    (hi : Tape.SeqView blank (S sIn) (leftSym :: v) 0) (hlen : v.length = x.length) :
    Tape.SeqView blank (runG blank (restoreInputActs x.length) S sIn)
      (leftSym :: v) x.length := by
  simp only [restoreInputActs, runG_append, runG_cons, runG_nil]
  rw [applyG_ne blank _ (TAct.keep sU .right) (show sIn ≠ sU by decide),
    leftWalkG_other (show sIn ≠ sU by decide)]
  simpa only [Nat.zero_add] using (tandemActs_spec (show sIn ≠ sU by decide) x.length S hu hi
    (by simp; omega) (by simp; omega)).2

theorem restoreInput_other {j : Fin 15} (hju : j ≠ sU) (hji : j ≠ sIn)
    (L : ℕ) (S : Tapes sc) :
    runG blank (restoreInputActs L) S j = S j := by
  simp only [restoreInputActs, runG_append, runG_cons, runG_nil]
  rw [applyG_ne blank _ (TAct.keep sU .right) hju, leftWalkG_other hju,
    tandemActs_other hju hji]

/-- Initial pushes, sentinel-controlled copying, and the two settling loops.
Neither this syntax nor its control conditions depend on the input length. -/
def prologuePrefix (blank startSym endSym leftSym : Fin sc) :
    Prog (ActG 15 sc) (CondG 15 sc) :=
  .seq (Fifteen.pushBothProg startSym)
    (.seq (copy2Prog sIn sU sP leftSym)
      (.seq (Fifteen.pushBothProg endSym)
        (.seq (settleProgG sU blank startSym) (settleProgG sP blank startSym))))

def settleTrace (blank : Fin sc) (i : Fin 15) (L : ℕ) : List (TAct 15 sc) :=
  .put i blank .left :: (leftWalkG i (L + 1) ++ [.keep i .right])

def prologuePrefixActs (blank startSym endSym : Fin sc) (L : ℕ) : List (TAct 15 sc) :=
  Fifteen.pushBothActs startSym ++ (copy2Acts sIn sU sP L ++
    (Fifteen.pushBothActs endSym ++ (settleTrace blank sU L ++ settleTrace blank sP L)))

theorem prologuePrefixActs_length (blank startSym endSym : Fin sc) (L : ℕ) :
    (prologuePrefixActs blank startSym endSym L).length = 5 * L + 10 := by
  simp [prologuePrefixActs, Fifteen.pushBothActs, copy2Acts_length, settleTrace]
  omega

theorem settleTrace_view {i : Fin 15} {a startSym : Fin sc} {X : List (Fin sc)}
    (S : Tapes sc) (h : Tape.StackView blank (S i) (a :: (X ++ [startSym]))) :
    Tape.SeqView blank (runG blank (settleTrace blank i X.length) S i)
      (startSym :: (X.reverse ++ [a])) 1 := by
  have hv := settle_spec blank i h (show (X ++ [startSym]).length = X.length + 1 by simp)
  have hword : (a :: (X ++ [startSym])).reverse = startSym :: (X.reverse ++ [a]) := by simp
  rw [hword] at hv
  have hl : (run blank (settle blank i X.length) S i).left = [startSym] := by
    simpa using hv.left_eq
  rw [settleTrace, Fifteen.settleActs_run blank i X.length S hl]
  exact hv

theorem settleTrace_other {i j : Fin 15} (hji : j ≠ i) (L : ℕ) (S : Tapes sc) :
    runG blank (settleTrace blank i L) S j = S j := by
  simp only [settleTrace, runG_cons, runG_append, runG_nil]
  rw [applyG_ne blank _ (TAct.keep i .right) hji, leftWalkG_other hji,
    applyG_ne blank _ (TAct.put i blank .left) hji]

theorem prologuePrefix_exec {startSym endSym leftSym : Fin sc} {v : List (Fin sc)}
    (hfresh : leftSym ∉ v) (hstart : startSym ∉ v) (hne : startSym ≠ endSym)
    (S : Tapes sc) (hi : Tape.SeqView blank (S sIn) (leftSym :: v) v.length)
    (hu : Tape.StackView blank (S sU) []) (hp : Tape.StackView blank (S sP) []) :
    ExecG Terminal blank (prologuePrefix blank startSym endSym leftSym) S
      (prologuePrefixActs blank startSym endSym v.length) ∧
    Tape.SeqView blank (runG blank (prologuePrefixActs blank startSym endSym v.length) S sU)
      (startSym :: (v.reverse ++ [endSym])) 1 ∧
    Tape.SeqView blank (runG blank (prologuePrefixActs blank startSym endSym v.length) S sP)
      (startSym :: (v.reverse ++ [endSym])) 1 ∧
    Tape.SeqView blank (runG blank (prologuePrefixActs blank startSym endSym v.length) S sIn)
      (leftSym :: v) 0 := by
  let S1 := runG blank (Fifteen.pushBothActs startSym) S
  let S2 := runG blank (copy2Acts sIn sU sP v.length) S1
  let S3 := runG blank (Fifteen.pushBothActs endSym) S2
  let S4 := runG blank (settleTrace blank sU v.length) S3
  let S5 := runG blank (settleTrace blank sP v.length) S4
  have h1u : Tape.StackView blank (S1 sU) [startSym] := by
    dsimp [S1]; rw [Fifteen.pushBothActs_run, pushBoth_U]
    simpa using Tape.push_spec hu startSym
  have h1p : Tape.StackView blank (S1 sP) [startSym] := by
    dsimp [S1]; rw [Fifteen.pushBothActs_run, pushBoth_P]
    simpa using Tape.push_spec hp startSym
  have h1i : Tape.SeqView blank (S1 sIn) (leftSym :: v) v.length := by
    dsimp [S1]; rw [Fifteen.pushBothActs_run, pushBoth_ne blank startSym (by decide) (by decide)]
    exact hi
  have h2 := copyLoop2_spec blank (show sU ≠ sIn by decide) (show sP ≠ sIn by decide)
    (show sU ≠ sP by decide) v.length v.length S1 (leftSym :: v)
    [startSym] [startSym] (by omega) h1i h1u h1p
  have hseg : ((leftSym :: v).take (v.length + 1)).drop (v.length + 1 - v.length) = v := by
    simp [List.take_of_length_le]
  have hr2 : S2 = run blank (copyLoop2 blank sIn sU sP v.length S1) S1 :=
    copy2Acts_run (by decide) _ _
  rw [← hr2, hseg, Nat.sub_self] at h2
  have h3u : Tape.StackView blank (S3 sU) (endSym :: (v ++ [startSym])) := by
    dsimp [S3]; rw [Fifteen.pushBothActs_run, pushBoth_U]
    exact Tape.push_spec h2.2.1 endSym
  have h3p : Tape.StackView blank (S3 sP) (endSym :: (v ++ [startSym])) := by
    dsimp [S3]; rw [Fifteen.pushBothActs_run, pushBoth_P]
    exact Tape.push_spec h2.2.2 endSym
  have h3i : Tape.SeqView blank (S3 sIn) (leftSym :: v) 0 := by
    dsimp [S3]; rw [Fifteen.pushBothActs_run, pushBoth_ne blank endSym (by decide) (by decide)]
    exact h2.1
  have h4p : Tape.StackView blank (S4 sP) (endSym :: (v ++ [startSym])) := by
    dsimp [S4]; rw [settleTrace_other (by decide)]; exact h3p
  have hs := Fifteen.settle_sentinel_fresh v endSym hstart hne
  have e4 : ExecG Terminal blank (settleProgG sU blank startSym) S3
      (settleTrace blank sU v.length) := by
    simpa [settleTrace] using settleProgG_exec (Terminal := Terminal) h3u hs.1 hs.2
  have e5 : ExecG Terminal blank (settleProgG sP blank startSym) S4
      (settleTrace blank sP v.length) := by
    simpa [settleTrace] using settleProgG_exec (Terminal := Terminal) h4p hs.1 hs.2
  have hr : runG blank (prologuePrefixActs blank startSym endSym v.length) S = S5 := by
    simp only [prologuePrefixActs, runG_append]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact execG_seq (Fifteen.pushBothProg_exec _ _)
      (execG_seq (copy2Prog_exec (by decide) (by decide) hfresh _ _ h1i)
        (execG_seq (Fifteen.pushBothProg_exec _ _) (execG_seq e4 e5)))
  · rw [hr]; dsimp [S5]; rw [settleTrace_other (by decide)]
    exact settleTrace_view S3 h3u
  · rw [hr]; exact settleTrace_view S4 h4p
  · rw [hr]; dsimp [S5, S4]
    rw [settleTrace_other (show sIn ≠ sP by decide), settleTrace_other (show sIn ≠ sU by decide)]
    exact h3i

theorem prologuePrefix_other {j : Fin 15} (hju : j ≠ sU) (hjp : j ≠ sP) (hji : j ≠ sIn)
    (startSym endSym : Fin sc) (L : ℕ) (S : Tapes sc) :
    runG blank (prologuePrefixActs blank startSym endSym L) S j = S j := by
  simp only [prologuePrefixActs, runG_append]
  rw [settleTrace_other hjp, settleTrace_other hju, Fifteen.pushBothActs_run,
    pushBoth_ne blank endSym hju hjp, copy2Acts_run (show sU ≠ sIn by decide),
    copyLoop2_untouched blank hji hju hjp, Fifteen.pushBothActs_run,
    pushBoth_ne blank startSym hju hjp]

/-- A single finite prologue for every input length. -/
def finitePrologue (blank startSym endSym leftSym : Fin sc) :
    Prog (ActG 15 sc) (CondG 15 sc) :=
  .seq (prologuePrefix blank startSym endSym leftSym) (restoreInputProg startSym endSym)

def finitePrologueActs (blank startSym endSym : Fin sc) (L : ℕ) : List (TAct 15 sc) :=
  prologuePrefixActs blank startSym endSym L ++ restoreInputActs L

theorem finitePrologueActs_length (blank startSym endSym : Fin sc) (L : ℕ) :
    (finitePrologueActs blank startSym endSym L).length = 8 * L + 12 := by
  simp only [finitePrologueActs, List.length_append, prologuePrefixActs_length,
    restoreInputActs_length]
  omega

theorem finitePrologue_other {j : Fin 15} (hju : j ≠ sU) (hjp : j ≠ sP) (hji : j ≠ sIn)
    (startSym endSym : Fin sc) (L : ℕ) (S : Tapes sc) :
    runG blank (finitePrologueActs blank startSym endSym L) S j = S j := by
  rw [finitePrologueActs, runG_append, restoreInput_other hju hji,
    prologuePrefix_other hju hjp hji]

theorem finitePrologue_exec {startSym endSym leftSym : Fin sc} {v : List (Fin sc)}
    (hfresh : leftSym ∉ v) (hstart : startSym ∉ v) (hend : endSym ∉ v)
    (hne : startSym ≠ endSym) (S : Tapes sc)
    (hi : Tape.SeqView blank (S sIn) (leftSym :: v) v.length)
    (hu : Tape.StackView blank (S sU) []) (hp : Tape.StackView blank (S sP) []) :
    ExecG Terminal blank (finitePrologue blank startSym endSym leftSym) S
      (finitePrologueActs blank startSym endSym v.length) ∧
    Tape.SeqView blank (runG blank (finitePrologueActs blank startSym endSym v.length) S sU)
      (startSym :: (v.reverse ++ [endSym])) 1 ∧
    Tape.SeqView blank (runG blank (finitePrologueActs blank startSym endSym v.length) S sP)
      (startSym :: (v.reverse ++ [endSym])) 1 ∧
    Tape.SeqView blank (runG blank (finitePrologueActs blank startSym endSym v.length) S sIn)
      (leftSym :: v) v.length := by
  obtain ⟨ep, hpu, hpp, hpi⟩ := prologuePrefix_exec (Terminal := Terminal)
    hfresh hstart hne S hi hu hp
  have er := restoreInput_exec (Terminal := Terminal) (by simpa using hstart)
    (by simpa using hend) hne _ hpu hpi (by simp)
  have hr := restoreInput_input _ hpu hpi (by simp)
  simp only [List.length_reverse] at er hr
  refine ⟨execG_seq ep er.1, ?_, ?_, ?_⟩
  · simpa only [finitePrologueActs, runG_append] using er.2
  · simp only [finitePrologueActs, runG_append]
    rw [restoreInput_other (show sP ≠ sU by decide) (show sP ≠ sIn by decide)]
    exact hpp
  · simpa only [finitePrologueActs, runG_append] using hr

theorem finitePrologue_spec {startSym endSym leftSym mark : Fin sc}
    {L : ℕ} {w Text : List (Fin sc)} {S : Tapes sc}
    (hpre : StageTapes.PrepPre blank mark leftSym L w Text S)
    (hstart : startSym ∉ PrepInstances.stagePat w L)
    (hend : endSym ∉ PrepInstances.stagePat w L) (hne : startSym ≠ endSym) :
    ExecG Terminal blank (finitePrologue blank startSym endSym leftSym) S
      (finitePrologueActs blank startSym endSym L) ∧
    GSPre.EncS blank startSym endSym mark (PrepInstances.stagePat w L) 0 0
      ⟨0, 0, 0, 0, 0, 0, 0⟩ ⟨0, 0, 0⟩
      (prj (runG blank (finitePrologueActs blank startSym endSym L) S)) ∧
    runG blank (finitePrologueActs blank startSym endSym L) S sT = S sT ∧
    runG blank (finitePrologueActs blank startSym endSym L) S sX2 = S sX2 ∧
    Tape.SeqView blank (runG blank (finitePrologueActs blank startSym endSym L) S sIn)
      (leftSym :: w.take L) L := by
  have hlen : (w.take L).length = L := List.length_take_of_le hpre.hle
  have hs : startSym ∉ w.take L := by simpa [PrepInstances.stagePat] using hstart
  have he : endSym ∉ w.take L := by simpa [PrepInstances.stagePat] using hend
  have hf : leftSym ∉ w.take L := fun hm => hpre.hfresh (List.mem_of_mem_take hm)
  have h := finitePrologue_exec (Terminal := Terminal) hf hs he hne S
    (by simpa [hlen] using hpre.inb) hpre.emptyU hpre.emptyP
  rw [hlen] at h
  let R := runG blank (finitePrologueActs blank startSym endSym L) S
  have hother : ∀ j : Fin 15, j ≠ sU → j ≠ sP → j ≠ sIn → R j = S j := by
    intro j hju hjp hji; exact finitePrologue_other hju hjp hji _ _ _ _
  have hpword : startSym :: ((w.take L).reverse ++ [endSym]) =
      GSPre.pword startSym endSym (PrepInstances.stagePat w L) := rfl
  rw [hpword] at h
  refine ⟨h.1, ?_, hother sT (by decide) (by decide) (by decide),
    hother sX2 (by decide) (by decide) (by decide), h.2.2.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left
  · change Tape.CounterView' blank mark (R sScr) 0
    rw [hother sScr (by decide) (by decide) (by decide)]; exact hpre.scr
  · change Tape.CounterView' blank mark (R sScr2) 0
    rw [hother sScr2 (by decide) (by decide) (by decide)]; exact hpre.scr2
  · change Tape.CounterView' blank mark (R sScr3) 0
    rw [hother sScr3 (by decide) (by decide) (by decide)]; exact hpre.scr3
  refine { v1 := h.2.2.1, v2 := h.2.1, cd := ?_, cq := ?_, ce := ?_, cp := ?_, cf := ?_, cs := ?_, cr := ?_ }
  · change Tape.CounterView' blank mark (R sC2) 0
    rw [hother sC2 (by decide) (by decide) (by decide)]; exact hpre.c2
  · change Tape.CounterView' blank mark (R sAp) 0
    rw [hother sAp (by decide) (by decide) (by decide)]; exact hpre.ap
  · change Tape.CounterView' blank mark (R sAn) 0
    rw [hother sAn (by decide) (by decide) (by decide)]; exact hpre.an
  · change Tape.CounterView' blank mark (R sC1) 0
    rw [hother sC1 (by decide) (by decide) (by decide)]; exact hpre.c1
  · change Tape.CounterView' blank mark (R sRn) 0
    rw [hother sRn (by decide) (by decide) (by decide)]; exact hpre.rn
  · change Tape.CounterView' blank mark (R sCs) 0
    rw [hother sCs (by decide) (by decide) (by decide)]; exact hpre.cs
  · change Tape.CounterView' blank mark (R sRp) 0
    rw [hother sRp (by decide) (by decide) (by decide)]; exact hpre.rp

/-- info: 'PalPeg.PrepInstance.finitePrologue_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finitePrologue_spec
/-- info: 'PalPeg.PrepInstance.finitePrologue_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finitePrologue_exec
/-- info: 'PalPeg.PrepInstance.restoreInput_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms restoreInput_exec
/-- info: 'PalPeg.PrepInstance.restoreInput_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms restoreInput_input
/-- info: 'PalPeg.PrepInstance.restoreInput_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms restoreInput_other
end PalPeg.PrepInstance
