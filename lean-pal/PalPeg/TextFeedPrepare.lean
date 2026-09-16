import PalPeg.TextFeedInit
import PalPeg.GSPreprocessProg76

/-! Co-located finite preprocessing, scanner setup, and queue bootstrap.
The 27 tapes are 11 private queue tapes, 15 preprocessing/verifier tapes,
and one input register. The 20-tape feeder is a fixed view, not a copy. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrepare
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedInit
open PalPeg.TextFeedRefine PalPeg.PatternTapes PalPeg.PatternProg
open PalPeg.PatternProg.Fifteen PalPeg.PrepInstance

variable {k : ℕ} {Terminal : Type}

abbrev Act (k : ℕ) := ((RTQueueProg.ActQ k ⊕ Mode) ⊕ PrepAct k) ⊕ Empty
abbrev Cond (k : ℕ) := ((RTQueueProg.CondQ k ⊕ Mode) ⊕ PrepCond k) ⊕ Fin k

noncomputable def interp (e : Env k) : Interp Terminal (Act k) (Cond k) (Fin k) 27 :=
  Interp.sum (Interp.sum (IC Terminal e.code) (prepInterp e.blank e.endSym e.mark))
    (IReg (Terminal := Terminal) (k := k))

def prepareProg (e : Env k) (leftSym : Fin k) (rate : ℕ) : Prog (Act k) (Cond k) :=
  (Prog.seq ((queueBoot e.blank e.mark).map Sum.inl Sum.inl)
    ((finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate).map Sum.inr Sum.inr)).map
      Sum.inl Sum.inl

def before (e : Env k) (S : PatternTapes.Tapes k) (old : Fin k) : Fin 27 → STape (Fin k) :=
  Fin.append (Fin.append (Fin.append (blankBundle e.blank 10) (blankBundle e.blank 1)) (TSg S))
    (TextFeedInput.cell old)

def after (e : Env k) (S : PatternTapes.Tapes k) (old : Fin k) : Fin 27 → STape (Fin k) :=
  Fin.append (Fin.append (RTQueueControl.tapes e.code (initQT e.blank e.mark) initialMode) (TSg S))
    (TextFeedInput.cell old)

def feedSlot : Fin 20 ↪ Fin 27 where
  toFun j := if h : j.val < 19 then ⟨j.val, by omega⟩ else ⟨26, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg Fin.val h
    by_cases hi : i.val < 19 <;> by_cases hj : j.val < 19 <;>
      simp [hi, hj] at hh <;> omega

def feedView (T : Fin 27 → STape (Fin k)) : Fin 20 → STape (Fin k) := fun j => T (feedSlot j)

theorem feedView_after (e : Env k) (S : PatternTapes.Tapes k) (old : Fin k) :
    feedView (after e S old) =
      rtapes e (initQT e.blank e.mark) initialMode (GSProg.TS (toGS S)) old := by
  funext j
  fin_cases j <;> rfl

/-- The fixed program computes the decomposition on tape, sets up its GS
scanner, and creates the private queue from blank tapes. Its output already
satisfies the feeder's initial Sim on a fixed injection of physical tapes. -/
theorem prepare_spec {e : Env k} {leftSym : Fin k} {w Text : List (Fin k)} {L : ℕ}
    {S : PatternTapes.Tapes k} (R rate : ℕ) (old : Fin k) (hmb : e.mark ≠ e.blank)
    (hpre : StageTapes.PrepPre e.blank e.mark leftSym L w Text S)
    (hstart : e.startSym ∉ PrepInstances.stagePat w L)
    (hend : e.endSym ∉ PrepInstances.stagePat w L) (hne : e.startSym ≠ e.endSym) :
    let d := PrepInstances.prepRes w L
    ∃ tr S', Exec (interp (Terminal := Terminal) e) e.blank (prepareProg e leftSym rate)
      (before e S old) tr ∧
      applyTrace e.blank (before e S old) tr = after e S' old ∧
      tr.length ≤ (GSPreProg.preprocessSlope + 25 + 7 * rate) * L +
        GSPreProg.preprocessOffset + 49 + 11 * rate ∧
      GSVTapes.VEncodes' e.blank e.startSym e.endSym e.mark
        ((w.take L).reverse.take d.1) ((w.take L).reverse.drop d.1)
        (TextFeed.padW e.blank Text 0) rate d.2.1 d.2.2
        (toGS S', toVExt S') (⟨0, 0⟩, 0) ∧
      Sim e ((w.take L).reverse.drop d.1) Text R rate d.2.1 d.2.2 0
        (seedModel e (toGS S')) .loop
        (initialCtrl e R rate, feedView (applyTrace e.blank (before e S old) tr)) old := by
  dsimp only
  obtain ⟨p, S', hep, htp, hv, hp⟩ := finitePrepSetup_exec (Terminal := Terminal) rate hmb
    hpre hstart hend hne
  obtain ⟨q, heq, hq, htq⟩ := queueBoot_exec (Terminal := Terminal) e
  let Q := Fin.append (blankBundle e.blank 10) (blankBundle e.blank 1)
  let P := TSg S
  let q' := q.map (extendVec (Fin.castAddEmb 15) (Fin.append Q P))
  let p' := p.map (extendVec (Fin.natAddEmb 11) (Fin.append (applyTrace e.blank Q q) P))
  let tr₀ := q' ++ p'
  have he₀ := exec_sum_seq heq hep
  have hq' := applyTrace_extend (Fin.castAddEmb 15) e.blank (Fin.append Q P) q Q
  simp only [extend_castAdd_append] at hq'
  have hp' := applyTrace_extend (Fin.natAddEmb 11) e.blank
    (Fin.append (applyTrace e.blank Q q) P) p P
  simp only [extend_natAdd_append] at hp'
  have ht₀ : applyTrace e.blank (Fin.append Q P) tr₀ =
      Fin.append (RTQueueControl.tapes e.code (initQT e.blank e.mark) initialMode) (TSg S') := by
    change applyTrace e.blank (Fin.append Q P) (q' ++ p') = _
    rw [applyTrace_append]
    change applyTrace e.blank (applyTrace e.blank (Fin.append Q P)
      (q.map (extendVec (Fin.castAddEmb 15) (Fin.append Q P))))
      (p.map (extendVec (Fin.natAddEmb 11) (Fin.append (applyTrace e.blank Q q) P))) = _
    rw [hq', hp']
    exact congrArg₂ Fin.append htq htp
  have he := exec_sum_inl (I2 := IReg (Terminal := Terminal) (k := k)) he₀ (before e S old)
  rw [before, extend_castAdd_append] at he
  have ht := applyTrace_extend (Fin.castAddEmb 1) e.blank (before e S old) tr₀ (Fin.append Q P)
  simp only [before, extend_castAdd_append] at ht
  have hfinal : applyTrace e.blank (before e S old)
      (tr₀.map (extendVec (Fin.castAddEmb 1) (before e S old))) = after e S' old := by
    apply ht.trans
    rw [ht₀]
    rfl
  refine ⟨tr₀.map (extendVec (Fin.castAddEmb 1) (before e S old)), S', he, hfinal, ?_, hv, ?_⟩
  · simp only [List.length_map, tr₀, q', p', List.length_append, hq]
    omega
  · rw [hfinal, feedView_after]
    exact seed_sim old hv.scan

/-- info: 'PalPeg.TextFeedPrepare.prepare_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepare_spec

end PalPeg.TextFeedPrepare
