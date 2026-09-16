import PalPeg.GalilScaffoldTopSteps3

/-!
# The fallback chain: fpp halt → marks → MarkEnd walk

After the FPP program halts (`fpp_scheduled`: MARKS = `marks w`, head 0),
`markNew` writes FIRST at cell 1 and leaves the head at cell 2. The MarkEnd
walk then finds END at cell `|w|+1` (cells `2..|w|` carry `7`/`8`) and stops
at cell `|w|` in `choose` mode. This module proves those tape facts and
composes the fpp phase with the MarkEnd phase on the unified VM.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

/-- A halted program absorbs any further enabled run. -/
theorem run_done_absorb {n : ℕ} {code : List (GalilFppWide.Instruction n)}
    (hw : ∀ i ∈ code, GalilScaffoldNextPc.WellFormed i)
    {p p' : GalilScaffoldControl.Machine n} (hd : p.done = true) {bs : List Bool}
    (h : GalilScaffoldControl.Run code p bs p') : p' = p := by
  have hidle : ∀ cs : List Bool, GalilScaffoldControl.Run code p cs p := by
    intro cs
    induction cs with
    | nil => exact .nil _
    | cons b cs ih => exact .cons _ _ _ _ _ (.idle _ _ (Or.inr hd)) ih
  exact control_run_unique hw h (hidle bs)

/-- The halted program of the fpp phase is the scheduled one. -/
theorem fpp_outcome_program (q : ℕ) (w : List (Fin 3)) (x : FppControl.State)
    (hp : x.program = ⟨fppInitial w, false⟩) (v : GalilScaffoldProgram.Config 9)
    (hsched : ∀ bs : List Bool, 1584*w.length+830 ≤ bs.count true →
      GalilScaffoldControl.Run GalilFppMarkedCode.code ⟨fppInitial w,false⟩ bs ⟨v,true⟩)
    (n : ℕ) (p : GalilScaffoldControl.Machine 9) (hd : p.done = true)
    (hr : GalilScaffoldControl.Run GalilFppMarkedCode.code x.program (List.replicate ((n+1)*q) true) p) :
    p = ⟨v, true⟩ := by
  rw [hp] at hr
  -- extend the run to at least the scheduled length
  let N := 1584*w.length+830
  have hlong := hsched (List.replicate ((n+1)*q + N) true) (by simp [N])
  rw [List.replicate_add] at hlong
  obtain ⟨y, h1, h2⟩ := control_run_split hlong
  have hy : y = p := control_run_unique marked_wellFormed h1 hr
  subst hy
  exact (run_done_absorb marked_wellFormed hd h2).symm

theorem markNew_tape (p : GalilScaffoldControl.Machine 9) (first : Fin 9) :
    GalilScaffoldTape.denote ((markNew p first).config.tapes 8) =
      Function.update (GalilScaffoldTape.denote (p.config.tapes 8)) (GalilScaffoldTape.head (p.config.tapes 8) + 1) first ∧
    GalilScaffoldTape.head ((markNew p first).config.tapes 8) = GalilScaffoldTape.head (p.config.tapes 8) + 2 := by
  constructor
  · simp only [markNew, GalilScaffoldLoading.put, Function.update_self]
    rw [GalilScaffoldTape.right_denote, GalilScaffoldTape.write_denote, GalilScaffoldTape.right_denote,
      GalilScaffoldTape.right_head]
  · simp only [markNew, GalilScaffoldLoading.put, Function.update_self]
    rw [GalilScaffoldTape.right_head, GalilScaffoldTape.write_head, GalilScaffoldTape.right_head]

theorem markNew_other (p : GalilScaffoldControl.Machine 9) (first : Fin 9) (i : Fin 9) (hi : i ≠ 8) :
    (markNew p first).config.tapes i = p.config.tapes i := by
  simp [markNew, GalilScaffoldLoading.put, hi]

/-- MARKS after the fpp phase: `marks w` with FIRST at cell 1, head at 2. -/
theorem marks_after_fpp (first : Fin 9) (w : List (Fin 3)) (v : GalilScaffoldProgram.Config 9)
    (hpos : (GalilScaffoldProgram.denote v).pos 8 = 0)
    (htape : (GalilScaffoldProgram.denote v).tape 8 = GalilFppMarkedLayout.marks w) :
    GalilScaffoldTape.denote ((markNew ⟨v,true⟩ first).config.tapes 8) =
      Function.update (GalilFppMarkedLayout.marks w) 1 first ∧
    GalilScaffoldTape.head ((markNew ⟨v,true⟩ first).config.tapes 8) = 2 := by
  obtain ⟨hd, hh⟩ := markNew_tape ⟨v,true⟩ first
  have hp0 : GalilScaffoldTape.head (v.tapes 8) = 0 := hpos
  have ht : GalilScaffoldTape.denote (v.tapes 8) = GalilFppMarkedLayout.marks w := htape
  refine ⟨?_, ?_⟩
  · rw [hd]
    show Function.update (GalilScaffoldTape.denote (v.tapes 8)) (GalilScaffoldTape.head (v.tapes 8) + 1) first = _
    rw [hp0, ht]
  · rw [hh]
    show GalilScaffoldTape.head (v.tapes 8) + 2 = 2
    rw [hp0]

/-- Cells `2 .. |w|` of the marked layout are not END; cell `|w|+1` is. -/
theorem marks_no_end (w : List (Fin 3)) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    GalilFppMarkedLayout.marks w i ≠ 5 := by
  unfold GalilFppMarkedLayout.marks
  have : i ≠ 0 := by omega
  simp only [this, ite_false, h2, ite_true]
  split <;> decide

theorem marks_end (w : List (Fin 3)) : GalilFppMarkedLayout.marks w (w.length+1) = 5 := by
  unfold GalilFppMarkedLayout.marks
  simp

/-- fpp phase followed by the MarkEnd walk, on the merged frame: from a
running prepared program the controller reaches `choose` mode with
`odd = false`, MARKS = `marks w` with FIRST at cell 1 and the head on cell
`|w|`; the fpp state otherwise unchanged; `ShiftIdle` preserved. -/
theorem fpp_then_markEnd (P : Shared) (q : ℕ) (hq : 0 < q) (first : Fin 9) (delay : ℕ)
    (c : Control) (hm : c.mode = .fpp) (s : GalilVM) (hi : ShiftIdle s)
    (hx : s.fpp.mode = .run) (w : List (Fin 3)) (hw : 1 ≤ w.length)
    (hp : s.fpp.program = ⟨fppInitial w, false⟩) :
    ∃ (n : ℕ) (y : FppControl.State),
      Steps (galilFrame P q first) delay (n+1 + (w.length-1+1)) ⟨c, s⟩
        ⟨{c with mode := .choose, odd := false}, {s with fpp := y}⟩ ∧
      GalilScaffoldTape.denote (marksTape y) = Function.update (GalilFppMarkedLayout.marks w) 1 first ∧
      GalilScaffoldTape.head (marksTape y) = w.length ∧
      y.mode = .run ∧ y.walker = s.fpp.walker ∧ y.work = s.fpp.work ∧ y.finalStage = s.fpp.finalStage ∧
      ShiftIdle {s with fpp := y} := by
  obtain ⟨v, hpc, hpos, ht7, ht8, hsched⟩ := fpp_scheduled w
  obtain ⟨n, p, y1, hs1, hprog, hmode, hwk, hwork, hfin, hd, hrun⟩ :=
    fpp_phase_vm q hq first (fun _ => True) (fun _ => True) delay c hm s hx w hp
  obtain ⟨hg1, hi1⟩ := steps_transfer_fpp P q first delay (n+1) hm hi hs1
  have hpv : p = ⟨v, true⟩ := fpp_outcome_program q w s.fpp hp v hsched n p hd hrun
  subst hpv
  obtain ⟨hden, hhead⟩ := marks_after_fpp first w v hpos ht8
  have hden1 : GalilScaffoldTape.denote (marksTape y1) = Function.update (GalilFppMarkedLayout.marks w) 1 first := by
    show GalilScaffoldTape.denote (y1.program.config.tapes 8) = _
    rw [hprog]; exact hden
  have hhead1 : GalilScaffoldTape.head (marksTape y1) = 2 := by
    show GalilScaffoldTape.head (y1.program.config.tapes 8) = 2
    rw [hprog]; exact hhead
  have hm1 : ({c with mode := .markEnd} : Control).mode = .markEnd := rfl
  have hne : ∀ j, j < w.length - 1 →
      GalilScaffoldTape.denote (marksTape ({s with fpp := y1} : GalilVM).fpp)
        (GalilScaffoldTape.head (marksTape ({s with fpp := y1} : GalilVM).fpp) + j) ≠ 5 := by
    intro j hj
    show GalilScaffoldTape.denote (marksTape y1) (GalilScaffoldTape.head (marksTape y1) + j) ≠ 5
    rw [hden1, hhead1, Function.update_of_ne (by omega)]
    exact marks_no_end w (2+j) (by omega) (by omega)
  have hend : GalilScaffoldTape.denote (marksTape ({s with fpp := y1} : GalilVM).fpp)
      (GalilScaffoldTape.head (marksTape ({s with fpp := y1} : GalilVM).fpp) + (w.length - 1)) = 5 := by
    show GalilScaffoldTape.denote (marksTape y1) (GalilScaffoldTape.head (marksTape y1) + (w.length - 1)) = 5
    rw [hden1, hhead1, Function.update_of_ne (by omega), show 2 + (w.length - 1) = w.length + 1 by omega]
    exact marks_end w
  have hpos' : 0 < GalilScaffoldTape.head (marksTape ({s with fpp := y1} : GalilVM).fpp) + (w.length - 1) := by
    show 0 < GalilScaffoldTape.head (marksTape y1) + (w.length - 1)
    rw [hhead1]; omega
  obtain ⟨y2, hs2, hsame, hhead2⟩ := markEnd_phase_vm first (fun _ => True) (fun _ => True) delay
    {c with mode := .markEnd} hm1 {s with fpp := y1} (w.length - 1) hne hend hpos'
  obtain ⟨hg2, hi2⟩ := steps_transfer_markEnd P q first delay (w.length - 1 + 1) hm1 hi1 hs2
  refine ⟨n, y2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hi2⟩
  · exact steps_trans hg1 hg2
  · rw [hsame.denote]; exact hden1
  · rw [hhead2]
    show GalilScaffoldTape.head (marksTape y1) + (w.length - 1) - 1 = w.length
    rw [hhead1]; omega
  · rw [hsame.mode]; exact hmode
  · rw [hsame.walker]; exact hwk
  · rw [hsame.work]; exact hwork
  · rw [hsame.finalStage]; exact hfin

#print axioms fpp_outcome_program
#print axioms marks_after_fpp
#print axioms marks_no_end
#print axioms fpp_then_markEnd

end PalPeg.GalilScaffoldChainInputSupply
