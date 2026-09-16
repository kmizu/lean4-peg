import PalPeg.TextFeedPrepFrames

/-! Certificates for the exact end of finite preprocessing and control
handoff into the existing worker. Residual control is normalized by the
next ordinary worker call, without an external assignment or reset. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrepHandoff
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.PrepInstance PalPeg.PatternTapes PalPeg.PatternProg
open PalPeg.PatternProg.Fifteen
open PalPeg.TextFeedControl PalPeg.TextFeedInput
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule
open PalPeg.TextFeedPrepResume PalPeg.TextFeedPrepFrames

variable {k : ℕ} {Terminal : Type}

theorem exec_live_prefix (e : Env k) (p : Prog (PrepAct k) (PrepCond k))
    (P : Fin 15 → STape (Fin k)) (tr : List (Fin 15 → Fin k × Move))
    (he : Exec (source e) e.blank p P tr) (N : ℕ) (hN : N ≤ tr.length) :
    (trace (source e) e.blank (List.replicate N none) ([p], P)).length = N := by
  have ht := congrArg List.length (he [] (List.replicate tr.length none) (by simp)).1
  simp only [List.append_nil] at ht
  have hlen : N + (tr.length - N) = tr.length := by omega
  exact (live_split e [p] P N (tr.length - N) (by simpa only [hlen] using ht)).1

theorem exec_endpoint (e : Env k) (p : Prog (PrepAct k) (PrepCond k))
    (P : Fin 15 → STape (Fin k)) (tr : List (Fin 15 → Fin k × Move))
    (he : Exec (source e) e.blank p P tr) :
    let u := runInputs (source e) e.blank (List.replicate tr.length none) ([p], P)
    u.2 = applyTrace e.blank P tr ∧
      (stepStack (evalConds (source e) (fun j => (u.2 j).focus)) u.1).2 = none := by
  obtain ⟨s', hrun, heq⟩ := (he [] (List.replicate tr.length none) (by simp)).2
  simp only [List.append_nil] at hrun
  dsimp only
  rw [hrun]
  exact ⟨rfl, by simpa only [stepStack_nil] using congrArg Prod.snd heq⟩

theorem prep_starts_with_action (e : Env k) (leftSym : Fin k) (rate : ℕ)
    (ev : PrepCond k → Bool) :
    (stepStack ev [finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate]).2 ≠ none := by
  simp only [finitePrepSetup, finitePrep, finitePrologue, prologuePrefix, Fifteen.pushBothProg,
    ACT, Prog.map, stepStack_seq, stepStack_act, ne_eq, reduceCtorEq, not_false_eq_true]

theorem prep_cost_pos (e : Env k) (leftSym : Fin k) (rate : ℕ)
    (P : Fin 15 → STape (Fin k)) (tr : List (Fin 15 → Fin k × Move))
    (he : Exec (source e) e.blank
      (finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate) P tr) : 0 < tr.length := by
  by_contra hn
  have hz : tr = [] := by
    cases tr with
    | nil => rfl
    | cons a tr => simp only [List.length_cons] at hn; omega
  subst tr
  have hh := (exec_endpoint e _ P [] he).2
  have hend : (stepStack (evalConds (source e) (fun j => (P j).focus))
      [finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate]).2 = none := by
    simpa only [List.length_nil, List.replicate_zero, runInputs_nil] using hh
  exact prep_starts_with_action e leftSym rate _ hend

/-- Finite preprocessing supplies productive prefix lengths and its
ending control fact, together with the GS/verifier representation. -/
theorem source_certificate {e : Env k} {leftSym : Fin k} {w Text : List (Fin k)} {L : ℕ}
    {S : PatternTapes.Tapes k} (rate : ℕ) (hmb : e.mark ≠ e.blank)
    (hpre : StageTapes.PrepPre e.blank e.mark leftSym L w Text S)
    (hstart : e.startSym ∉ PrepInstances.stagePat w L)
    (hend : e.endSym ∉ PrepInstances.stagePat w L) (hne : e.startSym ≠ e.endSym) :
    let p := finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate
    let d := PrepInstances.prepRes w L
    ∃ tr S', Exec (source e) e.blank p (TSg S) tr ∧
      tr.length ≤ (GSPreProg.preprocessSlope + 25 + 7 * rate) * L +
        GSPreProg.preprocessOffset + 37 + 11 * rate ∧
      (∀ N ≤ tr.length, (trace (source e) e.blank (List.replicate N none) ([p], TSg S)).length = N) ∧
      (let u := runInputs (source e) e.blank (List.replicate tr.length none) ([p], TSg S)
       u.2 = TSg S' ∧ (stepStack (evalConds (source e) (fun j => (u.2 j).focus)) u.1).2 = none) ∧
      GSVTapes.VEncodes' e.blank e.startSym e.endSym e.mark
        ((w.take L).reverse.take d.1) ((w.take L).reverse.drop d.1)
        (TextFeed.padW e.blank Text 0) rate d.2.1 d.2.2
        (toGS S', toVExt S') (⟨0, 0⟩, 0) := by
  dsimp only
  obtain ⟨tr, S', he, ht, hv, hn⟩ := finitePrepSetup_exec (Terminal := Unit) rate hmb hpre hstart hend hne
  obtain ⟨hout, hreturn⟩ := exec_endpoint e _ (TSg S) tr he
  exact ⟨tr, S', he, hn, exec_live_prefix e _ (TSg S) tr he, ⟨hout.trans ht, hreturn⟩, hv⟩

/-- Residual pure-control nodes disappear inside the next ordinary call;
handoff itself performs no tape action. -/
theorem return_control (e : Env k) (T : Fin 27 → STape (Fin k))
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (h : (stepStack (evalConds (source e) (fun j => (prepView T j).focus)) s).2 = none) :
    stepStack (fun c => taskCond e c (fun j => (T j).focus))
      (s.map TextFeedPrepResume.lift ++ r) =
      stepStack (fun c => taskCond e c (fun j => (T j).focus)) r :=
  (step_sim_map Sum.inl Sum.inl
    (evalConds (source e) (fun j => (prepView T j).focus))
    (fun c => taskCond e c (fun j => (T j).focus)) (prep_condition e T) s r).2 h

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _

attribute [local irreducible] ProgLangBank.runChunk

/-- The first ordinary worker call after preparation keeps all tapes
unchanged and advances into the mapped worker continuation. There is no
external reset of the actual task controller. -/
theorem run_handoff (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1)
    (hc0 : x.1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩)
    (s : Stack (PrepAct k) (PrepCond k))
    (hs : x.1.1.2.2.val = s.map TextFeedPrepResume.lift ++
      [(TextFeedSchedule.worker rate).map Sum.inr Sum.inr])
    (h : (stepStack (evalConds (source e) (fun j => (prepView x.2 j).focus)) s).2 = none) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    y.2 = x.2 ∧ AtBoundary (programs e) y.1.2.2.1 ∧
      y.1.1.2.2.val =
        (stepStack (fun c => TextFeedSchedule.workerCond e c
          (fun j => (TextFeedPrepare.feedView x.2 j).focus)) [TextFeedSchedule.worker rate]).1.map
          (Prog.map Sum.inr Sum.inr) := by
  let ev := fun c => taskCond e c (fun j => (x.2 j).focus)
  let wev := fun c => TextFeedSchedule.workerCond e c
    (fun j => (TextFeedPrepare.feedView x.2 j).focus)
  have ha : (stepStack wev [TextFeedSchedule.worker rate]).2 = some .idle := by
    rw [TextFeedSchedule.worker, stepStack_loop]
    rfl
  have hm : stepStack ev x.1.1.2.2.val =
      ((stepStack wev [TextFeedSchedule.worker rate]).1.map (Prog.map Sum.inr Sum.inr),
        some (.inr TextFeedSchedule.WorkerAct.idle)) := by
    rw [hs, return_control e x.2 s _ h]
    have hh := (step_sim_map (A₂ := TaskAct k) Sum.inr Sum.inr wev ev
      (fun _ => rfl) [TextFeedSchedule.worker rate] []).1 _ ha
    simpa only [List.append_nil, List.map_cons, List.map_nil, ev] using hh
  dsimp only [ev, wev] at hm
  have hsel : decode (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2 = .feed .idle := by
    simp only [TextFeedStartupSchedule.choose, if_neg hc0, hm,
      Option.getD_some, taskLabel, TextFeedSchedule.workerLabel, decode_encode]
  have hex : Exec (TextFeedStartupSchedule.interp (Terminal := Terminal) e).toInterp e.blank
      (programs e (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2) x.2 [] := by
    change Exec (shared e) e.blank (low e (decode _)) x.2 []
    rw [hsel]
    exact exec_skip x.2
  obtain ⟨ht, hb', _, _⟩ := callRun_exec (programs e)
    (fun _ => TextFeedStartupSchedule.interp (Terminal := Terminal) e)
    (choose e leftSym R rate) 48 e.blank x hb [] hex (by simp)
  refine ⟨ht, hb', ?_⟩
  simp only [TextFeedStartupSchedule.run, callRun, TextFeedStartupSchedule.choose,
    if_neg hc0, stepCtrlS_val, hm]

/-- info: 'PalPeg.TextFeedPrepHandoff.source_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_certificate

/-- info: 'PalPeg.TextFeedPrepHandoff.return_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms return_control

/-- info: 'PalPeg.TextFeedPrepHandoff.run_handoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_handoff

end PalPeg.TextFeedPrepHandoff
