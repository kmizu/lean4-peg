import PalPeg.TextFeedStartupRun

/-! Exact refinement of preparation instructions in the interrupted shared
task. FIFO state is immaterial: each resumed preparation call acts on the
same physical 15-tape view and advances the original continuation once. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrepResume
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.PrepInstance
open PalPeg.TextFeedControl PalPeg.TextFeedInput
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule PalPeg.TextFeedStartupSafety

variable {k : ℕ} {Terminal : Type}

def prepView (T : Fin 27 → STape (Fin k)) : Fin 15 → STape (Fin k) := fun j => T (prepSlot j)

noncomputable def source (e : Env k) : Interp Unit (PrepAct k) (PrepCond k) (Fin k) 15 :=
  prepInterp e.blank e.endSym e.mark

def lift : Prog (PrepAct k) (PrepCond k) → Prog (TaskAct k) (TaskCond k) :=
  Prog.map Sum.inl Sum.inl

noncomputable def sourceStep (e : Env k) (s : Stack (PrepAct k) (PrepCond k))
    (P : Fin 15 → STape (Fin k)) := microStep (source e) e.blank none (s, P)

theorem prep_condition (e : Env k) (T : Fin 27 → STape (Fin k)) (c : PrepCond k) :
    taskCond e (.inl c) (fun j => (T j).focus) =
      evalConds (source e) (fun j => (prepView T j).focus) c := rfl

theorem source_step_control (e : Env k) (T : Fin 27 → STape (Fin k))
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k)) (a : PrepAct k)
    (ha : (stepStack (evalConds (source e) (fun j => (prepView T j).focus)) s).2 = some a) :
    stepStack (fun c => taskCond e c (fun j => (T j).focus)) (s.map lift ++ r) =
      ((sourceStep e s (prepView T)).1.map lift ++ r, some (.inl a)) :=
  (step_sim_map Sum.inl Sum.inl
    (evalConds (source e) (fun j => (prepView T j).focus))
    (fun c => taskCond e c (fun j => (T j).focus))
    (prep_condition e T) s r).1 a ha

theorem source_step_tapes (e : Env k) (s : Stack (PrepAct k) (PrepCond k))
    (P : Fin 15 → STape (Fin k)) (a : PrepAct k)
    (ha : (stepStack (evalConds (source e) (fun j => (P j).focus)) s).2 = some a) :
    applyTrace e.blank P [actVec (prepInterp (Terminal := Terminal) e.blank e.endSym e.mark) a P] =
      (sourceStep e s P).2 := by
  simp only [sourceStep, microStep, ha, applyTrace, actVec]
  cases a <;> rfl

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _

attribute [local irreducible] ProgLangBank.runChunk

/-- A real 49-clock call advances precisely one source preparation step.
No completed-preprocessing initial control, queue invariant, or tape reset
is assumed. The suffix is the existing worker continuation. -/
theorem run_step_equiv (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1)
    (hc0 : x.1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩)
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (hs : stepStack (fun c => taskCond e c (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (fun c => taskCond e c (fun j => (x.2 j).focus)) (s.map lift ++ r)) (a : PrepAct k)
    (ha : (stepStack (evalConds (source e) (fun j => (prepView x.2 j).focus)) s).2 = some a) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    y.2 = extend prepSlot (sourceStep e s (prepView x.2)).2 x.2 ∧
      AtBoundary (programs e) y.1.2.2.1 ∧
      y.1.1.2.2.val = (sourceStep e s (prepView x.2)).1.map lift ++ r := by
  have hm : stepStack (fun c => taskCond e c (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      ((sourceStep e s (prepView x.2)).1.map lift ++ r, some (.inl a)) := by
    rw [hs]
    exact source_step_control e x.2 s r a ha
  have hsel : decode (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2 = .prep a := by
    simp only [TextFeedStartupSchedule.choose, if_neg hc0, hm, Option.getD_some,
      taskLabel, decode_encode]
  obtain ⟨tr, he, hn, ht⟩ := prep_exec (Terminal := Terminal) e a (prepView x.2) x.2
  have hself : extend prepSlot (prepView x.2) x.2 = x.2 := extend_restrict prepSlot x.2
  rw [hself] at he ht
  rw [source_step_tapes e s (prepView x.2) a ha] at ht
  have hex : Exec (TextFeedStartupSchedule.interp (Terminal := Terminal) e).toInterp e.blank
      (programs e (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2) x.2 tr := by
    change Exec (shared e) e.blank (low e (decode _)) x.2 tr
    rw [hsel]
    exact he
  obtain ⟨hyt, hby, _, _⟩ := callRun_exec (programs e)
    (fun _ => TextFeedStartupSchedule.interp (Terminal := Terminal) e)
    (choose e leftSym R rate) 48 e.blank x hb tr hex (by omega)
  refine ⟨hyt.trans ht, hby, ?_⟩
  simp only [TextFeedStartupSchedule.run, callRun, TextFeedStartupSchedule.choose,
    if_neg hc0, stepCtrlS_val, hm]

theorem run_step (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1)
    (hc0 : x.1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩)
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (hs : x.1.1.2.2.val = s.map lift ++ r) (a : PrepAct k)
    (ha : (stepStack (evalConds (source e) (fun j => (prepView x.2 j).focus)) s).2 = some a) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    y.2 = extend prepSlot (sourceStep e s (prepView x.2)).2 x.2 ∧
      AtBoundary (programs e) y.1.2.2.1 ∧
      y.1.1.2.2.val = (sourceStep e s (prepView x.2)).1.map lift ++ r :=
  run_step_equiv e leftSym R rate x hb hc0 s r (congrArg _ hs) a ha

/-- The initial sequential task needs no separate control-reset action:
the first source action expands `seq` and retains the worker as its suffix. -/
theorem run_start (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1)
    (hc0 : x.1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩)
    (hs : x.1.1.2.2.val = [task e leftSym rate]) (a : PrepAct k)
    (ha : (stepStack (evalConds (source e) (fun j => (prepView x.2 j).focus))
      [finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate]).2 = some a) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    let u := sourceStep e [finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate] (prepView x.2)
    y.2 = extend prepSlot u.2 x.2 ∧ AtBoundary (programs e) y.1.2.2.1 ∧
      y.1.1.2.2.val = u.1.map lift ++ [(TextFeedSchedule.worker rate).map Sum.inr Sum.inr] := by
  apply run_step_equiv e leftSym R rate x hb hc0 _ _ ?_ a ha
  rw [hs]
  exact stepStack_seq _ _ _ []

theorem prepView_extend (P : Fin 15 → STape (Fin k)) (T : Fin 27 → STape (Fin k)) :
    prepView (extend prepSlot P T) = P := by
  funext j
  exact extend_ι prepSlot P T j

theorem extend_twice (P Q : Fin 15 → STape (Fin k)) (T : Fin 27 → STape (Fin k)) :
    extend prepSlot P (extend prepSlot Q T) = extend prepSlot P T := by
  funext j
  cases hp : proj prepSlot j <;> simp only [extend, hp]

/-- A whole worker window runs a productive source prefix, with the
original continuation and all non-preparation tapes preserved exactly. -/
theorem run_prefix (e : Env k) (leftSym : Fin k) (R rate N : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1)
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (P : Fin 15 → STape (Fin k)) (hv : prepView x.2 = P)
    (hs : x.1.1.2.2.val = s.map lift ++ r)
    (htrace : (trace (source e) e.blank (List.replicate N none) (s, P)).length = N)
    (hpos : N ≠ 0 → 0 < x.1.1.1.val) (hlen : x.1.1.1.val + N ≤ R + 1) :
    let y := (run (Terminal := Terminal) e leftSym R rate)^[N] x
    let u := runInputs (source e) e.blank (List.replicate N none) (s, P)
    y.2 = extend prepSlot u.2 x.2 ∧ AtBoundary (programs e) y.1.2.2.1 ∧
      y.1.1.2.2.val = u.1.map lift ++ r := by
  induction N generalizing x s P with
  | zero =>
    refine ⟨?_, hb, hs⟩
    change x.2 = extend prepSlot P x.2
    rw [← hv]
    exact (extend_restrict prepSlot x.2).symm
  | succ N ih =>
    have hsome : ∃ a, (stepStack (evalConds (source e) (fun j => (P j).focus)) s).2 = some a := by
      cases hw : (stepStack (evalConds (source e) (fun j => (P j).focus)) s).2 with
      | some a => exact ⟨a, rfl⟩
      | none =>
        have hle := trace_length_le (source e) e.blank (List.replicate N none) (sourceStep e s P)
        rw [List.replicate_succ, trace_cons, hw] at htrace
        simp only [List.nil_append, List.length_replicate] at htrace hle
        change (trace (source e) e.blank (List.replicate N none) (sourceStep e s P)).length = N + 1 at htrace
        omega
    obtain ⟨a, ha⟩ := hsome
    have hc0 : x.1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩ := by
      have hh := hpos (Nat.succ_ne_zero N)
      intro hz
      rw [hz] at hh
      simp at hh
    have ha' : (stepStack (evalConds (source e) (fun j => (prepView x.2 j).focus)) s).2 = some a := by
      rw [hv]
      exact ha
    obtain ⟨ht, hb', hs'⟩ := run_step (Terminal := Terminal) e leftSym R rate x hb hc0 s r hs a ha'
    rw [hv] at ht hs'
    have hv' : prepView (run (Terminal := Terminal) e leftSym R rate x).2 = (sourceStep e s P).2 := by
      rw [ht, prepView_extend]
    have htrace' : (trace (source e) e.blank (List.replicate N none) (sourceStep e s P)).length = N := by
      rw [List.replicate_succ, trace_cons, ha] at htrace
      simpa only [List.singleton_append, List.length_cons, Nat.succ.injEq, sourceStep] using htrace
    have hnext (hn : N ≠ 0) : x.1.1.1.val + 1 < R + 1 := by omega
    have hp' : N ≠ 0 → 0 < (run (Terminal := Terminal) e leftSym R rate x).1.1.1.val := by
      intro hn
      rw [run_counter]
      simp only [nextPhase, dif_pos (hnext hn)]
      omega
    have hl' : (run (Terminal := Terminal) e leftSym R rate x).1.1.1.val + N ≤ R + 1 := by
      by_cases hn : N = 0
      · have hlt := (run (Terminal := Terminal) e leftSym R rate x).1.1.1.isLt
        omega
      · rw [run_counter]
        simp only [nextPhase, dif_pos (hnext hn)]
        omega
    obtain ⟨ht', hb'', hs''⟩ := ih (run (Terminal := Terminal) e leftSym R rate x) hb'
      (sourceStep e s P).1 (sourceStep e s P).2 hv' hs' htrace' hp' hl'
    rw [ht, extend_twice] at ht'
    simpa only [Function.iterate_succ_apply, List.replicate_succ, runInputs_cons,
      sourceStep, Prod.mk.eta] using And.intro ht' (And.intro hb'' hs'')

/-- info: 'PalPeg.TextFeedPrepResume.run_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_step

/-- info: 'PalPeg.TextFeedPrepResume.run_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_prefix

end PalPeg.TextFeedPrepResume
