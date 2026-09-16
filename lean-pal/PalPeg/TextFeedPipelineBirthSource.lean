import PalPeg.TextFeedPipelineBirthBuild
import PalPeg.HistoryRewind
import PalPeg.ClockHistoryInvariant

set_option autoImplicit false
set_option maxRecDepth 2048
namespace PalPeg.TextFeedPipelineBirthSource
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.TextFeedControl PalPeg.TextFeedInit
variable {k : ℕ}

def sourceAddr : Fin 40 := finSumFinEquiv (Sum.inl 0 : Fin 1 ⊕ Fin 39)
def targetAddr (j : Fin 39) : Fin 40 := finSumFinEquiv (Sum.inr j : Fin 1 ⊕ Fin 39)

def pack (q : Fin 3) (S : STape (Fin k)) (T : Fin 39 → STape (Fin k)) :
    SConfig (Fin 3) (Fin k) 40 :=
  ⟨q, fun j => match (finSumFinEquiv.symm j : Fin 1 ⊕ Fin 39) with
    | .inl _ => S | .inr i => T i⟩

def target (x : SConfig (Fin 3) (Fin k) 40) (j : Fin 39) := x.tape (targetAddr j)

noncomputable def stepT (e : Env k) (leftSym : Fin k) (cmd : TextFeedPipelineBirthBuild.Command k)
    (T : Fin 39 → STape (Fin k)) :=
  fun j => (T j).applyAction e.blank (TextFeedPipelineBirthBuild.vec e leftSym cmd j)

/-- Read a physical history source, initialize the 39 matcher tapes, and
freeze them on the source's blank terminator. Only three control states
are used; no input word, length, or copy-command list is supplied at runtime. -/
noncomputable def machine (e : Env k) (leftSym : Fin k) :
    StructuredMachine Unit (Fin 3) (Fin k) 40 1 where
  tapeCount_pos := by decide
  blank := e.blank
  initial := 0
  accepting := fun q => decide (q = 2)
  micro := fun q _ σ =>
    if q = 2 then (q, fun j => (σ j, .stay)) else
    let done := q ≠ 0 ∧ σ sourceAddr = e.blank
    let cmd := if q = 0 then TextFeedPipelineBirthBuild.Command.beginCopy
      else if done then .freeze else .copy (σ sourceAddr)
    (if done then 2 else 1, fun j =>
      match (finSumFinEquiv.symm j : Fin 1 ⊕ Fin 39) with
      | .inl _ => (σ j, if q = 0 ∨ done then .stay else .right)
      | .inr i => TextFeedPipelineBirthBuild.vec e leftSym cmd i)

noncomputable def run (e : Env k) (leftSym : Fin k) (n : ℕ) (x : SConfig (Fin 3) (Fin k) 40) :=
  (List.replicate n ()).foldl (machine e leftSym).sRound x

theorem run_add (e : Env k) (leftSym : Fin k) (n m : ℕ) (x : SConfig (Fin 3) (Fin k) 40) :
    run e leftSym (n + m) x = run e leftSym m (run e leftSym n x) := by
  simp only [run, List.replicate_add, List.foldl_append]

theorem begin_round (e : Env k) (leftSym : Fin k) (S : STape (Fin k)) (T : Fin 39 → STape (Fin k)) :
    (machine e leftSym).sRound (pack 0 S T) () =
      pack 1 S (stepT e leftSym .beginCopy T) := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, pack, sourceAddr, Equiv.symm_apply_apply,
    show (0 : Fin 3) ≠ 2 by decide, ↓reduceIte]
  congr 1
  funext j
  cases h : (finSumFinEquiv.symm j : Fin 1 ⊕ Fin 39)
  · rfl
  · rfl

theorem copy_round (e : Env k) (leftSym a : Fin k) (w junk : List (Fin k))
    (ha : a ≠ e.blank) (T : Fin 39 → STape (Fin k)) :
    (machine e leftSym).sRound (pack 1 (HistoryConcat.source e.blank (a :: w) junk) T) () =
      pack 1 (HistoryConcat.source e.blank w (a :: junk)) (stepT e leftSym (.copy a) T) := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, pack, sourceAddr, Equiv.symm_apply_apply,
    HistoryConcat.source, List.headD_cons, List.tail_cons, ha,
    show (1 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte,
    and_false, or_self]
  congr 1
  funext j
  cases h : (finSumFinEquiv.symm j : Fin 1 ⊕ Fin 39)
  · cases w <;> rfl
  · rfl

theorem freeze_round (e : Env k) (leftSym : Fin k) (junk : List (Fin k))
    (T : Fin 39 → STape (Fin k)) :
    (machine e leftSym).sRound (pack 1 (HistoryConcat.source e.blank [] junk) T) () =
      pack 2 (HistoryConcat.source e.blank [] junk) (stepT e leftSym .freeze T) := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, pack, sourceAddr, Equiv.symm_apply_apply,
    HistoryConcat.source, List.headD_nil, List.tail_nil,
    show (1 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte]
  congr 1
  funext j
  cases h : (finSumFinEquiv.symm j : Fin 1 ⊕ Fin 39)
  · rfl
  · rfl

theorem copy_word (e : Env k) (leftSym : Fin k) (w junk : List (Fin k))
    (hw : e.blank ∉ w) (T : Fin 39 → STape (Fin k)) :
    run e leftSym w.length (pack 1 (HistoryConcat.source e.blank w junk) T) =
      pack 1 (HistoryConcat.source e.blank [] (w.reverse ++ junk))
        (applyTrace e.blank T (w.map (fun a => TextFeedPipelineBirthBuild.vec e leftSym (.copy a)))) := by
  induction w generalizing junk T with
  | nil => rfl
  | cons a w ih =>
    have ha : a ≠ e.blank := by intro h; subst a; exact hw (by simp)
    have hw' : e.blank ∉ w := fun h => hw (by simp [h])
    change run e leftSym w.length
      ((machine e leftSym).sRound (pack 1 (HistoryConcat.source e.blank (a :: w) junk) T) ()) = _
    rw [copy_round e leftSym a w junk ha T, ih (a :: junk) hw']
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append,
      List.map_cons, applyTrace_cons]
    rfl

theorem seed_from_source (e : Env k) (leftSym : Fin k) (w junk : List (Fin k))
    (hw : e.blank ∉ w) :
    run e leftSym (w.length + 2)
      (pack 0 (HistoryConcat.source e.blank w junk) (blankBundle e.blank 39)) =
      pack 2 (HistoryConcat.source e.blank [] (w.reverse ++ junk))
        (TextFeedPipelineOutputBirth.seed e leftSym w w.length 0) := by
  change run e leftSym (w.length + 1)
    ((machine e leftSym).sRound
      (pack 0 (HistoryConcat.source e.blank w junk) (blankBundle e.blank 39)) ()) = _
  rw [begin_round, run_add, copy_word e leftSym w junk hw]
  change (machine e leftSym).sRound (pack 1 _ _) () = _
  rw [freeze_round]
  have hh : applyTrace e.blank (blankBundle e.blank 39)
      ((TextFeedPipelineBirthBuild.commands w).map (TextFeedPipelineBirthBuild.vec e leftSym)) =
      TextFeedPipelineOutputBirth.seed e leftSym w w.length 0 := by
    rw [← TextFeedPipelineBirthBuild.run_commands]
    exact TextFeedPipelineBirthBuild.build_machine e leftSym w
  apply congrArg (pack 2 (HistoryConcat.source e.blank [] (w.reverse ++ junk)))
  unfold stepT
  simpa only [TextFeedPipelineBirthBuild.commands, List.map_cons, List.map_append,
    List.map_map, Function.comp_def, List.map_nil, applyTrace_cons, applyTrace_append,
    applyTrace_nil, stepT] using hh

theorem done_round (e : Env k) (leftSym : Fin k) (S : STape (Fin k))
    (T : Fin 39 → STape (Fin k)) :
    (machine e leftSym).sRound (pack 2 S T) () = pack 2 S T := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, pack, ↓reduceIte]
  rfl

theorem done_run (e : Env k) (leftSym : Fin k) (n : ℕ) (S : STape (Fin k))
    (T : Fin 39 → STape (Fin k)) :
    run e leftSym n (pack 2 S T) = pack 2 S T := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change run e leftSym n ((machine e leftSym).sRound (pack 2 S T) ()) = _
    rw [done_round, ih]

theorem pack_blankEq (blank : Fin k) (q : Fin 3) (S U : STape (Fin k))
    (T V : Fin 39 → STape (Fin k)) (hS : STape.BlankEq blank S U)
    (hT : ∀ j, STape.BlankEq blank (T j) (V j)) :
    ConfigBlankEq blank (pack q S T) (pack q U V) := by
  refine ⟨rfl, ?_⟩
  intro j
  simp only [pack]
  cases h : (finSumFinEquiv.symm j : Fin 1 ⊕ Fin 39) with
  | inl i => exact hS
  | inr i => exact hT i

/-- This accepts the exact observational contracts supplied by the history
and workspace recyclers. Extra blank padding is never normalized externally. -/
theorem seed_padded (e : Env k) (leftSym : Fin k) (w junk : List (Fin k))
    (hw : e.blank ∉ w) (S : STape (Fin k)) (T : Fin 39 → STape (Fin k))
    (hS : STape.BlankEq e.blank S (HistoryConcat.source e.blank w junk))
    (hT : ∀ j, STape.BlankEq e.blank (T j) (STape.blankTape e.blank))
    (n : ℕ) (hn : w.length + 2 ≤ n) :
    let y := run e leftSym n (pack 0 S T)
    y.state = 2 ∧
      (∀ j, STape.BlankEq e.blank (target y j) (TextFeedPipelineOutputBirth.seed e leftSym w w.length 0 j)) ∧
      STape.BlankEq e.blank (y.tape sourceAddr) (HistoryConcat.source e.blank [] (w.reverse ++ junk)) := by
  have hr := (machine e leftSym).runFrom_blankEq (List.replicate n ())
    (pack_blankEq e.blank 0 S (HistoryConcat.source e.blank w junk) T (blankBundle e.blank 39) hS hT)
  change ConfigBlankEq e.blank (run e leftSym n (pack 0 S T))
    (run e leftSym n (pack 0 (HistoryConcat.source e.blank w junk) (blankBundle e.blank 39))) at hr
  have he : run e leftSym n (pack 0 (HistoryConcat.source e.blank w junk) (blankBundle e.blank 39)) =
      pack 2 (HistoryConcat.source e.blank [] (w.reverse ++ junk))
        (TextFeedPipelineOutputBirth.seed e leftSym w w.length 0) := by
    rw [show n = (w.length + 2) + (n - (w.length + 2)) by omega,
      run_add, seed_from_source e leftSym w junk hw, done_run]
  rw [he] at hr
  refine ⟨hr.1, ?_, ?_⟩
  · intro j
    have hh := hr.2 (targetAddr j)
    simpa only [target, pack, targetAddr, Equiv.symm_apply_apply] using hh
  · have hh := hr.2 sourceAddr
    simpa only [pack, sourceAddr, Equiv.symm_apply_apply] using hh

noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (TextFeedPipelineControl.Outer e leftSym R rate) := Classical.decEq _

noncomputable def start (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (S : STape (Fin k)) (T : Fin 39 → STape (Fin k)) (n : ℕ) :
    TextFeedPipelineOutputPrepFinish.Config e leftSym R rate :=
  ⟨((TextFeedPipelineOutput.initial e leftSym R rate, 0), 0),
    target (run e leftSym n (pack 0 S T))⟩

theorem start_blankEq (e : Env k) (leftSym : Fin k) (R rate : ℕ) (w junk : List (Fin k))
    (hw : e.blank ∉ w) (S : STape (Fin k)) (T : Fin 39 → STape (Fin k))
    (hS : STape.BlankEq e.blank S (HistoryConcat.source e.blank w junk))
    (hT : ∀ j, STape.BlankEq e.blank (T j) (STape.blankTape e.blank))
    (n : ℕ) (hn : w.length + 2 ≤ n) :
    ConfigBlankEq e.blank (start e leftSym R rate S T n)
      (TextFeedPipelineOutputBirth.start e leftSym R rate w w.length 0) :=
  ⟨rfl, (seed_padded e leftSym w junk hw S T hS hT n hn).2.1⟩

theorem future_output {Terminal : Type} (e : Env k) (leftSym : Fin k)
    (enc : Terminal → Fin k) (R rate : ℕ) (w junk : List (Fin k))
    (hw : e.blank ∉ w) (S : STape (Fin k)) (T : Fin 39 → STape (Fin k))
    (hS : STape.BlankEq e.blank S (HistoryConcat.source e.blank w junk))
    (hT : ∀ j, STape.BlankEq e.blank (T j) (STape.blankTape e.blank))
    (n : ℕ) (hn : w.length + 2 ≤ n) (input : List Terminal) :
    let M := TextFeedPipelineOutput.machine e leftSym enc R rate
    M.accepting (input.foldl M.sRound (start e leftSym R rate S T n)).state =
      M.accepting (input.foldl M.sRound (TextFeedPipelineOutputBirth.start e leftSym R rate w w.length 0)).state :=
  (TextFeedPipelineOutput.machine e leftSym enc R rate).accepting_runFrom_blankEq input
    (start_blankEq e leftSym R rate w junk hw S T hS hT n hn)

/-- The source condition is obtained from the all-blank, clock-driven
history run. The target workspace still has to satisfy its recycler contract;
the combined scheduler and shared-head restoration are separate obligations. -/
theorem seed_from_history {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (henc : ∀ a, enc a ≠ e.blank)
    (g : ℕ) (w : List Terminal) (hl : 2 ^ (g + 5) + 2 ^ (g + 5) / 8 ≤ w.length)
    (hh : w.length ≤ 2 * 2 ^ (g + 5)) (T : Fin 39 → STape (Fin k))
    (hT : ∀ j, STape.BlankEq e.blank (T j) (STape.blankTape e.blank))
    (n : ℕ) (hn : 2 ^ (g + 5) + 2 ≤ n) :
    let h := ClockHistory.history (WarmStart.view ((ClockHistoryStartup.machine e.blank enc).srun w))
    let S := h.tape (h.state.1 2)
    ∀ j, STape.BlankEq e.blank (target (run e leftSym n (pack 0 S T)) j)
      (TextFeedPipelineOutputBirth.seed e leftSym ((w.take (2 ^ (g + 5))).map enc) (2 ^ (g + 5)) 0 j) := by
  have hs := ClockHistoryInvariant.actual_window e.blank enc henc g w hl hh
  have hw := ClockHistoryInvariant.encoded_nonblank e.blank enc henc (w.take (2 ^ (g + 5)))
  have hlen : ((w.take (2 ^ (g + 5))).map enc).length = 2 ^ (g + 5) := by
    rw [List.length_map, List.length_take]
    omega
  have hb := seed_padded e leftSym ((w.take (2 ^ (g + 5))).map enc) [e.blank] hw _ T
    hs.2.2.2.1 hT n (by rw [hlen]; exact hn)
  simpa only [hlen] using hb.2.1

/-- info: 'PalPeg.TextFeedPipelineBirthSource.seed_from_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms seed_from_history

/-- info: 'PalPeg.TextFeedPipelineBirthSource.future_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms future_output

/-- info: 'PalPeg.TextFeedPipelineBirthSource.seed_padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms seed_padded

/-- info: 'PalPeg.TextFeedPipelineBirthSource.seed_from_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms seed_from_source

end PalPeg.TextFeedPipelineBirthSource
