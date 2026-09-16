import PalPeg.ReplayLoop

set_option autoImplicit false
namespace PalPeg.ReplayLoopReplay
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ReplayLoop
variable {Terminal Q : Type} [Fintype Q] [DecidableEq Q] {k t B : ℕ}

def lift (roles : Fin 4 ≃ Fin 4) (F : Fin 4 → STape (Fin k))
    (x : SConfig (Q × Fin B) (Fin k) (1 + t)) : SConfig (Control Q B) (Fin k) (4 + t) :=
  ⟨(x.state.1, roles, .inr x.state.2), fun j =>
    match (finSumFinEquiv.symm j : Fin 4 ⊕ Fin t) with
    | .inl i => if i = roles 2 then x.tape TapeReplay.sourceAddr else F i
    | .inr i => x.tape (TapeReplay.targetAddr i)⟩

theorem read_view (roles : Fin 4 ≃ Fin 4) (F : Fin 4 → STape (Fin k))
    (x : SConfig (Q × Fin B) (Fin k) (1 + t)) :
    (fun j => match (finSumFinEquiv.symm j : Fin 1 ⊕ Fin t) with
      | .inl _ => ((lift roles F x).tape (buf (roles 2))).focus
      | .inr i => ((lift roles F x).tape (dataAddr i)).focus) =
    (fun j => (x.tape j).focus) := by
  funext j
  have hj := (finSumFinEquiv : Fin 1 ⊕ Fin t ≃ Fin (1 + t)).apply_symm_apply j
  cases h : (finSumFinEquiv.symm j : Fin 1 ⊕ Fin t) with
  | inl a =>
    have ha : a = 0 := Subsingleton.elim _ _
    rw [h, ha] at hj
    rw [← hj]
    simp only [lift, buf, TapeReplay.sourceAddr, Equiv.symm_apply_apply, ↓reduceIte]
  | inr i =>
    rw [h] at hj
    rw [← hj]
    simp only [lift, dataAddr, TapeReplay.targetAddr, Equiv.symm_apply_apply]

/-- Before the source terminates, one actual loop tick is precisely one
tape-replay tick, and every other buffer is unchanged. -/
theorem tick_lift (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4) (F : Fin 4 → STape (Fin k))
    (x : SConfig (Q × Fin B) (Fin k) (1 + t))
    (h : ¬ (x.state.2.val = 0 ∧ (x.tape TapeReplay.sourceAddr).focus = M.blank)) :
    (worker M hB decode).sMicroStep (lift roles F x) none =
      lift roles F ((TapeReplay.machine M hB decode).sRound x ()) := by
  have hv := read_view roles F x
  simp only [lift, buf, dataAddr, Equiv.symm_apply_apply, ↓reduceIte] at hv
  have hd := congrArg ((TapeReplay.machine M hB decode).micro x.state (some ())) hv
  simp only [StructuredMachine.sMicroStep, worker, lift, buf, dataAddr,
    Equiv.symm_apply_apply, ↓reduceIte, h]
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep]
  simp only [Prod.mk.eta]
  congr 1
  · exact congrArg (fun d => (d.1.1, roles, (Sum.inr d.1.2 : (Fin 3 → Fin 3) ⊕ Fin B))) hd
  · funext j
    cases hj : (finSumFinEquiv.symm j : Fin 4 ⊕ Fin t) with
    | inl i =>
      by_cases hi : i = roles 2
      · simp only [hi, ↓reduceIte]
        exact congrArg (fun d => (x.tape TapeReplay.sourceAddr).applyAction M.blank
          (d.2 TapeReplay.sourceAddr)) hd
      · simp only [hi, ↓reduceIte]
        rfl
    | inr i =>
      exact congrArg (fun d => (x.tape (TapeReplay.targetAddr i)).applyAction M.blank
        (d.2 (TapeReplay.targetAddr i))) hd

def run (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (decode : Fin k → Terminal) (n : ℕ) (x : SConfig (Control Q B) (Fin k) (4 + t)) :=
  (List.replicate n none).foldl (worker M hB decode).sMicroStep x

theorem run_lift (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4) (F : Fin 4 → STape (Fin k))
    (n : ℕ) (x : SConfig (Q × Fin B) (Fin k) (1 + t))
    (h : ∀ i, i < n →
      ¬ ((TapeReplay.run M hB decode i x).state.2.val = 0 ∧
        ((TapeReplay.run M hB decode i x).tape TapeReplay.sourceAddr).focus = M.blank)) :
    run M hB decode n (lift roles F x) = lift roles F (TapeReplay.run M hB decode n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change run M hB decode n ((worker M hB decode).sMicroStep (lift roles F x) none) = _
    rw [tick_lift M hB decode roles F x (h 0 (by omega)), ih]
    · rfl
    · intro i hi
      exact h (i + 1) (by omega)

theorem stopped (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (decode : Fin k → Terminal) (n : ℕ) (x : SConfig (Q × Fin B) (Fin k) (1 + t))
    (h : x.state.2.val = 0 ∧ (x.tape TapeReplay.sourceAddr).focus = M.blank) :
    TapeReplay.run M hB decode n x = x := by
  have ht : (TapeReplay.machine M hB decode).sRound x () = x := by
    simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
      Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
      StructuredMachine.sMicroStep, TapeReplay.machine, h.1, h.2, ↓reduceIte]
    rfl
  induction n with
  | zero => rfl
  | succ n ih =>
    change TapeReplay.run M hB decode n ((TapeReplay.machine M hB decode).sRound x ()) = _
    rw [ht, ih]

/-- Once standalone replay reaches its terminator, the actual loop
reaches the same matcher/tape result and automatically rotates buffers.
No assumption about earlier replay ticks is required by the caller. -/
theorem handoff (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4) (F : Fin 4 → STape (Fin k))
    (n : ℕ) (x : SConfig (Q × Fin B) (Fin k) (1 + t))
    (h : (TapeReplay.run M hB decode n x).state.2.val = 0 ∧
      ((TapeReplay.run M hB decode n x).tape TapeReplay.sourceAddr).focus = M.blank) :
    ∃ d, d ≤ n + 1 ∧ run M hB decode d (lift roles F x) =
      ⟨((TapeReplay.run M hB decode n x).state.1, rotate.trans roles, .inl (fun _ => 0)),
        (lift roles F (TapeReplay.run M hB decode n x)).tape⟩ := by
  let P := fun i => (TapeReplay.run M hB decode i x).state.2.val = 0 ∧
    ((TapeReplay.run M hB decode i x).tape TapeReplay.sourceAddr).focus = M.blank
  have hex : ∃ i, P i := ⟨n, h⟩
  let d := Nat.find hex
  have hd : P d := Nat.find_spec hex
  have hn : d ≤ n := Nat.find_min' hex h
  have hp : ∀ i, i < d → ¬ P i := fun i hi => Nat.find_min hex hi
  have he : TapeReplay.run M hB decode n x = TapeReplay.run M hB decode d x := by
    rw [show n = d + (n - d) by omega, TapeReplay.run_add]
    exact stopped M hB decode _ _ hd
  refine ⟨d + 1, by omega, ?_⟩
  have hr : run M hB decode (d + 1) (lift roles F x) =
      (worker M hB decode).sMicroStep (run M hB decode d (lift roles F x)) none := by
    simp only [run, List.replicate_succ', List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [hr, run_lift M hB decode roles F d x hp, he]
  simp only [StructuredMachine.sMicroStep, worker, lift, buf, Equiv.symm_apply_apply,
    ↓reduceIte, show (TapeReplay.run M hB decode d x).state.2.val = 0 from hd.1,
    show ((TapeReplay.run M hB decode d x).tape TapeReplay.sourceAddr).focus = M.blank from hd.2]
  rfl

theorem batch_handoff (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal)
    (hdec : ∀ a, decode (enc a) = a) (henc : ∀ a, enc a ≠ M.blank)
    (roles : Fin 4 ≃ Fin 4) (F : Fin 4 → STape (Fin k))
    (w : List Terminal) (junk : List (Fin k)) (x : SConfig Q (Fin k) t) :
    ∃ d, d ≤ w.length * B + 1 ∧
      run M hB decode d (lift roles F
        (TapeReplay.pack ⟨0, hB⟩ (TapeReplay.source M.blank (w.map enc) junk) x)) =
      ⟨((w.foldl M.sRound x).state, rotate.trans roles, .inl (fun _ => 0)),
        (lift roles F (TapeReplay.pack ⟨0, hB⟩
          (TapeReplay.source M.blank [] ((w.map enc).reverse ++ junk))
          (w.foldl M.sRound x))).tape⟩ := by
  let z := TapeReplay.pack ⟨0, hB⟩ (TapeReplay.source M.blank (w.map enc) junk) x
  have hw := TapeReplay.encoded_word M hB enc decode hdec henc w junk x
    (w.length * B) (by omega)
  have hh : (TapeReplay.run M hB decode (w.length * B) z).state.2.val = 0 ∧
      ((TapeReplay.run M hB decode (w.length * B) z).tape TapeReplay.sourceAddr).focus = M.blank := by
    rw [hw]
    exact ⟨rfl, by simp only [TapeReplay.pack, TapeReplay.sourceAddr,
      Equiv.symm_apply_apply, TapeReplay.source, List.headD_nil]⟩
  have hr := handoff M hB decode roles F (w.length * B) z hh
  dsimp only [z] at hr
  rw [hw] at hr
  exact hr

/-- info: 'PalPeg.ReplayLoopReplay.batch_handoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms batch_handoff

/-- info: 'PalPeg.ReplayLoopReplay.handoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms handoff

/-- info: 'PalPeg.ReplayLoopReplay.run_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_lift

end PalPeg.ReplayLoopReplay
