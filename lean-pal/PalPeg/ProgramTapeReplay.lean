import PalPeg.HistoryConcat
import PalPeg.ProgramMachine

set_option autoImplicit false
namespace PalPeg.Program.TapeReplay
open PegSeparation.RealTimeTM
variable {Terminal Q Γ : Type} [Fintype Q] [DecidableEq Q]
  [Fintype Γ] [DecidableEq Γ] {t B : ℕ}

def source (blank : Γ) (w junk : List Γ) : STape Γ := ⟨junk, w.headD blank, w.tail⟩

def sourceAddr : Fin (1 + t) := finSumFinEquiv (.inl 0 : Fin 1 ⊕ Fin t)
def targetAddr (j : Fin t) : Fin (1 + t) := finSumFinEquiv (.inr j : Fin 1 ⊕ Fin t)
def pack (p : Fin B) (S : STape Γ) (x : SConfig Q Γ t) : SConfig (Q × Fin B) Γ (1 + t) :=
  ⟨(x.state, p), fun j => match (finSumFinEquiv.symm j : Fin 1 ⊕ Fin t) with
    | .inl _ => S | .inr i => x.tape i⟩

/-- Execute a machine's ordinary input round from a physical source.
Only phase zero reads and advances the source. Interior ticks forward none,
even if the source has just reached its blank terminator. -/
def machine (M : StructuredMachine Terminal Q Γ t B) (hB : 0 < B)
    (decode : Γ → Terminal) : StructuredMachine Unit (Q × Fin B) Γ (1 + t) 1 where
  tapeCount_pos := by omega
  blank := M.blank
  initial := (M.initial, ⟨0, hB⟩)
  accepting := fun q => M.accepting q.1
  micro := fun q _ σ =>
    if q.2.val = 0 ∧ σ sourceAddr = M.blank then (q, fun j => (σ j, .stay)) else
    let d := M.micro q.1 (if q.2.val = 0 then some (decode (σ sourceAddr)) else none)
      (fun i => σ (targetAddr i))
    ((d.1, nextPhase q.2), fun j => match (finSumFinEquiv.symm j : Fin 1 ⊕ Fin t) with
      | .inl _ => (σ j, if q.2.val = 0 then .right else .stay)
      | .inr i => d.2 i)

def run (M : StructuredMachine Terminal Q Γ t B) (hB : 0 < B)
    (decode : Γ → Terminal) (n : ℕ) (x : SConfig (Q × Fin B) Γ (1 + t)) :=
  (List.replicate n ()).foldl (machine M hB decode).sRound x

theorem first_tick (M : StructuredMachine Terminal Q Γ t B) (hB : 0 < B)
    (decode : Γ → Terminal) (a : Γ) (w junk : List Γ) (ha : a ≠ M.blank)
    (x : SConfig Q Γ t) :
    (machine M hB decode).sRound (pack ⟨0, hB⟩ (source M.blank (a :: w) junk) x) () =
      pack (nextPhase ⟨0, hB⟩) (source M.blank w (a :: junk))
        (M.sMicroStep x (some (decode a))) := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, pack, sourceAddr, targetAddr,
    Equiv.symm_apply_apply, source, List.headD_cons, List.tail_cons,
    ha, and_false, ↓reduceIte]
  congr 1
  funext j
  cases h : (finSumFinEquiv.symm j : Fin 1 ⊕ Fin t)
  · cases w <;> rfl
  · rfl

theorem inner_tick (M : StructuredMachine Terminal Q Γ t B) (hB : 0 < B)
    (decode : Γ → Terminal) (p : Fin B) (hp : p.val ≠ 0)
    (S : STape Γ) (x : SConfig Q Γ t) :
    (machine M hB decode).sRound (pack p S x) () =
      pack (nextPhase p) S (M.sMicroStep x none) := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, pack, sourceAddr, targetAddr,
    Equiv.symm_apply_apply, hp, false_and, ↓reduceIte]
  congr 1
  funext j
  cases h : (finSumFinEquiv.symm j : Fin 1 ⊕ Fin t) <;> rfl

theorem tail_run (M : StructuredMachine Terminal Q Γ t B) (hB : 0 < B)
    (decode : Γ → Terminal) (n : ℕ) (p : Fin B) (hp : 0 < p.val)
    (hn : p.val + n ≤ B) (S : STape Γ) (x : SConfig Q Γ t) :
    run M hB decode n (pack p S x) =
      pack (nextPhase^[n] p) S ((List.replicate n none).foldl M.sMicroStep x) := by
  induction n generalizing p x with
  | zero => rfl
  | succ n ih =>
    change run M hB decode n ((machine M hB decode).sRound (pack p S x) ()) = _
    rw [inner_tick M hB decode p (by omega)]
    cases n with
    | zero => rfl
    | succ n =>
      have hnext : p.val + 1 < B := by omega
      have hv : (nextPhase p).val = p.val + 1 := by simp only [nextPhase, dif_pos hnext]
      rw [ih _ (by rw [hv]; omega) (by rw [hv]; omega)]
      rfl

theorem input_round (M : StructuredMachine Terminal Q Γ t B) (hB : 0 < B)
    (decode : Γ → Terminal) (a : Γ) (w junk : List Γ) (ha : a ≠ M.blank)
    (x : SConfig Q Γ t) :
    run M hB decode B (pack ⟨0, hB⟩ (source M.blank (a :: w) junk) x) =
      pack ⟨0, hB⟩ (source M.blank w (a :: junk)) (M.sRound x (decode a)) := by
  have hlen : B = (B - 1) + 1 := by omega
  conv_lhs => arg 4; rw [hlen]
  change run M hB decode (B - 1)
    ((machine M hB decode).sRound (pack ⟨0, hB⟩ (source M.blank (a :: w) junk) x) ()) = _
  rw [first_tick M hB decode a w junk ha]
  by_cases hone : B = 1
  · subst B
    rfl
  have hp : (nextPhase (⟨0, hB⟩ : Fin B)).val = 1 := by
    simp only [nextPhase, dif_pos (show 0 + 1 < B by omega)]
  rw [tail_run M hB decode (B - 1) _ (by rw [hp]; omega) (by rw [hp]; omega)]
  have hc : nextPhase^[B - 1] (nextPhase (⟨0, hB⟩ : Fin B)) = ⟨0, hB⟩ := by
    rw [← Function.iterate_succ_apply, show (B - 1).succ = B by omega]
    exact nextPhase_iterate_round hB
  rw [hc]
  rfl

theorem run_add (M : StructuredMachine Terminal Q Γ t B) (hB : 0 < B)
    (decode : Γ → Terminal) (n m : ℕ) (x : SConfig (Q × Fin B) Γ (1 + t)) :
    run M hB decode (n + m) x = run M hB decode m (run M hB decode n x) := by
  simp only [run, List.replicate_add, List.foldl_append]

/-- Replay all stored symbols through precisely the machine's usual input
rounds. The word is proof data only; the finite machine reads its tape. -/
theorem word (M : StructuredMachine Terminal Q Γ t B) (hB : 0 < B)
    (decode : Γ → Terminal) (w junk : List Γ) (hw : M.blank ∉ w)
    (x : SConfig Q Γ t) :
    run M hB decode (w.length * B) (pack ⟨0, hB⟩ (source M.blank w junk) x) =
      pack ⟨0, hB⟩ (source M.blank [] (w.reverse ++ junk))
        ((w.map decode).foldl M.sRound x) := by
  induction w generalizing junk x with
  | nil => simp [run]
  | cons a w ih =>
    have ha : a ≠ M.blank := by intro h; subst a; exact hw (by simp)
    have hw' : M.blank ∉ w := fun h => hw (by simp [h])
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm (w.length * B) B, run_add,
      input_round M hB decode a w junk ha, ih (a :: junk) hw']
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append,
      List.map_cons, List.foldl_cons]

theorem empty_tick (M : StructuredMachine Terminal Q Γ t B) (hB : 0 < B)
    (decode : Γ → Terminal) (junk : List Γ) (x : SConfig Q Γ t) :
    (machine M hB decode).sRound (pack ⟨0, hB⟩ (source M.blank [] junk) x) () =
      pack ⟨0, hB⟩ (source M.blank [] junk) x := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, pack, sourceAddr,
    Equiv.symm_apply_apply, source, List.headD_nil, List.tail_nil, ↓reduceIte]
  rfl

theorem empty_run (M : StructuredMachine Terminal Q Γ t B) (hB : 0 < B)
    (decode : Γ → Terminal) (n : ℕ) (junk : List Γ) (x : SConfig Q Γ t) :
    run M hB decode n (pack ⟨0, hB⟩ (source M.blank [] junk) x) =
      pack ⟨0, hB⟩ (source M.blank [] junk) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change run M hB decode n ((machine M hB decode).sRound _ ()) = _
    rw [empty_tick, ih]

/-- An injective source encoding with a left inverse replays the original
input word, not a modified or repeated external input. -/
theorem encoded_word (M : StructuredMachine Terminal Q Γ t B) (hB : 0 < B)
    (enc : Terminal → Γ) (decode : Γ → Terminal)
    (hdec : ∀ a, decode (enc a) = a) (henc : ∀ a, enc a ≠ M.blank)
    (w : List Terminal) (junk : List Γ) (x : SConfig Q Γ t)
    (n : ℕ) (hn : w.length * B ≤ n) :
    run M hB decode n (pack ⟨0, hB⟩ (source M.blank (w.map enc) junk) x) =
      pack ⟨0, hB⟩ (source M.blank [] ((w.map enc).reverse ++ junk))
        (w.foldl M.sRound x) := by
  have hw : M.blank ∉ w.map enc := by
    intro h
    obtain ⟨a, _, ha⟩ := List.mem_map.mp h
    exact henc a ha
  have hmap : (w.map enc).map decode = w := by
    simp [List.map_map, Function.comp_def, hdec]
  rw [show n = w.length * B + (n - w.length * B) by omega, run_add]
  have hr := word M hB decode (w.map enc) junk hw x
  simp only [List.length_map, hmap] at hr
  rw [hr, empty_run]

/-- info: 'PalPeg.Program.TapeReplay.encoded_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms encoded_word

/-- info: 'PalPeg.Program.TapeReplay.word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms word

end PalPeg.Program.TapeReplay
