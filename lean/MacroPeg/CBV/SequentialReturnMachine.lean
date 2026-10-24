import MacroPeg.CBV.SequentialReturnScanMachine
import MacroPeg.CBV.SequentialSeqReturnMachine
import MacroPeg.CBV.SequentialAltReturnMachine
import MacroPeg.CBV.SequentialNotReturnMachine
import MacroPeg.CBV.SequentialStarReturnMachine
import MacroPeg.CBV.SequentialArgHeadReturnMachine
import MacroPeg.CBV.SequentialArgConsReturnMachine
import MacroPeg.CBV.SequentialCallReturnMachine

/-! One fixed, input-driven program implementing all nonterminal returns. -/
namespace Shallot.MacroPeg.CBV.SequentialReturnMachine
open Complexity Complexity.BinaryWord SequentialStack SequentialStackCodec SequentialStackCodecBound CBVtoCBN
open SequentialStackBinary
open SequentialFieldFetch
open SequentialFrontRead (frontSpace)

def continuations (ns : List CompileNode) : Nat → LProg 11
  | 0 => SequentialSeqReturnMachine.program
  | 1 => SequentialAltReturnMachine.program
  | 2 => SequentialNotReturnMachine.program
  | 3 => SequentialStarReturnMachine.program ns
  | 4 => SequentialArgHeadReturnMachine.program
  | 5 => SequentialArgConsReturnMachine.program
  | 6 => SequentialCallReturnMachine.program
  | _ => .halt false

def program (ns : List CompileNode) : LProg 11 := SequentialReturnScanMachine.program (continuations ns)

noncomputable def space (g : MGrammar) (x : List Char) (e : MExp) (c : Config) : Nat :=
  SequentialNotReturnMachine.space g x e c + SequentialSeqReturnMachine.space g x e c +
  SequentialAltReturnMachine.space g x e c + SequentialStarReturnMachine.space g x e c +
  SequentialArgHeadReturnMachine.space g x e c

def slope (A H : Nat) : Nat := 57 +
  (SequentialSeqReturn.cellBound A + SequentialSeqReturn.stepBound A) +
  (SequentialAltReturn.cellBound A + SequentialAltReturn.stepBound A) +
  (SequentialStarReturn.cellBound A + SequentialStarReturn.stepBound A H) +
  (SequentialArgHeadReturn.cellBound A + SequentialArgHeadReturn.stepBound A)
def offset (A H : Nat) : Nat := 2559 +
  (SequentialSeqReturn.cellBound A + SequentialSeqReturn.stepBound A * (SequentialSeqReturn.stepBound A + 1) + 2) +
  (SequentialAltReturn.cellBound A + SequentialAltReturn.stepBound A * (SequentialAltReturn.stepBound A + 1) + 2) +
  (SequentialStarReturn.cellBound A + SequentialStarReturn.stepBound A H * (SequentialStarReturn.stepBound A H + 1) + 2) +
  (SequentialArgHeadReturn.cellBound A + SequentialArgHeadReturn.stepBound A * (SequentialArgHeadReturn.stepBound A + 1) + 2)

theorem space_eq (g : MGrammar) (x : List Char) (e : MExp) (c : Config) :
    space g x e c = 5 * frontSpace g x e c +
      slope (SequentialStackPayload.arityBudget g) (SequentialStackPool.exprPool (compilerNodes g e)).length * numberBound g x e +
      offset (SequentialStackPayload.arityBudget g) (SequentialStackPool.exprPool (compilerNodes g e)).length := by
  unfold space
  rw [SequentialNotReturnMachine.space_eq]
  unfold SequentialSeqReturnMachine.space SequentialAltReturnMachine.space
    SequentialStarReturnMachine.space SequentialArgHeadReturnMachine.space
  rw [SequentialSeqReturn.scratchSpace_linear, SequentialAltReturn.scratchSpace_linear,
    SequentialStarReturn.scratchSpace_linear, SequentialArgHeadReturn.scratchSpace_linear]
  simp only [slope,offset,Nat.add_mul]
  omega

theorem space_bound (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) :
    let A := SequentialStackPayload.arityBudget g
    let H := (SequentialStackPool.exprPool (compilerNodes g e)).length
    let C := slope A H
    let D := offset A H
    space g x e c ≤
      (5 * ((13 + 6 * A + 4) * (numberCoefficient g e + 1) + 8) +
        (C * numberCoefficient g e + D)) * (x.length + 1) +
      5 * ((cellCoefficient g e * (x.length + 1)) *
        ((x.length + 1).log2 + (numberCoefficient g e).log2 + 2)) := by
  dsimp only
  let C := slope (SequentialStackPayload.arityBudget g) (SequentialStackPool.exprPool (compilerNodes g e)).length
  let D := offset (SequentialStackPayload.arityBudget g) (SequentialStackPool.exprPool (compilerNodes g e)).length
  have hf := SequentialFrontRead.frontSpace_bound g x e c h
  have hn := numberBound_linear g x e
  have hm := Nat.mul_le_mul_left C hn
  have hc : D ≤ D * (x.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hs : C * numberBound g x e + D ≤ (C * numberCoefficient g e + D) * (x.length + 1) := by
    have heq : (C * numberCoefficient g e + D) * (x.length + 1) =
        C * (numberCoefficient g e * (x.length + 1)) + D * (x.length + 1) := by
      rw [Nat.add_mul,Nat.mul_assoc]
    rw [heq]
    omega
  let F := (13 + 6 * SequentialStackPayload.arityBudget g + 4) * (numberCoefficient g e + 1) + 8
  let L := (cellCoefficient g e * (x.length + 1)) *
    ((x.length + 1).log2 + (numberCoefficient g e).log2 + 2)
  have hf' : frontSpace g x e c ≤ F * (x.length+1) + L := hf
  have hh := Nat.add_le_add (Nat.mul_le_mul_left 5 hf') hs
  have heq : (5 * F + (C * numberCoefficient g e + D)) * (x.length+1) + 5 * L =
      5 * (F * (x.length+1) + L) + (C * numberCoefficient g e + D) * (x.length+1) := by
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc]
    omega
  rw [space_eq]
  change 5 * frontSpace g x e c + C * numberBound g x e + D ≤
    (5 * F + (C * numberCoefficient g e + D)) * (x.length+1) + 5 * L
  rw [heq]
  omega

theorem front_le_space (g : MGrammar) (x : List Char) (e : MExp) (c : Config) :
    frontSpace g x e c ≤ space g x e c := by
  have hh : frontSpace g x e c ≤ SequentialNotReturnMachine.space g x e c := by
    unfold SequentialNotReturnMachine.space; omega
  unfold space; omega

theorem selected_runs (g : MGrammar) (x : List Char) (e : MExp) (v : SequentialStack.Value)
    (f : SequentialStack.Frame) (K : List SequentialStack.Frame) (next : Config)
    (h : SequentialStack.Runs g x (initial g x e) ⟨.value v,f :: K⟩)
    (op : LProg 11) (B : Nat)
    (hr : ∃ T, Complexity.Runs (LenOK B) op
      (start (width g x e) (encode (compilerNodes g e) ⟨.value v,f :: K⟩) [] [] 0 [])
      (start (width g x e) (encode (compilerNodes g e) next) [] [] 0 []) T)
    (hB : B ≤ space g x e ⟨.value v,f :: K⟩)
    (hop : continuations (compilerNodes g e) (SequentialReturnScan.frameKey f) = op) :
    ∃ T, Complexity.Runs (LenOK (space g x e ⟨.value v,f :: K⟩)) (program (compilerNodes g e))
      (start (width g x e) (encode (compilerNodes g e) ⟨.value v,f :: K⟩) [] [] 0 [])
      (start (width g x e) (encode (compilerNodes g e) next) [] [] 0 []) T := by
  obtain ⟨T,hr⟩ := hr
  apply SequentialReturnScanMachine.selected_runs g x e v f K h (continuations (compilerNodes g e)) _
    (front_le_space g x e _) (T := T)
  rw [hop]
  exact hr.weaken (fun _ hh i => Nat.le_trans (hh i) hB)

theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (v : SequentialStack.Value)
    (f : SequentialStack.Frame) (K : List SequentialStack.Frame) (next : Config)
    (h : SequentialStack.Runs g x (initial g x e) ⟨.value v,f :: K⟩)
    (hs : step g x ⟨.value v,f :: K⟩ = some next) :
    ∃ T, Complexity.Runs (LenOK (space g x e ⟨.value v,f :: K⟩)) (program (compilerNodes g e))
      (start (width g x e) (encode (compilerNodes g e) ⟨.value v,f :: K⟩) [] [] 0 [])
      (start (width g x e) (encode (compilerNodes g e) next) [] [] 0 []) T := by
  cases v with
  | expr r =>
    cases f with
    | seq m E b =>
      have hd : next = SequentialSeqReturnMachine.next r m E b K :=
        Option.some.inj (hs.symm.trans (SequentialSeqReturn.original_step g x r m E b K))
      subst next
      obtain ⟨T,hr⟩ := SequentialSeqReturnMachine.transition_runs g x e r m E b K h
      exact selected_runs g x e (.expr r) (.seq m E b) K _ h _ _ ⟨T,hr⟩
        (by simp only [SequentialSeqReturnMachine.before]; unfold space; omega) rfl
    | alt m E b p =>
      have hd : next = SequentialAltReturnMachine.next r m p E b K :=
        Option.some.inj (hs.symm.trans (SequentialAltReturn.original_step g x r m p E b K))
      subst next
      obtain ⟨T,hr⟩ := SequentialAltReturnMachine.transition_runs g x e r m p E b K h
      exact selected_runs g x e (.expr r) (.alt m E b p) K _ h _ _ ⟨T,hr⟩
        (by simp only [SequentialAltReturnMachine.before]; unfold space; omega) rfl
    | notP p =>
      have hd : next = SequentialNotReturnMachine.next r p K :=
        Option.some.inj (hs.symm.trans (SequentialNotReturn.original_step g x r p K))
      subst next
      obtain ⟨T,hr⟩ := SequentialNotReturnMachine.transition_runs g x e r p K h
      exact selected_runs g x e (.expr r) (.notP p) K _ h _ _ ⟨T,hr⟩
        (by simp only [SequentialNotReturnMachine.before]; unfold space; omega) rfl
    | star m E a p =>
      have hd : next = SequentialStarReturnMachine.next r m p E a K :=
        Option.some.inj (hs.symm.trans (SequentialStarDispatch.original_step g x r m p E a K))
      subst next
      obtain ⟨T,hr⟩ := SequentialStarReturnMachine.transition_runs g x e r m p E a K h
      exact selected_runs g x e (.expr r) (.star m E a p) K _ h _ _ ⟨T,hr⟩
        (by simp only [SequentialStarReturnMachine.before]; unfold space; omega) rfl
    | argHead m E es p =>
      have hd : next = SequentialArgHeadReturnMachine.next r m p E es K :=
        Option.some.inj (hs.symm.trans (SequentialArgHeadDispatch.original_step g x r m p E es K))
      subst next
      obtain ⟨T,hr⟩ := SequentialArgHeadReturnMachine.transition_runs g x e r m p E es K h
      exact selected_runs g x e (.expr r) (.argHead m E es p) K _ h _ _ ⟨T,hr⟩
        (by simp only [SequentialArgHeadReturnMachine.before]; unfold space; omega) rfl
    | argCons _ | call _ _ => simp [step] at hs
  | args r =>
    cases f with
    | argCons span =>
      obtain ⟨a,b⟩ := span
      have hd : next = SequentialArgConsReturnMachine.next r a b K :=
        Option.some.inj (hs.symm.trans (SequentialArgConsReturn.original_step g x r a b K))
      subst next
      obtain ⟨T,hr⟩ := SequentialArgConsReturnMachine.transition_runs g x e r a b K h
      exact selected_runs g x e (.args r) (.argCons (a,b)) K _ h _ _ ⟨T,hr⟩
        (by simp only [SequentialArgConsReturnMachine.before, SequentialArgConsReturnMachine.space]; unfold space; omega) rfl
    | call m i =>
      have hd : next = SequentialCallReturnMachine.next r m i K :=
        Option.some.inj (hs.symm.trans (SequentialCallReturn.original_step g x r m i K))
      subst next
      obtain ⟨T,hr⟩ := SequentialCallReturnMachine.transition_runs g x e r m i K h
      exact selected_runs g x e (.args r) (.call m i) K _ h _ _ ⟨T,hr⟩
        (by simp only [SequentialCallReturnMachine.before, SequentialCallReturnMachine.space]; unfold space; omega) rfl
    | seq _ _ _ | alt _ _ _ _ | notP _ | star _ _ _ _ | argHead _ _ _ _ => simp [step] at hs

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (v : SequentialStack.Value)
    (f : SequentialStack.Frame) (K : List SequentialStack.Frame) (next : Config)
    (h : SequentialStack.Runs g x (initial g x e) ⟨.value v,f :: K⟩)
    (hs : step g x ⟨.value v,f :: K⟩ = some next) (τ : Tapes 11)
    (hτ : Rep (start (width g x e) (encode (compilerNodes g e) ⟨.value v,f :: K⟩) [] [] 0 []) τ) :
    ∃ t τ', Exec (TFits (space g x e ⟨.value v,f :: K⟩)) (program (compilerNodes g e)).compile τ t (.cont τ') ∧
      Rep (start (width g x e) (encode (compilerNodes g e) next) [] [] 0 []) τ' := by
  obtain ⟨_,hr⟩ := transition_runs g x e v f K next h hs
  obtain ⟨t,τ',_,he,hr'⟩ := runs_tape hr τ hτ
  exact ⟨t,τ',he,hr'⟩

end Shallot.MacroPeg.CBV.SequentialReturnMachine
