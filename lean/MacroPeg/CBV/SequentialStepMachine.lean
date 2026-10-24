import MacroPeg.CBV.SequentialStepScanMachine
import MacroPeg.CBV.SequentialAtomMachine
import MacroPeg.CBV.SequentialReturnMachine
import MacroPeg.CBV.SequentialArgsEntryMachine
import MacroPeg.CBV.SequentialQueryEntryMachine
import MacroPeg.CBV.SequentialStructuralEntryMachine
import MacroPeg.CBV.SequentialCallEntryMachine

/-! One input-preserving machine for every nonterminal stack transition. The
terminal continuation is explicit, so termination/acceptance can be composed
without changing any of the transition proofs. -/
namespace Shallot.MacroPeg.CBV.SequentialStepMachine
open Complexity Complexity.BinaryWord SequentialStack SequentialStackCodec SequentialStackCodecBound CBVtoCBN
open SequentialInputHost (extend old old_runs)
open SequentialStackBinary
open SequentialFrontRead (frontSpace)

def continuations (ns : List CompileNode) (g : MGrammar) (terminal : LProg 20) : Nat → LProg 20
  | 0 => SequentialAtomMachine.program ns
  | 1 => (SequentialStructuralEntryMachine.program ns).rename old
  | 2 => (SequentialCallEntryMachine.program ns g).rename old
  | 3 => SequentialArgsEntryMachine.program.rename old
  | 4 => (SequentialQueryEntryMachine.program ns g).rename old
  | 5 => (SequentialReturnMachine.program ns).rename old
  | 6 => terminal
  | _ => .halt false

def program (ns : List CompileNode) (g : MGrammar) (terminal : LProg 20) : LProg 20 :=
  SequentialStepScanMachine.program ns (continuations ns g terminal)

noncomputable def state (g : MGrammar) (x : List Char) (e : MExp) (c : Config) : Lists 20 :=
  extend (SequentialFieldFetch.start (SequentialStackBinary.width g x e) (encode (compilerNodes g e) c) [] [] 0 [])
    (Complexity.encS (SequentialInputRead.codes x))

noncomputable def space (g : MGrammar) (x : List Char) (e : MExp) (c : Config) : Nat :=
  frontSpace g x e c + SequentialAtomMachine.space g x e c +
    SequentialStructuralEntryMachine.space g x e c + SequentialCallEntryMachine.space g x e c +
    SequentialArgsEntryMachine.space g x e c + SequentialQueryEntryMachine.space g x e c +
    SequentialReturnMachine.space g x e c + SequentialInputRead.space x.length

private theorem input_size (g : MGrammar) (x : List Char) (e : MExp) (c : Config) :
    (Complexity.encS (SequentialInputRead.codes x)).length+2 ≤ space g x e c := by
  have hh := SequentialInputRead.encoded_length x
  unfold space SequentialInputRead.space
  omega

private theorem lift_runs (g : MGrammar) (x : List Char) (e : MExp) (c d : Config)
    (p : LProg 11) {B T : Nat}
    (hr : Complexity.Runs (LenOK B) p
      (SequentialFieldFetch.start (SequentialStackBinary.width g x e) (encode (compilerNodes g e) c) [] [] 0 [])
      (SequentialFieldFetch.start (SequentialStackBinary.width g x e) (encode (compilerNodes g e) d) [] [] 0 []) T)
    (hB : B ≤ space g x e c) :
    Complexity.Runs (LenOK (space g x e c)) (p.rename old) (state g x e c) (state g x e d) T :=
  old_runs _ _ _ _ (hr.weaken (fun _ hh i => Nat.le_trans (hh i) hB)) (input_size g x e c)

private theorem atom_case (g : MGrammar) (x : List Char) (e : MExp) (m p : Nat) (E : CaptureEnv)
    (src : MExp) (hatom : SequentialAtomCodec.Atomic src) (K : List SequentialStack.Frame) (d : Config)
    (h : SequentialStack.Runs g x (initial g x e) ⟨.expr m E src p,K⟩)
    (hs : step g x ⟨.expr m E src p,K⟩ = some d) :
    ∃ T, Complexity.Runs (LenOK (space g x e ⟨.expr m E src p,K⟩)) (SequentialAtomMachine.program (compilerNodes g e))
      (state g x e ⟨.expr m E src p,K⟩) (state g x e d) T := by
  have hd : d=SequentialAtomMachine.after x p E src K :=
    Option.some.inj (hs.symm.trans (SequentialAtomCodec.original_step g x m p E src hatom K))
  subst d
  obtain ⟨T,hr⟩ := SequentialAtomMachine.transition_runs g x e m p E src hatom K h
  exact ⟨T,hr.weaken (fun _ hh i => Nat.le_trans (hh i) (by
    change SequentialAtomMachine.space g x e ⟨.expr m E src p,K⟩ ≤ space g x e ⟨.expr m E src p,K⟩
    unfold space
    omega))⟩

private theorem structural_case (g : MGrammar) (x : List Char) (e : MExp) (mode : SequentialFrameBuild.Mode)
    (m p : Nat) (E : CaptureEnv) (a b : MExp) (K : List SequentialStack.Frame) (d : Config)
    (h : SequentialStack.Runs g x (initial g x e) (SequentialStructuralEntryMachine.before mode m p E a b K))
    (hs : step g x (SequentialStructuralEntryMachine.before mode m p E a b K) = some d) :
    ∃ T, Complexity.Runs (LenOK (space g x e (SequentialStructuralEntryMachine.before mode m p E a b K)))
      ((SequentialStructuralEntryMachine.program (compilerNodes g e)).rename old)
      (state g x e (SequentialStructuralEntryMachine.before mode m p E a b K)) (state g x e d) T := by
  have hd : d=SequentialStructuralEntryMachine.next mode m p E a b K :=
    Option.some.inj (hs.symm.trans (SequentialStructuralEntry.original_step g x mode m p E a b K))
  subst d
  obtain ⟨T,hr⟩ := SequentialStructuralEntryMachine.transition_runs g x e mode m p E a b K h
  exact ⟨T,lift_runs g x e _ _ _ hr (by unfold space; omega)⟩

theorem component_runs (g : MGrammar) (x : List Char) (e : MExp) (c d : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) (hs : step g x c = some d) (terminal : LProg 20) :
    ∃ T, Complexity.Runs (LenOK (space g x e c))
      (continuations (compilerNodes g e) g terminal (SequentialStepScan.key c))
      (state g x e c) (state g x e d) T := by
  obtain ⟨task,K⟩ := c
  cases task with
  | expr m E src p =>
    cases src with
    | seq a b => exact structural_case g x e .seq m p E a b K d h hs
    | alt a b => exact structural_case g x e .alt m p E a b K d h hs
    | notP a => exact structural_case g x e .notP m p E a a K d h hs
    | star a => exact structural_case g x e .star m p E a a K d h hs
    | call i es =>
      have hd : d=SequentialCallEntryMachine.next g m p i E es K :=
        Option.some.inj (hs.symm.trans (SequentialCallEntry.original_step g x i es m p E K))
      subst d
      obtain ⟨T,hr⟩ := SequentialCallEntryMachine.transition_runs g x e m p i E es K h
      exact ⟨T,lift_runs g x e _ _ _ hr (by simp only [SequentialCallEntryMachine.before]; unfold space; omega)⟩
    | eps | any | chr _ | range _ _ | lit _ | param _ | dbg _ | lam _ _ | callParam _ _ | invoke _ _ _ =>
      exact atom_case g x e _ _ _ _ (by trivial) _ _ h hs
  | args m E es p =>
    have hd : d=SequentialArgsEntryMachine.next m p E es K :=
      Option.some.inj (hs.symm.trans (SequentialArgsEntry.original_step g x m p E es K))
    subst d
    obtain ⟨T,hr⟩ := SequentialArgsEntryMachine.transition_runs g x e m p E es K h
    exact ⟨T,lift_runs g x e _ _ _ hr (by simp only [SequentialArgsEntryMachine.before]; unfold space; omega)⟩
  | query m i E p =>
    have hp : p ≤ x.length := by
      obtain ⟨kind,ht,hK⟩ := SequentialStackPayload.reachable_typed g x e _ h
      cases ht with | query _ _ _ _ _ _ hp => exact hp
    have hd : d=SequentialQueryEntryMachine.next g m i p E K :=
      Option.some.inj (hs.symm.trans (SequentialQueryEntry.original_step g x m i p E K hp))
    subst d
    obtain ⟨T,hr⟩ := SequentialQueryEntryMachine.transition_runs g x e m i p E K h
    exact ⟨T,lift_runs g x e _ _ _ hr (by simp only [SequentialQueryEntryMachine.before]; unfold space; omega)⟩
  | value v =>
    cases K with
    | nil => simp [step] at hs
    | cons f K =>
      obtain ⟨T,hr⟩ := SequentialReturnMachine.transition_runs g x e v f K d h hs
      exact ⟨T,lift_runs g x e _ _ _ hr (by unfold space; omega)⟩

theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (c d : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) (hs : step g x c = some d) (terminal : LProg 20) :
    ∃ T, Complexity.Runs (LenOK (space g x e c)) (program (compilerNodes g e) g terminal)
      (state g x e c) (state g x e d) T := by
  obtain ⟨T,hr⟩ := component_runs g x e c d h hs terminal
  exact SequentialStepScanMachine.selected_runs g x e c h (continuations (compilerNodes g e) g terminal)
    (Complexity.encS (SequentialInputRead.codes x)) (state g x e d) (by unfold space; omega)
    (input_size g x e c) hr

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (c d : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) (hs : step g x c = some d)
    (terminal : LProg 20) (τ : Tapes 20) (hτ : Rep (state g x e c) τ) :
    ∃ t τ', Exec (TFits (space g x e c)) (program (compilerNodes g e) g terminal).compile τ t (.cont τ') ∧
      Rep (state g x e d) τ' := by
  obtain ⟨_,hr⟩ := transition_runs g x e c d h hs terminal
  obtain ⟨t,τ',_,he,hr'⟩ := runs_tape hr τ hτ
  exact ⟨t,τ',he,hr'⟩

noncomputable def slope (g : MGrammar) (e : MExp) : Nat :=
  let A := SequentialStackPayload.arityBudget g
  let H := (SequentialStackPool.exprPool (compilerNodes g e)).length
  SequentialStructuralEntryMachine.slope A H+SequentialCallEntryMachine.slope A g.rules.length H+
    SequentialArgsEntryMachine.slope A+SequentialQueryEntryMachine.slope A g.rules.length H+
    SequentialReturnMachine.slope A H

noncomputable def offset (g : MGrammar) (e : MExp) : Nat :=
  let A := SequentialStackPayload.arityBudget g
  let H := (SequentialStackPool.exprPool (compilerNodes g e)).length
  SequentialStructuralEntryMachine.offset A H+SequentialCallEntryMachine.offset A g.rules.length H+
    SequentialArgsEntryMachine.offset A+SequentialQueryEntryMachine.offset A g.rules.length H+
    SequentialReturnMachine.offset A H

theorem space_eq (g : MGrammar) (e : MExp) :
    ∃ a b d, ∀ x c, space g x e c = 11*frontSpace g x e c+a*x.length+b*numberBound g x e+d := by
  obtain ⟨a,b,d,ha⟩ := SequentialAtomMachine.space_eq g e
  refine ⟨a+(2^32+2),b+slope g e,d+offset g e+3,?_⟩
  intro x c
  rw [space,ha,SequentialStructuralEntryMachine.space_eq,SequentialCallEntryMachine.space_eq,
    SequentialArgsEntryMachine.space_eq,SequentialQueryEntryMachine.space_eq,SequentialReturnMachine.space_eq]
  simp only [slope,offset,SequentialInputRead.space,Nat.add_mul]
  omega

theorem space_bound (g : MGrammar) (e : MExp) :
    ∃ C, ∀ x c, SequentialStack.Runs g x (initial g x e) c →
      space g x e c ≤ C*(x.length+1)+11*((cellCoefficient g e*(x.length+1))*
        ((x.length+1).log2+(numberCoefficient g e).log2+2)) := by
  obtain ⟨a,b,d,heq⟩ := space_eq g e
  let F := (13+6*SequentialStackPayload.arityBudget g+4)*(numberCoefficient g e+1)+8
  refine ⟨11*F+(a+b*numberCoefficient g e+d),?_⟩
  intro x c hc
  let L := (cellCoefficient g e*(x.length+1))*((x.length+1).log2+(numberCoefficient g e).log2+2)
  have hf : frontSpace g x e c ≤ F*(x.length+1)+L := SequentialFrontRead.frontSpace_bound g x e c hc
  have hn := numberBound_linear g x e
  have hb := Nat.mul_le_mul_left b hn
  have ha : a*x.length ≤ a*(x.length+1) := Nat.mul_le_mul_left a (by omega)
  have hd : d ≤ d*(x.length+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hnum : a*x.length+b*numberBound g x e+d ≤ (a+b*numberCoefficient g e+d)*(x.length+1) := by
    rw [Nat.add_mul,Nat.add_mul,Nat.mul_assoc]
    omega
  have hf11 := Nat.mul_le_mul_left 11 hf
  rw [heq]
  change 11*frontSpace g x e c+a*x.length+b*numberBound g x e+d ≤
    (11*F+(a+b*numberCoefficient g e+d))*(x.length+1)+11*L
  rw [Nat.add_mul]
  rw [Nat.mul_add,← Nat.mul_assoc] at hf11
  omega

end Shallot.MacroPeg.CBV.SequentialStepMachine
