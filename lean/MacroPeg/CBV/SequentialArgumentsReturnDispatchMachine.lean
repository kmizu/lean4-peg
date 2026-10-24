import MacroPeg.CBV.SequentialExpressionReturnDispatchMachine

/-! Select argument-value returns while accounting for the extra captured-word
count in successful result headers. All inspected fields are restored. -/
namespace Shallot.MacroPeg.CBV.SequentialArgumentsReturnDispatchMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialReturnControlMachine
open SequentialSharedWords (Config CaptureEnv ArgsResult Runs initial)
open SequentialSharedStateCodec (encode writeFrames)
open SequentialCaptureCopyMachine (withInput)
open SequentialArgConsReturnPackedMachine (resultTag extraFields)
open SequentialScopeWordMachine (resultFields)

def headerLength (r : ArgsResult) : Nat := 2+(resultFields (.args r)).length

def ruleProgram (rules saved : Nat) : LProg 8 :=
  SequentialTagDispatchMachine.program 2 1 saved rules SequentialCallPackedMachine.program

def branches (rules saved tag : Nat) : LProg 8 :=
  if tag=5 then SequentialArgConsReturnPackedMachine.program
  else if tag=6 then ruleProgram rules (saved+1)
  else if tag=7 then SequentialScopePackedMachine.program
  else skipP 2

def frames (rules saved : Nat) : LProg 8 := SequentialReturnFields.program saved (branches rules saved)

def program (rules : Nat) : LProg 8 := dispatch 2 1 3 (frames rules 4) (frames rules 4) (frames rules 5)

theorem rule_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (i : Nat) (r : ArgsResult) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (SequentialCallPackedMachine.before m E i r K))
    (hs : SequentialSharedWords.step g x (SequentialCallPackedMachine.before m E i r K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (ruleProgram g.rules.length (headerLength r+1))
      (withInput (encode (CBVtoCBN.compilerNodes g e) (SequentialCallPackedMachine.before m E i r K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let L := withInput (encode ns (SequentialCallPackedMachine.before m E i r K)) x
  let target := withInput (encode ns next) x
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  have he := Option.some.inj (hs.symm.trans (SequentialCallPackedMachine.actual_step g x m E i r K))
  obtain ⟨T,ht⟩ := SequentialCallPackedMachine.transition_runs g x e m E i r K h
  rw [← he] at ht
  have hb : Complexity.Runs (LenOK B) (SequentialCallPackedMachine.program i) L target T := ht
  have hL : LenOK B L := by obtain ⟨t,ht,hx⟩ := hb; exact hx.q_start
  have hi : i < g.rules.length := (SequentialSharedStateBound.reachable_fits g x e _ h).2 (.call i)
    (by simp [SequentialCallPackedMachine.before])
  let header := [E.length,K.length+1] ++ resultFields (.args r) ++ [6]
  let C := SequentialCursorEdit.blocks (writeFrames ns K).control ++ [0]
  have hsrc : L 2=C ++ unary i ++ blocks header := by
    change withInput (encode ns (SequentialReturnFields.before m E (.args r) (.call i) K)) x 2 = _
    rw [SequentialReturnFields.before_control]
    change blocks (writeFrames ns K).control ++ blocks [6,i] ++
      blocks ([E.length,K.length+1] ++ resultFields (.args r)) = _
    simp only [C,header,blocks_append,blocks_cons,show blocks []=[] from rfl,List.nil_append,List.append_assoc]
  obtain ⟨U,hu⟩ := SequentialTagDispatchMachine.dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    header g.rules.length i (Nat.le_of_lt hi) C SequentialCallPackedMachine.program L target hsrc
    (by rw [lastSym_append]; rfl) rfl hL hb
  have hlen : header.length=headerLength r+1 := by simp [header,headerLength,List.length_append]; omega
  rw [hlen] at hu
  exact ⟨U,hu⟩

theorem branch_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (r : ArgsResult) (f : SequentialSharedWords.Frame) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (SequentialReturnFields.before m E (.args r) f K))
    (hs : SequentialSharedWords.step g x (SequentialReturnFields.before m E (.args r) f K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (branches g.rules.length (headerLength r) (SequentialReturnFields.frameTag f))
      (withInput (encode (CBVtoCBN.compilerNodes g e) (SequentialReturnFields.before m E (.args r) f K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  cases f with
  | call i => exact rule_runs g x e m E i r K next h hs
  | argCons w =>
    have he := Option.some.inj (hs.symm.trans (SequentialArgConsReturnPackedMachine.actual_step g x m E w r K))
    rw [he]
    exact SequentialArgConsReturnPackedMachine.transition_runs g x e m E w r K h
  | scope S =>
    have he := Option.some.inj (hs.symm.trans (SequentialScopePackedMachine.actual_step g x m E S (.args r) K))
    rw [he]
    exact SequentialScopePackedMachine.transition_runs g x e m E S (.args r) K h
  | seq a => simp [SequentialReturnFields.before,SequentialSharedWords.step] at hs
  | alt a p => simp [SequentialReturnFields.before,SequentialSharedWords.step] at hs
  | notP p => simp [SequentialReturnFields.before,SequentialSharedWords.step] at hs
  | star a p => simp [SequentialReturnFields.before,SequentialSharedWords.step] at hs
  | argHead es p => simp [SequentialReturnFields.before,SequentialSharedWords.step] at hs

theorem frames_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (r : ArgsResult) (f : SequentialSharedWords.Frame) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (SequentialReturnFields.before m E (.args r) f K))
    (hs : SequentialSharedWords.step g x (SequentialReturnFields.before m E (.args r) f K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (frames g.rules.length (headerLength r))
      (withInput (encode (CBVtoCBN.compilerNodes g e) (SequentialReturnFields.before m E (.args r) f K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let L := withInput (encode ns (SequentialReturnFields.before m E (.args r) f K)) x
  let target := withInput (encode ns next) x
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  obtain ⟨T,ht⟩ := branch_runs g x e m E r f K next h hs
  have hb : Complexity.Runs (LenOK B) (branches g.rules.length (headerLength r) (SequentialReturnFields.frameTag f)) L target T := ht
  have hL : LenOK B L := by obtain ⟨t,ht,hx⟩ := hb; exact hx.q_start
  obtain ⟨U,hu⟩ := SequentialReturnFields.dispatch_runs (branches g.rules.length (headerLength r))
    (SequentialReturnFields.frameTag f) (SequentialReturnFields.frame_tag_bound f)
    ([E.length,K.length+1] ++ resultFields (.args r)) (SequentialReturnFields.payload ns f)
    (blocks (writeFrames ns K).control) L target (SequentialReturnFields.before_control ns x m E (.args r) f K) rfl hL hb
  have hlen : ([E.length,K.length+1] ++ resultFields (.args r)).length=headerLength r := by
    simp only [List.length_append,List.length_cons,List.length_nil,headerLength]
  rw [hlen] at hu
  exact ⟨U,hu⟩

/-- The result tag selects four- or five-field frame inspection. A successful
argument value's actual word count is skipped, never treated as a frame tag. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (r : ArgsResult) (f : SequentialSharedWords.Frame) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (SequentialReturnFields.before m E (.args r) f K))
    (hs : SequentialSharedWords.step g x (SequentialReturnFields.before m E (.args r) f K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program g.rules.length)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (SequentialReturnFields.before m E (.args r) f K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let L := withInput (encode ns (SequentialReturnFields.before m E (.args r) f K)) x
  let target := withInput (encode ns next) x
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  obtain ⟨T,ht⟩ := frames_runs g x e m E r f K next h hs
  have hb : Complexity.Runs (LenOK B)
      (select (resultTag r) (frames g.rules.length 4) (frames g.rules.length 4) (frames g.rules.length 5)) L target T := by
    cases r with
    | none => exact ht
    | some v => cases v with
      | none => exact ht
      | some Wq => cases Wq; exact ht
  have hL : LenOK B L := by obtain ⟨t,ht,hx⟩ := hb; exact hx.q_start
  let C := blocks (writeFrames ns K).control ++ blocks (SequentialReturnFields.frameTag f :: SequentialReturnFields.payload ns f) ++
    blocks (extraFields r)
  have hsrc : L 2=C ++ blocks [resultTag r] ++ blocks [E.length,K.length+1,4] := by
    change withInput (encode ns (SequentialReturnFields.before m E (.args r) f K)) x 2 = _
    rw [SequentialReturnFields.before_control]
    simp only [C,resultFields,show [E.length,K.length+1] ++ ([4,resultTag r] ++ extraFields r) =
      [E.length,K.length+1,4] ++ [resultTag r] ++ extraFields r from rfl,blocks_append,List.append_assoc]
  have htag : resultTag r ≤ 2 := by cases r with
    | none => decide
    | some v => cases v <;> simp [resultTag]
  exact dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide) [E.length,K.length+1,4] (resultTag r) htag C
    (frames g.rules.length 4) (frames g.rules.length 4) (frames g.rules.length 5) L target hsrc rfl hL hb

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (r : ArgsResult) (f : SequentialSharedWords.Frame) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (SequentialReturnFields.before m E (.args r) f K))
    (hs : SequentialSharedWords.step g x (SequentialReturnFields.before m E (.args r) f K)=some next)
    (tau : Tapes 8) (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e)
      (SequentialReturnFields.before m E (.args r) f K)) x) tau) :
    ∃ t tau', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program g.rules.length).compile tau t (.cont tau') ∧
      Rep (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) tau' := by
  obtain ⟨T,hr⟩ := transition_runs g x e m E r f K next h hs
  exact tape_runs hr tau hrep

theorem finite_alphabet (rules : Nat) : ∃ E, 0x110001 ≤ E ∧ (program rules).compile.SymOK (E+4) := by
  obtain ⟨E,_hE,hc⟩ := LProg.exists_constOK (program rules)
  exact ⟨max E 0x110001,Nat.le_max_right _ _,compile_symOK _ _
    (LProg.ConstOK.mono (Nat.le_max_left E 0x110001) hc)⟩

end Shallot.MacroPeg.CBV.SequentialArgumentsReturnDispatchMachine
