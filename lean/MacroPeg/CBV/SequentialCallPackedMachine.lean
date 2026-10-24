import MacroPeg.CBV.SequentialArgConsReturnPackedMachine

/-! Complete call-frame returns, preserving actual argument words and their
current input position. The rule index is fixed by the source call template. -/
namespace Shallot.MacroPeg.CBV.SequentialCallPackedMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialReturnControlMachine
open SequentialSharedWords (Config CaptureEnv ArgsResult Runs initial)
open SequentialSharedStateCodec (Packed encode write writeTask writeFrames Input)
open SequentialCaptureCopyMachine (withInput)
open SequentialArgConsReturnPackedMachine (resultTag extraFields)
open SequentialArgHeadPackedMachine (bad badTag)

private theorem blocks_nil : blocks [] = [] := rfl

def success (i : Nat) : LProg 8 := .seq (replace 2 1 5 2 [])
  (.seq (decrementSecond 2 1) (replace 2 1 2 2 [2,i]))

def unsuccessful : LProg 8 := .seq (replace 2 1 4 2 [])
  (.seq (decrementSecond 2 1) (replace 2 1 2 1 [3]))

def program (i : Nat) : LProg 8 := dispatch 2 1 3 unsuccessful unsuccessful (success i)

theorem success_runs (i a k n : Nat) (tail : List Nat) (L : Lists 8) {B : Nat}
    (hsrc : L 2 = tail ++ blocks [6,i] ++ blocks [a,k+1,4,2,n]) (h1 : L 1 = [])
    (hL : LenOK B L) (hcap : (tail ++ blocks [a,k,2,i,n]).length+2 ≤ B) :
    ∃ T, Complexity.Runs (LenOK B) (success i) L (L.set 2 (tail ++ blocks [a,k,2,i,n])) T := by
  have hh := hL 2
  rw [hsrc] at hh
  simp only [List.length_append] at hh
  obtain ⟨T1,hr⟩ := replace_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    [a,k+1,4,2,n] [6,i] [] tail L hsrc h1 hL
    (by simp only [blocks_nil,List.append_nil,List.length_append]; omega)
  simp only [blocks_nil,List.append_nil] at hr
  let N := L.set 2 (tail ++ blocks [a,k+1,4,2,n])
  have hn2 : N 2 = (tail ++ blocks [4,2,n]) ++ blocks [a,k+1] := by
    simp only [N,Lists.set_same]
    rw [show [a,k+1,4,2,n] = [a,k+1] ++ [4,2,n] from rfl,blocks_append]
    simp only [List.append_assoc]
  obtain ⟨T2,hd⟩ := decrementSecond_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    a k (tail ++ blocks [4,2,n]) N hn2 (by simpa [N,Lists.set] using h1) (end_fits hr)
  let M := N.set 2 ((tail ++ blocks [4,2,n]) ++ blocks [a,k])
  have hm2 : M 2 = (tail ++ blocks [n]) ++ blocks [4,2] ++ blocks [a,k] := by
    simp only [M,Lists.set_same]
    rw [show [4,2,n] = [4,2] ++ [n] from rfl,blocks_append]
    simp only [List.append_assoc]
  have hnew : (tail ++ blocks [n]) ++ blocks [2,i] ++ blocks [a,k] = tail ++ blocks [a,k,2,i,n] := by
    rw [show [a,k,2,i,n] = ([a,k] ++ [2,i]) ++ [n] from rfl,blocks_append,blocks_append]
    simp only [List.append_assoc]
  obtain ⟨T3,ht⟩ := replace_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    [a,k] [4,2] [2,i] (tail ++ blocks [n]) M hm2
    (by simpa [M,N,Lists.set] using h1) (end_fits hd) (by rwa [hnew])
  rw [hnew] at ht
  simp only [M,N,Lists.set_set_u] at ht
  simp only [N,Lists.set_set_u] at hd
  exact ⟨_,hr.seq (hd.seq ht)⟩

theorem unsuccessful_runs (i a k t : Nat) (tail : List Nat) (L : Lists 8) {B : Nat}
    (hsrc : L 2 = tail ++ blocks [6,i] ++ blocks [a,k+1,4,t]) (h1 : L 1 = [])
    (hL : LenOK B L) (hcap : (tail ++ blocks [a,k,3,t]).length+2 ≤ B) :
    ∃ T, Complexity.Runs (LenOK B) unsuccessful L (L.set 2 (tail ++ blocks [a,k,3,t])) T := by
  have hh := hL 2
  rw [hsrc] at hh
  simp only [List.length_append] at hh
  obtain ⟨T1,hr⟩ := replace_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    [a,k+1,4,t] [6,i] [] tail L hsrc h1 hL
    (by simp only [blocks_nil,List.append_nil,List.length_append]; omega)
  simp only [blocks_nil,List.append_nil] at hr
  let N := L.set 2 (tail ++ blocks [a,k+1,4,t])
  have hn2 : N 2 = (tail ++ blocks [4,t]) ++ blocks [a,k+1] := by
    simp only [N,Lists.set_same]
    rw [show [a,k+1,4,t] = [a,k+1] ++ [4,t] from rfl,blocks_append]
    simp only [List.append_assoc]
  obtain ⟨T2,hd⟩ := decrementSecond_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    a k (tail ++ blocks [4,t]) N hn2 (by simpa [N,Lists.set] using h1) (end_fits hr)
  let M := N.set 2 ((tail ++ blocks [4,t]) ++ blocks [a,k])
  have hm2 : M 2 = (tail ++ blocks [t]) ++ blocks [4] ++ blocks [a,k] := by
    simp only [M,Lists.set_same]
    rw [show [4,t] = [4] ++ [t] from rfl,blocks_append]
    simp only [List.append_assoc]
  have hnew : (tail ++ blocks [t]) ++ blocks [3] ++ blocks [a,k] = tail ++ blocks [a,k,3,t] := by
    rw [show [a,k,3,t] = ([a,k] ++ [3]) ++ [t] from rfl,blocks_append,blocks_append]
    simp only [List.append_assoc]
  obtain ⟨T3,ht⟩ := replace_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    [a,k] [4] [3] (tail ++ blocks [t]) M hm2
    (by simpa [M,N,Lists.set] using h1) (end_fits hd) (by rwa [hnew])
  rw [hnew] at ht
  simp only [M,N,Lists.set_set_u] at ht
  simp only [N,Lists.set_set_u] at hd
  exact ⟨_,hr.seq (hd.seq ht)⟩

def before (m : Nat) (E : CaptureEnv) (i : Nat) (r : ArgsResult)
    (K : List SequentialSharedWords.Frame) : Config := ⟨m,.value (.args r),E,.call i :: K⟩

def after (m : Nat) (E : CaptureEnv) (i : Nat) (r : ArgsResult)
    (K : List SequentialSharedWords.Frame) : Config := ⟨m,match r with
  | none => .value (.expr none)
  | some none => .value (.expr (some none))
  | some (some (W,q)) => .query i W q,E,K⟩

theorem actual_step (g : MGrammar) (x : List Char) (m : Nat) (E : CaptureEnv)
    (i : Nat) (r : ArgsResult) (K : List SequentialSharedWords.Frame) :
    SequentialSharedWords.step g x (before m E i r K) = some (after m E i r K) := by
  cases r with
  | none => rfl
  | some v => cases v <;> rfl

def taskFields (i : Nat) : ArgsResult → List Nat
  | none => [3,0]
  | some none => [3,1]
  | some (some (W,_)) => [2,i,W.length]

theorem before_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat)
    (E : CaptureEnv) (i : Nat) (r : ArgsResult) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before m E i r K)) x 2 =
      blocks (writeFrames ns K).control ++ blocks [6,i] ++
        blocks ([E.length,K.length+1,4] ++ [resultTag r] ++ extraFields r) := by
  change SequentialCursorEntryMachine.layout (encode ns (before m E i r K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (before m E i r K)).control =
      ([E.length,K.length+1,4] ++ [resultTag r] ++ extraFields r) ++ [6,i] ++ (writeFrames ns K).control := by
    cases r with
    | none => simp [write,before,writeTask,writeFrames,SequentialSharedStateCodec.writeFrame,resultTag,extraFields,
        Input.append,SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords]
    | some v => cases v with
      | none => simp [write,before,writeTask,writeFrames,SequentialSharedStateCodec.writeFrame,resultTag,extraFields,
          Input.append,SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords]
      | some Wq => rcases Wq with ⟨W,q⟩; simp [write,before,writeTask,writeFrames,SequentialSharedStateCodec.writeFrame,
          resultTag,extraFields,Input.append,SequentialSharedStateCodec.putControl,
          SequentialSharedStateCodec.putWords,SequentialSharedStateCodec.putCursor]
  rw [he,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem after_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat)
    (E : CaptureEnv) (i : Nat) (r : ArgsResult) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (after m E i r K)) x 2 =
      blocks (writeFrames ns K).control ++ blocks ([E.length,K.length] ++ taskFields i r) := by
  change SequentialCursorEntryMachine.layout (encode ns (after m E i r K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (after m E i r K)).control =
      ([E.length,K.length] ++ taskFields i r) ++ (writeFrames ns K).control := by
    cases r with
    | none => simp [write,after,taskFields,writeTask,Input.append,
        SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords]
    | some v => cases v with
      | none => simp [write,after,taskFields,writeTask,Input.append,
          SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords]
      | some Wq => rcases Wq with ⟨W,q⟩; simp [write,after,taskFields,writeTask,Input.append,
          SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,SequentialSharedStateCodec.putCursor]
  rw [he,blocks_append]

theorem other_streams (ns : List CBVtoCBN.CompileNode) (m : Nat) (E : CaptureEnv)
    (i : Nat) (r : ArgsResult) (K : List SequentialSharedWords.Frame) :
    (encode ns (before m E i r K)).clock = (encode ns (after m E i r K)).clock ∧
    (encode ns (before m E i r K)).cursors = (encode ns (after m E i r K)).cursors ∧
    (encode ns (before m E i r K)).words = (encode ns (after m E i r K)).words := by
  cases r with
  | none => exact ⟨rfl,rfl,rfl⟩
  | some v => cases v with
    | none => exact ⟨rfl,rfl,rfl⟩
    | some Wq => rcases Wq with ⟨W,q⟩; exact ⟨rfl,rfl,rfl⟩

theorem control_only_update (a b : Packed) (x : List Char)
    (hc : a.clock=b.clock) (hp : a.cursors=b.cursors) (hw : a.words=b.words) :
    (withInput a x).set 2 (withInput b x 2) = withInput b x := by
  have h0 : withInput a x 0 = withInput b x 0 := by
    change bits a.cursors = bits b.cursors
    rw [hp]
  have h4 : withInput a x 4 = withInput b x 4 := by
    change (a.words.map SequentialCaptureCopyMachine.wordSymbol).reverse =
      (b.words.map SequentialCaptureCopyMachine.wordSymbol).reverse
    rw [hw]
  have hu := SequentialArgCapturePackedMachine.withInput_update a b x hc
  rw [← h4,Lists.set_get_self,← h0,Lists.set_get_self] at hu
  exact hu

private theorem next_reachable {g : MGrammar} {x : List Char} {a b c : Config}
    (h : Runs g x a b) (hs : SequentialSharedWords.step g x b = some c) : Runs g x a c := by
  induction h with
  | refl => exact .cons hs (.refl _)
  | cons hh ht ih => exact .cons hh (ih hs)

/-- The actual argument-result tag selects all outcomes; successful arguments
become the query's actual word environment at exactly the same input position. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (i : Nat) (r : ArgsResult) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E i r K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program i) (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E i r K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (after m E i r K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before m E i r K)) x
  let target := withInput (encode ns (after m E i r K)) x
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  change (encode ns (before m E i r K)).length ≤ _ at hb
  have hx : x.length+2 ≤ B := by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
  have hL : LenOK B L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hx
  have ha := next_reachable h (actual_step g x m E i r K)
  have hba := SequentialSharedStateBound.encoded_state_linear g x e _ ha
  change (encode ns (after m E i r K)).length ≤ _ at hba
  have htarget : LenOK B target := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hx
  have hcontrol : L 2 = blocks (writeFrames ns K).control ++ blocks [6,i] ++
      blocks ([E.length,K.length+1,4] ++ [resultTag r] ++ extraFields r) := before_control ns x m E i r K
  have hcap : (blocks (writeFrames ns K).control ++ blocks ([E.length,K.length] ++ taskFields i r)).length+2 ≤ B := by
    rw [← after_control ns x m E i r K]
    exact htarget 2
  obtain ⟨T,hr⟩ : ∃ T, Complexity.Runs (LenOK B)
      (select (resultTag r) unsuccessful unsuccessful (success i)) L
      (L.set 2 (blocks (writeFrames ns K).control ++ blocks ([E.length,K.length] ++ taskFields i r))) T := by
    cases r with
    | none => simpa [select,resultTag,extraFields,taskFields] using
        unsuccessful_runs i E.length K.length 0 (blocks (writeFrames ns K).control) L hcontrol rfl hL hcap
    | some v => cases v with
      | none => simpa [select,resultTag,extraFields,taskFields] using
          unsuccessful_runs i E.length K.length 1 (blocks (writeFrames ns K).control) L hcontrol rfl hL hcap
      | some Wq => rcases Wq with ⟨W,q⟩
                   simpa [select,resultTag,extraFields,taskFields] using
                     success_runs i E.length K.length W.length (blocks (writeFrames ns K).control) L hcontrol rfl hL hcap
  have htag : resultTag r ≤ 2 := by cases r with
    | none => decide
    | some v => cases v <;> simp [resultTag]
  have hsrc : L 2 = (blocks (writeFrames ns K).control ++ blocks [6,i] ++ blocks (extraFields r)) ++
      blocks [resultTag r] ++ blocks [E.length,K.length+1,4] := by
    rw [hcontrol,blocks_append,blocks_append]
    simp only [List.append_assoc]
  obtain ⟨Td,hd⟩ := dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide) [E.length,K.length+1,4]
    (resultTag r) htag (blocks (writeFrames ns K).control ++ blocks [6,i] ++ blocks (extraFields r))
    unsuccessful unsuccessful (success i) L _ hsrc rfl hL hr
  have he : L.set 2 (blocks (writeFrames ns K).control ++ blocks ([E.length,K.length] ++ taskFields i r)) = target := by
    have ho := other_streams ns m E i r K
    rw [← after_control ns x m E i r K]
    exact control_only_update _ _ x ho.1 ho.2.1 ho.2.2
  rw [he] at hd
  exact ⟨_,hd⟩

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (i : Nat) (r : ArgsResult) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E i r K)) (τ : Tapes 8)
    (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E i r K)) x) τ) :
    ∃ t τ', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program i).compile τ t (.cont τ') ∧
      Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (after m E i r K)) x) τ' := by
  obtain ⟨T,hr⟩ := transition_runs g x e m E i r K h
  exact tape_runs hr τ hrep

theorem finite_alphabet (i E : Nat) (hE : 2 ≤ E) : (program i).compile.SymOK (E+4) := by
  apply compile_symOK E
  have hs : (success i).ConstOK E := ⟨replace_constOK hE _ _ _ _ _,decrementSecond_constOK E _ _,replace_constOK hE _ _ _ _ _⟩
  have hf : unsuccessful.ConstOK E := ⟨replace_constOK hE _ _ _ _ _,decrementSecond_constOK E _ _,replace_constOK hE _ _ _ _ _⟩
  exact dispatch_constOK E _ _ _ _ _ _ hf hf hs

end Shallot.MacroPeg.CBV.SequentialCallPackedMachine
