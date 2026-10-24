import MacroPeg.CBV.SequentialInputScan
import MacroPeg.CBV.SequentialFrontRoundtrip

/-! Select the next machine from the actual binary task, restoring that task
before entering the selected continuation in the expanded input host. -/
namespace Shallot.MacroPeg.CBV.SequentialStepScanMachine
open Complexity Complexity.BinaryWord SequentialStack SequentialStackCodec SequentialStackCodecBound
open SequentialStackBinary SequentialFieldFetch CBVtoCBN
open SequentialFrontRead (locals frontSpace)
open SequentialInputHost (extend old old_runs extend_project extend_fits)

def program (ns : List CompileNode) (next : Nat → LProg 20) : LProg 20 :=
  SequentialInputScan.compile (fun key => .seq (SequentialFrontWrite.writeFront.rename old) (next key))
    (SequentialStepScan.parser ns)

theorem selected_runs (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) (next : Nat → LProg 20) (X : List Nat)
    (target : Lists 20) {B T : Nat} (hspace : frontSpace g x e c ≤ B) (hX : X.length+2 ≤ B)
    (hr : Complexity.Runs (LenOK B) (next (SequentialStepScan.key c))
      (extend (start (width g x e) (encode (compilerNodes g e) c) [] [] 0 []) X) target T) :
    ∃ T', Complexity.Runs (LenOK B) (program (compilerNodes g e) next)
      (extend (start (width g x e) (encode (compilerNodes g e) c) [] [] 0 []) X) target T' := by
  let ns := compilerNodes g e
  let N := numberBound g x e
  let P := SequentialFront.prefixCode ns (SequentialFront.tail c) (SequentialFront.front c)
  let S := SequentialFront.suffixCode ns (SequentialFront.tail c)
  have hcode : encode ns c = P ++ S := SequentialFront.encode_front ns c
  have hv : ∀ v ∈ P, v ≤ N := by
    intro v hv
    apply reachable_numbers g x e c h v
    rw [hcode]
    exact List.mem_append_left _ hv
  have hnum : 3*N+4 ≤ B := by
    unfold frontSpace at hspace
    rw [Nat.add_mul] at hspace
    omega
  obtain ⟨oldHeld,oldT,oldRun⟩ := SequentialFrontScanMachine.reachable_parser_runs g x e c h
  obtain ⟨oldSteps,_,oldExec⟩ := oldRun
  have hstart : LenOK B (extend (start (width g x e) (P ++ S) [] [] 0 []) X) := by
    apply extend_fits _ hX
    rw [← hcode]
    intro i
    exact Nat.le_trans (oldExec.q_start i) hspace
  have hend := oldExec.q_end _ (Or.inl rfl)
  have hloc : (locals P).length+2 ≤ B := by
    have hh := hend 9
    change (locals P).length+2 ≤ frontSpace g x e c at hh
    exact Nat.le_trans hh hspace
  obtain ⟨out,ht⟩ := SequentialStepScan.parser_trace ns c (SequentialStackPool.reachable_ok g x e c h).1 0
  have ht' : SequentialReturnScan.Trace (SequentialStepScan.parser ns) 0 P out (SequentialStepScan.key c) := ht
  have restore (held : Nat) (hparsed : LenOK B (extend (start (width g x e) S [] (locals P) held []) X)) :
      ∃ Tw, Complexity.Runs (LenOK B) (SequentialFrontWrite.writeFront.rename old)
        (extend (start (width g x e) S [] (locals P) held []) X)
        (extend (start (width g x e) (encode ns c) [] [] 0 []) X) Tw := by
    have hfuse : start (width g x e) S [] (locals P) held [] =
        start (width g x e) [] (SequentialStackBinary.pack (width g x e) S) (locals P) held [] := by
      simpa only [List.append_nil] using SequentialFrontRoundtrip.start_fuse (width g x e) S [] (locals P) held []
    have hbits : (encodeBits ns (width g x e) c).length+2 ≤ B := by
      dsimp only [ns]
      unfold frontSpace at hspace
      omega
    obtain ⟨Tw,hw⟩ := SequentialFrontRoundtrip.write_attach (B := B) (w := width g x e) (held := held)
      ns (SequentialFront.tail c) (SequentialFront.front c)
      (fun v hm => Nat.lt_of_le_of_lt (hv v hm) Nat.lt_log2_self)
      (fun v hm => by have := hv v hm; omega) (by rw [← hfuse]; exact extend_project hparsed)
      (by simpa only [SequentialFront.attach_front] using hbits)
    rw [SequentialFront.attach_front,← hfuse] at hw
    exact ⟨Tw,old_runs _ _ _ X hw hX⟩
  obtain ⟨T',hres⟩ := SequentialInputScan.compile_trace
    (fun key => .seq (SequentialFrontWrite.writeFront.rename old) (next key)) ht'
    (width := width g x e) S [] [] X
    (fun v hm => Nat.lt_of_le_of_lt (hv v hm) Nat.lt_log2_self)
    (fun v hm => by have := hv v hm; omega) hstart (by simpa using hloc) target (by
      intro hparsed
      obtain ⟨Tw,hw⟩ := restore out (by simpa using hparsed)
      exact ⟨Tw+T,by simpa using hw.seq hr⟩)
  exact ⟨T',by simpa only [← hcode,program,ns] using hres⟩

end Shallot.MacroPeg.CBV.SequentialStepScanMachine
