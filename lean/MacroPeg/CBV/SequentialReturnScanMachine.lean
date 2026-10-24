import MacroPeg.CBV.SequentialReturnScan
import MacroPeg.CBV.SequentialFrontRoundtrip

namespace Shallot.MacroPeg.CBV.SequentialReturnScanMachine
open Complexity Complexity.BinaryWord SequentialStack SequentialStackCodec SequentialStackCodecBound
open SequentialStackBinary SequentialFieldFetch CBVtoCBN
open SequentialFrontRead (locals frontSpace)

def program (next : Nat → LProg 11) : LProg 11 :=
  SequentialReturnScan.compile (fun key => .seq SequentialFrontWrite.writeFront (next key)) SequentialReturnScan.parser

/-- Select a return continuation from the actual input, restore the original
binary state, then execute that continuation. No front-length counter or
external frame selector is provided to the program. -/
theorem selected_runs (g : MGrammar) (x : List Char) (e : MExp) (v : SequentialStack.Value)
    (f : SequentialStack.Frame) (K : List SequentialStack.Frame)
    (h : SequentialStack.Runs g x (initial g x e) ⟨.value v,f :: K⟩)
    (next : Nat → LProg 11) (target : Lists 11) {B T : Nat}
    (hspace : frontSpace g x e ⟨.value v,f :: K⟩ ≤ B)
    (hr : Complexity.Runs (LenOK B) (next (SequentialReturnScan.frameKey f))
      (start (width g x e) (encode (compilerNodes g e) ⟨.value v,f :: K⟩) [] [] 0 []) target T) :
    ∃ T', Complexity.Runs (LenOK B) (program next)
      (start (width g x e) (encode (compilerNodes g e) ⟨.value v,f :: K⟩) [] [] 0 []) target T' := by
  let c : Config := ⟨.value v,f :: K⟩
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
  have hstart : LenOK B (start (width g x e) (P ++ S) [] [] 0 []) := by
    rw [← hcode]
    intro i
    exact Nat.le_trans (oldExec.q_start i) hspace
  have hend := oldExec.q_end _ (Or.inl rfl)
  have hloc : (locals P).length + 2 ≤ B := by
    have hh := hend 9
    change (locals P).length + 2 ≤ frontSpace g x e c at hh
    simpa using Nat.le_trans hh hspace
  obtain ⟨out,ht⟩ := SequentialReturnScan.parser_trace ns v f K 0
  have ht' : SequentialReturnScan.Trace SequentialReturnScan.parser 0 P out (SequentialReturnScan.frameKey f) := ht
  have restore (held : Nat) (hparsed : LenOK B (start (width g x e) S [] (locals P) held [])) :
      ∃ T, Complexity.Runs (LenOK B) SequentialFrontWrite.writeFront
        (start (width g x e) S [] (locals P) held [])
        (start (width g x e) (encode ns c) [] [] 0 []) T := by
    have hfuse : start (width g x e) S [] (locals P) held [] =
        start (width g x e) [] (SequentialStackBinary.pack (width g x e) S) (locals P) held [] := by
      simpa only [List.append_nil] using SequentialFrontRoundtrip.start_fuse (width g x e) S [] (locals P) held []
    have hbits : (encodeBits ns (width g x e) c).length + 2 ≤ B := by
      dsimp only [ns,c]
      unfold frontSpace at hspace
      omega
    obtain ⟨T,hw⟩ := SequentialFrontRoundtrip.write_attach (B := B) (w := width g x e) (held := held) ns (SequentialFront.tail c) (SequentialFront.front c)
      (fun v hm => Nat.lt_of_le_of_lt (hv v hm) Nat.lt_log2_self)
      (fun v hm => by have := hv v hm; omega) (by rwa [← hfuse])
      (by simpa only [SequentialFront.attach_front] using hbits)
    rw [SequentialFront.attach_front, ← hfuse] at hw
    exact ⟨T,hw⟩
  obtain ⟨T',hres⟩ := SequentialReturnScan.compile_trace
    (fun key => .seq SequentialFrontWrite.writeFront (next key)) ht' (width := width g x e) S [] []
    (fun v hm => Nat.lt_of_le_of_lt (hv v hm) Nat.lt_log2_self)
    (fun v hm => by have := hv v hm; omega) hstart (by simpa using hloc) target (by
      intro hparsed
      obtain ⟨Tw,hw⟩ := restore out (by simpa using hparsed)
      exact ⟨Tw+T,by simpa using hw.seq hr⟩)
  exact ⟨T',by simpa only [← hcode, program, ns, c] using hres⟩
end Shallot.MacroPeg.CBV.SequentialReturnScanMachine
