import MacroPeg.CBV.SequentialFrontWrite

namespace Shallot.MacroPeg.CBV.SequentialFrontRoundtrip

open Complexity Complexity.BinaryWord SequentialFieldFetch SequentialStackBinary
open SequentialStack SequentialStackCodec SequentialStackCodecBound SequentialStackPayload CBVtoCBN
open SequentialFrontRead (locals frontSpace)
open SequentialFront (prefixCode suffixCode front tail)

theorem start_fuse (w : Nat) (vs : List Nat) (bits : List Bool) (D : List Nat) (held : Nat) (C : List Nat) :
    start w vs bits D held C = start w [] (SequentialStackBinary.pack w vs ++ bits) D held C := by
  funext i
  simp [start, SequentialStackBinary.pack]

def program : LProg 11 :=
  .seq SequentialFrontScan.parserProgram SequentialFrontWrite.writeFront

/-- Execute the tag/header parser and then restore its entire local field
list. The original binary state and every scratch register are restored. -/
theorem roundtrip_runs (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) :
    ∃ T, Complexity.Runs (LenOK (frontSpace g x e c)) program
      (start (width g x e) (encode (compilerNodes g e) c) [] [] 0 [])
      (start (width g x e) (encode (compilerNodes g e) c) [] [] 0 []) T := by
  let P := prefixCode (compilerNodes g e) (tail c) (front c)
  let S := suffixCode (compilerNodes g e) (tail c)
  let N := numberBound g x e
  let R := (encodeBits (compilerNodes g e) (width g x e) c).length
  have hcode : encode (compilerNodes g e) c = P ++ S := SequentialFront.encode_front _ c
  have hv : ∀ v ∈ P, v ≤ N := by
    intro v hm
    exact reachable_numbers g x e c h v (by simp [hcode, hm])
  have hspace : 3 * N + 4 ≤ frontSpace g x e c := by
    unfold frontSpace
    rw [Nat.add_mul]
    omega
  have hbits : (SequentialStackBinary.pack (width g x e) S).length + P.length * width g x e = R := by
    simp only [R, encodeBits, hcode, SequentialStackBinary.pack_length, List.length_append, Nat.add_mul]
    omega
  have hR : R + 2 ≤ frontSpace g x e c := by unfold frontSpace; omega
  obtain ⟨held, T1, hr⟩ := SequentialFrontScanMachine.reachable_parser_runs g x e c h
  have hr' : Complexity.Runs (LenOK (frontSpace g x e c)) SequentialFrontScan.parserProgram
      (start (width g x e) (encode (compilerNodes g e) c) [] [] 0 [])
      (start (width g x e) [] (SequentialStackBinary.pack (width g x e) S) (locals P) held []) T1 := by
    have hstate : start (width g x e) S [] (locals P) held [] =
        start (width g x e) [] (SequentialStackBinary.pack (width g x e) S) (locals P) held [] := by
      simpa only [List.append_nil] using start_fuse (width g x e) S [] (locals P) held []
    have hr0 : Complexity.Runs (LenOK (frontSpace g x e c)) SequentialFrontScan.parserProgram
        (start (width g x e) (encode (compilerNodes g e) c) [] [] 0 [])
        (start (width g x e) S [] (locals P) held []) T1 := hr
    rw [hstate] at hr0
    exact hr0
  have hparsed : LenOK (frontSpace g x e c)
      (start (width g x e) [] (SequentialStackBinary.pack (width g x e) S) (locals P) held []) := by
    obtain ⟨_, _, hx⟩ := hr'
    exact hx.q_end _ (Or.inl rfl)
  obtain ⟨T2, hw⟩ := SequentialFrontWrite.write_runs (width := width g x e) P (SequentialStackBinary.pack (width g x e) S) []
    (fun v hm => Nat.lt_of_le_of_lt (hv v hm) Nat.lt_log2_self)
    (fun v hm => by have := hv v hm; omega) hparsed (by rw [hbits]; exact hR)
  have he : start (width g x e) P (SequentialStackBinary.pack (width g x e) S) [] 0 [] =
      start (width g x e) (encode (compilerNodes g e) c) [] [] 0 [] := by
    funext i
    simp [start, hcode, SequentialStackBinary.pack, List.flatMap_append]
  rw [he] at hw
  exact ⟨T1 + T2, hr'.seq hw⟩

theorem roundtrip_tape (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) (τ : Tapes 11)
    (hτ : Rep (start (width g x e) (encode (compilerNodes g e) c) [] [] 0 []) τ) :
    ∃ t τ', Exec (TFits (frontSpace g x e c)) program.compile τ t (.cont τ') ∧
      Rep (start (width g x e) (encode (compilerNodes g e) c) [] [] 0 []) τ' := by
  obtain ⟨_, hr⟩ := roundtrip_runs g x e c h
  obtain ⟨t, τ', _, he, hr'⟩ := runs_tape hr τ hτ
  exact ⟨t, τ', he, hr'⟩

/-- Writer interface for an updated local transition result. The result's
local fields are inputs here; this theorem does not execute local `step`. -/
theorem write_attach {B w held : Nat} (ns : List CompileNode) (K : List SequentialStack.Frame) (localNext : Config)
    (hv : ∀ v ∈ prefixCode ns K localNext, v < 2 ^ w)
    (hval : ∀ v ∈ prefixCode ns K localNext, v + 3 ≤ B)
    (hB : LenOK B (start w [] (SequentialStackBinary.pack w (suffixCode ns K))
      (locals (prefixCode ns K localNext)) held []))
    (hout : (encodeBits ns w (SequentialFront.attach K localNext)).length + 2 ≤ B) :
    ∃ T, Complexity.Runs (LenOK B) SequentialFrontWrite.writeFront
      (start w [] (SequentialStackBinary.pack w (suffixCode ns K)) (locals (prefixCode ns K localNext)) held [])
      (start w (encode ns (SequentialFront.attach K localNext)) [] [] 0 []) T := by
  have hcode := SequentialFront.encode_attach ns K localNext
  obtain ⟨T, hr⟩ := SequentialFrontWrite.write_runs (prefixCode ns K localNext)
    (SequentialStackBinary.pack w (suffixCode ns K)) [] hv hval hB (by
      simpa [encodeBits, hcode, SequentialStackBinary.pack_length, Nat.add_mul, Nat.add_comm] using hout)
  have he : start w (prefixCode ns K localNext) (SequentialStackBinary.pack w (suffixCode ns K)) [] 0 [] =
      start w (encode ns (SequentialFront.attach K localNext)) [] [] 0 [] := by
    funext i
    simp [start, hcode, SequentialStackBinary.pack, List.flatMap_append]
  rw [he] at hr
  exact ⟨T, hr⟩

end Shallot.MacroPeg.CBV.SequentialFrontRoundtrip
