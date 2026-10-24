import MacroPeg.CBV.SequentialNotReturn

/-! Reusable composition of the verified front parser, an actual coreProg
operation, and the verified writer. Concrete operations discharge `hlocal`. -/

namespace Shallot.MacroPeg.CBV.SequentialLocalPipeline

open Complexity Complexity.BinaryWord SequentialStack SequentialStackCodec
open SequentialStackBinary SequentialStackCodecBound CBVtoCBN
open SequentialFrontRead (locals frontSpace)

def program (coreProg : LProg 11) : LProg 11 :=
  .seq SequentialFrontScan.parserProgram (.seq coreProg SequentialFrontWrite.writeFront)

theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (c next localNext : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) (hs : step g x c = some next)
    (hd : next = SequentialFront.attach (SequentialFront.tail c) localNext)
    (coreProg : LProg 11) (B : Nat)
    (hfront : frontSpace g x e c ≤ B) (hnum : numberBound g x e + 3 ≤ B)
    (hfinal : (encodeBits (compilerNodes g e) (width g x e) next).length + 2 ≤ B)
    (hlocal : ∀ held, LenOK B
      (SequentialFieldFetch.start (width g x e) []
        (SequentialStackBinary.pack (width g x e) (SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c)))
        (locals (SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) (SequentialFront.front c))) held []) →
      ∃ T, Complexity.Runs (LenOK B) coreProg
        (SequentialFieldFetch.start (width g x e) []
          (SequentialStackBinary.pack (width g x e) (SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c)))
          (locals (SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) (SequentialFront.front c))) held [])
        (SequentialFieldFetch.start (width g x e) []
          (SequentialStackBinary.pack (width g x e) (SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c)))
          (locals (SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) localNext)) held []) T) :
    ∃ T, Complexity.Runs (LenOK B) (program coreProg)
      (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) c) [] [] 0 [])
      (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) next) [] [] 0 []) T := by
  let ns := compilerNodes g e
  let P := SequentialFront.prefixCode ns (SequentialFront.tail c) (SequentialFront.front c)
  let P' := SequentialFront.prefixCode ns (SequentialFront.tail c) localNext
  let S := SequentialFront.suffixCode ns (SequentialFront.tail c)
  let bits := SequentialStackBinary.pack (width g x e) S
  have hcode' : encode ns next = P' ++ S := by rw [hd, SequentialFront.encode_attach]
  have hn := h.trans (SequentialStack.Runs.single hs)
  have hb' : ∀ v ∈ P', v ≤ numberBound g x e := by
    intro v hv
    apply reachable_numbers g x e next hn v
    change v ∈ encode ns next
    rw [hcode']
    exact List.mem_append_left _ hv
  obtain ⟨held, T1, hr⟩ := SequentialFrontScanMachine.reachable_parser_runs g x e c h
  have hstate : SequentialFieldFetch.start (width g x e) S [] (locals P) held [] =
      SequentialFieldFetch.start (width g x e) [] bits (locals P) held [] := by
    simpa only [List.append_nil] using SequentialFrontRoundtrip.start_fuse (width g x e) S [] (locals P) held []
  have hr0 : Complexity.Runs (LenOK (frontSpace g x e c)) SequentialFrontScan.parserProgram
      (SequentialFieldFetch.start (width g x e) (encode ns c) [] [] 0 [])
      (SequentialFieldFetch.start (width g x e) [] bits (locals P) held []) T1 := by
    have hh : Complexity.Runs (LenOK (frontSpace g x e c)) SequentialFrontScan.parserProgram
        (SequentialFieldFetch.start (width g x e) (encode ns c) [] [] 0 [])
        (SequentialFieldFetch.start (width g x e) S [] (locals P) held []) T1 := hr
    rw [hstate] at hh
    exact hh
  have hr1 := hr0.weaken (fun _ hh i => Nat.le_trans (hh i) hfront)
  have hparsed : LenOK B (SequentialFieldFetch.start (width g x e) [] bits (locals P) held []) := by
    obtain ⟨_, _, hx⟩ := hr1
    exact hx.q_end _ (Or.inl rfl)
  obtain ⟨T2, hr2⟩ := hlocal held hparsed
  have hupdated : LenOK B (SequentialFieldFetch.start (width g x e) [] bits (locals P') held []) := by
    obtain ⟨_, _, hx⟩ := hr2
    exact hx.q_end _ (Or.inl rfl)
  have hbitcap : bits.length + P'.length * width g x e + 2 ≤ B := by
    change (encodeBits ns (width g x e) next).length + 2 ≤ B at hfinal
    simpa [bits, encodeBits, hcode', SequentialStackBinary.pack_length, Nat.add_mul, Nat.add_comm] using hfinal
  obtain ⟨T3, hr3⟩ := SequentialFrontWrite.write_runs (width := width g x e) P' bits []
    (fun v hv => Nat.lt_of_le_of_lt (hb' v hv) Nat.lt_log2_self)
    (fun v hv => by have := hb' v hv; omega) hupdated hbitcap
  have he : SequentialFieldFetch.start (width g x e) P' bits [] 0 [] =
      SequentialFieldFetch.start (width g x e) (encode ns next) [] [] 0 [] := by
    funext i
    simp [SequentialFieldFetch.start, hcode', bits, SequentialStackBinary.pack, List.flatMap_append]
  rw [he] at hr3
  exact ⟨_, hr1.seq (hr2.seq hr3)⟩

end Shallot.MacroPeg.CBV.SequentialLocalPipeline
