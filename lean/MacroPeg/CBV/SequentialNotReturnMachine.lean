import MacroPeg.CBV.SequentialNotReturn

namespace Shallot.MacroPeg.CBV.SequentialNotReturnMachine

open Complexity Complexity.BinaryWord SequentialStack SequentialStackCodec
open SequentialStackBinary SequentialStackCodecBound CBVtoCBN SequentialNotReturn
open SequentialFrontRead (locals frontSpace)

def before (r : Res) (p : Nat) (K : List SequentialStack.Frame) : Config := ⟨.value (.expr r), .notP p :: K⟩
def next (r : Res) (p : Nat) (K : List SequentialStack.Frame) : Config := ⟨.value (.expr (neg r p)), K⟩

def program : LProg 11 := .seq SequentialFrontScan.parserProgram
  (.seq localProgram SequentialFrontWrite.writeFront)

noncomputable def space (g : MGrammar) (x : List Char) (e : MExp) (c : Config) : Nat :=
  frontSpace g x e c + scratchSpace (numberBound g x e)

theorem space_eq (g : MGrammar) (x : List Char) (e : MExp) (c : Config) :
    space g x e c = frontSpace g x e c + 57 * numberBound g x e + 2559 := by
  simp [space, scratchSpace_linear, Nat.add_assoc]

theorem space_bound (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) :
    space g x e c ≤
      (((13 + 6 * SequentialStackPayload.arityBudget g + 4) * (numberCoefficient g e + 1) + 8) +
        (57 * numberCoefficient g e + 2559)) * (x.length + 1) +
      (cellCoefficient g e * (x.length + 1)) *
        ((x.length + 1).log2 + (numberCoefficient g e).log2 + 2) := by
  have hf := SequentialFrontRead.frontSpace_bound g x e c h
  have hn := numberBound_linear g x e
  have hm := Nat.mul_le_mul_left 57 hn
  have hc : 2559 ≤ 2559 * (x.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hs : scratchSpace (numberBound g x e) ≤ (57 * numberCoefficient g e + 2559) * (x.length + 1) := by
    rw [scratchSpace_linear, Nat.add_mul, Nat.mul_assoc]
    omega
  have hh := Nat.add_le_add hf hs
  unfold space
  rw [Nat.add_mul]
  omega

/-- A complete state-changing Seq transition, from the original encoded state
to the actual encoded successor. No updated prefix is supplied by the caller. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (r : Res) (p : Nat)
    (K : List SequentialStack.Frame)
    (h : SequentialStack.Runs g x (initial g x e) (before r p K)) :
    ∃ T, Complexity.Runs (LenOK (space g x e (before r p K))) program
      (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (before r p K)) [] [] 0 [])
      (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (next r p K)) [] [] 0 []) T := by
  let c := before r p K
  let c' := next r p K
  let ns := compilerNodes g e
  let N := numberBound g x e
  let B := space g x e c
  let P := inputFields r K.length p
  let P' := outputFields r K.length p
  let S := SequentialFront.suffixCode ns K
  let bits := SequentialStackBinary.pack (width g x e) S
  have hP : SequentialFront.prefixCode ns (SequentialFront.tail c) (SequentialFront.front c) = P := by
    simpa [c, before, SequentialFront.front, SequentialFront.tail] using input_prefix ns r p K
  have hS : SequentialFront.suffixCode ns (SequentialFront.tail c) = S := rfl
  have hcode : encode ns c = P ++ S := by
    simpa only [hP, hS] using SequentialFront.encode_front ns c
  have hcode' : encode ns c' = P' ++ S := by
    change encode ns (SequentialFront.attach K ⟨.value (.expr (neg r p)), []⟩) = P' ++ S
    rw [SequentialFront.encode_attach, output_prefix]
  have hs : step g x c = some c' := original_step g x r p K
  have hn := h.trans (SequentialStack.Runs.single hs)
  have hb : ∀ v ∈ P, v ≤ N := by
    intro v hv
    apply reachable_numbers g x e c h v
    change v ∈ encode ns c
    rw [hcode]
    exact List.mem_append_left _ hv
  have hb' : ∀ v ∈ P', v ≤ N := by
    intro v hv
    apply reachable_numbers g x e c' hn v
    change v ∈ encode ns c'
    rw [hcode']
    exact List.mem_append_left _ hv
  have hfront : frontSpace g x e c ≤ B := by dsimp [B, space]; omega
  have hlocal : scratchSpace N ≤ B := by dsimp [B, space, N]; omega
  obtain ⟨held, T1, hr⟩ := SequentialFrontScanMachine.reachable_parser_runs g x e c h
  have hstate : SequentialFieldFetch.start (width g x e) S [] (locals P) held [] =
      SequentialFieldFetch.start (width g x e) [] bits (locals P) held [] := by
    simpa only [List.append_nil] using SequentialFrontRoundtrip.start_fuse (width g x e) S [] (locals P) held []
  have hr0 : Complexity.Runs (LenOK (frontSpace g x e c)) SequentialFrontScan.parserProgram
      (SequentialFieldFetch.start (width g x e) (encode ns c) [] [] 0 [])
      (SequentialFieldFetch.start (width g x e) [] bits (locals P) held []) T1 := by
    have hh : Complexity.Runs (LenOK (frontSpace g x e c)) SequentialFrontScan.parserProgram
        (SequentialFieldFetch.start (width g x e) (encode ns c) [] [] 0 [])
        (SequentialFieldFetch.start (width g x e) S [] (locals P) held []) T1 := by
      change Complexity.Runs (LenOK (frontSpace g x e c)) SequentialFrontScan.parserProgram
        (SequentialFieldFetch.start (width g x e) (encode ns c) [] [] 0 [])
        (SequentialFieldFetch.start (width g x e) (SequentialFront.suffixCode ns (SequentialFront.tail c)) []
          (locals (SequentialFront.prefixCode ns (SequentialFront.tail c) (SequentialFront.front c))) held []) T1 at hr
      rw [hP, hS] at hr
      exact hr
    rw [hstate] at hh
    exact hh
  have hr1 := hr0.weaken (fun _ hh i => Nat.le_trans (hh i) hfront)
  have hparsed : LenOK B (SequentialFieldFetch.start (width g x e) [] bits (locals P) held []) := by
    obtain ⟨_, _, hx⟩ := hr1
    exact hx.q_end _ (Or.inl rfl)
  have hr2 := local_runs r K.length p bits hb hlocal hparsed
  have hupdated : LenOK B (SequentialFieldFetch.start (width g x e) [] bits (locals P') held []) := by
    obtain ⟨_, _, hx⟩ := hr2
    exact hx.q_end _ (Or.inl rfl)
  have hlen : P'.length ≤ P.length := by
    cases r <;> (try (rename_i rr; cases rr)) <;> simp [P, P', inputFields, outputFields]
  have hbitcap : bits.length + P'.length * width g x e + 2 ≤ B := by
    have hR : (encodeBits ns (width g x e) c).length + 2 ≤ B := by
      have hh : (encodeBits ns (width g x e) c).length + 2 ≤ frontSpace g x e c := by
        change (encodeBits (compilerNodes g e) (width g x e) c).length + 2 ≤ frontSpace g x e c
        unfold frontSpace
        omega
      exact Nat.le_trans hh hfront
    have hm := Nat.mul_le_mul_right (width g x e) hlen
    simp only [bits, encodeBits, hcode, SequentialStackBinary.pack_length, List.length_append,
      Nat.add_mul] at hR ⊢
    omega
  have hval : ∀ v ∈ P', v + 3 ≤ B := by
    intro v hv
    have hh := hb' v hv
    have hcap : N + 3 ≤ scratchSpace N := by rw [scratchSpace_linear]; omega
    omega
  obtain ⟨T3, hr3⟩ := SequentialFrontWrite.write_runs (width := width g x e) P' bits []
    (fun v hv => Nat.lt_of_le_of_lt (hb' v hv) Nat.lt_log2_self) hval hupdated hbitcap
  have he : SequentialFieldFetch.start (width g x e) P' bits [] 0 [] =
      SequentialFieldFetch.start (width g x e) (encode ns c') [] [] 0 [] := by
    funext i
    simp [SequentialFieldFetch.start, hcode', bits, SequentialStackBinary.pack, List.flatMap_append]
  rw [he] at hr3
  exact ⟨_, hr1.seq (hr2.seq hr3)⟩

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (r : Res) (p : Nat)
    (K : List SequentialStack.Frame)
    (h : SequentialStack.Runs g x (initial g x e) (before r p K)) (τ : Tapes 11)
    (hτ : Rep (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (before r p K)) [] [] 0 []) τ) :
    ∃ t τ', Exec (TFits (space g x e (before r p K))) program.compile τ t (.cont τ') ∧
      Rep (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (next r p K)) [] [] 0 []) τ' := by
  obtain ⟨_, hr⟩ := transition_runs g x e r p K h
  obtain ⟨t, τ', _, he, hr'⟩ := runs_tape hr τ hτ
  exact ⟨t, τ', he, hr'⟩

end Shallot.MacroPeg.CBV.SequentialNotReturnMachine
