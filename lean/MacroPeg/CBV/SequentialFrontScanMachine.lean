import MacroPeg.CBV.SequentialFrontScan

namespace Shallot.MacroPeg.CBV.SequentialFrontScanMachine

open Complexity Complexity.BinaryWord SequentialFrontScan SequentialFieldFetch
open SequentialFrontRead (locals)

inductive Trace : Plan → Nat → List Nat → Nat → Prop where
  | done (h) : Trace .done h [] h
  | word {next v vs out held} (h : Trace next v vs out) : Trace (.word next) held (v :: vs) out
  | zero {a b vs out} (h : Trace a 0 vs out) : Trace (.branch a b) 0 vs out
  | positive {a b n vs out} (h : Trace b n vs out) : Trace (.branch a b) (n + 1) vs out
  | many {stride next n chunk vs out} (hlen : chunk.length = n * stride)
      (h : Trace next (after n chunk) vs out) : Trace (.many stride next) n (chunk ++ vs) out

theorem eval_trace (p : Plan) (held : Nat) (input rest : List Nat)
    (he : SequentialFrontScan.eval p held input = some rest) :
    ∃ vs out, input = vs ++ rest ∧ Trace p held vs out := by
  induction p generalizing held input rest with
  | done =>
    simp only [SequentialFrontScan.eval, Option.some.injEq] at he
    exact ⟨[], held, by simpa using he, .done held⟩
  | fail => simp [SequentialFrontScan.eval] at he
  | word next ih =>
    cases input with
    | nil => simp [SequentialFrontScan.eval] at he
    | cons v input =>
      obtain ⟨vs, out, hh, ht⟩ := ih v input rest he
      exact ⟨v :: vs, out, by simp [hh], .word ht⟩
  | branch a b iha ihb =>
    cases held with
    | zero =>
      obtain ⟨vs, out, hh, ht⟩ := iha 0 input rest (by simpa [SequentialFrontScan.eval] using he)
      exact ⟨vs, out, hh, .zero ht⟩
    | succ n =>
      obtain ⟨vs, out, hh, ht⟩ := ihb n input rest (by simpa [SequentialFrontScan.eval] using he)
      exact ⟨vs, out, hh, .positive ht⟩
  | many stride next ih =>
    simp only [SequentialFrontScan.eval] at he
    split at he
    · cases he
    · rename_i hn
      obtain ⟨vs, out, hh, ht⟩ := ih _ _ rest he
      refine ⟨input.take (held * stride) ++ vs, out, ?_, .many ?_ ht⟩
      · rw [List.append_assoc, ← hh, List.take_append_drop]
      · simp; omega

theorem compile_trace {p : Plan} {held out : Nat} {vs : List Nat} (ht : Trace p held vs out)
    {B width : Nat} (rest : List Nat) (tail : List Bool) (D : List Nat)
    (hv : ∀ v ∈ vs, v < 2 ^ width) (hval : ∀ v ∈ vs, 3 * v + 4 ≤ B)
    (hB : LenOK B (start width (vs ++ rest) tail D held []))
    (hloc : D.length + (locals vs).length + 2 ≤ B) :
    ∃ T, Complexity.Runs (LenOK B) (SequentialFrontScan.compile p) (start width (vs ++ rest) tail D held [])
      (start width rest tail (D ++ locals vs) out []) T := by
  induction ht generalizing D with
  | done h =>
    simpa [compile, SequentialFrontRead.locals] using
      (show ∃ T, Complexity.Runs (LenOK B) (skipP 3) (start width rest tail D h [])
        (start width rest tail D h []) T from ⟨1, runs_skip 3 hB⟩)
  | @word next v vs out held ht ih =>
    have hspace : D.length + (v + 1) + (locals vs).length + 2 ≤ B := by
      simpa [SequentialFrontRead.locals, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloc
    obtain ⟨T1, hr1⟩ := fetch_runs (vs ++ rest) tail D [] (hv v (by simp)) hB
      (hval v (by simp)) (by omega)
    have hnext : LenOK B (start width (vs ++ rest) tail (D ++ 2 :: List.replicate v 1) v []) := by
      obtain ⟨_, _, hx⟩ := hr1
      exact hx.q_end _ (Or.inl rfl)
    obtain ⟨T2, hr2⟩ := ih (D := D ++ 2 :: List.replicate v 1)
      (fun n hn => hv n (by simp [hn])) (fun n hn => hval n (by simp [hn])) hnext (by simp; omega)
    have he : (D ++ 2 :: List.replicate v 1) ++ locals vs = D ++ locals (v :: vs) := by
      simp [SequentialFrontRead.locals, List.append_assoc]
    rw [he] at hr2
    exact ⟨T1 + T2, hr1.seq hr2⟩
  | @zero a b vs out ht ih =>
    obtain ⟨T, hr⟩ := ih D hv hval hB hloc
    exact ⟨T + 1, hr.iteF hB (by simp [start, nonEmpty, lastSym])⟩
  | @positive a b n vs out ht ih =>
    have hp := pop_unary (n := n) (i := (3 : Fin 11))
      (L := start width (vs ++ rest) tail D (n + 1) []) (by simp [start]) hB
    have he : (start width (vs ++ rest) tail D (n + 1) []).set 3 (List.replicate n 1) =
        start width (vs ++ rest) tail D n [] := by
      funext i
      by_cases hi : i = 3 <;> simp_all [start, Lists.set]
    rw [he] at hp
    have hnext : LenOK B (start width (vs ++ rest) tail D n []) := by
      obtain ⟨_, _, hx⟩ := hp
      exact hx.q_end _ (Or.inl rfl)
    obtain ⟨T, hr⟩ := ih D hv hval hnext hloc
    exact ⟨_, (hp.seq hr).iteT hB (unary_nonEmpty (i := 3) (n := n) (by simp [start]))⟩
  | @many stride next n chunk vs out hlen ht ih =>
    let L := start width ((chunk ++ vs) ++ rest) tail D n []
    have hspace : D.length + (locals chunk).length + (locals vs).length + 2 ≤ B := by
      simpa [SequentialFrontRead.locals, List.flatMap_append, Nat.add_assoc] using hloc
    have hcount : n + 2 ≤ B := by simpa [L, start] using hB 3
    have hc := copyLen_spec (by decide : ([3, 10, 7] : List (Fin 11)).Nodup)
      (L := L) (B := B) (by simp [L, start]) hB (by simp [L, start]; exact hcount)
    have he : L.set 10 (L 10 ++ List.replicate (L 3).length 1) =
        start width (chunk ++ (vs ++ rest)) tail D n (List.replicate n 1) := by
      funext i
      by_cases hi : i = 10 <;> simp_all [L, start, Lists.set, List.append_assoc]
    rw [he] at hc
    have hloop : LenOK B (start width (chunk ++ (vs ++ rest)) tail D n (List.replicate n 1)) := by
      obtain ⟨_, _, hx⟩ := hc
      exact hx.q_end _ (Or.inl rfl)
    obtain ⟨T1, hr1⟩ := counted_fetch_runs chunk (vs ++ rest) tail D hlen
      (fun v hm => hv v (by simp [hm])) (fun v hm => hval v (by simp [hm])) hloop (by omega)
    have hnext : LenOK B (start width (vs ++ rest) tail (D ++ locals chunk) (after n chunk) []) := by
      obtain ⟨_, _, hx⟩ := hr1
      exact hx.q_end _ (Or.inl rfl)
    obtain ⟨T2, hr2⟩ := ih (D := D ++ locals chunk)
      (fun v hm => hv v (by simp [hm])) (fun v hm => hval v (by simp [hm])) hnext (by simp; omega)
    have heout : (D ++ locals chunk) ++ locals vs = D ++ locals (chunk ++ vs) := by
      simp [SequentialFrontRead.locals, List.flatMap_append, List.append_assoc]
    rw [heout] at hr2
    exact ⟨_, hc.seq (hr1.seq hr2)⟩

open SequentialStack SequentialStackCodec CBVtoCBN

/-- Complete input-driven front parsing by the compiled program. In
particular there is no supplied front-length counter in the initial state. -/
theorem parser_runs (ns : List CompileNode) (c : Config) {B width held : Nat}
    (tail : List Bool) (D : List Nat)
    (hv : ∀ v ∈ SequentialFront.prefixCode ns (SequentialFront.tail c) (SequentialFront.front c), v < 2 ^ width)
    (hval : ∀ v ∈ SequentialFront.prefixCode ns (SequentialFront.tail c) (SequentialFront.front c), 3 * v + 4 ≤ B)
    (hB : LenOK B (start width (encode ns c) tail D held []))
    (hloc : D.length + (locals (SequentialFront.prefixCode ns (SequentialFront.tail c) (SequentialFront.front c))).length + 2 ≤ B) :
    ∃ out T, Complexity.Runs (LenOK B) SequentialFrontScan.parserProgram (start width (encode ns c) tail D held [])
      (start width (SequentialFront.suffixCode ns (SequentialFront.tail c)) tail
        (D ++ locals (SequentialFront.prefixCode ns (SequentialFront.tail c) (SequentialFront.front c))) out []) T := by
  have he := parser_correct ns c (SequentialFront.suffixCode ns (SequentialFront.tail c)) held
  rw [← SequentialFront.encode_front] at he
  obtain ⟨vs, out, hh, ht⟩ := eval_trace SequentialFrontScan.parser held _ _ he
  have hvseq : vs = SequentialFront.prefixCode ns (SequentialFront.tail c) (SequentialFront.front c) := by
    apply List.append_cancel_right
    rw [← hh, SequentialFront.encode_front]
  subst vs
  have hstart : encode ns c = SequentialFront.prefixCode ns (SequentialFront.tail c) (SequentialFront.front c) ++
      SequentialFront.suffixCode ns (SequentialFront.tail c) := SequentialFront.encode_front ns c
  obtain ⟨T, hr⟩ := compile_trace ht (SequentialFront.suffixCode ns (SequentialFront.tail c)) tail D hv hval
    (by simpa only [← hstart] using hB) hloc
  exact ⟨out, T, by simpa only [← hstart, parserProgram] using hr⟩

open SequentialStackCodecBound SequentialStackPayload SequentialStackBinary

/-- The old supplied-count front reader's capacity also suffices for the
tag/header-driven parser on every reachable configuration. -/
theorem reachable_parser_runs (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) :
    ∃ out T, Complexity.Runs (LenOK (SequentialFrontRead.frontSpace g x e c)) parserProgram
      (start (width g x e) (encode (compilerNodes g e) c) [] [] 0 [])
      (start (width g x e) (SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c)) []
        (locals (SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) (SequentialFront.front c))) out []) T := by
  let P := SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) (SequentialFront.front c)
  let S := SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c)
  let N := numberBound g x e
  let M := 13 + 6 * arityBudget g
  let R := (encodeBits (compilerNodes g e) (width g x e) c).length
  have hcode : encode (compilerNodes g e) c = P ++ S := SequentialFront.encode_front _ c
  have hv : ∀ v ∈ P, v ≤ N := by
    intro v hm
    exact reachable_numbers g x e c h v (by simp [hcode, hm])
  have hlen : P.length ≤ M := SequentialFront.reachable_prefix_length g x e c h
  have hloc : (locals P).length ≤ M * (N + 1) :=
    Nat.le_trans (SequentialFrontRead.locals_length P N hv) (Nat.mul_le_mul_right _ hlen)
  have hwidth : width g x e ≤ N + 1 := by
    have hh := Nat.log2_le_self N
    change N.log2 + 1 ≤ N + 1
    omega
  have he : SequentialFrontRead.frontSpace g x e c = M * (N + 1) + 4 * (N + 1) + R + 8 := by
    simp only [SequentialFrontRead.frontSpace, M, N, R, Nat.add_mul]
  have hB : LenOK (SequentialFrontRead.frontSpace g x e c)
      (start (width g x e) (encode (compilerNodes g e) c) [] [] 0 []) := by
    intro i
    simp only [start]
    split
    · simp only [List.append_nil, storage, List.length_reverse, List.length_map]
      change R + 2 ≤ SequentialFrontRead.frontSpace g x e c
      omega
    · split
      · simp; omega
      · split
        · simp; omega
        · split
          · simp; omega
          · split
            · simp; omega
            · split <;> simp <;> omega
  obtain ⟨out, T, hr⟩ := parser_runs (compilerNodes g e) c [] [] (held := 0)
    (fun v hm => Nat.lt_of_le_of_lt (hv v hm) Nat.lt_log2_self)
    (fun v hm => by have := hv v hm; omega) hB (by simp; change (locals P).length + 2 ≤ _; omega)
  exact ⟨out, T, by simpa only [List.nil_append, width, N] using hr⟩

theorem reachable_parser_tape (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) (τ : Tapes 11)
    (hτ : Rep (start (width g x e) (encode (compilerNodes g e) c) [] [] 0 []) τ) :
    ∃ out t τ', Exec (TFits (SequentialFrontRead.frontSpace g x e c)) parserProgram.compile τ t (.cont τ') ∧
      Rep (start (width g x e) (SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c)) []
        (locals (SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) (SequentialFront.front c))) out []) τ' := by
  obtain ⟨out, _, hr⟩ := reachable_parser_runs g x e c h
  obtain ⟨t, τ', _, he, hr'⟩ := runs_tape hr τ hτ
  exact ⟨out, t, τ', he, hr'⟩

end Shallot.MacroPeg.CBV.SequentialFrontScanMachine
