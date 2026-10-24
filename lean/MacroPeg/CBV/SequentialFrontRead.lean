import MacroPeg.CBV.SequentialFront

/-! Decode a bounded front to a local unary field list while the continuation
tail stays binary. The front length is an explicit input, not an oracle step. -/

namespace Shallot.MacroPeg.CBV.SequentialFrontRead

open Complexity Complexity.BinaryWord SequentialStackBinary

def locals (vs : List Nat) : List Nat := vs.flatMap (fun v => 2 :: List.replicate v 1)

def start (width : Nat) (vs : List Nat) (tail : List Bool) (D : List Nat) : Lists 11 := fun i =>
  if i = 0 then storage (SequentialStackBinary.pack width vs ++ tail)
  else if i = 1 ∨ i = 8 then List.replicate width 1
  else if i = 4 then [1, 1]
  else if i = 9 then D
  else if i = 10 then List.replicate vs.length 1 else []

def body : LProg 11 :=
  .seq (readP 0 1 2 3 4 5 6 7)
    (.seq (.push 9 2) (.seq (moveAll 3 9) (.seq (copyLenP 8 1 7) (.pop 10))))

def readFront : LProg 11 := .loop 10 nonEmpty body

/-- Consume exactly the supplied field count. The retained tail may be the
entire remaining continuation. The width and all reusable scratch are restored. -/
theorem read_runs {B width : Nat} (vs : List Nat) (tail : List Bool) (D : List Nat)
    (hv : ∀ v ∈ vs, v < 2 ^ width)
    (hval : ∀ v ∈ vs, 3 * v + 4 ≤ B)
    (hB : LenOK B (start width vs tail D))
    (hloc : D.length + (locals vs).length + 2 ≤ B) :
    ∃ T, Complexity.Runs (LenOK B) readFront (start width vs tail D)
      (start width [] tail (D ++ locals vs)) T := by
  induction vs generalizing D with
  | nil =>
    have he : D ++ locals [] = D := by simp [locals]
    rw [he]
    exact ⟨1, 1, Nat.le_refl _, .loopF hB (by simp [start, nonEmpty, lastSym])⟩
  | cons v vs ih =>
    let L := start width (v :: vs) tail D
    let M := (((L.set 0 (storage (SequentialStackBinary.pack width vs ++ tail))).set 1 []).set 2 []).set 3
      (List.replicate v 1)
    obtain ⟨T1, hr1⟩ := SequentialWordRead.read_word_runs (by decide :
      ([0, 1, 2, 3, 4, 5, 6, 7] : List (Fin 11)).Nodup)
      (hv v (by simp)) (SequentialStackBinary.pack width vs ++ tail) (L := L)
      (by simp [L, start, SequentialStackBinary.pack, List.append_assoc]) (by simp [L, start])
      (by simp [L, start]) (by simp [L, start]) (by simp [L, start])
      (by simp [L, start]) (by simp [L, start]) (by simp [L, start]) hB (hval v (by simp))
    have hM : LenOK B M := by
      obtain ⟨_, _, hx⟩ := hr1
      exact hx.q_end M (Or.inl rfl)
    let N := M.set 9 (D ++ [2])
    have hD : M 9 = D := by simp [M, L, start, Lists.set]
    have hspace : D.length + (v + 1) + (locals vs).length + 2 ≤ B := by
      simpa [locals, List.flatMap_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloc
    have hN : LenOK B N := lenOK_set hM 9 (by simp; omega)
    have hr2 : Complexity.Runs (LenOK B) (.push 9 2) M N 1 := by
      simpa only [hD] using runs_push (i := 9) (e := 2) hM hN
    have hNa : N 3 = List.replicate v 1 := by simp [N, M, Lists.set]
    have hNd : N 9 = D ++ [2] := by simp [N]
    have hr3 := runs_moveAll (L := N) (by decide : (3 : Fin 11) ≠ 9) (Q := LenOK B)
      (fun i j _ _ => lenOK_moving hN (by decide)
        (by simp [hNa, hNd]; omega) i j)
    let P := N.moveAll 3 9
    have hP : LenOK B P := by
      obtain ⟨_, _, hx⟩ := hr3
      exact hx.q_end P (Or.inl rfl)
    have hP1 : P 1 = [] := by simp [P, N, M, Lists.moveAll, Lists.set]
    have hP8 : P 8 = List.replicate width 1 := by simp [P, N, M, L, start, Lists.moveAll, Lists.set]
    have hP7 : P 7 = [] := by simp [P, N, M, L, start, Lists.moveAll, Lists.set]
    have hwidth : width + 2 ≤ B := by simpa [L, start] using hB 8
    have hr4 := copyLen_spec (by decide : ([8, 1, 7] : List (Fin 11)).Nodup)
      (L := P) (B := B) hP7 hP (by simp [hP1, hP8]; exact hwidth)
    let Q := P.set 1 (List.replicate width 1)
    have hr4' : Complexity.Runs (LenOK B) (copyLenP 8 1 7) P Q (8 * (width + 1)) := by
      simpa only [hP1, hP8, List.length_replicate, List.nil_append] using hr4
    have hQ : LenOK B Q := by
      obtain ⟨_, _, hx⟩ := hr4'
      exact hx.q_end Q (Or.inl rfl)
    have hcount : Q 10 = List.replicate (vs.length + 1) 1 := by
      simp [Q, P, N, M, L, start, Lists.moveAll, Lists.set]
    have hr5 := pop_unary hcount hQ
    have he : Q.set 10 (List.replicate vs.length 1) =
        start width vs tail (D ++ 2 :: List.replicate v 1) := by
      funext i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨
          i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Q, P, N, M, L, start, Lists.moveAll, Lists.set, List.append_assoc]
    rw [he] at hr5
    have hb := hr1.seq (hr2.seq (hr3.seq (hr4'.seq hr5)))
    have hnext : LenOK B (start width vs tail (D ++ 2 :: List.replicate v 1)) := by
      obtain ⟨_, _, hx⟩ := hr5
      exact hx.q_end _ (Or.inl rfl)
    obtain ⟨T2, hr⟩ := ih (D := D ++ 2 :: List.replicate v 1)
      (fun n hn => hv n (by simp [hn])) (fun n hn => hval n (by simp [hn])) hnext
      (by simp; omega)
    have hout : (D ++ 2 :: List.replicate v 1) ++ locals vs = D ++ locals (v :: vs) := by
      simp [locals, List.append_assoc]
    rw [hout] at hr
    obtain ⟨t1, _, hx1⟩ := hb
    obtain ⟨t2, _, hx2⟩ := hr
    exact ⟨t1 + 1 + t2, t1 + 1 + t2, Nat.le_refl _,
      .loopC hB (unary_nonEmpty (i := 10) (L := L) (n := vs.length) (by simp [L, start])) hx1 hx2⟩

theorem read_tape {B width : Nat} (vs : List Nat) (tail : List Bool) (D : List Nat)
    (hv : ∀ v ∈ vs, v < 2 ^ width) (hval : ∀ v ∈ vs, 3 * v + 4 ≤ B)
    (hB : LenOK B (start width vs tail D))
    (hloc : D.length + (locals vs).length + 2 ≤ B)
    (τ : Tapes 11) (hτ : Rep (start width vs tail D) τ) :
    ∃ t τ', Exec (TFits B) readFront.compile τ t (.cont τ') ∧
      Rep (start width [] tail (D ++ locals vs)) τ' := by
  obtain ⟨_, hr⟩ := read_runs vs tail D hv hval hB hloc
  obtain ⟨t, τ', _, he, hr'⟩ := runs_tape hr τ hτ
  exact ⟨t, τ', he, hr'⟩

theorem locals_length (vs : List Nat) (N : Nat) (hv : ∀ v ∈ vs, v ≤ N) :
    (locals vs).length ≤ vs.length * (N + 1) := by
  have hh := sum_le_length_mul (fun v => v + 1) (N + 1) vs (fun v hm => by have := hv v hm; omega)
  simpa only [locals, List.length_flatMap, List.length_cons, List.length_replicate] using hh

open SequentialStack SequentialStackCodec SequentialStackCodecBound SequentialStackPayload CBVtoCBN

noncomputable def frontSpace (g : MGrammar) (x : List Char) (e : MExp) (c : Config) : Nat :=
  (13 + 6 * arityBudget g + 4) * (numberBound g x e + 1) +
    (encodeBits (compilerNodes g e) (width g x e) c).length + 8

/-- The decoded front is linear in input length for a fixed grammar. The
unexpanded binary continuation retains its previous bit-length bound. -/
theorem frontSpace_bound (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) :
    frontSpace g x e c ≤
      ((13 + 6 * arityBudget g + 4) * (numberCoefficient g e + 1) + 8) * (x.length + 1) +
      (cellCoefficient g e * (x.length + 1)) *
        ((x.length + 1).log2 + (numberCoefficient g e).log2 + 2) := by
  have hn := numberBound_linear g x e
  have hn' : numberBound g x e + 1 ≤ (numberCoefficient g e + 1) * (x.length + 1) := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  have hm := Nat.mul_le_mul_left (13 + 6 * arityBudget g + 4) hn'
  have hb := reachable_bit_bound g x e c h
  have h8 : 8 ≤ 8 * (x.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have he : ((13 + 6 * arityBudget g + 4) * (numberCoefficient g e + 1) + 8) * (x.length + 1) =
      (13 + 6 * arityBudget g + 4) * ((numberCoefficient g e + 1) * (x.length + 1)) +
        8 * (x.length + 1) := by rw [Nat.add_mul, Nat.mul_assoc]
  rw [he]
  unfold frontSpace
  omega

/-- An actual program reads every field of the reachable task, stack-length
header and top frame. Its initial word-count register is explicitly supplied
with the correct prefix length. Computing that count from the tags is a
separate controller obligation, not a premise-free parser supplied here. -/
theorem reachable_read_runs (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) :
    ∃ T, Complexity.Runs (LenOK (frontSpace g x e c)) readFront
      (start (width g x e) (SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c)
        (SequentialFront.front c))
        (SequentialStackBinary.pack (width g x e) (SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c))) [])
      (start (width g x e) []
        (SequentialStackBinary.pack (width g x e) (SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c)))
        (locals (SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) (SequentialFront.front c)))) T := by
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
  have hloc := locals_length P N hv
  have hloc' : (locals P).length ≤ M * (N + 1) :=
    Nat.le_trans hloc (Nat.mul_le_mul_right _ hlen)
  have hinput : SequentialStackBinary.pack (width g x e) P ++ SequentialStackBinary.pack (width g x e) S =
      encodeBits (compilerNodes g e) (width g x e) c := by
    simp [encodeBits, hcode, SequentialStackBinary.pack, List.flatMap_append]
  have hwidth : width g x e ≤ N + 1 := by
    have hh := Nat.log2_le_self N
    change N.log2 + 1 ≤ N + 1
    omega
  have hM : M ≤ M * (N + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have he : frontSpace g x e c = M * (N + 1) + 4 * (N + 1) + R + 8 := by
    simp only [frontSpace, M, N, R, Nat.add_mul]
  change ∃ T, Complexity.Runs (LenOK (frontSpace g x e c)) readFront
    (start (width g x e) P (SequentialStackBinary.pack (width g x e) S) [])
    (start (width g x e) [] (SequentialStackBinary.pack (width g x e) S) (locals P)) T
  have hcap : 3 * N + 4 ≤ frontSpace g x e c := by omega
  have hlocal : (locals P).length + 2 ≤ frontSpace g x e c := by omega
  have hcounter : P.length + 2 ≤ frontSpace g x e c := by omega
  apply read_runs P (SequentialStackBinary.pack (width g x e) S) []
  · intro v hm
    exact Nat.lt_of_le_of_lt (hv v hm) Nat.lt_log2_self
  · intro v hm
    have := hv v hm
    omega
  · intro i
    simp only [start]
    split
    · rw [hinput]
      simp only [storage, List.length_reverse, List.length_map]
      change R + 2 ≤ frontSpace g x e c
      omega
    · split
      · simp; rw [he]; omega
      · split
        · simp; rw [he]; omega
        · split
          · simp; rw [he]; omega
          · split
            · simpa only [List.length_replicate] using hcounter
            · simp; omega
  · simpa only [List.length_nil, Nat.zero_add] using hlocal

theorem reachable_read_tape (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) (τ : Tapes 11)
    (hτ : Rep (start (width g x e)
      (SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) (SequentialFront.front c))
      (SequentialStackBinary.pack (width g x e) (SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c))) []) τ) :
    ∃ t τ', Exec (TFits (frontSpace g x e c)) readFront.compile τ t (.cont τ') ∧
      Rep (start (width g x e) []
        (SequentialStackBinary.pack (width g x e) (SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c)))
        (locals (SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) (SequentialFront.front c)))) τ' := by
  obtain ⟨_, hr⟩ := reachable_read_runs g x e c h
  obtain ⟨t, τ', _, he, hr'⟩ := runs_tape hr τ hτ
  exact ⟨t, τ', he, hr'⟩

end Shallot.MacroPeg.CBV.SequentialFrontRead
