import MacroPeg.CBV.SequentialFrontRead

/-! A field fetch keeps the decoded value available for tag dispatch or a
length-controlled loop. No total front-length counter is an input. -/

namespace Shallot.MacroPeg.CBV.SequentialFieldFetch

open Complexity Complexity.BinaryWord SequentialStackBinary

def start (width : Nat) (vs : List Nat) (tail : List Bool) (D : List Nat)
    (held : Nat) (counter : List Nat) : Lists 11 := fun i =>
  if i = 0 then storage (SequentialStackBinary.pack width vs ++ tail)
  else if i = 3 then List.replicate held 1
  else if i = 4 then [1, 1]
  else if i = 8 then List.replicate width 1
  else if i = 9 then D
  else if i = 10 then counter else []

def fetch : LProg 11 :=
  .seq (clearP 3) (.seq (copyLenP 8 1 7)
    (.seq (readP 0 1 2 3 4 5 6 7) (.seq (.push 9 2) (copyLenP 3 9 7))))

/-- Fetch a field from the encoded stream, append its local representation,
and retain its value on register 3. Register 10 is available for parser loops. -/
theorem fetch_runs {B width held v : Nat} (vs : List Nat) (tail : List Bool)
    (D counter : List Nat) (hv : v < 2 ^ width)
    (hB : LenOK B (start width (v :: vs) tail D held counter))
    (hval : 3 * v + 4 ≤ B) (hout : D.length + v + 3 ≤ B) :
    ∃ T, Complexity.Runs (LenOK B) fetch (start width (v :: vs) tail D held counter)
      (start width vs tail (D ++ 2 :: List.replicate v 1) v counter) T := by
  let L := start width (v :: vs) tail D held counter
  let A := L.set 3 []
  have hc := clearP_spec (Q := LenOK B) (i := 3) (L := L) (by
    intro n hn
    apply lenOK_set hB 3
    have hh : (L 3).length + 2 ≤ B := hB 3
    simp only [List.length_take]
    omega)
  have hA : LenOK B A := by
    obtain ⟨_, _, hx⟩ := hc
    exact hx.q_end A (Or.inl rfl)
  have hwidth : width + 2 ≤ B := by simpa [L, start] using hB 8
  have hw := copyLen_spec (by decide : ([8, 1, 7] : List (Fin 11)).Nodup)
    (L := A) (B := B) (by simp [A, L, start, Lists.set]) hA
    (by simp [A, L, start, Lists.set]; exact hwidth)
  let M := A.set 1 (List.replicate width 1)
  have hw' : Complexity.Runs (LenOK B) (copyLenP 8 1 7) A M (8 * (width + 1)) := by
    simpa [A, L, start, Lists.set] using hw
  have hM : LenOK B M := by
    obtain ⟨_, _, hx⟩ := hw'
    exact hx.q_end M (Or.inl rfl)
  let H := (((M.set 0 (storage (SequentialStackBinary.pack width vs ++ tail))).set 1 []).set 2 []).set 3
    (List.replicate v 1)
  obtain ⟨T3, hr⟩ := SequentialWordRead.read_word_runs (by decide :
    ([0, 1, 2, 3, 4, 5, 6, 7] : List (Fin 11)).Nodup) hv
    (SequentialStackBinary.pack width vs ++ tail) (L := M)
    (by simp [M, A, L, start, Lists.set, SequentialStackBinary.pack, List.append_assoc])
    (by simp [M]) (by simp [M, A, L, start, Lists.set]) (by simp [M, A, Lists.set])
    (by simp [M, A, L, start, Lists.set]) (by simp [M, A, L, start, Lists.set])
    (by simp [M, A, L, start, Lists.set]) (by simp [M, A, L, start, Lists.set]) hM hval
  have hH : LenOK B H := by
    obtain ⟨_, _, hx⟩ := hr
    exact hx.q_end H (Or.inl rfl)
  let N := H.set 9 (D ++ [2])
  have hN : LenOK B N := lenOK_set hH 9 (by simp; omega)
  have hD : H 9 = D := by simp [H, M, A, L, start, Lists.set]
  have hp : Complexity.Runs (LenOK B) (.push 9 2) H N 1 := by
    simpa only [hD] using runs_push (i := 9) (e := 2) hH hN
  have hN3 : N 3 = List.replicate v 1 := by simp [N, H, Lists.set]
  have hN9 : N 9 = D ++ [2] := by simp [N]
  have hvout := copyLen_spec (by decide : ([3, 9, 7] : List (Fin 11)).Nodup)
    (L := N) (B := B) (by simp [N, H, M, A, L, start, Lists.set]) hN
    (by simp [hN3, hN9]; omega)
  have he : N.set 9 (N 9 ++ List.replicate (N 3).length 1) =
      start width vs tail (D ++ 2 :: List.replicate v 1) v counter := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨
      i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [N, H, M, A, L, start, Lists.set, List.append_assoc]
  rw [he] at hvout
  exact ⟨_, hc.seq (hw'.seq (hr.seq (hp.seq hvout)))⟩

theorem fetch_tape {B width held v : Nat} (vs : List Nat) (tail : List Bool)
    (D counter : List Nat) (hv : v < 2 ^ width)
    (hB : LenOK B (start width (v :: vs) tail D held counter))
    (hval : 3 * v + 4 ≤ B) (hout : D.length + v + 3 ≤ B)
    (τ : Tapes 11) (hτ : Rep (start width (v :: vs) tail D held counter) τ) :
    ∃ t τ', Exec (TFits B) fetch.compile τ t (.cont τ') ∧
      Rep (start width vs tail (D ++ 2 :: List.replicate v 1) v counter) τ' := by
  obtain ⟨_, hr⟩ := fetch_runs vs tail D counter hv hB hval hout
  obtain ⟨t, τ', _, he, hr'⟩ := runs_tape hr τ hτ
  exact ⟨t, τ', he, hr'⟩

def after (held : Nat) : List Nat → Nat
  | [] => held
  | v :: vs => after v vs

theorem after_append (held : Nat) (vs ws : List Nat) :
    after held (vs ++ ws) = after (after held vs) ws := by
  induction vs generalizing held with
  | nil => rfl
  | cons v vs ih => exact ih v

theorem repeat_fetch_runs {B width held : Nat} (vs rest : List Nat) (tail : List Bool)
    (D counter : List Nat) (hv : ∀ v ∈ vs, v < 2 ^ width)
    (hval : ∀ v ∈ vs, 3 * v + 4 ≤ B)
    (hB : LenOK B (start width (vs ++ rest) tail D held counter))
    (hloc : D.length + (SequentialFrontRead.locals vs).length + 2 ≤ B) :
    ∃ T, Complexity.Runs (LenOK B) (repeatP 3 fetch vs.length)
      (start width (vs ++ rest) tail D held counter)
      (start width rest tail (D ++ SequentialFrontRead.locals vs) (after held vs) counter) T := by
  induction vs generalizing held D with
  | nil => simpa [repeatP, after, SequentialFrontRead.locals] using
      (show ∃ T, Complexity.Runs (LenOK B) (skipP 3) (start width rest tail D held counter)
        (start width rest tail D held counter) T from ⟨1, runs_skip 3 hB⟩)
  | cons v vs ih =>
    have hspace : D.length + (v + 1) + (SequentialFrontRead.locals vs).length + 2 ≤ B := by
      simpa [SequentialFrontRead.locals, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloc
    obtain ⟨T1, hr1⟩ := fetch_runs (vs ++ rest) tail D counter (hv v (by simp)) hB
      (hval v (by simp)) (by omega)
    have hnext : LenOK B (start width (vs ++ rest) tail (D ++ 2 :: List.replicate v 1) v counter) := by
      obtain ⟨_, _, hx⟩ := hr1
      exact hx.q_end _ (Or.inl rfl)
    obtain ⟨T2, hr2⟩ := ih (held := v) (D := D ++ 2 :: List.replicate v 1)
      (fun n hn => hv n (by simp [hn])) (fun n hn => hval n (by simp [hn])) hnext
      (by simp; omega)
    have he : (D ++ 2 :: List.replicate v 1) ++ SequentialFrontRead.locals vs =
        D ++ SequentialFrontRead.locals (v :: vs) := by simp [SequentialFrontRead.locals, List.append_assoc]
    rw [he] at hr2
    exact ⟨T1 + T2, hr1.seq hr2⟩

def countedFetch (stride : Nat) : LProg 11 :=
  .loop 10 nonEmpty (.seq (repeatP 3 fetch stride) (.pop 10))

theorem counted_fetch_runs {B width held n stride : Nat} (vs rest : List Nat) (tail : List Bool)
    (D : List Nat) (hlen : vs.length = n * stride)
    (hv : ∀ v ∈ vs, v < 2 ^ width) (hval : ∀ v ∈ vs, 3 * v + 4 ≤ B)
    (hB : LenOK B (start width (vs ++ rest) tail D held (List.replicate n 1)))
    (hloc : D.length + (SequentialFrontRead.locals vs).length + 2 ≤ B) :
    ∃ T, Complexity.Runs (LenOK B) (countedFetch stride)
      (start width (vs ++ rest) tail D held (List.replicate n 1))
      (start width rest tail (D ++ SequentialFrontRead.locals vs) (after held vs) []) T := by
  induction n generalizing vs held D with
  | zero =>
    have he : vs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst vs
    simpa [after, SequentialFrontRead.locals] using
      (show ∃ T, Complexity.Runs (LenOK B) (countedFetch stride) (start width rest tail D held [])
        (start width rest tail D held []) T from
          ⟨1, 1, Nat.le_refl _, .loopF hB (by simp [start, nonEmpty, lastSym])⟩)
  | succ n ih =>
    let block := vs.take stride
    let more := vs.drop stride
    have hsplit : vs = block ++ more := (List.take_append_drop _ _).symm
    have hlong : stride ≤ vs.length := by rw [hlen, Nat.add_mul, Nat.one_mul]; omega
    have hblock : block.length = stride := by simp [block, Nat.min_eq_left hlong]
    have hmore : more.length = n * stride := by simp [more, hlen, Nat.add_mul]
    have hspace : D.length + (SequentialFrontRead.locals block).length +
        (SequentialFrontRead.locals more).length + 2 ≤ B := by
      simpa [hsplit, SequentialFrontRead.locals, List.flatMap_append, Nat.add_assoc] using hloc
    have hbin : LenOK B (start width (block ++ (more ++ rest)) tail D held (List.replicate (n + 1) 1)) := by
      simpa only [hsplit, List.append_assoc] using hB
    obtain ⟨T1, hr1⟩ := repeat_fetch_runs block (more ++ rest) tail D (List.replicate (n + 1) 1)
      (fun v hm => hv v (by simp [hsplit, hm])) (fun v hm => hval v (by simp [hsplit, hm])) hbin (by omega)
    rw [hblock] at hr1
    have hpost : LenOK B (start width (more ++ rest) tail (D ++ SequentialFrontRead.locals block)
        (after held block) (List.replicate (n + 1) 1)) := by
      obtain ⟨_, _, hx⟩ := hr1
      exact hx.q_end _ (Or.inl rfl)
    have hp := pop_unary (n := n) (i := (10 : Fin 11))
      (L := start width (more ++ rest) tail (D ++ SequentialFrontRead.locals block)
        (after held block) (List.replicate (n + 1) 1)) (by simp [start]) hpost
    have he : (start width (more ++ rest) tail (D ++ SequentialFrontRead.locals block)
        (after held block) (List.replicate (n + 1) 1)).set 10 (List.replicate n 1) =
        start width (more ++ rest) tail (D ++ SequentialFrontRead.locals block)
          (after held block) (List.replicate n 1) := by
      funext i
      by_cases hi : i = 10 <;> simp_all [start, Lists.set]
    rw [he] at hp
    have hnext : LenOK B (start width (more ++ rest) tail (D ++ SequentialFrontRead.locals block)
        (after held block) (List.replicate n 1)) := by
      obtain ⟨_, _, hx⟩ := hp
      exact hx.q_end _ (Or.inl rfl)
    obtain ⟨T2, hr2⟩ := ih more (D := D ++ SequentialFrontRead.locals block) hmore
      (fun v hm => hv v (by simp [hsplit, hm])) (fun v hm => hval v (by simp [hsplit, hm])) hnext
      (by simp; omega)
    have hout : start width rest tail ((D ++ SequentialFrontRead.locals block) ++ SequentialFrontRead.locals more)
        (after (after held block) more) [] =
        start width rest tail (D ++ SequentialFrontRead.locals vs) (after held vs) [] := by
      simp [hsplit, SequentialFrontRead.locals, List.flatMap_append, after_append, List.append_assoc]
    rw [hout] at hr2
    obtain ⟨t1, _, hx1⟩ := hr1.seq hp
    obtain ⟨t2, _, hx2⟩ := hr2
    have hloop : Complexity.Runs (LenOK B) (countedFetch stride)
        (start width (block ++ (more ++ rest)) tail D held (List.replicate (n + 1) 1))
        (start width rest tail (D ++ SequentialFrontRead.locals vs) (after held vs) []) (t1 + 1 + t2) :=
      ⟨t1 + 1 + t2, Nat.le_refl _, .loopC hbin
        (unary_nonEmpty (i := 10) (n := n) (by simp [start])) hx1 hx2⟩
    exact ⟨_, by simpa only [hsplit, List.append_assoc] using hloop⟩

end Shallot.MacroPeg.CBV.SequentialFieldFetch
