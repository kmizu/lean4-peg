import MacroPeg.CBV.SequentialWordWrite

/-! Compose actual field reading, counter restoration, and field writing.
The full binary tail is preserved throughout, without decoding it. -/

namespace Shallot.MacroPeg.CBV.SequentialWordCycle

open Complexity Complexity.BinaryWord SequentialStackBinary

/-- Stream, counter, word, accumulator, two, quotient, flag, temporary, width. -/
def start (width n : Nat) (tail : List Bool) : Lists 9 := fun i =>
  if i = 0 then storage (word width n ++ tail)
  else if i = 1 ∨ i = 8 then List.replicate width 1
  else if i = 4 then [1, 1] else []

def cycle : LProg 9 :=
  .seq (readP 0 1 2 3 4 5 6 7)
    (.seq (copyLenP 8 1 7) (writeP 3 5 6 1 2 0))

/-- A whole read/write cycle restores the original stream and clears its
consumable width counter. The permanent width is retained for later fields. -/
theorem cycle_runs {B width n : Nat} (hn : n < 2 ^ width) (tail : List Bool)
    (hcap : 3 * n + 4 ≤ B) (hstream : tail.length + width + 2 ≤ B) :
    ∃ T, Runs (LenOK B) cycle (start width n tail)
      ((start width n tail).set 1 []) T := by
  let L := start width n tail
  have hB : LenOK B L := by
    intro i
    simp only [L, start]
    split
    · simp [storage, word_length]; omega
    · split
      · simp; omega
      · split <;> simp <;> omega
  let M := (((L.set 0 (storage tail)).set 1 []).set 2 []).set 3 (List.replicate n 1)
  obtain ⟨T1, hr⟩ := SequentialWordRead.read_word_runs (by decide :
    ([0, 1, 2, 3, 4, 5, 6, 7] : List (Fin 9)).Nodup) hn tail
    (L := L) (by simp [L, start]) (by simp [L, start])
    (by simp [L, start]) (by simp [L, start]) (by simp [L, start])
    (by simp [L, start]) (by simp [L, start]) (by simp [L, start]) hB hcap
  have hM : LenOK B M := by
    obtain ⟨_, _, hx⟩ := hr
    exact hx.q_end M (Or.inl rfl)
  let F := M.set 1 (List.replicate width 1)
  have hcopy := copyLen_spec (by decide : ([8, 1, 7] : List (Fin 9)).Nodup)
    (L := M) (B := B) (by simp [M, L, start, Lists.set]) hM
    (by simp [M, L, start, Lists.set]; omega)
  have hc : Runs (LenOK B) (copyLenP 8 1 7) M F (8 * (width + 1)) := by
    simpa [M, L, start, Lists.set] using hcopy
  have hF : LenOK B F := by
    obtain ⟨_, _, hx⟩ := hc
    exact hx.q_end F (Or.inl rfl)
  obtain ⟨T3, hw⟩ := SequentialWordWrite.write_word_runs (by decide :
    ([3, 5, 6, 1, 2, 0] : List (Fin 9)).Nodup) hn tail
    (L := F) (by simp [F, M, Lists.set]) (by simp [F, M, L, start, Lists.set])
    (by simp [F, M, L, start, Lists.set]) (by simp [F])
    (by simp [F, M, Lists.set]) (by simp [F, M, Lists.set]) hF (by omega) hstream
  have he : (((((F.set 3 []).set 5 []).set 6 []).set 1 []).set 2 []).set 0
      (storage (word width n ++ tail)) = L.set 1 [] := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by
      omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [F, M, L, start, Lists.set]
  rw [he] at hw
  exact ⟨_, hr.seq (hc.seq hw)⟩

theorem cycle_tape {B width n : Nat} (hn : n < 2 ^ width) (tail : List Bool)
    (hcap : 3 * n + 4 ≤ B) (hstream : tail.length + width + 2 ≤ B)
    (τ : Tapes 9) (hτ : Rep (start width n tail) τ) :
    ∃ t τ', Exec (TFits B) cycle.compile τ t (.cont τ') ∧
      Rep ((start width n tail).set 1 []) τ' := by
  obtain ⟨_, hr⟩ := cycle_runs hn tail hcap hstream
  obtain ⟨t, τ', _, he, hr'⟩ := runs_tape hr τ hτ
  exact ⟨t, τ', he, hr'⟩

open SequentialStack SequentialStackCodec SequentialStackCodecBound
open CBVtoCBN (compilerNodes)

/-- The binary continuation plus linear scratch for one local field. -/
noncomputable def fieldSpace (g : MGrammar) (x : List Char) (e : MExp) (c : Config) : Nat :=
  3 * numberBound g x e + 4 + (encodeBits (compilerNodes g e) (width g x e) c).length

theorem fieldSpace_bound (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) :
    fieldSpace g x e c ≤
      (3 * numberCoefficient g e + 4) * (x.length + 1) +
      (cellCoefficient g e * (x.length + 1)) *
        ((x.length + 1).log2 + (numberCoefficient g e).log2 + 2) := by
  have hn := numberBound_linear g x e
  have hb := reachable_bit_bound g x e c h
  have h4 : 4 ≤ 4 * (x.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold fieldSpace
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

/-- Any numeric field in any reachable configuration can make this actual
roundtrip. The rest of the encoded suffix stays binary. This local interface
starts at the chosen field; traversing or storing earlier fields is not supplied
by this theorem. -/
theorem field_cycle_runs (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c)
    (before rest : List Nat) (v : Nat)
    (hc : encode (compilerNodes g e) c = before ++ v :: rest) :
    ∃ T, Complexity.Runs (LenOK (fieldSpace g x e c)) cycle
      (start (width g x e) v (SequentialStackBinary.pack (width g x e) rest))
      ((start (width g x e) v (SequentialStackBinary.pack (width g x e) rest)).set 1 []) T := by
  have hv := reachable_numbers g x e c h v (by simp [hc])
  have hn : v < 2 ^ width g x e := Nat.lt_of_le_of_lt hv Nat.lt_log2_self
  have hl : rest.length + 1 ≤ (encode (compilerNodes g e) c).length := by
    rw [hc]; simp
  have hm := Nat.mul_le_mul_right (width g x e) hl
  have hs : (SequentialStackBinary.pack (width g x e) rest).length + width g x e ≤
      (encodeBits (compilerNodes g e) (width g x e) c).length := by
    simpa only [encodeBits, SequentialStackBinary.pack_length, Nat.add_mul, Nat.one_mul] using hm
  exact cycle_runs hn _ (by unfold fieldSpace; omega) (by unfold fieldSpace; omega)

theorem field_cycle_tape (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c)
    (before rest : List Nat) (v : Nat)
    (hc : encode (compilerNodes g e) c = before ++ v :: rest)
    (τ : Tapes 9) (hτ : Rep (start (width g x e) v (SequentialStackBinary.pack (width g x e) rest)) τ) :
    ∃ t τ', Exec (TFits (fieldSpace g x e c)) cycle.compile τ t (.cont τ') ∧
      Rep ((start (width g x e) v (SequentialStackBinary.pack (width g x e) rest)).set 1 []) τ' := by
  obtain ⟨_, hr⟩ := field_cycle_runs g x e c h before rest v hc
  obtain ⟨t, τ', _, he, hr'⟩ := runs_tape hr τ hτ
  exact ⟨t, τ', he, hr'⟩

end Shallot.MacroPeg.CBV.SequentialWordCycle
