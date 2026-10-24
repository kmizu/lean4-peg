import MacroPeg.CBV.SequentialWordRead
import Complexity.BinaryWordWrite

/-! Write a local Seq field back to the fixed-width binary continuation stream,
with bounds on intermediate list and tape states. -/

namespace Shallot.MacroPeg.CBV.SequentialWordWrite

open Complexity Complexity.BinaryWord SequentialStackBinary

theorem lowWord_eq (width n : Nat) : lowWord width n = (word width n).map bit := by
  induction width generalizing n with
  | zero => rfl
  | succ width ih =>
    simp only [lowWord, word, List.map_cons, ih]
    congr 1
    have hm : n % 2 < 2 := Nat.mod_lt _ (by decide)
    by_cases h : n % 2 = 1 <;> simp [bit, h] <;> omega

/-- Add the exact existing Seq word format to an arbitrary untouched binary
tail. All local value/counter/scratch registers end empty. -/
theorem write_word_runs {k : Nat} {a q flag count bits dst : Fin k}
    (hd : [a, q, flag, count, bits, dst].Nodup) {B width n : Nat}
    (hn : n < 2 ^ width) {L : Lists k} (tail : List Bool)
    (ha : L a = List.replicate n 1) (hq : L q = []) (hf : L flag = [])
    (hc : L count = List.replicate width 1) (hb : L bits = [])
    (hdst : L dst = storage tail)
    (hB : LenOK B L) (hcap : n + 3 ≤ B) (hout : tail.length + width + 2 ≤ B) :
    ∃ T, Runs (LenOK B) (writeP a q flag count bits dst) L
      ((((((L.set a []).set q []).set flag []).set count []).set bits []).set dst
        (storage (word width n ++ tail))) T := by
  have hr := write_runs hd hn ha hq hf hc hb hB hcap (by simpa [hdst, storage] using hout)
  simpa only [hdst, lowWord_eq, storage, List.map_append, List.reverse_append] using hr

/-- The compiled writer respects the capacity during every tape scan and copy,
as well as at list instruction boundaries. -/
theorem write_word_tape {k : Nat} {a q flag count bits dst : Fin k}
    (hd : [a, q, flag, count, bits, dst].Nodup) {B width n : Nat}
    (hn : n < 2 ^ width) {L : Lists k} (tail : List Bool)
    (ha : L a = List.replicate n 1) (hq : L q = []) (hf : L flag = [])
    (hc : L count = List.replicate width 1) (hb : L bits = [])
    (hdst : L dst = storage tail)
    (hB : LenOK B L) (hcap : n + 3 ≤ B) (hout : tail.length + width + 2 ≤ B)
    (τ : Tapes k) (hτ : Rep L τ) :
    ∃ t τ', Exec (TFits B) (writeP a q flag count bits dst).compile τ t (.cont τ') ∧
      Rep ((((((L.set a []).set q []).set flag []).set count []).set bits []).set dst
        (storage (word width n ++ tail))) τ' := by
  obtain ⟨_, hr⟩ := write_word_runs hd hn tail ha hq hf hc hb hdst hB hcap hout
  obtain ⟨t, τ', _, he, hr'⟩ := runs_tape hr τ hτ
  exact ⟨t, τ', he, hr'⟩

end Shallot.MacroPeg.CBV.SequentialWordWrite
