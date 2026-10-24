import MacroPeg.CBV.SequentialStackBinary
import Complexity.BinaryWord

/-! An actual streaming reader for the fixed-width fields in the Seq binary
configuration encoding. Only the selected field is converted to unary.
-/

namespace Shallot.MacroPeg.CBV.SequentialWordRead

open Complexity Complexity.BinaryWord SequentialStackBinary

theorem value_reverse (a : Nat) (bs : List Bool) :
    value a bs.reverse = 2 ^ bs.length * a + unword bs := by
  induction bs with
  | nil => simp [value, unword]
  | cons b bs ih =>
    rw [List.reverse_cons, value_append]
    simp only [value, ih, unword, List.length_cons, bit, Nat.pow_succ,
      Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm]
    omega

/-- An arbitrary suffix may contain the entire remaining binary stack.
The program consumes exactly `width` source bits, returns their natural value,
and restores the word and arithmetic scratch registers to empty. -/
theorem read_word_runs {k : Nat} {src count w acc two p2 ta tb : Fin k}
    (hd : [src, count, w, acc, two, p2, ta, tb].Nodup)
    {B width n : Nat} (hn : n < 2 ^ width) {L : Lists k} (tail : List Bool)
    (hs : L src = storage (word width n ++ tail))
    (hc : L count = List.replicate width 1)
    (hw : L w = []) (ha : L acc = [])
    (htwo : L two = [1, 1]) (hp2 : L p2 = [])
    (hta : L ta = []) (htb : L tb = [])
    (hB : LenOK B L) (hcap : 3 * n + 4 ≤ B) :
    ∃ T, Runs (LenOK B) (readP src count w acc two p2 ta tb) L
      ((((L.set src (storage tail)).set count []).set w []).set acc
        (List.replicate n 1)) T := by
  have hv : value 0 (word width n).reverse = n := by
    simp [value_reverse, unword_word hn]
  simpa only [hv] using read_runs hd (word width n) tail hs
    (by simpa only [word_length] using hc) hw ha htwo hp2 hta htb hB (by simpa only [hv] using hcap)

/-- Every intermediate tape state fits, not just the list states at instruction
boundaries. This still describes a single-field reader, not the whole Seq VM. -/
theorem read_word_tape {k : Nat} {src count w acc two p2 ta tb : Fin k}
    (hd : [src, count, w, acc, two, p2, ta, tb].Nodup)
    {B width n : Nat} (hn : n < 2 ^ width) {L : Lists k} (tail : List Bool)
    (hs : L src = storage (word width n ++ tail))
    (hc : L count = List.replicate width 1)
    (hw : L w = []) (ha : L acc = [])
    (htwo : L two = [1, 1]) (hp2 : L p2 = [])
    (hta : L ta = []) (htb : L tb = [])
    (hB : LenOK B L) (hcap : 3 * n + 4 ≤ B)
    (τ : Tapes k) (hτ : Rep L τ) :
    ∃ t τ', Exec (TFits B) (readP src count w acc two p2 ta tb).compile τ t (.cont τ') ∧
      Rep ((((L.set src (storage tail)).set count []).set w []).set acc
        (List.replicate n 1)) τ' := by
  obtain ⟨_, hr⟩ := read_word_runs hd hn tail hs hc hw ha htwo hp2 hta htb hB hcap
  obtain ⟨t, τ', _, he, hr'⟩ := runs_tape hr τ hτ
  exact ⟨t, τ', he, hr'⟩

end Shallot.MacroPeg.CBV.SequentialWordRead
