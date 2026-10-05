import MacroPeg.HigherOrder.KExp.Run

/-!
# Order-`j` Macro PEG is `j`-EXPTIME-hard

`KEXP j` is the class of languages decided by a multi-tape machine (`Complexity.TM`) that halts within
`tower j (c * (n + 1) ^ d)` steps. For such a machine `M`, the tableau grammar `gT M (j - 1)` is a well-typed grammar
of order `j` with a closed start parser, and `w ↦ encBits (c + 1) (d + 1) w` (computable in polynomial time,
`enc_polytime`) maps `w` to an input that the grammar consumes iff `M` accepts `w` (`kexp_reduction`). So recognition
for fixed well-typed grammars of order `j` is `j`-EXPTIME-hard (`kexp_hard`), for every `j ≥ 1`, without assuming any
external fact. With the upper bound `decideCost_le` (order `j` grammars are decided at cost `tower j (poly)`), order `j`
is `j`-EXPTIME-complete in the cost model.

Grammars read characters; a bit string is read as 4-bit tokens (`ofBits`, as in the TQBF reduction), mapped to
characters by `tokChar` (`MPEG`).
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Levels
open Shallot.MacroPeg.Tableau

/-! ## The classes -/

/-- `M` halts within `T |w|` steps on every input `w`. -/
def TimeBounded {k : Nat} (M : TM k) (T : Nat → Nat) : Prop := ∀ w, (M.run (initCfg k w) (T w.length)).halted

/-- `j`-EXPTIME: decided by a machine halting within `tower j` of a polynomial. -/
def KEXP (j : Nat) (L : Lang) : Prop :=
  ∃ (kt : Nat) (M : TM kt) (T : Nat → Nat) (c d : Nat),
    (∀ n, T n ≤ tower j (c * (n + 1) ^ d)) ∧ M.Decides L ∧ TimeBounded M T

/-- The language of a grammar `g` with start `e`, on bit strings read as 4-bit tokens. -/
def MPEG (g : HGrammar) (e : HExp) : Lang := fun bits => HObs g e ((ofBits bits).map tokChar) (some [])

/-! ## Arithmetic -/

theorem tower_lt_succ : ∀ (k a : Nat), tower k a < tower k (a + 1)
  | 0, _ => by simp
  | k + 1, a => by
    simp only [tower_succ]
    exact Nat.pow_lt_pow_right (by decide) (tower_lt_succ k a)

theorem tower_lt (k : Nat) {a b : Nat} (h : a < b) : tower k a < tower k b :=
  Nat.lt_of_lt_of_le (tower_lt_succ k a) (tower_mono k h)

/-- The number of bit sites exceeds the time exponent and the input length. -/
theorem sites_large (c d n : Nat) : c * (n + 1) ^ d < rS (c + 1) (d + 1) n ∧ n < rS (c + 1) (d + 1) n := by
  have hp : 0 < (n + 1) ^ d := Nat.pow_pos (by omega)
  have e : rS (c + 1) (d + 1) n = (c + 1) * ((n + 1) ^ d * (n + 1)) := by simp [rS, rP, Nat.pow_succ]
  have h1 : (c + 1) * (n + 1) ^ d ≤ (c + 1) * ((n + 1) ^ d * (n + 1)) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
  have h2 : n + 1 ≤ (n + 1) ^ d * (n + 1) := Nat.le_mul_of_pos_left _ hp
  have h3 : (n + 1) ^ d * (n + 1) ≤ (c + 1) * ((n + 1) ^ d * (n + 1)) := Nat.le_mul_of_pos_left _ (by omega)
  rw [Nat.succ_mul] at h1
  rw [e]
  omega

/-! ## The reduction -/

/-- The output, read back as characters, is the encoding with `rS c d |w|` bit sites. -/
theorem decode_encBits (c d : Nat) (w : List Bool) (hn : w.length ≤ rS c d w.length) :
    (ofBits (encBits c d w)).map tokChar = encChars (rS c d w.length) w := by
  unfold encBits
  rw [ofBits_toBits _ (encT_tokens _)]
  exact encT_denote w _ 0 _ hn

/-- A machine halted at two times is in the same state. -/
theorem halted_state {k : Nat} (M : TM k) (c : Complexity.Cfg k) {t u : Nat} (ht : (M.run c t).halted)
    (hu : (M.run c u).halted) : (M.run c t).state = (M.run c u).state := by
  rcases Nat.le_total t u with h | h
  · rw [TM.run_stays M c h ht]
  · rw [TM.run_stays M c h hu]

/-- **The reduction is correct**: for `j ≥ 1`, `w` is accepted iff the order-`j` tableau grammar consumes its
encoding. -/
theorem kexp_reduction {j : Nat} (hj : 1 ≤ j) {kt : Nat} {M : TM kt} {T : Nat → Nat} {c d : Nat} {L : Lang}
    (hT : ∀ n, T n ≤ tower j (c * (n + 1) ^ d)) (hdec : M.Decides L) (htb : TimeBounded M T) (w : List Bool) :
    L w ↔ MPEG (gT M (j - 1)) (startT (j - 1)) (encBits (c + 1) (d + 1) w) := by
  obtain ⟨hlt, hnm⟩ := sites_large c d w.length
  have hdecode := decode_encBits (c + 1) (d + 1) w (Nat.le_of_lt hnm)
  generalize rS (c + 1) (d + 1) w.length = m at hlt hnm hdecode
  have hE : E m (j - 1) = tower j m := by simp only [E]; congr 1; omega
  have hn : w.length < E m (j - 1) := by rw [hE]; exact Nat.lt_of_lt_of_le hnm (le_tower j m)
  have hTE : T w.length ≤ E m (j - 1) - 1 := by
    have := Nat.lt_of_le_of_lt (hT w.length) (tower_lt j hlt)
    rw [hE]; omega
  have hspec := spec_all (gT_levels M (j - 1)) m (inputTail w) (j - 1) (Nat.le_refl _)
  unfold MPEG
  rw [hdecode, start_obs hspec hn]
  obtain ⟨t, hht, hiff⟩ := hdec w
  rw [← hiff, cfg, TM.run_stays M _ hTE (htb w), halted_state M _ hht (htb w)]

/-- **Order-`j` Macro PEG is `j`-EXPTIME-hard** (`j ≥ 1`): every `j`-EXPTIME language reduces in polynomial time to
the language of a well-typed grammar of order `j` with a closed start parser. -/
theorem kexp_hard {j : Nat} (hj : 1 ≤ j) {L : Lang} (hL : KEXP j L) :
    ∃ (g : HGrammar) (s : HExp), g.WellTyped ∧ g.order = j ∧ HasTy g.types [] s .p ∧ Reduces L (MPEG g s) := by
  obtain ⟨kt, M, T, c, d, hT, hdec, htb⟩ := hL
  refine ⟨gT M (j - 1), startT (j - 1), gT_wellTyped M _, ?_, startT_hasTy M _,
    encBits (c + 1) (d + 1), enc_polytime _ _, kexp_reduction hj hT hdec htb⟩
  rw [gT_order]; omega

end Shallot.MacroPeg.KExp
