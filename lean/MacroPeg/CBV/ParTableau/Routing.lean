import MacroPeg.CBV.ParTableau.Transitions
import MacroPeg.CBV.ParSimulation.LookupRouting

namespace Shallot.MacroPeg.CBV.ParTableau

open PrefixCounters
open CBVtoCBN (RulesAt predClock)
open Complexity (TM)

def Timed {k : Nat} : Node k → Prop
  | .state _ | .head _ | .cell _ _ => True
  | _ => False

theorem timed_rawRules {k : Nat} (M : TM k) (digits base : Nat) (node : Node k) (ht : Timed node) :
    rawRules M digits base node = timeRules M digits base node := by
  cases node <;> simp_all [Timed, rawRules]

theorem timed_clock_at {k : Nat} (M : TM k) (digits : Nat) (node : Node k)
    (hn : node ∈ nodes M) (ht : Timed node) :
    RulesAt (compile M digits) (address M digits node)
      (clockBlock (address M digits node) 0 (address M digits node + nextSlot digits)
        (address M digits node + zeroSlot digits) digits digits) := by
  intro j hj
  have hraw := timed_rawRules M digits (address M digits node) node ht
  have hh := compile_raw_at M digits node hn j (by
    rw [hraw, timeRules, List.length_append]
    omega)
  rw [hraw, timeRules, List.getElem?_append_left hj] at hh
  simpa only [ruleAtM_eq_getElem?] using hh

/-- The actual compiled state/head/cell entry performs a predecessor and
dispatches to its own initial or next-time rule, preserving all observations. -/
theorem timed_call_iff {k : Nat} (M : TM k) (digits : Nat) (node : Node k)
    (hn : node ∈ nodes M) (ht : Timed node) (x : List Char) (time position : List Nat)
    (hTime : time.length = digits) (hPos : position.length = digits)
    (hv : ∀ a ∈ time, a ≤ x.length) (r : Option (List Char)) :
    SObs (compile M digits) .callByValuePar
      (.call (address M digits node) (prefixValues x (x.length :: (time ++ position)))) x r ↔
      match predClock x.length time with
      | none => SObs (compile M digits) .callByValuePar
          (.call (address M digits node + zeroSlot digits) (prefixValues x position)) x r
      | some previous => SObs (compile M digits) .callByValuePar
          (.call (address M digits node + nextSlot digits)
            (prefixValues x (x.length :: (previous ++ position)))) x r := by
  have hh := timed_clock_at M digits node hn ht
  have hh' : RulesAt (compile M digits) (address M digits node)
      (clockBlock (address M digits node) 0 (address M digits node + nextSlot digits)
        (address M digits node + zeroSlot digits) digits position.length) := by simpa [hPos] using hh
  exact ParSimulation.RulesAt.clock_iff position hh' (equal_rule M digits) x time hTime hv r

theorem timed_zero_rule {k : Nat} (M : TM k) (digits : Nat) (node : Node k)
    (hn : node ∈ nodes M) (ht : Timed node) :
    ruleAtM (compile M digits).rules (address M digits node + zeroSlot digits) =
      some ⟨digits, zeroBody digits node⟩ := by
  have hh := compile_at M digits node hn (zeroSlot digits) (by unfold zeroSlot slotSize; omega)
  rw [timed_rawRules M digits (address M digits node) node ht, timeRules] at hh
  have hlen : zeroSlot digits =
      (clockBlock (address M digits node) 0 (address M digits node + nextSlot digits)
        (address M digits node + zeroSlot digits) digits digits).length := by
    simp only [clockBlock_length, zeroSlot]
  rw [List.getElem?_append_right (by omega), ← hlen, Nat.sub_self] at hh
  exact hh

theorem timed_next_rule {k : Nat} (M : TM k) (digits : Nat) (node : Node k)
    (hn : node ∈ nodes M) (ht : Timed node) :
    ruleAtM (compile M digits).rules (address M digits node + nextSlot digits) =
      some ⟨width digits, nextBody M digits node⟩ := by
  have hh := compile_at M digits node hn (nextSlot digits) (by unfold nextSlot slotSize; omega)
  rw [timed_rawRules M digits (address M digits node) node ht, timeRules] at hh
  have hlen : nextSlot digits -
      (clockBlock (address M digits node) 0 (address M digits node + nextSlot digits)
        (address M digits node + zeroSlot digits) digits digits).length = 1 := by
    rw [clockBlock_length]; unfold nextSlot; omega
  rw [List.getElem?_append_right (by rw [clockBlock_length]; unfold nextSlot; omega), hlen] at hh
  exact hh

theorem read_entry_rule {k : Nat} (M : TM k) (digits : Nat) (i : Fin k) (s : Nat) (hs : s < M.na) :
    let base := address M digits (.read i s)
    ruleAtM (compile M digits).rules base = some ⟨width digits,
      tupleSearch (base + 1) (base + zeroSlot digits) digits (.param 0 :: timeRefs digits)⟩ := by
  have hh := compile_at M digits (.read i s) (read_mem M i s hs) 0 (by unfold slotSize; omega)
  simpa only [Nat.add_zero, rawRules, List.cons_append, List.nil_append, List.getElem?_cons_zero,
    Option.getD_some] using hh

theorem read_leaf_rule {k : Nat} (M : TM k) (digits : Nat) (i : Fin k) (s : Nat) (hs : s < M.na) :
    let base := address M digits (.read i s)
    ruleAtM (compile M digits).rules (base + zeroSlot digits) =
      some ⟨width digits, readLeaf M digits i s⟩ := by
  have hh := compile_at M digits (.read i s) (read_mem M i s hs) (zeroSlot digits)
    (by unfold zeroSlot slotSize; omega)
  simp only [rawRules, List.cons_append, List.nil_append] at hh
  rw [show zeroSlot digits = 2 * digits + 1 by unfold zeroSlot; omega,
    List.getElem?_cons_succ, List.getElem?_append_right (by rw [tupleRules_length]; omega),
    tupleRules_length, Nat.sub_self] at hh
  simpa only [zeroSlot, Nat.add_comm 1 (2 * digits), List.getElem?_cons_zero, Option.getD_some] using hh

theorem read_search_at {k : Nat} (M : TM k) (digits : Nat) (i : Fin k) (s : Nat) (hs : s < M.na) :
    let base := address M digits (.read i s)
    RulesAt (compile M digits) (base + 1)
      (tupleRules (base + 1) (base + zeroSlot digits) digits (1 + digits)) := by
  dsimp only
  intro j hj
  have hh := compile_raw_at M digits (.read i s) (read_mem M i s hs) (j + 1) (by
    simp only [rawRules, List.length_append, List.length_cons, List.length_nil] at *
    omega)
  simp only [rawRules, List.cons_append, List.nil_append, List.getElem?_cons_succ] at hh
  rw [List.getElem?_append_left hj] at hh
  simpa only [Nat.add_assoc, Nat.add_comm 1 j, ruleAtM_eq_getElem?] using hh

theorem tuple_rules_of_at {g : MGrammar} {entry leaf digits ctxSize : Nat}
    (h : RulesAt g entry (tupleRules entry leaf digits ctxSize)) :
    TupleRules g entry leaf digits ctxSize := by
  cases digits with
  | zero => trivial
  | succ d =>
    obtain ⟨pre, tail, hpre, hg⟩ := h.split (by simp [tupleRules])
    have hh := tupleRules_rules pre tail leaf (d + 1) ctxSize
    simpa only [hpre, ← hg] using hh

end Shallot.MacroPeg.CBV.ParTableau
