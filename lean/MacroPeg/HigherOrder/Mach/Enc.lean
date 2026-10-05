import MacroPeg.HigherOrder.Mach.ReadAll
import Complexity.NMacros

/-!
# The reading machine's state on stacks

The machine program works on `40` stacks of numbers. A state of the reading machine (`PSt`) is laid out as:

* `1` the tokens, `2` the control stack, `3` the types (each with its head on top);
* `4` the items of the current body (four numbers each, oldest at the bottom), `5` the current context;
* `6` the arrows and `7` the contexts (two numbers per entry), `8` the literals (codes plus one, each ended by `0`);
* `9` the rule types, `10` the finished bodies (each ended by `13`), `11` their number, `12` the start, `13` the
  string;
* `14`–`17` the numbers of arrows, contexts, literals and rule types; from `18` on, scratch.

`enc_with_*`: changing a field changes one stack.
-/

namespace Shallot.MacroPeg.Mach

open Complexity

/-- The number of stacks. -/
abbrev NK : Nat := 40

def encItem (it : MItem) : List Nat := [it.tag, it.a, it.b, it.ctx]
def encItems (l : List MItem) : List Nat := l.flatMap encItem
def encPairs (l : List (Nat × Nat)) : List Nat := l.flatMap (fun p => [p.1, p.2])
def encLits (lt : List (List Nat)) : List Nat := lt.flatMap (fun str => str.map (· + 1) ++ [0])
def encBodies (bs : List (List MItem)) : List Nat := bs.flatMap (fun b => encItems b ++ [13])

/-- The contents of the stacks `0`–`17` of a reading state. -/
def encList (s : PSt) : List (List Nat) :=
  [[], s.tk.reverse, s.ctl.reverse, s.ty.reverse, encItems s.out.reverse, [s.cur], encPairs s.tt, encPairs s.ct,
    encLits s.lt, s.rt, encBodies s.bodies, [s.bodies.length], encItems s.start, s.x, [s.tt.length],
    [s.ct.length], [s.lt.length], [s.rt.length]]

/-- The stacks of a reading state. -/
def enc (s : PSt) : Lists NK := fun i => (encList s).getD i.val []

theorem length_encList (s : PSt) : (encList s).length = 18 := rfl

/-- Changing stack `k < 18` of the layout. -/
theorem enc_set {s s' : PSt} {k : Nat} (hk : k < 18) {v : List Nat} (h : encList s' = (encList s).set k v) :
    enc s' = (enc s).set ⟨k, by show k < 40; omega⟩ v := by
  funext i
  simp only [enc, Lists.set, h]
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hi : i = ⟨k, by show k < 40; omega⟩
  · subst hi; simp [length_encList, hk]
  · have : k ≠ i.val := fun e => hi (Fin.ext e.symm)
    simp [hi, this, List.getD_eq_getElem?_getD]

/-- Changing two stacks of the layout. -/
theorem enc_set₂ {s s' : PSt} {k k' : Nat} (hk : k < 18) (hk' : k' < 18) {v v' : List Nat}
    (h : encList s' = ((encList s).set k v).set k' v') :
    enc s' = ((enc s).set ⟨k, by show k < 40; omega⟩ v).set ⟨k', by show k' < 40; omega⟩ v' := by
  funext i
  simp only [enc, Lists.set, h]
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getElem?_set]
  by_cases hi' : i = ⟨k', by show k' < 40; omega⟩
  · subst hi'; simp [length_encList, hk']
  · have : k' ≠ i.val := fun e => hi' (Fin.ext e.symm)
    by_cases hi : i = ⟨k, by show k < 40; omega⟩
    · subst hi; simp [hi', this, length_encList, hk]
    · have : k ≠ i.val := fun e => hi (Fin.ext e.symm)
      simp [hi, hi', this, *, List.getD_eq_getElem?_getD]

/-! ## Changing one field -/

section With

variable (s : PSt)

theorem enc_with_tk (v : List Nat) : enc { s with tk := v } = (enc s).set 1 v.reverse :=
  enc_set (k := 1) (by omega) rfl
theorem enc_with_ctl (v : List Nat) : enc { s with ctl := v } = (enc s).set 2 v.reverse :=
  enc_set (k := 2) (by omega) rfl
theorem enc_with_ty (v : List Nat) : enc { s with ty := v } = (enc s).set 3 v.reverse :=
  enc_set (k := 3) (by omega) rfl
theorem enc_with_out (v : List MItem) : enc { s with out := v } = (enc s).set 4 (encItems v.reverse) :=
  enc_set (k := 4) (by omega) rfl
theorem enc_with_cur (v : Nat) : enc { s with cur := v } = (enc s).set 5 [v] :=
  enc_set (k := 5) (by omega) rfl
theorem enc_with_tt (v : List (Nat × Nat)) :
    enc { s with tt := v } = ((enc s).set 6 (encPairs v)).set 14 [v.length] :=
  enc_set₂ (k := 6) (k' := 14) (by omega) (by omega) rfl
theorem enc_with_ct (v : List (Nat × Nat)) :
    enc { s with ct := v } = ((enc s).set 7 (encPairs v)).set 15 [v.length] :=
  enc_set₂ (k := 7) (k' := 15) (by omega) (by omega) rfl
theorem enc_with_lt (v : List (List Nat)) : enc { s with lt := v } = ((enc s).set 8 (encLits v)).set 16 [v.length] :=
  enc_set₂ (k := 8) (k' := 16) (by omega) (by omega) rfl
theorem enc_with_rt (v : List Nat) : enc { s with rt := v } = ((enc s).set 9 v).set 17 [v.length] :=
  enc_set₂ (k := 9) (k' := 17) (by omega) (by omega) rfl
theorem enc_with_start (v : List MItem) : enc { s with start := v } = (enc s).set 12 (encItems v) :=
  enc_set (k := 12) (by omega) rfl
theorem enc_with_x (v : List Nat) : enc { s with x := v } = (enc s).set 13 v :=
  enc_set (k := 13) (by omega) rfl

theorem enc_tk : enc s 1 = s.tk.reverse := rfl
theorem enc_ctl : enc s 2 = s.ctl.reverse := rfl
theorem enc_ty : enc s 3 = s.ty.reverse := rfl
theorem enc_out : enc s 4 = encItems s.out.reverse := rfl
theorem enc_cur : enc s 5 = [s.cur] := rfl
theorem enc_tt : enc s 6 = encPairs s.tt := rfl
theorem enc_ct : enc s 7 = encPairs s.ct := rfl
theorem enc_lt : enc s 8 = encLits s.lt := rfl
theorem enc_rt : enc s 9 = s.rt := rfl
theorem enc_bod : enc s 10 = encBodies s.bodies := rfl
theorem enc_nb : enc s 11 = [s.bodies.length] := rfl
theorem enc_start : enc s 12 = encItems s.start := rfl
theorem enc_x : enc s 13 = s.x := rfl
theorem enc_ntt : enc s 14 = [s.tt.length] := rfl
theorem enc_nct : enc s 15 = [s.ct.length] := rfl
theorem enc_nlt : enc s 16 = [s.lt.length] := rfl
theorem enc_nrt : enc s 17 = [s.rt.length] := rfl
theorem enc_scratch (i : Fin NK) (h : 18 ≤ i.val) : enc s i = [] := by
  simp only [enc, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by rw [length_encList]; exact h)]; rfl

end With

end Shallot.MacroPeg.Mach
