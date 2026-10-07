import Shallot.Peg.Undecidable.MachPrintKit
import Shallot.Peg.Undecidable.Bin

/-!
# Printing one side alternative

A word `w` lies on stack `r` as its length and then its symbols, the length on top. `copyWord` moves it onto `r2`
as it is. `emitWord sd` moves it too, and appends to `m` the numbers of the alternative of the side `sd` for the card
of index `j` (held on `i`): `blk sd j w` (`rn_emitWord`).
-/

namespace Shallot

open Complexity
open Complexity.Univ

/-- The numbers of the alternative `w (A_sd) #|^j$` of index `j` of the side `sd` with word `bin w`. -/
def blk (sd j : Nat) (w : List Nat) : List Nat :=
  [7, 6, 4, (bin w).length] ++ (bin w).map (fun b => (bitC b).toNat) ++ [6, 5, sd, 4, j + 2, 35] ++
    List.replicate j 124 ++ [36]

/-- The characters of `bin w` as numbers, as the program writes them. -/
def binChars (w : List Nat) : List Nat := (w.map fun a => List.replicate a 49 ++ [48]).flatten

theorem binChars_eq : ∀ w : List Nat, (bin w).map (fun b => (bitC b).toNat) = binChars w
  | [] => rfl
  | a :: w => by
    simp only [bin_cons, List.map_append, List.map_cons, binChars_eq w, List.map_replicate]
    simp only [binChars, List.map_cons, List.flatten_cons, bitC, List.append_assoc]
    rfl

theorem bin_length : ∀ w : List Nat, (bin w).length = (w.map (· + 1)).sum
  | [] => rfl
  | a :: w => by rw [bin_cons]; simp [bin_length w]; omega

/-! ## Copying a word -/

/-- Close a state equation. -/
macro "st_eq" : tactic => `(tactic| first | rfl | (simp [PS.upd, PS.get, mapTop_snoc]))


def copyWord : NProg UK :=
  .seq (pmv .r .c (by decide)) <| .seq (pdup .c .r2 (by decide)) <|
  .seq (.loop Fld.c.idx .pos (.seq (.prim (.dec Fld.c.idx)) (pmv .r .r2 (by decide)))) (.prim (.pop Fld.c.idx))

theorem foldl_r2 : ∀ (w : List Nat) (s : PS),
    w.foldl (fun s v => s.upd .r2 (s.r2 ++ [v])) s = s.upd .r2 (s.r2 ++ w)
  | [], s => by cases s; simp [PS.upd]
  | v :: w, s => by
    rw [List.foldl_cons, foldl_r2 w]
    cases s; simp [PS.upd]

theorem rn_copyWord (rest w R2 M I : List Nat) :
    Rn copyWord ⟨[], [], rest ++ (w.length :: w).reverse, R2, M, I, [], [], [], []⟩
      ⟨[], [], rest, R2 ++ w.length :: w, M, I, [], [], [], []⟩ := by
  have e0 : rest ++ (w.length :: w).reverse = (rest ++ w.reverse) ++ [w.length] := by simp
  have h2 := rn_mv (g := .r) (h := .c) (by decide)
    ⟨[], [], rest ++ (w.length :: w).reverse, R2, M, I, [], [], [], []⟩ (l := rest ++ w.reverse) (v := w.length) e0
  have h3 := rn_dup (g := .c) (h := .r2) (by decide)
    ⟨[], [], rest ++ w.reverse, R2, M, I, [w.length], [], [], []⟩ (l := []) (v := w.length) rfl
  have h4 := rn_count .c .r (by decide) (pmv .r .r2 (by decide)) (fun v s => s.upd .r2 (s.r2 ++ [v])) []
    (fun s v u rest' => by
      refine (rn_mv (g := .r) (h := .r2) (by decide) _ (l := rest') (v := v) rfl).eq ?_
      cases s; rfl) w ⟨[], [], rest ++ w.reverse, R2 ++ [w.length], M, I, [w.length], [], [], []⟩ rest
  rw [foldl_r2] at h4
  have h5 := rn_pop .c ⟨[], [], rest, R2 ++ [w.length] ++ w, M, I, [0], [], [], []⟩ (l := []) (v := 0) rfl
  refine (h2.eq (by st_eq)).seq <| (h3.eq (by st_eq)).seq <| (h4.eq (by st_eq)).seq <| h5.eq ?_
  simp [PS.upd]

/-! ## Emitting a word -/

/-- One symbol `v` of the word: onto `t` and `r2`, and `v + 1` added to the length on `m`. -/
def wordStep : NProg UK :=
  .seq (pmv .r .t (by decide)) <| .seq (pdup .t .r2 (by decide)) <| .seq (pdup .t .x (by decide)) <|
  .seq (addInto .x .m) (.prim (.inc Fld.m.idx))

def emitWord (sd : Nat) : NProg UK :=
  .seq (nloadP Fld.m.idx [7, 6, 4, 0]) <|
  .seq (pmv .r .c (by decide)) <|
  .seq (pdup .c .r2 (by decide)) <|
  .seq (.loop Fld.c.idx .pos (.seq (.prim (.dec Fld.c.idx)) wordStep)) <|
  .seq (.prim (.pop Fld.c.idx)) <|
  .seq (pmvAll .t .t2 (by decide)) <|
  .seq (.loop Fld.t2.idx .nonempty (.seq (repPush .t2 .m 49) (npushC Fld.m.idx 48))) <|
  .seq (nloadP Fld.m.idx [6, 5, sd, 4]) <|
  .seq (pdup .i .m (by decide)) <|
  .seq (.prim (.inc Fld.m.idx)) <|
  .seq (.prim (.inc Fld.m.idx)) <|
  .seq (npushC Fld.m.idx 35) <|
  .seq (pdup .i .x (by decide)) <|
  .seq (repPush .x .m 124) (npushC Fld.m.idx 36)

/-- The action of `wordStep` on a symbol. -/
def stepφ (v : Nat) (s : PS) : PS :=
  ((s.upd .t (s.t ++ [v])).upd .r2 (s.r2 ++ [v])).upd .m (mapTop (· + (v + 1)) s.m)

theorem foldl_step : ∀ (w : List Nat) (s : PS),
    w.foldl (fun s v => stepφ v s) s =
      ((s.upd .t (s.t ++ w)).upd .r2 (s.r2 ++ w)).upd .m (mapTop (· + (bin w).length) s.m)
  | [], s => by
    have : mapTop (· + 0) s.m = s.m := by
      rcases List.eq_nil_or_concat s.m with h | ⟨l', w, h⟩
      · rw [h]; rfl
      · rw [h, List.concat_eq_append, mapTop_snoc]; rfl
    cases s; simp_all [PS.upd, bin_nil]
  | v :: w, s => by
    rw [List.foldl_cons, foldl_step w]
    have hl : v + 1 + (bin w).length = (bin (v :: w)).length := by rw [bin_cons]; simp; omega
    cases s
    simp only [stepφ, PS.upd, List.append_assoc, List.singleton_append, mapTop_add, hl]

/-- The action of a character run. -/
def charφ (v : Nat) (s : PS) : PS := s.upd .m ((s.m ++ List.replicate v 49) ++ [48])

theorem foldl_char : ∀ (w : List Nat) (s : PS), w.foldl (fun s v => charφ v s) s = s.upd .m (s.m ++ binChars w)
  | [], s => by cases s; simp [PS.upd, binChars]
  | v :: w, s => by
    rw [List.foldl_cons, foldl_char w]
    cases s; simp [charφ, PS.upd, binChars]

theorem rn_wordStep (s : PS) (v u : Nat) (rest : List Nat) :
    Rn wordStep ((s.upd .c ([] ++ [u])).upd .r (rest ++ [v])) (((stepφ v s).upd .c ([] ++ [u])).upd .r rest) := by
  refine (rn_mv (g := .r) (h := .t) (by decide) _ (l := rest) (v := v) rfl).seq ?_
  refine (rn_dup (g := .t) (h := .r2) (by decide) _ (l := s.t) (v := v) rfl).seq ?_
  refine (rn_dup (g := .t) (h := .x) (by decide) _ (l := s.t) (v := v) rfl).seq ?_
  refine (rn_addInto (x := .x) (g := .m) (by decide) _ (l := s.x) (v := v) rfl).seq ?_
  refine (rn_inc .m _).eq ?_
  cases s
  simp only [stepφ, PS.upd, PS.get, mapTop_add]

theorem rn_emitWord (sd j : Nat) (rest w R2 M : List Nat) :
    Rn (emitWord sd) ⟨[], [], rest ++ (w.length :: w).reverse, R2, M, [j], [], [], [], []⟩
      ⟨[], [], rest, R2 ++ w.length :: w, M ++ blk sd j w, [j], [], [], [], []⟩ := by
  have e0 : rest ++ (w.length :: w).reverse = (rest ++ w.reverse) ++ [w.length] := by simp
  have em : mapTop (· + (bin w).length) (M ++ [7, 6, 4, 0]) = M ++ [7, 6, 4, (bin w).length] := by
    have : M ++ [7, 6, 4, 0] = (M ++ [7, 6, 4]) ++ [0] := by simp
    rw [this, mapTop_snoc]; simp
  have h1 := (rn_load .m ⟨[], [], rest ++ (w.length :: w).reverse, R2, M, [j], [], [], [], []⟩ [7, 6, 4, 0])
  have h2 := rn_mv (g := .r) (h := .c) (by decide)
    ⟨[], [], rest ++ (w.length :: w).reverse, R2, M ++ [7, 6, 4, 0], [j], [], [], [], []⟩
    (l := rest ++ w.reverse) (v := w.length) e0
  have h3 := rn_dup (g := .c) (h := .r2) (by decide)
    ⟨[], [], rest ++ w.reverse, R2, M ++ [7, 6, 4, 0], [j], [w.length], [], [], []⟩ (l := []) (v := w.length) rfl
  have h4 := rn_count .c .r (by decide) wordStep stepφ [] (fun s v u rest' => rn_wordStep s v u rest') w
    ⟨[], [], rest ++ w.reverse, R2 ++ [w.length], M ++ [7, 6, 4, 0], [j], [w.length], [], [], []⟩ rest
  rw [foldl_step] at h4
  have h5 := rn_pop .c ⟨[], [], rest, R2 ++ [w.length] ++ w, M ++ [7, 6, 4, (bin w).length], [j], [0], [], w, []⟩
    (l := []) (v := 0) rfl
  have h6 := rn_mvAll (g := .t) (h := .t2) (by decide)
    ⟨[], [], rest, R2 ++ [w.length] ++ w, M ++ [7, 6, 4, (bin w).length], [j], [], [], w, []⟩
  have h7 := rn_consume .t2 (.seq (repPush .t2 .m 49) (npushC Fld.m.idx 48)) charφ
    (fun s v l => by
      refine (rn_repPush (x := .t2) (g := .m) (by decide) 49 _ (l := l) (v := v) rfl).seq ?_
      refine (rn_pushC .m _ 48).eq ?_
      cases s; rfl) w
    ⟨[], [], rest, R2 ++ [w.length] ++ w, M ++ [7, 6, 4, (bin w).length], [j], [], [], [], w.reverse⟩
  rw [foldl_char] at h7
  let M1 := M ++ [7, 6, 4, (bin w).length] ++ binChars w ++ [6, 5, sd, 4]
  have h8 := rn_load .m ⟨[], [], rest, R2 ++ [w.length] ++ w, M ++ [7, 6, 4, (bin w).length] ++ binChars w, [j],
    [], [], [], []⟩ [6, 5, sd, 4]
  have h9 := rn_dup (g := .i) (h := .m) (by decide) ⟨[], [], rest, R2 ++ [w.length] ++ w, M1, [j], [], [], [], []⟩
    (l := []) (v := j) rfl
  have h10 := rn_inc .m ⟨[], [], rest, R2 ++ [w.length] ++ w, M1 ++ [j], [j], [], [], [], []⟩
  have h11 := rn_inc .m ⟨[], [], rest, R2 ++ [w.length] ++ w, M1 ++ [j + 1], [j], [], [], [], []⟩
  have h12 := rn_pushC .m ⟨[], [], rest, R2 ++ [w.length] ++ w, M1 ++ [j + 1 + 1], [j], [], [], [], []⟩ 35
  have h13 := rn_dup (g := .i) (h := .x) (by decide)
    ⟨[], [], rest, R2 ++ [w.length] ++ w, M1 ++ [j + 1 + 1] ++ [35], [j], [], [], [], []⟩ (l := []) (v := j) rfl
  have h14 := rn_repPush (x := .x) (g := .m) (by decide) 124
    ⟨[], [], rest, R2 ++ [w.length] ++ w, M1 ++ [j + 1 + 1] ++ [35], [j], [], [j], [], []⟩ (l := []) (v := j) rfl
  have h15 := rn_pushC .m
    ⟨[], [], rest, R2 ++ [w.length] ++ w, M1 ++ [j + 1 + 1] ++ [35] ++ List.replicate j 124, [j], [], [], [], []⟩ 36
  refine (h1.eq (by st_eq)).seq <| (h2.eq (by st_eq)).seq <| (h3.eq (by st_eq)).seq <|
    (h4.eq (by simp [PS.upd, em])).seq <| (h5.eq (by st_eq)).seq <| (h6.eq (by st_eq)).seq <|
    (h7.eq (by st_eq)).seq <| (h8.eq (by st_eq)).seq <| (h9.eq (by st_eq)).seq <| (h10.eq (by st_eq)).seq <|
    (h11.eq (by st_eq)).seq <| (h12.eq (by st_eq)).seq <| (h13.eq (by st_eq)).seq <| (h14.eq (by st_eq)).seq <|
    h15.eq ?_
  simp [PS.upd, PS.get, M1, blk, binChars_eq]

end Shallot
