import Shallot.Peg.Undecidable.MachCardsKit

/-!
# The cards stage at the level of lists

* the cards of `tablePCPN T w` in the format of `encCards`, cut into the pieces the program writes one after the
  other (`encCards_table`): the first card, the rule cards, the separator, the copies, the closing card, the end card;
* the table of whole chunks: its bound (`bnd_table1`), its row numbers (`idx_table1`), its rows (`rows_table1`);
* starred cards from linear expressions (`scE`, `scE_ev`).
-/

namespace Shallot

open Complexity
open Complexity.Univ
open Complexity.Undec

namespace MC

/-! ## Cards as numbers -/

/-- One card in the format of `encCards`. -/
def encC (c : Card) : List Nat := c.1.length :: (c.1 ++ c.2.length :: c.2)

theorem encCards_eq (N : List Card) : encCards N = N.flatMap encC := rfl

/-- A card with its stars. -/
def encSC (m : Nat) (c : Card) : List Nat := encC (mpStar m c.1, mpRStar m c.2)

theorem mpStar_length (m : Nat) : ∀ u : Word, (mpStar m u).length = 2 * u.length
  | [] => rfl
  | a :: u => by rw [mpStar_cons]; simp only [List.length_cons, mpStar_length m u]; omega

theorem mpRStar_length (m : Nat) : ∀ v : Word, (mpRStar m v).length = 2 * v.length
  | [] => rfl
  | a :: v => by rw [mpRStar_cons]; simp only [List.length_cons, mpRStar_length m v]; omega

/-- The cards of the instance, piece by piece. -/
theorem encCards_table (T : TTable) (w : List Bool) :
    encCards (tablePCPN T w) =
      encC (mpStar (2 * bnd T + 4) [2 * bnd T + 2],
          (2 * bnd T + 4) :: mpRStar (2 * bnd T + 4) ((2 * bnd T + 2) :: (tmStart T w ++ [2 * bnd T + 3]))) ++
        (tmSRS T).flatMap (encSC (2 * bnd T + 4)) ++ encSC (2 * bnd T + 4) ([2 * bnd T + 3], [2 * bnd T + 3]) ++
        (List.range (2 * bnd T + 2)).flatMap (fun a => encSC (2 * bnd T + 4) ([a], [a])) ++
        encSC (2 * bnd T + 4) ([bnd T + 2, 2 * bnd T + 3, 2 * bnd T + 2], [2 * bnd T + 2]) ++
        encC ([2 * bnd T + 4, 2 * bnd T + 5], [2 * bnd T + 5]) := by
  simp only [encCards_eq, tablePCPN, mpcpToPCP, srFirst, srCards, tmSyms, tmAcc, stS, List.flatMap_cons,
    List.flatMap_append, List.map_append, List.map_cons, List.map_nil, List.flatMap_map, List.flatMap_nil,
    List.append_nil, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
  rfl

/-- The rule cards, piece by piece. -/
theorem tmSRS_flatMap (T : TTable) (f : Word × Word → List Nat) :
    (tmSRS T).flatMap f =
      (List.range (bnd T)).flatMap (fun q => (List.range (bnd T)).flatMap fun a => (rulesQA T q a).flatMap f) ++
        (List.range (bnd T)).flatMap (fun q => if q = 0 ∨ q = 1 then [] else f (endRule T q)) ++
        (List.range (bnd T + 2)).flatMap (fun x => f ([x, stS T 0], [stS T 0]) ++ f ([stS T 0, x], [stS T 0])) := by
  simp only [tmSRS, endRules, eraseRules, List.flatMap_append, List.flatMap_assoc]
  congr 2
  · congr 1; funext q; split <;> simp
  · congr 1; funext q; simp [List.flatMap_cons]

/-- The start word. -/
theorem tmStart_eq (T : TTable) (w : List Bool) :
    tmStart T w = bnd T :: (bnd T + 4) :: (w.map bitSym ++ [bnd T + 1]) := by
  simp [tmStart, cword, finit, zw, lbS, stS, rbS]

/-- A list through its positions. -/
theorem range_flatMap_getD {α : Type} (f : Nat → List α) (d : Nat) :
    ∀ l : List Nat, (List.range l.length).flatMap (fun j => f (l.getD j d)) = l.flatMap f
  | [] => rfl
  | x :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.flatMap_cons]
    congr 1
    exact range_flatMap_getD f d l

/-! ## The table of whole chunks -/

theorem chunks3_get : ∀ (f : Nat) (l : List Nat), l.length % 3 = 0 → l.length ≤ f → ∀ i,
    (chunks 3 f l)[i]? =
      if 3 * i < l.length then some [l.getD (3 * i) 0, l.getD (3 * i + 1) 0, l.getD (3 * i + 2) 0] else none
  | 0, l, _, hf, i => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [chunks]
  | f + 1, [], _, _, i => by simp [chunks]
  | f + 1, [_], h, _, _ => by simp at h
  | f + 1, [_, _], h, _, _ => by simp at h
  | f + 1, x :: y :: z :: l, h, hf, i => by
    rw [chunks, if_neg (by simp)]
    have ht : (x :: y :: z :: l).take 3 = [x, y, z] := rfl
    have hd : (x :: y :: z :: l).drop 3 = l := rfl
    rw [ht, hd]
    cases i with
    | zero => simp
    | succ i =>
      rw [List.getElem?_cons_succ, chunks3_get f l (by simp at h; omega) (by simp at hf; omega) i]
      have e : ∀ k, (x :: y :: z :: l).getD (3 * (i + 1) + k) 0 = l.getD (3 * i + k) 0 := fun k => by
        rw [show 3 * (i + 1) + k = 3 * i + k + 1 + 1 + 1 by omega]; simp only [List.getD_cons_succ]
      have e0 := e 0
      simp only [Nat.add_zero] at e0
      rw [e0, e 1, e 2]
      by_cases hi : 3 * i < l.length
      · rw [if_pos hi, if_pos (by simp; omega)]
      · rw [if_neg hi, if_neg (by simp; omega)]

theorem table1_rows (nq na : Nat) (rest : List Nat) :
    (table1 nq na rest).rows = (chunks 3 rest.length rest).map (rowOfChunk 1) := rfl

/-- The rows of the table of whole chunks. -/
theorem rows_table1 {nq na : Nat} {rest : List Nat} (h : rest.length % 3 = 0) (i : Nat) :
    (table1 nq na rest).rows[i]? = if 3 * i < rest.length then
      some (rest.getD (3 * i) 0, [rest.getD (3 * i + 1) 0], [rest.getD (3 * i + 2) 0]) else none := by
  rw [table1_rows, List.getElem?_map, chunks3_get _ _ h (Nat.le_refl _)]
  split <;> rfl

theorem idx_table1 (nq na : Nat) (rest : List Nat) (q a : Nat) : (table1 nq na rest).idx q [a] = q * na + a := by
  simp [TTable.idx, table1, rcode]

theorem bnd_table1 (nq na : Nat) (rest : List Nat) : bnd (table1 nq na rest) = 3 + rest.sum := by
  simp only [bnd, table1, MacroPeg.KExp.encRows_decRows]

/-! ## Starred cards from expressions -/

variable {K : Nat}

/-- The expressions of a starred card: `⋆ = ` the top of `M`. -/
def scE (M : Fin K) (ls rs : List (LinE K)) : List (LinE K) :=
  ⟨[], 2 * ls.length⟩ :: (ls.flatMap (fun e => [⟨[M], 0⟩, e]) ++
    ⟨[], 2 * rs.length⟩ :: rs.flatMap (fun e => [e, ⟨[M], 0⟩]))

theorem ev_M (S : Lists K) (M : Fin K) : LinE.ev S ⟨[M], 0⟩ = tv S M := by simp [LinE.ev]

theorem ev_const (S : Lists K) (c : Nat) : LinE.ev S ⟨[], c⟩ = c := by simp [LinE.ev]

theorem star_ev (S : Lists K) (M : Fin K) :
    ∀ ls : List (LinE K), (ls.flatMap (fun e => [⟨[M], 0⟩, e])).map (LinE.ev S) = mpStar (tv S M) (ls.map (LinE.ev S))
  | [] => rfl
  | e :: ls => by
    simp [List.flatMap_cons, star_ev S M ls, mpStar_cons, ev_M]

theorem rstar_ev (S : Lists K) (M : Fin K) :
    ∀ rs : List (LinE K), (rs.flatMap (fun e => [e, ⟨[M], 0⟩])).map (LinE.ev S) =
      mpRStar (tv S M) (rs.map (LinE.ev S))
  | [] => rfl
  | e :: rs => by
    simp [List.flatMap_cons, rstar_ev S M rs, mpRStar_cons, ev_M]

/-- **A starred card from expressions.** -/
theorem scE_ev (S : Lists K) (M : Fin K) (ls rs : List (LinE K)) :
    (scE M ls rs).map (LinE.ev S) = encSC (tv S M) (ls.map (LinE.ev S), rs.map (LinE.ev S)) := by
  simp only [scE, List.map_cons, List.map_append, star_ev, rstar_ev, encSC, encC, mpStar_length, mpRStar_length,
    List.length_map, ev_const]

end MC

end Shallot
