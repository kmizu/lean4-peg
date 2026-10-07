import Shallot.Peg.Undecidable.MachPrintWord
import Shallot.Peg.Undecidable.FordCor

/-!
# The numbers of Ford's grammar, card by card

`serG (fordG (toPCP N))` is a constant, then the alternatives of the tops card by card (`sideFrom 1 Prod.fst N 0`),
`0`, the alternatives of the bottoms, `0` (`serG_fordG`); the loop grammar adds a constant at both ends
(`serG_loopG`).
-/

namespace Shallot

open Complexity
open Complexity.Univ
open Complexity.Undec

/-- The alternatives of a side for the cards `N`, the first of index `j`. -/
def sideFrom (sd : Nat) (sel : Card → Word) : List Card → Nat → List Nat
  | [], _ => []
  | c :: N, j => blk sd j (sel c) ++ sideFrom sd sel N (j + 1)

theorem ser_sideAlt (f : Nat → List Bool) (sd j : Nat) (w : List Nat) (h : f j = bin w) :
    7 :: serE (sideAlt f sd j) = blk sd j w := by
  simp only [sideAlt, serE, serStrN, word, mark, blk, h, List.length_map, List.map_cons,
    List.map_append, List.map_replicate, List.length_cons, List.length_append, List.length_replicate,
    List.map_nil, List.length_nil, List.cons_append, List.nil_append, List.append_assoc, List.map_map,
    Function.comp_def]
  rfl

theorem ser_sideAlts (f : Nat → List Bool) (sd : Nat) (sel : Card → Word) :
    ∀ (M : List Card) (j : Nat), (∀ i (h : i < M.length), f (j + i) = bin (sel M[i])) →
      serE (sideAlts f sd (List.range' j M.length)) = sideFrom sd sel M j ++ [0]
  | [], _, _ => rfl
  | c :: M, j, h => by
    rw [List.length_cons, List.range'_succ]
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have ih := ser_sideAlts f sd sel M (j + 1) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [← this]; congr 1; omega)
    simp only [sideAlts, serE]
    rw [ih, sideFrom, ← ser_sideAlt f sd j (sel c) h0]
    simp

theorem top_toPCP (N : List Card) (i : Nat) (h : i < N.length) : (toPCP N).top i = bin N[i].1 := by
  rw [PCP.top, getD_toPCP, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem bot_toPCP (N : List Card) (i : Nat) (h : i < N.length) : (toPCP N).bot i = bin N[i].2 := by
  rw [PCP.bot, getD_toPCP, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem length_toPCP (N : List Card) : (toPCP N).length = N.length := by simp [toPCP]

/-- The constant start of the numbers of Ford's grammar. -/
def preF : List Nat := [0, 3] ++ serE fordD

/-- The constant start of the numbers of the loop grammar. -/
def preL : List Nat := [3, 4] ++ serE fordD

/-- The numbers of the loop rule of Ford's grammar. -/
def sufL : List Nat := serE (.seq (PExp.andP (.nt 0)) (.nt 3))

/-- **The numbers of Ford's grammar.** -/
theorem serG_fordG (N : List Card) :
    serG (fordG (toPCP N)) = preF ++ sideFrom 1 Prod.fst N 0 ++ [0] ++ sideFrom 2 Prod.snd N 0 ++ [0] := by
  have h1 := ser_sideAlts (toPCP N).top 1 Prod.fst N 0 (fun i h => by rw [Nat.zero_add]; exact top_toPCP N i h)
  have h2 := ser_sideAlts (toPCP N).bot 2 Prod.snd N 0 (fun i h => by rw [Nat.zero_add]; exact bot_toPCP N i h)
  simp only [serG, fordG, preF, List.range_eq_range', length_toPCP, h1, h2, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.length_cons, List.length_nil]
  simp

/-- **The numbers of the loop grammar of Ford's grammar.** -/
theorem serG_loopG (N : List Card) :
    serG (loopG (fordG (toPCP N))) =
      preL ++ sideFrom 1 Prod.fst N 0 ++ [0] ++ sideFrom 2 Prod.snd N 0 ++ [0] ++ sufL := by
  have h1 := ser_sideAlts (toPCP N).top 1 Prod.fst N 0 (fun i h => by rw [Nat.zero_add]; exact top_toPCP N i h)
  have h2 := ser_sideAlts (toPCP N).bot 2 Prod.snd N 0 (fun i h => by rw [Nat.zero_add]; exact bot_toPCP N i h)
  simp only [serG, loopG, loopRule, fordG, preL, sufL, List.range_eq_range', length_toPCP, h1, h2, List.map_cons,
    List.map_nil, List.map_append, List.flatten_cons, List.flatten_nil, List.flatten_append, List.length_cons,
    List.length_nil, List.length_append]
  simp

end Shallot
