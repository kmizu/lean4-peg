import Shallot.Peg.Undecidable.MachPrintSer

/-!
# The printing stage

`printP` turns the result of the cards stage into the input stacks of the bits of Ford's grammar of the cards
(`printP_good`), or of the empty grammar on the flag 1 (`printP_bad`); `printLP` does the same for the loop grammars
(`printLP_good`, `printLP_bad`).

On the flag 0 it reverses the cards onto `r`, writes the constant start onto `m`, runs through the cards twice
(`cardLoop`: the alternatives of the tops, then of the bottoms, the index on `i`), adds the ends, and finally turns
the numbers on `m` into their unary bits on stack 0 (`conv`).
-/

namespace Shallot

open Complexity
open Complexity.Univ
open Complexity.Undec

/-! ## Running through the cards -/

def cardBody1 : NProg UK := .seq (emitWord 1) (.seq copyWord (.prim (.inc Fld.i.idx)))
def cardBody2 : NProg UK := .seq copyWord (.seq (emitWord 2) (.prim (.inc Fld.i.idx)))

def cardLoop (body : NProg UK) : NProg UK := .loop Fld.r.idx .nonempty body

theorem encCards_cons (c : Card) (N : List Card) : encCards (c :: N) = encCards [c] ++ encCards N := by
  simp [encCards]

theorem encCards_one_rev (c : Card) :
    (encCards [c]).reverse = (c.2.length :: c.2).reverse ++ (c.1.length :: c.1).reverse := by
  simp [encCards]

theorem rn_cardBody1 (c : Card) (rest R2 M : List Nat) (j : Nat) :
    Rn cardBody1 ⟨[], [], rest ++ (encCards [c]).reverse, R2, M, [j], [], [], [], []⟩
      ⟨[], [], rest, R2 ++ encCards [c], M ++ blk 1 j c.1, [j + 1], [], [], [], []⟩ := by
  have h1 := rn_emitWord 1 j (rest ++ (c.2.length :: c.2).reverse) c.1 R2 M
  have h2 := rn_copyWord rest c.2 (R2 ++ c.1.length :: c.1) (M ++ blk 1 j c.1) [j]
  have h3 := rn_inc .i ⟨[], [], rest, R2 ++ c.1.length :: c.1 ++ c.2.length :: c.2, M ++ blk 1 j c.1, [j],
    [], [], [], []⟩
  rw [encCards_one_rev, ← List.append_assoc]
  refine h1.seq (h2.seq (h3.eq ?_))
  simp [PS.upd, PS.get, encCards, mapTop]

theorem rn_cardBody2 (c : Card) (rest R2 M : List Nat) (j : Nat) :
    Rn cardBody2 ⟨[], [], rest ++ (encCards [c]).reverse, R2, M, [j], [], [], [], []⟩
      ⟨[], [], rest, R2 ++ encCards [c], M ++ blk 2 j c.2, [j + 1], [], [], [], []⟩ := by
  have h1 := rn_copyWord (rest ++ (c.2.length :: c.2).reverse) c.1 R2 M [j]
  have h2 := rn_emitWord 2 j rest c.2 (R2 ++ c.1.length :: c.1) M
  have h3 := rn_inc .i ⟨[], [], rest, R2 ++ c.1.length :: c.1 ++ c.2.length :: c.2, M ++ blk 2 j c.2, [j],
    [], [], [], []⟩
  rw [encCards_one_rev, ← List.append_assoc]
  refine h1.seq (h2.seq (h3.eq ?_))
  simp [PS.upd, PS.get, encCards, mapTop]

/-- **The loop over the cards**, for a body handling one card. -/
theorem rn_cardLoop (body : NProg UK) (sd : Nat) (sel : Card → Word)
    (hb : ∀ (c : Card) (rest R2 M : List Nat) (j : Nat),
      Rn body ⟨[], [], rest ++ (encCards [c]).reverse, R2, M, [j], [], [], [], []⟩
        ⟨[], [], rest, R2 ++ encCards [c], M ++ blk sd j (sel c), [j + 1], [], [], [], []⟩) :
    ∀ (N : List Card) (R2 M : List Nat) (j : Nat),
      Rn (cardLoop body) ⟨[], [], (encCards N).reverse, R2, M, [j], [], [], [], []⟩
        ⟨[], [], [], R2 ++ encCards N, M ++ sideFrom sd sel N j, [j + N.length], [], [], [], []⟩
  | [], R2, M, j => by
    have : (⟨[], [], [], R2 ++ encCards [], M ++ sideFrom sd sel [] j, [j + ([] : List Card).length], [], [], [], []⟩
        : PS) = ⟨[], [], (encCards []).reverse, R2, M, [j], [], [], [], []⟩ := by simp [encCards, sideFrom]
    rw [this]
    exact Rn.loopF (by simp [encCards, PS.get, NTest.eval])
  | c :: N, R2, M, j => by
    have h1 := hb c (encCards N).reverse R2 M j
    rw [← List.reverse_append, ← encCards_cons] at h1
    refine Rn.loopC (by simp [PS.get, NTest.eval, encCards]) h1 ((rn_cardLoop body sd sel hb N _ _ (j + 1)).eq ?_)
    simp [encCards_cons c N, sideFrom, Nat.add_assoc, Nat.add_comm 1 N.length]

/-! ## From numbers to bits -/

/-- Turn the numbers on `m` into their unary bits on stack 0, the first bit on top. -/
def conv : NProg UK := .loop Fld.m.idx .nonempty (.seq (npushC Fld.o.idx 0) (repPush .m .o 1))

def convφ (v : Nat) (s : PS) : PS := s.upd .o ((s.o ++ [0]) ++ List.replicate v 1)

theorem foldl_conv : ∀ (L : List Nat) (s : PS),
    L.foldl (fun s v => convφ v s) s = s.upd .o (s.o ++ (L.map fun v => 0 :: List.replicate v 1).flatten)
  | [], s => by cases s; simp [PS.upd]
  | v :: L, s => by
    rw [List.foldl_cons, foldl_conv L]
    cases s; simp [convφ, PS.upd]

theorem bits_rev : ∀ l : List Nat,
    (l.reverse.map fun v => 0 :: List.replicate v 1).flatten = ((unary l).map bitElem).reverse
  | [] => rfl
  | v :: l => by
    rw [List.reverse_cons, List.map_append, List.flatten_append, bits_rev l]
    simp [unary, bitElem, List.map_replicate]

theorem rn_conv (l : List Nat) :
    Rn conv ⟨[], [], [], [], l, [], [], [], [], []⟩ ⟨((unary l).map bitElem).reverse, [], [], [], [], [], [], [], [], []⟩ := by
  have h := rn_consume .m (.seq (npushC Fld.o.idx 0) (repPush .m .o 1)) convφ
    (fun s v L => by
      refine (rn_pushC .o _ 0).seq ?_
      refine (rn_repPush (x := .m) (g := .o) (by decide) 1 _ (l := L) (v := v) rfl).eq ?_
      cases s; rfl) l.reverse PS.e
  rw [foldl_conv, bits_rev, List.reverse_reverse] at h
  exact h.eq rfl

/-! ## The programs -/

/-- On the flag 0: print a grammar with the start `pre` and the end `suf` around the two sides. -/
def printGood (pre suf : List Nat) : NProg UK :=
  .seq (.prim (.pop Fld.f.idx)) <|
  .seq (pmvAll .o .r (by decide)) <|
  .seq (nloadP Fld.m.idx pre) <|
  .seq (.prim (.pushZ Fld.i.idx)) <|
  .seq (cardLoop cardBody1) <|
  .seq (.prim (.pushZ Fld.m.idx)) <|
  .seq (pmvAll .r2 .r (by decide)) <|
  .seq (.prim (.pop Fld.i.idx)) <|
  .seq (.prim (.pushZ Fld.i.idx)) <|
  .seq (cardLoop cardBody2) <|
  .seq (.prim (.pushZ Fld.m.idx)) <|
  .seq (nloadP Fld.m.idx suf) <|
  .seq (.prim (.pop Fld.i.idx)) <|
  .seq (nclr Fld.r2.idx) conv

/-- On the flag 1: print the constant numbers `l`. -/
def printBad (l : List Nat) : NProg UK := .seq (.prim (.pop Fld.f.idx)) (.seq (nloadP Fld.m.idx l) conv)

def printGen (pre suf bad : List Nat) : NProg UK := .ite Fld.f.idx .zero (printGood pre suf) (printBad bad)

/-- **The printing stage** for Ford's grammar. -/
def printP : NProg UK := printGen preF [] (serG emptyG)

/-- **The printing stage** for the loop grammar. -/
def printLP : NProg UK := printGen preL sufL (serG (loopG emptyG))

/-! ## Correctness -/

theorem rn_printGood (pre suf : List Nat) (N : List Card) :
    Rn (printGood pre suf) ⟨encCards N, [0], [], [], [], [], [], [], [], []⟩
      ⟨((unary (pre ++ sideFrom 1 Prod.fst N 0 ++ [0] ++ sideFrom 2 Prod.snd N 0 ++ [0] ++ suf)).map bitElem).reverse,
        [], [], [], [], [], [], [], [], []⟩ := by
  have h1 := rn_pop .f (⟨(encCards N), [0], [], [], [], [], [], [], [], []⟩ : PS) (l := []) (v := 0) rfl
  have h2 := rn_mvAll (g := .o) (h := .r) (by decide) (⟨(encCards N), [], [], [], [], [], [], [], [], []⟩ : PS)
  have h3 := rn_load .m (⟨[], [], (encCards N).reverse, [], [], [], [], [], [], []⟩ : PS) pre
  have h4 := rn_pushZ .i (⟨[], [], (encCards N).reverse, [], pre, [], [], [], [], []⟩ : PS)
  have h5 := rn_cardLoop cardBody1 1 Prod.fst rn_cardBody1 N [] pre 0
  have h6 := rn_pushZ .m (⟨[], [], [], (encCards N), pre ++ (sideFrom 1 Prod.fst N 0), [N.length], [], [], [], []⟩ : PS)
  have h7 := rn_mvAll (g := .r2) (h := .r) (by decide) (⟨[], [], [], (encCards N), pre ++ (sideFrom 1 Prod.fst N 0) ++ [0], [N.length], [], [], [], []⟩ : PS)
  have h8 := rn_pop .i (⟨[], [], (encCards N).reverse, [], pre ++ (sideFrom 1 Prod.fst N 0) ++ [0], [N.length], [], [], [], []⟩ : PS)
    (l := []) (v := N.length) rfl
  have h9 := rn_pushZ .i (⟨[], [], (encCards N).reverse, [], pre ++ (sideFrom 1 Prod.fst N 0) ++ [0], [], [], [], [], []⟩ : PS)
  have h10 := rn_cardLoop cardBody2 2 Prod.snd rn_cardBody2 N [] (pre ++ (sideFrom 1 Prod.fst N 0) ++ [0]) 0
  have h11 := rn_pushZ .m (⟨[], [], [], (encCards N), pre ++ (sideFrom 1 Prod.fst N 0) ++ [0] ++ (sideFrom 2 Prod.snd N 0), [N.length], [], [], [], []⟩ : PS)
  have h12 := rn_load .m (⟨[], [], [], (encCards N), pre ++ (sideFrom 1 Prod.fst N 0) ++ [0] ++ (sideFrom 2 Prod.snd N 0) ++ [0], [N.length], [], [], [], []⟩ : PS) suf
  have h13 := rn_pop .i (⟨[], [], [], (encCards N), pre ++ (sideFrom 1 Prod.fst N 0) ++ [0] ++ (sideFrom 2 Prod.snd N 0) ++ [0] ++ suf, [N.length], [], [], [], []⟩ : PS)
    (l := []) (v := N.length) rfl
  have h14 := rn_clr .r2 (⟨[], [], [], (encCards N), pre ++ (sideFrom 1 Prod.fst N 0) ++ [0] ++ (sideFrom 2 Prod.snd N 0) ++ [0] ++ suf, [], [], [], [], []⟩ : PS)
  have h15 := rn_conv (pre ++ (sideFrom 1 Prod.fst N 0) ++ [0] ++ (sideFrom 2 Prod.snd N 0) ++ [0] ++ suf)
  refine (h1.eq (by st_eq)).seq <| (h2.eq (by st_eq)).seq <| (h3.eq (by st_eq)).seq <| (h4.eq (by st_eq)).seq <|
    (h5.eq (by st_eq)).seq <| (h6.eq (by st_eq)).seq <| (h7.eq (by st_eq)).seq <| (h8.eq (by st_eq)).seq <|
    (h9.eq (by st_eq)).seq <| (h10.eq (by st_eq)).seq <| (h11.eq (by st_eq)).seq <| (h12.eq (by st_eq)).seq <|
    (h13.eq (by st_eq)).seq <| (h14.eq (by st_eq)).seq h15

theorem rn_printBad (l : List Nat) :
    Rn (printBad l) ⟨[], [1], [], [], [], [], [], [], [], []⟩
      ⟨((unary l).map bitElem).reverse, [], [], [], [], [], [], [], [], []⟩ := by
  have h1 := rn_pop .f (⟨[], [1], [], [], [], [], [], [], [], []⟩ : PS) (l := []) (v := 1) rfl
  have h2 := rn_load .m (⟨[], [], [], [], [], [], [], [], [], []⟩ : PS) l
  exact (h1.eq (by st_eq)).seq ((h2.eq (by st_eq)).seq (rn_conv l))

/-! ## The stacks of the specification as records -/

theorem cardsSt_eq (N : List Card) : cardsSt N = (⟨encCards N, [0], [], [], [], [], [], [], [], []⟩ : PS).L := by
  funext j
  simp only [cardsSt, PS.L]
  repeat' split
  all_goals first | rfl | (exfalso; omega)

theorem badSt_eq : badSt = (⟨[], [1], [], [], [], [], [], [], [], []⟩ : PS).L := by
  funext j
  simp only [badSt, PS.L]
  repeat' split
  all_goals first | rfl | (exfalso; omega)

theorem nInit_eq (w : List Bool) : nInit UK w = (⟨(w.map bitElem).reverse, [], [], [], [], [], [], [], [], []⟩ : PS).L := by
  funext j
  simp only [nInit, PS.L]
  repeat' split
  all_goals first | rfl | (exfalso; omega)

theorem printGen_good (pre suf bad : List Nat) (N : List Card) :
    ∃ c, NRuns (printGen pre suf bad) (cardsSt N)
      (nInit UK (unary (pre ++ sideFrom 1 Prod.fst N 0 ++ [0] ++ sideFrom 2 Prod.snd N 0 ++ [0] ++ suf))) c := by
  rw [cardsSt_eq, nInit_eq]
  exact Rn.iteT (by simp [PS.get, NTest.eval]) (rn_printGood pre suf N)

theorem printGen_bad (pre suf bad : List Nat) : ∃ c, NRuns (printGen pre suf bad) badSt (nInit UK (unary bad)) c := by
  rw [badSt_eq, nInit_eq]
  exact Rn.iteF (by simp [PS.get, NTest.eval]) (rn_printBad bad)

theorem printP_good (N : List Complexity.Undec.Card) :
    ∃ c, NRuns printP (cardsSt N) (nInit Complexity.Univ.UK (encG (fordG (toPCP N)))) c := by
  have := printGen_good preF [] (serG emptyG) N
  rw [List.append_nil, ← serG_fordG] at this
  exact this

theorem printP_bad : ∃ c, NRuns printP badSt (nInit Complexity.Univ.UK (encG emptyG)) c :=
  printGen_bad preF [] (serG emptyG)

theorem printLP_good (N : List Complexity.Undec.Card) :
    ∃ c, NRuns printLP (cardsSt N) (nInit Complexity.Univ.UK (encG (loopG (fordG (toPCP N))))) c := by
  have := printGen_good preL sufL (serG (loopG emptyG)) N
  rw [← serG_loopG] at this
  exact this

theorem printLP_bad : ∃ c, NRuns printLP badSt (nInit Complexity.Univ.UK (encG (loopG emptyG))) c :=
  printGen_bad preL sufL (serG (loopG emptyG))

end Shallot
