import MacroPeg.HigherOrder.KExp.DiagParse
import MacroPeg.HigherOrder.KExp.DiagChunk

/-!
# The front of the diagonal machine: the table and the configuration

After reading (`S2`):
* `loadP` turns the numbers over, the first on top;
* `takesP` takes `k`, `nq`, `na`, `c`, `d` (halting with `false` when there are fewer than five numbers);
* `chunkPre` moves the rows onto `TBL` while counting in chunks of `2k+1`; `checkP` halts with `false` unless
  the count ends at a chunk boundary;
* `layP` writes the state, the heads, and the other tapes.
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Complexity.Univ
open Shallot.MacroPeg.HO

/-! ## Facts on the codes -/

theorem deUnaryGo_bound : ∀ (a : Nat) (u : List Bool), (deUnaryGo a u).sum + (deUnaryGo a u).length ≤ a + u.length
  | a, [] => by simp [deUnaryGo]
  | a, true :: u => by
    have := deUnaryGo_bound (a + 1) u
    simp only [deUnaryGo, List.length_cons]; omega
  | a, false :: u => by
    have := deUnaryGo_bound 0 u
    simp only [deUnaryGo, List.length_cons, List.sum_cons]; omega

theorem deUnary_bound (w : List Bool) : (deUnary w).sum + (deUnary w).length ≤ w.length := by
  have := deUnaryGo_bound 0 w; simp only [deUnary]; omega

theorem chunks_flat (k : Nat) : ∀ (f : Nat) (l : List Nat), l.length ≤ f →
    (chunks (2 * k + 1) f l).flatMap (fun ch => (rowOfChunk k ch).1 :: (rowOfChunk k ch).2.1 ++ (rowOfChunk k ch).2.2)
      = l
  | 0, l, h => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [chunks]
  | f + 1, [], _ => by simp [chunks]
  | f + 1, x :: l, h => by
    rw [chunks, if_neg (by simp), List.flatMap_cons]
    have ih := chunks_flat k f ((x :: l).drop (2 * k + 1)) (by simp at h ⊢; omega)
    rw [ih]
    rw [List.take_succ_cons, List.drop_succ_cons]
    simp only [rowOfChunk, List.cons_append, List.take_append_drop]
    try (rw [← List.cons_append, ← List.take_succ_cons]; exact List.take_append_drop _ _)

/-- **Whole rows read back**: the rows of a list of numbers give the list again. -/
theorem encRows_decRows (k : Nat) (l : List Nat) : encRows (decRows k l) = l := by
  simp only [encRows, decRows, List.flatMap_map]
  exact chunks_flat k l.length l (Nat.le_refl _)

/-- The tapes laid out: the first tape, then `k - 1` empty ones. -/
def tpOut (tp : List Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => tp ++ List.replicate k 0

theorem encTapes_finit (k : Nat) (w : List Bool) :
    encTapes (finit k w).tapes = tpOut (w.length :: w.map bitSym) k := by
  cases k with
  | zero => simp [finit, encTapes, tpOut]
  | succ k =>
    simp only [finit, tpOut]
    rw [List.ofFn_succ]
    simp only [Fin.val_zero, if_true, Fin.val_succ, Nat.add_one_ne_zero, if_false]
    simp only [encTapes, List.flatMap_cons, List.length_map, List.cons_append]
    congr 2
    induction k with
    | zero => rfl
    | succ k ih => rw [List.ofFn_succ, List.flatMap_cons, ih]; rfl

/-! ## Turning the numbers over -/

def loadP : NProg UK := nmvAll LL MM (by decide)

def S2L (w : List Bool) : Lists UK :=
  ((E0.set NN [w.length]).set TP (w.length :: w.map bitSym)).set MM (deUnary w).reverse

theorem nruns_load (w : List Bool) : NRuns loadP (S2 w) (S2L w) (3 * w.length + 1) := by
  have d := nruns_mvAll LL MM (by decide) (S2 w)
  have h1 : (S2 w) MM = [] := by simp only [S2]; stk_simp
  have h2 : (S2 w) LL = deUnary w := by simp only [S2]; stk_simp
  rw [h1, h2] at d
  have e : (((S2 w).set MM ([] ++ (deUnary w).reverse)).set LL []) = S2L w := by
    simp only [S2, S2L]; lsimp
  rw [e] at d
  refine d.mono ?_
  have := deUnary_bound w
  omega

/-! ## Taking the five constants -/

def dsTakes : List (Fin UK) := [KS, NQ, NA, CC, DD]

theorem dsTakes_ne : ∀ d ∈ dsTakes, MM ≠ d := by decide

/-- After the takes. -/
def S3a (n : Nat) (tp rest : List Nat) (k nq na c d : Nat) : Lists UK :=
  (((((((E0.set NN [n]).set TP tp).set MM rest.reverse).set KS [k]).set NQ [nq]).set NA [na]).set CC [c]).set DD [d]

theorem take_step (d : Fin UK) (h : MM ≠ d) (S : Lists UK) (x : Nat) (l : List Nat)
    (hS : S MM = (x :: l).reverse) (hd : S d = []) :
    NRuns (takeP MM d h) S ((S.set d [x]).set MM l.reverse) 3 := by
  have := nruns_take MM d h S (l := l.reverse) (v := x) (by rw [hS, List.reverse_cons])
  rw [hd] at this; exact this

theorem takes_good (n : Nat) (tp rest : List Nat) (k nq na c d : Nat) (q : NProg UK) :
    (∀ {S' : Lists UK} {T : Nat}, NRuns q (S3a n tp rest k nq na c d) S' T →
      NRuns (takesP MM dsTakes dsTakes_ne q) (((E0.set NN [n]).set TP tp).set MM (k :: nq :: na :: c :: d :: rest).reverse)
        S' (15 + T)) ∧
    (∀ {S' : Lists UK} {T : Nat} {b : Bool}, NHalts q (S3a n tp rest k nq na c d) b S' T →
      NHalts (takesP MM dsTakes dsTakes_ne q) (((E0.set NN [n]).set TP tp).set MM (k :: nq :: na :: c :: d :: rest).reverse)
        b S' (15 + T)) := by
  let A₀ := ((E0.set NN [n]).set TP tp).set MM (k :: nq :: na :: c :: d :: rest).reverse
  have r₁ := take_step KS (by decide) A₀ k (nq :: na :: c :: d :: rest) (by simp only [A₀]; stk_simp) (by simp only [A₀]; stk_simp)
  let A₁ := (A₀.set KS [k]).set MM (nq :: na :: c :: d :: rest).reverse
  have r₂ := take_step NQ (by decide) A₁ nq (na :: c :: d :: rest) (by simp only [A₁]; stk_simp) (by simp only [A₁, A₀]; stk_simp)
  let A₂ := (A₁.set NQ [nq]).set MM (na :: c :: d :: rest).reverse
  have r₃ := take_step NA (by decide) A₂ na (c :: d :: rest) (by simp only [A₂]; stk_simp) (by simp only [A₂, A₁, A₀]; stk_simp)
  let A₃ := (A₂.set NA [na]).set MM (c :: d :: rest).reverse
  have r₄ := take_step CC (by decide) A₃ c (d :: rest) (by simp only [A₃]; stk_simp)
    (by simp only [A₃, A₂, A₁, A₀]; stk_simp)
  let A₄ := (A₃.set CC [c]).set MM (d :: rest).reverse
  have r₅ := take_step DD (by decide) A₄ d rest (by simp only [A₄]; stk_simp)
    (by simp only [A₄, A₃, A₂, A₁, A₀]; stk_simp)
  have e : (A₄.set DD [d]).set MM rest.reverse = S3a n tp rest k nq na c d := by
    simp only [A₄, A₃, A₂, A₁, A₀, S3a]; lsimp
  rw [e] at r₅
  constructor
  · intro S' T hq
    exact (r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq hq))))).mono (by omega)
  · intro S' T b hq
    exact (r₁.seqH (r₂.seqH (r₃.seqH (r₄.seqH (r₅.seqH hq))))).mono (by omega)

/-! ## The rows, counted in chunks -/

def chunkPre : NProg UK :=
  .seq (.prim (.dup KS K2 (by decide))) (.seq (.prim (.dup KS TT (by decide))) (.seq (addTo TT K2)
    (.seq (.prim (.pushZ DC)) (chunkLoop MM TBL DC K2 (by decide) (by decide)))))

/-- After the rows are moved. -/
def S3b (n : Nat) (tp rest : List Nat) (k nq na c d : Nat) : Lists UK :=
  ((((((((E0.set NN [n]).set TP tp).set TBL rest).set KS [k]).set NQ [nq]).set NA [na]).set CC [c]).set DD
    [d]).set K2 [k + k] |>.set DC [ccR (k + k) rest.length]

theorem nruns_chunkPre (n : Nat) (tp rest : List Nat) (k nq na c d : Nat) :
    NRuns chunkPre (S3a n tp rest k nq na c d) (S3b n tp rest k nq na c d) (6 * rest.length + 3 * k + 8) := by
  let A := S3a n tp rest k nq na c d
  have d₁ := nruns_dup KS K2 (by decide) A (l := []) (v := k) (by simp only [A, S3a]; stk_simp)
  have hk : A K2 = [] := by simp only [A, S3a]; stk_simp
  rw [hk] at d₁
  let A₁ := A.set K2 ([] ++ [k])
  have d₂ := nruns_dup KS TT (by decide) A₁ (l := []) (v := k) (by simp only [A₁, A, S3a]; stk_simp)
  have ht : A₁ TT = [] := by simp only [A₁, A, S3a]; stk_simp
  rw [ht] at d₂
  let A₂ := A₁.set TT ([] ++ [k])
  have d₃ := nruns_addTo TT K2 (by decide) A₂ (l := []) (l' := []) (a := k) (b := k) (by simp only [A₂, Lists.set_same])
    (by simp only [A₂, A₁]; stk_simp)
  let A₃ := (A₂.set TT []).set K2 ([] ++ [k + k])
  have d₄ := nruns_pushZ DC A₃
  have hdc : A₃ DC = [] := by simp only [A₃, A₂, A₁, A, S3a]; stk_simp
  rw [hdc] at d₄
  let A₄ := A₃.set DC ([] ++ [0])
  have d₅ := nruns_chunkLoop MM TBL DC K2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) A₄
    (l := rest.reverse) (lc := []) (lr := []) (R := k + k)
    (by simp only [A₄, A₃, A₂, A₁, A, S3a]; stk_simp) (by simp only [A₄, A₃, A₂, A₁, A, S3a]; stk_simp)
    (by simp only [A₄, Lists.set_same]) (by simp only [A₄, A₃]; stk_simp)
  have e : ((A₄.set MM []).set TBL rest.reverse.reverse).set DC ([] ++ [ccR (k + k) rest.reverse.length]) =
      S3b n tp rest k nq na c d := by
    simp only [A₄, A₃, A₂, A₁, A, S3a, S3b, List.reverse_reverse, List.length_reverse]; lsimp
  rw [e] at d₅
  refine (d₁.seq (d₂.seq (d₃.seq (d₄.seq d₅)))).mono ?_
  simp only [List.length_reverse]; omega

def checkP : NProg UK :=
  .ite DC .zero (.seq (.prim (.pop DC)) (.seq (.prim (.pop K2)) (.prim (.pop NQ)))) (.halt false)

/-- The table in place. -/
def S3 (n : Nat) (tp rest : List Nat) (k na c d : Nat) : Lists UK :=
  ((((((E0.set NN [n]).set TP tp).set TBL rest).set KS [k]).set NA [na]).set CC [c]).set DD [d]

theorem nruns_check (n : Nat) (tp rest : List Nat) (k nq na c d : Nat) (h : rest.length % (2 * k + 1) = 0) :
    NRuns checkP (S3b n tp rest k nq na c d) (S3 n tp rest k na c d) 4 := by
  have h0 : ccR (k + k) rest.length = 0 := (ccR_zero_iff _ _).2 (by rw [show k + k + 1 = 2 * k + 1 by omega]; exact h)
  let A := S3b n tp rest k nq na c d
  have hA : (S3b n tp rest k nq na c d) DC = [] ++ [0] := by simp only [S3b, h0]; stk_simp
  have d₁ := nruns_pop DC A hA
  have d₂ := nruns_pop K2 (A.set DC []) (l := []) (v := k + k) (by simp only [A, S3b]; stk_simp)
  have d₃ := nruns_pop NQ ((A.set DC []).set K2 []) (l := []) (v := nq) (by simp only [A, S3b]; stk_simp)
  have e : (((A.set DC []).set K2 []).set NQ []) = S3 n tp rest k na c d := by
    simp only [A, S3b, S3]; lsimp
  rw [e] at d₃
  exact (d₁.seq (d₂.seq d₃)).iteT (by rw [hA]; exact eval_zero_zero [])

theorem nhalts_check (n : Nat) (tp rest : List Nat) (k nq na c d : Nat) (h : rest.length % (2 * k + 1) ≠ 0) :
    NHalts checkP (S3b n tp rest k nq na c d) false (S3b n tp rest k nq na c d) 2 := by
  have h0 : ccR (k + k) rest.length ≠ 0 := fun e =>
    h (by have := (ccR_zero_iff _ _).1 e; rw [show k + k + 1 = 2 * k + 1 by omega] at this; exact this)
  obtain ⟨v, hv⟩ : ∃ v, ccR (k + k) rest.length = v + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero h0).symm⟩
  have hA : (S3b n tp rest k nq na c d) DC = [] ++ [v + 1] := by simp only [S3b, hv]; stk_simp
  exact (nhalts_halt false _).iteF (by rw [hA]; exact eval_zero_succ [] v)

/-! ## The state, the heads and the tapes -/

def layP : NProg UK :=
  .seq (npushC ST 2) (.seq (.prim (.dup KS TT (by decide))) (.seq (zerosP TT POS)
    (.ite KS .zero (nclr TP) (.seq (.prim (.dup KS TT (by decide))) (.seq (.prim (.dec TT)) (zerosP TT TP))))))

/-- The configuration in place. -/
def S4 (n : Nat) (tp rest : List Nat) (k na c d : Nat) : Lists UK :=
  ((((((((E0.set NN [n]).set TP (tpOut tp k)).set TBL rest).set KS [k]).set NA [na]).set CC [c]).set DD [d]).set ST
    [2]).set POS (List.replicate k 0)

theorem nruns_lay (n : Nat) (tp rest : List Nat) (k na c d : Nat) :
    NRuns layP (S3 n tp rest k na c d) (S4 n tp rest k na c d) (2 * tp.length + 6 * k + 20) := by
  let A := S3 n tp rest k na c d
  have d₁ := nruns_pushC ST A 2
  have hst : A ST = [] := by simp only [A, S3]; stk_simp
  rw [hst] at d₁
  let A₁ := A.set ST ([] ++ [2])
  have d₂ := nruns_dup KS TT (by decide) A₁ (l := []) (v := k) (by simp only [A₁, A, S3]; stk_simp)
  have ht : A₁ TT = [] := by simp only [A₁, A, S3]; stk_simp
  rw [ht] at d₂
  let A₂ := A₁.set TT ([] ++ [k])
  have d₃ := nruns_zeros TT POS (by decide) A₂ (lt := []) (x := k) (by simp only [A₂, Lists.set_same])
  have hp : A₂ POS = [] := by simp only [A₂, A₁, A, S3]; stk_simp
  rw [hp] at d₃
  let A₃ := (A₂.set TT []).set POS ([] ++ List.replicate k 0)
  have hKS : A₃ KS = [] ++ [k] := by simp only [A₃, A₂, A₁, A, S3]; stk_simp
  cases k with
  | zero =>
    have d₄ := nruns_clr TP A₃
    have e : A₃.set TP [] = S4 n tp rest 0 na c d := by
      simp only [A₃, A₂, A₁, A, S3, S4, tpOut, List.replicate_zero]; lsimp
    rw [e] at d₄
    have hl : (A₃ TP).length = tp.length := by simp only [A₃, A₂, A₁, A, S3]; stk_simp
    rw [hl] at d₄
    have x := d₄.iteT (i := KS) (c := .zero)
      (q := .seq (.prim (.dup KS TT (by decide))) (.seq (.prim (.dec TT)) (zerosP TT TP))) (by rw [hKS]; exact eval_zero_zero [])
    exact (d₁.seq (d₂.seq (d₃.seq x))).mono (by omega)
  | succ k =>
    have d₄ := nruns_dup KS TT (by decide) A₃ hKS
    have ht' : A₃ TT = [] := by simp only [A₃, Lists.set_ne _ _ (show TT ≠ POS by decide), Lists.set_same]
    rw [ht'] at d₄
    let A₄ := A₃.set TT ([] ++ [k + 1])
    have d₅ := nruns_dec TT A₄ (l := []) (v := k + 1) (by simp only [A₄, Lists.set_same])
    let A₅ := A₄.set TT ([] ++ [k + 1 - 1])
    have d₆ := nruns_zeros TT TP (by decide) A₅ (lt := []) (x := k + 1 - 1) (by simp only [A₅, Lists.set_same])
    have e : (A₅.set TT []).set TP (A₅ TP ++ List.replicate (k + 1 - 1) 0) = S4 n tp rest (k + 1) na c d := by
      have htp : A₅ TP = tp := by simp only [A₅, A₄, A₃, A₂, A₁, A, S3]; stk_simp
      rw [htp]
      simp only [A₅, A₄, A₃, A₂, A₁, A, S3, S4, tpOut, Nat.add_sub_cancel]; lsimp
    rw [e] at d₆
    have x := (d₄.seq (d₅.seq d₆)).iteF (i := KS) (c := .zero) (p := nclr TP) (by rw [hKS]; exact eval_zero_succ [] k)
    exact (d₁.seq (d₂.seq (d₃.seq x))).mono (by omega)

end Shallot.MacroPeg.KExp
