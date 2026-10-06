import MacroPeg.HigherOrder.Mach.EvalSpec
import MacroPeg.HigherOrder.Mach.CodesNum
import Complexity.NFrame

/-!
# The item programs of the parser operators

The items `seq` (`5`), `alt` (`6`), `star` (`7`), `!` (`8`) and `λ` (`11`) on the evaluation stack.

`λ` leaves the stack as it is. The others replace the top vector(s) by a vector made chunk by chunk: the top
vectors are cut into `n` chunks of `N + 1` codes (`n` the number of environments of the item's context, `N` the
length of the input), and every chunk of the result is a function of the chunks at the same place.

The machine (`ops_core`):

* moves the two top vectors `va`, `vb` (reversed) to `RA`, `RB`; a unary operator first pushes an empty vector, so it
  runs as a binary one whose second operand is empty;
* repeats `n` times (`ops_outer`): cut the next chunk of each operand into the tables `CA`, `CB`, padded with zeros
  to `N + 1` codes (`ops_extract`); push the `N + 1` codes of the result (`ops_inner`), each by an element program `E`
  that reads the tables at random (`peekAt`); clear the tables.

The element programs are verified against a local specification (`ops_ElemOK`): from any state with the tables in
place and the position `q` on `QQ`, push the code at `q` on `EV`.
-/

namespace Shallot.MacroPeg.Mach

open Complexity
open Shallot.MacroPeg.HO Shallot.MacroPeg.Flat

/-! ## Names of the scratch stacks -/

/-- The rest of the first operand (reversed: the next code on top). -/
abbrev ops_RA : Fin NK := 18
/-- The rest of the second operand. -/
abbrev ops_RB : Fin NK := 19
/-- The current chunk of the first operand, as a table. -/
abbrev ops_CA : Fin NK := 20
/-- The current chunk of the second operand. -/
abbrev ops_CB : Fin NK := 21
/-- The chunks still to do. -/
abbrev ops_OC : Fin NK := 22
/-- The positions still to do in the current chunk. -/
abbrev ops_LC : Fin NK := 23
/-- The current position in the chunk. -/
abbrev ops_QQ : Fin NK := 24
/-- Scratch of `peekAt`. -/
abbrev ops_TT : Fin NK := 25
/-- The index read by `peekAt`. -/
abbrev ops_II : Fin NK := 26
/-- The code read. -/
abbrev ops_OO : Fin NK := 27
/-- The counter of `ops_extract`. -/
abbrev ops_CC : Fin NK := 28
/-- Scratch of the element programs. -/
abbrev ops_DD : Fin NK := 29
abbrev ops_UU : Fin NK := 30
abbrev ops_GG : Fin NK := 31
abbrev ops_PP : Fin NK := 32
abbrev ops_WW : Fin NK := 33

/-- The stacks an element program may use: empty. -/
def ops_AuxEmpty (S : Lists NK) : Prop := ∀ i : Fin NK, 25 ≤ i.val → i.val ≤ 33 → S i = []

theorem ops_aux_set {S : Lists NK} (h : ops_AuxEmpty S) {i : Fin NK} (hi : i.val < 25 ∨ 33 < i.val)
    (v : List Nat) : ops_AuxEmpty (S.set i v) := by
  intro x h₁ h₂
  have hx : x ≠ i := by intro e; subst e; omega
  rw [Lists.set_ne _ _ hx]; exact h x h₁ h₂

/-- Equalities of states updated at a few stacks: compare stack by stack (the names are numerals, so `decide`
settles any two of them). -/
macro "ops_eq" : tactic =>
  `(tactic| (funext x; simp only [Lists.set]; repeat' split
             all_goals (try subst_vars)
             all_goals (try simp_all (config := { decide := true }))
             all_goals (try omega)))

/-- Like `ops_eq`, settling the impossible cases by `decide` first. -/
macro "ops_eq'" : tactic =>
  `(tactic| (funext x; simp only [Lists.set]; repeat' split
             all_goals (try subst_vars)
             all_goals (first | rfl | (exact absurd ‹@Eq (Fin NK) _ _› (by decide)) |
               (simp_all (config := { decide := true })))))

/-- The value of a state updated at a few stacks, at one stack. -/
macro "ops_at" : tactic =>
  `(tactic| (simp only [Lists.set]; (try simp (config := { decide := true })); all_goals (first | assumption | rfl | skip)))

/-! ## Lists -/

theorem ops_getD_lt (l : List Nat) {k : Nat} (h : k < l.length) : l.getD k 0 = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- A chunk padded with zeros to exactly `N + 1` codes. -/
def ops_pad (N : Nat) (L : List Nat) : List Nat := (L ++ List.replicate (N + 1) 0).take (N + 1)

theorem ops_length_pad (N : Nat) (L : List Nat) : (ops_pad N L).length = N + 1 := by
  simp [ops_pad]

theorem ops_getD_pad (N : Nat) (L : List Nat) (k : Nat) :
    (ops_pad N L).getD k 0 = (L.take (N + 1)).getD k 0 := by
  simp only [ops_pad, List.getD_eq_getElem?_getD, List.getElem?_take]
  by_cases hk : k < N + 1
  · simp only [hk, if_true]
    by_cases hl : k < L.length
    · rw [List.getElem?_append_left hl]
    · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := L) (by omega),
        List.getElem?_replicate, if_pos (by omega)]
      rfl
  · simp [hk]

/-- `chunksN` as chunks at the multiples of `k`. -/
theorem ops_chunksN (k : Nat) : ∀ (n : Nat) (l : List Nat),
    chunksN k n l = (List.range n).map (fun i => (l.drop (i * k)).take k)
  | 0, _ => rfl
  | n + 1, l => by
    rw [chunksN, ops_chunksN k n (l.drop k), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.zero_mul, List.drop_zero, Function.comp_def, List.drop_drop]
    congr 1
    apply List.map_congr_left
    intro i _
    congr 2
    rw [Nat.succ_mul]; omega

/-! ## Small programs -/

/-- Lower the top of `d` by the top of `u` (the top of `u` becomes `0`). -/
def ops_subLoop (u d : Fin NK) : NProg NK := .loop u .pos (.seq (.prim (.dec u)) (.prim (.dec d)))

theorem ops_subLoop_runs (u d : Fin NK) (hud : u ≠ d) (S : Lists NK) {lu ld : List Nat} {a b : Nat}
    (hu : S u = lu ++ [a]) (hd : S d = ld ++ [b]) :
    NRuns (ops_subLoop u d) S ((S.set u (lu ++ [0])).set d (ld ++ [b - a])) (3 * a + 1) := by
  let F : Nat → Lists NK := fun m => (S.set u (lu ++ [a - m])).set d (ld ++ [b - m])
  have h0 : F 0 = S := by
    simp only [F, Nat.sub_zero, ← hu, ← hd, Lists.set_get_self]
  have hFu : ∀ m, F m u = lu ++ [a - m] := fun m => by simp only [F]; rw [Lists.set_ne _ _ hud, Lists.set_same]
  have hFd : ∀ m, F m d = ld ++ [b - m] := fun m => by simp only [F, Lists.set_same]
  have hl := nruns_family_const (i := u) (c := .pos) (p := .seq (.prim (.dec u)) (.prim (.dec d))) F a 2
    (fun m hm => by rw [hFu, show a - m = (a - m - 1) + 1 by omega]; simp)
    (by rw [hFu, Nat.sub_self]; simp)
    (fun m hm => by
      have h₁ := nruns_dec u (F m) (hFu m)
      have h₂ := nruns_dec d ((F m).set u (lu ++ [a - m - 1])) (l := ld) (v := b - m)
        (by rw [Lists.set_ne _ _ (Ne.symm hud)]; exact hFd m)
      have e : ((F m).set u (lu ++ [a - m - 1])).set d (ld ++ [b - m - 1]) = F (m + 1) := by
        simp only [F]; ops_eq
      rw [e] at h₂; exact h₁.seq h₂)
  rw [h0] at hl
  have e : F a = (S.set u (lu ++ [0])).set d (ld ++ [b - a]) := by simp only [F, Nat.sub_self]
  rw [e] at hl
  exact hl.mono (by omega)

/-- `caseTop` beyond its branches, for a program that runs on. -/
theorem ops_caseTop_default (i : Fin NK) : ∀ (ps : List (NProg NK)) (q : NProg NK) (v : Nat) (S : Lists NK)
    (l : List Nat), S i = l ++ [v + ps.length] → ∀ (S' : Lists NK) (T : Nat),
      NRuns q (S.set i (l ++ [v])) S' T → NRuns (caseTop i ps q) S S' (T + 2 * ps.length)
  | [], q, v, S, l, hS, S', T, h => by
    simp only [List.length_nil, Nat.add_zero] at hS ⊢
    rw [← hS, Lists.set_get_self] at h; exact h
  | p :: ps, q, v, S, l, hS, S', T, h => by
    simp only [List.length_cons] at hS ⊢
    have hS' : S i = l ++ [(v + ps.length) + 1] := by rw [hS]; congr 2
    have h₁ := nruns_dec i S hS'
    simp only [Nat.add_sub_cancel] at h₁
    have h₂ := ops_caseTop_default i ps q v (S.set i (l ++ [v + ps.length])) l (by simp) S' T
      (by rw [Lists.set_set_u]; exact h)
    exact ((h₁.seq h₂).iteF (by rw [hS']; simp)).mono (by omega)

/-! ## Cutting a chunk -/

/-- Move the next `N + 1` codes of `R` (the next on top) to the table `C`, pushing zeros once `R` is empty. -/
def ops_extract (R C : Fin NK) (h : R ≠ C) : NProg NK :=
  .seq (.prim (.dup NX ops_CC (by decide))) (.seq (.prim (.inc ops_CC))
    (.seq (.loop ops_CC .pos (.seq (.prim (.dec ops_CC)) (.ite R .nonempty (nmv R C h) (.prim (.pushZ C)))))
      (.prim (.pop ops_CC))))

theorem ops_take_pad_succ {N m : Nat} (L : List Nat) (hm : m < N + 1) :
    (L ++ List.replicate (N + 1) 0).take (m + 1) =
      (L ++ List.replicate (N + 1) 0).take m ++ [(L ++ List.replicate (N + 1) 0)[m]'(by simp; omega)] :=
  List.take_succ_eq_append_getElem _

theorem ops_extract_runs (R C : Fin NK) (h : R ≠ C) (hRN : R ≠ NX) (hCN : C ≠ NX) (hRc : R ≠ ops_CC)
    (hCc : C ≠ ops_CC) (S : Lists NK) (N : Nat) (L : List Nat) (hN : S NX = [N]) (hcc : S ops_CC = [])
    (hR : S R = L.reverse) (hC : S C = []) :
    NRuns (ops_extract R C h) S ((S.set R (L.drop (N + 1)).reverse).set C (ops_pad N L)) (5 * (N + 1) + 4) := by
  have x₁ := nruns_dup NX ops_CC (by decide) S (l := []) (v := N) hN
  rw [hcc, List.nil_append] at x₁
  have x₂ := nruns_inc ops_CC (S.set ops_CC [N]) (l := []) (v := N) (by simp)
  rw [Lists.set_set_u] at x₂
  let F : Nat → Lists NK := fun m =>
    ((S.set ops_CC [N + 1 - m]).set R (L.drop m).reverse).set C ((L ++ List.replicate (N + 1) 0).take m)
  have h0 : F 0 = S.set ops_CC [N + 1] := by
    simp only [F, Nat.sub_zero, List.drop_zero, List.take_zero, ← hR, ← hC]
    ops_eq
  have hFc : ∀ m, F m ops_CC = [] ++ [N + 1 - m] := fun m => by
    simp only [F]; rw [Lists.set_ne _ _ (Ne.symm hCc), Lists.set_ne _ _ (Ne.symm hRc), Lists.set_same]; rfl
  have hl := nruns_family_const (i := ops_CC) (c := .pos)
    (p := .seq (.prim (.dec ops_CC)) (.ite R .nonempty (nmv R C h) (.prim (.pushZ C)))) F (N + 1) 4
    (fun m hm => by rw [hFc, show N + 1 - m = (N + 1 - m - 1) + 1 by omega]; simp [NTest.eval])
    (by rw [hFc, Nat.sub_self]; simp [NTest.eval])
    (fun m hm => by
      have d₁ := nruns_dec ops_CC (F m) (hFc m)
      let S₂ := (F m).set ops_CC ([] ++ [N + 1 - m - 1])
      have hS₂R : S₂ R = (L.drop m).reverse := by
        simp only [S₂, F]; rw [Lists.set_ne _ _ hRc, Lists.set_ne _ _ h, Lists.set_same]
      have hS₂C : S₂ C = (L ++ List.replicate (N + 1) 0).take m := by
        simp only [S₂, F]; rw [Lists.set_ne _ _ hCc, Lists.set_same]
      by_cases hlm : m < L.length
      · have hd : (L.drop m).reverse = (L.drop (m + 1)).reverse ++ [L[m]] := by
          rw [List.drop_eq_getElem_cons hlm, List.reverse_cons]
        have d₂ := nruns_mv R C h S₂ (l := (L.drop (m + 1)).reverse) (v := L[m]) (by rw [hS₂R, hd])
        have e : (S₂.set C (S₂ C ++ [L[m]])).set R (L.drop (m + 1)).reverse = F (m + 1) := by
          rw [hS₂C, ← List.getElem_append_left (bs := List.replicate (N + 1) 0) hlm, ← ops_take_pad_succ L hm]
          simp only [S₂, F]
          ops_eq
        rw [e] at d₂
        exact (d₁.seq (d₂.iteT (by show NTest.nonempty.eval (S₂ R) = true; rw [hS₂R, hd]; simp))).mono (by omega)
      · have hnil : L.drop m = [] := List.drop_eq_nil_of_le (by omega)
        have hnil' : L.drop (m + 1) = [] := List.drop_eq_nil_of_le (by omega)
        have d₂ := nruns_pushZ C S₂
        have hz : (L ++ List.replicate (N + 1) 0)[m]'(by simp; omega) = 0 := by
          rw [List.getElem_append_right (by omega)]; simp
        have e : S₂.set C (S₂ C ++ [0]) = F (m + 1) := by
          have ht := ops_take_pad_succ L hm
          rw [hz] at ht
          rw [hS₂C, ← ht]
          simp only [S₂, F, hnil, hnil']
          ops_eq
        rw [e] at d₂
        exact (d₁.seq (d₂.iteF (by show NTest.nonempty.eval (S₂ R) = false; rw [hS₂R, hnil]; rfl))).mono (by omega))
  rw [h0] at hl
  have hp := nruns_pop ops_CC (F (N + 1)) (l := []) (v := 0) (by rw [hFc, Nat.sub_self])
  have e : (F (N + 1)).set ops_CC [] = (S.set R (L.drop (N + 1)).reverse).set C (ops_pad N L) := by
    simp only [F, ops_pad]
    rw [← hcc]
    ops_eq
  rw [e] at hp
  exact (x₁.seq (x₂.seq (hl.seq hp))).mono (by omega)

/-! ## The codes of one chunk -/

/-- An element program: from a state with the chunk tables `ca`, `cb` on `CA`, `CB` and the position `q` on `QQ`,
it pushes the code `g ca cb q` on `EV`, within `TE` steps. -/
def ops_ElemOK (E : NProg NK) (N : Nat) (g : List Nat → List Nat → Nat → Nat) (TE : Nat) : Prop :=
  ∀ (ca cb : List Nat), ca.length = N + 1 → cb.length = N + 1 → ∀ q, q ≤ N → ∀ (S : Lists NK),
    S ops_CA = ca → S ops_CB = cb → S ops_QQ = [q] → S NX = [N] → ops_AuxEmpty S →
    NRuns E S (S.set EV (S EV ++ [g ca cb q])) TE

/-- Push the codes at the positions `0, …, N`, counting them on the top of `EVL`. -/
def ops_inner (E : NProg NK) : NProg NK :=
  .seq (.prim (.pushZ ops_QQ)) (.seq (.prim (.dup NX ops_LC (by decide))) (.seq (.prim (.inc ops_LC))
    (.seq (.loop ops_LC .pos
        (.seq E (.seq (.prim (.inc EVL)) (.seq (.prim (.inc ops_QQ)) (.prim (.dec ops_LC))))))
      (.seq (.prim (.pop ops_LC)) (.prim (.pop ops_QQ))))))

theorem ops_inner_runs {E : NProg NK} {N : Nat} {g : List Nat → List Nat → Nat → Nat} {TE : Nat}
    (hE : ops_ElemOK E N g TE) (S : Lists NK) (ca cb : List Nat) (hca : ca.length = N + 1)
    (hcb : cb.length = N + 1) (hA : S ops_CA = ca) (hB : S ops_CB = cb) (hN : S NX = [N]) (hq : S ops_QQ = [])
    (hl : S ops_LC = []) (haux : ops_AuxEmpty S) {lv : List Nat} {k : Nat} (hv : S EVL = lv ++ [k]) :
    NRuns (ops_inner E) S ((S.set EV (S EV ++ (List.range (N + 1)).map (g ca cb))).set EVL (lv ++ [k + (N + 1)]))
      ((N + 1) * (TE + 4) + 6) := by
  have x₁ := nruns_pushZ ops_QQ S
  rw [hq, List.nil_append] at x₁
  have x₂ := nruns_dup NX ops_LC (by decide) (S.set ops_QQ [0]) (l := []) (v := N) (by rw [Lists.set_ne _ _ (by decide)]; exact hN)
  rw [Lists.set_ne _ _ (by decide), hl, List.nil_append] at x₂
  have x₃ := nruns_inc ops_LC ((S.set ops_QQ [0]).set ops_LC [N]) (l := []) (v := N) (by simp)
  rw [Lists.set_set_u] at x₃
  let F : Nat → Lists NK := fun m =>
    (((S.set ops_QQ [m]).set ops_LC [N + 1 - m]).set EV (S EV ++ (List.range m).map (g ca cb))).set EVL
      (lv ++ [k + m])
  have h0 : F 0 = (S.set ops_QQ [0]).set ops_LC ([] ++ [N + 1]) := by
    simp only [F, Nat.sub_zero, List.range_zero, List.map_nil, List.append_nil, Nat.add_zero, ← hv]
    ops_eq
  have hFl : ∀ m, F m ops_LC = [] ++ [N + 1 - m] := fun m => by simp only [F]; ops_at
  have hloop := nruns_family_const (i := ops_LC) (c := .pos)
    (p := .seq E (.seq (.prim (.inc EVL)) (.seq (.prim (.inc ops_QQ)) (.prim (.dec ops_LC))))) F (N + 1) (TE + 3)
    (fun m hm => by rw [hFl, show N + 1 - m = (N + 1 - m - 1) + 1 by omega]; simp [NTest.eval])
    (by rw [hFl, Nat.sub_self]; simp [NTest.eval])
    (fun m hm => by
      have hFA : F m ops_CA = ca := by simp only [F]; ops_at
      have hFB : F m ops_CB = cb := by simp only [F]; ops_at
      have hFq : F m ops_QQ = [m] := by simp only [F]; ops_at
      have hFN : F m NX = [N] := by simp only [F]; ops_at
      have hFa : ops_AuxEmpty (F m) :=
        ops_aux_set (ops_aux_set (ops_aux_set (ops_aux_set haux (by decide) _) (by decide) _) (by decide) _)
          (by decide) _
      have e₁ := hE ca cb hca hcb m (by omega) (F m) hFA hFB hFq hFN hFa
      have hFv : F m EV = S EV ++ (List.range m).map (g ca cb) := by simp only [F]; ops_at
      let S₁ := (F m).set EV (F m EV ++ [g ca cb m])
      have e₂ := nruns_inc EVL S₁ (l := lv) (v := k + m) (by simp only [S₁, F]; ops_at)
      have e₃ := nruns_inc ops_QQ (S₁.set EVL (lv ++ [k + m + 1])) (l := []) (v := m)
        (by simp only [S₁, F]; ops_at)
      have e₄ := nruns_dec ops_LC ((S₁.set EVL (lv ++ [k + m + 1])).set ops_QQ ([] ++ [m + 1])) (l := [])
        (v := N + 1 - m) (by simp only [S₁, F]; ops_at)
      have e : (((S₁.set EVL (lv ++ [k + m + 1])).set ops_QQ ([] ++ [m + 1])).set ops_LC ([] ++ [N + 1 - m - 1])) =
          F (m + 1) := by
        simp only [S₁, hFv, F, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
          show N + 1 - m - 1 = N + 1 - (m + 1) by omega, show k + m + 1 = k + (m + 1) by omega]
        ops_eq
      rw [e] at e₄
      exact (e₁.seq (e₂.seq (e₃.seq e₄))).mono (by omega))
  rw [h0] at hloop
  have p₁ := nruns_pop ops_LC (F (N + 1)) (l := []) (v := 0) (by rw [hFl, Nat.sub_self])
  have p₂ := nruns_pop ops_QQ ((F (N + 1)).set ops_LC []) (l := []) (v := N + 1) (by simp only [F]; ops_at)
  have e : ((F (N + 1)).set ops_LC []).set ops_QQ [] =
      (S.set EV (S EV ++ (List.range (N + 1)).map (g ca cb))).set EVL (lv ++ [k + (N + 1)]) := by
    simp only [F, Nat.sub_self]
    ops_eq
  rw [e] at p₂
  simp only [List.nil_append] at hloop
  exact (x₁.seq (x₂.seq (x₃.seq (hloop.seq (p₁.seq p₂))))).mono (by
    rw [Nat.mul_add]; omega)

/-! ## All the chunks -/

/-- The codes of chunk `i`: the function `g` on the padded chunks `i` of `va` and `vb`. -/
def ops_chunkOut (N : Nat) (g : List Nat → List Nat → Nat → Nat) (va vb : List Nat) (i : Nat) : List Nat :=
  (List.range (N + 1)).map (g (ops_pad N (va.drop (i * (N + 1)))) (ops_pad N (vb.drop (i * (N + 1)))))

/-- Repeat for the chunks still to do (on `OC`): cut a chunk of each operand, push its codes, clear the tables. -/
def ops_outer (E : NProg NK) : NProg NK :=
  .loop ops_OC .pos (.seq (.prim (.dec ops_OC)) (.seq (ops_extract ops_RA ops_CA (by decide))
    (.seq (ops_extract ops_RB ops_CB (by decide)) (.seq (ops_inner E) (.seq (nclr ops_CA) (nclr ops_CB))))))

theorem ops_drop_succ (v : List Nat) (N i : Nat) :
    (v.drop (i * (N + 1))).drop (N + 1) = v.drop ((i + 1) * (N + 1)) := by
  rw [List.drop_drop, Nat.succ_mul]

/-- One round of `ops_outer`, on the stacks. -/
theorem ops_outer_step_eq (S : Lists NK) (o o' ra ra' rb rb' ca cb ev ev' l l' : List Nat)
    (hca : S ops_CA = []) (hcb : S ops_CB = []) :
    (((((((((((((S.set ops_OC o).set ops_RA ra).set ops_RB rb).set EV ev).set EVL l).set ops_OC o').set ops_RA
      ra').set ops_CA ca).set ops_RB rb').set ops_CB cb).set EV ev').set EVL l').set ops_CA []).set ops_CB [] =
    ((((S.set ops_OC o').set ops_RA ra').set ops_RB rb').set EV ev').set EVL l' := by
  funext x
  simp only [Lists.set]
  by_cases h₁ : x = ops_CB
  · subst h₁; simp (config := { decide := true }) [hcb]
  by_cases h₂ : x = ops_CA
  · subst h₂; simp (config := { decide := true }) [hca]
  simp only [h₁, h₂, if_false]
  by_cases h₃ : x = EVL
  · simp [h₃]
  by_cases h₄ : x = EV
  · simp [h₄]
  by_cases h₅ : x = ops_RB
  · simp [h₅]
  by_cases h₆ : x = ops_RA
  · simp [h₆]
  by_cases h₇ : x = ops_OC <;> simp [h₃, h₄, h₅, h₆, h₇]

theorem ops_outer_runs {E : NProg NK} {N : Nat} {g : List Nat → List Nat → Nat → Nat} {TE : Nat}
    (hE : ops_ElemOK E N g TE) (S : Lists NK) (n : Nat) (va vb : List Nat) (hN : S NX = [N])
    (hoc : S ops_OC = [n]) (hra : S ops_RA = va.reverse) (hrb : S ops_RB = vb.reverse) (hca : S ops_CA = [])
    (hcb : S ops_CB = []) (hq : S ops_QQ = []) (hl : S ops_LC = []) (haux : ops_AuxEmpty S) {lv : List Nat}
    {k : Nat} (hv : S EVL = lv ++ [k]) :
    NRuns (ops_outer E) S
      (((((S.set ops_OC [0]).set ops_RA (va.drop (n * (N + 1))).reverse).set ops_RB
        (vb.drop (n * (N + 1))).reverse).set EV (S EV ++ ((List.range n).map (ops_chunkOut N g va vb)).flatten)).set
        EVL (lv ++ [k + n * (N + 1)]))
      (n * ((N + 1) * (TE + 4) + 14 * (N + 1) + 18) + 1) := by
  have hcc : S ops_CC = [] := haux ops_CC (by decide) (by decide)
  let G : Nat → Lists NK := fun i =>
    ((((S.set ops_OC [n - i]).set ops_RA (va.drop (i * (N + 1))).reverse).set ops_RB
      (vb.drop (i * (N + 1))).reverse).set EV (S EV ++ ((List.range i).map (ops_chunkOut N g va vb)).flatten)).set
      EVL (lv ++ [k + i * (N + 1)])
  have h0 : G 0 = S := by
    simp only [G, Nat.sub_zero, Nat.zero_mul, List.drop_zero, List.range_zero, List.map_nil, List.flatten_nil,
      List.append_nil, Nat.add_zero, ← hoc, ← hra, ← hrb, ← hv]
    ops_eq
  have hGo : ∀ i, G i ops_OC = [] ++ [n - i] := fun i => by simp only [G]; ops_at
  have hloop := nruns_family_const (i := ops_OC) (c := .pos)
    (p := .seq (.prim (.dec ops_OC)) (.seq (ops_extract ops_RA ops_CA (by decide))
      (.seq (ops_extract ops_RB ops_CB (by decide)) (.seq (ops_inner E) (.seq (nclr ops_CA) (nclr ops_CB))))))
    G n ((N + 1) * (TE + 4) + 14 * (N + 1) + 17)
    (fun i hi => by rw [hGo, show n - i = (n - i - 1) + 1 by omega]; simp [NTest.eval])
    (by rw [hGo, Nat.sub_self]; simp [NTest.eval])
    (fun i hi => by
      let La := va.drop (i * (N + 1))
      let Lb := vb.drop (i * (N + 1))
      have d₁ := nruns_dec ops_OC (G i) (hGo i)
      let S₁ := (G i).set ops_OC ([] ++ [n - i - 1])
      have d₂ := ops_extract_runs ops_RA ops_CA (by decide) (by decide) (by decide) (by decide) (by decide) S₁ N La
        (by simp only [S₁, G]; ops_at) (by simp only [S₁, G]; ops_at) (by simp only [S₁, G]; ops_at)
        (by simp only [S₁, G]; ops_at)
      let S₂ := (S₁.set ops_RA (La.drop (N + 1)).reverse).set ops_CA (ops_pad N La)
      have d₃ := ops_extract_runs ops_RB ops_CB (by decide) (by decide) (by decide) (by decide) (by decide) S₂ N Lb
        (by simp only [S₂, S₁, G]; ops_at) (by simp only [S₂, S₁, G]; ops_at) (by simp only [S₂, S₁, G]; ops_at)
        (by simp only [S₂, S₁, G]; ops_at)
      let S₃ := (S₂.set ops_RB (Lb.drop (N + 1)).reverse).set ops_CB (ops_pad N Lb)
      have haux₃ : ops_AuxEmpty S₃ := by
        simp only [S₃, S₂, S₁, G]
        repeat (apply ops_aux_set _ (by decide))
        exact haux
      have d₄ := ops_inner_runs hE S₃ (ops_pad N La) (ops_pad N Lb) (ops_length_pad N La) (ops_length_pad N Lb)
        (by simp only [S₃, S₂, S₁, G]; ops_at) (by simp only [S₃, S₂, S₁, G]; ops_at)
        (by simp only [S₃, S₂, S₁, G]; ops_at) (by simp only [S₃, S₂, S₁, G]; ops_at)
        (by simp only [S₃, S₂, S₁, G]; ops_at) haux₃ (lv := lv) (k := k + i * (N + 1))
        (by simp only [S₃, S₂, S₁, G]; ops_at)
      let S₄ := (S₃.set EV (S₃ EV ++ (List.range (N + 1)).map (g (ops_pad N La) (ops_pad N Lb)))).set EVL
        (lv ++ [k + i * (N + 1) + (N + 1)])
      have d₅ := nruns_clr ops_CA S₄
      have d₆ := nruns_clr ops_CB (S₄.set ops_CA [])
      have hlA : (S₄ ops_CA).length = N + 1 := by
        simp only [S₄, S₃, S₂, S₁, G]; ops_at; exact ops_length_pad N La
      have hlB : ((S₄.set ops_CA []) ops_CB).length = N + 1 := by
        simp only [S₄, S₃, S₂, S₁, G]; ops_at; exact ops_length_pad N Lb
      rw [hlA] at d₅
      rw [hlB] at d₆
      have e : (S₄.set ops_CA []).set ops_CB [] = G (i + 1) := by
        have hEV : S₃ EV = S EV ++ ((List.range i).map (ops_chunkOut N g va vb)).flatten := by
          simp only [S₃, S₂, S₁, G]; ops_at
        simp only [S₄, hEV]
        simp only [S₃, S₂, S₁, G]
        rw [ops_outer_step_eq S _ _ _ _ _ _ _ _ _ _ _ _ hca hcb]
        simp only [La, Lb, ops_drop_succ, List.range_succ (n := i), List.map_append, List.map_cons,
          List.map_nil, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc,
          show n - i - 1 = n - (i + 1) by omega, show k + i * (N + 1) + (N + 1) = k + (i + 1) * (N + 1) by
            rw [Nat.succ_mul]; omega, List.nil_append]
        rfl
      rw [e] at d₆
      exact (d₁.seq (d₂.seq (d₃.seq (d₄.seq (d₅.seq d₆))))).mono (by omega))
  rw [h0] at hloop
  have e : G n = ((((S.set ops_OC [0]).set ops_RA (va.drop (n * (N + 1))).reverse).set ops_RB
        (vb.drop (n * (N + 1))).reverse).set EV (S EV ++ ((List.range n).map (ops_chunkOut N g va vb)).flatten)).set
        EVL (lv ++ [k + n * (N + 1)]) := by
    simp only [G, Nat.sub_self]
  rw [e] at hloop
  exact hloop

/-! ## Reading a code and branching on it -/

/-- Read the code at the position on `src` of the table `CA` onto `OO`. -/
def ops_read (src : Fin NK) (h : src ≠ ops_II) : NProg NK :=
  .seq (.prim (.dup src ops_II h)) (peekAt ops_CA ops_TT ops_II ops_OO (by decide) (by decide))

theorem ops_read_runs (src : Fin NK) (h : src ≠ ops_II) (S : Lists NK) (N q : Nat)
    (ca : List Nat) (hca : ca.length = N + 1) (hq : q ≤ N) (hA : S ops_CA = ca) (hQ : S src = [q])
    (hI : S ops_II = []) (hO : S ops_OO = []) (hT : S ops_TT = []) :
    NRuns (ops_read src h) S (S.set ops_OO [ca.getD q 0]) (10 * (N + 1) + 7) := by
  have x₁ := nruns_dup src ops_II h S (l := []) (v := q) hQ
  rw [hI, List.nil_append] at x₁
  have x₂ := nruns_peekAt ops_CA ops_TT ops_II ops_OO (by decide) (by decide) (by decide) (S.set ops_II [q])
    (by rw [Lists.set_ne _ _ (by decide)]; exact hT) (lc := []) (k := q) (by simp)
    (by rw [Lists.set_ne _ _ (by decide), hA, hca]; omega)
  have hv : (S.set ops_II [q]) ops_CA = ca := by rw [Lists.set_ne _ _ (by decide)]; exact hA
  have e : ((S.set ops_II [q]).set ops_II []).set ops_OO ((S.set ops_II [q]) ops_OO ++
      [((S.set ops_II [q]) ops_CA)[q]'(by rw [hv, hca]; omega)]) = S.set ops_OO [ca.getD q 0] := by
    have hg : ((S.set ops_II [q]) ops_CA)[q]'(by rw [hv, hca]; omega) = ca.getD q 0 := by
      simp only [hv]; rw [ops_getD_lt _ (by omega)]
    have hS : S.set ops_II [] = S := by rw [← hI]; exact Lists.set_get_self S _
    rw [hg, Lists.set_set_u, Lists.set_ne _ _ (by decide), hO, List.nil_append, hS]
  rw [e, hv, hca] at x₂
  exact (x₁.seq x₂).mono (by omega)

/-- Read the code at the position on `QQ` of the table `CA` onto `OO`. -/
abbrev ops_readA : NProg NK := ops_read ops_QQ (by decide)

theorem ops_readA_runs (S : Lists NK) (N q : Nat) (ca : List Nat) (hca : ca.length = N + 1) (hq : q ≤ N)
    (hA : S ops_CA = ca) (hQ : S ops_QQ = [q]) (haux : ops_AuxEmpty S) :
    NRuns ops_readA S (S.set ops_OO [ca.getD q 0]) (10 * (N + 1) + 7) :=
  ops_read_runs ops_QQ (by decide) S N q ca hca hq hA hQ (haux ops_II (by decide) (by decide))
    (haux ops_OO (by decide) (by decide)) (haux ops_TT (by decide) (by decide))

/-- Branch on the code `c` on `OO`: `0`, `1`, or `v + 2` (then `v` is left on `OO`). -/
theorem ops_case3 (p₀ p₁ d : NProg NK) (S S' : Lists NK) (c T : Nat) (hO : S ops_OO = [])
    (h₀ : c = 0 → NRuns p₀ S S' T) (h₁ : c = 1 → NRuns p₁ S S' T)
    (h₂ : ∀ v, c = v + 2 → NRuns d (S.set ops_OO [v]) S' T) :
    NRuns (caseTop ops_OO [p₀, p₁] d) (S.set ops_OO [c]) S' (T + 4) := by
  have hS : (S.set ops_OO [c]).set ops_OO [] = S := by rw [Lists.set_set_u, ← hO, Lists.set_get_self]
  match c with
  | 0 =>
    have := caseTop_runs ops_OO [p₀, p₁] d 0 (by simp) (S.set ops_OO [0]) [] (by simp) S' T
      (by rw [hS]; exact h₀ rfl)
    exact this.mono (by omega)
  | 1 =>
    have := caseTop_runs ops_OO [p₀, p₁] d 1 (by simp) (S.set ops_OO [1]) [] (by simp) S' T
      (by rw [hS]; exact h₁ rfl)
    exact this.mono (by omega)
  | v + 2 =>
    have := ops_caseTop_default ops_OO [p₀, p₁] d v (S.set ops_OO [v + 2]) [] (by simp) S' T
      (by rw [Lists.set_set_u]; exact h₂ v rfl)
    exact this.mono (by simp)

/-! ## `seq` -/

/-- The code of `seq` at position `q`. -/
def ops_seqG (ca cb : List Nat) (q : Nat) : Nat := let c := ca.getD q 0; if 2 ≤ c then cb.getD (c - 2) 0 else c

/-- With `v = c - 2` on `OO`: the code of `cb` at `v`, if `v ≤ N`, else `0`. -/
def ops_seqTail : NProg NK :=
  .seq (.prim (.dup ops_OO ops_DD (by decide))) (.seq (.prim (.dup NX ops_UU (by decide)))
    (.seq (ops_subLoop ops_UU ops_DD) (.seq (.prim (.pop ops_UU))
      (.ite ops_DD .zero (.seq (.prim (.pop ops_DD)) (peekAt ops_CB ops_TT ops_OO EV (by decide) (by decide)))
        (.seq (.prim (.pop ops_DD)) (.seq (.prim (.pop ops_OO)) (.prim (.pushZ EV))))))))

def ops_seqE : NProg NK :=
  .seq ops_readA (caseTop ops_OO [.prim (.pushZ EV), npushC EV 1] ops_seqTail)

theorem ops_seqTail_runs (S : Lists NK) (N v : Nat) (cb : List Nat) (hcb : cb.length = N + 1)
    (hB : S ops_CB = cb) (hN : S NX = [N]) (haux : ops_AuxEmpty S) :
    NRuns ops_seqTail (S.set ops_OO [v]) (S.set EV (S EV ++ [cb.getD v 0])) (13 * (N + 1) + 9) := by
  have hO : S ops_OO = [] := haux ops_OO (by decide) (by decide)
  have hD : S ops_DD = [] := haux ops_DD (by decide) (by decide)
  have hU : S ops_UU = [] := haux ops_UU (by decide) (by decide)
  have hT : S ops_TT = [] := haux ops_TT (by decide) (by decide)
  have x₁ := nruns_dup ops_OO ops_DD (by decide) (S.set ops_OO [v]) (l := []) (v := v) (by simp)
  have x₂ := nruns_dup NX ops_UU (by decide) ((S.set ops_OO [v]).set ops_DD ((S.set ops_OO [v]) ops_DD ++ [v]))
    (l := []) (v := N) (by ops_at)
  have x₃ := ops_subLoop_runs ops_UU ops_DD (by decide) ((((S.set ops_OO [v]).set ops_DD
    ((S.set ops_OO [v]) ops_DD ++ [v])).set ops_UU (((S.set ops_OO [v]).set ops_DD
    ((S.set ops_OO [v]) ops_DD ++ [v])) ops_UU ++ [N]))) (lu := []) (ld := []) (a := N) (b := v) (by ops_at)
    (by ops_at)
  let S₃ := (((((S.set ops_OO [v]).set ops_DD ((S.set ops_OO [v]) ops_DD ++ [v])).set ops_UU
    (((S.set ops_OO [v]).set ops_DD ((S.set ops_OO [v]) ops_DD ++ [v])) ops_UU ++ [N])).set ops_UU ([] ++ [0])).set
    ops_DD ([] ++ [v - N]))
  have x₄ := nruns_pop ops_UU S₃ (l := []) (v := 0) (by simp only [S₃]; ops_at)
  let S₄ := S₃.set ops_UU []
  have hS₄ : S₄ = ((S.set ops_OO [v]).set ops_DD [v - N]) := by
    simp only [S₄, S₃]
    ops_eq
  rw [show S₃.set ops_UU [] = S₄ from rfl, hS₄] at x₄
  by_cases hv : v ≤ N
  · have p₁ := nruns_pop ops_DD ((S.set ops_OO [v]).set ops_DD [v - N]) (l := []) (v := 0)
      (by rw [show v - N = 0 by omega]; simp)
    have hS₅ : ((S.set ops_OO [v]).set ops_DD [v - N]).set ops_DD [] = S.set ops_OO [v] := by
      rw [Lists.set_set_u, ← hD]
      ops_eq
    rw [hS₅] at p₁
    have p₂ := nruns_peekAt ops_CB ops_TT ops_OO EV (by decide) (by decide) (by decide) (S.set ops_OO [v])
      (by ops_at) (lc := []) (k := v) (by simp) (by ops_at; rw [hB, hcb]; omega)
    have hg : ((S.set ops_OO [v]) ops_CB)[v]'(by ops_at; rw [hB, hcb]; omega) = cb.getD v 0 := by
      simp only [Lists.set_ne _ _ (show ops_CB ≠ ops_OO by decide), hB]
      rw [ops_getD_lt _ (by omega)]
    have e : ((S.set ops_OO [v]).set ops_OO []).set EV ((S.set ops_OO [v]) EV ++
        [((S.set ops_OO [v]) ops_CB)[v]'(by ops_at; rw [hB, hcb]; omega)]) = S.set EV (S EV ++ [cb.getD v 0]) := by
      rw [hg]
      ops_eq
    rw [e] at p₂
    have hlen : ((S.set ops_OO [v]) ops_CB).length = N + 1 := by ops_at; rw [hB, hcb]
    rw [hlen] at p₂
    have := (x₁.seq (x₂.seq (x₃.seq (x₄.seq ((p₁.seq p₂).iteT (i := ops_DD) (c := .zero)
      (q := .seq (.prim (.pop ops_DD)) (.seq (.prim (.pop ops_OO)) (.prim (.pushZ EV))))
      (by ops_at; rw [show v - N = 0 by omega]; rfl))))))
    exact this.mono (by omega)
  · have p₁ := nruns_pop ops_DD ((S.set ops_OO [v]).set ops_DD [v - N]) (l := []) (v := v - N) (by simp)
    have p₂ := nruns_pop ops_OO (((S.set ops_OO [v]).set ops_DD [v - N]).set ops_DD []) (l := []) (v := v)
      (by ops_at)
    have p₃ := nruns_pushZ EV ((((S.set ops_OO [v]).set ops_DD [v - N]).set ops_DD []).set ops_OO [])
    have hz : cb.getD v 0 = 0 := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have e : ((((S.set ops_OO [v]).set ops_DD [v - N]).set ops_DD []).set ops_OO []).set EV
        (((((S.set ops_OO [v]).set ops_DD [v - N]).set ops_DD []).set ops_OO []) EV ++ [0]) =
        S.set EV (S EV ++ [cb.getD v 0]) := by
      rw [hz]
      ops_eq
    rw [e] at p₃
    have := (x₁.seq (x₂.seq (x₃.seq (x₄.seq ((p₁.seq (p₂.seq p₃)).iteF (i := ops_DD) (c := .zero)
      (p := .seq (.prim (.pop ops_DD)) (peekAt ops_CB ops_TT ops_OO EV (by decide) (by decide)))
      (by ops_at; simp [NTest.eval]; omega))))))
    exact this.mono (by omega)

theorem ops_seqE_ok (N : Nat) : ops_ElemOK ops_seqE N ops_seqG (23 * (N + 1) + 20) := by
  intro ca cb hca hcb q hq S hA hB hQ hN haux
  have x₁ := ops_readA_runs S N q ca hca hq hA hQ haux
  have hO : S ops_OO = [] := haux ops_OO (by decide) (by decide)
  have x₂ := ops_case3 (.prim (.pushZ EV)) (npushC EV 1) ops_seqTail S (S.set EV (S EV ++ [ops_seqG ca cb q]))
    (ca.getD q 0) (13 * (N + 1) + 9) hO
    (fun h => by
      have := nruns_pushZ EV S
      simp only [ops_seqG, h]
      exact this.mono (by omega))
    (fun h => by
      have := nruns_pushC EV S 1
      simp only [ops_seqG, h]
      exact this.mono (by omega))
    (fun v h => by
      have := ops_seqTail_runs S N v cb hcb hB hN haux
      simp only [ops_seqG, h, show 2 ≤ v + 2 by omega, if_true, Nat.add_sub_cancel]
      exact this)
  exact (x₁.seq x₂).mono (by omega)

/-! ## `alt` -/

/-- The code of `alt` at position `q`. -/
def ops_altG (ca cb : List Nat) (q : Nat) : Nat := let c := ca.getD q 0; if c = 1 then cb.getD q 0 else c

def ops_altE : NProg NK :=
  .seq ops_readA (caseTop ops_OO [.prim (.pushZ EV),
      .seq (.prim (.dup ops_QQ ops_II (by decide))) (peekAt ops_CB ops_TT ops_II EV (by decide) (by decide))]
    (.seq (.prim (.inc ops_OO)) (.seq (.prim (.inc ops_OO)) (nmv ops_OO EV (by decide)))))

/-- Push the code on top of `OO`, with `v + 2` there. -/
theorem ops_pushBack_runs (S : Lists NK) (v : Nat) (hO : S ops_OO = []) :
    NRuns (.seq (.prim (.inc ops_OO)) (.seq (.prim (.inc ops_OO)) (nmv ops_OO EV (by decide))))
      (S.set ops_OO [v]) (S.set EV (S EV ++ [v + 2])) 4 := by
  have x₁ := nruns_inc ops_OO (S.set ops_OO [v]) (l := []) (v := v) (by simp)
  rw [Lists.set_set_u] at x₁
  have x₂ := nruns_inc ops_OO (S.set ops_OO ([] ++ [v + 1])) (l := []) (v := v + 1) (by simp)
  rw [Lists.set_set_u] at x₂
  have x₃ := nruns_mv ops_OO EV (by decide) (S.set ops_OO ([] ++ [v + 1 + 1])) (l := []) (v := v + 1 + 1) (by simp)
  have e : ((S.set ops_OO ([] ++ [v + 1 + 1])).set EV ((S.set ops_OO ([] ++ [v + 1 + 1])) EV ++ [v + 1 + 1])).set
      ops_OO [] = S.set EV (S EV ++ [v + 2]) := by
    rw [Lists.set_ne _ _ (by decide)]
    ops_eq
  rw [e] at x₃
  exact x₁.seq (x₂.seq x₃)

theorem ops_altE_ok (N : Nat) : ops_ElemOK ops_altE N ops_altG (23 * (N + 1) + 20) := by
  intro ca cb hca hcb q hq S hA hB hQ hN haux
  have x₁ := ops_readA_runs S N q ca hca hq hA hQ haux
  have hO : S ops_OO = [] := haux ops_OO (by decide) (by decide)
  have hI : S ops_II = [] := haux ops_II (by decide) (by decide)
  have hT : S ops_TT = [] := haux ops_TT (by decide) (by decide)
  have x₂ := ops_case3 (.prim (.pushZ EV))
    (.seq (.prim (.dup ops_QQ ops_II (by decide))) (peekAt ops_CB ops_TT ops_II EV (by decide) (by decide)))
    (.seq (.prim (.inc ops_OO)) (.seq (.prim (.inc ops_OO)) (nmv ops_OO EV (by decide))))
    S (S.set EV (S EV ++ [ops_altG ca cb q])) (ca.getD q 0) (13 * (N + 1) + 9) hO
    (fun h => by
      have := nruns_pushZ EV S
      simp only [ops_altG, h]
      exact this.mono (by omega))
    (fun h => by
      have y₁ := nruns_dup ops_QQ ops_II (by decide) S (l := []) (v := q) hQ
      rw [hI, List.nil_append] at y₁
      have y₂ := nruns_peekAt ops_CB ops_TT ops_II EV (by decide) (by decide) (by decide) (S.set ops_II [q])
        (by ops_at) (lc := []) (k := q) (by simp) (by ops_at; rw [hB, hcb]; omega)
      have hg : ((S.set ops_II [q]) ops_CB)[q]'(by ops_at; rw [hB, hcb]; omega) = cb.getD q 0 := by
        simp only [Lists.set_ne _ _ (show ops_CB ≠ ops_II by decide), hB]
        rw [ops_getD_lt _ (by omega)]
      have hlen : ((S.set ops_II [q]) ops_CB).length = N + 1 := by ops_at; rw [hB, hcb]
      have e : ((S.set ops_II [q]).set ops_II []).set EV ((S.set ops_II [q]) EV ++
          [((S.set ops_II [q]) ops_CB)[q]'(by ops_at; rw [hB, hcb]; omega)]) =
          S.set EV (S EV ++ [ops_altG ca cb q]) := by
        simp only [ops_altG, h, if_true]
        rw [hg]
        ops_eq
      rw [e, hlen] at y₂
      exact (y₁.seq y₂).mono (by omega))
    (fun v h => by
      have := ops_pushBack_runs S v hO
      simp only [ops_altG, h, show v + 2 ≠ 1 by omega, if_false]
      exact this.mono (by omega))
  exact (x₁.seq x₂).mono (by omega)

/-! ## `!` -/

/-- The code of `!` at position `q`. -/
def ops_notG (ca _cb : List Nat) (q : Nat) : Nat :=
  let c := ca.getD q 0; if 2 ≤ c then 1 else if c = 1 then q + 2 else 0

def ops_notE : NProg NK :=
  .seq ops_readA (caseTop ops_OO [.prim (.pushZ EV),
      .seq (.prim (.dup ops_QQ EV (by decide))) (.seq (.prim (.inc EV)) (.prim (.inc EV)))]
    (.seq (.prim (.pop ops_OO)) (npushC EV 1)))

theorem ops_notE_ok (N : Nat) : ops_ElemOK ops_notE N ops_notG (23 * (N + 1) + 20) := by
  intro ca cb hca hcb q hq S hA hB hQ hN haux
  have x₁ := ops_readA_runs S N q ca hca hq hA hQ haux
  have hO : S ops_OO = [] := haux ops_OO (by decide) (by decide)
  have x₂ := ops_case3 (.prim (.pushZ EV))
    (.seq (.prim (.dup ops_QQ EV (by decide))) (.seq (.prim (.inc EV)) (.prim (.inc EV))))
    (.seq (.prim (.pop ops_OO)) (npushC EV 1))
    S (S.set EV (S EV ++ [ops_notG ca cb q])) (ca.getD q 0) (13 * (N + 1) + 9) hO
    (fun h => by
      have := nruns_pushZ EV S
      simp only [ops_notG, h]
      exact this.mono (by omega))
    (fun h => by
      have y₁ := nruns_dup ops_QQ EV (by decide) S (l := []) (v := q) hQ
      have y₂ := nruns_inc EV (S.set EV (S EV ++ [q])) (l := S EV) (v := q) (by simp)
      rw [Lists.set_set_u] at y₂
      have y₃ := nruns_inc EV (S.set EV (S EV ++ [q + 1])) (l := S EV) (v := q + 1) (by simp)
      rw [Lists.set_set_u] at y₃
      simp only [ops_notG, h]
      exact (y₁.seq (y₂.seq y₃)).mono (by omega))
    (fun v h => by
      have y₁ := nruns_pop ops_OO (S.set ops_OO [v]) (l := []) (v := v) (by simp)
      have hS : S.set ops_OO [] = S := by rw [← hO]; exact Lists.set_get_self S _
      rw [Lists.set_set_u, hS] at y₁
      have y₂ := nruns_pushC EV S 1
      simp only [ops_notG, h, show 2 ≤ v + 2 by omega, if_true]
      exact (y₁.seq y₂).mono (by omega))
  exact (x₁.seq x₂).mono (by omega)

/-! ## `star` -/

/-- The code of `star` at position `q`. -/
def ops_starG (ca _cb : List Nat) (q : Nat) : Nat := starAt ca q

/-- One step of following `a*` down the chunk: the current position, and the code once found. -/
def ops_starStep (ca : List Nat) : Nat × Option Nat → Nat × Option Nat
  | (cur, some r) => (cur, some r)
  | (cur, none) =>
    let c := ca.getD cur 0
    if 2 ≤ c then (if c - 2 < cur then (c - 2, none) else (cur, some 0))
    else if c = 1 then (cur, some (cur + 2)) else (cur, some 0)

/-- `k` search steps. -/
def ops_starIter (ca : List Nat) : Nat → Nat × Option Nat → Nat × Option Nat
  | 0, σ => σ
  | k + 1, σ => ops_starIter ca k (ops_starStep ca σ)

theorem ops_starIter_succ (ca : List Nat) : ∀ (k : Nat) (σ : Nat × Option Nat),
    ops_starIter ca (k + 1) σ = ops_starStep ca (ops_starIter ca k σ)
  | 0, _ => rfl
  | k + 1, σ => by
    rw [ops_starIter, ops_starIter_succ ca k]; rfl

theorem ops_starStep_found (ca : List Nat) (cur r : Nat) : ∀ k, ops_starIter ca k (cur, some r) = (cur, some r)
  | 0 => rfl
  | k + 1 => by rw [ops_starIter]; exact ops_starStep_found ca cur r k

theorem ops_starStep_le (ca : List Nat) : ∀ (k : Nat) (σ : Nat × Option Nat), (ops_starIter ca k σ).1 ≤ σ.1
  | 0, _ => Nat.le_refl _
  | k + 1, (cur, r) => by
    rw [ops_starIter]
    refine Nat.le_trans (ops_starStep_le ca k _) ?_
    cases r with
    | some r => exact Nat.le_refl _
    | none =>
      simp only [ops_starStep]
      split
      · split
        · simp only; omega
        · exact Nat.le_refl _
      · split <;> exact Nat.le_refl _

/-- Within `k > q` steps from `q`, the code of `a*` at `q` is found. -/
theorem ops_starStep_iter (ca : List Nat) (q : Nat) : ∀ k, q < k →
    (ops_starIter ca k (q, none)).2 = some (starAt ca q) := by
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [ops_starIter, starAt]
    simp only [ops_starStep]
    split
    · split
      · rename_i h₁ h₂
        rw [ih _ h₂ k (by omega)]
      · simp [ops_starStep_found]
    · split <;> simp [ops_starStep_found]

/-- The found flag: empty while searching, `[0]` once found. -/
def ops_flag : Option Nat → List Nat
  | none => []
  | some _ => [0]

/-- With `v = c - 2` on `OO`: go down to `v` if `v < cur`, else the code is `0`. -/
def ops_starTail : NProg NK :=
  .seq (.prim (.dup ops_OO ops_DD (by decide))) (.seq (.prim (.inc ops_DD))
    (.seq (.prim (.dup ops_PP ops_WW (by decide))) (.seq (ops_subLoop ops_WW ops_DD) (.seq (.prim (.pop ops_WW))
      (.ite ops_DD .zero (.seq (.prim (.pop ops_DD)) (.seq (.prim (.pop ops_PP)) (nmv ops_OO ops_PP (by decide))))
        (.seq (.prim (.pop ops_DD)) (.seq (.prim (.pop ops_OO)) (.seq (.prim (.pushZ EV)) (.prim (.pushZ ops_GG))))))))))

/-- One search step, with the current position on `PP`. -/
def ops_starStepP : NProg NK :=
  .seq (ops_read ops_PP (by decide)) (caseTop ops_OO
    [.seq (.prim (.pushZ EV)) (.prim (.pushZ ops_GG)),
     .seq (.prim (.dup ops_PP EV (by decide))) (.seq (.prim (.inc EV)) (.seq (.prim (.inc EV)) (.prim (.pushZ ops_GG))))]
    ops_starTail)

/-- The state of the search on the stacks. -/
def ops_starSt (S : Lists NK) (σ : Nat × Option Nat) : Lists NK :=
  ((S.set ops_PP [σ.1]).set ops_GG (ops_flag σ.2)).set EV (S EV ++ σ.2.toList)

/-- The search stops with the code `0`, on the stacks. -/
theorem ops_starEq_stop (S : Lists NK) (cur v : Nat) (hO : S ops_OO = []) (hD : S ops_DD = []) :
    let R₇ := ((((ops_starSt S (cur, none)).set ops_OO [v]).set ops_DD [v + 1 - cur]).set ops_DD []).set ops_OO []
    (R₇.set EV (R₇ EV ++ [0])).set ops_GG ((R₇.set EV (R₇ EV ++ [0])) ops_GG ++ [0]) = ops_starSt S (cur, some 0) := by
  intro R₇
  simp only [R₇, ops_starSt, ops_flag, Option.toList]
  ops_eq

theorem ops_starStepP_runs (S : Lists NK) (N cur : Nat) (ca : List Nat) (hca : ca.length = N + 1) (hcur : cur ≤ N)
    (hA : S ops_CA = ca) (haux : ops_AuxEmpty S) :
    NRuns ops_starStepP (ops_starSt S (cur, none)) (ops_starSt S (ops_starStep ca (cur, none)))
      (13 * (N + 1) + 20) := by
  have hO : S ops_OO = [] := haux ops_OO (by decide) (by decide)
  have hD : S ops_DD = [] := haux ops_DD (by decide) (by decide)
  have hW : S ops_WW = [] := haux ops_WW (by decide) (by decide)
  have hP : S ops_PP = [] := haux ops_PP (by decide) (by decide)
  have hG : S ops_GG = [] := haux ops_GG (by decide) (by decide)
  let R := ops_starSt S (cur, none)
  have x₁ := ops_read_runs ops_PP (by decide) R N cur ca hca hcur
    (by simp only [R, ops_starSt]; ops_at) (by simp only [R, ops_starSt]; ops_at)
    (by simp only [R, ops_starSt]; ops_at; exact haux _ (by decide) (by decide))
    (by simp only [R, ops_starSt]; ops_at) (by simp only [R, ops_starSt]; ops_at; exact haux _ (by decide) (by decide))
  have hRO : R ops_OO = [] := by simp only [R, ops_starSt]; ops_at
  have x₂ := ops_case3 (.seq (.prim (.pushZ EV)) (.prim (.pushZ ops_GG)))
    (.seq (.prim (.dup ops_PP EV (by decide))) (.seq (.prim (.inc EV)) (.seq (.prim (.inc EV)) (.prim (.pushZ ops_GG)))))
    ops_starTail R (ops_starSt S (ops_starStep ca (cur, none))) (ca.getD cur 0) (3 * (N + 1) + 9) hRO
    (fun h => by
      have y₁ := nruns_pushZ EV R
      have y₂ := nruns_pushZ ops_GG (R.set EV (R EV ++ [0]))
      have e : (R.set EV (R EV ++ [0])).set ops_GG ((R.set EV (R EV ++ [0])) ops_GG ++ [0]) =
          ops_starSt S (ops_starStep ca (cur, none)) := by
        simp only [ops_starStep, h, R, ops_starSt, ops_flag, Option.toList, List.append_nil]
        simp (config := { decide := true })
        ops_eq
      rw [e] at y₂
      exact (y₁.seq y₂).mono (by omega))
    (fun h => by
      have y₁ := nruns_dup ops_PP EV (by decide) R (l := []) (v := cur) (by simp only [R, ops_starSt]; ops_at)
      have y₂ := nruns_inc EV (R.set EV (R EV ++ [cur])) (l := R EV) (v := cur) (by simp)
      rw [Lists.set_set_u] at y₂
      have y₃ := nruns_inc EV (R.set EV (R EV ++ [cur + 1])) (l := R EV) (v := cur + 1) (by simp)
      rw [Lists.set_set_u] at y₃
      have y₄ := nruns_pushZ ops_GG (R.set EV (R EV ++ [cur + 1 + 1]))
      have e : (R.set EV (R EV ++ [cur + 1 + 1])).set ops_GG ((R.set EV (R EV ++ [cur + 1 + 1])) ops_GG ++ [0]) =
          ops_starSt S (ops_starStep ca (cur, none)) := by
        simp only [ops_starStep, h, R, ops_starSt, ops_flag, Option.toList, List.append_nil]
        simp (config := { decide := true })
        ops_eq
      rw [e] at y₄
      exact (y₁.seq (y₂.seq (y₃.seq y₄))).mono (by omega))
    (fun v h => by
      let R₀ := R.set ops_OO [v]
      have y₁ := nruns_dup ops_OO ops_DD (by decide) R₀ (l := []) (v := v) (by simp only [R₀]; ops_at)
      have y₂ := nruns_inc ops_DD (R₀.set ops_DD (R₀ ops_DD ++ [v])) (l := []) (v := v)
        (by simp only [R₀, R, ops_starSt]; ops_at)
      rw [Lists.set_set_u] at y₂
      have y₃ := nruns_dup ops_PP ops_WW (by decide) (R₀.set ops_DD ([] ++ [v + 1])) (l := []) (v := cur)
        (by simp only [R₀, R, ops_starSt]; ops_at)
      have y₄ := ops_subLoop_runs ops_WW ops_DD (by decide)
        ((R₀.set ops_DD ([] ++ [v + 1])).set ops_WW ((R₀.set ops_DD ([] ++ [v + 1])) ops_WW ++ [cur]))
        (lu := []) (ld := []) (a := cur) (b := v + 1)
        (by simp only [R₀, R, ops_starSt]; ops_at) (by simp only [R₀, R, ops_starSt]; ops_at)
      let R₄ := (((R₀.set ops_DD ([] ++ [v + 1])).set ops_WW ((R₀.set ops_DD ([] ++ [v + 1])) ops_WW ++ [cur])).set
        ops_WW ([] ++ [0])).set ops_DD ([] ++ [v + 1 - cur])
      have y₅ := nruns_pop ops_WW R₄ (l := []) (v := 0) (by simp only [R₄]; ops_at)
      have hR₅ : R₄.set ops_WW [] = R₀.set ops_DD [v + 1 - cur] := by
        simp only [R₄, R₀, R, ops_starSt]
        ops_eq
      rw [hR₅] at y₅
      by_cases hv : v < cur
      · have p₁ := nruns_pop ops_DD (R₀.set ops_DD [v + 1 - cur]) (l := []) (v := 0)
          (by rw [show v + 1 - cur = 0 by omega]; simp)
        have p₂ := nruns_pop ops_PP ((R₀.set ops_DD [v + 1 - cur]).set ops_DD []) (l := []) (v := cur)
          (by simp only [R₀, R, ops_starSt]; ops_at)
        have p₃ := nruns_mv ops_OO ops_PP (by decide) (((R₀.set ops_DD [v + 1 - cur]).set ops_DD []).set ops_PP [])
          (l := []) (v := v) (by simp only [R₀]; ops_at)
        have e : ((((R₀.set ops_DD [v + 1 - cur]).set ops_DD []).set ops_PP []).set ops_PP
            ((((R₀.set ops_DD [v + 1 - cur]).set ops_DD []).set ops_PP []) ops_PP ++ [v])).set ops_OO [] =
            ops_starSt S (ops_starStep ca (cur, none)) := by
          have hs : ops_starStep ca (cur, none) = (v, none) := by
            simp only [ops_starStep, h]; rw [if_pos (by omega), Nat.add_sub_cancel, if_pos hv]
          rw [hs]
          simp only [R₀, R, ops_starSt, ops_flag, Option.toList, List.append_nil]
          ops_eq
        rw [e] at p₃
        have := (y₁.seq (y₂.seq (y₃.seq (y₄.seq (y₅.seq ((p₁.seq (p₂.seq p₃)).iteT (i := ops_DD) (c := .zero)
          (q := .seq (.prim (.pop ops_DD)) (.seq (.prim (.pop ops_OO)) (.seq (.prim (.pushZ EV))
            (.prim (.pushZ ops_GG)))))
          (by ops_at; rw [show v + 1 - cur = 0 by omega]; rfl)))))))
        exact this.mono (by omega)
      · have p₁ := nruns_pop ops_DD (R₀.set ops_DD [v + 1 - cur]) (l := []) (v := v + 1 - cur) (by simp)
        have p₂ := nruns_pop ops_OO ((R₀.set ops_DD [v + 1 - cur]).set ops_DD []) (l := []) (v := v)
          (by simp only [R₀]; ops_at)
        let R₇ := ((R₀.set ops_DD [v + 1 - cur]).set ops_DD []).set ops_OO []
        have p₃ := nruns_pushZ EV R₇
        have p₄ := nruns_pushZ ops_GG (R₇.set EV (R₇ EV ++ [0]))
        have e : (R₇.set EV (R₇ EV ++ [0])).set ops_GG ((R₇.set EV (R₇ EV ++ [0])) ops_GG ++ [0]) =
            ops_starSt S (ops_starStep ca (cur, none)) := by
          have hs : ops_starStep ca (cur, none) = (cur, some 0) := by
            simp only [ops_starStep, h]; rw [if_pos (by omega), Nat.add_sub_cancel, if_neg hv]
          rw [hs]
          exact ops_starEq_stop S cur v hO hD
        rw [e] at p₄
        have := (y₁.seq (y₂.seq (y₃.seq (y₄.seq (y₅.seq ((p₁.seq (p₂.seq (p₃.seq p₄))).iteF (i := ops_DD)
          (c := .zero) (p := .seq (.prim (.pop ops_DD)) (.seq (.prim (.pop ops_PP)) (nmv ops_OO ops_PP (by decide))))
          (by rw [Lists.set_same]; simp [NTest.eval]; omega)))))))
        exact this.mono (by omega))
  exact (x₁.seq x₂).mono (by omega)

/-- Follow `a*` from the position on `QQ` for `N + 1` steps (enough: the position goes down), then push the code. -/
def ops_starE : NProg NK :=
  .seq (.prim (.dup ops_QQ ops_PP (by decide))) (.seq (.prim (.dup NX ops_UU (by decide))) (.seq (.prim (.inc ops_UU))
    (.seq (.loop ops_UU .pos (.seq (.prim (.dec ops_UU)) (.ite ops_GG .nonempty (nskip ops_DD) ops_starStepP)))
      (.seq (.prim (.pop ops_UU)) (.seq (.prim (.pop ops_GG)) (.prim (.pop ops_PP)))))))

theorem ops_starSt_GG (S : Lists NK) (σ : Nat × Option Nat) : ops_starSt S σ ops_GG = ops_flag σ.2 := by
  simp only [ops_starSt]; ops_at

theorem ops_starStepP_untouched : ops_starStepP.touches ops_UU = false := by decide

theorem ops_starE_start (S : Lists NK) (q N : Nat) (hP : S ops_PP = []) (hG : S ops_GG = []) :
    (((S.set ops_PP (S ops_PP ++ [q])).set ops_UU ((S.set ops_PP (S ops_PP ++ [q])) ops_UU ++ [N])).set ops_UU
      ([] ++ [N + 1])) = (ops_starSt S (q, none)).set ops_UU [N + 1 - 0] := by
  simp only [ops_starSt, ops_flag, Option.toList, List.append_nil, Nat.sub_zero, List.nil_append]
  ops_eq

theorem ops_starE_finish (S : Lists NK) (cur r : Nat) (hP : S ops_PP = []) (hU : S ops_UU = []) (hG : S ops_GG = []) :
    ((((ops_starSt S (cur, some r)).set ops_UU []).set ops_GG []).set ops_PP []) = S.set EV (S EV ++ [r]) := by
  simp only [ops_starSt, ops_flag, Option.toList]
  ops_eq

theorem ops_starE_ok (N : Nat) :
    ops_ElemOK ops_starE N ops_starG ((N + 1) * (13 * (N + 1) + 23) + 7) := by
  intro ca cb hca hcb q hq S hA hB hQ hN haux
  have hP : S ops_PP = [] := haux ops_PP (by decide) (by decide)
  have hU : S ops_UU = [] := haux ops_UU (by decide) (by decide)
  have hG : S ops_GG = [] := haux ops_GG (by decide) (by decide)
  have x₁ := nruns_dup ops_QQ ops_PP (by decide) S (l := []) (v := q) hQ
  have x₂ := nruns_dup NX ops_UU (by decide) (S.set ops_PP (S ops_PP ++ [q])) (l := []) (v := N) (by ops_at)
  have x₃ := nruns_inc ops_UU ((S.set ops_PP (S ops_PP ++ [q])).set ops_UU
    ((S.set ops_PP (S ops_PP ++ [q])) ops_UU ++ [N])) (l := []) (v := N) (by ops_at)
  rw [ops_starE_start S q N hP hG] at x₃
  let F : Nat → Lists NK := fun m => (ops_starSt S (ops_starIter ca m (q, none))).set ops_UU [N + 1 - m]
  have hFu : ∀ m, F m ops_UU = [] ++ [N + 1 - m] := fun m => by simp only [F, Lists.set_same]; rfl
  have hloop := nruns_family_const (i := ops_UU) (c := .pos)
    (p := .seq (.prim (.dec ops_UU)) (.ite ops_GG .nonempty (nskip ops_DD) ops_starStepP)) F (N + 1)
    (13 * (N + 1) + 22)
    (fun m hm => by rw [hFu, show N + 1 - m = (N + 1 - m - 1) + 1 by omega]; simp [NTest.eval])
    (by rw [hFu, Nat.sub_self]; simp [NTest.eval])
    (fun m hm => by
      have d₁ := nruns_dec ops_UU (F m) (hFu m)
      have hS₁ : (F m).set ops_UU ([] ++ [N + 1 - m - 1]) =
          (ops_starSt S (ops_starIter ca m (q, none))).set ops_UU [N + 1 - (m + 1)] := by
        simp only [F, Lists.set_set_u, List.nil_append, show N + 1 - m - 1 = N + 1 - (m + 1) by omega]
      rw [hS₁] at d₁
      have hF₁ : F (m + 1) = (ops_starSt S (ops_starStep ca (ops_starIter ca m (q, none)))).set ops_UU
          [N + 1 - (m + 1)] := by simp only [F, ops_starIter_succ]
      rw [hF₁]
      rcases hσ : ops_starIter ca m (q, none) with ⟨cur, _ | r⟩ <;> rw [hσ] at d₁
      · have hcur : cur ≤ N := by
          have := ops_starStep_le ca m (q, none); rw [hσ] at this; simp at this; omega
        have d₂ := (ops_starStepP_runs S N cur ca hca hcur hA haux).frame ops_starStepP_untouched
          [N + 1 - (m + 1)]
        exact (d₁.seq (d₂.iteF (by rw [Lists.set_ne _ _ (by decide), ops_starSt_GG]; rfl))).mono (by omega)
      · have d₂ := nruns_skip ops_DD ((ops_starSt S (cur, some r)).set ops_UU [N + 1 - (m + 1)])
        exact (d₁.seq (d₂.iteT (by rw [Lists.set_ne _ _ (by decide), ops_starSt_GG]; rfl))).mono (by omega))
  have hend := ops_starStep_iter ca q (N + 1) (by omega)
  rcases hσ : ops_starIter ca (N + 1) (q, none) with ⟨cur, r⟩
  rw [hσ] at hend
  simp only at hend
  subst hend
  have hFN : F (N + 1) = (ops_starSt S (cur, some (starAt ca q))).set ops_UU ([] ++ [0]) := by
    simp only [F, hσ, Nat.sub_self, List.nil_append]
  rw [hFN] at hloop
  have p₁ := nruns_pop ops_UU ((ops_starSt S (cur, some (starAt ca q))).set ops_UU ([] ++ [0])) (l := [])
    (v := 0) (by simp)
  rw [Lists.set_set_u] at p₁
  have p₂ := nruns_pop ops_GG ((ops_starSt S (cur, some (starAt ca q))).set ops_UU []) (l := []) (v := 0)
    (by simp only [ops_starSt, ops_flag]; ops_at)
  have p₃ := nruns_pop ops_PP (((ops_starSt S (cur, some (starAt ca q))).set ops_UU []).set ops_GG []) (l := [])
    (v := cur) (by simp only [ops_starSt, ops_flag]; ops_at)
  rw [ops_starE_finish S cur (starAt ca q) hP hU hG] at p₃
  have hc : (N + 1) * (13 * (N + 1) + 22 + 1) = (N + 1) * (13 * (N + 1) + 23) := rfl
  exact (x₁.seq (x₂.seq (x₃.seq (hloop.seq (p₁.seq (p₂.seq p₃)))))).mono (by omega)

/-! ## The whole operator -/

theorem ops_ElemOK.mono {E : NProg NK} {N : Nat} {g : List Nat → List Nat → Nat → Nat} {T T' : Nat}
    (h : ops_ElemOK E N g T) (hT : T ≤ T') : ops_ElemOK E N g T' :=
  fun ca cb hca hcb q hq S hA hB hQ hN haux => (h ca cb hca hcb q hq S hA hB hQ hN haux).mono hT

/-- The steps of `ops_core`. -/
def ops_coreCost (tl ctx la lb n N TE : Nat) : Nat :=
  6 * tl + 4 * ctx + 6 * la + 6 * lb + 30 + n * ((N + 1) * (TE + 4) + 14 * (N + 1) + 18)

/-- With the two top vectors `va`, `vb` of lengths on `EVL`: read the number of chunks (entry `ctx` of `ENVT`), move
the operands away, push the chunks of the result, clear. -/
def ops_core (E : NProg NK) : NProg NK :=
  .seq (.prim (.dup IT ops_II (by decide))) (.seq (peekAt ENVT ops_TT ops_II ops_OC (by decide) (by decide))
    (.seq (moveN EVL EV ops_RB (by decide)) (.seq (moveN EVL EV ops_RA (by decide)) (.seq (.prim (.pushZ EVL))
      (.seq (ops_outer E) (.seq (.prim (.pop ops_OC)) (.seq (nclr ops_RA) (nclr ops_RB))))))))

/-- Scratch stacks `18`–`33` empty. -/
def ops_Scr (S : Lists NK) : Prop := ∀ i : Fin NK, 18 ≤ i.val → i.val ≤ 33 → S i = []

theorem ops_core_final (S : Lists NK) (n N : Nat) (va vb e lv out dA dB : List Nat) (hOC : S ops_OC = [])
    (hRA : S ops_RA = []) (hRB : S ops_RB = []) :
    (((((((((((((S.set ops_OC [n]).set ops_RA va.reverse).set ops_RB vb.reverse).set EV e).set EVL (lv ++ [0])).set
      ops_OC [0]).set ops_RA dA).set ops_RB dB).set EV (e ++ out)).set EVL (lv ++ [0 + n * (N + 1)])).set ops_OC
      []).set ops_RA []).set ops_RB []) = (S.set EV (e ++ out)).set EVL (lv ++ [n * (N + 1)]) := by
  funext x
  simp only [Lists.set, Nat.zero_add]
  by_cases h₁ : x = ops_RB
  · subst h₁; simp (config := { decide := true }) [hRB]
  by_cases h₂ : x = ops_RA
  · subst h₂; simp (config := { decide := true }) [hRA]
  by_cases h₃ : x = ops_OC
  · subst h₃; simp (config := { decide := true }) [hOC]
  by_cases h₄ : x = EVL
  · subst h₄; simp (config := { decide := true })
  by_cases h₅ : x = EV
  · subst h₅; simp (config := { decide := true })
  simp [h₁, h₂, h₃, h₄, h₅]

theorem ops_core_runs {E : NProg NK} {N : Nat} {g : List Nat → List Nat → Nat → Nat} {TE : Nat}
    (hE : ops_ElemOK E N g TE) (S : Lists NK) (hs : ops_Scr S) (hN : S NX = [N]) {li tab : List Nat} {ctx : Nat}
    (hI : S IT = li ++ [ctx]) (hT : S ENVT = tab) (hctx : ctx < tab.length) {e lv va vb : List Nat}
    (hv : S EV = e ++ va ++ vb) (hl : S EVL = lv ++ [va.length, vb.length]) :
    NRuns (ops_core E) S
      ((S.set EV (e ++ ((List.range tab[ctx]).map (ops_chunkOut N g va vb)).flatten)).set EVL
        (lv ++ [tab[ctx] * (N + 1)]))
      (ops_coreCost tab.length ctx va.length vb.length tab[ctx] N TE) := by
  have hII : S ops_II = [] := hs ops_II (by decide) (by decide)
  have hTT : S ops_TT = [] := hs ops_TT (by decide) (by decide)
  have hOC : S ops_OC = [] := hs ops_OC (by decide) (by decide)
  have hRA : S ops_RA = [] := hs ops_RA (by decide) (by decide)
  have hRB : S ops_RB = [] := hs ops_RB (by decide) (by decide)
  have hCA : S ops_CA = [] := hs ops_CA (by decide) (by decide)
  have hCB : S ops_CB = [] := hs ops_CB (by decide) (by decide)
  have hQQ : S ops_QQ = [] := hs ops_QQ (by decide) (by decide)
  have hLC : S ops_LC = [] := hs ops_LC (by decide) (by decide)
  have haux : ops_AuxEmpty S := fun i h₁ h₂ => hs i (by omega) h₂
  obtain ⟨n, hn⟩ : ∃ n, tab[ctx] = n := ⟨_, rfl⟩
  simp only [hn]
  -- the number of chunks
  have y₁ := nruns_dup IT ops_II (by decide) S hI
  rw [hII, List.nil_append] at y₁
  have y₂ := nruns_peekAt ENVT ops_TT ops_II ops_OC (by decide) (by decide) (by decide) (S.set ops_II [ctx])
    (by ops_at) (lc := []) (k := ctx) (by simp) (by ops_at; rw [hT]; exact hctx)
  have e₂ : ((S.set ops_II [ctx]).set ops_II []).set ops_OC ((S.set ops_II [ctx]) ops_OC ++
      [((S.set ops_II [ctx]) ENVT)[ctx]'(by ops_at; rw [hT]; exact hctx)]) = S.set ops_OC [n] := by
    have hg : ((S.set ops_II [ctx]) ENVT)[ctx]'(by ops_at; rw [hT]; exact hctx) = n := by
      simp only [Lists.set_ne _ _ (show ENVT ≠ ops_II by decide), hT, hn]
    rw [hg]
    ops_eq'
  rw [e₂] at y₂
  have hlen : ((S.set ops_II [ctx]) ENVT).length = tab.length := by ops_at; rw [hT]
  rw [hlen] at y₂
  -- the operands
  let S₂ := S.set ops_OC [n]
  have y₃ := nruns_moveN EVL EV ops_RB (by decide) (by decide) (by decide) S₂ (lc := lv ++ [va.length])
    (n := vb.length) (by simp only [S₂]; ops_at; all_goals simp [hl]) (l := e ++ va) (seg := vb)
    (by simp only [S₂]; ops_at; all_goals simp [hv]) rfl
  let S₃ := ((S₂.set EVL (lv ++ [va.length])).set EV (e ++ va)).set ops_RB (S₂ ops_RB ++ vb.reverse)
  have y₄ := nruns_moveN EVL EV ops_RA (by decide) (by decide) (by decide) S₃ (lc := lv) (n := va.length)
    (by simp only [S₃, S₂]; ops_at) (l := e) (seg := va) (by simp only [S₃, S₂]; ops_at) rfl
  let S₄ := ((S₃.set EVL lv).set EV e).set ops_RA (S₃ ops_RA ++ va.reverse)
  have y₅ := nruns_pushZ EVL S₄
  have e₅ : S₄.set EVL (S₄ EVL ++ [0]) =
      ((((S.set ops_OC [n]).set ops_RA va.reverse).set ops_RB vb.reverse).set EV e).set EVL (lv ++ [0]) := by
    simp only [S₄, S₃, S₂]
    ops_eq'
  rw [e₅] at y₅
  -- the chunks
  let S₅ := ((((S.set ops_OC [n]).set ops_RA va.reverse).set ops_RB vb.reverse).set EV e).set EVL (lv ++ [0])
  have haux₅ : ops_AuxEmpty S₅ := by
    simp only [S₅]
    repeat (apply ops_aux_set _ (by decide))
    exact haux
  have y₆ := ops_outer_runs hE S₅ n va vb (by simp only [S₅]; ops_at) (by simp only [S₅]; ops_at)
    (by simp only [S₅]; ops_at) (by simp only [S₅]; ops_at) (by simp only [S₅]; ops_at)
    (by simp only [S₅]; ops_at) (by simp only [S₅]; ops_at) (by simp only [S₅]; ops_at) haux₅ (lv := lv) (k := 0)
    (by simp only [S₅]; ops_at)
  let out := ((List.range n).map (ops_chunkOut N g va vb)).flatten
  have hEV : S₅ EV = e := by simp only [S₅]; ops_at
  rw [hEV] at y₆
  let S₆ := ((((S₅.set ops_OC [0]).set ops_RA (va.drop (n * (N + 1))).reverse).set ops_RB
    (vb.drop (n * (N + 1))).reverse).set EV (e ++ out)).set EVL (lv ++ [0 + n * (N + 1)])
  have y₇ := nruns_pop ops_OC S₆ (l := []) (v := 0) (by simp only [S₆]; ops_at)
  have y₈ := nruns_clr ops_RA (S₆.set ops_OC [])
  have y₉ := nruns_clr ops_RB ((S₆.set ops_OC []).set ops_RA [])
  have hla : ((S₆.set ops_OC []) ops_RA).length ≤ va.length := by
    simp only [S₆]; ops_at; all_goals simp
  have hlb : (((S₆.set ops_OC []).set ops_RA []) ops_RB).length ≤ vb.length := by
    simp only [S₆]; ops_at; all_goals simp
  have e₉ : ((S₆.set ops_OC []).set ops_RA []).set ops_RB [] =
      (S.set EV (e ++ out)).set EVL (lv ++ [n * (N + 1)]) := by
    rw [Nat.zero_add] at *
    exact ops_core_final S n N va vb e lv out _ _ hOC hRA hRB
  rw [e₉] at y₉
  refine (y₁.seq (y₂.seq (y₃.seq (y₄.seq (y₅.seq (y₆.seq (y₇.seq (y₈.seq y₉)))))))).mono ?_
  simp only [ops_coreCost]
  omega

/-! ## The chunks of the result, as in `stepT` -/

theorem ops_zip_chunks (f : List Nat → List Nat → List Nat) (k n : Nat) (a b : List Nat) :
    List.zipWith f (chunksN k n a) (chunksN k n b) =
      (List.range n).map (fun i => f ((a.drop (i * k)).take k) ((b.drop (i * k)).take k)) := by
  rw [ops_chunksN, ops_chunksN, List.zipWith_map, List.zipWith_self]

theorem ops_length_out (N : Nat) (g : List Nat → List Nat → Nat → Nat) (va vb : List Nat) :
    ∀ n, (((List.range n).map (ops_chunkOut N g va vb)).flatten).length = n * (N + 1)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append, ops_length_out N g va vb n,
      Nat.succ_mul]
    simp [ops_chunkOut]

theorem ops_seq_out (x : List Char) (n : Nat) (va vb : List Nat) :
    (List.zipWith (seqCodes x) (chunksN (x.length + 1) n va) (chunksN (x.length + 1) n vb)).flatten =
      ((List.range n).map (ops_chunkOut x.length ops_seqG va vb)).flatten := by
  rw [ops_zip_chunks]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [seqCodes_eq]
  simp only [seqC, ops_chunkOut]
  apply List.map_congr_left
  intro q _
  simp only [ops_seqG, ops_getD_pad]

theorem ops_alt_out (x : List Char) (n : Nat) (va vb : List Nat) :
    (List.zipWith (altCodes x) (chunksN (x.length + 1) n va) (chunksN (x.length + 1) n vb)).flatten =
      ((List.range n).map (ops_chunkOut x.length ops_altG va vb)).flatten := by
  rw [ops_zip_chunks]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [altCodes_eq]
  simp only [altC, ops_chunkOut]
  apply List.map_congr_left
  intro q _
  simp only [ops_altG, ops_getD_pad]

theorem ops_not_out (x : List Char) (n : Nat) (va : List Nat) :
    ((chunksN (x.length + 1) n va).map (notCodes x)).flatten =
      ((List.range n).map (ops_chunkOut x.length ops_notG va [])).flatten := by
  rw [ops_chunksN, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  rw [notCodes_eq]
  simp only [notC, ops_chunkOut]
  apply List.map_congr_left
  intro q _
  simp only [ops_notG, ops_getD_pad]

theorem ops_starAt_congr {a b : List Nat} (h : ∀ k, a.getD k 0 = b.getD k 0) (q : Nat) : starAt a q = starAt b q := by
  induction q using Nat.strongRecOn with
  | _ q ih =>
    rw [starAt.eq_1 a q, starAt.eq_1 b q, h q]
    split
    · split
      · rename_i _ h₂; exact ih _ h₂
      · rfl
    · rfl

theorem ops_star_out (x : List Char) (n : Nat) (va : List Nat) :
    ((chunksN (x.length + 1) n va).map (starCodes x)).flatten =
      ((List.range n).map (ops_chunkOut x.length ops_starG va [])).flatten := by
  rw [ops_chunksN, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  rw [starCodes_eq]
  simp only [starC, ops_chunkOut]
  apply List.map_congr_left
  intro q _
  exact ops_starAt_congr (fun k => (ops_getD_pad _ _ k).symm) q

/-! ## The bound on the steps -/

theorem ops_cost_le (Z N n tl ctx la lb : Nat) (hZ : 2 ≤ Z) (hN : N + 1 ≤ Z) (hn : n ≤ Z) (htl : tl ≤ Z)
    (hctx : ctx ≤ Z) (hab : la + lb ≤ Z) :
    ops_coreCost tl ctx la lb n N ((N + 1) * (13 * (N + 1) + 23) + 7) + 6 ≤ 1000 * (Z * Z * Z * Z * Z) := by
  have h₂ : Z ≤ Z * Z := Nat.le_mul_self Z
  have h₃ : Z * Z ≤ Z * Z * Z := Nat.le_mul_of_pos_right _ (by omega)
  have h₄ : Z * Z * Z ≤ Z * Z * Z * Z := Nat.le_mul_of_pos_right _ (by omega)
  have h₅ : Z * Z * Z * Z ≤ Z * Z * Z * Z * Z := Nat.le_mul_of_pos_right _ (by omega)
  have hZZ : 4 ≤ Z * Z := Nat.mul_le_mul hZ hZ
  -- the element programs
  have t₁ : (N + 1) * (13 * (N + 1) + 23) ≤ Z * (13 * Z + 23) := Nat.mul_le_mul hN (by omega)
  have t₂ : Z * (13 * Z + 23) = 13 * (Z * Z) + 23 * Z := by
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm Z 23]
  have hTE : (N + 1) * (13 * (N + 1) + 23) + 7 + 4 ≤ 47 * (Z * Z) := by omega
  -- one chunk
  have c₁ : (N + 1) * ((N + 1) * (13 * (N + 1) + 23) + 7 + 4) ≤ Z * (47 * (Z * Z)) := Nat.mul_le_mul hN hTE
  have c₂ : Z * (47 * (Z * Z)) = 47 * (Z * Z * Z) := by
    rw [Nat.mul_left_comm, Nat.mul_comm Z (Z * Z)]
  have hX : (N + 1) * ((N + 1) * (13 * (N + 1) + 23) + 7 + 4) + 14 * (N + 1) + 18 ≤ 79 * (Z * Z * Z) := by
    omega
  -- all chunks
  have o₁ := Nat.mul_le_mul hn hX
  have o₂ : Z * (79 * (Z * Z * Z)) = 79 * (Z * Z * Z * Z) := by
    rw [Nat.mul_left_comm, Nat.mul_comm Z (Z * Z * Z)]
  simp only [ops_coreCost]
  omega

/-! ## Too few vectors, and the size of the item step -/

/-- Move the top of `EVL` to `WW` and back: the state is as before. -/
theorem ops_restore (S : Lists NK) (l : List Nat) (v : Nat) (hW : S ops_WW = []) (hL : S EVL = l ++ [v]) :
    (((S.set ops_WW (S ops_WW ++ [v])).set EVL l).set EVL
      (((S.set ops_WW (S ops_WW ++ [v])).set EVL l) EVL ++ [v])).set ops_WW [] = S := by
  rw [hW]
  ops_eq'

theorem ops_getElem_le_sum : ∀ (l : List Nat) (i : Nat) (h : i < l.length), l[i] ≤ l.sum
  | [], _, h => absurd h (by simp)
  | a :: l, 0, _ => by simp
  | a :: l, i + 1, h => by
    have := ops_getElem_le_sum l i (by simpa using h)
    simp only [List.getElem_cons_succ, List.sum_cons]
    omega

theorem ops_envTable_get (j cap N : Nat) (tt ct : List (Nat × Nat)) (c : Nat)
    (h : c < (envTable j cap N tt ct).length) : (envTable j cap N tt ct)[c] = envT j cap N tt ct c := by
  simp [envTable]

theorem ops_itemCost_ge (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (vs : List (List Nat)) :
    6 ≤ itemCost j cap st Tf it vs := by
  have hZ : 1 ≤ itemZ j cap st Tf it vs := by unfold itemZ; omega
  have h : 1 ≤ itemZ j cap st Tf it vs * itemZ j cap st Tf it vs * itemZ j cap st Tf it vs *
      itemZ j cap st Tf it vs * itemZ j cap st Tf it vs :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hZ hZ) hZ) hZ) hZ
  unfold itemCost
  omega

/-- The core's steps fit in the item's bound. -/
theorem ops_core_cost_le (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (vs : List (List Nat))
    (va vb : List Nat) (hab : va.length + vb.length ≤ (evFlat vs).length) (hcur : it.ctx ≤ st.ct.length) :
    ops_coreCost (envTable j cap st.x.length st.tt st.ct).length it.ctx va.length vb.length
      (envT j cap st.x.length st.tt st.ct it.ctx) st.x.length
      ((st.x.length + 1) * (13 * (st.x.length + 1) + 23) + 7) + 6 ≤ itemCost j cap st Tf it vs := by
  have hlen : (envTable j cap st.x.length st.tt st.ct).length = st.ct.length + 1 := by simp [envTable]
  have hn : envT j cap st.x.length st.tt st.ct it.ctx ≤ (envTable j cap st.x.length st.tt st.ct).sum := by
    rw [← ops_envTable_get j cap st.x.length st.tt st.ct it.ctx (by rw [hlen]; omega)]
    exact ops_getElem_le_sum _ _ _
  unfold itemCost
  rw [hlen]
  exact ops_cost_le _ _ _ _ _ _ _ (by unfold itemZ; omega) (by unfold itemZ; omega) (by unfold itemZ; omega)
    (by unfold itemZ; omega) (by unfold itemZ; omega) (by unfold itemZ; omega)

/-! ## The programs of the operators -/

/-- A binary operator: with at least two vectors, `ops_core`; else nothing. -/
def ops_binTop (E : NProg NK) : NProg NK :=
  .ite EVL .nonempty (.seq (nmv EVL ops_WW (by decide)) (.ite EVL .nonempty
      (.seq (nmv ops_WW EVL (by decide)) (ops_core E)) (nmv ops_WW EVL (by decide))))
    (nskip ops_WW)

/-- A unary operator: with at least one vector, push an empty one and run `ops_core`; else nothing. -/
def ops_unTop (E : NProg NK) : NProg NK :=
  .ite EVL .nonempty (.seq (.prim (.pushZ EVL)) (ops_core E)) (nskip ops_WW)

theorem ops_scr_of (S : Lists NK) (h : ScratchEmpty S) : ops_Scr S := h

theorem ops_binTop_runs (E : NProg NK) (g : List Nat → List Nat → Nat → Nat) (j cap : Nat) (st : PSt)
    (Tf : List (List Nat)) (it : MItem)
    (hE : ops_ElemOK E st.x.length g ((st.x.length + 1) * (13 * (st.x.length + 1) + 23) + 7))
    (hcur : it.ctx ≤ st.ct.length)
    (h₀ : stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it [] = [])
    (h₁ : ∀ v, stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it [v] = [v])
    (h₂ : ∀ vb va rest, stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it (vb :: va :: rest) =
      ((List.range (envT j cap st.x.length st.tt st.ct it.ctx)).map (ops_chunkOut st.x.length g va vb)).flatten ::
        rest) :
    ItemRuns (ops_binTop E) j cap st Tf it := by
  intro S vs hEnv hIT hEV hEVL
  have hs := ops_scr_of S hEnv.scratch
  have hW : S ops_WW = [] := hs ops_WW (by decide) (by decide)
  have hC := ops_itemCost_ge j cap st Tf it vs
  rcases vs with _ | ⟨vb, _ | ⟨va, rest⟩⟩
  · rw [h₀]
    have e : (S.set EV (evFlat [])).set EVL (evLens []) = S := by
      rw [← hEV, ← hEVL, Lists.set_get_self, Lists.set_get_self]
    rw [e]
    exact ((nruns_skip ops_WW S).iteF (by rw [hEVL]; rfl)).mono (by omega)
  · rw [h₁]
    have e : (S.set EV (evFlat [vb])).set EVL (evLens [vb]) = S := by
      rw [← hEV, ← hEVL, Lists.set_get_self, Lists.set_get_self]
    rw [e]
    have hL : S EVL = [] ++ [vb.length] := by rw [hEVL]; rfl
    have m₁ := nruns_mv EVL ops_WW (by decide) S hL
    have m₂ := nruns_mv ops_WW EVL (by decide) ((S.set ops_WW (S ops_WW ++ [vb.length])).set EVL [])
      (l := []) (v := vb.length) (by rw [Lists.set_ne _ _ (by decide), Lists.set_same, hW])
    rw [ops_restore S [] vb.length hW hL] at m₂
    exact ((m₁.seq (m₂.iteF (i := EVL) (c := .nonempty) (p := .seq (nmv ops_WW EVL (by decide)) (ops_core E))
      (by rw [Lists.set_same]; rfl))).iteT (by rw [hEVL]; rfl)).mono (by omega)
  · rw [h₂]
    have hL : S EVL = (evLens rest ++ [va.length]) ++ [vb.length] := by rw [hEVL, evLens_cons, evLens_cons]
    have m₁ := nruns_mv EVL ops_WW (by decide) S hL
    have m₂ := nruns_mv ops_WW EVL (by decide)
      ((S.set ops_WW (S ops_WW ++ [vb.length])).set EVL (evLens rest ++ [va.length])) (l := []) (v := vb.length)
      (by rw [Lists.set_ne _ _ (by decide), Lists.set_same, hW])
    rw [ops_restore S _ vb.length hW hL] at m₂
    have hlen : (envTable j cap st.x.length st.tt st.ct).length = st.ct.length + 1 := by simp [envTable]
    have core := ops_core_runs hE S hs hEnv.nx (li := [it.tag, it.a, it.b]) (ctx := it.ctx)
      (by rw [hIT]; rfl) hEnv.envt (by rw [hlen]; omega) (e := evFlat rest) (lv := evLens rest) (va := va)
      (vb := vb) (by rw [hEV, evFlat_cons, evFlat_cons]) (by rw [hL]; simp)
    rw [ops_envTable_get] at core
    have e : (S.set EV (evFlat rest ++ ((List.range (envT j cap st.x.length st.tt st.ct it.ctx)).map
        (ops_chunkOut st.x.length g va vb)).flatten)).set EVL
        (evLens rest ++ [envT j cap st.x.length st.tt st.ct it.ctx * (st.x.length + 1)]) =
        (S.set EV (evFlat (((List.range (envT j cap st.x.length st.tt st.ct it.ctx)).map
          (ops_chunkOut st.x.length g va vb)).flatten :: rest))).set EVL
          (evLens (((List.range (envT j cap st.x.length st.tt st.ct it.ctx)).map
          (ops_chunkOut st.x.length g va vb)).flatten :: rest)) := by
      rw [evFlat_cons, evLens_cons, ops_length_out]
    rw [e] at core
    have hab : va.length + vb.length ≤ (evFlat (vb :: va :: rest)).length := by
      simp [evFlat_cons]
    have hcost := ops_core_cost_le j cap st Tf it (vb :: va :: rest) va vb hab hcur
    rw [hlen] at hcost
    exact ((m₁.seq ((m₂.seq core).iteT (by rw [Lists.set_same]; simp [NTest.eval]))).iteT
      (by rw [hEVL]; simp [NTest.eval, evLens])).mono (by rw [hlen] at *; omega)

theorem ops_unTop_runs (E : NProg NK) (g : List Nat → List Nat → Nat → Nat) (j cap : Nat) (st : PSt)
    (Tf : List (List Nat)) (it : MItem)
    (hE : ops_ElemOK E st.x.length g ((st.x.length + 1) * (13 * (st.x.length + 1) + 23) + 7))
    (hcur : it.ctx ≤ st.ct.length)
    (h₀ : stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it [] = [])
    (h₁ : ∀ va rest, stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it (va :: rest) =
      ((List.range (envT j cap st.x.length st.tt st.ct it.ctx)).map (ops_chunkOut st.x.length g va [])).flatten ::
        rest) :
    ItemRuns (ops_unTop E) j cap st Tf it := by
  intro S vs hEnv hIT hEV hEVL
  have hs := ops_scr_of S hEnv.scratch
  have hC := ops_itemCost_ge j cap st Tf it vs
  rcases vs with _ | ⟨va, rest⟩
  · rw [h₀]
    have e : (S.set EV (evFlat [])).set EVL (evLens []) = S := by
      rw [← hEV, ← hEVL, Lists.set_get_self, Lists.set_get_self]
    rw [e]
    exact ((nruns_skip ops_WW S).iteF (by rw [hEVL]; rfl)).mono (by omega)
  · rw [h₁]
    have p₁ := nruns_pushZ EVL S
    let S' := S.set EVL (S EVL ++ [0])
    have hs' : ops_Scr S' := fun i h₁ h₂ => by
      have hi : i ≠ EVL := by intro e; subst e; exact absurd h₁ (by decide)
      simp only [S']; rw [Lists.set_ne _ _ hi]; exact hs i h₁ h₂
    have hlen : (envTable j cap st.x.length st.tt st.ct).length = st.ct.length + 1 := by simp [envTable]
    have core := ops_core_runs hE S' hs' (by simp only [S']; rw [Lists.set_ne _ _ (by decide)]; exact hEnv.nx)
      (li := [it.tag, it.a, it.b]) (ctx := it.ctx) (tab := envTable j cap st.x.length st.tt st.ct)
      (by simp only [S']; rw [Lists.set_ne _ _ (by decide), hIT]; rfl)
      (by simp only [S']; rw [Lists.set_ne _ _ (by decide)]; exact hEnv.envt) (by rw [hlen]; omega)
      (e := evFlat rest) (lv := evLens rest) (va := va) (vb := [])
      (by simp only [S']; rw [Lists.set_ne _ _ (by decide), hEV, evFlat_cons, List.append_nil])
      (by simp only [S']; rw [Lists.set_same, hEVL, evLens_cons]; simp)
    rw [ops_envTable_get] at core
    have e : (S'.set EV (evFlat rest ++ ((List.range (envT j cap st.x.length st.tt st.ct it.ctx)).map
        (ops_chunkOut st.x.length g va [])).flatten)).set EVL
        (evLens rest ++ [envT j cap st.x.length st.tt st.ct it.ctx * (st.x.length + 1)]) =
        (S.set EV (evFlat (((List.range (envT j cap st.x.length st.tt st.ct it.ctx)).map
          (ops_chunkOut st.x.length g va [])).flatten :: rest))).set EVL
          (evLens (((List.range (envT j cap st.x.length st.tt st.ct it.ctx)).map
          (ops_chunkOut st.x.length g va [])).flatten :: rest)) := by
      rw [evFlat_cons, evLens_cons, ops_length_out]
      simp only [S']
      rw [Lists.set_comm (show EVL ≠ EV by decide), Lists.set_set_u]
    rw [e] at core
    have hab : va.length + ([] : List Nat).length ≤ (evFlat (va :: rest)).length := by
      simp [evFlat_cons]
    have hcost := ops_core_cost_le j cap st Tf it (va :: rest) va [] hab hcur
    rw [hlen] at hcost
    exact ((p₁.seq core).iteT (by rw [hEVL, evLens_cons]; simp [NTest.eval])).mono (by rw [hlen] at *; omega)

/-! ## The item programs -/

theorem ops_TE_le (N : Nat) : 23 * (N + 1) + 20 ≤ (N + 1) * (13 * (N + 1) + 23) + 7 := by
  have : (N + 1) * 23 ≤ (N + 1) * (13 * (N + 1) + 23) := Nat.mul_le_mul_left _ (by omega)
  have h : (N + 1) * 13 ≤ (N + 1) * (13 * (N + 1) + 23) - (N + 1) * 23 := by
    rw [← Nat.mul_sub]; exact Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_comm] at this h
  omega

/-- `seq` (`5`). -/
def itemSeqP : NProg NK := ops_binTop ops_seqE
/-- `alt` (`6`). -/
def itemAltP : NProg NK := ops_binTop ops_altE
/-- `star` (`7`). -/
def itemStarP : NProg NK := ops_unTop ops_starE
/-- `!` (`8`). -/
def itemNotP : NProg NK := ops_unTop ops_notE
/-- `λ` (`11`): the stack stays as it is. -/
def itemLamP : NProg NK := nskip ops_WW

theorem itemSeqP_runs (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (htag : it.tag = 5)
    (_hc : CTWF st.tt st.ct) (hcur : it.ctx ≤ st.ct.length) : ItemRuns itemSeqP j cap st Tf it :=
  ops_binTop_runs ops_seqE ops_seqG j cap st Tf it ((ops_seqE_ok _).mono (ops_TE_le _)) hcur
    (by simp [stepT, htag, opOf]) (fun v => by simp [stepT, htag, opOf])
    (fun vb va rest => by
      simp only [stepT, htag]
      rw [ops_seq_out]
      simp only [List.length_map])

theorem itemAltP_runs (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (htag : it.tag = 6)
    (_hc : CTWF st.tt st.ct) (hcur : it.ctx ≤ st.ct.length) : ItemRuns itemAltP j cap st Tf it :=
  ops_binTop_runs ops_altE ops_altG j cap st Tf it ((ops_altE_ok _).mono (ops_TE_le _)) hcur
    (by simp [stepT, htag, opOf]) (fun v => by simp [stepT, htag, opOf])
    (fun vb va rest => by
      simp only [stepT, htag]
      rw [ops_alt_out]
      simp only [List.length_map])

theorem itemStarP_runs (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (htag : it.tag = 7)
    (_hc : CTWF st.tt st.ct) (hcur : it.ctx ≤ st.ct.length) : ItemRuns itemStarP j cap st Tf it :=
  ops_unTop_runs ops_starE ops_starG j cap st Tf it (ops_starE_ok _) hcur
    (by simp [stepT, htag, opOf])
    (fun va rest => by
      simp only [stepT, htag]
      rw [ops_star_out]
      simp only [List.length_map])

theorem itemNotP_runs (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (htag : it.tag = 8)
    (_hc : CTWF st.tt st.ct) (hcur : it.ctx ≤ st.ct.length) : ItemRuns itemNotP j cap st Tf it :=
  ops_unTop_runs ops_notE ops_notG j cap st Tf it ((ops_notE_ok _).mono (ops_TE_le _)) hcur
    (by simp [stepT, htag, opOf])
    (fun va rest => by
      simp only [stepT, htag]
      rw [ops_not_out]
      simp only [List.length_map])

theorem itemLamP_runs (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (htag : it.tag = 11)
    (_hc : CTWF st.tt st.ct) (_hcur : it.ctx ≤ st.ct.length) : ItemRuns itemLamP j cap st Tf it := by
  intro S vs _ _ hEV hEVL
  have hs : stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it vs = vs := by simp [stepT, htag]
  rw [hs, ← hEV, ← hEVL, Lists.set_get_self, Lists.set_get_self]
  exact (nruns_skip ops_WW S).mono (by have := ops_itemCost_ge j cap st Tf it vs; omega)

end Shallot.MacroPeg.Mach
