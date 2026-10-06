import MacroPeg.HigherOrder.Mach.VarTy

/-!
# Registering an arrow on stacks

The arrows are on stack `tt` as pairs (`encPairs`, entry `0` at the bottom) with their number on `ntt`.
`internP` registers the pair `(a, b)` (the tops of `sa`, `sb`, kept) and pushes its number on `d` — exactly as
`intern`: the arrows are moved to the scratch stack `w` and back one pair at a time, each compared with `(a, b)`; the
first match is remembered on `fnd` (its index plus one); without a match the pair is appended.
-/

namespace Shallot.MacroPeg.Mach

open Complexity

variable {K : Nat}

/-- If nothing is found yet (`fnd` is `0`), remember the current index plus one. -/
def markP (idx fnd z : Fin K) (hif : idx ≠ fnd) : NProg K :=
  .ite fnd .zero (.seq (.prim (.pop fnd)) (.seq (.prim (.dup idx fnd hif)) (.prim (.inc fnd)))) (nskip z)

/-- Read the two comparison results (the tops of `f`, `f2`, both popped); mark when both say equal (`1`). -/
def selectP (idx fnd f f2 z : Fin K) (hif : idx ≠ fnd) : NProg K :=
  caseTop f [.prim (.pop f2), caseTop f2 [nskip z, markP idx fnd z hif, nskip z] (nskip z), .prim (.pop f2)] (nskip z)

/-- Move one pair back from `w` to `tt`, compare it with `(a, b)` (the tops of `sa`, `sb`), mark a first match,
and count the index up. Scratch: `t u g` for the comparisons, `f f2` for their results, `z` for doing nothing. -/
def internStep (tt w sa sb idx fnd t u g f f2 z : Fin K) (hw : w ≠ tt) (htt : tt ≠ t) (hsa : sa ≠ u) (hsb : sb ≠ u)
    (hif : idx ≠ fnd) : NProg K :=
  .seq (nmv w tt hw) (.seq (cmpTop tt sa t u g f htt hsa) (.seq (nmv w tt hw) (.seq (cmpTop tt sb t u g f2 htt hsb)
    (.seq (selectP idx fnd f f2 z hif) (.prim (.inc idx))))))

/-- Register `(a, b)` and push its number on `d`. -/
def internP (tt ntt w sa sb d idx fnd t u g f f2 z : Fin K) (htw : tt ≠ w) (htt : tt ≠ t) (hsa : sa ≠ u)
    (hsb : sb ≠ u) (hif : idx ≠ fnd) (hfd : fnd ≠ d) (hsat : sa ≠ tt) (hsbt : sb ≠ tt) (hnd : ntt ≠ d) : NProg K :=
  .seq (nmvAll tt w htw) (.seq (.prim (.pushZ fnd)) (.seq (.prim (.pushZ idx))
    (.seq (.loop w .nonempty (internStep tt w sa sb idx fnd t u g f f2 z (Ne.symm htw) htt hsa hsb hif))
      (.seq (.prim (.pop idx))
        (.seq (.ite fnd .zero
            (.seq (.prim (.dup sa tt hsat)) (.seq (.prim (.dup sb tt hsbt)) (.seq (.prim (.inc ntt))
              (.prim (.dup ntt d hnd)))))
            (.prim (.dup fnd d hfd)))
          (.prim (.pop fnd)))))))

/-! ## The first match -/

/-- The first match of `q` among the first `k` entries (its index plus one), or `0`. -/
def hitAt (P : List (Nat × Nat)) (q : Nat × Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if hitAt P q k = 0 ∧ P[k]? = some q then k + 1 else hitAt P q k

theorem indexIn_first (q : Nat × Nat) : ∀ (P : List (Nat × Nat)) (k : Nat), q ∉ P.take k → P[k]? = some q →
    indexIn q P = k
  | [], _, _, h => by simp at h
  | p :: P, 0, _, h => by simp at h; simp [indexIn, h]
  | p :: P, k + 1, hn, h => by
    have hp : p ≠ q := fun e => hn (by simp [e])
    have := indexIn_first q P k (fun hm => hn (by simp [hm])) (by simpa using h)
    simp [indexIn, hp, this]

theorem hitAt_eq (P : List (Nat × Nat)) (q : Nat × Nat) :
    ∀ k, k ≤ P.length → hitAt P q k = if q ∈ P.take k then indexIn q P + 1 else 0
  | 0, _ => by simp [hitAt]
  | k + 1, hk => by
    have ih := hitAt_eq P q k (by omega)
    have hlt : k < P.length := by omega
    have hmem : q ∈ P.take (k + 1) ↔ q ∈ P.take k ∨ P[k] = q := by
      rw [List.take_succ_eq_append_getElem hlt, List.mem_append, List.mem_singleton, eq_comm]
    rw [hitAt, ih]
    simp only [hmem]
    by_cases hm : q ∈ P.take k
    · simp [hm]
    · by_cases he : P[k] = q
      · have := indexIn_first q P k hm (by simp [List.getElem?_eq_getElem hlt, he])
        simp [hm, he, List.getElem?_eq_getElem hlt, this]
      · simp [hm, he, List.getElem?_eq_getElem hlt]

/-! ## Marking -/

theorem markP_runs (idx fnd z : Fin K) (hif : idx ≠ fnd) (S : Lists K) {lix lfd : List Nat} {k v : Nat}
    (hi : S idx = lix ++ [k]) (hf : S fnd = lfd ++ [v]) :
    NRuns (markP idx fnd z hif) S (S.set fnd (lfd ++ [if v = 0 then k + 1 else v])) 4 := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · have x₁ := nruns_pop fnd S hf
    have x₂ := nruns_dup idx fnd hif (S.set fnd lfd) (l := lix) (v := k) (by rw [Lists.set_ne _ _ hif]; exact hi)
    have hX : (S.set fnd lfd).set fnd ((S.set fnd lfd) fnd ++ [k]) = S.set fnd (lfd ++ [k]) := by
      rw [Lists.set_same, Lists.set_set_u]
    rw [hX] at x₂
    have x₃ := nruns_inc fnd (S.set fnd (lfd ++ [k])) (l := lfd) (v := k) (by simp)
    rw [Lists.set_set_u] at x₃
    simp only [if_true]
    exact (x₁.seq (x₂.seq x₃)).iteT (by rw [hf]; exact eval_zero_zero _)
  · have x := nruns_skip z S
    have e : S.set fnd (lfd ++ [if v = 0 then k + 1 else v]) = S := by
      rw [if_neg (by omega), ← hf, Lists.set_get_self]
    rw [e]
    obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
    exact (x.iteF (by rw [hf]; exact eval_zero_succ _ _)).mono (by omega)

theorem selectP_runs (idx fnd f f2 z : Fin K) (hif : idx ≠ fnd) (hd : [idx, fnd, f, f2].Nodup) (S : Lists K)
    {lix lfd lf lf2 : List Nat} {k v c₁ c₂ : Nat} (hi : S idx = lix ++ [k]) (hfd : S fnd = lfd ++ [v])
    (hf : S f = lf ++ [c₁]) (hf2 : S f2 = lf2 ++ [c₂]) (h₁ : c₁ ≤ 2) (h₂ : c₂ ≤ 2) :
    NRuns (selectP idx fnd f f2 z hif) S
      (((S.set f lf).set f2 lf2).set fnd (lfd ++ [if c₁ = 1 ∧ c₂ = 1 ∧ v = 0 then k + 1 else v])) 16 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  have n₁ : idx ≠ f := hd.1.2.1
  have n₂ : idx ≠ f2 := hd.1.2.2
  have n₃ : fnd ≠ f := hd.2.1.1
  have n₄ : fnd ≠ f2 := hd.2.1.2
  have n₅ : f ≠ f2 := hd.2.2.1
  -- after both pops, nothing changes unless both are equal
  have hsame : ∀ (c₁ c₂ : Nat), ¬(c₁ = 1 ∧ c₂ = 1) →
      ((S.set f lf).set f2 lf2).set fnd (lfd ++ [if c₁ = 1 ∧ c₂ = 1 ∧ v = 0 then k + 1 else v]) =
        (S.set f lf).set f2 lf2 := by
    intro c₁ c₂ hne
    rw [if_neg (fun h => hne ⟨h.1, h.2.1⟩), ← hfd]
    funext x
    by_cases hx : x = fnd
    · subst hx; simp [Lists.set, n₃, n₄]
    · simp [Lists.set, hx]
  have hpop2 : ∀ L : Lists K, L f2 = lf2 ++ [c₂] → NRuns (.prim (.pop f2)) L (L.set f2 lf2) 1 :=
    fun L hL => nruns_pop f2 L hL
  have hf2' : (S.set f lf) f2 = lf2 ++ [c₂] := by rw [Lists.set_ne _ _ (Ne.symm n₅)]; exact hf2
  rcases (show c₁ = 0 ∨ c₁ = 1 ∨ c₁ = 2 by omega) with rfl | rfl | rfl
  · rw [hsame 0 c₂ (by omega)]
    exact (caseTop_runs f _ _ 0 (by simp) S lf hf _ 1 (hpop2 _ hf2')).mono (by omega)
  · rcases (show c₂ = 0 ∨ c₂ = 1 ∨ c₂ = 2 by omega) with rfl | rfl | rfl
    · rw [hsame 1 0 (by omega)]
      have hin := caseTop_runs f2 [nskip z, markP idx fnd z hif, nskip z] (nskip z) 0 (by simp) (S.set f lf) lf2
        hf2' _ 2 (nruns_skip z _)
      exact (caseTop_runs f _ _ 1 (by simp) S lf hf _ _ hin).mono (by omega)
    · have hm := markP_runs idx fnd z hif ((S.set f lf).set f2 lf2) (lix := lix) (lfd := lfd) (k := k) (v := v)
        (by simp [Lists.set, n₁, n₂, hi]) (by simp [Lists.set, n₃, n₄, hfd])
      have hin := caseTop_runs f2 [nskip z, markP idx fnd z hif, nskip z] (nskip z) 1 (by simp) (S.set f lf) lf2
        hf2' _ 4 hm
      have e : (if v = 0 then k + 1 else v) = (if 1 = 1 ∧ 1 = 1 ∧ v = 0 then k + 1 else v) := by simp
      rw [← e]
      exact (caseTop_runs f _ _ 1 (by simp) S lf hf _ _ hin).mono (by omega)
    · rw [hsame 1 2 (by omega)]
      have hin := caseTop_runs f2 [nskip z, markP idx fnd z hif, nskip z] (nskip z) 2 (by simp) (S.set f lf) lf2
        hf2' _ 2 (nruns_skip z _)
      exact (caseTop_runs f _ _ 1 (by simp) S lf hf _ _ hin).mono (by omega)
  · rw [hsame 2 c₂ (by omega)]
    exact (caseTop_runs f _ _ 2 (by simp) S lf hf _ 1 (hpop2 _ hf2')).mono (by omega)

/-! ## One entry -/

/-- The stacks of `internP`, all different: `tt ntt w sa sb d idx fnd t u g f f2 z`. -/
abbrev InternStacks (tt ntt w sa sb d idx fnd t u g f f2 z : Fin K) : Prop :=
  [tt, ntt, w, sa, sb, d, idx, fnd, t, u, g, f, f2, z].Nodup

theorem cmpRes_le (a b : Nat) : cmpRes a b ≤ 2 := by
  unfold cmpRes; by_cases h₁ : a < b <;> by_cases h₂ : a = b <;> simp [h₁, h₂]

theorem cmpRes_one {a b : Nat} : cmpRes a b = 1 ↔ a = b := by
  unfold cmpRes; by_cases h₁ : a < b <;> by_cases h₂ : a = b <;> simp [h₁, h₂] <;> omega

theorem encPairs_append (P Q : List (Nat × Nat)) : encPairs (P ++ Q) = encPairs P ++ encPairs Q := by
  simp [encPairs]

theorem encPairs_take_succ (P : List (Nat × Nat)) (k : Nat) (h : k < P.length) :
    encPairs (P.take (k + 1)) = encPairs (P.take k) ++ [P[k].1, P[k].2] := by
  rw [List.take_succ_eq_append_getElem h, encPairs_append]; rfl

theorem encPairs_drop (P : List (Nat × Nat)) (k : Nat) (h : k < P.length) :
    (encPairs (P.drop k)).reverse = ((encPairs (P.drop (k + 1))).reverse ++ [P[k].2]) ++ [P[k].1] := by
  rw [List.drop_eq_getElem_cons h]
  simp only [encPairs, List.flatMap_cons, List.reverse_append]
  simp

/-- The cost of one entry, with all numbers at most `B`. -/
def internStepCost (B : Nat) : Nat := 2 * ((2 * B + 1) * (2 * B + 6) + 20) + 22

theorem cmpCost_le {x y B : Nat} (hx : x ≤ B) (hy : y ≤ B) :
    (x + y + 1) * (2 * x + 6) + 20 ≤ (2 * B + 1) * (2 * B + 6) + 20 :=
  Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) _

/-- The states of the search: `k` entries moved back. -/
def internSt (tt w idx fnd : Fin K) (S : Lists K) (P : List (Nat × Nat)) (q : Nat × Nat) (k : Nat) : Lists K :=
  (((S.set tt (encPairs (P.take k))).set w (encPairs (P.drop k)).reverse).set idx (S idx ++ [k])).set fnd
    (S fnd ++ [hitAt P q k])

theorem hitAt_succ_val (P : List (Nat × Nat)) (a b k : Nat) (h : k < P.length) :
    (if cmpRes P[k].1 a = 1 ∧ cmpRes P[k].2 b = 1 ∧ hitAt P (a, b) k = 0 then k + 1 else hitAt P (a, b) k) =
      hitAt P (a, b) (k + 1) := by
  rw [hitAt, List.getElem?_eq_getElem h]
  simp only [cmpRes_one]
  by_cases h₁ : P[k].1 = a <;> by_cases h₂ : P[k].2 = b <;> by_cases h₃ : hitAt P (a, b) k = 0 <;>
    simp [h₁, h₂, h₃, Prod.ext_iff]

theorem internStep_runs (tt ntt w sa sb d idx fnd t u g f f2 z : Fin K) (hw : w ≠ tt) (htt : tt ≠ t) (hsa : sa ≠ u)
    (hsb : sb ≠ u) (hif : idx ≠ fnd) (hd : InternStacks tt ntt w sa sb d idx fnd t u g f f2 z) (S : Lists K)
    {P : List (Nat × Nat)} {la lb : List Nat} {a b B : Nat} (ha : S sa = la ++ [a]) (hb : S sb = lb ++ [b])
    (hPB : ∀ q ∈ P, q.1 ≤ B ∧ q.2 ≤ B) (haB : a ≤ B) (hbB : b ≤ B) {k : Nat} (hk : k < P.length) :
    NRuns (internStep tt w sa sb idx fnd t u g f f2 z hw htt hsa hsb hif) (internSt tt w idx fnd S P (a, b) k)
      (internSt tt w idx fnd S P (a, b) (k + 1)) (internStepCost B) := by
  have hd₁ : [tt, sa, t, u, g, f].Nodup := hd.sublist
    (.cons_cons _ (.cons _ (.cons _ (.cons_cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons_cons _ (.cons_cons _
      (.cons_cons _ (.cons_cons _ (.cons _ (.cons _ .slnil))))))))))))))
  have hd₂ : [tt, sb, t, u, g, f2].Nodup := hd.sublist
    (.cons_cons _ (.cons _ (.cons _ (.cons _ (.cons_cons _ (.cons _ (.cons _ (.cons _ (.cons_cons _ (.cons_cons _
      (.cons_cons _ (.cons _ (.cons_cons _ (.cons _ .slnil))))))))))))))
  have hd₃ : [idx, fnd, f, f2].Nodup := hd.sublist
    (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons_cons _ (.cons_cons _ (.cons _ (.cons _ (.cons _
      (.cons_cons _ (.cons_cons _ (.cons _ .slnil))))))))))))))
  simp only [InternStacks, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true] at hd
  have n_tt_w : tt ≠ w := hd.1.2.1
  have n_tt_sa : tt ≠ sa := hd.1.2.2.1
  have n_tt_sb : tt ≠ sb := hd.1.2.2.2.1
  have n_tt_idx : tt ≠ idx := hd.1.2.2.2.2.2.1
  have n_tt_fnd : tt ≠ fnd := hd.1.2.2.2.2.2.2.1
  have n_tt_f : tt ≠ f := hd.1.2.2.2.2.2.2.2.2.2.2.1
  have n_tt_f2 : tt ≠ f2 := hd.1.2.2.2.2.2.2.2.2.2.2.2.1
  have n_w_idx : w ≠ idx := hd.2.2.1.2.2.2.1
  have n_w_fnd : w ≠ fnd := hd.2.2.1.2.2.2.2.1
  have n_w_f : w ≠ f := hd.2.2.1.2.2.2.2.2.2.2.2.1
  have n_w_f2 : w ≠ f2 := hd.2.2.1.2.2.2.2.2.2.2.2.2.1
  have n_w_sa : w ≠ sa := hd.2.2.1.1
  have n_w_sb : w ≠ sb := hd.2.2.1.2.1
  have n_idx_fnd : idx ≠ fnd := hd.2.2.2.2.2.2.1.1
  have n_idx_f : idx ≠ f := hd.2.2.2.2.2.2.1.2.2.2.2.1
  have n_idx_f2 : idx ≠ f2 := hd.2.2.2.2.2.2.1.2.2.2.2.2.1
  have n_fnd_f : fnd ≠ f := hd.2.2.2.2.2.2.2.1.2.2.2.1
  have n_fnd_f2 : fnd ≠ f2 := hd.2.2.2.2.2.2.2.1.2.2.2.2.1
  have n_f_f2 : f ≠ f2 := hd.2.2.2.2.2.2.2.2.2.2.2.1.1
  have n_sa_f : sa ≠ f := hd.2.2.2.1.2.2.2.2.2.2.2.1
  have n_sa_idx : sa ≠ idx := hd.2.2.2.1.2.2.1
  have n_sa_fnd : sa ≠ fnd := hd.2.2.2.1.2.2.2.1
  have n_sb_f : sb ≠ f := hd.2.2.2.2.1.2.2.2.2.2.2.1
  have n_sb_f2 : sb ≠ f2 := hd.2.2.2.2.1.2.2.2.2.2.2.2.1
  have n_sb_idx : sb ≠ idx := hd.2.2.2.2.1.2.1
  have n_sb_fnd : sb ≠ fnd := hd.2.2.2.2.1.2.2.1
  clear hd
  have hq : P[k] ∈ P := List.getElem_mem hk
  let q := P[k]
  let E := encPairs (P.take k)
  let R := (encPairs (P.drop (k + 1))).reverse
  let X₀ := internSt tt w idx fnd S P (a, b) k
  have h₀w : X₀ w = (R ++ [q.2]) ++ [q.1] := by
    simp [X₀, internSt, Lists.set, n_w_idx, n_w_fnd, R, q, encPairs_drop P k hk]
  have h₀tt : X₀ tt = E := by simp [X₀, internSt, Lists.set, n_tt_w, n_tt_idx, n_tt_fnd, E]
  have x₁ := nruns_mv w tt hw X₀ h₀w
  rw [h₀tt] at x₁
  let X₁ := (X₀.set tt (E ++ [q.1])).set w (R ++ [q.2])
  have x₂ := nruns_cmpTop tt sa t u g f htt hsa hd₁ X₁ (li := E) (lj := la) (a := q.1) (b := a)
    (by simp [X₁, Lists.set, n_tt_w]) (by simp [X₁, X₀, internSt, Lists.set, n_tt_sa.symm, n_w_sa.symm,
      n_sa_idx, n_sa_fnd, ha])
  have h₁f : X₁ f = S f := by
    simp [X₁, X₀, internSt, Lists.set, n_tt_f.symm, n_w_f.symm, n_idx_f.symm, n_fnd_f.symm]
  rw [h₁f] at x₂
  let X₂ := X₁.set f (S f ++ [cmpRes q.1 a])
  have x₃ := nruns_mv w tt hw X₂ (l := R) (v := q.2) (by simp [X₂, X₁, Lists.set, n_w_f])
  have h₂tt : X₂ tt = E ++ [q.1] := by simp [X₂, X₁, Lists.set, n_tt_f, n_tt_w]
  rw [h₂tt] at x₃
  let X₃ := (X₂.set tt ((E ++ [q.1]) ++ [q.2])).set w R
  have x₄ := nruns_cmpTop tt sb t u g f2 htt hsb hd₂ X₃ (li := E ++ [q.1]) (lj := lb) (a := q.2) (b := b)
    (by simp [X₃, Lists.set, n_tt_w]) (by simp [X₃, X₂, X₁, X₀, internSt, Lists.set, n_tt_sb.symm, n_w_sb.symm,
      n_sb_f, n_sb_idx, n_sb_fnd, hb])
  have h₃f2 : X₃ f2 = S f2 := by
    simp [X₃, X₂, X₁, X₀, internSt, Lists.set, n_tt_f2.symm, n_w_f2.symm, n_f_f2.symm, n_idx_f2.symm,
      n_fnd_f2.symm]
  rw [h₃f2] at x₄
  let X₄ := X₃.set f2 (S f2 ++ [cmpRes q.2 b])
  have x₅ := selectP_runs idx fnd f f2 z hif hd₃ X₄ (lix := S idx) (lfd := S fnd) (lf := S f) (lf2 := S f2)
    (k := k) (v := hitAt P (a, b) k) (c₁ := cmpRes q.1 a) (c₂ := cmpRes q.2 b)
    (by simp [X₄, X₃, X₂, X₁, X₀, internSt, Lists.set, n_idx_f2, n_idx_f, n_tt_idx.symm, n_w_idx.symm, n_idx_fnd])
    (by simp [X₄, X₃, X₂, X₁, X₀, internSt, Lists.set, n_fnd_f2, n_fnd_f, n_tt_fnd.symm, n_w_fnd.symm])
    (by simp [X₄, X₃, X₂, Lists.set, n_f_f2, n_tt_f.symm, n_w_f.symm])
    (by simp [X₄]) (cmpRes_le _ _) (cmpRes_le _ _)
  rw [hitAt_succ_val P a b k hk] at x₅
  let X₅ := ((X₄.set f (S f)).set f2 (S f2)).set fnd (S fnd ++ [hitAt P (a, b) (k + 1)])
  have x₆ := nruns_inc idx X₅ (l := S idx) (v := k)
    (by simp [X₅, X₄, X₃, X₂, X₁, X₀, internSt, Lists.set, n_idx_fnd, n_idx_f, n_idx_f2, n_tt_idx.symm,
      n_w_idx.symm])
  have e : X₅.set idx (S idx ++ [k + 1]) = internSt tt w idx fnd S P (a, b) (k + 1) := by
    have htk : encPairs (P.take (k + 1)) = (E ++ [q.1]) ++ [q.2] := by
      rw [encPairs_take_succ P k hk]; simp [E, q]
    clear x₁ x₂ x₃ x₄ x₅ x₆ hPB
    have := n_tt_w.symm
    have := n_tt_sa.symm
    have := n_tt_sb.symm
    have := n_tt_idx.symm
    have := n_tt_fnd.symm
    have := n_tt_f.symm
    have := n_tt_f2.symm
    have := n_w_idx.symm
    have := n_w_fnd.symm
    have := n_w_f.symm
    have := n_w_f2.symm
    have := n_w_sa.symm
    have := n_w_sb.symm
    have := n_idx_fnd.symm
    have := n_idx_f.symm
    have := n_idx_f2.symm
    have := n_fnd_f.symm
    have := n_fnd_f2.symm
    have := n_f_f2.symm
    have := n_sa_f.symm
    have := n_sa_idx.symm
    have := n_sa_fnd.symm
    have := n_sb_f.symm
    have := n_sb_f2.symm
    have := n_sb_idx.symm
    have := n_sb_fnd.symm
    simp only [internSt, htk]
    funext x
    by_cases h₁ : x = fnd
    · subst h₁; simp [X₅, Lists.set, *]
    by_cases h₂ : x = idx
    · subst h₂; simp [X₅, Lists.set, *]
    by_cases h₃ : x = f2
    · subst h₃; simp [X₅, X₄, Lists.set, *]
    by_cases h₄ : x = f
    · subst h₄; simp [X₅, X₄, Lists.set, *]
    by_cases h₅ : x = w
    · subst h₅; simp [X₅, X₄, X₃, Lists.set, R, *]
    by_cases h₆ : x = tt
    · subst h₆; simp [X₅, X₄, X₃, Lists.set, *]
    simp [X₅, X₄, X₃, X₂, X₁, X₀, internSt, Lists.set, *]
  rw [e] at x₆
  refine (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq x₆))))).mono ?_
  have c₁ := cmpCost_le (hPB q hq).1 haB
  have c₂ := cmpCost_le (hPB q hq).2 hbB
  simp only [internStepCost]
  omega

/-! ## Registering -/

/-- The cost of `internP` on `n` arrows, with all numbers at most `B`. -/
def internCost (n B : Nat) : Nat := (n + 1) * (internStepCost B + 30)

theorem eval_nonempty_nil : NTest.nonempty.eval [] = false := rfl

/-- `internP` registers the arrow as `intern` and pushes its number. -/
theorem internP_runs (tt ntt w sa sb d idx fnd t u g f f2 z : Fin K) (htw : tt ≠ w) (htt : tt ≠ t) (hsa : sa ≠ u)
    (hsb : sb ≠ u) (hif : idx ≠ fnd) (hfd : fnd ≠ d) (hsat : sa ≠ tt) (hsbt : sb ≠ tt) (hnd : ntt ≠ d)
    (hd : InternStacks tt ntt w sa sb d idx fnd t u g f f2 z) (S : Lists K) {P : List (Nat × Nat)}
    {la lb ln : List Nat} {a b B : Nat} (hP : S tt = encPairs P) (hw : S w = []) (ha : S sa = la ++ [a])
    (hb : S sb = lb ++ [b]) (hn : S ntt = ln ++ [P.length]) (hPB : ∀ q ∈ P, q.1 ≤ B ∧ q.2 ≤ B) (haB : a ≤ B)
    (hbB : b ≤ B) :
    NRuns (internP tt ntt w sa sb d idx fnd t u g f f2 z htw htt hsa hsb hif hfd hsat hsbt hnd) S
      (((S.set tt (encPairs (intern P a b).1)).set ntt (ln ++ [(intern P a b).1.length])).set d
        (S d ++ [(intern P a b).2])) (internCost P.length B) := by
  have hstep := fun k (hk : k < P.length) => internStep_runs tt ntt w sa sb d idx fnd t u g f f2 z (Ne.symm htw)
    htt hsa hsb hif hd S ha hb hPB haB hbB hk
  simp only [InternStacks, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true] at hd
  have n_tt_ntt : tt ≠ ntt := hd.1.1
  have n_ntt_tt : ntt ≠ tt := Ne.symm n_tt_ntt
  have n_tt_w : tt ≠ w := hd.1.2.1
  have n_w_tt : w ≠ tt := Ne.symm n_tt_w
  have n_tt_sa : tt ≠ sa := hd.1.2.2.1
  have n_sa_tt : sa ≠ tt := Ne.symm n_tt_sa
  have n_tt_sb : tt ≠ sb := hd.1.2.2.2.1
  have n_sb_tt : sb ≠ tt := Ne.symm n_tt_sb
  have n_tt_d : tt ≠ d := hd.1.2.2.2.2.1
  have n_d_tt : d ≠ tt := Ne.symm n_tt_d
  have n_tt_idx : tt ≠ idx := hd.1.2.2.2.2.2.1
  have n_idx_tt : idx ≠ tt := Ne.symm n_tt_idx
  have n_tt_fnd : tt ≠ fnd := hd.1.2.2.2.2.2.2.1
  have n_fnd_tt : fnd ≠ tt := Ne.symm n_tt_fnd
  have n_ntt_w : ntt ≠ w := hd.2.1.1
  have n_w_ntt : w ≠ ntt := Ne.symm n_ntt_w
  have n_ntt_sa : ntt ≠ sa := hd.2.1.2.1
  have n_sa_ntt : sa ≠ ntt := Ne.symm n_ntt_sa
  have n_ntt_sb : ntt ≠ sb := hd.2.1.2.2.1
  have n_sb_ntt : sb ≠ ntt := Ne.symm n_ntt_sb
  have n_ntt_d : ntt ≠ d := hd.2.1.2.2.2.1
  have n_d_ntt : d ≠ ntt := Ne.symm n_ntt_d
  have n_ntt_idx : ntt ≠ idx := hd.2.1.2.2.2.2.1
  have n_idx_ntt : idx ≠ ntt := Ne.symm n_ntt_idx
  have n_ntt_fnd : ntt ≠ fnd := hd.2.1.2.2.2.2.2.1
  have n_fnd_ntt : fnd ≠ ntt := Ne.symm n_ntt_fnd
  have n_w_sa : w ≠ sa := hd.2.2.1.1
  have n_sa_w : sa ≠ w := Ne.symm n_w_sa
  have n_w_sb : w ≠ sb := hd.2.2.1.2.1
  have n_sb_w : sb ≠ w := Ne.symm n_w_sb
  have n_w_d : w ≠ d := hd.2.2.1.2.2.1
  have n_d_w : d ≠ w := Ne.symm n_w_d
  have n_w_idx : w ≠ idx := hd.2.2.1.2.2.2.1
  have n_idx_w : idx ≠ w := Ne.symm n_w_idx
  have n_w_fnd : w ≠ fnd := hd.2.2.1.2.2.2.2.1
  have n_fnd_w : fnd ≠ w := Ne.symm n_w_fnd
  have n_sa_sb : sa ≠ sb := hd.2.2.2.1.1
  have n_sb_sa : sb ≠ sa := Ne.symm n_sa_sb
  have n_sa_d : sa ≠ d := hd.2.2.2.1.2.1
  have n_d_sa : d ≠ sa := Ne.symm n_sa_d
  have n_sa_idx : sa ≠ idx := hd.2.2.2.1.2.2.1
  have n_idx_sa : idx ≠ sa := Ne.symm n_sa_idx
  have n_sa_fnd : sa ≠ fnd := hd.2.2.2.1.2.2.2.1
  have n_fnd_sa : fnd ≠ sa := Ne.symm n_sa_fnd
  have n_sb_d : sb ≠ d := hd.2.2.2.2.1.1
  have n_d_sb : d ≠ sb := Ne.symm n_sb_d
  have n_sb_idx : sb ≠ idx := hd.2.2.2.2.1.2.1
  have n_idx_sb : idx ≠ sb := Ne.symm n_sb_idx
  have n_sb_fnd : sb ≠ fnd := hd.2.2.2.2.1.2.2.1
  have n_fnd_sb : fnd ≠ sb := Ne.symm n_sb_fnd
  have n_d_idx : d ≠ idx := hd.2.2.2.2.2.1.1
  have n_idx_d : idx ≠ d := Ne.symm n_d_idx
  have n_d_fnd : d ≠ fnd := hd.2.2.2.2.2.1.2.1
  have n_fnd_d : fnd ≠ d := Ne.symm n_d_fnd
  have n_idx_fnd : idx ≠ fnd := hd.2.2.2.2.2.2.1.1
  have n_fnd_idx : fnd ≠ idx := Ne.symm n_idx_fnd
  clear hd
  let n := P.length
  -- move the arrows out, start the index and the mark
  have x₁ := nruns_mvAll tt w htw S
  rw [hw, hP, List.nil_append] at x₁
  let Y₁ := (S.set w (encPairs P).reverse).set tt []
  have x₂ := nruns_pushZ fnd Y₁
  have hY₁f : Y₁ fnd = S fnd := by simp [Y₁, Lists.set, *]
  rw [hY₁f] at x₂
  let Y₂ := Y₁.set fnd (S fnd ++ [0])
  have x₃ := nruns_pushZ idx Y₂
  have hY₂i : Y₂ idx = S idx := by simp [Y₂, Y₁, Lists.set, *]
  rw [hY₂i] at x₃
  have hY : Y₂.set idx (S idx ++ [0]) = internSt tt w idx fnd S P (a, b) 0 := by
    simp only [internSt, List.take_zero, List.drop_zero, hitAt]
    funext x
    by_cases h₁ : x = idx
    · subst h₁; simp [Y₂, Y₁, Lists.set, *]
    by_cases h₂ : x = fnd
    · subst h₂; simp [Y₂, Y₁, Lists.set, *]
    by_cases h₃ : x = tt
    · subst h₃; simp [Y₂, Y₁, Lists.set, *, encPairs]
    simp [Y₂, Y₁, Lists.set, *]
  rw [hY] at x₃
  -- the search
  let F := internSt tt w idx fnd S P (a, b)
  have hFw : ∀ m, F m w = (encPairs (P.drop m)).reverse := fun m => by simp [F, internSt, Lists.set, n, *]
  have hl := nruns_family_const (i := w) (c := .nonempty)
    (p := internStep tt w sa sb idx fnd t u g f f2 z (Ne.symm htw) htt hsa hsb hif) F n (internStepCost B)
    (fun m hm => by rw [hFw, encPairs_drop P m hm]; exact eval_nonempty_ne (by simp))
    (by rw [hFw, List.drop_length]; exact eval_nonempty_nil) hstep
  -- the end of the search
  have hFi : F n idx = S idx ++ [n] := by simp [F, internSt, Lists.set, n, *]
  have x₄ := nruns_pop idx (F n) hFi
  let G := (F n).set idx (S idx)
  have hGf : G fnd = S fnd ++ [hitAt P (a, b) n] := by simp [G, F, internSt, Lists.set, n, *]
  have hGtt : G tt = encPairs P := by simp [G, F, internSt, Lists.set, n, *]
  have hGd : G d = S d := by simp [G, F, internSt, Lists.set, n, *]
  have hhit := hitAt_eq P (a, b) n (Nat.le_refl _)
  rw [List.take_length] at hhit
  by_cases hm : (a, b) ∈ P
  · rw [if_pos hm] at hhit
    rw [hhit] at hGf
    have y₁ := nruns_dup fnd d hfd G hGf
    rw [hGd] at y₁
    have y₂ := nruns_pop fnd (G.set d (S d ++ [indexIn (a, b) P + 1])) (l := S fnd) (v := indexIn (a, b) P + 1)
      (by simp [Lists.set, *])
    have hint : intern P a b = (P, indexIn (a, b) P + 1) := by simp [intern, hm]
    have e : (G.set d (S d ++ [indexIn (a, b) P + 1])).set fnd (S fnd) =
        ((S.set tt (encPairs (intern P a b).1)).set ntt (ln ++ [(intern P a b).1.length])).set d
          (S d ++ [(intern P a b).2]) := by
      rw [hint]
      funext x
      by_cases h₁ : x = fnd
      · subst h₁; simp [Lists.set, *]
      by_cases h₂ : x = d
      · subst h₂; simp [Lists.set, *]
      by_cases h₃ : x = idx
      · subst h₃; simp [G, Lists.set, *]
      by_cases h₄ : x = tt
      · subst h₄; simp [G, F, internSt, Lists.set, n, *]
      by_cases h₅ : x = ntt
      · subst h₅; simp [G, F, internSt, Lists.set, n, *]
      by_cases h₆ : x = w
      · subst h₆; simp [G, F, internSt, Lists.set, n, encPairs, *]
      simp [G, F, internSt, Lists.set, n, *]
    rw [e] at y₂
    refine (x₁.seq (x₂.seq (x₃.seq (hl.seq (x₄.seq (((y₁.iteF (p := .seq (.prim (.dup sa tt hsat))
      (.seq (.prim (.dup sb tt hsbt)) (.seq (.prim (.inc ntt)) (.prim (.dup ntt d hnd)))))
      (by rw [hGf]; exact eval_zero_succ _ _)).seq y₂))))))).mono ?_
    have h₁ : P.length * (internStepCost B + 30) = P.length * (internStepCost B + 1) + P.length * 29 := by
      rw [← Nat.mul_add]
    simp only [internCost, encPairs_length, n]
    rw [Nat.add_mul, Nat.one_mul, h₁]; omega
  · rw [if_neg hm] at hhit
    rw [hhit] at hGf
    have hGsa : G sa = la ++ [a] := by simp [G, F, internSt, Lists.set, n, *]
    have y₁ := nruns_dup sa tt hsat G hGsa
    rw [hGtt] at y₁
    have y₂ := nruns_dup sb tt hsbt (G.set tt (encPairs P ++ [a])) (l := lb) (v := b)
      (by simp [G, F, internSt, Lists.set, n, *])
    rw [Lists.set_same, Lists.set_set_u] at y₂
    have y₃ := nruns_inc ntt (G.set tt (encPairs P ++ [a] ++ [b])) (l := ln) (v := n)
      (by simp [G, F, internSt, Lists.set, n, *])
    have y₄ := nruns_dup ntt d hnd ((G.set tt (encPairs P ++ [a] ++ [b])).set ntt (ln ++ [n + 1])) (l := ln)
      (v := n + 1) (by simp)
    have hdd : ((G.set tt (encPairs P ++ [a] ++ [b])).set ntt (ln ++ [n + 1])) d = S d := by
      simp [Lists.set, *]
    rw [hdd] at y₄
    let H := ((G.set tt (encPairs P ++ [a] ++ [b])).set ntt (ln ++ [n + 1])).set d (S d ++ [n + 1])
    have y₅ := nruns_pop fnd H (l := S fnd) (v := 0) (by simp [H, Lists.set, n, *])
    have hint : intern P a b = (P ++ [(a, b)], P.length + 1) := by simp [intern, hm]
    have e : H.set fnd (S fnd) = ((S.set tt (encPairs (intern P a b).1)).set ntt
        (ln ++ [(intern P a b).1.length])).set d (S d ++ [(intern P a b).2]) := by
      rw [hint]
      funext x
      by_cases h₁ : x = fnd
      · subst h₁; simp [Lists.set, *]
      by_cases h₂ : x = d
      · subst h₂; simp [H, Lists.set, n, *]
      by_cases h₃ : x = ntt
      · subst h₃; simp [H, Lists.set, n, *]
      by_cases h₄ : x = tt
      · subst h₄; simp [H, Lists.set, encPairs_append, *]; rfl
      by_cases h₅ : x = idx
      · subst h₅; simp [H, G, Lists.set, *]
      by_cases h₆ : x = w
      · subst h₆; simp [H, G, F, internSt, Lists.set, n, encPairs, *]
      simp [H, G, F, internSt, Lists.set, n, *]
    rw [e] at y₅
    refine (x₁.seq (x₂.seq (x₃.seq (hl.seq (x₄.seq (((y₁.seq (y₂.seq (y₃.seq y₄))).iteT (q := .prim (.dup fnd d hfd))
      (by rw [hGf]; exact eval_zero_zero _)).seq y₅)))))).mono ?_
    have h₁ : P.length * (internStepCost B + 30) = P.length * (internStepCost B + 1) + P.length * 29 := by
      rw [← Nat.mul_add]
    simp only [internCost, encPairs_length, n]
    rw [Nat.add_mul, Nat.one_mul, h₁]; omega

end Shallot.MacroPeg.Mach
