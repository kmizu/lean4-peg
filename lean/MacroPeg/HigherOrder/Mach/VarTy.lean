import MacroPeg.HigherOrder.Mach.Tok
import MacroPeg.HigherOrder.Mach.ParseSpec

/-!
# The type of a variable on stacks

The contexts are on stack `ct` as pairs `(parent, type)` (`encPairs`, entry `0` at the bottom).

* `entryP`: push the parent (or the type) of the context entry `c` (the top of `cc`, kept) on `o`.
* `varTyP`: walk from context `cur` (the top of `cs`, kept) up `i` parents (the top of `ci`, consumed) and push the
  type of the innermost binder there on `o` — exactly as `varTy` on well-formed contexts (`varTyP_ok`); stop
  rejecting when the walk runs out (`varTyP_fail`).

On well-formed contexts `varTy` only follows parents: `varTy_walk`.
-/

namespace Shallot.MacroPeg.Mach

open Complexity

variable {K : Nat}

/-! ## Pairs on a stack -/

theorem encPairs_fst : ∀ (P : List (Nat × Nat)) (k : Nat) (h : k < P.length), (encPairs P)[2 * k]? = some P[k].1
  | [], _, h => absurd h (by simp)
  | _ :: _, 0, _ => rfl
  | p :: P, k + 1, h => by
    have := encPairs_fst P k (by simpa using h)
    simpa [encPairs, show 2 * (k + 1) = 2 * k + 2 by omega] using this

theorem encPairs_snd : ∀ (P : List (Nat × Nat)) (k : Nat) (h : k < P.length),
    (encPairs P)[2 * k + 1]? = some P[k].2
  | [], _, h => absurd h (by simp)
  | _ :: _, 0, _ => rfl
  | p :: P, k + 1, h => by
    have := encPairs_snd P k (by simpa using h)
    simpa [encPairs, show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by omega] using this

theorem encPairs_length (P : List (Nat × Nat)) : (encPairs P).length = 2 * P.length := by
  induction P with
  | nil => rfl
  | cons p P ih => simp [encPairs] at ih ⊢; omega

/-! ## Walking up the contexts -/

/-- The parent of context `c` (`0` stays `0`). -/
def upCtx (ct : List (Nat × Nat)) : Nat → Nat
  | 0 => 0
  | c + 1 => (ct[c]?.map Prod.fst).getD 0

/-- `m` steps up from context `c`. -/
def walkCtx (ct : List (Nat × Nat)) (c : Nat) : Nat → Nat
  | 0 => c
  | m + 1 => upCtx ct (walkCtx ct c m)

theorem walkCtx_succ' (ct : List (Nat × Nat)) : ∀ (m c : Nat), walkCtx ct c (m + 1) = walkCtx ct (upCtx ct c) m
  | 0, _ => rfl
  | m + 1, c => by rw [walkCtx, walkCtx_succ' ct m c]; rfl

theorem walkCtx_zero (ct : List (Nat × Nat)) : ∀ m, walkCtx ct 0 m = 0
  | 0 => rfl
  | m + 1 => by rw [walkCtx, walkCtx_zero ct m]; rfl

/-- Once the walk reaches `0` it stays there. -/
theorem walkCtx_stuck (ct : List (Nat × Nat)) (c : Nat) {m : Nat} (h : walkCtx ct c m = 0) :
    ∀ m', m ≤ m' → walkCtx ct c m' = 0 := by
  intro m' hm
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction r with
  | zero => exact h
  | succ r ih => rw [← Nat.add_assoc, walkCtx, ih (by omega)]; rfl

theorem upCtx_le {tt ct : List (Nat × Nat)} (hc : CTWF tt ct) : ∀ c, c ≤ ct.length → upCtx ct c < c ∨ c = 0
  | 0, _ => .inr rfl
  | c + 1, h => by
    have hlt : c < ct.length := by omega
    left; simp only [upCtx, List.getElem?_eq_getElem hlt, Option.map_some, Option.getD_some]
    have := (hc c hlt).1; omega

theorem walkCtx_le {tt ct : List (Nat × Nat)} (hc : CTWF tt ct) (c : Nat) (hcl : c ≤ ct.length) :
    ∀ m, walkCtx ct c m ≤ ct.length
  | 0 => hcl
  | m + 1 => by
    have ih := walkCtx_le hc c hcl m
    rw [walkCtx]
    rcases upCtx_le hc _ ih with h | h
    · omega
    · rw [h]; exact Nat.zero_le _

/-- On well-formed contexts, `varTy` reads the type at the end of the walk. -/
theorem varTy_walk {tt ct : List (Nat × Nat)} (hc : CTWF tt ct) :
    ∀ i c, c ≤ ct.length →
      varTy ct c i = if walkCtx ct c i = 0 then none else (ct[walkCtx ct c i - 1]?).map Prod.snd
  | 0, 0, _ => by rw [varTy]; rfl
  | 0, c + 1, _ => by rw [varTy]; rfl
  | i + 1, 0, _ => by rw [varTy, walkCtx_zero]; rfl
  | i + 1, c + 1, h => by
    have hlt : c < ct.length := by omega
    have hpar := (hc c hlt).1
    rw [varTy, List.getElem?_eq_getElem hlt]
    simp only [hpar, if_true]
    rw [walkCtx_succ', varTy_walk hc i ct[c].1 (by omega)]
    simp only [upCtx, List.getElem?_eq_getElem hlt, Option.map_some, Option.getD_some]

/-! ## Reading an entry -/

/-- Push entry `2 c` (`odd = false`) or `2 c + 1` (`odd = true`) of `ct` on `o`, where `c` is the top of `cc`
(kept). Scratch: `j d T`. -/
def entryP (ct cc j d T o : Fin K) (hcj : cc ≠ j) (hcd : cc ≠ d) (hT : ct ≠ T) (hTo : T ≠ o) (odd : Bool) : NProg K :=
  .seq (.prim (.dup cc j hcj)) (.seq (.prim (.dup cc d hcd)) (.seq (addTo d j)
    (.seq (cond odd (.prim (.inc j)) (nskip j)) (peekAt ct T j o hT hTo))))

theorem entryP_runs (ct cc j d T o : Fin K) (hcj : cc ≠ j) (hcd : cc ≠ d) (hdj : d ≠ j) (hT : ct ≠ T) (hTo : T ≠ o)
    (odd : Bool) (hd : [ct, cc, j, d, T, o].Nodup) (S : Lists K) {lc : List Nat} {c v : Nat}
    (hc : S cc = lc ++ [c]) (hTe : S T = []) (hv : (S ct)[2 * c + cond odd 1 0]? = some v) :
    NRuns (entryP ct cc j d T o hcj hcd hT hTo odd) S (S.set o (S o ++ [v]))
      (6 * (S ct).length + 11 * c + 16) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨hcc, hcj', hcd', hcT, hco⟩, ⟨_, _, _, _⟩, ⟨_, hjT, hjo⟩, ⟨hdT, hdo⟩, _⟩ := hd
  have x₁ := nruns_dup cc j hcj S hc
  have x₂ := nruns_dup cc d hcd (S.set j (S j ++ [c])) (l := lc) (v := c) (by rw [Lists.set_ne _ _ hcj]; exact hc)
  let S₂ := (S.set j (S j ++ [c])).set d ((S.set j (S j ++ [c])) d ++ [c])
  have x₃ := nruns_addTo d j hdj S₂ (l := S d) (a := c) (l' := S j) (b := c)
    (by simp only [S₂]; lists_at) (by simp only [S₂]; lists_at)
  let S₃ := (S₂.set d (S d)).set j (S j ++ [c + c])
  let k := 2 * c + cond odd 1 0
  have x₄ : NRuns (cond odd (.prim (.inc j)) (nskip j)) S₃ (S₃.set j (S j ++ [k])) 2 := by
    cases odd
    · have h := nruns_skip j S₃
      have e : S₃.set j (S j ++ [k]) = S₃ := by
        simp only [S₃, k, cond, show c + c = 2 * c + 0 by omega]; lists_eq
      rw [e]; exact h
    · have h := nruns_inc j S₃ (l := S j) (v := c + c) (by simp only [S₃]; lists_at)
      have e : c + c + 1 = k := by simp only [k, cond]; omega
      rw [e] at h; exact h.mono (by omega)
  let S₄ := S₃.set j (S j ++ [k])
  have hct : S₄ ct = S ct := by simp only [S₄, S₃, S₂]; lists_at
  have hk : k < (S₄ ct).length := by
    rw [hct]; exact (List.getElem?_eq_some_iff.mp hv).1
  have x₅ := nruns_peekAt ct T j o hT hTo (by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨hcT, hcj', hco⟩, ⟨fun h => hjT h.symm, hTo⟩, hjo, by simp⟩) S₄ (by simp only [S₄, S₃, S₂]; lists_at)
    (lc := S j) (k := k) (by simp only [S₄]; lists_at) hk
  have hval : (S₄ ct)[k] = v := by
    have := List.getElem?_eq_some_iff.mp hv
    obtain ⟨_, h⟩ := this; simp only [hct]; exact h
  have e : (S₄.set j (S j)).set o (S₄ o ++ [(S₄ ct)[k]]) = S.set o (S o ++ [v]) := by
    rw [hval]; simp only [S₄, S₃, S₂]; lists_eq
  rw [e] at x₅
  rw [hct] at x₅
  refine (x₁.seq (x₂.seq (x₃.seq (x₄.seq x₅)))).mono ?_
  simp only [k]; cases odd <;> simp [cond] <;> omega

/-! ## Walking on stacks -/

/-- One step up: the top of `cc` (nonzero) becomes its parent; count `ci` down. -/
def varUpP (ct cc ci j d T p : Fin K) (hcj : cc ≠ j) (hcd : cc ≠ d) (hT : ct ≠ T) (hTp : T ≠ p) (hpc : p ≠ cc) :
    NProg K :=
  .ite cc .zero (.halt false)
    (.seq (.prim (.dec cc)) (.seq (entryP ct cc j d T p hcj hcd hT hTp false)
      (.seq (.prim (.pop cc)) (.seq (nmv p cc hpc) (.prim (.dec ci))))))

/-- The type at the end: entry `2 (c - 1) + 1` for the top `c` (nonzero) of `cc`. -/
def varEndP (ct cc j d T o : Fin K) (hcj : cc ≠ j) (hcd : cc ≠ d) (hT : ct ≠ T) (hTo : T ≠ o) : NProg K :=
  .ite cc .zero (.halt false)
    (.seq (.prim (.dec cc)) (.seq (entryP ct cc j d T o hcj hcd hT hTo true) (.prim (.pop cc))))

/-- Push the type of variable `i` (the top of `ci`, consumed) in context `c` (the top of `cs`, kept) on `o`. -/
def varTyP (ct cs ci o cc j d T p : Fin K) (hsc : cs ≠ cc) (hcj : cc ≠ j) (hcd : cc ≠ d) (hT : ct ≠ T) (hTp : T ≠ p)
    (hpc : p ≠ cc) (hTo : T ≠ o) : NProg K :=
  .seq (.prim (.dup cs cc hsc))
    (.seq (.loop ci .pos (varUpP ct cc ci j d T p hcj hcd hT hTp hpc))
      (.seq (.prim (.pop ci)) (varEndP ct cc j d T o hcj hcd hT hTo)))

/-- The cost of `varTyP` on `n` contexts and variable `i`. -/
def varTyCost (n i : Nat) : Nat := (i + 1) * (23 * n + 30)

/-- The states of the walk: `m` steps done. -/
def walkSt (cc ci : Fin K) (S : Lists K) (P : List (Nat × Nat)) (c i : Nat) (li lc : List Nat) (m : Nat) : Lists K :=
  (S.set cc (lc ++ [walkCtx P c m])).set ci (li ++ [i - m])

/-- The stacks of `varTyP`, all different: `ct cs ci cc j d T p o`. -/
abbrev VarStacks (ct cs ci cc j d T p o : Fin K) : Prop := [ct, cs, ci, cc, j, d, T, p, o].Nodup

theorem varStacks_up {ct cs ci cc j d T p o : Fin K} (hd : VarStacks ct cs ci cc j d T p o) :
    [ct, cc, j, d, T, p].Nodup :=
  hd.sublist (.cons_cons _ (.cons _ (.cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _ (.cons _ .slnil)))))))))

theorem varStacks_end {ct cs ci cc j d T p o : Fin K} (hd : VarStacks ct cs ci cc j d T p o) :
    [ct, cc, j, d, T, o].Nodup :=
  hd.sublist (.cons_cons _ (.cons _ (.cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _ (.cons _ (.cons_cons _ .slnil)))))))))

/-- One step of the walk, from a nonzero context. -/
theorem varUpP_step (ct cs ci cc j d T p o : Fin K) (hcj : cc ≠ j) (hcd : cc ≠ d) (hT : ct ≠ T) (hTp : T ≠ p)
    (hpc : p ≠ cc) (hd : VarStacks ct cs ci cc j d T p o) (S : Lists K) {tt P : List (Nat × Nat)}
    (hP : S ct = encPairs P) (hTe : S T = []) (hw : CTWF tt P) {c i : Nat} (hcl : c ≤ P.length)
    (li lc : List Nat) {m : Nat} (hm : m < i) (hz : walkCtx P c m ≠ 0) :
    NRuns (varUpP ct cc ci j d T p hcj hcd hT hTp hpc) (walkSt cc ci S P c i li lc m)
      (walkSt cc ci S P c i li lc (m + 1)) (23 * P.length + 22) := by
  have hup := varStacks_up hd
  simp only [VarStacks, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true] at hd
  have h₁ : ct ≠ ci := hd.1.2.1
  have h₂ : ct ≠ cc := hd.1.2.2.1
  have h₃ : ci ≠ cc := hd.2.2.1.1
  have h₄ : ci ≠ T := hd.2.2.1.2.2.2.1
  have h₅ : ci ≠ p := hd.2.2.1.2.2.2.2.1
  have h₆ : cc ≠ T := hd.2.2.2.1.2.2.1
  have hjd : j ≠ d := hd.2.2.2.2.1.1
  clear hd
  have h₇ := Ne.symm h₁; have h₈ := Ne.symm h₂; have h₉ := Ne.symm h₃; have h₁₀ := Ne.symm h₄
  have h₁₁ := Ne.symm h₅; have h₁₂ := Ne.symm h₆; have h₁₃ := Ne.symm hpc
  obtain ⟨w, hwe⟩ : ∃ w, walkCtx P c m = w + 1 := ⟨walkCtx P c m - 1, by omega⟩
  have hwl : w < P.length := by have := walkCtx_le hw c hcl m; omega
  let W := walkSt cc ci S P c i li lc m
  have hWc : W cc = lc ++ [w + 1] := by simp [W, walkSt, Lists.set, hwe, h₉]
  have x₁ := nruns_dec cc W hWc
  rw [Nat.add_sub_cancel] at x₁
  let W₁ := W.set cc (lc ++ [w])
  have hW₁ct : W₁ ct = encPairs P := by simp [W₁, W, walkSt, Lists.set, h₁, h₂, hP]
  have x₂ := entryP_runs ct cc j d T p hcj hcd (Ne.symm hjd) hT hTp false hup W₁ (lc := lc) (c := w)
    (v := P[w].1) (by simp [W₁]) (by simp [W₁, W, walkSt, Lists.set, h₁₀, h₁₂, hTe])
    (by rw [hW₁ct]; simpa using encPairs_fst P w hwl)
  have hW₁p : W₁ p = S p := by simp [W₁, W, walkSt, Lists.set, h₁₁, hpc]
  rw [hW₁p] at x₂
  let W₂ := W₁.set p (S p ++ [P[w].1])
  have x₃ := nruns_pop cc W₂ (l := lc) (v := w) (by simp [W₂, W₁, Lists.set, h₁₃])
  let W₃ := W₂.set cc lc
  have x₄ := nruns_mv p cc hpc W₃ (l := S p) (v := P[w].1) (by simp [W₃, W₂, Lists.set, hpc])
  have hW₃c : W₃ cc = lc := by simp [W₃]
  rw [hW₃c] at x₄
  let W₄ := (W₃.set cc (lc ++ [P[w].1])).set p (S p)
  have x₅ := nruns_dec ci W₄ (l := li) (v := i - m)
    (by simp [W₄, W₃, W₂, W₁, W, walkSt, Lists.set, h₃, h₅])
  have hnext : walkCtx P c (m + 1) = P[w].1 := by
    rw [walkCtx, hwe]; simp [upCtx, List.getElem?_eq_getElem hwl]
  have e : W₄.set ci (li ++ [i - m - 1]) = walkSt cc ci S P c i li lc (m + 1) := by
    simp only [walkSt, hnext, show i - (m + 1) = i - m - 1 by omega, W₄, W₃, W₂, W₁, W]
    funext x
    by_cases hx : x = ci
    · subst hx; simp [Lists.set, h₃, h₅]
    by_cases hy : x = cc
    · subst hy; simp [Lists.set, hx, h₁₃]
    by_cases hz : x = p
    · subst hz; simp [Lists.set, hx, hy]
    simp [Lists.set, hx, hy, hz]
  rw [e] at x₅
  rw [hW₁ct, encPairs_length] at x₂
  refine ((x₁.seq (x₂.seq (x₃.seq (x₄.seq x₅)))).iteF (by rw [hWc]; exact eval_zero_succ _ _)).mono ?_
  omega

theorem varTyCost_le (n i m : Nat) (hm : m ≤ i) : (m + 1) * (23 * n + 23) + 7 ≤ varTyCost n i := by
  have h₁ := Nat.mul_le_mul_right (23 * n + 23) (show m + 1 ≤ i + 1 by omega)
  have h₂ : (i + 1) * (23 * n + 30) = (i + 1) * (23 * n + 23) + (i + 1) * 7 := by
    rw [← Nat.mul_add]
  rw [varTyCost, h₂]; omega

/-- The first time the walk reaches `0`. -/
theorem walkCtx_first (P : List (Nat × Nat)) (c : Nat) :
    ∀ i, walkCtx P c i = 0 → ∃ m₀, m₀ ≤ i ∧ walkCtx P c m₀ = 0 ∧ ∀ m, m < m₀ → walkCtx P c m ≠ 0
  | 0, h => ⟨0, Nat.le_refl _, h, fun _ hm => absurd hm (Nat.not_lt_zero _)⟩
  | i + 1, h => by
    by_cases hi : walkCtx P c i = 0
    · obtain ⟨m₀, hm₀, h₀, hlt⟩ := walkCtx_first P c i hi
      exact ⟨m₀, by omega, h₀, hlt⟩
    · exact ⟨i + 1, Nat.le_refl _, h, fun m hm hz => hi (walkCtx_stuck P c hz i (by omega))⟩

section Run

variable (ct cs ci cc j d T p o : Fin K) (hsc : cs ≠ cc) (hcj : cc ≠ j) (hcd : cc ≠ d) (hT : ct ≠ T) (hTp : T ≠ p)
  (hpc : p ≠ cc) (hTo : T ≠ o)

/-- `varTyP` pushes the type of the variable, as `varTy`. -/
theorem varTyP_ok (hd : VarStacks ct cs ci cc j d T p o) (S : Lists K) {tt P : List (Nat × Nat)}
    (hP : S ct = encPairs P) (hTe : S T = []) (hw : CTWF tt P) {c i v : Nat} (hcl : c ≤ P.length)
    {ls li : List Nat} (hcs : S cs = ls ++ [c]) (hci : S ci = li ++ [i]) (hv : varTy P c i = some v) :
    NRuns (varTyP ct cs ci o cc j d T p hsc hcj hcd hT hTp hpc hTo) S ((S.set ci li).set o (S o ++ [v]))
      (varTyCost P.length i) := by
  have hend := varStacks_end hd
  have hd' := hd
  simp only [VarStacks, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true] at hd'
  have h₁ : ct ≠ ci := hd'.1.2.1
  have h₂ : ct ≠ cc := hd'.1.2.2.1
  have h₃ : ci ≠ cc := hd'.2.2.1.1
  have h₄ : ci ≠ T := hd'.2.2.1.2.2.2.1
  have h₅ : ci ≠ o := hd'.2.2.1.2.2.2.2.2
  have h₆ : cc ≠ T := hd'.2.2.2.1.2.2.1
  have h₇ : cc ≠ o := hd'.2.2.2.1.2.2.2.2
  have hjd : j ≠ d := hd'.2.2.2.2.1.1
  clear hd'
  rw [varTy_walk hw i c hcl] at hv
  split at hv
  · exact absurd hv (by simp)
  rename_i hz
  have hnz : ∀ m, m ≤ i → walkCtx P c m ≠ 0 := fun m hm h => hz (walkCtx_stuck P c h i hm)
  obtain ⟨w, hwe⟩ : ∃ w, walkCtx P c i = w + 1 := ⟨walkCtx P c i - 1, by omega⟩
  have hwl : w < P.length := by have := walkCtx_le hw c hcl i; omega
  rw [hwe, Nat.add_sub_cancel, List.getElem?_eq_getElem hwl] at hv
  simp only [Option.map_some, Option.some.injEq] at hv
  subst hv
  have x₁ := nruns_dup cs cc hsc S hcs
  let F := walkSt cc ci S P c i li (S cc)
  have hF0 : F 0 = S.set cc (S cc ++ [c]) := by
    simp only [F, walkSt, walkCtx, Nat.sub_zero]
    funext x
    by_cases hx : x = ci
    · subst hx; simp [Lists.set, h₃, hci]
    · simp [Lists.set, hx]
  have hFci : ∀ m, F m ci = li ++ [i - m] := fun m => by simp [F, walkSt]
  have hl := nruns_family_const (i := ci) (c := .pos) (p := varUpP ct cc ci j d T p hcj hcd hT hTp hpc) F i
    (23 * P.length + 22)
    (fun m hm => by rw [hFci, show i - m = (i - m - 1) + 1 by omega]; exact eval_pos_succ _ _)
    (by rw [hFci, Nat.sub_self]; exact eval_pos_zero _)
    (fun m hm => varUpP_step ct cs ci cc j d T p o hcj hcd hT hTp hpc hd S hP hTe hw hcl li (S cc) hm
      (hnz m (by omega)))
  rw [hF0] at hl
  have x₂ := nruns_pop ci (F i) (l := li) (v := 0) (by rw [hFci, Nat.sub_self])
  let G := (F i).set ci li
  have hGc : G cc = S cc ++ [w + 1] := by simp [G, F, walkSt, Lists.set, hwe, h₃.symm]
  have x₃ := nruns_dec cc G hGc
  rw [Nat.add_sub_cancel] at x₃
  let G₁ := G.set cc (S cc ++ [w])
  have hG₁ct : G₁ ct = encPairs P := by simp [G₁, G, F, walkSt, Lists.set, h₁, h₂, hP]
  have x₄ := entryP_runs ct cc j d T o hcj hcd (Ne.symm hjd) hT hTo true hend G₁ (lc := S cc) (c := w)
    (v := P[w].2) (by simp [G₁]) (by simp [G₁, G, F, walkSt, Lists.set, h₄.symm, h₆.symm, hTe])
    (by rw [hG₁ct]; simpa using encPairs_snd P w hwl)
  have hG₁o : G₁ o = S o := by simp [G₁, G, F, walkSt, Lists.set, h₅.symm, h₇.symm]
  rw [hG₁o, hG₁ct, encPairs_length] at x₄
  have x₅ := nruns_pop cc (G₁.set o (S o ++ [P[w].2])) (l := S cc) (v := w) (by simp [G₁, Lists.set, h₇])
  have e : (G₁.set o (S o ++ [P[w].2])).set cc (S cc) = (S.set ci li).set o (S o ++ [P[w].2]) := by
    simp only [G₁, G, F, walkSt]
    funext x
    by_cases hx : x = ci
    · subst hx; simp [Lists.set, h₃, h₅]
    by_cases hy : x = cc
    · subst hy; simp [Lists.set, hx, h₇]
    by_cases hz : x = o
    · subst hz; simp [Lists.set, hx, hy]
    simp [Lists.set, hx, hy, hz]
  rw [e] at x₅
  have xe := ((x₃.seq (x₄.seq x₅)).iteF (p := .halt false) (i := cc) (c := .zero) (by rw [hGc]; exact eval_zero_succ _ _))
  refine (x₁.seq (hl.seq (x₂.seq xe))).mono ?_
  have := varTyCost_le P.length i i (Nat.le_refl _)
  rw [Nat.succ_mul] at this
  try rw [show 23 * P.length + 22 + 1 = 23 * P.length + 23 by omega]
  omega

/-- `varTyP` stops rejecting where `varTy` fails. -/
theorem varTyP_fail (hd : VarStacks ct cs ci cc j d T p o) (S : Lists K) {tt P : List (Nat × Nat)}
    (hP : S ct = encPairs P) (hTe : S T = []) (hw : CTWF tt P) {c i : Nat} (hcl : c ≤ P.length)
    {ls li : List Nat} (hcs : S cs = ls ++ [c]) (hci : S ci = li ++ [i]) (hv : varTy P c i = none) :
    ∃ S', NHalts (varTyP ct cs ci o cc j d T p hsc hcj hcd hT hTp hpc hTo) S false S' (varTyCost P.length i) := by
  have hd' := hd
  simp only [VarStacks, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true] at hd'
  have h₃ : ci ≠ cc := hd'.2.2.1.1
  clear hd'
  have hz : walkCtx P c i = 0 := by
    rw [varTy_walk hw i c hcl] at hv
    split at hv
    · assumption
    · rename_i hne
      have := walkCtx_le hw c hcl i
      rw [List.getElem?_eq_getElem (by omega)] at hv
      simp at hv
  obtain ⟨m₀, hm₀, h₀, hlt⟩ := walkCtx_first P c i hz
  have x₁ := nruns_dup cs cc hsc S hcs
  let F := walkSt cc ci S P c i li (S cc)
  have hF0 : F 0 = S.set cc (S cc ++ [c]) := by
    simp only [F, walkSt, walkCtx, Nat.sub_zero]
    funext x
    by_cases hx : x = ci
    · subst hx; simp [Lists.set, h₃, hci]
    · simp [Lists.set, hx]
  have hFci : ∀ m, F m ci = li ++ [i - m] := fun m => by simp [F, walkSt]
  have hFcc : F m₀ cc = S cc ++ [0] := by simp [F, walkSt, Lists.set, h₀, h₃.symm]
  have hbody : ∀ m, m < m₀ → NRuns (varUpP ct cc ci j d T p hcj hcd hT hTp hpc) (F m) (F (m + 1))
      (23 * P.length + 22) := fun m hm =>
    varUpP_step ct cs ci cc j d T p o hcj hcd hT hTp hpc hd S hP hTe hw hcl li (S cc) (by omega) (hlt m hm)
  rcases Nat.lt_or_eq_of_le hm₀ with hm | rfl
  · -- the walk runs out inside the loop
    have hlast : NHalts (varUpP ct cc ci j d T p hcj hcd hT hTp hpc) (F m₀) false (F m₀) (23 * P.length + 22) :=
      ((nhalts_halt false (F m₀)).iteT (by rw [hFcc]; exact eval_zero_zero _)).mono (by omega)
    have hl := nhalts_family (i := ci) (c := .pos) F m₀ (23 * P.length + 22)
      (fun m hm' => by rw [hFci, show i - m = (i - m - 1) + 1 by omega]; exact eval_pos_succ _ _) hbody hlast
      m₀ 0 (by omega)
    rw [hF0] at hl
    refine ⟨F m₀, (x₁.seqH hl.seq).mono ?_⟩
    have := varTyCost_le P.length i m₀ hm₀
    try rw [show 23 * P.length + 22 + 1 = 23 * P.length + 23 by omega]
    omega
  · -- the walk runs out at the end
    have hl := nruns_family_const (i := ci) (c := .pos) (p := varUpP ct cc ci j d T p hcj hcd hT hTp hpc) F m₀
      (23 * P.length + 22)
      (fun m hm => by rw [hFci, show m₀ - m = (m₀ - m - 1) + 1 by omega]; exact eval_pos_succ _ _)
      (by rw [hFci, Nat.sub_self]; exact eval_pos_zero _) hbody
    rw [hF0] at hl
    have x₂ := nruns_pop ci (F m₀) (l := li) (v := 0) (by rw [hFci, Nat.sub_self])
    have hGc : ((F m₀).set ci li) cc = S cc ++ [0] := by rw [Lists.set_ne _ _ (Ne.symm h₃), hFcc]
    have xe := (nhalts_halt false ((F m₀).set ci li)).iteT
      (p := .halt false) (q := .seq (.prim (.dec cc)) (.seq (entryP ct cc j d T o hcj hcd hT hTo true) (.prim (.pop cc))))
      (i := cc) (c := .zero) (by rw [hGc]; exact eval_zero_zero _)
    refine ⟨_, (x₁.seqH (hl.seqH (x₂.seqH xe))).mono ?_⟩
    have := varTyCost_le P.length m₀ m₀ (Nat.le_refl _)
    rw [Nat.succ_mul] at this
    try rw [show 23 * P.length + 22 + 1 = 23 * P.length + 23 by omega]
    omega

end Run

end Shallot.MacroPeg.Mach
