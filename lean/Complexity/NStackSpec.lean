import Complexity.NStack
import Complexity.UnarySpec

/-!
# The translation of stack machines over numbers is correct

`nexec_compile`: a run of `p` in `t` steps whose states fit in `B` (`NFits`) is matched by a run of `p.compile` from
the encoded state, to the encoded outcome, within `t · ncost B` steps, every list staying below `B`.
-/

namespace Complexity

variable {K : Nat}

/-! ## The encoding -/

theorem encS_nil : encS [] = [] := rfl

theorem encS_snoc (l : List Nat) (v : Nat) : encS (l ++ [v]) = encS l ++ encN v := by
  simp [encS, List.flatMap_append]

theorem encS_snoc' (l : List Nat) (v : Nat) : encS (l ++ [v]) = (encS l ++ [2]) ++ List.replicate v 1 := by
  rw [encS_snoc, encN, List.append_assoc]; rfl

theorem lastSym_mark (l : List Nat) : lastSym (encS l ++ [2]) = 6 := lastSym_append _ _

theorem lastSym_ones (l : List Nat) (r : Nat) : lastSym (l ++ List.replicate (r + 1) 1) = 5 := by
  rw [List.replicate_succ', ← List.append_assoc, lastSym_append]

theorem sym_eval (c : NTest) (l : List Nat) : c.sym (lastSym (encS l)) = c.eval l := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', v, rfl⟩
  · cases c <;> rfl
  · rw [List.concat_eq_append, encS_snoc']
    cases v with
    | zero =>
      rw [List.replicate_zero, List.append_nil, lastSym_mark]
      cases c <;> simp [NTest.sym, NTest.eval]
    | succ v =>
      rw [lastSym_ones]
      cases c <;> simp [NTest.sym, NTest.eval]

theorem length_encS_snoc (l : List Nat) (v : Nat) : (encS (l ++ [v])).length = (encS l).length + v + 1 := by
  simp [encS_snoc']; omega

/-! ## Encoded states -/

theorem lift_ne_scratch (i : Fin K) : lift i ≠ scratch K := by
  intro h; have := congrArg Fin.val h; simp [lift, scratch] at this; omega

theorem lift_inj {i j : Fin K} (h : lift i = lift j) : i = j := by
  apply Fin.ext; have := congrArg Fin.val h; simpa [lift] using this

theorem encL_lift (S : Lists K) (i : Fin K) : encL S (lift i) = encS (S i) := by
  simp [encL, lift]

theorem encL_scratch (S : Lists K) : encL S (scratch K) = [] := by
  simp [encL, scratch]

theorem encL_set (S : Lists K) (i : Fin K) (l : List Nat) :
    encL (S.set i l) = (encL S).set (lift i) (encS l) := by
  funext x
  simp only [encL, Lists.set, lift]
  by_cases hx : x.val < K
  · by_cases hxi : x = i.castSucc
    · subst hxi; simp
    · have : (⟨x.val, hx⟩ : Fin K) ≠ i := fun e => hxi (by subst e; rfl)
      simp [hx, hxi, this]
  · have : x ≠ i.castSucc := fun e => hx (by subst e; simp)
    simp [hx, this]

theorem lenOK_encL {B : Nat} {S : Lists K} (h : NFits B S) : LenOK B (encL S) := by
  intro x
  simp only [encL]
  split
  · exact h.2 _
  · simpa using h.1

/-! ## A loop that runs through a family of states -/

theorem runs_family {k : Nat} {Q : Lists k → Prop} {i : Fin k} {c : Nat → Bool} {p : LProg k} (F : Nat → Lists k)
    (n T : Nat) (hQ : ∀ m, m ≤ n → Q (F m)) (htest : ∀ m, m < n → c (lastSym (F m i)) = true)
    (hstop : c (lastSym (F n i)) = false) (hbody : ∀ m, m < n → Runs Q p (F m) (F (m + 1)) T) :
    ∀ r m, m + r = n → Runs Q (.loop i c p) (F m) (F n) ((r + 1) * (T + 1))
  | 0, m, h => by
    obtain rfl : m = n := by omega
    exact ⟨1, by rw [Nat.zero_add, Nat.one_mul]; omega, .loopF (hQ m (by omega)) hstop⟩
  | r + 1, m, h => by
    obtain ⟨t₁, ht₁, hx₁⟩ := hbody m (by omega)
    obtain ⟨t₂, ht₂, hx₂⟩ := runs_family F n T hQ htest hstop hbody r (m + 1) (by omega)
    refine ⟨t₁ + 1 + t₂, ?_, .loopC (hQ m (by omega)) (htest m (by omega)) hx₁ hx₂⟩
    rw [Nat.add_mul (r + 1) 1, Nat.one_mul]; omega

/-! ## The primitives -/

theorem mapTop_snoc (f : Nat → Nat) (l : List Nat) (v : Nat) : mapTop f (l ++ [v]) = l ++ [f v] := by
  simp [mapTop]

theorem mapTop_nil (f : Nat → Nat) : mapTop f [] = [] := rfl

/-- Two lists of lists agree if they agree at `a`, `b`, `s` and elsewhere. -/
theorem lists_ext3 {k : Nat} {L L' : Lists k} (a b s : Fin k) (ha : L a = L' a) (hb : L b = L' b) (hs : L s = L' s)
    (ho : ∀ x, x ≠ a → x ≠ b → x ≠ s → L x = L' x) : L = L' := by
  funext x
  by_cases hxa : x = a
  · subst hxa; exact ha
  by_cases hxb : x = b
  · subst hxb; exact hb
  by_cases hxs : x = s
  · subst hxs; exact hs
  exact ho x hxa hxb hxs

theorem v_le {B : Nat} {S : Lists K} (hS : NFits B S) {i : Fin K} {l : List Nat} {v : Nat} (h : S i = l ++ [v]) :
    (encS l).length + v + 3 ≤ B := by
  have := hS.2 i; rw [h, length_encS_snoc] at this; omega

theorem ncost_ge {B : Nat} : B ≤ ncost B := by unfold ncost; omega

section Prims

variable {B : Nat} {S : Lists K}

theorem pushZ_runs (i : Fin K) (hS : NFits B S) (hS' : NFits B ((NPrim.pushZ i).apply S)) :
    Runs (LenOK B) (NPrim.pushZ i).compile (encL S) (encL ((NPrim.pushZ i).apply S)) (ncost B) := by
  have e : encL ((NPrim.pushZ i).apply S) = (encL S).set (lift i) (encL S (lift i) ++ [2]) := by
    simp [NPrim.apply, encL_set, encL_lift, encS_snoc, encN]
  rw [e]
  exact (runs_push (lenOK_encL hS) (e ▸ lenOK_encL hS')).mono (by unfold ncost; omega)

/-- On an empty stack a primitive leaves the state as it is. -/
theorem set_nil_self {S : Lists K} {i : Fin K} (h : S i = []) : S.set i [] = S := by
  rw [← h]; exact Lists.set_get_self S i

theorem inc_runs (i : Fin K) (hS : NFits B S) (hS' : NFits B ((NPrim.inc i).apply S)) :
    Runs (LenOK B) (NPrim.inc i).compile (encL S) (encL ((NPrim.inc i).apply S)) (ncost B) := by
  have hL := lenOK_encL hS
  rcases List.eq_nil_or_concat (S i) with h | ⟨l, v, h⟩
  · have e : (NPrim.inc i).apply S = S := by simp only [NPrim.apply, h, mapTop_nil]; exact set_nil_self h
    rw [e]
    exact (Runs.iteT hL (by rw [encL_lift, h]; rfl) (runs_skip _ hL)).mono (by unfold ncost; omega)
  · rw [List.concat_eq_append] at h
    have e : encL ((NPrim.inc i).apply S) = (encL S).set (lift i) (encL S (lift i) ++ [1]) := by
      simp only [NPrim.apply, h, mapTop_snoc, encL_set, encL_lift, encS_snoc', List.replicate_succ',
        List.append_assoc]
    rw [e]
    refine (Runs.iteF hL ?_ (runs_push hL (e ▸ lenOK_encL hS'))).mono (by unfold ncost; omega)
    rw [encL_lift, h, encS_snoc']
    cases v with
    | zero => rw [List.replicate_zero, List.append_nil, lastSym_mark]; rfl
    | succ v => rw [lastSym_ones]; rfl

theorem dec_runs (i : Fin K) (hS : NFits B S) (hS' : NFits B ((NPrim.dec i).apply S)) :
    Runs (LenOK B) (NPrim.dec i).compile (encL S) (encL ((NPrim.dec i).apply S)) (ncost B) := by
  have hL := lenOK_encL hS
  rcases List.eq_nil_or_concat (S i) with h | ⟨l, v, h⟩
  · have e : (NPrim.dec i).apply S = S := by simp only [NPrim.apply, h, mapTop_nil]; exact set_nil_self h
    rw [e]
    exact (Runs.iteF hL (by rw [encL_lift, h]; rfl) (runs_skip _ hL)).mono (by unfold ncost; omega)
  · rw [List.concat_eq_append] at h
    cases v with
    | zero =>
      have e : (NPrim.dec i).apply S = S := by
        simp only [NPrim.apply, h, mapTop_snoc, Nat.zero_sub]; rw [← h]; exact Lists.set_get_self S i
      rw [e]
      refine (Runs.iteF hL ?_ (runs_skip _ hL)).mono (by unfold ncost; omega)
      rw [encL_lift, h, encS_snoc', List.replicate_zero, List.append_nil, lastSym_mark]; rfl
    | succ v =>
      have e : encL ((NPrim.dec i).apply S) = (encL S).set (lift i) (encL S (lift i)).dropLast := by
        simp only [NPrim.apply, h, mapTop_snoc, Nat.add_sub_cancel, encL_set, encL_lift, encS_snoc',
          List.replicate_succ', ← List.append_assoc, List.dropLast_concat]
      rw [e]
      refine (Runs.iteT hL ?_ (runs_pop hL (e ▸ lenOK_encL hS'))).mono (by unfold ncost; omega)
      rw [encL_lift, h, encS_snoc', lastSym_ones]; rfl

theorem dropLast_ones (A : List Nat) (r : Nat) : (A ++ List.replicate (r + 1) 1).dropLast = A ++ List.replicate r 1 := by
  rw [List.replicate_succ', ← List.append_assoc, List.dropLast_concat]

theorem lastSym_A_ones (A : List Nat) {r : Nat} (hr : 0 < r) : lastSym (A ++ List.replicate r 1) = 5 := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  exact lastSym_ones A r

theorem pop_runs (i : Fin K) (hS : NFits B S) (hS' : NFits B ((NPrim.pop i).apply S)) :
    Runs (LenOK B) (NPrim.pop i).compile (encL S) (encL ((NPrim.pop i).apply S)) (ncost B) := by
  have hL := lenOK_encL hS
  rcases List.eq_nil_or_concat (S i) with h | ⟨l, v, h⟩
  · have e : (NPrim.pop i).apply S = S := by simp only [NPrim.apply, h, List.dropLast_nil]; exact set_nil_self h
    rw [e]
    have hs : lastSym (encL S (lift i)) = 3 := by rw [encL_lift, h]; rfl
    have h₁ : Runs (LenOK B) (.loop (lift i) (· == 5) (.pop (lift i))) (encL S) (encL S) 1 :=
      ⟨1, Nat.le_refl _, .loopF hL (by rw [hs]; rfl)⟩
    exact (h₁.seq (Runs.iteT hL (by rw [hs]; rfl) (runs_skip _ hL))).mono (by unfold ncost; omega)
  · rw [List.concat_eq_append] at h
    have hv := v_le hS h
    let L := encL S
    let A := encS l ++ [2]
    have hLi : L (lift i) = A ++ List.replicate v 1 := by simp only [L, A, encL_lift, h, encS_snoc']
    let F : Nat → Lists (K + 1) := fun m => L.set (lift i) (A ++ List.replicate (v - m) 1)
    have hF0 : F 0 = L := by simp only [F, Nat.sub_zero, ← hLi]; exact Lists.set_get_self L _
    have hlen : ∀ m, (A ++ List.replicate (v - m) 1).length + 2 ≤ B := fun m => by
      simp only [A, List.length_append, List.length_singleton, List.length_replicate]; omega
    have hQ : ∀ m, m ≤ v → LenOK B (F m) := fun m _ => lenOK_set hL _ (hlen m)
    have hloop := runs_family (Q := LenOK B) (i := lift i) (c := (· == 5)) (p := .pop (lift i)) F v 1 hQ
      (fun m hm => by simp only [F, Lists.set_same]; rw [lastSym_A_ones A (by omega)]; rfl)
      (by simp only [F, Lists.set_same, Nat.sub_self, List.replicate_zero, List.append_nil, A, lastSym_mark]; rfl)
      (fun m hm => by
        have e : (F m).set (lift i) ((F m) (lift i)).dropLast = F (m + 1) := by
          simp only [F, Lists.set_same, Lists.set_set_u]
          rw [show v - m = (v - (m + 1)) + 1 by omega, dropLast_ones]
        have := runs_pop (Q := LenOK B) (hQ m (by omega)) (by rw [e]; exact hQ (m + 1) (by omega))
        rw [e] at this; exact this) v 0 (by omega)
    rw [hF0] at hloop
    have hFv : F v = L.set (lift i) A := by simp only [F, Nat.sub_self, List.replicate_zero, List.append_nil]
    have e : encL ((NPrim.pop i).apply S) = (F v).set (lift i) ((F v) (lift i)).dropLast := by
      rw [hFv]
      simp only [NPrim.apply, h, List.dropLast_concat, encL_set, Lists.set_same, Lists.set_set_u, A, L]
    rw [e]
    have hpop := runs_pop (Q := LenOK B) (hQ v (Nat.le_refl _)) (by rw [← e]; exact lenOK_encL hS')
    have hite := Runs.iteF (i := lift i) (c := (· == 3)) (p := skipP (lift i)) (hQ v (Nat.le_refl _))
      (by rw [hFv]; simp only [Lists.set_same, A, lastSym_mark]; rfl) hpop
    refine (hloop.seq hite).mono ?_
    unfold ncost; have : (v + 1) * (1 + 1) = 2 * v + 2 := by omega
    omega

theorem dup_runs (i j : Fin K) (hij : i ≠ j) (hS : NFits B S) (hS' : NFits B ((NPrim.dup i j hij).apply S)) :
    Runs (LenOK B) (NPrim.dup i j hij).compile (encL S) (encL ((NPrim.dup i j hij).apply S)) (ncost B) := by
  have hL := lenOK_encL hS
  rcases List.eq_nil_or_concat (S i) with h | ⟨l, v, h⟩
  · have e : (NPrim.dup i j hij).apply S = S := by
      simp only [NPrim.apply, h, List.getLast?_nil, Option.toList_none, List.append_nil]
      exact Lists.set_get_self S j
    rw [e]
    exact (Runs.iteT hL (by rw [encL_lift, h]; rfl) (runs_skip _ hL)).mono (by unfold ncost; omega)
  rw [List.concat_eq_append] at h
  have hv := v_le hS h
  -- the three lists involved
  let a := lift i
  let b := lift j
  let sc := scratch K
  have hab : a ≠ b := fun e => hij (lift_inj e)
  have has : a ≠ sc := lift_ne_scratch i
  have hbs : b ≠ sc := lift_ne_scratch j
  let L := encL S
  let A := encS l ++ [2]
  have hLa : L a = A ++ List.replicate v 1 := by simp only [L, a, A, encL_lift, h, encS_snoc']
  have hLs : L sc = [] := encL_scratch S
  have hfinal := hS'.2 j
  simp only [NPrim.apply, h, List.getLast?_concat, Option.toList_some, Lists.set_same, length_encS_snoc] at hfinal
  have hLb : (L b).length + v + 3 ≤ B := by simp only [L, b, encL_lift]; omega
  -- phase 1: the ones of `a` to the scratch list
  let F : Nat → Lists (K + 1) := fun m => (L.set a (A ++ List.replicate (v - m) 1)).set sc (List.replicate m 1)
  have hF0 : F 0 = L := by
    simp only [F, Nat.sub_zero, List.replicate_zero, ← hLa, ← hLs, Lists.set_get_self]
  have hlenA : ∀ m, (A ++ List.replicate (v - m) 1).length + 2 ≤ B := fun m => by
    simp only [A, List.length_append, List.length_singleton, List.length_replicate]; omega
  have hQF : ∀ m, m ≤ v → LenOK B (F m) := fun m hm =>
    lenOK_set (lenOK_set hL _ (hlenA m)) _ (by simp only [List.length_replicate]; omega)
  have hFa : ∀ m, F m a = A ++ List.replicate (v - m) 1 := fun m => by
    simp only [F]; rw [Lists.set_ne _ _ has, Lists.set_same]
  have h1 := runs_family (Q := LenOK B) (i := a) (c := (· == 5)) (p := moveTop a sc) F v 2 hQF
    (fun m hm => by rw [hFa, lastSym_A_ones A (by omega)]; rfl)
    (by rw [hFa, Nat.sub_self, List.replicate_zero, List.append_nil]; simp only [A, lastSym_mark]; rfl)
    (fun m hm => by
      have hlast : (F m a).getLast? = some 1 := by
        rw [hFa, show v - m = (v - (m + 1)) + 1 by omega, List.replicate_succ', ← List.append_assoc,
          List.getLast?_concat]
      have e : (F m).moveTop a sc = F (m + 1) := by
        apply lists_ext3 a b sc
        · rw [moveTop_i, hFa, hFa, show v - m = (v - (m + 1)) + 1 by omega, dropLast_ones]
        · rw [moveTop_other hab.symm hbs]; simp only [F]
          rw [Lists.set_ne _ _ hbs, Lists.set_ne _ _ hab.symm, Lists.set_ne _ _ hbs, Lists.set_ne _ _ hab.symm]
        · rw [moveTop_j has, hlast]; simp only [F, Lists.set_same, Option.toList_some, List.replicate_succ']
        · intro x hxa _ hxs
          rw [moveTop_other hxa hxs]; simp only [F]
          rw [Lists.set_ne _ _ hxs, Lists.set_ne _ _ hxa, Lists.set_ne _ _ hxs, Lists.set_ne _ _ hxa]
      have hmid : LenOK B ((F m).set sc ((F m) sc ++ ((F m) a).getLast?.toList)) := by
        apply lenOK_set (hQF m (by omega))
        rw [hlast]; simp only [F, Lists.set_same, Option.toList_some, List.length_append, List.length_replicate,
          List.length_singleton]; omega
      have := runs_moveTop has (hQF m (by omega)) hmid (by rw [e]; exact hQF (m + 1) (by omega))
      rw [e] at this; exact this) v 0 (by omega)
  rw [hF0] at h1
  -- the mark of the copy
  let P := (F v).set b (F v b ++ [2])
  have hFb : F v b = L b := by simp only [F]; rw [Lists.set_ne _ _ hbs, Lists.set_ne _ _ hab.symm]
  have hQP : LenOK B P := lenOK_set (hQF v (Nat.le_refl _)) _ (by
    rw [hFb]; simp only [List.length_append, List.length_singleton]; omega)
  have h2 : Runs (LenOK B) (.push b 2) (F v) P 1 := runs_push (hQF v (Nat.le_refl _)) hQP
  -- phase 2: the ones back onto `a` and onto `b`
  let H : Nat → Lists (K + 1) := fun m =>
    ((P.set a (A ++ List.replicate m 1)).set b ((L b ++ [2]) ++ List.replicate m 1)).set sc
      (List.replicate (v - m) 1)
  have hHa : ∀ m, H m a = A ++ List.replicate m 1 := fun m => by
    simp only [H]; rw [Lists.set_ne _ _ has, Lists.set_ne _ _ hab, Lists.set_same]
  have hHb : ∀ m, H m b = (L b ++ [2]) ++ List.replicate m 1 := fun m => by
    simp only [H]; rw [Lists.set_ne _ _ hbs, Lists.set_same]
  have hHs : ∀ m, H m sc = List.replicate (v - m) 1 := fun m => by simp only [H, Lists.set_same]
  have hHo : ∀ m x, x ≠ a → x ≠ b → x ≠ sc → H m x = L x := fun m x hxa hxb hxs => by
    simp only [H, P, F]
    rw [Lists.set_ne _ _ hxs, Lists.set_ne _ _ hxb, Lists.set_ne _ _ hxa, Lists.set_ne _ _ hxb, Lists.set_ne _ _ hxs,
      Lists.set_ne _ _ hxa]
  have hH0 : H 0 = P := by
    apply lists_ext3 a b sc
    · rw [hHa]; simp only [P, F]
      rw [Lists.set_ne _ _ hab, Lists.set_ne _ _ has, Lists.set_same, Nat.sub_self]
    · rw [hHb]; simp only [P, Lists.set_same, hFb, List.replicate_zero, List.append_nil]
    · rw [hHs]; simp only [P, F]; rw [Lists.set_ne _ _ hbs.symm, Lists.set_same, Nat.sub_zero]
    · intro x hxa hxb hxs
      rw [hHo 0 x hxa hxb hxs]; simp only [P, F]
      rw [Lists.set_ne _ _ hxb, Lists.set_ne _ _ hxs, Lists.set_ne _ _ hxa]
  have hlenH : ∀ m, m ≤ v → LenOK B (H m) := fun m hm => by
    refine lenOK_set (lenOK_set (lenOK_set hQP _ ?_) _ ?_) _ ?_
    · simp only [A, List.length_append, List.length_singleton, List.length_replicate]; omega
    · simp only [List.length_append, List.length_singleton, List.length_replicate]; omega
    · simp only [List.length_replicate]; omega
  have h3 := runs_family (Q := LenOK B) (i := sc) (c := (· == 5))
    (p := .seq (.copy sc a) (.seq (.copy sc b) (.pop sc))) H v 3 hlenH
    (fun m hm => by rw [hHs, show List.replicate (v - m) 1 = [] ++ List.replicate (v - m) 1 from rfl,
      lastSym_A_ones [] (by omega)]; rfl)
    (by rw [hHs, Nat.sub_self]; rfl)
    (fun m hm => by
      have hlast : (H m sc).getLast? = some 1 := by
        rw [hHs, show v - m = (v - (m + 1)) + 1 by omega, List.replicate_succ', List.getLast?_concat]
      let H₁ := (H m).set a (H m a ++ [1])
      let H₂ := H₁.set b (H₁ b ++ [1])
      have hH₁s : H₁ sc = H m sc := by simp only [H₁]; rw [Lists.set_ne _ _ has.symm]
      have hH₂s : H₂ sc = H m sc := by simp only [H₂]; rw [Lists.set_ne _ _ hbs.symm, hH₁s]
      have hH₁b : H₁ b = H m b := by simp only [H₁]; rw [Lists.set_ne _ _ hab.symm]
      have e₃ : H₂.set sc (H₂ sc).dropLast = H (m + 1) := by
        apply lists_ext3 a b sc
        · rw [Lists.set_ne _ _ has, show H₂ a = H₁ a by simp only [H₂]; rw [Lists.set_ne _ _ hab]]
          simp only [H₁, Lists.set_same]; rw [hHa, hHa, List.replicate_succ', List.append_assoc]
        · rw [Lists.set_ne _ _ hbs]; simp only [H₂, Lists.set_same]
          rw [hH₁b, hHb, hHb, List.replicate_succ', List.append_assoc]
        · rw [Lists.set_same, hH₂s, hHs, hHs, show v - m = (v - (m + 1)) + 1 by omega,
            show List.replicate (v - (m + 1) + 1) 1 = [] ++ List.replicate (v - (m + 1) + 1) 1 from rfl, dropLast_ones]
          rfl
        · intro x hxa hxb hxs
          rw [Lists.set_ne _ _ hxs, hHo (m + 1) x hxa hxb hxs]
          simp only [H₂, H₁]; rw [Lists.set_ne _ _ hxb, Lists.set_ne _ _ hxa, hHo m x hxa hxb hxs]
      have hQ₁ : LenOK B H₁ := lenOK_set (hlenH m (by omega)) _ (by
        rw [hHa]; simp only [A, List.length_append, List.length_singleton, List.length_replicate]; omega)
      have hQ₂ : LenOK B H₂ := lenOK_set hQ₁ _ (by
        rw [hH₁b, hHb]; simp only [List.length_append, List.length_singleton, List.length_replicate]; omega)
      have r₁ : Runs (LenOK B) (.copy sc a) (H m) H₁ 1 := by
        have := runs_copy (Q := LenOK B) has.symm (hlenH m (by omega)) (by rw [hlast]; exact hQ₁)
        rw [hlast] at this; exact this
      have r₂ : Runs (LenOK B) (.copy sc b) H₁ H₂ 1 := by
        have := runs_copy (Q := LenOK B) hbs.symm hQ₁ (by rw [hH₁s, hlast]; exact hQ₂)
        rw [hH₁s, hlast] at this; exact this
      have r₃ := runs_pop (Q := LenOK B) (i := sc) hQ₂ (by rw [e₃]; exact hlenH (m + 1) (by omega))
      rw [e₃] at r₃
      exact (r₁.seq (r₂.seq r₃)).mono (by omega)) v 0 (by omega)
  rw [hH0] at h3
  have hend : H v = encL ((NPrim.dup i j hij).apply S) := by
    simp only [NPrim.apply, h, List.getLast?_concat, Option.toList_some]
    rw [encL_set]
    apply lists_ext3 a b sc
    · rw [hHa, Lists.set_ne _ _ hab]; exact hLa.symm
    · rw [hHb, Lists.set_same, encS_snoc']; simp only [L, b, encL_lift]
    · rw [hHs, Nat.sub_self, Lists.set_ne _ _ hbs.symm]; exact hLs.symm
    · intro x hxa hxb hxs; rw [hHo v x hxa hxb hxs, Lists.set_ne _ _ hxb]
  rw [← hend]
  have hite := Runs.iteF (i := a) (c := (· == 3)) (p := skipP a) hL
    (by
      have hne : L a ≠ [] := by rw [hLa]; simp [A]
      have h3' := mt lastSym_eq_three.1 hne
      show (lastSym (L a) == 3) = false
      simpa using h3')
    ((h1.seq (h2.seq h3)))
  refine hite.mono ?_
  unfold ncost
  have : (v + 1) * (2 + 1) + (1 + (v + 1) * (3 + 1)) + 1 = 7 * v + 9 := by
    simp only [Nat.add_mul, Nat.one_mul]; omega
  omega

theorem prim_runs (a : NPrim K) (hS : NFits B S) (hS' : NFits B (a.apply S)) :
    Runs (LenOK B) a.compile (encL S) (encL (a.apply S)) (ncost B) := by
  cases a with
  | pushZ i => exact pushZ_runs i hS hS'
  | inc i => exact inc_runs i hS hS'
  | dec i => exact dec_runs i hS hS'
  | pop i => exact pop_runs i hS hS'
  | dup i j hij => exact dup_runs i j hij hS hS'

end Prims

/-! ## The translation -/

theorem one_le_ncost (B : Nat) : 1 ≤ ncost B := by unfold ncost; omega

/-- **The translation is correct**: a run of `p` within `t` steps whose states fit in `B` is matched by a run of
`p.compile` within `t · ncost B` steps, every list of which fits in `B`. -/
theorem nexec_compile {Q : Lists K → Prop} {B : Nat} (hQ : ∀ S, Q S → NFits B S) :
    ∀ {p : NProg K} {S : Lists K} {t : Nat} {o : LOutcome K}, NExec Q p S t o →
      ∃ t', t' ≤ t * ncost B ∧ LExec (LenOK B) p.compile (encL S) t' (encO o) := by
  have hc := one_le_ncost B
  intro p S t o h
  induction h with
  | prim hS hS' =>
    obtain ⟨t', ht', hx⟩ := prim_runs _ (hQ _ hS) (hQ _ hS')
    exact ⟨t', by omega, hx⟩
  | halt hS => exact ⟨1, by omega, .halt (lenOK_encL (hQ _ hS))⟩
  | seqC _ _ ih₁ ih₂ =>
    obtain ⟨t₁', h₁, x₁⟩ := ih₁
    obtain ⟨t₂', h₂, x₂⟩ := ih₂
    exact ⟨t₁' + t₂', by rw [Nat.add_mul]; omega, .seqC x₁ x₂⟩
  | seqS _ ih =>
    obtain ⟨t', h', x⟩ := ih
    exact ⟨t', h', .seqS x⟩
  | iteT hS hc' _ ih =>
    obtain ⟨t', h', x⟩ := ih
    refine ⟨t' + 1, by rw [Nat.add_mul, Nat.one_mul]; omega,
      .iteT (lenOK_encL (hQ _ hS)) (by rw [encL_lift, sym_eval]; exact hc') x⟩
  | iteF hS hc' _ ih =>
    obtain ⟨t', h', x⟩ := ih
    refine ⟨t' + 1, by rw [Nat.add_mul, Nat.one_mul]; omega,
      .iteF (lenOK_encL (hQ _ hS)) (by rw [encL_lift, sym_eval]; exact hc') x⟩
  | loopF hS hc' =>
    exact ⟨1, by omega, .loopF (lenOK_encL (hQ _ hS)) (by rw [encL_lift, sym_eval]; exact hc')⟩
  | loopC hS hc' _ _ ih₁ ih₂ =>
    obtain ⟨t₁', h₁, x₁⟩ := ih₁
    obtain ⟨t₂', h₂, x₂⟩ := ih₂
    refine ⟨t₁' + 1 + t₂', by rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega,
      .loopC (lenOK_encL (hQ _ hS)) (by rw [encL_lift, sym_eval]; exact hc') x₁ x₂⟩
  | loopS hS hc' _ ih =>
    obtain ⟨t', h', x⟩ := ih
    refine ⟨t' + 1, by rw [Nat.add_mul, Nat.one_mul]; omega,
      .loopS (lenOK_encL (hQ _ hS)) (by rw [encL_lift, sym_eval]; exact hc') x⟩

end Complexity
