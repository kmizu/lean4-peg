import Shallot.Peg.Undecidable.MachSpec
import MacroPeg.HigherOrder.KExp.DiagLayout
import Complexity.NTable

/-!
# A kit for the cards stage

Programs of the cards stage are verified without step bounds (`Reach`). Most of them only push numbers onto one
stack and leave every other stack as it was (`Pushes`):
* `pushE t s e` pushes the value of a linear expression `e` (a sum of tops of stacks plus a constant) onto `t`,
  `s` being scratch (`pushE_pushes`); `pushEs` pushes a list of them;
* `letP X p body` computes a value onto `X`, runs `body` and pops `X` (`letP_pushes`);
* `forP X Y s lim body` runs `body` for `j < lim` with `j` on top of `X` (`forP_pushes`).
-/

namespace Shallot

open Complexity

namespace MC

variable {K : Nat}

/-! ## Reaching a state -/

/-- The program continues from `S` in `S'`, within some number of steps. -/
def Reach (p : NProg K) (S S' : Lists K) : Prop := ∃ c, NRuns p S S' c

theorem Reach.of {p : NProg K} {S S' : Lists K} {c : Nat} (h : NRuns p S S' c) : Reach p S S' := ⟨c, h⟩

theorem Reach.seq {p q : NProg K} {S S₁ S₂ : Lists K} (h₁ : Reach p S S₁) (h₂ : Reach q S₁ S₂) :
    Reach (.seq p q) S S₂ :=
  let ⟨_, x₁⟩ := h₁; let ⟨_, x₂⟩ := h₂; ⟨_, x₁.seq x₂⟩

theorem Reach.iteT {i : Fin K} {c : NTest} {p q : NProg K} {S S' : Lists K} (hc : c.eval (S i) = true)
    (h : Reach p S S') : Reach (.ite i c p q) S S' :=
  let ⟨_, x⟩ := h; ⟨_, x.iteT hc⟩

theorem Reach.iteF {i : Fin K} {c : NTest} {p q : NProg K} {S S' : Lists K} (hc : c.eval (S i) = false)
    (h : Reach q S S') : Reach (.ite i c p q) S S' :=
  let ⟨_, x⟩ := h; ⟨_, x.iteF hc⟩

theorem reach_prim (a : NPrim K) (S : Lists K) : Reach (.prim a) S (a.apply S) := ⟨1, nruns_prim a S⟩

theorem Reach.cast {p : NProg K} {S S' S'' : Lists K} (h : Reach p S S') (e : S' = S'') : Reach p S S'' := e ▸ h

/-- A loop through a family of states. -/
theorem reach_family_gen {i : Fin K} {c : NTest} {p : NProg K} (F : Nat → Lists K) (n : Nat)
    (htest : ∀ m, m < n → c.eval (F m i) = true) (hstop : c.eval (F n i) = false)
    (hbody : ∀ m, m < n → Reach p (F m) (F (m + 1))) :
    ∀ r m, m + r = n → Reach (.loop i c p) (F m) (F n)
  | 0, m, h => by
    obtain rfl : m = n := by omega
    exact ⟨1, nruns_loop_exit hstop⟩
  | r + 1, m, h => by
    obtain ⟨_, t₁, _, x₁⟩ := hbody m (by omega)
    obtain ⟨_, t₂, _, x₂⟩ := reach_family_gen F n htest hstop hbody r (m + 1) (by omega)
    exact ⟨t₁ + 1 + t₂, t₁ + 1 + t₂, Nat.le_refl _, .loopC trivial (htest m (by omega)) x₁ x₂⟩

theorem reach_family {i : Fin K} {c : NTest} {p : NProg K} (F : Nat → Lists K) (n : Nat)
    (htest : ∀ m, m < n → c.eval (F m i) = true) (hstop : c.eval (F n i) = false)
    (hbody : ∀ m, m < n → Reach p (F m) (F (m + 1))) : Reach (.loop i c p) (F 0) (F n) :=
  reach_family_gen F n htest hstop hbody n 0 (by omega)

/-! ## Tests and tops -/

theorem eval_pos_snoc (l : List Nat) (v : Nat) : NTest.pos.eval (l ++ [v]) = decide (0 < v) := by
  cases v <;> simp [NTest.eval]

theorem eval_zero_snoc (l : List Nat) (v : Nat) : NTest.zero.eval (l ++ [v]) = decide (v = 0) := by
  cases v <;> simp [NTest.eval]

/-- The top of a stack (`0` when empty). -/
def tv (S : Lists K) (v : Fin K) : Nat := (S v).getLast?.getD 0

theorem tv_snoc {S : Lists K} {v : Fin K} {l : List Nat} {x : Nat} (h : S v = l ++ [x]) : tv S v = x := by
  simp [tv, h]

theorem tv_set_ne (S : Lists K) {v t : Fin K} (h : v ≠ t) (x : List Nat) : tv (S.set t x) v = tv S v := by
  simp only [tv, Lists.set_ne _ _ h]

/-- `v` is the top of `X`. -/
def Top (S : Lists K) (X : Fin K) (v : Nat) : Prop := ∃ l, S X = l ++ [v]

theorem Top.tv {S : Lists K} {X : Fin K} {v : Nat} (h : Top S X v) : tv S X = v :=
  let ⟨_, h⟩ := h; tv_snoc h

theorem Top.set_ne {S : Lists K} {X Y : Fin K} {v : Nat} (h : Top S X v) (hXY : X ≠ Y) (x : List Nat) :
    Top (S.set Y x) X v := by
  obtain ⟨l, h⟩ := h; exact ⟨l, by rw [Lists.set_ne _ _ hXY, h]⟩

theorem Top.set_same (S : Lists K) (X : Fin K) (l : List Nat) (v : Nat) : Top (S.set X (l ++ [v])) X v :=
  ⟨l, Lists.set_same _ _ _⟩

/-! ## Pushing onto one stack -/

/-- The program pushes `xs` onto `t` and leaves every other stack as it was. -/
def Pushes (t : Fin K) (p : NProg K) (S : Lists K) (xs : List Nat) : Prop := Reach p S (S.set t (S t ++ xs))

theorem pushes_seq {t : Fin K} {p q : NProg K} {S : Lists K} {xs ys : List Nat} (h₁ : Pushes t p S xs)
    (h₂ : Pushes t q (S.set t (S t ++ xs)) ys) : Pushes t (.seq p q) S (xs ++ ys) := by
  have := h₁.seq h₂
  unfold Pushes
  rw [Lists.set_same, Lists.set_set_u, List.append_assoc] at this
  exact this

theorem Pushes.cast {t : Fin K} {p : NProg K} {S : Lists K} {xs ys : List Nat} (h : Pushes t p S xs)
    (e : xs = ys) : Pushes t p S ys := e ▸ h

theorem Pushes.iteT {t i : Fin K} {c : NTest} {p q : NProg K} {S : Lists K} {xs : List Nat}
    (hc : c.eval (S i) = true) (h : Pushes t p S xs) : Pushes t (.ite i c p q) S xs := Reach.iteT hc h

theorem Pushes.iteF {t i : Fin K} {c : NTest} {p q : NProg K} {S : Lists K} {xs : List Nat}
    (hc : c.eval (S i) = false) (h : Pushes t q S xs) : Pushes t (.ite i c p q) S xs := Reach.iteF hc h

theorem reach_skip (s : Fin K) (S : Lists K) : Reach (nskip s) S S := ⟨2, nruns_skip s S⟩

theorem pushes_skip (t s : Fin K) (S : Lists K) : Pushes t (nskip s) S [] := by
  unfold Pushes; rw [List.append_nil, Lists.set_get_self]; exact reach_skip s S

/-! ## Linear expressions -/

/-- A sum of tops of stacks plus a constant. -/
structure LinE (K : Nat) where
  vs : List (Fin K)
  c : Nat

def LinE.ev (S : Lists K) (e : LinE K) : Nat := (e.vs.map (tv S)).sum + e.c

/-- The variables of `e` avoid `t`. -/
def LinE.Avoid (e : LinE K) (t : Fin K) : Prop := ∀ v ∈ e.vs, v ≠ t

instance (e : LinE K) (t : Fin K) : Decidable (e.Avoid t) := by unfold LinE.Avoid; infer_instance

theorem map_tv_set {S : Lists K} {t : Fin K} (x : List Nat) :
    ∀ (vs : List (Fin K)), (∀ v ∈ vs, v ≠ t) → vs.map (tv (S.set t x)) = vs.map (tv S)
  | [], _ => rfl
  | v :: vs, h => by
    simp only [List.map_cons]
    rw [tv_set_ne S (h v (by simp)), map_tv_set x vs (fun v' h' => h v' (by simp [h']))]

theorem LinE.ev_set {S : Lists K} {t : Fin K} {e : LinE K} (h : e.Avoid t) (x : List Nat) :
    e.ev (S.set t x) = e.ev S := by
  simp only [LinE.ev, map_tv_set x e.vs h]

/-- Copy the top of `i` onto `j` (nothing when `i = j`). -/
def dupD (i j : Fin K) : NProg K := if h : i = j then nskip j else .prim (.dup i j h)

def addVar (v s t : Fin K) : NProg K := .seq (dupD v s) (addTo s t)

def addVars (s t : Fin K) : List (Fin K) → NProg K
  | [] => nskip t
  | v :: vs => .seq (addVar v s t) (addVars s t vs)

def incN (t : Fin K) : Nat → NProg K
  | 0 => nskip t
  | c + 1 => .seq (incN t c) (.prim (.inc t))

def pushE (t s : Fin K) (e : LinE K) : NProg K := .seq (.prim (.pushZ t)) (.seq (addVars s t e.vs) (incN t e.c))

def pushEs (t s : Fin K) : List (LinE K) → NProg K
  | [] => nskip t
  | e :: es => .seq (pushE t s e) (pushEs t s es)

theorem reach_addVar {v s t : Fin K} (hvs : v ≠ s) (_hvt : v ≠ t) (hst : s ≠ t) (S : Lists K) (hs : S s = [])
    {l : List Nat} {b : Nat} (ht : S t = l ++ [b]) : Reach (addVar v s t) S (S.set t (l ++ [b + tv S v])) := by
  rcases List.eq_nil_or_concat (S v) with h | ⟨lv, x, h⟩
  · have e₁ : (NPrim.dup v s hvs).apply S = S := by
      simp only [NPrim.apply, h, hs, List.getLast?_nil, Option.toList_none, List.append_nil]
      rw [← hs, Lists.set_get_self]
    have d₁ : Reach (dupD v s) S S := by
      unfold dupD; rw [dif_neg hvs]; exact (reach_prim _ S).cast e₁
    have d₂ : Reach (.loop s .pos (.seq (.prim (.dec s)) (.prim (.inc t)))) S S :=
      ⟨1, nruns_loop_exit (by rw [hs]; rfl)⟩
    have d₃ : Reach (.prim (.pop s)) S S := by
      refine (reach_prim _ S).cast ?_
      simp only [NPrim.apply, hs, List.dropLast_nil]; rw [← hs, Lists.set_get_self]
    have htv : tv S v = 0 := by simp [tv, h]
    refine (d₁.seq (d₂.seq d₃)).cast ?_
    rw [htv, Nat.add_zero, ← ht, Lists.set_get_self]
  · rw [List.concat_eq_append] at h
    have d₁ : Reach (dupD v s) S (S.set s (S s ++ [x])) := by
      unfold dupD; rw [dif_neg hvs]; exact Reach.of (nruns_dup v s hvs S h)
    rw [hs, List.nil_append] at d₁
    have d₂ := nruns_addTo s t hst (S.set s [x]) (l := []) (l' := l) (a := x) (b := b) (by simp)
      (by rw [Lists.set_ne _ _ (Ne.symm hst), ht])
    have htv : tv S v = x := tv_snoc h
    refine (d₁.seq (Reach.of d₂)).cast ?_
    rw [htv, Lists.set_set_u, ← hs, Lists.set_get_self]

theorem reach_addVars {s t : Fin K} (hst : s ≠ t) :
    ∀ (vs : List (Fin K)), (∀ v ∈ vs, v ≠ s ∧ v ≠ t) → ∀ (S : Lists K), S s = [] → ∀ (l : List Nat) (b : Nat),
      S t = l ++ [b] → Reach (addVars s t vs) S (S.set t (l ++ [b + (vs.map (tv S)).sum]))
  | [], _, S, _, l, b, ht => by
    refine (reach_skip t S).cast ?_
    simp only [List.map_nil, List.sum_nil, Nat.add_zero]; rw [← ht, Lists.set_get_self]
  | v :: vs, h, S, hs, l, b, ht => by
    have hv := h v (by simp)
    have d₁ := reach_addVar hv.1 hv.2 hst S hs ht
    have d₂ := reach_addVars hst vs (fun v' h' => h v' (by simp [h'])) (S.set t (l ++ [b + tv S v]))
      (by rw [Lists.set_ne _ _ hst, hs]) l (b + tv S v) (by rw [Lists.set_same])
    rw [map_tv_set _ vs (fun v' h' => (h v' (by simp [h'])).2), Lists.set_set_u] at d₂
    refine (d₁.seq d₂).cast ?_
    simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

theorem reach_incN (t : Fin K) : ∀ (c : Nat) (S : Lists K) (l : List Nat) (b : Nat), S t = l ++ [b] →
    Reach (incN t c) S (S.set t (l ++ [b + c]))
  | 0, S, l, b, ht => by
    refine (reach_skip t S).cast ?_
    rw [Nat.add_zero, ← ht, Lists.set_get_self]
  | c + 1, S, l, b, ht => by
    have d₁ := reach_incN t c S l b ht
    have d₂ := Reach.of (nruns_inc t (S.set t (l ++ [b + c])) (l := l) (v := b + c) (by simp))
    rw [Lists.set_set_u] at d₂
    exact d₁.seq d₂

theorem pushE_pushes {t s : Fin K} (hst : s ≠ t) {e : LinE K} (hes : e.Avoid s) (het : e.Avoid t) (S : Lists K)
    (hs : S s = []) : Pushes t (pushE t s e) S [e.ev S] := by
  have d₁ := reach_prim (.pushZ t) S
  simp only [NPrim.apply] at d₁
  have d₂ := reach_addVars hst e.vs (fun v hv => ⟨hes v hv, het v hv⟩) (S.set t (S t ++ [0]))
    (by rw [Lists.set_ne _ _ hst, hs]) (S t) 0 (by rw [Lists.set_same])
  rw [map_tv_set _ e.vs het, Lists.set_set_u] at d₂
  have d₃ := reach_incN t e.c (S.set t (S t ++ [0 + (e.vs.map (tv S)).sum])) (S t) _ (by rw [Lists.set_same])
  rw [Lists.set_set_u] at d₃
  refine (d₁.seq (d₂.seq d₃)).cast ?_
  simp [LinE.ev]

/-- Every expression avoids `t`. -/
def AllAvoid (es : List (LinE K)) (t : Fin K) : Prop := ∀ e ∈ es, e.Avoid t

instance (es : List (LinE K)) (t : Fin K) : Decidable (AllAvoid es t) := by unfold AllAvoid; infer_instance

theorem pushEs_pushes {t s : Fin K} (hst : s ≠ t) :
    ∀ (es : List (LinE K)), AllAvoid es s → AllAvoid es t → ∀ (S : Lists K), S s = [] →
      Pushes t (pushEs t s es) S (es.map (LinE.ev S))
  | [], _, _, S, _ => pushes_skip t t S
  | e :: es, h₁, h₂, S, hs => by
    have d₁ := pushE_pushes hst (h₁ e (by simp)) (h₂ e (by simp)) S hs
    have d₂ := pushEs_pushes hst es (fun e' h' => h₁ e' (by simp [h'])) (fun e' h' => h₂ e' (by simp [h']))
      (S.set t (S t ++ [e.ev S])) (by rw [Lists.set_ne _ _ hst, hs])
    have e₂ : es.map (LinE.ev (S.set t (S t ++ [e.ev S]))) = es.map (LinE.ev S) :=
      List.map_congr_left (fun e' h' => LinE.ev_set (h₂ e' (by simp [h'])) _)
    rw [e₂] at d₂
    exact pushes_seq d₁ d₂

/-! ## Computing a value for a while -/

/-- Compute a value onto `X`, run `body`, pop `X`. -/
def letP (X : Fin K) (p body : NProg K) : NProg K := .seq p (.seq body (.prim (.pop X)))

theorem letP_pushes {t X : Fin K} (hXt : X ≠ t) {p body : NProg K} {S : Lists K} {v : Nat} {xs : List Nat}
    (hp : Pushes X p S [v]) (hb : Pushes t body (S.set X (S X ++ [v])) xs) : Pushes t (letP X p body) S xs := by
  have d₃ := Reach.of (nruns_pop X ((S.set X (S X ++ [v])).set t ((S.set X (S X ++ [v])) t ++ xs)) (l := S X)
    (v := v) (by rw [Lists.set_ne _ _ hXt, Lists.set_same]))
  refine hp.seq (hb.seq d₃) |>.cast ?_
  rw [Lists.set_ne _ _ (Ne.symm hXt)]
  funext x
  simp only [Lists.set]
  by_cases h1 : x = X
  · subst h1; simp [hXt]
  · simp [h1]

/-- Push `e - 1`. -/
def predE (t s : Fin K) (e : LinE K) : NProg K := .seq (pushE t s e) (.prim (.dec t))

theorem predE_pushes {t s : Fin K} (hst : s ≠ t) {e : LinE K} (hes : e.Avoid s) (het : e.Avoid t) (S : Lists K)
    (hs : S s = []) : Pushes t (predE t s e) S [e.ev S - 1] := by
  have d₁ := pushE_pushes hst hes het S hs
  have d₂ := Reach.of (nruns_dec t (S.set t (S t ++ [e.ev S])) (l := S t) (v := e.ev S) (by simp))
  rw [Lists.set_set_u] at d₂
  exact d₁.seq d₂

/-- Push entry `e` of the table `tab` on `o` (`cc` and `tmp` are scratch). -/
def peekE (tab tmp cc o s : Fin K) (h₁ : tab ≠ tmp) (h₂ : tmp ≠ o) (e : LinE K) : NProg K :=
  .seq (pushE cc s e) (peekAt tab tmp cc o h₁ h₂)

theorem peekE_pushes {tab tmp cc o s : Fin K} (h₁ : tab ≠ tmp) (h₂ : tmp ≠ o) (hd : [tab, tmp, cc, o].Nodup)
    (hsc : s ≠ cc) {e : LinE K} (hes : e.Avoid s) (hec : e.Avoid cc) (S : Lists K) (hs : S s = [])
    (ht : S tmp = []) (hk : e.ev S < (S tab).length) :
    Pushes o (peekE tab tmp cc o s h₁ h₂ e) S [(S tab).getD (e.ev S) 0] := by
  have hnd := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨_, htc, _⟩, ⟨htc', _⟩, hco, _⟩ := hnd
  have d₁ := pushE_pushes hsc hes hec S hs
  have d₂ := Reach.of (nruns_peekAt tab tmp cc o h₁ h₂ hd (S.set cc (S cc ++ [e.ev S]))
    (by rw [Lists.set_ne _ _ htc', ht]) (lc := S cc) (k := e.ev S) (by simp)
    (by rw [Lists.set_ne _ _ htc]; exact hk))
  refine (d₁.seq d₂).cast ?_
  rw [Lists.set_set_u, Lists.set_get_self, Lists.set_ne _ _ (Ne.symm hco)]
  have hT : (S.set cc (S cc ++ [e.ev S])) tab = S tab := Lists.set_ne _ _ htc
  simp [hT, List.getD_eq_getElem?_getD, hk]

/-! ## Counting loops -/

/-- Run `body` for `j = 0, 1, …, lim - 1`, with `j` on top of `X` and `lim - j` on top of `Y`. -/
def forP (X Y s : Fin K) (lim : LinE K) (body : NProg K) : NProg K :=
  .seq (.prim (.pushZ X)) (.seq (pushE Y s lim)
    (.seq (.loop Y .pos (.seq body (.seq (.prim (.inc X)) (.prim (.dec Y))))) (.seq (.prim (.pop X)) (.prim (.pop Y)))))

theorem forP_pushes {t X Y s : Fin K} {lim : LinE K} {body : NProg K} (hXY : X ≠ Y) (htX : t ≠ X) (htY : t ≠ Y)
    (hsY : s ≠ Y) (hsX : s ≠ X) (hls : lim.Avoid s) (hlY : lim.Avoid Y) (hlX : lim.Avoid X) (S : Lists K)
    (hs : S s = []) (g : Nat → List Nat)
    (hbody : ∀ j, j < lim.ev S → ∀ o, Pushes t body (((S.set t o).set X (S X ++ [j])).set Y (S Y ++ [lim.ev S - j]))
      (g j)) :
    Pushes t (forP X Y s lim body) S ((List.range (lim.ev S)).flatMap g) := by
  let k := lim.ev S
  have d₁ := reach_prim (.pushZ X) S
  simp only [NPrim.apply] at d₁
  have d₂ := pushE_pushes hsY hls hlY (S.set X (S X ++ [0])) (by rw [Lists.set_ne _ _ hsX, hs])
  unfold Pushes at d₂
  rw [LinE.ev_set hlX, Lists.set_ne _ _ (Ne.symm hXY)] at d₂
  let F : Nat → Lists K := fun j =>
    ((S.set t (S t ++ (List.range j).flatMap g)).set X (S X ++ [j])).set Y (S Y ++ [k - j])
  have hFY : ∀ j, F j Y = S Y ++ [k - j] := fun j => Lists.set_same _ _ _
  have hFX : ∀ j, F j X = S X ++ [j] := fun j => by simp only [F]; rw [Lists.set_ne _ _ hXY, Lists.set_same]
  have h0 : F 0 = (S.set X (S X ++ [0])).set Y (S Y ++ [k]) := by
    simp only [F, List.range_zero, List.flatMap_nil, List.append_nil, Nat.sub_zero, Lists.set_get_self]
  have hl := reach_family (i := Y) (c := .pos) (p := .seq body (.seq (.prim (.inc X)) (.prim (.dec Y)))) F k
    (fun m hm => by rw [hFY, eval_pos_snoc]; simp; omega)
    (by rw [hFY, Nat.sub_self, eval_pos_snoc]; rfl)
    (fun m hm => by
      have b₁ := hbody m hm (S t ++ (List.range m).flatMap g)
      have b₂ := Reach.of (nruns_inc X ((F m).set t (F m t ++ g m)) (l := S X) (v := m)
        (by rw [Lists.set_ne _ _ (Ne.symm htX), hFX]))
      have b₃ := Reach.of (nruns_dec Y (((F m).set t (F m t ++ g m)).set X (S X ++ [m + 1])) (l := S Y) (v := k - m)
        (by rw [Lists.set_ne _ _ (Ne.symm hXY), Lists.set_ne _ _ (Ne.symm htY), hFY]))
      refine (b₁.seq (b₂.seq b₃)).cast ?_
      have hFt : F m t = S t ++ (List.range m).flatMap g := by
        simp only [F]; rw [Lists.set_ne _ _ htY, Lists.set_ne _ _ htX, Lists.set_same]
      rw [hFt]
      simp only [F, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.append_assoc]
      rw [show k - m - 1 = k - (m + 1) by omega]
      funext x
      simp only [Lists.set]
      by_cases h1 : x = Y
      · subst h1; simp [hXY, htY]
      · by_cases h2 : x = X
        · subst h2; simp [h1, htX]
        · by_cases h3 : x = t
          · subst h3; simp [h1, h2]
          · simp [h1, h2, h3])
  rw [h0] at hl
  have d₄ := Reach.of (nruns_pop X (F k) (hFX k))
  have d₅ := Reach.of (nruns_pop Y ((F k).set X (S X)) (l := S Y) (v := k - k)
    (by rw [Lists.set_ne _ _ (Ne.symm hXY), hFY]))
  refine (d₁.seq (d₂.seq (hl.seq (d₄.seq d₅)))).cast ?_
  simp only [F, Nat.sub_self]
  funext x
  simp only [Lists.set]
  by_cases h1 : x = Y
  · subst h1; simp [htY, Ne.symm htY]
  · by_cases h2 : x = X
    · subst h2; simp [h1, htX, Ne.symm htX]
    · by_cases h3 : x = t
      · subst h3; simp only [h1, h2, if_false, if_true]; rfl
      · simp [h1, h2, h3]

/-- `forP` with the number of rounds named. -/
theorem forP_pushes' {t X Y s : Fin K} {lim : LinE K} {body : NProg K} (hXY : X ≠ Y) (htX : t ≠ X) (htY : t ≠ Y)
    (hsY : s ≠ Y) (hsX : s ≠ X) (hls : lim.Avoid s) (hlY : lim.Avoid Y) (hlX : lim.Avoid X) (S : Lists K)
    (hs : S s = []) (k : Nat) (hk : lim.ev S = k) (g : Nat → List Nat)
    (hbody : ∀ j, j < k → ∀ o, Pushes t body (((S.set t o).set X (S X ++ [j])).set Y (S Y ++ [k - j])) (g j)) :
    Pushes t (forP X Y s lim body) S ((List.range k).flatMap g) := by
  subst hk
  exact forP_pushes hXY htX htY hsY hsX hls hlY hlX S hs g hbody

end MC

end Shallot
