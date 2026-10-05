import Complexity.TqbfEval

/-!
# Specification of the matrix evaluation on a list machine
-/

namespace Complexity

variable {k : Nat}

theorem moving_i (L : Lists k) (i j : Fin k) (n m : Nat) :
    (L.moving i j n m) i = (L i).take ((L i).length - n) := by
  simp [Lists.moving]

theorem moving_j (L : Lists k) {i j : Fin k} (h : i ≠ j) (n m : Nat) :
    (L.moving i j n m) j = L j ++ (L i).reverse.take m := by
  simp [Lists.moving, Lists.set_ne _ _ (Ne.symm h)]

theorem moving_other (L : Lists k) {i j x : Fin k} (hi : x ≠ i) (hj : x ≠ j) (n m : Nat) :
    (L.moving i j n m) x = L x := by
  simp [Lists.moving, Lists.set_ne _ _ hi, Lists.set_ne _ _ hj]

theorem moving_zero (L : Lists k) {i j : Fin k} (h : i ≠ j) : L.moving i j 0 0 = L := by
  funext x
  by_cases hxi : x = i
  · subst hxi; simp [moving_i]
  · by_cases hxj : x = j
    · subst hxj; simp [moving_j _ h]
    · simp [moving_other _ hxi hxj]

theorem moving_full (L : Lists k) {i j : Fin k} (h : i ≠ j) :
    L.moving i j (L i).length (L i).length = L.moveAll i j := by
  funext x
  by_cases hxi : x = i
  · subst hxi; simp [moving_i, Lists.moveAll]
  · by_cases hxj : x = j
    · subst hxj; simp [moving_j _ h, Lists.moveAll, Lists.set_ne _ _ (Ne.symm h), List.take_of_length_le]
    · simp [moving_other _ hxi hxj, Lists.moveAll, Lists.set_ne _ _ hxi, Lists.set_ne _ _ hxj]

theorem moving_step_top (L : Lists k) {i j : Fin k} (h : i ≠ j) {n : Nat} (hn : n < (L i).length) :
    (L.moving i j n n).moveTop i j = L.moving i j (n + 1) (n + 1) ∧
    (L.moving i j n n).set j ((L.moving i j n n) j ++ ((L.moving i j n n) i).getLast?.toList) =
      L.moving i j n (n + 1) := by
  have key : ((L i).take ((L i).length - n)).getLast?.toList = (L i).reverse[n]?.toList := by
    have : (L i).take ((L i).length - n) = ((L i).reverse.drop n).reverse := by
      rw [List.drop_reverse]; simp
    rw [this, List.getLast?_reverse, List.head?_drop]
  have key2 : ((L i).take ((L i).length - n)).dropLast = (L i).take ((L i).length - (n + 1)) := by
    have e1 : (L i).take ((L i).length - n) = ((L i).reverse.drop n).reverse := by
      rw [List.drop_reverse]; simp
    have e2 : (L i).take ((L i).length - (n + 1)) = ((L i).reverse.drop (n + 1)).reverse := by
      rw [List.drop_reverse]; simp
    rw [e1, e2, List.dropLast_reverse, List.tail_drop]
  constructor
  · funext x
    by_cases hxi : x = i
    · subst hxi; simp [moving_i, Lists.moveTop, key2]
    · by_cases hxj : x = j
      · subst hxj
        simp [moveTop_j h, moving_j _ h, moving_i, key, List.take_add_one]
      · simp [moveTop_other hxi hxj, moving_other _ hxi hxj]
  · funext x
    by_cases hxj : x = j
    · subst hxj
      simp [Lists.set, moving_j _ h, moving_i, key, List.take_add_one]
    · simp [Lists.set, hxj]
      by_cases hxi : x = i
      · subst hxi; simp [moving_i]
      · simp [moving_other _ hxi hxj]

/-- Moving everything from `i` to `j`. -/
theorem runs_moveAll {Q : Lists k → Prop} {i j : Fin k} (hij : i ≠ j) {L : Lists k}
    (hq : ∀ n m, n ≤ (L i).length → m ≤ (L i).length → Q (L.moving i j n m)) :
    Runs Q (moveAll i j) L (L.moveAll i j) (((L i).length + 1) * 3) := by
  have hmain := runs_loop (Q := Q) (i := i) (c := (· != 3)) (p := moveTop i j)
    (I := fun L' => ∃ n ≤ (L i).length, L' = L.moving i j n n) (μ := fun L' => (L' i).length) (T := 2)
    (fun L' ⟨n, hn, e⟩ => by subst e; exact hq n n hn hn)
    (by
      rintro L' ⟨n, hn, rfl⟩ hc
      have hne : (L.moving i j n n i).length ≠ 0 := by
        intro h0
        have : lastSym (L.moving i j n n i) = 3 := by
          rw [List.length_eq_zero_iff.1 h0]; rfl
        simp [this] at hc
      have hlen : (L.moving i j n n i).length = (L i).length - n := by simp [moving_i]
      have hlt : n < (L i).length := by omega
      obtain ⟨e1, e2⟩ := moving_step_top L hij hlt
      refine ⟨L.moving i j (n + 1) (n + 1), ?_, ⟨n + 1, hlt, rfl⟩, ?_⟩
      · have := runs_moveTop (Q := Q) hij (L := L.moving i j n n) (hq n n hn hn)
          (by rw [e2]; exact hq n (n + 1) hn hlt) (by rw [e1]; exact hq (n + 1) (n + 1) hlt hlt)
        rwa [e1] at this
      · simp [moving_i]; omega)
    L ⟨0, Nat.zero_le _, (moving_zero L hij).symm⟩
  obtain ⟨L', hr, ⟨n, hn, rfl⟩, hc⟩ := hmain
  have h0 : (L.moving i j n n i).length = 0 := by
    have : lastSym (L.moving i j n n i) = 3 := by simpa using hc
    rw [lastSym_eq_three.1 this]; rfl
  have hn' : n = (L i).length := by simp [moving_i] at h0; omega
  rw [hn', moving_full L hij] at hr
  exact hr

/-! ## Infrastructure -/

theorem lenOK_set {B : Nat} {L : Lists k} (h : LenOK B L) (i : Fin k) {l : List Nat} (hl : l.length + 2 ≤ B) :
    LenOK B (L.set i l) := by
  intro x
  by_cases hx : x = i
  · subst hx; simpa using hl
  · rw [Lists.set_ne _ _ hx]; exact h x

theorem lenOK_moveTop {B : Nat} {L : Lists k} (h : LenOK B L) {i j : Fin k} (hij : i ≠ j)
    (hb : (L j).length + 3 ≤ B) : LenOK B (L.set j (L j ++ (L i).getLast?.toList)) ∧ LenOK B (L.moveTop i j) := by
  have h1 : LenOK B (L.set j (L j ++ (L i).getLast?.toList)) := by
    apply lenOK_set h
    have : (L i).getLast?.toList.length ≤ 1 := by cases (L i).getLast? <;> simp
    simp; omega
  refine ⟨h1, ?_⟩
  unfold Lists.moveTop
  apply lenOK_set h1
  simp [Lists.set_ne _ _ hij]
  have := h i
  simp [List.length_dropLast]; omega

theorem lenOK_moving {B : Nat} {L : Lists k} (h : LenOK B L) {i j : Fin k} (hij : i ≠ j)
    (hb : (L j).length + (L i).length + 2 ≤ B) (n m : Nat) : LenOK B (L.moving i j n m) := by
  unfold Lists.moving
  have h1 : LenOK B (L.set j (L j ++ (L i).reverse.take m)) := by
    apply lenOK_set h
    have : ((L i).reverse.take m).length ≤ (L i).length := by simp; omega
    simp; omega
  apply lenOK_set h1
  simp [Lists.set_ne _ _ hij]
  have := h i
  simp; omega

theorem lenOK_moveAll {B : Nat} {L : Lists k} (h : LenOK B L) {i j : Fin k} (hij : i ≠ j)
    (hb : (L j).length + (L i).length + 2 ≤ B) : LenOK B (L.moveAll i j) := by
  rw [← moving_full L hij]; exact lenOK_moving h hij hb _ _

def Step (B T : Nat) (p : LProg k) (L : Lists k) (P : Lists k → Prop) : Prop :=
  ∃ L', Runs (LenOK B) p L L' T ∧ LenOK B L' ∧ P L'

theorem Step.mono {B T T' : Nat} {p : LProg k} {L : Lists k} {P R : Lists k → Prop} (h : Step B T p L P)
    (hT : T ≤ T') (hP : ∀ L', P L' → R L') : Step B T' p L R :=
  let ⟨L', hr, hl, hp⟩ := h; ⟨L', hr.mono hT, hl, hP _ hp⟩

theorem Step.seq {B T₁ T₂ : Nat} {p q : LProg k} {L : Lists k} {P R : Lists k → Prop} (h : Step B T₁ p L P)
    (hq : ∀ L₁, LenOK B L₁ → P L₁ → Step B T₂ q L₁ R) : Step B (T₁ + T₂) (.seq p q) L R :=
  let ⟨L₁, hr, hl, hp⟩ := h
  let ⟨L₂, hr₂, hl₂, hp₂⟩ := hq L₁ hl hp
  ⟨L₂, hr.seq hr₂, hl₂, hp₂⟩

theorem Step.iteT {B T : Nat} {i : Fin k} {c : Nat → Bool} {p q : LProg k} {L : Lists k} {P : Lists k → Prop}
    (hL : LenOK B L) (hc : c (lastSym (L i)) = true) (h : Step B T p L P) : Step B (T + 1) (.ite i c p q) L P :=
  let ⟨L', hr, hl, hp⟩ := h; ⟨L', hr.iteT hL hc, hl, hp⟩

theorem Step.iteF {B T : Nat} {i : Fin k} {c : Nat → Bool} {p q : LProg k} {L : Lists k} {P : Lists k → Prop}
    (hL : LenOK B L) (hc : c (lastSym (L i)) = false) (h : Step B T q L P) : Step B (T + 1) (.ite i c p q) L P :=
  let ⟨L', hr, hl, hp⟩ := h; ⟨L', hr.iteF hL hc, hl, hp⟩

theorem Step.refl {B : Nat} {p : LProg k} {L : Lists k} {P : Lists k → Prop} (hL : LenOK B L) (hP : P L)
    (hr : Runs (LenOK B) p L L 1) : Step B 1 p L P := ⟨L, hr, hL, hP⟩

structure Dist (mr mr2 fr ft vs : Fin k) : Prop where
  a : mr ≠ mr2
  b : mr ≠ fr
  c : mr ≠ ft
  d : mr ≠ vs
  e : mr2 ≠ fr
  f : mr2 ≠ ft
  g : mr2 ≠ vs
  h : fr ≠ ft
  i : fr ≠ vs
  j : ft ≠ vs

theorem Dist.of_nodup {mr mr2 fr ft vs : Fin k} (hd : [mr, mr2, fr, ft, vs].Nodup) : Dist mr mr2 fr ft vs := by
  simp [List.nodup_cons] at hd
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10⟩ := hd
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- The five working tapes hold `a b c d e`; every other tape is as in `L0`. -/
def Is (mr mr2 fr ft vs : Fin k) (L0 : Lists k) (a b c d e : List Nat) (L : Lists k) : Prop :=
  L mr = a ∧ L mr2 = b ∧ L fr = c ∧ L ft = d ∧ L vs = e ∧
    ∀ x, x ≠ mr → x ≠ mr2 → x ≠ fr → x ≠ ft → x ≠ vs → L x = L0 x

theorem moveAll_i {L : Lists k} {i j : Fin k} : (L.moveAll i j) i = [] := by
  simp [Lists.moveAll]

theorem moveAll_j {L : Lists k} {i j : Fin k} (h : i ≠ j) : (L.moveAll i j) j = L j ++ (L i).reverse := by
  simp [Lists.moveAll, Lists.set_ne _ _ (Ne.symm h)]

theorem moveAll_other {L : Lists k} {i j x : Fin k} (hi : x ≠ i) (hj : x ≠ j) : (L.moveAll i j) x = L x := by
  simp [Lists.moveAll, Lists.set_ne _ _ hi, Lists.set_ne _ _ hj]

section Blocks
variable {B : Nat} {mr mr2 fr ft vs : Fin k} {L0 L : Lists k} {a b c d e : List Nat}

theorem is_set_vs (hd : Dist mr mr2 fr ft vs) (hI : Is mr mr2 fr ft vs L0 a b c d e L) (e' : List Nat) :
    Is mr mr2 fr ft vs L0 a b c d e' (L.set vs e') := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Lists.set_ne _ _ hd.d, h1]
  · rw [Lists.set_ne _ _ hd.g, h2]
  · rw [Lists.set_ne _ _ hd.i, h3]
  · rw [Lists.set_ne _ _ hd.j, h4]
  · simp
  · intro x hx1 hx2 hx3 hx4 hx5
    rw [Lists.set_ne _ _ hx5, h6 x hx1 hx2 hx3 hx4 hx5]

theorem is_moveTop_mr (hd : Dist mr mr2 fr ft vs) (hI : Is mr mr2 fr ft vs L0 a b c d e L) :
    Is mr mr2 fr ft vs L0 a.dropLast (b ++ a.getLast?.toList) c d e (L.moveTop mr mr2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [moveTop_i, h1]
  · rw [moveTop_j hd.a, h1, h2]
  · rw [moveTop_other hd.b.symm hd.e.symm, h3]
  · rw [moveTop_other hd.c.symm hd.f.symm, h4]
  · rw [moveTop_other hd.d.symm hd.g.symm, h5]
  · intro x hx1 hx2 hx3 hx4 hx5
    rw [moveTop_other hx1 hx2, h6 x hx1 hx2 hx3 hx4 hx5]

theorem is_moveTop_fr (hd : Dist mr mr2 fr ft vs) (hI : Is mr mr2 fr ft vs L0 a b c d e L) :
    Is mr mr2 fr ft vs L0 a b c.dropLast (d ++ c.getLast?.toList) e (L.moveTop fr ft) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [moveTop_other hd.b hd.c, h1]
  · rw [moveTop_other hd.e hd.f, h2]
  · rw [moveTop_i, h3]
  · rw [moveTop_j hd.h, h3, h4]
  · rw [moveTop_other hd.i.symm hd.j.symm, h5]
  · intro x hx1 hx2 hx3 hx4 hx5
    rw [moveTop_other hx3 hx4, h6 x hx1 hx2 hx3 hx4 hx5]

theorem is_moveAll_ft (hd : Dist mr mr2 fr ft vs) (hI : Is mr mr2 fr ft vs L0 a b c d e L) :
    Is mr mr2 fr ft vs L0 a b (c ++ d.reverse) [] e (L.moveAll ft fr) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [moveAll_other hd.c hd.b, h1]
  · rw [moveAll_other hd.f hd.e, h2]
  · rw [moveAll_j hd.h.symm, h3, h4]
  · rw [moveAll_i]
  · rw [moveAll_other hd.j.symm hd.i.symm, h5]
  · intro x hx1 hx2 hx3 hx4 hx5
    rw [moveAll_other hx4 hx3, h6 x hx1 hx2 hx3 hx4 hx5]

theorem is_moveAll_mr2 (hd : Dist mr mr2 fr ft vs) (hI : Is mr mr2 fr ft vs L0 a b c d e L) :
    Is mr mr2 fr ft vs L0 (a ++ b.reverse) [] c d e (L.moveAll mr2 mr) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [moveAll_j hd.a.symm, h1, h2]
  · rw [moveAll_i]
  · rw [moveAll_other hd.e.symm hd.b.symm, h3]
  · rw [moveAll_other hd.f.symm hd.c.symm, h4]
  · rw [moveAll_other hd.g.symm hd.d.symm, h5]
  · intro x hx1 hx2 hx3 hx4 hx5
    rw [moveAll_other hx2 hx1, h6 x hx1 hx2 hx3 hx4 hx5]

theorem step_pushV (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) (hI : Is mr mr2 fr ft vs L0 a b c d e L)
    (x : Nat) (hb : e.length + 3 ≤ B) : Step B 1 (.push vs x) L (Is mr mr2 fr ft vs L0 a b c d (e ++ [x])) := by
  have hv : L vs = e := hI.2.2.2.2.1
  have hl : LenOK B (L.set vs (L vs ++ [x])) := lenOK_set hL vs (by rw [hv]; simp; omega)
  refine ⟨_, runs_push hL hl, hl, ?_⟩
  rw [hv]; exact is_set_vs hd hI _

theorem step_popV (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) (hI : Is mr mr2 fr ft vs L0 a b c d e L) :
    Step B 1 (.pop vs) L (Is mr mr2 fr ft vs L0 a b c d e.dropLast) := by
  have hv : L vs = e := hI.2.2.2.2.1
  have hl : LenOK B (L.set vs (L vs).dropLast) := lenOK_set hL vs (by have := hL vs; simp [List.length_dropLast]; omega)
  refine ⟨_, runs_pop hL hl, hl, ?_⟩
  rw [hv]; exact is_set_vs hd hI _

theorem step_skip (i : Fin k) {P : Lists k → Prop} (hL : LenOK B L) (hP : P L) : Step B 1 (skipP i) L P :=
  Step.refl hL hP (runs_skip i hL)

theorem step_moveTop_mr (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) (hI : Is mr mr2 fr ft vs L0 a b c d e L)
    (hb : b.length + 3 ≤ B) :
    Step B 2 (moveTop mr mr2) L (Is mr mr2 fr ft vs L0 a.dropLast (b ++ a.getLast?.toList) c d e) := by
  have hb' : (L mr2).length + 3 ≤ B := by rw [hI.2.1]; exact hb
  obtain ⟨h1, h2⟩ := lenOK_moveTop hL hd.a hb'
  exact ⟨_, runs_moveTop hd.a hL h1 h2, h2, is_moveTop_mr hd hI⟩

theorem step_moveTop_fr (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) (hI : Is mr mr2 fr ft vs L0 a b c d e L)
    (hb : d.length + 3 ≤ B) :
    Step B 2 (moveTop fr ft) L (Is mr mr2 fr ft vs L0 a b c.dropLast (d ++ c.getLast?.toList) e) := by
  have hb' : (L ft).length + 3 ≤ B := by rw [hI.2.2.2.1]; exact hb
  obtain ⟨h1, h2⟩ := lenOK_moveTop hL hd.h hb'
  exact ⟨_, runs_moveTop hd.h hL h1 h2, h2, is_moveTop_fr hd hI⟩

theorem step_moveAll_ft (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) (hI : Is mr mr2 fr ft vs L0 a b c d e L)
    (hb : c.length + d.length + 2 ≤ B) :
    Step B (3 * B) (moveAll ft fr) L (Is mr mr2 fr ft vs L0 a b (c ++ d.reverse) [] e) := by
  have hb' : (L fr).length + (L ft).length + 2 ≤ B := by rw [hI.2.2.1, hI.2.2.2.1]; exact hb
  have hq := fun n m (_ : n ≤ (L ft).length) (_ : m ≤ (L ft).length) => lenOK_moving hL hd.h.symm hb' n m
  refine ⟨_, (runs_moveAll hd.h.symm hq).mono ?_, lenOK_moveAll hL hd.h.symm hb', is_moveAll_ft hd hI⟩
  have := hL ft; omega

theorem step_moveAll_mr2 (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) (hI : Is mr mr2 fr ft vs L0 a b c d e L)
    (hb : a.length + b.length + 2 ≤ B) :
    Step B (3 * B) (moveAll mr2 mr) L (Is mr mr2 fr ft vs L0 (a ++ b.reverse) [] c d e) := by
  have hb' : (L mr).length + (L mr2).length + 2 ≤ B := by rw [hI.1, hI.2.1]; exact hb
  have hq := fun n m (_ : n ≤ (L mr2).length) (_ : m ≤ (L mr2).length) => lenOK_moving hL hd.a.symm hb' n m
  refine ⟨_, (runs_moveAll hd.a.symm hq).mono ?_, lenOK_moveAll hL hd.a.symm hb', is_moveAll_mr2 hd hI⟩
  have := hL mr2; omega

/-- Boolean values on the value stack. -/
def sb (b : Bool) : Nat := if b then 1 else 0

theorem stackL_nil {α : Type} (f : α → Nat) : stackL f [] = [] := rfl

theorem stackL_cons {α : Type} (f : α → Nat) (x : α) (st : List α) : stackL f (x :: st) = stackL f st ++ [f x] := by
  simp [stackL]

theorem stackL_length {α : Type} (f : α → Nat) (st : List α) : (stackL f st).length = st.length := by
  simp [stackL]

theorem step_popV' (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) (hI : Is mr mr2 fr ft vs L0 a b c d e L)
    {E : List Nat} {y : Nat} (h : e = E ++ [y]) :
    Step B 1 (.pop vs) L (Is mr mr2 fr ft vs L0 a b c d E) := by
  refine (step_popV hd hL hI).mono (Nat.le_refl _) (fun L' hp => ?_)
  subst h; simpa using hp

theorem lastSym_stack_nil : lastSym ([] : List Nat) = 3 := rfl

theorem step_negV (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) {st : List Bool}
    (hI : Is mr mr2 fr ft vs L0 a b c d (stackL sb st) L) (hb : st.length + 3 ≤ B) :
    Step B 4 (negP vs) L (Is mr mr2 fr ft vs L0 a b c d (stackL sb ((!st.headD false) :: st.tail))) := by
  have hv : L vs = stackL sb st := hI.2.2.2.2.1
  unfold negP
  rcases st with _ | ⟨x, st'⟩
  · have hc : nonEmpty (lastSym (L vs)) = false := by rw [hv]; rfl
    refine (Step.iteF hL hc (step_pushV hd hL hI 1 (by simpa [stackL] using hb))).mono (by omega) ?_
    intro L' hp; simpa [stackL, sb] using hp
  · rw [stackL_cons] at hI hv
    have hc : nonEmpty (lastSym (L vs)) = true := by rw [hv, lastSym_append]; simp [nonEmpty]
    have hb' : (stackL sb st').length + 3 ≤ B := by simp [stackL_length] at hb ⊢; omega
    refine Step.iteT (T := 3) hL hc ?_
    cases x
    · have hc2 : symIs 1 (lastSym (L vs)) = false := by rw [hv, lastSym_append]; simp [symIs, sb]
      refine Step.iteF (T := 2) hL hc2 ?_
      refine ((step_popV' hd hL hI rfl).seq fun L1 hL1 hI1 => step_pushV hd hL1 hI1 1 hb').mono (by omega) ?_
      intro L' hp; simpa [stackL, sb] using hp
    · have hc2 : symIs 1 (lastSym (L vs)) = true := by rw [hv, lastSym_append]; simp [symIs, sb]
      refine Step.iteT (T := 2) hL hc2 ?_
      refine ((step_popV' hd hL hI rfl).seq fun L1 hL1 hI1 => step_pushV hd hL1 hI1 0 hb').mono (by omega) ?_
      intro L' hp; simpa [stackL, sb] using hp

theorem Step.seq' {B T₁ T₂ T : Nat} {p q : LProg k} {L : Lists k} {P R : Lists k → Prop} (h : Step B T₁ p L P)
    (hq : ∀ L₁, LenOK B L₁ → P L₁ → Step B T₂ q L₁ R) (hT : T₁ + T₂ ≤ T) : Step B T (.seq p q) L R :=
  (h.seq hq).mono hT (fun _ h => h)

theorem lastSym_vs (hI : Is mr mr2 fr ft vs L0 a b c d e L) : lastSym (L vs) = lastSym e := by
  rw [hI.2.2.2.2.1]

theorem lastSym_mr (hI : Is mr mr2 fr ft vs L0 a b c d e L) : lastSym (L mr) = lastSym a := by
  rw [hI.1]

theorem lastSym_stack_cons {α : Type} (f : α → Nat) (x : α) (st : List α) :
    lastSym (stackL f (x :: st)) = f x + 4 := by
  rw [stackL_cons, lastSym_append]

local macro "ev_fin_tac" : tactic => `(tactic| (intro L' hp; simpa [stackL, sb] using hp))

theorem step_conjV (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) {st : List Bool}
    (hI : Is mr mr2 fr ft vs L0 a b c d (stackL sb st) L) (hb : st.length + 3 ≤ B) :
    Step B 6 (conjP vs) L
      (Is mr mr2 fr ft vs L0 a b c d (stackL sb ((st.tail.headD false && st.headD false) :: st.tail.tail))) := by
  unfold conjP
  rcases st with _ | ⟨x, st'⟩
  · have hc : nonEmpty (lastSym (L vs)) = false := by rw [lastSym_vs hI]; rfl
    refine (Step.iteF (T := 1) hL hc (step_pushV hd hL hI 0 (by simpa [stackL] using hb))).mono (by omega) ?_
    ev_fin_tac
  · have hc : nonEmpty (lastSym (L vs)) = true := by rw [lastSym_vs hI, lastSym_stack_cons]; simp [nonEmpty]
    refine Step.iteT (T := 5) hL hc ?_
    have hb' : st'.length + 3 ≤ B := by simp at hb; omega
    cases x
    · have hc2 : symIs 1 (lastSym (L vs)) = false := by rw [lastSym_vs hI, lastSym_stack_cons]; simp [symIs, sb]
      refine Step.iteF (T := 4) hL hc2 ?_
      refine Step.seq' (T₁ := 1) (T₂ := 3) (step_popV' hd hL hI (stackL_cons _ _ _)) (fun L1 hL1 hI1 => ?_) (by omega)
      rcases st' with _ | ⟨y, st''⟩
      · have hc3 : nonEmpty (lastSym (L1 vs)) = false := by rw [lastSym_vs hI1]; rfl
        have h1 : Step B 2 (.ite vs nonEmpty (.pop vs) (skipP vs)) L1
            (Is mr mr2 fr ft vs L0 a b c d (stackL sb [])) :=
          Step.iteF (T := 1) hL1 hc3 (step_skip vs hL1 hI1)
        refine Step.seq' (T₁ := 2) (T₂ := 1) h1
          (fun L2 hL2 hI2 => (step_pushV hd hL2 hI2 0 (by simp [stackL]; omega)).mono (by omega) (by ev_fin_tac)) (by omega)
      · have hc3 : nonEmpty (lastSym (L1 vs)) = true := by rw [lastSym_vs hI1, lastSym_stack_cons]; simp [nonEmpty]
        have h1 : Step B 2 (.ite vs nonEmpty (.pop vs) (skipP vs)) L1
            (Is mr mr2 fr ft vs L0 a b c d (stackL sb st'')) :=
          Step.iteT (T := 1) hL1 hc3 (step_popV' hd hL1 hI1 (stackL_cons _ _ _))
        refine Step.seq' (T₁ := 2) (T₂ := 1) h1
          (fun L2 hL2 hI2 => (step_pushV hd hL2 hI2 0 (by simp [stackL_length] at hb' ⊢; omega)).mono (by omega) (by ev_fin_tac)) (by omega)
    · have hc2 : symIs 1 (lastSym (L vs)) = true := by rw [lastSym_vs hI, lastSym_stack_cons]; simp [symIs, sb]
      refine Step.iteT (T := 4) hL hc2 ?_
      refine Step.seq' (T₁ := 1) (T₂ := 2) (step_popV' hd hL hI (stackL_cons _ _ _)) (fun L1 hL1 hI1 => ?_) (by omega)
      rcases st' with _ | ⟨y, st''⟩
      · have hc3 : nonEmpty (lastSym (L1 vs)) = false := by rw [lastSym_vs hI1]; rfl
        refine Step.iteF (T := 1) hL1 hc3 ?_
        exact (step_pushV hd hL1 hI1 0 (by simp [stackL]; omega)).mono (by omega) (by ev_fin_tac)
      · have hc3 : nonEmpty (lastSym (L1 vs)) = true := by rw [lastSym_vs hI1, lastSym_stack_cons]; simp [nonEmpty]
        refine Step.iteT (T := 1) hL1 hc3 ?_
        exact step_skip vs hL1 (by simpa [stackL, sb] using hI1)

theorem step_disjV (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) {st : List Bool}
    (hI : Is mr mr2 fr ft vs L0 a b c d (stackL sb st) L) (hb : st.length + 3 ≤ B) :
    Step B 6 (disjP vs) L
      (Is mr mr2 fr ft vs L0 a b c d (stackL sb ((st.tail.headD false || st.headD false) :: st.tail.tail))) := by
  unfold disjP
  rcases st with _ | ⟨x, st'⟩
  · have hc : nonEmpty (lastSym (L vs)) = false := by rw [lastSym_vs hI]; rfl
    refine (Step.iteF (T := 1) hL hc (step_pushV hd hL hI 0 (by simpa [stackL] using hb))).mono (by omega) ?_
    ev_fin_tac
  · have hc : nonEmpty (lastSym (L vs)) = true := by rw [lastSym_vs hI, lastSym_stack_cons]; simp [nonEmpty]
    refine Step.iteT (T := 5) hL hc ?_
    have hb' : st'.length + 3 ≤ B := by simp at hb; omega
    cases x
    · have hc2 : symIs 1 (lastSym (L vs)) = false := by rw [lastSym_vs hI, lastSym_stack_cons]; simp [symIs, sb]
      refine Step.iteF (T := 4) hL hc2 ?_
      refine Step.seq' (T₁ := 1) (T₂ := 2) (step_popV' hd hL hI (stackL_cons _ _ _)) (fun L1 hL1 hI1 => ?_) (by omega)
      rcases st' with _ | ⟨y, st''⟩
      · have hc3 : nonEmpty (lastSym (L1 vs)) = false := by rw [lastSym_vs hI1]; rfl
        refine Step.iteF (T := 1) hL1 hc3 ?_
        exact (step_pushV hd hL1 hI1 0 (by simp [stackL]; omega)).mono (by omega) (by ev_fin_tac)
      · have hc3 : nonEmpty (lastSym (L1 vs)) = true := by rw [lastSym_vs hI1, lastSym_stack_cons]; simp [nonEmpty]
        refine Step.iteT (T := 1) hL1 hc3 ?_
        exact step_skip vs hL1 (by simpa [stackL, sb] using hI1)
    · have hc2 : symIs 1 (lastSym (L vs)) = true := by rw [lastSym_vs hI, lastSym_stack_cons]; simp [symIs, sb]
      refine Step.iteT (T := 4) hL hc2 ?_
      refine Step.seq' (T₁ := 1) (T₂ := 3) (step_popV' hd hL hI (stackL_cons _ _ _)) (fun L1 hL1 hI1 => ?_) (by omega)
      rcases st' with _ | ⟨y, st''⟩
      · have hc3 : nonEmpty (lastSym (L1 vs)) = false := by rw [lastSym_vs hI1]; rfl
        have h1 : Step B 2 (.ite vs nonEmpty (.pop vs) (skipP vs)) L1
            (Is mr mr2 fr ft vs L0 a b c d (stackL sb [])) :=
          Step.iteF (T := 1) hL1 hc3 (step_skip vs hL1 hI1)
        refine Step.seq' (T₁ := 2) (T₂ := 1) h1
          (fun L2 hL2 hI2 => (step_pushV hd hL2 hI2 1 (by simp [stackL]; omega)).mono (by omega) (by ev_fin_tac)) (by omega)
      · have hc3 : nonEmpty (lastSym (L1 vs)) = true := by rw [lastSym_vs hI1, lastSym_stack_cons]; simp [nonEmpty]
        have h1 : Step B 2 (.ite vs nonEmpty (.pop vs) (skipP vs)) L1
            (Is mr mr2 fr ft vs L0 a b c d (stackL sb st'')) :=
          Step.iteT (T := 1) hL1 hc3 (step_popV' hd hL1 hI1 (stackL_cons _ _ _))
        refine Step.seq' (T₁ := 2) (T₂ := 1) h1
          (fun L2 hL2 hI2 => (step_pushV hd hL2 hI2 1 (by simp [stackL_length] at hb' ⊢; omega)).mono (by omega) (by ev_fin_tac)) (by omega)

theorem lastSym_rev_drop (es : List Nat) (j : Nat) :
    lastSym (es.drop j).reverse = if h : j < es.length then es[j] + 4 else 3 := by
  unfold lastSym
  rw [List.getLast?_reverse, List.head?_drop]
  by_cases h : j < es.length
  · simp [h]
  · have : es[j]? = none := by simp; omega
    simp [h, this]

theorem mr_succ (rest : List Nat) (n : Nat) :
    rest ++ 3 :: List.replicate (n + 1) 1 = (rest ++ 3 :: List.replicate n 1) ++ [1] := by
  simp [List.replicate_succ']

theorem step_refBody (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) {rest m es V : List Nat} {n j : Nat}
    (hI : Is mr mr2 fr ft vs L0 (rest ++ 3 :: List.replicate (n + 1) 1) m (es.drop j).reverse (es.take j) V L)
    (hbm : m.length + 3 ≤ B) (hbF : es.length + 2 ≤ B) :
    Step B 5 (.seq (moveTop mr mr2) (.ite fr nonEmpty (moveTop fr ft) (skipP fr))) L
      (Is mr mr2 fr ft vs L0 (rest ++ 3 :: List.replicate n 1) (m ++ [1]) (es.drop (j + 1)).reverse
        (es.take (j + 1)) V) := by
  rw [mr_succ] at hI
  have h1 := step_moveTop_mr hd hL hI hbm
  refine Step.seq' (T₁ := 2) (T₂ := 3) (h1.mono (Nat.le_refl _) (fun L' hp => by rw [List.dropLast_concat, List.getLast?_concat] at hp; exact hp))
    (fun L1 hL1 hI1 => ?_) (by omega)
  have hlast : lastSym (L1 fr) = lastSym (es.drop j).reverse := by rw [hI1.2.2.1]
  by_cases hj : j < es.length
  · have hc : nonEmpty (lastSym (L1 fr)) = true := by rw [hlast, lastSym_rev_drop]; simp [hj, nonEmpty]
    refine Step.iteT (T := 2) hL1 hc ?_
    refine (step_moveTop_fr hd hL1 hI1 (by simp; omega)).mono (by omega) (fun L' hp => ?_)
    have e1 : ((es.drop j).reverse).dropLast = (es.drop (j + 1)).reverse := by
      rw [List.dropLast_reverse, List.tail_drop]
    have e2 : ((es.drop j).reverse).getLast?.toList = es[j]?.toList := by
      rw [List.getLast?_reverse, List.head?_drop]
    rw [e1, e2, ← List.take_add_one] at hp
    exact hp
  · have hc : nonEmpty (lastSym (L1 fr)) = false := by rw [hlast, lastSym_rev_drop]; simp [hj, nonEmpty]
    refine Step.iteF (T := 2) hL1 hc ?_
    refine (step_skip fr hL1 ?_).mono (by omega) (fun _ h => h)
    have h1 : es.drop (j + 1) = es.drop j := by
      rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]
    have h2 : es.take (j + 1) = es.take j := by
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    rw [h1, h2]; exact hI1

theorem step_refLoop (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) {rest m es V : List Nat} {r : Nat}
    (hI : Is mr mr2 fr ft vs L0 (rest ++ 3 :: List.replicate r 1) m es.reverse [] V L)
    (hbm : m.length + r + 2 ≤ B) (hbF : es.length + 2 ≤ B) :
    Step B (((rest ++ 3 :: List.replicate r 1).length + 1) * 6)
      (.loop mr (symIs 1) (.seq (moveTop mr mr2) (.ite fr nonEmpty (moveTop fr ft) (skipP fr)))) L
      (Is mr mr2 fr ft vs L0 (rest ++ [3]) (m ++ List.replicate r 1) (es.drop r).reverse (es.take r) V) := by
  have hmain := runs_loop (Q := LenOK B) (i := mr) (c := symIs 1)
    (p := .seq (moveTop mr mr2) (.ite fr nonEmpty (moveTop fr ft) (skipP fr)))
    (I := fun L' => LenOK B L' ∧ ∃ j ≤ r, Is mr mr2 fr ft vs L0 (rest ++ 3 :: List.replicate (r - j) 1)
      (m ++ List.replicate j 1) (es.drop j).reverse (es.take j) V L')
    (μ := fun L' => (L' mr).length) (T := 5)
    (fun _ h => h.1)
    (by
      rintro L' ⟨hl, j, hj, hI'⟩ hc
      have hjr : j < r := by
        rcases Nat.lt_or_ge j r with h | h
        · exact h
        · exfalso
          have : j = r := by omega
          subst this
          rw [lastSym_mr hI'] at hc
          simp [lastSym_append, symIs] at hc
      obtain ⟨n, hn⟩ : ∃ n, r - j = n + 1 := ⟨r - j - 1, by omega⟩
      rw [hn] at hI'
      have hstep := step_refBody hd hl hI' (by simp; omega) hbF
      obtain ⟨L'', hr, hl'', hp⟩ := hstep
      refine ⟨L'', hr, ⟨hl'', j + 1, hjr, ?_⟩, ?_⟩
      · rw [show r - (j + 1) = n by omega, List.replicate_succ', ← List.append_assoc]; exact hp
      · rw [hI'.1, hp.1]; simp)
    L ⟨hL, 0, Nat.zero_le _, by simpa using hI⟩
  obtain ⟨L', hr, ⟨hl, j, hj, hI'⟩, hc⟩ := hmain
  have hjr : j = r := by
    rcases Nat.lt_or_ge j r with h | h
    · exfalso
      obtain ⟨n, hn⟩ : ∃ n, r - j = n + 1 := ⟨r - j - 1, by omega⟩
      rw [lastSym_mr hI', hn, mr_succ, lastSym_append] at hc
      simp [symIs] at hc
    · omega
  subst hjr
  have hlen : (L mr).length = (rest ++ 3 :: List.replicate j 1).length := by rw [hI.1]
  rw [hlen] at hr
  refine ⟨L', hr, hl, ?_⟩
  simpa using hI'

theorem lastSym_fr (hI : Is mr mr2 fr ft vs L0 a b c d e L) : lastSym (L fr) = lastSym c := by
  rw [hI.2.2.1]

theorem step_pushBit (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) (hI : Is mr mr2 fr ft vs L0 a b c d e L)
    (hb : e.length + 3 ≤ B) :
    Step B 2 (pushBitP fr vs) L
      (Is mr mr2 fr ft vs L0 a b c d (e ++ [if symIs 20 (lastSym c) = true then 1 else 0])) := by
  unfold pushBitP
  cases h : symIs 20 (lastSym c)
  · have hc : symIs 20 (lastSym (L fr)) = false := by rw [lastSym_fr hI, h]
    exact (Step.iteF (T := 1) hL hc (step_pushV hd hL hI 0 hb)).mono (by omega) (fun _ hp => by simpa using hp)
  · have hc : symIs 20 (lastSym (L fr)) = true := by rw [lastSym_fr hI, h]
    exact (Step.iteT (T := 1) hL hc (step_pushV hd hL hI 1 hb)).mono (by omega) (fun _ hp => by simpa using hp)

theorem encV_ref_rev (r : Nat) : (encV (.ref r)).reverse = 3 :: List.replicate r 1 ++ [6] := by
  simp [encV]

theorem step_ref (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) {rest mdone es V : List Nat} {r : Nat}
    (hI : Is mr mr2 fr ft vs L0 (rest ++ (encV (.ref r)).reverse) mdone es.reverse [] V L)
    (hbm : mdone.length + r + 4 ≤ B) (hbF : es.length + 2 ≤ B) (hbV : V.length + 3 ≤ B) :
    Step B (9 * B + 12) (refP mr mr2 fr ft vs) L
      (Is mr mr2 fr ft vs L0 rest (mdone ++ encV (.ref r)) es.reverse []
        (V ++ [if symIs 20 (lastSym (es.drop r).reverse) = true then 1 else 0])) := by
  have hmr : rest ++ (encV (.ref r)).reverse = (rest ++ 3 :: List.replicate r 1) ++ [6] := by
    rw [encV_ref_rev]; simp
  rw [hmr] at hI
  have hlen : (rest ++ 3 :: List.replicate r 1 ++ [6]).length + 2 ≤ B := by
    have := hL mr; rw [hI.1] at this; exact this
  have hlen' : (rest ++ 3 :: List.replicate r 1).length + 3 ≤ B := by simp at hlen ⊢; omega
  unfold refP
  have h1 := step_moveTop_mr hd hL hI (by omega : mdone.length + 3 ≤ B)
  refine Step.seq' (T₁ := 2) (T₂ := 9 * B + 10 - 2) (h1.mono (Nat.le_refl _)
    (fun L' hp => by rw [List.dropLast_concat, List.getLast?_concat] at hp; exact hp))
    (fun L1 hL1 hI1 => ?_) (by omega)
  have h2 := step_refLoop hd hL1 (es := es) hI1 (by simp; omega) hbF
  refine Step.seq' (T₁ := ((rest ++ 3 :: List.replicate r 1).length + 1) * 6) (T₂ := 9 * B + 10 - 2 - 2 - ((rest ++ 3 :: List.replicate r 1).length + 1) * 6)
    h2 (fun L2 hL2 hI2 => ?_) (by omega)
  have h3 := step_moveTop_mr hd hL2 hI2 (by simp; omega)
  refine Step.seq' (T₁ := 2) (T₂ := 3 * B + 2) (h3.mono (Nat.le_refl _)
    (fun L' hp => by rw [List.dropLast_concat, List.getLast?_concat] at hp; exact hp))
    (fun L3 hL3 hI3 => ?_) (by simp at hlen; omega)
  have h4 := step_pushBit hd hL3 hI3 hbV
  refine Step.seq' (T₁ := 2) (T₂ := 3 * B) h4 (fun L4 hL4 hI4 => ?_) (by omega)
  refine (step_moveAll_ft hd hL4 hI4 (by simp; omega)).mono (Nat.le_refl _) (fun L' hp => ?_)
  have e1 : (es.drop r).reverse ++ (es.take r).reverse = es.reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  rw [e1] at hp
  simp only [Option.toList_some, encV, List.append_assoc, List.cons_append, List.singleton_append] at hp ⊢
  exact hp

theorem lastSym_rev_drop' (es : List Nat) (j : Nat) :
    lastSym (es.drop j).reverse = match es[j]? with | none => 3 | some e => e + 4 := by
  unfold lastSym
  rw [List.getLast?_reverse, List.head?_drop]
  cases es[j]? <;> rfl

theorem bit_aux (frames : List Frame) (r : Nat) :
    symIs 20 (lastSym ((frames.map Frame.elem).drop r).reverse) = (frames.map Frame.bit).getD r false := by
  rw [lastSym_rev_drop', List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map]
  cases frames[r]? with
  | none => simp [symIs]
  | some f => cases f with
    | fresh => simp [Frame.elem, Frame.bit, symIs]
    | second a => cases a <;> simp [Frame.elem, Frame.bit, symIs]

theorem mr_ref (rest : List Nat) (r : Nat) :
    rest ++ (encV (.ref r)).reverse = (rest ++ 3 :: List.replicate r 1) ++ [6] := by
  rw [encV_ref_rev]; simp

theorem step_single (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) {rest mdone c d V : List Nat} {e : Nat} {T : Nat}
    {P : Lists k → Prop} {q : LProg k}
    (hI : Is mr mr2 fr ft vs L0 (rest ++ [e]) mdone c d V L) (hb : mdone.length + 3 ≤ B)
    (K : ∀ L1, LenOK B L1 → Is mr mr2 fr ft vs L0 rest (mdone ++ [e]) c d V L1 → Step B T q L1 P) :
    Step B (2 + T) (.seq (moveTop mr mr2) q) L P :=
  Step.seq' (T₁ := 2) (T₂ := T) ((step_moveTop_mr hd hL hI hb).mono (Nat.le_refl _)
    (fun L' hp => by rw [List.dropLast_concat, List.getLast?_concat] at hp; exact hp)) K (Nat.le_refl _)

theorem step_tok (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) {rest mdone : List Nat} {frames : List Frame}
    {st : List Bool} (t : VTok)
    (hI : Is mr mr2 fr ft vs L0 (rest ++ (encV t).reverse) mdone (stackL Frame.elem frames) [] (stackL sb st) L)
    (hbm : mdone.length + (encV t).length + 2 ≤ B) (hbF : frames.length + 2 ≤ B) (hbV : st.length + 3 ≤ B) :
    Step B (9 * B + 20) (tokP mr mr2 fr ft vs) L
      (Is mr mr2 fr ft vs L0 rest (mdone ++ encV t) (stackL Frame.elem frames) []
        (stackL sb (evalV (frames.map Frame.bit) [t] st))) := by
  unfold tokP
  cases t with
  | ref r =>
    have hc : symIs 6 (lastSym (L mr)) = true := by
      rw [lastSym_mr hI, mr_ref, lastSym_append]; rfl
    have hbV' : (stackL sb st).length + 3 ≤ B := by rw [stackL_length]; exact hbV
    have hbm' : mdone.length + r + 4 ≤ B := by simp [encV] at hbm; omega
    refine (Step.iteT (T := 9 * B + 12) hL hc
      ((step_ref hd hL (es := frames.map Frame.elem) hI hbm' (by simpa using hbF) hbV').mono (Nat.le_refl _) (fun L' hp => ?_))).mono
      (by omega) (fun _ h => h)
    rw [bit_aux] at hp
    simp only [evalV]
    rw [stackL_cons]
    exact hp
  | tt =>
    have hI' : Is mr mr2 fr ft vs L0 (rest ++ [7]) mdone (stackL Frame.elem frames) [] (stackL sb st) L := hI
    have hc6 : symIs 6 (lastSym (L mr)) = false := by rw [lastSym_mr hI', lastSym_append]; rfl
    have hc7 : symIs 7 (lastSym (L mr)) = true := by rw [lastSym_mr hI', lastSym_append]; rfl
    refine Step.iteF (T := 9 * B + 19) hL hc6 ?_
    refine (Step.iteT (T := 3) hL hc7 ?_).mono (by omega) (fun _ h => h)
    refine (step_single hd hL hI' (by simp [encV] at hbm; omega) (fun L1 hL1 hI1 =>
      (step_pushV hd hL1 hI1 1 (by rw [stackL_length]; exact hbV)).mono (Nat.le_refl 1) ?_)).mono (by omega) (fun _ h => h)
    intro L' hp; simpa [evalV, encV, stackL, sb] using hp
  | ff =>
    have hI' : Is mr mr2 fr ft vs L0 (rest ++ [8]) mdone (stackL Frame.elem frames) [] (stackL sb st) L := hI
    have hc6 : symIs 6 (lastSym (L mr)) = false := by rw [lastSym_mr hI', lastSym_append]; rfl
    have hc7 : symIs 7 (lastSym (L mr)) = false := by rw [lastSym_mr hI', lastSym_append]; rfl
    have hc8 : symIs 8 (lastSym (L mr)) = true := by rw [lastSym_mr hI', lastSym_append]; rfl
    refine Step.iteF (T := 9 * B + 19) hL hc6 ?_
    refine Step.iteF (T := 9 * B + 18) hL hc7 ?_
    refine (Step.iteT (T := 3) hL hc8 ?_).mono (by omega) (fun _ h => h)
    refine (step_single hd hL hI' (by simp [encV] at hbm; omega) (fun L1 hL1 hI1 =>
      (step_pushV hd hL1 hI1 0 (by rw [stackL_length]; exact hbV)).mono (Nat.le_refl 1) ?_)).mono (by omega) (fun _ h => h)
    intro L' hp; simpa [evalV, encV, stackL, sb] using hp
  | neg =>
    have hI' : Is mr mr2 fr ft vs L0 (rest ++ [9]) mdone (stackL Frame.elem frames) [] (stackL sb st) L := hI
    have hc6 : symIs 6 (lastSym (L mr)) = false := by rw [lastSym_mr hI', lastSym_append]; rfl
    have hc7 : symIs 7 (lastSym (L mr)) = false := by rw [lastSym_mr hI', lastSym_append]; rfl
    have hc8 : symIs 8 (lastSym (L mr)) = false := by rw [lastSym_mr hI', lastSym_append]; rfl
    have hc9 : symIs 9 (lastSym (L mr)) = true := by rw [lastSym_mr hI', lastSym_append]; rfl
    refine Step.iteF (T := 9 * B + 19) hL hc6 ?_
    refine Step.iteF (T := 9 * B + 18) hL hc7 ?_
    refine Step.iteF (T := 9 * B + 17) hL hc8 ?_
    refine (Step.iteT (T := 6) hL hc9 ?_).mono (by omega) (fun _ h => h)
    refine (step_single hd hL hI' (by simp [encV] at hbm; omega) (fun L1 hL1 hI1 =>
      (step_negV hd hL1 hI1 hbV).mono (Nat.le_refl 4) ?_)).mono (by omega) (fun _ h => h)
    intro L' hp; simpa [evalV, encV] using hp
  | conj =>
    have hI' : Is mr mr2 fr ft vs L0 (rest ++ [10]) mdone (stackL Frame.elem frames) [] (stackL sb st) L := hI
    have hc6 : symIs 6 (lastSym (L mr)) = false := by rw [lastSym_mr hI', lastSym_append]; rfl
    have hc7 : symIs 7 (lastSym (L mr)) = false := by rw [lastSym_mr hI', lastSym_append]; rfl
    have hc8 : symIs 8 (lastSym (L mr)) = false := by rw [lastSym_mr hI', lastSym_append]; rfl
    have hc9 : symIs 9 (lastSym (L mr)) = false := by rw [lastSym_mr hI', lastSym_append]; rfl
    have hc10 : symIs 10 (lastSym (L mr)) = true := by rw [lastSym_mr hI', lastSym_append]; rfl
    refine Step.iteF (T := 9 * B + 19) hL hc6 ?_
    refine Step.iteF (T := 9 * B + 18) hL hc7 ?_
    refine Step.iteF (T := 9 * B + 17) hL hc8 ?_
    refine Step.iteF (T := 9 * B + 16) hL hc9 ?_
    refine (Step.iteT (T := 8) hL hc10 ?_).mono (by omega) (fun _ h => h)
    refine (step_single hd hL hI' (by simp [encV] at hbm; omega) (fun L1 hL1 hI1 =>
      (step_conjV hd hL1 hI1 hbV).mono (Nat.le_refl 6) ?_)).mono (by omega) (fun _ h => h)
    intro L' hp; simpa [evalV, encV] using hp
  | disj =>
    have hI' : Is mr mr2 fr ft vs L0 (rest ++ [11]) mdone (stackL Frame.elem frames) [] (stackL sb st) L := hI
    have hc6 : symIs 6 (lastSym (L mr)) = false := by rw [lastSym_mr hI', lastSym_append]; rfl
    have hc7 : symIs 7 (lastSym (L mr)) = false := by rw [lastSym_mr hI', lastSym_append]; rfl
    have hc8 : symIs 8 (lastSym (L mr)) = false := by rw [lastSym_mr hI', lastSym_append]; rfl
    have hc9 : symIs 9 (lastSym (L mr)) = false := by rw [lastSym_mr hI', lastSym_append]; rfl
    have hc10 : symIs 10 (lastSym (L mr)) = false := by rw [lastSym_mr hI', lastSym_append]; rfl
    refine Step.iteF (T := 9 * B + 19) hL hc6 ?_
    refine Step.iteF (T := 9 * B + 18) hL hc7 ?_
    refine Step.iteF (T := 9 * B + 17) hL hc8 ?_
    refine Step.iteF (T := 9 * B + 16) hL hc9 ?_
    refine (Step.iteF (T := 8) hL hc10 ?_).mono (by omega) (fun _ h => h)
    refine (step_single hd hL hI' (by simp [encV] at hbm; omega) (fun L1 hL1 hI1 =>
      (step_disjV hd hL1 hI1 hbV).mono (Nat.le_refl 6) ?_)).mono (by omega) (fun _ h => h)
    intro L' hp; simpa [evalV, encV] using hp

end Blocks

/-! ## The matrix loop -/

theorem evalV_append (bits : List Bool) : ∀ (xs ys : List VTok) (st : List Bool),
    evalV bits (xs ++ ys) st = evalV bits ys (evalV bits xs st)
  | [], ys, st => rfl
  | x :: xs, ys, st => by
    cases x <;> simp [evalV, evalV_append bits xs ys]

theorem evalV_length_le (bits : List Bool) : ∀ (ts : List VTok) (st : List Bool),
    (evalV bits ts st).length ≤ st.length + ts.length
  | [], st => by simp [evalV]
  | x :: ts, st => by
    cases x <;> simp only [evalV] <;>
      · refine Nat.le_trans (evalV_length_le bits ts _) ?_
        simp only [List.length_cons, List.length_tail]
        omega

theorem encV_length_pos (t : VTok) : 0 < (encV t).length := by cases t <;> simp [encV]

theorem toksV_cons (x : VTok) (xs : List VTok) : toksV (x :: xs) = encV x ++ toksV xs := by
  simp [toksV, List.flatMap_cons]

theorem toksV_append (xs ys : List VTok) : toksV (xs ++ ys) = toksV xs ++ toksV ys := by
  simp [toksV, List.flatMap_append]

theorem toksV_drop_eq_nil {mv : List VTok} {p : Nat} (hp : p ≤ mv.length) (h : toksV (mv.drop p) = []) :
    p = mv.length := by
  rcases Nat.lt_or_ge p mv.length with hlt | hge
  · exfalso
    rw [List.drop_eq_getElem_cons hlt, toksV_cons, List.append_eq_nil_iff] at h
    have := encV_length_pos mv[p]
    rw [h.1] at this
    simp at this
  · omega

section Main
variable {B : Nat} {mr mr2 fr ft vs : Fin k} {L0 L : Lists k}

theorem step_evalLeaf (hd : Dist mr mr2 fr ft vs) (hL : LenOK B L) {mv : List VTok} {frames : List Frame}
    {st : List Bool}
    (hI : Is mr mr2 fr ft vs L0 (toksV mv).reverse [] (stackL Frame.elem frames) [] (stackL sb st) L)
    (hBt : (toksV mv).length + 2 ≤ B) (hBf : frames.length + 2 ≤ B) (hBs : st.length + mv.length + 2 ≤ B) :
    ∃ T, Step B T (evalLeafP mr mr2 fr ft vs) L
      (Is mr mr2 fr ft vs L0 (toksV mv).reverse [] (stackL Frame.elem frames) []
        (stackL sb (evalV (frames.map Frame.bit) mv st))) := by
  have hmain := runs_loop (Q := LenOK B) (i := mr) (c := nonEmpty) (p := tokP mr mr2 fr ft vs)
    (I := fun L' => LenOK B L' ∧ ∃ p ≤ mv.length, Is mr mr2 fr ft vs L0 (toksV (mv.drop p)).reverse
      (toksV (mv.take p)) (stackL Frame.elem frames) [] (stackL sb (evalV (frames.map Frame.bit) (mv.take p) st)) L')
    (μ := fun L' => (L' mr).length) (T := 9 * B + 20)
    (fun _ h => h.1)
    (by
      rintro L' ⟨hl, p, hp, hI'⟩ hc
      have hpl : p < mv.length := by
        rcases Nat.lt_or_ge p mv.length with h | h
        · exact h
        · exfalso
          have : p = mv.length := by omega
          subst this
          rw [lastSym_mr hI'] at hc
          simp [List.drop_length, toksV, lastSym, nonEmpty] at hc
      have hd1 : mv.drop p = mv[p] :: mv.drop (p + 1) := List.drop_eq_getElem_cons hpl
      rw [hd1, toksV_cons, List.reverse_append] at hI'
      have hsplit : toksV mv = toksV (mv.take p) ++ (encV mv[p] ++ toksV (mv.drop (p + 1))) := by
        have h0 : toksV mv = toksV (mv.take p ++ mv.drop p) := by rw [List.take_append_drop]
        rw [h0, hd1, toksV_append, toksV_cons]
      have hlen : (toksV mv).length = (toksV (mv.take p)).length + (encV mv[p]).length +
          (toksV (mv.drop (p + 1))).length := by
        rw [hsplit]; simp; omega
      have hev := evalV_length_le (frames.map Frame.bit) (mv.take p) st
      have hbV : (evalV (frames.map Frame.bit) (mv.take p) st).length + 3 ≤ B := by
        simp at hev; omega
      obtain ⟨L'', hr, hl'', hp''⟩ := step_tok hd hl (t := mv[p]) hI' (by omega) hBf hbV
      refine ⟨L'', hr, ⟨hl'', p + 1, hpl, ?_⟩, ?_⟩
      · have e2 : toksV (mv.take (p + 1)) = toksV (mv.take p) ++ encV mv[p] := by
          have h0 : toksV ([] : List VTok) = [] := rfl
          rw [List.take_add_one, List.getElem?_eq_getElem hpl, Option.toList_some, toksV_append, toksV_cons, h0,
            List.append_nil]
        have e3 : evalV (frames.map Frame.bit) (mv.take (p + 1)) st =
            evalV (frames.map Frame.bit) [mv[p]] (evalV (frames.map Frame.bit) (mv.take p) st) := by
          rw [List.take_add_one, List.getElem?_eq_getElem hpl]
          exact evalV_append _ _ _ _
        rw [e2, e3]; exact hp''
      · rw [hp''.1, hI'.1]
        have := encV_length_pos mv[p]
        simp; omega)
    L ⟨hL, 0, Nat.zero_le _, by simpa [toksV, evalV] using hI⟩
  obtain ⟨L', hr, ⟨hl, p, hp, hI'⟩, hc⟩ := hmain
  have hpe : p = mv.length := by
    apply toksV_drop_eq_nil hp
    have h1 : lastSym (L' mr) = 3 := by simpa [nonEmpty] using hc
    rw [lastSym_eq_three, hI'.1] at h1
    simpa using h1
  subst hpe
  rw [List.drop_length, List.take_length] at hI'
  have hI2 : Is mr mr2 fr ft vs L0 [] (toksV mv) (stackL Frame.elem frames) []
      (stackL sb (evalV (frames.map Frame.bit) mv st)) L' := by simpa [toksV] using hI'
  have hm := step_moveAll_mr2 hd hl hI2 (by simp; omega)
  obtain ⟨L'', hr2, hl2, hp2⟩ := hm
  rw [List.nil_append] at hp2
  exact ⟨_, L'', hr.seq hr2, hl2, hp2⟩

end Main

/-- Evaluating a resolved matrix at a leaf. -/
theorem evalLeaf_spec {mr mr2 fr ft vs : Fin k} (hd : [mr, mr2, fr, ft, vs].Nodup) {B : Nat}
    (mv : List VTok) (frames : List Frame) (st : List Bool) {L : Lists k}
    (hmr : L mr = (toksV mv).reverse) (hmr2 : L mr2 = []) (hfr : L fr = stackL Frame.elem frames)
    (hft : L ft = []) (hvs : L vs = stackL (fun b : Bool => if b then 1 else 0) st)
    (hB : LenOK B L) (hBt : (toksV mv).length + 2 ≤ B) (hBf : frames.length + 2 ≤ B)
    (hBs : st.length + mv.length + 2 ≤ B) :
    ∃ T, Runs (LenOK B) (evalLeafP mr mr2 fr ft vs) L
      (L.set vs (stackL (fun b : Bool => if b then 1 else 0) (evalV (frames.map Frame.bit) mv st))) T := by
  have hd' := Dist.of_nodup hd
  have hI : Is mr mr2 fr ft vs L (toksV mv).reverse [] (stackL Frame.elem frames) [] (stackL sb st) L :=
    ⟨hmr, hmr2, hfr, hft, hvs, fun _ _ _ _ _ _ => rfl⟩
  obtain ⟨T, L', hr, hl, h1, h2, h3, h4, h5, h6⟩ := step_evalLeaf hd' hB hI hBt hBf hBs
  have hL' : L' = L.set vs (stackL (fun b : Bool => if b then 1 else 0) (evalV (frames.map Frame.bit) mv st)) := by
    funext x
    by_cases hx5 : x = vs
    · subst hx5; rw [Lists.set_same]; exact h5
    · rw [Lists.set_ne _ _ hx5]
      by_cases hx1 : x = mr
      · subst hx1; rw [h1, hmr]
      · by_cases hx2 : x = mr2
        · subst hx2; rw [h2, hmr2]
        · by_cases hx3 : x = fr
          · subst hx3; rw [h3, hfr]
          · by_cases hx4 : x = ft
            · subst hx4; rw [h4, hft]
            · exact h6 x hx1 hx2 hx3 hx4 hx5
  rw [hL'] at hr
  exact ⟨T, hr⟩

end Complexity
