import Complexity.ListMachine

/-!
# Correctness of the list-machine tape macros

Exact step counts and results of `goEnd`, `goHome`, `goLast`, `pushP`, `popP`, `copyP`.
-/

namespace Complexity

variable {k : Nat}

/-! ## Tape plumbing -/

theorem eq_or_ne' (a b : Fin k) : a = b ∨ a ≠ b := by
  by_cases h : a = b
  · exact Or.inl h
  · exact Or.inr h

theorem Tapes.ext' {a b : Tapes k} (h1 : a.pos = b.pos) (h2 : a.cells = b.cells) : a = b := by
  cases a; cases b; simp_all

theorem setPos_pos_self (τ : Tapes k) (i : Fin k) (p : Nat) : (τ.setPos i p).pos i = p := by
  simp [Tapes.setPos]

theorem setPos_pos_ne (τ : Tapes k) {i j : Fin k} (p : Nat) (h : j ≠ i) : (τ.setPos i p).pos j = τ.pos j := by
  simp [Tapes.setPos, h]

theorem setPos_cells (τ : Tapes k) (i : Fin k) (p : Nat) : (τ.setPos i p).cells = τ.cells := rfl

theorem setPos_setPos (τ : Tapes k) (i : Fin k) (p q : Nat) : (τ.setPos i p).setPos i q = τ.setPos i q := by
  apply Tapes.ext'
  · funext j; by_cases hj : j = i <;> simp [Tapes.setPos, hj]
  · rfl

theorem setPos_eq_of (σ : Tapes k) (i : Fin k) (p : Nat) (h : σ.pos i = p) : σ.setPos i p = σ := by
  apply Tapes.ext'
  · funext j
    by_cases hj : j = i
    · subst hj; simp [Tapes.setPos, h]
    · simp [Tapes.setPos, hj]
  · rfl

theorem read_setPos_self (σ : Tapes k) (i : Fin k) (p : Nat) : (σ.setPos i p).read i = σ.cells i p := by
  simp [Tapes.read, Tapes.setPos]

theorem apply_mv (τ : Tapes k) (i : Fin k) (m : Move) :
    τ.apply τ.read (fun j => if j = i then m else .S) = τ.setPos i (m.apply (τ.pos i)) := by
  apply Tapes.ext'
  · funext j
    by_cases hj : j = i
    · subst hj; simp [Tapes.apply, Tapes.setPos]
    · simp [Tapes.apply, Tapes.setPos, hj, Move.apply]
  · funext j y
    simp only [Tapes.apply, Tapes.read, Tapes.setPos]
    split <;> simp_all

theorem exec_act {P : Tapes k → Prop} {f : Action k} {τ τ' : Tapes k} (h : P τ)
    (e : τ.apply (f τ.read).1 (f τ.read).2 = τ') (h' : P τ') : Exec P (.act f) τ 1 (.cont τ') := by
  subst e; exact Exec.act h h'

theorem exec_mv_at {P : Tapes k → Prop} (σ : Tapes k) (i : Fin k) (m : Move) (p q : Nat) (hq : m.apply p = q)
    (h : P (σ.setPos i p)) (h' : P (σ.setPos i q)) : Exec P (mv i m) (σ.setPos i p) 1 (.cont (σ.setPos i q)) := by
  refine exec_act h ?_ h'
  show (σ.setPos i p).apply (σ.setPos i p).read (fun j => if j = i then m else .S) = _
  rw [apply_mv, setPos_pos_self, hq, setPos_setPos]

theorem apply_write (σ : Tapes k) (i : Fin k) (c : Prop) [Decidable c] (v : Nat) (w : Fin k → Nat)
    (hw : w = fun x => if x = i ∧ c then v else σ.read x) :
    σ.apply w (fun _ => .S) = ⟨σ.pos, fun x y => if x = i ∧ y = σ.pos i ∧ c then v else σ.cells x y⟩ := by
  subst hw
  apply Tapes.ext'
  · rfl
  · funext x y
    simp only [Tapes.apply, Tapes.read]
    by_cases hx : x = i
    · subst hx
      by_cases hy : y = σ.pos x
      · subst hy; simp
      · simp [hy]
    · by_cases hy : y = σ.pos x
      · subst hy; simp [hx]
      · simp [hx, hy]

/-! ## Representation facts -/

theorem TapeRep.zero {l : List Nat} {f : Nat → Nat} (h : TapeRep l f) : f 0 = 3 := h.1

theorem TapeRep.mid {l : List Nat} {f : Nat → Nat} (h : TapeRep l f) {j : Nat} (hj : j < l.length) :
    f (j + 1) = l[j] + 4 := h.2.1 j hj

theorem TapeRep.tail {l : List Nat} {f : Nat → Nat} (h : TapeRep l f) {j : Nat} (hj : l.length < j) :
    f j = 0 := h.2.2 j hj

theorem TapeRep.ne_zero {l : List Nat} {f : Nat → Nat} (h : TapeRep l f) {p : Nat} (hp : p ≤ l.length) :
    f p ≠ 0 := by
  cases p with
  | zero => rw [h.zero]; omega
  | succ p => rw [h.mid (by omega)]; omega

theorem TapeRep.ne_three {l : List Nat} {f : Nat → Nat} (h : TapeRep l f) {p : Nat} (hp : 1 ≤ p) :
    f p ≠ 3 := by
  by_cases hl : p ≤ l.length
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [h.mid (by omega)]; omega
  · rw [h.tail (by omega)]; omega

theorem TapeRep.last {l : List Nat} {f : Nat → Nat} (h : TapeRep l f) : f l.length = lastSym l := by
  by_cases h0 : l.length = 0
  · have hl : l = [] := List.length_eq_zero_iff.1 h0
    rw [h0, h.zero, hl]; rfl
  · obtain ⟨q, hq⟩ : ∃ q, l.length = q + 1 := ⟨l.length - 1, by omega⟩
    have hg : l.getLast? = some l[q] := by
      rw [List.getLast?_eq_getElem?]; simp [hq]
    rw [hq, h.mid (by omega)]
    simp [lastSym, hg]

theorem Rep.pos0 {L : Lists k} {τ : Tapes k} (hR : Rep L τ) (i : Fin k) : τ.pos i = 0 := (hR i).1

theorem Lists.set_self (L : Lists k) (i : Fin k) (l : List Nat) : L.set i l i = l := by simp [Lists.set]

theorem Lists.set_ne_m (L : Lists k) {i j : Fin k} (h : j ≠ i) (l : List Nat) : L.set i l j = L j := by
  simp [Lists.set, h]

theorem lenOK_of_set {L : Lists k} {B : Nat} {i : Fin k} {l : List Nat} (hB : LenOK B (L.set i l))
    (hle : (L i).length ≤ l.length) : LenOK B L := by
  intro j
  have := hB j
  rcases eq_or_ne' j i with rfl | h
  · rw [Lists.set_self] at this; omega
  · rw [Lists.set_ne_m _ h] at this; exact this

theorem lenOK_set_le {L : Lists k} {B : Nat} (hB : LenOK B L) (i : Fin k) {l : List Nat}
    (hle : l.length ≤ (L i).length) : LenOK B (L.set i l) := by
  intro j
  have := hB j
  rcases eq_or_ne' j i with rfl | h
  · rw [Lists.set_self]; omega
  · rw [Lists.set_ne_m _ h]; exact this

theorem tfits_of {L : Lists k} {τ : Tapes k} {B : Nat} (hR : Rep L τ) (hB : LenOK B L) (σ : Tapes k)
    (hc : σ.cells = τ.cells) (hp : ∀ j, σ.pos j ≤ (L j).length + 1) : TFits B σ := by
  intro j
  refine ⟨by have := hp j; have := hB j; omega, fun x hx => ?_⟩
  rw [hc]; exact (hR j).2.tail (by have := hB j; omega)

theorem tfits_setPos {L : Lists k} {τ : Tapes k} {B : Nat} (hR : Rep L τ) (hB : LenOK B L) (i : Fin k) {p : Nat}
    (hp : p ≤ (L i).length + 1) : TFits B (τ.setPos i p) :=
  tfits_of hR hB _ rfl (fun j => by
    rcases eq_or_ne' j i with rfl | h
    · rw [setPos_pos_self]; exact hp
    · rw [setPos_pos_ne _ _ h, hR.pos0 j]; omega)

theorem pos_bound {L : Lists k} {τ : Tapes k} (hR : Rep L τ) {i j : Fin k} (hij : i ≠ j) {a b : Nat}
    (ha : a ≤ (L j).length + 1) (hb : b ≤ (L i).length + 1) :
    ∀ x, ((τ.setPos j a).setPos i b).pos x ≤ (L x).length + 1 := by
  intro x
  rcases eq_or_ne' x i with rfl | hxi
  · rw [setPos_pos_self]; exact hb
  · rw [setPos_pos_ne _ _ hxi]
    rcases eq_or_ne' x j with rfl | hxj
    · rw [setPos_pos_self]; exact ha
    · rw [setPos_pos_ne _ _ hxj, hR.pos0 x]; omega

/-! ## Head movement -/

theorem goEnd_gen {P : Tapes k → Prop} {σ : Tapes k} (i : Fin k) {l : List Nat} (hT : TapeRep l (σ.cells i))
    (hP : ∀ q, q ≤ l.length + 1 → P (σ.setPos i q)) :
    ∀ n p, p + n = l.length + 1 →
      Exec P (goEnd i) (σ.setPos i p) (2 * n + 1) (.cont (σ.setPos i (l.length + 1))) := by
  intro n
  induction n with
  | zero =>
    intro p hp
    have hp' : p = l.length + 1 := by omega
    subst hp'
    exact Exec.loopF (hP _ (Nat.le_refl _)) (by simp [read_setPos_self, hT.tail (Nat.lt_succ_self _)])
  | succ n ih =>
    intro p hp
    have hne := hT.ne_zero (p := p) (by omega)
    have hc : (fun r : Fin k → Nat => r i != 0) (σ.setPos i p).read = true := by
      simp [read_setPos_self, hne]
    have hb := exec_mv_at (P := P) σ i .R p (p + 1) rfl (hP p (by omega)) (hP (p + 1) (by omega))
    have := Exec.loopC (c := fun r : Fin k → Nat => r i != 0) (p := mv i .R) (hP p (by omega)) hc hb
      (ih (p + 1) (by omega))
    rw [show 1 + 1 + (2 * n + 1) = 2 * (n + 1) + 1 by omega] at this
    exact this

theorem goHome_gen {P : Tapes k → Prop} {σ : Tapes k} (i : Fin k) {l : List Nat} (hT : TapeRep l (σ.cells i))
    (hP : ∀ q, q ≤ l.length + 1 → P (σ.setPos i q)) :
    ∀ p, p ≤ l.length + 1 → Exec P (goHome i) (σ.setPos i p) (2 * p + 1) (.cont (σ.setPos i 0)) := by
  intro p
  induction p with
  | zero =>
    intro _
    exact Exec.loopF (hP _ (Nat.zero_le _)) (by simp [read_setPos_self, hT.zero])
  | succ p ih =>
    intro hp
    have hne := hT.ne_three (p := p + 1) (by omega)
    have hc : (fun r : Fin k → Nat => r i != 3) (σ.setPos i (p + 1)).read = true := by
      simp [read_setPos_self, hne]
    have hb := exec_mv_at (P := P) σ i .L (p + 1) p (by simp [Move.apply]) (hP _ hp) (hP p (by omega))
    have := Exec.loopC (c := fun r : Fin k → Nat => r i != 3) (p := mv i .L) (hP _ hp) hc hb (ih (by omega))
    rw [show 1 + 1 + (2 * p + 1) = 2 * (p + 1) + 1 by omega] at this
    exact this

theorem goLast_gen {P : Tapes k → Prop} {σ : Tapes k} (i : Fin k) {l : List Nat} (hT : TapeRep l (σ.cells i))
    (hP : ∀ q, q ≤ l.length + 1 → P (σ.setPos i q)) :
    Exec P (goLast i) (σ.setPos i 0) (2 * l.length + 4) (.cont (σ.setPos i l.length)) := by
  have h1 := goEnd_gen i hT hP (l.length + 1) 0 (by omega)
  have h2 := exec_mv_at (P := P) σ i .L (l.length + 1) l.length (by simp [Move.apply]) (hP _ (Nat.le_refl _))
    (hP _ (by omega))
  have := Exec.seqC h1 h2
  rw [show 2 * (l.length + 1) + 1 + 1 = 2 * l.length + 4 by omega] at this
  exact this

theorem goEnd_spec {L : Lists k} {τ : Tapes k} {B : Nat} (i : Fin k) (hR : Rep L τ) (hB : LenOK B L) :
    Exec (TFits B) (goEnd i) τ (2 * (L i).length + 3) (.cont (τ.setPos i ((L i).length + 1))) := by
  have h := goEnd_gen (σ := τ) (P := TFits B) i (hR i).2 (fun q hq => tfits_setPos hR hB i hq)
    ((L i).length + 1) 0 (by omega)
  rw [setPos_eq_of τ i 0 (hR.pos0 i)] at h
  rw [show 2 * ((L i).length + 1) + 1 = 2 * (L i).length + 3 by omega] at h
  exact h

theorem goHome_spec {L : Lists k} {τ : Tapes k} {B : Nat} (i : Fin k) {p : Nat} (hR : Rep L τ) (hB : LenOK B L)
    (hp : p ≤ (L i).length + 1) :
    Exec (TFits B) (goHome i) (τ.setPos i p) (2 * p + 1) (.cont τ) := by
  have h := goHome_gen (σ := τ) (P := TFits B) i (hR i).2 (fun q hq => tfits_setPos hR hB i hq) p hp
  rwa [setPos_eq_of τ i 0 (hR.pos0 i)] at h

theorem goLast_spec {L : Lists k} {τ : Tapes k} {B : Nat} (i : Fin k) (hR : Rep L τ) (hB : LenOK B L) :
    Exec (TFits B) (goLast i) τ (2 * (L i).length + 4) (.cont (τ.setPos i (L i).length)) := by
  have h := goLast_gen (σ := τ) (P := TFits B) i (hR i).2 (fun q hq => tfits_setPos hR hB i hq)
  rwa [setPos_eq_of τ i 0 (hR.pos0 i)] at h

theorem read_last {L : Lists k} {τ : Tapes k} (i : Fin k) (hR : Rep L τ) :
    (τ.setPos i (L i).length).read i = lastSym (L i) := by
  rw [read_setPos_self]; exact (hR i).2.last

/-! ## Representation after updates -/

theorem rep_push {L : Lists k} {τ : Tapes k} (hR : Rep L τ) (i : Fin k) (v : Nat) :
    Rep (L.set i (L i ++ [v]))
      ⟨τ.pos, fun x y => if x = i ∧ y = (L i).length + 1 then v + 4 else τ.cells x y⟩ := by
  intro j
  refine ⟨hR.pos0 j, ?_⟩
  dsimp only
  rcases eq_or_ne' j i with rfl | hj
  · rw [Lists.set_self]
    refine ⟨?_, fun m hm => ?_, fun y hy => ?_⟩
    · have := (hR j).2.zero
      simp [this]
    · simp only [List.length_append, List.length_singleton] at hm
      by_cases hml : m < (L j).length
      · dsimp only
        rw [if_neg (by omega), (hR j).2.mid hml, List.getElem_append_left hml]
      · have : m = (L j).length := by omega
        subst this
        simp [List.getElem_append_right]
    · simp only [List.length_append, List.length_singleton] at hy
      dsimp only
      rw [if_neg (by omega)]
      exact (hR j).2.tail (by omega)
  · rw [Lists.set_ne_m _ hj]
    simp only [hj, false_and, if_false]
    exact (hR j).2

theorem rep_pop {L : Lists k} {τ : Tapes k} (hR : Rep L τ) (i : Fin k) :
    Rep (L.set i (L i).dropLast)
      ⟨τ.pos, fun x y => if x = i ∧ y = (L i).length ∧ τ.cells i (L i).length ≠ 3 then 0 else τ.cells x y⟩ := by
  intro j
  refine ⟨hR.pos0 j, ?_⟩
  dsimp only
  rcases eq_or_ne' j i with rfl | hj
  · rw [Lists.set_self]
    by_cases h0 : (L j).length = 0
    · have hl : L j = [] := List.length_eq_zero_iff.1 h0
      have h3 : τ.cells j (L j).length = 3 := by rw [h0]; exact (hR j).2.zero
      have hfun : (fun y => if j = j ∧ y = (L j).length ∧ τ.cells j (L j).length ≠ 3 then 0 else τ.cells j y)
          = τ.cells j := by
        funext y; simp [h3]
      have := (hR j).2
      rw [hl] at this
      rw [hfun, hl]
      simpa using this
    · have h3 : τ.cells j (L j).length ≠ 3 := (hR j).2.ne_three (by omega)
      have hfun : (fun y => if j = j ∧ y = (L j).length ∧ τ.cells j (L j).length ≠ 3 then 0 else τ.cells j y)
          = fun y => if y = (L j).length then 0 else τ.cells j y := by
        funext y; simp [h3]
      rw [hfun]
      refine ⟨?_, fun m hm => ?_, fun y hy => ?_⟩
      · dsimp only; rw [if_neg (by omega)]; exact (hR j).2.zero
      · simp only [List.length_dropLast] at hm
        dsimp only
        rw [if_neg (by omega), (hR j).2.mid (by omega)]
        simp [List.getElem_dropLast]
      · simp only [List.length_dropLast] at hy
        dsimp only
        split
        · rfl
        · exact (hR j).2.tail (by omega)
  · rw [Lists.set_ne_m _ hj]
    simp only [hj, false_and, if_false]
    exact (hR j).2

theorem rep_copy {L : Lists k} {τ : Tapes k} (hR : Rep L τ) {i j : Fin k} (hij : i ≠ j) :
    Rep (L.set j (L j ++ (L i).getLast?.toList))
      ⟨τ.pos, fun x y => if x = j ∧ y = (L j).length + 1 ∧ τ.cells i (L i).length ≠ 3
        then τ.cells i (L i).length else τ.cells x y⟩ := by
  have hlast := (hR i).2.last
  rcases hl : (L i).getLast? with _ | e
  · have h3 : τ.cells i (L i).length = 3 := by rw [hlast]; simp [lastSym, hl]
    have hfun : (fun x y => if x = j ∧ y = (L j).length + 1 ∧ τ.cells i (L i).length ≠ 3
        then τ.cells i (L i).length else τ.cells x y) = τ.cells := by
      funext x y; simp [h3]
    rw [hfun]
    have hs : L.set j (L j ++ (none : Option Nat).toList) = L := by
      funext x
      rcases eq_or_ne' x j with rfl | hx
      · simp [Lists.set_self]
      · rw [Lists.set_ne_m _ hx]
    rw [hs]
    intro x
    exact hR x
  · have h4 : τ.cells i (L i).length = e + 4 := by rw [hlast]; simp [lastSym, hl]
    have hfun : (fun x y => if x = j ∧ y = (L j).length + 1 ∧ τ.cells i (L i).length ≠ 3
        then τ.cells i (L i).length else τ.cells x y)
        = fun x y => if x = j ∧ y = (L j).length + 1 then e + 4 else τ.cells x y := by
      funext x y; simp [h4]
    rw [hfun]
    exact rep_push hR j e

/-! ## Instructions -/

theorem pushP_spec {L : Lists k} {τ : Tapes k} {B : Nat} (i : Fin k) (e : Nat) (hR : Rep L τ)
    (hB : LenOK B (L.set i (L i ++ [e]))) :
    ∃ t τ', t ≤ 4 * B + 8 ∧ Exec (TFits B) (pushP i e) τ t (.cont τ') ∧ Rep (L.set i (L i ++ [e])) τ' := by
  have hB0 : LenOK B L := lenOK_of_set hB (by simp)
  have hR' := rep_push hR i e
  have h1 := goEnd_spec i hR hB0
  have hP1 : TFits B (τ.setPos i ((L i).length + 1)) := tfits_setPos hR hB0 i (Nat.le_refl _)
  have hlen : ((L.set i (L i ++ [e])) i).length = (L i).length + 1 := by simp [Lists.set_self]
  have hP2 := tfits_setPos hR' hB i (p := (L i).length + 1) (by omega)
  have h2 : Exec (TFits B) (Prog.act (fun r => (fun j => if j = i then e + 4 else r j, fun _ => Move.S)))
      (τ.setPos i ((L i).length + 1)) 1
      (.cont ((⟨τ.pos, fun x y => if x = i ∧ y = (L i).length + 1 then e + 4 else τ.cells x y⟩ : Tapes k).setPos i
        ((L i).length + 1))) := by
    refine exec_act hP1 ?_ hP2
    show (τ.setPos i ((L i).length + 1)).apply (fun j => if j = i then e + 4 else (τ.setPos i ((L i).length + 1)).read j)
      (fun _ => Move.S) = _
    rw [apply_write (τ.setPos i ((L i).length + 1)) i True (e + 4) _
      (by funext x; simp)]
    apply Tapes.ext'
    · rfl
    · funext x y
      simp [Tapes.setPos]
  have h3 := goHome_spec (L := L.set i (L i ++ [e])) (B := B) i hR' hB (p := (L i).length + 1) (by omega)
  refine ⟨(2 * (L i).length + 3) + (1 + (2 * ((L i).length + 1) + 1)), _, ?_, Exec.seqC h1 (Exec.seqC h2 h3), hR'⟩
  have := hB i
  rw [Lists.set_self] at this
  simp at this
  omega

theorem popP_spec {L : Lists k} {τ : Tapes k} {B : Nat} (i : Fin k) (hR : Rep L τ) (hB : LenOK B L) :
    ∃ t τ', t ≤ 4 * B + 8 ∧ Exec (TFits B) (popP i) τ t (.cont τ') ∧ Rep (L.set i (L i).dropLast) τ' := by
  have hR' := rep_pop hR i
  have hB' : LenOK B (L.set i (L i).dropLast) := lenOK_set_le hB i (by simp)
  have h1 := goLast_spec i hR hB
  have hP1 : TFits B (τ.setPos i (L i).length) := tfits_setPos hR hB i (by omega)
  have hlen : ((L.set i (L i).dropLast) i).length = (L i).length - 1 := by simp [Lists.set_self]
  have hP2 := tfits_setPos hR' hB' i (p := (L i).length) (by omega)
  have h2 : Exec (TFits B) (Prog.act (fun r => (fun j => if j = i ∧ r i ≠ 3 then 0 else r j, fun _ => Move.S)))
      (τ.setPos i (L i).length) 1
      (.cont ((⟨τ.pos, fun x y => if x = i ∧ y = (L i).length ∧ τ.cells i (L i).length ≠ 3 then 0 else τ.cells x y⟩
        : Tapes k).setPos i (L i).length)) := by
    refine exec_act hP1 ?_ hP2
    show (τ.setPos i (L i).length).apply
      (fun j => if j = i ∧ (τ.setPos i (L i).length).read i ≠ 3 then 0 else (τ.setPos i (L i).length).read j)
      (fun _ => Move.S) = _
    rw [apply_write (τ.setPos i (L i).length) i ((τ.setPos i (L i).length).read i ≠ 3) 0 _ rfl]
    apply Tapes.ext'
    · rfl
    · funext x y
      simp [Tapes.setPos, Tapes.read]
  have h3 := goHome_spec (L := L.set i (L i).dropLast) (B := B) i hR' hB' (p := (L i).length) (by omega)
  refine ⟨(2 * (L i).length + 4) + (1 + (2 * (L i).length + 1)), _, ?_, Exec.seqC h1 (Exec.seqC h2 h3), hR'⟩
  have := hB i
  omega

theorem copyP_spec {L : Lists k} {τ : Tapes k} {B : Nat} (i j : Fin k) (hij : i ≠ j) (hR : Rep L τ)
    (hB : LenOK B (L.set j (L j ++ (L i).getLast?.toList))) :
    ∃ t τ', t ≤ 8 * B + 16 ∧ Exec (TFits B) (copyP i j) τ t (.cont τ') ∧
      Rep (L.set j (L j ++ (L i).getLast?.toList)) τ' := by
  have hB0 : LenOK B L := lenOK_of_set hB (by simp)
  have hR' := rep_copy hR hij
  generalize hτ' : (⟨τ.pos, fun x y => if x = j ∧ y = (L j).length + 1 ∧ τ.cells i (L i).length ≠ 3
        then τ.cells i (L i).length else τ.cells x y⟩ : Tapes k) = τ' at hR'
  have hlenj : (L j).length ≤ ((L.set j (L j ++ (L i).getLast?.toList)) j).length := by
    rw [Lists.set_self]; simp
  have hleni : ((L.set j (L j ++ (L i).getLast?.toList)) i) = L i := Lists.set_ne_m _ hij _
  -- step 1
  have h1 := goEnd_spec j hR hB0
  -- step 2
  have hpos0 : (τ.setPos j ((L j).length + 1)).pos i = 0 := by rw [setPos_pos_ne _ _ hij, hR.pos0 i]
  have hP2 : ∀ q, q ≤ (L i).length + 1 → TFits B ((τ.setPos j ((L j).length + 1)).setPos i q) :=
    fun q hq => tfits_of hR hB0 _ rfl (pos_bound hR hij (Nat.le_refl _) hq)
  have h2 := goLast_gen (σ := τ.setPos j ((L j).length + 1)) (P := TFits B) i (hR i).2 hP2
  rw [setPos_eq_of _ i 0 hpos0] at h2
  -- step 3
  have hσ : (τ.setPos j ((L j).length + 1)).setPos i (L i).length = ((τ.setPos j ((L j).length + 1)).setPos i (L i).length) := rfl
  have hread : ((τ.setPos j ((L j).length + 1)).setPos i (L i).length).read i = τ.cells i (L i).length := by
    rw [read_setPos_self]; rfl
  have hP3 : TFits B ((τ.setPos j ((L j).length + 1)).setPos i (L i).length) :=
    tfits_of hR hB0 _ rfl (pos_bound hR hij (Nat.le_refl _) (Nat.le_succ _))
  have hP4 : TFits B ((τ'.setPos j ((L j).length + 1)).setPos i (L i).length) :=
    tfits_of hR' hB _ rfl (pos_bound hR' hij (by omega) (by rw [hleni]; omega))
  have h3 : Exec (TFits B)
      (Prog.act (fun r => (fun x => if x = j ∧ r i ≠ 3 then r i else r x, fun _ => Move.S)))
      ((τ.setPos j ((L j).length + 1)).setPos i (L i).length) 1
      (.cont ((τ'.setPos j ((L j).length + 1)).setPos i (L i).length)) := by
    subst hτ'
    refine exec_act hP3 ?_ hP4
    show ((τ.setPos j ((L j).length + 1)).setPos i (L i).length).apply
      (fun x => if x = j ∧ ((τ.setPos j ((L j).length + 1)).setPos i (L i).length).read i ≠ 3 then
        ((τ.setPos j ((L j).length + 1)).setPos i (L i).length).read i
        else ((τ.setPos j ((L j).length + 1)).setPos i (L i).length).read x)
      (fun _ => Move.S) = _
    rw [apply_write ((τ.setPos j ((L j).length + 1)).setPos i (L i).length) j
      (((τ.setPos j ((L j).length + 1)).setPos i (L i).length).read i ≠ 3)
      (((τ.setPos j ((L j).length + 1)).setPos i (L i).length).read i) _ rfl]
    apply Tapes.ext'
    · rfl
    · funext x y
      rw [hread]
      have hpj : ((τ.setPos j ((L j).length + 1)).setPos i (L i).length).pos j = (L j).length + 1 := by
        rw [setPos_pos_ne _ _ hij.symm, setPos_pos_self]
      have hji : ¬ j = i := fun h => hij h.symm
      simp [hji, Tapes.setPos]
  -- step 4
  have hT4 : TapeRep ((L.set j (L j ++ (L i).getLast?.toList)) i) ((τ'.setPos j ((L j).length + 1)).cells i) :=
    (hR' i).2
  have hP4' : ∀ q, q ≤ ((L.set j (L j ++ (L i).getLast?.toList)) i).length + 1 →
      TFits B ((τ'.setPos j ((L j).length + 1)).setPos i q) :=
    fun q hq => tfits_of hR' hB _ rfl (pos_bound hR' hij (by omega) hq)
  have h4 := goHome_gen (σ := τ'.setPos j ((L j).length + 1)) (P := TFits B) i hT4 hP4' (L i).length
    (by rw [hleni]; omega)
  have hpos4 : (τ'.setPos j ((L j).length + 1)).pos i = 0 := by
    rw [setPos_pos_ne _ _ hij, ← hτ']; exact hR.pos0 i
  rw [setPos_eq_of _ i 0 hpos4] at h4
  -- step 5
  have h5 := goHome_spec (L := L.set j (L j ++ (L i).getLast?.toList)) (B := B) j hR' hB
    (p := (L j).length + 1) (by omega)
  refine ⟨(2 * (L j).length + 3) + ((2 * (L i).length + 4) + (1 + ((2 * (L i).length + 1) +
    (2 * ((L j).length + 1) + 1)))), τ', ?_, Exec.seqC h1 (Exec.seqC h2 (Exec.seqC h3 (Exec.seqC h4 h5))), hR'⟩
  have := hB0 i
  have := hB0 j
  omega

end Complexity
