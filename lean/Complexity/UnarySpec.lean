import Complexity.Unary
import Complexity.TqbfEvalSpec

/-!
# Specification of the unary arithmetic programs
-/

namespace Complexity

variable {k : Nat}

theorem Lists.set_set_u (L : Lists k) (i : Fin k) (a b : List Nat) : (L.set i a).set i b = L.set i b := by
  funext x; by_cases h : x = i <;> simp [Lists.set, h]

theorem moveTop_set {L : Lists k} {i j d : Fin k} (hi : d ≠ i) (hj : d ≠ j) (l : List Nat) :
    (L.set d l).moveTop i j = (L.moveTop i j).set d l := by
  have hi' : i ≠ d := Ne.symm hi
  have hj' : j ≠ d := Ne.symm hj
  funext x
  by_cases hxd : x = d
  · subst hxd; simp [Lists.moveTop, Lists.set_ne _ _ hi, Lists.set_ne _ _ hj]
  · by_cases hxi : x = i
    · subst hxi; simp [Lists.moveTop, Lists.set, hxd, hi']
    · by_cases hxj : x = j
      · subst hxj; simp [Lists.moveTop, Lists.set, hxd, hi', hj', hxi]
      · simp [Lists.moveTop, Lists.set, hxd, hxi, hxj]

/-- A scanning loop: each pass moves the top of `src` and does some more. -/
theorem runs_scan {Q : Lists k → Prop} {src : Fin k} {body : LProg k} {T : Nat} (F : Nat → Lists k) (s : Nat)
    (hlen : ∀ n, n ≤ s → (F n src).length = s - n) (hq : ∀ n, n ≤ s → Q (F n))
    (hstep : ∀ n, n < s → Runs Q body (F n) (F (n + 1)) T) :
    Runs Q (.loop src nonEmpty body) (F 0) (F s) ((s + 1) * (T + 1)) := by
  have hmain := runs_loop (Q := Q) (i := src) (c := nonEmpty) (p := body)
    (I := fun L' => ∃ n ≤ s, L' = F n) (μ := fun L' => (L' src).length) (T := T)
    (fun L' ⟨n, hn, e⟩ => by subst e; exact hq n hn)
    (by
      rintro L' ⟨n, hn, rfl⟩ hc
      have hlt : n < s := by
        by_cases h : n < s
        · exact h
        · have h0 : (F n src).length = 0 := by rw [hlen n hn]; omega
          have : lastSym (F n src) = 3 := by rw [List.length_eq_zero_iff.1 h0]; rfl
          simp [nonEmpty, this] at hc
      refine ⟨F (n + 1), hstep n hlt, ⟨n + 1, hlt, rfl⟩, ?_⟩
      rw [hlen n hn, hlen (n + 1) hlt]; omega)
    (F 0) ⟨0, Nat.zero_le _, rfl⟩
  obtain ⟨L', hr, ⟨n, hn, rfl⟩, hc⟩ := hmain
  have h0 : (F n src).length = 0 := by
    have : lastSym (F n src) = 3 := by simpa [nonEmpty] using hc
    rw [lastSym_eq_three.1 this]; rfl
  have hns : n = s := by rw [hlen n hn] at h0; omega
  subst hns
  have h00 : (F 0 src).length = n := by rw [hlen 0 (Nat.zero_le _)]; omega
  rw [h00] at hr
  exact hr

theorem Lists.set_get_self (L : Lists k) (i : Fin k) : L.set i (L i) = L := by
  funext x; by_cases h : x = i <;> simp [Lists.set, h]

theorem take_dropLast_aux (l : List Nat) {n : Nat} (hn : n ≤ l.length) : (l.take n).dropLast = l.take (n - 1) := by
  rw [List.dropLast_eq_take, List.length_take, List.take_take]
  congr 1; omega

theorem clearP_spec {Q : Lists k → Prop} {i : Fin k} {L : Lists k}
    (hq : ∀ n, n ≤ (L i).length → Q (L.set i ((L i).take n))) :
    Runs Q (clearP i) L (L.set i []) (((L i).length + 1) * 2) := by
  have hmain := runs_loop (Q := Q) (i := i) (c := nonEmpty) (p := .pop i)
    (I := fun L' => ∃ n ≤ (L i).length, L' = L.set i ((L i).take n)) (μ := fun L' => (L' i).length) (T := 1)
    (fun L' ⟨n, hn, e⟩ => by subst e; exact hq n hn)
    (by
      rintro L' ⟨n, hn, rfl⟩ hc
      have hlen : ((L.set i ((L i).take n)) i).length = n := by simp; omega
      have hn0 : n ≠ 0 := by
        intro h0
        subst h0
        simp [nonEmpty, Lists.set_same] at hc
        exact hc (by simp [lastSym])
      have hn1 : n - 1 ≤ (L i).length := by omega
      refine ⟨L.set i ((L i).take (n - 1)), ?_, ⟨n - 1, hn1, rfl⟩, ?_⟩
      · have := runs_pop (Q := Q) (i := i) (L := L.set i ((L i).take n)) (hq n hn) (by
          rw [Lists.set_same, Lists.set_set_u, take_dropLast_aux _ hn]; exact hq (n - 1) hn1)
        rwa [Lists.set_same, Lists.set_set_u, take_dropLast_aux _ hn] at this
      · simp; omega)
    L ⟨(L i).length, Nat.le_refl _, by simp [Lists.set_get_self]⟩
  obtain ⟨L', hr, ⟨n, hn, rfl⟩, hc⟩ := hmain
  have h0 : (L.set i ((L i).take n)) i = [] := by
    have : lastSym ((L.set i ((L i).take n)) i) = 3 := by simpa [nonEmpty] using hc
    exact lastSym_eq_three.1 this
  rw [Lists.set_same] at h0
  rw [h0] at hr
  exact hr

theorem lenOK_getLast_aux {B : Nat} {L : Lists k} (h : LenOK B L) (i : Fin k) : (L i).length + 2 ≤ B := h i

theorem copyLen_spec {src dst tmp : Fin k} (hd : [src, dst, tmp].Nodup) {B : Nat} {L : Lists k}
    (htmp : L tmp = []) (hB : LenOK B L) (hBd : (L dst).length + (L src).length + 2 ≤ B) :
    Runs (LenOK B) (copyLenP src dst tmp) L (L.set dst (L dst ++ List.replicate (L src).length 1))
      (8 * ((L src).length + 1)) := by
  have hst : src ≠ tmp := by rintro rfl; simp at hd
  have hsd : src ≠ dst := by rintro rfl; simp at hd
  have hdt : dst ≠ tmp := by rintro rfl; simp at hd
  have hts : tmp ≠ src := Ne.symm hst
  have htd : tmp ≠ dst := Ne.symm hdt
  have hds : dst ≠ src := Ne.symm hsd
  let M : Nat → Lists k := fun n => L.moving src tmp n n
  let F : Nat → Lists k := fun n => (M n).set dst (L dst ++ List.replicate n 1)
  have hMl : ∀ n, n ≤ (L src).length → LenOK B (M n) := fun n _ => lenOK_moving hB hst (by rw [htmp]; simp; omega) n n
  have hFl : ∀ n, n ≤ (L src).length → LenOK B (F n) := fun n hn => lenOK_set (hMl n hn) dst (by simp; omega)
  have hloop : Runs (LenOK B) (.loop src nonEmpty (.seq (moveTop src tmp) (.push dst 1))) (F 0) (F (L src).length)
      (((L src).length + 1) * (3 + 1)) := by
    apply runs_scan F (L src).length
    · intro n hn; simp [F, M, Lists.set_ne _ _ hsd, moving_i]
    · exact hFl
    · intro n hn
      have hlt : n < (L src).length := hn
      have hm := moving_step_top L hst hlt
      have h1 : (F n).moveTop src tmp = (M (n + 1)).set dst (L dst ++ List.replicate n 1) := by
        show ((M n).set dst _).moveTop src tmp = _
        rw [moveTop_set hds hdt]
        rw [show M (n + 1) = L.moving src tmp (n + 1) (n + 1) from rfl, ← hm.1]
      have htl : ((F n) tmp).length + 3 ≤ B := by
        simp [F, M, Lists.set_ne _ _ htd, moving_j _ hst, htmp]; omega
      obtain ⟨hl1, hl2⟩ := lenOK_moveTop (hFl n (Nat.le_of_lt hn)) hst htl
      have r1 := runs_moveTop (Q := LenOK B) hst (hFl n (Nat.le_of_lt hn)) hl1 hl2
      rw [h1] at r1
      have hl3 : LenOK B (((M (n + 1)).set dst (L dst ++ List.replicate n 1)).set dst
          (((M (n + 1)).set dst (L dst ++ List.replicate n 1)) dst ++ [1])) := by
        rw [Lists.set_same, Lists.set_set_u]
        have := hFl (n + 1) hn
        simp only [F] at this
        rwa [List.replicate_succ', ← List.append_assoc] at this
      rw [h1] at hl2
      have r2 := runs_push (Q := LenOK B) (i := dst) (e := 1) hl2 hl3
      rw [Lists.set_same, Lists.set_set_u] at r2
      have := r1.seq r2
      simp only [F]
      rw [List.replicate_succ', ← List.append_assoc]
      exact this
  have hF0 : F 0 = L := by
    funext x
    by_cases h : x = dst
    · subst h; simp [F, M]
    · by_cases h2 : x = src
      · subst h2; simp [F, M, Lists.set_ne _ _ h, moving_i]
      · by_cases h3 : x = tmp
        · subst h3; simp [F, M, Lists.set_ne _ _ h, moving_j _ hst, htmp]
        · simp [F, M, Lists.set_ne _ _ h, moving_other _ h2 h3]
  rw [hF0] at hloop
  have hFt : (F (L src).length tmp).length = (L src).length := by
    simp [F, M, Lists.set_ne _ _ hdt.symm, moving_j _ hst, htmp]
  have hmv : Runs (LenOK B) (moveAll tmp src) (F (L src).length) ((F (L src).length).moveAll tmp src) (((F (L src).length tmp).length + 1) * 3) := by
    apply runs_moveAll hts
    intro n m hn hm
    refine lenOK_moving (hFl (L src).length (Nat.le_refl _)) hts ?_ n m
    have : (F (L src).length src).length = 0 := by simp [F, M, Lists.set_ne _ _ hsd, moving_i]
    have := hB src
    omega
  rw [hFt] at hmv
  have hfin : (F (L src).length).moveAll tmp src = L.set dst (L dst ++ List.replicate (L src).length 1) := by
    funext x
    by_cases h : x = dst
    · subst h; simp [F, M, Lists.moveAll, Lists.set, hdt, hds]
    · by_cases h2 : x = src
      · subst h2
        simp [F, M, Lists.moveAll, Lists.set, hsd, hst, htd, moving_i, moving_j _ hst, htmp, List.take_of_length_le]
      · by_cases h3 : x = tmp
        · subst h3; simp [F, M, Lists.moveAll, htmp, Lists.set, h]
        · simp [F, M, Lists.moveAll, Lists.set, h, h2, h3, moving_other _ h2 h3]
  rw [hfin] at hmv
  have := hloop.seq hmv
  exact this.mono (by omega)

theorem mulP_spec {a b dst ta tb : Fin k} (hd : [a, b, dst, ta, tb].Nodup) {B x y : Nat} {L : Lists k}
    (ha : L a = List.replicate x 1) (hb : L b = List.replicate y 1) (hta : L ta = []) (htb : L tb = [])
    (hB : LenOK B L) (hBd : (L dst).length + x * y + 2 ≤ B) :
    Runs (LenOK B) (mulP a b dst ta tb) L (L.set dst (L dst ++ List.replicate (x * y) 1)) (12 * (x + 1) * (y + 2)) := by
  have hab : a ≠ b := by rintro rfl; simp at hd
  have had : a ≠ dst := by rintro rfl; simp at hd
  have hat : a ≠ ta := by rintro rfl; simp at hd
  have hbd : b ≠ dst := by rintro rfl; simp at hd
  have hbt : b ≠ ta := by rintro rfl; simp at hd
  have hbtb : b ≠ tb := by rintro rfl; simp at hd
  have hdt : dst ≠ ta := by rintro rfl; simp at hd
  have hdtb : dst ≠ tb := by rintro rfl; simp at hd
  have hatb : a ≠ tb := by rintro rfl; simp at hd
  have httb : ta ≠ tb := by rintro rfl; simp at hd
  have hxa : (L a).length = x := by simp [ha]
  have hyb : (L b).length = y := by simp [hb]
  let M : Nat → Lists k := fun n => L.moving a ta n n
  let F : Nat → Lists k := fun n => (M n).set dst (L dst ++ List.replicate (n * y) 1)
  have hMl : ∀ n, n ≤ x → LenOK B (M n) := fun n _ =>
    lenOK_moving hB hat (by rw [hta]; have := hB a; simp; omega) n n
  have hFl : ∀ n, n ≤ x → LenOK B (F n) := fun n hn => lenOK_set (hMl n hn) dst (by
    have := Nat.mul_le_mul_right y hn
    simp; omega)
  have hloop : Runs (LenOK B) (.loop a nonEmpty (.seq (moveTop a ta) (copyLenP b dst tb))) (F 0) (F x)
      ((x + 1) * ((2 + 8 * (y + 1)) + 1)) := by
    apply runs_scan F x
    · intro n hn; simp [F, M, Lists.set_ne _ _ had, moving_i, hxa]
    · exact hFl
    · intro n hn
      have hm := moving_step_top L hat (n := n) (by omega)
      have h1 : (F n).moveTop a ta = (M (n + 1)).set dst (L dst ++ List.replicate (n * y) 1) := by
        show ((M n).set dst _).moveTop a ta = _
        rw [moveTop_set had.symm hdt]
        rw [show M (n + 1) = L.moving a ta (n + 1) (n + 1) from rfl, ← hm.1]
      have htl : ((F n) ta).length + 3 ≤ B := by
        simp [F, M, Lists.set_ne _ _ hdt.symm, moving_j _ hat, hta]
        have := hB a; omega
      obtain ⟨hl1, hl2⟩ := lenOK_moveTop (hFl n (Nat.le_of_lt hn)) hat htl
      have r1 := runs_moveTop (Q := LenOK B) hat (hFl n (Nat.le_of_lt hn)) hl1 hl2
      rw [h1] at r1
      rw [h1] at hl2
      have hn1 := Nat.mul_le_mul_right y (Nat.succ_le_of_lt hn)
      have hsm := Nat.succ_mul n y
      have hYtb : ((M (n + 1)).set dst (L dst ++ List.replicate (n * y) 1)) tb = [] := by
        rw [Lists.set_ne _ _ hdtb.symm]
        simp only [M]
        rw [moving_other _ hatb.symm httb.symm, htb]
      have hYb : ((M (n + 1)).set dst (L dst ++ List.replicate (n * y) 1)) b = L b := by
        rw [Lists.set_ne _ _ hbd]
        simp only [M]
        rw [moving_other _ hab.symm hbt]
      have r2 := copyLen_spec (src := b) (dst := dst) (tmp := tb)
        (by simp [hbd, hbtb, hdtb])
        (L := (M (n + 1)).set dst (L dst ++ List.replicate (n * y) 1)) (B := B) hYtb hl2
        (by rw [hYb, Lists.set_same]; simp; omega)
      rw [hYb, Lists.set_same, Lists.set_set_u] at r2
      have r3 := r1.seq r2
      have e : F (n + 1) = (M (n + 1)).set dst ((L dst ++ List.replicate (n * y) 1) ++ List.replicate (L b).length 1) := by
        simp only [F]
        rw [Nat.succ_mul, ← List.replicate_append_replicate, List.append_assoc, hyb]
      rw [e]
      refine r3.mono ?_
      omega
  have hF0 : F 0 = L := by
    funext x'
    by_cases h : x' = dst
    · subst h; simp [F, M]
    · by_cases h2 : x' = a
      · subst h2; simp [F, M, Lists.set_ne _ _ h, moving_i]
      · by_cases h3 : x' = ta
        · subst h3; simp [F, M, Lists.set_ne _ _ h, moving_j _ hat, hta]
        · simp [F, M, Lists.set_ne _ _ h, moving_other _ h2 h3]
  rw [hF0] at hloop
  have hFt : (F x ta).length = x := by
    simp [F, M, Lists.set_ne _ _ hdt.symm, moving_j _ hat, hta, hxa]
  have hmv : Runs (LenOK B) (moveAll ta a) (F x) ((F x).moveAll ta a) (((F x ta).length + 1) * 3) := by
    apply runs_moveAll hat.symm
    intro n m hn hm
    refine lenOK_moving (hFl x (Nat.le_refl _)) hat.symm ?_ n m
    have : (F x a).length = 0 := by simp [F, M, Lists.set_ne _ _ had, moving_i, hxa]
    have := hB a
    omega
  rw [hFt] at hmv
  have hfin : (F x).moveAll ta a = L.set dst (L dst ++ List.replicate (x * y) 1) := by
    funext x'
    by_cases h : x' = dst
    · subst h; simp [F, M, Lists.moveAll, Lists.set, hdt, had.symm]
    · by_cases h2 : x' = a
      · subst h2
        simp [F, M, Lists.moveAll, Lists.set, had, hat, hdt.symm, moving_i, moving_j _ hat, hta, List.take_of_length_le, hxa, ha]
      · by_cases h3 : x' = ta
        · subst h3; simp [F, M, Lists.moveAll, hta, Lists.set, h]
        · simp [F, M, Lists.moveAll, Lists.set, h, h2, h3, moving_other _ h2 h3]
  rw [hfin] at hmv
  have := hloop.seq hmv
  refine this.mono ?_
  have h12 : 2 + 8 * (y + 1) + 1 + 3 ≤ 12 * (y + 2) := by omega
  calc (x + 1) * (2 + 8 * (y + 1) + 1) + (x + 1) * 3 = (x + 1) * (2 + 8 * (y + 1) + 1 + 3) := (Nat.mul_add _ _ _).symm
    _ ≤ (x + 1) * (12 * (y + 2)) := Nat.mul_le_mul_left _ h12
    _ = 12 * (x + 1) * (y + 2) := by rw [Nat.mul_assoc, Nat.mul_left_comm]

theorem powStep_spec {pw n p2 ta tb : Fin k} (hd : [pw, n, p2, ta, tb].Nodup) {B x y : Nat} {L : Lists k}
    (hpw : L pw = List.replicate x 1) (hn : L n = List.replicate y 1) (hp2 : L p2 = []) (hta : L ta = [])
    (htb : L tb = []) (hB : LenOK B L) (hBd : x * y + x + 2 ≤ B) :
    Runs (LenOK B) (powStepP pw n p2 ta tb) L (L.set pw (List.replicate (x * y) 1))
      (20 * (x + 1) * (y + 2) + 3 * (x * y + 1)) := by
  have hpp : pw ≠ p2 := by rintro rfl; simp at hd
  have hxa : (L pw).length = x := by simp [hpw]
  have hm := mulP_spec hd hpw hn hta htb hB (B := B) (by rw [hp2]; simp; omega)
  rw [hp2, List.nil_append] at hm
  have hL1 : LenOK B (L.set p2 (List.replicate (x * y) 1)) := lenOK_set hB p2 (by simp; omega)
  have hc := clearP_spec (Q := LenOK B) (i := pw) (L := L.set p2 (List.replicate (x * y) 1)) (by
    intro m hm'
    refine lenOK_set hL1 pw ?_
    have := hB pw
    simp [Lists.set_ne _ _ hpp] at hm' ⊢
    omega)
  have hL2 : LenOK B ((L.set p2 (List.replicate (x * y) 1)).set pw []) := lenOK_set hL1 pw (by simp; omega)
  have hmv := runs_moveAll (Q := LenOK B) (i := p2) (j := pw) hpp.symm
    (L := (L.set p2 (List.replicate (x * y) 1)).set pw []) (by
      intro n' m hn' hm'
      refine lenOK_moving hL2 hpp.symm ?_ n' m
      simp [Lists.set_ne _ _ hpp.symm]; omega)
  have hfin : ((L.set p2 (List.replicate (x * y) 1)).set pw []).moveAll p2 pw = L.set pw (List.replicate (x * y) 1) := by
    funext x'
    by_cases h : x' = pw
    · subst h; simp [Lists.moveAll, Lists.set, hpp.symm, hpp]
    · by_cases h2 : x' = p2
      · subst h2; simp [Lists.moveAll, Lists.set, hp2, h, hpp]
      · simp [Lists.moveAll, Lists.set, h, h2]
  rw [hfin] at hmv
  have := hm.seq (hc.seq hmv)
  refine this.mono ?_
  simp [Lists.set_ne _ _ hpp, Lists.set_ne _ _ hpp.symm, hxa]
  have hP : x + 1 ≤ (x + 1) * (y + 2) := Nat.le_mul_of_pos_right _ (by omega)
  rw [Nat.mul_assoc 12, Nat.mul_assoc 20]
  generalize (x + 1) * (y + 2) = P at hP ⊢
  omega

theorem repeat_spec {Q : Lists k → Prop} {i : Fin k} {p : LProg k} (f : Nat → Lists k) (c m : Nat)
    (hstep : ∀ j, j < m → Runs Q p (f j) (f (j + 1)) c) (hq : Q (f m)) :
    Runs Q (repeatP i p m) (f 0) (f m) (m * c + 1) := by
  induction m generalizing f with
  | zero =>
    have := runs_skip (Q := Q) i hq
    simpa [repeatP] using this
  | succ m ih =>
    have := (hstep 0 (Nat.succ_pos m)).seq (ih (fun j => f (j + 1)) (fun j hj => hstep (j + 1) (by omega)) hq)
    refine this.mono ?_
    rw [Nat.succ_mul]; omega

end Complexity
