import Complexity.TmplLM
import Complexity.TqbfEvalSpec

namespace Complexity

variable {k : Nat}

/-! ## Generic infrastructure -/

def TlmFix (L L' : Lists k) (S : List (Fin k)) : Prop := ∀ x, x ∉ S → L' x = L x

theorem tlm_lenOK_fix {B : Nat} {L L' : Lists k} {S : List (Fin k)} (hL : LenOK B L) (hf : TlmFix L L' S)
    (hS : ∀ x ∈ S, (L' x).length + 2 ≤ B) : LenOK B L' := by
  intro x
  by_cases hx : x ∈ S
  · exact hS x hx
  · rw [hf x hx]; exact hL x

theorem tlm_set_set (L : Lists k) (i : Fin k) (a b : List Nat) : (L.set i a).set i b = L.set i b := by
  funext x; by_cases h : x = i <;> simp [Lists.set, h]

theorem tlm_set_self (L : Lists k) (i : Fin k) : L.set i (L i) = L := by
  funext x; by_cases h : x = i <;> simp [Lists.set, h]

theorem tlm_set_comm (L : Lists k) {i j : Fin k} (h : i ≠ j) (a b : List Nat) :
    (L.set i a).set j b = (L.set j b).set i a := by
  funext x
  by_cases h1 : x = i
  · subst h1; simp [Lists.set, h]
  · by_cases h2 : x = j
    · subst h2; simp [Lists.set, h1]
    · simp [Lists.set, h1, h2]

theorem tlm_eq_set {L L' : Lists k} {i : Fin k} {l : List Nat} (h1 : L' i = l) (h2 : ∀ x, x ≠ i → L' x = L x) :
    L' = L.set i l := by
  funext x; by_cases h : x = i
  · subst h; simp [h1]
  · simp [Lists.set, h, h2 x h]

theorem tlm_step_mvTop {B : Nat} {i j : Fin k} (hij : i ≠ j) {L : Lists k} (hL : LenOK B L) (hb : (L j).length + 3 ≤ B) :
    Step B 2 (moveTop i j) L (fun L' => L' = L.moveTop i j) := by
  obtain ⟨h1, h2⟩ := lenOK_moveTop hL hij hb
  exact ⟨_, runs_moveTop (Q := LenOK B) hij hL h1 h2, h2, rfl⟩

theorem tlm_step_mvAll {B : Nat} {i j : Fin k} (hij : i ≠ j) {L : Lists k} (hL : LenOK B L)
    (hb : (L j).length + (L i).length + 2 ≤ B) :
    Step B (((L i).length + 1) * 3) (moveAll i j) L (fun L' => L' = L.moveAll i j) :=
  ⟨_, runs_moveAll (Q := LenOK B) hij (fun n m _ _ => lenOK_moving hL hij hb n m), lenOK_moveAll hL hij hb, rfl⟩

theorem tlm_moveTop_step_facts {L' : Lists k} {i j : Fin k} (hij : i ≠ j) (L0 : Lists k) {m : Nat}
    (hm : m < (L0 i).length) (h1 : L' i = (L0 i).take ((L0 i).length - m))
    (h2 : L' j = L0 j ++ (L0 i).reverse.take m) :
    (L'.moveTop i j) i = (L0 i).take ((L0 i).length - (m + 1)) ∧
    (L'.moveTop i j) j = L0 j ++ (L0 i).reverse.take (m + 1) := by
  obtain ⟨e1, _⟩ := moving_step_top L0 hij hm
  have hi : (L'.moveTop i j) i = (L0.moving i j m m).moveTop i j i := by
    rw [moveTop_i, moveTop_i, h1, moving_i]
  have hj : (L'.moveTop i j) j = (L0.moving i j m m).moveTop i j j := by
    rw [moveTop_j hij, moveTop_j hij, h1, h2, moving_i, moving_j _ hij]
  rw [e1, moving_i] at hi; rw [e1, moving_j _ hij] at hj
  exact ⟨hi, hj⟩

/-! ## Loops moving elements -/

def tlm_loopA (c ta j j' : Fin k) : LProg k :=
  .loop c nonEmpty (.seq (moveTop c ta) (.ite j nonEmpty (moveTop j j') (skipP j)))

theorem tlm_nonEmpty_iff {l : List Nat} : nonEmpty (lastSym l) = true ↔ l ≠ [] := by
  simp [nonEmpty, lastSym_eq_three]

theorem tlm_step_loopA {B : Nat} {c ta j j' : Fin k} (hct : c ≠ ta) (hcj : c ≠ j) (hcj' : c ≠ j') (htj : ta ≠ j)
    (htj' : ta ≠ j') (hjj' : j ≠ j') {L : Lists k} (hL : LenOK B L)
    (hb1 : (L c).length + (L ta).length + 3 ≤ B) (hb2 : (L j).length + (L j').length + 3 ≤ B) :
    Step B (6 * (L c).length + 6) (tlm_loopA c ta j j') L (fun L' =>
      L' c = [] ∧ L' ta = L ta ++ (L c).reverse ∧ L' j = (L j).take ((L j).length - (L c).length) ∧
      L' j' = L j' ++ (L j).reverse.take (L c).length ∧ TlmFix L L' [c, ta, j, j']) := by
  have hmain := runs_loop (Q := LenOK B) (i := c) (c := nonEmpty)
    (p := .seq (moveTop c ta) (.ite j nonEmpty (moveTop j j') (skipP j)))
    (I := fun L' => LenOK B L' ∧ ∃ m ≤ (L c).length, L' c = (L c).take ((L c).length - m) ∧
      L' ta = L ta ++ (L c).reverse.take m ∧ L' j = (L j).take ((L j).length - m) ∧
      L' j' = L j' ++ (L j).reverse.take m ∧ TlmFix L L' [c, ta, j, j'])
    (μ := fun L' => (L' c).length) (T := 5) (fun L' h => h.1) ?_ L
    ⟨hL, 0, Nat.zero_le _, by simp [List.take_of_length_le], by simp, by simp, by simp, fun x _ => rfl⟩
  · obtain ⟨L', hr, ⟨hl, m, hm, h1, h2, h3, h4, hf⟩, hc⟩ := hmain
    have hc0 : L' c = [] := lastSym_eq_three.1 (by simpa [nonEmpty] using hc)
    have hmn : m = (L c).length := by
      rw [hc0] at h1
      have := congrArg List.length h1.symm
      simp at this; omega
    subst hmn
    refine ⟨L', hr.mono (by omega), hl, hc0, ?_, ?_, ?_, hf⟩
    · rw [h2]; simp [List.take_of_length_le]
    · rw [h3]
    · rw [h4]
  · rintro L' ⟨hl, m, hm, h1, h2, h3, h4, hf⟩ hc
    have hne : L' c ≠ [] := tlm_nonEmpty_iff.1 hc
    have hlen : (L' c).length = (L c).length - m := by rw [h1]; simp
    have hmn : m < (L c).length := by
      have : 0 < (L' c).length := List.length_pos_iff.2 hne
      omega
    have hLta : (L' ta).length = (L ta).length + m := by
      rw [h2]; simp; omega
    -- first move
    obtain ⟨f1, f2⟩ := tlm_moveTop_step_facts hct L hmn h1 h2
    have e1 := tlm_step_mvTop hct hl (by omega : (L' ta).length + 3 ≤ B)
    obtain ⟨M1, hM1, hlM1, hM1e⟩ := e1
    subst hM1e
    have gc : (L'.moveTop c ta) c = (L c).take ((L c).length - (m + 1)) := f1
    have gta : (L'.moveTop c ta) ta = L ta ++ (L c).reverse.take (m + 1) := f2
    have gj : (L'.moveTop c ta) j = L' j := moveTop_other (Ne.symm hcj) (Ne.symm htj)
    have gj' : (L'.moveTop c ta) j' = L' j' := moveTop_other (Ne.symm hcj') (Ne.symm htj')
    have gother : ∀ x, x ≠ c → x ≠ ta → (L'.moveTop c ta) x = L' x := fun x h h' => moveTop_other h h'
    by_cases hmj : m < (L j).length
    · have hLj : L' j ≠ [] := by
        rw [h3]; intro h; have := congrArg List.length h; simp at this; omega
      have hLj' : (L' j').length = (L j').length + m := by
        rw [h4]; simp; omega
      have hcond : nonEmpty (lastSym ((L'.moveTop c ta) j)) = true := tlm_nonEmpty_iff.2 (by rw [gj]; exact hLj)
      obtain ⟨M2, hM2, hlM2, hM2e⟩ := tlm_step_mvTop hjj' hlM1 (by rw [gj']; omega : ((L'.moveTop c ta) j').length + 3 ≤ B)
      subst hM2e
      obtain ⟨g1, g2⟩ := tlm_moveTop_step_facts (L' := L'.moveTop c ta) hjj' L hmj (by rw [gj]; exact h3) (by rw [gj']; exact h4)
      refine ⟨_, (hM1.seq (hM2.iteT hlM1 hcond)).mono (by omega), ⟨hlM2, m + 1, by omega, ?_, ?_, g1, g2, ?_⟩, ?_⟩
      · rw [moveTop_other hcj hcj', gc]
      · rw [moveTop_other htj htj', gta]
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        obtain ⟨x1, x2, x3, x4⟩ := hx
        rw [moveTop_other x3 x4, gother x x1 x2]; exact hf x (by simp [x1, x2, x3, x4])
      · show (((L'.moveTop c ta).moveTop j j') c).length < (L' c).length
        rw [moveTop_other hcj hcj', gc]
        simp; omega
    · have hLj : L' j = [] := by rw [h3]; simp; omega
      have hcond : nonEmpty (lastSym ((L'.moveTop c ta) j)) = false := by
        rw [gj, hLj]; simp [nonEmpty, lastSym]
      refine ⟨_, (hM1.seq ((runs_skip j hlM1).iteF hlM1 hcond)).mono (by omega), ⟨hlM1, m + 1, by omega, gc, gta, ?_, ?_, ?_⟩, ?_⟩
      · rw [gj, hLj]; simp; omega
      · rw [gj']
        have : (L j).reverse.take (m + 1) = (L j).reverse.take m := by
          rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
        rw [this]; exact h4
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        obtain ⟨x1, x2, x3, x4⟩ := hx
        rw [gother x x1 x2]; exact hf x (by simp [x1, x2, x3, x4])
      · show ((L'.moveTop c ta) c).length < (L' c).length
        rw [gc]; simp; omega

/-! ## Emitting tokens -/

def tlm_ebits (t : Nat) : List Nat := (tokBits t).map bit01

def tlm_bts (ts : List Nat) : List Nat := (toBits ts).map bit01

def tlm_repL : Nat → List Nat → List Nat
  | 0, _ => []
  | n + 1, l => tlm_repL n l ++ l

theorem tlm_repL_succ' (n : Nat) (l : List Nat) : tlm_repL (n + 1) l = l ++ tlm_repL n l := by
  induction n with
  | zero => simp [tlm_repL]
  | succ n ih =>
    show tlm_repL (n + 1) l ++ l = l ++ (tlm_repL n l ++ l)
    rw [ih]; simp

theorem tlm_repL_length (n : Nat) (l : List Nat) : (tlm_repL n l).length = n * l.length := by
  induction n with
  | zero => simp [tlm_repL]
  | succ n ih => simp [tlm_repL, ih, Nat.succ_mul]

theorem tlm_ebits_length (t : Nat) : (tlm_ebits t).length = 4 := by simp [tlm_ebits, tokBits]

theorem tlm_toBits_append (xs ys : List Nat) : toBits (xs ++ ys) = toBits xs ++ toBits ys := by
  simp [toBits]

theorem tlm_bts_append (xs ys : List Nat) : tlm_bts (xs ++ ys) = tlm_bts xs ++ tlm_bts ys := by
  simp [tlm_bts, tlm_toBits_append]

theorem tlm_toBits_length (ts : List Nat) : (toBits ts).length = 4 * ts.length := by
  induction ts with
  | nil => simp [toBits]
  | cons t ts ih => simp [toBits, tokBits] at ih ⊢; omega

theorem tlm_bts_length (ts : List Nat) : (tlm_bts ts).length = 4 * ts.length := by
  simp [tlm_bts, tlm_toBits_length]

theorem tlm_bts_replicate (n t : Nat) : tlm_bts (List.replicate n t) = tlm_repL n (tlm_ebits t) := by
  induction n with
  | zero => simp [tlm_bts, toBits, tlm_repL]
  | succ n ih =>
    rw [List.replicate_succ', tlm_bts_append, ih]
    simp [tlm_repL, tlm_bts, toBits, tlm_ebits]

theorem tlm_seqL_cons_ne (tt : TT k) (p : LProg k) (ps : List (LProg k)) (h : ps ≠ []) :
    seqL tt (p :: ps) = .seq p (seqL tt ps) := by
  cases ps with
  | nil => exact absurd rfl h
  | cons q rs => rfl

theorem tlm_step_push_p {B : Nat} (i : Fin k) (e : Nat) {L : Lists k} (hL : LenOK B L) (hb : (L i).length + 3 ≤ B) :
    Step B 1 (.push i e) L (fun L' => L' = L.set i (L i ++ [e])) :=
  have h := lenOK_set hL i (l := L i ++ [e]) (by simp; omega)
  ⟨_, runs_push (Q := LenOK B) hL h, h, rfl⟩

theorem tlm_step_pushes (tt : TT k) {B : Nat} : ∀ (es : List Nat) {L : Lists k}, LenOK B L →
    (L tt.out).length + es.length + 2 ≤ B →
    Step B (es.length + 1) (seqL tt (es.map (fun e => LProg.push tt.out e))) L
      (fun L' => L' = L.set tt.out (L tt.out ++ es))
  | [], L, hL, _ => ⟨L, runs_skip _ hL, hL, by simp [tlm_set_self]⟩
  | [e], L, hL, hb =>
    (tlm_step_push_p _ _ hL (by simp at hb; omega)).mono (by simp) (by intro L' h; simpa using h)
  | e :: e' :: es, L, hL, hb => by
    rw [List.map_cons, tlm_seqL_cons_ne _ _ _ (by simp)]
    refine Step.seq' (T₂ := (e' :: es).length + 1) (tlm_step_push_p _ _ hL (by simp at hb; omega)) (fun L1 hl1 h1 => ?_) (by simp; omega)
    subst h1
    have := tlm_step_pushes tt (e' :: es) hl1 (by simp at hb ⊢; omega)
    refine this.mono (Nat.le_refl _) ?_
    intro L' h; rw [h, tlm_set_set]; simp

theorem tlm_step_emitTok (tt : TT k) {B : Nat} (t : Nat) {L : Lists k} (hL : LenOK B L)
    (hb : (L tt.out).length + 6 ≤ B) :
    Step B 5 (emitTokP tt t) L (fun L' => L' = L.set tt.out (L tt.out ++ tlm_ebits t)) := by
  have := tlm_step_pushes tt (tlm_ebits t) hL (by rw [tlm_ebits_length]; omega)
  have e : (tlm_ebits t).map (fun e => LProg.push tt.out e) =
      (tokBits t).map (fun b => LProg.push tt.out (if b then 1 else 0)) := by
    simp [tlm_ebits, bit01, List.map_map, Function.comp_def]
  rw [e] at this
  exact this.mono (by simp [tlm_ebits_length]) (fun _ h => h)

theorem tlm_step_emitRep (tt : TT k) {B : Nat} (t : Nat) : ∀ (n : Nat) {L : Lists k}, LenOK B L →
    (L tt.out).length + 4 * n + 2 ≤ B →
    Step B (5 * n + 1) (seqL tt (List.replicate n (emitTokP tt t))) L
      (fun L' => L' = L.set tt.out (L tt.out ++ tlm_repL n (tlm_ebits t)))
  | 0, L, hL, _ => ⟨L, runs_skip _ hL, hL, by simp [tlm_repL, tlm_set_self]⟩
  | 1, L, hL, hb =>
    (tlm_step_emitTok tt t hL (by omega)).mono (by omega) (by intro L' h; simpa [tlm_repL] using h)
  | n + 2, L, hL, hb => by
    rw [List.replicate_succ, tlm_seqL_cons_ne _ _ _ (by simp)]
    refine Step.seq' (T₂ := 5 * (n + 1) + 1) (tlm_step_emitTok tt t hL (by omega)) (fun L1 hl1 h1 => ?_) (by omega)
    subst h1
    have := tlm_step_emitRep tt t (n + 1) hl1 (by simp [tlm_ebits_length]; omega)
    refine this.mono (Nat.le_refl _) ?_
    intro L' h
    rw [h, tlm_set_set, tlm_repL_succ' (n + 1)]; simp [List.append_assoc]

def tlm_loopB (tt : TT k) (c d : Fin k) (t : Nat) : LProg k :=
  .loop c nonEmpty (.seq (moveTop c d) (emitTokP tt t))

theorem tlm_step_loopB (tt : TT k) {B : Nat} {c d : Fin k} (t : Nat) (hcd : c ≠ d) (hco : c ≠ tt.out)
    (hdo : d ≠ tt.out) {L : Lists k} (hL : LenOK B L)
    (hb1 : (L c).length + (L d).length + 3 ≤ B) (hb2 : (L tt.out).length + 4 * (L c).length + 2 ≤ B) :
    Step B (8 * (L c).length + 8) (tlm_loopB tt c d t) L (fun L' =>
      L' c = [] ∧ L' d = L d ++ (L c).reverse ∧ L' tt.out = L tt.out ++ tlm_repL (L c).length (tlm_ebits t) ∧
      TlmFix L L' [c, d, tt.out]) := by
  have hmain := runs_loop (Q := LenOK B) (i := c) (c := nonEmpty)
    (p := .seq (moveTop c d) (emitTokP tt t))
    (I := fun L' => LenOK B L' ∧ ∃ m ≤ (L c).length, L' c = (L c).take ((L c).length - m) ∧
      L' d = L d ++ (L c).reverse.take m ∧ L' tt.out = L tt.out ++ tlm_repL m (tlm_ebits t) ∧
      TlmFix L L' [c, d, tt.out])
    (μ := fun L' => (L' c).length) (T := 7) (fun L' h => h.1) ?_ L
    ⟨hL, 0, Nat.zero_le _, by simp [List.take_of_length_le], by simp, by simp [tlm_repL], fun x _ => rfl⟩
  · obtain ⟨L', hr, ⟨hl, m, hm, h1, h2, h3, hf⟩, hc⟩ := hmain
    have hc0 : L' c = [] := lastSym_eq_three.1 (by simpa [nonEmpty] using hc)
    have hmn : m = (L c).length := by
      rw [hc0] at h1
      have := congrArg List.length h1.symm
      simp at this; omega
    subst hmn
    refine ⟨L', hr.mono (by omega), hl, hc0, ?_, h3, hf⟩
    rw [h2]; simp [List.take_of_length_le]
  · rintro L' ⟨hl, m, hm, h1, h2, h3, hf⟩ hc
    have hne : L' c ≠ [] := tlm_nonEmpty_iff.1 hc
    have hlen : (L' c).length = (L c).length - m := by rw [h1]; simp
    have hmn : m < (L c).length := by
      have : 0 < (L' c).length := List.length_pos_iff.2 hne
      omega
    have hLd : (L' d).length = (L d).length + m := by
      rw [h2]; simp; omega
    obtain ⟨f1, f2⟩ := tlm_moveTop_step_facts hcd L hmn h1 h2
    obtain ⟨M1, hM1, hlM1, hM1e⟩ := tlm_step_mvTop hcd hl (by omega : (L' d).length + 3 ≤ B)
    subst hM1e
    have go : (L'.moveTop c d) tt.out = L' tt.out := moveTop_other (Ne.symm hco) (Ne.symm hdo)
    obtain ⟨M2, hM2, hlM2, hM2e⟩ := tlm_step_emitTok tt t hlM1 (by rw [go, h3, List.length_append, tlm_repL_length, tlm_ebits_length]; omega)
    subst hM2e
    refine ⟨_, (hM1.seq hM2).mono (by omega), ⟨hlM2, m + 1, by omega, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [Lists.set_ne _ _ hco, f1]
    · rw [Lists.set_ne _ _ hdo, f2]
    · rw [Lists.set_same, go, h3, tlm_repL, List.append_assoc]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      obtain ⟨x1, x2, x3⟩ := hx
      rw [Lists.set_ne _ _ x3, moveTop_other x1 x2]; exact hf x (by simp [x1, x2, x3])
    · show (((L'.moveTop c d).set tt.out _) c).length < (L' c).length
      rw [Lists.set_ne _ _ hco, f1]; simp; omega

/-! ## Comparison -/

local macro "tlm_dis" : tactic => `(tactic| first | assumption | (apply Ne.symm; assumption))

local macro "tlm_nin" : tactic =>
  `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; repeat' apply And.intro
             all_goals tlm_dis))

theorem tlm_step_ltP_ne (tt : TT k) {B : Nat} {a b : Fin k} (hab : a ≠ b) (hat : a ≠ tt.ta)
    (hab' : a ≠ tt.tb') (haf : a ≠ tt.fl) (hbt : b ≠ tt.ta) (hbb' : b ≠ tt.tb') (hbf : b ≠ tt.fl)
    (htb : tt.ta ≠ tt.tb') (htf : tt.ta ≠ tt.fl) (hb'f : tt.tb' ≠ tt.fl)
    {L : Lists k} (hL : LenOK B L) {p q : Nat} (hLa : L a = List.replicate p 1) (hLb : L b = List.replicate q 1)
    (hta : L tt.ta = []) (htb' : L tt.tb' = []) (hfl : L tt.fl = []) (hp : p + 3 ≤ B) (hq : q + 3 ≤ B) :
    Step B (12 * p + 14) (ltP tt a b) L (fun L' => L' = L.set tt.fl (if p < q then [0] else [])) := by
  have hdef : ltP tt a b = .seq (tlm_loopA a tt.ta b tt.tb')
      (.seq (.ite b nonEmpty (.push tt.fl 0) (skipP b)) (.seq (moveAll tt.ta a) (moveAll tt.tb' b))) := rfl
  rw [hdef]
  have h1 := tlm_step_loopA hat hab hab' (Ne.symm hbt) htb hbb' hL (by rw [hLa, hta]; simp; omega)
    (by rw [hLb, htb']; simp; omega)
  have h1' : Step B (6 * p + 6) (tlm_loopA a tt.ta b tt.tb') L (fun L' => L' a = [] ∧
      L' tt.ta = List.replicate p 1 ∧ L' b = List.replicate (q - p) 1 ∧ L' tt.tb' = List.replicate (min p q) 1 ∧
      TlmFix L L' [a, tt.ta, b, tt.tb']) :=
    h1.mono (by rw [hLa]; simp) (fun L' ⟨g1, g2, g3, g4, gf⟩ =>
      ⟨g1, by rw [g2, hta, hLa]; simp, by rw [g3, hLb, hLa]; simp [List.take_replicate],
       by rw [g4, htb', hLb, hLa]; simp [List.take_replicate], gf⟩)
  refine Step.seq' (T₁ := 6 * p + 6) (T₂ := 2 + (3 * p + 3 + (3 * p + 3))) h1'
    (fun L1 hl1 ⟨g1, g2, g3, g4, gf⟩ => ?_) (by omega)
  have hfl1 : L1 tt.fl = [] := by rw [gf _ (by tlm_nin)]; exact hfl
  have h2 : Step B 2 (.ite b nonEmpty (.push tt.fl 0) (skipP b)) L1
      (fun L2 => L2 = L1.set tt.fl (if p < q then [0] else [])) := by
    by_cases hpq : p < q
    · have hc : nonEmpty (lastSym (L1 b)) = true := tlm_nonEmpty_iff.2 (by
        rw [g3]; intro h; have := congrArg List.length h; simp at this; omega)
      exact (Step.iteT (T := 1) hl1 hc (tlm_step_push_p _ 0 hl1 (by rw [hfl1]; simp; omega))).mono (by omega)
        (fun L' h => by rw [h, hfl1]; simp [hpq])
    · have hc : nonEmpty (lastSym (L1 b)) = false := by
        have : L1 b = [] := by rw [g3]; simp; omega
        rw [this]; simp [nonEmpty, lastSym]
      exact Step.iteF (T := 1) hl1 hc ⟨L1, runs_skip b hl1, hl1, by simp only [hpq, if_false]; rw [← hfl1, tlm_set_self]⟩
  refine Step.seq' (T₁ := 2) (T₂ := 3 * p + 3 + (3 * p + 3)) h2 (fun L2 hl2 e2 => ?_) (by omega)
  subst e2
  have s2a : (L1.set tt.fl (if p < q then [0] else [])) a = [] := by rw [Lists.set_ne _ _ haf, g1]
  have s2t : (L1.set tt.fl (if p < q then [0] else [])) tt.ta = List.replicate p 1 := by
    rw [Lists.set_ne _ _ htf, g2]
  have s2b : (L1.set tt.fl (if p < q then [0] else [])) tt.tb' = List.replicate (min p q) 1 := by
    rw [Lists.set_ne _ _ hb'f, g4]
  have s2bb : (L1.set tt.fl (if p < q then [0] else [])) b = List.replicate (q - p) 1 := by
    rw [Lists.set_ne _ _ hbf, g3]
  refine Step.seq' (T₁ := 3 * p + 3) (T₂ := 3 * p + 3)
    ((tlm_step_mvAll (Ne.symm hat) hl2 (by rw [s2a, s2t]; simp; omega)).mono (by rw [s2t]; simp; omega) (fun _ h => h))
    (fun L3 hl3 e3 => ?_) (by omega)
  subst e3
  have t3b : (((L1.set tt.fl (if p < q then [0] else [])).moveAll tt.ta a)) tt.tb' = List.replicate (min p q) 1 := by
    rw [moveAll_other (Ne.symm htb) (Ne.symm hab'), s2b]
  have t3bb : (((L1.set tt.fl (if p < q then [0] else [])).moveAll tt.ta a)) b = List.replicate (q - p) 1 := by
    rw [moveAll_other hbt (Ne.symm hab), s2bb]
  refine ((tlm_step_mvAll (Ne.symm hbb') hl3 (by rw [t3b, t3bb]; simp; omega)).mono
    (by rw [t3b]; simp; omega) ?_)
  intro L4 e4
  subst e4
  funext x
  by_cases xa : x = a
  · rw [xa]
    rw [moveAll_other hab' hab, moveAll_j (Ne.symm hat), s2a, s2t, Lists.set_ne _ _ haf, hLa]; simp
  by_cases xb : x = b
  · rw [xb]
    rw [moveAll_j (Ne.symm hbb'), moveAll_other hbt (Ne.symm hab), s2bb, t3b, Lists.set_ne _ _ hbf, hLb]
    simp [List.replicate_append_replicate]
    congr 1; omega
  by_cases xt : x = tt.ta
  · rw [xt]
    rw [moveAll_other htb (Ne.symm hbt), moveAll_i, Lists.set_ne _ _ htf, hta]
  by_cases xt' : x = tt.tb'
  · rw [xt']
    rw [moveAll_i, Lists.set_ne _ _ hb'f, htb']
  by_cases xf : x = tt.fl
  · rw [xf]
    rw [moveAll_other (Ne.symm hb'f) (Ne.symm hbf), moveAll_other (Ne.symm htf) (Ne.symm haf)]; simp
  rw [moveAll_other xt' xb, moveAll_other xt xa, Lists.set_ne _ _ xf, Lists.set_ne _ _ xf, gf x (by simp [xa, xt, xb, xt'])]

def tlm_loopS (a ta tb' : Fin k) : LProg k :=
  .loop a nonEmpty (.seq (moveTop a ta) (.ite a nonEmpty (moveTop a tb') (skipP a)))

theorem tlm_rep_dropLast (n : Nat) : (List.replicate n 1).dropLast = List.replicate (n - 1) 1 := by
  simp [List.dropLast_replicate]

theorem tlm_step_loopS {B : Nat} {a ta tb' : Fin k} (hat : a ≠ ta) (hab : a ≠ tb') (htb : ta ≠ tb')
    {L : Lists k} (hL : LenOK B L) {p : Nat} (hLa : L a = List.replicate p 1) (hta : L ta = [])
    (htb' : L tb' = []) (hp : p + 3 ≤ B) :
    Step B (6 * p + 6) (tlm_loopS a ta tb') L (fun L' => L' a = [] ∧ L' ta = List.replicate ((p + 1) / 2) 1 ∧
      L' tb' = List.replicate (p / 2) 1 ∧ TlmFix L L' [a, ta, tb']) := by
  have hmain := runs_loop (Q := LenOK B) (i := a) (c := nonEmpty)
    (p := .seq (moveTop a ta) (.ite a nonEmpty (moveTop a tb') (skipP a)))
    (I := fun L' => LenOK B L' ∧ ∃ r ≤ p, (r % 2 = 0 ∨ r = p) ∧ L' a = List.replicate (p - r) 1 ∧
      L' ta = List.replicate ((r + 1) / 2) 1 ∧ L' tb' = List.replicate (r / 2) 1 ∧ TlmFix L L' [a, ta, tb'])
    (μ := fun L' => (L' a).length) (T := 5) (fun L' h => h.1) ?_ L
    ⟨hL, 0, Nat.zero_le _, Or.inl rfl, by simp [hLa], by simp [hta], by simp [htb'], fun x _ => rfl⟩
  · obtain ⟨L', hr, ⟨hl, r, hr', hpar, h1, h2, h3, hf⟩, hc⟩ := hmain
    have hc0 : L' a = [] := lastSym_eq_three.1 (by simpa [nonEmpty] using hc)
    have hrp : r = p := by
      rw [hc0] at h1
      have := congrArg List.length h1
      simp at this; omega
    subst hrp
    refine ⟨L', ?_, hl, hc0, h2, h3, hf⟩
    rw [hLa] at hr; simp at hr; exact hr.mono (by omega)
  · rintro L' ⟨hl, r, hr, hpar, h1, h2, h3, hf⟩ hc
    have hne : L' a ≠ [] := tlm_nonEmpty_iff.1 hc
    have hrp : r < p := by
      rcases Nat.lt_or_ge r p with h | h
      · exact h
      · have : r = p := by omega
        rw [h1, this] at hne; simp at hne
    have hpe : r % 2 = 0 := by omega
    obtain ⟨M1, hM1, hlM1, hM1e⟩ := tlm_step_mvTop hat hl (by rw [h2]; simp; omega : (L' ta).length + 3 ≤ B)
    subst hM1e
    have ga : (L'.moveTop a ta) a = List.replicate (p - r - 1) 1 := by
      rw [moveTop_i, h1, tlm_rep_dropLast]
    have gt : (L'.moveTop a ta) ta = List.replicate ((r + 2) / 2) 1 := by
      rw [moveTop_j hat, h2, h1]
      have : p - r ≠ 0 := by omega
      have e1 : (List.replicate (p - r) 1).getLast?.toList = [1] := by simp [List.getLast?_replicate, this]
      rw [e1, ← List.replicate_succ', show (r + 1) / 2 + 1 = (r + 2) / 2 by omega]
    have gb : (L'.moveTop a ta) tb' = List.replicate (r / 2) 1 := by
      rw [moveTop_other (Ne.symm hab) (Ne.symm htb), h3]
    have gother : ∀ x, x ≠ a → x ≠ ta → (L'.moveTop a ta) x = L' x := fun x h h' => moveTop_other h h'
    by_cases h2' : 2 ≤ p - r
    · have hc2 : nonEmpty (lastSym ((L'.moveTop a ta) a)) = true := tlm_nonEmpty_iff.2 (by
        rw [ga]; intro h; have := congrArg List.length h; simp at this; omega)
      obtain ⟨M2, hM2, hlM2, hM2e⟩ := tlm_step_mvTop hab hlM1
        (by rw [gb]; simp; omega : ((L'.moveTop a ta) tb').length + 3 ≤ B)
      subst hM2e
      refine ⟨_, (hM1.seq (hM2.iteT hlM1 hc2)).mono (by omega),
        ⟨hlM2, r + 2, by omega, Or.inl (by omega), ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [moveTop_i, ga, tlm_rep_dropLast]; congr 1
      · rw [moveTop_other (Ne.symm hat) htb, gt, show (r + 2 + 1) / 2 = (r + 2) / 2 by omega]
      · rw [moveTop_j hab, gb, ga]
        have : p - r - 1 ≠ 0 := by omega
        have e1 : (List.replicate (p - r - 1) 1).getLast?.toList = [1] := by simp [List.getLast?_replicate, this]
        rw [e1, ← List.replicate_succ', show r / 2 + 1 = (r + 2) / 2 by omega]
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        obtain ⟨x1, x2, x3⟩ := hx
        rw [moveTop_other x1 x3, gother x x1 x2]; exact hf x (by simp [x1, x2, x3])
      · show (((L'.moveTop a ta).moveTop a tb') a).length < (L' a).length
        rw [moveTop_i, ga, h1]; simp; omega
    · have hc : nonEmpty (lastSym ((L'.moveTop a ta) a)) = false := by
        have : (L'.moveTop a ta) a = [] := by rw [ga]; simp; omega
        rw [this]; simp [nonEmpty, lastSym]
      refine ⟨_, (hM1.seq ((runs_skip a hlM1).iteF hlM1 hc)).mono (by omega),
        ⟨hlM1, r + 1, by omega, Or.inr (by omega), ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [ga]; congr 1
      · rw [gt]
      · rw [gb, show (r + 1) / 2 = r / 2 by omega]
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        obtain ⟨x1, x2, x3⟩ := hx
        rw [gother x x1 x2]; exact hf x (by simp [x1, x2, x3])
      · show ((L'.moveTop a ta) a).length < (L' a).length
        rw [ga, h1]; simp; omega

theorem tlm_step_ltP_self (tt : TT k) {B : Nat} {a : Fin k} (hat : a ≠ tt.ta) (hab' : a ≠ tt.tb')
    (htb : tt.ta ≠ tt.tb') {L : Lists k} (hL : LenOK B L) {p : Nat} (hLa : L a = List.replicate p 1)
    (hta : L tt.ta = []) (htb' : L tt.tb' = []) (hp : p + 3 ≤ B) :
    Step B (12 * p + 14) (ltP tt a a) L (fun L' => L' = L) := by
  have hdef : ltP tt a a = .seq (tlm_loopS a tt.ta tt.tb')
      (.seq (.ite a nonEmpty (.push tt.fl 0) (skipP a)) (.seq (moveAll tt.ta a) (moveAll tt.tb' a))) := rfl
  rw [hdef]
  refine Step.seq' (T₁ := 6 * p + 6) (T₂ := 2 + (3 * p + 3 + (3 * p + 3)))
    (tlm_step_loopS hat hab' htb hL hLa hta htb' hp) (fun L1 hl1 ⟨g1, g2, g3, gf⟩ => ?_) (by omega)
  have h2 : Step B 2 (.ite a nonEmpty (.push tt.fl 0) (skipP a)) L1 (fun L2 => L2 = L1) := by
    have hc : nonEmpty (lastSym (L1 a)) = false := by rw [g1]; simp [nonEmpty, lastSym]
    exact Step.iteF (T := 1) hl1 hc ⟨L1, runs_skip a hl1, hl1, rfl⟩
  refine Step.seq' (T₁ := 2) (T₂ := 3 * p + 3 + (3 * p + 3)) h2 (fun L2 hl2 e2 => ?_) (by omega)
  subst e2
  refine Step.seq' (T₁ := 3 * p + 3) (T₂ := 3 * p + 3)
    ((tlm_step_mvAll (Ne.symm hat) hl2 (by rw [g1, g2]; simp; omega)).mono (by rw [g2]; simp; omega) (fun _ h => h))
    (fun L3 hl3 e3 => ?_) (by omega)
  subst e3
  have t3b : ((L2.moveAll tt.ta a)) tt.tb' = List.replicate (p / 2) 1 := by
    rw [moveAll_other (Ne.symm htb) (Ne.symm hab'), g3]
  refine ((tlm_step_mvAll (Ne.symm hab') hl3 (by rw [t3b, moveAll_j (Ne.symm hat), g1, g2]; simp; omega)).mono
    (by rw [t3b]; simp; omega) ?_)
  intro L4 e4
  subst e4
  funext x
  by_cases xa : x = a
  · rw [xa, moveAll_j (Ne.symm hab'), moveAll_j (Ne.symm hat), g1, g2, t3b, hLa]
    simp [List.replicate_append_replicate]; congr 1; omega
  by_cases xt : x = tt.ta
  · rw [xt, moveAll_other htb (Ne.symm hat), moveAll_i, hta]
  by_cases xt' : x = tt.tb'
  · rw [xt', moveAll_i, htb']
  rw [moveAll_other xt' xa, moveAll_other xt xa, gf x (by simp [xa, xt, xt'])]

def tlm_flv (b : Bool) : List Nat := if b then [0] else []

theorem tlm_nonEmpty_flv (b : Bool) : nonEmpty (lastSym (tlm_flv b)) = b := by
  cases b <;> simp [tlm_flv, nonEmpty, lastSym]

theorem tlm_step_pop {B : Nat} (i : Fin k) {L : Lists k} (hL : LenOK B L) :
    Step B 1 (.pop i) L (fun L' => L' = L.set i (L i).dropLast) := by
  have h := lenOK_set hL i (l := (L i).dropLast) (by have := hL i; simp [List.length_dropLast]; omega)
  exact ⟨_, runs_pop (Q := LenOK B) hL h, h, rfl⟩

theorem tlm_step_ltP (tt : TT k) {B : Nat} {a b : Fin k} (hat : a ≠ tt.ta)
    (hab' : a ≠ tt.tb') (haf : a ≠ tt.fl) (hbt : b ≠ tt.ta) (hbb' : b ≠ tt.tb') (hbf : b ≠ tt.fl)
    (htb : tt.ta ≠ tt.tb') (htf : tt.ta ≠ tt.fl) (hb'f : tt.tb' ≠ tt.fl)
    {L : Lists k} (hL : LenOK B L) {p q : Nat} (hLa : L a = List.replicate p 1) (hLb : L b = List.replicate q 1)
    (hta : L tt.ta = []) (htb' : L tt.tb' = []) (hfl : L tt.fl = []) (hp : p + 3 ≤ B) (hq : q + 3 ≤ B) :
    Step B (12 * p + 14) (ltP tt a b) L (fun L' => L' = L.set tt.fl (tlm_flv (decide (p < q)))) := by
  by_cases hab : a = b
  · subst hab
    have hpq : p = q := by
      have := congrArg List.length (hLa.symm.trans hLb); simpa using this
    subst hpq
    refine (tlm_step_ltP_self tt hat hab' htb hL hLa hta htb' hp).mono (Nat.le_refl _) ?_
    intro L' h
    rw [h]; simp [tlm_flv]; rw [← hfl, tlm_set_self]
  · exact (tlm_step_ltP_ne tt hab hat hab' haf hbt hbb' hbf htb htf hb'f hL hLa hLb hta htb' hfl hp hq).mono
      (Nat.le_refl _) (fun L' h => by rw [h]; by_cases hh : p < q <;> simp [hh, tlm_flv])

theorem tlm_step_notFl (tt : TT k) {B : Nat} {L : Lists k} (hL : LenOK B L) (b : Bool) (hfl : L tt.fl = tlm_flv b)
    (hB : 3 ≤ B) :
    Step B 2 (notFlP tt) L (fun L' => L' = L.set tt.fl (tlm_flv (!b))) := by
  cases b
  · have hc : nonEmpty (lastSym (L tt.fl)) = false := by rw [hfl]; exact tlm_nonEmpty_flv false
    refine (Step.iteF (T := 1) hL hc (tlm_step_push_p tt.fl 0 hL (by rw [hfl]; simp [tlm_flv]; omega))).mono
      (Nat.le_refl _) ?_
    intro L' h; rw [h, hfl]; simp [tlm_flv]
  · have hc : nonEmpty (lastSym (L tt.fl)) = true := by rw [hfl]; exact tlm_nonEmpty_flv true
    refine (Step.iteT (T := 1) hL hc (tlm_step_pop tt.fl hL)).mono (Nat.le_refl _) ?_
    intro L' h; rw [h, hfl]; simp [tlm_flv]

theorem tlm_set_fl_nil {L : Lists k} {i : Fin k} (h : L i = []) : L.set i [] = L := by
  rw [← h, tlm_set_self]

theorem tlm_step_eqP (tt : TT k) {B : Nat} {a b : Fin k} (hat : a ≠ tt.ta)
    (hab' : a ≠ tt.tb') (haf : a ≠ tt.fl) (hbt : b ≠ tt.ta) (hbb' : b ≠ tt.tb') (hbf : b ≠ tt.fl)
    (htb : tt.ta ≠ tt.tb') (htf : tt.ta ≠ tt.fl) (hb'f : tt.tb' ≠ tt.fl)
    {L : Lists k} (hL : LenOK B L) {p q N : Nat} (hLa : L a = List.replicate p 1) (hLb : L b = List.replicate q 1)
    (hta : L tt.ta = []) (htb' : L tt.tb' = []) (hfl : L tt.fl = []) (hp : p ≤ N) (hq : q ≤ N)
    (hB : N + 3 ≤ B) :
    Step B (24 * N + 31) (eqP tt a b) L (fun L' => L' = L.set tt.fl (tlm_flv (decide (p = q)))) := by
  have hdef : eqP tt a b = .seq (ltP tt a b) (.ite tt.fl nonEmpty (.pop tt.fl) (.seq (ltP tt b a) (notFlP tt))) := rfl
  rw [hdef]
  refine Step.seq' (T₁ := 12 * N + 14) (T₂ := 12 * N + 17)
    ((tlm_step_ltP tt hat hab' haf hbt hbb' hbf htb htf hb'f hL hLa hLb hta htb' hfl (by omega) (by omega)).mono
      (by omega) (fun _ h => h)) (fun L1 hl1 e1 => ?_) (by omega)
  by_cases hpq : p < q
  · have hf1 : L1 tt.fl = [0] := by rw [e1]; simp [hpq, tlm_flv]
    have hc : nonEmpty (lastSym (L1 tt.fl)) = true := by rw [hf1]; rfl
    refine (Step.iteT (T := 1) hl1 hc (tlm_step_pop tt.fl hl1)).mono (by omega) ?_
    intro L' h
    rw [h, e1, tlm_set_set]; simp [tlm_flv, hpq, Nat.ne_of_lt hpq]
  · have e1' : L1 = L := by rw [e1]; simp [hpq, tlm_flv]; exact tlm_set_fl_nil hfl
    subst e1'
    have hc : nonEmpty (lastSym (L1 tt.fl)) = false := by rw [hfl]; rfl
    refine Step.iteF (T := 12 * N + 16) hl1 hc ?_ |>.mono (by omega) (fun _ h => h)
    refine Step.seq' (T₁ := 12 * N + 14) (T₂ := 2)
      ((tlm_step_ltP tt hbt hbb' hbf hat hab' haf htb htf hb'f hl1 hLb hLa hta htb' hfl (by omega) (by omega)).mono
        (by omega) (fun _ h => h)) (fun L2 hl2 e2 => ?_) (by omega)
    have hf2 : L2 tt.fl = tlm_flv (decide (q < p)) := by rw [e2]; simp
    refine (tlm_step_notFl tt hl2 _ hf2 (by omega)).mono (Nat.le_refl _) ?_
    intro L' h
    rw [h, e2, tlm_set_set]
    have : (!decide (q < p)) = decide (p = q) := by
      by_cases h1 : q < p
      · simp [h1]; omega
      · simp [h1]; omega
    rw [this]

theorem tlm_step_fill (tt : TT k) {B : Nat} : ∀ (n : Nat) {L : Lists k}, LenOK B L →
    (L tt.bc).length + n + 2 ≤ B →
    Step B (n + 1) (fillP tt n) L (fun L' => L' = L.set tt.bc (L tt.bc ++ List.replicate n 1))
  | 0, L, hL, _ => ⟨L, runs_skip _ hL, hL, by simp [tlm_set_self]⟩
  | 1, L, hL, hb =>
    (tlm_step_push_p _ _ hL (by omega)).mono (by omega) (by intro L' h; simpa using h)
  | n + 2, L, hL, hb => by
    unfold fillP
    rw [List.replicate_succ, tlm_seqL_cons_ne _ _ _ (by simp)]
    refine Step.seq' (T₂ := (n + 1) + 1) (tlm_step_push_p _ _ hL (by omega)) (fun L1 hl1 h1 => ?_) (by omega)
    subst h1
    have := tlm_step_fill tt (n + 1) hl1 (by simp; omega)
    unfold fillP at this
    refine this.mono (Nat.le_refl _) ?_
    intro L' h
    rw [h, tlm_set_set]; simp [List.replicate_succ, List.append_assoc]

theorem tlm_step_clear {B : Nat} (c : Fin k) {L : Lists k} (hL : LenOK B L) :
    Step B (2 * (L c).length + 2) (clearP' c) L (fun L' => L' = L.set c []) := by
  have hmain := runs_loop (Q := LenOK B) (i := c) (c := nonEmpty) (p := .pop c)
    (I := fun L' => LenOK B L' ∧ ∃ m ≤ (L c).length, L' = L.set c ((L c).take ((L c).length - m)))
    (μ := fun L' => (L' c).length) (T := 1) (fun L' h => h.1) ?_ L
    ⟨hL, 0, Nat.zero_le _, by simp [tlm_set_self, List.take_of_length_le]⟩
  · obtain ⟨L', hr, ⟨hl, m, hm, he⟩, hc⟩ := hmain
    have hc0 : L' c = [] := lastSym_eq_three.1 (by simpa [nonEmpty] using hc)
    have hmn : m = (L c).length := by
      rw [he] at hc0
      have := congrArg List.length hc0
      simp at this; omega
    subst hmn
    refine ⟨L', hr.mono (by omega), hl, ?_⟩
    rw [he]; simp
  · rintro L' ⟨hl, m, hm, he⟩ hc
    have hne : L' c ≠ [] := tlm_nonEmpty_iff.1 hc
    have hlen : (L' c).length = (L c).length - m := by rw [he]; simp
    have hmn : m < (L c).length := by
      have : 0 < (L' c).length := List.length_pos_iff.2 hne
      omega
    obtain ⟨L'', hr, hl', he'⟩ := tlm_step_pop c hl
    refine ⟨L'', hr, ⟨hl', m + 1, by omega, ?_⟩, ?_⟩
    · rw [he', he, tlm_set_set]; simp [List.dropLast_eq_take, List.take_take]
      rw [Nat.sub_sub]
    · rw [he']; simp [hlen]; omega

theorem tlm_take_rev (R : List Nat) (p : Nat) : R.reverse.take (R.length - p) = (R.drop p).reverse := by
  rw [List.take_reverse]
  by_cases h : p ≤ R.length
  · congr 2; omega
  · rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]

theorem tlm_symIs_iff (R : List Nat) (p e : Nat) :
    symIs e (lastSym ((R.drop p).reverse)) = decide (R[p]? = some e) := by
  simp only [lastSym, symIs, List.getLast?_reverse, List.head?_drop]
  cases R[p]? with
  | none => simp
  | some x => rw [Bool.eq_iff_iff]; simp

theorem tlm_bit_iff (w : List Bool) (p : Nat) (b : Bool) :
    decide ((w.map bit01)[p]? = some (bit01 b)) = decide (w[p]? = some b) := by
  rw [List.getElem?_map]
  cases w[p]? with
  | none => simp
  | some x => cases x <;> cases b <;> simp [bit01]

theorem tlm_step_inBit (tt : TT k) {B : Nat} {c : Fin k} (b : Bool) (hct : c ≠ tt.ta) (hci : c ≠ tt.inr)
    (hcb : c ≠ tt.tb') (hcf : c ≠ tt.fl) (hti : tt.ta ≠ tt.inr) (htb : tt.ta ≠ tt.tb') (htf : tt.ta ≠ tt.fl)
    (hib : tt.inr ≠ tt.tb') (hif : tt.inr ≠ tt.fl) (hbf : tt.tb' ≠ tt.fl)
    {L : Lists k} (hL : LenOK B L) {p : Nat} {w : List Bool} (hLc : L c = List.replicate p 1)
    (hLi : L tt.inr = (w.map bit01).reverse) (hta : L tt.ta = []) (htb' : L tt.tb' = []) (hfl : L tt.fl = [])
    (hp : p + 3 ≤ B) (hw : w.length + 3 ≤ B) :
    Step B (12 * p + 14) (inBitP tt c b) L (fun L' => L' = L.set tt.fl (tlm_flv (decide (w[p]? = some b)))) := by
  have hdef : inBitP tt c b = .seq (tlm_loopA c tt.ta tt.inr tt.tb')
      (.seq (.ite tt.inr (symIs (bit01 b)) (.push tt.fl 0) (skipP tt.inr))
        (.seq (moveAll tt.ta c) (moveAll tt.tb' tt.inr))) := rfl
  rw [hdef]
  obtain ⟨R, hR⟩ : ∃ R, R = w.map bit01 := ⟨_, rfl⟩
  rw [← hR] at hLi
  have hRl : R.length = w.length := by simp [hR]
  have h1 := tlm_step_loopA hct hci hcb hti htb hib hL (by rw [hLc, hta]; simp; omega)
    (by rw [hLi, htb']; simp; omega)
  have h1' : Step B (6 * p + 6) (tlm_loopA c tt.ta tt.inr tt.tb') L (fun L' => L' c = [] ∧
      L' tt.ta = List.replicate p 1 ∧ L' tt.inr = (R.drop p).reverse ∧ L' tt.tb' = R.take p ∧
      TlmFix L L' [c, tt.ta, tt.inr, tt.tb']) :=
    h1.mono (by rw [hLc]; simp) (fun L' ⟨g1, g2, g3, g4, gf⟩ =>
      ⟨g1, by rw [g2, hta, hLc]; simp, by
        rw [g3, hLi, hLc]; simp only [List.length_reverse]; rw [tlm_take_rev]; simp [hRl],
       by rw [g4, htb', hLi, hLc]; simp, gf⟩)
  refine Step.seq' (T₁ := 6 * p + 6) (T₂ := 2 + (3 * p + 3 + (3 * p + 3))) h1'
    (fun L1 hl1 ⟨g1, g2, g3, g4, gf⟩ => ?_) (by omega)
  have hfl1 : L1 tt.fl = [] := by rw [gf _ (by tlm_nin)]; exact hfl
  have hcond : symIs (bit01 b) (lastSym (L1 tt.inr)) = decide (w[p]? = some b) := by
    rw [g3, tlm_symIs_iff, hR, ← tlm_bit_iff]
  have h2 : Step B 2 (.ite tt.inr (symIs (bit01 b)) (.push tt.fl 0) (skipP tt.inr)) L1
      (fun L2 => L2 = L1.set tt.fl (tlm_flv (decide (w[p]? = some b)))) := by
    by_cases hh : w[p]? = some b
    · have hc : symIs (bit01 b) (lastSym (L1 tt.inr)) = true := by rw [hcond]; simp [hh]
      exact (Step.iteT (T := 1) hl1 hc (tlm_step_push_p _ 0 hl1 (by rw [hfl1]; simp; omega))).mono (by omega)
        (fun L' h => by rw [h, hfl1]; simp [hh, tlm_flv])
    · have hc : symIs (bit01 b) (lastSym (L1 tt.inr)) = false := by rw [hcond]; simp [hh]
      exact Step.iteF (T := 1) hl1 hc ⟨L1, runs_skip _ hl1, hl1, by
        simp only [hh, decide_false, tlm_flv, Bool.false_eq_true, if_false]
        exact (tlm_set_fl_nil hfl1).symm⟩
  refine Step.seq' (T₁ := 2) (T₂ := 3 * p + 3 + (3 * p + 3)) h2 (fun L2 hl2 e2 => ?_) (by omega)
  subst e2
  have s2c : (L1.set tt.fl (tlm_flv (decide (w[p]? = some b)))) c = [] := by rw [Lists.set_ne _ _ hcf, g1]
  have s2t : (L1.set tt.fl (tlm_flv (decide (w[p]? = some b)))) tt.ta = List.replicate p 1 := by
    rw [Lists.set_ne _ _ htf, g2]
  have s2i : (L1.set tt.fl (tlm_flv (decide (w[p]? = some b)))) tt.inr = (R.drop p).reverse := by
    rw [Lists.set_ne _ _ hif, g3]
  have s2b : (L1.set tt.fl (tlm_flv (decide (w[p]? = some b)))) tt.tb' = R.take p := by
    rw [Lists.set_ne _ _ hbf, g4]
  refine Step.seq' (T₁ := 3 * p + 3) (T₂ := 3 * p + 3)
    ((tlm_step_mvAll (Ne.symm hct) hl2 (by rw [s2c, s2t]; simp; omega)).mono (by rw [s2t]; simp; omega)
      (fun _ h => h)) (fun L3 hl3 e3 => ?_) (by omega)
  subst e3
  have t3b : ((L1.set tt.fl (tlm_flv (decide (w[p]? = some b)))).moveAll tt.ta c) tt.tb' = R.take p := by
    rw [moveAll_other (Ne.symm htb) (Ne.symm hcb), s2b]
  have t3i : ((L1.set tt.fl (tlm_flv (decide (w[p]? = some b)))).moveAll tt.ta c) tt.inr = (R.drop p).reverse := by
    rw [moveAll_other (Ne.symm hti) (Ne.symm hci), s2i]
  have hlen : (R.take p).length ≤ p := by simp; omega
  refine ((tlm_step_mvAll (Ne.symm hib) hl3 (by rw [t3b, t3i]; simp; omega)).mono
    (by rw [t3b]; omega) ?_)
  intro L4 e4
  subst e4
  funext x
  by_cases xc : x = c
  · rw [xc, moveAll_other hcb hci, moveAll_j (Ne.symm hct), s2c, s2t, Lists.set_ne _ _ hcf, hLc]; simp
  by_cases xi : x = tt.inr
  · rw [xi, moveAll_j (Ne.symm hib), moveAll_other (Ne.symm hti) (Ne.symm hci), s2i, t3b,
      Lists.set_ne _ _ hif, hLi, ← List.reverse_append, List.take_append_drop]
  by_cases xt : x = tt.ta
  · rw [xt, moveAll_other htb hti, moveAll_i, Lists.set_ne _ _ htf, hta]
  by_cases xt' : x = tt.tb'
  · rw [xt', moveAll_i, Lists.set_ne _ _ hbf, htb']
  by_cases xf : x = tt.fl
  · rw [xf, moveAll_other (Ne.symm hbf) (Ne.symm hif), moveAll_other (Ne.symm htf) (Ne.symm hcf)]; simp
  rw [moveAll_other xt' xi, moveAll_other xt xc, Lists.set_ne _ _ xf, Lists.set_ne _ _ xf,
    gf x (by simp [xc, xt, xi, xt'])]

theorem tlm_named {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) :
    tt.out ≠ tt.inr ∧
    tt.out ≠ tt.sb ∧
    tt.out ≠ tt.tb ∧
    tt.out ≠ tt.bc ∧
    tt.out ≠ tt.ta ∧
    tt.out ≠ tt.tb' ∧
    tt.out ≠ tt.tc ∧
    tt.out ≠ tt.fl ∧
    tt.inr ≠ tt.sb ∧
    tt.inr ≠ tt.tb ∧
    tt.inr ≠ tt.bc ∧
    tt.inr ≠ tt.ta ∧
    tt.inr ≠ tt.tb' ∧
    tt.inr ≠ tt.tc ∧
    tt.inr ≠ tt.fl ∧
    tt.sb ≠ tt.tb ∧
    tt.sb ≠ tt.bc ∧
    tt.sb ≠ tt.ta ∧
    tt.sb ≠ tt.tb' ∧
    tt.sb ≠ tt.tc ∧
    tt.sb ≠ tt.fl ∧
    tt.tb ≠ tt.bc ∧
    tt.tb ≠ tt.ta ∧
    tt.tb ≠ tt.tb' ∧
    tt.tb ≠ tt.tc ∧
    tt.tb ≠ tt.fl ∧
    tt.bc ≠ tt.ta ∧
    tt.bc ≠ tt.tb' ∧
    tt.bc ≠ tt.tc ∧
    tt.bc ≠ tt.fl ∧
    tt.ta ≠ tt.tb' ∧
    tt.ta ≠ tt.tc ∧
    tt.ta ≠ tt.fl ∧
    tt.tb' ≠ tt.tc ∧
    tt.tb' ≠ tt.fl ∧
    tt.tc ≠ tt.fl := by
  unfold TT.Distinct at hd
  have h2 := (List.nodup_append.1 (List.nodup_append.1 hd).1).1
  simp [List.nodup_cons] at h2
  grind

theorem tlm_dist_split {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) :
    (∀ x ∈ [tt.out, tt.inr, tt.sb, tt.tb, tt.bc, tt.ta, tt.tb', tt.tc, tt.fl], ∀ i, i < nc → x ≠ tt.ct i) ∧
    (∀ x ∈ [tt.out, tt.inr, tt.sb, tt.tb, tt.bc, tt.ta, tt.tb', tt.tc, tt.fl], ∀ i, i < nc → x ≠ tt.sv i) ∧
    (∀ i, i < nc → ∀ j, j < nc → tt.ct i ≠ tt.sv j) ∧
    (∀ i, i < nc → ∀ j, j < nc → i ≠ j → tt.ct i ≠ tt.ct j) ∧
    (∀ i, i < nc → ∀ j, j < nc → i ≠ j → tt.sv i ≠ tt.sv j) := by
  unfold TT.Distinct at hd
  rw [List.nodup_append] at hd
  obtain ⟨h1, h2, h3⟩ := hd
  rw [List.nodup_append] at h1
  obtain ⟨h1a, h1b, h4⟩ := h1
  have inj : ∀ (f : Nat → Fin k), (List.map f (List.range nc)).Nodup → ∀ i, i < nc → ∀ j, j < nc → i ≠ j → f i ≠ f j := by
    intro f hf i hi j hj hij
    have hf' := List.pairwise_map.1 hf
    rw [List.pairwise_iff_getElem] at hf'
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · have := hf' i j (by simpa using hi) (by simpa using hj) h
      rwa [List.getElem_range, List.getElem_range] at this
    · have := hf' j i (by simpa using hj) (by simpa using hi) h
      rw [List.getElem_range, List.getElem_range] at this
      exact Ne.symm this
  refine ⟨?_, ?_, ?_, inj _ h1b, inj _ h2⟩
  · intro x hx i hi
    exact h4 x hx _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
  · intro x hx i hi
    exact h3 x (List.mem_append_left _ hx) _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
  · intro i hi j hj
    exact h3 _ (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)) _
      (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)

theorem tlm_ctN {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {i : Nat} (hi : i < nc) :
    tt.ct i ≠ tt.out ∧ tt.ct i ≠ tt.inr ∧ tt.ct i ≠ tt.sb ∧ tt.ct i ≠ tt.tb ∧ tt.ct i ≠ tt.bc ∧ tt.ct i ≠ tt.ta ∧ tt.ct i ≠ tt.tb' ∧ tt.ct i ≠ tt.tc ∧ tt.ct i ≠ tt.fl :=
  ⟨Ne.symm ((tlm_dist_split hd |>.1) tt.out (by simp) i hi), Ne.symm ((tlm_dist_split hd |>.1) tt.inr (by simp) i hi), Ne.symm ((tlm_dist_split hd |>.1) tt.sb (by simp) i hi), Ne.symm ((tlm_dist_split hd |>.1) tt.tb (by simp) i hi), Ne.symm ((tlm_dist_split hd |>.1) tt.bc (by simp) i hi), Ne.symm ((tlm_dist_split hd |>.1) tt.ta (by simp) i hi), Ne.symm ((tlm_dist_split hd |>.1) tt.tb' (by simp) i hi), Ne.symm ((tlm_dist_split hd |>.1) tt.tc (by simp) i hi), Ne.symm ((tlm_dist_split hd |>.1) tt.fl (by simp) i hi)⟩

theorem tlm_svN {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {i : Nat} (hi : i < nc) :
    tt.sv i ≠ tt.out ∧ tt.sv i ≠ tt.inr ∧ tt.sv i ≠ tt.sb ∧ tt.sv i ≠ tt.tb ∧ tt.sv i ≠ tt.bc ∧ tt.sv i ≠ tt.ta ∧ tt.sv i ≠ tt.tb' ∧ tt.sv i ≠ tt.tc ∧ tt.sv i ≠ tt.fl :=
  ⟨Ne.symm ((tlm_dist_split hd |>.2.1) tt.out (by simp) i hi), Ne.symm ((tlm_dist_split hd |>.2.1) tt.inr (by simp) i hi), Ne.symm ((tlm_dist_split hd |>.2.1) tt.sb (by simp) i hi), Ne.symm ((tlm_dist_split hd |>.2.1) tt.tb (by simp) i hi), Ne.symm ((tlm_dist_split hd |>.2.1) tt.bc (by simp) i hi), Ne.symm ((tlm_dist_split hd |>.2.1) tt.ta (by simp) i hi), Ne.symm ((tlm_dist_split hd |>.2.1) tt.tb' (by simp) i hi), Ne.symm ((tlm_dist_split hd |>.2.1) tt.tc (by simp) i hi), Ne.symm ((tlm_dist_split hd |>.2.1) tt.fl (by simp) i hi)⟩


local macro "tlm_get_named" hd:term : tactic =>
  `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := tlm_named $hd)

local macro "tlm_get_ct" hd:term:max hi:term:max : tactic =>
  `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _⟩ := tlm_ctN $hd $hi)

local macro "tlm_get_sv" hd:term:max hi:term:max : tactic =>
  `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _⟩ := tlm_svN $hd $hi)

theorem tlm_repL_add (a b : Nat) (l : List Nat) : tlm_repL (a + b) l = tlm_repL a l ++ tlm_repL b l := by
  induction b with
  | zero => simp [tlm_repL]
  | succ b ih => rw [← Nat.add_assoc, tlm_repL, ih, tlm_repL, List.append_assoc]

theorem tlm_step_emitOnes (tt : TT k) {B : Nat} {c : Fin k} (hct : c ≠ tt.ta) (hco : c ≠ tt.out)
    (hto : tt.ta ≠ tt.out) {L : Lists k} (hL : LenOK B L) (hta : L tt.ta = [])
    (hb1 : (L c).length + 3 ≤ B) (hb2 : (L tt.out).length + 4 * (L c).length + 2 ≤ B) :
    Step B (11 * (L c).length + 11) (emitOnesP tt c) L
      (fun L' => L' = L.set tt.out (L tt.out ++ tlm_repL (L c).length (tlm_ebits Tok.one))) := by
  have hdef : emitOnesP tt c = .seq (tlm_loopB tt c tt.ta Tok.one) (moveAll tt.ta c) := rfl
  rw [hdef]
  have h1 := tlm_step_loopB tt Tok.one hct hco hto hL (by rw [hta]; simpa using hb1) hb2
  refine Step.seq' (T₁ := 8 * (L c).length + 8) (T₂ := 3 * (L c).length + 3) h1
    (fun L1 hl1 ⟨g1, g2, g3, gf⟩ => ?_) (by omega)
  refine ((tlm_step_mvAll (Ne.symm hct) hl1 (by rw [g1, g2, hta]; simp; omega)).mono
    (by rw [g2, hta]; simp; omega) ?_)
  intro L2 e2
  subst e2
  funext x
  by_cases xc : x = c
  · rw [xc, moveAll_j (Ne.symm hct), g1, g2, hta, Lists.set_ne _ _ hco]; simp
  by_cases xt : x = tt.ta
  · rw [xt, moveAll_i, Lists.set_ne _ _ hto, hta]
  by_cases xo : x = tt.out
  · rw [xo, moveAll_other (Ne.symm hto) (Ne.symm hco), g3]; simp
  rw [moveAll_other xt xc, Lists.set_ne _ _ xo, gf x (by simp [xc, xt, xo])]

theorem tlm_trep_out {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {e : TEnv} {acc : List Nat} {L : Lists k}
    (h : TRep tt nc e acc L) (acc' : List Nat) : TRep tt nc e acc' (L.set tt.out acc') := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  tlm_get_named hd
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | (rw [Lists.set_ne _ _ (by tlm_dis)]; assumption) | skip
  intro i hi
  tlm_get_ct hd hi
  rw [Lists.set_ne _ _ (by tlm_dis)]; exact h10 i hi

set_option hygiene false in
local macro "tlm_dd" : tactic =>
  `(tactic| (tlm_get_named hd; tlm_get_ct hd hi; tlm_dis))

set_option hygiene false in
local macro "tlm_ndd" : tactic =>
  `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; repeat' apply And.intro
             all_goals tlm_dd))

set_option hygiene false in
local macro "tlm_ev" : tactic =>
  `(tactic| simp (disch := tlm_dd) only [moveAll_other, moveAll_i, moveAll_j, Lists.set_ne, Lists.set_same])

set_option maxHeartbeats 4000000 in
theorem tlm_step_rev {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {B Z : Nat} (i c : Nat) (hi : i < nc)
    {e : TEnv} {acc : List Nat} {L : Lists k} (hT : TRep tt nc e acc L) (hL : LenOK B L) (hZ : Z + 4 ≤ B)
    (hS : e.S ≤ Z) (hTT : e.T ≤ Z) (hctr : e.ctr i ≤ Z) (hcZ : c ≤ Z)
    (hout : acc.length + 4 * (e.T - e.ctr i + c) + 2 ≤ B) :
    Step B (28 * Z + 30) (partP tt (.rev i c)) L
      (fun L' => L' = L.set tt.out (acc ++ tlm_repL (e.T - e.ctr i + c) (tlm_ebits Tok.one))) := by
  obtain ⟨ho, hin, hsb, htb, hbc, hta, htb', htc, hfl, hct⟩ := hT
  have hci := hct i hi
  have hdef : partP tt (.rev i c) = .seq (tlm_loopA (tt.ct i) tt.ta tt.tb tt.tc)
      (.seq (tlm_loopB tt tt.tb tt.tb' Tok.one) (.seq (moveAll tt.tb' tt.tb) (.seq (moveAll tt.tc tt.tb)
        (.seq (moveAll tt.ta (tt.ct i)) (seqL tt (List.replicate c (emitTokP tt Tok.one))))))) := rfl
  rw [hdef]
  have h1 := tlm_step_loopA (c := tt.ct i) (ta := tt.ta) (j := tt.tb) (j' := tt.tc)
    (by tlm_dd) (by tlm_dd) (by tlm_dd) (by tlm_dd) (by tlm_dd) (by tlm_dd)
    (L := L) hL (by rw [hci, hta]; simp; omega) (by rw [htb, htc]; simp; omega)
  have h1' : Step B (6 * e.ctr i + 6) (tlm_loopA (tt.ct i) tt.ta tt.tb tt.tc) L (fun L' => L' (tt.ct i) = [] ∧
      L' tt.ta = List.replicate (e.ctr i) 1 ∧ L' tt.tb = List.replicate (e.T - e.ctr i) 1 ∧
      L' tt.tc = List.replicate (min (e.ctr i) e.T) 1 ∧ TlmFix L L' [tt.ct i, tt.ta, tt.tb, tt.tc]) :=
    h1.mono (by rw [hci]; simp) (fun L' ⟨g1, g2, g3, g4, gf⟩ =>
      ⟨g1, by rw [g2, hta, hci]; simp, by rw [g3, htb, hci]; simp [List.take_replicate],
       by rw [g4, htc, htb, hci]; simp [List.take_replicate], gf⟩)
  refine Step.seq' (T₁ := 6 * e.ctr i + 6) (T₂ := 22 * Z + 24) h1'
    (fun L1 hl1 ⟨g1, g2, g3, g4, gf⟩ => ?_) (by omega)
  have f1 : ∀ x, x ≠ tt.ct i → x ≠ tt.ta → x ≠ tt.tb → x ≠ tt.tc → L1 x = L x := by
    intro x h1 h2 h3 h4; exact gf x (by simp [h1, h2, h3, h4])
  have e1o : L1 tt.out = acc := by rw [f1 tt.out (by tlm_dd) (by tlm_dd) (by tlm_dd) (by tlm_dd), ho]
  have e1b : L1 tt.tb' = [] := by rw [f1 tt.tb' (by tlm_dd) (by tlm_dd) (by tlm_dd) (by tlm_dd), htb']
  have hlen3 : (L1 tt.tb).length = e.T - e.ctr i := by rw [g3]; simp
  have hB := tlm_step_loopB tt Tok.one (c := tt.tb) (d := tt.tb') (by tlm_dd) (by tlm_dd) (by tlm_dd) hl1
    (by rw [e1b, hlen3]; simp; omega) (by rw [e1o, hlen3]; omega)
  have hB' : Step B (8 * (e.T - e.ctr i) + 8) (tlm_loopB tt tt.tb tt.tb' Tok.one) L1 (fun L' =>
      L' tt.tb = [] ∧ L' tt.tb' = List.replicate (e.T - e.ctr i) 1 ∧
      L' tt.out = acc ++ tlm_repL (e.T - e.ctr i) (tlm_ebits Tok.one) ∧ TlmFix L1 L' [tt.tb, tt.tb', tt.out]) :=
    hB.mono (by simp [hlen3]) (fun L' ⟨q1, q2, q3, qf⟩ =>
      ⟨q1, by rw [q2, e1b, g3]; simp, by rw [q3, e1o, hlen3], qf⟩)
  refine Step.seq' (T₁ := 8 * (e.T - e.ctr i) + 8) (T₂ := 14 * Z + 16) hB'
    (fun L2 hl2 ⟨q1, q2, q3, qf⟩ => ?_) (by omega)
  have f2 : ∀ x, x ≠ tt.ct i → x ≠ tt.ta → x ≠ tt.tb → x ≠ tt.tc → x ≠ tt.tb' → x ≠ tt.out → L2 x = L x := by
    intro x h1 h2 h3 h4 h5 h6; rw [qf x (by simp [h3, h5, h6]), f1 x h1 h2 h3 h4]
  have e2c : L2 (tt.ct i) = [] := by rw [qf (tt.ct i) (by tlm_ndd), g1]
  have e2a : L2 tt.ta = List.replicate (e.ctr i) 1 := by rw [qf tt.ta (by tlm_ndd), g2]
  have e2c' : L2 tt.tc = List.replicate (min (e.ctr i) e.T) 1 := by rw [qf tt.tc (by tlm_ndd), g4]
  refine Step.seq' (T₁ := 3 * (e.T - e.ctr i) + 3) (T₂ := 11 * Z + 13)
    ((tlm_step_mvAll (i := tt.tb') (j := tt.tb) (Ne.symm (by tlm_dd)) hl2 (by rw [q1, q2]; simp; omega)).mono
      (by rw [q2]; simp; omega) (fun _ h => h)) (fun L3 hl3 e3 => ?_) (by omega)
  subst e3
  have e3b : ((L2.moveAll tt.tb' tt.tb)) tt.tb = List.replicate (e.T - e.ctr i) 1 := by
    rw [moveAll_j (by tlm_dd), q1, q2]; simp
  have e3c : ((L2.moveAll tt.tb' tt.tb)) tt.tc = List.replicate (min (e.ctr i) e.T) 1 := by
    rw [moveAll_other (by tlm_dd) (by tlm_dd), e2c']
  refine Step.seq' (T₁ := 3 * Z + 3) (T₂ := 8 * Z + 10)
    ((tlm_step_mvAll (i := tt.tc) (j := tt.tb) (Ne.symm (by tlm_dd)) hl3 (by rw [e3b, e3c]; simp; omega)).mono
      (by rw [e3c]; simp; omega) (fun _ h => h)) (fun L4 hl4 e4 => ?_) (by omega)
  subst e4
  have e4a : (((L2.moveAll tt.tb' tt.tb).moveAll tt.tc tt.tb)) tt.ta = List.replicate (e.ctr i) 1 := by
    rw [moveAll_other (by tlm_dd) (by tlm_dd), moveAll_other (by tlm_dd) (by tlm_dd), e2a]
  have e4c : (((L2.moveAll tt.tb' tt.tb).moveAll tt.tc tt.tb)) (tt.ct i) = [] := by
    rw [moveAll_other (by tlm_dd) (by tlm_dd), moveAll_other (by tlm_dd) (by tlm_dd), e2c]
  refine Step.seq' (T₁ := 3 * Z + 3) (T₂ := 5 * Z + 6)
    ((tlm_step_mvAll (i := tt.ta) (j := tt.ct i) (Ne.symm (by tlm_dd)) hl4 (by rw [e4a, e4c]; simp; omega)).mono
      (by rw [e4a]; simp; omega) (fun _ h => h)) (fun L5 hl5 e5 => ?_) (by omega)
  subst e5
  have e5o : ((((L2.moveAll tt.tb' tt.tb).moveAll tt.tc tt.tb).moveAll tt.ta (tt.ct i))) tt.out =
      acc ++ tlm_repL (e.T - e.ctr i) (tlm_ebits Tok.one) := by
    tlm_ev; exact q3
  refine ((tlm_step_emitRep tt Tok.one c hl5 (by rw [e5o]; simp [tlm_repL_length, tlm_ebits_length]; omega)).mono
    (by omega) ?_)
  intro L6 e6
  subst e6
  apply tlm_eq_set (by rw [Lists.set_same, e5o, List.append_assoc, ← tlm_repL_add]) 
  intro x hx
  rw [Lists.set_ne _ _ hx]
  have e3b' : ((L2.moveAll tt.tb' tt.tb)) tt.tb' = [] := moveAll_i
  have e4t : (((L2.moveAll tt.tb' tt.tb).moveAll tt.tc tt.tb)) tt.tc = [] := moveAll_i
  have e4b : (((L2.moveAll tt.tb' tt.tb).moveAll tt.tc tt.tb)) tt.tb =
      List.replicate (e.T - e.ctr i) 1 ++ (List.replicate (min (e.ctr i) e.T) 1).reverse := by
    rw [moveAll_j (by tlm_dd), e3b, e3c]
  by_cases xc : x = tt.ct i
  · rw [xc, moveAll_j (by tlm_dd), e4c, e4a, hci]; simp
  by_cases xa : x = tt.ta
  · rw [xa, moveAll_i, hta]
  by_cases xb : x = tt.tb
  · rw [xb, moveAll_other (by tlm_dd) (by tlm_dd), e4b, htb]
    simp [List.replicate_append_replicate]; congr 1; omega
  by_cases xb' : x = tt.tb'
  · rw [xb', moveAll_other (by tlm_dd) (by tlm_dd), moveAll_other (by tlm_dd) (by tlm_dd), e3b', htb']
  by_cases xt : x = tt.tc
  · rw [xt, moveAll_other (by tlm_dd) (by tlm_dd), e4t, htc]
  rw [moveAll_other xa xc, moveAll_other xt xb, moveAll_other xb' xb]
  exact f2 x xc xa xb xt xb' hx

theorem tlm_step_part {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {B Z : Nat} (p : Part) (hp : p.WF nc)
    (hs : p.Small Z) {e : TEnv} {acc : List Nat} {L : Lists k} (hT : TRep tt nc e acc L) (hL : LenOK B L)
    (hZ : Z + 4 ≤ B) (hS : e.S ≤ Z) (hTT : e.T ≤ Z) (hctr : ∀ i, i < nc → e.ctr i ≤ Z)
    (hout : acc.length + 4 * p.val e + 2 ≤ B) :
    Step B (28 * Z + 30) (partP tt p) L
      (fun L' => L' = L.set tt.out (acc ++ tlm_repL (p.val e) (tlm_ebits Tok.one))) := by
  have hT' := hT
  obtain ⟨ho, hin, hsb, htb, hbc, hta, htb', htc, hfl, hct⟩ := hT'
  cases p with
  | const n =>
    have := tlm_step_emitRep tt Tok.one n hL (by rw [ho]; simpa [Part.val] using hout)
    refine (this.mono (by simp [Part.Small] at hs; omega) ?_)
    intro L' h; rw [h, ho]; rfl
  | ctr i =>
    have hi : i < nc := hp
    have hci := hct i hi
    have hc := hctr i hi
    have hn := tlm_named hd
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := tlm_ctN hd hi
    have := tlm_step_emitOnes tt (c := tt.ct i) c6 c1 hn.2.2.2.2.1.symm hL hta (by rw [hci]; simp; omega)
      (by rw [hci, ho]; simp [Part.val] at hout ⊢; omega)
    refine (this.mono (by rw [hci]; simp; omega) ?_)
    intro L' h; rw [h, hci, ho]; simp [Part.val]
  | rev i c =>
    have hi : i < nc := hp
    have := tlm_step_rev hd (B := B) (Z := Z) i c hi hT hL hZ hS hTT (hctr i hi) (by simpa [Part.Small] using hs)
      (by simpa [Part.val] using hout)
    exact this.mono (Nat.le_refl _) (fun L' h => by rw [h]; rfl)

theorem tlm_encName_cons (v : Nat) (vs : List Nat) :
    encName (v :: vs) = List.replicate v Tok.one ++ Tok.sep :: encName vs := by
  simp [encName, List.flatMap_cons]

theorem tlm_bts_single (t : Nat) : tlm_bts [t] = tlm_ebits t := by
  simp [tlm_bts, tlm_ebits, toBits]

theorem tlm_bts_cons (t : Nat) (l : List Nat) : tlm_bts (t :: l) = tlm_ebits t ++ tlm_bts l := by
  simp [tlm_bts, tlm_ebits, toBits]

theorem tlm_step_name {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {B Z : Nat} :
    ∀ (ps : List Part), (∀ p ∈ ps, p.WF nc) → (∀ p ∈ ps, p.Small Z) →
    ∀ {e : TEnv} {acc : List Nat} {L : Lists k}, TRep tt nc e acc L → LenOK B L → Z + 4 ≤ B → e.S ≤ Z → e.T ≤ Z →
    (∀ i, i < nc → e.ctr i ≤ Z) → acc.length + 4 * (encName (ps.map (Part.val e))).length + 2 ≤ B →
    Step B ((ps.length + 1) * tunit Z) (nameP tt ps) L
      (fun L' => L' = L.set tt.out (acc ++ tlm_bts (encName (ps.map (Part.val e)))))
  | [], _, _, e, acc, L, hT, hL, hZ, hS, hTT, hctr, hout => by
    have ho := hT.1
    have := tlm_step_emitTok tt Tok.fin hL (by rw [ho]; simp [encName] at hout; omega)
    refine this.mono (by simp [tunit]; omega) ?_
    intro L' h
    rw [h, ho]; simp [encName, tlm_bts_single]
  | p :: ps, hp, hs, e, acc, L, hT, hL, hZ, hS, hTT, hctr, hout => by
    have hdef : nameP tt (p :: ps) = .seq (.seq (partP tt p) (emitTokP tt Tok.sep)) (nameP tt ps) := by
      unfold nameP
      rw [List.map_cons, List.cons_append, tlm_seqL_cons_ne _ _ _ (by simp)]
    rw [hdef]
    have ho := hT.1
    have hpp := hp p (by simp)
    have hps := hs p (by simp)
    have hout' : acc.length + 4 * (Part.val e p) + 2 ≤ B := by
      simp [tlm_encName_cons] at hout; omega
    have h1 := tlm_step_part hd p hpp hps hT hL hZ hS hTT hctr hout'
    have h2 : Step B (28 * Z + 30 + 5) (.seq (partP tt p) (emitTokP tt Tok.sep)) L
        (fun L2 => L2 = L.set tt.out (acc ++ tlm_repL (Part.val e p) (tlm_ebits Tok.one) ++ tlm_ebits Tok.sep)) := by
      refine Step.seq' (T₁ := 28 * Z + 30) (T₂ := 5) h1 (fun L1 hl1 e1 => ?_) (Nat.le_refl _)
      subst e1
      have := tlm_step_emitTok tt Tok.sep hl1 (by
        simp [tlm_encName_cons, tlm_repL_length, tlm_ebits_length] at hout ⊢; omega)
      exact this.mono (Nat.le_refl _) (fun L' h => by
        rw [h, tlm_set_set]; simp [List.append_assoc])
    refine Step.seq' (T₁ := 28 * Z + 30 + 5) (T₂ := (ps.length + 1) * tunit Z) h2
      (fun L2 hl2 e2 => ?_) (by simp [tunit, Nat.add_mul]; omega)
    subst e2
    have hrec := tlm_step_name hd ps (fun q hq => hp q (by simp [hq])) (fun q hq => hs q (by simp [hq]))
      (e := e) (acc := acc ++ tlm_repL (Part.val e p) (tlm_ebits Tok.one) ++ tlm_ebits Tok.sep)
      (tlm_trep_out hd hT _) hl2 hZ hS hTT hctr (by
        simp [tlm_encName_cons, tlm_repL_length, tlm_ebits_length] at hout ⊢; omega)
    refine hrec.mono (by simp [Nat.add_mul]) ?_
    intro L' h
    rw [h, tlm_set_set]
    congr 1
    simp only [List.map_cons, tlm_encName_cons, tlm_bts_append, tlm_bts_replicate, List.append_assoc]
    simp [tlm_bts_cons]

structure TlmNE (tt : TT k) (a b : Fin k) : Prop where
  at_ : a ≠ tt.ta
  ab : a ≠ tt.tb'
  af : a ≠ tt.fl
  bt : b ≠ tt.ta
  bb : b ≠ tt.tb'
  bf : b ≠ tt.fl
  tb : tt.ta ≠ tt.tb'
  tf : tt.ta ≠ tt.fl
  bf' : tt.tb' ≠ tt.fl

theorem tlm_ne_ct_ct {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {i j : Nat} (hi : i < nc) (hj : j < nc) :
    TlmNE tt (tt.ct i) (tt.ct j) := by
  obtain ⟨_, _, _, _, _, c6, c7, _, c9⟩ := tlm_ctN hd hi
  obtain ⟨_, _, _, _, _, d6, d7, _, d9⟩ := tlm_ctN hd hj
  have hn := tlm_named hd
  exact ⟨c6, c7, c9, d6, d7, d9, by grind, by grind, by grind⟩

theorem tlm_ne_ct_bc {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {i : Nat} (hi : i < nc) :
    TlmNE tt (tt.ct i) tt.bc := by
  obtain ⟨_, _, _, _, _, c6, c7, _, c9⟩ := tlm_ctN hd hi
  have hn := tlm_named hd
  exact ⟨c6, c7, c9, by grind, by grind, by grind, by grind, by grind, by grind⟩

theorem tlm_step_ltP' (tt : TT k) {B : Nat} {a b : Fin k} (hN : TlmNE tt a b)
    {L : Lists k} (hL : LenOK B L) {p q : Nat} (hLa : L a = List.replicate p 1) (hLb : L b = List.replicate q 1)
    (hta : L tt.ta = []) (htb' : L tt.tb' = []) (hfl : L tt.fl = []) (hp : p + 3 ≤ B) (hq : q + 3 ≤ B) :
    Step B (12 * p + 14) (ltP tt a b) L (fun L' => L' = L.set tt.fl (tlm_flv (decide (p < q)))) :=
  tlm_step_ltP tt hN.at_ hN.ab hN.af hN.bt hN.bb hN.bf hN.tb hN.tf hN.bf' hL hLa hLb hta htb' hfl hp hq

theorem tlm_step_eqP' (tt : TT k) {B : Nat} {a b : Fin k} (hN : TlmNE tt a b)
    {L : Lists k} (hL : LenOK B L) {p q N : Nat} (hLa : L a = List.replicate p 1) (hLb : L b = List.replicate q 1)
    (hta : L tt.ta = []) (htb' : L tt.tb' = []) (hfl : L tt.fl = []) (hp : p ≤ N) (hq : q ≤ N)
    (hB : N + 3 ≤ B) :
    Step B (24 * N + 31) (eqP tt a b) L (fun L' => L' = L.set tt.fl (tlm_flv (decide (p = q)))) :=
  tlm_step_eqP tt hN.at_ hN.ab hN.af hN.bt hN.bb hN.bf hN.tb hN.tf hN.bf' hL hLa hLb hta htb' hfl hp hq hB

theorem tlm_set3 {L : Lists k} {b f : Fin k} (hb : L b = []) (hbf : b ≠ f) (v X : List Nat) :
    ((L.set b v).set f X).set b [] = L.set f X := by
  funext x
  by_cases h1 : x = b
  · subst h1; have h3 : ¬ f = x := fun h => hbf h.symm
    simp [Lists.set, hb, hbf, h3]
  · by_cases h2 : x = f
    · subst h2; simp [Lists.set, h1]
    · simp [Lists.set, h1, h2]

theorem tlm_set3' {L : Lists k} {b f : Fin k} {l : List Nat} (hb : L b = l) (hbf : b ≠ f) (X : List Nat) :
    ((L.set b (l ++ [1])).set f X).set b (((L.set b (l ++ [1])).set f X) b).dropLast = L.set f X := by
  funext x
  by_cases h1 : x = b
  · subst h1; have h3 : ¬ f = x := fun h => hbf h.symm
    simp [Lists.set, hb, hbf, h3]
  · by_cases h2 : x = f
    · subst h2; simp [Lists.set, h1]
    · simp [Lists.set, h1, h2]

theorem tlm_step_eqc {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {B Z : Nat} {i n : Nat} (hi : i < nc)
    (hn : n ≤ Z) {e : TEnv} {acc : List Nat} {L : Lists k} (hT : TRep tt nc e acc L) (hL : LenOK B L)
    (hZ : Z + 4 ≤ B) (hctr : e.ctr i ≤ Z) :
    Step B (tunit Z) (condP tt (.eqc i n)) L
      (fun L' => L' = L.set tt.fl (tlm_flv (decide (e.ctr i = n)))) := by
  obtain ⟨ho, hin, hsb, htb, hbc, hta, htb', htc, hfl, hct⟩ := hT
  have hci := hct i hi
  have hdef : condP tt (.eqc i n) = .seq (fillP tt n) (.seq (eqP tt (tt.ct i) tt.bc) (clearP' tt.bc)) := rfl
  rw [hdef]
  have hN := tlm_ne_ct_bc hd hi
  have hnf : tt.bc ≠ tt.fl := by have := tlm_named hd; grind
  refine Step.seq' (T₁ := n + 1) (T₂ := 24 * Z + 31 + (2 * n + 2))
    (tlm_step_fill tt n hL (by rw [hbc]; simp; omega)) (fun L1 hl1 e1 => ?_) (by simp [tunit]; omega)
  rw [hbc, List.nil_append] at e1
  subst e1
  have r_ct : (L.set tt.bc (List.replicate n 1)) (tt.ct i) = List.replicate (e.ctr i) 1 := by
    rw [Lists.set_ne _ _ (by tlm_dd), hci]
  have r_bc : (L.set tt.bc (List.replicate n 1)) tt.bc = List.replicate n 1 := by simp
  have r_ta : (L.set tt.bc (List.replicate n 1)) tt.ta = [] := by rw [Lists.set_ne _ _ (by tlm_dd), hta]
  have r_tb : (L.set tt.bc (List.replicate n 1)) tt.tb' = [] := by rw [Lists.set_ne _ _ (by tlm_dd), htb']
  have r_fl : (L.set tt.bc (List.replicate n 1)) tt.fl = [] := by rw [Lists.set_ne _ _ (by tlm_dd), hfl]
  have h2 := tlm_step_eqP' tt hN hl1 r_ct r_bc r_ta r_tb r_fl hctr hn (N := Z) (by omega)
  refine Step.seq' (T₁ := 24 * Z + 31) (T₂ := 2 * n + 2) h2 (fun L2 hl2 e2 => ?_) (Nat.le_refl _)
  subst e2
  refine (tlm_step_clear tt.bc hl2).mono ?_ ?_
  · rw [Lists.set_ne _ _ (by tlm_dd), r_bc]; simp
  · intro L' h
    rw [h]; exact tlm_set3 hbc (by tlm_dd) _ _

set_option hygiene false in
local macro "tlm_dd2" : tactic =>
  `(tactic| (tlm_get_named hd; tlm_get_ct hd hi; tlm_get_ct hd hj; tlm_dis))

theorem tlm_step_succ {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {B Z : Nat} {i j : Nat} (hi : i < nc)
    (hj : j < nc) (hij : i ≠ j) {e : TEnv} {acc : List Nat} {L : Lists k} (hT : TRep tt nc e acc L)
    (hL : LenOK B L) (hZ : Z + 4 ≤ B) (hci : e.ctr i ≤ Z) (hcj : e.ctr j ≤ Z) :
    Step B (tunit Z) (condP tt (.succ i j)) L
      (fun L' => L' = L.set tt.fl (tlm_flv (decide (e.ctr i = e.ctr j + 1)))) := by
  obtain ⟨ho, hin, hsb, htb, hbc, hta, htb', htc, hfl, hct⟩ := hT
  have hLi := hct i hi
  have hLj := hct j hj
  have hdef : condP tt (.succ i j) = .seq (.push (tt.ct j) 1) (.seq (eqP tt (tt.ct i) (tt.ct j)) (.pop (tt.ct j))) := rfl
  rw [hdef]
  have hN := tlm_ne_ct_ct hd hi hj
  have hcc : tt.ct i ≠ tt.ct j := (tlm_dist_split hd).2.2.2.1 i hi j hj hij
  have hcf : tt.ct j ≠ tt.fl := by tlm_dd2
  refine Step.seq' (T₁ := 1) (T₂ := 24 * (Z + 1) + 31 + 1)
    (tlm_step_push_p (tt.ct j) 1 hL (by rw [hLj]; simp; omega)) (fun L1 hl1 e1 => ?_) (by simp [tunit]; omega)
  subst e1
  have r_i : (L.set (tt.ct j) (L (tt.ct j) ++ [1])) (tt.ct i) = List.replicate (e.ctr i) 1 := by
    rw [Lists.set_ne _ _ hcc, hLi]
  have r_j : (L.set (tt.ct j) (L (tt.ct j) ++ [1])) (tt.ct j) = List.replicate (e.ctr j + 1) 1 := by
    rw [Lists.set_same, hLj, List.replicate_succ']
  have r_ta : (L.set (tt.ct j) (L (tt.ct j) ++ [1])) tt.ta = [] := by
    rw [Lists.set_ne _ _ (by tlm_dd2), hta]
  have r_tb : (L.set (tt.ct j) (L (tt.ct j) ++ [1])) tt.tb' = [] := by
    rw [Lists.set_ne _ _ (by tlm_dd2), htb']
  have r_fl : (L.set (tt.ct j) (L (tt.ct j) ++ [1])) tt.fl = [] := by
    rw [Lists.set_ne _ _ (by tlm_dd2), hfl]
  have h2 := tlm_step_eqP' tt hN hl1 r_i r_j r_ta r_tb r_fl (N := Z + 1) (by omega) (by omega) (by omega)
  refine Step.seq' (T₁ := 24 * (Z + 1) + 31) (T₂ := 1) h2 (fun L2 hl2 e2 => ?_) (Nat.le_refl _)
  subst e2
  refine (tlm_step_pop (tt.ct j) hl2).mono (Nat.le_refl _) ?_
  intro L' h
  rw [h]; exact tlm_set3' rfl hcf _

theorem tlm_step_cond {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {B Z : Nat} :
    ∀ (c : Cond), c.WF nc → c.Small Z →
    ∀ {e : TEnv} {acc : List Nat} {L : Lists k}, TRep tt nc e acc L → LenOK B L → Z + 4 ≤ B →
    e.w.length ≤ Z → (∀ i, i < nc → e.ctr i ≤ Z) →
    Step B (c.cost Z) (condP tt c) L (fun L' => L' = L.set tt.fl (tlm_flv (c.eval e)))
  | .tt, _, _, e, acc, L, hT, hL, hZ, hw, hctr => by
    have hfl := hT.2.2.2.2.2.2.2.2.1
    refine (tlm_step_push_p tt.fl 0 hL (by rw [hfl]; simp; omega)).mono (by simp [Cond.cost, tunit]; omega) ?_
    intro L' h; rw [h, hfl]; simp [Cond.eval, tlm_flv]
  | .lt i j, hwf, _, e, acc, L, hT, hL, hZ, hw, hctr => by
    obtain ⟨hi, hj⟩ := hwf
    obtain ⟨ho, hin, hsb, htb, hbc, hta, htb', htc, hfl, hct⟩ := hT
    have p1 := hctr i hi
    have p2 := hctr j hj
    refine (tlm_step_ltP' tt (tlm_ne_ct_ct hd hi hj) hL (hct i hi) (hct j hj) hta htb' hfl (by omega) (by omega)).mono
      (by simp [Cond.cost, tunit]; omega) ?_
    intro L' h; rw [h]; rfl
  | .eq i j, hwf, _, e, acc, L, hT, hL, hZ, hw, hctr => by
    obtain ⟨hi, hj⟩ := hwf
    obtain ⟨ho, hin, hsb, htb, hbc, hta, htb', htc, hfl, hct⟩ := hT
    have p1 := hctr i hi
    have p2 := hctr j hj
    refine (tlm_step_eqP' tt (tlm_ne_ct_ct hd hi hj) hL (hct i hi) (hct j hj) hta htb' hfl p1 p2 (N := Z) (by omega)).mono
      (by simp [Cond.cost, tunit]; omega) ?_
    intro L' h; rw [h]; rfl
  | .eqc i n, hwf, hs, e, acc, L, hT, hL, hZ, hw, hctr => by
    refine (tlm_step_eqc hd hwf hs hT hL hZ (hctr i hwf)).mono (by simp [Cond.cost]) ?_
    intro L' h; rw [h]; rfl
  | .succ i j, hwf, _, e, acc, L, hT, hL, hZ, hw, hctr => by
    obtain ⟨hi, hj, hij⟩ := hwf
    refine (tlm_step_succ hd hi hj hij hT hL hZ (hctr i hi) (hctr j hj)).mono (by simp [Cond.cost]) ?_
    intro L' h; rw [h]; rfl
  | .inBit i b, hwf, _, e, acc, L, hT, hL, hZ, hw, hctr => by
    have hi : i < nc := hwf
    obtain ⟨ho, hin, hsb, htb, hbc, hta, htb', htc, hfl, hct⟩ := hT
    have p1 := hctr i hi
    have q1 : e.ctr i + 3 ≤ B := by omega
    have q2 : e.w.length + 3 ≤ B := by omega
    have q3 : 12 * e.ctr i + 14 ≤ Cond.cost Z (.inBit i b) := by simp [Cond.cost, tunit]; omega
    refine (tlm_step_inBit tt b (by tlm_dd) (by tlm_dd) (by tlm_dd) (by tlm_dd) (by tlm_dd) (by tlm_dd)
      (by tlm_dd) (by tlm_dd) (by tlm_dd) (by tlm_dd) hL (hct i hi) hin hta htb' hfl q1 q2).mono q3 ?_
    intro L' h; rw [h]; rfl
  | .not c, hwf, hs, e, acc, L, hT, hL, hZ, hw, hctr => by
    have hfl := hT.2.2.2.2.2.2.2.2.1
    refine Step.seq' (T₁ := c.cost Z) (T₂ := 2) (tlm_step_cond hd c hwf hs hT hL hZ hw hctr)
      (fun L1 hl1 e1 => ?_) (by simp [Cond.cost, tunit]; omega)
    subst e1
    refine (tlm_step_notFl tt hl1 (c.eval e) (by simp) (by omega)).mono (Nat.le_refl _) ?_
    intro L' h; rw [h, tlm_set_set]; rfl
  | .and c d, hwf, hs, e, acc, L, hT, hL, hZ, hw, hctr => by
    have hfl := hT.2.2.2.2.2.2.2.2.1
    refine Step.seq' (T₁ := c.cost Z) (T₂ := d.cost Z + 2)
      (tlm_step_cond hd c hwf.1 hs.1 hT hL hZ hw hctr) (fun L1 hl1 e1 => ?_) (by simp [Cond.cost, tunit]; omega)
    have hfl1 : L1 tt.fl = tlm_flv (c.eval e) := by rw [e1]; simp
    cases hb : c.eval e with
    | false =>
      have hc : nonEmpty (lastSym (L1 tt.fl)) = false := by rw [hfl1, hb]; exact tlm_nonEmpty_flv false
      refine (Step.iteF (T := 1) hl1 hc ⟨L1, runs_skip _ hl1, hl1, ?_⟩).mono (by omega) (fun _ h => h)
      rw [e1, hb]; simp [Cond.eval, hb]
    | true =>
      have hc : nonEmpty (lastSym (L1 tt.fl)) = true := by rw [hfl1, hb]; exact tlm_nonEmpty_flv true
      refine (Step.iteT (T := d.cost Z + 1) hl1 hc
        (Step.seq' (T₁ := 1) (T₂ := d.cost Z) (tlm_step_pop tt.fl hl1) (fun L2 hl2 e2 => ?_) (by omega))).mono
        (Nat.le_refl _) (fun _ h => h)
      have hL2 : L2 = L := by
        rw [e2, e1, hb]; simp [tlm_flv, tlm_set_set, tlm_set_fl_nil hfl]
      have hT2 : TRep tt nc e acc L2 := by rw [hL2]; exact hT
      refine (tlm_step_cond hd d hwf.2 hs.2 hT2 hl2 hZ hw hctr).mono (Nat.le_refl _) ?_
      intro L' h; rw [h, hL2]; simp [Cond.eval, hb]
  | .or c d, hwf, hs, e, acc, L, hT, hL, hZ, hw, hctr => by
    have hfl := hT.2.2.2.2.2.2.2.2.1
    refine Step.seq' (T₁ := c.cost Z) (T₂ := d.cost Z + 2)
      (tlm_step_cond hd c hwf.1 hs.1 hT hL hZ hw hctr) (fun L1 hl1 e1 => ?_) (by simp [Cond.cost, tunit]; omega)
    have hfl1 : L1 tt.fl = tlm_flv (c.eval e) := by rw [e1]; simp
    cases hb : c.eval e with
    | true =>
      have hc : nonEmpty (lastSym (L1 tt.fl)) = true := by rw [hfl1, hb]; exact tlm_nonEmpty_flv true
      refine (Step.iteT (T := 1) hl1 hc ⟨L1, runs_skip _ hl1, hl1, ?_⟩).mono (by omega) (fun _ h => h)
      rw [e1, hb]; simp [Cond.eval, hb]
    | false =>
      have hc : nonEmpty (lastSym (L1 tt.fl)) = false := by rw [hfl1, hb]; exact tlm_nonEmpty_flv false
      have hL1 : L1 = L := by
        rw [e1, hb]; simp [tlm_flv]; exact tlm_set_fl_nil hfl
      have hT1 : TRep tt nc e acc L1 := by rw [hL1]; exact hT
      refine (Step.iteF (T := d.cost Z) hl1 hc (tlm_step_cond hd d hwf.2 hs.2 hT1 hl1 hZ hw hctr)).mono
        (by omega) ?_
      intro L' h; rw [h, hL1]; simp [Cond.eval, hb]

set_option hygiene false in
local macro "tlm_dd3" : tactic =>
  `(tactic| (
    tlm_get_named hd
    (tlm_get_ct hd hi)
    (tlm_get_sv hd hi)
    have _ := (tlm_dist_split hd).2.2.1 i hi i hi
    tlm_dis))

set_option hygiene false in
local macro "tlm_dj" : tactic =>
  `(tactic| (
    tlm_get_named hd
    (tlm_get_ct hd hi)
    (tlm_get_sv hd hi)
    (tlm_get_ct hd hj)
    (tlm_get_sv hd hj)
    have _ := (tlm_dist_split hd).2.2.1 i hi i hi
    have _ := (tlm_dist_split hd).2.2.1 i hi j hj
    have _ := (tlm_dist_split hd).2.2.1 j hj i hi
    have _ := (tlm_dist_split hd).2.2.1 j hj j hj
    have _ := (tlm_dist_split hd).2.2.2.1 i hi j hj hij
    have _ := (tlm_dist_split hd).2.2.2.2 i hi j hj hij
    tlm_dis))

set_option hygiene false in
local macro "tlm_nin_x" : tactic =>
  `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; repeat' apply And.intro
             all_goals tlm_dd3))

set_option hygiene false in
local macro "tlm_nin_j" : tactic =>
  `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; repeat' apply And.intro
             all_goals tlm_dj))

set_option hygiene false in
local macro "tlm_nx" : tactic =>
  `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; repeat' apply And.intro
             all_goals tlm_dd3))

theorem tlm_loops_lt {nc : Nat} : ∀ (t : Tmpl), t.WF nc → ∀ i ∈ t.loops, i < nc
  | .nil, _, i, h => by simp [Tmpl.loops] at h
  | .tok _, _, i, h => by simp [Tmpl.loops] at h
  | .name _, _, i, h => by simp [Tmpl.loops] at h
  | .seq a b, hw, i, h => by
    simp only [Tmpl.loops, List.mem_append] at h
    rcases h with h | h
    · exact tlm_loops_lt a hw.1 i h
    · exact tlm_loops_lt b hw.2 i h
  | .forR j _ body, hw, i, h => by
    simp only [Tmpl.loops, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact hw.1
    · exact tlm_loops_lt body hw.2.2 i h
  | .ite _ a b, hw, i, h => by
    simp only [Tmpl.loops, List.mem_append] at h
    rcases h with h | h
    · exact tlm_loops_lt a hw.2.1 i h
    · exact tlm_loops_lt b hw.2.2 i h

def tlm_fillB (tt : TT k) : Bound → LProg k
  | .const n => fillP tt n
  | _ => skipP tt.out

def tlm_clearB (tt : TT k) : Bound → LProg k
  | .const _ => clearP' tt.bc
  | _ => skipP tt.out

def tlm_fr : Bound → List Nat
  | .const n => List.replicate n 1
  | _ => []

def tlm_bsmall (Z : Nat) : Bound → Prop
  | .const n => n ≤ Z
  | _ => True

theorem tlm_step_fillB (tt : TT k) {B Z : Nat} (b : Bound) (hs : tlm_bsmall Z b) {L : Lists k} (hL : LenOK B L)
    (hbc : L tt.bc = []) (hZ : Z + 4 ≤ B) :
    Step B (Z + 1) (tlm_fillB tt b) L (fun L' => L' = L.set tt.bc (tlm_fr b)) := by
  cases b with
  | const n =>
    refine (tlm_step_fill tt n hL (by rw [hbc]; simp [tlm_bsmall] at hs ⊢; omega)).mono (by simp [tlm_bsmall] at hs; omega) ?_
    intro L' h; rw [h, hbc]; simp [tlm_fr]
  | S =>
    refine ⟨L, (runs_skip _ hL).mono (by omega), hL, ?_⟩
    simp [tlm_fr]; exact (tlm_set_fl_nil hbc).symm
  | T =>
    refine ⟨L, (runs_skip _ hL).mono (by omega), hL, ?_⟩
    simp [tlm_fr]; exact (tlm_set_fl_nil hbc).symm

theorem tlm_step_clearB (tt : TT k) {B Z : Nat} (b : Bound) (hs : tlm_bsmall Z b) {L : Lists k} (hL : LenOK B L)
    (hbc : L tt.bc = tlm_fr b) :
    Step B (2 * Z + 2) (tlm_clearB tt b) L (fun L' => L' = L.set tt.bc []) := by
  cases b with
  | const n =>
    refine (tlm_step_clear tt.bc hL).mono (by rw [hbc]; simp [tlm_fr, tlm_bsmall] at hs ⊢; omega) (fun _ h => h)
  | S =>
    refine ⟨L, (runs_skip _ hL).mono (by omega), hL, ?_⟩
    simp [tlm_fr] at hbc; exact (tlm_set_fl_nil hbc).symm
  | T =>
    refine ⟨L, (runs_skip _ hL).mono (by omega), hL, ?_⟩
    simp [tlm_fr] at hbc; exact (tlm_set_fl_nil hbc).symm

theorem tlm_forR_unfold (tt : TT k) (i : Nat) (b : Bound) (body : Tmpl) :
    compileT tt (.forR i b body) =
      .seq (moveAll (tt.ct i) (tt.sv i)) (.seq (tlm_fillB tt b) (.seq (ltP tt (tt.ct i) (boundTape tt b))
        (.seq (.loop tt.fl nonEmpty (.seq (.pop tt.fl) (.seq (tlm_clearB tt b) (.seq (compileT tt body)
            (.seq (tlm_fillB tt b) (.seq (.push (tt.ct i) 1) (ltP tt (tt.ct i) (boundTape tt b))))))))
          (.seq (tlm_clearB tt b) (.seq (clearP' (tt.ct i)) (moveAll (tt.sv i) (tt.ct i))))))) := by
  cases b <;> rfl

theorem tlm_ne_ct_x {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {i : Nat} (hi : i < nc) {x : Fin k}
    (h1 : x ≠ tt.ta) (h2 : x ≠ tt.tb') (h3 : x ≠ tt.fl) : TlmNE tt (tt.ct i) x := by
  obtain ⟨_, _, _, _, _, c6, c7, _, c9⟩ := tlm_ctN hd hi
  have hn := tlm_named hd
  exact ⟨c6, c7, c9, h1, h2, h3, by grind, by grind, by grind⟩

theorem tlm_ne_bt {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {i : Nat} (hi : i < nc) (b : Bound) :
    TlmNE tt (tt.ct i) (boundTape tt b) := by
  have hn := tlm_named hd
  cases b with
  | const n => exact tlm_ne_ct_x (x := tt.bc) hd hi (by grind) (by grind) (by grind)
  | S => exact tlm_ne_ct_x (x := tt.sb) hd hi (by grind) (by grind) (by grind)
  | T => exact tlm_ne_ct_x (x := tt.tb) hd hi (by grind) (by grind) (by grind)

theorem tlm_flat_len {f : Nat → List Nat} {v : Nat} :
    ∀ {n : Nat}, v < n →
    (toBits ((List.range v).flatMap f)).length + (toBits (f v)).length ≤ (toBits ((List.range n).flatMap f)).length := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hv
    simp only [List.range_succ, List.flatMap_append, tlm_toBits_append, List.length_append]
    rcases Nat.lt_or_ge v n with h | h
    · have := ih h; omega
    · have : v = n := by omega
      subst this; simp [tlm_toBits_append]

def TlmInv (tt : TT k) (i : Nat) (L : Lists k) (e : TEnv) (acc : List Nat) (b : Bound) (body : Tmpl)
    (L' : Lists k) (v : Nat) : Prop :=
  L' tt.out = acc ++ tlm_bts ((List.range v).flatMap (fun u => body.denote (e.set i u))) ∧
  L' (tt.ct i) = List.replicate v 1 ∧ L' tt.fl = tlm_flv (decide (v < b.val e)) ∧
  L' tt.bc = tlm_fr b ∧ L' (tt.sv i) = List.replicate (e.ctr i) 1 ∧
  TlmFix L L' [tt.out, tt.ct i, tt.fl, tt.bc, tt.sv i]

theorem tlm_bt_val {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {i : Nat} (hi : i < nc) (b : Bound)
    {e : TEnv} {acc : List Nat} {L L' : Lists k} (hT : TRep tt nc e acc L)
    (hf : TlmFix L L' [tt.out, tt.ct i, tt.fl, tt.bc, tt.sv i]) (hbc : L' tt.bc = tlm_fr b) :
    L' (boundTape tt b) = List.replicate (b.val e) 1 := by
  obtain ⟨ho, hin, hsb, htb, hbc', hta, htb', htc, hfl, hct⟩ := hT
  cases b with
  | const n => simpa [tlm_fr, boundTape, Bound.val] using hbc
  | S => simp only [boundTape, Bound.val]; rw [hf _ (by tlm_nin_x), hsb]
  | T => simp only [boundTape, Bound.val]; rw [hf _ (by tlm_nin_x), htb]

set_option maxHeartbeats 4000000 in
theorem tlm_forR_pass {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {B Z : Nat} {i : Nat} (hi : i < nc)
    (b : Bound) (body : Tmpl) (hbody : body.WF nc) (hnot : i ∉ body.loops) (hbs : tlm_bsmall Z b)
    (IH : ∀ (e' : TEnv) (acc' : List Nat) (L' : Lists k), TRep tt nc e' acc' L' →
      (∀ j ∈ body.loops, L' (tt.sv j) = []) → e'.S ≤ Z → e'.T ≤ Z → e'.w.length ≤ Z →
      (∀ j, j < nc → e'.ctr j ≤ Z) → LenOK B L' → acc'.length + (toBits (body.denote e')).length + 2 ≤ B →
      Step B (body.ucost Z) (compileT tt body) L'
        (fun L'' => L'' = L'.set tt.out (acc' ++ tlm_bts (body.denote e'))))
    {e : TEnv} {acc : List Nat} {L : Lists k} (hT : TRep tt nc e acc L)
    (hsv : ∀ j ∈ body.loops, L (tt.sv j) = []) (hS : e.S ≤ Z) (hTT : e.T ≤ Z) (hw : e.w.length ≤ Z)
    (hctr : ∀ j, j < nc → e.ctr j ≤ Z) (hZ : Z + 4 ≤ B) (hbnd : b.val e ≤ Z)
    (htot : acc.length + (toBits ((List.range (b.val e)).flatMap (fun u => body.denote (e.set i u)))).length + 2 ≤ B)
    {L' : Lists k} {v : Nat} (hv : v < b.val e) (hI : TlmInv tt i L e acc b body L' v) (hl : LenOK B L') :
    Step B (body.ucost Z + 2 * tunit Z)
      (.seq (.pop tt.fl) (.seq (tlm_clearB tt b) (.seq (compileT tt body) (.seq (tlm_fillB tt b)
        (.seq (.push (tt.ct i) 1) (ltP tt (tt.ct i) (boundTape tt b)))))))
      L' (fun L'' => TlmInv tt i L e acc b body L'' (v + 1)) := by
  have tun : tunit Z = 100 * (Z + 3) := rfl
  have hvZ : v + 1 ≤ Z := by omega
  have hT0 := hT
  obtain ⟨ho, hin, hsb, htb, hbc, hta, htb', htc, hfl, hct⟩ := hT
  obtain ⟨hio, hic, hif, hibc, hisv, hifix⟩ := hI
  have hflag : L' tt.fl = [0] := by rw [hif]; simp [hv, tlm_flv]
  refine Step.seq' (T₁ := 1) (T₂ := (2 * Z + 2) + (body.ucost Z + ((Z + 1) + (1 + (12 * (v + 1) + 14)))))
    (tlm_step_pop tt.fl hl) (fun L1 hl1 e1 => ?_) (by omega)
  have g1 : ∀ x, x ≠ tt.fl → L1 x = L' x := fun x h => by rw [e1, Lists.set_ne _ _ h]
  have g1f : L1 tt.fl = [] := by rw [e1, Lists.set_same, hflag]; rfl
  refine Step.seq' (T₁ := 2 * Z + 2) (T₂ := body.ucost Z + ((Z + 1) + (1 + (12 * (v + 1) + 14))))
    (tlm_step_clearB tt b hbs hl1 (by rw [g1 _ (by tlm_dd3), hibc])) (fun L2 hl2 e2 => ?_) (by omega)
  have g2 : ∀ x, x ≠ tt.bc → L2 x = L1 x := fun x h => by rw [e2, Lists.set_ne _ _ h]
  have g2b : L2 tt.bc = [] := by rw [e2, Lists.set_same]
  have hL2x : ∀ x, x ∉ [tt.out, tt.ct i, tt.fl, tt.bc, tt.sv i] → L2 x = L x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨x1, x2, x3, x4, x5⟩ := hx
    rw [g2 x x4, g1 x x3, hifix x (by simp [x1, x2, x3, x4, x5])]
  have hTR : TRep tt nc (e.set i v) (acc ++ tlm_bts ((List.range v).flatMap (fun u => body.denote (e.set i u)))) L2 := by
    refine ⟨?_, ?_, ?_, ?_, g2b, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g2 _ (by tlm_dd3), g1 _ (by tlm_dd3)]; exact hio
    · exact (hL2x _ (by tlm_nin_x)).trans hin
    · exact (hL2x _ (by tlm_nin_x)).trans hsb
    · exact (hL2x _ (by tlm_nin_x)).trans htb
    · exact (hL2x _ (by tlm_nin_x)).trans hta
    · exact (hL2x _ (by tlm_nin_x)).trans htb'
    · exact (hL2x _ (by tlm_nin_x)).trans htc
    · rw [g2 _ (by tlm_dd3)]; exact g1f
    · intro j hj
      by_cases hji : j = i
      · rw [hji, show (e.set i v).ctr i = v by simp [TEnv.set], g2 _ (by tlm_dd3), g1 _ (by tlm_dd3)]; exact hic
      · have hij : i ≠ j := fun h => hji h.symm
        rw [show (e.set i v).ctr j = e.ctr j by simp [TEnv.set, hji], hL2x _ (by tlm_nin_j)]
        exact hct j hj
  have hloops : ∀ j ∈ body.loops, L2 (tt.sv j) = [] := by
    intro j hjm
    have hj : j < nc := tlm_loops_lt body hbody j hjm
    have hij : i ≠ j := fun h => hnot (h ▸ hjm)
    rw [hL2x _ (by tlm_nin_j)]; exact hsv j hjm
  have hctr' : ∀ j, j < nc → (e.set i v).ctr j ≤ Z := by
    intro j hj
    by_cases hji : j = i
    · simp [TEnv.set, hji]; omega
    · simp [TEnv.set, hji]; exact hctr j hj
  have hbound : (acc ++ tlm_bts ((List.range v).flatMap (fun u => body.denote (e.set i u)))).length +
      (toBits (body.denote (e.set i v))).length + 2 ≤ B := by
    have := tlm_flat_len (f := fun u => body.denote (e.set i u)) hv
    simp only [List.length_append, tlm_bts, List.length_map]
    omega
  have hIH := IH (e.set i v) _ L2 hTR hloops hS hTT hw hctr' hl2 hbound
  refine Step.seq' (T₁ := body.ucost Z) (T₂ := (Z + 1) + (1 + (12 * (v + 1) + 14))) hIH
    (fun L3 hl3 e3 => ?_) (by omega)
  have g3 : ∀ x, x ≠ tt.out → L3 x = L2 x := fun x h => by rw [e3, Lists.set_ne _ _ h]
  have g3o : L3 tt.out = acc ++ tlm_bts ((List.range v).flatMap (fun u => body.denote (e.set i u))) ++
      tlm_bts (body.denote (e.set i v)) := by rw [e3, Lists.set_same]
  refine Step.seq' (T₁ := Z + 1) (T₂ := 1 + (12 * (v + 1) + 14))
    (tlm_step_fillB tt b hbs hl3 (by rw [g3 _ (by tlm_dd3), g2b]) hZ) (fun L4 hl4 e4 => ?_) (by omega)
  have g4 : ∀ x, x ≠ tt.bc → L4 x = L3 x := fun x h => by rw [e4, Lists.set_ne _ _ h]
  have g4b : L4 tt.bc = tlm_fr b := by rw [e4, Lists.set_same]
  have g4c : L4 (tt.ct i) = List.replicate v 1 := by
    rw [g4 _ (by tlm_dd3), g3 _ (by tlm_dd3), g2 _ (by tlm_dd3), g1 _ (by tlm_dd3)]; exact hic
  refine Step.seq' (T₁ := 1) (T₂ := 12 * (v + 1) + 14)
    (tlm_step_push_p (tt.ct i) 1 hl4 (by rw [g4c]; simp; omega)) (fun L5 hl5 e5 => ?_) (by omega)
  have g5 : ∀ x, x ≠ tt.ct i → L5 x = L4 x := fun x h => by rw [e5, Lists.set_ne _ _ h]
  have g5c : L5 (tt.ct i) = List.replicate (v + 1) 1 := by
    rw [e5, Lists.set_same, g4c, List.replicate_succ']
  have g5f : ∀ x, x ∉ [tt.out, tt.ct i, tt.fl, tt.bc, tt.sv i] → L5 x = L x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨x1, x2, x3, x4, x5⟩ := hx
    rw [g5 x x2, g4 x x4, g3 x x1, hL2x x (by simp [x1, x2, x3, x4, x5])]
  have g5b : L5 tt.bc = tlm_fr b := by rw [g5 _ (by tlm_dd3)]; exact g4b
  have g5fl : L5 tt.fl = [] := by
    rw [g5 _ (by tlm_dd3), g4 _ (by tlm_dd3), g3 _ (by tlm_dd3), g2 _ (by tlm_dd3)]; exact g1f
  have g5bt : L5 (boundTape tt b) = List.replicate (b.val e) 1 :=
    tlm_bt_val hd hi b hT0 (fun x hx => g5f x hx) g5b
  refine ((tlm_step_ltP' tt (tlm_ne_bt hd hi b) hl5 g5c g5bt (by rw [g5f _ (by tlm_nin_x)]; exact hta)
    (by rw [g5f _ (by tlm_nin_x)]; exact htb') g5fl (by omega) (by omega)).mono (Nat.le_refl _) ?_)
  intro L6 e6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e6, Lists.set_ne _ _ (by tlm_dd3), g5 _ (by tlm_dd3), g4 _ (by tlm_dd3), g3o]
    simp only [List.range_succ, List.flatMap_append, tlm_bts_append, List.flatMap_singleton, List.append_assoc]
  · rw [e6, Lists.set_ne _ _ (by tlm_dd3), g5c]
  · rw [e6, Lists.set_same]
  · rw [e6, Lists.set_ne _ _ (by tlm_dd3), g5b]
  · rw [e6, Lists.set_ne _ _ (by tlm_dd3), g5 _ (by tlm_dd3), g4 _ (by tlm_dd3), g3 _ (by tlm_dd3), g2 _ (by tlm_dd3),
      g1 _ (by tlm_dd3)]; exact hisv
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨x1, x2, x3, x4, x5⟩ := hx
    rw [e6, Lists.set_ne _ _ x3, g5f x (by simp [x1, x2, x3, x4, x5])]

set_option maxHeartbeats 4000000 in
theorem tlm_step_forR {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {B Z : Nat} {i : Nat} (hi : i < nc)
    (b : Bound) (body : Tmpl) (hbody : body.WF nc) (hnot : i ∉ body.loops) (hbs : tlm_bsmall Z b)
    (IH : ∀ (e' : TEnv) (acc' : List Nat) (L' : Lists k), TRep tt nc e' acc' L' →
      (∀ j ∈ body.loops, L' (tt.sv j) = []) → e'.S ≤ Z → e'.T ≤ Z → e'.w.length ≤ Z →
      (∀ j, j < nc → e'.ctr j ≤ Z) → LenOK B L' → acc'.length + (toBits (body.denote e')).length + 2 ≤ B →
      Step B (body.ucost Z) (compileT tt body) L'
        (fun L'' => L'' = L'.set tt.out (acc' ++ tlm_bts (body.denote e'))))
    {e : TEnv} {acc : List Nat} {L : Lists k} (hT : TRep tt nc e acc L)
    (hsv : ∀ j ∈ i :: body.loops, L (tt.sv j) = []) (hS : e.S ≤ Z) (hTT : e.T ≤ Z) (hw : e.w.length ≤ Z)
    (hctr : ∀ j, j < nc → e.ctr j ≤ Z) (hZ : Z + 4 ≤ B) (hL : LenOK B L) (hbnd : b.val e ≤ Z)
    (htot : acc.length + (toBits ((List.range (b.val e)).flatMap (fun u => body.denote (e.set i u)))).length + 2 ≤ B) :
    Step B (4 * tunit Z + (Z + 1) * (body.ucost Z + 4 * tunit Z)) (compileT tt (.forR i b body)) L
      (fun L' => L' = L.set tt.out (acc ++ tlm_bts ((List.range (b.val e)).flatMap (fun u => body.denote (e.set i u))))) := by
  have tun : tunit Z = 100 * (Z + 3) := rfl
  have hT0 := hT
  obtain ⟨ho, hin, hsb, htb, hbc, hta, htb', htc, hfl, hct⟩ := hT
  have hsvi : L (tt.sv i) = [] := hsv i (by simp)
  have hci := hct i hi
  have hcZ := hctr i hi
  rw [tlm_forR_unfold]
  have hbl : b.val e = b.val e := rfl
  refine Step.seq' (T₁ := (e.ctr i + 1) * 3)
    (T₂ := (Z + 1) + (14 + (((Z + 1) * (body.ucost Z + 4 * tunit Z)) + ((2 * Z + 2) + ((2 * Z + 2) + (3 * Z + 3))))))
    ((tlm_step_mvAll (i := tt.ct i) (j := tt.sv i) (by tlm_dd3) hL (by rw [hsvi, hci]; simp; omega)).mono
      (by rw [hci]; simp) (fun _ h => h))
    (fun L1 hl1 e1 => ?_) (by simp only [tun]; omega)
  have f1 : ∀ x, x ≠ tt.ct i → x ≠ tt.sv i → L1 x = L x := by
    intro x h1 h2; rw [e1, moveAll_other h1 h2]
  have f1c : L1 (tt.ct i) = [] := by rw [e1]; exact moveAll_i
  have f1s : L1 (tt.sv i) = List.replicate (e.ctr i) 1 := by
    rw [e1, moveAll_j (by tlm_dd3), hsvi, hci]; simp
  refine Step.seq' (T₁ := Z + 1)
    (T₂ := 14 + (((Z + 1) * (body.ucost Z + 4 * tunit Z)) + ((2 * Z + 2) + ((2 * Z + 2) + (3 * Z + 3)))))
    (tlm_step_fillB tt b hbs hl1 (by rw [f1 _ (by tlm_dd3) (by tlm_dd3)]; exact hbc) hZ)
    (fun L2 hl2 e2 => ?_) (by omega)
  have g2 : ∀ x, x ≠ tt.bc → L2 x = L1 x := fun x h => by rw [e2, Lists.set_ne _ _ h]
  have g2b : L2 tt.bc = tlm_fr b := by rw [e2, Lists.set_same]
  have hf2 : TlmFix L L2 [tt.out, tt.ct i, tt.fl, tt.bc, tt.sv i] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨x1, x2, x3, x4, x5⟩ := hx
    rw [g2 x x4, f1 x x2 x5]
  have hbt2 : L2 (boundTape tt b) = List.replicate (b.val e) 1 := tlm_bt_val hd hi b hT0 hf2 g2b
  have g2c : L2 (tt.ct i) = List.replicate 0 1 := by rw [g2 _ (by tlm_dd3), f1c]; rfl
  refine Step.seq' (T₁ := 14)
    (T₂ := ((Z + 1) * (body.ucost Z + 4 * tunit Z)) + ((2 * Z + 2) + ((2 * Z + 2) + (3 * Z + 3))))
    ((tlm_step_ltP' tt (tlm_ne_bt hd hi b) hl2 g2c hbt2 (by rw [hf2 _ (by tlm_nin_x)]; exact hta)
      (by rw [hf2 _ (by tlm_nin_x)]; exact htb') (by rw [g2 _ (by tlm_dd3), f1 _ (by tlm_dd3) (by tlm_dd3)]; exact hfl) (by omega) (by omega)).mono
      (by omega) (fun _ h => h))
    (fun L3 hl3 e3 => ?_) (by omega)
  have g3 : ∀ x, x ≠ tt.fl → L3 x = L2 x := fun x h => by rw [e3, Lists.set_ne _ _ h]
  have inv0 : TlmInv tt i L e acc b body L3 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g3 _ (by tlm_dd3), g2 _ (by tlm_dd3), f1 _ (by tlm_dd3) (by tlm_dd3), ho]; simp [tlm_bts, toBits]
    · rw [g3 _ (by tlm_dd3), g2c]
    · rw [e3, Lists.set_same]
    · rw [g3 _ (by tlm_dd3), g2b]
    · rw [g3 _ (by tlm_dd3), g2 _ (by tlm_dd3), f1s]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      obtain ⟨x1, x2, x3, x4, x5⟩ := hx
      rw [g3 x x3, hf2 x (by simp [x1, x2, x3, x4, x5])]
  have hsv' : ∀ j ∈ body.loops, L (tt.sv j) = [] := fun j hj => hsv j (List.mem_cons_of_mem _ hj)
  have hmain := runs_loop (Q := LenOK B) (i := tt.fl) (c := nonEmpty)
    (p := .seq (.pop tt.fl) (.seq (tlm_clearB tt b) (.seq (compileT tt body) (.seq (tlm_fillB tt b)
        (.seq (.push (tt.ct i) 1) (ltP tt (tt.ct i) (boundTape tt b)))))))
    (I := fun L' => LenOK B L' ∧ ∃ v, v ≤ b.val e ∧ TlmInv tt i L e acc b body L' v)
    (μ := fun L' => b.val e - (L' (tt.ct i)).length) (T := body.ucost Z + 2 * tunit Z)
    (fun L' h => h.1) ?_ L3 ⟨hl3, 0, Nat.zero_le _, inv0⟩
  · have hloop : Step B ((Z + 1) * (body.ucost Z + 4 * tunit Z))
        (.loop tt.fl nonEmpty (.seq (.pop tt.fl) (.seq (tlm_clearB tt b) (.seq (compileT tt body)
          (.seq (tlm_fillB tt b) (.seq (.push (tt.ct i) 1) (ltP tt (tt.ct i) (boundTape tt b))))))))
        L3 (fun L4 => TlmInv tt i L e acc b body L4 (b.val e)) := by
      obtain ⟨L4, hr, ⟨hl4, v, hv, hI4⟩, hc4⟩ := hmain
      have hvb : v = b.val e := by
        have h1 := tlm_nonEmpty_flv (decide (v < b.val e))
        rw [← hI4.2.2.1, hc4] at h1
        by_cases hh : v < b.val e
        · simp [hh] at h1
        · omega
      subst hvb
      refine ⟨L4, hr.mono ?_, hl4, hI4⟩
      have hl3c : (L3 (tt.ct i)).length = 0 := by rw [inv0.2.1]; simp
      show (b.val e - (L3 (tt.ct i)).length + 1) * (body.ucost Z + 2 * tunit Z + 1) ≤ _
      exact Nat.mul_le_mul (by omega) (by omega)
    refine Step.seq' (T₁ := (Z + 1) * (body.ucost Z + 4 * tunit Z)) (T₂ := (2 * Z + 2) + ((2 * Z + 2) + (3 * Z + 3)))
      hloop (fun L4 hl4 hI4 => ?_) (by omega)
    obtain ⟨i4o, i4c, i4f, i4b, i4s, i4x⟩ := hI4
    refine Step.seq' (T₁ := 2 * Z + 2) (T₂ := (2 * Z + 2) + (3 * Z + 3))
      (tlm_step_clearB tt b hbs hl4 i4b) (fun L5 hl5 e5 => ?_) (by omega)
    have g5 : ∀ x, x ≠ tt.bc → L5 x = L4 x := fun x h => by rw [e5, Lists.set_ne _ _ h]
    have g5b : L5 tt.bc = [] := by rw [e5, Lists.set_same]
    have g5c : L5 (tt.ct i) = List.replicate (b.val e) 1 := by rw [g5 _ (by tlm_dd3), i4c]
    refine Step.seq' (T₁ := 2 * Z + 2) (T₂ := 3 * Z + 3)
      ((tlm_step_clear (tt.ct i) hl5).mono (by rw [g5c]; simp; omega) (fun _ h => h)) (fun L6 hl6 e6 => ?_)
      (by omega)
    have g6 : ∀ x, x ≠ tt.ct i → L6 x = L5 x := fun x h => by rw [e6, Lists.set_ne _ _ h]
    have g6c : L6 (tt.ct i) = [] := by rw [e6, Lists.set_same]
    have g6s : L6 (tt.sv i) = List.replicate (e.ctr i) 1 := by
      rw [g6 _ (by tlm_dd3), g5 _ (by tlm_dd3), i4s]
    refine ((tlm_step_mvAll (i := tt.sv i) (j := tt.ct i) (Ne.symm (by tlm_dd3)) hl6
      (by rw [g6s, g6c]; simp; omega)).mono (by rw [g6s]; simp; omega) ?_)
    intro L7 e7
    apply tlm_eq_set
    · rw [e7, moveAll_other (by tlm_dd3) (by tlm_dd3), g6 _ (by tlm_dd3), g5 _ (by tlm_dd3), i4o]
    · intro x hx
      rw [e7]
      by_cases xc : x = tt.ct i
      · rw [xc, moveAll_j (Ne.symm (by tlm_dd3)), g6c, g6s, hci]; simp
      by_cases xs : x = tt.sv i
      · rw [xs, moveAll_i, hsvi]
      rw [moveAll_other xs xc, g6 x xc]
      by_cases xf : x = tt.fl
      · rw [xf, g5 _ (by tlm_dd3), i4f, hfl]; simp [tlm_flv]
      by_cases xb : x = tt.bc
      · rw [xb, g5b, hbc]
      rw [g5 x xb, i4x x (by simp [hx, xc, xf, xb, xs])]
  · rintro L' ⟨hl', v, hv, hI⟩ hc
    have hfl' : L' tt.fl = tlm_flv (decide (v < b.val e)) := hI.2.2.1
    have hvlt : v < b.val e := by
      have h1 := tlm_nonEmpty_flv (decide (v < b.val e))
      rw [← hfl', hc] at h1
      by_cases hh : v < b.val e
      · exact hh
      · simp [hh] at h1
    obtain ⟨L'', hr, hl'', hI''⟩ := tlm_forR_pass hd hi b body hbody hnot hbs IH hT0 hsv' hS hTT hw hctr hZ hbnd htot
      hvlt hI hl'
    refine ⟨L'', hr, ⟨hl'', v + 1, by omega, hI''⟩, ?_⟩
    show b.val e - (L'' (tt.ct i)).length < b.val e - (L' (tt.ct i)).length
    rw [hI''.2.1, hI.2.1]; simp; omega

theorem tlm_step_t {tt : TT k} {nc : Nat} (hd : tt.Distinct nc) {B Z : Nat} :
    ∀ (t : Tmpl), t.WF nc → t.Small Z →
    ∀ {e : TEnv} {acc : List Nat} {L : Lists k}, TRep tt nc e acc L → (∀ i ∈ t.loops, L (tt.sv i) = []) →
    e.S ≤ Z → e.T ≤ Z → e.w.length ≤ Z → (∀ i, i < nc → e.ctr i ≤ Z) → LenOK B L → Z + 4 ≤ B →
    acc.length + (toBits (t.denote e)).length + 2 ≤ B →
    Step B (t.ucost Z) (compileT tt t) L (fun L' => L' = L.set tt.out (acc ++ tlm_bts (t.denote e)))
  | .nil, _, _, e, acc, L, hT, _, _, _, _, _, hL, _, _ => by
    have ho := hT.1
    refine ⟨L, runs_skip _ hL, hL, ?_⟩
    show L = L.set tt.out (acc ++ tlm_bts [])
    rw [show tlm_bts [] = [] by simp [tlm_bts, toBits], List.append_nil, ← ho, tlm_set_self]
  | .tok t, _, _, e, acc, L, hT, _, _, _, _, _, hL, _, hb => by
    have ho := hT.1
    have := tlm_step_emitTok tt t hL (by
      rw [ho]; simp [Tmpl.denote, toBits, tokBits] at hb; omega)
    refine this.mono (by simp [Tmpl.ucost, tunit]; omega) ?_
    intro L' h
    rw [h, ho]; simp [Tmpl.denote, tlm_bts_single]
  | .name ps, hwf, hs, e, acc, L, hT, _, hS, hTT, hw, hctr, hL, hZ, hb => by
    have := tlm_step_name hd ps hwf hs hT hL hZ hS hTT hctr (by
      simp [Tmpl.denote, tlm_toBits_length] at hb ⊢; omega)
    exact this.mono (by simp [Tmpl.ucost]) (fun L' h => by rw [h]; rfl)
  | .seq a b, hwf, hs, e, acc, L, hT, hsv, hS, hTT, hw, hctr, hL, hZ, hb => by
    have hb' : acc.length + (toBits (a.denote e)).length + 2 + (toBits (b.denote e)).length ≤ B := by
      simp only [Tmpl.denote, tlm_toBits_append, List.length_append] at hb; omega
    have hsva : ∀ i ∈ a.loops, L (tt.sv i) = [] := fun i hi => hsv i (by simp [Tmpl.loops, hi])
    refine Step.seq' (T₁ := a.ucost Z) (T₂ := b.ucost Z)
      (tlm_step_t hd a hwf.1 hs.1 hT hsva hS hTT hw hctr hL hZ (by omega)) (fun L1 hl1 e1 => ?_) (Nat.le_refl _)
    subst e1
    have hT1 := tlm_trep_out hd hT (acc ++ tlm_bts (a.denote e))
    have hsvb : ∀ i ∈ b.loops, (L.set tt.out (acc ++ tlm_bts (a.denote e))) (tt.sv i) = [] := by
      intro i hi
      have hlt := tlm_loops_lt b hwf.2 i hi
      tlm_get_named hd
      tlm_get_sv hd hlt
      rw [Lists.set_ne _ _ (by tlm_dis)]
      exact hsv i (by simp [Tmpl.loops, hi])
    have := tlm_step_t hd b hwf.2 hs.2 hT1 hsvb hS hTT hw hctr hl1 hZ (by
      simp [tlm_bts, List.length_map]; omega)
    refine this.mono (Nat.le_refl _) ?_
    intro L' h
    rw [h, tlm_set_set, Tmpl.denote, tlm_bts_append, List.append_assoc]
  | .ite c a b, hwf, hs, e, acc, L, hT, hsv, hS, hTT, hw, hctr, hL, hZ, hb => by
    have hfl := hT.2.2.2.2.2.2.2.2.1
    have hsva : ∀ i ∈ a.loops, L (tt.sv i) = [] := fun i hi => hsv i (by simp [Tmpl.loops, hi])
    have hsvb : ∀ i ∈ b.loops, L (tt.sv i) = [] := fun i hi => hsv i (by simp [Tmpl.loops, hi])
    have hdef : compileT tt (.ite c a b) = .seq (condP tt c) (.ite tt.fl nonEmpty (.seq (.pop tt.fl) (compileT tt a))
        (compileT tt b)) := rfl
    rw [hdef]
    refine Step.seq' (T₁ := c.cost Z) (T₂ := 2 + a.ucost Z + b.ucost Z)
      (tlm_step_cond hd c hwf.1 hs.1 hT hL hZ hw hctr) (fun L1 hl1 e1 => ?_) (by simp [Tmpl.ucost]; omega)
    have hfl1 : L1 tt.fl = tlm_flv (c.eval e) := by rw [e1]; simp
    cases hbc : c.eval e with
    | false =>
      have hc : nonEmpty (lastSym (L1 tt.fl)) = false := by rw [hfl1, hbc]; exact tlm_nonEmpty_flv false
      have hL1 : L1 = L := by
        rw [e1, hbc]; simp [tlm_flv]; exact tlm_set_fl_nil hfl
      have hT1 : TRep tt nc e acc L1 := by rw [hL1]; exact hT
      have := tlm_step_t hd b hwf.2.2 hs.2.2 hT1 (by rw [hL1]; exact hsvb) hS hTT hw hctr hl1 hZ (by
        simp [Tmpl.denote, hbc] at hb; omega)
      refine (Step.iteF (T := b.ucost Z) hl1 hc this).mono (by omega) ?_
      intro L' h; rw [h, hL1]; simp [Tmpl.denote, hbc]
    | true =>
      have hc : nonEmpty (lastSym (L1 tt.fl)) = true := by rw [hfl1, hbc]; exact tlm_nonEmpty_flv true
      refine (Step.iteT (T := 1 + a.ucost Z) hl1 hc
        (Step.seq' (T₁ := 1) (T₂ := a.ucost Z) (tlm_step_pop tt.fl hl1) (fun L2 hl2 e2 => ?_) (Nat.le_refl _))).mono
        (by omega) (fun _ h => h)
      have hL2 : L2 = L := by
        rw [e2, e1, hbc]; simp [tlm_flv, tlm_set_set, tlm_set_fl_nil hfl]
      have hT2 : TRep tt nc e acc L2 := by rw [hL2]; exact hT
      have := tlm_step_t hd a hwf.2.1 hs.2.1 hT2 (by rw [hL2]; exact hsva) hS hTT hw hctr hl2 hZ (by
        simp [Tmpl.denote, hbc] at hb; omega)
      refine this.mono (Nat.le_refl _) ?_
      intro L' h; rw [h, hL2]; simp [Tmpl.denote, hbc]
  | .forR i bd body, hwf, hs, e, acc, L, hT, hsv, hS, hTT, hw, hctr, hL, hZ, hb => by
    obtain ⟨hi, hnot, hbody⟩ := hwf
    have hbnd : bd.val e ≤ Z := by
      cases bd with
      | const n => exact hs.1
      | S => exact hS
      | T => exact hTT
    exact tlm_step_forR hd hi bd body hbody hnot hs.1
      (fun e' acc' L' hT' hl hS' hT'' hw' hctr' hL' hb' =>
        tlm_step_t hd body hbody hs.2 hT' hl hS' hT'' hw' hctr' hL' hZ hb')
      hT hsv hS hTT hw hctr hZ hL hbnd hb

theorem compileT_spec (tt : TT k) (nc Z B : Nat) (hd : tt.Distinct nc) :
    ∀ (t : Tmpl), t.WF nc → t.Small Z → ∀ (e : TEnv) (acc : List Nat) (L : Lists k),
      TRep tt nc e acc L → (∀ i ∈ t.loops, L (tt.sv i) = []) →
      e.S ≤ Z → e.T ≤ Z → e.w.length ≤ Z → (∀ i, i < nc → e.ctr i ≤ Z) →
      LenOK B L → Z + 4 ≤ B → acc.length + (toBits (t.denote e)).length + 2 ≤ B →
      Runs (LenOK B) (compileT tt t) L (L.set tt.out (acc ++ (toBits (t.denote e)).map bit01)) (t.ucost Z) := by
  intro t hwf hs e acc L hT hsv hS hTT hw hctr hL hZ hb
  obtain ⟨L', hr, _, rfl⟩ := tlm_step_t hd t hwf hs hT hsv hS hTT hw hctr hL hZ hb
  exact hr

end Complexity
