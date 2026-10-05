import MacroPeg.Properties.DecideCBV

/-!
# The cost of the decision procedures

`Decide.lean` and `DecideCBV.lean` bound the number of rounds of the table iteration. This file counts the work: the
cost of one evaluation, of one round, and of the whole procedure, in a simple cost model that follows the evaluators'
control flow exactly (the branches taken are those of `ev`/`evV`):

* every expression node costs 1, a table lookup costs 1, a literal or parameter comparison costs the string's length + 1;
* call-by-value evaluates each actual argument once (`costV`); call-by-name computes each argument's value at all
  `n + 1` positions (`costN`), since that value is the table key.

Results:

* `costV_le` / `costN_le`: one evaluation costs at most `cbV n e` / `cbN n e`, and `cbV_le` / `cbN_le` bound these by
  `size e · (n+2)^(depth e + 1)` — polynomial in `n` for a fixed expression (the degree is the nesting depth of `star`,
  and for call-by-name also of actual arguments);
* `totalCostV_le`: the whole call-by-value procedure costs at most `iterBoundV² · B + cbV n e` (`B` bounds the rule
  bodies' `cbV`) — with `iterBoundV_le`, polynomial in `n`;
* `totalCostN_le`: likewise `iterBound² · B + cbN n e` for call-by-name — exponential through `iterBound`.

The model charges the table as an array indexed by the entry (lookup cost 1); building the index of an argument tuple is
counted as the cost of computing the tuple.
-/

namespace Shallot.MacroPeg

/-- `star`'s cost: the body's cost at each visited position, plus one per repetition. -/
def costStar (f : Nat → Res) (c : Nat → Nat) (p : Nat) : Nat :=
  c p + match f p with
    | some (some j) => if j < p then 1 + costStar f c j else 0
    | _ => 0
termination_by p
decreasing_by omega

theorem costStar_le {f : Nat → Res} {c : Nat → Nat} {B : Nat} :
    ∀ p, (∀ q, q ≤ p → c q ≤ B) → costStar f c p ≤ (p + 1) * (B + 1) := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro hc
    have hp := hc p (Nat.le_refl _)
    have h3 : (p + 1) * (B + 1) = p * (B + 1) + (B + 1) := Nat.succ_mul p (B + 1)
    rw [costStar]
    cases hf : f p with
    | none => simp only; omega
    | some r =>
      cases r with
      | none => simp only; omega
      | some j =>
        simp only
        by_cases hj : j < p
        · rw [if_pos hj]
          have h1 := ih j hj (fun q hq => hc q (by omega))
          have h2 : (j + 1) * (B + 1) ≤ p * (B + 1) := Nat.mul_le_mul_right _ (by omega)
          omega
        · rw [if_neg hj]; omega

/-! ## Call-by-value -/

section CostV

variable (g : MGrammar) (x : List Char)

mutual
  def costV (s : Strategy) (T : Nat → List (List Char) → Val) (E : List (List Char)) : MExp → Nat → Nat
    | .lit w, _ => w.length + 1
    | .param k, _ =>
      (match E[k]? with
        | some w => w.length
        | none => 0) + 1
    | .call i args, p =>
      match ruleAtM g.rules i with
      | some r =>
        if r.arity = args.length then
          match s with
          | .callByValueSeq => 2 + costSeqArgs s T E args p
          | _ => 2 + costParArgs s T E args p
        else 1
      | none => 1
    | .seq a b, p =>
      1 + costV s T E a p +
        match evV g x s T E a p with
        | some (some j) => costV s T E b j
        | _ => 0
    | .alt a b, p =>
      1 + costV s T E a p +
        match evV g x s T E a p with
        | some none => costV s T E b p
        | _ => 0
    | .notP a, p => 1 + costV s T E a p
    | .star a, p => 1 + costStar (fun q => evV g x s T E a q) (fun q => costV s T E a q) p
    | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .dbg _, _ | .lam _ _, _ | .callParam _ _, _
    | .invoke _ _ _, _ => 1

  def costParArgs (s : Strategy) (T : Nat → List (List Char) → Val) (E : List (List Char)) :
      List MExp → Nat → Nat
    | [], _ => 0
    | a :: as, p =>
      costV s T E a p +
        match evV g x s T E a p with
        | some (some _) => costParArgs s T E as p
        | _ => 0

  def costSeqArgs (s : Strategy) (T : Nat → List (List Char) → Val) (E : List (List Char)) :
      List MExp → Nat → Nat
    | [], _ => 0
    | a :: as, p =>
      costV s T E a p +
        match evV g x s T E a p with
        | some (some j) => costSeqArgs s T E as j
        | _ => 0
end

end CostV

/- The cost bound of one call-by-value evaluation at input length `n`. -/
mutual
  def cbV (n : Nat) : MExp → Nat
    | .lit w => w.length + 1
    | .param _ => n + 1
    | .call _ args => 2 + cbVArgs n args
    | .seq a b => 1 + cbV n a + cbV n b
    | .alt a b => 1 + cbV n a + cbV n b
    | .notP a => 1 + cbV n a
    | .star a => 1 + (n + 1) * (cbV n a + 1)
    | .eps | .any | .chr _ | .range _ _ | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => 1

  def cbVArgs (n : Nat) : List MExp → Nat
    | [] => 0
    | a :: as => cbV n a + cbVArgs n as
end

mutual
  theorem costV_le {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      {E : List (List Char)} (hT : OkTV x.length T) (hE : ∀ w ∈ E, w.length ≤ x.length) :
      ∀ (e : MExp) (p : Nat), p ≤ x.length → costV g x s T E e p ≤ cbV x.length e
    | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .dbg _, _, _ | .lam _ _, _, _
    | .callParam _ _, _, _ | .invoke _ _ _, _, _ => by simp only [costV, cbV]; omega
    | .lit w, _, _ => by simp only [costV, cbV]; omega
    | .param k, _, _ => by
      simp only [costV, cbV]
      split
      · rename_i w h; have := hE w (List.mem_of_getElem? h); omega
      · omega
    | .call i args, p, hp => by
      simp only [costV, cbV]
      split
      · split
        · split
          · exact Nat.add_le_add_left (costSeqArgs_le hT hE args p hp) 2
          · exact Nat.add_le_add_left (costParArgs_le hT hE args p hp) 2
        · omega
      · omega
    | .seq a b, p, hp => by
      simp only [costV, cbV]
      have ha := costV_le (g := g) (s := s) hT hE a p hp
      split
      · rename_i j h
        have := costV_le (g := g) (s := s) hT hE b j (evV_ok hT a p hp j h); omega
      · omega
    | .alt a b, p, hp => by
      simp only [costV, cbV]
      have ha := costV_le (g := g) (s := s) hT hE a p hp
      split
      · have := costV_le (g := g) (s := s) hT hE b p hp; omega
      · omega
    | .notP a, p, hp => by
      simp only [costV, cbV]; have := costV_le (g := g) (s := s) hT hE a p hp; omega
    | .star a, p, hp => by
      simp only [costV, cbV]
      have := costStar_le (f := fun q => evV g x s T E a q) (c := fun q => costV g x s T E a q) p
        (fun q hq => costV_le (g := g) (s := s) hT hE a q (by omega))
      have : (p + 1) * (cbV x.length a + 1) ≤ (x.length + 1) * (cbV x.length a + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      omega

  theorem costParArgs_le {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      {E : List (List Char)} (hT : OkTV x.length T) (hE : ∀ w ∈ E, w.length ≤ x.length) :
      ∀ (as : List MExp) (p : Nat), p ≤ x.length → costParArgs g x s T E as p ≤ cbVArgs x.length as
    | [], _, _ => by simp [costParArgs, cbVArgs]
    | a :: as, p, hp => by
      simp only [costParArgs, cbVArgs]
      have ha := costV_le (g := g) (s := s) hT hE a p hp
      split
      · have := costParArgs_le (g := g) (s := s) hT hE as p hp; omega
      · omega

  theorem costSeqArgs_le {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      {E : List (List Char)} (hT : OkTV x.length T) (hE : ∀ w ∈ E, w.length ≤ x.length) :
      ∀ (as : List MExp) (p : Nat), p ≤ x.length → costSeqArgs g x s T E as p ≤ cbVArgs x.length as
    | [], _, _ => by simp [costSeqArgs, cbVArgs]
    | a :: as, p, hp => by
      simp only [costSeqArgs, cbVArgs]
      have ha := costV_le (g := g) (s := s) hT hE a p hp
      split
      · rename_i j h
        have := costSeqArgs_le (g := g) (s := s) hT hE as j (evV_ok hT a p hp j h); omega
      · omega
end

/-! ## Size and depth -/

mutual
  /-- Size: nodes, plus literal lengths. -/
  def MExp.sz : MExp → Nat
    | .lit w => w.length + 1
    | .call _ args => 2 + MExp.szArgs args
    | .seq a b => 1 + MExp.sz a + MExp.sz b
    | .alt a b => 1 + MExp.sz a + MExp.sz b
    | .notP a => 1 + MExp.sz a
    | .star a => 1 + MExp.sz a
    | .eps | .any | .chr _ | .range _ _ | .param _ | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => 1

  def MExp.szArgs : List MExp → Nat
    | [] => 0
    | a :: as => MExp.sz a + MExp.szArgs as
end

mutual
  /-- Nesting depth of `star`. -/
  def MExp.starDepth : MExp → Nat
    | .call _ args => MExp.starDepthArgs args
    | .seq a b => max (MExp.starDepth a) (MExp.starDepth b)
    | .alt a b => max (MExp.starDepth a) (MExp.starDepth b)
    | .notP a => MExp.starDepth a
    | .star a => MExp.starDepth a + 1
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => 0

  def MExp.starDepthArgs : List MExp → Nat
    | [] => 0
    | a :: as => max (MExp.starDepth a) (MExp.starDepthArgs as)
end

theorem pow_pos' (n k : Nat) : 1 ≤ (n + 2) ^ k := Nat.pow_pos (by omega)

theorem sum_map_mul {α : Type} (f : α → Nat) (B : Nat) :
    ∀ l : List α, (l.map f).sum * B = (l.map (fun i => f i * B)).sum
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, Nat.add_mul, sum_map_mul f B l]

theorem pow_mono' (n : Nat) {a b : Nat} (h : a ≤ b) : (n + 2) ^ a ≤ (n + 2) ^ b := Nat.pow_le_pow_right (by omega) h

mutual
  /-- **One call-by-value evaluation is polynomial**: `cbV n e ≤ size e · (n+2)^(starDepth e + 1)`. -/
  theorem cbV_le (n : Nat) : ∀ e : MExp, cbV n e ≤ e.sz * (n + 2) ^ (e.starDepth + 1)
    | .eps | .any | .chr _ | .range _ _ | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => by
      simp only [cbV, MExp.sz, MExp.starDepth, Nat.one_mul]; exact pow_pos' n _
    | .param _ => by
      simp only [cbV, MExp.sz, MExp.starDepth, Nat.one_mul, Nat.zero_add, Nat.pow_one]; omega
    | .lit w => by
      simp only [cbV, MExp.sz, MExp.starDepth, Nat.zero_add, Nat.pow_one]
      exact Nat.le_mul_of_pos_right _ (by omega)
    | .call _ args => by
      simp only [cbV, MExp.sz, MExp.starDepth]
      have h := cbVArgs_le n args
      have h1 := pow_pos' n (MExp.starDepthArgs args + 1)
      rw [Nat.add_mul]
      omega
    | .seq a b => by
      simp only [cbV, MExp.sz, MExp.starDepth]
      have ha := cbV_le n a
      have hb := cbV_le n b
      have ha' := Nat.le_trans ha (Nat.mul_le_mul_left a.sz (pow_mono' n (Nat.add_le_add_right (Nat.le_max_left a.starDepth b.starDepth) 1)))
      have hb' := Nat.le_trans hb (Nat.mul_le_mul_left b.sz (pow_mono' n (Nat.add_le_add_right (Nat.le_max_right a.starDepth b.starDepth) 1)))
      have h1 := pow_pos' n (max a.starDepth b.starDepth + 1)
      rw [Nat.add_mul, Nat.add_mul]
      omega
    | .alt a b => by
      simp only [cbV, MExp.sz, MExp.starDepth]
      have ha := cbV_le n a
      have hb := cbV_le n b
      have ha' := Nat.le_trans ha (Nat.mul_le_mul_left a.sz (pow_mono' n (Nat.add_le_add_right (Nat.le_max_left a.starDepth b.starDepth) 1)))
      have hb' := Nat.le_trans hb (Nat.mul_le_mul_left b.sz (pow_mono' n (Nat.add_le_add_right (Nat.le_max_right a.starDepth b.starDepth) 1)))
      have h1 := pow_pos' n (max a.starDepth b.starDepth + 1)
      rw [Nat.add_mul, Nat.add_mul]
      omega
    | .notP a => by
      simp only [cbV, MExp.sz, MExp.starDepth]
      have ha := cbV_le n a
      have h1 := pow_pos' n (a.starDepth + 1)
      rw [Nat.add_mul]
      omega
    | .star a => by
      simp only [cbV, MExp.sz, MExp.starDepth]
      have ha := cbV_le n a
      generalize hQ : (n + 2) ^ (a.starDepth + 1) = Q at ha
      have hQ1 : 1 ≤ Q := hQ ▸ pow_pos' n _
      have hP : (n + 2) ^ (a.starDepth + 1 + 1) = Q * (n + 2) := by rw [← hQ, Nat.pow_succ]
      rw [hP]
      -- 1 + (n+1)(c + 1) ≤ (1 + s)·Q·(n+2), with c ≤ s·Q
      have h1 : (n + 1) * (cbV n a + 1) ≤ (n + 1) * (a.sz * Q + 1) := Nat.mul_le_mul_left _ (by omega)
      have h2 : (n + 1) * (a.sz * Q + 1) = (n + 1) * (a.sz * Q) + (n + 1) := by rw [Nat.mul_add, Nat.mul_one]
      have h3 : (n + 1) * (a.sz * Q) ≤ a.sz * Q * (n + 2) := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
      have h4 : n + 2 ≤ Q * (n + 2) := Nat.le_mul_of_pos_left _ (by omega)
      have h5 : (1 + a.sz) * (Q * (n + 2)) = Q * (n + 2) + a.sz * Q * (n + 2) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
      omega

  theorem cbVArgs_le (n : Nat) : ∀ as : List MExp, cbVArgs n as ≤ MExp.szArgs as * (n + 2) ^ (MExp.starDepthArgs as + 1)
    | [] => by simp [cbVArgs, MExp.szArgs]
    | a :: as => by
      simp only [cbVArgs, MExp.szArgs, MExp.starDepthArgs]
      have ha := Nat.le_trans (cbV_le n a)
        (Nat.mul_le_mul_left a.sz (pow_mono' n (Nat.add_le_add_right (Nat.le_max_left a.starDepth (MExp.starDepthArgs as)) 1)))
      have hs := Nat.le_trans (cbVArgs_le n as)
        (Nat.mul_le_mul_left (MExp.szArgs as) (pow_mono' n (Nat.add_le_add_right (Nat.le_max_right a.starDepth (MExp.starDepthArgs as)) 1)))
      rw [Nat.add_mul]
      omega
end

/-! ## One round and the whole procedure (call-by-value) -/

theorem length_of_mem_subStrs {x w : List Char} (h : w ∈ subStrs x) : w.length ≤ x.length := by
  simp only [subStrs, List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨p, hp, j, _, rfl⟩ := h
  unfold pre
  have := length_sfx_le x p
  simp only [List.length_take]; omega

/-- The cost of computing every relevant entry of the next table from `T`. -/
def roundCostV (s : Strategy) (g : MGrammar) (x : List Char) (T : Nat → List (List Char) → Val) : Nat :=
  ((List.range g.rules.length).map (fun i =>
    match ruleAtM g.rules i with
    | some r => ((words (subStrs x) r.arity).map (fun W =>
        ((List.range (x.length + 1)).map (fun p => costV g x s T W r.body p)).sum)).sum
    | none => 0)).sum

/-- The cost of the whole procedure: `iterBoundV` rounds, then the evaluation of `e`. -/
def totalCostV (s : Strategy) (g : MGrammar) (x : List Char) (e : MExp) : Nat :=
  ((List.range (iterBoundV g x)).map (fun m => roundCostV s g x (tblV g x s m))).sum +
    costV g x s (tblV g x s (iterBoundV g x)) [] e x.length

theorem roundCostV_le {s : Strategy} {g : MGrammar} {x : List Char} {T : Nat → List (List Char) → Val}
    (hT : OkTV x.length T) {B : Nat} (hB : ∀ r ∈ g.rules, cbV x.length r.body ≤ B) :
    roundCostV s g x T ≤ iterBoundV g x * B := by
  unfold roundCostV iterBoundV
  rw [sum_map_mul]
  refine sum_le_sum_of_le _ _ _ (fun i _ => ?_)
  cases hr : ruleAtM g.rules i with
  | none => simp
  | some r =>
    simp only
    have hb := hB r (ruleAtM_mem hr)
    have := sum_le_length_mul _ ((x.length + 1) * B) (words (subStrs x) r.arity) (fun W hW => by
      have hWl : ∀ w ∈ W, w.length ≤ x.length := fun w hw =>
        length_of_mem_subStrs (((mem_words _ _ _).1 hW).2 w hw)
      have := sum_le_length_mul (fun p => costV g x s T W r.body p) B (List.range (x.length + 1))
        (fun p hp => Nat.le_trans (costV_le hT hWl r.body p (by simp at hp; omega)) hb)
      simpa using this)
    rw [Nat.mul_assoc]; exact this

/-- **Total cost (call-by-value)**: at most `iterBoundV² · B + cbV n e`, where `B` bounds `cbV n` of every rule body. -/
theorem totalCostV_le {s : Strategy} {g : MGrammar} {x : List Char} {e : MExp} {B : Nat}
    (hB : ∀ r ∈ g.rules, cbV x.length r.body ≤ B) :
    totalCostV s g x e ≤ iterBoundV g x * (iterBoundV g x * B) + cbV x.length e := by
  unfold totalCostV
  have h₁ := sum_le_length_mul (fun m => roundCostV s g x (tblV g x s m)) (iterBoundV g x * B)
    (List.range (iterBoundV g x)) (fun m _ => roundCostV_le (tblV_ok g x s m) hB)
  have h₂ := costV_le (g := g) (s := s) (tblV_ok g x s (iterBoundV g x)) (E := []) (fun w hw => by cases hw) e x.length
    (Nat.le_refl _)
  simp only [List.length_range] at h₁
  omega

/-- **Polynomial time (call-by-value)**, all together: with arities `≤ K` and `cbV n` of the rule bodies `≤ B`,
the procedure costs at most `M² · B + cbV n e` where `M = |rules| · ((n+1)²)^K · (n+1)`. -/
theorem totalCostV_poly {s : Strategy} {g : MGrammar} {x : List Char} {e : MExp} {B K : Nat}
    (hK : ∀ r ∈ g.rules, r.arity ≤ K) (hB : ∀ r ∈ g.rules, cbV x.length r.body ≤ B) :
    totalCostV s g x e ≤
      (g.rules.length * (((x.length + 1) * (x.length + 1)) ^ K * (x.length + 1))) *
        ((g.rules.length * (((x.length + 1) * (x.length + 1)) ^ K * (x.length + 1))) * B) + cbV x.length e := by
  have h := totalCostV_le (s := s) (e := e) hB
  have hM := iterBoundV_le g x hK
  have := Nat.mul_le_mul hM (Nat.mul_le_mul_right B hM)
  omega

/-! ## Call-by-name -/

section CostN

variable (g : MGrammar) (x : List Char)

mutual
  def costN (T : Nat → List Val → Val) (E : List Val) : MExp → Nat → Nat
    | .lit w, _ => w.length + 1
    | .call i args, _ =>
      match ruleAtM g.rules i with
      | some r => if r.arity = args.length then 2 + costArgsN T E args else 1
      | none => 1
    | .seq a b, p =>
      1 + costN T E a p +
        match ev g x T E a p with
        | some (some j) => costN T E b j
        | _ => 0
    | .alt a b, p =>
      1 + costN T E a p +
        match ev g x T E a p with
        | some none => costN T E b p
        | _ => 0
    | .notP a, p => 1 + costN T E a p
    | .star a, p => 1 + costStar (fun q => ev g x T E a q) (fun q => costN T E a q) p
    | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .param _, _ | .dbg _, _ | .lam _ _, _ | .callParam _ _, _
    | .invoke _ _ _, _ => 1

  /-- Call-by-name computes each argument's value at every position. -/
  def costArgsN (T : Nat → List Val → Val) (E : List Val) : List MExp → Nat
    | [] => 0
    | a :: as => ((List.range (x.length + 1)).map (fun q => costN T E a q)).sum + costArgsN T E as
end

end CostN

mutual
  def cbN (n : Nat) : MExp → Nat
    | .lit w => w.length + 1
    | .call _ args => 2 + (n + 1) * cbNArgs n args
    | .seq a b => 1 + cbN n a + cbN n b
    | .alt a b => 1 + cbN n a + cbN n b
    | .notP a => 1 + cbN n a
    | .star a => 1 + (n + 1) * (cbN n a + 1)
    | .eps | .any | .chr _ | .range _ _ | .param _ | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => 1

  def cbNArgs (n : Nat) : List MExp → Nat
    | [] => 0
    | a :: as => cbN n a + cbNArgs n as
end

mutual
  theorem costN_le {g : MGrammar} {x : List Char} {T : Nat → List Val → Val} {E : List Val} (hT : OkT x.length T)
      (hE : ∀ w ∈ E, OkV x.length w) : ∀ (e : MExp) (p : Nat), p ≤ x.length → costN g x T E e p ≤ cbN x.length e
    | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .param _, _, _ | .dbg _, _, _ | .lam _ _, _, _
    | .callParam _ _, _, _ | .invoke _ _ _, _, _ => by simp only [costN, cbN]; omega
    | .lit w, _, _ => by simp only [costN, cbN]; omega
    | .call i args, _, _ => by
      simp only [costN, cbN]
      split
      · split
        · exact Nat.add_le_add_left (costArgsN_le hT hE args) 2
        · omega
      · omega
    | .seq a b, p, hp => by
      simp only [costN, cbN]
      have ha := costN_le (g := g) hT hE a p hp
      split
      · rename_i j h
        have := costN_le (g := g) hT hE b j (ev_ok hT hE a p hp j h); omega
      · omega
    | .alt a b, p, hp => by
      simp only [costN, cbN]
      have ha := costN_le (g := g) hT hE a p hp
      split
      · have := costN_le (g := g) hT hE b p hp; omega
      · omega
    | .notP a, p, hp => by
      simp only [costN, cbN]; have := costN_le (g := g) hT hE a p hp; omega
    | .star a, p, hp => by
      simp only [costN, cbN]
      have := costStar_le (f := fun q => ev g x T E a q) (c := fun q => costN g x T E a q) p
        (fun q hq => costN_le (g := g) hT hE a q (by omega))
      have : (p + 1) * (cbN x.length a + 1) ≤ (x.length + 1) * (cbN x.length a + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      omega

  theorem costArgsN_le {g : MGrammar} {x : List Char} {T : Nat → List Val → Val} {E : List Val}
      (hT : OkT x.length T) (hE : ∀ w ∈ E, OkV x.length w) :
      ∀ (as : List MExp), costArgsN g x T E as ≤ (x.length + 1) * cbNArgs x.length as
    | [] => by simp [costArgsN, cbNArgs]
    | a :: as => by
      simp only [costArgsN, cbNArgs]
      have h₁ := sum_le_length_mul (fun q => costN g x T E a q) (cbN x.length a) (List.range (x.length + 1))
        (fun q hq => costN_le (g := g) hT hE a q (by simp at hq; omega))
      have h₂ := costArgsN_le (g := g) hT hE as
      simp only [List.length_range] at h₁
      rw [Nat.mul_add]
      omega
end

mutual
  /-- Nesting depth of `star` and of actual arguments (call-by-name evaluates arguments at every position). -/
  def MExp.nameDepth : MExp → Nat
    | .call _ args => MExp.nameDepthArgs args + 1
    | .seq a b => max (MExp.nameDepth a) (MExp.nameDepth b)
    | .alt a b => max (MExp.nameDepth a) (MExp.nameDepth b)
    | .notP a => MExp.nameDepth a
    | .star a => MExp.nameDepth a + 1
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => 0

  def MExp.nameDepthArgs : List MExp → Nat
    | [] => 0
    | a :: as => max (MExp.nameDepth a) (MExp.nameDepthArgs as)
end

mutual
  /-- **One call-by-name evaluation is polynomial**: `cbN n e ≤ size e · (n+2)^(nameDepth e + 1)`. -/
  theorem cbN_le (n : Nat) : ∀ e : MExp, cbN n e ≤ e.sz * (n + 2) ^ (e.nameDepth + 1)
    | .eps | .any | .chr _ | .range _ _ | .param _ | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => by
      simp only [cbN, MExp.sz, MExp.nameDepth, Nat.one_mul]; exact pow_pos' n _
    | .lit w => by
      simp only [cbN, MExp.sz, MExp.nameDepth, Nat.zero_add, Nat.pow_one]
      exact Nat.le_mul_of_pos_right _ (by omega)
    | .call _ args => by
      simp only [cbN, MExp.sz, MExp.nameDepth]
      have h := cbNArgs_le n args
      generalize hQ : (n + 2) ^ (MExp.nameDepthArgs args + 1) = Q at h
      have hQ1 : 1 ≤ Q := hQ ▸ pow_pos' n _
      have hP : (n + 2) ^ (MExp.nameDepthArgs args + 1 + 1) = Q * (n + 2) := by rw [← hQ, Nat.pow_succ]
      rw [hP]
      have h1 : (n + 1) * cbNArgs n args ≤ (n + 1) * (MExp.szArgs args * Q) := Nat.mul_le_mul_left _ h
      have h3 : (n + 1) * (MExp.szArgs args * Q) ≤ MExp.szArgs args * Q * (n + 2) := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
      have h4 : n + 2 ≤ Q * (n + 2) := Nat.le_mul_of_pos_left _ (by omega)
      have h5 : (2 + MExp.szArgs args) * (Q * (n + 2)) = 2 * (Q * (n + 2)) + MExp.szArgs args * Q * (n + 2) := by
        rw [Nat.add_mul, Nat.mul_assoc]
      omega
    | .seq a b => by
      simp only [cbN, MExp.sz, MExp.nameDepth]
      have ha' := Nat.le_trans (cbN_le n a) (Nat.mul_le_mul_left a.sz (pow_mono' n (Nat.add_le_add_right (Nat.le_max_left a.nameDepth b.nameDepth) 1)))
      have hb' := Nat.le_trans (cbN_le n b) (Nat.mul_le_mul_left b.sz (pow_mono' n (Nat.add_le_add_right (Nat.le_max_right a.nameDepth b.nameDepth) 1)))
      have h1 := pow_pos' n (max a.nameDepth b.nameDepth + 1)
      rw [Nat.add_mul, Nat.add_mul]
      omega
    | .alt a b => by
      simp only [cbN, MExp.sz, MExp.nameDepth]
      have ha' := Nat.le_trans (cbN_le n a) (Nat.mul_le_mul_left a.sz (pow_mono' n (Nat.add_le_add_right (Nat.le_max_left a.nameDepth b.nameDepth) 1)))
      have hb' := Nat.le_trans (cbN_le n b) (Nat.mul_le_mul_left b.sz (pow_mono' n (Nat.add_le_add_right (Nat.le_max_right a.nameDepth b.nameDepth) 1)))
      have h1 := pow_pos' n (max a.nameDepth b.nameDepth + 1)
      rw [Nat.add_mul, Nat.add_mul]
      omega
    | .notP a => by
      simp only [cbN, MExp.sz, MExp.nameDepth]
      have ha := cbN_le n a
      have h1 := pow_pos' n (a.nameDepth + 1)
      rw [Nat.add_mul]
      omega
    | .star a => by
      simp only [cbN, MExp.sz, MExp.nameDepth]
      have ha := cbN_le n a
      generalize hQ : (n + 2) ^ (a.nameDepth + 1) = Q at ha
      have hQ1 : 1 ≤ Q := hQ ▸ pow_pos' n _
      have hP : (n + 2) ^ (a.nameDepth + 1 + 1) = Q * (n + 2) := by rw [← hQ, Nat.pow_succ]
      rw [hP]
      have h1 : (n + 1) * (cbN n a + 1) ≤ (n + 1) * (a.sz * Q + 1) := Nat.mul_le_mul_left _ (by omega)
      have h2 : (n + 1) * (a.sz * Q + 1) = (n + 1) * (a.sz * Q) + (n + 1) := by rw [Nat.mul_add, Nat.mul_one]
      have h3 : (n + 1) * (a.sz * Q) ≤ a.sz * Q * (n + 2) := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
      have h4 : n + 2 ≤ Q * (n + 2) := Nat.le_mul_of_pos_left _ (by omega)
      have h5 : (1 + a.sz) * (Q * (n + 2)) = Q * (n + 2) + a.sz * Q * (n + 2) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
      omega

  theorem cbNArgs_le (n : Nat) : ∀ as : List MExp, cbNArgs n as ≤ MExp.szArgs as * (n + 2) ^ (MExp.nameDepthArgs as + 1)
    | [] => by simp [cbNArgs, MExp.szArgs]
    | a :: as => by
      simp only [cbNArgs, MExp.szArgs, MExp.nameDepthArgs]
      have ha := Nat.le_trans (cbN_le n a)
        (Nat.mul_le_mul_left a.sz (pow_mono' n (Nat.add_le_add_right (Nat.le_max_left a.nameDepth (MExp.nameDepthArgs as)) 1)))
      have hs := Nat.le_trans (cbNArgs_le n as)
        (Nat.mul_le_mul_left (MExp.szArgs as) (pow_mono' n (Nat.add_le_add_right (Nat.le_max_right a.nameDepth (MExp.nameDepthArgs as)) 1)))
      rw [Nat.add_mul]
      omega
end

def roundCostN (g : MGrammar) (x : List Char) (T : Nat → List Val → Val) : Nat :=
  ((List.range g.rules.length).map (fun i =>
    match ruleAtM g.rules i with
    | some r => ((words (allVals x.length) r.arity).map (fun W =>
        ((List.range (x.length + 1)).map (fun p => costN g x T W r.body p)).sum)).sum
    | none => 0)).sum

def totalCostN (g : MGrammar) (x : List Char) (e : MExp) : Nat :=
  ((List.range (iterBound g x)).map (fun m => roundCostN g x (tbl g x m))).sum +
    costN g x (tbl g x (iterBound g x)) [] e x.length

theorem roundCostN_le {g : MGrammar} {x : List Char} {T : Nat → List Val → Val} (hT : OkT x.length T) {B : Nat}
    (hB : ∀ r ∈ g.rules, cbN x.length r.body ≤ B) : roundCostN g x T ≤ iterBound g x * B := by
  unfold roundCostN iterBound
  rw [sum_map_mul]
  refine sum_le_sum_of_le _ _ _ (fun i _ => ?_)
  cases hr : ruleAtM g.rules i with
  | none => simp
  | some r =>
    simp only
    have hb := hB r (ruleAtM_mem hr)
    have := sum_le_length_mul _ ((x.length + 1) * B) (words (allVals x.length) r.arity) (fun W hW => by
      have hWok : ∀ w ∈ W, OkV x.length w := fun w hw =>
        okV_of_mem_allVals (((mem_words _ _ _).1 hW).2 w hw)
      have := sum_le_length_mul (fun p => costN g x T W r.body p) B (List.range (x.length + 1))
        (fun p hp => Nat.le_trans (costN_le hT hWok r.body p (by simp at hp; omega)) hb)
      simpa using this)
    rw [Nat.mul_assoc]; exact this

/-- **Total cost (call-by-name)**: at most `iterBound² · B + cbN n e` — exponential in `n` through `iterBound`
(`iterBound_le`), with a polynomial per-entry factor (`cbN_le`). -/
theorem totalCostN_le {g : MGrammar} {x : List Char} {e : MExp} {B : Nat}
    (hB : ∀ r ∈ g.rules, cbN x.length r.body ≤ B) :
    totalCostN g x e ≤ iterBound g x * (iterBound g x * B) + cbN x.length e := by
  unfold totalCostN
  have h₁ := sum_le_length_mul (fun m => roundCostN g x (tbl g x m)) (iterBound g x * B)
    (List.range (iterBound g x)) (fun m _ => roundCostN_le (tbl_ok g x m) hB)
  have h₂ := costN_le (g := g) (tbl_ok g x (iterBound g x)) (nil_ok _) e x.length (Nat.le_refl _)
  simp only [List.length_range] at h₁
  omega

/-- **Exponential time (call-by-name)**, all together: with arities `≤ K` and `cbN n` of the rule bodies `≤ B`, the
procedure costs at most `M² · B + cbN n e` where `M = |rules| · (n+3)^((n+1)·K) · (n+1)`. -/
theorem totalCostN_exp {g : MGrammar} {x : List Char} {e : MExp} {B K : Nat}
    (hK : ∀ r ∈ g.rules, r.arity ≤ K) (hB : ∀ r ∈ g.rules, cbN x.length r.body ≤ B) :
    totalCostN g x e ≤
      (g.rules.length * ((x.length + 3) ^ ((x.length + 1) * K) * (x.length + 1))) *
        ((g.rules.length * ((x.length + 3) ^ ((x.length + 1) * K) * (x.length + 1))) * B) + cbN x.length e := by
  have h := totalCostN_le (e := e) hB
  have hM := iterBound_le g x hK
  have := Nat.mul_le_mul hM (Nat.mul_le_mul_right B hM)
  omega

end Shallot.MacroPeg
