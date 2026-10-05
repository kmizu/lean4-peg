import Complexity.CfgEnc

namespace Complexity

theorem ev_var (ρ : Name → Bool) (x : Name) : (Formula.var x).eval ρ = ρ x := rfl
theorem ev_and (ρ : Name → Bool) (a b : Formula) : (Formula.and a b).eval ρ = (a.eval ρ && b.eval ρ) := rfl
theorem ev_or (ρ : Name → Bool) (a b : Formula) : (Formula.or a b).eval ρ = (a.eval ρ || b.eval ρ) := rfl
theorem ev_not (ρ : Name → Bool) (a : Formula) : (Formula.not a).eval ρ = !a.eval ρ := rfl

theorem eval_bigOr_map {α : Type} (ρ : Name → Bool) (L : List α) (f : α → Formula) :
    (bigOr (L.map f)).eval ρ = true ↔ ∃ x ∈ L, (f x).eval ρ = true := by
  rw [eval_bigOr]
  constructor
  · rintro ⟨a, ha, h⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    exact ⟨x, hx, h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨_, List.mem_map.2 ⟨x, hx, rfl⟩, h⟩

theorem readWords_ofFn (na : Nat) : ∀ (n : Nat) (r : Fin n → Nat), (∀ i, r i < na) → List.ofFn r ∈ readWords n na
  | 0, r, _ => by simp [readWords]
  | n + 1, r, h => by
    rw [List.ofFn_succ]
    simp only [readWords, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨r 0, h 0, List.ofFn fun i => r i.succ, readWords_ofFn na n _ (fun i => h _), rfl⟩

theorem readWords_prop (na : Nat) :
    ∀ (n : Nat) (w : List Nat), w ∈ readWords n na → w.length = n ∧ ∀ x ∈ w, x < na
  | 0, w, h => by
    simp [readWords] at h; subst h; simp
  | n + 1, w, h => by
    simp only [readWords, List.mem_flatMap, List.mem_map, List.mem_range] at h
    obtain ⟨s, hs, w', hw', rfl⟩ := h
    obtain ⟨h1, h2⟩ := readWords_prop na n w' hw'
    refine ⟨by simp [h1], ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hs
    · exact h2 x hx

theorem mem_allReads {k na : Nat} (r : Fin k → Nat) (h : ∀ i, r i < na) : r ∈ allReads k na := by
  unfold allReads
  rw [List.mem_map]
  refine ⟨List.ofFn r, readWords_ofFn na k r h, ?_⟩
  funext i
  simp

theorem allReads_lt {k na : Nat} {r : Fin k → Nat} (h : r ∈ allReads k na) : ∀ i, r i < na := by
  unfold allReads at h
  rw [List.mem_map] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨h1, h2⟩ := readWords_prop na k w hw
  intro i
  have hi : i.val < w.length := by omega
  show w.getD i.val 0 < na
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact h2 _ (List.getElem_mem hi)

theorem mem_combos {k : Nat} (M : TM k) (p : Nat × (Fin k → Nat)) :
    p ∈ combos M ↔ p.1 < M.nq ∧ ∀ i, p.2 i < M.na := by
  constructor
  · intro h
    unfold combos at h
    simp only [List.mem_flatMap, List.mem_range, List.mem_map] at h
    obtain ⟨q, hq, r, hr, rfl⟩ := h
    exact ⟨hq, allReads_lt hr⟩
  · rintro ⟨h1, h2⟩
    unfold combos
    simp only [List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨p.1, h1, p.2, mem_allReads _ h2, rfl⟩

theorem halted_iff {k : Nat} (c : Cfg k) : c.halted ↔ c.state ≤ 1 := by
  unfold Cfg.halted; omega

theorem step_state {k : Nat} (M : TM k) (c : Cfg k) : (M.step c).state = nextState M c.state c.read := by
  by_cases hq : c.state ≤ 1
  · have hh : c.halted := (halted_iff c).2 hq
    simp [TM.step, hh, nextState, hq]
  · have hh : ¬ c.halted := fun h => hq ((halted_iff c).1 h)
    simp [TM.step, hh, nextState, hq]

theorem step_pos {k : Nat} (M : TM k) (c : Cfg k) (i : Fin k) :
    (M.step c).pos i = (moveOf M c.state c.read i).apply (c.pos i) := by
  by_cases hq : c.state ≤ 1
  · have hh : c.halted := (halted_iff c).2 hq
    simp [TM.step, hh, moveOf, hq, Move.apply]
  · have hh : ¬ c.halted := fun h => hq ((halted_iff c).1 h)
    simp [TM.step, hh, moveOf, hq]

theorem step_cells {k : Nat} (M : TM k) (c : Cfg k) (i : Fin k) (j : Nat) :
    (M.step c).cells i j = if j = c.pos i then writeSym M c.state c.read i else c.cells i j := by
  by_cases hq : c.state ≤ 1
  · have hh : c.halted := (halted_iff c).2 hq
    by_cases hj : j = c.pos i
    · subst hj; simp [TM.step, hh, writeSym, hq, Cfg.read]
    · simp [TM.step, hh, writeSym, hq, hj]
  · have hh : ¬ c.halted := fun h => hq ((halted_iff c).1 h)
    simp [TM.step, hh, writeSym, hq]

theorem encodes_iff {k : Nat} (M : TM k) (S : Nat) (ρ : Name → Bool) (b : Name) (d : Cfg k) :
    Encodes M S ρ b d ↔
      (∀ q, q < M.nq → ρ (b ++ [0, q]) = decide (d.state = q)) ∧
      (∀ i : Fin k, ∀ j, j < S → ρ (b ++ [1, i.val, j]) = decide (d.pos i = j)) ∧
      (∀ i : Fin k, ∀ j, j < S → ∀ s, s < M.na → ρ (b ++ [2, i.val, j, s]) = decide (d.cells i j = s)) := by
  constructor
  · intro h
    refine ⟨fun q hq => ?_, fun i j hj => ?_, fun i j hj s hs => ?_⟩
    · have := h [0, q] (by simp [blockSuf, sSuf, hq]); simpa [bit] using this
    · have := h [1, i.val, j] (by
        simp only [blockSuf, List.mem_append, hSuf, List.mem_flatMap, List.mem_range, List.mem_map]
        exact Or.inl (Or.inr ⟨i.val, i.isLt, j, hj, rfl⟩))
      simpa [bit] using this
    · have := h [2, i.val, j, s] (by
        simp only [blockSuf, List.mem_append, cSuf, List.mem_flatMap, List.mem_range, List.mem_map]
        exact Or.inr ⟨i.val, i.isLt, j, hj, s, hs, rfl⟩)
      simpa [bit] using this
  · rintro ⟨h1, h2, h3⟩ v hv
    simp only [blockSuf, List.mem_append, sSuf, hSuf, cSuf, List.mem_flatMap, List.mem_range, List.mem_map] at hv
    rcases hv with (⟨q, hq, rfl⟩ | ⟨i, hi, j, hj, rfl⟩) | ⟨i, hi, j, hj, s, hs, rfl⟩
    · simpa [bit] using h1 q hq
    · simpa [bit, hi] using h2 ⟨i, hi⟩ j hj
    · simpa [bit, hi] using h3 ⟨i, hi⟩ j hj s hs

theorem readF_iff {k : Nat} (M : TM k) (S : Nat) {ρ : Name → Bool} {b : Name} {c : Cfg k}
    (hc : Good M S c) (he : Encodes M S ρ b c) (i : Fin k) (s : Nat) (hs : s < M.na) :
    (readF S b i s).eval ρ = true ↔ c.read i = s := by
  obtain ⟨_, h2, h3⟩ := (encodes_iff M S ρ b c).1 he
  have hpos := (hc.2 i).1
  unfold readF
  rw [eval_bigOr_map]
  simp only [List.mem_range, ev_var, ev_and, Bool.and_eq_true]
  constructor
  · rintro ⟨j, hj, ha, hb⟩
    rw [h2 i j hj] at ha
    rw [h3 i j hj s hs] at hb
    simp at ha hb
    subst ha
    exact hb
  · intro h
    refine ⟨c.pos i, hpos, ?_, ?_⟩
    · rw [h2 i _ hpos]; simp
    · rw [h3 i _ hpos s hs]; simpa [Cfg.read] using h

theorem combF_iff {k : Nat} (M : TM k) (S : Nat) {ρ : Name → Bool} {b : Name} {c : Cfg k}
    (hc : Good M S c) (he : Encodes M S ρ b c) (q : Nat) (hq : q < M.nq) (r : Fin k → Nat)
    (hr : ∀ i, r i < M.na) :
    (combF S b q r).eval ρ = true ↔ (c.state = q ∧ c.read = r) := by
  obtain ⟨h1, _, _⟩ := (encodes_iff M S ρ b c).1 he
  unfold combF
  simp only [ev_var, ev_and, Bool.and_eq_true, eval_bigAnd, List.mem_map, List.mem_finRange, true_and,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff]
  rw [h1 q hq]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨ha, funext fun i => ?_⟩
    exact (readF_iff M S hc he i (r i) (hr i)).1 (hb i)
  · rintro ⟨ha, hb⟩
    exact ⟨ha, fun i => (readF_iff M S hc he i (r i) (hr i)).2 (congrFun hb i)⟩

theorem read_lt {k : Nat} {M : TM k} {S : Nat} {c : Cfg k} (hc : Good M S c) : ∀ i, c.read i < M.na := fun i =>
  ((hc.2 i).2 (c.pos i)).1 (hc.2 i).1

theorem or_combF {k : Nat} (M : TM k) (S : Nat) {ρ : Name → Bool} {b : Name} {c : Cfg k}
    (hc : Good M S c) (he : Encodes M S ρ b c) (f : Nat × (Fin k → Nat) → Bool) :
    (bigOr (((combos M).filter f).map (fun p => combF S b p.1 p.2))).eval ρ = f (c.state, c.read) := by
  have hcr := read_lt hc
  have hmem : (c.state, c.read) ∈ combos M := (mem_combos M _).2 ⟨hc.1, hcr⟩
  rw [Bool.eq_iff_iff, eval_bigOr_map]
  simp only [List.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, hf⟩, h⟩
    obtain ⟨h1, h2⟩ := (mem_combos M p).1 hp
    obtain ⟨e1, e2⟩ := (combF_iff M S hc he p.1 h1 p.2 h2).1 h
    have : p = (c.state, c.read) := Prod.ext e1.symm e2.symm
    rw [this] at hf
    exact hf
  · intro hf
    exact ⟨(c.state, c.read), ⟨hmem, hf⟩, (combF_iff M S hc he _ hc.1 _ hcr).2 ⟨rfl, rfl⟩⟩

theorem or_combF' {k : Nat} (M : TM k) (S : Nat) {ρ : Name → Bool} {b : Name} {c : Cfg k}
    (hc : Good M S c) (he : Encodes M S ρ b c) (G : Nat × (Fin k → Nat) → Formula) :
    (bigOr ((combos M).map (fun p => Formula.and (combF S b p.1 p.2) (G p)))).eval ρ
      = (G (c.state, c.read)).eval ρ := by
  have hcr := read_lt hc
  have hmem : (c.state, c.read) ∈ combos M := (mem_combos M _).2 ⟨hc.1, hcr⟩
  rw [Bool.eq_iff_iff, eval_bigOr_map]
  simp only [ev_var, ev_and, Bool.and_eq_true]
  constructor
  · rintro ⟨p, hp, h, hg⟩
    obtain ⟨h1, h2⟩ := (mem_combos M p).1 hp
    obtain ⟨e1, e2⟩ := (combF_iff M S hc he p.1 h1 p.2 h2).1 h
    have : p = (c.state, c.read) := Prod.ext e1.symm e2.symm
    rw [this] at hg
    exact hg
  · intro hg
    exact ⟨(c.state, c.read), hmem, (combF_iff M S hc he _ hc.1 _ hcr).2 ⟨rfl, rfl⟩, hg⟩

theorem stepF_iff {k : Nat} (M : TM k) (S : Nat) {ρ : Name → Bool} {b b' : Name} {c : Cfg k}
    (hc : Good M S c) (he : Encodes M S ρ b c) :
    (stepF M S b b').eval ρ = true ↔ Encodes M S ρ b' (M.step c) := by
  obtain ⟨_, h2, h3⟩ := (encodes_iff M S ρ b c).1 he
  have A : ∀ q', (Formula.iff (.var (b' ++ [0, q']))
      (bigOr (((combos M).filter (fun p => nextState M p.1 p.2 = q')).map
        (fun p => combF S b p.1 p.2)))).eval ρ = true ↔ ρ (b' ++ [0, q']) = decide ((M.step c).state = q') := by
    intro q'
    rw [eval_iff, or_combF M S hc he, step_state]
    simp [ev_var, ev_and, ev_or, ev_not]
  have B : ∀ (i : Fin k) j, j < S → ((headBitF M S b b' i j).eval ρ = true ↔
      ρ (b' ++ [1, i.val, j]) = decide ((M.step c).pos i = j)) := by
    intro i j hj
    have hpos := (hc.2 i).1
    unfold headBitF
    rw [eval_iff, or_combF' M S hc he (fun p => bigOr (((List.range S).filter
      (fun j' => (moveOf M p.1 p.2 i).apply j' = j)).map (fun j' => .var (b ++ [1, i.val, j'])))), step_pos]
    have H : (bigOr (((List.range S).filter
        (fun j' => (moveOf M c.state c.read i).apply j' = j)).map (fun j' => .var (b ++ [1, i.val, j'])))).eval ρ
        = decide ((moveOf M c.state c.read i).apply (c.pos i) = j) := by
      rw [Bool.eq_iff_iff, eval_bigOr_map]
      simp only [List.mem_filter, List.mem_range, ev_var, decide_eq_true_eq]
      constructor
      · rintro ⟨j', ⟨hj', hm⟩, hv⟩
        rw [h2 i j' hj'] at hv
        simp at hv hm
        rw [← hv] at hm; exact hm
      · intro hm
        exact ⟨c.pos i, ⟨hpos, by simpa using hm⟩, by rw [h2 i _ hpos]; simp⟩
    rw [H]
    simp [ev_var, ev_and, ev_or, ev_not]
  have C : ∀ (i : Fin k) j, j < S → ∀ s, s < M.na → ((cellBitF M S b b' i j s).eval ρ = true ↔
      ρ (b' ++ [2, i.val, j, s]) = decide ((M.step c).cells i j = s)) := by
    intro i j hj s hs
    unfold cellBitF
    rw [eval_iff]
    simp only [ev_var, ev_and, ev_or, ev_not]
    rw [or_combF M S hc he (fun p => decide (writeSym M p.1 p.2 i = s)), step_cells]
    simp only [h2 i j hj, h3 i j hj s hs, beq_iff_eq]
    by_cases h : c.pos i = j
    · subst h; simp
    · have h' : ¬ j = c.pos i := fun e => h e.symm
      simp [h, h']
  rw [encodes_iff, stepF, eval_bigAnd]
  simp only [List.mem_append, or_imp, forall_and, stateBitsF, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_finRange, true_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff]
  constructor
  · rintro ⟨⟨hA, hB⟩, hC⟩
    exact ⟨fun q hq => (A q).1 (hA _ q hq rfl), fun i j hj => (B i j hj).1 (hB _ i j hj rfl),
      fun i j hj s hs => (C i j hj s hs).1 (hC _ i j hj s hs rfl)⟩
  · rintro ⟨h1, h1', h1''⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro _ q hq rfl; exact (A q).2 (h1 q hq)
    · rintro _ i j hj rfl; exact (B i j hj).2 (h1' i j hj)
    · rintro _ i j hj s hs rfl; exact (C i j hj s hs).2 (h1'' i j hj s hs)

end Complexity
