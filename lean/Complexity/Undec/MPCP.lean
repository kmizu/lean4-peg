import Complexity.Undec.Defs

/-!
# From the modified correspondence problem to the plain one

The textbook star construction (Sipser, Thm 5.15). With fresh symbols `⋆ = n` and `◇ = n + 1`, a top `u` becomes
`⋆u₁⋆u₂…⋆uₖ` (`mpStar`) and a bottom `v` becomes `v₁⋆v₂⋆…vₗ⋆` (`mpRStar`). The first card becomes `(⋆u, ⋆v⋆)`,
every card of `P` becomes `(⋆u, v⋆)`, and the card `(⋆◇, ◇)` closes a match (`mpcpToPCP`).

For the way back, a match of the new cards is cut at its first `◇`: before it, the tops followed by `⋆` equal the
bottoms. Erasing the fresh symbols reads back a match of the original cards, and counting lengths shows the first
card occurs exactly once, at the front.
-/

namespace Complexity.Undec

/-- `⋆u₁⋆u₂…⋆uₖ`. -/
def mpStar (n : Nat) (u : Word) : Word := u.flatMap fun a => [n, a]

/-- `v₁⋆v₂⋆…vₗ⋆`. -/
def mpRStar (n : Nat) (v : Word) : Word := v.flatMap fun a => [a, n]

/-- **The star construction** with `⋆ = n` and `◇ = n + 1`. -/
def mpcpToPCP (d : Card) (P : List Card) (n : Nat) : List Card :=
  (mpStar n d.1, n :: mpRStar n d.2) :: (P.map fun c => (mpStar n c.1, mpRStar n c.2)) ++ [([n, n + 1], [n + 1])]

/-! ## Words -/

theorem mpStar_nil (n : Nat) : mpStar n [] = [] := rfl

theorem mpStar_cons (n a : Nat) (u : Word) : mpStar n (a :: u) = n :: a :: mpStar n u := by simp [mpStar]

theorem mpRStar_cons (n a : Nat) (v : Word) : mpRStar n (a :: v) = a :: n :: mpRStar n v := by simp [mpRStar]

theorem mpStar_append (n : Nat) (u v : Word) : mpStar n (u ++ v) = mpStar n u ++ mpStar n v := by
  simp [mpStar, List.flatMap_append]

theorem mpRStar_append (n : Nat) (u v : Word) : mpRStar n (u ++ v) = mpRStar n u ++ mpRStar n v := by
  simp [mpRStar, List.flatMap_append]

/-- `⋆u₁…⋆uₖ⋆ = ⋆u₁⋆…uₖ⋆`. -/
theorem mpStar_snoc (n : Nat) (w : Word) : mpStar n w ++ [n] = n :: mpRStar n w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [mpStar_cons, mpRStar_cons, ih]

theorem mpStar_length (n : Nat) (u : Word) : (mpStar n u).length = 2 * u.length := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [mpStar_cons, ih]; omega

theorem mpRStar_length (n : Nat) (v : Word) : (mpRStar n v).length = 2 * v.length := by
  induction v with
  | nil => rfl
  | cons a v ih => simp [mpRStar_cons, ih]; omega

theorem mem_mpStar {n a : Nat} {u : Word} (h : a ∈ mpStar n u) : a = n ∨ a ∈ u := by
  induction u with
  | nil => simp [mpStar_nil] at h
  | cons b u ih =>
    simp only [mpStar_cons, List.mem_cons] at h
    rcases h with h | h | h
    · exact .inl h
    · exact .inr (by simp [h])
    · rcases ih h with h' | h'
      · exact .inl h'
      · exact .inr (by simp [h'])

theorem mem_mpRStar {n a : Nat} {v : Word} (h : a ∈ mpRStar n v) : a = n ∨ a ∈ v := by
  induction v with
  | nil => simp [mpRStar] at h
  | cons b v ih =>
    simp only [mpRStar_cons, List.mem_cons] at h
    rcases h with h | h | h
    · exact .inr (by simp [h])
    · exact .inl h
    · rcases ih h with h' | h'
      · exact .inl h'
      · exact .inr (by simp [h'])

/-- Erasing the fresh symbols: keep those below `n`. -/
def mpErase (n : Nat) (w : Word) : Word := w.filter fun a => decide (a < n)

theorem mpErase_append (n : Nat) (u v : Word) : mpErase n (u ++ v) = mpErase n u ++ mpErase n v := by
  simp [mpErase, List.filter_append]

theorem mpErase_star {n : Nat} {u : Word} (hu : ∀ a ∈ u, a < n) : mpErase n (mpStar n u) = u := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    have ha : a < n := hu a (by simp)
    have ih' := ih (fun b hb => hu b (by simp [hb]))
    simp only [mpErase] at ih'
    simp [mpErase, mpStar_cons, ha, ih']

theorem mpErase_rstar {n : Nat} {v : Word} (hv : ∀ a ∈ v, a < n) : mpErase n (mpRStar n v) = v := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    have ha : a < n := hv a (by simp)
    have ih' := ih (fun b hb => hv b (by simp [hb]))
    simp only [mpErase] at ih'
    simp [mpErase, mpRStar_cons, ha, ih']

theorem mpErase_self (n : Nat) : mpErase n [n] = [] := by simp [mpErase]

/-- `x` occurs first right after `a` and right after `b`: then `a = b`. -/
theorem first_occ {x : Nat} : ∀ {a b r s : Word}, x ∉ a → x ∉ b → a ++ x :: r = b ++ x :: s → a = b ∧ r = s
  | [], [], r, s, _, _, h => by simpa using h
  | [], c :: b, r, s, _, hb, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hb
  | c :: a, [], r, s, ha, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) ha
  | c :: a, e :: b, r, s, ha, hb, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have := first_occ (fun hx => ha (List.mem_cons_of_mem _ hx)) (fun hx => hb (List.mem_cons_of_mem _ hx)) h
    exact ⟨by rw [this.1], this.2⟩

/-! ## Cards -/

theorem tops_nil : tops [] = [] := rfl

theorem bots_nil : bots [] = [] := rfl

theorem tops_cons (c : Card) (A : List Card) : tops (c :: A) = c.1 ++ tops A := by simp [tops]

theorem bots_cons (c : Card) (A : List Card) : bots (c :: A) = c.2 ++ bots A := by simp [bots]

theorem tops_append (A B : List Card) : tops (A ++ B) = tops A ++ tops B := by simp [tops]

theorem bots_append (A B : List Card) : bots (A ++ B) = bots A ++ bots B := by simp [bots]

/-- A converted card other than the closing one: the first card (flag `true`) or a card of `P`. -/
def mpG (n : Nat) (p : Bool × Card) : Card := (mpStar n p.2.1, (if p.1 then [n] else []) ++ mpRStar n p.2.2)

/-- The closing card `(⋆◇, ◇)`. -/
def mpE (n : Nat) : Card := ([n, n + 1], [n + 1])

/-- A flagged card comes from the first card (flag `true`) or from `P` (flag `false`). -/
def MpOk (d : Card) (P : List Card) (p : Bool × Card) : Prop := (p.1 = true ∧ p.2 = d) ∨ (p.1 = false ∧ p.2 ∈ P)

theorem MpOk.mem {d : Card} {P : List Card} {p : Bool × Card} (h : MpOk d P p) : p.2 ∈ d :: P := by
  rcases h with ⟨_, h⟩ | ⟨_, h⟩
  · simp [h]
  · exact List.mem_cons_of_mem _ h

/-- The cards of `mpcpToPCP` are the closing card and the converted cards. -/
theorem mem_mpcpToPCP {d : Card} {P : List Card} {n : Nat} {q : Card} (h : q ∈ mpcpToPCP d P n) :
    q = mpE n ∨ ∃ p, MpOk d P p ∧ q = mpG n p := by
  simp only [mpcpToPCP, List.cons_append, List.mem_cons, List.mem_append, List.mem_map] at h
  rcases h with rfl | ⟨c, hc, rfl⟩ | h
  · exact .inr ⟨(true, d), .inl ⟨rfl, rfl⟩, by simp [mpG]⟩
  · exact .inr ⟨(false, c), .inr ⟨rfl, hc⟩, by simp [mpG]⟩
  · simp at h; exact .inl (by rw [h]; rfl)

theorem first_mem_mpcpToPCP (d : Card) (P : List Card) (n : Nat) : mpG n (true, d) ∈ mpcpToPCP d P n := by
  simp [mpcpToPCP, mpG]

theorem P_mem_mpcpToPCP {d c : Card} {P : List Card} (n : Nat) (hc : c ∈ P) :
    mpG n (false, c) ∈ mpcpToPCP d P n := by
  simp only [mpcpToPCP, List.cons_append, List.mem_cons, List.mem_append, List.mem_map]
  exact .inr (.inl ⟨c, hc, by simp [mpG]⟩)

theorem E_mem_mpcpToPCP (d : Card) (P : List Card) (n : Nat) : mpE n ∈ mpcpToPCP d P n := by
  simp [mpcpToPCP, mpE]

/-- The tops of converted cards are the starred tops. -/
theorem tops_mpG (n : Nat) (L : List (Bool × Card)) : tops (L.map (mpG n)) = mpStar n (tops (L.map Prod.snd)) := by
  induction L with
  | nil => rfl
  | cons p L ih => rw [List.map_cons, List.map_cons, tops_cons, tops_cons, ih, mpStar_append]; rfl

/-- The tops of cards of `P` converted. -/
theorem tops_mpG_false (n : Nat) (A : List Card) :
    tops (A.map fun c => mpG n (false, c)) = mpStar n (tops A) := by
  induction A with
  | nil => rfl
  | cons c A ih => rw [List.map_cons, tops_cons, tops_cons, ih, mpStar_append]; rfl

/-- The bottoms of cards of `P` converted. -/
theorem bots_mpG_false (n : Nat) (A : List Card) :
    bots (A.map fun c => mpG n (false, c)) = mpRStar n (bots A) := by
  induction A with
  | nil => rfl
  | cons c A ih => rw [List.map_cons, bots_cons, bots_cons, ih, mpRStar_append]; simp [mpG]

/-- The number of first cards. -/
def nF : List (Bool × Card) → Nat
  | [] => 0
  | p :: L => (if p.1 then 1 else 0) + nF L

theorem nF_zero : ∀ {L : List (Bool × Card)}, nF L = 0 → ∀ p ∈ L, p.1 = false
  | [], _, _, hp => by simp at hp
  | q :: L, h, p, hp => by
    simp only [nF] at h
    rcases List.mem_cons.1 hp with rfl | hp
    · cases hq : p.1 <;> simp_all
    · exact nF_zero (by omega) p hp

theorem tops_mpG_length (n : Nat) (L : List (Bool × Card)) :
    (tops (L.map (mpG n))).length = 2 * (tops (L.map Prod.snd)).length := by
  rw [tops_mpG, mpStar_length]

/-- Each first card adds one `⋆` to the bottoms. -/
theorem bots_mpG_length (n : Nat) (L : List (Bool × Card)) :
    (bots (L.map (mpG n))).length = 2 * (bots (L.map Prod.snd)).length + nF L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [List.map_cons, List.map_cons, bots_cons, bots_cons, List.length_append, List.length_append, ih]
    simp only [mpG, nF, List.length_append, mpRStar_length]
    cases p.1 <;> simp <;> omega

/-- Erasing the fresh symbols from converted tops. -/
theorem mpErase_tops {d : Card} {P : List Card} {n : Nat} (hb : CardsBelow n (d :: P)) :
    ∀ {L : List (Bool × Card)}, (∀ p ∈ L, MpOk d P p) → mpErase n (tops (L.map (mpG n))) = tops (L.map Prod.snd)
  | [], _ => rfl
  | p :: L, hL => by
    rw [List.map_cons, List.map_cons, tops_cons, tops_cons, mpErase_append,
      mpErase_tops hb (fun q hq => hL q (List.mem_cons_of_mem _ hq))]
    simp only [mpG]
    rw [mpErase_star (hb _ (hL p List.mem_cons_self).mem).1]

/-- Erasing the fresh symbols from converted bottoms. -/
theorem mpErase_bots {d : Card} {P : List Card} {n : Nat} (hb : CardsBelow n (d :: P)) :
    ∀ {L : List (Bool × Card)}, (∀ p ∈ L, MpOk d P p) → mpErase n (bots (L.map (mpG n))) = bots (L.map Prod.snd)
  | [], _ => rfl
  | p :: L, hL => by
    rw [List.map_cons, List.map_cons, bots_cons, bots_cons, mpErase_append,
      mpErase_bots hb (fun q hq => hL q (List.mem_cons_of_mem _ hq))]
    simp only [mpG]
    rw [mpErase_append, mpErase_rstar (hb _ (hL p List.mem_cons_self).mem).2]
    cases p.1 <;> simp [mpErase_self] <;> rfl

/-- `◇` is not in converted tops. -/
theorem diamond_notMem_tops {d : Card} {P : List Card} {n : Nat} (hb : CardsBelow n (d :: P)) :
    ∀ {L : List (Bool × Card)}, (∀ p ∈ L, MpOk d P p) → n + 1 ∉ tops (L.map (mpG n))
  | [], _ => by simp [tops]
  | p :: L, hL => by
    rw [List.map_cons, tops_cons, List.mem_append, not_or]
    refine ⟨fun h => ?_, diamond_notMem_tops hb (fun q hq => hL q (List.mem_cons_of_mem _ hq))⟩
    rcases mem_mpStar h with h | h
    · omega
    · have := (hb _ (hL p List.mem_cons_self).mem).1 _ h; omega

/-- `◇` is not in converted bottoms. -/
theorem diamond_notMem_bots {d : Card} {P : List Card} {n : Nat} (hb : CardsBelow n (d :: P)) :
    ∀ {L : List (Bool × Card)}, (∀ p ∈ L, MpOk d P p) → n + 1 ∉ bots (L.map (mpG n))
  | [], _ => by simp [bots]
  | p :: L, hL => by
    rw [List.map_cons, bots_cons, List.mem_append, not_or]
    refine ⟨fun h => ?_, diamond_notMem_bots hb (fun q hq => hL q (List.mem_cons_of_mem _ hq))⟩
    simp only [mpG, List.mem_append] at h
    rcases h with h | h
    · cases p.1 <;> simp at h <;> omega
    · rcases mem_mpRStar h with h | h
      · omega
      · have := (hb _ (hL p List.mem_cons_self).mem).2 _ h; omega

/-- A list of new cards is converted cards, possibly followed by the closing card and more. -/
theorem mp_split (d : Card) (P : List Card) (n : Nat) : ∀ B : List Card, (∀ q ∈ B, q ∈ mpcpToPCP d P n) →
    (∃ L : List (Bool × Card), (∀ p ∈ L, MpOk d P p) ∧ B = L.map (mpG n)) ∨
    (∃ (L : List (Bool × Card)) (D : List Card), (∀ p ∈ L, MpOk d P p) ∧ B = L.map (mpG n) ++ mpE n :: D)
  | [], _ => .inl ⟨[], fun _ h => by simp at h, rfl⟩
  | q :: B, h => by
    rcases mem_mpcpToPCP (h q List.mem_cons_self) with rfl | ⟨p, hp, rfl⟩
    · exact .inr ⟨[], B, fun _ h => by simp at h, rfl⟩
    · have hcons : ∀ {L : List (Bool × Card)}, (∀ p ∈ L, MpOk d P p) → ∀ x ∈ p :: L, MpOk d P x :=
        fun hL x hx => by
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hp
          · exact hL x hx
      rcases mp_split d P n B (fun q hq => h q (List.mem_cons_of_mem _ hq)) with ⟨L, hL, rfl⟩ | ⟨L, D, hL, rfl⟩
      · exact .inl ⟨p :: L, hcons hL, rfl⟩
      · exact .inr ⟨p :: L, D, hcons hL, rfl⟩

/-- A match cannot start with a converted card of `P`: its top starts with `⋆`, its bottom does not. -/
theorem mp_head_false {d : Card} {P : List Card} {n : Nat} (hb : CardsBelow n (d :: P))
    (hne : CardsNonempty (d :: P)) {c : Card} (hc : c ∈ P) (L : List (Bool × Card)) (e : Word)
    (h : tops (((false, c) :: L).map (mpG n)) ++ e = bots (((false, c) :: L).map (mpG n))) : False := by
  obtain ⟨u, v⟩ := c
  have hcm : (u, v) ∈ d :: P := List.mem_cons_of_mem _ hc
  obtain ⟨hu, hv⟩ := hne _ hcm
  cases u with
  | nil => exact hu rfl
  | cons a u =>
    cases v with
    | nil => exact hv rfl
    | cons b v =>
      have hbn : b < n := (hb _ hcm).2 b (by simp)
      simp only [List.map_cons, tops_cons, bots_cons, mpG, mpStar_cons, mpRStar_cons] at h
      simp at h
      omega

/-- The forward direction: a modified match becomes a match. -/
theorem mpcp_pcp_mp {d : Card} {P : List Card} {n : Nat} (h : MPCPSol d P) : PCPNSol (mpcpToPCP d P n) := by
  obtain ⟨A, hA, heq⟩ := h
  refine ⟨mpG n (true, d) :: A.map (fun c => mpG n (false, c)) ++ [mpE n], by simp, fun q hq => ?_, ?_⟩
  · rcases List.mem_append.1 hq with hq | hq
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact first_mem_mpcpToPCP d P n
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hq
        exact P_mem_mpcpToPCP n (hA c hc)
    · rw [List.mem_singleton.1 hq]
      exact E_mem_mpcpToPCP d P n
  · rw [tops_append, bots_append, tops_cons, bots_cons, tops_mpG_false, bots_mpG_false]
    rw [tops_cons, bots_cons] at heq
    simp only [mpG, mpE, tops_cons, bots_cons, tops_nil, bots_nil, List.append_nil]
    have key : mpStar n (d.1 ++ tops A) ++ [n] = n :: mpRStar n (d.2 ++ bots A) := by
      rw [mpStar_snoc, heq]
    rw [mpStar_append, mpRStar_append] at key
    have : mpStar n d.1 ++ mpStar n (tops A) ++ [n, n + 1] =
        (mpStar n d.1 ++ mpStar n (tops A) ++ [n]) ++ [n + 1] := by simp
    rw [this, key]
    simp

/-- After the leading first card, a match of converted cards with `e` appended reads back a modified match. -/
theorem mp_read {d : Card} {P : List Card} {n : Nat} (hb : CardsBelow n (d :: P))
    {L : List (Bool × Card)} (hL : ∀ p ∈ L, MpOk d P p) (hL1 : nF L ≤ 1)
    (h : mpErase n (tops (L.map (mpG n))) = mpErase n (bots (L.map (mpG n))))
    (hlen : (tops (L.map (mpG n))).length + 1 = (bots (L.map (mpG n))).length)
    (hd : ∃ L', L = (true, d) :: L') : MPCPSol d P := by
  obtain ⟨L', rfl⟩ := hd
  rw [mpErase_tops hb hL, mpErase_bots hb hL] at h
  have h0 : nF L' = 0 := by simp only [nF] at hL1; simp at hL1; omega
  have hf := nF_zero h0
  refine ⟨L'.map Prod.snd, fun c hc => ?_, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    rcases hL p (List.mem_cons_of_mem _ hp) with ⟨h1, _⟩ | ⟨_, h2⟩
    · rw [hf p hp] at h1; exact absurd h1 (by decide)
    · exact h2
  · simpa using h

/-- The backward direction: a match reads back a modified match. -/
theorem mpcp_pcp_pm {d : Card} {P : List Card} {n : Nat} (hb : CardsBelow n (d :: P))
    (hne : CardsNonempty (d :: P)) (h : PCPNSol (mpcpToPCP d P n)) : MPCPSol d P := by
  obtain ⟨B, hBne, hBQ, heq⟩ := h
  rcases mp_split d P n B hBQ with ⟨L, hL, rfl⟩ | ⟨L, D, hL, rfl⟩
  · -- no closing card: impossible
    exfalso
    cases L with
    | nil => exact hBne rfl
    | cons p L =>
      obtain ⟨b, c⟩ := p
      rcases hL _ List.mem_cons_self with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only at h1 h2
        subst h1 h2
        have hlen := congrArg List.length heq
        have her := congrArg (mpErase n) heq
        rw [mpErase_tops hb hL, mpErase_bots hb hL] at her
        rw [tops_mpG_length, bots_mpG_length, her] at hlen
        simp [nF] at hlen
      · simp only at h1 h2
        subst h1
        exact mp_head_false hb hne h2 L [] (by rw [List.append_nil]; exact heq)
  · rw [tops_append, bots_append, tops_cons, bots_cons] at heq
    have h3 : (tops (L.map (mpG n)) ++ [n]) ++ (n + 1) :: tops D = bots (L.map (mpG n)) ++ (n + 1) :: bots D := by
      simpa [mpE] using heq
    have hnot : n + 1 ∉ tops (L.map (mpG n)) ++ [n] := by
      rw [List.mem_append, not_or]
      exact ⟨diamond_notMem_tops hb hL, by simp⟩
    have h4 := (first_occ hnot (diamond_notMem_bots hb hL) h3).1
    have hlen := congrArg List.length h4
    have her := congrArg (mpErase n) h4
    rw [mpErase_append, mpErase_self, List.append_nil] at her
    rw [List.length_append, List.length_singleton] at hlen
    have hlen' := hlen
    rw [tops_mpG_length, bots_mpG_length] at hlen'
    rw [mpErase_tops hb hL, mpErase_bots hb hL] at her
    rw [her] at hlen'
    have hF : nF L = 1 := by omega
    rw [← mpErase_tops hb hL, ← mpErase_bots hb hL] at her
    cases L with
    | nil => simp [tops, bots] at h4
    | cons p L =>
      obtain ⟨b, c⟩ := p
      rcases hL _ List.mem_cons_self with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only at h1 h2
        subst h1 h2
        exact mp_read hb hL (by omega) her hlen ⟨L, rfl⟩
      · simp only at h1 h2
        subst h1
        exact absurd h4 (fun h4 => mp_head_false hb hne h2 L [n] h4)

/-- **The modified correspondence problem reduces to the plain one.** -/
theorem mpcp_pcp (d : Card) (P : List Card) (n : Nat) (hb : CardsBelow n (d :: P)) (hne : CardsNonempty (d :: P)) :
    MPCPSol d P ↔ PCPNSol (mpcpToPCP d P n) :=
  ⟨mpcp_pcp_mp, mpcp_pcp_pm hb hne⟩

/-- The converted cards use the symbols below `n + 2`. -/
theorem mpcpToPCP_below (d : Card) (P : List Card) (n : Nat) (hb : CardsBelow n (d :: P)) :
    CardsBelow (n + 2) (mpcpToPCP d P n) := by
  intro q hq
  rcases mem_mpcpToPCP hq with rfl | ⟨p, hp, rfl⟩
  · constructor <;> intro a ha <;> simp [mpE] at ha <;> omega
  · have hpb := hb _ hp.mem
    constructor
    · intro a ha
      rcases mem_mpStar ha with h | h
      · omega
      · have := hpb.1 a h; omega
    · intro a ha
      simp only [mpG, List.mem_append] at ha
      rcases ha with h | h
      · simp at h; have := h.2; omega
      · rcases mem_mpRStar h with h | h
        · omega
        · have := hpb.2 a h; omega

/-- The converted cards have nonempty tops and bottoms. -/
theorem mpcpToPCP_nonempty (d : Card) (P : List Card) (n : Nat) (hne : CardsNonempty (d :: P)) :
    CardsNonempty (mpcpToPCP d P n) := by
  intro q hq
  rcases mem_mpcpToPCP hq with rfl | ⟨p, hp, rfl⟩
  · simp [mpE]
  · obtain ⟨hu, hv⟩ := hne _ hp.mem
    obtain ⟨b, u, v⟩ := p
    simp only at hu hv
    cases u with
    | nil => exact absurd rfl hu
    | cons a u =>
      cases v with
      | nil => exact absurd rfl hv
      | cons e v => simp [mpG, mpStar_cons, mpRStar_cons]

end Complexity.Undec
