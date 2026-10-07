import Cfg.Greibach.StdStack

/-!
# Leftmost derivations of a standard-form grammar (for `greibach_std`)

Following Nipkow's `drives`: the productions of a grammar are listed as triples `(A, a, Bs)` for `A → a Bs`
(`prods`); `Drives P ps α w β` says that applying the productions `ps` as successive leftmost steps to the
nonterminal stack `α` (top first) emits `w` and reaches `β`. For a grammar in standard form, generation of `w` from
the start is a drive from `[start]` to `[]` (`language_iff_drives`).

The code `xi p` of a production pops its left side and pushes its right-side nonterminals in reverse
(`stkRun_xi`, `stkRun_xi_inv`), so a drive is a run of the stack machine (`drives_stkRun`, `drives_of_stkRun`).
-/

namespace Shallot.Cfg
namespace GStd

/-- A production `A → a B₁ … Bₘ` as `(A, a, [B₁, …, Bₘ])`. -/
abbrev GProd := Nat × Char × List Nat

/-- The production read off a right side of nonterminal `i`. -/
def rhsProd (i : Nat) : Rhs → Option GProd
  | .t a :: rest => some (i, a, ntSeq rest)
  | _ => none

/-- The productions of the rule list, starting at index `k`. -/
def prodsFrom : Nat → List (List Rhs) → List GProd
  | _, [] => []
  | k, alts :: rs => alts.filterMap (rhsProd k) ++ prodsFrom (k + 1) rs

/-- The productions of a grammar. -/
def prods (g : CFGrammar) : List GProd := prodsFrom 0 g.rules

/-- A production of `prodsFrom k rs` comes from some right side of some nonterminal. -/
theorem mem_prodsFrom {p : GProd} : ∀ {k : Nat} {rs : List (List Rhs)}, p ∈ prodsFrom k rs →
    ∃ i alts r, altsAt rs i = some alts ∧ r ∈ alts ∧ rhsProd (k + i) r = some p
  | _, [], h => by cases h
  | k, alts :: rs, h => by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨r, hr, hp⟩ := List.mem_filterMap.mp h
      exact ⟨0, alts, r, rfl, hr, hp⟩
    · obtain ⟨i, alts', r, h1, h2, h3⟩ := mem_prodsFrom h
      exact ⟨i + 1, alts', r, h1, h2, by rw [← h3]; congr 1; omega⟩

/-- Every right side of every nonterminal yields its production. -/
theorem prodsFrom_mem : ∀ {k : Nat} {rs : List (List Rhs)} {i : Nat} {alts : List Rhs} {r : Rhs} {p : GProd},
    altsAt rs i = some alts → r ∈ alts → rhsProd (k + i) r = some p → p ∈ prodsFrom k rs
  | _, [], _, _, _, _, h, _, _ => by cases h
  | k, a :: rs, 0, alts, r, p, h, hr, hp => by
    simp only [altsAt, Option.some.injEq] at h
    subst h
    exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨r, hr, hp⟩)
  | k, a :: rs, i + 1, alts, r, p, h, hr, hp => by
    simp only [altsAt] at h
    exact List.mem_append_right _ (prodsFrom_mem (k := k + 1) h hr (by rw [← hp]; congr 1; omega))

/-- An alternative list found by `altsAt` is in the rule list. -/
theorem altsAt_mem : ∀ {rs : List (List Rhs)} {i : Nat} {alts : List Rhs}, altsAt rs i = some alts → alts ∈ rs
  | [], _, _, h => by cases h
  | a :: rs, 0, alts, h => by
    simp only [altsAt, Option.some.injEq] at h
    subst h; exact List.mem_cons_self
  | a :: rs, i + 1, alts, h => by
    simp only [altsAt] at h
    exact List.mem_cons_of_mem _ (altsAt_mem h)

/-- A list of nonterminal symbols is the image of its nonterminal sequence. -/
theorem eq_map_ntSeq : ∀ {rest : List Sym}, (∀ s ∈ rest, ∃ j, s = .nt j) → rest = (ntSeq rest).map Sym.nt
  | [], _ => rfl
  | .nt j :: rest, h => by
    simp only [ntSeq, List.map_cons]
    rw [← eq_map_ntSeq (fun s hs => h s (List.mem_cons_of_mem _ hs))]
  | .t c :: rest, h => by
    obtain ⟨j, hj⟩ := h (.t c) List.mem_cons_self
    cases hj

/-- In standard form, a production of the grammar is literally a right side of its left side. -/
theorem prods_rhs {g : CFGrammar} (hs : StdForm g) {A : Nat} {a : Char} {Bs : List Nat}
    (hp : (A, a, Bs) ∈ prods g) :
    ∃ alts, altsAt g.rules A = some alts ∧ (Sym.t a :: Bs.map Sym.nt) ∈ alts := by
  obtain ⟨i, alts, r, h1, h2, h3⟩ := mem_prodsFrom hp
  obtain ⟨⟨a', rest, hr, hnt⟩, _⟩ := hs alts (altsAt_mem h1) r h2
  subst hr
  simp only [rhsProd, Nat.zero_add, Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨hA, ha, hB⟩ := h3
  subst hA; subst ha; subst hB
  exact ⟨alts, h1, by rw [← eq_map_ntSeq hnt]; exact h2⟩

/-- In standard form, every right side of every nonterminal is a production. -/
theorem rhs_prods {g : CFGrammar} (hs : StdForm g) {A : Nat} {alts : List Rhs} {r : Rhs}
    (h1 : altsAt g.rules A = some alts) (h2 : r ∈ alts) :
    ∃ a Bs, r = Sym.t a :: Bs.map Sym.nt ∧ (A, a, Bs) ∈ prods g := by
  obtain ⟨⟨a, rest, hr, hnt⟩, _⟩ := hs alts (altsAt_mem h1) r h2
  refine ⟨a, ntSeq rest, by rw [hr, ← eq_map_ntSeq hnt], ?_⟩
  exact prodsFrom_mem (k := 0) h1 h2 (by rw [hr, Nat.zero_add]; rfl)

/-- In standard form, the start is on no right side of a production. -/
theorem prods_start {g : CFGrammar} (hs : StdForm g) {p : GProd} (hp : p ∈ prods g) : g.start ∉ p.2.2 := by
  obtain ⟨A, a, Bs⟩ := p
  obtain ⟨alts, h1, h2⟩ := prods_rhs hs hp
  have hno := (hs alts (altsAt_mem h1) _ h2).2
  intro hB
  exact hno (List.mem_cons_of_mem _ (List.mem_map_of_mem hB))

/-! ## Drives -/

/-- **Leftmost derivations on a nonterminal stack.** -/
inductive Drives (P : List GProd) : List GProd → List Nat → List Char → List Nat → Prop
  | nil (α : List Nat) : Drives P [] α [] α
  | cons {A : Nat} {a : Char} {Bs : List Nat} {ps : List GProd} {α : List Nat} {w : List Char} {β : List Nat} :
      (A, a, Bs) ∈ P → Drives P ps (Bs ++ α) w β → Drives P ((A, a, Bs) :: ps) (A :: α) (a :: w) β

/-- A drive works on any extension of the stack. -/
theorem Drives.extend {P : List GProd} {ps : List GProd} {α β : List Nat} {w : List Char}
    (h : Drives P ps α w β) (γ : List Nat) : Drives P ps (α ++ γ) w (β ++ γ) := by
  induction h with
  | nil α => exact Drives.nil _
  | cons hp _ ih => exact Drives.cons hp (by simpa [List.append_assoc] using ih)

/-- Drives compose. -/
theorem Drives.trans {P : List GProd} {ps ps' : List GProd} {α β γ : List Nat} {w w' : List Char}
    (h : Drives P ps α w β) (h' : Drives P ps' β w' γ) : Drives P (ps ++ ps') α (w ++ w') γ := by
  induction h with
  | nil α => exact h'
  | cons hp _ ih => exact Drives.cons hp (ih h')

/-- The productions of a drive are in `P` and their letters spell the emitted word. -/
theorem Drives.letters {P : List GProd} {ps : List GProd} {α β : List Nat} {w : List Char}
    (h : Drives P ps α w β) : ps.map (·.2.1) = w ∧ ∀ p ∈ ps, p ∈ P := by
  induction h with
  | nil α => exact ⟨rfl, fun p hp => by cases hp⟩
  | cons hp _ ih =>
    refine ⟨by simp [ih.1], fun p hq => ?_⟩
    rcases List.mem_cons.mp hq with h | h
    · subst h; exact hp
    · exact ih.2 p h

/-- Once the start has left the stack, no later production expands it. -/
theorem Drives.no_start {P : List GProd} {S : Nat} (hP : ∀ p ∈ P, S ∉ p.2.2) {ps : List GProd}
    {α β : List Nat} {w : List Char} (h : Drives P ps α w β) : S ∉ α → ∀ p ∈ ps, p.1 ≠ S := by
  induction h with
  | nil α => intro _ p hp; cases hp
  | @cons A a Bs ps α w β hp _ ih =>
    intro hS p hq
    rcases List.mem_cons.mp hq with h | h
    · subst h; intro hA; exact hS (List.mem_cons.mpr (Or.inl hA.symm))
    · apply ih _ p h
      intro hm
      rcases List.mem_append.mp hm with h1 | h1
      · exact hP _ hp h1
      · exact hS (List.mem_cons_of_mem _ h1)

/-! ## Generation and drives -/

/-- Splitting a generation of a concatenated right side. -/
theorem genRhs_append_split {g : CFGrammar} : ∀ {xs ys : List Sym} {w : List Char}, GenRhs g (xs ++ ys) w →
    ∃ w1 w2, w = w1 ++ w2 ∧ GenRhs g xs w1 ∧ GenRhs g ys w2
  | [], ys, w, h => ⟨[], w, rfl, GenRhs.nil, h⟩
  | x :: xs, ys, w, h => by
    cases h with
    | cons_t c _ w' h =>
      obtain ⟨w1, w2, he, h1, h2⟩ := genRhs_append_split h
      exact ⟨c :: w1, w2, by simp [he], GenRhs.cons_t c xs w1 h1, h2⟩
    | cons_nt j _ u1 u2 hj h =>
      obtain ⟨w1, w2, he, h1, h2⟩ := genRhs_append_split h
      exact ⟨u1 ++ w1, w2, by simp [he], GenRhs.cons_nt j xs u1 w1 hj h1, h2⟩

/-- A drive to `β` followed by a generation from `β` is a generation from the stack. -/
theorem genRhs_of_drives {g : CFGrammar} (hs : StdForm g) {ps : List GProd} {α β : List Nat} {w : List Char}
    (h : Drives (prods g) ps α w β) : ∀ w2, GenRhs g (β.map Sym.nt) w2 → GenRhs g (α.map Sym.nt) (w ++ w2) := by
  induction h with
  | nil α => intro w2 h2; exact h2
  | @cons A a Bs ps α w β hp _ ih =>
    intro w2 h2
    have h3 := ih w2 h2
    rw [List.map_append] at h3
    obtain ⟨u1, u2, he, hu1, hu2⟩ := genRhs_append_split h3
    obtain ⟨alts, ha, hm⟩ := prods_rhs hs hp
    have hA : Gen g A (a :: u1) := Gen.prod A alts _ _ ha hm (GenRhs.cons_t a _ u1 hu1)
    have := GenRhs.cons_nt A (α.map Sym.nt) (a :: u1) u2 hA hu2
    simpa [he] using this

/-- The motive for the right sides in `drives_of_gen`. -/
def DrivesRhs (g : CFGrammar) (rhs : List Sym) (w : List Char) : Prop :=
  ∀ Bs : List Nat, (rhs = Bs.map Sym.nt → ∃ ps, Drives (prods g) ps Bs w []) ∧
    ∀ a, rhs = Sym.t a :: Bs.map Sym.nt → ∃ w' ps, w = a :: w' ∧ Drives (prods g) ps Bs w' []

/-- A generation from a nonterminal is a drive from the one-element stack. -/
theorem drives_of_gen {g : CFGrammar} (hs : StdForm g) {i : Nat} {w : List Char} (h : Gen g i w) :
    ∃ ps, Drives (prods g) ps [i] w [] := by
  induction h using Gen.rec (motive_2 := fun rhs w _ => DrivesRhs g rhs w) with
  | prod i alts rhs w halts hmem _ ih =>
    obtain ⟨a, Bs, hr, hp⟩ := rhs_prods hs halts hmem
    obtain ⟨w', ps, hw, hd⟩ := (ih Bs).2 a hr
    exact ⟨(i, a, Bs) :: ps, by rw [hw]; exact Drives.cons hp (by simpa using hd)⟩
  | nil =>
    intro Bs
    refine ⟨fun h => ?_, fun a h => by cases h⟩
    cases Bs with
    | nil => exact ⟨[], Drives.nil _⟩
    | cons _ _ => cases h
  | cons_t c rest w _ ih =>
    intro Bs
    refine ⟨fun h => ?_, fun a h => ?_⟩
    · cases Bs with
      | nil => cases h
      | cons _ _ => cases h
    · simp only [List.cons.injEq, Sym.t.injEq] at h
      obtain ⟨hc, hr⟩ := h
      subst hc
      obtain ⟨ps, hd⟩ := (ih Bs).1 hr
      exact ⟨w, ps, rfl, hd⟩
  | cons_nt j rest w1 w2 _ _ ih1 ih2 =>
    intro Bs
    refine ⟨fun h => ?_, fun a h => by cases h⟩
    cases Bs with
    | nil => cases h
    | cons B Bs =>
      simp only [List.map_cons, List.cons.injEq, Sym.nt.injEq] at h
      obtain ⟨hj, hr⟩ := h
      subst hj
      obtain ⟨ps1, hd1⟩ := ih1
      obtain ⟨ps2, hd2⟩ := (ih2 Bs).1 hr
      exact ⟨ps1 ++ ps2, Drives.trans (by simpa using hd1.extend Bs) hd2⟩

/-- **Generation from the start is a drive from `[start]` to `[]`.** -/
theorem language_iff_drives {g : CFGrammar} (hs : StdForm g) (w : List Char) :
    g.language w ↔ ∃ ps, Drives (prods g) ps [g.start] w [] := by
  constructor
  · exact drives_of_gen hs
  · rintro ⟨ps, hd⟩
    have h := genRhs_of_drives hs hd [] GenRhs.nil
    rw [List.append_nil] at h
    generalize hr : ([g.start].map Sym.nt) = r at h
    cases h with
    | nil => cases hr
    | cons_t _ _ _ _ => cases hr
    | cons_nt j rest w1 w2 h1 h2 =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, Sym.nt.injEq] at hr
      obtain ⟨hj, hrest⟩ := hr
      subst hj; subst hrest
      cases h2
      simpa [CFGrammar.language] using h1

/-! ## The stack codes of productions -/

/-- `ξ(p)`: pop the left side, then push the right-side nonterminals in reverse. -/
def xi (p : GProd) : List Char := popcode p.1 ++ ((p.2.2.reverse).map pushcode).flatten

/-- Running `ξ(p)` on a stack topped by its left side replaces the left side by the right side. -/
theorem stkRun_xi (p : GProd) (s : List Char) : stkRun (frag p.1 ++ s) (xi p) = some (stkenc p.2.2 ++ s) := by
  rw [xi, stkRun_append, stkRun_popcode, Option.bind_some, stkRun_pushes, List.reverse_reverse]

/-- Inverting `stkRun_xi`: a successful run of `ξ(p)` on an encoded stack pops its left side. -/
theorem stkRun_xi_inv {p : GProd} {α : List Nat} {s : List Char} (h : stkRun (stkenc α) (xi p) = some s) :
    ∃ α', α = p.1 :: α' ∧ s = stkenc (p.2.2 ++ α') := by
  rw [xi] at h
  obtain ⟨s', h1, h2⟩ := stkRun_append_split h
  have hst := stkRun_popcode_inv h1
  rw [stkRun_pushes, List.reverse_reverse, Option.some.injEq] at h2
  cases α with
  | nil => simp [stkenc, frag] at hst
  | cons A α' =>
    have hst' : frag A ++ stkenc α' = frag p.1 ++ s' := by simpa [stkenc] using hst
    obtain ⟨hA, hs'⟩ := frag_append_inj hst'
    refine ⟨α', by rw [hA], ?_⟩
    rw [← h2, ← hs']
    simp [stkenc]

/-- **Central invariant**: a drive is a run of the stack machine on the codes of its productions. -/
theorem drives_stkRun {P : List GProd} {ps : List GProd} {α β : List Nat} {w : List Char}
    (h : Drives P ps α w β) : stkRun (stkenc α) ((ps.map xi).flatten) = some (stkenc β) := by
  induction h with
  | nil α => rfl
  | @cons A a Bs ps α w β _ _ ih =>
    simp only [List.map_cons, List.flatten_cons]
    rw [stkRun_append]
    have := stkRun_xi (A, a, Bs) (stkenc α)
    have he : stkenc (A :: α) = frag A ++ stkenc α := by simp [stkenc]
    rw [he, this, Option.bind_some]
    have he2 : stkenc Bs ++ stkenc α = stkenc (Bs ++ α) := by simp [stkenc]
    rw [he2]; exact ih

/-- **Converse of the central invariant**: a successful run of the codes of productions of `P` from an encoded
stack to the empty stack is a drive. -/
theorem drives_of_stkRun {P : List GProd} : ∀ {ps : List GProd} {α : List Nat}, (∀ p ∈ ps, p ∈ P) →
    stkRun (stkenc α) ((ps.map xi).flatten) = some [] → Drives P ps α (ps.map (·.2.1)) []
  | [], α, _, h => by
    simp only [List.map_nil, List.flatten_nil, stkRun, Option.some.injEq] at h
    rw [stkenc_eq_nil h]; exact Drives.nil _
  | p :: ps, α, hP, h => by
    simp only [List.map_cons, List.flatten_cons] at h
    obtain ⟨s', h1, h2⟩ := stkRun_append_split h
    obtain ⟨α', hα, hs'⟩ := stkRun_xi_inv h1
    rw [hs'] at h2
    have hd := drives_of_stkRun (fun q hq => hP q (List.mem_cons_of_mem _ hq)) h2
    obtain ⟨A, a, Bs⟩ := p
    subst hα
    exact Drives.cons (hP _ List.mem_cons_self) hd

end GStd
end Shallot.Cfg
