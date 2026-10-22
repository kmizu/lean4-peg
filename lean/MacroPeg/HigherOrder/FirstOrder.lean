import MacroPeg.HigherOrder.Embed
import MacroPeg.HigherOrder.KExp.LamFree

namespace Shallot.MacroPeg.HO

open Shallot.MacroPeg
open Shallot.MacroPeg.KExp

/-- Recover first-order calls from curried rule applications. -/
def unemb (ar : Nat) : HExp → MExp
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit s => .lit s
  | .var i => .param (ar - 1 - i)
  | .rule i => .call i []
  | .seq a b => .seq (unemb ar a) (unemb ar b)
  | .alt a b => .alt (unemb ar a) (unemb ar b)
  | .star a => .star (unemb ar a)
  | .notP a => .notP (unemb ar a)
  | .app f a => match unemb ar f with
    | .call i args => .call i (args ++ [unemb ar a])
    | _ => MExp.failAlways
  | .lam _ _ => MExp.failAlways

/-- Every decoded expression belongs to the first-order syntax. -/
theorem unemb_firstOrder (ar : Nat) (e : HExp) : (unemb ar e).FirstOrder := by
  induction e with
  | eps | any | chr | range | lit | var | rule | lam => simp [unemb, MExp.FirstOrder, MExp.FirstOrderArgs, MExp.failAlways]
  | seq a b ha hb | alt a b ha hb => exact ⟨ha, hb⟩
  | star a ha | notP a ha => exact ha
  | app f a hf ha =>
    simp only [unemb]
    cases he : unemb ar f <;> try simp [MExp.FirstOrder, MExp.failAlways]
    case call i args =>
      rw [he] at hf
      change MExp.FirstOrderArgs (args ++ [unemb ar a])
      have h : ∀ xs : List MExp, MExp.FirstOrderArgs xs →
          MExp.FirstOrderArgs (xs ++ [unemb ar a]) := by
        intro xs hx
        induction xs with
        | nil => exact ⟨ha, True.intro⟩
        | cons x xs ih => exact ⟨hx.1, ih hx.2⟩
      exact h args hf

/-- A lambda-free expression of function type has a named-rule head. -/
theorem unemb_function {R : List Ty} {ar : Nat} {e : HExp} {a b : Ty}
    (ht : HasTy R (List.replicate ar .p) e (.arr a b)) (hl : LF e) :
    ∃ i args, unemb ar e = .call i args := by
  induction e generalizing a b with
  | rule i => exact ⟨i, [], rfl⟩
  | app f x ihf ihx =>
    cases ht with
    | app hf hx =>
      have hlf : LF f := Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq hl))
      obtain ⟨i, args, hi⟩ := ihf hf hlf
      exact ⟨i, args ++ [unemb ar x], by simp [unemb, hi]⟩
  | var i =>
    cases ht with
    | var h =>
      have hp : Ty.arr a b = Ty.p := List.eq_of_mem_replicate (List.mem_of_getElem? h)
      cases hp
  | lam t e ih => simp [LF, lamOrd] at hl
  | _ => cases ht

/-- Decoding then embedding recovers every typed lambda-free expression in a parser context. -/
theorem emb_unemb {R : List Ty} {ar : Nat} {e : HExp} {τ : Ty}
    (ht : HasTy R (List.replicate ar .p) e τ) (hl : LF e) : emb ar (unemb ar e) = e := by
  induction e generalizing τ with
  | eps | any | chr | range | lit | rule => rfl
  | var i =>
    have hi : i < ar := by cases ht with | var h => simpa using (List.getElem?_eq_some_iff.mp h |>.1)
    simp only [unemb, emb]
    rw [if_pos (by omega)]
    congr 1
    omega
  | lam t e ih => simp [LF, lamOrd] at hl
  | seq a b ha hb | alt a b ha hb =>
    cases ht
    all_goals
      have hla : LF a := Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq hl))
      have hlb : LF b := Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq hl))
      simp only [unemb, emb]
      congr 1
      · exact ha (by assumption) hla
      · exact hb (by assumption) hlb
  | star a ha | notP a ha =>
    cases ht
    all_goals simp only [unemb, emb]; congr 1; exact ha (by assumption) hl
  | app f a hf ha =>
    cases ht with
    | app htf hta =>
      have hlf : LF f := Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq hl))
      have hla : LF a := Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq hl))
      obtain ⟨i, args, he⟩ := unemb_function htf hlf
      have hemb := hf htf hlf
      rw [he] at hemb
      simp only [unemb, he, emb, embArgs_eq_map, List.map_append, List.map_cons, List.map_nil]
      have happ : ∀ xs ys : List HExp, HExp.apps (.rule i) (xs ++ ys) = HExp.apps (HExp.apps (.rule i) xs) ys := by
        intro xs ys
        generalize hh : HExp.rule i = h
        clear hh
        induction xs generalizing h with
        | nil => rfl
        | cons x xs ih => exact ih (.app h x)
      rw [happ]
      simp only [HExp.apps]
      rw [← embArgs_eq_map]
      change (emb ar (.call i args)).app (emb ar (unemb ar a)) = _
      rw [hemb, ha hta hla]

/-- Number of parser arguments in a first-order type. -/
def Ty.width : Ty → Nat
  | .p => 0
  | .arr _ b => b.width + 1

/-- The low-order types contain only parser arguments. -/
theorem type_zero {τ : Ty} (h : τ.order = 0) : τ = .p := by
  cases τ with
  | p => rfl
  | arr a b => simp [Ty.order] at h

/-- A lambda-free term over first-order rules has first-order type. -/
theorem lf_type_order {R : List Ty} (hR : ∀ τ ∈ R, τ.order ≤ 1)
    {ar : Nat} {e : HExp} {τ : Ty}
    (ht : HasTy R (List.replicate ar .p) e τ) (hl : LF e) : τ.order ≤ 1 := by
  induction e generalizing τ with
  | lam a b ih => simp [LF, lamOrd] at hl
  | rule i => cases ht with | rule h => exact hR _ (List.mem_of_getElem? h)
  | var i =>
    cases ht with
    | var h => rw [List.eq_of_mem_replicate (List.mem_of_getElem? h)]; decide
  | app f a ihf iha =>
    cases ht with
    | app hf ha =>
      have hlf : LF f := Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq hl))
      have ho := ihf hf hlf
      exact Nat.le_trans (Nat.le_max_right _ _) ho
  | _ => cases ht <;> decide

/-- A call may be partially applied while reconstructing its curried head. -/
def Partial (G : MGrammar) (e : MExp) (τ : Ty) : Prop :=
  (τ = .p ∧ MExp.arityOk G e = true) ∨
  ∃ i args r, e = .call i args ∧ ruleAtM G.rules i = some r ∧
    r.arity = args.length + τ.width ∧ MExp.arityOkArgs G args = true

theorem partial_parser {G : MGrammar} {e : MExp} (h : Partial G e .p) :
    MExp.arityOk G e = true := by
  rcases h with h | ⟨i, args, r, rfl, hr, hn, ha⟩
  · exact h.2
  · simp [MExp.arityOk, hr, hn, Ty.width, ha]

theorem arityArgs_append (G : MGrammar) (xs ys : List MExp) :
    MExp.arityOkArgs G (xs ++ ys) = (MExp.arityOkArgs G xs && MExp.arityOkArgs G ys) := by
  induction xs with
  | nil => simp [MExp.arityOkArgs]
  | cons x xs ih => simp [MExp.arityOkArgs, ih, Bool.and_assoc]

/-- Typing certifies every fully applied call produced by decoding. -/
theorem unemb_partial {R : List Ty} {G : MGrammar}
    (hR : ∀ τ ∈ R, τ.order ≤ 1)
    (hG : ∀ i τ, R[i]? = some τ → ∃ r, ruleAtM G.rules i = some r ∧ τ = Ty.parsers r.arity)
    {ar : Nat} {e : HExp} {τ : Ty}
    (ht : HasTy R (List.replicate ar .p) e τ) (hl : LF e) : Partial G (unemb ar e) τ := by
  induction e generalizing τ with
  | eps | any | chr | range | lit => cases ht <;> exact Or.inl ⟨rfl, rfl⟩
  | lam a b ih => simp [LF, lamOrd] at hl
  | var i =>
    cases ht with
    | var h =>
      have hp := List.eq_of_mem_replicate (List.mem_of_getElem? h)
      exact Or.inl ⟨hp, rfl⟩
  | rule i =>
    cases ht with
    | rule h =>
      obtain ⟨r, hr, rfl⟩ := hG i _ h
      have hw : ∀ n, (Ty.parsers n).width = n := by
        intro n; induction n with
        | zero => rfl
        | succ n ih => simp [Ty.parsers, Ty.width, ih]
      exact Or.inr ⟨i, [], r, rfl, hr, by simp [hw], rfl⟩
  | seq a b ha hb | alt a b ha hb =>
    cases ht
    all_goals
      have hla : LF a := Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq hl))
      have hlb : LF b := Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq hl))
      apply Or.inl
      exact ⟨rfl, by simp only [unemb, MExp.arityOk]; rw [partial_parser (ha (by assumption) hla), partial_parser (hb (by assumption) hlb)]; rfl⟩
  | star a ha | notP a ha =>
    cases ht
    all_goals
      apply Or.inl
      refine ⟨rfl, ?_⟩
      change MExp.arityOk G (unemb ar a) = true
      exact partial_parser (ha (by assumption) hl)
  | app f a ihf iha =>
    cases ht with
    | app htf hta =>
      have hlf : LF f := Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq hl))
      have hla : LF a := Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq hl))
      rename_i dom
      have ho := lf_type_order hR htf hlf
      have hp : dom = Ty.p := type_zero (by simp only [Ty.order] at ho; omega)
      subst hp
      have ha := partial_parser (iha hta hla)
      rcases ihf htf hlf with ⟨hbad, _⟩ | ⟨i, args, r, he, hr, hn, hs⟩
      · cases hbad
      · apply Or.inr
        refine ⟨i, args ++ [unemb ar a], r, by simp [unemb, he], hr, ?_, ?_⟩
        · simp only [Ty.width] at hn
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · rw [arityArgs_append]; simp [MExp.arityOkArgs, hs, ha]

/-- Remove the declared leading parser binders. -/
def peel : Nat → HExp → HExp
  | 0, e => e
  | n + 1, .lam _ e => peel n e
  | _ + 1, _ => .eps

def firstRule (r : HRule) : MRule :=
  ⟨r.ty.width, unemb r.ty.width (peel r.ty.width r.body)⟩

def firstGrammar (g : HGrammar) : MGrammar := ⟨g.rules.map firstRule⟩

/-- Rule lambdas declare parser parameters; their bodies contain no lambdas. -/
def FirstShape (g : HGrammar) : Prop :=
  ∀ r ∈ g.rules, ∃ n b, r.ty = Ty.parsers n ∧ r.body = lams n b ∧ LF b

theorem width_parsers (n : Nat) : (Ty.parsers n).width = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Ty.parsers, Ty.width, ih]

theorem peel_lams (n : Nat) (b : HExp) : peel n (lams n b) = b := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem typed_lams {R Γ : List Ty} {n : Nat} {b : HExp}
    (ht : HasTy R Γ (lams n b) (Ty.parsers n)) :
    HasTy R (List.replicate n .p ++ Γ) b .p := by
  induction n generalizing Γ with
  | zero => exact ht
  | succ n ih =>
    cases ht with
    | lam h =>
      have hh := ih h
      simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using hh

theorem firstGrammar_shape {g : HGrammar} (hs : FirstShape g) :
    (∀ τ ∈ g.types, τ.order ≤ 1) ∧
    (∀ i τ, g.types[i]? = some τ → ∃ r,
      ruleAtM (firstGrammar g).rules i = some r ∧ τ = Ty.parsers r.arity) := by
  constructor
  · intro τ ht
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
    obtain ⟨n, b, he, _, _⟩ := hs r hr
    rw [he]; exact order_parsers n
  · intro i τ ht
    have lookup : ∀ (rs : List HRule) (i : Nat) (r : HRule), rs[i]? = some r →
        ruleAtM (rs.map firstRule) i = some (firstRule r) := by
      intro rs i r hr
      induction rs generalizing i with
      | nil => simp at hr
      | cons a rs ih => cases i with
        | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hr; subst r; rfl
        | succ i => exact ih i (by simpa using hr)
    have hm : (g.rules[i]?).map HRule.ty = some τ := by simpa [HGrammar.types] using ht
    cases hr : g.rules[i]? with
    | none => simp [hr] at hm
    | some r =>
      have hτ : r.ty = τ := by simpa [hr] using hm
      obtain ⟨n, b, hty, _, _⟩ := hs r (List.mem_of_getElem? hr)
      refine ⟨firstRule r, lookup _ _ _ hr, ?_⟩
      simp only [firstRule]
      rw [← hτ, hty, width_parsers]

/-- The recovered grammar embeds back into exactly the original grammar. -/
theorem emb_firstGrammar {g : HGrammar} (hw : g.WellTyped) (hs : FirstShape g) :
    embGrammar (firstGrammar g) = g := by
  have hmap : (g.rules.map firstRule).map embRule = g.rules := by
    rw [List.map_map]
    apply Eq.trans (b := g.rules.map id)
    · apply List.map_congr_left
      intro r hr
      obtain ⟨n, b, hty, hb, hl⟩ := hs r hr
      have ht := hw r hr
      rw [hty, hb] at ht
      have ht' : HasTy g.types (List.replicate n .p) b .p := by simpa using typed_lams ht
      have he := emb_unemb ht' hl
      cases r with
      | mk ty body =>
        change ty = Ty.parsers n at hty
        change body = lams n b at hb
        simp only [Function.comp_apply, firstRule, embRule, hty, hb, width_parsers, peel_lams, he]
        rfl
    · exact List.map_id _
  cases g with
  | mk rules => exact congrArg HGrammar.mk hmap

/-- The recovered grammar has only first-order expressions. -/
theorem firstGrammar_firstOrder (g : HGrammar) : (firstGrammar g).FirstOrder := by
  intro r hr
  obtain ⟨r', _, rfl⟩ := List.mem_map.mp hr
  exact unemb_firstOrder _ _

/-- Every recovered rule has valid call arities. -/
theorem firstGrammar_arityOk {g : HGrammar} (hw : g.WellTyped) (hs : FirstShape g) :
    (firstGrammar g).arityOk = true := by
  apply List.all_eq_true.mpr
  intro r hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  obtain ⟨n, b, ht, hb, hl⟩ := hs r' hr'
  have htyped := hw r' hr'
  rw [ht, hb] at htyped
  have htyped' : HasTy g.types (List.replicate n .p) b .p := by simpa using typed_lams htyped
  have ⟨hR, hG⟩ := firstGrammar_shape hs
  have hp := partial_parser (unemb_partial hR hG htyped' hl)
  simpa only [firstRule, ht, hb, width_parsers, peel_lams] using hp

/-- First-order decoding preserves and reflects finite observations. -/
theorem firstGrammar_obs {g : HGrammar} (hw : g.WellTyped) (hs : FirstShape g)
    {e : HExp} (ht : HasTy g.types [] e .p) (hl : LF e) (x : List Char) (r : Option (List Char)) :
    MacroObs (firstGrammar g) (unemb 0 e) x r ↔ HObs g e x r := by
  have ⟨hR, hG⟩ := firstGrammar_shape hs
  have he := emb_unemb (ar := 0) ht hl
  have ha := partial_parser (unemb_partial hR hG (ar := 0) ht hl)
  have ho := emb_obs (firstGrammar_firstOrder g) (firstGrammar_arityOk hw hs)
    (unemb_firstOrder 0 e) ha x r
  rw [emb_firstGrammar hw hs, he] at ho
  exact ho

theorem arrows_base {τs : List Ty} (h : (Shallot.MacroPeg.ExpSpace.arrows τs .p).order ≤ 1) :
    τs = List.replicate τs.length .p := by
  induction τs with
  | nil => rfl
  | cons τ τs ih =>
    have ho : τ.order = 0 := by simp only [Shallot.MacroPeg.ExpSpace.arrows, Ty.order] at h; omega
    have ht := type_zero ho
    have hs : (Shallot.MacroPeg.ExpSpace.arrows τs .p).order ≤ 1 :=
      Nat.le_trans (Nat.le_max_right _ _) h
    simp only [List.length_cons, List.replicate_succ]
    rw [ht]
    exact congrArg (List.cons Ty.p) (ih hs)

theorem lamsT_replicate (n : Nat) (b : HExp) :
    lamsT (List.replicate n .p) b = lams n b := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [lamsT, List.replicate_succ, lams] using congrArg (HExp.lam .p) ih

theorem arrows_replicate (n : Nat) :
    Shallot.MacroPeg.ExpSpace.arrows (List.replicate n .p) .p = Ty.parsers n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Shallot.MacroPeg.ExpSpace.arrows, List.replicate_succ, Ty.parsers, ih]

/-- The order-one tableau grammar uses only first-order rule declarations. -/
theorem tableau_firstShape {kt : Nat} (M : Complexity.TM kt) :
    FirstShape (Shallot.MacroPeg.Tableau.gT M 0) := by
  intro r hr
  have hshape : ∃ τs b, r.body = lamsT τs b ∧ LF b ∧
      r.ty = Shallot.MacroPeg.ExpSpace.arrows τs .p := by
    simp only [Shallot.MacroPeg.Tableau.gT, List.range_zero, List.flatMap_nil, List.append_nil, List.mem_append] at hr
    rcases hr with hr | hr
    · exact lf_level1 r hr
    · exact lf_tab_parser M 0 r hr
  obtain ⟨τs, b, hb, hl, ht⟩ := hshape
  have ho := Shallot.MacroPeg.Tableau.rule_order_le M 0 r hr
  rw [ht] at ho
  have hs := arrows_base ho
  refine ⟨τs.length, b, ?_, ?_, hl⟩
  · rw [ht, hs, arrows_replicate]; simp
  · rw [hb, hs, lamsT_replicate]; simp

/-- The same four-bit input encoding used by the machine-based complexity hierarchy. -/
def FirstLanguage (g : MGrammar) (e : MExp) : Complexity.Lang :=
  fun w => MacroObs g e ((Complexity.ofBits w).map tokChar) (some [])

/-- Every EXPTIME language reduces to one fixed, genuine first-order CBN grammar. -/
theorem first_order_hard {L : Complexity.Lang} (hL : KEXP 1 L) :
    ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧
      g.arityOk = true ∧ MExp.arityOk g e = true ∧
      Complexity.Reduces L (FirstLanguage g e) := by
  obtain ⟨kt, M, T, c, d, hT, hdec, htb⟩ := hL
  let H := Shallot.MacroPeg.Tableau.gT M 0
  let s := Shallot.MacroPeg.Tableau.startT 0
  have hw : H.WellTyped := Shallot.MacroPeg.Tableau.gT_wellTyped M 0
  have hs : FirstShape H := tableau_firstShape M
  have ht : HasTy H.types [] s .p := Shallot.MacroPeg.Tableau.startT_hasTy M 0
  have hl : LF s := lf_seq (lf_andP (lf_rcall1 (lf_ops 0).2.1)) (lf_star lf_any)
  have ⟨hR, hG⟩ := firstGrammar_shape hs
  refine ⟨firstGrammar H, unemb 0 s, firstGrammar_firstOrder H, unemb_firstOrder 0 s,
    firstGrammar_arityOk hw hs, partial_parser (unemb_partial hR hG (ar := 0) ht hl),
    encBits (c + 1) (d + 1), enc_polytime _ _, ?_⟩
  intro w
  exact (kexp_reduction (j := 1) (by decide) hT hdec htb w).trans
    (firstGrammar_obs hw hs ht hl _ _).symm

end Shallot.MacroPeg.HO
