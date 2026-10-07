import Cfg.NonemptyReduction
import Shallot.Peg.Determinism

/-!
# Adding or removing the empty word keeps a language in `PEL`

An arbitrary `IsPEL` witness may call rules that do not exist (they simply fail) and need not be
self-contained, so appending a new start rule could change what an out-of-range call means. We first
**pad** the rule list with failing rules beyond every index any rule (or the start) mentions: the padded
grammar derives exactly the same outcomes and is self-contained. Then the `&.`/`!.` guards add or remove `ε`.

- `isPEL_nonempty`: `L ∈ PEL → {w ∈ L | w ≠ ε} ∈ PEL`.
- `isPEL_addEps`: `L ∈ PEL → L ∪ {ε} ∈ PEL`.
-/

namespace Shallot.Cfg

open Shallot (Grammar Derives PExp PTree Outcome ruleAt Grammar.SelfContained PExp.NtBounded
  ruleAt_append_right derives_append_preserved derives_append_reflect derives_det)

/-- The always-failing expression `!ε`. -/
def phFail : PExp := .notP .eps

/-- `!ε` fails everywhere. -/
theorem phFail_fail {g : Grammar} (x : List Char) : Derives g phFail x .fail :=
  .notOk _ _ _ _ (.eps x)

/-- `!ε` never succeeds. -/
theorem phFail_not_ok {g : Grammar} {x : List Char} {t : PTree} {r : List Char}
    (h : Derives g phFail x (.ok t r)) : False := by
  cases h with
  | notFail _ _ hf => cases hf

/-- `ruleAt` is list indexing. -/
theorem ruleAt_eq_getElem? : ∀ (l : List PExp) (i : Nat), ruleAt l i = l[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: rs, n + 1 => by simp only [ruleAt, List.getElem?_cons_succ]; exact ruleAt_eq_getElem? rs n

/-- One more than the largest rule index an expression calls (`0` if none). -/
def ntBound : PExp → Nat
  | .nt i => i + 1
  | .seq e₁ e₂ => max (ntBound e₁) (ntBound e₂)
  | .alt e₁ e₂ => max (ntBound e₁) (ntBound e₂)
  | .star e => ntBound e
  | .notP e => ntBound e
  | _ => 0

/-- An expression only calls indices below its `ntBound`. -/
theorem ntBounded_ntBound : ∀ e : PExp, e.NtBounded (ntBound e)
  | .eps => trivial
  | .any => trivial
  | .chr _ => trivial
  | .range _ _ => trivial
  | .lit _ => trivial
  | .nt i => by simp only [PExp.NtBounded, ntBound]; omega
  | .seq e₁ e₂ => ⟨Shallot.PExp.NtBounded_mono (Nat.le_max_left _ _) (ntBounded_ntBound e₁),
      Shallot.PExp.NtBounded_mono (Nat.le_max_right _ _) (ntBounded_ntBound e₂)⟩
  | .alt e₁ e₂ => ⟨Shallot.PExp.NtBounded_mono (Nat.le_max_left _ _) (ntBounded_ntBound e₁),
      Shallot.PExp.NtBounded_mono (Nat.le_max_right _ _) (ntBounded_ntBound e₂)⟩
  | .star e => ntBounded_ntBound e
  | .notP e => ntBounded_ntBound e

/-- The largest `ntBound` of a rule list. -/
def rulesBound : List PExp → Nat
  | [] => 0
  | r :: rs => max (ntBound r) (rulesBound rs)

/-- Each rule's bound is below the list's bound. -/
theorem ntBound_le_rulesBound : ∀ {l : List PExp} {r : PExp}, r ∈ l → ntBound r ≤ rulesBound l
  | [], _, h => absurd h List.not_mem_nil
  | r' :: rs, r, h => by
    rcases List.mem_cons.mp h with h | h
    · subst h; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ntBound_le_rulesBound h) (Nat.le_max_right _ _)

/-- The padded length: past the rules, the start, and every called index. -/
def padLen (g : Grammar) : Nat := max (max g.rules.length (g.start + 1)) (rulesBound g.rules)

/-- **Padding**: append failing rules up to `padLen g`. -/
def phPad (g : Grammar) : Grammar :=
  { rules := g.rules ++ List.replicate (padLen g - g.rules.length) phFail, start := g.start }

/-- The padded rule list has length `padLen g`. -/
theorem phPad_length (g : Grammar) : (phPad g).rules.length = padLen g := by
  simp only [phPad, List.length_append, List.length_replicate, padLen]; omega

/-- A rule of the padded grammar is the original rule, or it is `!ε` where the original had none. -/
theorem phPad_ruleAt (g : Grammar) (i : Nat) :
    ruleAt (phPad g).rules i = ruleAt g.rules i ∨
      (ruleAt g.rules i = none ∧ ruleAt (phPad g).rules i = some phFail) := by
  simp only [ruleAt_eq_getElem?, phPad]
  by_cases hi : i < g.rules.length
  · left; rw [List.getElem?_append_left hi]
  · have hn : g.rules[i]? = none := List.getElem?_eq_none (by omega)
    rw [List.getElem?_append_right (by omega), hn]
    by_cases hj : i - g.rules.length < padLen g - g.rules.length
    · right; exact ⟨rfl, by rw [List.getElem?_replicate]; simp [hj]⟩
    · left; rw [List.getElem?_replicate]; simp [hj]

/-- Padding preserves every derivation. -/
theorem derives_phPad {g : Grammar} {e : PExp} {x : List Char} {o : Outcome}
    (h : Derives g e x o) : Derives (phPad g) e x o := by
  induction h with
  | eps input => exact .eps input
  | anyOk c rest => exact .anyOk c rest
  | anyFail => exact .anyFail
  | chrOk c d rest hcd => exact .chrOk c d rest hcd
  | chrFail c d rest hcd => exact .chrFail c d rest hcd
  | chrEmpty c => exact .chrEmpty c
  | rangeOk lo hi d rest hc => exact .rangeOk lo hi d rest hc
  | rangeFail lo hi d rest hc => exact .rangeFail lo hi d rest hc
  | rangeEmpty lo hi => exact .rangeEmpty lo hi
  | litOk s input rest hs => exact .litOk s input rest hs
  | litFail s input hs => exact .litFail s input hs
  | ntOk i e' input rest t hr _ ih =>
    rcases phPad_ruleAt g i with h' | ⟨h', _⟩
    · exact .ntOk i e' input rest t (h'.trans hr) ih
    · rw [h'] at hr; cases hr
  | ntFail i e' input hr _ ih =>
    rcases phPad_ruleAt g i with h' | ⟨h', _⟩
    · exact .ntFail i e' input (h'.trans hr) ih
    · rw [h'] at hr; cases hr
  | ntMissing i input hr =>
    rcases phPad_ruleAt g i with h' | ⟨_, h'⟩
    · exact .ntMissing i input (h'.trans hr)
    · exact .ntFail i phFail input h' (phFail_fail input)
  | seqOk e1 e2 input r1 r2 t1 t2 _ _ ih1 ih2 => exact .seqOk e1 e2 input r1 r2 t1 t2 ih1 ih2
  | seqFail₁ e1 e2 input _ ih1 => exact .seqFail₁ e1 e2 input ih1
  | seqFail₂ e1 e2 input r1 t1 _ _ ih1 ih2 => exact .seqFail₂ e1 e2 input r1 t1 ih1 ih2
  | altL e1 e2 input rest t _ ih => exact .altL e1 e2 input rest t ih
  | altR e1 e2 input rest t _ _ ih1 ih2 => exact .altR e1 e2 input rest t ih1 ih2
  | altFail e1 e2 input _ _ ih1 ih2 => exact .altFail e1 e2 input ih1 ih2
  | starNil e input _ ih => exact .starNil e input ih
  | starCons e input rest rest' t ts _ _ ih1 ih2 => exact .starCons e input rest rest' t ts ih1 ih2
  | notOk e input rest t _ ih => exact .notOk e input rest t ih
  | notFail e input _ ih => exact .notFail e input ih

/-- Padding reflects every derivation, up to the tree (outcome kind and rest are kept). -/
theorem derives_of_phPad {g : Grammar} {e : PExp} {x : List Char} {o : Outcome}
    (h : Derives (phPad g) e x o) :
    (o = .fail → Derives g e x .fail) ∧ (∀ t r, o = .ok t r → Derives g e x (.ok t r)) := by
  induction h with
  | eps input => exact ⟨(fun h => by cases h), fun t r h => by cases h; exact .eps input⟩
  | anyOk c rest => exact ⟨(fun h => by cases h), fun t r h => by cases h; exact .anyOk c rest⟩
  | anyFail => exact ⟨fun _ => .anyFail, fun _ _ h => by cases h⟩
  | chrOk c d rest hcd => exact ⟨(fun h => by cases h), fun t r h => by cases h; exact .chrOk c d rest hcd⟩
  | chrFail c d rest hcd => exact ⟨fun _ => .chrFail c d rest hcd, fun _ _ h => by cases h⟩
  | chrEmpty c => exact ⟨fun _ => .chrEmpty c, fun _ _ h => by cases h⟩
  | rangeOk lo hi d rest hc =>
    exact ⟨(fun h => by cases h), fun t r h => by cases h; exact .rangeOk lo hi d rest hc⟩
  | rangeFail lo hi d rest hc => exact ⟨fun _ => .rangeFail lo hi d rest hc, fun _ _ h => by cases h⟩
  | rangeEmpty lo hi => exact ⟨fun _ => .rangeEmpty lo hi, fun _ _ h => by cases h⟩
  | litOk s input rest hs => exact ⟨(fun h => by cases h), fun t r h => by cases h; exact .litOk s input rest hs⟩
  | litFail s input hs => exact ⟨fun _ => .litFail s input hs, fun _ _ h => by cases h⟩
  | ntOk i e' input rest t hr hd ih =>
    refine ⟨(fun h => by cases h), fun t' r h => ?_⟩
    cases h
    rcases phPad_ruleAt g i with h' | ⟨_, h'⟩
    · exact .ntOk i e' input rest t (h'.symm.trans hr) (ih.2 t rest rfl)
    · rw [h'] at hr; cases hr; exact (phFail_not_ok hd).elim
  | ntFail i e' input hr _ ih =>
    refine ⟨fun _ => ?_, fun _ _ h => by cases h⟩
    rcases phPad_ruleAt g i with h' | ⟨h', _⟩
    · exact .ntFail i e' input (h'.symm.trans hr) (ih.1 rfl)
    · exact .ntMissing i input h'
  | ntMissing i input hr =>
    refine ⟨fun _ => ?_, fun _ _ h => by cases h⟩
    rcases phPad_ruleAt g i with h' | ⟨_, h'⟩
    · exact .ntMissing i input (h'.symm.trans hr)
    · rw [h'] at hr; cases hr
  | seqOk e1 e2 input r1 r2 t1 t2 _ _ ih1 ih2 =>
    exact ⟨(fun h => by cases h), fun t r h => by
      cases h; exact .seqOk e1 e2 input r1 r2 t1 t2 (ih1.2 _ _ rfl) (ih2.2 _ _ rfl)⟩
  | seqFail₁ e1 e2 input _ ih1 => exact ⟨fun _ => .seqFail₁ e1 e2 input (ih1.1 rfl), fun _ _ h => by cases h⟩
  | seqFail₂ e1 e2 input r1 t1 _ _ ih1 ih2 =>
    exact ⟨fun _ => .seqFail₂ e1 e2 input r1 t1 (ih1.2 _ _ rfl) (ih2.1 rfl), fun _ _ h => by cases h⟩
  | altL e1 e2 input rest t _ ih =>
    exact ⟨(fun h => by cases h), fun t' r h => by cases h; exact .altL e1 e2 input rest t (ih.2 _ _ rfl)⟩
  | altR e1 e2 input rest t _ _ ih1 ih2 =>
    exact ⟨(fun h => by cases h), fun t' r h => by
      cases h; exact .altR e1 e2 input rest t (ih1.1 rfl) (ih2.2 _ _ rfl)⟩
  | altFail e1 e2 input _ _ ih1 ih2 =>
    exact ⟨fun _ => .altFail e1 e2 input (ih1.1 rfl) (ih2.1 rfl), fun _ _ h => by cases h⟩
  | starNil e input _ ih =>
    exact ⟨(fun h => by cases h), fun t r h => by cases h; exact .starNil e input (ih.1 rfl)⟩
  | starCons e input rest rest' t ts _ _ ih1 ih2 =>
    exact ⟨(fun h => by cases h), fun t' r h => by
      cases h; exact .starCons e input rest rest' t ts (ih1.2 _ _ rfl) (ih2.2 _ _ rfl)⟩
  | notOk e input rest t _ ih => exact ⟨fun _ => .notOk e input rest t (ih.2 _ _ rfl), fun _ _ h => by cases h⟩
  | notFail e input _ ih =>
    exact ⟨(fun h => by cases h), fun t r h => by cases h; exact .notFail e input (ih.1 rfl)⟩

/-- The padded grammar accepts the same words. -/
theorem phPad_accepts_iff (g : Grammar) (w : List Char) :
    (∃ t, Derives (phPad g) (.nt (phPad g).start) w (.ok t [])) ↔ ∃ t, Derives g (.nt g.start) w (.ok t []) :=
  ⟨fun ⟨t, h⟩ => ⟨t, (derives_of_phPad h).2 t [] rfl⟩, fun ⟨t, h⟩ => ⟨t, derives_phPad h⟩⟩

/-- The padded grammar is self-contained. -/
theorem phPad_selfContained (g : Grammar) : (phPad g).SelfContained := by
  intro r hr
  rw [phPad_length]
  simp only [phPad, List.mem_append] at hr
  rcases hr with hr | hr
  · exact Shallot.PExp.NtBounded_mono (Nat.le_trans (ntBound_le_rulesBound hr) (Nat.le_max_right _ _))
      (ntBounded_ntBound r)
  · rw [(List.mem_replicate.mp hr).2]; exact trivial

/-- The padded grammar's start is in range. -/
theorem phPad_start (g : Grammar) : (phPad g).start < (phPad g).rules.length := by
  rw [phPad_length]; simp only [phPad, padLen]; omega

/-- Every `PEL` language has a self-contained witness with its start in range. -/
theorem isPEL_selfContained {L : Language} (hL : IsPEL L) :
    ∃ g : Grammar, g.SelfContained ∧ g.start < g.rules.length ∧
      ∀ w, L w ↔ ∃ t, Derives g (.nt g.start) w (.ok t []) := by
  obtain ⟨g, hg⟩ := hL
  exact ⟨phPad g, phPad_selfContained g, phPad_start g, fun w => (hg w).trans (phPad_accepts_iff g w).symm⟩

/-- **Removing `ε`**: the non-empty words of a `PEL` language form a `PEL` language. -/
theorem isPEL_nonempty {L : Language} (hL : IsPEL L) : IsPEL (fun w => w ≠ [] ∧ L w) := by
  obtain ⟨g, hself, hstart, hg⟩ := isPEL_selfContained hL
  obtain ⟨g', hg'⟩ := isPEL_nonemptyRestriction_of_isPEL g hself hstart hg
  refine ⟨g', fun w => ?_⟩
  rw [← hg' w]
  exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨b, a⟩ => ⟨a, b⟩⟩

/-- The start rule `!. / S`: accept the empty word, otherwise run `S`. -/
def epsBody (start : Nat) : PExp := .alt (.notP .any) (.nt start)

/-- `g` with the start rule `!. / S` appended. -/
def epsGrammar (g : Grammar) : Grammar :=
  { rules := g.rules ++ [epsBody g.start], start := g.rules.length }

/-- `epsGrammar g` accepts `ε` and the words `g` accepts. -/
theorem epsGrammar_iff (g : Grammar) (hself : g.SelfContained) (hstart : g.start < g.rules.length)
    (w : List Char) :
    (∃ t, Derives (epsGrammar g) (.nt (epsGrammar g).start) w (.ok t [])) ↔
      (w = [] ∨ ∃ t, Derives g (.nt g.start) w (.ok t [])) := by
  have hre : ruleAt (epsGrammar g).rules g.rules.length = some (epsBody g.start) :=
    ruleAt_append_right g.rules (epsBody g.start)
  have hnt : (PExp.nt g.start).NtBounded g.rules.length := hstart
  constructor
  · rintro ⟨t, ht⟩
    cases ht with
    | ntOk _ _ _ _ _ hr hd =>
      simp only [epsGrammar] at hr hre
      rw [hre] at hr
      cases hr
      cases hd with
      | altL _ _ _ _ _ h =>
        cases h with
        | notFail _ _ hf => cases hf; exact Or.inl rfl
      | altR _ _ _ _ _ _ h₂ =>
        exact Or.inr ⟨_, derives_append_reflect [epsBody g.start] g.rules.length hnt hself h₂⟩
  · rintro (rfl | ⟨t, ht⟩)
    · exact ⟨_, .ntOk _ _ _ _ _ hre (.altL _ _ _ _ _ (.notFail _ _ .anyFail))⟩
    · have ht' := derives_append_preserved [epsBody g.start] g.rules.length hnt hself ht
      cases w with
      | nil => exact ⟨_, .ntOk _ _ _ _ _ hre (.altL _ _ _ _ _ (.notFail _ _ .anyFail))⟩
      | cons c cs =>
        exact ⟨_, .ntOk _ _ _ _ _ hre (.altR _ _ _ _ _ (.notOk _ _ _ _ (.anyOk c cs)) ht')⟩

/-- **Adding `ε`**: a `PEL` language with the empty word added is a `PEL` language. -/
theorem isPEL_addEps {L : Language} (hL : IsPEL L) : IsPEL (fun w => w = [] ∨ L w) := by
  obtain ⟨g, hself, hstart, hg⟩ := isPEL_selfContained hL
  refine ⟨epsGrammar g, fun w => ?_⟩
  rw [epsGrammar_iff g hself hstart w]
  exact or_congr_right (hg w)

end Shallot.Cfg
