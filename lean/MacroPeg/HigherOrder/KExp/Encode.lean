import MacroPeg.HigherOrder.Tableau.Typing
import Complexity.Hardness

/-!
# The input of the tableau grammar, as an output template

`encChars m w` (`m` bit sites, `|`, one site per input bit, `#`) is the denotation of the template `encT` in the
environment with `S = m` (whenever `|w| ≤ m`), with tokens read back as characters by `tokChar` (`encT_denote`).
Counters: `0` runs over the bit sites, `2` over the input sites, `1` and `3` write the site codes `1ʲ0`. The input
loop runs to `S` and emits nothing past the end of `w` (`Cond.inBit` fails there), so the template needs no length.
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Shallot.MacroPeg.Levels
open Shallot.MacroPeg.Tableau

/-! ## Tokens -/

/-- The characters of the encoding, as tokens `0 … 7`. -/
def tokChar : Nat → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => 'x'
  | 3 => ';'
  | 4 => '|'
  | 5 => 'a'
  | 6 => 'b'
  | _ => '#'

/-! ## The template -/

/-- `1ʲ0` for `j` the value of counter `outer`, written with counter `inner`. -/
def codeT (outer inner : Nat) : Tmpl :=
  .seq (.forR inner .S (.ite (.lt inner outer) (.tok 1) .nil)) (.tok 0)

/-- A bit site `1ʲ0x;`. -/
def bitSiteT : Tmpl := .seq (codeT 0 1) (.seq (.tok 2) (.tok 3))

/-- An input site `1ʲ0a` or `1ʲ0b`, or nothing past the end of the input. -/
def inSiteT : Tmpl :=
  .ite (.inBit 2 false) (.seq (codeT 2 3) (.tok 5)) (.ite (.inBit 2 true) (.seq (codeT 2 3) (.tok 6)) .nil)

/-- The whole encoding: `S` bit sites, `|`, the input sites, `#`. -/
def encT : Tmpl := .seq (.forR 0 .S bitSiteT) (.seq (.tok 4) (.seq (.forR 2 .S inSiteT) (.tok 7)))

theorem encT_WF : encT.WF 4 := by
  simp [encT, bitSiteT, inSiteT, codeT, Tmpl.WF, Tmpl.loops, Cond.WF]

theorem encT_small (Z : Nat) : encT.Small Z := by
  simp [encT, bitSiteT, inSiteT, codeT, Tmpl.Small, Cond.Small]

/-! ## Its denotation -/

/-- A counted loop that emits `a` below `j` emits `min j S` copies. -/
theorem flatMap_below (a j : Nat) : ∀ S, (List.range S).flatMap (fun v => if v < j then [a] else []) =
    List.replicate (min j S) a
  | 0 => by simp
  | S + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_below a j S]
    by_cases h : S < j
    · simp [h, show min j (S + 1) = min j S + 1 by omega, List.replicate_succ']
    · simp [h, show min j (S + 1) = min j S by omega]

theorem codeT_denote (e : TEnv) (outer inner : Nat) (hne : inner ≠ outer) (hj : e.ctr outer ≤ e.S) :
    ((codeT outer inner).denote e).map tokChar = codeStr (e.ctr outer) := by
  have h : ∀ v, (e.set inner v).ctr outer = e.ctr outer := fun v => by simp [TEnv.set, Ne.symm hne]
  have hs : ∀ v, (e.set inner v).ctr inner = v := fun v => by simp [TEnv.set]
  have hb := flatMap_below 1 (e.ctr outer) e.S
  simp only [codeT, Tmpl.denote, Bound.val, Cond.eval, h, hs, decide_eq_true_eq, hb, List.map_append,
    show min (e.ctr outer) e.S = e.ctr outer by omega]
  simp [codeStr, tokChar]

theorem flatMap_congr' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.flatMap_cons, h x List.mem_cons_self, flatMap_congr' (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- The bit sites from `j` on, as a list over `List.range'`. -/
theorem bitsFrom_range' : ∀ (c j : Nat), bitsFrom j c = (List.range' j c).flatMap (fun i => siteStr i false)
  | 0, _ => by simp [bitsFrom]
  | c + 1, j => by simp [bitsFrom, List.range'_succ, bitsFrom_range' c (j + 1)]

theorem bitLoop_denote (e : TEnv) :
    ((Tmpl.forR 0 .S bitSiteT).denote e).map tokChar = bitsFrom 0 e.S := by
  rw [bitsFrom_range', ← List.range_eq_range']
  simp only [Tmpl.denote, Bound.val, List.map_flatMap]
  apply flatMap_congr'
  intro v hv
  have hv := List.mem_range.1 hv
  simp only [bitSiteT, Tmpl.denote, List.map_append]
  rw [codeT_denote _ 0 1 (by decide) (by simp [TEnv.set]; omega)]
  simp [TEnv.set, siteStr, tokChar]

/-- One input site of `w`, at position `i`, as characters. -/
def siteAt (w : List Bool) (i : Nat) : List Char :=
  match w[i]? with
  | some b => inSite i b
  | none => []

theorem inSiteT_denote (e : TEnv) (hi : e.ctr 2 ≤ e.S) : (inSiteT.denote e).map tokChar = siteAt e.w (e.ctr 2) := by
  unfold inSiteT siteAt
  rcases hw : e.w[e.ctr 2]? with _ | b
  · simp [Tmpl.denote, Cond.eval, hw]
  · cases b <;> simp [Tmpl.denote, Cond.eval, hw, codeT_denote e 2 3 (by decide) hi, inSite, tokChar]

theorem inSitesFrom_range' (W : List Bool) : ∀ (v : List Bool) (j : Nat), (∀ i < v.length, W[j + i]? = v[i]?) →
    (List.range' j v.length).flatMap (siteAt W) = inSitesFrom j v
  | [], _, _ => by simp [inSitesFrom]
  | b :: v, j, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem?_cons_zero] at h0
    simp only [List.length_cons, List.range'_succ, List.flatMap_cons, inSitesFrom]
    rw [inSitesFrom_range' W v (j + 1) (fun i hi => by
      have := h (i + 1) (by simp; omega); rw [show j + 1 + i = j + (i + 1) by omega, this]; simp)]
    simp [siteAt, h0]

theorem inLoop_denote (e : TEnv) (hn : e.w.length ≤ e.S) :
    ((Tmpl.forR 2 .S inSiteT).denote e).map tokChar = inSitesFrom 0 e.w := by
  simp only [Tmpl.denote, Bound.val, List.map_flatMap]
  rw [flatMap_congr' (g := siteAt e.w) (fun v hv => by
    rw [inSiteT_denote _ (by simp [TEnv.set]; have := List.mem_range.1 hv; omega)]; simp [TEnv.set])]
  rw [List.range_eq_range', show e.S = e.w.length + (e.S - e.w.length) by omega, ← List.range'_append_1,
    List.flatMap_append]
  rw [inSitesFrom_range' e.w e.w 0 (fun i _ => by simp)]
  rw [List.flatMap_eq_nil_iff.2 (fun i hi => by
    have := (List.mem_range'_1.1 hi).1
    simp [siteAt, List.getElem?_eq_none (show e.w.length ≤ i by omega)])]
  simp

/-- **The template writes the encoding.** -/
theorem encT_denote (w : List Bool) (S T : Nat) (ctr : Nat → Nat) (hn : w.length ≤ S) :
    (encT.denote ⟨w, S, T, ctr⟩).map tokChar = encChars S w := by
  show ((Tmpl.forR 0 .S bitSiteT).denote _ ++ ([4] ++ ((Tmpl.forR 2 .S inSiteT).denote _ ++ [7]))).map tokChar = _
  simp only [List.map_append]
  rw [bitLoop_denote, inLoop_denote _ hn]
  simp [encChars, sfxB, inputTail, tokChar]

/-- A template without names: it only emits its `tok`s. -/
def Plain : Tmpl → Prop
  | .name _ => False
  | .seq a b => Plain a ∧ Plain b
  | .forR _ _ body => Plain body
  | .ite _ a b => Plain a ∧ Plain b
  | _ => True

/-- A small name-free template emits tokens below `16`. -/
theorem plain_tokens (Z : Nat) : ∀ (t : Tmpl), t.Small Z → Plain t → ∀ (e : TEnv), ∀ x ∈ t.denote e, x < 16
  | .nil, _, _, _, x, hx => by simp [Tmpl.denote] at hx
  | .tok _, hs, _, _, x, hx => by simp only [Tmpl.denote, List.mem_singleton] at hx; subst hx; exact hs
  | .name _, _, hp, _, _, _ => hp.elim
  | .seq a b, hs, hp, e, x, hx => by
    simp only [Tmpl.denote, List.mem_append] at hx
    exact hx.elim (plain_tokens Z a hs.1 hp.1 e x) (plain_tokens Z b hs.2 hp.2 e x)
  | .forR _ _ body, hs, hp, e, x, hx => by
    simp only [Tmpl.denote, List.mem_flatMap] at hx
    obtain ⟨v, _, hx⟩ := hx
    exact plain_tokens Z body hs.2 hp _ x hx
  | .ite c a b, hs, hp, e, x, hx => by
    simp only [Tmpl.denote] at hx
    split at hx
    · exact plain_tokens Z a hs.2.1 hp.1 e x hx
    · exact plain_tokens Z b hs.2.2 hp.2 e x hx

theorem encT_tokens (e : TEnv) : ∀ x ∈ encT.denote e, x < 16 :=
  plain_tokens 0 encT (encT_small 0) (by simp [encT, bitSiteT, inSiteT, codeT, Plain]) e

end Shallot.MacroPeg.KExp
